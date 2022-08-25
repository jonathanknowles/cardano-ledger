{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Cardano.Ledger.Examples.AlonzoUTXOW (tests) where

import Cardano.Ledger.Address (Addr (..))
import Cardano.Ledger.Alonzo.Data (Data (..), hashData)
import Cardano.Ledger.Alonzo.Language (Language (..))
import Cardano.Ledger.Alonzo.PParams (AlonzoPParamsHKD (..))
import Cardano.Ledger.Alonzo.PlutusScriptApi (CollectError (..))
import Cardano.Ledger.Alonzo.Rules
  ( AlonzoUtxoPredFailure (..),
    AlonzoUtxosPredFailure (..),
    AlonzoUtxowPredFailure (..),
    FailureDescription (..),
    TagMismatchDescription (..),
  )
import Cardano.Ledger.Alonzo.Scripts
  ( CostModels (..),
    ExUnits (..),
  )
import qualified Cardano.Ledger.Alonzo.Scripts as Tag (Tag (..))
import Cardano.Ledger.Alonzo.Tx
  ( IsValid (..),
    ScriptPurpose (..),
  )
import Cardano.Ledger.Alonzo.TxWitness (RdmrPtr (..), Redeemers (..), TxDats (..), unRedeemers)
import qualified Cardano.Ledger.Babbage.PParams as Babbage (BabbagePParamsHKD (..))
import Cardano.Ledger.Babbage.Rules (BabbageUtxoPredFailure (..))
import Cardano.Ledger.Babbage.Rules as Babbage (BabbageUtxowPredFailure (..))
import Cardano.Ledger.BaseTypes
  ( Network (..),
    StrictMaybe (..),
    TxIx,
    mkTxIxPartial,
  )
import Cardano.Ledger.Block (txid)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Core hiding (TranslationError)
import Cardano.Ledger.Credential
  ( Credential (..),
    StakeCredential,
    StakeReference (..),
  )
import qualified Cardano.Ledger.Crypto as CC
import Cardano.Ledger.Keys
  ( GenDelegs (..),
    KeyHash,
    KeyPair (..),
    KeyRole (..),
    asWitness,
    hashKey,
  )
import Cardano.Ledger.Mary.Value (MaryValue (..), MultiAsset (..))
import Cardano.Ledger.Pretty
import Cardano.Ledger.Pretty.Babbage ()
import Cardano.Ledger.SafeHash (hashAnnotated)
import Cardano.Ledger.Shelley.API
  ( ProtVer (..),
    UTxO (..),
  )
import Cardano.Ledger.Shelley.LedgerState
  ( UTxOState (..),
    smartUTxOState,
  )
import Cardano.Ledger.Shelley.PParams (ShelleyPParamsHKD (..))
import Cardano.Ledger.Shelley.Rules.Utxo (UtxoEnv (..))
import Cardano.Ledger.Shelley.Rules.Utxow as Shelley (ShelleyUtxowPredFailure (..))
import Cardano.Ledger.Shelley.TxBody
  ( DCert (..),
    DelegCert (..),
    RewardAcnt (..),
    Wdrl (..),
  )
import Cardano.Ledger.Shelley.UTxO (makeWitnessVKey)
import Cardano.Ledger.ShelleyMA.Timelocks (ValidityInterval (..))
import Cardano.Ledger.TxIn (TxIn (..))
import Cardano.Ledger.Val (inject, (<+>))
import Cardano.Slotting.Slot (SlotNo (..))
import Control.State.Transition.Extended hiding (Assertion)
import Data.Default.Class (Default (..))
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Stack
import Numeric.Natural (Natural)
import qualified Plutus.V1.Ledger.Api as Plutus
import Test.Cardano.Ledger.Examples.STSTestUtils
  ( AlonzoBased (..),
    datumExample1,
    freeCostModelV1,
    initUTxO,
    keyBy,
    mkGenesisTxIn,
    notValidatingTx,
    redeemerExample1,
    someKeys,
    testUTXOW,
    trustMeP,
    validatingBody,
  )
import Test.Cardano.Ledger.Generic.Fields
  ( PParamsField (..),
    TxBodyField (..),
    TxField (..),
    TxOutField (..),
    WitnessesField (..),
  )
import Test.Cardano.Ledger.Generic.Indexed (theKeyPair)
import Test.Cardano.Ledger.Generic.PrettyCore ()
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Generic.Scriptic (HasTokens (..), PostShelley, Scriptic (..), after, matchkey)
import Test.Cardano.Ledger.Generic.Updaters
import Test.Cardano.Ledger.Shelley.Utils
  ( RawSeed (..),
    mkKeyPair,
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, testCase, (@?=))

tests :: TestTree
tests =
  testGroup
    "Generic Tests, testing Alonzo UTXOW PredicateFailures, in postAlonzo eras."
    [ alonzoUTXOWexamplesB (Alonzo Mock),
      alonzoUTXOWexamplesB (Babbage Mock),
      alonzoUTXOWexamplesB (Conway Mock)
    ]

alonzoUTXOWexamplesB ::
  forall era.
  ( AlonzoBased era (PredicateFailure (EraRule "UTXOW" era)),
    State (EraRule "UTXOW" era) ~ UTxOState era,
    GoodCrypto (Crypto era),
    HasTokens era,
    Scriptic era,
    Default (State (EraRule "PPUP" era)),
    EraTx era,
    PostShelley era, -- MAYBE WE CAN REPLACE THIS BY GoodCrypto,
    Value era ~ MaryValue (Crypto era)
  ) =>
  Proof era ->
  TestTree
alonzoUTXOWexamplesB pf =
  testGroup
    (show pf ++ " UTXOW examples")
    [ testGroup
        "valid transactions"
        [ testCase "validating SPEND script" $
            testU
              pf
              (trustMeP pf True $ validatingTx pf)
              (Right . utxoStEx1 $ pf),
          testCase "not validating SPEND script" $
            testU
              pf
              (trustMeP pf False $ notValidatingTx pf)
              (Right . utxoStEx2 $ pf),
          testCase "validating CERT script" $
            testU
              pf
              (trustMeP pf True $ validatingTxWithCert pf)
              (Right . utxoStEx3 $ pf),
          testCase "not validating CERT script" $
            testU
              pf
              (trustMeP pf False $ notValidatingTxWithCert pf)
              (Right . utxoStEx4 $ pf),
          testCase "validating WITHDRAWAL script" $
            testU
              pf
              (trustMeP pf True $ validatingTxWithWithdrawal pf)
              (Right . utxoStEx5 $ pf),
          testCase "not validating WITHDRAWAL script" $
            testU
              pf
              (trustMeP pf False $ notValidatingTxWithWithdrawal pf)
              (Right . utxoStEx6 $ pf),
          testCase "validating MINT script" $
            testU
              pf
              (trustMeP pf True $ validatingTxWithMint pf)
              (Right . utxoStEx7 $ pf),
          testCase "not validating MINT script" $
            testU
              pf
              (trustMeP pf False $ notValidatingTxWithMint pf)
              (Right . utxoStEx8 $ pf),
          testCase "validating scripts everywhere" $
            testU
              pf
              (trustMeP pf True $ validatingTxManyScripts pf)
              (Right . utxoStEx9 $ pf),
          testCase "acceptable supplimentary datum" $
            testU
              pf
              (trustMeP pf True $ okSupplimentaryDatumTx pf)
              (Right . utxoStEx10 $ pf),
          testCase "multiple identical certificates" $
            testU
              pf
              (trustMeP pf True $ multipleEqualCertsTx pf)
              (Right . utxoStEx11 $ pf),
          testCase "non-script output with datum" $
            testU
              pf
              (trustMeP pf True $ nonScriptOutWithDatumTx pf)
              (Right . utxoStEx12 $ pf)
        ],
      testGroup
        "invalid transactions"
        [ testCase "wrong network ID" $
            testU
              pf
              (trustMeP pf True $ incorrectNetworkIDTx pf)
              ( Left
                  [ fromUtxo @era (WrongNetworkInTxBody Testnet Mainnet)
                  ]
              ),
          testCase "missing required key witness" $
            testU
              pf
              (trustMeP pf True $ missingRequiredWitnessTx pf)
              ( Left [(fromPredFail @era . MissingRequiredSigners . Set.singleton) extraneousKeyHash]
              ),
          testCase "missing redeemer" $
            testU
              pf
              (trustMeP pf True $ missingRedeemerTx pf)
              ( Left
                  [ fromUtxos @era . CollectErrors $
                      [NoRedeemer (Spending (mkGenesisTxIn 1))],
                    fromPredFail $
                      MissingRedeemers @era
                        [(Spending (mkGenesisTxIn 1), alwaysSucceedsHash 3 pf)]
                  ]
              ),
          testCase "wrong wpp hash" $
            testU
              pf
              (trustMeP pf True $ wrongWppHashTx pf)
              ( Left
                  [ fromPredFail @era $
                      PPViewHashesDontMatch
                        ( newScriptIntegrityHash
                            pf
                            (pp pf)
                            [PlutusV1]
                            (Redeemers mempty)
                            txDatsExample1
                        )
                        ( newScriptIntegrityHash
                            pf
                            (pp pf)
                            [PlutusV1]
                            validatingRedeemersEx1
                            txDatsExample1
                        )
                  ]
              ),
          testCase "missing 1-phase script witness" $
            testU
              pf
              (trustMeP pf True $ missing1phaseScriptWitnessTx pf)
              ( Left
                  [ fromUtxow @era . MissingScriptWitnessesUTXOW . Set.singleton $
                      timelockHash 0 pf
                  ]
              ),
          testCase "missing 2-phase script witness" $
            testU
              pf
              (trustMeP pf True $ missing2phaseScriptWitnessTx pf)
              ( Left
                  [ -- these redeemers are associated with phase-1 scripts
                    fromPredFail @era . ExtraRedeemers $
                      [ RdmrPtr Tag.Mint 1,
                        RdmrPtr Tag.Cert 1,
                        RdmrPtr Tag.Rewrd 0
                      ],
                    fromUtxow @era . MissingScriptWitnessesUTXOW . Set.singleton $
                      alwaysSucceedsHash 2 pf
                  ]
              ),
          testCase "redeemer with incorrect label" $
            testU
              pf
              (trustMeP pf True $ wrongRedeemerLabelTx pf)
              ( Left
                  [ fromUtxos @era (CollectErrors [NoRedeemer (Spending (mkGenesisTxIn 1))]),
                    -- now "wrong redeemer label" means there are both unredeemable scripts and extra redeemers
                    fromPredFail @era . MissingRedeemers $
                      [ ( Spending (mkGenesisTxIn 1),
                          alwaysSucceedsHash 3 pf
                        )
                      ],
                    fromPredFail @era . ExtraRedeemers $ [RdmrPtr Tag.Mint 0]
                  ]
              ),
          testCase "missing datum" $
            testU
              pf
              (trustMeP pf True $ missingDatumTx pf)
              ( Left
                  [ fromPredFail @era $
                      MissingRequiredDatums
                        (Set.singleton $ hashData @era datumExample1)
                        mempty
                  ]
              ),
          testCase "phase 1 script failure" $
            testU
              pf
              (trustMeP pf True $ phase1FailureTx pf)
              ( Left
                  [ fromUtxow @era $
                      ScriptWitnessNotValidatingUTXOW $
                        Set.fromList
                          [ timelockHash 0 pf,
                            timelockHash 1 pf,
                            timelockHash 2 pf
                          ]
                  ]
              ),
          testCase "valid transaction marked as invalid" $
            testU
              pf
              (trustMeP pf False $ validatingTx pf)
              ( Left [fromUtxos @era (ValidationTagMismatch (IsValid False) PassedUnexpectedly)]
              ),
          testCase "invalid transaction marked as valid" $
            specialCase
              (UTXOW pf)
              (initUTxO pf)
              (pp pf)
              (trustMeP pf True $ notValidatingTx pf)
              ( Left
                  [ fromUtxos @era
                      ( ValidationTagMismatch
                          (IsValid True)
                          (FailedUnexpectedly (quietPlutusFailure :| []))
                      )
                  ]
              ),
          testCase "too many execution units for tx" $
            testU
              pf
              (trustMeP pf True $ tooManyExUnitsTx pf)
              ( Left
                  [ fromUtxo @era $
                      ExUnitsTooBigUTxO
                        (ExUnits {exUnitsMem = 1000000, exUnitsSteps = 1000000})
                        (ExUnits {exUnitsMem = 1000001, exUnitsSteps = 5000})
                  ]
              ),
          testCase "missing signature for collateral input" $
            testU
              pf
              (trustMeP pf True $ missingCollateralSig pf)
              ( Left
                  [ fromUtxow @era
                      ( MissingVKeyWitnessesUTXOW
                          ( Set.fromList
                              [ asWitness $
                                  hashKey (vKey $ someKeys pf)
                              ]
                          )
                      )
                  ]
              ),
          testCase "insufficient collateral" $
            testUTXOW
              (UTXOW pf)
              (initUTxO pf)
              (newPParams pf $ defaultPPs ++ [CollateralPercentage 150])
              (trustMeP pf True $ validatingTx pf)
              ( Left [fromUtxo @era (InsufficientCollateral (Coin 5) (Coin 8))]
              ),
          testCase "two-phase UTxO with no datum hash" $
            testU
              pf
              (trustMeP pf True $ plutusOutputWithNoDataTx pf)
              ( Left
                  [ fromPredFail @era $ UnspendableUTxONoDatumHash . Set.singleton $ mkGenesisTxIn 101
                  ]
              ),
          testCase "unacceptable supplimentary datum" $
            testUTXOWsubset
              (UTXOW pf) -- Special rules apply here, use (expected `isSubset` computed)
              (initUTxO pf)
              (pp pf)
              (trustMeP pf True $ notOkSupplimentaryDatumTx pf)
              ( Left
                  [ fromPredFail @era $
                      NonOutputSupplimentaryDatums
                        (Set.singleton $ hashData @era totallyIrrelevantDatum)
                        mempty
                  ]
              ),
          testCase "unacceptable extra redeemer" $
            testU
              pf
              (trustMeP pf True $ extraRedeemersTx pf)
              ( Left
                  [ fromPredFail @era $
                      ExtraRedeemers
                        [RdmrPtr Tag.Spend 7]
                  ]
              ),
          testCase "multiple equal plutus-locked certs" $
            testU
              pf
              (trustMeP pf True $ multipleEqualCertsTxInvalid pf)
              ( Left
                  [ fromPredFail @era $ ExtraRedeemers [RdmrPtr Tag.Cert 1]
                  ]
              ),
          testCase "no cost model" $
            testU
              pf
              (trustMeP pf True $ noCostModelTx pf)
              ( Left [fromUtxos @era (CollectErrors [NoCostModel PlutusV2])]
              )
        ]
    ]

-- =======================
-- Setup the initial state
-- =======================

defaultPPs :: [PParamsField era]
defaultPPs =
  [ Costmdls . CostModels $ Map.singleton PlutusV1 freeCostModelV1,
    MaxValSize 1000000000,
    MaxTxExUnits $ ExUnits 1000000 1000000,
    MaxBlockExUnits $ ExUnits 1000000 1000000,
    ProtocolVersion $ ProtVer 5 0,
    CollateralPercentage 100
  ]

utxoEnv :: PParams era -> UtxoEnv era
utxoEnv pparams =
  UtxoEnv
    (SlotNo 0)
    pparams
    mempty
    (GenDelegs mempty)

-- | Create an address with a given payment script.
-- The proof here is used only as a Proxy.
scriptAddr :: forall era. (Scriptic era) => Script era -> Proof era -> Addr (Crypto era)
scriptAddr s _pf = Addr Testnet pCred sCred
  where
    pCred = ScriptHashObj . hashScript @era $ s
    (_ssk, svk) = mkKeyPair @(Crypto era) (RawSeed 0 0 0 0 0)
    sCred = StakeRefBase . KeyHashObj . hashKey $ svk

someAddr :: forall era. Era era => Proof era -> Addr (Crypto era)
someAddr pf = Addr Testnet pCred sCred
  where
    (_ssk, svk) = mkKeyPair @(Crypto era) (RawSeed 0 0 0 0 2)
    pCred = KeyHashObj . hashKey . vKey $ someKeys pf
    sCred = StakeRefBase . KeyHashObj . hashKey $ svk

alwaysSucceedsHash ::
  forall era.
  Scriptic era =>
  Natural ->
  Proof era ->
  ScriptHash (Crypto era)
alwaysSucceedsHash n pf = hashScript @era $ always n pf

alwaysFailsHash :: forall era. Scriptic era => Natural -> Proof era -> ScriptHash (Crypto era)
alwaysFailsHash n pf = hashScript @era $ never n pf

timelockScript :: PostShelley era => Int -> Proof era -> Script era
timelockScript s = allOf [matchkey 1, after (100 + s)]

timelockHash ::
  forall era.
  PostShelley era =>
  Int ->
  Proof era ->
  ScriptHash (Crypto era)
timelockHash n pf = hashScript @era $ timelockScript n pf

initialUtxoSt ::
  (Default (State (EraRule "PPUP" era)), EraTxOut era) =>
  UTxO era ->
  UTxOState era
initialUtxoSt utxo = smartUTxOState utxo (Coin 0) (Coin 0) def

-- | This is a helper type for the expectedUTxO function.
--  ExpectSuccess indicates that we created a valid transaction
--  where the IsValid flag is true.
data Expect era
  = ExpectSuccess (TxBody era) (TxOut era)
  | ExpectSuccessInvalid
  | ExpectFailure

-- | In each of our main eight examples, the UTxO map obtained
-- by applying the transaction is straightforward. This function
-- captures the logic.
--
-- Each example transaction (given a number i) will use
-- (TxIn genesisId (10+i), someOutput) for its' single input,
-- and (TxIn genesisId i, collateralOutput) for its' single collateral output.
--
-- If we expect the transaction script to validate, then
-- the UTxO for (TxIn genesisId i) will be consumed and a UTxO will be created.
-- Otherwise, the UTxO for (TxIn genesisId (10+i)) will be consumed.
expectedUTxO ::
  forall era.
  (HasCallStack, EraTxBody era) =>
  UTxO era ->
  Expect era ->
  Integer ->
  UTxO era
expectedUTxO initUtxo ex idx = UTxO utxo
  where
    utxo = case ex of
      ExpectSuccess txb newOut ->
        Map.insert (TxIn (txid txb) minBound) newOut (filteredUTxO (mkTxIxPartial idx))
      ExpectSuccessInvalid -> filteredUTxO (mkTxIxPartial idx)
      ExpectFailure -> filteredUTxO (mkTxIxPartial (10 + idx))
    filteredUTxO :: TxIx -> Map.Map (TxIn (Crypto era)) (TxOut era)
    filteredUTxO x = Map.filterWithKey (\(TxIn _ i) _ -> i /= x) $ unUTxO initUtxo

expectedUTxO' ::
  (HasCallStack, EraTxBody era, PostShelley era) =>
  Proof era ->
  Expect era ->
  Integer ->
  UTxO era
expectedUTxO' pf ex idx = expectedUTxO (initUTxO pf) ex idx

pp :: Proof era -> PParams era
pp pf = newPParams pf defaultPPs

-- =========================================================================
--  Example 1: Process a SPEND transaction with a succeeding Plutus script.
-- =========================================================================

txDatsExample1 :: Era era => TxDats era
txDatsExample1 = TxDats $ keyBy hashData [datumExample1]

validatingRedeemersEx1 :: Era era => Redeemers era
validatingRedeemersEx1 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Spend 0) (redeemerExample1, ExUnits 5000 5000)

extraRedeemersEx :: Era era => Redeemers era
extraRedeemersEx =
  Redeemers $
    Map.insert (RdmrPtr Tag.Spend 7) (redeemerExample1, ExUnits 432 444) (unRedeemers validatingRedeemersEx1)

extraRedeemersBody :: EraTxBody era => Proof era -> TxBody era
extraRedeemersBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 1],
      Collateral' [mkGenesisTxIn 11],
      Outputs' [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] extraRedeemersEx txDatsExample1)
    ]

extraRedeemersTx ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
extraRedeemersTx pf =
  newTx
    pf
    [ Body (extraRedeemersBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (extraRedeemersBody pf)) (someKeys pf)],
          ScriptWits' [always 3 pf],
          DataWits' [datumExample1],
          RdmrWits extraRedeemersEx
        ]
    ]

outEx1 :: EraTxOut era => Proof era -> TxOut era
outEx1 pf = newTxOut pf [Address (someAddr pf), Amount (inject $ Coin 4995)]

validatingTx ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
validatingTx pf =
  newTx
    pf
    [ Body (validatingBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (validatingBody pf)) (someKeys pf)],
          ScriptWits' [always 3 pf],
          DataWits' [datumExample1],
          RdmrWits validatingRedeemersEx1
        ]
    ]

utxoEx1 :: forall era. (PostShelley era, EraTxBody era) => Proof era -> UTxO era
utxoEx1 pf = expectedUTxO' pf (ExpectSuccess (validatingBody pf) (outEx1 pf)) 1

utxoStEx1 ::
  forall era.
  (Default (State (EraRule "PPUP" era)), EraTxBody era, PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx1 pf = smartUTxOState (utxoEx1 pf) (Coin 0) (Coin 5) def

-- ======================================================================
--  Example 2: Process a SPEND transaction with a failing Plutus script.
-- ======================================================================

utxoEx2 :: (EraTxBody era, PostShelley era) => Proof era -> UTxO era
utxoEx2 pf = expectedUTxO' pf ExpectFailure 2

utxoStEx2 ::
  (Default (State (EraRule "PPUP" era)), EraTxBody era, PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx2 pf = smartUTxOState (utxoEx2 pf) (Coin 0) (Coin 5) def

-- =========================================================================
--  Example 3: Process a CERT transaction with a succeeding Plutus script.
-- =========================================================================

outEx3 :: EraTxOut era => Proof era -> TxOut era
outEx3 pf = newTxOut pf [Address (someAddr pf), Amount (inject $ Coin 995)]

redeemerExample3 :: Era era => Data era
redeemerExample3 = Data (Plutus.I 42)

validatingRedeemersEx3 :: Era era => Redeemers era
validatingRedeemersEx3 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Cert 0) (redeemerExample3, ExUnits 5000 5000)

scriptStakeCredSuceed :: Scriptic era => Proof era -> StakeCredential (Crypto era)
scriptStakeCredSuceed pf = ScriptHashObj (alwaysSucceedsHash 2 pf)

validatingBodyWithCert :: (Scriptic era, EraTxBody era) => Proof era -> TxBody era
validatingBodyWithCert pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 3],
      Collateral' [mkGenesisTxIn 13],
      Outputs' [outEx3 pf],
      Certs' [DCertDeleg (DeRegKey $ scriptStakeCredSuceed pf)],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] validatingRedeemersEx3 mempty)
    ]

validatingTxWithCert ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
validatingTxWithCert pf =
  newTx
    pf
    [ Body (validatingBodyWithCert pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (validatingBodyWithCert pf)) (someKeys pf)],
          ScriptWits' [always 2 pf],
          RdmrWits validatingRedeemersEx3
        ]
    ]

utxoEx3 :: (PostShelley era, EraTxBody era) => Proof era -> UTxO era
utxoEx3 pf = expectedUTxO' pf (ExpectSuccess (validatingBodyWithCert pf) (outEx3 pf)) 3

utxoStEx3 ::
  (Default (State (EraRule "PPUP" era)), EraTxBody era, PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx3 pf = smartUTxOState (utxoEx3 pf) (Coin 0) (Coin 5) def

-- =====================================================================
--  Example 4: Process a CERT transaction with a failing Plutus script.
-- =====================================================================

outEx4 :: (Scriptic era, EraTxOut era) => Proof era -> TxOut era
outEx4 pf = newTxOut pf [Address (someAddr pf), Amount (inject $ Coin 995)]

redeemerExample4 :: Era era => Data era
redeemerExample4 = Data (Plutus.I 0)

notValidatingRedeemersEx4 :: Era era => Redeemers era
notValidatingRedeemersEx4 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Cert 0) (redeemerExample4, ExUnits 5000 5000)

scriptStakeCredFail :: Scriptic era => Proof era -> StakeCredential (Crypto era)
scriptStakeCredFail pf = ScriptHashObj (alwaysFailsHash 1 pf)

notValidatingBodyWithCert :: (Scriptic era, EraTxBody era) => Proof era -> TxBody era
notValidatingBodyWithCert pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 4],
      Collateral' [mkGenesisTxIn 14],
      Outputs' [outEx4 pf],
      Certs' [DCertDeleg (DeRegKey $ scriptStakeCredFail pf)],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] notValidatingRedeemersEx4 mempty)
    ]

notValidatingTxWithCert ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
notValidatingTxWithCert pf =
  newTx
    pf
    [ Body (notValidatingBodyWithCert pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (notValidatingBodyWithCert pf)) (someKeys pf)],
          ScriptWits' [never 1 pf],
          RdmrWits notValidatingRedeemersEx4
        ]
    ]

utxoEx4 :: (EraTxBody era, PostShelley era) => Proof era -> UTxO era
utxoEx4 pf = expectedUTxO' pf ExpectFailure 4

utxoStEx4 ::
  (Default (State (EraRule "PPUP" era)), EraTxBody era, PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx4 pf = smartUTxOState (utxoEx4 pf) (Coin 0) (Coin 5) def

-- ==============================================================================
--  Example 5: Process a WITHDRAWAL transaction with a succeeding Plutus script.
-- ==============================================================================

outEx5 :: (Scriptic era, EraTxOut era) => Proof era -> TxOut era
outEx5 pf = newTxOut pf [Address (someAddr pf), Amount (inject $ Coin 1995)]

redeemerExample5 :: Era era => Data era
redeemerExample5 = Data (Plutus.I 42)

validatingRedeemersEx5 :: Era era => Redeemers era
validatingRedeemersEx5 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Rewrd 0) (redeemerExample5, ExUnits 5000 5000)

validatingBodyWithWithdrawal :: (EraTxBody era, Scriptic era) => Proof era -> TxBody era
validatingBodyWithWithdrawal pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 5],
      Collateral' [mkGenesisTxIn 15],
      Outputs' [outEx5 pf],
      Txfee (Coin 5),
      Wdrls
        ( Wdrl $
            Map.singleton
              (RewardAcnt Testnet (scriptStakeCredSuceed pf))
              (Coin 1000)
        ),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] validatingRedeemersEx5 mempty)
    ]

validatingTxWithWithdrawal ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
validatingTxWithWithdrawal pf =
  newTx
    pf
    [ Body (validatingBodyWithWithdrawal pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (validatingBodyWithWithdrawal pf)) (someKeys pf)],
          ScriptWits' [always 2 pf],
          RdmrWits validatingRedeemersEx5
        ]
    ]

utxoEx5 :: (PostShelley era, EraTxBody era) => Proof era -> UTxO era
utxoEx5 pf = expectedUTxO' pf (ExpectSuccess (validatingBodyWithWithdrawal pf) (outEx5 pf)) 5

utxoStEx5 ::
  (Default (State (EraRule "PPUP" era)), EraTxBody era, PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx5 pf = smartUTxOState (utxoEx5 pf) (Coin 0) (Coin 5) def

-- ===========================================================================
--  Example 6: Process a WITHDRAWAL transaction with a failing Plutus script.
-- ===========================================================================

outEx6 :: (Scriptic era, EraTxOut era) => Proof era -> TxOut era
outEx6 pf = newTxOut pf [Address (someAddr pf), Amount (inject $ Coin 1995)]

redeemerExample6 :: Era era => Data era
redeemerExample6 = Data (Plutus.I 0)

notValidatingRedeemersEx6 :: Era era => Redeemers era
notValidatingRedeemersEx6 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Rewrd 0) (redeemerExample6, ExUnits 5000 5000)

notValidatingBodyWithWithdrawal :: (Scriptic era, EraTxBody era) => Proof era -> TxBody era
notValidatingBodyWithWithdrawal pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 6],
      Collateral' [mkGenesisTxIn 16],
      Outputs' [outEx6 pf],
      Txfee (Coin 5),
      Wdrls
        ( Wdrl $
            Map.singleton
              (RewardAcnt Testnet (scriptStakeCredFail pf))
              (Coin 1000)
        ),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] notValidatingRedeemersEx6 mempty)
    ]

notValidatingTxWithWithdrawal ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
notValidatingTxWithWithdrawal pf =
  newTx
    pf
    [ Body (notValidatingBodyWithWithdrawal pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (notValidatingBodyWithWithdrawal pf)) (someKeys pf)],
          ScriptWits' [never 1 pf],
          RdmrWits notValidatingRedeemersEx6
        ]
    ]

utxoEx6 :: (EraTxBody era, PostShelley era) => Proof era -> UTxO era
utxoEx6 pf = expectedUTxO' pf ExpectFailure 6

utxoStEx6 ::
  (Default (State (EraRule "PPUP" era)), EraTxBody era, PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx6 pf = smartUTxOState (utxoEx6 pf) (Coin 0) (Coin 5) def

-- =============================================================================
--  Example 7: Process a MINT transaction with a succeeding Plutus script.
-- =============================================================================

mintEx7 :: forall era. (Scriptic era, HasTokens era) => Proof era -> MultiAsset (Crypto era)
mintEx7 pf = forge @era 1 (always 2 pf)

outEx7 :: (HasTokens era, EraTxOut era, Scriptic era, Value era ~ MaryValue (Crypto era)) => Proof era -> TxOut era
outEx7 pf = newTxOut pf [Address (someAddr pf), Amount (MaryValue 0 (mintEx7 pf) <+> inject (Coin 995))]

redeemerExample7 :: Era era => Data era
redeemerExample7 = Data (Plutus.I 42)

validatingRedeemersEx7 :: Era era => Redeemers era
validatingRedeemersEx7 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Mint 0) (redeemerExample7, ExUnits 5000 5000)

validatingBodyWithMint ::
  (HasTokens era, EraTxBody era, Scriptic era, Value era ~ MaryValue (Crypto era)) =>
  Proof era ->
  TxBody era
validatingBodyWithMint pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 7],
      Collateral' [mkGenesisTxIn 17],
      Outputs' [outEx7 pf],
      Txfee (Coin 5),
      Mint (mintEx7 pf),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] validatingRedeemersEx7 mempty)
    ]

validatingTxWithMint ::
  forall era.
  ( Scriptic era,
    HasTokens era,
    EraTx era,
    GoodCrypto (Crypto era),
    Value era ~ MaryValue (Crypto era)
  ) =>
  Proof era ->
  Tx era
validatingTxWithMint pf =
  newTx
    pf
    [ Body (validatingBodyWithMint pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (validatingBodyWithMint pf)) (someKeys pf)],
          ScriptWits' [always 2 pf],
          RdmrWits validatingRedeemersEx7
        ]
    ]

utxoEx7 :: forall era. (HasTokens era, EraTxBody era, PostShelley era, Value era ~ MaryValue (Crypto era)) => Proof era -> UTxO era
utxoEx7 pf = expectedUTxO' pf (ExpectSuccess (validatingBodyWithMint pf) (outEx7 pf)) 7

utxoStEx7 ::
  forall era.
  (Default (State (EraRule "PPUP" era)), PostShelley era, EraTxBody era, HasTokens era, Value era ~ MaryValue (Crypto era)) =>
  Proof era ->
  UTxOState era
utxoStEx7 pf = smartUTxOState (utxoEx7 pf) (Coin 0) (Coin 5) def

-- ==============================================================================
--  Example 8: Process a MINT transaction with a failing Plutus script.
-- ==============================================================================

mintEx8 :: forall era. (Scriptic era, HasTokens era) => Proof era -> MultiAsset (Crypto era)
mintEx8 pf = forge @era 1 (never 1 pf)

outEx8 :: (HasTokens era, EraTxOut era, Scriptic era, Value era ~ MaryValue (Crypto era)) => Proof era -> TxOut era
outEx8 pf = newTxOut pf [Address (someAddr pf), Amount ((MaryValue 0 (mintEx8 pf)) <+> inject (Coin 995))]

redeemerExample8 :: Era era => Data era
redeemerExample8 = Data (Plutus.I 0)

notValidatingRedeemersEx8 :: Era era => Redeemers era
notValidatingRedeemersEx8 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Mint 0) (redeemerExample8, ExUnits 5000 5000)

notValidatingBodyWithMint ::
  (HasTokens era, EraTxBody era, Scriptic era, Value era ~ MaryValue (Crypto era)) =>
  Proof era ->
  TxBody era
notValidatingBodyWithMint pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 8],
      Collateral' [mkGenesisTxIn 18],
      Outputs' [outEx8 pf],
      Txfee (Coin 5),
      Mint (mintEx8 pf),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] notValidatingRedeemersEx8 mempty)
    ]

notValidatingTxWithMint ::
  forall era.
  ( Scriptic era,
    HasTokens era,
    EraTx era,
    GoodCrypto (Crypto era),
    Value era ~ MaryValue (Crypto era)
  ) =>
  Proof era ->
  Tx era
notValidatingTxWithMint pf =
  newTx
    pf
    [ Body (notValidatingBodyWithMint pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (notValidatingBodyWithMint pf)) (someKeys pf)],
          ScriptWits' [never 1 pf],
          RdmrWits notValidatingRedeemersEx8
        ]
    ]

utxoEx8 :: (PostShelley era, EraTxBody era) => Proof era -> UTxO era
utxoEx8 pf = expectedUTxO' pf ExpectFailure 8

utxoStEx8 ::
  (Default (State (EraRule "PPUP" era)), EraTxBody era, PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx8 pf = smartUTxOState (utxoEx8 pf) (Coin 0) (Coin 5) def

-- ====================================================================================
--  Example 9: Process a transaction with a succeeding script in every place possible,
--  and also with succeeding timelock scripts.
-- ====================================================================================

validatingRedeemersEx9 :: Era era => Redeemers era
validatingRedeemersEx9 =
  Redeemers . Map.fromList $
    [ (RdmrPtr Tag.Spend 0, (Data (Plutus.I 101), ExUnits 5000 5000)),
      (RdmrPtr Tag.Cert 1, (Data (Plutus.I 102), ExUnits 5000 5000)),
      (RdmrPtr Tag.Rewrd 0, (Data (Plutus.I 103), ExUnits 5000 5000)),
      (RdmrPtr Tag.Mint 1, (Data (Plutus.I 104), ExUnits 5000 5000))
    ]

mintEx9 :: forall era. (PostShelley era, HasTokens era) => Proof era -> MultiAsset (Crypto era)
mintEx9 pf = forge @era 1 (always 2 pf) <> forge @era 1 (timelockScript 1 pf)

outEx9 :: (HasTokens era, EraTxOut era, PostShelley era, Value era ~ MaryValue (Crypto era)) => Proof era -> TxOut era
outEx9 pf =
  newTxOut
    pf
    [ Address (someAddr pf),
      Amount ((MaryValue 0 (mintEx9 pf)) <+> inject (Coin 4996))
    ]

timelockStakeCred :: PostShelley era => Proof era -> StakeCredential (Crypto era)
timelockStakeCred pf = ScriptHashObj (timelockHash 2 pf)

validatingBodyManyScripts ::
  (HasTokens era, EraTxBody era, PostShelley era, Value era ~ MaryValue (Crypto era)) =>
  Proof era ->
  TxBody era
validatingBodyManyScripts pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 1, mkGenesisTxIn 100],
      Collateral' [mkGenesisTxIn 11],
      Outputs' [outEx9 pf],
      Txfee (Coin 5),
      Certs'
        [ DCertDeleg (DeRegKey $ timelockStakeCred pf),
          DCertDeleg (DeRegKey $ scriptStakeCredSuceed pf)
        ],
      Wdrls
        ( Wdrl $
            Map.fromList
              [ (RewardAcnt Testnet (scriptStakeCredSuceed pf), Coin 0),
                (RewardAcnt Testnet (timelockStakeCred pf), Coin 0)
              ]
        ),
      Mint (mintEx9 pf),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] validatingRedeemersEx9 txDatsExample1),
      Vldt (ValidityInterval SNothing (SJust $ SlotNo 1))
    ]

validatingTxManyScripts ::
  forall era.
  ( PostShelley era,
    HasTokens era,
    EraTxBody era,
    GoodCrypto (Crypto era),
    Value era ~ MaryValue (Crypto era)
  ) =>
  Proof era ->
  Tx era
validatingTxManyScripts pf =
  newTx
    pf
    [ Body (validatingBodyManyScripts pf),
      WitnessesI
        [ AddrWits' $
            map
              (makeWitnessVKey . hashAnnotated . validatingBodyManyScripts $ pf)
              [someKeys pf, theKeyPair 1],
          ScriptWits'
            [ always 2 pf,
              always 3 pf,
              timelockScript 0 pf,
              timelockScript 1 pf,
              timelockScript 2 pf
            ],
          DataWits' [datumExample1],
          RdmrWits validatingRedeemersEx9
        ]
    ]

utxoEx9 :: forall era. (EraTxBody era, PostShelley era, HasTokens era, Value era ~ MaryValue (Crypto era)) => Proof era -> UTxO era
utxoEx9 pf = UTxO utxo
  where
    utxo =
      Map.insert (TxIn (txid (validatingBodyManyScripts pf)) minBound) (outEx9 pf) $
        Map.filterWithKey
          (\k _ -> k /= mkGenesisTxIn 1 && k /= mkGenesisTxIn 100)
          (unUTxO $ initUTxO pf)

utxoStEx9 ::
  forall era.
  (EraTxBody era, Default (State (EraRule "PPUP" era)), PostShelley era, HasTokens era, Value era ~ MaryValue (Crypto era)) =>
  Proof era ->
  UTxOState era
utxoStEx9 pf = smartUTxOState (utxoEx9 pf) (Coin 0) (Coin 5) def

-- ====================================================================================
--  Example 10: A transaction with an acceptable supplimentary datum
-- ====================================================================================

outEx10 :: forall era. (EraTxBody era, Scriptic era) => Proof era -> TxOut era
outEx10 pf =
  newTxOut
    pf
    [ Address (scriptAddr (always 3 pf) pf),
      Amount (inject $ Coin 995),
      DHash' [hashData $ datumExample1 @era]
    ]

okSupplimentaryDatumTxBody :: (EraTxBody era, Scriptic era) => Proof era -> TxBody era
okSupplimentaryDatumTxBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 3],
      Outputs' [outEx10 pf],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [] (Redeemers mempty) txDatsExample1)
    ]

okSupplimentaryDatumTx ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
okSupplimentaryDatumTx pf =
  newTx
    pf
    [ Body (okSupplimentaryDatumTxBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (okSupplimentaryDatumTxBody pf)) (someKeys pf)],
          DataWits' [datumExample1]
        ]
    ]

utxoEx10 :: forall era. (EraTxBody era, PostShelley era) => Proof era -> UTxO era
utxoEx10 pf = expectedUTxO' pf (ExpectSuccess (okSupplimentaryDatumTxBody pf) (outEx10 pf)) 3

utxoStEx10 ::
  forall era.
  (EraTxBody era, Default (State (EraRule "PPUP" era)), PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx10 pf = smartUTxOState (utxoEx10 pf) (Coin 0) (Coin 5) def

-- ====================================================================================
--  Example 11: A transaction with multiple identical certificates
-- ====================================================================================

multipleEqualCertsRedeemers :: Era era => Redeemers era
multipleEqualCertsRedeemers =
  Redeemers $
    Map.fromList
      [ (RdmrPtr Tag.Cert 0, (redeemerExample3, ExUnits 5000 5000))
      ]

multipleEqualCertsBody :: (EraTxBody era, Scriptic era) => Proof era -> TxBody era
multipleEqualCertsBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 3],
      Collateral' [mkGenesisTxIn 13],
      Outputs' [outEx3 pf],
      Certs'
        [ DCertDeleg (DeRegKey $ scriptStakeCredSuceed pf),
          DCertDeleg (DeRegKey $ scriptStakeCredSuceed pf) -- not allowed by DELEG, but here is fine
        ],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] multipleEqualCertsRedeemers mempty)
    ]

multipleEqualCertsTx ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
multipleEqualCertsTx pf =
  newTx
    pf
    [ Body (multipleEqualCertsBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (multipleEqualCertsBody pf)) (someKeys pf)],
          ScriptWits' [always 2 pf],
          RdmrWits multipleEqualCertsRedeemers
        ]
    ]

utxoEx11 :: (EraTxBody era, PostShelley era) => Proof era -> UTxO era
utxoEx11 pf = expectedUTxO' pf (ExpectSuccess (multipleEqualCertsBody pf) (outEx3 pf)) 3

utxoStEx11 ::
  (EraTxBody era, Default (State (EraRule "PPUP" era)), PostShelley era) =>
  Proof era ->
  UTxOState era
utxoStEx11 pf = smartUTxOState (utxoEx11 pf) (Coin 0) (Coin 5) def

-- ====================================================================================
--  Example 12: Attaching a datum (hash) to a non-script output.
--
--  Note that a when spending a non-script output with a datum hash, the datum cannot
--  be supplied, because it is considered extraneous,
--  as in the 'notOkSupplimentaryDatumTx' example.
-- ====================================================================================

outEx12 :: EraTxOut era => Proof era -> TxOut era
outEx12 pf = newTxOut pf [Address (someAddr pf), Amount (inject $ Coin 1216)]

nonScriptOutWithDatumTxBody :: EraTxBody era => Proof era -> TxBody era
nonScriptOutWithDatumTxBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 103],
      Outputs' [outEx12 pf],
      Txfee (Coin 5)
    ]

nonScriptOutWithDatumTx ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
nonScriptOutWithDatumTx pf =
  newTx
    pf
    [ Body (nonScriptOutWithDatumTxBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (nonScriptOutWithDatumTxBody pf)) (someKeys pf)]
        ]
    ]

utxoEx12 :: (EraTxBody era, PostShelley era) => Proof era -> UTxO era
utxoEx12 pf = expectedUTxO' pf (ExpectSuccess (nonScriptOutWithDatumTxBody pf) (outEx12 pf)) 103

utxoStEx12 ::
  ( Default (State (EraRule "PPUP" era)),
    PostShelley era,
    EraTxBody era
  ) =>
  Proof era ->
  UTxOState era
utxoStEx12 pf =
  smartUTxOState
    (utxoEx12 pf)
    (Coin 0)
    (Coin 5)
    def

-- =======================
-- Invalid Transactions
-- =======================

incorrectNetworkIDTxBody :: EraTxBody era => Proof era -> TxBody era
incorrectNetworkIDTxBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 3],
      Outputs' [outEx3 pf],
      Txfee (Coin 5),
      Txnetworkid (SJust Mainnet)
    ]

incorrectNetworkIDTx :: (EraTx era, GoodCrypto (Crypto era)) => Proof era -> Tx era
incorrectNetworkIDTx pf =
  newTx
    pf
    [ Body (incorrectNetworkIDTxBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (incorrectNetworkIDTxBody pf)) (someKeys pf)]
        ]
    ]

extraneousKeyHash :: CC.Crypto c => KeyHash 'Witness c
extraneousKeyHash = hashKey . snd . mkKeyPair $ RawSeed 0 0 0 0 99

missingRequiredWitnessTxBody :: EraTxBody era => Proof era -> TxBody era
missingRequiredWitnessTxBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 3],
      Outputs' [outEx3 pf],
      Txfee (Coin 5),
      ReqSignerHashes' [extraneousKeyHash]
    ]

missingRequiredWitnessTx :: (EraTx era, GoodCrypto (Crypto era)) => Proof era -> Tx era
missingRequiredWitnessTx pf =
  newTx
    pf
    [ Body (missingRequiredWitnessTxBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (missingRequiredWitnessTxBody pf)) (someKeys pf)]
        ]
    ]

missingRedeemerTxBody :: EraTxBody era => Proof era -> TxBody era
missingRedeemerTxBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 1],
      Collateral' [mkGenesisTxIn 11],
      Outputs' [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] (Redeemers mempty) txDatsExample1)
    ]

missingRedeemerTx ::
  (Scriptic era, EraTx era, GoodCrypto (Crypto era)) =>
  Proof era ->
  Tx era
missingRedeemerTx pf =
  newTx
    pf
    [ Body (missingRedeemerTxBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (missingRedeemerTxBody pf)) (someKeys pf)],
          ScriptWits' [always 3 pf],
          DataWits' [datumExample1]
        ]
    ]

wrongWppHashTx ::
  (Scriptic era, EraTx era, GoodCrypto (Crypto era)) =>
  Proof era ->
  Tx era
wrongWppHashTx pf =
  newTx
    pf
    [ Body (missingRedeemerTxBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (missingRedeemerTxBody pf)) (someKeys pf)],
          ScriptWits' [always 3 pf],
          DataWits' [datumExample1],
          RdmrWits validatingRedeemersEx1
        ]
    ]

missing1phaseScriptWitnessTx ::
  forall era.
  ( PostShelley era,
    HasTokens era,
    EraTxBody era,
    GoodCrypto (Crypto era),
    Value era ~ MaryValue (Crypto era)
  ) =>
  Proof era ->
  Tx era
missing1phaseScriptWitnessTx pf =
  newTx
    pf
    [ Body (validatingBodyManyScripts pf),
      WitnessesI
        [ AddrWits' $
            map
              (makeWitnessVKey . hashAnnotated . validatingBodyManyScripts $ pf)
              [someKeys pf, theKeyPair 1],
          ScriptWits'
            [ always 2 pf,
              always 3 pf,
              -- intentionally missing -> timelockScript 0 pf,
              timelockScript 1 pf,
              timelockScript 2 pf
            ],
          DataWits' [datumExample1],
          RdmrWits validatingRedeemersEx9
        ]
    ]

missing2phaseScriptWitnessTx ::
  forall era.
  ( PostShelley era,
    HasTokens era,
    EraTx era,
    GoodCrypto (Crypto era),
    Value era ~ MaryValue (Crypto era)
  ) =>
  Proof era ->
  Tx era
missing2phaseScriptWitnessTx pf =
  newTx
    pf
    [ Body (validatingBodyManyScripts pf),
      WitnessesI
        [ AddrWits' $
            map
              (makeWitnessVKey . hashAnnotated . validatingBodyManyScripts $ pf)
              [someKeys pf, theKeyPair 1],
          ScriptWits'
            [ -- intentionally missing -> always 2 pf,
              always 3 pf,
              timelockScript 0 pf,
              timelockScript 1 pf,
              timelockScript 2 pf
            ],
          DataWits' [datumExample1],
          RdmrWits validatingRedeemersEx9
        ]
    ]

misPurposedRedeemer :: Era era => Redeemers era
misPurposedRedeemer =
  Redeemers $
    -- The label *should* be Spend, not Mint
    Map.singleton (RdmrPtr Tag.Mint 0) (redeemerExample1, ExUnits 5000 5000)

wrongRedeemerLabelTxBody :: EraTxBody era => Proof era -> TxBody era
wrongRedeemerLabelTxBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 1],
      Collateral' [mkGenesisTxIn 11],
      Outputs' [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] misPurposedRedeemer txDatsExample1)
    ]

wrongRedeemerLabelTx ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
wrongRedeemerLabelTx pf =
  newTx
    pf
    [ Body (wrongRedeemerLabelTxBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (wrongRedeemerLabelTxBody pf)) (someKeys pf)],
          ScriptWits' [always 3 pf],
          DataWits' [datumExample1],
          RdmrWits misPurposedRedeemer
        ]
    ]

missingDatumTxBody :: EraTxBody era => Proof era -> TxBody era
missingDatumTxBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 1],
      Collateral' [mkGenesisTxIn 11],
      Outputs' [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] validatingRedeemersEx1 mempty)
    ]

missingDatumTx ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
missingDatumTx pf =
  newTx
    pf
    [ Body (missingDatumTxBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (missingDatumTxBody pf)) (someKeys pf)],
          ScriptWits' [always 3 pf],
          RdmrWits validatingRedeemersEx1
        ]
    ]

phase1FailureTx ::
  forall era.
  ( PostShelley era,
    HasTokens era,
    EraTx era,
    GoodCrypto (Crypto era),
    Value era ~ MaryValue (Crypto era)
  ) =>
  Proof era ->
  Tx era
phase1FailureTx pf =
  newTx
    pf
    [ Body (validatingBodyManyScripts pf),
      WitnessesI
        [ AddrWits'
            [ makeWitnessVKey
                (hashAnnotated $ validatingBodyManyScripts pf)
                (someKeys pf)
            ],
          ScriptWits'
            [ always 2 pf,
              always 3 pf,
              timelockScript 0 pf,
              timelockScript 1 pf,
              timelockScript 2 pf
            ],
          DataWits' [datumExample1],
          RdmrWits validatingRedeemersEx9
        ]
    ]

validatingRedeemersTooManyExUnits :: Era era => Redeemers era
validatingRedeemersTooManyExUnits =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Spend 0) (redeemerExample1, ExUnits 1000001 5000)

tooManyExUnitsTxBody :: EraTxBody era => Proof era -> TxBody era
tooManyExUnitsTxBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 1],
      Collateral' [mkGenesisTxIn 11],
      Outputs' [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] validatingRedeemersTooManyExUnits txDatsExample1)
    ]

tooManyExUnitsTx ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
tooManyExUnitsTx pf =
  newTx
    pf
    [ Body (tooManyExUnitsTxBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (tooManyExUnitsTxBody pf)) (someKeys pf)],
          ScriptWits' [always 3 pf],
          DataWits' [datumExample1],
          RdmrWits validatingRedeemersTooManyExUnits
        ]
    ]

missingCollateralSig ::
  forall era.
  (Scriptic era, EraTx era) =>
  Proof era ->
  Tx era
missingCollateralSig pf =
  newTx
    pf
    [ Body (validatingBody pf),
      WitnessesI
        [ ScriptWits' [always 3 pf],
          DataWits' [datumExample1],
          RdmrWits validatingRedeemersEx1
        ]
    ]

plutusOutputWithNoDataTxBody :: EraTxBody era => Proof era -> TxBody era
plutusOutputWithNoDataTxBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 101],
      Collateral' [mkGenesisTxIn 11],
      Outputs' [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] validatingRedeemersEx1 mempty)
    ]

plutusOutputWithNoDataTx ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
plutusOutputWithNoDataTx pf =
  newTx
    pf
    [ Body (plutusOutputWithNoDataTxBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (plutusOutputWithNoDataTxBody pf)) (someKeys pf)],
          ScriptWits' [always 3 pf],
          RdmrWits validatingRedeemersEx1
        ]
    ]

totallyIrrelevantDatum :: Era era => Data era
totallyIrrelevantDatum = Data (Plutus.I 1729)

outputWithNoDatum :: forall era. EraTxOut era => Proof era -> TxOut era
outputWithNoDatum pf = newTxOut pf [Address $ someAddr pf, Amount (inject $ Coin 995)]

notOkSupplimentaryDatumTxBody :: EraTxBody era => Proof era -> TxBody era
notOkSupplimentaryDatumTxBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 3],
      Outputs' [outputWithNoDatum pf],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [] (Redeemers mempty) totallyIrrelevantTxDats)
    ]
  where
    totallyIrrelevantTxDats = TxDats $ keyBy hashData [totallyIrrelevantDatum]

notOkSupplimentaryDatumTx ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
notOkSupplimentaryDatumTx pf =
  newTx
    pf
    [ Body (notOkSupplimentaryDatumTxBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (notOkSupplimentaryDatumTxBody pf)) (someKeys pf)],
          DataWits' [totallyIrrelevantDatum]
        ]
    ]

multipleEqualCertsRedeemersInvalid :: Era era => Redeemers era
multipleEqualCertsRedeemersInvalid =
  Redeemers $
    Map.fromList
      [ (RdmrPtr Tag.Cert 0, (redeemerExample3, ExUnits 5000 5000)),
        (RdmrPtr Tag.Cert 1, (redeemerExample3, ExUnits 5000 5000))
      ]

multipleEqualCertsBodyInvalid :: EraTxBody era => Scriptic era => Proof era -> TxBody era
multipleEqualCertsBodyInvalid pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 3],
      Collateral' [mkGenesisTxIn 13],
      Outputs' [outEx3 pf],
      Certs'
        [ DCertDeleg (DeRegKey $ scriptStakeCredSuceed pf),
          DCertDeleg (DeRegKey $ scriptStakeCredSuceed pf) -- not allowed by DELEG, but here is fine
        ],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] multipleEqualCertsRedeemersInvalid mempty)
    ]

multipleEqualCertsTxInvalid ::
  forall era.
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
multipleEqualCertsTxInvalid pf =
  newTx
    pf
    [ Body (multipleEqualCertsBodyInvalid pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (multipleEqualCertsBodyInvalid pf)) (someKeys pf)],
          ScriptWits' [always 2 pf],
          RdmrWits multipleEqualCertsRedeemersInvalid
        ]
    ]

noCostModelBody :: EraTxBody era => Proof era -> TxBody era
noCostModelBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 102],
      Collateral' [mkGenesisTxIn 11],
      Outputs' [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV2] validatingRedeemersEx1 txDatsExample1)
    ]

noCostModelTx ::
  forall era.
  ( Scriptic era,
    GoodCrypto (Crypto era),
    EraTx era
  ) =>
  Proof era ->
  Tx era
noCostModelTx pf =
  newTx
    pf
    [ Body (noCostModelBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (noCostModelBody pf)) (someKeys pf)],
          ScriptWits' [alwaysAlt 3 pf],
          DataWits' [datumExample1],
          RdmrWits validatingRedeemersEx1
        ]
    ]

quietPlutusFailure :: FailureDescription
quietPlutusFailure = PlutusFailure "human" "debug"

-- =====================================================================================
-- Proof parameterized TestTrees

-- | This type is what you get when you use runSTS in the UTXOW rule. It is also
--   the type one uses for expected answers, to compare the 'computed' against 'expected'
type Result era = Either [PredicateFailure (EraRule "UTXOW" era)] (State (EraRule "UTXOW" era))

testUTXOWwith ::
  forall era.
  ( GoodCrypto (Crypto era),
    Default (State (EraRule "PPUP" era)),
    EraTx era
  ) =>
  WitRule "UTXOW" era ->
  (Result era -> Result era -> Assertion) ->
  UTxO era ->
  PParams era ->
  Tx era ->
  Result era ->
  Assertion
testUTXOWwith wit@(UTXOW proof) cont utxo pparams tx expected =
  let env = utxoEnv pparams
      state = initialUtxoSt utxo
   in case proof of
        Conway _ -> runSTS wit (TRC (env, state, tx)) (cont expected)
        Babbage _ -> runSTS wit (TRC (env, state, tx)) (cont expected)
        Alonzo _ -> runSTS wit (TRC (env, state, tx)) (cont expected)
        Mary _ -> runSTS wit (TRC (env, state, tx)) (cont expected)
        Allegra _ -> runSTS wit (TRC (env, state, tx)) (cont expected)
        Shelley _ -> runSTS wit (TRC (env, state, tx)) (cont expected)

isSubset :: Eq t => [t] -> [t] -> Bool
isSubset small big = List.all (`List.elem` big) small

subsetCont ::
  ( Eq x,
    Show x,
    PrettyA x,
    Eq y,
    Show y,
    PrettyA y
  ) =>
  Either [x] y ->
  Either [x] y ->
  Assertion
subsetCont expected computed =
  case (computed, expected) of
    (Left c, Left e) ->
      -- It is OK if the expected is a subset of what's computed
      if isSubset e c then e @?= e else c @?= e
    (Right c, Right e) -> c @?= e
    (Left x, Right y) ->
      error $
        "expected to pass with "
          ++ show (prettyA y)
          ++ "\n\nBut failed with\n\n"
          ++ show (ppList prettyA x)
    (Right x, Left y) ->
      error $
        "expected to fail with "
          ++ show (ppList prettyA y)
          ++ "\n\nBut passed with\n\n"
          ++ show (prettyA x)

-- ==============================================================================
-- Three slighty different ways to make an Assertion, but all with the same type

testUTXOWsubset,
  specialCase ::
    forall era.
    ( GoodCrypto (Crypto era),
      Default (State (EraRule "PPUP" era)),
      PostShelley era,
      EraTx era,
      HasCallStack
    ) =>
    WitRule "UTXOW" era ->
    UTxO era ->
    PParams era ->
    Tx era ->
    Either [PredicateFailure (EraRule "UTXOW" era)] (State (EraRule "UTXOW" era)) ->
    Assertion

-- | Use a subset test on the expected and computed [PredicateFailure]
testUTXOWsubset wit@(UTXOW (Alonzo _)) utxo = testUTXOWwith wit subsetCont utxo
testUTXOWsubset wit@(UTXOW (Babbage _)) utxo = testUTXOWwith wit subsetCont utxo
testUTXOWsubset wit@(UTXOW (Conway _)) utxo = testUTXOWwith wit subsetCont utxo
testUTXOWsubset (UTXOW other) _ = error ("Cannot use testUTXOW in era " ++ show other)

testU ::
  forall era.
  ( GoodCrypto (Crypto era),
    Default (State (EraRule "PPUP" era)),
    PostShelley era,
    EraTx era,
    HasCallStack
  ) =>
  Proof era ->
  Tx era ->
  Either [PredicateFailure (EraRule "UTXOW" era)] (State (EraRule "UTXOW" era)) ->
  Assertion
testU pf tx expect = testUTXOW (UTXOW pf) (initUTxO pf) (pp pf) tx expect

-- | Use a test where any two (ValidationTagMismatch x y) failures match regardless of 'x' and 'y'
specialCase wit@(UTXOW proof) utxo pparam tx expected =
  let env = utxoEnv pparam
      state = initialUtxoSt utxo
   in case proof of
        Alonzo _ -> runSTS wit (TRC (env, state, tx)) (specialCont proof expected)
        Babbage _ -> runSTS wit (TRC (env, state, tx)) (specialCont proof expected)
        Conway _ -> runSTS wit (TRC (env, state, tx)) (specialCont proof expected)
        other -> error ("Cannot use specialCase in era " ++ show other)

-- ========================================
-- This implements a special rule to test that for ValidationTagMismatch. Rather than comparing the insides of
-- ValidationTagMismatch (which are complicated and depend on Plutus) we just note that both the computed
-- and expected are ValidationTagMismatch. Of course the 'path' to ValidationTagMismatch differs by Era.
-- so we need to case over the Era proof, to get the path correctly.

findMismatch ::
  Proof era ->
  PredicateFailure (EraRule "UTXOW" era) ->
  Maybe (AlonzoUtxosPredFailure era)
findMismatch (Alonzo _) (ShelleyInAlonzoUtxowPredFailure (Shelley.UtxoFailure (UtxosFailure x@(ValidationTagMismatch _ _)))) = Just x
findMismatch (Babbage _) (Babbage.UtxoFailure (AlonzoInBabbageUtxoPredFailure (UtxosFailure x@(ValidationTagMismatch _ _)))) = Just x
findMismatch (Conway _) (Babbage.UtxoFailure (AlonzoInBabbageUtxoPredFailure (UtxosFailure x@(ValidationTagMismatch _ _)))) = Just x
findMismatch _ _ = Nothing

specialCont ::
  ( Eq (PredicateFailure (EraRule "UTXOW" era)),
    Eq a,
    Show (PredicateFailure (EraRule "UTXOW" era)),
    Show a,
    HasCallStack
  ) =>
  Proof era ->
  Either [PredicateFailure (EraRule "UTXOW" era)] a ->
  Either [PredicateFailure (EraRule "UTXOW" era)] a ->
  Assertion
specialCont proof expected computed =
  case (computed, expected) of
    (Left [x], Left [y]) ->
      case (findMismatch proof x, findMismatch proof y) of
        (Just _, Just _) -> y @?= y
        (_, _) -> error "Not both ValidationTagMismatch case 1"
    (Left _, Left _) -> error "Not both ValidationTagMismatch case 2"
    (Right x, Right y) -> x @?= y
    (Left _, Right _) -> error "expected to pass, but failed."
    (Right _, Left _) -> error "expected to fail, but passed."
