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

module Test.Cardano.Ledger.Examples.AlonzoBBODYExamples (alonzoBBODYExamples) where
import Cardano.Crypto.Hash.Class (sizeHash)
import Cardano.Ledger.Address (Addr (..))
import Cardano.Ledger.Alonzo.Data (Data (..), hashData)
import Cardano.Ledger.Alonzo.Language (Language (..))
import Cardano.Ledger.Alonzo.PParams (AlonzoPParamsHKD (..))
import Cardano.Ledger.Alonzo.Rules
  ( AlonzoBBODY,
    AlonzoBbodyPredFailure (..),
  )
import Cardano.Ledger.Alonzo.Scripts
  ( CostModels (..),
    ExUnits (..),
  )
import qualified Cardano.Ledger.Alonzo.Scripts as Tag (Tag (..))
import Cardano.Ledger.Alonzo.TxWitness (RdmrPtr (..), Redeemers (..))
import Cardano.Ledger.BHeaderView (BHeaderView (..))
import qualified Cardano.Ledger.Babbage.PParams as Babbage (BabbagePParamsHKD (..))
import Cardano.Ledger.BaseTypes
  ( BlocksMade (..),
    Network (..),
    StrictMaybe (..),
    textToUrl,
  )
import Cardano.Ledger.Block (Block (..), txid)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Core hiding (TranslationError)
import Cardano.Ledger.Credential
  ( Credential (..),
    StakeCredential,
    StakeReference (..),
  )
import qualified Cardano.Ledger.Crypto as CC
import Cardano.Ledger.Keys
  ( KeyPair (..),
    KeyRole (..),
    coerceKeyRole,
    hashKey,
    hashVerKeyVRF,
  )
import Cardano.Ledger.Mary.Value (MaryValue (..), MultiAsset (..))
import Cardano.Ledger.Pretty
import Cardano.Ledger.Pretty.Babbage ()
import Cardano.Ledger.SafeHash (hashAnnotated)
import Cardano.Ledger.Shelley.API
  ( DPState (..),
    DState (..),
    LedgerState (..),
    PoolParams (..),
    ProtVer (..),
    UTxO (..),
  )
import Cardano.Ledger.Shelley.BlockChain (bBodySize)
import Cardano.Ledger.Shelley.LedgerState
  ( UTxOState (..),
    smartUTxOState,
  )
import Cardano.Ledger.Shelley.Rules.Bbody (BbodyEnv (..), ShelleyBbodyPredFailure (..), ShelleyBbodyState (..))
import Cardano.Ledger.Shelley.Rules.Delegs (ShelleyDelegsPredFailure (..))
import Cardano.Ledger.Shelley.Rules.Delpl (ShelleyDelplPredFailure (..))
import Cardano.Ledger.Shelley.Rules.Ledger (ShelleyLedgerPredFailure (..))
import Cardano.Ledger.Shelley.Rules.Ledgers (ShelleyLedgersPredFailure (..))
import Cardano.Ledger.Shelley.Rules.Pool (ShelleyPoolPredFailure (..))
import Cardano.Ledger.Shelley.TxBody
  ( DCert (..),
    DelegCert (..),
    PoolCert (..),
    PoolMetadata (..),
    RewardAcnt (..),
    Wdrl (..),
  )
import Cardano.Ledger.Shelley.UTxO (makeWitnessVKey)
import Cardano.Ledger.TxIn (TxIn (..))
import Cardano.Ledger.Val (inject, (<+>))
import Cardano.Slotting.Slot (SlotNo (..))
import Control.State.Transition.Extended hiding (Assertion)
import qualified Data.ByteString as BS (replicate)
import Data.Default.Class (Default (..))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Sequence.Strict as StrictSeq
import Data.UMap (View (Rewards))
import qualified Data.UMap as UM
import GHC.Stack
import Numeric.Natural (Natural)
import qualified Plutus.V1.Ledger.Api as Plutus
import Test.Cardano.Ledger.Generic.Fields
  ( PParamsField (..),
    TxBodyField (..),
    TxField (..),
    TxOutField (..),
    WitnessesField (..),
  )
import Test.Cardano.Ledger.Generic.PrettyCore ()
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Generic.Scriptic (HasTokens (..), PostShelley, Scriptic (..), after, matchkey)
import Test.Cardano.Ledger.Generic.Updaters
import Test.Cardano.Ledger.Shelley.Utils
  ( RawSeed (..),
    mkKeyPair,
    mkVRFKeyPair,
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase)

import Test.Cardano.Ledger.Examples.TwoPhaseValidationLib
  ( datumExample1,
    initUTxO,
    redeemerExample1,
    someKeys,
    validatingBody,
    freeCostModelV1,
    mkGenesisTxIn,
    trustMeP,
    notValidatingTx,
  )


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

someOutput :: EraTxOut era => Proof era -> TxOut era
someOutput pf =
  newTxOut pf [Address $ someAddr pf, Amount (inject $ Coin 1000)]

nonScriptOutWithDatum :: forall era. EraTxOut era => Proof era -> TxOut era
nonScriptOutWithDatum pf =
  newTxOut
    pf
    [ Address (someAddr pf),
      Amount (inject $ Coin 1221),
      DHash' [hashData $ datumExample1 @era]
    ]

collateralOutput :: EraTxOut era => Proof era -> TxOut era
collateralOutput pf =
  newTxOut pf [Address $ someAddr pf, Amount (inject $ Coin 5)]

alwaysSucceedsHash ::
  forall era.
  Scriptic era =>
  Natural ->
  Proof era ->
  ScriptHash (Crypto era)
alwaysSucceedsHash n pf = hashScript @era $ always n pf

timelockScript :: PostShelley era => Int -> Proof era -> Script era
timelockScript s = allOf [matchkey 1, after (100 + s)]

timelockHash ::
  forall era.
  PostShelley era =>
  Int ->
  Proof era ->
  ScriptHash (Crypto era)
timelockHash n pf = hashScript @era $ timelockScript n pf

timelockAddr :: forall era. PostShelley era => Proof era -> Addr (Crypto era)
timelockAddr pf = Addr Testnet pCred sCred
  where
    (_ssk, svk) = mkKeyPair @(Crypto era) (RawSeed 0 0 0 0 2)
    pCred = ScriptHashObj (timelockHash 0 pf)
    sCred = StakeRefBase . KeyHashObj . hashKey $ svk

timelockOut :: (EraTxOut era, PostShelley era) => Proof era -> TxOut era
timelockOut pf =
  newTxOut pf [Address $ timelockAddr pf, Amount (inject $ Coin 1)]

-- | This output is unspendable since it is locked by a plutus script,
--  but has no datum hash.
unspendableOut :: forall era. (EraTxOut era, Scriptic era) => Proof era -> TxOut era
unspendableOut pf =
  newTxOut
    pf
    [ Address (scriptAddr (always 3 pf) pf),
      Amount (inject $ Coin 5000)
    ]

initialUtxoSt ::
  (Default (State (EraRule "PPUP" era)), EraTxOut era) =>
  UTxO era ->
  UTxOState era
initialUtxoSt utxo = smartUTxOState utxo (Coin 0) (Coin 0) def


pp :: Proof era -> PParams era
pp pf = newPParams pf defaultPPs


hashsize :: forall c. CC.Crypto c => Int
hashsize = fromIntegral $ sizeHash ([] @(CC.HASH c))

scriptStakeCredSuceed :: Scriptic era => Proof era -> StakeCredential (Crypto era)
scriptStakeCredSuceed pf = ScriptHashObj (alwaysSucceedsHash 2 pf)

poolMDHTooBigTxBody :: forall era. (EraTxBody era, Scriptic era) => Proof era -> TxBody era
poolMDHTooBigTxBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 3],
      Outputs' [newTxOut pf [Address $ someAddr pf, Amount (inject $ Coin 995)]],
      Certs' [DCertPool (RegPool poolParams)],
      Txfee (Coin 5)
    ]
  where
    tooManyBytes = BS.replicate (hashsize @(Crypto era) + 1) 0
    poolParams =
      PoolParams
        { _poolId = coerceKeyRole . hashKey . vKey $ someKeys pf,
          _poolVrf = hashVerKeyVRF . snd . mkVRFKeyPair $ RawSeed 0 0 0 0 0,
          _poolPledge = Coin 0,
          _poolCost = Coin 0,
          _poolMargin = minBound,
          _poolRAcnt = RewardAcnt Testnet (scriptStakeCredSuceed pf),
          _poolOwners = mempty,
          _poolRelays = mempty,
          _poolMD = SJust $ PoolMetadata (fromJust $ textToUrl "") tooManyBytes
        }

poolMDHTooBigTx ::
  forall era.
  ( Scriptic era,
    EraTxBody era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
poolMDHTooBigTx pf =
  -- Note that the UTXOW rule will no trigger the expected predicate failure,
  -- since it is checked in the POOL rule. BBODY will trigger it, however.
  newTx
    pf
    [ Body (poolMDHTooBigTxBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (poolMDHTooBigTxBody pf)) (someKeys pf)]
        ]
    ]

-- =======================
-- Alonzo BBODY Tests
-- =======================

bbodyEnv :: Proof era -> BbodyEnv era
bbodyEnv pf = BbodyEnv (pp pf) def

dpstate :: Scriptic era => Proof era -> DPState (Crypto era)
dpstate pf =
  def
    { dpsDState =
        def {_unified = UM.insert (scriptStakeCredSuceed pf) (Coin 1000) (Rewards UM.empty)}
    }

initialBBodyState ::
  ( Default (State (EraRule "PPUP" era)),
    EraTxOut era,
    PostShelley era
  ) =>
  Proof era ->
  UTxO era ->
  ShelleyBbodyState era
initialBBodyState pf utxo =
  BbodyState (LedgerState (initialUtxoSt utxo) (dpstate pf)) (BlocksMade mempty)

coldKeys :: CC.Crypto c => KeyPair 'BlockIssuer c
coldKeys = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (RawSeed 1 2 3 2 1)

makeNaiveBlock ::
  forall era. EraSegWits era => [Tx era] -> Block (BHeaderView (Crypto era)) era
makeNaiveBlock txs = UnsafeUnserialisedBlock bhView txs'
  where
    bhView =
      BHeaderView
        { bhviewID = hashKey (vKey coldKeys),
          bhviewBSize = fromIntegral $ bBodySize txs',
          bhviewHSize = 0,
          bhviewBHash = hashTxSeq @era txs',
          bhviewSlot = SlotNo 0
        }
    txs' = (toTxSeq @era) . StrictSeq.fromList $ txs


outEx1 :: EraTxOut era => Proof era -> TxOut era
outEx1 pf = newTxOut pf [Address (someAddr pf), Amount (inject $ Coin 4995)]

datumExample2 :: Era era => Data era
datumExample2 = Data (Plutus.I 0)


alwaysFailsOutput :: forall era. (Scriptic era, EraTxOut era) => Proof era -> TxOut era
alwaysFailsOutput pf =
  newTxOut
    pf
    [ Address (scriptAddr (never 0 pf) pf),
      Amount (inject $ Coin 3000),
      DHash' [hashData $ datumExample2 @era]
    ]

validatingRedeemersEx1 :: Era era => Redeemers era
validatingRedeemersEx1 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Spend 0) (redeemerExample1, ExUnits 5000 5000)

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


alwaysFailsHash :: forall era. Scriptic era => Natural -> Proof era -> ScriptHash (Crypto era)
alwaysFailsHash n pf = hashScript @era $ never n pf

scriptStakeCredFail :: Scriptic era => Proof era -> StakeCredential (Crypto era)
scriptStakeCredFail pf = ScriptHashObj (alwaysFailsHash 1 pf)


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

outEx3 :: EraTxOut era => Proof era -> TxOut era
outEx3 pf = newTxOut pf [Address (someAddr pf), Amount (inject $ Coin 995)]

redeemerExample3 :: Era era => Data era
redeemerExample3 = Data (Plutus.I 42)

validatingRedeemersEx3 :: Era era => Redeemers era
validatingRedeemersEx3 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Cert 0) (redeemerExample3, ExUnits 5000 5000)

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

outEx4 :: (Scriptic era, EraTxOut era) => Proof era -> TxOut era
outEx4 pf = newTxOut pf [Address (someAddr pf), Amount (inject $ Coin 995)]

redeemerExample4 :: Era era => Data era
redeemerExample4 = Data (Plutus.I 0)

notValidatingRedeemersEx4 :: Era era => Redeemers era
notValidatingRedeemersEx4 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Cert 0) (redeemerExample4, ExUnits 5000 5000)

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

alwaysSucceedsOutputV2 :: forall era. (EraTxOut era, Scriptic era) => Proof era -> TxOut era
alwaysSucceedsOutputV2 pf =
  newTxOut
    pf
    [ Address (scriptAddr (alwaysAlt 3 pf) pf),
      Amount (inject $ Coin 5000),
      DHash' [hashData $ datumExample1 @era]
    ]


testAlonzoBlock ::
  ( GoodCrypto (Crypto era),
    HasTokens era,
    Scriptic era,
    EraSegWits era,
    Value era ~ MaryValue (Crypto era)
  ) =>
  Proof era ->
  Block (BHeaderView (Crypto era)) era
testAlonzoBlock pf =
  makeNaiveBlock
    [ trustMeP pf True $ validatingTx pf,
      trustMeP pf False $ notValidatingTx pf,
      trustMeP pf True $ validatingTxWithWithdrawal pf,
      trustMeP pf False $ notValidatingTxWithWithdrawal pf,
      trustMeP pf True $ validatingTxWithCert pf,
      trustMeP pf False $ notValidatingTxWithCert pf,
      trustMeP pf True $ validatingTxWithMint pf,
      trustMeP pf False $ notValidatingTxWithMint pf
    ]

testAlonzoBadPMDHBlock :: GoodCrypto (Crypto era) => Proof era -> Block (BHeaderView (Crypto era)) era
testAlonzoBadPMDHBlock pf@(Alonzo _) = makeNaiveBlock [trustMeP pf True $ poolMDHTooBigTx pf]
testAlonzoBadPMDHBlock pf@(Babbage _) = makeNaiveBlock [trustMeP pf True $ poolMDHTooBigTx pf]
testAlonzoBadPMDHBlock pf@(Conway _) = makeNaiveBlock [trustMeP pf True $ poolMDHTooBigTx pf]
testAlonzoBadPMDHBlock other = error ("testAlonzoBadPMDHBlock does not work in era " ++ show other)


example1UTxO ::
  ( GoodCrypto (Crypto era),
    HasTokens era,
    PostShelley era,
    EraTxBody era,
    Value era ~ MaryValue (Crypto era)
  ) =>
  Proof era ->
  UTxO era
example1UTxO pf =
  UTxO $
    Map.fromList
      [ (TxIn (txid (validatingBody pf)) minBound, outEx1 pf),
        (TxIn (txid (validatingBodyWithCert pf)) minBound, outEx3 pf),
        (TxIn (txid (validatingBodyWithWithdrawal pf)) minBound, outEx5 pf),
        (TxIn (txid (validatingBodyWithMint pf)) minBound, outEx7 pf),
        (mkGenesisTxIn 11, collateralOutput pf),
        (mkGenesisTxIn 2, alwaysFailsOutput pf),
        (mkGenesisTxIn 13, collateralOutput pf),
        (mkGenesisTxIn 4, someOutput pf),
        (mkGenesisTxIn 15, collateralOutput pf),
        (mkGenesisTxIn 6, someOutput pf),
        (mkGenesisTxIn 17, collateralOutput pf),
        (mkGenesisTxIn 8, someOutput pf),
        (mkGenesisTxIn 100, timelockOut pf),
        (mkGenesisTxIn 101, unspendableOut pf),
        (mkGenesisTxIn 102, alwaysSucceedsOutputV2 pf),
        (mkGenesisTxIn 103, nonScriptOutWithDatum pf)
      ]

example1UtxoSt ::
  ( EraTxBody era,
    GoodCrypto (Crypto era),
    HasTokens era,
    PostShelley era,
    Default (State (EraRule "PPUP" era)),
    Value era ~ MaryValue (Crypto era)
  ) =>
  Proof era ->
  UTxOState era
example1UtxoSt proof = smartUTxOState (example1UTxO proof) (Coin 0) (Coin 40) def

example1BBodyState ::
  ( GoodCrypto (Crypto era),
    HasTokens era,
    PostShelley era,
    Default (State (EraRule "PPUP" era)),
    EraTxBody era,
    Value era ~ MaryValue (Crypto era)
  ) =>
  Proof era ->
  ShelleyBbodyState era
example1BBodyState proof =
  BbodyState (LedgerState (example1UtxoSt proof) def) (BlocksMade $ Map.singleton poolID 1)
  where
    poolID = hashKey . vKey . coerceKeyRole $ coldKeys


-- =====================================================================================
-- Proof parameterized TestTrees

-- | A small example of what a continuation for 'runSTS' might look like
genericCont ::
  ( Eq x,
    PrettyA x,
    Eq y,
    PrettyA y,
    HasCallStack
  ) =>
  String ->
  Either [x] y ->
  Either [x] y ->
  Assertion
genericCont cause expected computed =
  case (computed, expected) of
    (Left c, Left e)
      | c /= e -> assertFailure $ causedBy ++ expectedToFail e ++ failedWith c
    (Right c, Right e)
      | c /= e -> assertFailure $ causedBy ++ expectedToPass e ++ passedWith c
    (Left x, Right y) ->
      assertFailure $ causedBy ++ expectedToPass y ++ failedWith x
    (Right x, Left y) ->
      assertFailure $ causedBy ++ expectedToFail y ++ passedWith x
    _ -> pure ()
  where
    causedBy
      | null cause = ""
      | otherwise = "Caused by:\n" ++ cause ++ "\n"
    expectedToPass y = "Expected to pass with:\n" ++ show (prettyA y) ++ "\n"
    expectedToFail y = "Expected to fail with:\n" ++ show (ppList prettyA y) ++ "\n"
    failedWith x = "But failed with:\n" ++ show (ppList prettyA x)
    passedWith x = "But passed with:\n" ++ show (prettyA x)


-- ========================================
-- This implements a special rule to test that for ValidationTagMismatch. Rather than comparing the insides of
-- ValidationTagMismatch (which are complicated and depend on Plutus) we just note that both the computed
-- and expected are ValidationTagMismatch. Of course the 'path' to ValidationTagMismatch differs by Era.
-- so we need to case over the Era proof, to get the path correctly.

-- ================================================================================================
testBBODY ::
  (GoodCrypto (Crypto era), HasCallStack) =>
  WitRule "BBODY" era ->
  ShelleyBbodyState era ->
  Block (BHeaderView (Crypto era)) era ->
  Either [PredicateFailure (AlonzoBBODY era)] (ShelleyBbodyState era) ->
  Assertion
testBBODY wit@(BBODY proof) initialSt block expected =
  let env = bbodyEnv proof
   in case proof of
        Alonzo _ -> runSTS wit (TRC (env, initialSt, block)) (genericCont "" expected)
        Babbage _ -> runSTS wit (TRC (env, initialSt, block)) (genericCont "" expected)
        Conway _ -> runSTS wit (TRC (env, initialSt, block)) (genericCont "" expected)
        other -> error ("We cannot testBBODY in era " ++ show other)

alonzoBBODYexamplesP ::
  forall era.
  ( GoodCrypto (Crypto era),
    HasTokens era,
    Default (State (EraRule "PPUP" era)),
    PostShelley era,
    Value era ~ MaryValue (Crypto era),
    EraSegWits era
  ) =>
  Proof era ->
  TestTree
alonzoBBODYexamplesP proof =
  testGroup
    (show proof ++ " BBODY examples")
    [ testCase "eight plutus scripts cases" $
        testBBODY
          (BBODY proof)
          (initialBBodyState proof (initUTxO proof))
          (testAlonzoBlock proof)
          (Right (example1BBodyState proof)),
      testCase "block with bad pool md hash in tx" $
        testBBODY
          (BBODY proof)
          (initialBBodyState proof (initUTxO proof))
          (testAlonzoBadPMDHBlock proof)
          (Left [makeTooBig proof])
    ]

makeTooBig :: Proof era -> AlonzoBbodyPredFailure era
makeTooBig proof@(Alonzo _) =
  ShelleyInAlonzoBbodyPredFailure . LedgersFailure . LedgerFailure . DelegsFailure . DelplFailure . PoolFailure $
    PoolMedataHashTooBig (coerceKeyRole . hashKey . vKey $ someKeys proof) (hashsize @Mock + 1)
makeTooBig proof@(Babbage _) =
  ShelleyInAlonzoBbodyPredFailure . LedgersFailure . LedgerFailure . DelegsFailure . DelplFailure . PoolFailure $
    PoolMedataHashTooBig (coerceKeyRole . hashKey . vKey $ someKeys proof) (hashsize @Mock + 1)
makeTooBig proof@(Conway _) =
  ShelleyInAlonzoBbodyPredFailure . LedgersFailure . LedgerFailure . DelegsFailure . DelplFailure . PoolFailure $
    PoolMedataHashTooBig (coerceKeyRole . hashKey . vKey $ someKeys proof) (hashsize @Mock + 1)
makeTooBig proof = error ("makeTooBig does not work in era " ++ show proof)

-- ==============================================================================

alonzoBBODYExamples :: TestTree
alonzoBBODYExamples =
  testGroup
    "Generic Tests, testing Alonzo PredicateFailures, in postAlonzo eras."
    [ alonzoBBODYexamplesP (Alonzo Mock),
      alonzoBBODYexamplesP (Babbage Mock),
      alonzoBBODYexamplesP (Conway Mock)
    ]
