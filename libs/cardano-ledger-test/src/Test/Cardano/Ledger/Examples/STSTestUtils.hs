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

module Test.Cardano.Ledger.Examples.STSTestUtils
  ( AlonzoBased (..),
    freeCostModelV1,
    freeCostModelV2,
    initUTxO,
    mkGenesisTxIn,
    mkTxDats,
    someAddr,
    someKeys,
    someScriptAddr,
    testBBODY,
    testUTXOW,
    trustMeP,
    datumExample1,
    redeemerExample1,
    testSystemStart,
    validatingBody,
    keyBy,
    notValidatingTx,
  )
where

import qualified Cardano.Crypto.Hash as CH
import Cardano.Ledger.Address (Addr (..))
import Cardano.Ledger.Alonzo.Data (Data (..), hashData)
import Cardano.Ledger.Alonzo.Language (Language (..))
import Cardano.Ledger.Alonzo.PParams (AlonzoPParamsHKD (..))
import Cardano.Ledger.Alonzo.Rules
  ( AlonzoBBODY,
    AlonzoUtxoPredFailure (..),
    AlonzoUtxosPredFailure (..),
    AlonzoUtxowPredFailure (..),
  )
import Cardano.Ledger.Alonzo.Scripts
  ( CostModel,
    CostModels (..),
    ExUnits (..),
    mkCostModel,
  )
import qualified Cardano.Ledger.Alonzo.Scripts as Tag (Tag (..))
import Cardano.Ledger.Alonzo.Tx
  ( AlonzoTx (..),
    IsValid (..),
  )
import Cardano.Ledger.Alonzo.TxWitness (RdmrPtr (..), Redeemers (..), TxDats (..))
import Cardano.Ledger.BHeaderView (BHeaderView (..))
import qualified Cardano.Ledger.Babbage.PParams as Babbage (BabbagePParamsHKD (..))
import Cardano.Ledger.Babbage.Rules (BabbageUtxoPredFailure (..))
import Cardano.Ledger.Babbage.Rules as Babbage (BabbageUtxowPredFailure (..))
import Cardano.Ledger.BaseTypes
  ( Network (..),
    mkTxIxPartial,
  )
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Core hiding (TranslationError)
import Cardano.Ledger.Credential
  ( Credential (..),
    StakeReference (..),
  )
import qualified Cardano.Ledger.Crypto as CC
import Cardano.Ledger.Keys
  ( GenDelegs (..),
    KeyPair (..),
    KeyRole (..),
    hashKey,
  )
import Cardano.Ledger.Pretty
import Cardano.Ledger.Pretty.Babbage ()
import Cardano.Ledger.SafeHash (hashAnnotated)
import Cardano.Ledger.Shelley.API
  ( Block (..),
    ProtVer (..),
    UTxO (..),
  )
import Cardano.Ledger.Shelley.LedgerState
  ( UTxOState (..),
    smartUTxOState,
  )
import Cardano.Ledger.Shelley.PParams (ShelleyPParamsHKD (..))
import Cardano.Ledger.Shelley.Rules.Bbody (BbodyEnv (..), ShelleyBbodyState)
import Cardano.Ledger.Shelley.Rules.Utxo (UtxoEnv (..))
import Cardano.Ledger.Shelley.Rules.Utxow as Shelley (ShelleyUtxowPredFailure (..))
import Cardano.Ledger.Shelley.UTxO (makeWitnessVKey)
import Cardano.Ledger.TxIn (TxIn (..))
import Cardano.Ledger.Val (inject)
import Cardano.Slotting.Slot (SlotNo (..))
import Cardano.Slotting.Time (SystemStart (..))
import Control.State.Transition.Extended hiding (Assertion)
import Data.Default.Class (Default (..))
import Data.Either (fromRight)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Time.Clock.POSIX (posixSecondsToUTCTime)
import GHC.Stack
import qualified Plutus.V1.Ledger.Api as Plutus
import Plutus.V1.Ledger.EvaluationContext (costModelParamsForTesting)
import Test.Cardano.Ledger.Generic.Fields
  ( PParamsField (..),
    TxBodyField (..),
    TxField (..),
    TxOutField (..),
    WitnessesField (..),
  )
import Test.Cardano.Ledger.Generic.PrettyCore ()
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Generic.Scriptic (PostShelley, Scriptic (..), after, matchkey)
import Test.Cardano.Ledger.Generic.Updaters
import Test.Cardano.Ledger.Shelley.Generator.EraGen (genesisId)
import Test.Cardano.Ledger.Shelley.Utils
  ( RawSeed (..),
    mkKeyPair,
  )
import Test.Tasty.HUnit (Assertion, assertFailure)

-- =======================
-- Setup the initial state
-- =======================

testSystemStart :: SystemStart
testSystemStart = SystemStart $ posixSecondsToUTCTime 0

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

mkGenesisTxIn :: (CH.HashAlgorithm (CC.HASH crypto), HasCallStack) => Integer -> TxIn crypto
mkGenesisTxIn = TxIn genesisId . mkTxIxPartial

collateralOutput :: EraTxOut era => Proof era -> TxOut era
collateralOutput pf =
  newTxOut pf [Address $ someAddr pf, Amount (inject $ Coin 5)]

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
    [ Address (someScriptAddr (always 3 pf) pf),
      Amount (inject $ Coin 5000)
    ]

initUTxO :: (EraTxOut era, PostShelley era) => Proof era -> UTxO era
initUTxO pf =
  UTxO $
    Map.fromList $
      [ (mkGenesisTxIn 1, alwaysSucceedsOutput pf),
        (mkGenesisTxIn 2, alwaysFailsOutput pf)
      ]
        ++ map (\i -> (mkGenesisTxIn i, someOutput pf)) [3 .. 8]
        ++ map (\i -> (mkGenesisTxIn i, collateralOutput pf)) [11 .. 18]
        ++ [ (mkGenesisTxIn 100, timelockOut pf),
             (mkGenesisTxIn 101, unspendableOut pf),
             (mkGenesisTxIn 102, alwaysSucceedsOutputV2 pf),
             (mkGenesisTxIn 103, nonScriptOutWithDatum pf)
           ]

initialUtxoSt ::
  (Default (State (EraRule "PPUP" era)), EraTxOut era) =>
  UTxO era ->
  UTxOState era
initialUtxoSt utxo = smartUTxOState utxo (Coin 0) (Coin 0) def

keyBy :: Ord k => (a -> k) -> [a] -> Map k a
keyBy f xs = Map.fromList $ (\x -> (f x, x)) <$> xs

pp :: Proof era -> PParams era
pp pf = newPParams pf defaultPPs

-- =========================================================================
--  Example 1: Process a SPEND transaction with a succeeding Plutus script.
-- =========================================================================

datumExample1 :: Era era => Data era
datumExample1 = Data (Plutus.I 123)

redeemerExample1 :: Era era => Data era
redeemerExample1 = Data (Plutus.I 42)

txDatsExample1 :: Era era => TxDats era
txDatsExample1 = TxDats $ keyBy hashData [datumExample1]

alwaysSucceedsOutput :: forall era. (EraTxOut era, Scriptic era) => Proof era -> TxOut era
alwaysSucceedsOutput pf =
  newTxOut
    pf
    [ Address (someScriptAddr (always 3 pf) pf),
      Amount (inject $ Coin 5000),
      DHash' [hashData $ datumExample1 @era]
    ]

alwaysSucceedsOutputV2 :: forall era. (EraTxOut era, Scriptic era) => Proof era -> TxOut era
alwaysSucceedsOutputV2 pf =
  newTxOut
    pf
    [ Address (someScriptAddr (alwaysAlt 3 pf) pf),
      Amount (inject $ Coin 5000),
      DHash' [hashData $ datumExample1 @era]
    ]

validatingRedeemersEx1 :: Era era => Redeemers era
validatingRedeemersEx1 =
  Redeemers $
    Map.singleton (RdmrPtr Tag.Spend 0) (redeemerExample1, ExUnits 5000 5000)

outEx1 :: EraTxOut era => Proof era -> TxOut era
outEx1 pf = newTxOut pf [Address (someAddr pf), Amount (inject $ Coin 4995)]

validatingBody :: (Scriptic era, EraTxBody era) => Proof era -> TxBody era
validatingBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 1],
      Collateral' [mkGenesisTxIn 11],
      Outputs' [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] validatingRedeemersEx1 txDatsExample1)
    ]

-- ======================================================================
--  Example 2: Process a SPEND transaction with a failing Plutus script.
-- ======================================================================

datumExample2 :: Era era => Data era
datumExample2 = Data (Plutus.I 0)

redeemerExample2 :: Era era => Data era
redeemerExample2 = Data (Plutus.I 1)

txDatsExample2 :: Era era => TxDats era
txDatsExample2 = TxDats $ keyBy hashData $ [datumExample2]

notValidatingRedeemers :: Era era => Redeemers era
notValidatingRedeemers =
  Redeemers
    ( Map.fromList
        [ ( RdmrPtr Tag.Spend 0,
            (redeemerExample2, ExUnits 5000 5000)
          )
        ]
    )

alwaysFailsOutput :: forall era. (Scriptic era, EraTxOut era) => Proof era -> TxOut era
alwaysFailsOutput pf =
  newTxOut
    pf
    [ Address (someScriptAddr (never 0 pf) pf),
      Amount (inject $ Coin 3000),
      DHash' [hashData $ datumExample2 @era]
    ]

outEx2 :: (Scriptic era, EraTxOut era) => Proof era -> TxOut era
outEx2 pf = newTxOut pf [Address (someAddr pf), Amount (inject $ Coin 2995)]

notValidatingBody :: (Scriptic era, EraTxBody era) => Proof era -> TxBody era
notValidatingBody pf =
  newTxBody
    pf
    [ Inputs' [mkGenesisTxIn 2],
      Collateral' [mkGenesisTxIn 12],
      Outputs' [outEx2 pf],
      Txfee (Coin 5),
      WppHash (newScriptIntegrityHash pf (pp pf) [PlutusV1] notValidatingRedeemers txDatsExample2)
    ]

notValidatingTx ::
  ( Scriptic era,
    EraTx era,
    GoodCrypto (Crypto era)
  ) =>
  Proof era ->
  Tx era
notValidatingTx pf =
  newTx
    pf
    [ Body (notValidatingBody pf),
      WitnessesI
        [ AddrWits' [makeWitnessVKey (hashAnnotated (notValidatingBody pf)) (someKeys pf)],
          ScriptWits' [never 0 pf],
          DataWits' [datumExample2],
          RdmrWits notValidatingRedeemers
        ]
    ]

trustMeP :: Proof era -> Bool -> Tx era -> Tx era
trustMeP (Alonzo _) iv' (AlonzoTx b w _ m) = AlonzoTx b w (IsValid iv') m
trustMeP (Babbage _) iv' (AlonzoTx b w _ m) = AlonzoTx b w (IsValid iv') m
trustMeP (Conway _) iv' (AlonzoTx b w _ m) = AlonzoTx b w (IsValid iv') m
trustMeP _ _ tx = tx

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

-- ==============================================================================
-- Three slighty different ways to make an Assertion, but all with the same type

testUTXOW ::
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

-- | Use an equality test on the expected and computed [PredicateFailure]
testUTXOW wit@(UTXOW (Alonzo _)) utxo p tx = testUTXOWwith wit (genericCont (show tx)) utxo p tx
testUTXOW wit@(UTXOW (Babbage _)) utxo p tx = testUTXOWwith wit (genericCont (show tx)) utxo p tx
testUTXOW wit@(UTXOW (Conway _)) utxo p tx = testUTXOWwith wit (genericCont (show tx)) utxo p tx
testUTXOW (UTXOW other) _ _ _ = error ("Cannot use testUTXOW in era " ++ show other)

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
  PParams era ->
  Assertion
testBBODY wit@(BBODY proof) initialSt block expected pparams =
  let env = BbodyEnv pparams def
   in case proof of
        Alonzo _ -> runSTS wit (TRC (env, initialSt, block)) (genericCont "" expected)
        Babbage _ -> runSTS wit (TRC (env, initialSt, block)) (genericCont "" expected)
        Conway _ -> runSTS wit (TRC (env, initialSt, block)) (genericCont "" expected)
        other -> error ("We cannot testBBODY in era " ++ show other)

-- =====================================

-- | We use this to write set of tests that raise AlonzoBased PredicateFailures.
--   The type we use is for '(fail ~ PredicateFailure (EraRule "UTXOW" era))' .
--   There are 4 types of AlonzoBased PredicateFailures: 'UtxowPredFail',
--   'UtxosPredicateFailure',  'UtxoPredicateFailure', and  'UtxowPredicateFailure' .
--   The idea is to make tests that only raise these failures, in Alonzo and future Eras.
class AlonzoBased era failure where
  fromUtxos :: AlonzoUtxosPredFailure era -> failure
  fromUtxo :: AlonzoUtxoPredFailure era -> failure
  fromUtxow :: ShelleyUtxowPredFailure era -> failure
  fromPredFail :: AlonzoUtxowPredFailure era -> failure

instance AlonzoBased (AlonzoEra c) (AlonzoUtxowPredFailure (AlonzoEra c)) where
  fromUtxos = ShelleyInAlonzoUtxowPredFailure . Shelley.UtxoFailure . UtxosFailure
  fromUtxo = ShelleyInAlonzoUtxowPredFailure . Shelley.UtxoFailure
  fromUtxow = ShelleyInAlonzoUtxowPredFailure
  fromPredFail = id

instance AlonzoBased (BabbageEra c) (BabbageUtxowPredFailure (BabbageEra c)) where
  fromUtxos = Babbage.UtxoFailure . AlonzoInBabbageUtxoPredFailure . UtxosFailure
  fromUtxo = Babbage.UtxoFailure . AlonzoInBabbageUtxoPredFailure
  fromUtxow = AlonzoInBabbageUtxowPredFailure . ShelleyInAlonzoUtxowPredFailure
  fromPredFail = AlonzoInBabbageUtxowPredFailure

instance AlonzoBased (ConwayEra c) (BabbageUtxowPredFailure (ConwayEra c)) where
  fromUtxos = Babbage.UtxoFailure . AlonzoInBabbageUtxoPredFailure . UtxosFailure
  fromUtxo = Babbage.UtxoFailure . AlonzoInBabbageUtxoPredFailure
  fromUtxow = AlonzoInBabbageUtxowPredFailure . ShelleyInAlonzoUtxowPredFailure
  fromPredFail = AlonzoInBabbageUtxowPredFailure

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------

-- | A cost model that sets everything as being free
freeCostModelV1 :: CostModel
freeCostModelV1 =
  fromRight (error "corrupt freeCostModelV1") $
    mkCostModel PlutusV1 (0 <$ costModelParamsForTesting)

-- | A cost model that sets everything as being free
freeCostModelV2 :: CostModel
freeCostModelV2 =
  fromRight (error "corrupt freeCostModelV1") $
    mkCostModel PlutusV1 (0 <$ costModelParamsForTesting) -- TODO use PV2 when it exists

mkTxDats :: Era era => Data era -> TxDats era
mkTxDats d = TxDats $ keyBy hashData [d]

someKeys :: forall era. Era era => Proof era -> KeyPair 'Payment (Crypto era)
someKeys _pf = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair @(Crypto era) (RawSeed 1 1 1 1 1)

someAddr :: forall era. Era era => Proof era -> Addr (Crypto era)
someAddr pf = Addr Testnet pCred sCred
  where
    (_ssk, svk) = mkKeyPair @(Crypto era) (RawSeed 0 0 0 0 2)
    pCred = KeyHashObj . hashKey . vKey $ someKeys pf
    sCred = StakeRefBase . KeyHashObj . hashKey $ svk

-- | Create an address with a given payment script.
-- The proof here is used only as a Proxy.
someScriptAddr :: forall era. (Scriptic era) => Script era -> Proof era -> Addr (Crypto era)
someScriptAddr s _pf = Addr Testnet pCred sCred
  where
    pCred = ScriptHashObj . hashScript @era $ s
    (_ssk, svk) = mkKeyPair @(Crypto era) (RawSeed 0 0 0 0 0)
    sCred = StakeRefBase . KeyHashObj . hashKey $ svk
