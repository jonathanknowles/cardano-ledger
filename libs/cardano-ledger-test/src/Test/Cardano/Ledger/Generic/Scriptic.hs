{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Cardano.Ledger.Generic.Scriptic where

import Cardano.Ledger.Allegra.Scripts (Timelock (..))
import Cardano.Ledger.Alonzo.Language (Language (..))
import Cardano.Ledger.Alonzo.Scripts (AlonzoScript (..))
import Cardano.Ledger.Core
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Keys (KeyHash, KeyRole (..))
import Cardano.Ledger.Mary.Value (AssetName (..), MultiAsset (..), PolicyID (..))
import qualified Cardano.Ledger.Shelley.Scripts as Multi
import Cardano.Slotting.Slot (SlotNo (..))
import qualified Data.Map.Strict as Map
import qualified Data.Sequence.Strict as Seq (fromList)
import Numeric.Natural (Natural)
import Test.Cardano.Ledger.Alonzo.Arbitrary (alwaysFails, alwaysSucceeds)
import Test.Cardano.Ledger.Generic.Indexed (theKeyHash)
import Test.Cardano.Ledger.Generic.Proof

-- =============================================
-- Making era parameterized Scripts

theSlot :: Int -> SlotNo
theSlot n = SlotNo (fromIntegral n)

class (EraScript era, Show (Script era)) => Scriptic era where
  always :: Natural -> Proof era -> Script era
  alwaysAlt :: Natural -> Proof era -> Script era
  never :: Natural -> Proof era -> Script era
  require :: KeyHash 'Witness (EraCrypto era) -> Proof era -> Script era
  allOf :: [Proof era -> Script era] -> Proof era -> Script era
  anyOf :: [Proof era -> Script era] -> Proof era -> Script era
  mOf :: Int -> [Proof era -> Script era] -> Proof era -> Script era

class Scriptic era => PostShelley era where
  before :: Int -> Proof era -> Script era
  after :: Int -> Proof era -> Script era

class HasTokens era where
  forge :: Integer -> Script era -> MultiAsset (EraCrypto era)

instance CC.Crypto c => Scriptic (ShelleyEra c) where
  never _ (Shelley _) = Multi.RequireAnyOf mempty -- always False
  always _ (Shelley _) = Multi.RequireAllOf mempty -- always True
  alwaysAlt _ (Shelley _) = Multi.RequireAllOf mempty -- always True
  require key (Shelley _) = Multi.RequireSignature key
  allOf xs (Shelley c) = Multi.RequireAllOf (map ($ Shelley c) xs)
  anyOf xs (Shelley c) = Multi.RequireAnyOf (map ($ Shelley c) xs)
  mOf n xs (Shelley c) = Multi.RequireMOf n (map ($ Shelley c) xs)

-- Make Scripts in AllegraEra

instance CC.Crypto c => Scriptic (AllegraEra c) where
  never _ (Allegra _) = RequireAnyOf mempty -- always False
  always _ (Allegra _) = RequireAllOf mempty -- always True
  alwaysAlt _ (Allegra _) = RequireAllOf mempty -- always True
  require key (Allegra _) = RequireSignature key
  allOf xs (Allegra c) = RequireAllOf (Seq.fromList (map ($ Allegra c) xs))
  anyOf xs (Allegra c) = RequireAnyOf (Seq.fromList (map ($ Allegra c) xs))
  mOf n xs (Allegra c) = RequireMOf n (Seq.fromList (map ($ Allegra c) xs))

instance CC.Crypto c => PostShelley (AllegraEra c) where
  before n (Allegra _) = RequireTimeStart (theSlot n)
  after n (Allegra _) = RequireTimeExpire (theSlot n)

-- Make Scripts in Mary era

instance CC.Crypto c => Scriptic (MaryEra c) where
  never _ (Mary _) = RequireAnyOf mempty -- always False
  always _ (Mary _) = RequireAllOf mempty -- always True
  alwaysAlt _ (Mary _) = RequireAllOf mempty -- always True
  require key (Mary _) = RequireSignature key
  allOf xs (Mary c) = RequireAllOf (Seq.fromList (map ($ Mary c) xs))
  anyOf xs (Mary c) = RequireAnyOf (Seq.fromList (map ($ Mary c) xs))
  mOf n xs (Mary c) = RequireMOf n (Seq.fromList (map ($ Mary c) xs))

instance CC.Crypto c => PostShelley (MaryEra c) where
  before n (Mary _) = RequireTimeStart (theSlot n)
  after n (Mary _) = RequireTimeExpire (theSlot n)

instance forall c. CC.Crypto c => HasTokens (MaryEra c) where
  forge n s = MultiAsset $ Map.singleton pid (Map.singleton an n)
    where
      pid = PolicyID (hashScript @(MaryEra c) s)
      an = AssetName "an"

instance forall c. CC.Crypto c => HasTokens (AlonzoEra c) where
  forge n s = MultiAsset $ Map.singleton pid (Map.singleton an n)
    where
      pid = PolicyID (hashScript @(AlonzoEra c) s)
      an = AssetName "an"

instance forall c. CC.Crypto c => HasTokens (BabbageEra c) where
  forge n s = MultiAsset $ Map.singleton pid (Map.singleton an n)
    where
      pid = PolicyID (hashScript @(BabbageEra c) s)
      an = AssetName "an"

instance forall c. CC.Crypto c => HasTokens (ConwayEra c) where
  forge n s = MultiAsset $ Map.singleton pid (Map.singleton an n)
    where
      pid = PolicyID (hashScript @(ConwayEra c) s)
      an = AssetName "an"

-- =================================
-- Make Scripts in Alonzo era

-- | Not every Alonzo Script can be used in a Timelock context.
unTime :: Era era => Proof era -> (Proof era -> AlonzoScript era) -> Timelock era
unTime wit f = case f wit of
  (TimelockScript x) -> x
  (PlutusScript _ "\SOH\NUL\NUL \ACK\SOH") -> RequireAnyOf mempty
  (PlutusScript _ "\SOH\NUL\NUL \STX\NUL\NUL\DC1") -> RequireAllOf mempty
  (PlutusScript _ _) -> error "Plutus script in Timelock context"

instance CC.Crypto c => Scriptic (AlonzoEra c) where
  never n (Alonzo _) = alwaysFails PlutusV1 n -- always False
  always n (Alonzo _) = alwaysSucceeds PlutusV1 n -- always True
  alwaysAlt n (Alonzo _) = alwaysSucceeds PlutusV2 n -- always True
  require key (Alonzo _) = TimelockScript (RequireSignature key)
  allOf xs (Alonzo c) = TimelockScript (RequireAllOf (Seq.fromList (map (unTime (Alonzo c)) xs)))
  anyOf xs (Alonzo c) = TimelockScript (RequireAnyOf (Seq.fromList (map (unTime (Alonzo c)) xs)))
  mOf n xs (Alonzo c) = TimelockScript (RequireMOf n (Seq.fromList (map (unTime (Alonzo c)) xs)))

instance CC.Crypto c => PostShelley (AlonzoEra c) where
  before n (Alonzo _) = TimelockScript $ RequireTimeStart (theSlot n)
  after n (Alonzo _) = TimelockScript $ RequireTimeExpire (theSlot n)

-- =================================

instance CC.Crypto c => Scriptic (BabbageEra c) where
  never n (Babbage _) = alwaysFails PlutusV1 n -- always False
  always n (Babbage _) = alwaysSucceeds PlutusV1 n -- always True
  alwaysAlt n (Babbage _) = alwaysSucceeds PlutusV2 n -- always True
  require key (Babbage _) = TimelockScript (RequireSignature key)
  allOf xs (Babbage c) = TimelockScript (RequireAllOf (Seq.fromList (map (unTime (Babbage c)) xs)))
  anyOf xs (Babbage c) = TimelockScript (RequireAnyOf (Seq.fromList (map (unTime (Babbage c)) xs)))
  mOf n xs (Babbage c) = TimelockScript (RequireMOf n (Seq.fromList (map (unTime (Babbage c)) xs)))

instance CC.Crypto c => PostShelley (BabbageEra c) where
  before n (Babbage _) = TimelockScript $ RequireTimeStart (theSlot n)
  after n (Babbage _) = TimelockScript $ RequireTimeExpire (theSlot n)

-- =================================

instance CC.Crypto c => Scriptic (ConwayEra c) where
  never n (Conway _) = alwaysFails PlutusV1 n -- always False
  always n (Conway _) = alwaysSucceeds PlutusV1 n -- always True
  alwaysAlt n (Conway _) = alwaysSucceeds PlutusV2 n -- always True
  require key (Conway _) = TimelockScript (RequireSignature key)
  allOf xs (Conway c) = TimelockScript (RequireAllOf (Seq.fromList (map (unTime (Conway c)) xs)))
  anyOf xs (Conway c) = TimelockScript (RequireAnyOf (Seq.fromList (map (unTime (Conway c)) xs)))
  mOf n xs (Conway c) = TimelockScript (RequireMOf n (Seq.fromList (map (unTime (Conway c)) xs)))

instance CC.Crypto c => PostShelley (ConwayEra c) where
  before n (Conway _) = TimelockScript $ RequireTimeStart (theSlot n)
  after n (Conway _) = TimelockScript $ RequireTimeExpire (theSlot n)

-- =======================================
-- Some examples that work in multiple Eras
matchkey :: Scriptic era => Int -> Proof era -> Script era
matchkey n era = require (theKeyHash n) era

test21 :: Scriptic era => Proof era -> Script era
test21 wit = allOf [always 1, matchkey 1, anyOf [matchkey 2, matchkey 3]] wit

test22 :: PostShelley era => Proof era -> Script era
test22 wit = mOf 2 [matchkey 1, before 100, anyOf [matchkey 2, matchkey 3]] wit
