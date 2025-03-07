{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The stake distribution, aggregated by stake pool (as opposed to stake credential),
-- plays a primary role in Cardano's proof of stake network.
-- Together with the VRF checks, the stake distribution determines leader election.
-- The leader election is the precisely the part of the ledger that is
-- determined by Ouroboros (Praos and Genesis), our consensus mechanism.
-- See Section 16, "Leader Value Calculation", of the
-- <https://github.com/input-output-hk/cardano-ledger/releases/latest/download/shelley-ledger.pdf formal specification>.
module Cardano.Ledger.PoolDistr (
  IndividualPoolStake (..),
  PoolDistr (..),
)
where

import Cardano.Ledger.Binary (DecCBOR (..), EncCBOR (..), decodeRecordNamed, encodeListLen)
import Cardano.Ledger.Crypto
import Cardano.Ledger.Keys (Hash, KeyHash, KeyRole (..), VerKeyVRF)
import Cardano.Ledger.TreeDiff (ToExpr)
import Control.DeepSeq (NFData)
import Control.SetAlgebra (BaseRep (MapR), Embed (..), Exp (Base), HasExp (..))
import Data.Aeson (KeyValue, ToJSON (..), object, pairs, (.=))
import Data.Map.Strict (Map)
import GHC.Generics (Generic)
import NoThunks.Class (NoThunks (..))

-- | The 'IndividualPoolStake' contains all the stake controlled
-- by a single stake pool (the combination of owners and delegates)
-- for a given epoch, and also the hash of the stake pool's
-- registered VRF key.
--
-- When a stake pool produces a block, the header contains the
-- full VRF verification key and VRF value for leader election.
-- We check the VRF key against the value in 'IndividualPoolStake'
-- and we check the VRF value using the epoch nonce and
-- the relative stake of the pool as given in 'IndividualPoolStake'.
-- The stake is relative to the total amount of active stake
-- in the network. Stake is active if it is both registered and
-- delegated to a registered stake pool.
data IndividualPoolStake c = IndividualPoolStake
  { individualPoolStake :: !Rational
  , individualPoolStakeVrf :: !(Hash c (VerKeyVRF c))
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (NFData, NoThunks)

instance Crypto c => EncCBOR (IndividualPoolStake c) where
  encCBOR (IndividualPoolStake stake vrf) =
    mconcat
      [ encodeListLen 2
      , encCBOR stake
      , encCBOR vrf
      ]

instance Crypto c => DecCBOR (IndividualPoolStake c) where
  decCBOR =
    decodeRecordNamed "IndividualPoolStake" (const 2) $
      IndividualPoolStake
        <$> decCBOR
        <*> decCBOR

instance Crypto c => ToJSON (IndividualPoolStake c) where
  toJSON = object . toIndividualPoolStakePair
  toEncoding = pairs . mconcat . toIndividualPoolStakePair

toIndividualPoolStakePair :: (KeyValue a, Crypto c) => IndividualPoolStake c -> [a]
toIndividualPoolStakePair indivPoolStake@(IndividualPoolStake _ _) =
  let IndividualPoolStake {..} = indivPoolStake
   in [ "individualPoolStake" .= individualPoolStake
      , "individualPoolStakeVrf" .= individualPoolStakeVrf
      ]

-- | A map of stake pool IDs (the hash of the stake pool operator's
-- verification key) to 'IndividualPoolStake'.
newtype PoolDistr c = PoolDistr
  { unPoolDistr :: Map (KeyHash 'StakePool c) (IndividualPoolStake c)
  }
  deriving stock (Show, Eq, Generic)
  deriving newtype (EncCBOR, DecCBOR, NFData, NoThunks, ToJSON)

-- ===============================

instance
  HasExp
    (PoolDistr c)
    ( Map
        (KeyHash 'StakePool c)
        (IndividualPoolStake c)
    )
  where
  toExp (PoolDistr x) = Base MapR x

-- | We can Embed a Newtype around a Map (or other Iterable type) and then use it in a set expression.
instance
  Embed
    (PoolDistr c)
    ( Map
        (KeyHash 'StakePool c)
        (IndividualPoolStake c)
    )
  where
  toBase (PoolDistr x) = x
  fromBase = PoolDistr

-- =======================================

instance ToExpr (PoolDistr c)

instance ToExpr (IndividualPoolStake c)
