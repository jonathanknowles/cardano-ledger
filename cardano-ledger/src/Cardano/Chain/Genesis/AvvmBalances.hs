{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE UndecidableInstances       #-}

module Cardano.Chain.Genesis.AvvmBalances
  ( GenesisAvvmBalances(..)
  )
where

import Cardano.Prelude hiding (toStrict)
import Prelude (id)

import Data.Map.Strict as Map
import Text.JSON.Canonical (FromJSON(..), ToJSON(..))

import Cardano.Chain.Common (Lovelace)
import Cardano.Crypto.Signing.Redeem (RedeemVerificationKey)


-- | Predefined balances of AVVM (Ada Voucher Vending Machine) entries.
-- People who purchased Ada at a pre-sale were issued a certificate during
-- the pre-sale period. These certificates allow customers to redeem ADA.
newtype GenesisAvvmBalances = GenesisAvvmBalances
  { unGenesisAvvmBalances :: Map RedeemVerificationKey Lovelace
  } deriving (Show, Eq, Semigroup)

instance Monad m => ToJSON m GenesisAvvmBalances where
    toJSON = toJSON . unGenesisAvvmBalances

instance MonadError SchemaError m => FromJSON m GenesisAvvmBalances where
    -- | Unfortunately, because @canonical-json@ doesn't utilize operations from
    -- "Data.Map.Strict" but only those from "Data.Map.Lazy" (i.e. 'fromJSON'
    -- will return a 'Map' that is not necessarily strict in its values), we
    -- need to be careful in order to ensure that we're still dealing with a
    -- 'Map' that's strict in both its keys and values.
    --
    -- To remedy this, we use @Map.map id@ to convert the 'Map'
    -- to one that is now guaranteed to be strict in both its keys and values.
    --
    -- n.b. both the strict and lazy 'Map' modules utilize the same 'Map' data
    -- type which is what makes something like this possible.
    fromJSON = fmap (GenesisAvvmBalances . toStrict) . fromJSON
     where
      -- | /O(n)/. Ensures that all values in the given 'Map' are in WHNF.
      toStrict :: Map k a -> Map k a
      toStrict = Map.map id
