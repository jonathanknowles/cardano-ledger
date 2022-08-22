{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Cardano.Ledger.Twiddle
  ( Twiddler (unTwiddler),
    Twiddle (..),
  )
where

import Cardano.Binary (ToCBOR (..))
import Cardano.Ledger.Alonzo (AlonzoTxBody, AlonzoTxOut)
import Cardano.Ledger.Alonzo.TxBody (AlonzoTxBody (..))
import Cardano.Ledger.Coin (Coin)
import Cardano.Ledger.Core (Era, EraTxBody, Value)
import Cardano.Ledger.Crypto (Crypto)
import Cardano.Ledger.TxIn (TxIn (..))
import Cardano.Ledger.Val (DecodeNonNegative, Val)
import Codec.CBOR.Read (deserialiseFromBytes)
import Codec.CBOR.Term (Term (..), decodeTerm, encodeTerm)
import Codec.CBOR.Write (toLazyByteString)
import Data.Bitraversable (bimapM)
import Data.ByteString (ByteString)
import Data.ByteString.Lazy (fromStrict)
import Data.Foldable (toList)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text.Lazy as T
import Data.Typeable (Typeable)
import GHC.Generics
import Test.QuickCheck (Arbitrary (..), Gen, elements, shuffle)

data Twiddler a = Twiddler
  { unTwiddler :: !a,
    _unEnc :: !Term
  }

gTwiddleTList :: forall a p. (Generic a, TwiddleL' (Rep a p)) => a -> Gen Term
gTwiddleTList a = TList <$> twiddleL' (from @a @p a)

class Twiddle a where
  twiddle :: a -> Gen Term
  default twiddle :: forall p. (Generic a, TwiddleL' (Rep a p)) => a -> Gen Term
  twiddle = gTwiddleTList @a @p

instance Twiddle a => Twiddle [a] where
  twiddle l = do
    f <- elements [TList, TListI]
    l' <- traverse twiddle l
    pure $ f l'

instance (Twiddle k, Twiddle v) => Twiddle (Map k v) where
  twiddle m = do
    -- Elements of a map do not have to be in a specific order,
    -- so we shuffle them
    m' <- shuffle $ Map.toList m
    m'' <- traverse (bimapM twiddle twiddle) m'
    f <- elements [TMap, TMapI]
    pure $ f m''

instance Twiddle ByteString where
  twiddle bs = do
    f <- elements [TBytes, TBytesI . fromStrict]
    pure $ f bs

instance Twiddle Text where
  twiddle t = do
    f <- elements [TString, TStringI . T.fromStrict]
    pure $ f t

instance Twiddle Int where
  -- TODO: Put small ints into bigger words (e.g. a Word16 value into Word32)
  --
  -- This is not possible with the CBOR AST provided by cborg
  twiddle = pure . TInt

instance (Twiddle a, Arbitrary a, ToCBOR a) => Arbitrary (Twiddler a) where
  arbitrary = do
    x <- arbitrary
    enc' <- twiddle x
    pure $ Twiddler x enc'

instance Twiddle a => Twiddle (Set a) where
  twiddle = twiddle . toList

instance Twiddle a => Twiddle (Seq a) where
  twiddle = twiddle . toList

instance Twiddle a => Twiddle (StrictSeq a) where
  twiddle = twiddle . toList

instance Typeable a => ToCBOR (Twiddler a) where
  toCBOR (Twiddler _ x) = encodeTerm x

instance Show a => Show (Twiddler a) where
  show (Twiddler x _) = "Twiddler " <> show x

instance Eq a => Eq (Twiddler a) where
  (Twiddler x _) == (Twiddler y _) = x == y

class TwiddleL' a where
  twiddleL' :: a -> Gen [Term]

instance TwiddleL' (V1 p) where
  twiddleL' v1 = case v1 of

instance TwiddleL' (U1 p) where
  twiddleL' U1 = pure []

instance (TwiddleL' (l x), TwiddleL' (r x)) => TwiddleL' ((l :*: r) x) where
  twiddleL' (lx :*: rx) = do
    lx' <- twiddleL' lx
    rx' <- twiddleL' rx
    pure $ lx' <> rx'

instance (TwiddleL' (l x), TwiddleL' (r x)) => TwiddleL' ((l :+: r) x) where
  twiddleL' (L1 lx) = twiddleL' lx
  twiddleL' (R1 rx) = twiddleL' rx

instance Twiddle c => TwiddleL' (K1 i c p) where
  twiddleL' (K1 c) = pure <$> twiddle c

instance (TwiddleL' (f p)) => TwiddleL' (M1 i c f p) where
  twiddleL' (M1 fp) = twiddleL' fp

instance Twiddle Integer where
  twiddle = pure . TInteger

instance Crypto c => Twiddle (TxIn c) where
  twiddle = pure . toTerm

instance (Era era, Val (Value era), DecodeNonNegative (Value era)) => Twiddle (AlonzoTxOut era) where
  twiddle = pure . toTerm

instance Twiddle Coin where
  twiddle = pure . toTerm

instance EraTxBody era => Twiddle (AlonzoTxBody era) where
  twiddle txBody = do
    inputs' <- twiddle $ inputs txBody
    outputs' <- twiddle $ outputs txBody
    fee' <- twiddle $ txfee txBody
    optionalFields <- undefined
    pure . TMap $
      [ (TInt 0, inputs'),
        (TInt 1, outputs'),
        (TInt 2, fee')
      ]
        <> optionalFields

toTerm :: ToCBOR a => a -> Term
toTerm enc = case res of
  Right (_, t) -> t
  Left err -> error $ show err
  where
    res = deserialiseFromBytes decodeTerm . toLazyByteString $ toCBOR enc
