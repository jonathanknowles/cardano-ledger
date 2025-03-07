{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Allegra.TxCert () where

import Cardano.Ledger.Allegra.Era
import Cardano.Ledger.Crypto
import Cardano.Ledger.Shelley.TxCert

instance Crypto c => EraTxCert (AllegraEra c) where
  {-# SPECIALIZE instance EraTxCert (AllegraEra StandardCrypto) #-}

  type TxCert (AllegraEra c) = ShelleyTxCert (AllegraEra c)

  mkTxCertPool = ShelleyTxCertPool

  getTxCertPool (ShelleyTxCertPool c) = Just c
  getTxCertPool _ = Nothing

  mkTxCertGenesis = ShelleyTxCertGenesis

  getTxCertGenesis (ShelleyTxCertGenesis c) = Just c
  getTxCertGenesis _ = Nothing

instance Crypto c => ShelleyEraTxCert (AllegraEra c) where
  {-# SPECIALIZE instance ShelleyEraTxCert (AllegraEra StandardCrypto) #-}

  mkShelleyTxCertDeleg = ShelleyTxCertDelegCert

  getShelleyTxCertDeleg (ShelleyTxCertDelegCert c) = Just c
  getShelleyTxCertDeleg _ = Nothing

  mkTxCertMir = ShelleyTxCertMir

  getTxCertMir (ShelleyTxCertMir c) = Just c
  getTxCertMir _ = Nothing
