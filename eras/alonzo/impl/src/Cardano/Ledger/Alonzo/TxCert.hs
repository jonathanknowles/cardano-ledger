{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Alonzo.TxCert () where

import Cardano.Ledger.Alonzo.Era (AlonzoEra)
import Cardano.Ledger.Crypto (Crypto, StandardCrypto)
import Cardano.Ledger.Shelley.TxCert (EraTxCert (..), ShelleyEraTxCert (..), ShelleyTxCert (..))

instance Crypto c => EraTxCert (AlonzoEra c) where
  {-# SPECIALIZE instance EraTxCert (AlonzoEra StandardCrypto) #-}

  type TxCert (AlonzoEra c) = ShelleyTxCert (AlonzoEra c)

  mkTxCertPool = ShelleyTxCertPool

  getTxCertPool (ShelleyTxCertPool c) = Just c
  getTxCertPool _ = Nothing

  mkTxCertGenesis = ShelleyTxCertGenesis

  getTxCertGenesis (ShelleyTxCertGenesis c) = Just c
  getTxCertGenesis _ = Nothing

instance Crypto c => ShelleyEraTxCert (AlonzoEra c) where
  {-# SPECIALIZE instance ShelleyEraTxCert (AlonzoEra StandardCrypto) #-}

  mkShelleyTxCertDeleg = ShelleyTxCertDelegCert

  getShelleyTxCertDeleg (ShelleyTxCertDelegCert c) = Just c
  getShelleyTxCertDeleg _ = Nothing

  mkTxCertMir = ShelleyTxCertMir

  getTxCertMir (ShelleyTxCertMir c) = Just c
  getTxCertMir _ = Nothing
