{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Babbage.TxCert () where

import Cardano.Ledger.Babbage.Era
import Cardano.Ledger.Crypto
import Cardano.Ledger.Shelley.TxCert

instance Crypto c => EraTxCert (BabbageEra c) where
  {-# SPECIALIZE instance EraTxCert (BabbageEra StandardCrypto) #-}

  type TxCert (BabbageEra c) = ShelleyTxCert (BabbageEra c)

  mkTxCertPool = ShelleyTxCertPool

  getTxCertPool (ShelleyTxCertPool c) = Just c
  getTxCertPool _ = Nothing

  mkTxCertGenesis = ShelleyTxCertGenesis

  getTxCertGenesis (ShelleyTxCertGenesis c) = Just c
  getTxCertGenesis _ = Nothing

instance Crypto c => ShelleyEraTxCert (BabbageEra c) where
  {-# SPECIALIZE instance ShelleyEraTxCert (BabbageEra StandardCrypto) #-}

  mkShelleyTxCertDeleg = ShelleyTxCertDelegCert

  getShelleyTxCertDeleg (ShelleyTxCertDelegCert c) = Just c
  getShelleyTxCertDeleg _ = Nothing

  mkTxCertMir = ShelleyTxCertMir

  getTxCertMir (ShelleyTxCertMir c) = Just c
  getTxCertMir _ = Nothing
