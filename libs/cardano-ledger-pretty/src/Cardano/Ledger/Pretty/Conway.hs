{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use record patterns" #-}

module Cardano.Ledger.Pretty.Conway (
  ppConwayTxBody,
) where

import Cardano.Ledger.Conway (ConwayEra)
import Cardano.Ledger.Conway.Core
import Cardano.Ledger.Conway.Governance (
  Anchor,
  ConwayGovernance (..),
  ConwayTallyState (..),
  GovernanceAction (..),
  GovernanceActionId (..),
  GovernanceActionIx (..),
  GovernanceActionState (..),
  GovernanceProcedure,
  ProposalProcedure (..),
  Vote (..),
  VoterRole (..),
  VotingProcedure (..),
 )
import Cardano.Ledger.Conway.Rules (
  ConwayDelegsPredFailure (..),
  ConwayLedgerPredFailure (..),
  ConwayTallyPredFailure,
  EnactState (..),
  PredicateFailure,
  RatifyState (..),
 )
import Cardano.Ledger.Conway.TxBody (ConwayTxBody (..))
import Cardano.Ledger.Conway.TxCert (
  ConwayDelegCert (..),
  ConwayTxCert (..),
  Delegatee (..),
 )
import Cardano.Ledger.Crypto
import Cardano.Ledger.Pretty (
  PDoc,
  PrettyA (..),
  ppAuxiliaryDataHash,
  ppCoin,
  ppConstitutionalDelegCert,
  ppKeyHash,
  ppNetwork,
  ppPoolCert,
  ppRecord,
  ppSafeHash,
  ppSet,
  ppSexp,
  ppStrictMaybe,
  ppStrictSeq,
  ppString,
  ppTxIn,
  ppWithdrawals,
 )
import Cardano.Ledger.Pretty.Babbage (ppBabbagePParams, ppBabbagePParamsUpdate)
import Cardano.Ledger.Pretty.Mary (ppMultiAsset, ppValidityInterval)
import Lens.Micro ((^.))
import Prettyprinter (viaShow)

instance
  ( ConwayEraTxBody era
  , PrettyA (TxOut era)
  , TxBody era ~ ConwayTxBody era
  ) =>
  PrettyA (ConwayTxBody era)
  where
  prettyA = ppConwayTxBody

instance PrettyA (Delegatee era) where
  prettyA (DelegStake skh) =
    ppRecord
      "DelegStake"
      [ ("Staking Key Hash", prettyA skh)
      ]
  prettyA (DelegVote vc) =
    ppRecord
      "DelegVote"
      [ ("Voting Credential", prettyA vc)
      ]
  prettyA (DelegStakeVote skh vc) =
    ppRecord
      "DelegStakeVote"
      [ ("Staking Key Hash", prettyA skh)
      , ("Voting Credential", prettyA vc)
      ]

instance PrettyA (ConwayDelegCert c) where
  prettyA (ConwayRegCert c deposit) =
    ppRecord
      "ConwayRegCert"
      [ ("StakeCredential", prettyA c)
      , ("Deposit", prettyA deposit)
      ]
  prettyA (ConwayUnRegCert c deposit) =
    ppRecord
      "ConwayUnRegCert"
      [ ("StakeCredential", prettyA c)
      , ("Deposit", prettyA deposit)
      ]
  prettyA (ConwayDelegCert stakeCredential delegatee) =
    ppRecord
      "ConwayDeleg"
      [ ("Stake Credential", prettyA stakeCredential)
      , ("Delegatee", prettyA delegatee)
      ]
  prettyA (ConwayRegDelegCert stakeCredential delegatee deposit) =
    ppRecord
      "ConwayRegDeleg"
      [ ("Stake Credential", prettyA stakeCredential)
      , ("Delegatee", prettyA delegatee)
      , ("Deposit", prettyA deposit)
      ]

ppConwayTxCert :: ConwayTxCert c -> PDoc
ppConwayTxCert (ConwayTxCertDeleg dc) = ppSexp "ConwayTxCertDeleg" [prettyA dc]
ppConwayTxCert (ConwayTxCertPool pc) = ppSexp "ConwayTxCertPool" [ppPoolCert pc]
ppConwayTxCert (ConwayTxCertConstitutional gdc) = ppSexp "ConwayTxCertConstitutional" [ppConstitutionalDelegCert gdc]

ppConwayTxBody ::
  forall era.
  ( ConwayEraTxBody era
  , PrettyA (TxOut era)
  , TxBody era ~ ConwayTxBody era
  ) =>
  ConwayTxBody era ->
  PDoc
ppConwayTxBody txb =
  ppRecord
    "TxBody (Conway)"
    [ ("spending inputs", ppSet ppTxIn $ txb ^. inputsTxBodyL)
    , ("collateral inputs", ppSet ppTxIn $ txb ^. collateralInputsTxBodyL)
    , ("reference inputs", ppSet ppTxIn $ txb ^. referenceInputsTxBodyL)
    , ("outputs", ppStrictSeq prettyA (txb ^. outputsTxBodyL))
    , ("collateral return", ppStrictMaybe prettyA (txb ^. collateralReturnTxBodyL))
    , ("total collateral", ppStrictMaybe ppCoin $ txb ^. totalCollateralTxBodyL)
    , ("withdrawals", ppWithdrawals $ txb ^. withdrawalsTxBodyL)
    , ("transaction fee", ppCoin $ txb ^. feeTxBodyL)
    , ("validity interval", ppValidityInterval $ txb ^. vldtTxBodyL)
    , ("required signer hashes", ppSet ppKeyHash $ txb ^. reqSignerHashesTxBodyL)
    , ("mint", ppMultiAsset $ txb ^. mintTxBodyL)
    , ("script integrity hash", ppStrictMaybe ppSafeHash $ txb ^. scriptIntegrityHashTxBodyL)
    , ("auxiliary data hash", ppStrictMaybe ppAuxiliaryDataHash $ txb ^. auxDataHashTxBodyL)
    , ("network id", ppStrictMaybe ppNetwork $ txb ^. networkIdTxBodyL)
    , ("voting procedures", ppStrictSeq prettyA $ txb ^. votingProceduresTxBodyL)
    , ("proposal procedures", ppStrictSeq prettyA $ txb ^. proposalProceduresTxBodyL)
    ]

instance PrettyA Vote where
  prettyA = viaShow

instance EraPParams era => PrettyA (VotingProcedure era) where
  prettyA = viaShow

instance EraPParams era => PrettyA (ProposalProcedure era) where
  prettyA = viaShow

instance EraPParams era => PrettyA (GovernanceProcedure era) where
  prettyA = viaShow

instance PrettyA (PParamsUpdate era) => PrettyA (GovernanceAction era) where
  prettyA (ParameterChange ppup) =
    ppRecord
      "ParameterChange"
      [("protocol parameters update", prettyA ppup)]
  prettyA (HardForkInitiation pv) =
    ppRecord
      "HardForkInitiation"
      [("protocol version", prettyA pv)]
  prettyA (TreasuryWithdrawals ws) =
    ppRecord
      "TreasuryWithdrawals"
      [("withdrawals map", prettyA ws)]
  prettyA NoConfidence =
    ppRecord "NoConfidence" []
  prettyA (NewCommittee ms q) =
    ppRecord
      "NewCommittee"
      [ ("members", prettyA ms)
      , ("quorum", prettyA q)
      ]
  prettyA (NewConstitution c) =
    ppRecord
      "NewConstitution"
      [("hash", prettyA c)]

instance forall c. PrettyA (ConwayTxCert c) where
  prettyA = ppConwayTxCert

instance Crypto c => PrettyA (PParams (ConwayEra c)) where
  prettyA = ppBabbagePParams

instance Crypto c => PrettyA (PParamsUpdate (ConwayEra c)) where
  prettyA = ppBabbagePParamsUpdate

instance
  ( PrettyA (PredicateFailure (EraRule "UTXOW" era))
  , PrettyA (PredicateFailure (EraRule "DELEGS" era))
  , PrettyA (PredicateFailure (EraRule "TALLY" era))
  ) =>
  PrettyA (ConwayLedgerPredFailure era)
  where
  prettyA (ConwayUtxowFailure x) = prettyA x
  prettyA (ConwayDelegsFailure x) = prettyA x
  prettyA (ConwayTallyFailure x) = prettyA x

instance PrettyA (ConwayTallyPredFailure era) where
  prettyA = viaShow

instance PrettyA (PParamsUpdate era) => PrettyA (ConwayTallyState era) where
  prettyA (ConwayTallyState x) = prettyA x

instance PrettyA (GovernanceActionId era) where
  prettyA gaid@(GovernanceActionId _ _) =
    let GovernanceActionId {..} = gaid
     in ppRecord
          "GovernanceActionId"
          [ ("Transaction ID", prettyA gaidTxId)
          , ("Governance Action Index", prettyA gaidGovActionIx)
          ]

instance PrettyA GovernanceActionIx where
  prettyA (GovernanceActionIx x) = prettyA x

instance PrettyA VoterRole where
  prettyA = ppString . show

instance PrettyA (Anchor era) where
  prettyA = viaShow

instance PrettyA (PParamsUpdate era) => PrettyA (GovernanceActionState era) where
  prettyA gas@(GovernanceActionState _ _ _ _ _) =
    let GovernanceActionState {..} = gas
     in ppRecord
          "GovernanceActionState"
          [ ("Votes", prettyA gasVotes)
          , ("Deposit", prettyA gasDeposit)
          , ("Return Address", prettyA gasReturnAddr)
          , ("Action", prettyA gasAction)
          , ("Proposed In", prettyA gasProposedIn)
          ]

instance PrettyA (PParams era) => PrettyA (EnactState era) where
  prettyA ens@(EnactState _ _ _ _ _ _) =
    let EnactState {..} = ens
     in ppRecord
          "EnactState"
          [ ("Constitutional Committee", prettyA ensCommittee)
          , ("PParams", prettyA ensPParams)
          , ("ProtVer", prettyA ensProtVer)
          , ("Constitution", prettyA ensConstitution)
          , ("Treasury", prettyA ensTreasury)
          , ("Withdrawals", prettyA ensWithdrawals)
          ]

instance
  ( PrettyA (PParamsUpdate era)
  , PrettyA (PParams era)
  ) =>
  PrettyA (RatifyState era)
  where
  prettyA rs@(RatifyState _ _) =
    let RatifyState {..} = rs
     in ppRecord
          "RatifyState"
          [ ("EnactState", prettyA rsEnactState)
          , ("Future", prettyA rsFuture)
          ]

instance
  ( PrettyA (PParamsUpdate era)
  , PrettyA (PParams era)
  ) =>
  PrettyA (ConwayGovernance era)
  where
  prettyA cg@(ConwayGovernance _ _ _) =
    let ConwayGovernance {..} = cg
     in ppRecord
          "ConwayGovernance"
          [ ("Tally", prettyA cgTally)
          , ("Ratify", prettyA cgRatify)
          , ("VoterRoles", prettyA cgVoterRoles)
          ]

instance
  PrettyA (PredicateFailure (EraRule "CERT" era)) =>
  PrettyA (ConwayDelegsPredFailure era)
  where
  prettyA (DelegateeNotRegisteredDELEG x) =
    ppRecord
      "DelegateeNotRegisteredDELEG"
      [("KeyHash", prettyA x)]
  prettyA (WithdrawalsNotInRewardsDELEGS x) =
    ppRecord
      "WithdrawalsNotInRewardsDELEGS"
      [("Missing Withdrawals", prettyA x)]
  prettyA (CertFailure x) = prettyA x
