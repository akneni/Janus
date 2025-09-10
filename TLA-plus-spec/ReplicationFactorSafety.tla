---------------- MODULE ReplicationFactorSafetyProof ----------------
EXTENDS Janus, TLAPS

(***************************************************************************)
(* This module contains a formal proof of the ReplicationFactorSafety      *)
(* invariant from the Janus specification.                                 *)
(***************************************************************************)

THEOREM Spec_Implies_ReplicationFactorSafety == Spec => []ReplicationFactorSafety
PROOF
  <1> SUFFICES ASSUME ReplicationFactorSafety, [Next]_Vars
               PROVE  ReplicationFactorSafety'
    BY PTL, <1>1, <1>2

  <1>1. Init => ReplicationFactorSafety
    PROOF
      ASSUME Init
      PROVE  ReplicationFactorSafety

      TAKE n, m \in NodeSet
      ASSUME Term[n] = Term[m]
      HAVE Term[n] = 0 /\ Term[m] = 0
        BY ASSUME Init DEF Init
      HAVE ReplicationFactor[n] = 2 /\ ReplicationFactor[m] = 2
        BY ASSUME Init DEF Init
    QED

  <1>2. ReplicationFactorSafety /\ [Next]_Vars => ReplicationFactorSafety'
    PROOF
      ASSUME Inv == ReplicationFactorSafety,
             Action == [Next]_Vars
      PROVE  Goal == ReplicationFactorSafety'

      DEFINE AllActions(n) ==
          \/ FollowerSendInitWorkload(n)
          \/ FollowerAckInitWorkload(n)
          \/ CandidateProcessAckInitWorkload(n)
          \/ LeaderProcessAckAE_RF1(n)
          \/ LeaderProcessAckAE_RF2(n)
          \/ LeaderSendSwitchToRF1(n)
          \/ LeaderProcessSwitchToRF1(n)
          \/ FollowerSendSwitchToRF1Leader(n)
          \/ CandidateProcessSwitchToRF1Leader(n)
          \/ FollowerAckSwitchToRF2_P1(n)
          \/ LeaderProcessAckSwitchToRF2_P1(n)
          \/ (\E d \in {0,1}: LeaderSendAE_RF1(n,d))
          \/ (\E d \in {0,1}: LeaderSendAE_RF2(n,d))
          \/ FollowerAckAE_RF2(n)
          \/ (\E d \in {0,1}: LeaderSendSwitchToRF2_P1(n,d))

      TAKE n, m \in NodeSet
      ASSUME Term'[n] = Term'[m]

      CASEUNCHANGED <<Term, ReplicationFactor>>
        BY DEF ReplicationFactorSafety

      CASE \E act \in { "ElectorAckAE_RF1",
                        "ElectorAckSwitchToRF1",
                        "ElectorAckSwitchToRF1Leader",
                        "ElectorProcessAE_RF2",
                        "ElectorAckSwitchToRF2_P2" } :
        \E e \in ElectorNodes :
          \/ (act = "ElectorAckAE_RF1" /\ ElectorAckAE_RF1(e))
          \/ (act = "ElectorAckSwitchToRF1" /\ ElectorAckSwitchToRF1(e))
          \/ (act = "ElectorAckSwitchToRF1Leader" /\ ElectorAckSwitchToRF1Leader(e))
          \/ (act = "ElectorProcessAE_RF2" /\ ElectorProcessAE_RF2(e))
          \/ (act = "ElectorAckSwitchToRF2_P2" /\ ElectorAckSwitchToRF2_P2(e))
        BY Inv, Action

      CASE \E d_node \in DataNodes : AllActions(d_node)
        BY Inv, Action

      CASE DropMsg \/ DupMsg \/ HardReset \/ HardResetWipeMsgs
        BY Inv, Action
    QED

  QED
=============================================================================
