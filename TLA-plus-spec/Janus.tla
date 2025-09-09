------------------------------- MODULE Janus -------------------------------
EXTENDS Integers, FiniteSets, Sequences

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
CONSTANT MaxTerm, MaxIndex, DataNodes, ElectorNodes

(***************************************************************************)
(* Node universe (built from constants; safe for use in type operators)    *)
(***************************************************************************)
NodeSet == DataNodes \cup ElectorNodes

(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)
VARIABLES
  ActivatedNode,     \* Not actually in the state machine. Just here for TLA+ debugging
  LoggedIdx,         \* [DataNodes -> LogEntryMd]
  CommittedIdx,      \* [DataNodes -> LogEntryMd]
  Term,              \* [NodeSet   -> 0..MaxTerm]
  Role,              \* [NodeSet   -> {"leader","candidate","follower","elector"}]
  Nodes,             \* runtime alias of NodeSet
  ReplicationFactor, \* [NodeSet -> {1,2}]
  NumFailures,       \* Nat, at most 1
  CurrentLeader,     \* [NodeSet -> DataNodes \cup {"unknown","none"}]
  DmlLog,            \* [DataNodes -> Seq(LogEntry)]
  Messages           \* Seq(AllMsgs)


(***************************************************************************)
(* Types & Helpers                                                         *)
(***************************************************************************)
LogEntryMd == [ term: 0..MaxTerm, index: 0..MaxIndex ]

LogEntry ==
  [ metadata: LogEntryMd,
    data     : {0,1} ]

OtherDataNode(n) == CHOOSE m \in DataNodes : m # n

LastMd(s) ==
  IF Len(s) = 0 THEN [term |-> 0, index |-> 0] ELSE s[Len(s)].metadata

PosUpToIndex(n, i) ==
  { p \in 1..Len(DmlLog[n]) : DmlLog[n][p].metadata.index <= i }

LastPosUpToIndex(n, i) ==
  IF PosUpToIndex(n, i) = {} THEN 0
  ELSE CHOOSE p \in PosUpToIndex(n, i) :
         \A q \in PosUpToIndex(n, i) : p >= q

\* Returns true if a > b
LeMdGreater(a, b) ==
  (a.term  >  b.term) \/
  (
    a.term  =  b.term /\
    a.index >= b.index
  )

\* Returns true if a >= b
LeMdGreaterOrEq(a, b) ==
  (a.term  >  b.term) \/
  (
    a.term  =  b.term /\
    a.index >= b.index
  )

LeMdMax(a, b) ==
  IF LeMdGreater(a, b) THEN a ELSE b

LeMdMin(a, b) ==
  IF LeMdGreater(a, b) THEN b ELSE a

Prefix(s,t) == Len(s) <= Len(t) /\ \A i \in 1..Len(s) : s[i] = t[i]

UpToIndex(n, i) ==
  IF LastPosUpToIndex(n, i) = 0 THEN << >>
  ELSE SubSeq(DmlLog[n], 1, LastPosUpToIndex(n, i))

Appears(n, md) ==
  \E p \in 1..Len(DmlLog[n]) : DmlLog[n][p].metadata = md

EntryCommitted(md) ==
  /\ md.index > 0 /\ md.term > 0
  /\ \E n \in DataNodes :
       /\ Appears(n, md)
       /\ md.index <= CommittedIdx[n].index

RECURSIVE KeepNotDest(_, _)
KeepNotDest(seq, dest) ==
  IF Len(seq) = 0 THEN << >>
  ELSE
    IF seq[1].destination = dest
    THEN KeepNotDest(SubSeq(seq, 2, Len(seq)), dest)
    ELSE << seq[1] >> \o KeepNotDest(SubSeq(seq, 2, Len(seq)), dest)


(***************************************************************************)
(* Message "types" as record universes (depend only on constants)          *)
(***************************************************************************)
MessageTypes == {
  "AppendEntries RF1", 
  "AppendEntries RF2",
  "SwitchToRF1", 
  "SwitchToRF1Leader",
  "SwitchToRF2 P1", 
  "SwitchToRF2 P2",
  "InitWorkload",
  
  "AppendEntries RF1 Resp", 
  "AppendEntries RF2 Resp",
  "SwitchToRF1 Resp", 
  "SwitchToRF1Leader Resp",
  "SwitchToRF2 P1 Resp",
  "InitWorkload Resp"
}

AeRf1 == [
  source       : NodeSet,
  destination  : NodeSet,
  rpc_type     : {"AppendEntries RF1"},
  committed_idx: LogEntryMd,
  term         : 0..MaxTerm,
  RF           : 1..2,
  logentry_md  : LogEntryMd
]
AeRf1Resp == [
  source       : NodeSet,
  destination  : NodeSet,
  rpc_type     : {"AppendEntries RF1 Resp"},
  logged_idx   : LogEntryMd,
  committed_idx: LogEntryMd,
  term         : 0..MaxTerm,
  RF           : 1..2,
  ok           : {TRUE,FALSE}
]

AeRf2 == [
  source       : NodeSet,
  destination  : NodeSet,
  rpc_type     : {"AppendEntries RF2"},
  committed_idx: LogEntryMd,
  term         : 0..MaxTerm,
  RF           : 1..2,
  logentry     : LogEntry
]
AeRf2Resp == [
  source       : NodeSet,
  destination  : NodeSet,
  rpc_type     : {"AppendEntries RF2 Resp"},
  logged_idx   : LogEntryMd,
  committed_idx: LogEntryMd,
  term         : 0..MaxTerm,
  RF           : 1..2,
  ok           : {TRUE,FALSE}
]

StRf1 == [
  source       : NodeSet,
  destination  : NodeSet,
  rpc_type     : {"SwitchToRF1"},
  committed_idx: LogEntryMd,
  term         : 0..MaxTerm,
  RF           : 1..2
]
StRf1Resp == [
  source       : NodeSet,
  destination  : NodeSet,
  rpc_type     : {"SwitchToRF1 Resp"},
  committed_idx: LogEntryMd,
  term         : 0..MaxTerm,
  RF           : 1..2,
  ok           : {TRUE,FALSE}
]

StRf1L == [
  source       : NodeSet,
  destination  : NodeSet,
  rpc_type     : {"SwitchToRF1Leader"},
  logged_idx   : LogEntryMd,
  committed_idx: LogEntryMd,
  term         : 0..MaxTerm,
  RF           : 1..2
]
StRf1LResp == [
  source       : NodeSet,
  destination  : NodeSet,
  rpc_type     : {"SwitchToRF1Leader Resp"},
  committed_idx: LogEntryMd,
  term         : 0..MaxTerm,
  RF           : 1..2,
  ok           : {TRUE,FALSE}
]

StRf2P1 == [
  source       : NodeSet,
  destination  : NodeSet,
  rpc_type     : {"SwitchToRF2 P1"},
  logged_idx   : LogEntryMd,  
  committed_idx: LogEntryMd,
  term         : 0..MaxTerm,
  RF           : 1..2,
  dml_log      : Seq(LogEntry)
]
StRf2P1Resp == [
  source       : NodeSet,
  destination  : NodeSet,
  rpc_type     : {"SwitchToRF2 P1 Resp"},
  logged_idx   : LogEntryMd,
  committed_idx: LogEntryMd,
  term         : 0..MaxTerm,
  RF           : 1..2
]

StRf2P2 == [
  source       : NodeSet,
  destination  : NodeSet,
  rpc_type     : {"SwitchToRF2 P2"},
  committed_idx: LogEntryMd,
  term         : 0..MaxTerm,
  RF           : 1..2
]

InitWorkload == [
  source      : NodeSet,
  destination : NodeSet,
  rpc_type    : {"InitWorkload"},
  logged_index: LogEntryMd,
  term        : 0..MaxTerm,
  RF          : 1..2
]

InitWorkloadResp == [
  source      : NodeSet,
  destination : NodeSet,
  rpc_type    : {"InitWorkload Resp"},
  logged_index: LogEntryMd,
  term        : 0..MaxTerm,
  RF          : 1..2,
  ok          : {TRUE, FALSE}
]

AllMsgs ==
  AeRf1 \cup AeRf1Resp \cup AeRf2 \cup AeRf2Resp \cup
  StRf1 \cup StRf1Resp \cup StRf1L \cup StRf1LResp \cup
  StRf2P1 \cup StRf2P1Resp \cup StRf2P2 \cup 
  InitWorkload \cup InitWorkloadResp

(***************************************************************************)
(* Invariants / Properties                                                 *)
(***************************************************************************)
TypeOk ==
  /\ LoggedIdx \in [DataNodes -> LogEntryMd]
  /\ CommittedIdx \in [Nodes -> LogEntryMd]
  /\ Term \in [NodeSet -> 0..MaxTerm]
  /\ Role \in [NodeSet -> {"leader","candidate","follower","elector"}]
  /\ \A n \in DataNodes : Role[n] \in {"leader","candidate","follower"}
  /\ \A n \in ElectorNodes : Role[n] \in {"elector"}
  /\ NumFailures \in Nat /\ NumFailures <= 1
  /\ ReplicationFactor \in [NodeSet -> {1,2}]
  /\ CurrentLeader \in [NodeSet -> DataNodes \cup {"unknown","none"}]
  /\ DmlLog \in [DataNodes -> Seq(LogEntry)]
  /\ Messages \in Seq(AllMsgs)

StructureOk ==
  /\ \A n \in DataNodes :
       /\ LoggedIdx[n] = LastMd(DmlLog[n])
       /\ CommittedIdx[n].index <= LoggedIdx[n].index
       /\ (CommittedIdx[n].index = 0 \/ CommittedIdx[n].term <= LoggedIdx[n].term)
  /\ \A n \in DataNodes :
       \A p \in 1..Len(DmlLog[n]) :
         DmlLog[n][p].metadata.index = p

MiscOk ==
    \* CurrentLeader is consistant with the actual leader
    /\ \A i \in NodeSet :
        /\ (CurrentLeader[i] # "none"  /\ CurrentLeader[i] # "unknown" )
            => \A k \in DataNodes :
                (k # CurrentLeader[i] /\ Term[k] = Term[i]) => Role[k] # "leader"
    
    \* No one sends messages to themselves
    /\ \A i \in 1..Len(Messages) : Messages[i].source # Messages[i].destination
            
(* 1. Leader Safety *)
LeaderSafety ==
  \A n,m \in DataNodes :
    (Role[n] = "leader" /\ Role[m] = "leader" /\ Term[n] = Term[m]) => n = m

(* 2. RF Safety *)
ReplicationFactorSafety ==
  \A n,m \in NodeSet :
    (Term[n] = Term[m]) => (ReplicationFactor[n] = ReplicationFactor[m])

(* 3. Leader Append-Only *)
LeaderAppendOnly ==
  \A n \in DataNodes :
    (Role[n] = "leader" /\ Role'[n] = "leader")
      => Prefix(DmlLog[n], DmlLog'[n])


(* 4. Log Matching *)
LogMatching ==
  \A n,m \in DataNodes :
    \A md \in LogEntryMd :
      /\ md.index > 0 /\ md.term > 0
      /\ Appears(n, md) /\ Appears(m, md)
      => UpToIndex(n, md.index) = UpToIndex(m, md.index)

(* 5. Leader Completeness *)
LeaderCompleteness ==
  \A md \in LogEntryMd :
    \A m \in DataNodes :
      (EntryCommitted(md) /\ Role[m] = "leader" /\ Term[m] > md.term)
        => Appears(m, md)

(* 6. State-Machine Safety *)
StateMachineSafety ==
  \A n,m \in DataNodes :
    \A i \in 1..MaxIndex :
      /\ i <= CommittedIdx[n].index
      /\ i <= CommittedIdx[m].index
      /\ i <= Len(DmlLog[n])
      /\ i <= Len(DmlLog[m])
   => DmlLog[n][i] = DmlLog[m][i]

(***************************************************************************)
(* Init                                                                    *)
(***************************************************************************)
Init ==
    /\ ActivatedNode = "none"
    /\ LoggedIdx = [n \in DataNodes |-> [term |-> 0, index |-> 0]]
    /\ CommittedIdx = [n \in NodeSet |-> [term |-> 0, index |-> 0]]
    /\ Term = [n \in NodeSet |-> 0]
    /\ Role = [n \in NodeSet |->
        CASE n \in DataNodes /\ n = CHOOSE d \in DataNodes : TRUE -> "follower"
        [] n \in DataNodes /\ n # CHOOSE d \in DataNodes : TRUE -> "follower"
        [] n \in ElectorNodes -> "elector"]
    /\ Nodes = NodeSet
    /\ NumFailures = 0
    /\ ReplicationFactor = [n \in NodeSet |-> 2]
    /\ CurrentLeader = [n \in NodeSet |-> "none"]
    /\ DmlLog = [n \in DataNodes |-> <<>>]
    /\ Messages = << >>

(***************************************************************************)
(* Sequence helpers for message queue                                      *)
(***************************************************************************)
RemoveAt(seq, i) ==
  IF i = 1 THEN SubSeq(seq, 2, Len(seq))
  ELSE IF i = Len(seq) THEN SubSeq(seq, 1, Len(seq)-1)
  ELSE SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

(***************************************************************************)
(* Leader/Follower/Elector Actions                                         *)
(***************************************************************************)
FollowerSendInitWorkload(n) ==
  /\ n \in DataNodes
  /\ Role[n] = "follower"
  /\ Term[n] = 0
  /\ LET msg == [
         source       |-> n,
         destination  |-> OtherDataNode(n),
         rpc_type     |-> "InitWorkload",
         logged_index |-> LoggedIdx[n],
         term         |-> Term[n],
         RF           |-> ReplicationFactor[n]
     ]
     IN
       /\ Messages'      = Append(Messages, msg)
       /\ Role'          = [Role EXCEPT ![n] = "candidate"]
       /\ ActivatedNode' = n
       /\ UNCHANGED << LoggedIdx, CommittedIdx, Term, Nodes,
                       ReplicationFactor, NumFailures, DmlLog, CurrentLeader >>

FollowerAckInitWorkload(f) ==
  /\ f \in DataNodes
  /\ \E i \in 1..Len(Messages) :
       LET m == Messages[i] IN
         /\ m.rpc_type = "InitWorkload"
         /\ m.destination = f
         /\ m.term >= Term[f]
  /\ LET m == Messages[
         CHOOSE j \in 1..Len(Messages) :
           /\ Messages[j].rpc_type = "InitWorkload"
           /\ Messages[j].destination = f
           /\ Messages[j].term >= Term[f]
       ]
       \* Lexicographic “at least as up-to-date”
       newerOrEq ==
            (m.logged_index.term  >  LoggedIdx[f].term)
         \/ (m.logged_index.term  =  LoggedIdx[f].term /\ m.logged_index.index >  LoggedIdx[f].index)
         \/ (m.logged_index.term  =  LoggedIdx[f].term /\ m.logged_index.index = LoggedIdx[f].index)
       \* tie-break only when exactly equal
       tie   == (m.logged_index.term = LoggedIdx[f].term /\ m.logged_index.index = LoggedIdx[f].index)
       idWins == (m.source = "d2" /\ f = "d1")  \* d2 > d1
       ok    == IF tie THEN idWins ELSE (m.logged_index.term > LoggedIdx[f].term \/ m.logged_index.index > LoggedIdx[f].index)

       newTermF    == IF ok THEN m.term + 1 ELSE Term[f]
       newLeaderF  == IF ok THEN m.source ELSE CurrentLeader[f]
       resp == [
         source       |-> f,
         destination  |-> m.source,
         rpc_type     |-> "InitWorkload Resp",
         logged_index |-> m.logged_index,
         term         |-> newTermF,
         RF           |-> m.RF,
         ok           |-> ok
       ]
       idx == CHOOSE k \in 1..Len(Messages) : Messages[k] = m
    IN
     /\ Term'          = [Term EXCEPT ![f] = newTermF]
     /\ CurrentLeader' = [CurrentLeader EXCEPT ![f] = newLeaderF]
     /\ Messages'      = Append(RemoveAt(Messages, idx), resp)
     /\ ActivatedNode' = f
     /\ UNCHANGED << LoggedIdx, CommittedIdx, Role, Nodes,
                     ReplicationFactor, NumFailures, DmlLog >>

CandidateProcessAckInitWorkload_OK(n) ==
  /\ n \in DataNodes
  /\ Role[n] = "candidate"
  /\ \E i \in 1..Len(Messages) :
       LET r == Messages[i] IN
         /\ r.rpc_type = "InitWorkload Resp"
         /\ r.destination = n
         /\ r.source = OtherDataNode(n)
         /\ r.ok = TRUE
         /\ r.term > Term[n]
  /\ LET r == Messages[
         CHOOSE j \in 1..Len(Messages) :
           /\ Messages[j].rpc_type = "InitWorkload Resp"
           /\ Messages[j].destination = n
           /\ Messages[j].source = OtherDataNode(n)
           /\ Messages[j].ok = TRUE
           /\ Messages[j].term > Term[n]
       ]
       newTermN == r.term
       newRFN   == r.RF
       idx      == CHOOSE k \in 1..Len(Messages) : Messages[k] = r
     IN
       /\ Term'              = [Term EXCEPT ![n] = newTermN]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = newRFN]
       /\ Role'              = [Role EXCEPT ![n] = "leader"]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = n]
       /\ Messages'          = RemoveAt(Messages, idx)
       /\ ActivatedNode'     = n
       /\ UNCHANGED << LoggedIdx, CommittedIdx, Nodes, NumFailures, DmlLog >>

CandidateProcessAckInitWorkload_NACK(n) ==
  /\ n \in DataNodes
  /\ Role[n] = "candidate"
  /\ \E i \in 1..Len(Messages) :
       LET r == Messages[i] IN
         /\ r.rpc_type = "InitWorkload Resp"
         /\ r.destination = n
         /\ r.source = OtherDataNode(n)
         /\ r.ok = FALSE
         /\ r.term >= Term[n]
  /\ LET r == Messages[
         CHOOSE j \in 1..Len(Messages) :
           /\ Messages[j].rpc_type = "InitWorkload Resp"
           /\ Messages[j].destination = n
           /\ Messages[j].source = OtherDataNode(n)
           /\ Messages[j].ok = FALSE
           /\ Messages[j].term >= Term[n]
       ]
       higher    == r.term > Term[n]
       newTermN  == IF higher THEN r.term ELSE Term[n]
       newRFN    == IF higher THEN r.RF   ELSE ReplicationFactor[n]
       newCurLdN == IF higher THEN "unknown" ELSE CurrentLeader[n]
       idx       == CHOOSE k \in 1..Len(Messages) : Messages[k] = r
     IN
       /\ Term'              = [Term EXCEPT ![n] = newTermN]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = newRFN]
       /\ Role'              = [Role EXCEPT ![n] = "follower"]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = newCurLdN]
       /\ Messages'          = RemoveAt(Messages, idx)
       /\ ActivatedNode'     = n
       /\ UNCHANGED << LoggedIdx, CommittedIdx, Nodes, NumFailures, DmlLog >>

CandidateProcessAckInitWorkload(n) ==
    CandidateProcessAckInitWorkload_OK(n) \/ CandidateProcessAckInitWorkload_NACK(n)

LeaderSendAE_RF1(n, d) ==
  /\ n \in DataNodes
  /\ Role[n] = "leader"
  /\ ReplicationFactor[n] = 1
  /\ Term[n] > 0
  /\ d \in {0,1}
  /\ LET newMd    == [term |-> Term[n], index |-> LoggedIdx[n].index + 1]
         newEntry == [metadata |-> newMd, data |-> d]
         msg == [
           source       |-> n,
           destination  |-> CHOOSE e \in ElectorNodes : TRUE,
           rpc_type     |-> "AppendEntries RF1",
           committed_idx |-> CommittedIdx[n],
           term         |-> Term[n],
           RF           |-> ReplicationFactor[n],
           logentry_md  |-> newMd
         ]
     IN
       /\ DmlLog'    = [DmlLog EXCEPT ![n] = Append(@, newEntry)]
       /\ LoggedIdx' = [LoggedIdx EXCEPT ![n] = newMd]
       /\ Messages'  = Append(Messages, msg)
       /\ ActivatedNode' = n
       /\ UNCHANGED << CommittedIdx, Term, Role, Nodes,
                       ReplicationFactor, NumFailures, CurrentLeader >>

ElectorAckAE_RF1(e) ==
  /\ e \in ElectorNodes
  /\ \E i \in 1..Len(Messages) :
       LET m == Messages[i] IN
         /\ m.rpc_type = "AppendEntries RF1"
         /\ m.destination = e
         /\ m.term >= Term[e]
  /\ LET m == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "AppendEntries RF1"
                        /\ Messages[j].destination = e
                        /\ Messages[j].term >= Term[e]]
         higher == m.term > Term[e]
         ciHigh == LeMdGreater(m.committed_idx, CommittedIdx[e])
         newTermE   == IF higher THEN m.term ELSE Term[e]
         newRFE     == IF higher THEN m.RF   ELSE ReplicationFactor[e]
         newLeaderE == IF higher THEN m.source ELSE CurrentLeader[e]
         newCIE     == IF ciHigh THEN m.committed_idx ELSE CommittedIdx[e]
         \* ok iff leader's commit index >= elector's own (term, index)
         okGE == LeMdGreaterOrEq(m.committed_idx, CommittedIdx[e])
         resp == [
           source        |-> e,
           destination   |-> m.source,
           rpc_type      |-> "AppendEntries RF1 Resp",
           logged_idx    |-> m.logentry_md,
           committed_idx |-> newCIE,
           term          |-> newTermE,
           RF            |-> newRFE,
           ok            |-> okGE
         ]
         idx == CHOOSE j \in 1..Len(Messages) : Messages[j] = m
     IN
       /\ Term'              = [Term EXCEPT ![e] = newTermE]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![e] = newRFE]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![e] = newLeaderE]
       /\ CommittedIdx'      = [CommittedIdx EXCEPT ![e] = newCIE]
       /\ Messages'          = Append(RemoveAt(Messages, idx), resp)
       /\ ActivatedNode'     = e
       /\ UNCHANGED << LoggedIdx, Role, Nodes, NumFailures, DmlLog >>


LeaderProcessAckAE_RF1_OK(n) ==
  /\ n \in DataNodes
  /\ Term[n] > 0
  /\ \E i \in 1..Len(Messages) :
       LET r == Messages[i] IN
         /\ r.rpc_type = "AppendEntries RF1 Resp"
         /\ r.destination = n
         /\ r.ok = TRUE
         /\ r.term >= Term[n]
  /\ LET r == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "AppendEntries RF1 Resp"
                        /\ Messages[j].destination = n
                        /\ Messages[j].ok = TRUE
                        /\ Messages[j].term >= Term[n]]
         higher      == r.term > Term[n]
         aheadCI     == LeMdGreater(r.committed_idx, CommittedIdx[n])
         newTermN    == IF higher THEN r.term ELSE Term[n]
         newRFN      == IF higher THEN r.RF   ELSE ReplicationFactor[n]
         demote      == higher /\ aheadCI
         newRoleN    == IF demote THEN "follower" ELSE Role[n]
         newCurLeadN == IF demote THEN "none" ELSE CurrentLeader[n]
         newCi       == IF demote THEN CommittedIdx[n] ELSE LeMdMin(LeMdMax(r.logged_idx, CommittedIdx[n]), LoggedIdx[n])
         idx == CHOOSE j \in 1..Len(Messages) : Messages[j] = r
     IN
       /\ Term'              = [Term EXCEPT ![n] = newTermN]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = newRFN]
       /\ Role'              = [Role EXCEPT ![n] = newRoleN]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = newCurLeadN]
       /\ CommittedIdx'      = [CommittedIdx EXCEPT ![n] = newCi]
       /\ Messages'          = RemoveAt(Messages, idx)
       /\ ActivatedNode' = n
       /\ UNCHANGED << LoggedIdx, Nodes, NumFailures, DmlLog >>

LeaderProcessAckAE_RF1_NACK(n) ==
  /\ n \in DataNodes
  /\ Term[n] > 0
  /\ \E i \in 1..Len(Messages) :
       LET r == Messages[i] IN
         /\ r.rpc_type = "AppendEntries RF1 Resp"
         /\ r.destination = n
         /\ r.ok = FALSE
         /\ r.term >= Term[n]
  /\ LET r == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "AppendEntries RF1 Resp"
                        /\ Messages[j].destination = n
                        /\ Messages[j].ok = FALSE
                        /\ Messages[j].term >= Term[n]]
         higher      == r.term > Term[n]
         newTermN    == IF higher THEN r.term ELSE Term[n]
         newRFN      == IF higher THEN r.RF   ELSE ReplicationFactor[n]
         newRoleN    == IF higher THEN "follower" ELSE Role[n]
         newCurLeadN == IF higher THEN "unknown" ELSE CurrentLeader[n]
         idx == CHOOSE j \in 1..Len(Messages) : Messages[j] = r
     IN
       /\ Term'              = [Term EXCEPT ![n] = newTermN]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = newRFN]
       /\ Role'              = [Role EXCEPT ![n] = newRoleN]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = newCurLeadN]
       /\ Messages'          = RemoveAt(Messages, idx)
       /\ ActivatedNode' = n
       /\ UNCHANGED << LoggedIdx, CommittedIdx, Nodes, NumFailures, DmlLog >>

LeaderProcessAckAE_RF1(n) == LeaderProcessAckAE_RF1_OK(n) \/ LeaderProcessAckAE_RF1_NACK(n)

LeaderSendAE_RF2(n, d) ==
  /\ n \in DataNodes
  /\ Role[n] = "leader"
  /\ ReplicationFactor[n] = 2
  /\ d \in {0,1}
  /\ Term[n] > 0
  /\ LET newMd    == [term |-> Term[n], index |-> LoggedIdx[n].index + 1]
         newEntry == [metadata |-> newMd, data |-> d]
         f        == OtherDataNode(n)
         eDest    == CHOOSE e \in ElectorNodes : TRUE
         msgF     == [
           source       |-> n,
           destination  |-> f,
           rpc_type     |-> "AppendEntries RF2",
           committed_idx |-> CommittedIdx[n],
           term         |-> Term[n],
           RF           |-> ReplicationFactor[n],
           logentry     |-> newEntry
         ]
         msgE     == [
           source       |-> n,
           destination  |-> eDest,
           rpc_type     |-> "AppendEntries RF2",
           committed_idx |-> CommittedIdx[n],
           term         |-> Term[n],
           RF           |-> ReplicationFactor[n],
           logentry     |-> newEntry
         ]
     IN
       /\ DmlLog'    = [DmlLog EXCEPT ![n] = Append(@, newEntry)]
       /\ LoggedIdx' = [LoggedIdx EXCEPT ![n] = newMd]
       /\ Messages'  = Append(Append(Messages, msgF), msgE)
       /\ ActivatedNode' = n
       /\ UNCHANGED << CommittedIdx, Term, Role, Nodes,
                       ReplicationFactor, NumFailures, CurrentLeader >>

FollowerAckAE_RF2(f) ==
  /\ f \in DataNodes
  /\ Role[f] \in {"follower","candidate","leader"}
  /\ \E i \in 1..Len(Messages) :
       LET m == Messages[i] IN
         /\ m.rpc_type = "AppendEntries RF2"
         /\ m.destination = f
         /\ m.term >= Term[f]
  /\ LET m == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "AppendEntries RF2"
                        /\ Messages[j].destination = f
                        /\ Messages[j].term >= Term[f]]
         higher    == m.term > Term[f]
         newTermF  == IF higher THEN m.term ELSE Term[f]
         newRFF    == IF higher THEN m.RF   ELSE ReplicationFactor[f]
         newRoleF  == IF higher THEN "follower" ELSE Role[f]
         nextOk    == m.logentry.metadata.index = LoggedIdx[f].index + 1
         accept    == nextOk
         respOk == [
           source        |-> f,
           destination   |-> m.source,
           rpc_type      |-> "AppendEntries RF2 Resp",
           logged_idx    |-> m.logentry.metadata,
           committed_idx |-> m.committed_idx,
           term          |-> newTermF,
           RF            |-> newRFF,
           ok            |-> TRUE
         ]
         respNo == [
           source        |-> f,
           destination   |-> m.source,
           rpc_type      |-> "AppendEntries RF2 Resp",
           logged_idx    |-> LoggedIdx[f],
           committed_idx |-> m.committed_idx,
           term          |-> newTermF,
           RF            |-> newRFF,
           ok            |-> FALSE
         ]
         idx == CHOOSE j \in 1..Len(Messages) : Messages[j] = m
     IN
       /\ Term'              = [Term EXCEPT ![f] = newTermF]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![f] = newRFF]
       /\ Role'              = [Role EXCEPT ![f] = newRoleF]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![f] = m.source]
       /\ IF accept THEN
            /\ DmlLog'       = [DmlLog EXCEPT ![f] = Append(@, m.logentry)]
            /\ LoggedIdx'    = [LoggedIdx EXCEPT ![f] = m.logentry.metadata]
            /\ CommittedIdx' = [CommittedIdx EXCEPT ![f] = m.committed_idx]
            /\ Messages'     = Append(RemoveAt(Messages, idx), respOk)
            /\ ActivatedNode' = f
            /\ UNCHANGED << Nodes, NumFailures >>
          ELSE
            /\ Messages'     = Append(RemoveAt(Messages, idx), respNo)
            /\ ActivatedNode' = f
            /\ UNCHANGED << DmlLog, LoggedIdx, CommittedIdx, Nodes, NumFailures >>

ElectorProcessAE_RF2(e) ==
  /\ e \in ElectorNodes
  /\ \E i \in 1..Len(Messages) :
       LET m == Messages[i] IN
         /\ m.rpc_type = "AppendEntries RF2"
         /\ m.destination = e
         /\ m.term >= Term[e]
  /\ LET m == Messages[
         CHOOSE j \in 1..Len(Messages) :
           /\ Messages[j].rpc_type = "AppendEntries RF2"
           /\ Messages[j].destination = e
           /\ Messages[j].term >= Term[e]
       ]
       higher == m.term > Term[e]
       ciHigh == LeMdGreater(m.committed_idx,  CommittedIdx[e])
       newTermE   == IF higher THEN m.term ELSE Term[e]
       newRFE     == IF higher THEN m.RF   ELSE ReplicationFactor[e]
       newLeaderE == IF higher THEN m.source ELSE CurrentLeader[e]
       newCIE     == IF ciHigh THEN m.committed_idx ELSE CommittedIdx[e]
       idx        == CHOOSE k \in 1..Len(Messages) : Messages[k] = m
     IN
       /\ Term'              = [Term EXCEPT ![e] = newTermE]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![e] = newRFE]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![e] = newLeaderE]
       /\ CommittedIdx'      = [CommittedIdx EXCEPT ![e] = newCIE]
       /\ Messages'          = RemoveAt(Messages, idx)
       /\ ActivatedNode'     = e
       /\ UNCHANGED << LoggedIdx, Role, Nodes, NumFailures, DmlLog >>

LeaderProcessAckAE_RF2_OK(n) ==
  /\ n \in DataNodes
  /\ Term[n] > 0
  /\ \E i \in 1..Len(Messages) :
       LET r == Messages[i] IN
         /\ r.rpc_type = "AppendEntries RF2 Resp"
         /\ r.destination = n
         /\ r.ok = TRUE
         /\ r.term >= Term[n]
  /\ LET r == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "AppendEntries RF2 Resp"
                        /\ Messages[j].destination = n
                        /\ Messages[j].ok = TRUE
                        /\ Messages[j].term >= Term[n]]
         higher      == r.term > Term[n]
         newTermN    == IF higher THEN r.term ELSE Term[n]
         newRFN      == IF higher THEN r.RF   ELSE ReplicationFactor[n]
         newRoleN    == IF higher THEN "follower" ELSE Role[n]
         newCurLeadN == IF higher THEN "unknown" ELSE CurrentLeader[n]
         newCi       == IF higher THEN CommittedIdx[n] ELSE (
          IF LeMdGreaterOrEq(CommittedIdx[n], r.logged_idx) THEN CommittedIdx[n] 
          ELSE (IF LeMdGreater(r.logged_idx, LoggedIdx[n]) THEN LoggedIdx[n] ELSE r.logged_idx)
        )
         idx == CHOOSE j \in 1..Len(Messages) : Messages[j] = r
     IN
       /\ Term'              = [Term EXCEPT ![n] = newTermN]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = newRFN]
       /\ Role'              = [Role EXCEPT ![n] = newRoleN]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = newCurLeadN]
       /\ CommittedIdx'      = [CommittedIdx EXCEPT ![n] = newCi]
       /\ Messages'          = RemoveAt(Messages, idx)
       /\ ActivatedNode' = n
       /\ UNCHANGED << LoggedIdx, Nodes, NumFailures, DmlLog >>

LeaderProcessAckAE_RF2_NACK(n) ==
  /\ n \in DataNodes
  /\ Term[n] > 0
  /\ \E i \in 1..Len(Messages) :
       LET r == Messages[i] IN
         /\ r.rpc_type = "AppendEntries RF2 Resp"
         /\ r.destination = n
         /\ r.ok = FALSE
         /\ r.term >= Term[n]
  /\ LET r == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "AppendEntries RF2 Resp"
                        /\ Messages[j].destination = n
                        /\ Messages[j].ok = FALSE
                        /\ Messages[j].term >= Term[n]]
         higher      == r.term > Term[n]
         newTermN    == IF higher THEN r.term ELSE Term[n]
         newRFN      == IF higher THEN r.RF   ELSE ReplicationFactor[n]
         newRoleN    == IF higher THEN "follower" ELSE Role[n]
         newCurLeadN == IF higher THEN "unknown" ELSE CurrentLeader[n]
         idx == CHOOSE j \in 1..Len(Messages) : Messages[j] = r
     IN
       /\ Term'              = [Term EXCEPT ![n] = newTermN]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = newRFN]
       /\ Role'              = [Role EXCEPT ![n] = newRoleN]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = newCurLeadN]
       /\ Messages'          = RemoveAt(Messages, idx)
       /\ ActivatedNode' = n
       /\ UNCHANGED << LoggedIdx, CommittedIdx, Nodes, NumFailures, DmlLog >>

LeaderProcessAckAE_RF2(n) == LeaderProcessAckAE_RF2_OK(n) \/ LeaderProcessAckAE_RF2_NACK(n)

LeaderSendSwitchToRF1(n) ==
  /\ n \in DataNodes
  /\ Role[n] = "leader"
  /\ ReplicationFactor[n] = 2
  /\ LET msg == [
         source        |-> n,
         destination   |-> CHOOSE e \in ElectorNodes : TRUE,
         rpc_type      |-> "SwitchToRF1",
         committed_idx |-> CommittedIdx[n],
         term          |-> Term[n],
         RF            |-> ReplicationFactor[n]
     ]
     IN
       /\ Messages' = Append(Messages, msg)
       /\ ActivatedNode' = n
       /\ UNCHANGED << LoggedIdx, CommittedIdx, Term, Role, Nodes,
                       ReplicationFactor, NumFailures, DmlLog, CurrentLeader >>

ElectorAckSwitchToRF1(e) ==
  /\ e \in ElectorNodes
  /\ Term[e] > 0
  /\ \E i \in 1..Len(Messages) :
       LET m == Messages[i] IN
         /\ m.rpc_type = "SwitchToRF1"
         /\ m.destination = e
         /\ m.term >= Term[e]
  /\ LET m == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "SwitchToRF1"
                        /\ Messages[j].destination = e
                        /\ Messages[j].term >= Term[e]]
         newTermE == m.term + 1
         newRFE   == 1
         ok ==    (m.committed_idx.term  >  CommittedIdx[e].term)
                \/ (m.committed_idx.term  =  CommittedIdx[e].term
                    /\ m.committed_idx.index >= CommittedIdx[e].index)
         ciGreater == (m.committed_idx.term  >  CommittedIdx[e].term) \/
                      (m.committed_idx.term  =  CommittedIdx[e].term /\
                       m.committed_idx.index >  CommittedIdx[e].index)
         newCIE == IF ciGreater THEN m.committed_idx ELSE CommittedIdx[e]
         resp == [
           source        |-> e,
           destination   |-> m.source,
           rpc_type      |-> "SwitchToRF1 Resp",
           committed_idx |-> m.committed_idx,
           term          |-> newTermE,
           RF            |-> newRFE,
           ok            |-> ok
         ]
         idx == CHOOSE j \in 1..Len(Messages) : Messages[j] = m
     IN
       /\ Term'              = [Term EXCEPT ![e] = newTermE]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![e] = newRFE]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![e] = m.source]
       /\ CommittedIdx'      = [CommittedIdx EXCEPT ![e] = newCIE]
       /\ Messages'          = Append(RemoveAt(Messages, idx), resp)
       /\ ActivatedNode'     = e
       /\ UNCHANGED << LoggedIdx, Role, Nodes, NumFailures, DmlLog >>

LeaderProcessSwitchToRF1_OK(n) ==
  /\ n \in DataNodes
  /\ \E i \in 1..Len(Messages) :
       LET r == Messages[i] IN
         /\ r.rpc_type = "SwitchToRF1 Resp"
         /\ r.destination = n
         /\ r.ok = TRUE
         /\ r.term > Term[n]
  /\ LET r == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "SwitchToRF1 Resp"
                        /\ Messages[j].destination = n
                        /\ Messages[j].ok = TRUE
                        /\ Messages[j].term > Term[n]]
         aheadCI  == (r.committed_idx.term  >  CommittedIdx[n].term) \/
                     (r.committed_idx.term  =  CommittedIdx[n].term /\
                      r.committed_idx.index >  CommittedIdx[n].index)
         newTermN == r.term
         newRFN   == r.RF
         newRoleN == IF aheadCI THEN "follower" ELSE Role[n]
         newCurLd == IF aheadCI THEN "none" ELSE CurrentLeader[n]
         idx == CHOOSE j \in 1..Len(Messages) : Messages[j] = r
     IN
       /\ Term'              = [Term EXCEPT ![n] = newTermN]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = newRFN]
       /\ Role'              = [Role EXCEPT ![n] = newRoleN]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = newCurLd]
       /\ Messages'          = RemoveAt(Messages, idx)
       /\ ActivatedNode' = n
       /\ UNCHANGED << LoggedIdx, CommittedIdx, Nodes, NumFailures, DmlLog >>

LeaderProcessSwitchToRF1_NACK(n) ==
  /\ n \in DataNodes
  /\ \E i \in 1..Len(Messages) :
       LET r == Messages[i] IN
         /\ r.rpc_type = "SwitchToRF1 Resp"
         /\ r.destination = n
         /\ r.ok = FALSE
         /\ r.term >= Term[n]
  /\ LET r == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "SwitchToRF1 Resp"
                        /\ Messages[j].destination = n
                        /\ Messages[j].ok = FALSE
                        /\ Messages[j].term >= Term[n]]
         higher      == r.term > Term[n]
         newTermN    == IF higher THEN r.term ELSE Term[n]
         newRFN      == IF higher THEN r.RF   ELSE ReplicationFactor[n]
         newRoleN    == IF higher THEN "follower" ELSE Role[n]
         newCurLd    == IF higher THEN "unknown"  ELSE CurrentLeader[n]
         idx == CHOOSE j \in 1..Len(Messages) : Messages[j] = r
     IN
       /\ Term'              = [Term EXCEPT ![n] = newTermN]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = newRFN]
       /\ Role'              = [Role EXCEPT ![n] = newRoleN]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = newCurLd]
       /\ Messages'          = RemoveAt(Messages, idx)
       /\ ActivatedNode' = n
       /\ UNCHANGED << LoggedIdx, CommittedIdx, Nodes, NumFailures, DmlLog >>

LeaderProcessSwitchToRF1(n) == 
    LeaderProcessSwitchToRF1_OK(n) \/ LeaderProcessSwitchToRF1_NACK(n)

FollowerSendSwitchToRF1Leader(n) ==
  /\ n \in DataNodes
  /\ Role[n] \in {"follower"}
  /\ Term[n] > 0
  /\ LET msg == [
         source         |-> n,
         destination    |-> CHOOSE e \in ElectorNodes : TRUE,
         rpc_type       |-> "SwitchToRF1Leader",
         logged_idx     |-> LoggedIdx[n],
         committed_idx  |-> CommittedIdx[n],
         term           |-> Term[n],
         RF             |-> ReplicationFactor[n]
     ]
     IN
       /\ Role'     = [Role EXCEPT ![n] = "candidate"]
       /\ Messages' = Append(Messages, msg)
       /\ ActivatedNode' = n
       /\ UNCHANGED << LoggedIdx, CommittedIdx, Term, Nodes,
                       ReplicationFactor, NumFailures, DmlLog,
                       CurrentLeader >>

ElectorAckSwitchToRF1Leader(e) ==
  /\ e \in ElectorNodes
  /\ Term[e] > 0
  /\ ReplicationFactor[e] = 2 \* TODO: determine if we need this or not
  /\ \E i \in 1..Len(Messages) :
       LET m == Messages[i] IN
         /\ m.rpc_type = "SwitchToRF1Leader"
         /\ m.destination = e
         /\ m.term >= Term[e]
  /\ LET m == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "SwitchToRF1Leader"
                        /\ Messages[j].destination = e
                        /\ Messages[j].term >= Term[e]]
         higher == m.term > Term[e]
         ciGreaterOrEq ==
              (m.committed_idx.term  >  CommittedIdx[e].term)
           \/ (m.committed_idx.term  =  CommittedIdx[e].term
               /\ m.committed_idx.index >= CommittedIdx[e].index)
         newCIE == IF ciGreaterOrEq THEN m.committed_idx ELSE CommittedIdx[e]
         idx == CHOOSE j \in 1..Len(Messages) : Messages[j] = m
     IN
       /\ \E ok \in {TRUE,FALSE} :
            
            /\ LET voteYes == ciGreaterOrEq /\ ok
                   newTermE ==
                     IF higher THEN (IF voteYes THEN m.term + 1 ELSE m.term)
                                ELSE (IF voteYes THEN Term[e] + 1 ELSE Term[e])
                   newRFE ==
                     IF voteYes THEN 1 ELSE (IF higher THEN m.RF ELSE ReplicationFactor[e])
                   newLeaderE ==
                     IF voteYes THEN m.source ELSE IF higher THEN "unknown" ELSE CurrentLeader[e]
                   resp == [
                     source        |-> e,
                     destination   |-> m.source,
                     rpc_type      |-> "SwitchToRF1Leader Resp",
                     committed_idx |-> newCIE,
                     term          |-> newTermE,
                     RF            |-> newRFE,
                     ok            |-> voteYes
                   ]
               IN
                 /\ Term'              = [Term EXCEPT ![e] = newTermE]
                 /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![e] = newRFE]
                 /\ CurrentLeader'     = [CurrentLeader EXCEPT ![e] = newLeaderE]
                 /\ CommittedIdx'      = [CommittedIdx EXCEPT ![e] = newCIE]
                 /\ Messages'          = Append(RemoveAt(Messages, idx), resp)
                 /\ ActivatedNode'     = e
                 /\ UNCHANGED << LoggedIdx, Role, Nodes, NumFailures, DmlLog >>

CandidateProcessSwitchToRF1Leader_OK(n) ==
  /\ n \in DataNodes
  /\ Role[n] = "candidate"
  /\ Term[n] > 0
  /\ \E i \in 1..Len(Messages) :
       LET r == Messages[i] IN
         /\ r.rpc_type = "SwitchToRF1Leader Resp"
         /\ r.destination = n
         /\ r.ok = TRUE
         /\ r.term > Term[n]
  /\ LET r == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "SwitchToRF1Leader Resp"
                        /\ Messages[j].destination = n
                        /\ Messages[j].ok = TRUE
                        /\ Messages[j].term > Term[n]]
         aheadCI  == (r.committed_idx.term  >  CommittedIdx[n].term) \/
                     (r.committed_idx.term  =  CommittedIdx[n].term /\
                      r.committed_idx.index >  CommittedIdx[n].index)
         newTermN == r.term
         newRFN   == r.RF
         promote  == ~aheadCI
         newRoleN == IF promote THEN "leader" ELSE "follower"
         newCurLd == IF promote THEN n ELSE "none"
         idx == CHOOSE j \in 1..Len(Messages) : Messages[j] = r
     IN
       /\ Term'              = [Term EXCEPT ![n] = newTermN]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = newRFN]
       /\ Role'              = [Role EXCEPT ![n] = newRoleN]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = newCurLd]
       /\ Messages'          = RemoveAt(Messages, idx)
       /\ ActivatedNode' = n
       /\ UNCHANGED << LoggedIdx, CommittedIdx, Nodes, NumFailures, DmlLog >>

CandidateProcessSwitchToRF1Leader_NACK(n) ==
  /\ n \in DataNodes
  /\ Role[n] = "candidate"
  /\ \E i \in 1..Len(Messages) :
       LET r == Messages[i] IN
         /\ r.rpc_type = "SwitchToRF1Leader Resp"
         /\ r.destination = n
         /\ r.ok = FALSE
         /\ r.term >= Term[n]
  /\ LET r == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "SwitchToRF1Leader Resp"
                        /\ Messages[j].destination = n
                        /\ Messages[j].ok = FALSE
                        /\ Messages[j].term >= Term[n]]
         higher      == r.term > Term[n]
         newTermN    == IF higher THEN r.term ELSE Term[n]
         newRFN      == IF higher THEN r.RF   ELSE ReplicationFactor[n]
         newRoleN    == "follower"
         newCurLeadN == IF higher THEN "unknown" ELSE CurrentLeader[n]
         idx == CHOOSE j \in 1..Len(Messages) : Messages[j] = r
     IN
       /\ Term'              = [Term EXCEPT ![n] = newTermN]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = newRFN]
       /\ Role'              = [Role EXCEPT ![n] = newRoleN]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = newCurLeadN]
       /\ Messages'          = RemoveAt(Messages, idx)
       /\ ActivatedNode' = n
       /\ UNCHANGED << LoggedIdx, CommittedIdx, Nodes, NumFailures, DmlLog >>

CandidateProcessSwitchToRF1Leader(n) ==
  CandidateProcessSwitchToRF1Leader_OK(n) \/ CandidateProcessSwitchToRF1Leader_NACK(n)

(*
  Switch to RF=2 phase 1: packaged tail (optimistic one-entry append included)
*)
LeaderSendSwitchToRF2_P1(n, d) ==
  /\ n \in DataNodes
  /\ Role[n] = "leader"
  /\ ReplicationFactor[n] = 1
  /\ d \in {0,1}
  /\ LET oldMd    == LoggedIdx[n]
         newMd    == [term |-> Term[n], index |-> oldMd.index + 1]
         newEntry == [metadata |-> newMd, data |-> d]
         newLog   == Append(DmlLog[n], newEntry)
         msgF     == [
           source         |-> n,
           destination    |-> OtherDataNode(n),
           rpc_type       |-> "SwitchToRF2 P1",
           logged_idx     |-> newMd,
           committed_idx  |-> CommittedIdx[n],
           term           |-> Term[n],
           RF             |-> ReplicationFactor[n],
           dml_log        |-> newLog
         ]
     IN
       /\ DmlLog'       = [DmlLog EXCEPT ![n] = newLog]
       /\ LoggedIdx'    = [LoggedIdx EXCEPT ![n] = newMd]
       /\ Messages'     = Append(Messages, msgF)
       /\ ActivatedNode' = n
       /\ UNCHANGED << Term, Role, Nodes, ReplicationFactor, NumFailures, CurrentLeader, CommittedIdx >>

FollowerAckSwitchToRF2_P1(f) ==
  /\ f \in DataNodes
  /\ \E i \in 1..Len(Messages) :
       LET m == Messages[i] IN
         /\ m.rpc_type = "SwitchToRF2 P1"
         /\ m.destination = f
         /\ m.term >= Term[f]
  /\ LET m == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "SwitchToRF2 P1"
                        /\ Messages[j].destination = f
                        /\ Messages[j].term >= Term[f]]
         higher   == m.term > Term[f]
         newTermF == m.term + 1
         newRf    == 2
         respOk == [
           source        |-> f,
           destination   |-> m.source,
           rpc_type      |-> "SwitchToRF2 P1 Resp",
           logged_idx    |-> m.logged_idx,
           committed_idx |-> m.committed_idx,
           term          |-> newTermF,
           RF            |-> newRf
         ]
         newCI == LeMdMax(m.committed_idx, CommittedIdx[f])
         idx == CHOOSE k \in 1..Len(Messages) : Messages[k] = m
     IN
       /\ Term'              = [Term EXCEPT ![f] = newTermF]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![f] = newRf]
       /\ DmlLog'            = [DmlLog EXCEPT ![f] = m.dml_log]
       /\ Role'              = [Role EXCEPT ![f] = "follower"]
       /\ LoggedIdx'         = [LoggedIdx EXCEPT ![f] = m.logged_idx]
       /\ CommittedIdx'      = [CommittedIdx EXCEPT ![f] = newCI]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![f] = m.source]
       /\ Messages'          = Append(RemoveAt(Messages, idx), respOk)
       /\ ActivatedNode' = f
       /\ UNCHANGED << Nodes, NumFailures >>

LeaderProcessAckSwitchToRF2_P1(n) ==
  /\ n \in DataNodes
  /\ Role[n] = "leader"
  /\ ReplicationFactor[n] = 1
  /\ Term[n] > 0
  /\ \E i \in 1..Len(Messages) :
       LET r == Messages[i] IN
         /\ r.rpc_type = "SwitchToRF2 P1 Resp"
         /\ r.destination = n
         /\ r.source = OtherDataNode(n)
         /\ r.term > Term[n]
  /\ LET r == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "SwitchToRF2 P1 Resp"
                        /\ Messages[j].destination = n
                        /\ Messages[j].source = OtherDataNode(n)
                        /\ Messages[j].term > Term[n]]
         newTermN == r.term
         newRFN   == r.RF
         newCi    == LeMdMin(LeMdMax(r.logged_idx, CommittedIdx[n]), LoggedIdx[n])
         msgE == [
           source        |-> n,
           destination   |-> CHOOSE e \in ElectorNodes : TRUE,
           rpc_type      |-> "SwitchToRF2 P2",
           committed_idx |-> newCi,
           term          |-> newTermN,
           RF            |-> newRFN
         ]
         idx == CHOOSE k \in 1..Len(Messages) : Messages[k] = r
     IN
        /\ Term'              = [Term EXCEPT ![n] = newTermN]
        /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = newRFN]
        /\ Role'              = [Role EXCEPT ![n] = "leader"]
        /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = n]
        /\ CommittedIdx'      = [CommittedIdx EXCEPT ![n] = newCi]
        /\ Messages'          = Append(RemoveAt(Messages, idx), msgE)
        /\ NumFailures'       = 0
        /\ ActivatedNode' = n
        /\ UNCHANGED << LoggedIdx, Nodes, DmlLog >>

ElectorAckSwitchToRF2_P2(e) ==
  /\ e \in ElectorNodes
  /\ \E i \in 1..Len(Messages) :
       LET m == Messages[i] IN
         /\ m.rpc_type = "SwitchToRF2 P2"
         /\ m.destination = e
         /\ m.term > Term[e]
  /\ LET m == Messages[CHOOSE j \in 1..Len(Messages) :
                        /\ Messages[j].rpc_type = "SwitchToRF2 P2"
                        /\ Messages[j].destination = e
                        /\ Messages[j].term > Term[e]]
         ciHigh == (m.committed_idx.term  >  CommittedIdx[e].term) \/
                   (m.committed_idx.term  =  CommittedIdx[e].term /\
                    m.committed_idx.index >  CommittedIdx[e].index)
         newTermE == m.term
         newRFE   == m.RF
         newCIE   == IF ciHigh THEN m.committed_idx ELSE CommittedIdx[e]
         idx == CHOOSE k \in 1..Len(Messages) : Messages[k] = m
     IN
       /\ Term'              = [Term EXCEPT ![e] = newTermE]
       /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![e] = newRFE]
       /\ CurrentLeader'     = [CurrentLeader EXCEPT ![e] = m.source]
       /\ CommittedIdx'      = [CommittedIdx EXCEPT ![e] = newCIE]
       /\ Messages'          = RemoveAt(Messages, idx)
       /\ ActivatedNode'     = e
       /\ UNCHANGED << LoggedIdx, Role, Nodes, NumFailures, DmlLog >>

(***************************************************************************)
(* Environment steps                                                       *)
(***************************************************************************)
 DropMsg ==
   /\ FALSE
   /\ Len(Messages) > 0
   /\ \E i \in 1..Len(Messages) :
        /\ Messages' = RemoveAt(Messages, i)
        /\ ActivatedNode' = "environment"
        /\ UNCHANGED << LoggedIdx, CommittedIdx, Term, Role, Nodes,
                        ReplicationFactor, NumFailures, CurrentLeader, DmlLog >>

DupMsg ==
  /\ Len(Messages) > 0
  /\ \E i \in 1..Len(Messages) :
       /\ Messages' = Append(Messages, Messages[i])
       /\ ActivatedNode' = "environment"
       /\ UNCHANGED << LoggedIdx, CommittedIdx, Term, Role, Nodes,
                       ReplicationFactor, NumFailures, CurrentLeader, DmlLog >>

HardReset ==
    /\ FALSE
    /\ NumFailures = 0
    /\ \E n \in Nodes :
        IF n \in DataNodes THEN
            /\ LoggedIdx'    = [LoggedIdx EXCEPT ![n] = [term |-> 0, index |-> 0]]
            /\ CommittedIdx' = [CommittedIdx EXCEPT ![n] = [term |-> 0, index |-> 0]]
            /\ DmlLog'       = [DmlLog EXCEPT ![n] = <<>>]
            /\ Term'         = [Term EXCEPT ![n] = 0]
            /\ Role'         = [Role EXCEPT ![n] = "follower"]
            /\ NumFailures'  = 1
            /\ CurrentLeader' =
                [CurrentLeader EXCEPT ![n] = OtherDataNode(n)]
            /\ ReplicationFactor' =
                [ReplicationFactor EXCEPT ![n] = 2]
            /\ ActivatedNode' = n
            /\ UNCHANGED << Nodes, Messages >>
        ELSE
            /\ Term' = [Term EXCEPT ![n] = 0]
            /\ Role' = [Role EXCEPT ![n] = "elector"]
            /\ NumFailures' = 1
            /\ CommittedIdx' = 
                [CommittedIdx EXCEPT ![n] = [term |-> 0, index |-> 0]]
            /\ ReplicationFactor' =
                [ReplicationFactor EXCEPT ![n] = 2]
            /\ CurrentLeader' =
                [CurrentLeader EXCEPT ![n] = "unknown"]
            /\ ActivatedNode' = n
            /\ UNCHANGED << Nodes, Messages, LoggedIdx, DmlLog >>

HardResetWipeMsgs ==
  /\ FALSE
  /\ NumFailures = 0
  /\ \E n \in Nodes :
       LET msgsNoN == KeepNotDest(Messages, n)
       IN
         IF n \in DataNodes THEN
           /\ LoggedIdx'         = [LoggedIdx EXCEPT ![n] = [term |-> 0, index |-> 0]]
           /\ CommittedIdx'      = [CommittedIdx EXCEPT ![n] = [term |-> 0, index |-> 0]]
           /\ DmlLog'            = [DmlLog EXCEPT ![n] = <<>>]
           /\ Term'              = [Term EXCEPT ![n] = 0]
           /\ Role'              = [Role EXCEPT ![n] = "follower"]
           /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = 2]
           /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = OtherDataNode(n)]
           /\ NumFailures'       = 1
           /\ Messages'          = msgsNoN
           /\ ActivatedNode'     = n
           /\ UNCHANGED << Nodes >>
         ELSE
           /\ Term'              = [Term EXCEPT ![n] = 0]
           /\ Role'              = [Role EXCEPT ![n] = "elector"]
           /\ ReplicationFactor' = [ReplicationFactor EXCEPT ![n] = 2]
           /\ CurrentLeader'     = [CurrentLeader EXCEPT ![n] = "unknown"]
           /\ CommittedIdx'      = [CommittedIdx EXCEPT ![n] = [term |-> 0, index |-> 0]]
           /\ NumFailures'       = 1
           /\ Messages'          = msgsNoN
           /\ ActivatedNode'     = n
           /\ UNCHANGED << Nodes, LoggedIdx, DmlLog >>


(***************************************************************************)
(* Next / Spec                                                             *)
(***************************************************************************)
Vars == << LoggedIdx, CommittedIdx, Term, Role, Nodes,
            ActivatedNode,
           ReplicationFactor, NumFailures, CurrentLeader, DmlLog, Messages >>

Next ==
    \/ \E n \in DataNodes              : FollowerSendInitWorkload(n)
    \/ \E n \in DataNodes              : FollowerAckInitWorkload(n)
    \/ \E n \in DataNodes              : CandidateProcessAckInitWorkload(n)

    \/ \E n \in DataNodes, d \in {0,1} : LeaderSendAE_RF1(n,d)
    \/ \E e \in ElectorNodes           : ElectorAckAE_RF1(e)
    \/ \E n \in DataNodes              : LeaderProcessAckAE_RF1(n)
    
    \/ \E n \in DataNodes, d \in {0,1} : LeaderSendAE_RF2(n,d)
    \/ \E f \in DataNodes              : FollowerAckAE_RF2(f)
    \/ \E e \in ElectorNodes           : ElectorProcessAE_RF2(e)
    \/ \E n \in DataNodes              : LeaderProcessAckAE_RF2(n)
    
    \/ \E n \in DataNodes              : LeaderSendSwitchToRF1(n)
    \/ \E e \in ElectorNodes           : ElectorAckSwitchToRF1(e)
    \/ \E n \in DataNodes              : LeaderProcessSwitchToRF1(n)
    
    \/ \E n \in DataNodes              : FollowerSendSwitchToRF1Leader(n)
    \/ \E e \in ElectorNodes           : ElectorAckSwitchToRF1Leader(e)
    \/ \E n \in DataNodes              : CandidateProcessSwitchToRF1Leader(n)
    
    \/ \E n \in DataNodes, d \in {0,1} : LeaderSendSwitchToRF2_P1(n,d)
    \/ \E f \in DataNodes              : FollowerAckSwitchToRF2_P1(f)
    \/ \E n \in DataNodes              : LeaderProcessAckSwitchToRF2_P1(n)
    \/ \E e \in ElectorNodes           : ElectorAckSwitchToRF2_P2(e)
    
    \/ DropMsg
    \/ DupMsg
    \/ HardReset
    \/ HardResetWipeMsgs

Spec == Init /\ [][Next]_Vars

AllInvariants ==
    /\ TypeOk
    /\ StructureOk
    /\ MiscOk
    /\ LeaderSafety
    /\ ReplicationFactorSafety
    /\ LogMatching
    /\ LeaderCompleteness
    /\ StateMachineSafety

AllProperties == [] [LeaderAppendOnly]_Vars


(***************************************************************************)
(* State Constraints                                                       *)
(***************************************************************************)
StateConstraint ==
    \A n \in DataNodes :
        LoggedIdx[n].index < 3 /\ CommittedIdx[n].index < 3


=============================================================================
\* Modification History
\* Last modified Sat Sep 06 17:27:41 PDT 2025 by aknen
\* Created Thu Aug 28 19:55:21 PDT 2025 by aknen




