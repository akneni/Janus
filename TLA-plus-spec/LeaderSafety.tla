----------------------------- MODULE LeaderSafety -----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Node, Term

VARIABLE Role, TermOf, VotedFor

(*
  Role[n] ∈ {"follower", "candidate", "leader"}
  TermOf[n] ∈ Term
  VotedFor[n][t] ∈ Node ∪ {"none"} -- who node n voted for in term t
*)

LeaderSafety ==
  \A t \in Term :
    Cardinality({ n \in Node : Role[n] = "leader" /\ TermOf[n] = t }) <= 1

ASSUME NodeIsFinite == IsFiniteSet(Node)

(***************************************************************************)
(* Assumptions for Janus/Raft-like election rules                           *)
(***************************************************************************)

VoteUniqueness ==
  \A n \in Node, t \in Term :
    \E! c \in Node \cup {"none"} : VotedFor[n][t] = c

ElectionRestriction ==
  \A l \in Node, t \in Term :
    Role[l] = "leader" /\ TermOf[l] = t =>
      Cardinality({ n \in Node : VotedFor[n][t] = l }) > Cardinality(Node) \div 2

MajorityIntersection ==
  \A S1, S2 \in SUBSET Node :
    Cardinality(S1) > Cardinality(Node) \div 2 /\
    Cardinality(S2) > Cardinality(Node) \div 2 =>
      S1 \cap S2 # {}

THEOREM LeaderSafetyThm ==
  ASSUME VoteUniqueness, ElectionRestriction, MajorityIntersection
  PROVE  LeaderSafety
PROOF
  TAKE t \in Term
  ASSUME NEW l1 \in Node, NEW l2 \in Node
  ASSUME H1: Role[l1] = "leader" /\ TermOf[l1] = t
  ASSUME H2: Role[l2] = "leader" /\ TermOf[l2] = t
  ASSUME H3: l1 # l2

  (*
     From H1, ElectionRestriction => set S1 of voters for l1 has majority
     From H2, ElectionRestriction => set S2 of voters for l2 has majority
     By MajorityIntersection => exists m in S1 ∩ S2
     So m voted for l1 and l2 in term t
     Contradicts VoteUniqueness
  *)

  DEFINE S1 == { n \in Node : VotedFor[n][t] = l1 }
  DEFINE S2 == { n \in Node : VotedFor[n][t] = l2 }

  HAVE Cardinality(S1) > Cardinality(Node) \div 2 BY ElectionRestriction, H1
  HAVE Cardinality(S2) > Cardinality(Node) \div 2 BY ElectionRestriction, H2
  HAVE \E m \in Node : m \in S1 /\ m \in S2 BY MajorityIntersection
  PICK m \in Node : m \in S1 /\ m \in S2

  HAVE VotedFor[m][t] = l1 /\ VotedFor[m][t] = l2 BY DEF S1, S2
  HAVE l1 = l2 BY VoteUniqueness
  CONTRADICTION WITH H3
  QED
=============================================================================
