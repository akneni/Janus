----------------------------- MODULE LeaderSafety -----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLAPS

CONSTANT Node, Term

VARIABLE Role, TermOf, VotedFor

LeaderSafety ==
  \A t \in Term :
    \A l1, l2 \in Node :
      (Role[l1] = "leader" /\ TermOf[l1] = t /\ 
       Role[l2] = "leader" /\ TermOf[l2] = t) => l1 = l2

ASSUME NodeIsFinite == IsFiniteSet(Node)

(***************************************************************************)
(* Assumptions for Janus election rules                                    *)
(***************************************************************************)

(* Simplified: Each node votes for at most one candidate per term *)
VoteUniqueness ==
  \A n \in Node, t \in Term, c1, c2 \in Node :
    (VotedFor[n][t] = c1 /\ VotedFor[n][t] = c2) => c1 = c2

(* A leader must have votes from a majority *)
ElectionRestriction ==
  \A l \in Node, t \in Term :
    (Role[l] = "leader" /\ TermOf[l] = t) =>
      Cardinality({ n \in Node : VotedFor[n][t] = l }) > Cardinality(Node) \div 2

(* Two majorities must intersect *)
MajorityIntersection ==
  \A S1, S2 \in SUBSET Node :
    (Cardinality(S1) > Cardinality(Node) \div 2 /\
     Cardinality(S2) > Cardinality(Node) \div 2) =>
      \E n \in Node : n \in S1 /\ n \in S2

THEOREM LeaderSafetyThm ==
  ASSUME 
    \A n \in Node, t \in Term, c1, c2 \in Node : (VotedFor[n][t] = c1 /\ VotedFor[n][t] = c2) => c1 = c2,
    \A l \in Node, t \in Term :
      (Role[l] = "leader" /\ TermOf[l] = t) =>
        Cardinality({ n \in Node : VotedFor[n][t] = l }) > Cardinality(Node) \div 2,
    \A S1, S2 \in SUBSET Node :
      Cardinality(S1) > Cardinality(Node) \div 2 /\ Cardinality(S2) > Cardinality(Node) \div 2
      => (\E n \in Node : n \in S1 /\ n \in S2)
  PROVE LeaderSafety


(***************************************************************************)

THEOREM LeaderSafetyDetailed ==
  ASSUME VoteUniqueness, ElectionRestriction, MajorityIntersection
  PROVE  LeaderSafety
PROOF
  <1>1. SUFFICES ASSUME NEW t \in Term,
                        NEW l1 \in Node, NEW l2 \in Node,
                        Role[l1] = "leader", TermOf[l1] = t,
                        Role[l2] = "leader", TermOf[l2] = t
                 PROVE  l1 = l2
    BY DEF LeaderSafety
    
  <1>2. CASE l1 = l2
    BY <1>2
    
  <1>3. CASE l1 # l2
    <2>1. DEFINE Voters1 == { n \in Node : VotedFor[n][t] = l1 }
    <2>2. DEFINE Voters2 == { n \in Node : VotedFor[n][t] = l2 }
    
    <2>3. Cardinality(Voters1) > Cardinality(Node) \div 2
      BY <1>1, ElectionRestriction DEF ElectionRestriction
      
    <2>4. Cardinality(Voters2) > Cardinality(Node) \div 2
      BY <1>1, ElectionRestriction DEF ElectionRestriction
      
    <2>5. Voters1 \in SUBSET Node /\ Voters2 \in SUBSET Node
      OBVIOUS
      
    <2>6. \E n \in Node : n \in Voters1 /\ n \in Voters2
      BY <2>3, <2>4, <2>5, MajorityIntersection DEF MajorityIntersection
      
    <2>7. PICK voter \in Node : voter \in Voters1 /\ voter \in Voters2
      BY <2>6
      
    <2>8. VotedFor[voter][t] = l1 /\ VotedFor[voter][t] = l2
      BY <2>7 DEF Voters1, Voters2
      
    <2>9. l1 = l2
      BY <2>8, <1>3, VoteUniqueness DEF VoteUniqueness
      
    <2>10. FALSE
      BY <1>3, <2>9
      
    <2>11. QED
      BY <2>10
      
  <1>4. QED
    BY <1>2, <1>3

=============================================================================