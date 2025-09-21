## Terminology
*Receiver-first semantics*: This is when the sender of the RPC that would update the term sends out the RPC without changing their own term, and the receiver of the RPC updates their term upon receiving this message. The sender will update their term once they receive the ACK from the receiver. This avoids the unnecessary term update (and and resulting failovers) if this RPC fails (since the term only gets incremented on a success). However, this is safe to use iff there is a single receiver to this term-update RPC. 

## Change Membership
This RPC has two main jobs (other than merely changing the membership for operational reasons)
1) If two data nodes are down, then we need to change the membership to the surviving data node and the elector. 
2) When we detect that the data nodes have gotten back up, we want to change the membership back to the full cluster. 

In scenario 1 above, it would be best (implementation wise) to use *receiver-first semantics* to update the term. However, for the sake of understandability of the spec, I am going to use sender-first semantics for the entire algorithm. 