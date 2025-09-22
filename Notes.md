# Overview
- This is a protocol that can use 2 full nodes to tolerate 1 failure or 3 full nodes to tolerate 2 (non-simultaneous) failures. 

## Cluster States
The entire cluster can be in one of three states (defined by the membership from the viewpoint of the leader with the highest term). 
1) Stable State (RF3): Elector is not part of the membership yet; 3 nodes act as classic raft. 
2) Tentative State (RF2): One follower is assumed to be down, and we've added the elector to the cluster. The leader still needs an ACK from the follower and the elector to commit something. 
3) Solo State (RF3): The other follower has failed, so the leader does two membership changes to remove both of the other nodes from the cluster. Now, the leader only needs an ACK from the elector to commit a log entry. 

Note that the bullet points above only discuss the followers failing. If a leader fails, the cluster just does a leader election, and the new leader proceeds as is described above. 


## Append Entries
This doesn't change: the leader just needs an ACK from the majority of followers/electors. 

## Leader Election
This doesn't change: the candidate just needs an ACK from the majority of followers/electors. 

## Change Membership
- This spec only models single server membership changes. 
- Note that a membership change is modeled as a special Append Entries RPC.
- Since it's a special version of the Append Entires request, only leaders can send this RPC. If a follower wants to do a membership change, it will have to do a leader election and then one a membership change.

## What If?
What if a follower/elector receives a membership change request? 
- It will ignore the membership change request and process the vote request (so it treats the membership change just like an append entries). 