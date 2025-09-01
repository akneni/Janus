# What is Janus
Janus is a practical consensus algorithm inspired by Raft. The key distinction is that it provides all of raft's safety guarantees while only requiring 2 of the 3 nodes to maintain a full raft log (and datafiles for the underlying database). 

# Should I consider Janus
Janus requires 1/3 less hardware and 1/2 less bandwidth than other common consensus protocols such as Raft and Paxos. 
However, it is complex to reason about and even more so to implement. Additionally, a failed node is not considered to be online until it is brought back online *and* catches up with the leader node. This means that node recovery will take meaningfully longer when using Janus than when using Raft/Paxos. 

# Proof Assumptions
Fault Model: crash-recover
Timing Model: Asynchronous Timing Model

# Safety Properties
1) Leader Safety: There will be one or fewer leaders uring any given term. 
2) Replication factor safety: There will only ever be a single replication factor per term. 
3) Leader Append-Only: A leader never overwrites or deletes entries in its log, it will only append to its own log. 
4) Log Matching Property: If the logs on two nodes have a log entry with the same index and same term, then all log entries up to that point must be identical. 
5) Leader Completeness Property: If a log entry is committed in term $t$, then that log entry will be present in all the leaders terms coming after term $t$. 
6) State Machine Safety: If a node has committed a log entry at a given index, no other node will ever apply a different log entry for the same index.