![Banner](.assets/janus-banner.png)

# Overview
Janus is a practical consensus algorithm inspired by Raft. Unlike Raft, Janus can tolerate 2 failures with only 3 full nodes (nodes that maintain a raft log and the underlying database/application state); the fourth node acts as an arbiter in elections, holds < 100 bytes of state, and does not need to be send log entries during append entries requests. 

Note: this protocol can tolerate the failure of any one node or the failure of 2 data nodes. A failure of a data node and the elector will cause a loss of availability (not not a loss of consistency). Since the elector only maintains < 100 bytes of state, the assumption is that a failed elector can be replaced with a new one almost immediately. 


# Why Janus?
Janus requires 1/3 less hardware and 1/2 less bandwidth than other common consensus protocols such as Raft and Paxos. 
However, it is complex to reason about and even more so to implement. Additionally, a failed node is not considered to be online until it is brought back online *and* catches up with the leader node. This means that node recovery will take meaningfully longer when using Janus than when using Raft/Paxos. 

|                        | Paxos | Raft | Janus |
|------------------------|-------|------|-------|
| Strong Consistency  | ✅     | ✅    | ✅  |
| Hardware Requirements  | ❌     | ❌    | ✅  |
| Bandwidth Requirements  | ❌     | ❌    | ✅     |
| Ease of Implementation | ❌     | ✅    | ❌     |
| Failover Time | ✅     | ✅    | ❌     |


# Proof Assumptions
Fault Model: Crash Recover
Timing Model: Asynchronous Timing Model

# Safety Properties
1) Leader Safety: There will be one or fewer leaders uring any given term. 
2) Replication factor safety: There will only ever be a single replication factor per term. 
3) Leader Append-Only: A leader never overwrites or deletes entries in its log, it will only append to its own log. 
4) Log Matching Property: If the logs on two nodes have a log entry with the same index and same term, then all log entries up to that point must be identical. 
5) Leader Completeness Property: If a log entry is committed in term $t$, then that log entry will be present in all the leaders terms coming after term $t$. 
6) State Machine Safety: If a node has committed a log entry at a given index, no other node will ever apply a different log entry for the same index.