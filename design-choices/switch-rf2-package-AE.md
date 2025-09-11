# Switch RF 2 Optimization
There are two ways we can make the cluster switch to RF 2. While a typical 2-phase protocol may be the go-to answer here, I believe there are some better options. 


## 2 Phase Switch
1) The leader sends `(switch-rf-2, logged-idx, term)`
2) The follower increments its term, changes its RF to 2, and responds with `(ok)`
3) The leader receives `ok` and increments its term, and then changes its RF to 2. It then sends `(switch-rf-2_post-commit, term)` to the follower and the elector. 

- 1.5 round trips

## 1 Phase Switch/Optimistic Switch
1) The leader increments its term, changes RF to 2 and sends sends `(switch-rf-2, logged-idx, term)` to the follower and elector. Immediately after, without receiving any feedback from its followers, it assumes that this succeeded and will start sending AppendEntriesRF2. 

- 0.5 round trips. 
- If it turns our that the follower isn't caught up, then it will increment its term but keep its RF at 1. The leader will then have to do a switch to RF 1, and then a switch to RF 2 again. Only if the follower accepts this will the entire cluster be switched to RF 2. 
- Message reordering causes some problems here. If the leader sends an AppendEntriesRF2 request to the follower immediately after the SwitchRF2 RPC, and the append entries arrives first, then the leader will have to do more work retransmitting the append entries RPC. 
- While we could likely use this and uphold all safety properties and get better performance in the normal case (when the follower actually is caught up), this increases the likelihood of there being unconsidered edge cases, and it's harder to reason about which often leads to implementation bugs. 

## Switch RF 2 w packaged AppendEntries
1) The leader sends `(switch-rf-2, logged-idx, term, DML-log-tail)` to the follower.
2) The follower responds with `ok` if its own log + the DML log tail it received allow it to get up to `LoggedIdx` without any holes. The follower will also increment its term and set its replication factor to 2. 
3) When the leader receives `ok`, it will increments its term, set its RF to 2, and send `(switch-rf-2_post-commit, term)` to the elector. (If necessary, it can also just send another AppendEntriesRF2 RPC to the follower at this point).

- 0 round trips. Since the DML log tail can contain new logs that even the caught-up follower hasn't seen yet, this effectively doubles as an append entries request. So, we wasted 0 network trips switching to RF 2. 
- If the follower isn't caught up for some reason, then retrying the switch to RF 2 is much cheaper than in the 1 Phase Switch/Optimistic Switch. 


## Conclusion
- **Switch RF 2 w packaged AppendEntries:** This is the one I decided to use in the end. It gives us the safety (and simplicity) of a two phase protocol without actually wasting any network trips as there isn't a single message that isn't also performing work to advance state of the cluster. 
- **2 Phase Switch:** This was my first idea for implementing this state transition. It's conceptually identical to the 2PC protocol, is easy to prove, and is a solid (but boring) option. 
- **1 Phase Switch/Optimistic Switch:** This was my first attempt at creating a more optimal protocol than a simple 2 phase protocol. It does significantly reduce the number of round trips, and the increased cost of failing and retrying SwitchRF2 is not important since SwitchRF2 should only happen when the leader is sure that the follower has caught up. However, the increased complexity (which inevitable leads to increased implementation bugs), decreased resistance to message reordering makes this the least viable option. 