# Fix for Error 1
Consider the follower behavior
1) All nodes are at term 5, with d1 being the follower, d2 being the leader, and e1 being the elector. 
2) d2 sends the SwitchRF1 RPC to e1. 
3) d1 sends the SwitchRF1BecomeLeader RPC to e1. 
4) d2's message reaches e1 first. e1 accepts, updates its term to 6, current_leader to d2, and responds with OK. 
5) d2 gets this ack, and updates itself to be leader in term 6. 
6) e1 hard crashes (looses all state) and immediately comes back online. 
7) e1 gets d1's SwitchRF1BecomeLeader message. Since it has a higher term (term 5). e1 accepts, updates its term to 6, current_leader to d1, and responds with OK.  
8) d1 gets this ack, and updates itself to be leader in term 6. 
**Split Brain!**

## Solution 1
Simply model a hard reset as wiping all state from the node that was reset *and* delete all messages whose destination was the crashed node. 
Practically, this will work in almost all real world scenarios, but there is a very small edge case in which this model of a hard reset doesn't hold true: if a process is bound to port XXXX listening for UDP packets, fails, is immediately restarted, and binds to the same XXXX port, *only* the UDP packets in the kernel's buffer will be dropped. All UDP packets destined for the previous process that are still in transit over the network will be delivered to the new process (even though they were intended for the old process). 
Since I'd rather not force implementations of Janus to use TCP based network protocols, this solution doesn't work. 

## Solution 2
Just make it so that an elector doesn't respond to SwitchRFXX commands when its term is zero. 
This works in theory and in practice, but it breaks the blanket rule (a node that receives a message of a higher term will update its term and RF to those specified in the message). Janus is already filled with IF, THEN, ELSE logic, so I'd rather not introduce an exception to the one rule that's constant across all RPCs. 

## Solution 3
Make each node ID a random integer generated on startup. 
This is a much more elegant solution than solution 2, but it also has its own edge cases. Firstly, if the `UUID` a 64 bit integer, there is a 1 in (1.9 * 10^19) chance of a hash collision (making the error discussed here still possible), And that probability is only for 2 nodes: the chances of a hash collision increase with the number of notes. If we want to be extremely sure, we could make the node ID 256 bits (if its good enough for SHA 256, its good enough for me). This does add extra implementation complexity and extra overhead, which I want to reduce as much as possible. 

## Conclusion
Since Term 0 is already a "special term" (in term zero, we cannot guarantee liveness with even a single failure for example), it seems fine that term 0 can also be an exception to the blanket rule. 
Thus, I'm going to go with solution 2. 