# This is outdated. The only up-to-date specification is the formal TLA+ spec

# Overview
While not a formal specification, this should give you the general idea. 
A Janus cluster is comprised of 3 nodes, 2 of which are data nodes and one of which is an elector. 
All changes to the underlying structure (we'll call these changes DMLs), will be preserved as long as there is no more than a single failure. 


## State
This is the state that each node will maintain. 
- `DML Log`: Equivalent to a raft log: it is a (mostly) append only log of DMLs. (not maintained by elector node)
- `Logged Index`: The index and term of the last log entry that was appended to the janus log. (not maintained by elector node)
- `Committed Index`: The index and term of the last log entry appended to the janus log that is confirmed to be committed. (not maintained by elector node)
- `Term`: This is a logical unit of time for which there is at most 1 leader.  
- `Replication Factor`: This is the number of notes that the data is replicated on. This will always be either 1 or 2 for a three node cluster. 
- `Role`: This is the role of the node. This can be `leader, follower, candidate, elector`. 
- `CurrentLeader`: This is the id of the leader node. 

## Rules of Thumb
- Receiver First Semantics: Whenever a node proposes a change to leadership, term, or replication factor, it will `not` update its term first. It will simply send a request to the appropriate node. When the receiving node gets this message, it will be the first one to update the term/RF/leader. It will send an ack back to the node that initiated this change, and only then will that node update its term/RF/leader.

## RPCs
Unfortunately, Janus is a little more complicated than Raft or Paxos: there are 5 RPCs in total. 
- `AppendEntries RF 2`
    - As the name suggests, it can only be made when the leader's value for `Replication Factor` is 2. 
    - After the leader gets a DML from a client, it will insert the DML into its DML log, and update its logged index. 
    - The leader will send a the message (`Term`, `Logged Index`, `DML`) to the follower.
    - The leader will send a the message (`Term`) to the elector.
    - The leader only needs to receive an acknowledgement from the follower to consider this DML to be committed. 
    - After this, the leader will update its committed index and will respond with `OK` to the client. 

- `AppendEntries RF 1`
    - As the name suggests, it can only be made when the leader's value for `Replication Factor` is 1, meaning that the follower is assumed to be down.  
    - After the leader gets a DML from a client, it will insert the DML into its DML log, and update its logged index.
    - The leader will send a the message (`Term`, `Logged Index`) to the elector.
    - The leader needs to receive an acknowledgement from the elector to consider this DML to be committed. 
    - After this, the leader will update its committed index and will respond with `OK` to the client. 

- `Switch to RF 1`
    - This is an RPC made by a node that thinks it's the leader when it's current replication factor is 2, and it cannot reach the follower. 
    - The leader simply sends (`Term`) to the elector. 
    - Whenever an elector receives this RPC from a node, it responds with (`Term`, `True/False`). It will respond with true if the the RPC's message has a higher term, or if the message ahs the same term as the elector, and the elector believes that the node is actually the leader. If it responds with true, then it updates its replication factor to be 1. 
    - After the node receives the response from the elector, it will do one of two things. 
        - True
            - The node will change its replication factor to 1, increment its term, and continue on with normal operation. 
        - False
            - The leader will update it's term to match the one received from the elector, will change it's role to `follower`. 

- `Switch to RF 1 & Become Leader`
    - This is an RPC made by a node that thinks it's the follower when it's current replication factor is 2, and it has not heard from the leader in T ms (where T is some timeout in milliseconds). 
    - This node changes its role to `candidate`, and sends (`Term`, `Logged Index`) to the elector. 
    - Whenever an elector receives this RPC from a node, it responds with (`Term`, `True/False`). It will respond with true only if the elector hasn't heard from the leader in at least T ms. If it responds with true, then it updates its `Logged Index` to equal the one sent in the node's RPC, updates its `CurrentLeader` to be this node, and updates it's replication factor to be 1. 
    - After the node receives the response from the elector, it will do one of two things. 
        - True
            - The node will change its replication factor to 1, increment its term, and change its role to `leader`.
        - False
            - The node will update it's term to match the one received from the elector, will change it's role to `follower`. 

- `Switch to RF 2`
    - This is an RPC made by the leader when the replication factor is 1, and it detects that the other data node is up and has ensured that the other node's DML log is caught up with it's own DML log (up to `Logged Index`, not just `Committed Index`). 
    - It increments its term, then sends (`Committed Index`, `Term`) to the elector and follower and waits for a `OK` response from both. 
    - The follower will respond with `OK` if it really has caught up with the leader. If so, then it will also update its term. Same is true for the elector. 
    - After this, the leader updates its own replication factor to 2, and updates the term. 