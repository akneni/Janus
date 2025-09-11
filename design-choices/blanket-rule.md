# Blanket Rule
- This is a rule that always applies. Because of this, they make the protocol slightly easier to reason about. 

## Term Progression
- Unlike raft the node that initiates a term change is not the first node to update their term. The initiator node (a node trying to make an update to the term, replication factor, or leader), must fir request permission to do this from another node (which node depends on the scenario). This receiving node is the first one to update its term, replication factor, and/or leader. The initiator node will only update these fields after it receives an ack from the other node. 

## Term, RF, leader handling 
- Every message contains `(term, RF, leader-id)`. 
- Whenever a node receives a message with term lower than it's own, it ignores it. 
- Whenever a node receives a message with term equal to its own, it processes it. 
- Whenever a node receives a message with term greater than its own, it sets its term to the message's term and sets its RF to the messages's RF. It will then process the message.