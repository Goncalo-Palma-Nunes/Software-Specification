module Ex1


sig Node {
    var outbox: set Msg,
}

var sig Member in Node {
    var nxt: lone Member,
    var qnxt : Node -> lone Node
}

var one sig Leader in Member {
    var lnxt: Node -> lone Node
}

var sig LQueue in Member {

}

sig Msg {
  sndr: Node, 
  var rcvrs: set Node 
}

var sig SentMsg, SendingMsg, PendingMsg in Msg {}


fact MemberRing {
    /* From one member you can get to all others 
    through the next pointer */
    all m: Member | Member in m.*nxt
}

fact LeaderCandidatesAreMembers {
    /* all nodes in the leader queue are members */
    // Node.(~(Leader.lnxt)) = LQueue && Leader !in LQueue
	Leader.lnxt.Node = LQueue //&& Leader !in LQueue
}

fact allRoadsLeadtoLeader {
	/* Leader is always reached by following the leader queue (order)*/
	all lq: LQueue | Leader in lq.^(Leader.lnxt)
}


fact indianLeaderQueue {
	/* Reachable queue members only have one arrow pointing at them */
	all m: Member.(Leader.lnxt) | one (Leader.lnxt).m
}

fact noLoopsLeaderQueue {
	/* Member cannot reach self following the queue (order + no repetition)*/
	all m: Member | m !in m.^(Leader.lnxt)
}

fact allRoadsLeadtoMember {
	/* Member is always reached by following the member queue (order)*/
	all n: Node, m: Member | n in m.qnxt.Node implies m in n.^(m.qnxt)
}


fact indianMemberQueue {
	/* Reachable queue nodes only have one arrow pointing at them */
	all n: Node.(Member.qnxt) | one (Member.qnxt).n
}

fact noLoopsMemberQueue {
	/* Node cannot reach self following the queue (order)*/
	all n: Node | n !in n.^(Member.qnxt)
}

fact NoMemberInQueue {
    /* no member in a member queue*/
	no (Member.qnxt.Node & Member)
}


fact {
    /* non-member nodes are not allowed to queue in more than one member queue
        at a time. */
    all m1, m2: Member | 
        m1 != m2 => no (m1.qnxt.Node & m2.qnxt.Node)
}

fact {
    /* A message is considered sent when broadcasting process 
        has terminated (the leader received back the message) */
    all msg: SentMsg | msg.sndr in msg.rcvrs and some (msg.rcvrs - msg.sndr)

    /* if the sender is in the receiver set, then the message
        already cycled through the ring */
}

fact {
    /* If a message is in the sent state, then it has left
    everyone's outbox */
    all msg: SentMsg, node: Node | msg !in node.outbox
}

fact {
    /* A message is considered pending, if the broadcasting
        process has not yet started. In other words, the message
        hasn't left the leader and no one has received it yet. */
    all msg: PendingMsg | no msg.rcvrs
}

fact {
    /* A message can't be in more than one state at once */
    (no (SentMsg & SendingMsg))
    and 
    (no (SentMsg & PendingMsg))
    and
    (no (SendingMsg & PendingMsg))
}

fact {
    /* A message must be in some state */
    Msg = (SentMsg + SendingMsg + PendingMsg)
}

fact {
    /* If a node has a sending message in the outbox,
    then it is a member */
    all n: Node | some (n.outbox & SendingMsg) => n in Member
}

fact {
    /* A message is considered sending, if the broadcasting
        process has started, but not yet finished. In other words,
        the message has left the leader, but it hasn't received it
        back yet. */
    all msg: SendingMsg | (some msg.rcvrs) && (msg.sndr !in msg.rcvrs)
}


fact {
    /* A node can't be outside the ring if it has messages in the
    sending state */
    all msg: SendingMsg | msg.sndr in Member
}

fact {
    /* Sending messages are in someone's outbox */
    all msg: SendingMsg | some n: Node | 
        (n.outbox = n.outbox + msg) && (msg.sndr != n)
}

fact {
    /* the outbox can only contain pending messages belonging
    to the node itself or sending messages belonging to other nodes */
    all n: Node | 
        all msg: Msg | msg in n.outbox implies
            (msg in (n.(~sndr) & PendingMsg))
            or 
            (msg in (Node.(~sndr) & SendingMsg))

}

fact {
    /* Messages are in, at most, one outbox */
    //all msg: Msg | lone outbox.msg
    all msg: Msg | lone (msg.(~outbox) & Node)
}

fact PendingMsgsNotReceived {
    /* If a message is pending, it shouldn't be in anyone's outbox 
    except the sender's */
    all msg: PendingMsg | msg !in (Member - msg.sndr).outbox
}

fact PendingMsgInSndrOutbox {
    /* If a message is pending, it should be in the sender's outbox */
    all msg: PendingMsg | msg in msg.sndr.outbox
}


pred nonMembersQueued {
    all n: Node | n !in Member => one m: Member | n in m.qnxt.Node
}

pred someMessageEach {
	some SentMsg && some SendingMsg && some PendingMsg 
}

fun visQueueNext[]: Node -> lone Node {
	Member.qnxt
}

fun visLeaderNext[]: Node -> lone Node {
	Leader.lnxt
}

// Ex 1.2.1 and 1.2.2 (Generates multiple configurations)
run {#Node=5 && #Member=2 && (#Member.qnxt.Member>1) && (some LQueue) && someMessageEach} for 5
