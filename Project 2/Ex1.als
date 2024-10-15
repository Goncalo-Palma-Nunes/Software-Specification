
sig Node {

}

sig Member in Node {
    nxt: lone Member,
    qnxt : Node -> lone Node,
    outbox: set Msg
}

one sig Leader in Member {
    lnxt: Node -> lone Node
}

sig LQueue in Member {

}

abstract sig Msg {
   sndr: Node,
   rcvrs: set Node
}

sig SentMsg, SendingMsg, PendingMsg extends Msg {}


fact MemberRing {
    /* From one member you can get to all others 
    through the next pointer */
    all m: Member | Member in m.*nxt
    // TODO - without forall?
}

fact LeaderCandidatesAreMembers {
    /* all nodes in the leader queue are members */
    // Node.(~(Leader.lnxt)) = LQueue && Leader !in LQueue
	Leader.lnxt.Node = LQueue && Leader !in LQueue
}

fact allRoadsLeadtoLeader {
	/* Leader is always reached by following the leader queue (order)*/
	all lq: LQueue | Leader in lq.^(Leader.lnxt)
	// TODO - without forall ?
}

fact oneLeaderQueue {
	/* There can only be a single leader queue */
	one Leader.lnxt.Leader
}

fact allRoadsLeadtoMember {
	/* Member is always reached by following the member queue (order)*/
	all n: Node, m: Member | n in m.qnxt.Node implies m in n.^(m.qnxt)
	// TODO - without forall ?
}

fact oneMemberQueue {
	/* Only a single member queue per member */
	all m: Member | lone m.qnxt.m
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
    all msg: SentMsg | msg.sndr in msg.rcvrs

    /* if the sender is in the receiver set, then the message
        already cycled through the ring */
}

fact {
    /* A message is considered pending, if the broadcasting
        process has not yet started. In other words, the message
        hasn't left the leader and no one has received it yet. */
    all msg: PendingMsg | no msg.rcvrs
}

fact {
    /* A message is considered sending, if the broadcasting
        process has started, but not yet finished. In other words,
        the message has left the leader, but it hasn't received it
        back yet. */
    all msg: SendingMsg | (some msg.rcvrs) && (msg.sndr !in msg.rcvrs)
}

assert PendingMsgsNotReceived {
    /* If a message is sending, it shouldn't be in anyone's outbox */
    all msg: PendingMsg | msg !in Member.outbox

    // TODO - Isto talvez seja útil para dar debug com checks? Não sei...
    // Será que fazia sentido ser um facto?
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

run {#Node=5 && #Member=2 && #Member.qnxt.Member>1 && some LQueue && someMessageEach } for 5
