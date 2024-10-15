
sig Node {

}

var sig Member in Node {
    var nxt: lone Member,
    var qnxt : Node -> lone Node,
    outbox: set Msg
}

var one sig Leader in Member {
    var lnxt: Node -> lone Node
}

var sig LQueue in Member {

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

/* == DYNAMIC MODELLING == */

pred init[] {
	// Set of members consists only of the leader
	Member = Leader
	// All messages are in pending state
	PendingMsg = Msg
	// No node is queueing to become the leader
	no LQueue
}

pred stutter[] {
	// TODO - do we need to mention every attribute remains the same? doing it anyway...
	// Nodes
	Member' = Member
	nxt' = nxt
	qnxt' = qnxt
	
	Leader' = Leader
	lnxt' = lnxt
	LQueue' = LQueue
	// Messages
}

pred trans[] {
	stutter[]
}

pred addQueue[n: Node, m: Member] {
    // Pre-conditions
    n !in Member
    n !in m.qnxt.Node

    // Post-conditions
    m.qnxt' = m.qnxt + (n -> (m.qnxt.Node - Node.(m.lnxt)))

    // Frame
    Member' = Member
	nxt' = nxt
	all m: Member - m | m.qnxt' = m.qnxt 
	Leader' = Leader
	lnxt = lnxt

    // TODO - Perguntar ao fragoso
}

pred promoteMember[n: Node, m: Member] {
    // Pre-conditions
    n !in Member
    m.qnxt.m = n // n is head of m's queue

    // Post-conditions
	m.qnxt.m' = m.qnxt.n // m.qnxt' = (m.qnxt - (m.qnxt.n -> n) + (m.qnxt.n -> m)) - (n -> m)
    Member' = Member + n // TODO n in Member
    n.nxt' = m.nxt // TODO
    m.nxt' = n // TODO

    // Frame (nxt,qnxt,Member,LQueue,Leader,lnxt)
	all m: Member - m | m.qnxt' = m.qnxt && m.nxt' = m.nxt
	Leader' = Leader
	lnxt' = lnxt
}

pred dropQueue[n: Node, m: Member] {
    // Pre-conditions
    n !in Member
    n in m.qnxt.Node

    // Post-conditions
	(m.qnxt.n).(m.qnxt)' = n.m.qnxt //m.qnxt' = m.qnxt - (m->n)

    // Frame
    Member' = Member
	nxt' = nxt
	all m1: Member - m | m1.qnxt' = m.qnxt
	Leader' = Leader
	lnxt' = lnxt 
}

pred QueueLeader[n: Node] {
    // Pre-conditions
    n in Member
    n !in Leader.lnxt.Node

    // Post-conditions
    Leader.lnxt' = Leader.lnxt + (n -> (Leader.lnxt.Member - Member.(Leader.lnxt)))
	// ^^ points to last in queue ^^
    LQueue' = LQueue + n // n in LQueue

    // Frame
	Member' = Member
	Leader' = Leader
	nxt' = nxt
	qnxt' = qnxt
}

pred LeaveMemberRing[m: Member] {
    // Pre-conditions
    m !in Leader

    // Post-conditions
    m.nxt.qnxt' = m.nxt.qnxt + m.qnxt
	(nxt.m).nxt' = m.nxt // if its a single node ring this probably doesnt do anything 
	Member' = Member - m

    // Frame
	// TODO
}

pred PromoteLeader[m: Member, l: Leader] {
    // Pre-conditions
    m = Leader.(~(Leader.lnxt)) // m in Leader.lnxt.Node

    // Post-conditions
    Leader' = m
    LQueue' = LQueue - m
    m.lnxt' = l.lnxt - (m -> l)

    // Frame
	Member' = Member
	qnxt' = qnxt
	nxt' = nxt
}

fun visQueueNext[]: Node -> lone Node {
	Member.qnxt
}

fun visLeaderNext[]: Node -> lone Node {
	Leader.lnxt
}

run {#Node=5 && #Member=2 && #Member.qnxt.Member>1 && some LQueue && someMessageEach } for 5
