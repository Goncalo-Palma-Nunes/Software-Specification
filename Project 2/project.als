
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
    all m1, m2: Member | m1 in m2.^nxt

    // TODO - without forall?
}

fact LeaderCandidatesAreMembers {
    /* all nodes in the leader queue are members */
    all n: Node | n !in Member implies n !in Leader.lnxt.Node

    // Leader.lnxt.Node in Member
    // TODO - how do we relate it to LQueue?
}

fact NoMemberInQueue {
    /* no member is in the queue of another member */
    // all m: Member | no m.qnxt.Member

    all m: Member | no (m.qnxt.Node & Member)

    // (Member.qnxt.Node & Member) ?????
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
        back  yet. */
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

pred oneMemberInLQueue {
    one m: Member | m in LQueue
}

pred addQueue[n: Node, m: Member] {
    // Pre-conditions
    n !in Member
    n !in m.qnxt.Node

    // Post-conditions
    m.qnxt' = m.qnxt + (m -> n)

    // Frame
    n !in Member
    m in Member


    // TODO - Perguntar ao fragoso
}

pred promoteMember[n: Node, m: Member] {
    // Pre-conditions
    n !in Member
    n in m.qnxt.Node

    // Post-conditions
    m.qnxt' = m.qnxt - (m -> n)
    n in Member
    n.nxt' = m.nxt
    m.nxt' = n

    // Frame
    m in Member
}

pred dropQueue[n: Node, m: Member] {
    // Pre-conditions
    n !in Member
    n in m.qnxt.Node

    // Post-conditions
    m.qnxt' = m.qnxt - (m -> n)

    // Frame
    n !in Member
    m in Member
}

pred QueueLeader[n: Node] {
    // Pre-conditions
    n in Member
    n !in Leader.lnxt.Node

    // Post-conditions
    Leader.lnxt' = Leader.lnxt + (Leader -> n)
    n in LQueue
    n in Leader.lnxt.Node

    // Frame
}

pred LeaveMemberRing[n: Node] {
    // Pre-conditions
    n in Member
    n !in Leader

    // Post-conditions
    n.nxt.qnxt' = n.nxt.qnxt + n.qnxt   // TODO - what if it is a single node ring?
    n !in Member

    // Frame
}

pred PromoteLeader[n: Node, l: Leader] {
    // Pre-conditions
    n in Member
    n in Leader.lnxt.Node

    // Post-conditions
    n in Leader
    n !in LQueue
    n.lnxt' = l.lnxt - (l -> n)
    l !in Leader

    // Frame
}

run {#Node=3 && #Member=2 && nonMembersQueued && oneMemberInLQueue} for 5
