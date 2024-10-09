
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


fact NoMembersInQueue {
    // all m: Member | no n: m.qnxt.Node | n !in Member
    Member.qnxt.Node !in Member
}

fact LeaderCandidatesAreMembers {
    /* all nodes in the leader queue are members */
    Leader.lnxt.Node in LQueue

    // TODO - how do we relate it to LQueue?
}

fact {
    /* non-member nodes are not allowed to queue in more than one member queue
        at a time. */
    all m1, m2: Member | 
        m1 != m2 => no (m1.qnxt.Node & m2.qnxt.Node)
}

fact MemberRing {
    /* From one member you can get to all others 
    through the next pointer */
    all m: Member | m in m.^nxt

    // TODO - without forall?
}