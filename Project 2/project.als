
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
    Leader.lnxt.Node in Member
}

fact {
    /* non-member nodes are not allowed to queue in more than one member queue
        at a time. */
    all m1, m2: Member | 
        m1 != m2 => no (m1.qnxt.Node & m2.qnxt.Node)
}