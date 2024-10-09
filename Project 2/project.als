
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