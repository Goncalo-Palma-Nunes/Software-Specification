module Ex2
open Ex1

pred init[] {
    Member = Leader
    Msg = PendingMsg
    no Node.qnxt
}

pred stutter[] {
    Member' = Member
    nxt' = nxt
    qnxt' = qnxt
    Leader' = Leader
    lnxt' = lnxt
    LQueue' = LQueue
    Msg' = Msg

    // TODO - do we need all of this?
}

pred trans[] {
    stutter[]
}

pred system[] {
    init[]
    trans[]
}