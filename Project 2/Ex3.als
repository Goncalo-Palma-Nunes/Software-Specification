module Ex3
open Ex2

pred Valid[] {
    always (
        (all m: Member | Member in m.*nxt)
        and
        (Leader.lnxt.Node = LQueue)
        and
        (all lq: LQueue | Leader in lq.^(Leader.lnxt))
        and
        (all m: Member.(Leader.lnxt) | one (Leader.lnxt).m)
        and
        (all m: Member | m !in m.^(Leader.lnxt))
        and
        (all n: Node, m: Member | n in m.qnxt.Node implies m in n.^(m.qnxt))
        and
        (all n: Node.(Member.qnxt) | one (Member.qnxt).n)
        and
        (all n: Node | n !in n.^(Member.qnxt))
        and
        (no (Member.qnxt.Node & Member))
        and
        (all m1, m2: Member | 
            m1 != m2 => no (m1.qnxt.Node & m2.qnxt.Node))
        and
        (all msg: SentMsg | msg.sndr in msg.rcvrs and some (msg.rcvrs - msg.sndr))
        and
        (all msg: SentMsg, node: Node | msg !in node.outbox)
        and
        (all msg: PendingMsg | no msg.rcvrs)
        and
        (
            (no (SentMsg & SendingMsg))
            and 
            (no (SentMsg & PendingMsg))
            and
            (no (SendingMsg & PendingMsg))
        )
        and
        (Msg = (SentMsg + SendingMsg + PendingMsg))
        and
        (all n: Node | some (n.outbox & SendingMsg) => n in Member)
        and
        (all msg: SendingMsg | (some msg.rcvrs) && (msg.sndr !in msg.rcvrs))
        and
        (all msg: SendingMsg | msg.sndr in Member)
        and
        (all msg: SendingMsg | some n: Node | 
            (n.outbox = n.outbox + msg) && (msg.sndr != n)
        )
        and
        (all n: Node | 
            all msg: Msg | msg in n.outbox implies
                (msg in (n.(~sndr) & PendingMsg))
                or 
                (msg in (Node.(~sndr) & SendingMsg))
        )
        and
        (all msg: Msg | lone (msg.(~outbox) & Node))
        and
        (all msg: PendingMsg | msg !in (Member - msg.sndr).outbox)
        and
        (all msg: PendingMsg | msg in msg.sndr.outbox)

    )
}

pred noExits[] {
    always (
        (
            no m: Member | 
            memberExit[m]
        )
        and
        (
            no n: Node | dropQueue[n]
        )
    )
}

pred addQueuePre[n: Node, nlast: Node, m: Member] {
    n != m 
    and n != nlast 
    and n !in m.qnxt.Node 
    and no m.qnxt.nlast 
    and nlast in m.*(~(m.qnxt))
}

pred fairnessAddQueue[n: Node] {
    // TODO - should the some statements be outside?
    (eventually always 
        (some nlast: Node, m: Member | (addQueuePre[n, nlast, m]))
    ) 
    implies 
    (
        always eventually (some m: Member | addQueue[n, m])
    )
}

pred memberPromotionPre[n: Node, nprev: Node, m: Member] {
    n !in Member
    and 
    (m.qnxt).m = n
    and 
    (
        (no (m.qnxt).n) // No other node in queue
        or
        
        ((m.qnxt).n = nprev) // nprev is node in queue pointing to n
    )
}

pred fairnessJoinRing[n: Node] {
    (eventually always 
        (some nprev: Node, m: Member | memberPromotionPre[n, nprev, m])
    )
    implies
    (
        always eventually (some m: Member | memberPromotion[m])
    )

    // I think this way the fairness predicate is about the member promoting someone
    // and not someone being promoted
}

pred leaderPromotionPre[n: Node] {
    n in Member
	n in LQueue
	n = Leader.lnxt.Leader
	sndr.Leader in SentMsg
}

pred fairnessLeaderPromotion[n: Node] {
    (eventually always leaderPromotionPre[n])
    implies
    (always eventually leaderPromotionAux1[n])
}

pred redirectMsgPre[n: Node, msg: Msg] {
    redirectMsgEndBroadcastPre[msg, n]
    or
    (some mnext: Member | redirectMsgPreAux[msg, n, mnext])
}

pred redirectMsgEndBroadcastPre[msg: Msg, m: Member] {
    (msg in m.outbox and msg in SendingMsg and m = msg.sndr)
}

pred redirectMsgPreAux[msg: Msg, m: Node, mnext: Member] {
    (
        m in Member
        and m = msg.sndr implies msg in PendingMsg
        and msg in m.outbox
	    and m != mnext
        and mnext = m.nxt
        and (
            (msg in SendingMsg)
            or
            (msg in PendingMsg
            and m = msg.sndr)
        )
    )

}

pred fairnessRedirectMsg[n: Node] {
    all msg: sndr.n | 
        (
            (eventually always redirectMsgPre[n, msg])
            implies
            (always eventually redirectMessage[msg, n])
        )
}

pred fairness[] {
    all n: Node | 
        (
            fairnessAddQueue[n]
            and
            fairnessJoinRing[n]
            and
            fairnessLeaderPromotion[n]
            and
            fairnessRedirectMsg[n]
        )
}

pred OneAtATimePre[] {
    fairness[] and noExits[] and #Node >= 2
}

pred OneAtATime[] {
    OneAtATimePre[] implies (eventually Msg = SentMsg)
}

run {fairness[] and #Node >= 2} for 5

run {noExits[] and #Node >= 2} for 5

run OneAtATimePre for 5

run OneAtATime for 6

run {(fairness[] and #Node >= 2) implies (eventually Msg = SentMsg)}

run {always Valid[]} for 5