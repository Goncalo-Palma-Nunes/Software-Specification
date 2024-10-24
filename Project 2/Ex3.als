module Ex3
open Ex2

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