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

pred redirectMsgPre[] {
    // TODO
}

pred fairnessRedirectMsg[] {
    // TODO
}

pred fairness[] {
    all n: Node | 
        (
            fairnessAddQueue[n]
            and
            fairnessJoinRing[n]
            and
            fairnessLeaderPromotion[n]
        )
}