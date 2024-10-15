module Ex2
open Ex1

pred init[] {
    Member = Leader
    Msg = PendingMsg
    no Node.qnxt
}

pred stutter[] {
    // Nodes
    Member' = Member
    nxt' = nxt
    qnxt' = qnxt
	
    Leader' = Leader
    lnxt' = lnxt
    LQueue' = LQueue
    // Messages


    // TODO - do we need all of this?
}

pred trans[] {
    stutter[]
    ||
    some n: Node, m: Member | addQueue[n, m]
    ||
    some m: Member | memberPromotion[m]
}

pred system[] {
    init[]
    trans[]
}

pred addQueue[n: Node, m: Member] {
    some nlast: Node | addQueueAux[n, m, nlast]
}

pred addQueueAux[n: Node, m: Member, nlast: Node] {
    // Pre-condition
    // n is not a member
    n !in Member
    n != nlast
    // n not in m's queue
    n !in m.qnxt.Node
    // nlast has no queue nodes pointing to it AND its reachable thru the queue
    no m.qnxt.nlast && nlast in m.*(~(m.qnxt))

    // Post-condition
    // n points to last node in m's queue
    m.qnxt' = m.qnxt + (n -> nlast)
    // TODO - Perguntar ao fragoso

    // Frame
    Member' = Member
    nxt' = nxt
    all m: Member - m | m.qnxt' = m.qnxt 
    Leader' = Leader
    lnxt' = lnxt
}


run {eventually (some n: Node, m: Member | addQueue[n, m])} for 5

pred memberPromotion[m: Member] {
    some n: Node | memberPromotionAux[m, n]
}

pred memberPromotionAux[m: Member, n: Node] {
    // Pre-conditions
    n !in Member
    m.qnxt.n = n // n is head of m's queue

    // Post-conditions
    m.qnxt.n' = m.qnxt.m // m.qnxt' = (m.qnxt - (m.qnxt.m -> n) + (m.qnxt.m -> m)) - (n -> m)
    Member' = Member + n // TODO n in Member
    n.nxt' = m.nxt // TODO
    m.nxt' = n // TODO

    // Frame (nxt,qnxt,Member,LQueue,Leader,lnxt)
    all m: Member - m | m.qnxt' = m.qnxt && m.nxt' = m.nxt
    Leader' = Leader
    lnxt' = lnxt
}


fact {
    system[]
}

run {} for 5