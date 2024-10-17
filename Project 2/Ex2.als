module Ex2
open Ex1

fun visQueueNext[]: Node -> lone Node {
    Member.qnxt
}

fun visLeaderNext[]: Node -> lone Node {
    Leader.lnxt
}

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
    // ||
    // some n: Node | dropQueue[n]
    // ||
    // some m: Member | memberPromotion[m]
}

pred system[] {
    init[]
    && always trans[]
}

pred addQueue[n: Node, m: Member] {
    some nlast: Node | addQueueAux1[n, m, nlast]
}

pred addQueueAux1[n: Node, m: Member, nlast: Node] {
    // Pre-condition
    // n is not a member
    n !in Member
    n != nlast
    // n not in m's queue
    n !in m.qnxt.Node
    // nlast has no queue nodes pointing to it AND its reachable thru the queue
    no m.qnxt.nlast
    nlast in m.*(~(m.qnxt))

    // Post-condition
    // n points to last node in m's queue
    m.qnxt' = m.qnxt + (n -> nlast)
    // m.qnxt' = m.qnxt + (nlast -> n)
    // TODO - Perguntar ao fragoso

    // Frame
    Member' = Member
    nxt' = nxt
    all m: Member - m | m.qnxt' = m.qnxt 
    Leader' = Leader
    lnxt' = lnxt
}

run {#Member=1 && #Node=4 && #Msg=0 && 
    (eventually (some n1, n2: Node, m: Member | n1 != n2 && addQueue[n1, m] 
                                                && (eventually addQueue[n2, m])))
    } for 5


pred dropQueue[n: Node] {
    some m: Member | dropQueueAux1[n, m]
}

pred dropQueueAux1[n: Node, m: Member] {
    // Pre-conditions
    n in m.qnxt.Node
    no n.~(m.qnxt)

    // Post-conditions
    m.qnxt' = m.qnxt - (n -> m.qnxt.n)

    // Frame (nxt,qnxt,Member,LQueue,Leader,lnxt)
    Member' = Member
    nxt' = nxt
    all m: Member - m | m.qnxt' = m.qnxt
    Leader' = Leader
    lnxt' = lnxt
}

// pred dropQueueAux2[n: Node, m: Member] {
//     // Pre-conditions
//     n in m.qnxt.Node
//     some n.~(m.qnxt)

//     // Post-conditions
//     m.qnxt' = m.qnxt - (m.qnxt.n -> n) + (m.qnxt.n -> m)

//     // Frame (nxt,qnxt,Member,LQueue,Leader,lnxt)
//     Member' = Member
//     nxt' = nxt
//     all m: Member - m | m.qnxt' = m.qnxt
//     Leader' = Leader
//     lnxt' = lnxt
// }

// Gera modelo que 1 tira 1 nó da queue
run {#Msg=0 && eventually (some n: Node | dropQueue[n])} for 5

// Gera modelo que adiciona 1 nó a uma queue
run {#Msg=0 && eventually (some n: Node, m: Member | addQueue[n, m])} for 5

// Gera modelo que adiciona 2 nós a uma queue
run {#Member=1 && #Node=4 && #Msg=0 && 
    (eventually (some n1, n2: Node, m: Member | n1 != n2 && addQueue[n1, m] 
                                                && (eventually addQueue[n2, m])))
    } for 5


// Gera modelo que tira 2 nós de uma queue
run {#Member=1 && #Node=4 && #Msg=0 && 
    (eventually #Member.qnxt=2)
    // (eventually (some n1, n2: Node| n1 != n2 && dropQueue[n1] && (eventually dropQueue[n2])))
    } for 5

pred memberPromotion[m: Member] {
    some n: Node | memberPromotionAux[m, n]
}

pred memberPromotionAux[m: Member, n: Node] {
    // Pre-conditions
    n !in Member
    (m.qnxt).m = n // n is head of m's queue
    no n.~(m.qnxt)
    //some (m.qnxt).n

    // Post-conditions
    Member' = Member + n // n in Member
    no (m.qnxt') 
    nxt' = nxt + (m->n) + (n->m.nxt) - (m->m.nxt)

    // Frame (nxt,qnxt,Member,LQueue,Leader,lnxt)
    all m: Member - m | m.qnxt' = m.qnxt && m.nxt' = m.nxt
    Leader' = Leader
    lnxt' = lnxt

}


fact {
    system[]
}

run { eventually some m: Member | memberPromotion[m] } for 2 Node, 0 Msg

run { eventually some m: Member | memberPromotion[m] } for 3 Node, 0 Msg, 3 steps
