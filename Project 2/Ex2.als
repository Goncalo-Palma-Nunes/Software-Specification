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
	nxt = (Leader->Leader)
    Msg = PendingMsg
    no Node.qnxt
}

pred stutter[] {
    stutterRing[]
    stutterQueue[]
    stutterLeader[]
    stutterMsg[]
}

pred stutterMsg[] {
    SendingMsg' = SendingMsg
    SentMsg' = SentMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
}

pred stutterLeader[] {
    Leader' = Leader
    lnxt' = lnxt
    LQueue' = LQueue
}

pred stutterRing[] {
    Member' = Member
    nxt' = nxt
}

pred stutterQueue[] {
    qnxt' = qnxt
}

pred trans[] {
    stutter[]
    ||
    some n: Node, m: Member | addQueue[n, m]
    ||
    some n: Node | dropQueue[n]
    ||
    some m: Member | memberPromotion[m]
	||
	some m: Member | memberExit[m]
	||
	some m: Member | leaderApplication[m]
	||
	leaderPromotion[]
    ||
    some msg: Msg, m: Member | redirectMessage[msg, m]
}

pred system[] {
    init[]
    && always trans[]
}

fact {
    system[]
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
    // TODO - Perguntar ao fragoso

    // Frame
    stutterRing[]
    all m: Member - m | m.qnxt' = m.qnxt 
    stutterLeader[]
    stutterMsg[]
}

pred dropQueue[n: Node] {
    some m: Member | dropQueueAux1[n, m]
	||
	some m: Member, nprev: Node | dropQueueAux2[n, m, nprev]
}

pred dropQueueAux1[n: Node, m: Member] {
    // Pre-conditions
    n in m.qnxt.Node
    no n.~(m.qnxt)

    // Post-conditions
    // m.qnxt' = m.qnxt - (n -> m.qnxt.n)
    m.qnxt' = m.qnxt - (n -> n.(m.qnxt))

    // Frame (nxt,qnxt,Member,LQueue,Leader,lnxt)
    stutterRing[]
    all m: Member - m | m.qnxt' = m.qnxt
    stutterLeader[]
    stutterMsg[]
}

pred dropQueueAux2[n: Node, m: Member, nprev: Node] {
    // Pre-conditions
    n in m.qnxt.Node
    nprev = (m.qnxt).n
	// TODO nprev != n 

    // Post-conditions
    m.qnxt' = m.qnxt - (n -> n.(m.qnxt)) - (nprev -> n) + (nprev -> n.(m.qnxt))

    // Frame (nxt,qnxt,Member,LQueue,Leader,lnxt)
    stutterRing[]
    all m: Member - m | m.qnxt' = m.qnxt
    stutterLeader[]
    stutterMsg[]
}

// Gera modelo que 1 tira 1 nó da queue
run {#Msg=0 && eventually (#qnxt=2 && eventually (some n1, n2: Node, m: Member | dropQueueAux2[n1, m, n2]))} for 5

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
    some n: Node | memberPromotionAux1[m, n]
	||
	some n, nprev: Node | memberPromotionAux2[m, n, nprev]
}

pred memberPromotionAux1[m: Member, n: Node] {
    // Pre-conditions
    n !in Member
    (m.qnxt).m = n // n is head of m's queue
    no (m.qnxt).n // No other node in queue
	// TODO nprev != n 

    // Post-conditions
	Member' = Member + n // n in Member
	m.qnxt' = m.qnxt - (n->m)
    nxt' = nxt + (m -> n) + (n -> m.nxt) - (m -> m.nxt)
	no n.qnxt' // Possibly unnecessary
	no n.outbox' // Possibly unnecessary

    // Frame (nxt,qnxt,Member,LQueue,Leader,lnxt)
    all m: Member - m | m.qnxt' = m.qnxt && m.nxt' = m.nxt
    stutterLeader[]
    stutterMsg[]
}

pred memberPromotionAux2[m: Member, n: Node, nprev: Node] {
    // Pre-conditions
    n !in Member
    (m.qnxt).m = n // n is head of m's queue
    (m.qnxt).n = nprev // nprev is node in queue pointing to n
	// TODO nprev != n 

    // Post-conditions
    Member' = Member + n // n in Member
    m.qnxt' = m.qnxt - (n -> m) - (nprev -> n) + (nprev -> m)
    nxt' = nxt + (m->n) + (n->m.nxt) - (m->m.nxt)
	no n.qnxt' // Possibly unnecessary
	no n.outbox' // Possibly unnecessary

    // Frame (nxt,qnxt,Member,LQueue,Leader,lnxt)
    all m: Member - m | m.qnxt' = m.qnxt && m.nxt' = m.nxt
    stutterLeader[]
    stutterMsg[]
}

pred memberExit[m: Member] {
	some mprev: Member | memberExitAux1[m, mprev]
}

pred memberExitAux1[m: Member, mprev: Member] {
	// Pre-conditions
	mprev != m
	// mprev next is to m
	mprev.nxt = m
	// m is not the Leader
	m != Leader
	// m is not in the Leader queue
	m !in LQueue
	// m does not have any nodes in it's member queue
	no m.qnxt
	// All of m's messages have finished broadcasting 
	sndr.m in SentMsg
	
	// Post-conditions
	// mprev next is to m.nxt
	nxt' = nxt - (m->m.nxt) + (mprev->m.nxt)
	// mprev or m.nxt gets m's qnxt
	// EDIT: NOT NEEDED!
	// m no longer a member
	Member' = Member - m
	
	// Frame
	all m: Member - m - mprev | m.nxt' = m.nxt
	qnxt' = qnxt // EDIT: !!
	stutterLeader[]
    stutterMsg[]
}

pred leaderApplication[m: Member] {
    some mlast: Member | leaderApplicationAux1[m, mlast]
}

pred leaderApplicationAux1[m: Member, mlast: Member] {
    // Pre-condition
    // m is a member
    m in Member
    m != mlast
    // m not in Leader application queue
    m !in LQueue
	m !in Leader.lnxt.Node
    // mlast has no members pointing to it AND its reachable thru the queue
    no Leader.lnxt.mlast
    mlast in Leader.*(~(Leader.lnxt))

    // Post-condition
    // m points to last member in Leader application queue (or the leader)
    Leader.lnxt' = Leader.lnxt + (m -> mlast)
	LQueue' = LQueue + m

    // Frame
    stutterRing[]
    stutterQueue[]
    stutterMsg[]
    Leader' = Leader
}

pred leaderPromotion[] {
	some m: Member | leaderPromotionAux1[m]
}

pred leaderPromotionAux1[m: Member] {
	// Pre-condition
	// m in LQueue
	m in LQueue // kinda unnecessary
	// m is the head of the leader queue
	m = Leader.lnxt.Leader
	// All of Leader's messages have finished broadcasting
	sndr.Leader in SentMsg
	
	// Post-condition
	// m is the new Leader
	Leader' = m
	LQueue' = LQueue - m
	m.lnxt' = Leader.lnxt - (m -> Leader)

	// Frame
	stutterRing[]
    stutterQueue[]
    stutterMsg[]
}

pred redirectMessage[msg: Msg, m: Member] {
    redirectEndBroadcast[msg, m]
    ||
    some mnext: Member | redirectMessageAux[msg, m, mnext]
}

pred redirectEndBroadcast[msg: Msg, m: Member] {
    // Message reached the leader again
    
    // Pre-conditions
    msg in m.outbox
    msg in SendingMsg
    m = msg.sndr

    // Post-conditions
    SentMsg' = SentMsg + msg
    SendingMsg' = SendingMsg - msg
    m.outbox' = m.outbox - msg

    // Frame (nxt,qnxt,Member,LQueue,Leader,lnxt)
	stutterRing[]
    stutterQueue[]
    stutterLeader[]
    PendingMsg' = PendingMsg
}

pred redirectMessageAux[msg: Msg, m: Member, mnext: Member] {
    // Pre-conditions
    msg in m.outbox
    (redirectSendingMsg[msg, m] or redirectPendingMsg[msg, m])
    m != mnext // can't message itself (only happens if m is the only member)
    mnext = m.nxt

    // Post-conditions
    mnext.outbox' = mnext.outbox + msg
    m.outbox' = m.outbox - msg

    // Frame (nxt,qnxt,Member,LQueue,Leader,lnxt)
	stutterRing[]
    stutterQueue[]
    stutterLeader[]
    SentMsg' = SentMsg  // Msg hasn't reached leader so it hasn't terminated broadcast
}

pred redirectSendingMsg[msg: Msg, m: Member] {
    // Pre-conditions
    msg in SendingMsg

    // Frame
    PendingMsg' = PendingMsg
    SendingMsg' = SendingMsg
}

pred redirectPendingMsg[msg: Msg, m: Member] {
    // Pre-conditions
    msg in PendingMsg
    m = msg.sndr

    // Post-conditions
    SendingMsg' = SendingMsg + msg
    PendingMsg' = PendingMsg - msg
}

run {
    eventually (#Member=2 and
        (after (some msg: Msg, m: Member, mnext: Member |
            redirectMessage[msg, m] and
                (after redirectMessage[msg, mnext]) and
                    (after redirectMessage[msg, m])
            )
        )
    )
}

run {eventually some SentMsg} for 5


run { eventually some m: Member | memberPromotion[m] } for 2 Node, 0 Msg

// Test Member promotion twice
run { #Msg=0 && #Member=1 && #Node=3 && eventually (some n1,n2,n3: Member | n1 != n2 && n2 != n3 && n1 != n3) } for 5

// Test Member promotion and leader application
run { #Msg=0 && #Member=1 && #Node=3 && eventually (some n1,n2: Member | n1 != n2 && eventually (some m: Member | leaderApplication[m])) } for 5

// Test Member promotion twice and leader application
run { #Msg=0 && #Member=1 && #Node=3 && eventually (some n1,n2,n3: Member | n1 != n2 && n2 != n3 && n1 != n3 &&
	eventually (some m1: Member | leaderApplication[m1] && eventually (some m2: Member - m1 | leaderApplication[m2]))) } for 5

// Test Leader Promotion
run { #Msg=0 && #Member=1 && #Node=3 && eventually (some n1,n2: Member | n1 != n2 && eventually (leaderPromotion[])) } for 5

// Test Member Exit
run { #Msg=0 && #Member=1 && #Node=3 && eventually (some n1,n2: Member | n1 != n2 && eventually (some m: Member | memberExit[m])) } for 5
