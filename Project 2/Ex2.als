module Ex2
open Ex1

pred init[] {
    Member = Leader
    Msg = PendingMsg
    no Node.qnxt
}
