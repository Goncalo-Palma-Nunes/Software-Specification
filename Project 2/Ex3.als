module Ex3
open Ex2

pred noExits[] {
    always (
        no m: Member | 
            memberExit[m]
    )
}

run {noExits[]} for 10