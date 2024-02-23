#lang forge/bsl 

abstract sig Player {}
one sig Player1, Player2 extends Player {}

sig Board {
    hole: pfunc Int -> Hole
}

sig Hole {
    next: one Hole,
    marbles: one Int
}

sig Marble {}


pred wellformed {
    all b: Board | {
        all holeNum: Int | {
            (holeNum < 0 or holeNum > 7) implies no b.hole[holeNum] 
            (holeNum >=0 and holeNum <= 7) implies {
                some b.hole[holeNum]

                // ints form cycle from 0 to 7
                (holeNum < 7) implies (b.hole[holeNum]).next = b.hole[add[holeNum, 1]]
                (holeNum = 7) implies (b.hole[holeNum]).next = b.hole[0]

                // each int points to unique hole
                all num: Int | (num != holeNum) implies b.hole[num] != b.hole[holeNum]
            }
        }
        all h, h2: Hole | {
            // no negative marbles
            h.marbles >= 0
            h2.marbles >= 0 

            // form cycle 
            reachable[h2, h, next]

            // next not itself
            h.next != h
            h2.next != h2
        }
    }
}


pred init{
    // nests empty and cells have two marbles
    all b: Board | {
        (b.hole[3]).marbles = 0 
        (b.hole[7]).marbles = 0
        all holeNum: Int | (holeNum >= 0 and holeNum <= 7 and holeNum != 3 and holeNum !=7) implies (b.hole[holeNum]).marbles = 2
    }
}

run {
    wellformed
    init
} for exactly 1 Board, 8 Hole