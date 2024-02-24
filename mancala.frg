#lang forge/bsl 

abstract sig Player {}
one sig Player1, Player2 extends Player {}

sig Board {
    next: pfunc Int -> Int,
    hole: pfunc Int -> Int
}


pred wellformed {
    all b: Board | {
        all holeNum: Int | {
            (holeNum < 0 or holeNum > 7) implies b.hole[holeNum] = 0
            (holeNum >=0 and holeNum <= 7) implies {
                // ints form cycle from 0 to 7
                (holeNum < 7) implies b.next[holeNum] = add[holeNum, 1]
                (holeNum = 7) implies b.next[holeNum] = 0
                b.hole[holeNum] >= 0
            }
        }
    }
}

pred init{
    // nests empty and cells have two marbles
    all b: Board | {
        b.hole[3]= 0 
        b.hole[7] = 0
        all holeNum: Int | (holeNum >= 0 and holeNum <= 7 and holeNum != 3 and holeNum !=7) implies b.hole[holeNum] = 2
    }
}

run {
    wellformed
    init
} for exactly 1 Board