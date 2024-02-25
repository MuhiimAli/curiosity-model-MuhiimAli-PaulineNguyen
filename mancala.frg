#lang forge/bsl 

abstract sig Player {}
one sig Player1, Player2 extends Player {}

sig Board {
    prev: pfunc Int -> Int,
    hole: pfunc Int -> Int,
    turn: one Player
}


pred wellformed[b: Board] {
        all holeNum: Int | {
            (holeNum < 0 or holeNum > 7) implies no b.hole[holeNum] and no b.prev[holeNum]
            (holeNum >=0 and holeNum <= 7) implies {
                // ints form cycle from 0 to 7
                some b.hole[holeNum]
                (holeNum >0) implies b.prev[holeNum] = subtract[holeNum, 1]
                (holeNum = 0) implies b.prev[holeNum] = 7
                // no negative marbles
                b.hole[holeNum] >= 0
                // no marbles exceeds 7
            }
        }
}

pred init[b: Board]{
    // nests empty and cells have two marbles
    b.hole[3]= 0 
    b.hole[7] = 0
    b.turn = Player1
    all holeNum: Int | (holeNum >= 0 and holeNum <= 7 and holeNum != 3 and holeNum !=7) implies b.hole[holeNum] = 2
}

pred checkTurn[pre, post: Board, myMancala: Int] {
    all holeNums: Int | {
        pre.prev[holeNums] = myMancala and post.hole[holeNums] = pre.hole[holeNums] and (post.hole[myMancala] = add[pre.hole[myMancala], 1]) => {
            post.turn = pre.turn
        } 
        else {
            post.turn != pre.turn
        }
    }
}

pred updateNumMarbles[pre, post: Board, startingHole, otherMancala: Int] {
    post.hole[startingHole] = 0

    post.hole[otherMancala] = pre.hole[otherMancala]

    // number of holes whose marbles increased = number of marbles in starting hole        
    #{ holeNum: Int | post.hole[holeNum] = add[pre.hole[holeNum], 1]} = pre.hole[startingHole]

    // for all holes whose marbles increased, their previous hole must also increase (unless it's the starting hole, or the other mancala)
    all holeNums: Int | (holeNums != startingHole) implies {
        post.hole[holeNums] = pre.hole[holeNums] or
        (post.hole[holeNums] = add[pre.hole[holeNums], 1] and
            {(post.hole[post.prev[holeNums]] = add[pre.hole[pre.prev[holeNums]], 1]) or
            (post.prev[holeNums] = otherMancala) or
            (post.prev[holeNums] = startingHole)}
        )
        pre.prev[holeNums] = otherMancala and post.hole[holeNums] = add[pre.hole[holeNums], 1] implies {
            post.hole[post.prev[otherMancala]] = add[pre.hole[pre.prev[otherMancala]], 1]
        }
    }

    // all holeNums: Int | {
        // // if holeNum is (1) within range of (startingHole and (startingHole + numMarbles))
        // // (2) is in bounds, and (3) is not the other mancala, increment 1
        // (holeNum > startingHole and holeNum <= add[startingHole, pre.hole[startingHole]] and holeNum <= 7 and holeNum != otherMancala) implies 
        // post.hole[holeNum] = add[pre.hole[holeNum],1] 

        // // if the range (startingHole and (startingHole + numMarbles) exceeds bounds, need to wrap around
        // (add[startingHole, pre.hole[startingHole]] > 7) implies {

        //     // if otherMancala is within the wraparound range, do mod7
        //     (otherMancala < subtract[remainder[add[startingHole, pre.hole[startingHole]], 7], 1]) => 
        //     {
        //         // if holeNum > 0 and holeNum < (holeNum + numMarbles) mod 7, and holeNum is not othermancala, increment 1
        //         ((holeNum >= 0 and holeNum <= remainder[add[startingHole, pre.hole[startingHole]], 7]) and holeNum != otherMancala) implies
        //         post.hole[holeNum] = add[pre.hole[holeNum],1] 
        //     }

        //     // else, do mod7 - 1
        //     else {
        //         ((holeNum >= 0 and holeNum <= subtract[remainder[add[startingHole, pre.hole[startingHole]], 7], 1]) and holeNum != otherMancala) implies
        //         post.hole[holeNum] = add[pre.hole[holeNum],1] 
        //     }
        // }
    // }

}

pred move[pre: Board, holeNum: Int, post: Board] {
    // guard:
    holeNum >= 0 and holeNum <= 2 or 
    holeNum >= 4 and holeNum <= 6

    not endGame[pre]
    (pre.turn = Player1) implies {
        holeNum >= 0 and holeNum <= 2
        pre.hole[holeNum] > 0
        updateNumMarbles[pre, post, holeNum, 7]
        checkTurn[pre, post, 3]
    }

    (pre.turn = Player2) implies {
        holeNum >= 4 and holeNum <= 6
        pre.hole[holeNum] > 0
        updateNumMarbles[pre, post, holeNum, 3]
        checkTurn[pre, post, 7]
    }


    // some hole with n marbles is now empty

    // following n holes inc marbles by 1 

    // if player 1 turn, starting hole is 0, 1, or 2, and hole 7 shouldn't change

    // if player 2 turn, starting hole is 4, 5, or 6, and hole 3 shouldn't change
}

pred player1Win[b: Board] {
    // row 1 empty 
    {b.hole[0] = 0
    b.hole[1] = 0
    b.hole[2] = 0}

}

pred player2Win[b: Board] {
    // row 1 empty 
    {b.hole[4] = 0
    b.hole[5] = 0
    b.hole[6] = 0}
}

pred endGame[b: Board] {
    player1Win[b] or player2Win[b]
}

pred doNothing[pre, post: Board] {
    -- guard
    endGame[pre] and endGame[post]

    -- action
    all holeNum: Int | {
        pre.hole[holeNum] = post.hole[holeNum]
        post.turn = pre.turn
    }
}

// checking valid first moves 
// run {
//     some pre, post: Board | {
//         some holeNum: Int, p: Player | { 
//             move[pre, 5, p, post]
//             init[pre]
//             wellformed[pre]
//             wellformed[post]
//         }
//     }
// } for exactly 2 Board

one sig Game {
    first: one Board, 
    next: pfunc Board -> Board
}

pred game_trace {
    init[Game.first]
    all b: Board | { some Game.next[b] implies {
        wellformed[b]
        (some holeNum: Int | 
            move[b, holeNum, Game.next[b]])
        or
        doNothing[b, Game.next[b]]
        -- TODO: ensure X moves first
    }}
}

run { 
    game_trace
} for 20 Board for {next is linear}