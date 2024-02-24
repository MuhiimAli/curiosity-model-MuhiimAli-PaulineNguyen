#lang forge/bsl 

abstract sig Player {}
one sig Player1, Player2 extends Player {}

sig Board {
    next: pfunc Int -> Int,
    hole: pfunc Int -> Int
}


pred wellformed[b: Board] {
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

pred init[b: Board]{
    // nests empty and cells have two marbles
    b.hole[3]= 0 
    b.hole[7] = 0
    all holeNum: Int | (holeNum >= 0 and holeNum <= 7 and holeNum != 3 and holeNum !=7) implies b.hole[holeNum] = 2
}

pred updateNumMarbles[pre, post: Board, startingHole: Int, otherMancala: Int] {
    post.hole[startingHole] = 0
   
    // number of original marbles (number of holes to update)
    // pre.hole[startingHole]

    all holeNums: Int | {
        // if holeNum is within range of startingHole and startingHole + numMarbles and is in bounds, increment 1
        (holeNums > startingHole and holeNums <= add[startingHole, pre.hole[startingHole]] and holeNums <= 7) implies 
        post.hole[holeNums] = add[pre.hole[holeNums],1] 

        // else, need to wrap around
        (add[startingHole, pre.hole[startingHole]] > 7) implies {

            // if otherMancala is within this range, do mod7
            (otherMancala < subtract[remainder[add[startingHole, pre.hole[startingHole]], 7], 1]) implies 
            {
                // if holeNum > 0 and holeNum < (holeNum + numMarbles) mod 7, and holeNum is not othermancala, increment 1
                ((holeNum >= 0 and holeNum <= remainder[add[startingHole, pre.hole[startingHole]], 7]) and holeNum != otherMancala) implies
                post.hole[holeNums] = add[pre.hole[holeNums],1] 
            }

             // else, do mod7 - 1
                ((holeNum >= 0 and holeNum <= subtract[remainder[add[startingHole, pre.hole[startingHole]], 7], 1]) and holeNum != otherMancala) implies
                post.hole[holeNums] = add[pre.hole[holeNums],1] 
        }
    }

}

pred move[pre: Board, holeNum: Int, turn: Player, post: Board] {
    // guard:
    not endGame 
    (turn = Player1) implies some holeNum: Int | {
        holeNum >= 0 and holeNum <= 2
        pre.hole[holeNum] > 0
        updateNumMarbles[pre, post, holeNum, 7]
    }

    (turn = Player2) implies some holeNum: Int | {
        holeNum >= 4 and holeNum <= 6
        pre.hole[holeNum] > 0
        updateNumMarbles[pre, post, holeNum, 3]
    }


    // some hole with n marbles is now empty

    // following n holes inc marbles by 1 

    // if player 1 turn, starting hole is 0, 1, or 2, and hole 7 shouldn't change

    // if player 2 turn, starting hole is 4, 5, or 6, and hole 3 shouldn't change
}

pred player1Win[b: Board, p: Player] {
    // row 1 empty 
    {b.hole[0] = 0
    b.hole[1] = 0
    b.hole[2] = 0}

}

pred player1Win[b: Board, p: Player] {
    // row 1 empty 
    {b.hole[4] = 0
    b.hole[5] = 0
    b.hole[6] = 0}
}

pred endGame[b: Board, p: Player] {
    player1Win or player2Win
}

pred doNothing[pre, post: board] {
    -- guard
    endGame

    -- action
    all holeNum: Int | {
        pre.hole[holeNum] = post.hole[holeNum]
    }
}

run {
    wellformed
    init
} for exactly 1 Board