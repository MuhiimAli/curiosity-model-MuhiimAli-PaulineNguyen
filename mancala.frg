#lang forge/bsl 

abstract sig Player {}
one sig Player1, Player2 extends Player {}

sig Board {
    prev: pfunc Int -> Int,
    hole: pfunc Int -> Int,
    turn: one Player
}
---------------------------------------------------------------
--  -Model of our Board:
--      -There are exactly 8 holes on the board, numbered 0 through 5
--      - Each hole has a previous hole (hole0's prev = hole7). This creates a linear, sequantial link between the holes
--      - The number of marbles per hole can't be negative
    

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
---------------------------------------------------------------
--  -For our initial Board, the following are true:
--      - The two mancalas, hole3 and hole7, are empty
--      - There are exactly two marbles in each hole
--      - It is Player1's turn
pred init[b: Board]{
    // mancalas empty and cells have two marbles
    b.hole[3]= 0 
    b.hole[7] = 0
    b.turn = Player1
    all holeNum: Int | (holeNum >= 0 and holeNum <= 7 and holeNum != 3 and holeNum !=7) implies b.hole[holeNum] = 2
}

---------------------------------------------------------------
--  (Helper Method for move)
--  - allows the player to continue playing if they've placed the last marble in their mancala
--  - If that is not the case, it updates turn to be the next player's turn

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
---------------------------------------------------------------
--  -(Helper Method for move):
--  - It updates the number of marbles in each hole after a move is made
--      - The starting hole, which is the hole that the player chose to pick the marbles from, is set to 0
--      - The number of marbles in the other person's mancala remains unchanged
--      - marbles are distributed sequentially
--      - number of holes whose marbles increased = number of marbles in starting hole 
--      -- number of marbles increase by 1
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
}

-------------------------------------------------------------------
--  - player one wins if hole0, hole1 and hole2 are empty
pred player1Win[b: Board] {
    // row 1 empty 
    {b.hole[0] = 0
    b.hole[1] = 0
    b.hole[2] = 0}

}

-------------------------------------------------------------------
--  - player 2 wins if hole4, hole5 and hole6 are empty
pred player2Win[b: Board] {
    // row 1 empty 
    {b.hole[4] = 0
    b.hole[5] = 0
    b.hole[6] = 0}
}

-------------------------------------------------------------------
--  Game ends when there is a player
pred endGame[b: Board] {
    player1Win[b] or player2Win[b]
}

-------------------------------------------------------------------
--  - After game ends:
--      - winner stays winner
--      - no more moves can be made. Thus, board remains unchanged
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