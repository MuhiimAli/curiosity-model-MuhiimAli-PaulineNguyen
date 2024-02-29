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
--      - There are exactly 8 holes on the board, numbered 0 through 7, that can have marbles
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
        }
    }
}
---------------------------------------------------------------
--  -For our initial Board, the following are true:
--      - The two mancalas, hole3 and hole7, are empty
--      - There are exactly two marbles in other holes
--      - It is Player1's turn

pred init[b: Board]{
    b.hole[3]= 0 
    b.hole[7] = 0
    b.turn = Player1
    all holeNum: Int | (holeNum >= 0 and holeNum <= 7 and holeNum != 3 and holeNum !=7) implies b.hole[holeNum] = 2
}

---------------------------------------------------------------
--  (Helper Method for move)
--      - Allows the player to continue playing if they've placed the last marble in their mancala
--      - If that is not the case, it updates turn to be the next player's turn

pred checkTurn[pre, post: Board, myMancala: Int] {
    all holeNums: Int | {
        pre.prev[holeNums] = myMancala implies {
            (post.hole[holeNums] = pre.hole[holeNums] and post.hole[myMancala] = add[pre.hole[myMancala], 1]) => {
                post.turn = pre.turn
            } 
            else {
                post.turn != pre.turn
            }
        }
    }
}
---------------------------------------------------------------
--  -(Helper Method for move):
--  - It updates the number of marbles in each hole after a move is made
--      - The starting hole, which is the hole that the player chose to pick the marbles from, is set to 0
--      - The number of marbles in the other person's mancala remains unchanged
--      - Marbles are distributed sequentially
--      - Number of holes whose marbles increased = number of marbles in starting hole 
--      - Number of marbles increase by 1 for each hole

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

    // frame: everything else about board should stay the same
    all holeNums: Int | {
        some pre.prev[holeNums] implies post.prev[holeNums] = pre.prev[holeNums]
        no pre.prev[holeNums] implies no post.prev[holeNums]
        no pre.hole[holeNums] implies no post.hole[holeNums]
    }

}

---------------------------------------------------------------
-- "Transition relation"
--      - Checks that game is not over 
--      - Checks that the starting hole is on the board
--      - Checks that the it's the right player's turn, and then allows player to make 
--        a move starting from a non-empty hole in their row 

pred move[pre: Board, holeNum: Int, post: Board] {
    -- guard:  game can't be over
        -- valid move location (has to be on board)
        -- it needs to be the player's turn 

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
--  Player one wins if hole0, hole1 and hole2 are empty
pred player1Win[b: Board] {
    // row 1 empty 
    {b.hole[0] = 0
    b.hole[1] = 0
    b.hole[2] = 0}

}

-------------------------------------------------------------------
--  Player 2 wins if hole4, hole5 and hole6 are empty
pred player2Win[b: Board] {
    // row 2 empty 
    {b.hole[4] = 0
    b.hole[5] = 0
    b.hole[6] = 0}
}

-------------------------------------------------------------------
--  Game ends when there is a player who won
pred endGame[b: Board] {
    player1Win[b] or player2Win[b]
}

-------------------------------------------------------------------
--  - After game ends:
--      - Winner stays winner
--      - No more moves can be made. Thus, board remains unchanged

pred doNothing[pre, post: Board] {
    -- guard: game not over
    endGame[pre]

    -- action: marbles stay same and turn stays same
    all holeNum: Int | {
        post.hole[holeNum] = pre.hole[holeNum]
        post.turn = pre.turn
    }

    -- frame: all other aspects of board stay same
    all holeNums: Int | {
        some pre.prev[holeNums] implies post.prev[holeNums] = pre.prev[holeNums]
        no pre.prev[holeNums] implies no post.prev[holeNums]
        no pre.hole[holeNums] implies no post.hole[holeNums]
    }
}

one sig Game {
    first: one Board, 
    next: pfunc Board -> Board
}

pred game_trace {
    wellformed[Game.first]
    init[Game.first]
    all b: Board | { some Game.next[b] implies {
        (some holeNum: Int | move[b, holeNum, Game.next[b]]) or
        doNothing[b, Game.next[b]]
    }}
}

// checking initial board
// run {
//     some b: Board | { init[b] and wellformed[b]}
// } for exactly 1 Board

// checking valid first moves 
// run {
//     some disj pre, post: Board | {
//         init[pre]
//         wellformed[pre]
//         some holeNum: Int | { 
//             move[pre, holeNum, post]
//         }
//     }
// } for exactly 2 Board

// checking valid moves 
// run {
//     some disj pre, post: Board | {
//         wellformed[pre]
//         all holeNum: Int | pre.hole[holeNum] < 7 
//         some holeNum: Int | { 
//             move[pre, holeNum, post]
//         }
//     }
// } for exactly 2 Board

// checking valid cases of doing nothing 
// run {
//     some disj pre, post: Board | {
//         wellformed[pre]
//         all holeNum: Int | pre.hole[holeNum] < 7 
//         doNothing[pre, post]
//     }
// } for exactly 2 Board

// checking entire game
run { 
    game_trace
} for 15 Board for {next is linear}