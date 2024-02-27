#lang forge/bsl
open "mancala.frg"

pred allBoardsWellformed { all b: Board | wellformed[b] }
pred winningPreservedCounterexample {
  some pre, post: Board | {
    some holeNum: Int, p: Player | 
        // holeNum >= 0 and holeNum <= 2
        move[pre,holeNum, post]
        player1Win[pre]
        not player1Win[post]
  }
}

test expect {
  winningPreserved: { 
    allBoardsWellformed
    winningPreservedCounterexample } is unsat
}


example simpleWellFormedTest is {allBoardsWellformed} for {
    Board = `Board0
    Player1 = `player1
    Player2 = `player2
    Player = Player1 + Player2
    `Board0.hole =  (0) -> 2 + 
                    (1) -> 2 + 
                    (2) -> 0 +
                    (3) -> 1 +
                    (4) -> 3 +
                    (5) -> 2 +
                    (6) -> 2+
                    (7) -> 0

}
-- total number of marbles on the board is greater than 12
example numMarblesGreaterThan12 is {not allBoardsWellformed} for {
    Board = `Board0
    Player1 = `player1
    Player2 = `player2
    Player = Player1 + Player2
    `Board0.hole =  (0) -> 2 + 
                    (1) -> 2 + 
                    (2) -> 0 +
                    (3) -> 1 +
                    (4) -> 7 +
                    (5) -> 2 +
                    (6) -> 2+
                    (7) -> 7

}

-- Tests whether marble numbers are negative
example negativeMarbles is {not allBoardsWellformed} for {
    Board = `Board0
    Player1 = `player1
    Player2 = `player2
    Player = Player1 + Player2
    `Board0.hole =  (0) -> 2 + 
                    (1) -> 2 + 
                    (2) -> 0 +
                    (3) -> 1 +
                    (4) -> -3 +
                    (5) -> -2 +
                    (6) -> 2+
                    (7) -> 0

}

--Tests whether the hole numbers are outside the range 0 to 7 (exclusive).
example offBoardX_not_wellformed is {not allBoardsWellformed} for {
    Board = `Board0
    Player1 = `player1
    Player2 = `player2
    Player = Player1 + Player2
    `Board0.hole =  (0) -> 2 + 
                    (1) -> 2 + 
                    (2) -> 0 +
                    (-3) -> 1 +
                    (4) -> 3 +
                    (5) -> 2 +
                    (6) -> 2+
                    (8) -> 0

}