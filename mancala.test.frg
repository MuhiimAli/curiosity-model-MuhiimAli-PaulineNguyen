#lang forge/bsl

open "mancala.frg"

// PREDICATES FOR TESTING WELLFORMED 
pred correctHoles[b: Board] {
    all holeNum: Int | some b.hole[holeNum] implies (holeNum >=0 and holeNum <=7)
}

pred orderedPrev[b: Board] {
    all holeNum: Int | {
        some b.prev[holeNum] implies {
        holeNum = 0 => {b.prev[holeNum] = 7} 
        else b.prev[holeNum] = subtract[holeNum, 1] 
        }
    }
}

pred emptyBoard[b: Board] {
    correctHoles[b]
    all holeNum: Int | {
        b.hole[holeNum] = 0
    }
}

pred fullBoard[b: Board] {
    correctHoles[b]
    all holeNum: Int | {
        b.hole[holeNum] = 7
    }
}

pred notWellformed[b: Board] {
    not wellformed[b]
}

pred someNegMarbles[b: Board] {
    some holeNum: Int | b.hole[holeNum] < 0
}

pred someNegHoles[b: Board] {
    some holeNum: Int | holeNum < 0 and b.hole[holeNum] = 0
}

pred missingMancala[b: Board] {
    no b.hole[3] or no b.hole[7]
}

// TEST SUITE FOR WELLFORMED + NOTWELLFORMED
test suite for wellformed {
    -- wellformed board must have holes 0 - 7 
    assert all b: Board | correctHoles[b] is necessary for wellformed[b]
    -- wellformed board must have correct prev (in descending order)
    assert all b: Board | orderedPrev[b] is necessary for wellformed[b]
    -- a board with no marbles in all holes is wellformed
    assert all b: Board | emptyBoard[b] is sufficient for wellformed[b]
    -- a board with 7 marbles in all holes is wellformed
    assert all b: Board | fullBoard[b] is sufficient for wellformed[b]
}

test suite for notWellformed {
    -- a board with negative marbles is not wellformed
    assert all b: Board | someNegMarbles[b] is sufficient for notWellformed[b]
    -- a board with negative holes is not wellformed
    assert all b: Board | someNegHoles[b] is sufficient for notWellformed[b]
    -- a board that has no hole 3 or 7 (mancala holes) is not wellformed
    assert all b: Board | missingMancala[b] is sufficient for notWellformed[b]
}

---------------------------------------------------------------

// PREDICATES FOR TESTING INIT 
pred correctMancalas[b: Board] {
    b.hole[7] = 0
    b.hole[3] = 0
} 

pred twoMarblesForNonMancalas[b: Board] {
    b.hole[0] = 2
    b.hole[1] = 2
    b.hole[2] = 2
    b.hole[4] = 2
    b.hole[5] = 2
    b.hole[6] = 2
} 

pred nonOrderedPrev[b: Board] {
    b.prev[1] = 1
} 

pred playerOneStarts[b: Board] {
    b.turn = Player1 
}

pred only7GoodHoles[b: Board] {
    correctMancalas[b]
    twoMarblesForNonMancalas[b]
    playerOneStarts[b]
    b.hole[-1] = 0
    b.hole[-2] = -2
}

test suite for init {
    -- mancalas must start out with no marbles
    assert all b: Board | correctMancalas[b] is necessary for init[b]
    -- all holes except mancalas must have two marbles
    assert all b: Board | twoMarblesForNonMancalas[b] is necessary for init[b]
    -- player one always start initially
    assert all b: Board | playerOneStarts[b] is necessary for init[b]
    -- some board with goot turn and good holes 0 - 7 can satisty init without being wellformed
    assert all b: Board | only7GoodHoles[b] is sufficient for init[b]

    test expect { 
        -- initial board can be wellformed
        initWellformed: { all b: Board | wellformed[b] and init[b] } is sat
        -- initial board doesn't guarantee non-negative holes like wellformed does 
        initNegHoles: { all b: Board | someNegHoles[b] and init[b] } is sat
        -- initial board doesn't guarantee correct prev field like wellformed does
        initPrevNotOrdered: { all b: Board | nonOrderedPrev[b] and init[b] } is sat
        -- player two can't ever start on initial board
        playerTwoStarts: { all b: Board | b.turn = Player2 and init[b] } is unsat
        -- a board with negative marbles in mancala is not init
        initNegMarbles: { all b: Board | b.hole[3] = -1 and init[b] } is unsat
        -- an empty board is not init
        initEmpty: { all b: Board | emptyBoard[b] and init[b]} is unsat 
    }
}

---------------------------------------------------------------

//PREDICATES FOR TESTING CHECKTURN
pred turnSwitchCase[pre, post: Board, myMancala: Int] {
    all holeNums: Int | {
        pre.prev[holeNums] = myMancala implies {
            post.hole[myMancala] = pre.hole[myMancala] implies post.turn != pre.turn
        }}
}

pred myMancalaIncreaseCase[pre, post: Board, myMancala: Int] {
    all holeNums: Int | {
        pre.prev[holeNums] = myMancala implies {
            post.turn = pre.turn implies post.hole[myMancala] = add[pre.hole[myMancala], 1]
    }}
}

pred noTurnSwitchMove[pre, post: Board] {
    wellformed[pre] and wellformed[post]
    pre.turn = Player1
    post.turn = Player1
    pre.hole[1] = 1
    pre.hole[2] = 1
    pre.hole[3] = 0
    post.hole[2] = 0
    post.hole[3] = 1
    pre.hole[4] = 1
    all holeNum: Int | (holeNum != 2 and holeNum != 3) implies {
        post.hole[holeNum] = pre.hole[holeNum]
    }
}

pred turnSwitchMove[pre, post: Board] {
    wellformed[pre] and wellformed[post]
    pre.turn = Player2
    post.turn = Player1
    pre.hole[5] = 2
    pre.hole[6] = 3
    pre.hole[7] = 0
    pre.hole[0] = 1
    pre.hole[1] = 1
    post.hole[6] = 0
    post.hole[7] = 1
    post.hole[0] = 2
    post.hole[1] = 2
    all holeNum: Int | (holeNum >= 2 and holeNum <= 5) implies {
        post.hole[holeNum] = pre.hole[holeNum]
    }
}

pred notCheckTurn[pre, post: Board, myMancala: Int] {
    not checkTurn[pre, post, myMancala]
}

pred lastMarblePassedMyMancala[pre, post: Board, myMancala: Int] {
    some holeNums: Int | pre.prev[holeNums] = myMancala
    post.hole[myMancala] = add[pre.hole[myMancala], 1]
    some h: Int | some pre.prev[h] and pre.prev[h] = myMancala and post.hole[h] = add[pre.hole[h], 1]
    post.turn = pre.turn
}

pred lastMarbleInMyMancala[pre, post: Board, myMancala: Int] {
    some holeNums: Int | pre.prev[holeNums] = myMancala
    post.hole[myMancala] = add[pre.hole[myMancala], 1]
    some h: Int | some pre.prev[h] and pre.prev[h] = myMancala and post.hole[h] = pre.hole[h]
    post.turn != pre.turn
}

pred myMancalaDecreased[pre, post: Board, myMancala: Int] {
    some holeNums: Int | pre.prev[holeNums] = myMancala
    post.hole[myMancala] = subtract[pre.hole[myMancala], 1]
    post.turn = pre.turn
}

test suite for checkTurn {
    -- checkTurn ensures that if my mancala doesn't get a new marble, there's turn switching
    assert all disj b1, b2: Board, h: Int | turnSwitchCase[b1, b2, h] is necessary for checkTurn[b1, b2, h]
    -- checkTurn ensures that if there is no turn switch, my mancala must have gotten a new marble
    assert all disj b1, b2: Board, h: Int | myMancalaIncreaseCase[b1, b2, h] is necessary for checkTurn[b1, b2, h]
    -- moving one marble into mancala and keeping the turn satisfies checkTurn
    assert all disj b1, b2: Board | noTurnSwitchMove[b1, b2] is sufficient for checkTurn[b1, b2, 3]
    -- moving marbles past my mancala and switching the turn satisfies checkTurn
    assert all disj b1, b2: Board | turnSwitchMove[b1, b2] is sufficient for checkTurn[b1, b2, 7]
}

test suite for notCheckTurn {
    -- if last marble passed my mancala, and turn stays same, it violates checkTurn
    assert all disj b1, b2: Board, h: Int | lastMarblePassedMyMancala[b1, b2, h] is sufficient for notCheckTurn[b1, b2, h]
    -- if last marble is in my mancala, and turn doesn't stay the same, it violates checkTurn
    assert all disj b1, b2: Board, h: Int | lastMarbleInMyMancala[b1, b2, h] is sufficient for notCheckTurn[b1, b2, h]
    -- if my mancala loses a marble (which shouldn't happen), and turn stays same, it violates checkTurn
    assert all disj b1, b2: Board, h: Int | myMancalaDecreased[b1, b2, h] is sufficient for notCheckTurn[b1, b2, h]
}

---------------------------------------------------------------

// PREDICATES FOR TESTING UPDATENUMMARBLES
pred startingHoleEmpty[pre, post: Board, startingHole: Int] {
    post.hole[startingHole] = 0
}

pred otherMancalaStaysSame[pre, post: Board, otherMancala: Int] {
    post.hole[otherMancala] = pre.hole[otherMancala]
}

pred numChangedHolesEqualsNumMarbles[pre, post: Board, startingHole: Int] {
    #{ holeNum: Int | post.hole[holeNum] = add[pre.hole[holeNum], 1]} = pre.hole[startingHole]
}

pred player2MoveTwoMarbles[pre, post: Board] {
    wellformed[pre] and wellformed[post]
    pre.turn = Player2
    post.turn = Player2
    pre.hole[5] = 2
    pre.hole[6] = 1
    pre.hole[7] = 2
    post.hole[5] = 0
    post.hole[6] = 2
    pre.hole[7] = 3
    all holeNum: Int | (holeNum >= 0 and holeNum <= 4) implies {
        post.hole[holeNum] = pre.hole[holeNum]
    }
}

pred notUpdateNumMarbles[pre, post: Board, startingHole, otherMancala: Int] {
    not updateNumMarbles[pre, post, startingHole, otherMancala]
}

pred nonLinearMarbleMovement[pre, post: Board] {
    wellformed[pre] and wellformed[post]
    post.hole[3] = add[pre.hole[3], 1]
    post.hole[2] = pre.hole[2]
}

pred allHolesGainMarble[pre, post: Board] {
    all h: Int | post.hole[h] = add[pre.hole[h], 1]
}

pred marbleMoveWrongWay[pre, post: Board] {
    wellformed[pre] and wellformed[post]
    post.hole[2] = 0
    post.hole[1] = add[pre.hole[1],1]
    post.hole[3] = pre.hole[0]
}

test suite for updateNumMarbles {
    -- starting hole must be empty after a player makes a move
    assert all disj b1, b2: Board, h, otherMancala: Int | startingHoleEmpty[b1, b2, h] is necessary for updateNumMarbles[b1, b2, h, otherMancala]
    -- a player shouldn't update the other player's mancala
    assert all disj b1, b2: Board, h, otherMancala: Int | otherMancalaStaysSame[b1, b2, otherMancala] is necessary for updateNumMarbles[b1, b2, h, otherMancala]
    -- the number of holes that gain a marble must be equal to the number of marbles in the starting hole
    assert all disj b1, b2: Board, h, otherMancala: Int | numChangedHolesEqualsNumMarbles[b1, b2, h] is necessary for updateNumMarbles[b1, b2, h, otherMancala]
    -- player2 moving two marbles to their mancala satisfies updateNumMarbles
    assert all disj b1, b2: Board | player2MoveTwoMarbles[b1, b2] is sufficient for updateNumMarbles[b1, b2, 5, 3]
    -- a move that switches turns and starts at hole 6 satisfies updateNumMabrles
    assert all disj b1, b2: Board | turnSwitchMove[b1, b2] is sufficient for updateNumMarbles[b1, b2, 6, 3]
    -- updating num marbles does not interfere with checkturn 
    test expect { updateMarblesAndTurn : {some disj b1, b2: Board, h: Int | checkTurn[b1, b2, 3] and updateNumMarbles[b1, b2, h, 7]} is sat}

}

test suite for notUpdateNumMarbles {
    -- assuming the other player's mancala is hole 7, nonlinear movement from 2 to 3 violates updateNumMarbles
    assert all disj b1, b2: Board, h: Int| nonLinearMarbleMovement[b1, b2] is sufficient for notUpdateNumMarbles[b1, b2, h, 7]
    -- if all holes increase num of marbles by 1, this violates updateNumMarbles
    assert all disj b1, b2: Board, h, otherMancala: Int| allHolesGainMarble[b1, b2] is sufficient for notUpdateNumMarbles[b1, b2, h, otherMancala]
    -- backwards movement from 2 to 1 violates updateNumMarbles
    assert all disj b1, b2: Board, h: Int| nonLinearMarbleMovement[b1, b2] is sufficient for notUpdateNumMarbles[b1, b2, h, 7]
}

---------------------------------------------------------------

// PREDICATES FOR TESTING MOVE
pred correctStartingHole[pre: Board, h: Int] {
    pre.turn = Player1 implies h >= 0 and h <= 2
    pre.turn = Player2 implies h >= 4 and h <= 7
}

pred startingHoleHasMarbles[pre: Board, h: Int] {
    pre.hole[h] != 0
}

pred boardChanges[pre, post: Board] {
    some holeNum: Int | {
        post.hole[holeNum] != pre.hole[holeNum]
    }
}

pred moveOneMarble[pre, post: Board] {
    wellformed[pre] and wellformed[post]
    pre.turn = Player1
    post.turn = Player2
    pre.hole[0] = 1
    pre.hole[1] = 0
    post.hole[0] = 0
    post.hole[1] = 1
    pre.hole[4] = 1
    all holeNum: Int | (holeNum != 0 and holeNum != 1) implies {
        post.hole[holeNum] = pre.hole[holeNum]
    }
}

pred moveMultMarbles[pre, post: Board] {
    wellformed[pre] and wellformed[post]
    pre.turn = Player1
    post.turn = Player2
    pre.hole[0] = 4
    pre.hole[1] = 0
    pre.hole[2] = 0
    pre.hole[3] = 0
    pre.hole[4] = 1
    post.hole[0] = 0
    post.hole[1] = 1
    post.hole[2] = 1
    post.hole[3] = 1
    post.hole[4] = 2
    all holeNum: Int | (holeNum > 4) implies {
        post.hole[holeNum] = pre.hole[holeNum]
    }
}

pred notMove[pre: Board, h: Int, post: Board] {
    not move[pre, h, post]
}

pred moveOnWrongTurn[pre, post: Board] {
    wellformed[pre] and wellformed[post]
    pre.turn = Player2
    post.turn = Player1
    pre.hole[0] = 1
    pre.hole[1] = 0
    post.hole[0] = 0
    post.hole[1] = 1
    pre.hole[4] = 1
    all holeNum: Int | (holeNum != 0 and holeNum != 1) implies {
        post.hole[holeNum] = pre.hole[holeNum]
    }
}

pred moveWrongAmount[pre, post: Board] {
    wellformed[pre] and wellformed[post]
    pre.turn = Player2
    post.turn = Player1
    pre.hole[0] = 2
    pre.hole[1] = 0
    post.hole[0] = 0
    post.hole[1] = 1
    pre.hole[4] = 1
    all holeNum: Int | (holeNum != 0 and holeNum != 1) implies {
        post.hole[holeNum] = pre.hole[holeNum]
    }
}

pred moveWhenGameOver[pre, post: Board] {
    wellformed[pre] and wellformed[post]
    pre.turn = Player2
    post.turn = Player1
    pre.hole[0] = 2
    pre.hole[1] = 0
    post.hole[0] = 0
    post.hole[1] = 1
    pre.hole[4] = 0
    pre.hole[5] = 0
    pre.hole[6] = 0
    all holeNum: Int | (holeNum != 0 and holeNum != 1) implies {
        post.hole[holeNum] = pre.hole[holeNum]
    }
}

pred moveWrongWay[pre, post: Board] {
    wellformed[pre] and wellformed[post]
    pre.turn = Player2
    post.turn = Player1
    pre.hole[0] = 1
    pre.hole[7] = 0
    post.hole[0] = 0
    post.hole[7] = 1
    pre.hole[4] = 1
    all holeNum: Int | (holeNum != 0 and holeNum != 1) implies {
        post.hole[holeNum] = pre.hole[holeNum]
    }
}

test suite for move {
    -- starting hole must be in the respective player's row
    assert all disj b1, b2: Board, h: Int | correctStartingHole[b1, h] is necessary for move[b1, h, b2]
    -- starting hole must have some marles
    assert all disj b1, b2: Board, h: Int | startingHoleHasMarbles[b1, h] is necessary for move[b1, h, b2]
    -- at least one hole has to change when a player makes a move
    assert all disj b1, b2: Board, h: Int | boardChanges[b1, b2] is necessary for move[b1, h, b2]
    -- player 1 moving one marble is sufficient for move
    assert all disj b1, b2: Board | moveOneMarble[b1, b2] is sufficient for move[b1, 0, b2]
    -- player 1 moving multiple marbles is sufficient for move
    assert all disj b1, b2: Board | moveMultMarbles[b1, b2] is sufficient for move[b1, 0, b2]

    test expect { 
        -- move doesn't interfere with wellformed
        wellformedMove: {all disj b1, b2: Board, h: Int | wellformed[b1] and move[b1, h, b2]} is sat
        -- move works with initial board
        initMove: {all disj b1, b2: Board, h: Int | init[b1] and move[b1, h, b2]} is sat
        -- move is satisfiable
        moveOnly: {all disj b1, b2: Board, h: Int | move[b1, h, b2]} is sat
    }
}

test suite for notMove {
    -- moving on wrong turn violates move
    assert all disj b1, b2: Board, h: Int | moveOnWrongTurn[b1, b2] is sufficient for notMove[b1, h, b2]
    -- moving wrong amount of marbles violates move 
    assert all disj b1, b2: Board, h: Int | moveWrongAmount[b1, b2] is sufficient for notMove[b1, h, b2]
    -- moving when game is over violates move 
    assert all disj b1, b2: Board, h: Int | moveWhenGameOver[b1, b2] is sufficient for notMove[b1, h, b2]
    -- moving wrong way violates move 
    assert all disj b1, b2: Board, h: Int | moveWrongWay[b1, b2] is sufficient for notMove[b1, h, b2]
}

---------------------------------------------------------------

// PREDICATES FOR TESTING PLAYER1WIN, PLAYER2WIN, AND ENDGAME
pred threeEmptyHoles[b: Board] {
    some disj h1, h2, h3: Int | b.hole[h1] = 0 and b.hole[h2] = 0 and b.hole[h3] = 0
}

pred holes012Empty[b: Board] {
    b.hole[0] = 0 and b.hole[1] = 0 and b.hole[1] = 0
}

pred holes456Empty[b: Board] {
    b.hole[4] = 0 and b.hole[5] = 0 and b.hole[6] = 0
}

pred notPlayer1Win[b: Board] {
    not player1Win[b]
}

pred notPlayer2Win[b: Board] {
    not player2Win[b]
}

pred notEndGame[b: Board] {
    not endGame[b]
}

pred allNegativeMarbles[b: Board] {
    all h: Int | b.hole[h] < 0
}

pred oneHole012Full[b: Board] {
    some h: Int | h >= 0 and h <= 2 and b.hole[h] > 0
}

pred oneHole456Full[b: Board] {
    some h: Int | h >= 4 and h <= 6 and b.hole[h] > 0
}

pred marbleInEachRow[b: Board] {
    b.hole[0] = 1
    b.hole[4] = 2
}

test suite for player1Win {
    -- must have three empty holes for player 1 to win
    assert all b: Board | threeEmptyHoles[b] is necessary for player1Win[b]
    -- the three empty holes must be 0, 1, 2 (player 1's row)
    assert all b: Board | holes012Empty[b] is necessary for player1Win[b]
    -- the board when player 1 wins can be wellformed
    test expect { wellFormedPLayer1Win : {all b: Board | wellformed[b] and player1Win[b]} is sat}
}

test suite for notPlayer1Win {
    -- if all holes have negative marbles, player1 doesn't win
    assert all b: Board | allNegativeMarbles[b] is sufficient for notPlayer1Win[b]
    -- if one hole between 0 and 2 has marbles, plaer1 doesn't win
    assert all b: Board | oneHole012Full[b] is sufficient for notPlayer1Win[b]
}

test suite for player2Win {
    -- must have three empty holes for player 2 to win
    assert all b: Board | threeEmptyHoles[b] is necessary for player2Win[b]
    -- the three empty holes must be 4, 5, 6 (player 2's row)
    assert all b: Board | holes456Empty[b] is necessary for player2Win[b]
    -- the board when player 2 wins can be wellformed
    test expect { wellFormedPLayer2Win : {all b: Board | wellformed[b] and player2Win[b]} is sat}
}

test suite for notPlayer2Win {
    -- if all holes have negative marbles, player2 doesn't win
    assert all b: Board | allNegativeMarbles[b] is sufficient for notPlayer2Win[b]
    -- if one hole between 4 and 6 has marbles, plaer2 doesn't win
    assert all b: Board | oneHole456Full[b] is sufficient for notPlayer2Win[b]
}

test suite for endGame {
    -- must have three empty holes for game to end
    assert all b: Board | threeEmptyHoles[b] is necessary for endGame[b]
    -- player 1 winning will end game
    assert all b: Board | player1Win[b] is sufficient for endGame[b]
    -- player 2 winning will end game
    assert all b: Board | player2Win[b] is sufficient for endGame[b]
    -- both players can win at once (though not expected in game)
    test expect { bothPlayersWin: {all b: Board | player1Win[b] and player2Win[b] and endGame[b]} is sat}
}

test suite for notEndGame {
    -- marbles in both row 1 and 2 will not end game
    assert all b: Board | marbleInEachRow[b] is sufficient for notEndGame[b]
    -- a full board will not end game
    assert all b: Board | fullBoard[b] is sufficient for notEndGame[b]
    -- initial board will not endgame
    assert all b: Board | init[b] is sufficient for notEndGame[b]
}

---------------------------------------------------------------

// PREDICATES FOR TESTING DONOTHING
pred boardStaysSame[pre, post: Board]{
    all h: Int | post.hole[h] = pre.hole[h]
}

pred playerStaysSame[pre, post: Board] {
    post.turn = pre.turn
}

pred notDoNothing[pre, post: Board] {
    not doNothing[pre, post]
}

pred playerChanges[pre, post: Board] {
    post.turn != pre.turn
}

test suite for doNothing {
    -- all holes must stay the same when doing nothing
    assert all disj b1, b2: Board | boardStaysSame[b1, b2] is necessary for doNothing[b1, b2]
    -- player turn must stay the same when doing nothing
    assert all disj b1, b2: Board | playerStaysSame[b1, b2] is necessary for doNothing[b1, b2]
    -- other mancala must stay the same when doing nothing
    assert all disj b1, b2: Board | otherMancalaStaysSame[b1, b2, 3] is necessary for doNothing[b1, b2]
    -- game must be over when doing nothing
    assert all disj b1, b2: Board | endGame[b1] is necessary for doNothing[b1, b2]

    test expect { 
        -- doNothing doesn't interfere with wellformed
        wellformedDoNothing: {all disj b1, b2: Board | wellformed[b1] and doNothing[b1, b2]} is sat
        -- doNothing works with init
        initDoNothing: {all disj b1, b2: Board | init[b1] and doNothing[b1, b2]} is sat
        -- doNothing is satisfiable
        doNothingOnly: {all disj b1, b2: Board | doNothing[b1, b2]} is sat
    }
}

test suite for notDoNothing {
    -- any board change violates doNothing
    assert all disj b1, b2: Board | boardChanges[b1, b2] is sufficient for notDoNothing[b1, b2]
    -- player changing violates doNothing
    assert all disj b1, b2: Board | playerChanges[b1, b2] is sufficient for notDoNothing[b1, b2]
    -- moving one marbles violates doNothing
    assert all disj b1, b2: Board | moveOneMarble[b1, b2] is sufficient for notDoNothing[b1, b2]
}

---------------------------------------------------------------

// PREDICATES FOR TESTING GAME_TRACE
pred wellformedBoards {
    all b: Board | wellformed[b]
}

pred oneMove {
    init[Game.first]
    some Game.next[Game.first]
    some holeNum: Int | move[Game.first, holeNum, Game.next[Game.first]]
    wellformedBoards
}

pred someMove {
    some b: Board | {
        some Game.next[b]
        some holeNum: Int | move[b, holeNum, Game.next[b]]
    }
}

pred oneDoNothing {
    init[Game.first]
    some Game.next[Game.first]
    doNothing[Game.first, Game.next[Game.first]]
    wellformedBoards
}

pred twoTransitionsAtOnce {
    wellformedBoards
    some b: Board | {
        some Game.next[b]
        doNothing[b, Game.next[b]]
        some holeNum: Int | move[b, holeNum, Game.next[b]]
    }
}

test suite for game_trace {
    assert all g: Game | init[g.first] is necessary for game_trace 
    assert all g: Game | wellformedBoards is necessary for game_trace

    test expect { 
        -- initial move satisfies game_trace
        initialMove: {oneMove and game_trace} is sat
        -- some move satisfies game_trace
        randomMove: {someMove and game_trace} is sat
        -- can't do nothing initially
        initialDoNothing: {oneDoNothing and game_trace} is unsat
        -- can't do two transitions at once
        twoTransitions: {twoTransitionsAtOnce and game_trace} is unsat
    }
}