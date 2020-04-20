-------------------------- MODULE ChessRoyalMurder --------------------------
EXTENDS Integers
(***************************************************************************)
(* The set of all valid squares on the board that the knights can move to. *)
(* The squares are represented as 2-tuples <<File, Rank>>: (x = valid      *)
(* square)                                                                 *)
(*     Rank                                                                *)
(*     8 o o o x o o o o                                                   *)
(*     7 o o o o o o o o                                                   *)
(*     6 o x x x x x x x                                                   *)
(*     5 x x x x x x x x                                                   *)
(*     4 x x x x x x x x                                                   *)
(*     3 x x x x x x x x                                                   *)
(*     2 o o o o o o o o                                                   *)
(*     1 o x o o o o x o                                                   *)
(*       1 2 3 4 5 6 7 8 File                                              *)
(*                                                                         *)
(* This set includes their starting squares, b1 and g1, the black Queen's  *)
(* square, d8, and any square not occupied by another piece excluding a6,  *)
(* which the black knight can move to.  There are other squares that the   *)
(* knights could visit, namely a1, h1, a8, b8, g8, and h8, but they aren't *)
(* necessary to include to find a solution.                                *)
(***************************************************************************)
CONSTANTS Squares

(***************************************************************************)
(* These variables are the board location of each knight starting on files *)
(* B/G and the number of moves each knight has made.                       *)
(***************************************************************************)
VARIABLES knightBpos, knightGpos, knightBmove, knightGmove

(***************************************************************************)
(* The knights must always be on valid squares.  The number of moves must  *)
(* always be a natural number.                                             *)
(***************************************************************************)
TypeOK ==
    /\ knightBpos \in Squares
    /\ knightGpos \in Squares
    /\ knightBmove \in Nat
    /\ knightGmove \in Nat
    
(***************************************************************************)
(* The initial state of the board.  The knights are on their starting      *)
(* squares and they haven't moved.                                         *)
(***************************************************************************)
Init ==
    /\ knightBpos = <<2, 1>>
    /\ knightGpos = <<7, 1>>
    /\ knightBmove = 0
    /\ knightGmove = 0
    
(***************************************************************************)
(* An action describing all possible knight moves.                         *)
(***************************************************************************)
KnightMove(knightpos) == 
    /\ knightpos' \in Squares
    /\ \/ /\ knightpos[1]' = knightpos[1] - 2
          /\ \/ knightpos[2]' = knightpos[2] + 1
             \/ knightpos[2]' = knightpos[2] - 1
       \/ /\ knightpos[1]' = knightpos[1] + 2
          /\ \/ knightpos[2]' = knightpos[2] + 1
             \/ knightpos[2]' = knightpos[2] - 1
       \/ /\ knightpos[1]' = knightpos[1] - 1
          /\ \/ knightpos[2]' = knightpos[2] + 2
             \/ knightpos[2]' = knightpos[2] - 2
       \/ /\ knightpos[1]' = knightpos[1] + 1
          /\ \/ knightpos[2]' = knightpos[2] + 2
             \/ knightpos[2]' = knightpos[2] - 2
          
(***************************************************************************)
(* This is what it means to move the knight starting on b1:                *)
(*                                                                         *)
(* It is moved, its move count increases, and the other knight doesn't     *)
(* move.                                                                   *)
(***************************************************************************)   
KnightBMove ==
    /\ KnightMove(knightBpos)
    /\ knightBmove' = knightBmove + 1
    /\ UNCHANGED <<knightGpos, knightGmove>>
    
(***************************************************************************)
(* This is what it means to move the knight starting on g1:                *)
(*                                                                         *)
(* It is moved, its move count increases, and the other knight doesn't     *)
(* move.                                                                   *)
(***************************************************************************)
KnightGMove ==
    /\ KnightMove(knightGpos)
    /\ knightGmove' = knightGmove + 1
    /\ UNCHANGED <<knightBpos, knightBmove>>
    
(***************************************************************************)
(* This describes each possible move for white.  Either knight is moved,   *)
(* but they can't end up on the same square.                               *)
(***************************************************************************)
Next ==
    /\ (KnightBMove \/ KnightGMove)
    /\ knightBpos' /= knightGpos'
    
(***************************************************************************)
(* By telling the model checker that a solution to the puzzle does not     *)
(* exist as described by this invariant, it will produce a counterexample  *)
(* when it finds one, which is a solution.                                 *)
(***************************************************************************)
Solution ==
    ~(\/ (knightBpos = <<4, 8>> /\ knightGpos = <<7, 1>> /\ knightBmove = 8)
      \/ (knightBpos = <<7, 1>> /\ knightGpos = <<4, 8>> /\ knightGmove = 8))

=============================================================================

