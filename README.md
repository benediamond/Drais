# Drais
A chess engine written in Haskell

A basic chess engine written in Haskell, using few external libraries or fancy features. As far as I know, Drais is the most complete chess engine written in Haskell thus far.

Drais employs an iterative-deepening approach, repeatedly calling an internal search routine with successively higher levels of depth, and retaining in each case a principal variation. This search routine itself performs the "NegaScout" or "PVS" variant of Alpha-Beta pruning upon each call, using a move ordering informed by the recent principal variation as well as by heuristic considerations.

The search depth parameter passed in each case into the main search routine represents the maximum search depth of its Floyd-style quiescence search (see Knuth and Moore, An Analysis of Alpha-Beta Pruning, p. 302), in which "likely" (i.e., capture) moves decrement the remaining search depth less than do unlikely moves.

The engine is a bit slow and rudimentary, but chugs along; an 8-depth search in the middlegame will typically take around 20-30 seconds.

I've also written a JavaScript GUI. I've compiled Drais into JavaScript using Haste; I'd like to thank them for their work. A live version of the applet is available at math.jhu.edu/~bdiamond/chess/chess.html.

As it's currently written, the first argument of the main routine is the FEN-notation string of some game; the second is the search depth. Here is a sample input and output:
```
ghc --make Main.hs
./Main "1r5k/1b2K2p/7p/2pp3P/7B/5pp1/4p3/5r2 w - - 0 3" 12
_ r _ _ _ _ _ k
_ b _ _ K _ _ p
_ _ _ _ _ _ _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ B
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: True, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 7.136869e18, Unlikelihood: 0
(6,1)'r' (5,2)'p' (7,3)'p' (6,3)'p' (8,4)'B' (8,5)'P' (4,5)'p' (3,5)'p' (8,6)'p' (8,7)'p' (5,7)'K' (2,7)'b' (8,8)'k' (2,8)'r'
_ r _ _ _ _ _ k
_ b _ _ _ K _ p
_ _ _ _ _ _ _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ B
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: False, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 7.512494e18, Unlikelihood: 2
(6,7)'K' (6,1)'r' (5,2)'p' (7,3)'p' (6,3)'p' (8,4)'B' (8,5)'P' (4,5)'p' (3,5)'p' (8,6)'p' (8,7)'p' (2,7)'b' (8,8)'k' (2,8)'r'
_ _ _ _ _ _ r k
_ b _ _ _ K _ p
_ _ _ _ _ _ _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ B
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: True, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 7.9078883e18, Unlikelihood: 2
(7,8)'r' (6,7)'K' (6,1)'r' (5,2)'p' (7,3)'p' (6,3)'p' (8,4)'B' (8,5)'P' (4,5)'p' (3,5)'p' (8,6)'p' (8,7)'p' (2,7)'b' (8,8)'k'
_ _ _ _ _ _ r k
_ b _ _ _ K _ p
_ _ _ _ _ B _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ _
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: False, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 8.324093e18, Unlikelihood: 2
(6,6)'B' (7,8)'r' (6,7)'K' (6,1)'r' (5,2)'p' (7,3)'p' (6,3)'p' (8,5)'P' (4,5)'p' (3,5)'p' (8,6)'p' (8,7)'p' (2,7)'b' (8,8)'k'
_ _ _ _ _ _ _ k
_ b _ _ _ K r p
_ _ _ _ _ B _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ _
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: True, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 8.7622033e18, Unlikelihood: 2
(7,7)'r' (6,6)'B' (6,7)'K' (6,1)'r' (5,2)'p' (7,3)'p' (6,3)'p' (8,5)'P' (4,5)'p' (3,5)'p' (8,6)'p' (8,7)'p' (2,7)'b' (8,8)'k'
_ _ _ _ _ _ _ k
_ b _ _ _ K B p
_ _ _ _ _ _ _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ _
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: False, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -13.4, Eval: 9.223372e18, Unlikelihood: 1
(7,7)'B' (6,7)'K' (6,1)'r' (5,2)'p' (7,3)'p' (6,3)'p' (8,5)'P' (4,5)'p' (3,5)'p' (8,6)'p' (8,7)'p' (2,7)'b' (8,8)'k'
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
Turn: True, Castling: [], Emp: (0,0),  Heuristic: 0.0, Eval: 9.2224495e18, Unlikelihood: 0
```
Drais uses a "lazy" legality checking technique whereby a move is not checked for legality until after its visitation has begun and its children have been generated. Determining the legality of a move requires knowing its children (to determine whether the king "gets taken", etc.), so delaying this step until the next generation facilitates parsimony and speed.

Differing from most minimax formulations, Drais does not determine a node's evaluation by simply "lifting" the eval of its best child. Drais instead uses a "dampening" function whereby a node's evaluation is given by a weighted average of its best child's evaluation together with its own heuristic evaluation (where the former gets the vast majority of the weight). This dampening method has a number of advantages. For one, it provides a seamless way of convincing the engine to prefer to undertake a winning move or variation immediately, as opposed to delaying it with repeated checks or exchanges. Along a similar vein, it provides a parsimonious way of directing the engine to the shortest-possible mating (and longest-possible getting-mated) sequences. Finally, dampening has technical advantages with regard to the above "lazy" legality-checking scheme. As illegal positions are not deleted from the tree but merely given mating evaluations upon exit of visitation, dampening directs the engine to choose a legal (but eventually mated) position over a flatly illegal one.

This dampening procedure creates complications with respect to the Alpha-Beta and PVS algorithms. Indeed, the local parameters alpha and beta must serve to determine the suitability or rejectability of a child's eval with regard to the higher nodes in the tree against which it will eventually be compared, and comparison across levels is tricky because eval is affine-linearly transformed each time it is lifted. We adopt a procedure whereby the relevant alpha and beta parameters are inverted under a node's weighting function before being made to serve as benchmarks for that node's children. As the dampening function is bijective and order-preserving, order determinations made at the level of the child suffice for comparisons after all quantites are transformed.

Please contact me if you have any comments: bdiamond@math.jhu.edu
