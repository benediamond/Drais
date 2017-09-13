# Drais
A chess engine written in Haskell

Drais is a basic chess engine written in Haskell, using no external libraries. Drais occasionally plays on the [FICS](http://ficsgames.org/cgi-bin/search.cgi?player=benediamond&action=History), where it enjoys ratings of 1500-1600 in blitz and 1900-2000 in lightning.

Drais employs an iterative-deepening approach, repeatedly calling an internal search routine with successively higher levels of depth and retaining after each iteration a principal variation. This search routine itself performs the "Principal Variation Search" or "NegaScout" variant of Alpha-Beta pruning upon each call, using move orderings informed by the most recently retained principal variation as well as by heuristic pre-sorts (that is, by Internal Iterative Deepning searches of minimal depth).

The search depth parameter passed in each successive iteration into the main search routine represents the maximum search depth of its Floyd-style quiescence search (see Knuth and Moore, An Analysis of Alpha-Beta Pruning, p. 302), in which "likely" (i.e., capture) moves decrement the remaining depth less than do unlikely moves.

Drais uses a heuristic evaluation function which incorporates material, castling, advanced pawns, central rooks, and other similar considerations.

For testing purposes during the earlier stages of the engine's development, I wrote a JavaScript GUI. Drais can be compiled into JavaScript using Haste; be advised, however, that, significant slowdowns result. A live version of this applet can be found [here](http://www.math.jhu.edu/~bdiamond/chess/chess.html).

As it's written in the file uploaded here, the first argument of the main routine is the FEN-notation string of some game; the second is a search depth. Given these, Drais will compute and print a principal variation. Here is a sample input and output:
```
ghc --make -O2 Main.hs
./Main "1r5k/1b2K2p/7p/2pp3P/7B/5pp1/4p3/5r2 w - - 0 3" 12
_ r _ _ _ _ _ k
_ b _ _ K _ _ p
_ _ _ _ _ _ _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ B
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: True, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 6.779347985910482e18, Unlikelihood: 0
(6,1)'r' (5,2)'p' (7,3)'p' (6,3)'p' (8,4)'B' (8,5)'P' (4,5)'p' (3,5)'p' (8,6)'p' (8,7)'p' (5,7)'K' (2,7)'b' (8,8)'k' (2,8)'r'
_ r _ _ _ _ _ k
_ b _ _ _ K _ p
_ _ _ _ _ _ _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ B
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: False, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 7.136155774642613e18, Unlikelihood: 2
(6,7)'K' (6,1)'r' (5,2)'p' (7,3)'p' (6,3)'p' (8,4)'B' (8,5)'P' (4,5)'p' (3,5)'p' (8,6)'p' (8,7)'p' (2,7)'b' (8,8)'k' (2,8)'r'
_ _ _ _ _ _ r k
_ b _ _ _ K _ p
_ _ _ _ _ _ _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ B
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: True, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 7.511742920676435e18, Unlikelihood: 2
(7,8)'r' (6,7)'K' (6,1)'r' (5,2)'p' (7,3)'p' (6,3)'p' (8,4)'B' (8,5)'P' (4,5)'p' (3,5)'p' (8,6)'p' (8,7)'p' (2,7)'b' (8,8)'k'
_ _ _ _ _ _ r k
_ b _ _ _ K _ p
_ _ _ _ _ B _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ _
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: False, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 7.907097811238353e18, Unlikelihood: 2
(6,6)'B' (7,8)'r' (6,7)'K' (6,1)'r' (5,2)'p' (7,3)'p' (6,3)'p' (8,5)'P' (4,5)'p' (3,5)'p' (8,6)'p' (8,7)'p' (2,7)'b' (8,8)'k'
_ _ _ _ _ _ _ k
_ b _ _ _ K r p
_ _ _ _ _ B _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ _
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: True, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 8.323260853935109e18, Unlikelihood: 2
(7,7)'r' (6,6)'B' (6,7)'K' (6,1)'r' (5,2)'p' (7,3)'p' (6,3)'p' (8,5)'P' (4,5)'p' (3,5)'p' (8,6)'p' (8,7)'p' (2,7)'b' (8,8)'k'
_ _ _ _ _ _ _ k
_ b _ _ _ K B p
_ _ _ _ _ _ _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ _
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: False, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -13.4, Eval: 8.761327214668536e18, Unlikelihood: 1
(7,7)'B' (6,7)'K' (6,1)'r' (5,2)'p' (7,3)'p' (6,3)'p' (8,5)'P' (4,5)'p' (3,5)'p' (8,6)'p' (8,7)'p' (2,7)'b' (8,8)'k'
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
_ _ _ _ _ _ _ _
Turn: True, Castling: [], Emp: (0,0),  Heuristic: 0.0, Eval: 9.22244969965109e18, Unlikelihood: 0
```
Differing from most minimax formulations, Drais does not determine a node's evaluation by simply "lifting" the evaluation of its best child. Drais instead uses a "dampening" function whereby a node's evaluation is determined by a weighted average of its best child's evaluation together with its own heuristic evaluation (where the former gets the vast majority of the weight). This "distance dampening" method has a number of advantages. For one, it provides a seamless way of convincing the engine to prefer to undertake a winning move or variation immediately, as opposed to (being indifferent to) delaying it with repeated checks or exchanges. Along a similar vein, it provides a parsimonious way of directing the engine to the shortest-possible mating (and longest-possible getting-mated) sequences. Finally, dampening has technical advantages with regard to the above "lazy" legality-checking scheme. As illegal positions are not deleted from the tree but merely given mating evaluations upon exit of visitation, dampening directs the engine to choose a legal (but eventually mated) position over a flatly illegal one.

This dampening procedure creates complications with respect to the Alpha-Beta and PVS algorithms. Indeed, the local parameters alpha and beta must serve to determine the suitability or rejectability of a child's eval with regard to the higher nodes in the tree against which it will eventually be compared, and comparison across levels is tricky because eval is affine-linearly transformed each time it is lifted. We adopt a procedure whereby the relevant alpha and beta parameters are inverted under a node's weighting function before being made to serve as benchmarks for that node's children. As the dampening function is bijective and order-preserving, order determinations made at the level of the child suffice for comparisons made at higher levels of the tree after all quantites are transformed.

Please contact me if you have any comments: bdiamond@math.jhu.edu
