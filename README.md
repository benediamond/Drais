# Drais
A chess engine written in Haskell

Drais is a chess engine written in Haskell. Drais occasionally plays on the [FICS](http://ficsgames.org/cgi-bin/search.cgi?player=benediamond&action=History), where it boasts ratings of about 1600 in blitz and 2000 in lightning.

Drais employs an iterative-deepening approach, iteratively calling an internal search routine with successively higher levels of depth, and retaining, after each iteration, a principal variation. The internal search routine itself performs the "Principal Variation Search" or "NegaScout" variant of Alpha-Beta pruning upon each call, using a move ordering informed by the recently retained principal variation as well as by heuristic pre-sorts (that is, by Internal Iterative Deepning searches of trivial depth).

The depth parameter passed into the main search routine represents the maximum search depth of its Floyd-style quiescence search (see Knuth and Moore, [An Analysis of Alpha-Beta Pruning](https://pdfs.semanticscholar.org/dce2/6118156e5bc287bca2465a62e75af39c7e85.pdf), p. 302), in which "violent" moves (i.e. captures, catles, and queen-promotions) decrement the remaining depth less than do "quiet" moves (i.e. non-captures and underpromotions).

Drais's heuristic evaluation function incorporates material, castling, pawn advancement, rook centrality, and other similar considerations.

For testing purposes during the earlier stages of the engine's development, I wrote a JavaScript GUI. Drais can be compiled into JavaScript using [Haste](https://haste-lang.org/); be advised, however, that, significant slowdowns result. A live version of this applet can be found [here](http://www.math.jhu.edu/~bdiamond/chess/chess.html).

`Main.hs`'s main routine takes two parameters: an FEN-notation string and a search depth. Given these, Drais will compute and print a principal variation. Here is a sample input and output:
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
_ r _ _ _ _ _ k
_ b _ _ _ K _ p
_ _ _ _ _ _ _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ B
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: False, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 7.136155774642613e18, Unlikelihood: 2
_ _ _ _ _ _ r k
_ b _ _ _ K _ p
_ _ _ _ _ _ _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ B
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: True, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 7.511742920676435e18, Unlikelihood: 2
_ _ _ _ _ _ r k
_ b _ _ _ K _ p
_ _ _ _ _ B _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ _
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: False, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 7.907097811238353e18, Unlikelihood: 2
_ _ _ _ _ _ _ k
_ b _ _ _ K r p
_ _ _ _ _ B _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ _
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: True, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -18.4, Eval: 8.323260853935109e18, Unlikelihood: 2
_ _ _ _ _ _ _ k
_ b _ _ _ K B p
_ _ _ _ _ _ _ p
_ _ p p _ _ _ P
_ _ _ _ _ _ _ _
_ _ _ _ _ p p _
_ _ _ _ p _ _ _
_ _ _ _ _ r _ _
Turn: False, Castling: [True,True,True,True], Emp: (0,0),  Heuristic: -13.4, Eval: 8.761327214668536e18, Unlikelihood: 1
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
Not unusually, Drais understands legality "lazily", in that a position is not checked for legality until after its own visitation has begun and its pseudo-children have been generated. As determining the legality of a position requires knowing its pseudo-children (to determine whether the king "can get taken", etc.), delaying this step facilitates parsimony and speed.

Marking a departure from minimax's classical formulations, Drais determines a node's evaluation not simply by "lifting" the evaluation of its best child, but rather by (weighted) averaging this child's eval with the node's _own_ static eval (the former gets the vast majority of the weight). Macroscopically, this amounts to an exponential "dampening" of a position's heuristic eval as it progresses from leaf to root.

This protocol confers a number of advantages. For one, it seamlessly impels the engine to undertake winning moves or variations immediately, as opposed to (being indifferent to) delaying them with repeated checks or exchanges. Along a similar vein, it parsimoniously directs the engine toward the shortest-possible _mate_ and longest-possible _mated_ sequences. Relatedly, dampening has technical advantages with regard to the aforementioned lazy legality-checking scheme. Illegal positions are not deleted from the tree after visitation, but merely given mating evaluations; dampening thus directs the engine to select legal (but eventually mated) positions over flatly illegal ones. Experimental work has suggested an optimal dampening factor of about 0.95.

This dampening procedure creates complications with respect to the Alpha-Beta and PVS algorithms. Indeed, the local parameters alpha and beta must serve to determine the suitability or rejectability of a child's eval with regard to the higher nodes in the tree against which it will eventually be compared, and comparison across levels is non-trivial because eval is affine-linearly transformed each time it is lifted. We adopt a procedure whereby the relevant alpha and beta parameters are inverted under a node's weighting function before being made to serve as benchmarks for that node's children. As the dampening function is bijective and order-preserving, order determinations made at the level of the child suffice for comparisons made at higher levels of the tree after all quantites are transformed.

Please contact me if you have any comments: bdiamond@math.jhu.edu
