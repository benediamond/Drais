module Main where

import System.Environment
import Data.List
import Data.Array
import Data.Char
import Data.Maybe
--import Haste.Foreign
--import Haste.Prim

-- |The "Locations" type synonym encodes a piece list. Positions are in algebraic notation. e.g., the starting position: [((1,1),'R'), ((2,1),'N'), ... , ((8,8), 'r')]
type Locations                                = [((Int, Int), Char)]
-- |The "Game" data type encodes a board state and all of its relevant accompanying information.
data Game                                     = Game {locations     :: Locations, -- position's "piece list"
                                                      turn          :: Bool, -- whose turn is it? True iff white
                                                      cancastle     :: [Bool], -- [K Q k q] -- whether the respective four castle types are forever off limits. True iff off-limits.
                                                      incentive     :: [Bool], -- [K Q k q] -- which castles have actually occurred. This is used _internally_ by the engine to incentivize castling
                                                      unlikelihood  :: Int, -- by how much should this position decrement the search depth? Lower for more "likely" moves, e.g. captures
                                                      enpassant     :: (Int,Int), -- en passant target square
                                                      heur          :: Double, -- instantaneous heurstic eval
                                                      eval          :: Double, -- minimax eval
                                                      child         :: Maybe Game} -- the principal variation, or "best" child node

-- |Performs an iterative-deepening search with user-supplied (ultimate) depth on user-provided game. Operates as a wrapper, repeatedly calling the "populate" routine.
deepening                                     :: Int->Game->Game
deepening 0 game                              = populate 0 [False,False,False,False] (specials False) (specials True) game
deepening n game                              = populate n [False,False,False,False] (specials False) (specials True) (deepening (n - 1) game)

-- |Fundamental routine which populates a game with a principal variation of user-specified (maximum) depth.
populate                                      :: Int->[Bool]->Double->Double->Game->Game -- (max) depth, _parent_'s cancastle flags, alpha, beta, game --> game
populate n po a b (Game l t ca o u m h e ch)  = if n <= 0 then Game l t ca o u m h h Nothing else if legal then Game l t ca o u m h score (Just winner) else Game l t ca o u m h (specials t) Nothing
    where
        score                                 = if (if t then (<) else (>)) (eval winner) ((specials . not $ t) * 0.999) && stale then 0 else wt True h $ eval winner
            where
                stale                         = (if t then (>) else (<)) (eval . populate 1 o (specials False) (specials True) $ Game l (not t) ca o u m h e ch) ((specials . not $ t) * 0.999)
        winner                                = best t (Game [] (not t) [] [] 0 (0,0) 0.0 ((specials . not $ t) * 0.9999) Nothing) propagated
            where
                best t run []                 = run
                best t run (x:xs)             = best t (if if t then eval x > eval run else eval x < eval run then x else run) xs
        propagated                            = alphabeta True (if t then inva else invb) ready
            where
                alphabeta _ _ []              = [] -- alpha-beta pruning algorithm. first parameter: "is it the principal variation?" if not, uses a null window.
                alphabeta p run (x:xs)        = if t then if run > invb + 0.00001 then [] else let try = populate (n - unlikelihood x) o run (if p then invb else run) x;
                                                                                                   redo = if (not p) && run < eval try && eval try < invb then populate (n - unlikelihood x) o (eval try) invb x else try
                                                                                                   in redo:alphabeta False (max run (eval redo)) xs
                                                     else if run < inva - 0.00001 then [] else let try = populate (n - unlikelihood x) o (if p then inva else run) run x;
                                                                                                   redo = if (not p) && inva < eval try && eval try < run then populate (n - unlikelihood x) o inva (eval try) x else try
                                                                                                   in redo:alphabeta False (min run (eval redo)) xs
                (inva, invb)                  = (wt False h a, wt False h b)
        ready                                 = if isNothing ch || (null . locations . fromJust) ch then heursort else let old = fromJust ch in old:filter ((/= locations old) . locations) heursort
        heursort                              = sortBy (heurcompare (not t)) heured
            where
                heurcompare t g1 g2
                    | heur g1 > heur g2       = if t then GT else LT
                    | heur g1 < heur g2       = if t then LT else GT
                    | otherwise               = EQ
        heured                                = map heuristic newbies
        legal                                 = not (null l) && case () of
                                                  _ | po!!0 /= o!!0 -> all (\l->all (\p -> (isUpper . snd) p || fst p /= (5,1) && fst p /= (6,1) && fst p /= (7,1)) l) (map locations newbies)
                                                    | po!!1 /= o!!1 -> all (\l->all (\p -> (isUpper . snd) p || fst p /= (3,1) && fst p /= (4,1) && fst p /= (5,1)) l) (map locations newbies)
                                                    | po!!2 /= o!!2 -> all (\l->all (\p -> (isLower . snd) p || fst p /= (5,8) && fst p /= (6,8) && fst p /= (7,8)) l) (map locations newbies)
                                                    | po!!3 /= o!!3 -> all (\l->all (\p -> (isLower . snd) p || fst p /= (3,8) && fst p /= (4,8) && fst p /= (5,8)) l) (map locations newbies)
                                                    | otherwise     -> all (\l->any (\p -> snd p == if (not t) then 'K' else 'k') l) (map locations newbies) -- has the king gotten taken?
        newbies                               = (if t then concat [if all ((/= temp) . fst) l then if snd temp /= 8 then [Game ((temp,'P'):filter (/= i) l) (not t) ca o (2) (0,0) 0.0 0.0 Nothing] else [Game ((temp,'Q'):filter (/= i) l) (not t) ca o (1) (0,0) 0.0 0.0 Nothing, Game ((temp,'R'):filter (/= i) l) (not t) ca o (2) (0,0) 0.0 0.0 Nothing, Game ((temp,'B'):filter (/= i) l) (not t) ca o (2) (0,0) 0.0 0.0 Nothing, Game ((temp,'N'):filter (/= i) l) (not t) ca o (2) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((=='P') . snd) l, let temp = ((fst . fst) i, (snd . fst) i + 1)] ++ -- white pawn moves one square or promotes
                                                           concat [if (snd . fst) i == 2 && all (\p -> fst p /= temp2 && fst p /= temp1) l then [Game ((temp2,'P'):filter (/= i) l) (not t) ca o (2) temp1 0.0 0.0 Nothing] else [] | i <- filter ((=='P') . snd) l, let temp2 = ((fst . fst) i, (snd . fst) i + 2), let temp1 = ((fst . fst) i, (snd . fst) i + 1)] ++ -- white pawn moves two squares
                                                           concat [if bounds temp && any (\p -> fst p == temp && (isLower . snd) p) l then if snd temp /= 8 then [Game ((temp,'P'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) ca o (1) (0,0) 0.0 0.0 Nothing] else let newca = (replace 2 (ca!!2 || temp == (8,8)) . replace 3 (ca!!3 || temp == (1,8)) $ ca) in [Game ((temp,'Q'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) newca o (1) (0,0) 0.0 0.0 Nothing, Game ((temp,'R'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) newca o (2) (0,0) 0.0 0.0 Nothing, Game ((temp,'B'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) newca o (2) (0,0) 0.0 0.0 Nothing, Game ((temp,'N'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) newca o (2) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((=='P') . snd) l, j <-[-1, 1], let temp = ((fst . fst) i + j, (snd . fst) i + 1)] ++ -- white pawn takes diagonally
                                                           concat [if temp==m then let target = (fst temp, snd temp - 1) in [Game ((temp,'P'):(filter (/= i) . filter ((/= target) . fst) $ l)) (not t) ca o (1) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((=='P') . snd) l, j <-[-1, 1], let temp = ((fst . fst) i + j, (snd . fst) i + 1)] ++ -- white pawn takes en passant
                                                           concat [if bounds temp && all (\p -> all ((/= p) . fst) l) (init . tail . myrange $ (fst i, temp)) && all (\p -> fst p /= temp || (isLower . snd) p) l then [Game ((temp,'R'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) (replace 2 (ca!!2 || temp == (8,8)) . replace 3 (ca!!3 || temp == (1,8)) . replace 0 (fst i==(8,1) || ca!!0) . replace 1 (fst i == (1,1) || ca!!1) $ ca) o (if any ((== temp) . fst) l then (1) else (2)) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((== 'R') . snd) l, j <- filter (/=(0,0)) (range((-8,0),(8,0))++range((0,-8),(0,8))), let temp = ((fst . fst) i + fst j, (snd . fst) i + snd j)] ++ -- white rook moves or takes
                                                           concat [if bounds temp && all (\p -> all ((/= p) . fst) l) (init . tail . myrange $ (fst i, temp)) && all (\p -> fst p /= temp || (isLower . snd) p) l then [Game ((temp,'B'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) (replace 2 (ca!!2 || temp == (8,8)) . replace 3 (ca!!3 || temp == (1,8)) $ ca) o (if any ((== temp) . fst) l then (1) else (2)) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((=='B') . snd) l, j <- filter (/=(0,0)) ([(k,k) | k <- [-8..8]]++[(k,-k) | k <- [-8..8]]), let temp = ((fst . fst) i + fst j, (snd . fst) i + snd j)] ++ -- white bishop moves or takes
                                                           concat [if bounds temp && all (\p -> fst p /= temp || (isLower . snd) p) l then [Game ((temp,'N'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) (replace 2 (ca!!2 || temp == (8,8)) . replace 3 (ca!!3 || temp == (1,8)) $ ca) o (if any ((== temp) . fst) l then (1) else (2)) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((=='N') . snd) l, j <- [(1,2),(2,1),(1,-2),(-2,1),(-1,2),(2,-1),(-1,-2),(-2,-1)], let temp = ((fst . fst) i + fst j, (snd . fst) i + snd j)] ++ -- white knight moves or takes
                                                           concat [if bounds temp && all (\p -> all ((/= p) . fst) l) (init . tail . myrange $ (fst i, temp)) && all (\p -> fst p /= temp || (isLower . snd) p) l then [Game ((temp,'Q'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) (replace 2 (ca!!2 || temp == (8,8)) . replace 3 (ca!!3 || temp == (1,8)) $ ca) o (if any ((== temp) . fst) l then (1) else (2)) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((== 'Q') . snd) l, j <- filter (/=(0,0)) ([(k,k) | k <- [-8..8]]++[(k,-k) | k <- [-8..8]]++(range((-8,0),(8,0))++range((0,-8),(0,8)))), let temp = ((fst . fst) i + fst j, (snd . fst) i + snd j)] ++ -- white queen moves or takes
                                                           concat [if bounds temp && all (\p -> fst p /= temp || (isLower . snd) p) l then [Game ((temp,'K'):(filter (/= king) . filter ((/= temp) . fst) $ l)) (not t) (replace 2 (ca!!2 || temp == (8,8)) . replace 3 (ca!!3 || temp == (1,8)) . replace 0 True . replace 1 True $ ca) o (if any ((== temp) . fst) l then (1) else (2)) (0,0) 0.0 0.0 Nothing] else [] | j <- [(-1,1),(0,1),(1,1),(1,0),(1,-1),(0,-1),(-1,-1),(-1,0)], let temp = ((fst . fst) king + fst j, (snd . fst) king + snd j)] -- white king moves or takes
                                                      else concat [if all ((/= temp) . fst) l then if snd temp /= 1 then [Game ((temp,'p'):(filter (/= i) l)) (not t) ca o (2) (0,0) 0.0 0.0 Nothing] else [Game ((temp,'q'):(filter (/= i) l)) (not t) ca o (1) (0,0) 0.0 0.0 Nothing, Game ((temp,'r'):(filter (/= i) l)) (not t) ca o (2) (0,0) 0.0 0.0 Nothing, Game ((temp,'b'):(filter (/= i) l)) (not t) ca o (2) (0,0) 0.0 0.0 Nothing, Game ((temp,'n'):(filter (/= i) l)) (not t) ca o (2) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((== 'p') . snd) l, let temp = ((fst . fst) i, (snd . fst) i - 1)] ++ -- black pawn moves one square or promotes
                                                           concat [if (snd . fst) i == 7 && all (\p -> fst p /= temp2 && fst p /= temp1) l then [Game ((temp2,'p'):(filter (/= i) l)) (not t) ca o (2) temp1 0.0 0.0 Nothing] else [] | i <- filter ((== 'p') . snd) l, let temp2 = ((fst . fst) i, (snd . fst) i - 2), let temp1 = ((fst . fst) i, (snd . fst) i - 1)] ++ -- black pawn moves two squares
                                                           concat [if bounds temp && any (\p -> fst p == temp && (isUpper . snd) p) l then if snd temp /= 1 then [Game ((temp,'p'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) ca o (1) (0,0) 0.0 0.0 Nothing] else let newca = (replace 0 (ca!!0 || temp == (8,1)) . replace 1 (ca!!1 || temp == (1,1)) $ ca) in [Game ((temp,'q'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) newca o (1) (0,0) 0.0 0.0 Nothing, Game ((temp,'r'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) newca o (2) (0,0) 0.0 0.0 Nothing, Game ((temp,'b'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) newca o (2) (0,0) 0.0 0.0 Nothing, Game ((temp,'n'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) newca o (2) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((== 'p') . snd) l, j <-[-1, 1], let temp = ((fst . fst) i + j, (snd . fst) i - 1)] ++ -- black pawn takes diagonally
                                                           concat [if temp==m then let target = (fst temp, snd temp + 1) in [Game ((temp,'p'):(filter (/= i) . filter ((/= target) . fst) $ l)) (not t) ca o (1) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((== 'p') . snd) l, j <-[-1, 1], let temp = ((fst . fst) i + j, (snd . fst) i - 1)] ++ -- black pawn takes en passant
                                                           concat [if bounds temp && all (\p -> all ((/= p) . fst) l) (init . tail . myrange $ (fst i, temp)) && all (\p -> fst p /= temp || (isUpper . snd) p) l then [Game ((temp,'r'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) (replace 0 (ca!!0 || temp == (8,1)) . replace 1 (ca!!1 || temp == (1,1)) . replace 2 (fst i==(8,8) || ca!!2) . replace 3 (fst i == (1,8) || ca!!3) $ ca) o (if any ((== temp) . fst) l then (1) else (2)) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((== 'r') . snd) l, j <- filter (/=(0,0)) (range((-8,0),(8,0))++range((0,-8),(0,8))), let temp = ((fst . fst) i + fst j, (snd . fst) i + snd j)] ++ -- black rook moves or takes
                                                           concat [if bounds temp && all (\p -> all ((/= p) . fst) l) (init . tail . myrange $ (fst i, temp)) && all (\p -> fst p /= temp || (isUpper . snd) p) l then [Game ((temp,'b'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) (replace 0 (ca!!0 || temp == (8,1)) . replace 1 (ca!!1 || temp == (1,1)) $ ca) o (if any ((== temp) . fst) l then (1) else (2)) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((== 'b') . snd) l, j <- filter (/=(0,0)) ([(k,k) | k <- [-8..8]]++[(k,-k) | k <- [-8..8]]), let temp = ((fst . fst) i + fst j, (snd . fst) i + snd j)] ++ -- black bishop moves or takes
                                                           concat [if bounds temp && all (\p -> fst p /= temp || (isUpper . snd) p) l then [Game ((temp,'n'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) (replace 0 (ca!!0 || temp == (8,1)) . replace 1 (ca!!1 || temp == (1,1)) $ ca) o (if any ((== temp) . fst) l then (1) else (2)) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((== 'n') . snd) l, j <- [(1,2),(2,1),(1,-2),(-2,1),(-1,2),(2,-1),(-1,-2),(-2,-1)], let temp = ((fst . fst) i + fst j, (snd . fst) i + snd j)] ++ -- black knight moves or takes
                                                           concat [if bounds temp && all (\p -> all ((/= p) . fst) l) (init . tail . myrange $ (fst i, temp)) && all (\p -> fst p /= temp || (isUpper . snd) p) l then [Game ((temp,'q'):(filter (/= i) . filter ((/= temp) . fst) $ l)) (not t) (replace 0 (ca!!0 || temp == (8,1)) . replace 1 (ca!!1 || temp == (1,1)) $ ca) o (if any ((== temp) . fst) l then (1) else (2)) (0,0) 0.0 0.0 Nothing] else [] | i <- filter ((== 'q') . snd) l, j <- filter (/=(0,0)) ([(k,k) | k <- [-8..8]]++[(k,-k) | k <- [-8..8]]++(range((-8,0),(8,0))++range((0,-8),(0,8)))), let temp = ((fst . fst) i + fst j, (snd . fst) i + snd j)] ++ -- black queen moves or takes
                                                           concat [if bounds temp && all (\p -> fst p /= temp || (isUpper . snd) p) l then [Game ((temp,'k'):(filter (/= king) . filter ((/= temp) . fst) $ l)) (not t) (replace 0 (ca!!0 || temp == (8,1)) . replace 1 (ca!!1 || temp == (1,1)) . replace 3 True . replace 2 True $ ca) o (if any ((== temp) . fst) l then (1) else (2)) (0,0) 0.0 0.0 Nothing] else [] | j <- [(-1,1),(0,1),(1,1),(1,0),(1,-1),(0,-1),(-1,-1),(-1,0)], let temp = ((fst . fst) king + fst j, (snd . fst) king + snd j)]) -- black king moves or takes
                                                      ++
                                                if not (and ca) then if t && not (ca!!0) && all (\p -> fst p /= (6,1) && fst p /= (7,1)) l then [Game (((7,1),'K'):((6,1),'R'):filter (\p -> fst p /= (5,1)) (filter ((/= (8,1)) . fst) l)) (not t) (replace 0 True . replace 1 True $ ca) (replace 0 True o) (1) (0,0) 0.0 0.0 Nothing] else [] ++ -- white kingside castles
                                                                     if t && not (ca!!1) && all (\p -> fst p /= (2,1) && fst p /= (3,1) && fst p /= (4,1)) l then [Game (((3,1),'K'):((4,1),'R'):filter (/= king) (filter ((/= (1,1)) . fst) l)) (not t) (replace 0 True . replace 1 True $ ca) (replace 1 True o) (1) (0,0) 0.0 0.0 Nothing] else [] ++ -- white queenside castles
                                                                     if (not t) && not (ca!!2) && all (\p -> fst p /= (6,8) && fst p /= (7,8)) l then [Game (((7,8),'k'):((6,8),'r'):filter (/= king) (filter ((/= (8,8)) . fst) l)) (not t) (replace 2 True . replace 3 True $ ca) (replace 2 True o) (1) (0,0) 0.0 0.0 Nothing] else [] ++ -- black kingside castles
                                                                     if (not t) && not (ca!!3) && all (\p -> fst p /= (2,1) && fst p /= (3,8) && fst p /= (4,8)) l then [Game (((3,8),'k'):((4,8),'R'):filter (/= king) (filter ((/= (1,8)) . fst) l)) (not t) (replace 2 True . replace 3 True $ ca) (replace 3 True o) (1) (0,0) 0.0 0.0 Nothing] else [] -- black queenside castles
                                                                else []
            where
                bounds (a,b)                  = a>=1&&a<=8&&b>=1&&b<=8
                myrange ((a1,b1),(a2,b2))
                    | a1==a2                  = if b1 < b2 then range ((a1,b1),(a2,b2)) else reverse $ range ((a2,b2),(a1,b1))
                    | b1==b2                  = if a1 < a2 then range ((a1,b2),(a2,b2)) else reverse $ range ((a2,b2),(a1,b1))
                    | a1 < a2                 = if b1 < b2 then filter (\j->snd j-fst j==b1-a1) $ range ((a1,b1),(a2,b2)) else reverse $ filter (\j->fst j+snd j==a1+b1) $ range ((a1,b2),(a2,b1))
                    | a2 < a1                 = if b1 < b2 then filter (\j->fst j+snd j==a1+b1) $ range ((a2,b1),(a1,b2)) else reverse $ filter (\j->snd j-fst j==b1-a1) $ range ((a2,b2),(a1,b1))
                king                          = head $ filter ((== if t then 'K' else 'k') . snd) l
        wt d h e                              = if d then (1 - weight) * h + weight * e else (e - (1 - weight) * h) / weight
            where
                weight                        = 0.95

-- |Computes the instantaneous "heuristic" eval of a game
heuristic                                     :: Game->Game
heuristic game@(Game l _ ca o _ _ _ _ _)      = game { heur = tot }
    where
        tot                                   = sum (map (val . snd) l)
                                                + sum [ if file == 4 || file == 5 then 0.5 else 0 | i <- filter ((== 'R') . snd) l, let file = fst . fst $ i]
                                                + sum [ if file == 4 || file == 5 then -0.5 else 0 | i <- filter ((== 'r') . snd) l, let file = fst . fst $ i]
                                                + sum [ if rank >= 6 || ((file == 4 || file == 5) && rank >= 4) then 0.6 else 0 | i <- filter ((=='P') . snd) l, let (file, rank) = fst i]
                                                + sum [ if rank <= 3 || ((file == 4 || file == 5) && rank <= 5) then -0.6 else 0 | i <- filter ((== 'p') . snd) l, let (file, rank) = fst i]
                                                + sum [ if rank == 1 then -0.3 else 0.0 | i <- filter (\p -> snd p=='N'||snd p=='B') l, let rank = snd . fst $ i]
                                                + sum [ if rank == 8 then 0.3 else 0.0 | i <- filter (\p -> snd p=='n'||snd p=='b') l, let rank = snd . fst $ i]
                                                + (if o!!0||o!!1 then 0.9 else ((if ca!!0 then -0.5 else 0) + (if ca!!1 then -0.5 else 0))) -- note: potentially remove these latter conditions.
                                                + (if o!!2||o!!3 then -0.9 else ((if ca!!2 then 0.5 else 0) + (if ca!!3 then 0.5 else 0))) -- they seem to slow down the execution a lot.
        val p
            | p=='R'                          = 5
            | p=='N'                          = 3.5
            | p=='B'                          = 3.75
            | p=='Q'                          = 9
            | p=='P'                          = 1
            | p=='r'                          = -5
            | p=='n'                          = -3.5
            | p=='b'                          = -3.75
            | p=='q'                          = -9
            | p=='p'                          = -1
            | otherwise                       = 0

-- |Takes a piece list and assembles an 8x8 array of chars. Used in the "display" and "mover" functions.
boarder                                       :: Locations->Array (Int,Int) Char
boarder l                                     = array ((1,1),(8,8)) ([((i,j),'_') | i <- [1..8], j <- [1..8]] ++ l)

-- |Translates a game into a display containing a board and some relevant information.
display                                       :: Game->String
display (Game l t ca o u m h e _)             = unlines [unwords [ [board!(i,j)] | i <- [1..8]] | j <- (reverse [1..8])] ++ "Turn: "++show t++", Castling: "++show ca++", Emp: "++show m++",  Heuristic: "++show h++", Eval: "++show e++", Unlikelihood: "++show u++"\n" ++ unwords (map (\p -> show (fst p) ++ show (snd p)) l)++"\n"
    where
        board                                 = boarder l

-- |Displays the principal variation of a game for which one has already been generated.
variation                                     :: Game->String
variation game@(Game _ _ _ _ _ _ _ _ ch)      = display game ++ if isNothing ch then "" else variation (fromJust ch)

-- |Takes a FEN of a desired game position and a (max) search depth, populates it using an iterative-deepening search, and then returns the source and target squares of the best move, in the format [sourcerank, sourcefile, targetrank, targetfile]
mover                                         ::String->Int->(Int,Int,Int,Int)
mover fen depth                               = case length diff of 4 -> case head diff of 0 -> (1,5,1,3) -- Q
                                                                                           7 -> (8,5,8,3) -- q
                                                                                           32 -> (1,5,1,7) -- K
                                                                                           39 -> (8,5,8,7) -- k
                                                                    3 -> if (head diff) `mod` 8 <= 3 then if (head diff) `mod` 8 == 3 then (((head diff) `mod` 8) + 1, ((head diff) `quot` 8) + 1, (head diff) `mod` 8, ((head diff) `quot` 8) + 2) -- black takes white en passant to the right
                                                                                                                                      else (((head diff) `mod` 8) + 2, ((head diff) `quot` 8) + 2, ((head diff) `mod` 8) + 1, ((head diff) `quot` 8) + 1) -- black takes white en passant to the left
                                                                                                     else if (last diff) `mod` 8 == 5 then (((head diff) `mod` 8) + 1, ((head diff) `quot` 8) + 1, ((head diff) `mod` 8) + 2, ((head diff) `quot` 8) + 2) -- white takes black en passant to the right
                                                                                                                                      else (((head diff) `mod` 8) + 1, ((head diff) `quot` 8) + 2, ((head diff) `mod` 8) + 2, ((head diff) `quot` 8) + 1) -- white takes black en passant to the left
                                                                    2 -> let (f1,f2) = ((diff!!0) `mod` 8, (diff!!0) `quot` 8); (s1,s2) = ((diff!!1) `mod` 8, (diff!!1) `quot` 8) in if snd(l2!!(head diff)) == '_' then (f1+1,f2+1,s1+1,s2+1) else (s1+1,s2+1,f1+1,f2+1)
    where
        diff                                  = filter (\p -> (l1!!p) /= (l2!!p)) [0..63]
        l1                                    = assocs . boarder . locations $ game
        l2                                    = assocs . boarder . locations . fromJust . child $ game
        game                                  = deepening depth $ loader fen

-- |Reads a FEN and generates a corresponding Game.
loader                                        :: String->Game
loader fen                                    = let fen1 = drop fen; fen2 = drop fen1; fen3 = drop fen2
                                                in heuristic . emper fen3 . castler fen2 . turner fen1 . piecer fen (1,8) $ Game [] True [True, True, True, True] [False, False, False, False] 0 (0,0) 0.0 0.0 Nothing
    where
        emper str game                        = case head str of '-' -> game
                                                                 'a' -> game { enpassant = (1,rank) }
                                                                 'b' -> game { enpassant = (2,rank) }
                                                                 'c' -> game { enpassant = (3,rank) }
                                                                 'd' -> game { enpassant = (4,rank) }
                                                                 'e' -> game { enpassant = (5,rank) }
                                                                 'f' -> game { enpassant = (6,rank) }
                                                                 'g' -> game { enpassant = (7,rank) }
                                                                 'h' -> game { enpassant = (8,rank) }
            where
                rank                          = digitToInt . head . tail $ str
        castler str game
            | head str == '-'                 = game
            | head str == ' '                 = game
            | head str == 'K'                 = castler (tail str) game { cancastle = replace 0 False $ cancastle game }
            | head str == 'Q'                 = castler (tail str) game { cancastle = replace 1 False $ cancastle game }
            | head str == 'k'                 = castler (tail str) game { cancastle = replace 2 False $ cancastle game }
            | head str == 'q'                 = castler (tail str) game { cancastle = replace 3 False $ cancastle game }
        turner str game                       = game {turn = if head str == 'w' then True else False }
        piecer str pos game
            | head str == ' '                 = game
            | head str == '/'                 = piecer (tail str) (1, snd pos - 1) game
            | isDigit . head $ str            = piecer (if head str == '1' then tail str else (intToDigit $ (digitToInt . head) str - 1):tail str) (fst pos + 1, snd pos) game
            | otherwise                       = piecer (tail str) (fst pos + 1, snd pos) game { locations = (pos, head str):locations game }
        drop str                              = if head str == ' ' then tail str else drop (tail str)

-- |An auxiliary function that returns very large and very negative floats.
specials                                      :: Bool->Double
specials t                                    = if t then fromIntegral positive else fromIntegral negative
    where
        negative, positive                    :: Int
        negative                              = minBound
        positive                              = maxBound

-- |Replaces the nth element of a list with a new element.
replace                                       :: Int->a->[a]->[a]
replace (-1) new (x:xs)                       = x:xs
replace 0 new (x:xs)                          = new:xs
replace n new (x:xs)                          = x:replace (n-1) new xs

--main                                          = do -- ENABLE THIS MAIN BLOCK, as well as the imports Haste.Foreign and Haste.Prim above (and disable the below one), if you'd like to compile with Haste and export "mover" to JavaScript.
--                                                  export (toJSStr "mover") mover

main                                          = do
                                                  strs <- getArgs
                                                  putStr . variation $ deepening (read . head . tail $ strs) (loader . head $ strs) -- Prints the principal variation of the game whose FEN is given by the first argument, and (integral) max search depth is given by the second.