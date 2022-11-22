\documentclass[a4]{tufte-handout}
% The documentclass can be changed, but keep fonts at a reasonable size.

% comments
\usepackage{comment}

% code environments
\usepackage{listings}
\lstnewenvironment{code}{
  \lstset{language=haskell, basicstyle=\ttfamily }}{}
\lstnewenvironment{spec}{
  \lstset{language=haskell, basicstyle=\ttfamily }}{}
\lstset{language=haskell, basicstyle=\ttfamily }


\title{CO202: Coursework 1}
\date{Autumn Term, 2019}
\author{Aporva Varshney and Adam Lau}

\begin{document}
\maketitle
\begin{comment}
\begin{code}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
\end{code}
\end{comment}

\begin{comment}
\begin{code}
module Submission where

import Prelude hiding (maximum)
import Data.Maybe (fromJust, isNothing, isJust)
import Data.Coerce (coerce)
import Data.Function (on)

import Data.Array
import Data.List (nub, sortBy, maximumBy, minimumBy, tails, inits, mapAccumL, (\\), find)
import Data.Map (Map, keys)
import qualified Data.Map as M

\end{code}
\end{comment}

\begin{spec}
ghc -fforce-recomp -c Submission.lhs-boot Submission.lhs
\end{spec}

\begin{comment}
\begin{code}
data Player = Player1 | Player2
data Planet = Planet Owner Ships Growth
newtype Ships = Ships Int
newtype Growth = Growth Int
data Owner = Neutral | Owned Player
newtype PlanetId = PlanetId Int
type Planets = Map PlanetId Planet
data Wormhole = Wormhole Source Target Turns

newtype Source = Source PlanetId
newtype Target = Target PlanetId
newtype Turns  = Turns Int
newtype WormholeId = WormholeId Int
type Wormholes = Map WormholeId Wormhole
data Fleet = Fleet Player Ships WormholeId Turns
type Fleets = [Fleet]
data GameState = GameState Planets Wormholes Fleets
data Order = Order WormholeId Ships
\end{code}
\end{comment}

\begin{comment}
\begin{code}
fib :: Int -> Integer
fib 0 = 0
fib 1 = 1
fib n = fib (n-2) + fib (n-1)

fib' :: Int -> Integer
fib' n = table ! n
  where
    table :: Array Int Integer
    table = tabulate (0, n) mfib

    mfib 0 = 0
    mfib 1 = 1
    mfib n = table ! (n-1) + table ! (n-2)
    
shortestPathsTo :: forall g e v. Graph g e v => g -> v -> [Path e]
shortestPathsTo g v = dijkstraTo g (vertices g \\ [v]) ps
 where
  ps :: PList (Path e)
  ps = foldr insert (empty cmpPath) (map pathFromEdge (edgesTo g v))

extend2 :: Edge e v => Path e -> e -> Path e
extend2 (Path _ []) _ = error "extend2: Empty path"
extend2 (Path d (e:es)) e'
  | source e == target e' = Path (d + weight e') (e':e:es)
  | otherwise = error "extend2: Incompatible endpoints"

dijkstraTo :: (Graph g e v, PQueue pqueue) =>
  g -> [v] -> pqueue (Path e) -> [Path e]
dijkstraTo g [] ps = []
dijkstraTo g us ps
  | isEmpty ps  = []
  | v `elem` us = p : dijkstraTo g (us \\ [v]) 
                                 (foldr insert ps' (map (extend2 p) (edgesTo g v)))
  | otherwise  = dijkstraTo g us ps'
  where 
    (p@(Path d xs), ps') = detach ps
    v = source (head xs)

tabulate :: Ix i => (i,i) -> (i -> a) -> Array i a
tabulate (u,v) f = array (u,v) [ (i, f i) | i <- range (u, v)]
\end{code}
\end{comment}

\begin{comment}
\begin{code}  
example1 :: GameState
example1 = GameState planets wormholes fleets where
  planets = M.fromList
    [ (PlanetId 0, Planet (Owned Player1) (Ships 300) (Growth 0))
    , (PlanetId 1, Planet Neutral         (Ships 200) (Growth 50))
    , (PlanetId 2, Planet Neutral         (Ships 150) (Growth 10))
    , (PlanetId 3, Planet Neutral         (Ships 30)  (Growth 5))
    , (PlanetId 4, Planet Neutral         (Ships 100) (Growth 20))
    ]
  wormholes = M.fromList
    [ (WormholeId 0, Wormhole homePlanet (Target 1) (Turns 1))
    , (WormholeId 1, Wormhole homePlanet (Target 2) (Turns 1))
    , (WormholeId 2, Wormhole homePlanet (Target 3) (Turns 1))
    , (WormholeId 3, Wormhole homePlanet (Target 4) (Turns 1))
    ] where homePlanet = Source 0
  fleets = []

targetPlanets :: GameState -> Source -> [(PlanetId, Ships, Growth)]
targetPlanets st s
  = map (planetDetails . target) (M.elems (wormholesFrom s st))
  where
    planetDetails :: PlanetId -> (PlanetId, Ships, Growth)
    planetDetails pId = (pId, ships, growth)
      where Planet _ ships growth = lookupPlanet pId st

shipsOnPlanet :: GameState -> PlanetId -> Ships
shipsOnPlanet st pId = ships
  where Planet _ ships _ = lookupPlanet pId st

lookupPlanet :: PlanetId -> GameState -> Planet
lookupPlanet pId (GameState ps _ _) = fromJust (M.lookup pId ps)

wormholesFrom :: Source -> GameState -> Wormholes
wormholesFrom pId (GameState _ ws _)
  = M.filter (\(Wormhole s _ _) -> s == pId) ws

wormholesTo :: Target -> GameState -> Wormholes
wormholesTo pId (GameState _ ws _)
  = M.filter (\(Wormhole _ t _) -> t == pId) ws

knapsack :: (Ord weight, Num weight, Ord value, Num value) => 
  [(name, weight, value)] -> weight -> value
knapsack wvs c = maximum 0 [ v + knapsack wvs (c - w) | (_,w,v) <- wvs , w <= c ]

maximum :: Ord a => a -> [a] -> a
maximum x xs = foldr max x xs
\end{code}
\end{comment}

\section*{Problem 1: Dynamic Knapsack}
\subsection*{How the code works}

Values for the recursive subcalls are stored in the table for fast lookup later on.
We effectively use the knapsack function defined above in order to create the table,
but with any recursive calls replaced with lookups within the table.

\begin{code}
knapsack' :: forall name weight value .
  (Ix weight, Num weight, Ord value, Num value) => 
  [(name, weight, value)] -> weight -> value
knapsack' wvs c = table ! c
  where
    table :: Array weight value
    table = tabulate (0,c) mknapsack

    mknapsack :: weight -> value
    mknapsack c = maximum 0 [ v + table ! (c - w) | (_, w, v) <- wvs, w <= c ]
\end{code}

\section*{Problem 2: Knapsack Elements}

In order to also produce a list of elements chosen in order to get the maximum
value, we store in the table for any given weight a tuple of the maximum value 
and also the names already chosen. We compute the possible options at the
weight given, prepending the name of the current element to the existing list
of names, and take the maximum by comparing the first element (i.e. the value).
The base case is a value of 0 and an empty list.

\begin{code}
knapsack'' :: forall name weight value .
  (Ix weight, Num weight, Ord value, Num value) =>
  [(name, weight, value)] -> weight -> (value, [name])
knapsack'' wvs c = table ! c
  where
    table :: Array weight (value, [name])
    table = tabulate (0,c) mknapsack

    mknapsack :: weight -> (value, [name])
    mknapsack c = maximumBy (compare `on` fst) ((0, []):xs)
      where
        xs = [(v + (fst (table ! (c - w))), n:(snd (table ! (c - w)))) 
              | (n, w, v) <- wvs, w <= c]
\end{code}

\section*{Problem 3: Bounded Knapsack}

To create a bounded knapsack algorithm, we take each element of the list of 
tuples given, and check whether the weight of the element is greater than
the capacity. If it is then we carry on searching through the list. If it isn't,
then we compute the values the algorithm gives with the rest of the elements
at the same capacity - hence assuming that the current element does not contribute
to the optimal solution - and with the rest of the elements at a reduced capacity
- hence assuming that the element does contribute to the optimal solution. We 
choose the approach which then gives the greater weight. Since the optimal 
solution can be reordered to start from any element, we can simply remove the 
current element from later recursive calls when assuming that it is not part
of the solution.

\begin{code}
bknapsack
  :: (Ord weight, Num weight, Ord value, Num value)
  => [(name, weight, value)] -> weight -> (value, [name])

bknapsack [] c = (0, [])
bknapsack ((n, w, v):wvs) c
  | w > c       = (v', ns')
  | otherwise   
    = if (v + v'') > v' then (v + v'', ns'' ++ [n]) 
      else (v', ns')
  where
    (v', ns') = bknapsack wvs c
    (v'', ns'') = bknapsack wvs (c - w)
\end{code}

\section*{Problem 4: Reasonable Indexes}

\section*{Problem 5: Bounded Knapsack Revisited}

\begin{code}
bknapsack' :: forall name weight value . 
  (Ord weight, Num weight, Ord value, Num value) =>
  [(name, weight, value)] -> Int -> 
  weight -> (value, [name])
bknapsack' wvs track c 
  | track == (length wvs) = (0, [])
  | w > c                 = (v', ns') 
  | otherwise             = if (v + v'') > v' then (v + v'', ns'' ++ [n]) else (v', ns')
  where
    (n, w, v)   = wvs !! track
    (v', ns')   = bknapsack' wvs (track + 1) c
    (v'', ns'') = bknapsack' wvs (track + 1) (c-w)
\end{code}

\section*{Problem 6: Dynamic Bounded Knapsack}

\begin{code}
bknapsack'' :: forall name weight value .
  (Ord name, Ix weight, Ord weight, Num weight, 
    Ord value, Num value) =>
  [(name, weight, value)] -> weight -> (value, [name])
bknapsack'' wvs c = (max, reverse ns)
  where
    (max, ns) = table ! (c, 0)
    m = length wvs

    table :: Array (weight, Int) (value, [name])
    table = tabulate ((0, 0), (c, m)) mbknapsack

    mbknapsack :: (weight, Int) -> (value, [name])
    mbknapsack (c, track)
      | track == m = (0, [])
      | w > c      = (v', ns')
      | otherwise
        = if (v + v'') > v' then (v + v'', n:ns'') else (v', ns')
        where
          (n, w, v)  = wvs !! track
          (v', ns')  = table ! (c, track + 1)
          (v'', ns'') = table ! (c - w, track + 1)
\end{code}

\section*{Problem 7: Dijkstra Dualized}

In order to modify Dijkstra's algorithm so that it returns paths to the vertex,
we change it so that v = source p, and then extend p with edges to the vertex
instead of edges from the vertex. We also must modify extend so that it prepends
the path with the new edge instead of appending to it. TODO: Add code here?

\begin{comment}
\begin{code}
optimise :: GameState -> Source -> (Growth, [PlanetId])
optimise st s@(Source p) = bknapsack'' (targetPlanets st s) (shipsOnPlanet st p)

type Weight = Integer

class Eq v => Edge e v | e -> v where
  source :: e -> v
  target :: e -> v
  weight :: e -> Weight

instance Edge (String, String, Integer) String where
  source (s, _, _) = s
  target (_, t, _) = t
  weight (_, _, i) = i

instance Edge Wormhole PlanetId where
  source (Wormhole (Source s) _ _)    = s
  target (Wormhole _ (Target t) _)    = t
  weight (Wormhole _ _ (Turns turns)) = toInteger turns

instance Edge (WormholeId, Wormhole) PlanetId where
  source (_, w) = source w
  target (_, w) = target w
  weight (_, w) = weight w

data Path e = Path Weight [e]
\end{code}

\begin{code}
pathFromEdge :: Edge e v => e -> Path e
pathFromEdge e = Path (weight e) [e]
\end{code}

\begin{code}
extend :: Edge e v => Path e -> e -> Path e
extend (Path _ []) _ = error "extend: Empty path"
extend (Path d (e:es)) e'
  | target e == source e' = Path (d + weight e') (e':e:es)
  | otherwise = error "extend: Incompatible endpoints"
\end{code}

\begin{code}
pathFromEdges :: Edge e v => [e] -> Path e
pathFromEdges (x : xs) = foldl extend (pathFromEdge x) xs
pathFromEdges [] = error "pathFromEdges: Empty list of edges"
\end{code}

\begin{code}
instance Edge e v => Edge (Path e) v where
  source (Path _ es) = source (last es)
  target (Path _ es) = target (head es)
  weight (Path w _)  = w
\end{code}

\begin{code}
class Edge e v => Graph g e v | g -> e where
  vertices  :: g -> [v]
  edges     :: g -> [e]
  edgesFrom :: g -> v -> [e]
  edgesTo   :: g -> v -> [e]
  velem     :: v -> g -> Bool
  eelem     :: e -> g -> Bool
\end{code}

\begin{code}
instance (Eq e, Edge e v) => Graph [e] e v where
  vertices es = nub (map source es ++ map target es)
  edges es    = es
  edgesFrom es v = [ e | e <- es, v == source e ]
  edgesTo   es v = [ e | e <- es, v == target e ]
  velem v es = v `elem` vertices es
  eelem v es = v `elem` edges es
\end{code}

\begin{code}
example2 :: [(String, String, Integer)]
example2 = [("s","t",10), ("s","y",5), ("t","x",1), ("t","y",2), ("y","t",3),
            ("y","x", 9), ("x","z",4), ("z","x",6), ("y","z",2), ("z","s",7)]
\end{code}

\begin{code}
instance Graph GameState (WormholeId, Wormhole) PlanetId where
  vertices (GameState ps _ _) = M.keys ps
  edges    (GameState _ ws _) = M.assocs ws
  edgesTo   st pId = M.toList (wormholesTo (Target pId) st)
  edgesFrom st pId = M.toList (wormholesFrom (Source pId) st)
  velem pId      (GameState ps _ _) = M.member pId ps
  eelem (wId, _) (GameState _ ws _) = M.member wId ws
\end{code}
\end{comment}

\begin{comment}
\begin{code}
lte :: (a -> a -> Ordering) -> (a -> a -> Bool)
lte cmp x y = cmp x y /= GT

eq :: (a -> a -> Ordering) -> (a -> a -> Bool)
eq cmp x y = cmp x y == EQ
\end{code}

\begin{code}
class PQueue pqueue where
  toPQueue   :: (a -> a -> Ordering) -> [a] -> pqueue a
  fromPQueue :: pqueue a -> [a]

  priority :: pqueue a -> (a -> a -> Ordering)

  empty :: (a -> a -> Ordering) -> pqueue a
  isEmpty :: pqueue a -> Bool

  insert :: a -> pqueue a -> pqueue a
  delete :: a -> pqueue a -> pqueue a

  extract :: pqueue a -> a
  discard :: pqueue a -> pqueue a
  detach  :: pqueue a -> (a, pqueue a)

data PList a = PList (a -> a -> Ordering) [a]

instance PQueue PList where

  toPQueue cmp xs = PList cmp (sortBy cmp xs)

  fromPQueue (PList _ xs) = xs

  empty cmp = PList cmp []

  isEmpty (PList _ xs) = null xs

  priority (PList cmp _) = cmp

  insert x (PList cmp []) = PList cmp [x]
  insert x ps@(PList cmp xs)
    | x <= y    = cons x ps
    | otherwise = cons y (insert x ys)
    where (<=) = lte cmp
          (y, ys) = detach ps
          cons x (PList cmp xs) = PList cmp (x:xs)

  delete x (PList cmp []) = PList cmp []
  delete x ps@(PList cmp _)
    | x == y    = ys
    | otherwise = cons y (delete x ys)
    where (==) = eq cmp
          (y, ys) = detach ps
          cons x (PList cmp xs) = PList cmp (x:xs)

  extract (PList cmp (x:xs)) = x

  discard (PList cmp (x:xs)) = PList cmp xs

  detach  (PList cmp (x:xs)) = (x, PList cmp xs)

cmpPath :: Path v -> Path v -> Ordering
cmpPath (Path d _) (Path d' _) = compare d d'
\end{code}
\end{comment}

\begin{comment}
\begin{code}
shortestPaths :: forall g e v. Graph g e v => g -> v -> [Path e]
shortestPaths g v = dijkstra g (vertices g \\ [v]) ps
 where
  ps :: PList (Path e)
  ps = foldr insert (empty cmpPath) (map pathFromEdge (edgesFrom g v))
\end{code}

\begin{code}
example3 :: GameState
example3 = GameState planets wormholes fleets where
  planets = M.fromList
    [ (PlanetId 0, Planet (Owned Player1) (Ships 300) (Growth 0))
    , (PlanetId 1, Planet Neutral         (Ships 200) (Growth 50))
    , (PlanetId 2, Planet Neutral         (Ships 150) (Growth 10))
    , (PlanetId 3, Planet Neutral         (Ships 30)  (Growth 5))
    , (PlanetId 4, Planet Neutral         (Ships 100) (Growth 20))
    , (PlanetId 5, Planet Neutral         (Ships 100) (Growth 20))
    ]
  wormholes = M.fromList
    [ (WormholeId 0, Wormhole homePlanet (Target 1) (Turns 1))
    , (WormholeId 1, Wormhole homePlanet (Target 2) (Turns 2))
    , (WormholeId 2, Wormhole homePlanet (Target 3) (Turns 3))
    , (WormholeId 3, Wormhole homePlanet (Target 4) (Turns 4))
    , (WormholeId 4, Wormhole (Source 4) (Target 5) (Turns 1))
    , (WormholeId 5, Wormhole (Source 2) (Target 5) (Turns 1))
    ] where homePlanet = Source 0
  fleets = []
\end{code}

\begin{code}
dijkstra :: (Graph g e v, PQueue pqueue) =>
  g -> [v] -> pqueue (Path e) -> [Path e]
dijkstra g [] ps = []
dijkstra g us ps
  | isEmpty ps  = []
  | v `elem` us = p : dijkstra g (us \\ [v]) 
                                 (foldr insert ps' (map (extend p) (edgesFrom g v)))
  | otherwise  = dijkstra g us ps'
  where 
    (p, ps') = detach ps
    v = target p
\end{code}
\end{comment}

\section*{Problem 8: Heap Operations}

The heap invariants for our implementation are that the root of any tree
is the minimum of the elements in the left and right subtrees, and that
the height of the left and right subtrees differs by at most 1.

To create a heap, we begin by defining some helpful functions. The height function
returns the height of a tree in constant time, whereas the hnode smart constructor
creates a new node, maintaining the height of the resulting node to be 1 greater
than the maximum height of its left and right subtrees.

The fixHeap function fixes a heap so that the root of the tree is the 
minimum of all elements in the  left and right subtrees. Given a comparator,
this function assumes that the left and right subtrees are valid heaps, and
finds their minimum before pushing the current root down if it is larger than
the minimum element. It then recursively calls itself on the modified subtree,
in case the element which has been pushed down is not the minimum of that subtree.
We can push an element down at most the height of the tree. Since the heap is
a balanced tree, the height is logarithmic in the number of nodes.
This function therefore runs in $O (log(n))$ time. 

The removeDeepest function finds the deepest left most element in the tree
and removes it from the tree, returning a tuple of the modified tree and the
removed element. At each stage, we descend down the tree into one of the 
subtrees, so similarly to fixHeap, the function runs in $O (log(n))$ time.

Finally we can begin to implement the functions for the priority queue.
Inserting into the heap involves finding the subtree with the least height
(choosing the left subtree if they are of equal height), requiring log n steps
as the tree is assumed balanced before the insertion. We fix the heap as we
recurse, so that the inserted element bubbles up to the right place in the tree.
However, since the heap is sorted before the insertion, the new element can
only move up to at most the root, which would require log n comparisons. Although
fixHeap is itself $O(log(n))$, in this case once we swap the elements no further
recursion occurs down the tree, as the replaced element is already the minimum
of the subtrees - hence when inserting, fixHeap executes in constant time. 
Hence, insertion occurs in $O (log(n))$ time.

Creating a priority queue from a list calls insert on every element in the list,
so that it takes $O (n log(n))$ time.

Extract simply returns the root of the tree, and is therefore a constant time function.
Discard deletes the root of the tree, taking $log(n)$ steps to find the deepest
element, and a further $log(n)$ steps to fix the heap afterwards. Hence it has
a complexity of $O(log(n))$. 

\begin{code}
data Heap a = Heap (a -> a -> Ordering) (Tree a)
data Tree a = Nil | Node Int (Tree a) a (Tree a)

height :: Tree a -> Int
height Nil = 0
height (Node h _ _ _) = h

hnode :: Tree a -> a -> Tree a -> Tree a 
hnode l x r = Node h l x r
  where
    h = 1 + max (height l) (height r)

showTree :: (Show a) => Tree a -> String
showTree (Nil) = ""
showTree (Node _ Nil x Nil) = show x
showTree (Node _ l x r) = show x ++ "(" ++ showTree l ++ ")(" ++ showTree r ++ ")"

showHeap :: (Show a) => Heap a -> String
showHeap (Heap _ t) = showTree t

-- Fixes the heap so minimum element at the top
-- Assumes that the subtrees have minimum element at the top
fixHeap :: (a -> a -> Ordering) -> Tree a -> Tree a
fixHeap cmp Nil = Nil
fixHeap cmp t@(Node h Nil x Nil) = t
fixHeap cmp t@(Node h (Node lh ll lx lr) x Nil) 
  | cmp lx x == LT = hnode l' lx Nil
  | otherwise      = t
  where
    l' = fixHeap cmp (hnode ll x lr)
fixHeap cmp t@(Node h Nil x (Node rh rl rx rr)) 
  | cmp rx x == LT = hnode Nil rx r'
  | otherwise      = t
  where
    r' = fixHeap cmp (Node rh rl x rr)
fixHeap cmp t@(Node h l@(Node lh ll lx lr) x r@(Node rh rl rx rr)) 
  | cmp lx rx == LT = if cmp lx x == LT then hnode l' lx r else t
  | cmp rx lx == LT = if cmp rx x == LT then hnode l rx r' else t
  | otherwise       = t
  where
    l' = fixHeap cmp (hnode ll x lr)
    r' = fixHeap cmp (hnode rl x rr)

removeDeepest :: Tree a -> (Tree a, a)
removeDeepest Nil = error "Can't remove deepest element: tree has no elements"
removeDeepest (Node _ Nil x Nil) = (Nil, x)
removeDeepest (Node _ l x Nil) = (hnode l' x Nil, x')
  where
    (l', x') = removeDeepest l
removeDeepest (Node _ Nil x r) = (hnode Nil x r', x')
  where
    (r', x') = removeDeepest r
removeDeepest (Node _ l x r)
  | height l >= height r = (hnode l' x r, x')
  | otherwise            = (hnode l x r', x'')
  where
    (l', x') = removeDeepest l
    (r', x'') = removeDeepest r


instance PQueue Heap where
  toPQueue cmp [] = empty cmp
  toPQueue cmp (x:xs)
    = insert x (toPQueue cmp xs)

  fromPQueue (Heap _ Nil) = []
  fromPQueue ps
    = e:(fromPQueue es)
    where
      (e, es) = detach ps

  priority :: Heap a -> (a -> a -> Ordering)
  priority (Heap cmp _) = cmp

  empty :: (a -> a -> Ordering) -> Heap a
  empty cmp = Heap cmp Nil

  isEmpty :: Heap a -> Bool
  isEmpty (Heap _ Nil) = True
  isEmpty _ = False
  
  insert :: a -> Heap a -> Heap a
  insert x (Heap cmp t)
    = Heap cmp (insert' t)
    where
      insert' Nil = hnode Nil x Nil
      insert' (Node h l y r)
        | height l <= height r = fixHeap cmp (hnode (insert' l) y r)
        | otherwise            = fixHeap cmp (hnode l y (insert' r))

  delete :: a -> Heap a -> Heap a
  delete x (Heap cmp t)
    | elemDepth == -1 = Heap cmp t
    | elemDepth /= h  = Heap cmp (fst $ deleteAndReplace t')
    | elemDepth == h  = Heap cmp (fst $ deleteDeepestLeaf t)
    where
      h = height t
      (t', d) = removeDeepest t
      elemDepth = depthToRemove t 1

      depthToRemove Nil _ = -1
      depthToRemove (Node _ l y r) depth
        | cmp x y == EQ = depth
        | depthL == -1  = depthR
        | otherwise     = depthL
        where
          depthL = depthToRemove l (depth + 1)
          depthR = depthToRemove r (depth + 1)

      deleteAndReplace Nil = (Nil, False)
      deleteAndReplace t@(Node h l y r)
        | cmp x y == EQ = (fixHeap cmp (hnode l d r), True)
        | bl == True    = (fixHeap cmp (hnode l' y r), bl) 
        | br == True    = (fixHeap cmp (hnode l y r'), br)
        | otherwise     = (t, False)
        where
          (l', bl) = deleteAndReplace l 
          (r', br)  = deleteAndReplace r

      deleteDeepestLeaf t@(Node h Nil y Nil)
        | cmp x y == EQ = (Nil, True)
        | otherwise     = (t, False)
      deleteDeepestLeaf t@(Node h l y r)
          | bl == True = (hnode l' y r, True) 
          | br == True = (hnode l y r', True) 
          | otherwise  = (t, False)
        where
          (l', bl) = deleteDeepestLeaf l
          (r', br) = deleteDeepestLeaf r

  extract :: Heap a -> a
  extract (Heap cmp Nil) = error "Cannot extract from empty heap"
  extract (Heap cmp (Node _ _ x _)) = x 
  
  discard :: Heap a -> Heap a
  discard (Heap cmp Nil) = error "Cannot extract from empty heap"
  discard (Heap cmp (Node _ Nil x Nil)) = Heap cmp Nil
  discard (Heap cmp t)
    = Heap cmp (fixHeap cmp (hnode l d r))
    where
      (Node _ l x r, d) = removeDeepest t

  detach :: Heap a -> (a, Heap a)
  detach h = (extract h, discard h)
\end{code}

\begin{comment}
\begin{code}
shortestPaths' :: forall g e v . Graph g e v => g -> v -> [Path e]
shortestPaths' g v = dijkstra g (vertices g \\ [v]) ps
 where
  ps :: Heap (Path e)
  ps = foldr insert (empty cmpPath) (map pathFromEdge (edgesFrom g v))
\end{code}
\end{comment}

\section*{Problem 9: Adjacency List Graphs}

\begin{code}
newtype AdjList e v = AdjList [(v, [e])]

instance (Eq e, Edge e v) => Graph (AdjList e v) e v where
  vertices (AdjList ves)    = map fst ves
  edges (AdjList ves)       = concat [snd ve | ve <- ves]
  edgesFrom (AdjList ves) s 
    = case es of
        Just e  -> e
        Nothing -> []
    where
      es = lookup s ves
  edgesTo   (AdjList ves) t = filter ((== t) . target) (edges (AdjList ves))
  velem v                   = elem v . vertices
  eelem e                   = elem e . edges
\end{code}

\section*{Problem 10: Conflict Zones}

\begin{code}
conflictZones :: GameState -> PlanetId -> PlanetId
  -> ([PlanetId], [PlanetId], [PlanetId])
conflictZones g@(GameState planets _ _) p q = conflictZones' (vertices g)
  where
    xs = shortestPaths' g p 
    ys = shortestPaths' g q 
    
    conflictZones' :: [PlanetId] -> ([PlanetId], [PlanetId], [PlanetId])
    conflictZones' [] = ([], [], [])
    conflictZones' (pid:pids)
      | p == pid                               = (p:ps', pqs', qs')
      | q == pid                               = (ps', pqs', q:qs')
      | isNothing pathInP && isNothing pathInQ = (ps', pqs', qs')
      | isNothing pathInP && isJust pathInQ    = (ps', pqs', pid:qs')
      | isJust pathInP && isNothing pathInQ    = (pid:ps', pqs', qs')
      | weightP < weightQ                      = (pid:ps', pqs', qs')
      | weightP > weightQ                      = (ps', pqs', pid:qs')
      | otherwise                              = (ps', pid:pqs', qs')
      where
        (ps', pqs', qs') = conflictZones' pids
        pathInP = find (\(Path w es) -> target (head es) == pid) xs
        pathInQ = find (\(Path w es) -> target (head es) == pid) ys
        (Path weightP _) = fromJust pathInP
        (Path weightQ _) = fromJust pathInQ
        
\end{code}

\begin{comment}
\begin{code}
deriving instance Show Player
deriving instance Read Player
deriving instance Show Owner
deriving instance Read Owner
deriving instance Show Planet
deriving instance Read Planet
deriving instance Show Fleet
deriving instance Read Fleet

deriving instance Show Wormhole
deriving instance Read Wormhole

deriving instance Show Order
deriving instance Read Order
deriving instance Show GameState
deriving instance Read GameState

deriving instance Ord PlanetId
deriving instance Eq PlanetId
deriving instance Num PlanetId
instance Show PlanetId where
  show (PlanetId x) = show x
instance Read PlanetId where
  readsPrec = coerce (readsPrec @Int)

deriving instance Ord Turns
deriving instance Eq Turns
deriving instance Num Turns
instance Show Turns where
  show (Turns x) = show x
instance Read Turns where
  readsPrec = coerce (readsPrec @Int)

deriving instance Ord Source
deriving instance Eq Source
instance Show Source where
  show (Source x) = show x
instance Read Source where
  readsPrec = coerce (readsPrec @Int)

deriving instance Num Growth
deriving instance Ord Growth
deriving instance Eq Growth
instance Show Growth where
  show (Growth x) = show x
instance Read Growth where
  readsPrec = coerce (readsPrec @Int)

deriving instance Ix Ships
deriving instance Num Ships
deriving instance Ord Ships
deriving instance Eq Ships
instance Show Ships where
  show (Ships x) = show x
instance Read Ships where
  readsPrec = coerce (readsPrec @Int)

deriving instance Ord Target
deriving instance Eq Target
instance Show Target where
  show (Target x) = show x
instance Read Target where
  readsPrec = coerce (readsPrec @Int)

deriving instance Eq WormholeId
deriving instance Ord WormholeId
instance Show WormholeId where
  show (WormholeId x) = show x
instance Read WormholeId where
  readsPrec = coerce (readsPrec @Int)

deriving instance Eq e   => Eq (Path e)
deriving instance Show e => Show (Path e)
instance Show a => Show (PList a) where
  show (PList _ xs) = show xs

\end{code}
\end{comment}

\end{document}
