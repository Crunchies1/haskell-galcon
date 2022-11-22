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
    (p, ps') = detach ps
    v = source p
