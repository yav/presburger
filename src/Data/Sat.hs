-- module Data.Sat (checkSat) where

import Debug.Trace

import           Data.IntMap ( IntMap )
import qualified Data.IntMap as IntMap
import           Data.IntSet ( IntSet )
import qualified Data.IntSet as IntSet
import           Data.List ( partition )
import           Control.Monad (mplus)

import System.Environment

dbg | False = trace
    | otherwise = \_ x -> x

main :: IO ()
main = mapM_ testFile =<< getArgs

testFile file =
  do mapM_ putStrLn (replicate 30 "")
     putStr (show file ++ " ")
     txt <- readFile file
     let lss = dimacs txt
     case checkSat lss of
       Nothing -> putStrLn "unsat"
       Just m | all (any (val m)) lss -> putStrLn "sat"
              | otherwise -> putStrLn "BUG, invalid SAT"
  where
  val m x = if x > 0 then m IntMap.! x else not (m IntMap.! negate x)

dimacs :: String -> [[Lit]]
dimacs = map (map read . init) . filter (not . skip) . map words . lines
  where
  skip [] = True
  skip ("c" : _) = True
  skip ("p" : _) = True
  skip _  = False

checkSat :: [[Lit]] -> Maybe (IntMap{-Var-} Bool)
checkSat lss =
  dbg (show (IntSet.size vs, length lss)) $
  do (cs,us) <- foldr add (Just (noClauses,[])) lss
     search0 vs cs us
  where
  vs       = IntSet.fromList [ abs l | ls <- lss, l <- ls ]
  add c mb = do (cs,us) <- mb
                case clause c of
                  MalformedClause  -> error "0 is not a valid clause literal."
                  FalseClause      -> Nothing
                  TrivialClause    -> mb
                  UnitClause u     -> Just (cs, u:us)
                  NormalClause x y -> Just (addClause x y cs, us)


data Cla = MalformedClause
         | FalseClause
         | TrivialClause
         | UnitClause (Lit,Clause)
         | NormalClause (Lit,Clause) Lit
           deriving Show

clause :: [Lit] -> Cla
clause ls
  | not (null bad) = MalformedClause
  | not (IntSet.null (IntSet.intersection posL negL)) = TrivialClause
  | otherwise = case IntSet.minView good of
                  Nothing -> FalseClause
                  Just (a,xs) ->
                    case IntSet.minView xs of
                      Nothing    -> UnitClause (a,c)
                      Just (b,_) -> NormalClause (a,c) b
  where
  (bad,good')   = partition (== 0) ls
  good          = IntSet.fromList good'
  (neg,_,posL)  = IntSet.splitMember 0 good
  negL          = IntSet.map negate neg

  c             = Clause { posLits = posL, negLits = negL }


--------------------------------------------------------------------------------

-- | Represents a propisitional variable. Must be positive.
type Var = Int

-- | Represents a variable, or a negated variable.
--    * Negative numbers correspond to negated literals.
--    * 0 is not a valid literal.
type Lit = Int

-- | A set of literals.
-- Invariant: a variable may appear in at most one of 'posLits' and 'negLits'.
data Clause     = Clause { posLits :: IntSet {- Var -}
                         , negLits :: IntSet {- Var -}
                         } deriving Show

showClause :: Clause -> String
showClause c = show (IntSet.toList (posLits c) ++
                          map negate (IntSet.toList (negLits c)))

claFalse :: Clause
claFalse = Clause { posLits = IntSet.empty, negLits = IntSet.empty }

clauseVars :: Clause -> IntSet {- Var -}
clauseVars c = IntSet.union (negLits c) (posLits c)
--------------------------------------------------------------------------------

type ClauseId   = Int

data Clauses = Clauses
  { clauses :: IntMap {- Lit -}        [(ClauseId,Clause)]
  , watched :: IntMap {- ClauseId -}   (Lit,Lit)
  , nextId  :: !ClauseId
  } deriving Show

-- | An empty collection of clauses.
noClauses :: Clauses
noClauses = Clauses { clauses = IntMap.empty
                    , watched = IntMap.empty
                    , nextId  = 0
                    }

-- | Add a cluase to the colleciton.
addClause :: (Lit,Clause) -> Lit -> Clauses -> Clauses
addClause (a,c) b ws =
  Clauses { clauses = add a (add b (clauses ws))
          , watched = IntMap.insert cid (a,b) (watched ws)
          , nextId  = 1 + cid
          }
  where
  add k m = IntMap.insertWith (++) k [(cid,c)] m
  cid     = nextId ws


-- | Reorganize the clauses, knowing that a literal became false.
setLitFalse ::
  Assignment      ->
  Lit             ->    -- This literal became false.
  Clauses         ->
    ( [(Lit,Clause)]    -- Unit clauses, these did not get moved.
    , Clauses           -- Rearranged collection of clauses.
    )
setLitFalse as l ws =
  dbg ("Setting " ++ show l ++ " to false") $
  case IntMap.updateLookupWithKey (\_ _ -> Nothing) l (clauses ws) of
    (Nothing, _)  -> ([], ws)
    (Just cs, mp) -> go [] [] mp (watched ws) cs

  where
  go unitRes u cs ps [] =
    dbg ("units: " ++ show (map fst unitRes)) $
    (unitRes, ws { clauses = IntMap.insert l u cs, watched = ps })

  go unitRes u cs ps ((cid,c) : more) =
    case newLoc cid c of
      (o, Just l') -> go unitRes u (IntMap.insertWith (++) l' [(cid,c)] cs)
                                   (IntMap.insert cid (o,l') ps)
                                   more
      (o, Nothing) -> go ((o,c) : unitRes) ((cid,c): u) cs ps more

  newLoc cid c =
    let avoid     = IntSet.insert (abs l) $ IntSet.insert (abs o)
                                          $ IntMap.keysSet as
        o         = other cid
        get f     = fmap fst (IntSet.minView (f c `IntSet.difference` avoid))

    in (o, let xx = get posLits `mplus` fmap negate (get negLits)
           in dbg ("moving " ++ show c ++ " to " ++ show xx) xx
      )

  other cid = case IntMap.lookup cid (watched ws) of
                Just (a,b) -> if a == l then b else a
                Nothing    -> error ("[setLit] missing watched pair for: "
                                                                  ++ show cid)



--------------------------------------------------------------------------------

data Reason       = ImpliedBy    !Clause
                  | GuessAtLevel !Int
                    deriving Show

type Assignment   = IntMap {-Var-} (Reason, Bool)

showAssign as =
              show [ if b then x else negate x | (x,(_,b)) <- IntMap.toList as ]


data SearchResult = Done (Maybe (IntMap{-Var-} Bool))
                  | BackTrack Int (Lit,Clause) Clauses
                  | GoOn Clauses Assignment

pickVar :: IntSet{-Var-} -> IntMap{-Var-} a -> Maybe Var
pickVar vs as =
  do (a,_) <- IntSet.minView (vs `IntSet.difference` IntMap.keysSet as)
     return a


guess vs d asUndo cs as =
  trace (let (n,as') = head asUndo in show n ++ ": " ++ showAssign as')
  $
  case pickVar vs as of
    Nothing -> Just (fmap snd as)
    Just v  ->
      trace (show d ++ ": guessing " ++ show v ++ " to be true") $
      let (cs1,as1,units)  = setLitTrue v (GuessAtLevel d) cs as
      in search vs d asUndo cs1 as1 units


search0 vs cs us =
  case propagate cs IntMap.empty us of
    (cs1,as1,mbConf) ->
       case mbConf of
         Just _  -> Nothing
         Nothing -> guess vs 1 [(0,as1)] cs1 as1

search vs d asUndo cs as us =
  case propagate cs as us of
    (cs1,as1,mbConf) ->
       case mbConf of
         Nothing -> guess vs (d+1) ((d,as1) : asUndo) cs1 as1
         Just c  ->
           trace ("conflict: " ++ showClause c) $
           case analyzeConflict as1 c of
             LearnedFalse    -> Nothing
             Learned d' u mb ->
               let cs2 = case mb of
                           Nothing -> cs1
                           Just l  -> addClause u l cs1
                   (_,as') : asUndo' = dropWhile ((>d') . fst) asUndo
               in trace ("learned: " ++ showClause (snd u))
                  $ trace ("undo to " ++ show d')
                  $ search vs d' asUndo' cs2 as' [u]


--------------------------------------------------------------------------------

-- | Propagate some unit clauses.
--   Returns a new state, and an optional conflict.
propagate :: Clauses -> Assignment -> [(Lit,Clause)] ->
             (Clauses, Assignment, Maybe Clause)
propagate ws as todo =
  case todo of
    []            -> (ws, as, Nothing)
    (l, c) : more ->
      trace ("prpagate: " ++ show l) $
      case IntMap.lookup (abs l) as of

        Just (_,True)
          | l > 0     -> propagate ws as more
          | otherwise -> (ws, as, Just c)

        Just (_,False)
          | l < 0     -> propagate ws as more
          | otherwise -> (ws, as, Just c)

        Nothing ->
          case setLitTrue l (ImpliedBy c) ws as of
            (ws', as', new) -> propagate ws' as' (new ++ more)



{- | Set the literal to true, with the given justification.
      * PRE: the varialbe of the literal is not assigned.
      * This just sets the variable and updates the watchers.
      * It does not look for conflicts.
-}
setLitTrue :: Lit -> Reason -> Clauses -> Assignment ->
             ( Clauses
             , Assignment
             , [(Lit,Clause)]     -- new unit clauses
             )
setLitTrue l reason ws as = (ws', as', unit)
  where
  (unit, ws')   = setLitFalse as' (negate l) ws
  as'           = IntMap.insert x (reason, b) as

  x             = abs l
  b             = l > 0



--------------------------------------------------------------------------------

data LearnedClause =
    LearnedFalse
  | Learned Int (Lit,Clause) (Maybe Lit)

{- | Given an assignment and a conflict clause, compute how far to undo,
     and a new learned clause. -}
analyzeConflict :: Assignment -> Clause -> LearnedClause
analyzeConflict as c = go IntSet.empty (IntMap.empty, claFalse) (clauseVars c)
  where
  go done result@(undo,learn) todo =
    case IntSet.minView todo of
      Nothing -> learnedClause result
      Just (v, todo')
        | v `IntSet.member` done -> go done result todo'
        | otherwise ->
          case IntMap.lookup v as of

            Just (reason, val) ->
              case reason of

                GuessAtLevel n ->
                  let (l, learn') =
                        if val
                           then ( negate v
                                , learn { negLits = IntSet.insert
                                                          v (negLits learn) })
                           else ( v
                                , learn { posLits = IntSet.insert
                                                          v (posLits learn) })

                  in go (IntSet.insert v done)
                        (IntMap.insert n l undo, learn')
                        todo'

                ImpliedBy c' ->
                  go (IntSet.insert v done) result
                     (IntSet.union (clauseVars c') todo')

            Nothing ->
              error ("[analyzeConflict] missing binding for " ++ show v)

-- | Package up the result of conflict analysis.
learnedClause :: (IntMap {-decision level-} Lit, Clause) -> LearnedClause
learnedClause (m0, c) =
  case IntMap.maxViewWithKey m0 of
    Nothing               -> LearnedFalse
    Just ((_,l1),m1)      ->
      case IntMap.maxViewWithKey m1 of
        Nothing          -> Learned 0  (l1,c) Nothing
        Just ((k2,l2),_) -> Learned k2 (l1,c) (Just l2)

