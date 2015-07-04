-- module Data.Sat (checkSat) where
{-# LANGUAGE BangPatterns #-}

import Debug.Trace

import           Data.IntMap ( IntMap )
import qualified Data.IntMap as IntMap
import           Data.IntSet ( IntSet )
import qualified Data.IntSet as IntSet
import           Data.List ( partition, find, nub, sort )
import           Data.Array.Unboxed (UArray)
import qualified Data.Array.Unboxed as Arr
import qualified Data.Array.Base as Arr

import System.Environment

main :: IO ()
main = mapM_ testFile =<< getArgs

testFile file =
  do putStr (show file ++ " ")
     txt <- readFile file
     let lss = dimacs txt
     case checkSat lss of
       Nothing -> putStrLn "unsat"
       Just m | Just bad <- find (unsatClause m) lss
                        -> error $ unlines [ "BUG", show m, show bad ]
              | otherwise -> putStrLn "sat"
  where
  val m x = if x > 0 then m IntMap.! x else not (m IntMap.! negate x)
  unsatClause m = all (not . val m)

dimacs :: String -> [[Lit]]
dimacs = map (map read . init) . filter (not . skip) . map words . fst . break (=="%") . lines
  where
  skip [] = True
  skip ("c" : _) = True
  skip ("p" : _) = True
  skip _  = False

checkSat :: [[Lit]] -> Maybe (IntMap{-Var-} Bool)
checkSat lss =
  do (cs,us) <- foldr add (Just (noClauses,[])) lss
     search vs 0 [] cs IntMap.empty us
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
  -- | not (IntSet.null (IntSet.intersection posL negL)) = TrivialClause
  | otherwise = case els of
                  [] -> FalseClause
                  [a] -> UnitClause (a,c)
                  a : b : _ -> NormalClause (a,c) b
  where
  (bad,good') = partition (== 0) ls
  good        = IntSet.fromList good'
  els         = IntSet.toList good
  c           = Arr.listArray (0, IntSet.size good - 1) els



--------------------------------------------------------------------------------

-- | Represents a propisitional variable. Must be positive.
type Var = Int

-- | Represents a variable, or a negated variable.
--    * Negative numbers correspond to negated literals.
--    * 0 is not a valid literal.
type Lit = Int

type MaybeLit = Int   -- ^ Use 0 for 'Nothing'

-- | A set of literals.
-- Invariant: a variable may appear only once.
type Clause = UArray Int Lit

showClause :: Clause -> String
showClause c = unwords $ map show (sort (Arr.elems c) ++ [0])

clauseLits :: Clause -> [Lit]
clauseLits c = Arr.elems c

{-# INLINE clauseFromIntSet #-}
clauseFromIntSet :: IntSet{-Lit-} -> Clause
clauseFromIntSet x = Arr.listArray (0, IntSet.size x - 1) (IntSet.toList x)

{-# INLINE findInClause #-}
findInClause :: (Lit -> Bool) -> Clause -> MaybeLit
findInClause p c = go 0
  where
  go i | i < Arr.numElements c = let v = Arr.unsafeAt c i
                                 in if p v then v else go (i+1)
       | otherwise = 0


--------------------------------------------------------------------------------

type ClauseId   = Int

data Clauses = Clauses
  { clauses :: !(IntMap {- Lit -}        [(ClauseId,Clause)])
  , watched :: !(IntMap {- ClauseId -}   (Lit,Lit))
  , nextId  :: !ClauseId
  } deriving Show

-- | An empty collection of clauses.
noClauses :: Clauses
noClauses = Clauses { clauses = IntMap.empty
                    , watched = IntMap.empty
                    , nextId  = 0
                    }

-- | Add a cluase to the colleciton.
{-# INLINE addClause #-}
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
{-# INLINE setLitFalse #-}
setLitFalse ::
  Assignment      ->
  Lit             ->    -- This literal became false.
  Clauses         ->
    ( [(Lit,Clause)]    -- Unit clauses, these did not get moved.
    , Clauses           -- Rearranged collection of clauses.
    )
setLitFalse as l ws =
  case IntMap.updateLookupWithKey (\_ _ -> Nothing) l (clauses ws) of
    (Nothing, _)  -> ([], ws)
    (Just cs, mp) -> go [] [] mp (watched ws) cs

  where
  go unitRes u !cs !ps [] =
    let ws' = ws { clauses = IntMap.insert l u cs, watched = ps }
    in seq ws' (unitRes, ws')

  go unitRes u cs ps ((cid,c) : more) =
    case newLoc cid c of
      (!o,l')
        | l' == 0   -> go ((o,c) : unitRes) ((cid,c) : u) cs ps more
        | otherwise -> go unitRes u (IntMap.insertWith (++) l' [(cid,c)] cs)
                                    (IntMap.insert cid (o,l') ps)
                                    more

  newLoc cid c =
    let o       = other cid
        avoid x = x == o || x == l || litVal x as == Just False
    in (o,findInClause (not . avoid) c)

  other cid = case IntMap.lookup cid (watched ws) of
                Just (a,b) -> if a == l then b else a
                Nothing    -> error ("[setLit] missing watched pair for: "
                                                                  ++ show cid)



--------------------------------------------------------------------------------

data Reason       = ImpliedBy    !Clause
                  | GuessAtLevel !Int
                    deriving Show

type Assignment   = IntMap {-Var-} (Reason, Bool)

{-# INLINE litVal #-}
litVal :: Lit -> Assignment -> Maybe Bool
litVal l as
  | l > 0     = fmap snd         (IntMap.lookup l as)
  | otherwise = fmap (not . snd) (IntMap.lookup (negate l) as)

showAssign :: Assignment -> String
showAssign as =
              show [ if b then x else negate x | (x,(_,b)) <- IntMap.toList as ]


pickVar :: IntSet{-Var-} -> IntMap{-Var-} a -> Maybe Var
pickVar vs as =
  do (a,_) <- IntSet.minView (vs `IntSet.difference` IntMap.keysSet as)
     return a

guess :: IntSet{-Var-} -> Int -> [(Int,Assignment)] -> Clauses ->
                                      Assignment -> Maybe (IntMap{-Var-} Bool)
guess vs d asUndo cs as =
  case pickVar vs as of
    Nothing -> Just (fmap snd as)
    Just v  ->
      let d'               = d + 1
          (cs1,as1,units)  = setLitTrue v (GuessAtLevel d') cs as
      in search vs d' ((d,as) : asUndo) cs1 as1 units


search :: IntSet{-Var-} -> Int -> [(Int,Assignment)] -> Clauses ->
                Assignment -> [(Lit,Clause)] -> Maybe (IntMap{-Var-} Bool)
search vs !d asUndo !cs !as us =
  propagate cs as us $ \cs1 as1 mbConf ->
       case mbConf of
         Nothing -> guess vs d asUndo cs1 as1
         Just c  ->
           case analyzeConflict as1 c of
             LearnedFalse    -> Nothing
             Learned d' u mb ->
               let cs2 | mb == 0   = cs1
                       | otherwise = addClause u mb cs1
                   (_,as') : asUndo' = dropWhile ((> d') . fst) asUndo
               in search vs d' asUndo' cs2 as' [u]


--------------------------------------------------------------------------------

-- | Propagate some unit clauses.
--   Returns a new state, and an optional conflict.
-- propagate :: Clauses -> Assignment -> [(Lit,Clause)] ->
--              (Clauses, Assignment, Maybe Clause)
propagate ws as todo k =
  case todo of
    []            -> k ws as Nothing
    (l, c) : more ->
      case IntMap.lookup (abs l) as of

        Just (_,True)
          | l > 0     -> propagate ws as more k
          | otherwise -> k ws as (Just c)

        Just (_,False)
          | l < 0     -> propagate ws as more k
          | otherwise -> k ws as (Just c)

        Nothing ->
          case setLitTrue l (ImpliedBy c) ws as of
            (ws', as', new) -> propagate ws' as' (new ++ more) k



{-# INLINE setLitTrue #-}
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
  as'           = IntMap.insert (abs l) (reason, l > 0) as

--------------------------------------------------------------------------------

data LearnedClause =
    LearnedFalse
  | Learned Int (Lit,Clause) MaybeLit

data Undo = Undo Int MaybeLit Int MaybeLit

emptyUndo :: Undo
emptyUndo = Undo 0 0 0 0

{-# INLINE addUndo #-}
addUndo :: Int -> Lit -> Undo -> Undo
addUndo n l (Undo big bL small sL)
  | n > big   = Undo n l big bL
  | n > small = Undo big bL n l
  | otherwise = Undo big bL small sL


{- | Given an assignment and a conflict clause, compute how far to undo,
     and a new learned clause. -}
{-# INLINE analyzeConflict #-}
analyzeConflict :: Assignment -> Clause -> LearnedClause
analyzeConflict as c =
  go IntSet.empty emptyUndo IntSet.empty 0 c []
  where

  go :: IntSet -> Undo -> IntSet -> Int -> Clause -> [Clause] -> LearnedClause
  go done undo learn n c more
    | n < Arr.numElements c =
    let l' = Arr.unsafeAt c n
        v = abs l'
    in if v `IntSet.member` done
          then go done undo learn (n+1) c more
          else case IntMap.lookup v as of

                 Just (reason, _) ->
                   case reason of

                     GuessAtLevel n' ->
                       go (IntSet.insert v done)
                          (addUndo n' l' undo)
                          (IntSet.insert l' learn)
                          (n+1) c more

                     ImpliedBy c' ->
                       go (IntSet.insert v done) undo learn
                          (n+1) c (c' : more)

                 Nothing ->
                   error ("[analyzeConflict] missing binding for " ++ show v)

  go _    undo learn _ _ []       = learnedClause undo learn
  go done undo learn n _ (c : cs) = go done undo learn 0 c cs

-- | Package up the result of conflict analysis.
{-# INLINE learnedClause #-}
learnedClause :: Undo -> IntSet{-Lit-} -> LearnedClause
learnedClause (Undo big bL small sL) c
  | big == 0    = LearnedFalse
  | otherwise   = let c' = clauseFromIntSet c
                  in seq c' (Learned small (bL, c') sL)




