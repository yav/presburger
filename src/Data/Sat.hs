module Data.Sat (Lit, checkSat) where

-- import Debug.Trace

import           Data.IntMap ( IntMap )
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Strict as StrictIntMap
import           Data.IntSet ( IntSet )
import qualified Data.IntSet as IntSet
import           Data.List ( partition, sort )
import           Data.Vector.Unboxed ( Vector )
import qualified Data.Vector.Unboxed as V

checkSat :: [[Lit]] -> Maybe (IntMap{-Var-} Bool)
checkSat lss =
  do (cs,us) <- foldr add (Just (noClauses,[])) lss
     search vs 0 IntMap.empty cs IntMap.empty us
  where
  vs       = IntSet.fromList [ abs l | ls <- lss, l <- ls ]
  add c mb = do (cs,us) <- mb
                case clause c of
                  MalformedClause  -> error "0 is not a valid clause literal."
                  FalseClause      -> Nothing
                  TrivialClause    -> mb
                  UnitClause u     -> Just (cs, u:us)
                  NormalClause a b c' -> Just (addClause a b c' cs, us)


data Cla = MalformedClause
         | FalseClause
         | TrivialClause
         | UnitClause (Lit,Clause)
         | NormalClause Lit Lit Clause
           deriving Show

clause :: [Lit] -> Cla
clause ls
  | not (null bad) = MalformedClause
  -- XXX:
  -- | not (IntSet.null (IntSet.intersection posL negL)) = TrivialClause
  | otherwise = case els of
                  [] -> FalseClause
                  [a] -> UnitClause (a,c)
                  a : b : _ -> NormalClause a b c
  where
  (bad,good') = partition (== 0) ls
  good        = IntSet.fromList good'
  els         = IntSet.toList good
  c           = V.fromList els



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
type Clause = Vector Lit

_showClause :: Clause -> String
_showClause c = unwords $ map show (sort (V.toList c) ++ [0])

findInClause :: (Lit -> Bool) -> Clause -> MaybeLit
findInClause p = V.foldr check 0
  where check a x = if p a then a else x



--------------------------------------------------------------------------------

type ClauseId   = Int

data Clauses = Clauses
  { clauses :: !(StrictIntMap.IntMap {- Lit -}        [(ClauseId,Clause)])
  , watched :: !(IntMap {- ClauseId -}   (Lit,Lit))
  , nextId  :: !ClauseId
  } deriving Show

-- | An empty collection of clauses.
noClauses :: Clauses
noClauses = Clauses { clauses = StrictIntMap.empty
                    , watched = IntMap.empty
                    , nextId  = 0
                    }

-- | Add a cluase to the colleciton.
addClause :: Lit -> Lit -> Clause -> Clauses -> Clauses
addClause a b c ws =
  Clauses { clauses = add a (add b (clauses ws))
          , watched = IntMap.insert cid (a,b) (watched ws)
          , nextId  = 1 + cid
          }
  where
  add k m = StrictIntMap.insertWith (++) k [(cid,c)] m
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
  case StrictIntMap.updateLookupWithKey (\_ _ -> Nothing) l (clauses ws) of
    (Nothing, _)  -> ([], ws)
    (Just cs, mp) -> go [] [] mp (watched ws) cs

  where
  go unitRes u cs ps [] =
    let ws' = ws { clauses = StrictIntMap.insert l u cs, watched = ps }
    in ws' `seq` (unitRes, ws')

  go unitRes u cs ps ((cid,c) : more) =
    case newLoc cid c of
      (o,l')
        | l' == 0   -> go ((o,c) : unitRes) ((cid,c) : u) cs ps more
        | otherwise ->
          let cs' = StrictIntMap.insertWith (++) l' [(cid,c)] cs
              ps' = IntMap.insert cid (o,l') ps
          in cs' `seq` ps' `seq` go unitRes u cs' ps' more

  newLoc cid c =
    let o       = other cid
        avoid x = x == o || x == l || litVal x as == Just False
    in o `seq` (o, findInClause (not . avoid) c)

  other cid = case IntMap.lookup cid (watched ws) of
                Just (a,b) -> if a == l then b else a
                Nothing    -> error ("[setLit] missing watched pair for: "
                                                                  ++ show cid)



--------------------------------------------------------------------------------

data Reason       = ImpliedBy    Clause
                  | GuessAtLevel Int
                    deriving Show

type Assignment   = IntMap {-Var-} (Reason, Bool)

litVal :: Lit -> Assignment -> Maybe Bool
litVal l as
  | l > 0     = fmap snd         (IntMap.lookup l as)
  | otherwise = fmap (not . snd) (IntMap.lookup (negate l) as)

_showAssign :: Assignment -> String
_showAssign as =
  show [ if b then x else negate x | (x,(_,b)) <- IntMap.toList as ]


pickVar :: IntSet{-Var-} -> IntMap{-Var-} a -> Maybe Var
pickVar vs as =
  do (a,_) <- IntSet.minView (vs `IntSet.difference` IntMap.keysSet as)
     return a

guess :: IntSet{-Var-} -> Int -> IntMap Assignment -> Clauses ->
                                      Assignment -> Maybe (IntMap{-Var-} Bool)
guess vs d asUndo cs as =
  case pickVar vs as of
    Nothing -> Just (fmap snd as)
    Just v  ->
      let d'               = d + 1
          (cs1,as1,units)  = setLitTrue v (GuessAtLevel d') cs as
          asUndo'          = IntMap.insert d as asUndo
      in d' `seq` asUndo `seq`
         search vs d' asUndo' cs1 as1 units


search :: IntSet{-Var-} -> Int -> IntMap Assignment -> Clauses ->
                Assignment -> [(Lit,Clause)] -> Maybe (IntMap{-Var-} Bool)
search vs d asUndo cs as us =
  case propagate cs as us of
    (cs1,as1,mbConf) ->
       case mbConf of
         Nothing -> guess vs d asUndo cs1 as1
         Just c  ->
           case analyzeConflict as1 c of
             LearnedFalse  -> Nothing
             Learned d' l mb c' ->
               let cs2 | mb == 0   = cs1
                       | otherwise = addClause l mb c' cs1
               in cs2 `seq`
                  case IntMap.splitLookup d' asUndo of
                    (asUndo',Just as',_) ->
                      search vs d' asUndo' cs2 as' [(l,c')]
                    _ -> error "[search] Undo to unknown decision level."


--------------------------------------------------------------------------------

-- | Propagate some unit clauses.
--   Returns a new state, and an optional conflict.
propagate :: Clauses -> Assignment -> [(Lit,Clause)] ->
            (Clauses, Assignment, Maybe Clause)
propagate ws as todo =
  case todo of
    []            -> (ws,as,Nothing)
    (l, c) : more ->
      case IntMap.lookup (abs l) as of

        Just (_,True)
          | l > 0     -> propagate ws as more
          | otherwise -> (ws,as,Just c)

        Just (_,False)
          | l < 0     -> propagate ws as more
          | otherwise -> (ws,as,Just c)

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
  as'           = v `seq` IntMap.insert (abs l) (reason, v) as
  v             = l > 0

--------------------------------------------------------------------------------

data LearnedClause =
    LearnedFalse
  | Learned !Int !Lit !MaybeLit !Clause


{- | Given an assignment and a conflict clause, compute how far to learn,
     and a new learned clause. -}
analyzeConflict :: Assignment -> Clause -> LearnedClause
analyzeConflict as c0 = go IntSet.empty IntMap.empty [c0]
  where

  go _    learn []       = learnedClause learn
  go done learn (c : cs) =
    case V.foldl' goL (done,learn,cs) c of
      (done',learn',todo') -> go done' learn' todo'

  goL s@(done,learn,todo) l
    | v `IntSet.member` done = s
    | otherwise =
      done' `seq`
      case IntMap.lookup v as of
        Just (reason, _) ->
          case reason of

            GuessAtLevel d ->
              let learn' = IntMap.insert d l learn
              in learn' `seq` (done', learn', todo)

            ImpliedBy c' -> (done', learn, c' : todo)

        Nothing -> error ("[analyzeConflict] missing binding for " ++ show v)
    where
    v     = abs l
    done' = IntSet.insert v done


-- | Package up the result of conflict analysis.
learnedClause :: IntMap{-Decision-} Lit -> LearnedClause
learnedClause learn =
  case IntMap.toDescList learn of
    [] -> LearnedFalse
    ls ->
      let c = V.fromList (map snd ls)
      in case ls of
           [ (_,l) ]           -> Learned 0 l  0  c
           (_,l1) : (d,l2) : _ -> Learned d l1 l2 c





