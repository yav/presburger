module Data.Sat where


import           Data.IntMap ( IntMap )
import qualified Data.IntMap as IntMap
import           Data.IntSet ( IntSet )
import qualified Data.IntSet as IntSet
import           Data.List ( partition )
import           Control.Monad ( mplus )




-- | Represents a propisitional variable.
-- Must be positive.
type Var = Int

-- | Represents a variable, or a negated variable.
--    * Negative numbers correspond to negated literals.
--    * 0 is not a valid literal.
type Lit = Int


-- | Get the variables mentioned in the keys of the map.
-- WARNING: This implementation assumes a specific implementation for
-- the literals, namely negative integers are negated literals.
varsInKeys :: IntMap {-Lit-} a -> IntSet {-Var-}
varsInKeys m =
  let ks          = IntMap.keysSet m
      (neg,_,pos) = IntSet.splitMember 0 ks
  in IntSet.union (IntSet.map negate neg) pos



-- | A set of literals.
-- Invariant: a variable may appear in at most one of 'posLit' and 'negLits'.
data Clause     = Clause { posLits :: IntSet {- Var -}
                         , negLits :: IntSet {- Var -}
                         }

claFalse :: Clause
claFalse = Clause { posLits = IntSet.empty, negLits = IntSet.empty }


clause :: [Lit] -> Clause
clause ls = Clause { posLits = IntSet.fromList pos
                   , negLits = IntSet.fromList (map negate neg)
                   }
  where
  (pos,neg) = partition (> 0) ls


clauseVars :: Clause -> IntSet {- Var -}
clauseVars c = IntSet.union (negLits c) (posLits c)

clauseLits :: Clause -> IntSet {- Lit -}
clauseLits c = IntSet.union (IntSet.map negate (negLits c)) (posLits c)

--------------------------------------------------------------------------------

data Watchers = Watchers
  { watchedCaluses :: IntMap {- Lit -}        [(ClauseId,Clause)]
  , watchedPair    :: IntMap {- ClauseId -}   (Lit,Lit)
  , watchNextId    :: !ClauseId
  }

emptyWatchers :: Watchers
emptyWatchers = Watchers { watchedCaluses = IntMap.empty
                         , watchedPair    = IntMap.empty
                         , watchNextId    = 0
                         }

addClause :: (Lit,Clause) -> Lit -> Watchers -> Watchers
addClause (a,c) b ws =
  Watchers { watchedCaluses = add a (add b (watchedCaluses ws))
           , watchedPair    = IntMap.insert cid (a,b) (watchedPair ws)
           , watchNextId    = 1 + cid
           }
  where
  add k m = IntMap.insertWith (++) k [new] m
  cid     = watchNextId ws
  new     = (cid, c)


setLitFalse ::
  IntSet{-Var-} ->
  Lit           ->      -- This literal got assigned 'False'
  Watchers      ->
    ( [(Lit,Clause)]    -- Unit clauses, these did not get moved
    , Watchers          -- New watchers, with wathcees rearranged
    )
setLitFalse as l ws =
  case IntMap.updateLookupWithKey (\_ _ -> Nothing) l (watchedCaluses ws) of
    (Nothing, _)  -> ([], ws)
    (Just cs, mp) -> go [] [] mp (watchedPair ws) cs

  where
  go unitRes u cs ps [] =
    (unitRes, ws { watchedCaluses = IntMap.insert l u cs, watchedPair = ps })

  go unitRes u cs ps ((cid,c) : more) =
    case newLoc c of
      (o, Just l') -> go unitRes u (IntMap.insertWith (++) l' [(cid,c)] cs)
                                   (IntMap.insert cid (o,l) ps)
                                   more
      (o, Nothing) -> go ((o,c) : unitRes) ((cid,c): u) cs ps more

  newLoc c =
    let avoid = IntSet.insert l (IntSet.insert o as)
        o     = other l
    in (o, findLit avoid c)

  other cid = case IntMap.lookup cid (watchedPair ws) of
                Just (a,b) -> if a == l then b else a
                Nothing    -> error ("[setLit] missing watched pair for: "
                                                                  ++ show cid)

-- | Try to find a literal that does not mention any of the given vars.
findLit :: IntSet{-Var-} -> Clause -> Maybe Lit
findLit avoid c = mplus (get posLits) (fmap negate (get negLits))
  where
  get f = fst `fmap` IntSet.minView (f c `IntSet.difference` avoid)




--------------------------------------------------------------------------------

type ClauseId   = Int

data Reason     = ImpliedBy !Clause
                | GuessAtLevel !Int

type Assignment = IntMap {-Var-} (Reason, Bool)

data Res = Sat (IntMap Bool)
         | Unsat
         | BackTrack Int (Lit,Clause) (Maybe Lit) Watchers

search allVars decisionLevel ws as =
  case IntSet.minView todoVars of
    Nothing -> Sat (fmap snd as)
    Just (v,_) ->
      case setLitTrue v (GuessAtLevel decisionLevel) ws as of
        (ws1,as1,new) -> goProp ws1 as1 new
  where
  todoVars = allVars `IntSet.difference` IntMap.keysSet as

  goProp ws' as' todo =
    case propagate ws' as' todo of
      (ws2,as2,mbConfl) ->
        case mbConfl of
          Nothing ->
            case search allVars (decisionLevel+1) ws2 as2 of
              Sat m -> Sat m
              Unsat -> Unsat
              BackTrack undo learn mb ws3
                | undo < decisionLevel -> BackTrack undo learn mb ws3
                | otherwise ->
                  case mb of
                    Just l ->
                      let ws4 = addClause learn l ws3
                      in goProp ws4 as [learn]
                    Nothing -> undefined    -- ? rewrite all clauses?
                      -- or just propagate?  but can we accidentally undo

          Just c ->
            case analyzeConflict as2 c of
              LearnedFalse          -> Unsat
              Learned undo unit lit -> BackTrack undo unit lit ws2


--------------------------------------------------------------------------------

-- | Propagate some unit clauses.
--   Returns a new state, and an optional conflict.
propagate :: Watchers -> Assignment -> [(Lit,Clause)] ->
             (Watchers, Assignment, Maybe Clause)
propagate ws as todo =
  case todo of
    []            -> (ws, as, Nothing)
    (l, c) : more ->
      case IntMap.lookup l as of

        Just (_,True)
          | l > 0     -> propagate ws as more
          | otherwise -> (ws, as, Just c)

        Just (_,False)
          | l < 0     -> propagate ws as more
          | otherwise -> (ws, as, Just c)

        Nothing ->
          case setLitTrue l (ImpliedBy c) ws as of
            (ws', as', new) -> propagate ws' as' (new ++ todo)




{- | Set the literal to true, with the given justification.
      * PRE: the varialbe of the literal is not assigned.
      * This just sets the variable and updates the watchers.
      * It does not look for conflicts.
-}
setLitTrue :: Lit -> Reason ->
              Watchers -> Assignment ->
             ( Watchers
             , Assignment
             , [(Lit,Clause)]     -- new unit clauses
             )
setLitTrue l reason ws as = (ws', as', newUnit)
  where
  (newUnit, ws') = setLitFalse assignedVars notL ws
  as'            = IntMap.insert x (reason, b) as

  x              = abs l
  b              = l > 0
  notL           = negate l

  assignedVars   = IntMap.keysSet as


--------------------------------------------------------------------------------

{- | Given an assignment and the variables and a conflict clause,
compute how far to undo, and a learned clause to avoid the conflict
in the future. -}
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


data LearnedClause = LearnedFalse
                   | Learned Int (Lit,Clause) (Maybe Lit)

learnedClause :: (IntMap {-decision level-} Lit, Clause) -> LearnedClause
learnedClause (m0, c) =
  case IntMap.maxViewWithKey m0 of
    Nothing -> LearnedFalse
    Just ((_,l1),m1) ->
      case IntMap.maxViewWithKey m1 of
        Nothing -> Learned 1 (l1,c) Nothing
        Just ((k2,l2),_) -> Learned (k2 + 1) (l1,c) (Just l2)









