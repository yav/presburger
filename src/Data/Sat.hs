module Data.Sat where


import Data.Integer.Decide

import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set

-- | A positive 'Int'.
type Var        = Int

newtype Lit = Lit Int

-- | The variable must be positive.
litPos :: Var -> Lit
litPos = Lit

-- | Negate a literal.
litNeg :: Lit -> Lit
litNeg (Lit x) = Lit (negate x)

litVar :: Lit -> Var
litVar (Lit x) = abs x

litIsPos :: Lit -> Bool
litIsPos (Lit x) = x > 0

litVal :: S -> Lit -> Maybe Bool
litVal s l = do (_,v) <- Map.lookup (litVar l) (sAssigment s)
                return (if litIsPos l then v else not v)


data Polarity   = Pos | Neg

type Clause     = Map Var Polarity

clause :: [Lit] -> Clause
clause ls = Map.fromList [ (litVar l, if litIsPos l then Pos else Neg)
                              | l <- ls ]

clauseLits :: Clause -> [Lit]
clauseLits = map toLit . Map.toList
  where toLit (x,pol) = case pol of
                          Pos -> litPos x
                          Neg -> litNeg (litPos x)


type ClauseId   = Int

data AssignInfo = ImpliedBy !ClauseId
                | GuessAtLevel !Int

data S = S
  { sIntProps   :: PropSet Int

  , sAssigment  :: Map Var (AssignInfo, Bool)
    -- ^ Assignment for a vaible, and justificaiton for assignment.

  , sNextClause :: !ClauseId
    -- ^ Used to number clauses.

  , sClauses    :: Map ClauseId Clause
    -- ^ The current set of clauses.
  }


setVar :: Var -> AssignInfo -> Bool -> S -> S
setVar x r b s = s { sAssigment = Map.insert x (r,b) (sAssigment s)
                   , sClauses   = Map.mapMaybe upd (sClauses s)
                   }
  where
  upd c = case Map.lookup x c of
            Nothing  -> Just c
            Just Pos -> if b then Nothing else Just (Map.delete x c)
            Just Neg -> if b then Just (Map.delete x c) else Nothing





-- | Extract the conflict clause.
conflictClause :: Map int Lit -> Clause
conflictClause = clause . Map.elems

-- | Undo until the given level, and this literal should be set to true.
undoLevel :: Map Int Lit -> Maybe (Int,Lit)
undoLevel m =
  do ((_,l), more) <- Map.maxViewWithKey m
     case Map.maxViewWithKey more of
       Nothing         -> Just (1,      l)
       Just ((m',_),_) -> Just (m' + 1, l)

{- | Given an assignment and the variables in a conflict clause,
compute which decisions lead to the conflict.
The result maps decision levels, to the corresponding literal in
the conflict clause. -}
analyzeConflict :: S -> Set Var -> Map Int Lit
analyzeConflict s = go Set.empty Map.empty
  where
  go done result todo =
    case Set.minView todo of
      Nothing -> result
      Just (v, todo')
        | v `Set.member` done -> go done result todo'
        | otherwise ->
          case Map.lookup v (sAssigment s) of

            Just (reason, val) ->
              case reason of

                GuessAtLevel n ->
                  let l = if val then litNeg (litPos v) else litPos v
                  in go (Set.insert v done) (Map.insert n l result) todo'

                ImpliedBy c ->

                  case Map.lookup c (sClauses s) of
                    Just ls ->
                      go (Set.insert v done) result
                         (foldr (Set.insert . litVar) todo' (clauseLits ls))

                    Nothing ->
                      error ("[analyzeConflict] Missing clause: " ++ show c)


            Nothing ->
              error ("[analyzeConflict] missing binding for " ++ show v)






