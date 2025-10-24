module Syntax

import MAST.Core
import MAST.Presheaf
import MAST.Substitution
import MAST.Tensor
import MAST.Modality
import MAST.Signature
import MAST

0
(.RSortedFamilyBiFun) : (r : SortingSystemOver a b both) -> Type
r.RSortedFamilyBiFun = r.RSortedFamily -> r.RSortedFamilyFun

-- Is this correct?
Mrg : (s : r.RSortedFamilyBiFun) -> (x : r.RSortedFamily) -> r.RSortedFamily
Mrg s x = s x x

data Free : {r : SortingSystemOver a b both} ->
   (s : r.RSortedFamilyFun) ->
   (x : r.RSortedFamily) ->
   r.RSortedFamily
   where
  Res : x -|> Free s x
  Cont : (s $ Free {r} s x) -|> Free {r} s x

(.FreeMap) : {0 r : SortingSystemOver a b both} ->
  (s : (both,a) ====> (both,a)) ->
  s.RSortedFamilyFunctor ->
  (Free {r} s).RSortedFamilyFunctor

s.FreeMap map = MkRSortedFamilyFunctor $ \f => \case
    Res  x => Res (f x)
    Cont x => let MkRSortedFamilyFunctor map' = (s.FreeMap map)
              in Cont $ map.map (map' f) x



0
Initial : (s : r.RSortedFamilyFun) -> r.RSortedFamily
Initial s = Free {r} s $ const $ const Void

sigOp : {0 r : SortingSystemOver a b both} ->
  {s : r.RSortedFamilyBiFun} ->
  {x : r.RSortedFamily} ->
  s (Free {r} (Mrg {r} s) x) (Free {r} (Mrg {r} s) x) -|> Free {r} (Mrg {r} s) x
sigOp = Cont

-- Monad
(.extend) : {0 r : SortingSystemOver a b both} ->
  (s : (both,a) ====> (both,a)) ->
  s.RSortedFamilyFunctor ->
  {x,y : r.RSortedFamily} ->
  (x -|> Free {r} s y) -> (Free {r} s x -|> Free {r} s y)
s.extend map f (Res  i) = f i
s.extend maprec@(MkRSortedFamilyFunctor map) {x,y} f (Cont {s} k)
  = Cont (map (s.extend maprec f) k)

public export
record (.RSortedFamilyBiFunctor) (r : SortingSystemOver a b both)
  (f : r.RSortedFamilyBiFun) where
  constructor MkRSortedFamilyBiFunctor
  map : {0 p1,p2, q1,q2 : r.RSortedFamily} ->
  (p1 -|> p2) -> (q1 -|> q2) ->
  (f p1 q1 -|> f p2 q2 )

MrgFunctor : {r : SortingSystemOver a b both} ->
  (s : r.RSortedFamilyBiFun) ->
  r.RSortedFamilyBiFunctor s ->
  (Mrg {r} s).RSortedFamilyFunctor
MrgFunctor s (MkRSortedFamilyBiFunctor bimap) = MkRSortedFamilyFunctor $
  \f => bimap f f
