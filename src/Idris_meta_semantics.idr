module Idris_meta_semantics

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
  Cont : (s $ Free  s x) -|> Free s x

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
s.extend maprec@(MkRSortedFamilyFunctor map) f (Cont {s} k)
  = let foo : Free {r} s x ty ctx -> Free {r} s y ty ctx = s.extend maprec f
          --map {p = ?wut2, q = ?wut1}
        k' : s (Free s x) ty ctx = k
        baz : (0 ctx : a.Ctx) -> (0 ty : both) ->
           Free s x ty ctx -> Free s y ty ctx := \ctx', ty' =>
              map foo ?wughg
    in Cont ?wut

test : String
test = "Hello from Idris2!"
