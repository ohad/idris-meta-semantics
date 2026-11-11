||| Higher-order GSOS (HO-GSOS) specification format and the generic
||| operational model gamma.
module HOGSOS

import MAST.Core
import MAST.Presheaf
import MAST.Substitution
import MAST.Tensor
import MAST.Modality
import MAST.Signature
import MAST

import Syntax
import Behaviour

||| Pointwise product of families.
public export
0
PairF : {0 r : SortingSystemOver a b both} ->
  (x, y : r.RSortedFamily) -> r.RSortedFamily
PairF x y ty ctx = (x ty ctx, y ty ctx)

||| Pointwise coproduct of families.
public export
0
EitherF : {0 r : SortingSystemOver a b both} ->
  (x, y : r.RSortedFamily) -> r.RSortedFamily
EitherF x y ty ctx = Either (x ty ctx) (y ty ctx)

||| HO-GSOS law (Sec 2.3, Display (3)).
public export
record HOGSOS (r : SortingSystemOver a b both)
  (s : r.RSortedFamilyBiFun) (beh : r.RSortedFamilyBiFun) where
  constructor MkHOGSOS
  bimap : r.RSortedFamilyBiFunctor s
  mix   : r.RSortedFamilyMixFunctor beh
  rho   : {0 x, y : r.RSortedFamily} ->
          s (PairF {r} x (beh x y)) x -|>
          beh x (Free {r} (Mrg {r} s) (EitherF {r} x y))

||| Operational model (Sec 2.3, Display (4)).
public export
gamma : {r : SortingSystemOver a b both} ->
  {s : r.RSortedFamilyBiFun} ->
  {0 beh : r.RSortedFamilyBiFun} ->
  (law : HOGSOS r s beh) ->
  Initial {r} (Mrg {r} s) -|>
  beh (Initial {r} (Mrg {r} s)) (Initial {r} (Mrg {r} s))
gamma law (Res v)  = absurd v
gamma law (Cont t) =
  law.mix.mxSecond ((Mrg {r} s).extend (MrgFunctor s law.bimap) (either id id)) $
  law.rho $ law.bimap.map (\u => (u, gamma law u)) (\u => u) t
