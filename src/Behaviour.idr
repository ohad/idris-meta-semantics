||| General definitions related to modelling higher-order behaviours as
||| (mixed variance) functors.
|||
||| Port of `Behaviour.hs`. The Haskell `MixFunctor` type class becomes an
||| explicitly-passed dictionary record, following the convention already used
||| for functors and bifunctors in `Syntax`.
module Behaviour

import MAST.Core
import MAST.Presheaf
import MAST.Substitution
import MAST.Tensor
import MAST.Modality
import MAST.Signature
import MAST

import Syntax

||| The class of mixed-variance functors: contravariant in the first argument,
||| covariant in the second.
|||
||| Haskell's `mx_first`/`mx_second` are class methods with mutually-recursive
||| defaults; here they are derived operations (`.mxFirst`, `.mxSecond`) taking
||| the dictionary, since every instance defines `mvmap` anyway.
public export
record (.RSortedFamilyMixFunctor) (r : SortingSystemOver a b both)
  (f : r.RSortedFamilyBiFun) where
  constructor MkRSortedFamilyMixFunctor
  mvmap : {0 p1, p2, q1, q2 : r.RSortedFamily} ->
          (p1 -|> p2) -> (q1 -|> q2) ->
          (f p2 q1 -|> f p1 q2)

public export
(.mxSecond) : {0 r : SortingSystemOver a b both} ->
  {0 f : r.RSortedFamilyBiFun} ->
  (mix : r.RSortedFamilyMixFunctor f) ->
  {0 p, q1, q2 : r.RSortedFamily} ->
  (q1 -|> q2) -> (f p q1 -|> f p q2)
mix.mxSecond g = mix.mvmap (\u => u) g

public export
(.mxFirst) : {0 r : SortingSystemOver a b both} ->
  {0 f : r.RSortedFamilyBiFun} ->
  (mix : r.RSortedFamilyMixFunctor f) ->
  {0 p1, p2, q : r.RSortedFamily} ->
  (p1 -|> p2) -> (f p2 q -|> f p1 q)
mix.mxFirst g = mix.mvmap g (\u => u)

||| A handy instance of behaviour (mixed variance) functor: B(X,Y) = Y + Y^X.
|||
||| The exponential is MAST's pointwise `(=|>)`, the literal reading of
||| Haskell's `x -> y`. See the note in CLAUDE.md: the Kripke exponential is
||| the alternative worth considering for the presheaf case studies.
public export
data Beh : {0 r : SortingSystemOver a b both} ->
  (x, y : r.RSortedFamily) ->
  r.RSortedFamily
  where
  Eval : (x =|> y) -|> Beh {r} x y
  Red  : y -|> Beh {r} x y

||| Effectless "separated" behaviour functor (Sec. 2.1., didactic purpose only)
public export
data SepBeh : {0 r : SortingSystemOver a b both} ->
  (d : r.RSortedFamilyBiFun) ->
  (x, y : r.RSortedFamily) ->
  r.RSortedFamily
  where
  BehV : d x y -|> SepBeh {r} d x y
  BehC : y     -|> SepBeh {r} d x y

||| (Effectful) "separated" behaviour functor, Def. 3.1
public export
data SepBehT : {0 r : SortingSystemOver a b both} ->
  (t : r.RSortedFamilyFun) ->
  (d : r.RSortedFamilyBiFun) ->
  (x, y : r.RSortedFamily) ->
  r.RSortedFamily
  where
  BehVT : d x y -|> SepBehT {r} t d x y
  BehCT : t y   -|> SepBehT {r} t d x y

||| Instantiating `Beh` as a mixed-variance functor.
public export
BehMixFunctor : {0 r : SortingSystemOver a b both} ->
  r.RSortedFamilyMixFunctor (Beh {r})
BehMixFunctor = MkRSortedFamilyMixFunctor $ \f, g => \case
  Red  y => Red (g y)
  Eval h => Eval (\u => g (h (f u)))

||| The exponential as a behaviour mixed-variance functor (Haskell's
||| `MixFunctor (->)` instance).
|||
||| Use sites must supply `r` explicitly, as `(ExpMixFunctor {r}).mvmap`:
||| `r.RSortedFamily` unfolds to `both.SortedFamilyOver a`, which never mentions
||| `r`'s middle parameter, so `r` is not recoverable from the family types.
||| `BehMixFunctor` and friends do not need this — their `r` is pinned by the
||| `Beh {r}` / `SepBeh {r} d` index.
public export
ExpMixFunctor : {0 r : SortingSystemOver a b both} ->
  r.RSortedFamilyMixFunctor (=|>)
ExpMixFunctor = MkRSortedFamilyMixFunctor $ \f, g, h => \u => g (h (f u))

||| Instantiating the separated effectless behaviour as a mixed-variance functor.
public export
SepBehMixFunctor : {0 r : SortingSystemOver a b both} ->
  {0 d : r.RSortedFamilyBiFun} ->
  r.RSortedFamilyMixFunctor d ->
  r.RSortedFamilyMixFunctor (SepBeh {r} d)
SepBehMixFunctor mix = MkRSortedFamilyMixFunctor $ \f, g => \case
  BehV u => BehV (mix.mvmap f g u)
  BehC u => BehC (g u)

||| Instantiating the separated effectful behaviour as a mixed-variance functor.
public export
SepBehTMixFunctor : {0 r : SortingSystemOver a b both} ->
  {0 d : r.RSortedFamilyBiFun} ->
  (t : (both, a) ====> (both, a)) ->
  t.RSortedFamilyFunctor ->
  r.RSortedFamilyMixFunctor d ->
  r.RSortedFamilyMixFunctor (SepBehT {r} t d)
SepBehTMixFunctor t (MkRSortedFamilyFunctor map) mix = MkRSortedFamilyMixFunctor $ \f, g => \case
  BehVT u => BehVT (mix.mvmap f g u)
  BehCT u => BehCT (map g u)
