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

public export infixr 3 ~~>

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

||| The Kripke function space: the internal hom of the presheaf category, and
||| the binder-correct reading of Haskell's `x -> y`.
|||
||| Unfolding `SortedBox`:
|||   (x ~~> y) ty ctx  =  {0 dtx : a.Ctx} -> (dtx ~> ctx) -> x ty dtx -> y ty dtx
|||
||| i.e. a function that still works in *every extension* of the current
||| context. MAST's pointwise exponential `(=|>)` is the wrong choice here: a
||| function value valid only at `ctx` is invalidated the moment it travels
||| under a binder, so `Beh` built on `(=|>)` cannot model a higher-order
||| language with binding.
||| Phrased over `sort`/`bindable` rather than over a `SortingSystemOver`,
||| matching MAST's own `(=|>)`: an extra `{0 r}` implicit here would be
||| undetermined at every use site inside `Beh`.
public export
0
(~~>) : (x, y : sort.SortedFamilyOver bindable) -> sort.SortedFamilyOver bindable
x ~~> y = SortedBox (x =|> y)

||| A handy instance of behaviour (mixed variance) functor: B(X,Y) = Y + Y^X.
|||
||| NOTE: `Eval` relates `x` and `y` at the *same* sort. That is the right
||| notion for an untyped object language, but it is NOT the STLC function
||| space, which sends sort `sigma` to sort `tau` at an arrow type
||| `sigma => tau`. `SortingSystemOver` supplies only the value/computation
||| split, not arrow decomposition of sorts, so the typed version cannot be
||| written at this generality — it belongs with the object language in
||| `Examples`. See CLAUDE.md.
public export
data Beh : {0 r : SortingSystemOver a b both} ->
  (x, y : r.RSortedFamily) ->
  r.RSortedFamily
  where
  Eval : (x ~~> y) -|> Beh {r} x y
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
  Eval h => Eval (\ren, u => g (h ren (f u)))

||| The Kripke function space as a behaviour mixed-variance functor (Haskell's
||| `MixFunctor (->)` instance).
|||
||| `f` and `g` are natural transformations, so they act at the extended
||| context `dtx` without needing any coalgebra structure on `x` or `y`; the
||| renaming `ren` is simply passed through.
|||
||| Use sites must supply `r` explicitly, as `(KripkeExpMixFunctor {r}).mvmap`:
||| `r.RSortedFamily` unfolds to `both.SortedFamilyOver a`, which never mentions
||| `r`'s middle parameter, so `r` is not recoverable from the family types.
||| `BehMixFunctor` and friends do not need this — their `r` is pinned by the
||| `Beh {r}` / `SepBeh {r} d` index.
public export
KripkeExpMixFunctor : {0 r : SortingSystemOver a b both} ->
  r.RSortedFamilyMixFunctor (~~>)
KripkeExpMixFunctor = MkRSortedFamilyMixFunctor $
  \f, g, h => \ren, u => g (h ren (f u))

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
