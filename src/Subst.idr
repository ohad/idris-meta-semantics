module Subst

import MAST.Core
import MAST.Presheaf
import MAST.Substitution
import MAST.Tensor
import MAST.Modality
import MAST.Signature
import MAST.Initiality

import Syntax

||| The sorting system in which every sort is a value sort.
public export
Triv : SortingSystemOver sort Void sort
Triv = MkSortingSystemOver
  { fst = id
  , snd = absurd
  , copair = \val, _ => val
  }

||| Terms over the signature `sig` with variables as generators.
public export
0
Syn : (sig : sort.HomogeneousFamily -> sort.HomogeneousFamily) -> sort.HomogeneousFamily
Syn sig = Free {r = Triv} sig Var

||| The empty family of metavariables.
public export
0
NoMeta : sort.HomogeneousFamily
NoMeta = \_, _ => Void

public export
synAlgebra : {0 sig : (sort,sort) ====> (sort,sort)} ->
  Algebra Triv sig NoMeta (Syn sig)
synAlgebra = MkAlgebra
  { alg  = Cont
  , var  = Res
  , menv = \u => absurd (fst u.snd)
  }

public export
synFold : {0 sig : (sort,sort) ====> (sort,sort)} ->
  sig.RSortedFamilyFunctor ->
  FamInitial {o = sig, mvar = NoMeta} Triv (synAlgebra {sig})
synFold smap blg (Res  i) = blg.var i
synFold smap blg (Cont k) = blg.alg (smap.map (synFold smap blg) k)

||| The renaming action.
public export
synRen : {0 sig : (sort,sort) ====> (sort,sort)} ->
  (smap : sig.RSortedFamilyFunctor) ->
  BoxLift sig ->
  (Syn sig).SortedBoxCoalgebraStructure
synRen smap lift = PShInitial smap (synAlgebra {sig}) (synFold smap) lift

||| Capture-avoiding substitution, in transposed form.
public export
substExp : {0 sig : (sort,sort) ====> (sort,sort)} ->
  (smap : sig.RSortedFamilyFunctor) ->
  BoxLift sig ->
  sig.PointedClosedStrength ->
  Syn sig -|> Syn sig <-# Syn sig
substExp smap lift str =
  (synFold smap).subst {synAlg = synAlgebra} smap lift str

||| Capture-avoiding substitution.
public export
subst : {0 sig : (sort,sort) ====> (sort,sort)} ->
  (smap : sig.RSortedFamilyFunctor) ->
  BoxLift sig ->
  sig.PointedClosedStrength ->
  Syn sig <#> Syn sig -|> Syn sig
subst smap lift str = sortedFamilyUncurry
  {x = Syn sig, y = Syn sig, z = Syn sig}
  (substExp smap lift str)
