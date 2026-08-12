||| Requires `MAST.Initiality` to export the definitions of
||| `boxClosedCostrength`, `associate`, `tensorClosedStrength` and
||| `Prop11_2_1`; without `public export` on those four, `Subst.subst`
||| typechecks but does not reduce, and `smoke` below fails.
module Smoke

import MAST.Core
import MAST.Presheaf
import MAST.Substitution
import MAST.Tensor
import MAST.Modality
import MAST.Signature
import MAST.Initiality

import Syntax
import Subst

||| The empty signature: `Syn NoSig` is just variables.
public export
0
NoSig : (Unit,Unit) ====> (Unit,Unit)
NoSig x = \_, _ => Void

noSigMap : (NoSig).RSortedFamilyFunctor
noSigMap = MkRSortedFamilyFunctor $ \_ => absurd

noSigLift : BoxLift NoSig
noSigLift x coalg = absurd

noSigStr : (NoSig).PointedClosedStrength
noSigStr x var = absurd

ctx1 : (Unit).Ctx
ctx1 = [< "x" :- ()]

ctx2 : (Unit).Ctx
ctx2 = [< "y" :- ()]

env : (Syn NoSig).env Smoke.ctx1 Smoke.ctx2
env {ty = ()} _ = Syntax.Res ((%%) "y" {pos = Here})

||| Substituting `y` for `x` in the term `x` yields `y`.
smoke : Subst.subst Smoke.noSigMap Smoke.noSigLift Smoke.noSigStr
          {ty = ()} {ctx = Smoke.ctx2}
          (Evidence Smoke.ctx1 (Syntax.Res ((%%) "x" {pos = Here}), Smoke.env))
      = the (Syn NoSig () Smoke.ctx2) (Syntax.Res ((%%) "y" {pos = Here}))
smoke = Refl
