||| Requires `MAST.Initiality` to export the definitions of `(.Algebra)`,
||| `(.hat)`, `(.hatMap)`, `(.hatLift)`, `BoxMap`, `Prop3_1_4`,
||| `AlgebraLift`, `cast` and the `Cast` implementation for `Algebra`;
||| without `public export` on those, `Subst.synRen` typechecks but does
||| not reduce, and `smoke` below fails.
module Smoke2

import MAST.Core
import MAST.Presheaf
import MAST.Substitution
import MAST.Tensor
import MAST.Modality
import MAST.Signature
import MAST.Initiality

import Syntax
import Subst

0
NoSig : (Unit,Unit) ====> (Unit,Unit)
NoSig x = \_, _ => Void

noSigMap : (NoSig).RSortedFamilyFunctor
noSigMap = MkRSortedFamilyFunctor $ \_ => absurd

noSigLift : BoxLift NoSig
noSigLift x coalg = absurd

ctx1 : (Unit).Ctx
ctx1 = [< "x" :- ()]

ctx2 : (Unit).Ctx
ctx2 = [< "y" :- ()]

ren : Smoke2.ctx2 ~> Smoke2.ctx1
ren {ty = ()} _ = (%%) "y" {pos = Here}

||| Renaming `x` to `y` in the term `x` yields `y`.
smoke : Subst.synRen Smoke2.noSigMap Smoke2.noSigLift
          {s = ()} {ctx = Smoke2.ctx1}
          (Syntax.Res ((%%) "x" {pos = Here})) {dtx = Smoke2.ctx2} Smoke2.ren
      = the (Syn NoSig () Smoke2.ctx2) (Syntax.Res ((%%) "y" {pos = Here}))
smoke = Refl
