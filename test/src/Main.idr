module Main

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
ctx1 = [< "x" :- (), "w" :- ()]

ctx2 : (Unit).Ctx
ctx2 = [< "y" :- (), "z" :- ()]

||| `x ↦ z`, `w ↦ y`.
env : (Syn NoSig).env Main.ctx1 Main.ctx2
env {ty = ()} ((%%) _ {pos = Here})         = Res ((%%) "y" {pos = There Here})
env {ty = ()} ((%%) _ {pos = There Here})   = Res ((%%) "z" {pos = Here})

||| `y ↦ w`, `z ↦ x`.
ren : Main.ctx1 ~> Main.ctx2
ren {ty = ()} ((%%) _ {pos = Here})         = (%%) "x" {pos = There Here}
ren {ty = ()} ((%%) _ {pos = There Here})   = (%%) "w" {pos = Here}

||| De Bruijn index of a variable, counted from the right.
index : {0 ctx : (Unit).Ctx} -> ctx.var () -> Nat
index v = go v.pos
  where
    go : {0 c : (Unit).Ctx} -> {0 n : String} -> c.varPos n () -> Nat
    go Here      = 0
    go (There p) = S (go p)

showSyn : {0 ctx : (Unit).Ctx} -> Syn NoSig () ctx -> String
showSyn (Res v)  = "#" ++ show (index v)
showSyn (Cont k) = absurd k

x1 : Syn NoSig () Main.ctx1
x1 = Res ((%%) "x" {pos = There Here})

w1 : Syn NoSig () Main.ctx1
w1 = Res ((%%) "w" {pos = Here})

substitute : Syn NoSig () Main.ctx1 -> Syn NoSig () Main.ctx2
substitute t = Subst.subst noSigMap noSigLift noSigStr
  {ty = ()} {ctx = Main.ctx2} (Evidence Main.ctx1 (t, Main.env))

rename : Syn NoSig () Main.ctx2 -> Syn NoSig () Main.ctx1
rename t = Subst.synRen noSigMap noSigLift
  {s = ()} {ctx = Main.ctx2} t {dtx = Main.ctx1} Main.ren

check : String -> String -> String -> IO Bool
check label expected actual = do
  let ok = expected == actual
  putStrLn $ (if ok then "ok   " else "FAIL ") ++ label
          ++ ": expected " ++ expected ++ ", got " ++ actual
  pure ok

main : IO ()
main = do
  r1 <- check "subst x[x:=z,w:=y]" "#0" (showSyn (substitute x1))
  r2 <- check "subst w[x:=z,w:=y]" "#1" (showSyn (substitute w1))
  r3 <- check "rename y[y:=w,z:=x]" "#0"
          (showSyn (rename (Res ((%%) "y" {pos = There Here}))))
  r4 <- check "rename z[y:=w,z:=x]" "#1"
          (showSyn (rename (Res ((%%) "z" {pos = Here}))))
  putStrLn $ if r1 && r2 && r3 && r4 then "all passed" else "FAILURES"
