/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean

namespace Algebra

open Lean

def isNum? (e : Expr) : Option Nat := do
  guard $ e.isAppOfArity `OfNat.ofNat 3
  e.appFn!.appArg!.natLit?

def isHBin? (n : Name) (e : Expr) : Option (Expr × Expr) := do
  guard $ e.isAppOfArity n 6
  let args := e.getAppArgs
  pure (args[4], args[5])

def isAdd? : Expr → Option (Expr × Expr) := isHBin? `HAdd.hAdd
def isSub? : Expr → Option (Expr × Expr) := isHBin? `HSub.hSub
def isMul? : Expr → Option (Expr × Expr) := isHBin? `HMul.hMul
def isPow? : Expr → Option (Expr × Expr) := isHBin? `HPow.hPow

end Algebra
