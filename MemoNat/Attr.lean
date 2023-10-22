import MemoNat
import Lean.Compiler.CSimpAttr

open Lean Meta Elab Tactic Term

def memoAttrImpl (n : Name) : AttrM Unit := do
  let defn ← getConstInfoDefn n

  let (u, f, drt, dmemo, eq_dmemo) <- match defn.value with
    | .app (.app (.app (.app (.app (.const ``WellFounded.fix [_u, u]) dt) drt) _) _) f =>
      match dt with
      | .const ``Nat _ => pure ()
      | _ =>  throwError s!"first argument to fix not `Nat` but {dt}"
      pure (u, f, drt, ``NatMemo.dmemo, ``NatMemo.fix_eq_dmemo)
    | .lam _ (.const ``Nat _) ( .app (.app (.app (.const ``Nat.brecOn [u]) drt) _) f) _ =>
      pure (u, f, drt, ``NatMemo.dmemo_below, ``NatMemo.brecOn_eq_dmemo_below)
    | _ => throwError s!"definition right hand side not of expected form: {defn.value}"
    
  let slow_name := defn.name
  let fast_name := slow_name ++ `fast
  let eq_name   := slow_name ++ `eq_fast

  addAndCompile (.defnDecl { defn with
    name := fast_name
    -- NB: This declaration has the same type as slow
    value := mkAppN (.const dmemo [u]) #[drt, f]
  })

  addDecl (.thmDecl { defn with
    name := eq_name
    type := mkAppN (.const ``Eq [u]) #[defn.type, .const slow_name [], .const fast_name []]
     -- FIXME: is it necessarily the case that `slow_name` and `fast_name` have no universe params?
    value := mkAppN (.const eq_dmemo [u]) #[drt, f]
  })

  Lean.Compiler.CSimp.add eq_name AttributeKind.global


initialize memoAttr : TagAttribute ←
  registerTagAttribute `memo
    "Create a memoized version of this function, and use it during evaluation instead"
      memoAttrImpl
