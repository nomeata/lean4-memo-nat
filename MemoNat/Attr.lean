import MemoNat
import Lean.Compiler.CSimpAttr

open Lean Meta Elab Tactic Term

def memoAttrImpl (n : Name) : AttrM Unit := do
  let defn ← getConstInfoDefn n

  let (u, f, drt, dmemo, eq_dmemo) <- match defn.value with
    | .app (.app (.app (.app (.app (.const ``WellFounded.fix [_u, u]) dt) drt) _) _) f => do
      match dt with
      | .const `Nat _ => pure ()
      | _ =>  throwError ("first argument to fix not `Nat` but" ++ toString dt)


      pure (u, f, drt, ``NatMemo.dmemo, ``NatMemo.fix_eq_dmemo)
    | .lam _ (.const `Nat _) ( .app (.app (.app (.const `Nat.brecOn [u]) drt) _) f) _ => do
      pure (u, f, drt, ``NatMemo.dmemo_below, ``NatMemo.brecOn_eq_dmemo_below)
    | _ => throwError ("definition right hand side not of expected form: " ++ toString defn.value)
    
  let slow_name := defn.name
  let fast_name := slow_name.append (.mkSimple "fast")
  let eq_name   := slow_name.append (.mkSimple "eq_fast")

  addAndCompile (.defnDecl { defn with
    name := fast_name
    -- NB: This declaration has the same type as slow
    value := mkAppN (mkConst dmemo [u]) #[drt, f]
  })

  addAndCompile (.thmDecl { defn with
    name := eq_name
    type := mkAppN (mkConst `Eq [u]) #[defn.type, mkConst slow_name, mkConst fast_name]
    value := mkAppN (mkConst eq_dmemo [u]) #[drt, f]
  })

  Lean.Compiler.CSimp.add eq_name AttributeKind.global


initialize memoAttr : TagAttribute ←
  registerTagAttribute `memo
    "Create a memoized version of this function, and use it during evaluation instead"
      memoAttrImpl
