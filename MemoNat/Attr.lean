import MemoNat
import Lean.Compiler.CSimpAttr

open Lean Meta Elab Tactic Term

def memoAttrImpl (n : Name) : AttrM Unit := do
  let defn ← getConstInfoDefn n

  let (u, f, drt) <- match defn.value with
    | .app (.app (.app (.app (.app (.const `WellFounded.fix [u1, _u2]) dt) drt) _) _) f => do
      match dt with
      | .const `Nat _ => pure ()
      | _ =>  throwError ("first argument to fix not Nat but" ++ toString dt)
      pure (u1, f, drt)
    | .lam _ (.const `Nat _) ( .app (.app (.app (.const `Nat.brecOn [u]) drt) _) f) _ => do
      throwError "definitions using Nat.brecOn are not yet supported"
      pure (u, f, drt)
    | _ => throwError ("definition right hand side not of expected form: " ++ toString defn.value)
    
  -- We assume the result motive to be non-dependent.
  -- If it's dependent there will be a type error later
  let rt := mkApp drt (mkConst `Nat.zero)

  let slow_name := defn.name
  let fast_name := slow_name.append (.mkSimple "fast")
  let eq_name   := slow_name.append (.mkSimple "eq_fast")
  
  addAndCompile (.defnDecl { defn with
    name := fast_name
    -- NB: This declaration has the same type as slow
    value := mkAppN (mkConst `NatMemo.memo []) #[rt, f]
  })

  addAndCompile (.thmDecl { defn with
    name := eq_name
    type := mkAppN (mkConst `Eq [u]) #[defn.type, mkConst slow_name, mkConst fast_name]
    value := mkAppN (mkConst `NatMemo.fix_eq_memo) #[rt, f]
  })

  Lean.Compiler.CSimp.add eq_name AttributeKind.global


initialize memoAttr : TagAttribute ←
  registerTagAttribute `memo
    "Create a memoized version of this function, and use it during evaluation instead"
      memoAttrImpl
