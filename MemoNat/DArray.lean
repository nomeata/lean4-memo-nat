-- This intentionally only uses std, not mathlib
import Std.Data.Array.Lemmas
import Std.Data.Fin.Basic
import Std.Tactic.Congr

set_option autoImplicit false


inductive Any.{u} : Type u
| mk {α : Sort u} : α → Any

protected abbrev Any.Sort : Any → Sort _
| @mk α _ => α

protected abbrev Any.val : (a : Any) → a.Sort
| mk x => x

theorem Any.congr.{u} {a₁ a₂ : Any}  (h : a₁ = a₂) {α : Sort u} {h₁ : a₁.Sort = α}
    {h₂ : a₂.Sort = α} :
    h₁ ▸ a₁.val = h₂ ▸ a₂.val := by induction h; rfl

--  (_ : Any.Sort (Array.get (Array.push { arr := a, types := types }.arr (Any.mk x)) i) = C i.val) ▸
    -- Any.val (Array.push a (Any.mk x))

structure DArray.{u} (C : Nat → Type u) : Type (u+1):=
  arr : Array Any.{u+1}
  types : ∀ (i : Fin arr.size), (arr.get i).Sort = C i

namespace DArray

protected def empty {C} (cap : Nat) : DArray C :=
  ⟨ Array.mkEmpty cap, λ i => Fin.elim0 i⟩

def size {C} (a : DArray C) := a.arr.size

protected def push {C} (a : DArray C) (x : C a.size) : DArray C :=
  ⟨ a.arr.push (Any.mk x),
   by 
    cases a with | _ a types =>
    dsimp
    intro ⟨i, hi⟩
    dsimp
    rewrite [Array.get_push]
    split
    case inl hi2 =>
      apply types
    case inr hi2 =>
      rewrite [Array.size_push, <- Nat.succ_eq_add_one] at hi
      have : i = Array.size a :=
        Nat.le_antisymm (Nat.le_of_lt_succ hi) (Nat.le_of_not_lt hi2)
      cases this
      rfl
  ⟩

protected theorem size_push {C} (a : DArray C) (x : C a.size) : (a.push x).size = a.size + 1 :=
  Array.size_push _ _

protected def get.{u} {C : Nat → Type u} (a : DArray C) (i : Fin a.size) : C i :=
  let x : Any := Array.get a.arr i
  a.types i ▸ x.val


protected theorem get_push {C} (a : DArray C) (x : C a.size) (i : Fin (a.push x).size) :
    (a.push x).get i =
      if h : i < a.size
      then a.get ⟨i, h⟩
      else
        have : size a = i := Nat.le_antisymm
          (Nat.le_of_not_lt h)
          (Nat.le_of_lt_succ (by simpa [a.size_push x] using i.isLt))
        (this ▸ x : C i) := by
  split 
  case inl hi2 =>
    rcases a with ⟨a, types⟩ 
    apply Any.congr
    dsimp
    unfold DArray.push
    rw [Array.get_push ]
    dsimp
    dsimp [DArray.size] at hi2
    simp [hi2]
  case inr hi2 =>
    have : size a = i := Nat.le_antisymm
      (Nat.le_of_not_lt hi2)
      (Nat.le_of_lt_succ (by simpa [a.size_push x] using i.isLt))
    rcases a with ⟨a, types⟩ 
    dsimp [DArray.get, DArray.push]
    sorry
    


    

  -- rw [ SArray.get_push a.1 (Any.mk x) i hi ]
  sorry
  

end DArray
