-- This intentionally only uses std, not mathlib
import Std.Data.Array.Lemmas
import Std.Data.Fin.Basic
import Std.Tactic.Congr

set_option autoImplicit false

/-- Arrays of a given size, H'T Kyle Miller -/
def SArray (α : Type _) (n : Nat) := {a : Array α // a.size = n}

namespace SArray

protected def push {α n} (a : SArray α n) (x : α) : SArray α (n + 1) :=
  ⟨a.1.push x, by rw [Array.size_push, a.2]⟩

protected def get {α n} (a : SArray α n) (i : Fin n) : α :=
  a.1.get ⟨i, a.2.symm ▸ i.2⟩

protected theorem get_push {α n} (a : SArray α n) (x : α) (i : Nat) (hi : i < n + 1) :
    (a.push x).get (⟨i, hi⟩) = if h : i < n then a.get ⟨i, h⟩ else x := by
  simp only [SArray.get, SArray.push, Array.get_eq_getElem, Array.get_push, a.2]

protected def empty {α} (cap : Nat) : SArray α 0 := ⟨Array.mkEmpty cap, rfl⟩

end SArray

inductive Any.{u} : Type u
| mk {α : Sort u} : α → Any

protected abbrev Any.Sort : Any → Sort _
| @mk α _ => α

protected abbrev Any.val : (a : Any) → a.Sort
| mk x => x

structure DArray.{u} (n : Nat) (C : Nat → Type u) : Type (u+1):=
  arr : Array Any.{u+1}
  size_eq : arr.size = n
  types : ∀ (i : Fin arr.size), (arr.get i).Sort = C i
/-
def DArray.{u} (n : Nat) (C : Nat → Type u) : Type (u+1):=
  { a : Array Any.{u+1} //
    a.size = n ∧ ∀ (i : Fin a.size), (a.get i).Sort = C i}
-/

namespace DArray

protected def empty {C} (cap : Nat) : DArray 0 C :=
  ⟨ Array.mkEmpty cap, rfl, λ i => Fin.elim0 i⟩

protected def push {n C} (a : DArray n C) (x : C n) : DArray (n + 1) C :=
  ⟨ a.arr.push (Any.mk x),
   by rw [Array.size_push, a.size_eq],
   by 
    cases a with | _ a size_eq types =>
    cases size_eq
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

protected def get.{u} {n} {C : Nat → Type u} (a : DArray n C) (i : Fin n) : C i :=
  let i' := i.cast a.size_eq.symm
  let x : Any := Array.get a.arr i'
  a.types i' ▸ x.val

protected theorem get_push {n C} (a : DArray n C) (x : C n) (i : Nat) (hi : i < n + 1) :
    (a.push x).get ⟨i, hi⟩ =
      if h : i < n
      then a.get ⟨i, h⟩
      else (Nat.le_antisymm (Nat.le_of_lt_succ hi) (Nat.le_of_not_lt h) ▸ x : C i) := by
  split 
  case inl hi2 =>
    rcases a with ⟨a, rfl, types⟩ 
    unfold DArray.push
    unfold DArray.get
    dsimp
    

  -- rw [ SArray.get_push a.1 (Any.mk x) i hi ]
  sorry
  

end DArray

namespace NatMemo

protected def memoVec {C} (cap : Nat) (f : (n : Nat) → (∀ i, i < n → C i) → C n) :
  (n : Nat) → DArray n C
  | 0 => .empty cap
  | n + 1 =>
    let v := NatMemo.memoVec cap f n
    v.push (f n (fun i ih => v.get ⟨i, ih⟩))

def memo {C : Nat → Sort _} (f : (n : Nat) → (∀ i, i < n → C i) → C n) (n : Nat) : C n :=
  (NatMemo.memoVec (n + 1) f (n + 1)).get ⟨n, Nat.le_refl _⟩

theorem memoVec_spec {C : Nat → Sort _}
  (g : ∀ n, C n)
  (f : (n : Nat) → (∀ i, i < n → C i) → C n)
  (h : ∀ n, f n (fun i _ => g i) = g n)
  n : ∀ c i hi, (NatMemo.memoVec c f n).get ⟨i, hi⟩ = g i := by
    induction n
    case zero => 
      intro c i hi
      cases hi
    case succ n ih =>
      intro c i hi
      rw [NatMemo.memoVec]
      apply Eq.trans (DArray.get_push _ _ _ _)
      split
      case inl hn =>
        apply ih
      case inr hn =>
        have i_eq_n : i = n := Nat.le_antisymm (Nat.lt_succ.1 hi) (Nat.not_lt.1 hn)
        rcases i_eq_n
        rw [<- h]
        simp only
        congr with i hi'
        apply ih

theorem memo_spec {C : Nat → Sort _}
  (g : ∀ n, C n)
  (f : (n : Nat) → (∀ i, i < n → C i) → C n)
  (h : ∀ n, f n (fun i _ => g i) = g n) :
  g = memo f := funext (fun _ => (memoVec_spec g f h _ _ _ _).symm)

theorem fix_eq_memo {α}
  (f : (n : Nat) → (∀ i, i < n → α) → α)
  : WellFounded.fix (invImage (fun a => sizeOf a) instWellFoundedRelation).2 f = memo f := by
    apply memo_spec
    intro n
    apply (WellFounded.fix_eq _ _ _).symm

/-
theorem Brec_eq_memo {α}
  (f : (n : Nat) → Nat.below n → α)
  : (fun n => Nat.brecOn n f) = memo f := by
    apply memo_spec
    intro n
    apply (WellFounded.fix_eq _ _ _).symm
-/


end NatMemo
