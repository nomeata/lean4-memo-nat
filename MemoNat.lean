-- This intentionally only uses std, not mathlib
import Std.Data.Array.Lemmas
import Std.Data.Fin.Basic
import Std.Tactic.Congr
import MemoNat.DArray

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

/-- Dependent arrays of a given size, H'T Kyle Miller -/
def DSArray (n : Nat) (C : Nat → Type _)  := {a : DArray C // a.size = n}

namespace DSArray

protected def empty {C} (cap : Nat) : DSArray 0 C := ⟨DArray.mkEmpty cap, rfl⟩

protected def push {C n} (a : DSArray n C) (x : C n) : DSArray (n + 1) C :=
  ⟨a.1.push (a.2.symm ▸ x), by rw [DArray.size_push, a.2]⟩

protected def get {C n} (a : DSArray n C) (i : Fin n) : C i :=
  a.1.get ⟨i, a.2.symm ▸ i.2⟩

protected theorem get_push {C n} (a : DSArray n C) (i : Nat) (hi : i < n + 1) (x : C n) :
    (a.push x).get (⟨i, hi⟩) =
      if h : i < n then
        a.get ⟨i, h⟩
      else
        have : n = i := Nat.le_antisymm
          (Nat.le_of_not_lt h)
          (Nat.le_of_lt_succ hi)
        this ▸ x := by
  simp only [DSArray.get, DSArray.push, DArray.get_push, a.2]
  split
  · rfl
  case inr h =>
    have : n = i := Nat.le_antisymm
          (Nat.le_of_not_lt h)
          (Nat.le_of_lt_succ hi)
    cases this
    cases a
    case _ a ha =>
      dsimp
      cases ha
      rfl

end DSArray

namespace NatMemo

protected def memoVec {C} (cap : Nat) (f : (n : Nat) → (∀ i, i < n → C i) → C n) :
  (n : Nat) → DSArray n C
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
      apply Eq.trans (DSArray.get_push _ _ _ _)
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
