-- This intentionally only uses std, not mathlib
import Std.Data.Array.Lemmas
import Std.Data.Fin.Basic
import Std.Tactic.Congr
import MemoNat.DArray

set_option autoImplicit false

universe u

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

def DSArray (n : Nat) (C : Nat → Sort u) : Type u := {a : DArray C // a.size = n}

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

protected def dmemoVec {C : Nat → Sort u} (cap : Nat)
    (f : (n : Nat) → (∀ i, i < n → C i) → C n) :
    (n : Nat) → DSArray n C
  | 0 => .empty cap
  | n + 1 =>
    let v := NatMemo.dmemoVec cap f n
    v.push (f n (fun i ih => v.get ⟨i, ih⟩))

def dmemo {C : Nat → Sort u} (f : (n : Nat) → (∀ i, i < n → C i) → C n) (n : Nat) : C n :=
  (NatMemo.dmemoVec (n + 1) f (n + 1)).get ⟨n, Nat.le_refl _⟩

theorem dmemoVec_spec {C : Nat → Sort u}
  (g : ∀ n, C n)
  (f : (n : Nat) → (∀ i, i < n → C i) → C n)
  (h : ∀ n, f n (fun i _ => g i) = g n)
  n : ∀ c i hi, (NatMemo.dmemoVec c f n).get ⟨i, hi⟩ = g i := by
    induction n
    case zero => 
      intro c i hi
      cases hi
    case succ n ih =>
      intro c i hi
      rw [NatMemo.dmemoVec]
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

theorem dmemo_spec {C : Nat → Sort u}
    (g : ∀ n, C n)
    (f : (n : Nat) → (∀ i, i < n → C i) → C n)
    (h : ∀ n, f n (fun i _ => g i) = g n) :
    g = dmemo f :=
  funext (fun _ => (dmemoVec_spec g f h _ _ _ _).symm)


theorem fix_eq_dmemo {α : Sort u}
  (f : (n : Nat) → (∀ i, i < n → α) → α)
  : WellFounded.fix (invImage (fun a => sizeOf a) instWellFoundedRelation).2 f = dmemo f := by
    apply dmemo_spec
    intro n
    apply (WellFounded.fix_eq _ _ _).symm

def memo {α : Sort u} (f : (n : Nat) → (∀ i, i < n → α) → α) (n : Nat) : α :=
  dmemo f n

theorem memo_spec {α : Sort u}
    (g : Nat → α)
    (f : (n : Nat) → (∀ i, i < n → α) → α)
    (h : ∀ n, f n (fun i _ => g i) = g n) :
    g = dmemo f :=
  dmemo_spec g f h


theorem fix_eq_memo {α} (f : (n : Nat) → (∀ i, i < n → α) → α) :
    WellFounded.fix (invImage (fun a => sizeOf a) instWellFoundedRelation).2 f = memo f :=
  fix_eq_dmemo f


/-
theorem Brec_eq_memo {α}
  (f : (n : Nat) → Nat.below n → α)
  : (fun n => Nat.brecOn n f) = memo f := by
    apply memo_spec
    intro n
    apply (WellFounded.fix_eq _ _ _).symm
-/


end NatMemo
