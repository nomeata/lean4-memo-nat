-- This intentionally only uses std, not mathlib
import Std.Data.Array.Lemmas
import Std

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

namespace NatMemo

protected def memoVec {α} (cap : Nat) (f : (n : Nat) → (∀ i, i < n → α) → α ) :
  (n : Nat) → SArray α n
  | 0 => .empty cap
  | n + 1 =>
    let v := NatMemo.memoVec cap f n
    v.push (f n (fun i ih => v.get ⟨i, ih⟩))

def memo {α : Type} (f : (n : Nat) → (∀ i, i < n → α) → α) (n : Nat) : α :=
  (NatMemo.memoVec (n + 1) f (n + 1)).get ⟨n, Nat.le_refl _⟩

theorem memoVec_spec {α}
  (g : Nat → α)
  (f : (n : Nat) → (∀ i, i < n → α) → α)
  (h : ∀ n, f n (fun i _ => g i) = g n)
  n : ∀ c i hi, (NatMemo.memoVec c f n).get ⟨i, hi⟩ = g i := by
    induction n
    case zero => 
      intro c i hi
      cases hi
    case succ n ih =>
      intro c i hi
      rw [NatMemo.memoVec]
      apply Eq.trans (SArray.get_push _ _ _ _)
      split
      case inl hn =>
        apply ih
      case inr hn =>
        have i_eq_n : i = n := Nat.le_antisymm (Nat.lt_succ.1 hi) (Nat.not_lt.1 hn)
        rcases i_eq_n
        rw [<- h]
        congr with i hi'
        apply ih

theorem memo_spec {α}
  (g : Nat → α)
  (f : (n : Nat) → (∀ i, i < n → α) → α)
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
