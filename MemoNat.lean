-- This intentionally only uses std, not mathlib
import Std.Data.Array.Lemmas
import Std.Data.Fin.Basic
import Std.Data.Fin.Lemmas
import Std.Tactic.Congr
import MemoNat.DArray
import MemoNat.DSArray

set_option autoImplicit false

universe u

namespace NatMemo

protected def dmemoVec {C : Nat → Sort u} (cap : Nat)
    (f : (n : Nat) → DSArray n C → C n) :
    (n : Nat) → DSArray n C
  | 0 => .empty cap
  | n + 1 =>
    let v := NatMemo.dmemoVec cap f n
    v.push (f n v)

theorem dmemoVec_eq_ofFn {C : Nat → Sort u}
    (c : Nat)
    (g : ∀ n, C n)
    (f : (n : Nat) → DSArray n C → C n)
    (h : ∀ n, f n (.ofFn (n := n) (fun i => g i)) = g n)
    (n : Nat) : NatMemo.dmemoVec c f n = .ofFn (n:=n) (fun i => g i) := by
  induction n
  · case zero => rfl
  · case succ n IH => 
    unfold NatMemo.dmemoVec
    simp only
    rw [IH]
    ext i hi
    dsimp
    rw [DSArray.get_push, DSArray.get_ofFn]
    split
    case inl hn =>
      simp only [DSArray.get_ofFn]
    case inr hn =>
      have i_eq_n : i = n := Nat.le_antisymm (Nat.lt_succ.1 hi) (Nat.not_lt.1 hn)
      rcases i_eq_n
      simp only [DSArray.get_ofFn, h]

def dmemo {C : Nat → Sort u} (f : (n : Nat) → (∀ i, i < n → C i) → C n) (n : Nat) : C n :=
  (NatMemo.dmemoVec (n + 1) (fun n a => f n (fun i ih => a.get ⟨i, ih⟩)) (n + 1)
  ).get ⟨n, Nat.le_refl _⟩


theorem dmemo_spec {C : Nat → Sort u}
    (g : ∀ n, C n)
    (f : (n : Nat) → (∀ i, i < n → C i) → C n)
    (h : ∀ n, f n (fun i _ => g i) = g n) :
    g = dmemo f := by
  ext n
  unfold dmemo
  rw [dmemoVec_eq_ofFn _ g]
  · simp only [DSArray.get_ofFn]
  · intro n' 
    simp only [DSArray.get_ofFn, h]

theorem fix_eq_dmemo {C : Nat → Sort u}
    (f : (n : Nat) → (∀ i, i < n → C i) → C n) :
    WellFounded.fix (invImage (fun a => sizeOf a) instWellFoundedRelation).2 f = dmemo f := by
  apply dmemo_spec
  intro n
  apply (WellFounded.fix_eq _ _ _).symm

def dmemo_below {C : Nat → Sort u}
    (f : (n : Nat) → @Nat.below C n → C n)
    (n : Nat) : C n :=
  (NatMemo.dmemoVec (n + 1) (fun n a => f n a.to_below) (n + 1)).get ⟨n, Nat.le_refl _⟩

def below_ofFn {C : Nat → Sort u} (g : ∀ n, C n) : (n : Nat) → @Nat.below C n
  | 0 => PUnit.unit
  | n+1 => ⟨⟨g n, below_ofFn g n⟩,.unit⟩



theorem DSArray.to_below_ofFn_eq_below_ofFn {C : Nat → Sort u} (n : Nat) (g : (i : Nat) → C i)  :
    DSArray.to_below (DSArray.ofFn n (fun i => g i)) = below_ofFn g n := by
  induction n
  · case zero => rfl
  · case succ n IH => 
    rw [DSArray.to_below_succ]
    dsimp [below_ofFn]
    rw [DSArray.get_ofFn]
    congr
    rw [DSArray.pop_ofFn]
    exact IH

theorem dmemo_below_spec {C : Nat → Sort u}
    (g : ∀ n, C n)
    (f : (n : Nat) → @Nat.below C n → C n)
    (h : ∀ n, f n (below_ofFn g n) = g n) :
    g = dmemo_below f := by
  ext n
  unfold dmemo_below
  rw [dmemoVec_eq_ofFn _ g]
  · simp only [DSArray.get_ofFn]
  · intro n' 
    rw [DSArray.to_below_ofFn_eq_below_ofFn n']
    apply h

noncomputable
def brecOn_recurser {C : Nat → Sort u} (f : (n : Nat) → @Nat.below C n → C n)  :
    (n : Nat) → PProd (C n) (@Nat.below C n) :=
  Nat.rec (motive := fun n => PProd (C n) (Nat.below n))
    ⟨f Nat.zero PUnit.unit, PUnit.unit ⟩
    fun n ih => ⟨f (Nat.succ n) ⟨ih, PUnit.unit⟩, ⟨ih, PUnit.unit ⟩⟩

theorem brecOn_eq_brecOn_recurser
     {C : Nat → Sort u} (f : (n : Nat) → @Nat.below C n → C n) (n : Nat) :
     @Nat.brecOn C n f = (brecOn_recurser f n).1 := rfl

theorem brecOn_recurser_eq {C : Nat → Sort u} (f : (n : Nat) → @Nat.below C n → C n) :
  (n : Nat) → brecOn_recurser f n =
    ⟨f n (brecOn_recurser f n).2,(brecOn_recurser f n).2⟩ := by
  intro n; cases n <;> rfl

theorem recurser_two_eq {C : Nat → Sort u} (f : (n : Nat) → @Nat.below C n → C n) (n : Nat) :
  (brecOn_recurser f n).2 = below_ofFn (fun n => @Nat.brecOn C n f) n := by
  induction n
  · case zero => rfl
  · case succ n IH =>
    unfold brecOn_recurser
    show (⟨brecOn_recurser f n, PUnit.unit⟩ = (_ : PProd _ _))
    rw [brecOn_recurser_eq]
    congr
    simp only [brecOn_eq_brecOn_recurser]
    rw [brecOn_recurser_eq]

theorem brecOn_eq {C : Nat → Sort u} 
    (f : (n : Nat) → @Nat.below C n → C n)
    (n : Nat) : @Nat.brecOn C n f = f n (below_ofFn (fun n => @Nat.brecOn C n f) n) := by
  rw [brecOn_eq_brecOn_recurser, brecOn_recurser_eq, recurser_two_eq]

theorem brecOn_eq_dmemo_below {C : Nat → Sort u}
    (f : (n : Nat) → @Nat.below C n → C n)
    : (fun n => @Nat.brecOn C n f) = dmemo_below f := by
    apply dmemo_below_spec
    intro n
    exact (brecOn_eq f n).symm

def memo {α : Sort u} (f : (n : Nat) → (∀ i, i < n → α) → α) (n : Nat) : α :=
  dmemo f n

theorem memo_spec {α : Sort u}
    (g : Nat → α)
    (f : (n : Nat) → (∀ i, i < n → α) → α)
    (h : ∀ n, f n (fun i _ => g i) = g n) :
    g = memo f :=
  dmemo_spec g f h


theorem fix_eq_memo {α} (f : (n : Nat) → (∀ i, i < n → α) → α) :
    WellFounded.fix (invImage (fun a => sizeOf a) instWellFoundedRelation).2 f = memo f :=
  fix_eq_dmemo f

end NatMemo
