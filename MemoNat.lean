-- This intentionally only uses std, not mathlib
import Std.Data.Array.Lemmas
import Std.Data.Fin.Basic
import Std.Data.Fin.Lemmas
import Std.Tactic.Congr
import MemoNat.DArray

set_option autoImplicit false

universe u

/-- Arrays of a given size, H'T Kyle Miller -/
def SArray (α : Type _) (n : Nat) := {a : Array α // a.size = n}

namespace SArray

protected def mkEmpty {α} (cap : Nat) : SArray α 0 := ⟨Array.mkEmpty cap, rfl⟩

protected def empty {α} : SArray α 0 := SArray.mkEmpty 0

protected def push {α n} (a : SArray α n) (x : α) : SArray α (n + 1) :=
  ⟨a.1.push x, by rw [Array.size_push, a.2]⟩

protected def get {α n} (a : SArray α n) (i : Fin n) : α :=
  a.1.get ⟨i, a.2.symm ▸ i.2⟩

protected theorem get_push {α n} (a : SArray α n) (x : α) (i : Nat) (hi : i < n + 1) :
    (a.push x).get (⟨i, hi⟩) = if h : i < n then a.get ⟨i, h⟩ else x := by
  simp only [SArray.get, SArray.push, Array.get_eq_getElem, Array.get_push, a.2]

protected def ofFn {α} (n : Nat) (f : Fin n → α) : SArray α n :=
  ⟨.ofFn f, Array.size_ofFn f⟩

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

protected def ofFn {C} (n : Nat) (f : (i : Fin n) → C i) : DSArray n C :=
  ⟨.ofFn n f, DArray.size_ofFn n f⟩

@[simp]
protected theorem get_ofFn  {C : Nat → Sort _} (n : Nat) (f : (i : Fin n) → C i)
    (i : Fin n) : (DSArray.ofFn n f).get i = f i := DArray.get_ofFn _ _ _

theorem Array.get_pop {α} (a : Array α) (i : Fin a.pop.size) :
  a.pop.get i = a.get (i.castLE (a.size_pop ▸ Nat.sub_le _ _ )) := by
    cases i with | _ i hi =>
    cases a with | _ xs =>
    unfold Array.pop Array.size Array.get at *
    dsimp
    dsimp at hi
    induction i generalizing xs
    case zero =>
      cases xs
      case nil => rfl
      case cons x xs =>
        cases xs
        · simp at hi
        · simp
    case succ i IH =>
      cases xs
      case nil => rfl
      case cons x xs =>
        cases xs
        case nil =>
          simp at hi
          exfalso
          apply Nat.not_lt_zero _ hi
        case cons y ys =>
          apply IH

def _root_.DArray.pop {C} (a : DArray C) : DArray C :=
  ⟨a.arr.pop, by
    intro i
    cases a with | _ a ha =>
    rw [Array.get_pop]
    apply ha ⟩

theorem _root_.DArray.size_pop {C} (a : DArray C) :
  a.pop.size = a.size - 1 := Array.size_pop _

@[simp]
theorem _root_.DArray.get_pop {C} (a : DArray C) (i : Fin a.pop.size):
  a.pop.get i = a.get (i.castLE (a.size_pop ▸ Nat.sub_le _ _)) := by
    unfold DArray.pop DArray.get
    apply Any.eq_rec_val
    simp only [Fin.coe_castLE, Any.mk_eq_rec', Array.get_pop]

def pop {C n} (a : DSArray (n + 1) C) : DSArray n C :=
  ⟨a.val.pop, by rw [DArray.size_pop, a.2]; rfl⟩

@[simp]
theorem _root_.DSArray.get_pop {C n} (a : DSArray (n + 1) C) (i : Fin n):
    a.pop.get i = a.get i.castSucc := DArray.get_pop _ _

def of_below {C} : {n : Nat} → @Nat.below C n → DSArray n C
  | 0, .unit => .empty 0
  | n + 1, ⟨⟨x,y⟩,.unit⟩ => (@of_below C n y).push x

def below_ofFn {C} : (n : Nat) → (f : (i : Fin n) → C i) → @Nat.below C n
  | 0, _ => .unit
  | n+1, f => ⟨⟨f (Fin.last n), below_ofFn n (fun i => f i.castSucc)⟩,.unit⟩

def to_below {C n} (a : DSArray n C) : @Nat.below C n :=
  below_ofFn n a.get

theorem to_below_succ {C n} (a : DSArray (n + 1) C) :
  a.to_below = ⟨⟨a.get (Fin.last n), a.pop.to_below⟩, .unit⟩ := by
  cases n <;> simp only [to_below, ← Fin.succ_last, below_ofFn, get_pop]

@[ext]
theorem ext {C n} (a b : DSArray n C)
    (h₂ : (i : Nat) → (hi : i < n) → a.get ⟨i, hi⟩ = b.get ⟨i, hi⟩)
    : a = b := by
  cases a with | _ a ha =>
  cases b with | _ b hb =>
  suffices a = b by simp [this]
  apply DArray.ext _ _ (ha.trans hb.symm)
  intro i hi₁ _hi₂ 
  exact h₂ i (ha ▸ hi₁)

@[simp]
theorem pop_ofFn {C : Nat → Sort u} (n : Nat) (g : (i : Fin (n+1)) → C i) :
    DSArray.pop (DSArray.ofFn (Nat.succ n) g) = DSArray.ofFn n (fun i => g i.castSucc) := by
  ext i hi
  simp

end DSArray

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
