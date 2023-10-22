import MemoNat.DArray

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
    have : n = i := Nat.le_antisymm (Nat.le_of_not_lt h) (Nat.le_of_lt_succ hi)
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