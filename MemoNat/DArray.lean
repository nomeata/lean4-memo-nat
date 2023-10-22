-- This intentionally only uses std, not mathlib
import Std.Data.Array.Lemmas
import Std.Data.Fin.Basic
import Std.Data.Fin.Lemmas
import Std.Tactic.Congr

set_option autoImplicit false

universe u

inductive Any : Type u
| mk {α : Sort u} : α → Any

protected abbrev Any.Sort : Any → Sort _
| @mk α _ => α

protected abbrev Any.val : (a : Any) → a.Sort
| mk x => x

-- theorem Any.congr {a₁ a₂ : Any} (h : a₁ = a₂) {α : Sort u} {h₁ : a₁.Sort = α}
--     {h₂ : a₂.Sort = α} :
--     h₁ ▸ a₁.val = h₂ ▸ a₂.val := by induction h; rfl

@[simp]
theorem Any.eq_rec_val_iff {a₁ a₂ : Any} {α : Sort u} {h₁ : a₁.Sort = α}
    {h₂ : a₂.Sort = α} :
    (h₁ ▸ a₁.val = h₂ ▸ a₂.val) ↔ (a₁ = a₂) := by
    constructor
    · intro h
      cases a₁ with | @mk α₁ x =>
      cases a₂ with | @mk α₂ y =>
      cases h₁
      cases h₂
      exact congrArg Any.mk h
    · intro h; induction h; rfl

theorem Any.rw {a₁ a₂ : Any}  (h : a₁ = a₂) {α : Sort u} {h₁ : a₁.Sort = α} :
    h₁ ▸ a₁.val = (h ▸ h₁) ▸ a₂.val := by induction h; rfl

theorem Any.eq_rec_val {α : Sort u} {a : Any} (h : a.Sort = α) (x : α) (eq : a = Any.mk x) :
    h ▸ a.val = x := by cases eq; rfl

@[simp]
theorem Any.mk_eq_rec.{u₁,u₂} {β : Sort u₁} {x y : β} {P : β → Sort u₂} (h : x = y) (a : P x):
    Any.mk (h ▸ a) = Any.mk a := by cases h; rfl

@[simp]
theorem Any.mk_eq_rec'  {α β : Sort u} (h : α = β) (a : α) :
    Any.mk (h ▸ a) = Any.mk a := @Any.mk_eq_rec _ α β (fun x => x) h a

--  (_ : Any.Sort (Array.get (Array.push { arr := a, types := types }.arr (Any.mk x)) i) = C i.val) ▸
    -- Any.val (Array.push a (Any.mk x))

structure DArray (C : Nat → Sort u) : Type u:=
  arr : Array Any.{u}
  types : ∀ (i : Fin arr.size), (arr.get i).Sort = C i

namespace DArray

def mkEmpty {C} (cap : Nat) : DArray C :=
  ⟨ Array.mkEmpty cap, λ i => Fin.elim0 i⟩

def size {C} (a : DArray C) := a.arr.size

def push {C} (a : DArray C) (x : C a.size) : DArray C :=
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

theorem size_push {C} (a : DArray C) (x : C a.size) : (a.push x).size = a.size + 1 :=
  Array.size_push _ _

def get {C : Nat → Sort u} (a : DArray C) (i : Fin a.size) : C i :=
  let x : Any := Array.get a.arr i
  a.types i ▸ x.val

theorem get_push {C} (a : DArray C) (x : C a.size) (i : Fin (a.push x).size) :
    (a.push x).get i =
      if h : i < a.size
      then a.get ⟨i, h⟩
      else
        have : size a = i := Nat.le_antisymm
          (Nat.le_of_not_lt h)
          (Nat.le_of_lt_succ (by simpa [a.size_push x] using i.isLt))
        (this ▸ x : C i) := by
  apply (Any.rw (Array.get_push a.arr (Any.mk x) i.val i.isLt)).trans
  apply Any.eq_rec_val
  unfold DArray.size
  split
  case inl _ =>
    simp only [get, Array.get, Any.mk_eq_rec']
    rfl
  case inr hi2 =>
    simp only [get, Array.get, Any.mk_eq_rec', DArray.size, Any.mk_eq_rec ]
 
protected def ofFn {C} (n : Nat) (f : (i : Fin n) → C i) : DArray C :=
  ⟨ .ofFn fun i => Any.mk (f i),
    by intro i; rw [Array.get_eq_getElem, Array.getElem_ofFn] ⟩

protected theorem size_ofFn  {C : Nat → Sort _} (n : Nat) (f : (i : Fin n) → C i) :
  (DArray.ofFn n f).size = n := by
  dsimp [DArray.size, DArray.ofFn]
  exact Array.size_ofFn _

protected theorem get_ofFn {C : Nat → Sort _} (n : Nat) (f : (i : Fin n) → C i)
    (i : Fin (size (DArray.ofFn n f))) : (DArray.ofFn n f).get i =
    f (i.cast (DArray.size_ofFn n f)) := by
  dsimp [DArray.get, DArray.size, DArray.ofFn]
  apply Any.eq_rec_val
  simp only [Array.getElem_ofFn, Any.mk.injEq, heq_eq_eq, true_and]
  rfl

@[ext]
theorem ext {C} (a b : DArray C)
    (h₁ : a.size = b.size)
    (h₂ : (i : Nat) → (hi₁ : i < a.size) → (hi₂ : i < b.size) → a.get ⟨i, hi₁⟩ = b.get ⟨i, hi₂⟩)
    : a = b := by
  cases a with | _ a ha =>
  cases b with | _ b hb =>
  simp only [mk.injEq]
  apply Array.ext
  · exact h₁
  · clear h₁
    intro i hi₁ hi₂
    specialize h₂ i hi₁ hi₂
    unfold DArray.get at h₂
    dsimp at h₂
    rw [Any.eq_rec_val_iff] at h₂
    assumption

theorem _root_.List.length_dropLast {α} (xs : List α) :
    xs.dropLast.length = xs.length - 1 := by
  match xs with
  | [] => rfl
  | x::xs => simp [Nat.succ_sub_succ_eq_sub]

theorem _root_.List.get_dropLast {α} (xs : List α) (i : Fin xs.dropLast.length) :
  xs.dropLast.get i = xs.get (i.castLE (xs.length_dropLast ▸ Nat.sub_le _ _ )) := by
  cases i with | _ i hi =>
  induction i generalizing xs
  case zero =>
    cases xs
    case nil => rfl
    case cons x xs =>
      cases xs
      case nil => simp at hi
      case cons => rfl
  case succ i IH =>
    cases xs
    case nil => rfl
    case cons x xs =>
      cases xs
      case nil => apply False.elim (Nat.not_lt_zero _ hi)
      case cons y ys => apply IH

theorem _root_.Array.get_pop {α} (a : Array α) (i : Fin a.pop.size) :
    a.pop.get i = a.get (i.castLE (a.size_pop ▸ Nat.sub_le _ _ )) :=
  List.get_dropLast _ _

def pop {C} (a : DArray C) : DArray C :=
  ⟨a.arr.pop, by
    intro i
    cases a with | _ a ha =>
    rw [Array.get_pop]
    apply ha ⟩

theorem size_pop {C} (a : DArray C) :
  a.pop.size = a.size - 1 := Array.size_pop _

@[simp]
theorem get_pop {C} (a : DArray C) (i : Fin a.pop.size):
  a.pop.get i = a.get (i.castLE (a.size_pop ▸ Nat.sub_le _ _)) := by
    unfold DArray.pop DArray.get
    apply Any.eq_rec_val
    simp only [Fin.coe_castLE, Any.mk_eq_rec', Array.get_pop]


end DArray
