-- This intentionally only uses std, not mathlib
import Std.Data.Array.Lemmas
import Std.Data.Fin.Basic
import Std.Tactic.Congr

set_option autoImplicit false

universe u

inductive Any : Type u
| mk {α : Sort u} : α → Any

protected abbrev Any.Sort : Any → Sort _
| @mk α _ => α

protected abbrev Any.val : (a : Any) → a.Sort
| mk x => x

theorem Any.congr {a₁ a₂ : Any}  (h : a₁ = a₂) {α : Sort u} {h₁ : a₁.Sort = α}
    {h₂ : a₂.Sort = α} :
    h₁ ▸ a₁.val = h₂ ▸ a₂.val := by induction h; rfl

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

end DArray
