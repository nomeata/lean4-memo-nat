import Std.Data.Array.Lemmas

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