set_option autoImplicit false

universe u

inductive Any : Type u
| mk {α : Sort u} : α → Any

protected abbrev Any.Sort : Any → Sort _
| @mk α _ => α

protected abbrev Any.val : (a : Any) → a.Sort
| mk x => x

--- Homogeneous version of `Any.mk.inj`
theorem Any.mk_inj {α} (x y : α) (h : Any.mk x = Any.mk y) : x = y :=
  eq_of_heq (@Any.mk.inj α x α y h).2

@[simp]
theorem Any.mk_val (a : Any) : Any.mk (Any.val a) = a :=
  rfl

@[simp]
theorem Any.mk_eq_rec.{u₁,u₂} {β : Sort u₁} {x y : β} {P : β → Sort u₂} (h : x = y) (a : P x):
    Any.mk (h ▸ a) = Any.mk a := by cases h; rfl

@[simp]
theorem Any.mk_eq_rec'  {α β : Sort u} (h : α = β) (a : α) :
    Any.mk (h ▸ a) = Any.mk a := @Any.mk_eq_rec _ α β (fun x => x) h a

theorem Any.eq_rec_val {α : Sort u} {a : Any} (h : a.Sort = α) (x : α) (eq : a = Any.mk x) :
    h ▸ a.val = x := by
    cases eq; rfl

@[simp]
theorem Any.eq_rec_val_iff {α : Sort u} {a : Any} (hS : a.Sort = α) (x : α)  :
    (hS ▸ a.val = x) ↔ (a = Any.mk x) := by
    constructor
    · intro h
      cases a with | @mk β y =>
      cases hS
      simp at *
      apply h
    · intro h
      cases h
      rfl

theorem Any.rw {a₁ a₂ : Any}  (h : a₁ = a₂) {α : Sort u} {h₁ : a₁.Sort = α} :
    h₁ ▸ a₁.val = (h ▸ h₁) ▸ a₂.val := by induction h; rfl