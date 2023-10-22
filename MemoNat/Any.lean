set_option autoImplicit false

universe u

inductive Any : Type u
| mk {α : Sort u} : α → Any

protected abbrev Any.Sort : Any → Sort _
| @mk α _ => α

protected abbrev Any.val : (a : Any) → a.Sort
| mk x => x

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