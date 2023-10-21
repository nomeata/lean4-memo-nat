import MemoNat
import MemoNat.Attr

set_option profiler true

/-
A small demo. Here a slow implemntation of a recursive function.
(The if inside is just to please the recursion checker, the condition is always true).
-/
def slow (n : Nat) : Nat :=
  1 + List.foldl (fun a i => a + (if _ : i<n then slow i else 0)) 0 (List.range n)

-- Kinda slow:
-- #eval (slow 20)

/-
Define the fast version using the fixed-point version
-/
def fast (n : Nat) : Nat :=
  NatMemo.memo (fun n r =>
    1 + List.foldl (fun a i => a + (if h : i<n then r i h else 0)) 0 (List.range n)
  ) n

/-
And prove them to be qual. The csimp attribute makes Lean use the fast version
when evaluating.
-/

@[csimp]
theorem slow_is_fast: slow = fast := by
  apply NatMemo.memo_spec
  intro n
  rw [slow]
  
-- Now faster:
-- #eval (slow 20)

/-
Also works very conveniently using an attribute.
-/
@[memo]
def slow2 (n : Nat) : Nat :=
  1 + List.foldl (fun a i => a + (if _ : i<n then slow2 i else 0)) 0 (List.range n)

-- #eval (slow2 20)

/-
One may have to use `termination_by` to make Lean elaborate to use `WellFounded.fix`.
(else it uses `Nat.brecOn`, and that is not yet suported.)
-/
@[memo]
def fib : Nat → Nat
  | 0 | 1 => 1
  | n + 2 => fib n + fib (n + 1)
termination_by fib n => n

-- #eval fib 100