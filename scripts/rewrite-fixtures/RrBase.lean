def rrT : Nat → Type
  | 0 => Nat → Nat
  | n+1 => rrT n
def rrFn : Type := Nat → Nat
theorem rrT_eq : ∀ n, rrT n = rrFn
  | 0 => rfl
  | n+1 => rrT_eq n
theorem rrT_pi : ∀ n, rrT n = (Nat → Nat)
  | 0 => rfl
  | n+1 => rrT_pi n
theorem rrT_refl : ∀ n, rrT n = rrT n := fun _ => rfl
theorem rrT_succ : ∀ n, rrT (n+1) = rrT n := fun _ => rfl
def rr_use (n : Nat) (g : rrT n) : Nat := (cast (rrT_eq n) g) 0
