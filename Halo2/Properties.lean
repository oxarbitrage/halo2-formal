import Halo2.Spec
import Mathlib.Tactic.LinearCombination

namespace Halo2

/-! # Properties of the PLONKish constraint system

Key properties:

1. **Gate soundness**: a satisfied gate implies the intended arithmetic
   relation holds on every row.

2. **Permutation soundness**: the identity permutation trivially satisfies
   the grand product check.

3. **Composition**: combining gates preserves satisfaction.
-/

open Pasta

noncomputable section

/-! ## Addition gate soundness -/

/-- If the addition gate is satisfied, then `a + b = c` on every row. -/
theorem addGate_sound {n : ℕ} (a b c : Column n)
    (h : (addGate n).satisfied a b c) :
    ∀ i : Fin n, a i + b i = c i := by
  intro i
  have := h i
  simp only [Gate.eval, addGate] at this
  linear_combination this

/-- If `a + b = c` on every row, then the addition gate is satisfied. -/
theorem addGate_complete {n : ℕ} (a b c : Column n)
    (h : ∀ i, a i + b i = c i) :
    (addGate n).satisfied a b c := by
  intro i
  simp only [Gate.eval, addGate]
  linear_combination h i

/-! ## Multiplication gate soundness -/

/-- If the multiplication gate is satisfied, then `a * b = c` on every row. -/
theorem mulGate_sound {n : ℕ} (a b c : Column n)
    (h : (mulGate n).satisfied a b c) :
    ∀ i : Fin n, a i * b i = c i := by
  intro i
  have := h i
  simp only [Gate.eval, mulGate] at this
  linear_combination this

/-- If `a * b = c` on every row, then the multiplication gate is satisfied. -/
theorem mulGate_complete {n : ℕ} (a b c : Column n)
    (h : ∀ i, a i * b i = c i) :
    (mulGate n).satisfied a b c := by
  intro i
  simp only [Gate.eval, mulGate]
  linear_combination h i

/-! ## Constant gate soundness -/

/-- If the constant gate is satisfied, then `a = val` on every row. -/
theorem constGate_sound {n : ℕ} (val : Pasta.Fp) (a b c : Column n)
    (h : (constGate n val).satisfied a b c) :
    ∀ i : Fin n, a i = val := by
  intro i
  have := h i
  simp only [Gate.eval, constGate] at this
  linear_combination this

/-! ## Boolean gate soundness -/

/-- If the boolean gate is satisfied, then `a ∈ {0, 1}` on every row.

The gate enforces `a² - a = 0`, i.e. `a(a - 1) = 0`. -/
theorem boolGate_sound {n : ℕ} (a : Column n)
    (h : (boolGate n).satisfied a a (fun _ => 0)) :
    ∀ i : Fin n, a i = 0 ∨ a i = 1 := by
  intro i
  have := h i
  simp only [Gate.eval, boolGate] at this
  have hab : a i * (a i - 1) = 0 := by linear_combination this
  rcases mul_eq_zero.mp hab with h | h
  · left; exact h
  · right; linear_combination h

/-! ## Permutation argument -/

/-- The identity permutation trivially satisfies the permutation argument,
    provided no denominator is zero (non-degeneracy condition). -/
theorem perm_id_satisfied {n : ℕ} (a : Column n)
    (β γ : Pasta.Fp)
    (hnd : ∀ i : Fin n, a i + β * (i.val : Pasta.Fp) + γ ≠ 0) :
    permSatisfied a (fun i => i) β γ := by
  unfold permSatisfied
  suffices ∀ k, permProduct a (fun i => i) β γ k = 1 by exact this n
  intro k
  induction k with
  | zero => simp [permProduct]
  | succ k ih =>
    simp only [permProduct]
    split
    · rw [ih]; simp [div_self (hnd ⟨_, ‹_›⟩)]
    · exact ih

/-! ## Gate composition -/

/-- If two gates are independently satisfied, they can be composed.

This models the key PLONKish property: multiple gates can constrain
the same columns, and satisfaction of each gate is independent. -/
theorem gates_compose {n : ℕ} (g₁ g₂ : Gate n) (a b c : Column n)
    (h₁ : g₁.satisfied a b c) (h₂ : g₂.satisfied a b c) :
    ∀ i, g₁.eval a b c i = 0 ∧ g₂.eval a b c i = 0 :=
  fun i => ⟨h₁ i, h₂ i⟩

end

end Halo2
