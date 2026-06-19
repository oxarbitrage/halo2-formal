import Pasta.Fields
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace Halo2

/-! # ECC Gadget Circuit Constraint Soundness

Formalizes the **circuit-level polynomial constraints** for elliptic curve
operations in the Halo 2 ECC gadget and proves they are **sound**, **complete**,
and **unique**: any assignment satisfying the constraints computes the correct
EC operation, correct computations satisfy the constraints, and no two different
outputs can satisfy the same constraints for the same inputs.

This addresses the vulnerability class from the Orchard counterfeiting bug
(GHSA-jfw5-j458-pfv6, discovered 2026-05-29): an under-constrained EC scalar
multiplication gadget allowed provers to supply arbitrary false intermediate
values. The polynomial gate constraints did not fully determine the outputs,
enabling unlimited undetectable counterfeiting for ~4 years.

Circuit constraints must be polynomial (no division), so the standard EC
addition formula involving λ = (y₁ - y₂)/(x₁ - x₂) is rewritten as
division-free polynomial gates. We prove these gates uniquely determine
the output coordinates under non-exceptional conditions.
-/

open Pasta

noncomputable section

/-! ## Characteristic lemma -/

private theorem two_ne_zero_fp : (2 : Fp) ≠ 0 := by native_decide

/-! ## Incomplete addition: division-free constraints

For P = (x_p, y_p) and Q = (x_q, y_q) with x_p ≠ x_q, the slope is
λ = (y_p - y_q)/(x_p - x_q). The division-free circuit constraints:

  C1: (x_r + x_p + x_q) · (x_p - x_q)² = (y_p - y_q)²
  C2: (y_r + y_p) · (x_p - x_q) = (y_p - y_q) · (x_p - x_r)
-/

def addC1 (x_p y_p x_q y_q x_r : Fp) : Prop :=
  (x_r + x_p + x_q) * (x_p - x_q) ^ 2 = (y_p - y_q) ^ 2

def addC2 (x_p y_p x_q y_q x_r y_r : Fp) : Prop :=
  (y_r + y_p) * (x_p - x_q) = (y_p - y_q) * (x_p - x_r)

/-! ### Addition soundness -/

theorem addC1_sound (x_p y_p x_q y_q x_r : Fp)
    (hne : x_p ≠ x_q) (hc1 : addC1 x_p y_p x_q y_q x_r) :
    x_r = ((y_p - y_q) / (x_p - x_q)) ^ 2 - x_p - x_q := by
  unfold addC1 at hc1
  have hdiff : x_p - x_q ≠ 0 := sub_ne_zero.mpr hne
  have hsq : (x_p - x_q) ^ 2 ≠ 0 := pow_ne_zero 2 hdiff
  have h1 : x_r + x_p + x_q = (y_p - y_q) ^ 2 / (x_p - x_q) ^ 2 := by
    rw [eq_div_iff hsq]; exact hc1
  rw [← div_pow] at h1
  have eq1 : x_r = x_r + x_p + x_q - x_p - x_q := by ring
  rw [h1] at eq1; exact eq1

theorem addC2_sound (x_p y_p x_q y_q x_r y_r : Fp)
    (hne : x_p ≠ x_q) (hc2 : addC2 x_p y_p x_q y_q x_r y_r) :
    y_r = (y_p - y_q) / (x_p - x_q) * (x_p - x_r) - y_p := by
  unfold addC2 at hc2
  have hdiff : x_p - x_q ≠ 0 := sub_ne_zero.mpr hne
  have h1 : y_r + y_p = (y_p - y_q) * (x_p - x_r) / (x_p - x_q) := by
    rw [eq_div_iff hdiff]; exact hc2
  rw [mul_div_right_comm] at h1
  have eq1 : y_r = y_r + y_p - y_p := by ring
  rw [h1] at eq1; exact eq1

/-! ### Addition completeness -/

theorem addC1_complete (x_p y_p x_q y_q : Fp) (hne : x_p ≠ x_q) :
    addC1 x_p y_p x_q y_q
      (((y_p - y_q) / (x_p - x_q)) ^ 2 - x_p - x_q) := by
  unfold addC1
  have : x_p - x_q ≠ 0 := sub_ne_zero.mpr hne
  field_simp; ring

theorem addC2_complete (x_p y_p x_q y_q x_r : Fp) (hne : x_p ≠ x_q) :
    addC2 x_p y_p x_q y_q x_r
      ((y_p - y_q) / (x_p - x_q) * (x_p - x_r) - y_p) := by
  unfold addC2
  have : x_p - x_q ≠ 0 := sub_ne_zero.mpr hne
  field_simp; ring

/-! ### Addition uniqueness -/

theorem add_unique (x_p y_p x_q y_q x_r y_r x_r' y_r' : Fp)
    (hne : x_p ≠ x_q)
    (hc1 : addC1 x_p y_p x_q y_q x_r) (hc2 : addC2 x_p y_p x_q y_q x_r y_r)
    (hc1' : addC1 x_p y_p x_q y_q x_r') (hc2' : addC2 x_p y_p x_q y_q x_r' y_r') :
    x_r = x_r' ∧ y_r = y_r' := by
  unfold addC1 at hc1 hc1'
  unfold addC2 at hc2 hc2'
  have hdiff : x_p - x_q ≠ 0 := sub_ne_zero.mpr hne
  have hsq : (x_p - x_q) ^ 2 ≠ 0 := pow_ne_zero 2 hdiff
  constructor
  · have h := mul_right_cancel₀ hsq (hc1.trans hc1'.symm)
    linear_combination h
  · have hx : x_r = x_r' := by
      have h := mul_right_cancel₀ hsq (hc1.trans hc1'.symm)
      linear_combination h
    rw [hx] at hc2
    have h := mul_right_cancel₀ hdiff (hc2.trans hc2'.symm)
    linear_combination h

/-! ### Under-constrained vulnerability class -/

/-- C1 alone does not constrain the y-coordinate. Two different y-values
coexist with the same satisfied C1, because C1 does not mention y_r.
This is the vulnerability class from GHSA-jfw5-j458-pfv6. -/
theorem add_c1_alone_admits_distinct_y :
    ∃ (x_p y_p x_q y_q x_r y₁ y₂ : Fp),
    x_p ≠ x_q ∧ y₁ ≠ y₂ ∧ addC1 x_p y_p x_q y_q x_r := by
  refine ⟨0, 1, 1, 0, 0, 0, 1, zero_ne_one, zero_ne_one, ?_⟩
  unfold addC1; ring

/-! ## Point doubling: division-free constraints

For P = (x_p, y_p) with y_p ≠ 0 on Pallas (y² = x³ + 5, a₄ = 0),
the doubling slope is λ = 3x_p²/(2y_p). Division-free constraints:

  D1: (x_r + 2·x_p) · (2·y_p)² = (3·x_p²)²
  D2: (y_r + y_p) · (2·y_p) = 3·x_p² · (x_p - x_r)
-/

def dblC1 (x_p y_p x_r : Fp) : Prop :=
  (x_r + 2 * x_p) * (2 * y_p) ^ 2 = (3 * x_p ^ 2) ^ 2

def dblC2 (x_p y_p x_r y_r : Fp) : Prop :=
  (y_r + y_p) * (2 * y_p) = 3 * x_p ^ 2 * (x_p - x_r)

/-! ### Doubling soundness -/

theorem dblC1_sound (x_p y_p x_r : Fp) (hy : y_p ≠ 0)
    (hd1 : dblC1 x_p y_p x_r) :
    x_r = (3 * x_p ^ 2 / (2 * y_p)) ^ 2 - 2 * x_p := by
  unfold dblC1 at hd1
  have h2y : 2 * y_p ≠ 0 := mul_ne_zero two_ne_zero_fp hy
  have hsq : (2 * y_p) ^ 2 ≠ 0 := pow_ne_zero 2 h2y
  have h1 : x_r + 2 * x_p = (3 * x_p ^ 2) ^ 2 / (2 * y_p) ^ 2 := by
    rw [eq_div_iff hsq]; exact hd1
  rw [← div_pow] at h1
  have eq1 : x_r = x_r + 2 * x_p - 2 * x_p := by ring
  rw [h1] at eq1; exact eq1

theorem dblC2_sound (x_p y_p x_r y_r : Fp) (hy : y_p ≠ 0)
    (hd2 : dblC2 x_p y_p x_r y_r) :
    y_r = 3 * x_p ^ 2 / (2 * y_p) * (x_p - x_r) - y_p := by
  unfold dblC2 at hd2
  have h2y : 2 * y_p ≠ 0 := mul_ne_zero two_ne_zero_fp hy
  have h1 : y_r + y_p = 3 * x_p ^ 2 * (x_p - x_r) / (2 * y_p) := by
    rw [eq_div_iff h2y]; exact hd2
  rw [mul_div_right_comm] at h1
  have eq1 : y_r = y_r + y_p - y_p := by ring
  rw [h1] at eq1; exact eq1

/-! ### Doubling completeness -/

theorem dblC1_complete (x_p y_p : Fp) (hy : y_p ≠ 0) :
    dblC1 x_p y_p ((3 * x_p ^ 2 / (2 * y_p)) ^ 2 - 2 * x_p) := by
  unfold dblC1
  have : (2 : Fp) ≠ 0 := two_ne_zero_fp
  have : y_p ≠ 0 := hy
  field_simp; ring

theorem dblC2_complete (x_p y_p x_r : Fp) (hy : y_p ≠ 0) :
    dblC2 x_p y_p x_r (3 * x_p ^ 2 / (2 * y_p) * (x_p - x_r) - y_p) := by
  unfold dblC2
  have : (2 : Fp) ≠ 0 := two_ne_zero_fp
  have : y_p ≠ 0 := hy
  field_simp; ring

/-! ### Doubling uniqueness -/

theorem dbl_unique (x_p y_p x_r y_r x_r' y_r' : Fp) (hy : y_p ≠ 0)
    (hd1 : dblC1 x_p y_p x_r) (hd2 : dblC2 x_p y_p x_r y_r)
    (hd1' : dblC1 x_p y_p x_r') (hd2' : dblC2 x_p y_p x_r' y_r') :
    x_r = x_r' ∧ y_r = y_r' := by
  unfold dblC1 at hd1 hd1'
  unfold dblC2 at hd2 hd2'
  have h2y : 2 * y_p ≠ 0 := mul_ne_zero two_ne_zero_fp hy
  have hsq : (2 * y_p) ^ 2 ≠ 0 := pow_ne_zero 2 h2y
  constructor
  · have h := mul_right_cancel₀ hsq (hd1.trans hd1'.symm)
    linear_combination h
  · have hx : x_r = x_r' := by
      have h := mul_right_cancel₀ hsq (hd1.trans hd1'.symm)
      linear_combination h
    rw [hx] at hd2
    have h := mul_right_cancel₀ h2y (hd2.trans hd2'.symm)
    linear_combination h

/-! ## Constrained double-and-add step

A single step of variable-base scalar multiplication processes one
scalar bit: conditionally add the base point, then double.
-/

def stepConstrained (bit x_P y_P x_A y_A x_T y_T x_A' y_A' : Fp) : Prop :=
  (bit = 0 ∨ bit = 1) ∧
  (bit = 1 → addC1 x_A y_A x_P y_P x_T ∧ addC2 x_A y_A x_P y_P x_T y_T) ∧
  (bit = 0 → x_T = x_A ∧ y_T = y_A) ∧
  dblC1 x_T y_T x_A' ∧ dblC2 x_T y_T x_A' y_A'

/-- A fully constrained step has a unique output: given the same inputs,
no two different outputs can satisfy all constraints. -/
theorem step_unique
    (bit x_P y_P x_A y_A : Fp)
    (x_T₁ y_T₁ x_A₁' y_A₁' x_T₂ y_T₂ x_A₂' y_A₂' : Fp)
    (hs₁ : stepConstrained bit x_P y_P x_A y_A x_T₁ y_T₁ x_A₁' y_A₁')
    (hs₂ : stepConstrained bit x_P y_P x_A y_A x_T₂ y_T₂ x_A₂' y_A₂')
    (hadd : bit = 1 → x_A ≠ x_P)
    (_hy₁ : y_T₁ ≠ 0) (hy₂ : y_T₂ ≠ 0) :
    x_A₁' = x_A₂' ∧ y_A₁' = y_A₂' := by
  obtain ⟨hb₁, hadd₁, hpass₁, hdbl₁_x, hdbl₁_y⟩ := hs₁
  obtain ⟨_, hadd₂, hpass₂, hdbl₂_x, hdbl₂_y⟩ := hs₂
  have hT : x_T₁ = x_T₂ ∧ y_T₁ = y_T₂ := by
    rcases hb₁ with rfl | rfl
    · obtain ⟨hx₁, hy_eq₁⟩ := hpass₁ rfl
      obtain ⟨hx₂, hy_eq₂⟩ := hpass₂ rfl
      exact ⟨hx₁.trans hx₂.symm, hy_eq₁.trans hy_eq₂.symm⟩
    · exact add_unique x_A y_A x_P y_P x_T₁ y_T₁ x_T₂ y_T₂
        (hadd rfl) (hadd₁ rfl).1 (hadd₁ rfl).2 (hadd₂ rfl).1 (hadd₂ rfl).2
  obtain ⟨hxT, hyT⟩ := hT
  rw [hxT, hyT] at hdbl₁_x hdbl₁_y
  exact dbl_unique x_T₂ y_T₂ x_A₁' y_A₁' x_A₂' y_A₂' hy₂
    hdbl₁_x hdbl₁_y hdbl₂_x hdbl₂_y

end

end Halo2
