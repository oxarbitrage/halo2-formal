import Halo2.Spec
import Mathlib.Tactic.Ring

namespace Halo2

/-! # Lookup-based range check

The LookupRangeCheck gadget decomposes a value `v` into `w` words
of base `b` (each word < b), and checks each word against a lookup
table `{0, ..., b-1}`. If the decomposition succeeds, then `v < b^w`.

In Orchard, `b = 1024` (10-bit words) and `w` varies depending on
the range being checked.

See §4.1 of the Halo 2 book.
-/

open Finset

/-! ## Decomposition -/

/-- A base-b decomposition of a value into w words, each < b. -/
structure Decomposition (w : ℕ) (b : ℕ) where
  words : Fin w → ℕ
  word_bound : ∀ i, words i < b

/-- Reconstruct the value from a decomposition: `Σᵢ words(i) · b^i`. -/
def Decomposition.value {w b : ℕ} (d : Decomposition w b) : ℕ :=
  ∑ i : Fin w, d.words i * b ^ i.val

/-- A value has a base-b decomposition with w words. -/
def hasDecomposition (v : ℕ) (w b : ℕ) : Prop :=
  ∃ d : Decomposition w b, d.value = v

/-! ## Soundness -/

private theorem sum_words_lt_pow (b : ℕ) (_hb : 0 < b) :
    ∀ (w : ℕ) (words : Fin w → ℕ), (∀ i, words i < b) →
    ∑ i : Fin w, words i * b ^ i.val < b ^ w := by
  intro w
  induction w with
  | zero => simp
  | succ n ih =>
    intro words hw
    rw [Fin.sum_univ_castSucc, pow_succ, mul_comm]
    simp only [Fin.val_castSucc, Fin.val_last]
    have ih' : ∑ i : Fin n, words (Fin.castSucc i) * b ^ i.val < b ^ n :=
      ih (fun i => words (Fin.castSucc i)) (fun i => hw (Fin.castSucc i))
    have h2 : b ^ n + words (Fin.last n) * b ^ n ≤ b * b ^ n := by
      have h3 := Nat.mul_le_mul_right (b ^ n) (hw (Fin.last n) : words (Fin.last n) + 1 ≤ b)
      rw [Nat.succ_mul] at h3; linarith
    linarith

/-- **Range check soundness**: if `v` has a base-b decomposition with `w`
words (each < b), then `v < b^w`. -/
theorem range_check_soundness {w b : ℕ} (hb : 0 < b) (d : Decomposition w b) :
    d.value < b ^ w :=
  sum_words_lt_pow b hb w d.words d.word_bound

/-! ## Completeness -/

/-- **Range check completeness**: any `v < b^w` has a base-b decomposition
with `w` words. Uses Euclidean division at each step. -/
theorem range_check_completeness (v w b : ℕ) (hb : 1 < b) (hv : v < b ^ w) :
    hasDecomposition v w b := by
  induction w generalizing v with
  | zero =>
    simp at hv; subst hv
    exact ⟨⟨Fin.elim0, fun i => i.elim0⟩, by simp [Decomposition.value]⟩
  | succ n ih =>
    have hb' : 0 < b := by omega
    have hdiv : v / b < b ^ n := by
      rw [pow_succ, mul_comm] at hv
      exact Nat.div_lt_of_lt_mul hv
    obtain ⟨d, hd⟩ := ih (v / b) hdiv
    refine ⟨⟨Fin.cons (v % b) d.words, fun i => ?_⟩, ?_⟩
    · exact Fin.cases (Nat.mod_lt v hb') (fun j => d.word_bound j) i
    · unfold Decomposition.value
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.val_zero, pow_zero, mul_one, Fin.cons_succ, Fin.val_succ]
      have hfactor : ∑ i : Fin n, d.words i * b ^ (i.val + 1) =
             b * ∑ i : Fin n, d.words i * b ^ i.val := by
        rw [Finset.mul_sum]; congr 1; ext i; rw [pow_succ]; ring
      rw [hfactor, ← Decomposition.value, hd, Nat.mod_add_div]

end Halo2
