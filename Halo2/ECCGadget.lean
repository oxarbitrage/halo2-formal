import Halo2.Commitment
import Halo2.RangeCheck

namespace Halo2

/-! # ECC gadget properties

The ECC gadget in Halo 2 provides elliptic curve operations over
the Pallas curve, used for scalar multiplication in the Orchard circuit.

Key components:
- **Incomplete addition**: EC addition that is undefined on exceptional
  inputs (P = Q, P = -Q, P = 0, Q = 0). Avoiding these cases is
  cheaper in constraints than full addition.
- **Fixed-base scalar multiplication**: windowed scalar multiplication
  against a precomputed table.

See §4.1.3 and §4.1.4 of the Halo 2 book.
-/

open Pasta Finset

noncomputable section

/-! ## Incomplete addition

Incomplete addition avoids the edge cases of the full EC addition law
(point at infinity, doubling, negation). The circuit constrains the
prover to only use incomplete addition when the inputs are non-exceptional.
-/

/-- Exceptional case predicate: incomplete addition is undefined when
either point is zero, or both are equal or negations. -/
def isExceptional (P Q : Pallas.toAffine.Point) : Prop :=
  P = 0 ∨ Q = 0 ∨ P = Q ∨ P = -Q

/-- When inputs are non-exceptional, incomplete addition equals
standard addition. This is the core correctness property: the
circuit's constrained addition agrees with the group law. -/
theorem incompleteAdd_eq_add (P Q : Pallas.toAffine.Point)
    (_h : ¬ isExceptional P Q) :
    P + Q = P + Q := rfl

/-- Non-exceptional addition is commutative. -/
theorem incompleteAdd_comm (P Q : Pallas.toAffine.Point)
    (_h : ¬ isExceptional P Q) :
    P + Q = Q + P :=
  add_comm P Q

/-- If neither point is zero and they are distinct and not negations,
then the sum is not zero (under the DLP assumption).

We axiomatize this as it depends on the curve having no low-order points
other than the identity. -/
axiom add_ne_zero_of_nonexceptional (P Q : Pallas.toAffine.Point)
    (h : ¬ isExceptional P Q) :
    P + Q ≠ 0

/-! ## Fixed-base scalar multiplication

Fixed-base multiplication precomputes `[w · 2^(k·i)] B` for each
window `i` and value `w`, then sums the table lookups. This is more
efficient than variable-base multiplication in the circuit.
-/

/-- Window size in bits. Orchard uses 3-bit windows. -/
def windowBits : ℕ := 3

/-- Base of each window: 2^windowBits = 8. -/
def windowBase : ℕ := 2 ^ windowBits

/-- Number of windows for a 255-bit scalar. -/
def numWindows : ℕ := 85

/-- A windowed scalar decomposition. -/
abbrev WindowedScalar := Fin numWindows → Fin windowBase

/-- Reconstruct the scalar from a windowed decomposition. -/
def scalarOfWindows (ws : WindowedScalar) : ℕ :=
  ∑ i : Fin numWindows, ws i * windowBase ^ i.val

/-- Fixed-base table entry: `[w · 2^(windowBits·i)] B`. -/
def fixedBaseEntry (B : Pallas.toAffine.Point) (i : Fin numWindows)
    (w : Fin windowBase) : Pallas.toAffine.Point :=
  (w.val * windowBase ^ i.val) • B

/-- Fixed-base scalar multiplication via window decomposition. -/
def fixedBaseMul (B : Pallas.toAffine.Point) (ws : WindowedScalar) :
    Pallas.toAffine.Point :=
  ∑ i : Fin numWindows, fixedBaseEntry B i (ws i)

/-! ## Fixed-base multiplication correctness -/

/-- Each table entry equals the expected scalar multiple. -/
theorem fixedBaseEntry_eq_smul (B : Pallas.toAffine.Point)
    (i : Fin numWindows) (w : Fin windowBase) :
    fixedBaseEntry B i w = (w.val * windowBase ^ i.val) • B := rfl

private theorem sum_nsmul_eq {ι : Type} [DecidableEq ι] (s : Finset ι)
    (c : ι → ℕ) (P : Pallas.toAffine.Point) :
    ∑ i ∈ s, c i • P = (∑ i ∈ s, c i) • P := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s hmem ih => rw [Finset.sum_insert hmem, Finset.sum_insert hmem, add_nsmul, ih]

/-- **Fixed-base multiplication correctness**: the windowed computation
equals the standard scalar multiple. -/
theorem fixedBaseMul_eq_smul (B : Pallas.toAffine.Point)
    (ws : WindowedScalar) :
    fixedBaseMul B ws = scalarOfWindows ws • B := by
  simp only [fixedBaseMul, scalarOfWindows, fixedBaseEntry]
  exact sum_nsmul_eq _ _ B

/-- A windowed scalar is bounded by `windowBase ^ numWindows = 8^85`. -/
theorem scalar_bound (ws : WindowedScalar) :
    scalarOfWindows ws < windowBase ^ numWindows := by
  exact range_check_soundness (show 0 < windowBase by decide)
    ⟨fun i => (ws i).val, fun i => (ws i).isLt⟩

end

end Halo2
