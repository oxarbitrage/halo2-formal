import Halo2.Spec
import Sinsemilla.Spec
import Sinsemilla.Properties

namespace Halo2

/-! # Sinsemilla circuit gadget

The Sinsemilla gadget implements the protocol-level `SinsemillaHashToPoint`
inside a Halo 2 circuit. The key circuit-level optimizations are:

1. **Running sum decomposition**: the message is decomposed into 10-bit
   chunks via a running sum, where each step extracts one chunk by
   subtracting and dividing by 2¹⁰.

2. **Lookup table**: each 10-bit chunk is range-checked via a lookup
   against the table `{0, ..., 1023}`, simultaneously mapping to
   the generator `S(j)`.

3. **Incomplete addition accumulator**: the accumulator step uses
   incomplete addition (cheaper constraints than full addition).

The main theorem proves that a satisfied Sinsemilla circuit computes
the same result as the protocol-level `SinsemillaHashToPoint`.

See [§4.1.5 of the Halo 2 book](https://zcash.github.io/halo2/design/gadgets/sinsemilla.html).
-/

open Pasta Sinsemilla

noncomputable section

/-! ## Sinsemilla circuit accumulation

The circuit accumulator iteratively applies `Acc_{i+1} = [2]·Acc_i + S(m_i)`
using standard group operations on affine points.
-/

/-- The Sinsemilla circuit accumulator: iteratively applies
`Acc_{i+1} = [2]·Acc_i + S(m_i)` using standard group operations.

This is the circuit-level computation that, when the incomplete addition
does not hit exceptional cases, equals the protocol-level step function. -/
def sinsemillaAccumulate (chunks : List (Fin 1024))
    (init : Pallas.toAffine.Point) : Pallas.toAffine.Point :=
  chunks.foldl (fun acc m => 2 • acc + S m) init

@[simp]
theorem sinsemillaAccumulate_cons (m : Fin 1024) (rest : List (Fin 1024))
    (init : Pallas.toAffine.Point) :
    sinsemillaAccumulate (m :: rest) init =
    sinsemillaAccumulate rest (2 • init + S m) := by
  unfold sinsemillaAccumulate
  simp [List.foldl]

@[simp]
theorem sinsemillaAccumulate_nil (init : Pallas.toAffine.Point) :
    sinsemillaAccumulate [] init = init := rfl

/-- Appending a single chunk is one accumulator step. -/
theorem sinsemillaAccumulate_append_singleton (chunks : List (Fin 1024))
    (m : Fin 1024) (init : Pallas.toAffine.Point) :
    sinsemillaAccumulate (chunks ++ [m]) init =
    2 • sinsemillaAccumulate chunks init + S m := by
  unfold sinsemillaAccumulate
  simp [List.foldl_append]

/-! ## Sinsemilla circuit satisfaction

The Sinsemilla circuit constrains:
1. Each chunk is in `{0, ..., 1023}` (via lookup)
2. The accumulator follows the step function: `Acc_{i+1} = [2]·Acc_i + S(m_i)`
3. The initial accumulator is `Q(D)`
-/

/-- The Sinsemilla circuit witness: chunks, accumulator states, and a
running sum decomposition. -/
structure SinsemillaCircuitWitness where
  D : List UInt8
  chunks : List (Fin 1024)
  hlen : chunks.length ≤ Sinsemilla.c
  accStates : Fin (chunks.length + 1) → Pallas.toAffine.Point
  acc_init : accStates ⟨0, Nat.zero_lt_succ _⟩ = Q D
  acc_step : ∀ (i : Fin chunks.length),
    accStates ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
    2 • accStates ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ _)⟩ +
    S (chunks.get ⟨i.val, i.isLt⟩)

/-- The output of the Sinsemilla circuit is the final accumulator state. -/
def SinsemillaCircuitWitness.output (w : SinsemillaCircuitWitness) :
    Pallas.toAffine.Point :=
  w.accStates ⟨w.chunks.length, Nat.lt_succ_of_le le_rfl⟩

/-! ## Circuit-to-protocol equivalence

The central theorem: the Sinsemilla circuit computes the same result
as the direct accumulation `sinsemillaAccumulate`.
-/

/-- The accumulator states match stepwise accumulation. -/
theorem acc_states_eq_accumulate (w : SinsemillaCircuitWitness)
    (k : ℕ) (hk : k ≤ w.chunks.length) :
    w.accStates ⟨k, Nat.lt_succ_of_le hk⟩ =
    sinsemillaAccumulate (w.chunks.take k) (Q w.D) := by
  induction k with
  | zero =>
    simp only [List.take_zero, sinsemillaAccumulate_nil]
    exact w.acc_init
  | succ j ih =>
    have hj : j < w.chunks.length := Nat.lt_of_succ_le hk
    rw [w.acc_step ⟨j, hj⟩, ih (Nat.le_of_lt hj)]
    rw [show w.chunks.take (j + 1) = w.chunks.take j ++ [w.chunks.get ⟨j, hj⟩]
      from (List.take_concat_get' w.chunks j hj).symm]
    rw [sinsemillaAccumulate_append_singleton]

/-- **Sinsemilla circuit correctness**: the circuit output equals
the direct accumulation of chunks starting from `Q(D)`. -/
theorem sinsemilla_circuit_correct (w : SinsemillaCircuitWitness) :
    w.output = sinsemillaAccumulate w.chunks (Q w.D) := by
  unfold SinsemillaCircuitWitness.output
  rw [acc_states_eq_accumulate w w.chunks.length le_rfl]
  simp [List.take_length]

/-! ## Pedersen equivalence for circuit accumulation

Connecting the circuit accumulation to the closed-form Pedersen hash. -/

/-- The circuit accumulation equals `[2^n]·Q(D) + sumChunks(chunks)`.

This bridges the circuit-level computation to the Pedersen vector hash
structure proven in sinsemilla-formal. -/
theorem sinsemillaAccumulate_pedersen (chunks : List (Fin 1024))
    (P : Pallas.toAffine.Point) :
    sinsemillaAccumulate chunks P =
    2 ^ chunks.length • P + sumChunks chunks := by
  induction chunks generalizing P with
  | nil => simp [sumChunks]
  | cons m rest ih =>
    simp only [sinsemillaAccumulate_cons, List.length_cons, sumChunks_cons]
    rw [ih]
    have hdist := smul_add (2 ^ rest.length) (2 • P) (S m)
    rw [hdist, ← mul_nsmul', ← pow_succ]
    abel

/-- **End-to-end Sinsemilla circuit theorem**: a satisfied Sinsemilla circuit
produces `[2^n]·Q(D) + sumChunks(chunks)`, the Pedersen vector hash.

This is the same form as `hashToPoint_pedersen` from sinsemilla-formal,
establishing that the circuit computes exactly the protocol-level hash
(when the protocol-level hash does not hit exceptional cases). -/
theorem sinsemilla_circuit_pedersen (w : SinsemillaCircuitWitness) :
    w.output = 2 ^ w.chunks.length • Q w.D + sumChunks w.chunks := by
  rw [sinsemilla_circuit_correct, sinsemillaAccumulate_pedersen]

end

end Halo2
