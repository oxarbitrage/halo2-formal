# halo2-formal

Lean 4 formalization of [Halo 2](https://zcash.github.io/halo2/)'s PLONKish constraint system and polynomial commitment scheme, as used in Zcash's Orchard protocol.

**Status: fully proven — zero `sorry`.**

## What's formalized

All definitions and theorems live under the `Halo2` namespace. Built on top of [pasta-formal](https://github.com/oxarbitrage/pasta-formal).

### Polynomial commitment (`Halo2/Commitment.lean`)

| Component | Description |
|-----------|-------------|
| Generators | Public generators `G(i)` and blinding generator `H` |
| Polynomial type | `Poly n = Fin n → Fp` — coefficient vectors |
| Commitment | `C = Σᵢ aᵢ · G(i) + r · H` |
| Evaluation | `evalPoly a z = Σᵢ aᵢ · zⁱ` |
| IPA verification | Axiomatized verification relation for opening proofs |
| IPA completeness | Axiomatized: honest proofs always verify |

### PLONKish arithmetization (`Halo2/Spec.lean`)

| Component | Description |
|-----------|-------------|
| Column | `Fin n → Fp` — field elements indexed by row |
| Gate | Standard PLONKish gate: `q_L·a + q_R·b + q_O·c + q_M·a·b + q_C = 0` |
| Addition gate | `a + b = c` — selectors `(1, 1, -1, 0, 0)` |
| Multiplication gate | `a * b = c` — selectors `(0, 0, -1, 1, 0)` |
| Constant gate | `a = val` — selectors `(1, 0, 0, 0, -val)` |
| Boolean gate | `a ∈ {0,1}` — selectors `(-1, 0, 0, 1, 0)` with `b = a` |
| Wire permutation | `Fin n → Fin n` mapping connected wires |
| Grand product | Accumulator `Z(i)` for the permutation argument |
| Product-based perm check | `∏ᵢ (a(i) + β·i + γ) = ∏ᵢ (a(i) + β·σ(i) + γ)` |
| Copy constraints | `∀ i, a(i) = a(σ(i))` |
| Lookup table | Subset check: every witness value appears in a table |
| Lookup witness map | `w : Fin n → Fin m` mapping witness to table entries |
| Circuit example | `mulAddCircuit`: computes `a * b + d` in 2 rows |

### Properties (`Halo2/Properties.lean`)

| Property | Description |
|----------|-------------|
| **Addition gate soundness** | Satisfied gate ↔ `a + b = c` on every row |
| **Multiplication gate soundness** | Satisfied gate ↔ `a * b = c` on every row |
| **Constant gate soundness** | Satisfied gate → `a = val` on every row |
| **Boolean gate soundness** | Satisfied gate → `a = 0 ∨ a = 1` on every row |
| **Permutation argument completeness** | Copy constraints + σ bijective → grand product check passes |
| **Permutation check identity** | Identity permutation trivially passes |
| **Permutation argument soundness** | Check passes for all challenges → copy constraints (axiom, Schwartz-Zippel) |
| **Lookup completeness** | Witness map exists → lookup products equal |
| **Lookup soundness** | Lookup satisfied ↔ witness map exists |
| **Circuit soundness** | `mulAddCircuit` satisfied → row 0 is mul, row 1 is add |
| **End-to-end circuit correctness** | Gate + wire constraint → `c(1) = a(0) * b(0) + b(1)` |
| **Gate composition** | Multiple satisfied gates can constrain the same columns |

## Axioms

- **Generator points** (`G`, `H`): opaque data from hash-to-curve
- **IPA opening proof** and verification: opaque type and relation
- **IPA completeness**: honestly generated proofs verify
- **Permutation soundness**: product equality for all challenges implies copy constraints (Schwartz-Zippel)

All gate soundness, permutation completeness, lookup, and circuit correctness properties are fully proven.

## Building

Requires [elan](https://github.com/leanprover/elan). The correct Lean toolchain is installed automatically.

```sh
lake update    # fetch Mathlib + dependencies (~3 GB of cached oleans)
lake build     # builds in ~10 seconds after cache download
```

## Dependencies

- **Lean 4** (v4.30.0-rc2)
- **Mathlib4** — finite field theory, big operators, tactics
- **[pasta-formal](https://github.com/oxarbitrage/pasta-formal)** — Pallas/Vesta curve definitions and primality proofs
- **[poseidon-formal](https://github.com/oxarbitrage/poseidon-formal)** — Poseidon hash function specification

## References

- [Halo 2 book](https://zcash.github.io/halo2/) — PLONKish arithmetization and IPA
- [PLONK: Permutations over Lagrange-bases for Oecumenical Noninteractive arguments of Knowledge](https://eprint.iacr.org/2019/953) — original PLONK paper
- [Recursive Proof Composition without a Trusted Setup](https://eprint.iacr.org/2019/1021) — original Halo paper
- [Zcash protocol specification](https://zips.z.cash/protocol/protocol.pdf) — §5.4.9 Halo 2 instantiation
