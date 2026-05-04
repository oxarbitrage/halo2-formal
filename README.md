# halo2-formal

Lean 4 formalization of [Halo 2](https://zips.z.cash/protocol/protocol.pdf#halo2)'s PLONKish constraint system and polynomial commitment scheme, as used in Zcash's Orchard protocol.

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

### Range check (`Halo2/RangeCheck.lean`)

| Component | Description |
|-----------|-------------|
| Decomposition | Base-b word decomposition: `v = Σᵢ wᵢ · b^i` with each `wᵢ < b` |
| **Range check soundness** | Valid decomposition → `v < b^w` |
| **Range check completeness** | `v < b^w` → decomposition exists (via Euclidean division) |

### Fiat-Shamir transcript (`Halo2/Transcript.lean`)

| Component | Description |
|-----------|-------------|
| Transcript state | Sequence of absorbed field elements |
| Challenge derivation | Iterated PoseidonHash fold over absorbed values |
| Absorb injectivity | Different absorbed values → different transcript states |
| **Challenge binding** | Under Poseidon collision resistance, distinct inputs → distinct challenges |
| **Domain separation** | Different domain separators → different challenges (prevents Frozen Heart) |
| **Transcript separation** | Different domain OR different value → different challenges |

### ECC gadget (`Halo2/ECCGadget.lean`)

| Component | Description |
|-----------|-------------|
| Exceptional cases | `P = 0 ∨ Q = 0 ∨ P = Q ∨ P = -Q` |
| Incomplete addition commutativity | Non-exceptional addition is commutative |
| Fixed-base table | Precomputed `[w · 2^(3i)] B` for 3-bit windows |
| **Fixed-base mul correctness** | Windowed computation = standard scalar multiple |
| **Scalar bound** | Windowed scalar < `8^85` (from range check soundness) |
| Variable-base bit decomposition | `ScalarBits n = Fin n → Fin 2` with reconstruction |
| Variable-base mul | `∑ᵢ bᵢ · 2^i · P` via double-and-add |
| **Variable-base mul correctness** | Bit-decomposed computation = standard scalar multiple |
| **Variable-base scalar bound** | Bit-decomposed scalar < `2^n` |

### Sinsemilla circuit gadget (`Halo2/SinsemillaGadget.lean`)

| Component | Description |
|-----------|-------------|
| Circuit accumulator | `sinsemillaAccumulate`: iterative `Acc_{i+1} = [2]·Acc_i + S(m_i)` |
| Circuit witness | Chunks, accumulator states, init/step constraints |
| Append step | `sinsemillaAccumulate (chunks ++ [m]) init = 2 • acc + S m` |
| **Circuit correctness** | Circuit output = `sinsemillaAccumulate chunks (Q D)` |
| **Pedersen equivalence** | `sinsemillaAccumulate chunks P = [2^n]·P + sumChunks(chunks)` |
| **End-to-end circuit theorem** | Circuit output = `[2^n]·Q(D) + sumChunks(chunks)` (Pedersen vector hash) |

## Axioms

**Opaque data/functions:**

- `G`, `H`, `H_ne_zero` — commitment generators (hash-to-curve outputs)
- `OpeningProof`, `verifyOpening` — IPA proof type and verification relation

**Cryptographic assumptions:**

- `ipaCompleteness` — honestly generated IPA proofs verify
- `permCheck_sound` — product equality for all challenges implies copy constraints ([Schwartz-Zippel](https://en.wikipedia.org/wiki/Schwartz%E2%80%93Zippel_lemma))
- `poseidon_collision_resistant` — distinct inputs produce distinct outputs (Fiat-Shamir binding)
- `add_ne_zero_of_nonexceptional` — `P + Q ≠ 0` when non-exceptional (DLP-based)

All gate soundness, permutation completeness, lookup, range check, scalar multiplication, transcript binding, Sinsemilla circuit correctness, and circuit properties are **fully proven**.

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
- **[sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal)** — Sinsemilla hash function and Pedersen equivalence

## References

- [Zcash Protocol Specification §5.4.9](https://zips.z.cash/protocol/protocol.pdf#halo2) — Halo 2 instantiation
- [Halo 2 book — Sinsemilla gadget](https://zcash.github.io/halo2/design/gadgets/sinsemilla.html) — Circuit-level Sinsemilla
- [Halo 2 book](https://zcash.github.io/halo2/) — PLONKish arithmetization and IPA
- [PLONK](https://eprint.iacr.org/2019/953) — Permutations over Lagrange-bases for Oecumenical Noninteractive arguments of Knowledge
- [Halo](https://eprint.iacr.org/2019/1021) — Recursive Proof Composition without a Trusted Setup
- [pasta-formal](https://github.com/oxarbitrage/pasta-formal) — Pallas/Vesta Lean 4 formalization
- [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal) — Sinsemilla Lean 4 formalization

## License

MIT
