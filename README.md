# halo2-formal

**Status:** Fully proven — zero `sorry` statements.

A Lean 4 formalization of the core components of Halo 2: the PLONKish arithmetization, polynomial commitment scheme, elliptic curve gadgets, Sinsemilla circuit, and Fiat-Shamir transcript. All algebraic and circuit-level properties are machine-verified; soundness results beyond algebraic correctness are axiomatized with documented justification.

## Overview

Halo 2 is a zk-SNARK (zero-knowledge Succinct Non-interactive ARgument of Knowledge) used in Zcash's Orchard protocol. It combines PLONKish arithmetization — a generalization of PLONK that supports custom gates and flexible column layouts — with an Inner Product Argument (IPA) polynomial commitment scheme that requires no trusted setup. A key feature of Halo 2 is its support for efficient recursive proof composition: proofs can verify other proofs inside the circuit, enabling amortized verification across chains of proofs. The protocol achieves 128-bit security over the Pasta curve cycle (Pallas and Vesta), which is specifically designed for recursive SNARK constructions.

This formalization covers the constraint system layer (PLONKish gates, permutation argument, lookup argument), the gadget layer (range checks, ECC scalar multiplication, Sinsemilla hashing), and the non-interactive layer (Poseidon-based Fiat-Shamir transcript). Every gate soundness theorem, range check, scalar multiplication correctness result, and transcript binding property is fully machine-proven in Lean 4 with Mathlib. The Sinsemilla circuit theorem — the headline result — establishes that the circuit gadget output equals `[2^n]·Q(D) + Σᵢ 2^(n-1-i)·S(mᵢ)`, connecting the circuit implementation directly to the protocol-level Pedersen vector hash from sinsemilla-formal.

This formalization does not cover IPA soundness (the Inner Product Argument extractability proof), full SNARK security (knowledge soundness with a rewinding extractor), or zero-knowledge. The permutation argument soundness is probabilistic by nature and is axiomatized with a Schwartz-Zippel justification; a full Lean proof would require building the symbolic polynomial machinery currently absent from Mathlib. All axioms are listed and justified in the [Axioms](#axioms) section below.

## Architecture

The seven components are organized in two dependency layers. The base layer contains `Commitment.lean` (Pedersen polynomial commitments, IPA interface) and `Spec.lean` (PLONKish gates, permutation, lookup, circuit example). Above that, `Properties.lean` imports `Spec.lean` and proves all gate soundness and circuit correctness theorems; `RangeCheck.lean` imports `Spec.lean` and provides the base-b decomposition gadget. The gadget layer then builds on these: `Transcript.lean` imports `Commitment.lean` and the Poseidon library for the Fiat-Shamir transcript; `ECCGadget.lean` imports both `Commitment.lean` and `RangeCheck.lean` for windowed and bit-decomposed scalar multiplication; and `SinsemillaGadget.lean` imports `Spec.lean` together with both the Sinsemilla spec and properties from sinsemilla-formal, proving the end-to-end circuit-to-protocol equivalence.

```
Commitment ──────────────────────────┐
    │                                 ▼
    └──────────────────────►  Transcript
                                      
Spec ──────────────────────┐
    │                       ▼
    ├──────────────►  Properties
    │
    └──────────────►  RangeCheck ──► ECCGadget
    │
    └──────────────►  SinsemillaGadget
                      (also uses Sinsemilla.{Spec,Properties})
```

## Formalization

### `Halo2/Commitment.lean`

Defines the Pedersen polynomial commitment scheme underlying Halo 2's polynomial IOP. `Poly n` is the type `Fin n → Fp` of coefficient vectors over the Pallas base field. `commit a blind` computes `C = Σᵢ aᵢ · G(i) + blind · H` where `G : ℕ → Point` and `H : Point` are axiomatized generators (hash-to-curve outputs certified by the Zcash parameter generation). `evalPoly a z` computes `Σᵢ aᵢ · z^i`. The IPA proof type `OpeningProof` and verification predicate `verifyOpening` are axiomatized as opaque, and `ipaCompleteness` — the axiom that honestly committed polynomials always produce valid opening proofs — is documented with its justification (see Axioms).

### `Halo2/Spec.lean`

Defines the PLONKish constraint system. A `Column n` is `Fin n → Fp`. A `Gate n` structure holds five selector columns (`q_L`, `q_R`, `q_O`, `q_M`, `q_C`), and `Gate.eval` computes `q_L·a + q_R·b + q_O·c + q_M·a·b + q_C` at each row; `Gate.satisfied` requires this to vanish everywhere. Four specialized gates are defined by their selector configurations: `addGate` (`a + b = c`), `mulGate` (`a * b = c`), `constGate n val` (`a = val`), and `boolGate` (`a(a−1) = 0`). The permutation argument uses `WirePerm n := Fin n → Fin n`, a running accumulator `permProduct`, the product-form check `permCheck` (numerator product = denominator product), and `copySatisfied` (pointwise copy constraint). The lookup argument uses `lookupSatisfied` (every witness value appears in the table), `lookupWitness` (an explicit index map), and the product pair `lookupProdF`/`lookupProdT`. `mulAddCircuit` is a two-row example circuit encoding `c = a * b + d`.

### `Halo2/Properties.lean`

Proves all semantic correctness theorems for the constraint system.

**Gate soundness (and completeness):**
- `addGate_sound` / `addGate_complete` — `(addGate n).satisfied a b c ↔ ∀ i, a i + b i = c i`
- `mulGate_sound` / `mulGate_complete` — `(mulGate n).satisfied a b c ↔ ∀ i, a i * b i = c i`
- `constGate_sound` — satisfied constant gate implies `a i = val` for all rows
- `boolGate_sound` — satisfied boolean gate implies `a i = 0 ∨ a i = 1` for all rows

**Permutation argument:**
- `perm_id_satisfied` — the identity permutation satisfies the running accumulator check under non-degeneracy
- `permCheck_of_copy` — copy constraints + bijectivity → `permCheck` passes (via `Equiv.prod_comp`)
- `permCheck_id` — the identity permutation trivially passes `permCheck`
- `permCheck_sound` — **AXIOM** (see extended note below)

**Lookup argument:**
- `lookup_prod_eq` — witness map existence → lookup products are equal
- `lookupSatisfied_of_witness` — witness map implies lookup satisfaction
- `lookup_witness_of_satisfied` — lookup satisfaction implies witness map exists (via `Classical.choice`)

**Circuit correctness:**
- `mulAddCircuit_sound` — the `mulAddCircuit` gate satisfied → row 0 computes product, row 1 computes sum
- `mulAdd_correct` — gate satisfaction + wire constraint `c(0) = a(1)` → `c(1) = a(0) * b(0) + b(1)`
- `gates_compose` — independently satisfied gates can constrain the same columns simultaneously

### `Halo2/RangeCheck.lean`

Defines and proves the lookup-based range check gadget. `Decomposition w b` is a structure holding `words : Fin w → ℕ` with `word_bound : ∀ i, words i < b`. `Decomposition.value` reconstructs `v = Σᵢ words(i) · b^i` via `Finset.sum`. Both the soundness and completeness directions are fully proven:
- `range_check_soundness` — a valid decomposition implies `d.value < b^w` (proved by induction over words with `Fin.sum_univ_castSucc`)
- `range_check_completeness` — for any `v < b^w` a decomposition exists (constructed by iterated Euclidean division `Nat.div` / `Nat.mod`)

### `Halo2/Transcript.lean`

Defines the Poseidon-based Fiat-Shamir transcript. A `Transcript` holds a `List Fp` of absorbed values. `Transcript.init domain` seeds the transcript with a domain separator; `Transcript.absorb t x` appends `x`; `Transcript.squeeze` folds the absorbed list via iterated `Poseidon.poseidonHash`. Fully proven properties include:
- `squeeze_deterministic` — same state → same challenge (trivially by `rfl`)
- `absorb_ne_comm` — absorb order matters: `absorb x then y ≠ absorb y then x ↔ x ≠ y`
- `absorb_injective` — different values produce different transcript states
- `challenge_binding_pair` — under `poseidon_collision_resistant`, same domain + different value → different challenge
- `domain_separation` — different domain separator → different challenge (prevents Frozen Heart)
- `transcript_separation` — different domain OR different value → different challenge

`poseidon_collision_resistant` is axiomatized (see Axioms).

### `Halo2/ECCGadget.lean`

Formalizes elliptic curve gadgets over the Pallas curve. `isExceptional P Q` flags the four degenerate cases (`P = 0`, `Q = 0`, `P = Q`, `P = -Q`) where incomplete addition is undefined. `incompleteAdd_comm` proves commutativity for non-exceptional inputs. `add_ne_zero_of_nonexceptional` is axiomatized (see Axioms).

For fixed-base scalar multiplication: `WindowedScalar := Fin 85 → Fin 8` (3-bit windows, 85 windows covering a 255-bit scalar). `fixedBaseEntry B i w` returns `(w · 8^i) • B`. `fixedBaseMul` sums all window contributions. Key theorems:
- `fixedBaseMul_eq_smul` — `fixedBaseMul B ws = scalarOfWindows ws • B` (via `sum_nsmul_eq`)
- `scalar_bound` — `scalarOfWindows ws < 8^85` (via `range_check_soundness`)

For variable-base scalar multiplication: `ScalarBits n := Fin n → Fin 2`, with `scalarOfBits bits = Σᵢ bᵢ · 2^i`. Key theorems:
- `variableBaseMul_eq_smul` — `variableBaseMul P bits = scalarOfBits bits • P`
- `scalar_bits_bound` — `scalarOfBits bits < 2^n`

### `Halo2/SinsemillaGadget.lean`

Formalizes the Sinsemilla hash circuit gadget. `sinsemillaAccumulate chunks init` folds the chunk list left-to-right computing `Acc_{i+1} = 2 • Acc_i + S(mᵢ)`. `SinsemillaCircuitWitness` bundles the domain `D : List UInt8`, the chunk list, accumulator states at each step, and two algebraic constraints: `acc_init` (initial state = `Q D`) and `acc_step` (each transition follows the accumulator rule). The output is the final accumulator state.

The proof proceeds in two steps. First, `acc_states_eq_accumulate` shows by induction that the circuit accumulator states match `sinsemillaAccumulate (chunks.take k) (Q D)` for all `k`; this uses `sinsemillaAccumulate_append_singleton` and `List.take_concat_get'`. Second, `sinsemillaAccumulate_pedersen` gives the closed-form Pedersen representation by induction on the chunk list:

```
sinsemillaAccumulate chunks P = 2^n • P + sumChunks chunks
```

Combining these gives the **headline theorem**:

**`sinsemilla_circuit_pedersen`**: for any satisfied `SinsemillaCircuitWitness w`,

```
w.output = 2^(w.chunks.length) • Q(w.D) + sumChunks(w.chunks)
```

This is the same form as `hashToPoint_pedersen` from sinsemilla-formal, establishing that the circuit computes exactly the protocol-level Sinsemilla Pedersen vector hash.

## Key Results

### Gate Soundness

`addGate_sound` states that if `(addGate n).satisfied a b c`, then `∀ i, a i + b i = c i`. The proof unfolds the selector definitions and closes by `linear_combination`. Analogously, `mulGate_sound` establishes `a i * b i = c i`, `constGate_sound` establishes `a i = val`, and `boolGate_sound` establishes `a i = 0 ∨ a i = 1` (using `mul_eq_zero` to split the quadratic). These are the semantic correctness theorems for PLONKish gates: a syntactic gate configuration implies the intended arithmetic relation on the advice columns.

### Range Check Completeness and Soundness

**Soundness** (`range_check_soundness`): given `d : Decomposition w b` with `hb : 0 < b`, we have `d.value < b^w`. Proved by induction using `Fin.sum_univ_castSucc` to split off the most-significant word and `Nat.mul_le_mul_right` to bound the contribution of that word.

**Completeness** (`range_check_completeness`): for any `v : ℕ` with `hv : v < b^w` and `hb : 1 < b`, there exists a `d : Decomposition w b` with `d.value = v`. Constructed by downward induction on `w`: the digit at position 0 is `v % b` and the remaining words decompose `v / b < b^(w-1)`, using `Nat.mod_add_div` to verify reconstruction.

### ECC Scalar Multiplication

`fixedBaseMul_eq_smul`: the windowed fixed-base computation `Σᵢ fixedBaseEntry B i (ws i)` equals `scalarOfWindows ws • B`, where `scalarOfWindows ws = Σᵢ ws(i) · 8^i`. The proof reduces to `sum_nsmul_eq`, which distributes scalar multiplication over a `Finset.sum` by induction.

`variableBaseMul_eq_smul`: the double-and-add computation `Σᵢ (bᵢ · 2^i) • P` equals `scalarOfBits bits • P`. These two theorems bridge the circuit-level windowed/bit-decomposed computations to the standard abstract scalar multiplication `(•)` on the Pallas group.

### Sinsemilla Circuit = Protocol

**`sinsemilla_circuit_pedersen`**: for any satisfied `SinsemillaCircuitWitness w` with `n = w.chunks.length` chunks,

```
w.output = 2^n • Q(w.D) + sumChunks(w.chunks)
```

where `sumChunks` is defined in sinsemilla-formal as `Σᵢ 2^(n-1-i) • S(mᵢ)` (the Pedersen weight vector). This theorem connects the Halo 2 circuit implementation — which operates via the running `2 • acc + S m` accumulation rule — to the closed-form Pedersen hash `hashToPoint_pedersen` from sinsemilla-formal, completing the circuit-to-protocol equivalence chain.

### Transcript Binding

**`transcript_separation`**: for domain separators `d₁, d₂` and absorbed values `x₁, x₂`, if `d₁ ≠ d₂ ∨ x₁ ≠ x₂`, then the squeezed challenges differ. The proof reduces the squeeze to `poseidonHash d x` (via `squeeze_init_absorb`) and then applies `poseidon_collision_resistant` to extract the contradiction. This is the binding property of the Fiat-Shamir transcript: distinct protocol contexts or distinct committed values yield distinct verifier challenges.

## Axioms

| Axiom | File | Type | Justification |
|-------|------|------|---------------|
| `ipaCompleteness` | Commitment.lean | IPA completeness | Inner Product Argument completeness — deep proof theory, not yet in Mathlib |
| `permCheck_sound` | Properties.lean | Schwartz-Zippel | See extended note below |
| `poseidon_collision_resistant` | Transcript.lean | Hardness assumption | Conjectured from algebraic degree bounds; not derivable from bijectivity alone |
| `add_ne_zero_of_nonexceptional` | ECCGadget.lean | Group order | Sum of non-exceptional Pallas points is non-zero; requires prime group order axiom |
| `G` | Commitment.lean | Generator existence | Pedersen commitment generators (hash-to-curve certified parameters) |
| `H` | Commitment.lean | Generator existence | Independent blinding generator (hash-to-curve certified parameter) |

### Extended Note on `permCheck_sound` (Schwartz-Zippel)

The permutation argument soundness axiom states: if `σ` is a bijection and `permCheck a σ β γ` holds for all field elements `β` and `γ`, then the copy constraints `copySatisfied a σ` hold. The justification is probabilistic via the Schwartz-Zippel lemma. Fix any failing assignment `a` (i.e., some `i` with `a i ≠ a (σ i)`). The permutation check `numProd a β γ = denProd a σ β γ` can be rewritten as the vanishing of a rational function in `β` whose numerator is a nonzero polynomial of degree at most `n` in `β` (since the two products are distinct multisets of linear factors when the copy constraint fails). By Schwartz-Zippel, a nonzero polynomial of degree `n` over `Fp` has at most `n` roots, so a uniformly random `β ∈ Fp` makes the check pass with probability at most `n / |Fp|`. Since `|Fp| ≈ 2^254`, this is cryptographically negligible.

A formal Lean proof would require three ingredients:
1. Expressing `numProd` and `denProd` as evaluations of explicit univariate polynomials in `β` (symbolic polynomial representation over `Fp[β]`).
2. Showing that if the copy constraints fail, the difference polynomial is nonzero in `Fp[β]` (which requires reasoning about roots of products of linear factors, connecting to unique factorization in `Fp[β]`).
3. Applying `Polynomial.card_roots_le_degree` from Mathlib to conclude that the set of "bad" challenges `β` has size at most `n`.

This is in principle derivable from existing Mathlib primitives, but requires substantial setup — in particular, a formal bridge between the finset-product definition of `permCheck` and an element of `Polynomial Fp` — that is beyond the current scope.

## Dependencies

- Lean 4 (v4.30.0-rc2)
- Mathlib4
- [pasta-formal](https://github.com/oxarbitrage/pasta-formal)
- [poseidon-formal](https://github.com/oxarbitrage/poseidon-formal)
- [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal)

## Building

```shell
lake build
```

## References

- [Halo 2 book](https://zcash.github.io/halo2/)
- [PLONKish arithmetization](https://zcash.github.io/halo2/concepts/arithmetization.html)
- [Zcash Protocol Specification §5.4.9](https://zips.z.cash/protocol/protocol.pdf)
- [Bünz et al., "Proofs for Inner Pairing Products and Applications"](https://eprint.iacr.org/2019/1021) (IPA)
- [Gabizon, Williamson, Ciobotaru, "PLONK"](https://eprint.iacr.org/2019/953)

## License

MIT
