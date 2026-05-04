# halo2-formal

**Status:** Fully proven — zero `sorry` statements.

Lean 4 formalization of core Halo 2 components: PLONKish constraint system, elliptic curve gadgets, Sinsemilla circuit gadget, and Fiat-Shamir transcript.

## What's formalized

**Key results:**

- **`sinsemilla_circuit_pedersen`** — the Sinsemilla circuit gadget computes [2ⁿ]·Q(D) + Σᵢ 2^(n−1−i)·S(mᵢ): the circuit matches the protocol spec.
- **`fixedBaseMul_eq_smul`**, **`variableBaseMul_eq_smul`** — fixed-base (3-bit windowed) and variable-base (double-and-add) scalar multiplication circuits equal standard scalar multiplication.
- **`addGate_sound`**, **`mulGate_sound`**, **`boolGate_sound`** — gate satisfaction implies the claimed arithmetic relation.
- **`range_check_soundness`** / **`range_check_completeness`** — base-b decomposition is sound and complete.
- **`transcript_separation`** — distinct domain or value → distinct Fiat-Shamir challenge.

## Axioms

| Axiom | Justification |
|-------|--------------|
| `permCheck_sound` | Schwartz-Zippel soundness — probabilistic argument, see inline doc comment |
| `ipaCompleteness` | IPA completeness — deep proof theory, not yet in Mathlib |
| `poseidon_collision_resistant` | Conjectured; not derivable from `permutation_bijective` |
| `add_ne_zero_of_nonexceptional` | DLP assumption for EC sum non-zeroness |

## Build

```shell
lake build
```

## Dependencies

Lean 4 (`v4.30.0-rc2`), [Mathlib4](https://github.com/leanprover-community/mathlib4), [pasta-formal](https://github.com/oxarbitrage/pasta-formal), [poseidon-formal](https://github.com/oxarbitrage/poseidon-formal), [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal).

## References

- [Halo 2 book](https://zcash.github.io/halo2/)
- [PLONKish arithmetization](https://zcash.github.io/halo2/concepts/arithmetization.html)
- [PLONK paper](https://eprint.iacr.org/2019/953)

---

## Part of a series

Six repositories formally verifying the Zcash Orchard cryptographic stack:

| Layer | Repository |
|-------|-----------|
| Curves | [pasta-formal](https://github.com/oxarbitrage/pasta-formal) |
| Hash | [poseidon-formal](https://github.com/oxarbitrage/poseidon-formal) |
| Hash-to-curve | [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal) |
| Signatures | [redpallas-formal](https://github.com/oxarbitrage/redpallas-formal) |
| Protocol | [orchard-formal](https://github.com/oxarbitrage/orchard-formal) |
| Proof system | [halo2-formal](https://github.com/oxarbitrage/halo2-formal) |
