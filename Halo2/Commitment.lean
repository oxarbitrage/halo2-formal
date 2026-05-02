import Pasta.Pallas
import Pasta.Fields
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Halo2

/-! # Pedersen polynomial commitment scheme

A Pedersen commitment to a polynomial `p(X)` of degree < `n` is:

  `C = Σᵢ aᵢ · Gᵢ + r · H`

where `aᵢ` are the coefficients of `p`, `Gᵢ` are public generator
points, `r` is a blinding factor, and `H` is a separate blinding
generator.

This is the commitment scheme underlying Halo 2's polynomial IOP.

See §3.2 of the Halo paper and the halo2 book.
-/

open Pasta Finset

noncomputable section

/-! ## Generators and parameters -/

/-- Public generator points for polynomial commitments.

`G i` is the generator for the i-th coefficient. In practice these
are derived via a hash-to-curve construction. -/
axiom G : ℕ → Pallas.toAffine.Point

/-- Blinding generator, independent of the coefficient generators. -/
axiom H : Pallas.toAffine.Point
axiom H_ne_zero : H ≠ 0

/-! ## Polynomial commitment -/

/-- A polynomial of degree < n, represented as n coefficients. -/
abbrev Poly (n : ℕ) := Fin n → Pasta.Fp

/-- Commit to a polynomial with a blinding factor.

`commit a r = Σᵢ aᵢ.val • G i + r.val • H` -/
def commit {n : ℕ} (a : Poly n) (blind : Pasta.Fp) :
    Pallas.toAffine.Point :=
  (∑ i : Fin n, (a i).val • G i.val) + blind.val • H

/-- Evaluate a polynomial at a point.

`evalPoly a z = Σᵢ aᵢ · z ^ i` -/
def evalPoly {n : ℕ} (a : Poly n) (z : Pasta.Fp) : Pasta.Fp :=
  ∑ i : Fin n, a i * z ^ i.val

/-! ## Opening proof (IPA)

An opening proof demonstrates that the committed polynomial evaluates
to a claimed value `v` at a challenge point `z`. In Halo 2 this is
done via the Inner Product Argument (IPA), which recursively halves
the polynomial and produces a logarithmic-sized proof.

We axiomatize the IPA verification and its completeness. -/

/-- An IPA opening proof (opaque). -/
axiom OpeningProof : Type

/-- IPA verification: `verifyOpening C z v π` holds when `π` proves
that the polynomial committed in `C` evaluates to `v` at `z`. -/
axiom verifyOpening :
    Pallas.toAffine.Point → Pasta.Fp → Pasta.Fp → OpeningProof → Prop

/-- IPA completeness: an honestly generated proof for a correctly
committed polynomial always verifies. -/
axiom ipaCompleteness {n : ℕ} (a : Poly n) (blind : Pasta.Fp)
    (z : Pasta.Fp) (π : OpeningProof) :
    verifyOpening (commit a blind) z (evalPoly a z) π

end

end Halo2
