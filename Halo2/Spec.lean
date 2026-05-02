import Pasta.Fields
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Halo2

/-! # PLONKish arithmetization

Halo 2 uses a PLONKish constraint system where a circuit is defined by:

1. **Columns**: fixed (preprocessed), advice (witness), instance (public input)
2. **Gates**: polynomial constraints that must vanish on every row
3. **Permutation argument**: ensures wires are correctly connected

A valid assignment is one where all gate polynomials evaluate to zero
on every row and the permutation constraints are satisfied.

See the [halo2 book](https://zcash.github.io/halo2/concepts/arithmetization.html).
-/

open Pasta

noncomputable section

/-! ## Circuit types -/

/-- A column of field elements, one per row. -/
abbrev Column (n : ℕ) := Fin n → Pasta.Fp

/-! ## Gate model

A gate is a polynomial constraint over column values at each row.
For a width-3 PLONKish gate (a, b, c) with selectors (q_L, q_R, q_O, q_M, q_C):

  `q_L·a + q_R·b + q_O·c + q_M·a·b + q_C = 0`

This generalizes to custom gates with arbitrary polynomial expressions.
-/

/-- A standard PLONKish gate with selectors. -/
structure Gate (n : ℕ) where
  q_L : Column n
  q_R : Column n
  q_O : Column n
  q_M : Column n
  q_C : Column n

/-- Evaluate a standard gate at row `i` given advice columns a, b, c. -/
def Gate.eval {n : ℕ} (gate : Gate n) (a b c : Column n) (i : Fin n) :
    Pasta.Fp :=
  gate.q_L i * a i + gate.q_R i * b i + gate.q_O i * c i +
  gate.q_M i * (a i * b i) + gate.q_C i

/-- A gate is satisfied by an assignment if it evaluates to zero on every row. -/
def Gate.satisfied {n : ℕ} (gate : Gate n) (a b c : Column n) : Prop :=
  ∀ i : Fin n, gate.eval a b c i = 0

/-! ## Specialized gates

Common circuit operations can be expressed as specific gate configurations.
-/

/-- An addition gate: `a + b = c`.

Selectors: q_L = 1, q_R = 1, q_O = -1, q_M = 0, q_C = 0. -/
def addGate (n : ℕ) : Gate n where
  q_L := fun _ => 1
  q_R := fun _ => 1
  q_O := fun _ => -1
  q_M := fun _ => 0
  q_C := fun _ => 0

/-- A multiplication gate: `a * b = c`.

Selectors: q_L = 0, q_R = 0, q_O = -1, q_M = 1, q_C = 0. -/
def mulGate (n : ℕ) : Gate n where
  q_L := fun _ => 0
  q_R := fun _ => 0
  q_O := fun _ => -1
  q_M := fun _ => 1
  q_C := fun _ => 0

/-- A constant gate: `a = const` at row `i`.

Selectors: q_L = 1, q_R = 0, q_O = 0, q_M = 0, q_C = -const. -/
def constGate (n : ℕ) (val : Pasta.Fp) : Gate n where
  q_L := fun _ => 1
  q_R := fun _ => 0
  q_O := fun _ => 0
  q_M := fun _ => 0
  q_C := fun _ => -val

/-- A boolean gate: `a * (1 - a) = 0`.

Ensures `a ∈ {0, 1}`. Selectors: q_L = -1, q_R = 0, q_O = 0, q_M = 1, q_C = 0. -/
def boolGate (n : ℕ) : Gate n where
  q_L := fun _ => -1
  q_R := fun _ => 0
  q_O := fun _ => 0
  q_M := fun _ => 1
  q_C := fun _ => 0

/-! ## Permutation argument

The permutation argument ensures that wires are correctly connected
across different gates. A permutation `σ` maps each cell (column, row)
to the cell it must equal.

The grand product argument checks that:
  `∏ᵢ (aᵢ + β·σ(i) + γ) / (aᵢ + β·i + γ) = 1`

which holds iff the assignment is consistent with the permutation.
-/

/-- A wire permutation maps each row index to the row it is connected to.

For simplicity we model permutation on a single column; the full
PLONKish permutation extends across multiple columns. -/
def WirePerm (n : ℕ) := Fin n → Fin n

/-- The grand product accumulator for the permutation argument.

`Z(0) = 1` and `Z(i+1) = Z(i) · (a(i) + β·i + γ) / (a(i) + β·σ(i) + γ)`.

For the permutation to hold, `Z(n) = 1`. -/
def permProduct {n : ℕ} (a : Column n) (σ : WirePerm n)
    (β γ : Pasta.Fp) (k : ℕ) : Pasta.Fp :=
  match k with
  | 0 => 1
  | k + 1 =>
    if h : k < n then
      let i : Fin n := ⟨k, h⟩
      permProduct a σ β γ k *
        (a i + β * (i.val : Pasta.Fp) + γ) /
        (a i + β * ((σ i).val : Pasta.Fp) + γ)
    else permProduct a σ β γ k

/-- A permutation is satisfied when the grand product equals 1. -/
def permSatisfied {n : ℕ} (a : Column n) (σ : WirePerm n)
    (β γ : Pasta.Fp) : Prop :=
  permProduct a σ β γ n = 1

/-! ## Product-based permutation check

The division-based formulation above is used in the protocol's running
accumulator. For proving soundness, the equivalent product formulation
is cleaner: the numerator product must equal the denominator product.
-/

/-- Numerator product: `∏ᵢ (a(i) + β·i + γ)`. -/
def numProd {n : ℕ} (a : Column n) (β γ : Pasta.Fp) : Pasta.Fp :=
  ∏ i : Fin n, (a i + β * (i.val : Pasta.Fp) + γ)

/-- Denominator product: `∏ᵢ (a(i) + β·σ(i) + γ)`. -/
def denProd {n : ℕ} (a : Column n) (σ : WirePerm n) (β γ : Pasta.Fp) :
    Pasta.Fp :=
  ∏ i : Fin n, (a i + β * ((σ i).val : Pasta.Fp) + γ)

/-- The permutation check in product form: numerator = denominator. -/
def permCheck {n : ℕ} (a : Column n) (σ : WirePerm n)
    (β γ : Pasta.Fp) : Prop :=
  numProd a β γ = denProd a σ β γ

/-- Copy constraint satisfaction: the assignment at each position equals
the assignment at its permuted position. -/
def copySatisfied {n : ℕ} (a : Column n) (σ : WirePerm n) : Prop :=
  ∀ i : Fin n, a i = a (σ i)

/-! ## Lookup argument

The lookup argument ensures every value in a witness column appears
in a fixed lookup table. Halo 2 uses a product-based argument:

Given witness values `f(i)` and table values `t(i)`, the check is:

  `∏ᵢ (γ + f(i)) = ∏ᵢ (γ + t(s(i)))`

where `s` is a permutation showing how to reorder `t` to match `f`.
More precisely, the prover sorts `f` and `t` together and the product
argument verifies consistency.

For simplicity we formalize the core subset check: every `f(i)` appears
in the table.
-/

/-- A lookup table: a column of allowed values. -/
abbrev Table (m : ℕ) := Fin m → Pasta.Fp

/-- Lookup satisfaction: every witness value appears in the table. -/
def lookupSatisfied {n m : ℕ} (f : Column n) (table : Table m) : Prop :=
  ∀ i : Fin n, ∃ j : Fin m, f i = table j

/-- The lookup product check (simplified).

If there exists a mapping `w : Fin n → Fin m` such that `f(i) = table(w(i))`
for all `i`, then `∏ᵢ (γ + f(i)) = ∏ᵢ (γ + table(w(i)))`. -/
def lookupWitness {n m : ℕ} (f : Column n) (table : Table m)
    (w : Fin n → Fin m) : Prop :=
  ∀ i : Fin n, f i = table (w i)

/-- The lookup product for witness values. -/
def lookupProdF {n : ℕ} (f : Column n) (γ : Pasta.Fp) : Pasta.Fp :=
  ∏ i : Fin n, (γ + f i)

/-- The lookup product for table values via witness map. -/
def lookupProdT {n m : ℕ} (table : Table m) (w : Fin n → Fin m)
    (γ : Pasta.Fp) : Pasta.Fp :=
  ∏ i : Fin n, (γ + table (w i))

/-! ## Circuit examples

A circuit is a collection of gates and wire constraints that together
enforce a computation. We demonstrate with concrete examples.
-/

/-- A circuit for `c = a * b + d` using two rows:
    - Row 0: multiplication gate `a * b = intermediate`
    - Row 1: addition gate `intermediate + d = c`

    The wire connecting `intermediate` across rows is enforced by
    the permutation argument (column c row 0 = column a row 1). -/
def mulAddCircuit : Gate 2 where
  q_L := fun i => if i.val = 0 then 0 else 1
  q_R := fun i => if i.val = 0 then 0 else 1
  q_O := fun _ => -1
  q_M := fun j => if j.val = 0 then 1 else 0
  q_C := fun _ => 0

end

end Halo2
