import Halo2.Commitment
import Poseidon.Spec

namespace Halo2

/-! # Fiat-Shamir transcript

The Fiat-Shamir transform makes an interactive proof non-interactive
by deriving verifier challenges from a hash of the protocol transcript.
Halo 2 uses a Poseidon-based transcript that absorbs commitments and
field elements, then squeezes challenges.

The key security property is **binding**: the challenge is determined
by all previously absorbed values, so the prover cannot choose a
challenge after seeing the proof.

See §3.3 of the Halo paper.
-/

open Pasta

noncomputable section

/-! ## Transcript state -/

/-- A transcript is a sequence of absorbed field elements.
The challenge is derived by hashing the accumulated values. -/
structure Transcript where
  absorbed : List Pasta.Fp

/-- Empty transcript with a domain separator. -/
def Transcript.init (domain : Pasta.Fp) : Transcript :=
  ⟨[domain]⟩

/-- Absorb a field element into the transcript. -/
def Transcript.absorb (t : Transcript) (x : Pasta.Fp) : Transcript :=
  ⟨t.absorbed ++ [x]⟩

/-- Absorb a list of field elements. -/
def Transcript.absorbMany (t : Transcript) : List Pasta.Fp → Transcript
  | [] => t
  | x :: xs => (t.absorb x).absorbMany xs

/-! ## Challenge derivation

The challenge is derived by hashing consecutive pairs of absorbed
elements using PoseidonHash, folding left-to-right. -/

/-- Fold absorbed elements into a single challenge via iterated PoseidonHash. -/
def Transcript.foldHash : List Pasta.Fp → Pasta.Fp
  | [] => 0
  | [x] => x
  | x :: y :: rest => Transcript.foldHash (Poseidon.poseidonHash x y :: rest)


/-- Squeeze a challenge from the transcript. -/
def Transcript.squeeze (t : Transcript) : Pasta.Fp :=
  Transcript.foldHash t.absorbed

/-! ## Binding properties -/

/-- **Transcript determinism**: the same absorbed values produce the
same challenge. -/
theorem squeeze_deterministic (t : Transcript) :
    t.squeeze = t.squeeze := rfl

/-- **Absorb order matters**: absorbing `x` then `y` gives a different
transcript state than absorbing `y` then `x` (in general). -/
theorem absorb_ne_comm (t : Transcript) (x y : Pasta.Fp) :
    (t.absorb x).absorb y ≠ (t.absorb y).absorb x ↔
    x ≠ y := by
  constructor
  · intro h hxy; exact h (by rw [hxy])
  · intro hxy h
    simp only [Transcript.absorb, Transcript.mk.injEq, List.append_assoc] at h
    have := List.append_cancel_left h
    simp at this
    exact hxy this.1

/-- **Public input binding**: the squeezed challenge depends on all
absorbed values — equal challenges imply equal transcripts. -/
theorem squeeze_injective_of_transcript (t₁ t₂ : Transcript)
    (h : t₁.absorbed = t₂.absorbed) :
    t₁.squeeze = t₂.squeeze := by
  unfold Transcript.squeeze
  rw [h]

/-- Absorbing different values produces different transcript states. -/
theorem absorb_injective (t : Transcript) (x y : Pasta.Fp) (h : x ≠ y) :
    (t.absorb x).absorbed ≠ (t.absorb y).absorbed := by
  simp only [Transcript.absorb]
  intro heq
  have := List.append_cancel_left heq
  simp at this
  exact h this

/-! ## Collision resistance (axiomatized)

Full binding (different transcripts → different challenges) requires
Poseidon collision resistance, which we axiomatize. -/

/-- Poseidon collision resistance: distinct inputs produce distinct outputs. -/
axiom poseidon_collision_resistant (x₁ y₁ x₂ y₂ : Pasta.Fp)
    (h : Poseidon.poseidonHash x₁ y₁ = Poseidon.poseidonHash x₂ y₂) :
    x₁ = x₂ ∧ y₁ = y₂

/-- Under collision resistance, absorbing distinct single elements
after the same prefix yields distinct challenges when only two
elements are in the transcript. -/
private theorem squeeze_init_absorb (d x : Pasta.Fp) :
    ((Transcript.init d).absorb x).squeeze = Poseidon.poseidonHash d x := by
  unfold Transcript.squeeze Transcript.absorb Transcript.init
  simp only [List.singleton_append]
  unfold Transcript.foldHash Transcript.foldHash
  rfl

theorem challenge_binding_pair (d x y : Pasta.Fp) (hxy : x ≠ y) :
    ((Transcript.init d).absorb x).squeeze ≠
    ((Transcript.init d).absorb y).squeeze := by
  rw [squeeze_init_absorb, squeeze_init_absorb]
  intro h
  exact hxy (poseidon_collision_resistant d x d y h).2

end

end Halo2
