import YangMills.Construction.Lattice.PlaquetteFunctionsAndTheLatticeIntegral
import YangMills.Construction.Lattice.RingsAndRingKernels
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Tuples
variable {L m : ℕ} {k : ℤ}
def edgesOfRing {n : ℕ} {J : Type*} (R : Set (Fin n → J)) : Set (Sym2 J) :=
  {e | ∃ σ ∈ R, e ∈ cyclicEdges σ}
theorem edgesOfRing_ringClass {n : ℕ} {J : Type*} (σ : Fin n → J) :
    edgesOfRing (ringClass σ) = cyclicEdges σ := by
  ext e
  constructor
  · rintro ⟨σ', hσ', he⟩
    rwa [cyclicEdges_eq_of_mem_ringClass hσ'] at he
  · exact fun he => ⟨σ, Or.inl (mem_rotationClass_self σ), he⟩
def pairKernel {n : ℕ} (C : Plaquette L m k → Plaquette L m k → ℝ)
    (hC : IsSymmetricKernel C) (p : Fin n → Plaquette L m k) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun a b => C (p a) (p b), fun _ _ => hC _ _⟩
def RingsOfOrderThreeFourAndKernels : Prop :=
  ((∃! R : Set (Fin 3 → Fin 3), IsRingOfTuples R) ∧
    {R : Set (Fin 4 → Fin 4) | IsRingOfTuples R}.ncard = 3 ∧
    {R : Set (Fin 4 → Fin 4) | IsRingOfTuples R} = Set.range standardFourRing) ∧
  (∀ R : Set (Fin 4 → Fin 4), IsRingOfTuples R →
    ∃ τ τ' : Equiv.Perm (TailPosition 4), τ ≠ τ' ∧
      {σ : Equiv.Perm (TailPosition 4) | ringClass (fixFirst σ) = R} = {τ, τ'} ∧
      rotationClass (fixFirst τ') = reversedSet (rotationClass (fixFirst τ))) ∧
  (∀ (L m : ℕ) (k : ℤ) (C : Plaquette L m k → Plaquette L m k → ℝ)
      (hC : IsSymmetricKernel C) (φ : Fin 4 → Plaquette L m k → ℝ),
    (∀ i, IsBoundedPlaquetteFunction (φ i)) →
    cyclicKernel C φ =
      ∑ᶠ R : {R : Set (Fin 4 → Fin 4) // IsRingOfTuples R}, ∑ᶠ p : Fin 4 → Plaquette L m k,
        (∏ i, φ i (p i)) * ∏ᶠ e ∈ edgesOfRing R.1, pairKernel C hC p e) ∧
  (∀ (L m : ℕ) (k : ℤ) (C : Plaquette L m k → Plaquette L m k → ℝ),
    IsSymmetricKernel C → ∀ φ : Fin 2 → Plaquette L m k → ℝ,
    (∀ i, IsBoundedPlaquetteFunction (φ i)) →
    2 * cyclicKernel C φ =
      ∑ᶠ x : Plaquette L m k × Plaquette L m k, φ 0 x.1 * φ 1 x.2 * C x.1 x.2 ^ 2)
end YangMills.Construction.PeriodicLattice
