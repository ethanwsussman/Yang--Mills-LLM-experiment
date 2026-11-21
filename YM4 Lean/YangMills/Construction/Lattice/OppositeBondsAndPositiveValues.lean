import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices YangMills.Construction.Conventions
namespace OppositeBonds
variable {L m : ℕ} {j : ℤ}
def AxisSignRepresents (b : Bond L m j) (μ : Fin 4) (σ : ℤ) : Prop :=
  (b.target : FourTorus L m) - (b.source : FourTorus L m) =
    fun ν => (((σ : ℝ) * meshSize L j * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ν : ℝ) :
      AddCircle (torusSide L m))
def positiveBonds (ℬ : Set (Bond L m j)) : Set (Bond L m j) :=
  {b | b ∈ ℬ ∧ b.IsPositivelyOriented}
def gaugeFieldsOn (H : Set ComplexMatrix2) (ℬ : Set (Bond L m j)) : Set (ℬ → ComplexMatrix2) :=
  {V | ∃ U : Bond L m j → ComplexMatrix2, IsGaugeField H ℬ U ∧ ∀ b : ℬ, V b = U b}
def restrictToPositive (ℬ : Set (Bond L m j)) (V : ℬ → ComplexMatrix2) :
    positiveBonds ℬ → ComplexMatrix2 :=
  fun b => V ⟨b.1, b.2.1⟩
def familiesValuedIn (H : Set ComplexMatrix2) (ℬ : Set (Bond L m j)) :
    Set (positiveBonds ℬ → ComplexMatrix2) :=
  {g | ∀ b, g b ∈ H}
def OppositeAndPositiveRestriction : Prop :=
  ∀ (s : StandingParameters) (j : ℤ), -((s.m : ℕ) : ℤ) < j →
    (∀ b : Bond s.L s.m j,
      b.opposite.source = b.target ∧ b.opposite.target = b.source ∧ b.opposite.opposite = b ∧
        (∃! p : Fin 4 × ℤ, (p.2 = 1 ∨ p.2 = -1) ∧ AxisSignRepresents b p.1 p.2) ∧
        (∀ (μ : Fin 4) (σ : ℤ), (σ = 1 ∨ σ = -1) → AxisSignRepresents b μ σ →
          AxisSignRepresents b.opposite μ (-σ)) ∧
        Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) ∧
    ∀ (ℬ : Set (Bond s.L s.m j)) (H : Set ComplexMatrix2), IsReversalClosed ℬ →
      (H = compactGaugeGroup ∨ H = complexGaugeGroup) →
        Set.BijOn (restrictToPositive ℬ) (gaugeFieldsOn H ℬ) (familiesValuedIn H ℬ)
end OppositeBonds
end YangMills.Construction.PeriodicLattice
end
