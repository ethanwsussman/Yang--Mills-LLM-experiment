import YangMills.Construction.Lattice.StepSequencePaths
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def nonParallelStepCount (𝔞 : StepWord L m j) (f : UnitStepVec L m j) : ℕ :=
  open Classical in
  𝔞.countP fun s => decide ((s : Site L m j) ≠ f ∧ (s : Site L m j) ≠ -(f : Site L m j))
def HolonomyCommutesWithEqualSteps : Prop :=
  ∀ L m : ℕ, Odd L → 13 ≤ L → 0 < m → ∀ j : ℤ, -(m : ℤ) ≤ j →
    ∀ U : Bond L m j → Matrices.ComplexMatrix2, U ∈ compactGaugeFields L m j →
    ∀ (z : Site L m j) (𝔞 : StepWord L m j) (f : UnitStepVec L m j) (n : ℕ) (ω : ℝ), 0 ≤ ω →
      (∀ p : Plaquette L m j, p.vertices ⊆ partialSumSites z (𝔞 ++ List.replicate n f) →
        Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) ≤ ω) →
      Matrices.ComplexMatrix2.operatorNorm (wordHolonomy U z (𝔞 ++ List.replicate n f) -
          wordHolonomy U z (List.replicate n f ++ 𝔞)) ≤
        (n : ℝ) * (nonParallelStepCount 𝔞 f : ℝ) * ω
end YangMills.Construction.PeriodicLattice
