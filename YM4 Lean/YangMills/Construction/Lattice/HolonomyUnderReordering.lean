import YangMills.Construction.Lattice.StepSequencePaths
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def HolonomyReorderingBound : Prop :=
  ∀ L m : ℕ, Odd L → 13 ≤ L → 0 < m → ∀ j : ℤ, -(m : ℤ) ≤ j →
    ∀ U : Bond L m j → Matrices.ComplexMatrix2, U ∈ compactGaugeFields L m j →
    ∀ (z : Site L m j) (𝔰 𝔰' : StepWord L m j) (ω : ℝ),
      IsPermutationOf 𝔰' 𝔰 → 0 ≤ ω →
      (∀ p : Plaquette L m j, p.vertices ⊆ partialSumSites z 𝔰 →
        Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) ≤ ω) →
      Matrices.ComplexMatrix2.operatorNorm
          (wordHolonomy U z 𝔰' * (wordHolonomy U z 𝔰)⁻¹ - 1) ≤
        (1 + ω) ^ (𝔰.length * (𝔰.length - 1) / 2) - 1
end PeriodicLattice
end YangMills.Construction
