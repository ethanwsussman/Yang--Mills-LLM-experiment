import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import YangMills.Construction.RunningCouplingSlope.TriplesOfTheChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower
def FibreActionGaugeInvariant : Prop :=
  ∀ a : ℝ, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ X : ChainPoint L n k, IsCompactValued X →
      ∀ v : Vertex L n k 0 → Matrices.ComplexMatrix2, (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) →
        (∀ y : Vertex L n k k, restrictVertexFunction k v y = 1) →
        ∃ A : LevelForms L n k ≃ₗ[ℝ] LevelForms L n k, (∀ ξ, IsConjugatedCurrent v ξ (A ξ)) ∧
          ∀ (N : ℕ) (e : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k), ∀ᶠ w in 𝓝 (0 : Fin N → ℝ),
            chainAction a (fibreMove (gaugeTransformPoint v X) (A (e w))) =
              chainAction a (fibreMove X (e w))
end RunningCouplingSlope
end YangMills.Construction
end
