import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import YangMills.Construction.RunningCouplingSlope.TriplesOfTheChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def ChainFreeEnergyAnalytic.Claim : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    (∀ (N : ℕ) (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k),
      AnalyticAt ℝ (fun w => tripleFreeEnergy a (e w)) 0 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ w in 𝓝 (0 : Fin N → ℝ),
        ∀ v : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2,
          (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) →
          ((∀ x, Matrices.ComplexMatrix2.operatorNorm (v x - 1) < δ) ∨ ∀ x y, v x = v y) →
          ∀ (J' : LevelForms L n k) (μ' : Tower.edgeFormSpace L n k k),
            IsConjugatedCurrent v (e w).2.1 J' →
            (μ' : Tower.Edge L n k k → Matrices.ComplexMatrix2) =
              Tower.adjointForm (Tower.restrictVertexFunction k v)
                ((e w).2.2 : Tower.Edge L n k k → Matrices.ComplexMatrix2) →
            chainFreeEnergy a (gaugeTransformPoint v (expMove (e w).1 (unitPoint L n k))) J' μ' =
              tripleFreeEnergy a (e w)) ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
        ∀ W : Tower.Edge L n k k → Matrices.ComplexMatrix2, RepresentsTorusField W V →
        ∀ X : ChainPoint L n k, IsMinimizerOver a W X →
          ∃ (J : LevelForms L n k) (μ : Tower.edgeFormSpace L n k k),
            IsLevelGradient (chainAction a) X J ∧ IsTopMultiplier X J μ ∧ IsTopLevelGradient a W μ ∧
              SlopeCoefficient.chainLogarithm a ρ L k (2 * L ^ n) V =
                chainFreeEnergy a X J μ - chainFreeEnergy a (unitPoint L n k) 0 0
end YangMills.Construction.RunningCouplingSlope
end
