import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace StepSettings
open BlockAverages TorusFields TorusLumps
def coarseWeightSmoothStatement : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → 1 ≤ R.params.coupling * R.coupling →
    2 ^ 6 * (R.params.coupling + 1) ≤ R.params.derivBound → 0 < R.nextCoupling →
    R.coupling ≤ 1.01 * R.nextCoupling → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
    ∀ (V : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side),
      IsHullState R.params R.nextRange V Y → 0 < coarseWeightExpansion R n V Y ω →
      ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
        (∀ l, ∀ z ∈ Y, R.nextRange ≤ supDist (c l).1 z) →
        ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => coarseWeightExpansion R n (perturb c X σ V) Y ω) 0 ∧
        (1 ≤ k → k ≤ 3 → AreUnitVectors X →
          |mixedDeriv (fun V' => Real.log (coarseWeightExpansion R n V' Y ω)) V c X| ≤
            (R.params.derivBound * R.nextCoupling) ^ k)
end StepSettings
end YangMills.Construction
end
