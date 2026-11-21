import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields BlockAverages
def plaquetteEdges {n : ℕ} (x : TorusSite n) (μ ν : Fin 4) : Fin 4 → TorusBond n :=
  ![(x, μ), (x + TorusFields.unitStep n μ, ν), (x + TorusFields.unitStep n ν, μ), (x, ν)]
def PlaquetteEnergySmoothBound : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ (n k : ℕ) (U : TorusField n) (x : TorusSite n) (μ ν : Fin 4) (b : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions),
    ContDiff ℝ ⊤ (fun s : Fin k → ℝ => plaquetteEnergy (perturb b X s U) x μ ν) ∧
    (k ≤ 3 → AreUnitVectors X → |mixedDeriv (fun V : TorusField n => plaquetteEnergy V x μ ν) U b X| ≤ M) ∧
    ∀ l, (∀ i, plaquetteEdges x μ ν i ≠ b l) → mixedDeriv (fun V : TorusField n => plaquetteEnergy V x μ ν) U b X = 0
end YangMills.Construction.WeightedResponses
end
