import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Parametrix
open scoped ContDiff
open EuclideanFunctionals TorusMetric TestFunctions MeasureTheory Filter Topology
def RationalKernelTendstoDelta : Prop :=
  ∀ φ : R4 → ℂ, Continuous φ → IsBoundedFun φ →
    Tendsto
      (fun ε : ℝ => ∫ x : R4,
        ((12 * ε ^ 3 / Real.pi ^ 2 * (euclidNormVec x ^ 2 + ε) ^ (-5 : ℤ) : ℝ) : ℂ) * φ x)
      (𝓝[>] 0) (𝓝 (φ 0))
end YangMills.Construction.Parametrix
end
