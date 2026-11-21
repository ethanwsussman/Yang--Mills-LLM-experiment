import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def AxialFunctionAnalyticNearOne : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∃ 𝒰 : Set (Edge L n k i → Matrices.ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      𝒰 ⊆ axialFunctionDomain L n k i ∧ IsAnalyticFieldFunction 𝒰 (axialFunction L n k i)
end YangMills.Construction.Tower
end
