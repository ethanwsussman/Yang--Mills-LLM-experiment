import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def AnalyticSubmanifoldScaling : Prop :=
  ∀ (L n k j : ℕ) (hL : 0 < L) (hj : j ≤ k), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ l ≤ j, ∀ N : Set (Edge L n k l → Matrices.ComplexMatrix2), IsAnalyticFieldSubmanifold N →
      IsAnalyticFieldSubmanifold (transportTotal (scaleEdge hL hj l) '' N)
end YangMills.Construction.Tower
end
