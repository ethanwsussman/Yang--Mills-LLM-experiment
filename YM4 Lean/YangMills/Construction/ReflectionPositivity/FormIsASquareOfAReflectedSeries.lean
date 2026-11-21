import YangMills.Construction.ReflectionPositivity.WeightsFormAndSeriesOfASplitTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open NormalFamilies
def ReflectionPairingIsIntegralSquare : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (Λ : PeriodSublattice 1) (v : AmbientSpace) (hv : v ∈ normalSet) (k : ℤ),
    Λ.SplitsAlongWithHalfPeriod v k → ∀ (c : ℝ) (hc : IsAllowedLevel 1 v c) (s : ℝ),
      let P : NormalLevelPair 1 := ⟨v, hv, c, hc⟩
      Λ.HasReflectionSeries k P
        (Λ.integrateOut (Λ.crossingLinks v k c)
          fun U => (Λ.splitFaceWeight β v k c U : ℂ)) s →
      ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
        (Φ : ↥(Λ.plusAlgebra v k c) →ₗ[ℂ] (X → ℂ)),
        IsFiniteMeasure μ ∧ (∀ G, Measurable (Φ G)) ∧
        (∀ G x, ‖Φ G x‖ ≤ PeriodSublattice.supNorm G.1) ∧
        ∀ G G', Λ.reflectionPairing β P G'.1 G.1 = ∫ x, conj (Φ G' x) * Φ G x ∂μ
end YangMills.Construction.InfiniteLattice
