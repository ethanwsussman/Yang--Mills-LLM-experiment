import YangMills.Construction.ReflectionPositivity.WeightsFormAndSeriesOfASplitTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.NormalFamilies
def CrossingIntegralReflectionSeriesInteger : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (Λ : PeriodSublattice 1) (n : AmbientSpace) (hn : n ∈ normalSet) (z : ℤ),
    Λ.SplitsAlongWithHalfPeriod n z → ∀ (c : ℝ) (hc : IsAllowedLevel 1 n c),
      (∃ k : ℤ, c = (k : ℝ)) →
      let P : NormalLevelPair 1 := ⟨n, hn, c, hc⟩
      Λ.HasReflectionSeries z P
        (Λ.integrateOut (Λ.crossingLinks n z c)
          fun U => (Λ.splitFaceWeight β n z c U : ℂ))
        (Real.exp (β * (Λ.numSplitPlaquettes n z c : ℝ)))
end YangMills.Construction.InfiniteLattice
