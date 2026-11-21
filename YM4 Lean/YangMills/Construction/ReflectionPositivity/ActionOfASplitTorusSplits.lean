import YangMills.Construction.ReflectionPositivity.WeightsFormAndSeriesOfASplitTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.NormalFamilies
def SplitTorusActionSplits : Prop :=
  ∀ (Γ : PeriodSublattice 1) (n : AmbientSpace) (hn : n ∈ normalSet) (z : ℤ),
    Γ.SplitsAlongWithHalfPeriod n z → ∀ (c : ℝ) (hc : IsAllowedLevel 1 n c),
      let P : NormalLevelPair 1 := ⟨n, hn, c, hc⟩
      ∃ A₀ Aplus : Γ.QuotientField → ℝ,
        Continuous A₀ ∧ Continuous Aplus ∧ (∀ U, 0 ≤ A₀ U) ∧ (∀ U, 0 ≤ Aplus U) ∧
        PeriodSublattice.DependsOnlyOn A₀ (Γ.sharedLinks n z c) ∧
        PeriodSublattice.DependsOnlyOn Aplus (Γ.plusLinks n z c) ∧
        ∀ (β : ℝ) (U : Γ.QuotientField),
          Γ.boltzmannWeight β U =
            Real.exp (-β * A₀ U) * Real.exp (-β * Aplus U) *
              Real.exp (-β * Γ.compPullback P.reflectSymmetry Aplus U) *
                Γ.splitFaceWeight β n z c U
end YangMills.Construction.InfiniteLattice
