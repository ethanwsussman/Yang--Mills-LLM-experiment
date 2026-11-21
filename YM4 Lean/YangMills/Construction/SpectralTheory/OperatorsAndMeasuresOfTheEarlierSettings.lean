import YangMills.Construction.SpectralTheory.PreliminarySettingsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SettingsComparison
def AllSettingsAgree : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E],
    SettingsComparison.BoundedOpsAgree E ∧ SettingsComparison.UnboundedOpsAgree E ∧
      (∀ (n : ℕ) (S : Set (Fin n → ℝ)), 1 ≤ n → MeasurableSet S → S.Nonempty →
        SettingsComparison.BorelSetMeasuresAgree E S) ∧
      (∀ (n : ℕ) [NeZero n], SettingsComparison.FullSpaceMeasuresAgree E n) ∧
      SettingsComparison.SpectralMeasuresAgree E ∧ SettingsComparison.CommutingBoundedOpsAgree E
end YangMills.Construction.SettingsComparison
