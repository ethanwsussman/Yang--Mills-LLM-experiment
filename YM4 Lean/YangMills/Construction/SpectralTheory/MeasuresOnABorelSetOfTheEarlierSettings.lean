import YangMills.Construction.SpectralTheory.PreliminarySettingsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SettingsComparison
def BorelSetMeasuresAgreeForAllSpaces : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (n : ℕ) (S : Set (Fin n → ℝ)), 1 ≤ n → MeasurableSet S → S.Nonempty →
      SettingsComparison.BorelSetMeasuresAgree E S
end YangMills.Construction.SettingsComparison
