import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfigurationDefs
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
def AdmissiblePolydiscRadiusExists : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, IsAdmissiblePolydiscRadius L ρ
end YangMills.Construction.Tower
