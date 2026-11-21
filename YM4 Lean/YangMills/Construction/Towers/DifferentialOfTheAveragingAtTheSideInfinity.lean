import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfigurationDefs
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.FullSpace
def SmoothingDerivAtOneAllScales : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    SmoothingDerivAtOne L k j
end YangMills.Construction.Tower.FullSpace
