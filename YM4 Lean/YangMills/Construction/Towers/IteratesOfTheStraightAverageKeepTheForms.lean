import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def CrossingSmoothingIterMapsForms : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n i : ℕ, 0 < n →
    ∀ B ∈ edgeFormSpace L n (i + 1) 0,
      crossingSmoothingIter L n (i + 1) i B ∈ edgeFormSpace L n (i + 1) i
end YangMills.Construction.Tower
end
