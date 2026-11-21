import YangMills.Construction.LimitsOfLatticeFamilies.TensorsOfSeparatedTuplesAndCentredFunctionals
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
def SepTensorsInFiniteBalls.Claim : Prop :=
  ∀ (s : Conventions.StandingParameters) (Y : ModelSpace), ∀ q, 1 ≤ q →
    (∀ F ∈ sepTensorsTop s Y q,
      ∃ ρ : ℝ, 0 < ρ ∧ F ∈ sepTensors s Y q (ENNReal.ofReal ρ)) ∧
    ∀ ρ ρ' : ℝ≥0∞, 0 < ρ → ρ ≤ ρ' → sepTensors s Y q ρ ≤ sepTensors s Y q ρ'
end YangMills.Construction.LatticeLimits
end
