import YangMills.Construction.TotalDensitiesGiveASystem.ConditionsOfTheMainStatement
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensities
def TrajectoryTopStatement : Prop :=
  ∃ J Lstar : ℕ, 1 ≤ J ∧ ∀ L : ℕ, Odd L → Lstar ≤ L →
    ∃ (ℓ : TorusLumps.StepParameters) (Bs c₅ γ : ℝ) (Nw : ℕ) (CT : ℝ),
    ℓ.side = L ∧ ℓ.baseDepth = J ∧ TotalDensitySystem.IsUnitMeshStepParameters ℓ ∧ 2 ≤ Bs ∧ 0 ≤ c₅ ∧
      γ ∈ Ioo (0 : ℝ) 1 ∧ 0 < CT ∧ 1 ≤ Nw ∧
      ∀ g ∈ Ioc 0 γ, TotalDensitySystem.CouplingConditions ℓ Bs c₅ (3 / 4 * TotalDensitySystem.oneLoopShift L) Nw CT g
end YangMills.Construction.TotalDensities
end
