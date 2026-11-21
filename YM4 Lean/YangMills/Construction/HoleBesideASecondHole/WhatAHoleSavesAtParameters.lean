import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.HoleBesideASecondHole.TheInequalityOfAHoleAsRead
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace HoleBounds
open BlockAverages LumpContours
def WorkingBoundsFromThresholds : Prop :=
  ∀ {L : ℕ} (g : LumpGrid L) (a κ s cE c₁ c₂ : ℝ) (J₀ : ℕ), Odd L → 0 ≤ a → 0 < κ → 0 < s → 0 ≤ cE →
    cE ≤ c₁ → cE ≤ c₂ →
    (∀ (F : BlockFrame) (S : Finset F.Cell) (V : F.GaugeField F.top), F.blockSide = L → IsAdmissibleAmbient F →
      IsOrthantRegular S 2047 → IsCold S F.top s V → ∃ ρ N₀ : ℝ, HasColdMinimizer a ρ N₀ s S V) →
    RenormalizationStepParameters.HoleSavingAt g a κ 1 s c₁ J₀ → RenormalizationStepParameters.HoleSavingAt g a κ (9 / 8) s c₂ J₀ →
    HoleSavingWorkingBounds g a κ s cE J₀
end HoleBounds
end YangMills.Construction
end
