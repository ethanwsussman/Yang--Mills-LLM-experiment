import YangMills.Construction.ColdStepAtMirrorFrames.JetOfAFunctionOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def CriticalAtExactFit : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell) (k : ℕ) (W : F.GaugeField k) (V : F.GaugeField (k + 1)), 0 ≤ a →
    ContDiffThreeAlongBonds (minimalAction a S (k + 1)) V →
    minimalAction a S (k + 1) V = minimalAction a S k W →
    (∀ c : F.Site (k + 1) × Fin 4, ∃ ρ : ℝ, 0 < ρ ∧ contourAverage W c = ρ • ((V c.1 c.2 : UnitQuaternion) : Quaternion ℝ)) →
    HasFDerivAt (formComposition (innerBonds S (k + 1)) (minimalAction a S (k + 1)) V)
      (0 : (↥(innerBonds S (k + 1)) → imaginaryQuaternions) →L[ℝ] ℝ) 0
end YangMills.Construction.ColdStepAtMirrorFrames
end
