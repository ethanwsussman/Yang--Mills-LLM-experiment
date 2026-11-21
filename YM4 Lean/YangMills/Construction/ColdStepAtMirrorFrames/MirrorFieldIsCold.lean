import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ReflectedFieldSmallCurvature : Prop :=
  ∀ (F : BlockFrame) (m : ℕ) (y : F.Cell) (V : F.GaugeField F.top) (s : ℝ), 0 < m → IsSmallCurvature s V →
    IsSmallCurvature s (reflectedField m y V)
end YangMills.Construction.ColdStepAtMirrorFrames
end
