import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def LumpGridExists : Prop :=
  ∀ L : ℕ, 2 ^ 16 ≤ L → Nonempty (YangMills.Construction.LumpContours.LumpGrid L)
end YangMills.Construction.ColdStepAtMirrorFrames
end
