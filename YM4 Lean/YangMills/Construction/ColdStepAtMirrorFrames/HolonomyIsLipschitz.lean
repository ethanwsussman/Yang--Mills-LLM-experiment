import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
def PathHolonomyLipschitz : Prop :=
  ∀ (F : BlockFrame) (j : ℕ) (X X' : F.GaugeField j) (ε : ℝ),
    (∀ x i, ‖((X x i : UnitQuaternion) : ℍ[ℝ]) - ((X' x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε) →
    ∀ (x : F.Site j) (l : List PathStep),
      ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) - ((pathHolonomy X' x l : UnitQuaternion) : ℍ[ℝ])‖ ≤
        l.length * ε
end YangMills.Construction.ColdStepAtMirrorFrames
end
