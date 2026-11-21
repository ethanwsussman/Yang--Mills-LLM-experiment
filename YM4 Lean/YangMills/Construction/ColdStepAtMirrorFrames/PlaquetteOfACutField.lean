import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
open BlockOffsets
def fourPlaquette (a : Fin 4 → imaginaryQuaternions) : UnitQuaternion :=
  expUnit (a 0) * expUnit (a 1) * (expUnit (a 2))⁻¹ * (expUnit (a 3))⁻¹
def ScaledPlaquetteBound : Prop :=
  ∀ (a : Fin 4 → imaginaryQuaternions) (c : Fin 4 → ℝ), (∀ i, 0 ≤ c i ∧ c i ≤ 1) → ∑ i, ‖a i‖ ≤ 1 →
    distFromOne (fourPlaquette fun i => c i • a i) ≤
      c 0 * distFromOne (fourPlaquette a) + ∑ i, |c i - c 0| * ‖a i‖ + 4 * (∑ i, ‖a i‖) ^ 2
end ColdStepAtMirrorFrames
end YangMills.Construction
end
