import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
open scoped Quaternion in
def adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) : imaginaryQuaternions :=
  ⟨(g : ℍ[ℝ]) * (X : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]), by
    have hX : (X : ℍ[ℝ]).re = 0 := X.2
    show ((g : ℍ[ℝ]) * (X : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = 0
    have hs : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
    rw [hs]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, hX]
    ring⟩
def minimalOffset (Y z : F.Cell) : Fin 4 → ℤ := fun i => ((z - Y) i).valMinAbs
def axialGaugeHolonomy (V : F.GaugeField F.top) (Y z : F.Cell) : UnitQuaternion :=
  pathHolonomy V Y (axisPath (minimalOffset Y z) 1)
def axialGaugeRotated {k : ℕ} (V : F.GaugeField F.top) (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) : Fin k → imaginaryQuaternions :=
  fun l => adjointAction (axialGaugeHolonomy V Y (c l).1) (X l)
end YangMills.Construction.ColdStepAtMirrorFrames
end
