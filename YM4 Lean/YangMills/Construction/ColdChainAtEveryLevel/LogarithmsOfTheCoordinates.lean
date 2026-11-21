import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesAtTheLevels
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
open Classical in
def unitQuaternionLog (g : UnitQuaternion) : ℍ[ℝ] :=
  if pureComponent (g : ℍ[ℝ]) = 0 then (if 0 ≤ (g : ℍ[ℝ]).re then 0 else ⟨0, Real.pi, 0, 0⟩)
  else (Real.arccos (g : ℍ[ℝ]).re / ‖pureComponent (g : ℍ[ℝ])‖) • pureComponent (g : ℍ[ℝ])
def levelCoordinate (R : F.FieldChain) (U : ChainChart F) (j : ℕ) : F.Site j → Fin 4 → ℍ[ℝ] :=
  fun x i => unitQuaternionLog (chartGap R U j x i)
def gaugedBondAverage (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) c
def bondAverageGap (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (c : F.Site (j + 1) × Fin 4) : UnitQuaternion :=
  polarUnit (gaugedBondAverage R U j c) * (polarUnit (contourAverage (R j) c))⁻¹
def bondAngle (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  unitQuaternionLog (bondAverageGap R U j c)
end YangMills.Construction.BlockAverages
end
