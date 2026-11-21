import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def chartGap (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (x : F.Site j) (i : Fin 4) : UnitQuaternion :=
  chartField R U j x i * (R j x i)⁻¹
def constOneWeights (F : BlockFrame) : F.SiteWeights := fun _ _ => 1
def chartShiftMulti {k : ℕ} (U : ChainChart F) (A : Fin k → ChainChart F) (t : Fin k → ℝ) :
    ChainChart F :=
  ⟨fun x i => U.fine x i + ∑ l, t l • (A l).fine x i, fun j y i => U.coarse j y i + ∑ l, t l • (A l).coarse j y i⟩
def zeroChart (F : BlockFrame) : ChainChart F := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
end BlockAverages
end YangMills.Construction
end
