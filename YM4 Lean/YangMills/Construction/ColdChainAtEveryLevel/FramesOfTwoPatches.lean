import YangMills.Construction.ColdChainAtEveryLevel.NormsOfFunctionsOnCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def patchFrameTransition (S : Finset F.Cell) (V : F.GaugeField F.top) (z z' : F.Cell) (x : F.Site 0) :
    UnitQuaternion :=
  (GaugeMap.frameChange S V z' x)⁻¹ * GaugeMap.frameChange S V z x
def patchFrameComparisonStatement : Prop :=
  ∃ (C c : ℝ) (L₁ : ℕ), 0 < C ∧ 0 < c ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide →
    L₁ ≤ F.blockSide → IsAdmissibleAmbient F →
    1024 ≤ m → IsOrthantRegular S m → ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
      ∀ z₀ ∈ S, ∀ z ∈ cellBall S z₀ 2, ∀ z' ∈ cellBall S z₀ 2, ∃ g : UnitQuaternion,
        (∀ y ∈ cellBall S z₀ 5, ∀ x ∈ cellSites S y,
          ‖((patchFrameTransition S V z z' x : UnitQuaternion) : ℍ[ℝ]) - (g : ℍ[ℝ])‖ ≤ C * s) ∧
        ∀ y ∈ cellBall S z₀ 5, ∀ y' ∈ cellBall S z₀ 5, ∀ x ∈ cellSites S y, ∀ (e : PathStep),
          x + stepDisplacement 0 e ∈ cellSites S y' →
          ‖((patchFrameTransition S V z z' x : UnitQuaternion) : ℍ[ℝ]) -
              ((patchFrameTransition S V z z' (x + stepDisplacement 0 e) : UnitQuaternion) : ℍ[ℝ])‖ ≤
            C * s / (GaugeMap.cellSideLength F : ℝ)
end YangMills.Construction.BlockAverages
end
