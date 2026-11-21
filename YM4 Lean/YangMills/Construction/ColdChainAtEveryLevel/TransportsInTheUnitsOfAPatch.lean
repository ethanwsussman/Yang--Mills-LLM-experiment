import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open YangMills.Construction.LatticeFractionalIntegration
def patchTransportStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide → IsAdmissibleAmbient F →
    1024 ≤ m → IsOrthantRegular S m →
    ∀ (s : ℝ) (V : F.GaugeField F.top), 0 ≤ s → IsCold S F.top s V → ∀ z ∈ S,
      (∀ v ∈ localCellIndex S z, ∀ v' ∈ localCellIndex S z, supNorm (v' - v) ≤ 3 →
        ‖(((GaugeMap.cellTransport S V z (localCell S z v))⁻¹ *
            cellParallelTransport S V (localCell S z v) (localCell S z v') *
            GaugeMap.cellTransport S V z (localCell S z v') : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ C * s) ∧
      ∀ i, z + unitStep F.top i ∈ S →
        ‖(((GaugeMap.cellTransport S V z z)⁻¹ * V z i *
            GaugeMap.cellTransport S V z (z + unitStep F.top i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ C * s
end YangMills.Construction.BlockAverages
end
