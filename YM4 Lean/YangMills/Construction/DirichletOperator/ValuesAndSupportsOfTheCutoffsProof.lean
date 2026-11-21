import YangMills.Construction.DirichletOperator.DistanceToTheComplementAndTheCutsProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
open RegionSequence
namespace PartitionCubes.CutoffValues
variable {𝒮 : NestedRegions} {M : ℕ}
theorem norm_torusProj_le {S : ℝ} (v : Fin 4 → ℝ) : ‖Torus.torusProj 4 S v‖ ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.norm_torusProj_le <;> assumption
theorem supSetDist_singleton {S : ℝ} (x : Torus.PeriodicTorus 4 S)
    (A : Set (Torus.PeriodicTorus 4 S)) :
    Torus.supSetDist {x} A = Metric.infEDist x A := by apply _root_.YangMills.Construction.PartitionCubes.CubeFunctionDerivBounds.supSetDist_singleton <;> assumption
theorem mem_thicken_iff (Q : LevelCube 𝒮 M) (s : ℝ) (x : 𝒮.Point) :
    x ∈ Q.thicken s ↔
      Metric.infEDist x Q.supp ≤ ENNReal.ofReal (s * mollifyRadius 𝒮 M Q.level) := by
  simp only [LevelCube.thicken, mem_ofPred_eq, supSetDist_singleton]
theorem isClosed_thicken (Q : LevelCube 𝒮 M) (s : ℝ) : IsClosed (Q.thicken s) := by apply _root_.YangMills.Construction.PartitionCubes.CubeFunctionDerivBounds.isClosed_thicken <;> assumption
theorem mollifierScaled_eq_zero_of_lt_norm {r : ℝ} (hr : 0 < r) {v : Fin 4 → ℝ} (hv : r < ‖v‖) :
    mollifierScaled r v = 0 := by apply _root_.YangMills.Construction.PartitionCubes.OutsideDistanceAndCutoffs.mollifierScaled_eq_zero_of_lt_norm <;> assumption
theorem integral_mollifierScaled {r : ℝ} (hr : 0 < r) : ∫ v, mollifierScaled r v = 1 := by apply _root_.YangMills.Construction.PartitionCubes.SmoothedIndicatorBounds.integral_mollifierScaled <;> assumption
theorem mollifyRadius_pos {K m R₁ : ℕ} (hchain : 𝒮.IsLevelUnitChain K m M R₁) (n : ℕ) :
    0 < mollifyRadius 𝒮 M n := by
  have hL : 0 < (𝒮.L : ℝ) := by
    have h := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 0 < 𝒮.L)
  have hM : 0 < (M : ℝ) := by
    have h₁ := hchain.separated.blockSize_isPowerGe.1
    have h₂ := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 0 < M)
  exact div_pos (mul_pos hM (mul_pos (zpow_pos hL _) 𝒮.ξ_pos)) (mul_pos (by norm_num) hL)
end PartitionCubes.CutoffValues
end YangMills.Construction
