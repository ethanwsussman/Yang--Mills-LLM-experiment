import YangMills.Construction.ColdChainAtEveryLevel.NormsOfFunctionsOnCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
structure CellNormFamily (S : Finset F.Cell) (N₀ N₁ N₂ : (F.Site 0 → ℝ) → F.Cell → ℝ) (σ : F.Cell → ℝ) (C : ℝ) :
    Prop where
  isSeminorm_base : IsCellSeminorm S N₀
  isSeminorm_target : IsCellSeminorm S N₁
  isSeminorm_source : IsCellSeminorm S N₂
  base_le_target : ∀ f z, N₀ f z ≤ N₁ f z
  source_le : ∀ f z, N₂ f z ≤ C * (GaugeMap.cellSideLength F : ℝ) * N₀ f z
  kernel_le : ∀ z ∈ S, ∀ f y, N₁ (patchCubicKernel S z f) y ≤ C * ∑ x ∈ cellBall S z 20, N₂ (restrictToPatch S z f) x
  const_le : ∀ z, N₁ (fun _ => 1) z ≤ C * (GaugeMap.cellSideLength F : ℝ) * σ z
  mean_le : ∀ f z, σ z * ∑ x ∈ cellSites S z, |f x| ≤ C * (GaugeMap.cellSideLength F : ℝ) ^ 3 * N₀ f z
  scale_pos : ∀ z, 0 < σ z
  scale_le_of_near : ∀ y z, cellSupDist y z ≤ 22 → σ y ≤ C * σ z
  base_shift_le : ∀ (e : PathStep) f z, (∀ x, x ∉ sitesOfCells S 0 → f x = 0) →
    N₀ (fun x => f (x + stepDisplacement 0 e)) z ≤ C * ∑ y ∈ cellBall S z 1, N₀ f y
  target_shift_le : ∀ (e : PathStep) f z, (∀ x, x ∉ sitesOfCells S 0 → f x = 0) →
    N₁ (fun x => f (x + stepDisplacement 0 e)) z ≤ C * ∑ y ∈ cellBall S z 1, N₁ f y
def cellKernelBoundsStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide → IsAdmissibleAmbient F →
    1024 ≤ m → IsOrthantRegular S m →
    (∀ (φ : F.Cell → ℝ) (θ δ : ℝ) (p : F.Site 0), |θ| ≤ 1 / 8 → |δ| ≤ 1 / 8 →
      (∀ y y', |φ y - φ y'| ≤ |δ| * cellSupDist y y') →
      CellNormFamily S (weightedLpNormOnCell 4 S (classWeight F φ θ p 0))
        (fun f z => weightedLpNormOnCell 4 S (classWeight F φ θ p 0) f z +
          weightedLpNormOnCell 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x) f z)
        (weightedLpNormOnCell 2 S (classWeight F φ θ p 0)) (fun z => Real.exp (φ z)) C) ∧
    CellNormFamily S (weightedLpNormOnCell 3 S (fun _ => 1)) (weightedLpNormOnCell 3 S (fun _ => 1))
      (weightedLpNormOnCell (12 / 7) S (fun _ => 1)) (fun _ => (GaugeMap.cellSideLength F : ℝ) ^ ((1 : ℝ) / 3)) C
end BlockAverages
end YangMills.Construction
end
