import YangMills.Construction.ColdChainAtEveryLevel.ComplexLevels
import YangMills.Construction.ColdChainAtEveryLevel.TotalAtAComplexTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def complexCellTermsAnalyticStatement : Prop :=
  ∀ (F : BlockFrame) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top) (a : ℝ), Odd F.blockSide →
    IsAdmissibleAmbient F →
    (∀ W : ComplexChainChart F, complexTotalOverTop a S R W (complexifyField V) = ∑ z ∈ S, complexCellTerms a S R W V z) ∧
    ∀ (m : ℕ) (W : (Fin m → ℂ) → ComplexChainChart F) (t₀ : Fin m → ℂ) (z : F.Cell) (t σ : ℝ), 0 ≤ t → t < 1 →
      σ ≤ 1 / 64 →
      8 * (F.blockSide : ℝ) * (YangMills.Construction.ComplexLevels.hullBondCount F.blockSide * t) ≤ 1 / 1024 →
      (∀ b ∈ innerBonds (cellBall S z 1) 0,
        AnalyticAt ℂ (fun w => complexifiedImaginary ((W w).re.fine b.1 b.2) ((W w).im.fine b.1 b.2)) t₀) →
      (∀ b ∈ innerBonds (cellBall S z 1) 0,
        ‖complexifiedImaginary ((W t₀).re.fine b.1 b.2) ((W t₀).im.fine b.1 b.2)‖ ≤ 1 / 16) →
      (∀ j, j + 1 < F.top → ∀ b ∈ innerBonds (cellBall S z 1) (j + 1),
        AnalyticAt ℂ (fun w => complexifiedImaginary ((W w).re.coarse j b.1 b.2) ((W w).im.coarse j b.1 b.2)) t₀) →
      (∀ j, j + 1 < F.top → ∀ b ∈ innerBonds (cellBall S z 1) (j + 1),
        ‖complexifiedImaginary ((W t₀).re.coarse j b.1 b.2) ((W t₀).im.coarse j b.1 b.2)‖ ≤ 1 / 16) →
      (∀ j, j < F.top → ∀ b ∈ innerBonds (cellBall S z 1) j,
        ‖YangMills.Construction.ComplexLevels.levelDeviation R (W t₀) j b.1 b.2‖ ≤ t) →
      (∀ j, j + 1 ≤ F.top → ∀ c ∈ innerBonds (cellBall S z 1) (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π,
        ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
          (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ) →
      AnalyticAt ℂ (fun w => complexCellTerms a S R (W w) V z) t₀
end YangMills.Construction.BlockAverages
end
