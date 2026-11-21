import YangMills.Construction.SeparatedSequences.InverseGreenConstants
import YangMills.Construction.Torus.GreenOperatorBoundsOnTheTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace CoarseGreenInverse
variable {L : ℕ}
def AboveThresholds (c : GreenBounds.GreenConstants) (q : GreenBounds.LevelUnitChain L) : Prop :=
  max c.blockLower (L : ℝ) ≤ (q.data.blockCount : ℝ) ∧
    SeparatedSequences.gapBlockThreshold 4 L c.rate c.bound c.gapLower ≤
      (q.data.gapCount : ℝ) * (q.data.blockCount : ℝ)
structure Conclusion (c : GreenBounds.GreenConstants) (q : GreenBounds.LevelUnitChain L) : Prop where
  symmetric : ∀ f g : q.setting.CoarseField,
    q.setting.coarseInner (q.setting.coarseGreen f) g =
      q.setting.coarseInner f (q.setting.coarseGreen g)
  pos : ∀ f : q.setting.CoarseField, f ≠ 0 →
    0 < q.setting.coarseInner f (q.setting.coarseGreen f)
  isUnit : IsUnit q.setting.coarseGreen
  matrixEntry_bound : ∀ b b' : q.setting.CoarseBond,
    |q.setting.matrixEntry (Ring.inverse q.setting.coarseGreen) b b'| ≤
      2 * (SeparatedSequences.compressedGreenLowerBound 4 1)⁻¹ *
        (GaugeSetting.coarseSpacing b)⁻¹ * (GaugeSetting.coarseSpacing b')⁻¹ *
        Real.exp (-SeparatedSequences.inverseDecayRate 4 L c.rate c.bound *
          GaugeSetting.coarseDist b b')
  kernelEntry_bound : ∀ b b' : q.setting.CoarseBond,
    |q.setting.kernelEntry (Ring.inverse q.setting.coarseGreen) b b'| ≤
      SeparatedSequences.inverseKernelConstant 4 L * (GaugeSetting.coarseSpacing b ^ 2)⁻¹ *
        Real.exp (-(1 / 2 * SeparatedSequences.inverseDecayRate 4 L c.rate c.bound) *
          GaugeSetting.coarseDist b b')
end CoarseGreenInverse
def CoarseGreenInverse.Statement : Prop :=
  ∀ L : ℕ, Blocking.DimFourOddBlockingFactorGeThirteen 4 L →
    ∀ q : GreenBounds.LevelUnitChain L,
      CoarseGreenInverse.AboveThresholds (GreenBounds.chosen L) q →
        CoarseGreenInverse.Conclusion (GreenBounds.chosen L) q
end YangMills.Construction.GeneralTorus
