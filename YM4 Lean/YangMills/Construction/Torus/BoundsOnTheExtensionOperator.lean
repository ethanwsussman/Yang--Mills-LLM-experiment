import YangMills.Construction.Torus.InverseOfTheCompressedGreenOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace HarmonicExtBounds
open SeparatedSequences GreenBounds
variable {L : ℕ}
def coarseDecay (K : GreenConstants) (s : LevelUnitChain L) (y : s.data.Space)
    (c : s.setting.CoarseBond) : ℝ :=
  Real.exp (-halfInverseDecayRate 4 L K.rate K.bound *
    GaugeSetting.siteCoarseDist (W := s.setting) y c)
structure Conclusion (K : GreenConstants) (s : LevelUnitChain L) : Prop where
  wellPosed : s.setting.WellPosed
  expansion : ∀ (B : s.setting.CoarseField) (b : ↥s.setting.bondSet),
    (s.setting.harmonicExt B).1 b.1 = ∑ᶠ c, s.setting.harmonicExtKernel b c * B c
  kernel_le : ∀ y ∈ s.chain.shellSitesUnion, ∀ c : s.setting.CoarseBond,
    ∀ b : ↥s.setting.bondSet, s.chain.LiesInCell b.1 y →
      |s.setting.harmonicExtKernel b c| ≤
        fieldKernelConstant 4 L K.rate K.bound * coarseDecay K s y c
  grad_le : ∀ y ∈ s.chain.shellSitesUnion, ∀ c : s.setting.CoarseBond,
    ∀ x : s.data.BaseSite, (x : s.data.Space) ∈ s.chain.localCube y → ∀ μ ν : Fin 4,
      |s.grad (s.setting.harmonicExt (s.setting.coarseDelta c)).1 x μ ν| ≤
        fieldKernelConstant 4 L K.rate K.bound * (s.chain.localSpacing y)⁻¹ *
          coarseDecay K s y c
  holder_le : ∀ y ∈ s.chain.shellSitesUnion, ∀ c : s.setting.CoarseBond, ∀ α : ℝ, 0 ≤ α →
    α < 1 → ∀ ζ : s.data.Space → ℂ, s.IsSmoothSupportedInDoubleCube y ζ →
      ∀ path, IsGeodesicChoice s.scales path →
        s.cutoffGradSeminorm α ζ (s.setting.harmonicExt (s.setting.coarseDelta c)).1 path ≤
          ENNReal.ofReal (fieldKernelConstant 4 L K.rate K.bound *
              (K.holderBound α / K.bound) * s.chain.localSpacing y ^ (-1 - α) *
              coarseDecay K s y c) *
            s.cutoffSize α (s.chain.localSpacing y) ζ
end HarmonicExtBounds
def HarmonicExtBounds.Statement : Prop :=
  ∀ L : ℕ, Blocking.DimFourOddBlockingFactorGeThirteen 4 L →
    ∀ s : GreenBounds.LevelUnitChain L,
      CoarseGreenInverse.AboveThresholds (GreenBounds.chosen L) s →
        HarmonicExtBounds.Conclusion (GreenBounds.chosen L) s
end YangMills.Construction.GeneralTorus
