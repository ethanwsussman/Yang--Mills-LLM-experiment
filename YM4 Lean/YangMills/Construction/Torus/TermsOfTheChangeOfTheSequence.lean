import YangMills.Construction.SeparatedSequences.InverseExpansionCutoff
import YangMills.Construction.Torus.CompressionOfTheCutOperatorToACube
import YangMills.Construction.Torus.GreenOperatorBoundsOnTheTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace GeneralTorus.CubeGaugeSetting
variable (C : CubeGaugeSetting) (Q : C.data.CubeIndex)
def changeBonds : Set C.CoarseBond :=
  {c₁ | (∃ e : (C.localSetting Q).CoarseBond, GaugeSetting.levelBond e = GaugeSetting.levelBond c₁) ∧
    (ScaleData.bondSupport c₁.2.1 ∩ ScaleData.scaledCube Q (5 / 3)).Nonempty ∧
    ∃ x : C.data.BaseSite, (x : C.data.Space) ∈ ScaleData.bondSupport c₁.2.1 ∧
      (x : C.data.Space) ∉ ScaleData.scaledCube Q (4 / 3)}
def bondMeanAt (c₁ : C.CoarseBond) (F : C.data.BondField) : ℝ :=
  C.data.blockBondMean c₁.1 F c₁.2.1
def cutoffShift (c₁ : C.CoarseBond) : C.data.SiteField :=
  fun x => ScaleData.cutoffFn Q x - ScaleData.cutoffFn Q (GaugeSetting.coarseAnchor c₁)
def changeTerm (A A' : C.data.BondField) (c₁ : C.CoarseBond) : ℝ :=
  C.mass * GaugeSetting.coarseSpacing c₁ ^ 2 *
    (C.bondMeanAt c₁ A * C.bondMeanAt c₁ (C.data.bondMul (C.cutoffShift Q c₁) A') -
      C.bondMeanAt c₁ (C.data.bondMul (C.cutoffShift Q c₁) A) *
        C.bondMeanAt c₁ A')
def ChangeAboveThresholds : Prop :=
  (GreenBounds.chosen C.data.L).blockLower ≤ (C.data.blockCount : ℝ) ∧
    SeparatedSequences.gapBlockThreshold 4 C.data.L
        (GreenBounds.chosen C.data.L).rate
        (GreenBounds.chosen C.data.L).bound
        (GreenBounds.chosen C.data.L).gapLower ≤
      (C.data.gapCount : ℝ) * (C.data.blockCount : ℝ)
def changeBound (c c'' : C.CoarseBond) : ℝ :=
  SeparatedSequences.cubeOperatorChangeConstant 4 C.data.L
      (GreenBounds.chosen C.data.L).rate
      (GreenBounds.chosen C.data.L).bound *
    (C.data.L : ℝ) ^ (2 * 4 + 5) *
    SeparatedSequences.expSumConstant 4 C.data.L
      ((GreenBounds.chosen C.data.L).rate / 2) *
    (C.data.blockCount : ℝ)⁻¹ *
    Real.exp (-(GreenBounds.chosen C.data.L).rate * (C.data.blockCount : ℝ) /
      (4 * (C.data.L : ℝ))) *
    Real.exp (-(1 / 2) * (GreenBounds.chosen C.data.L).rate *
      GaugeSetting.coarseDist c c'')
def changeSites : Set C.data.Space :=
  {y | y ∈ C.chain.shellSitesUnion ∧ C.chain.localSpacing y ≤ C.data.levelSpacing (Q.1 + 1) ∧
    7 / 6 * ScaleData.cubeScale Q ≤ torusSupNorm (y - Q.2) ∧
      torusSupNorm (y - Q.2) ≤ 2 * ScaleData.cubeScale Q}
def changeSiteSum (c c'' : C.CoarseBond) : ℝ :=
  ∑ᶠ y ∈ C.changeSites Q, C.chain.localSpacing y ^ 7 *
    Real.exp (-(GreenBounds.chosen C.data.L).rate * GaugeSetting.siteCoarseDist y c) *
    Real.exp (-(GreenBounds.chosen C.data.L).rate * GaugeSetting.siteCoarseDist y c'')
end GeneralTorus.CubeGaugeSetting
end YangMills.Construction
