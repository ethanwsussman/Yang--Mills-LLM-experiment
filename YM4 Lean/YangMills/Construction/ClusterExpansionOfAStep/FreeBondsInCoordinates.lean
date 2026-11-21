import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.PotentialOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open TorusFields StepSettings ColdStepAtMirrorFrames
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
def axialTreeBonds (L : ℕ) [NeZero L] (A : Finset (TorusSite n)) : Finset (TorusBond (n * L)) :=
  Finset.univ.filter fun b => TorusLumps.parentBlock L b.1 ∈ A ∧
    BlockAverages.IsAxialTreeBond (F := TorusLumps.stepBlockFrame L n)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 0 b.1, b.2)
open Classical in
def _root_.YangMills.Construction.StepSettings.ChartSetting.glueOver (s : ChartSetting R n)
    (A : Finset (TorusSite n)) (W : TorusField (n * R.params.side)) : TorusField (n * R.params.side) :=
  fun x i => if (x, i) ∈ s.free ∨ (x, i) ∈ axialTreeBonds R.params.side A then W x i else s.fine x i
structure _root_.YangMills.Construction.StepSettings.ChartSetting.IsChartCover (s : ChartSetting R n)
    (A : Finset (TorusSite n)) : Prop where
  subset_chart : s.free ⊆ StepCosts.chartBonds R.params.side n
  mem_of_touching : ∀ b ∈ StepCosts.chartBonds R.params.side n,
    TorusLumps.parentBlock R.params.side b.1 ∈ A ∨
      TorusLumps.parentBlock R.params.side (b.1 + unitStep (n * R.params.side) b.2) ∈ A → b ∈ s.free
  fine_eq_one : ∀ b ∈ axialTreeBonds R.params.side A, s.fine b.1 b.2 = 1
def _root_.YangMills.Construction.StepSettings.ChartSetting.bondCutoff (s : ChartSetting R n)
    (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) : ℝ :=
  cutoffFactor R.ballRadius R.barrierFn
    ‖((StepCosts.chartCoord R.params s.coarse W b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) -
      ((s.frame b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖
def IsBlockGauge (L : ℕ) [NeZero L] (A : Finset (TorusSite n))
    (g : TorusSite (n * L) → BlockAverages.UnitQuaternion) : Prop :=
  (∀ x, TorusLumps.parentBlock L x ∉ A → g x = 1) ∧
    ∀ x, BlockAverages.cellOffset (F := TorusLumps.stepBlockFrame L n)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 0 x) = 0 → g x = 1
def HaarInChartCoordinates : Prop :=
  ∀ R : StepSetup, Odd R.params.side → IsCutoff R.ballRadius R.barrierFn →
    ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ (s : ChartSetting R n) (A : Finset (TorusSite n)), s.IsChartCover A →
      ∀ H : TorusField (n * R.params.side) → ENNReal, Measurable H →
        (∀ g, IsBlockGauge R.params.side A g → ∀ W, H (gaugeTransform g W) = H W) →
        ∫⁻ W, H (s.glueOver A W) * ∏ b : s.free, ENNReal.ofReal (s.bondCutoff (s.glueOver A W) b)
            ∂fieldHaar (n * R.params.side) =
          ∫⁻ η, H (s.field η) * ENNReal.ofReal (s.cutoffProduct η * s.haarJacobian η)
end ClusterExpansionOfAStep
end YangMills.Construction
end
