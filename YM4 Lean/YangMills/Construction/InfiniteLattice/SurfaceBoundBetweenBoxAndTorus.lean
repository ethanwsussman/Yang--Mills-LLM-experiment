import YangMills.Construction.Constants.BoxTorusNumbers
import YangMills.Construction.InfiniteLattice.DataOfTheComparisonOfABoxWithATorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def boxCoverNumber (ϱ : ℕ+) : ℕ := ((ϱ : ℕ) + 1) ^ 4 + 1
namespace BoxTorusSurfaceBound
def Holds (d : BoxTorusComparisonData) (β : ℝ) : Prop :=
  (∀ x : LatticePoint 1, {z : LatticePoint 1 | x ∈ siteCube z d.boxWidth}.ncard + 1 = boxCoverNumber d.boxWidth) ∧
  (boxCoverNumber d.boxWidth : ℝ) ≤ (Constants.BoxTorus.anchorNumber : ℝ) * ((d.boxWidth : ℕ) : ℝ) ^ 4 ∧
  ∀ W : LinkWindow 1, (W.links : Set (Link 1)) = d.normalFrame.boxLinks d.sideLengths →
    (∀ (t : ℝ) (V : GaugeField 1),
      |Real.log (d.obsArray.windowPartition β t W V) -
          Real.log (d.obsArray.tiltedPartition d.periodSublattice β t)| ≤
        (Constants.BoxTorus.surfaceNumber : ℝ) * (β + |t| * observableSupNorm d.obs) *
          (boxCoverNumber d.boxWidth : ℝ) * ((d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard : ℝ)) ∧
    |((d.obsArray.labelsTouching W).ncard : ℝ) -
        d.obsArray.invIndex * ((d.normalFrame.fundamentalBox d.sideLengths).ncard : ℝ)| ≤
      (boxCoverNumber d.boxWidth : ℝ) * ((d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard : ℝ)
def AllData : Prop := ∀ (d : BoxTorusComparisonData) (β : ℝ), 0 < β → Holds d β
end BoxTorusSurfaceBound
end YangMills.Construction.InfiniteLattice
