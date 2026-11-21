import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages
def borelOuterFillingStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (o : TorusSite n) (R : ℕ) (δ : ℝ), ∃ f : OuterField o R → InnerField o R,
    let F : Set (OuterField o R) := {u | ∃ w, ∀ p ∈ plaquettesIn (supBall o (2 * R)),
      curvature (glueField u w) p.1 p.2.1 p.2.2 ≤ δ}
    MeasurableSet F ∧ Measurable (fun u : F => f u) ∧
      ∀ u ∈ F, ∀ p ∈ plaquettesIn (supBall o (2 * R)), curvature (glueField u (f u)) p.1 p.2.1 p.2.2 ≤ δ
end YangMills.Construction.BoxGaussian
end
