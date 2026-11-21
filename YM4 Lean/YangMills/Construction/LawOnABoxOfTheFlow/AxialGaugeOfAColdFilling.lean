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
def coldAxialGaugeStatement : Prop :=
  ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∃ xs : ℝ, ∀ (x : ℝ) (R n : ℕ) [NeZero n] (o : TorusSite n),
    xs ≤ x → R = boxRadius κ₀ x → 16 * R < n →
    ∃ (g : TorusField n → TorusSite n → UnitQuaternion) (A : TorusField n → TorusBond n → imaginaryQuaternions),
      let cold : Set (TorusField n) :=
        {V | ∀ p ∈ plaquettesIn (supBall o (2 * R)), curvature V p.1 p.2.1 p.2.2 ≤ boxScale x}
      Measurable (fun V : cold => g V) ∧ Measurable (fun V : cold => A V) ∧
      ∀ V ∈ cold, g V o = 1 ∧
        (∀ b ∈ bondsWithin (supBall o (2 * R)), gaugeTransform (g V) V b.1 b.2 = expUnit (A V b)) ∧
        IsAxialSmall o R (boxScale x) (A V)
end YangMills.Construction.BoxGaussian
end
