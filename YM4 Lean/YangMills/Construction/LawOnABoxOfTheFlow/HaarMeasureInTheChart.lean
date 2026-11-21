import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields RenormalizationStepParameters BlockAverages ResponseInTheExpansion
variable {n : ℕ} [NeZero n]
def innerHaar (o : TorusSite n) (R : ℕ) : Measure (InnerField o R) := Measure.pi fun _ => haarUnit
def boxGaugeHaar (o : TorusSite n) (R : ℕ) : Measure ({z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) :=
  Measure.pi fun _ => haarUnit
open Classical in
def extendGaugeByOne {o : TorusSite n} {R : ℕ} (g : {z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) :
    TorusSite n → UnitQuaternion :=
  fun z => if h : z ∈ supBall o R then g ⟨z, h⟩ else 1
def gaugedChartField (o : TorusSite n) (R : ℕ) (A ζ : TorusBond n → imaginaryQuaternions)
    (g : {z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) : InnerField o R :=
  restrictInner o R (TorusFields.gaugeTransform (extendGaugeByOne g) (glueField (restrictOuter o R (exponentialField A))
    (fun b => toUnit (chartPoint (A b.1) (ζ b.1)))))
def chartChangeOfVariablesStatement : Prop :=
  ∀ Tb : ParameterAssignment, Tb.Admissible → ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∀ C₀ : ℝ, 0 < C₀ → ∃ K xs : ℝ,
    ∀ (x : ℝ) (R k n : ℕ) [NeZero n] (o : TorusSite n) (A : TorusBond n → imaginaryQuaternions),
      xs ≤ x → R = boxRadius κ₀ x → 16 * R < n → IsAxialSmall o R (boxScale x) A →
      ∃ (c : ℝ) (J : (TorusBond n → imaginaryQuaternions) → ℝ), 0 < c ∧ Measurable J ∧
        (∀ ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2), 0 < J ζ ∧
          |Real.log (J ζ)| ≤ K * ((R : ℝ) ^ 5 * boxScale x + (R : ℝ) ^ 6 * boxScale x ^ 2)) ∧
        Set.InjOn (fun p : ({z : TorusSite n // z ∈ supBall o R} → UnitQuaternion) × (TorusBond n → imaginaryQuaternions) =>
            gaugedChartField o R A p.2 p.1)
          (Set.univ ×ˢ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2)) ∧
        ∀ Φ : InnerField o R → ENNReal, Measurable Φ →
          ∫⁻ w in {w | ∃ g, ∃ ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2),
              w = gaugedChartField o R A ζ g}, Φ w ∂(innerHaar o R) =
            ENNReal.ofReal c * ∫⁻ g, ∫⁻ ζ in sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2),
              Φ (gaugedChartField o R A ζ g) * ENNReal.ofReal (J ζ) ∂(subspaceVolume (gaugeSlice o R A)) ∂(boxGaugeHaar o R)
end YangMills.Construction.BoxGaussian
end
