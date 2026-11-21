import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames WeightedResponses RenormalizationStepParameters StepSettings StepCosts
  TorusFields TorusLumps
namespace ResponseInTheExpansion
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
variable {m : ℕ}
def expOfColourForm {m : ℕ} (τ : ℝ) (A : TorusBond m → ℝ) : TorusField m :=
  fun x i => expUnit ((τ * A (x, i)) • unitGenerator)
def contourMeanSlope (L n : ℕ) (W : TorusBond (n * L) → ℝ) (c : TorusBond n) : ℝ :=
  deriv (fun τ : ℝ => -(contourAverage (readAtLevel (stepBlockFrame L n) 0 (expOfColourForm τ W))
    (torusSiteInFrame (stepBlockFrame L n) 1 c.1, c.2) * (unitGenerator : Quaternion ℝ)).re) 0
def chartRestriction (L u n : ℕ) [NeZero L] [NeZero n] (h : TorusBond (n * L) → ℝ) :
    ↥(chordBonds (finiteCells (torusFrame L u n))) → ℝ := fun b =>
  ∑ c : TorusBond (n * L),
    if (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth c.1, c.2) = b.1 then h c else 0
def stepHessianForm (a : ℝ) (L u n : ℕ) [NeZero L] [NeZero n] (h : TorusBond (n * L) → ℝ) : ℝ :=
  chartRestriction L u n h ⬝ᵥ Matrix.mulVec (trivialHessian a L u n) (chartRestriction L u n h)
def maxwellFormStepIdentityAt : Prop :=
  ∀ (u n : ℕ) [NeZero n], Tb.n₀ ≤ n → ∀ (W : TorusBond (n * (Tb.stepParameters y).side) → ℝ) (B : TorusBond n → ℝ),
    (∀ b, b ∉ chartBonds (Tb.stepParameters y).side n → W b = 0) →
    maxwellForm Tb.coupling (Tb.stepParameters y).side u W W +
        Tb.coupling * ∑ c : TorusBond n, (contourMeanSlope (Tb.stepParameters y).side n W c - B c) ^ 2 =
      maxwellForm Tb.coupling (Tb.stepParameters y).side (u + 1) B B +
        stepHessianForm Tb.coupling (Tb.stepParameters y).side u n
          (W - responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u B)
def maxwellFormStepIdentityStatement : Prop := HoldsOnParameterFamilies maxwellFormStepIdentityAt
end ResponseInTheExpansion
end YangMills.Construction
end
