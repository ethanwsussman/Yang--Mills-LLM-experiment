import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.EuclideanFunctionals.MultiIndicesConvolutionsAndSeriesOfOperators
import YangMills.Construction.EuclideanFunctionals.OperatorsOverThePyramid
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
theorem SharpScale.sharpNorm_eq_max {E : Type*} [NormedAddCommGroup E] (s : SharpScale)
    (f : R4 → E) :
    s.sharpNorm f = max (TestFunctions.uniformNorm f) (40 * s.M * TestFunctions.lipConstR4 f) :=
  rfl
def Multiindex.twice (γ : Multiindex) : Multiindex := fun i => 2 * γ i
def smoothCompactSupp (X 𝕜 : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜] : Set (X → 𝕜) :=
  {g | ContDiff ℝ ∞ g ∧ HasCompactSupport g}
def l1Norm {X E : Type*} [MeasureSpace X] [NormedAddCommGroup E] (g : X → E) : ℝ :=
  ∫ x, ‖g x‖
abbrev upperOpenHalf (t : ℝ) : Set R4 := {x | t < x 3}
abbrev lowerHalf (t : ℝ) : Set R4 := {x | x 3 < t}
abbrev timeSlab (t : ℝ) : Set R4 := {x | |x 3| < t}
theorem isOpen_upperHalf (t : ℝ) : IsOpen (upperOpenHalf t) :=
  isOpen_lt continuous_const (continuous_apply 3)
def pyramidDomain : Set (Fin 4 → ℂ) := {w | 0 ≤ SpectralPoint.coneMargin w}
def IsHolomorphicFn {ν : ℕ} (U : Set (Coordinates.ComplexCoordinates ν))
    (g : Coordinates.ComplexCoordinates ν → ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U fun w _ => g w
def IsRealAnalyticFn {ν : ℕ} (U : Set (Coordinates.ComplexCoordinates ν))
    (g : Coordinates.ComplexCoordinates ν → ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsRealAnalyticIn (N' := 1) U fun w _ => g w
end YangMills.Construction.EuclideanFunctionals
