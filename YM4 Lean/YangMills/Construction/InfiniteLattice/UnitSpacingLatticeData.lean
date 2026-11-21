import YangMills.Construction.ReflectionPositivity.AxisMirrorData
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace FixedSpacing
abbrev Params : Type := ReflectionPositivity.AxisMirror.MirrorData
section Functions
variable {X E : Type*}
def normSup [NormedAddCommGroup E] (F : X → E) : ℝ≥0∞ := ⨆ x, ‖F x‖ₑ
def continuousSet (X : Type*) [TopologicalSpace X] : Set (X → ℂ) := {F | Continuous F}
def IsBorelMeasurableFn [TopologicalSpace X] [TopologicalSpace E] (F : X → E) : Prop :=
  Measurable[borel X, borel E] F
end Functions
end FixedSpacing
end
end YangMills.Construction
