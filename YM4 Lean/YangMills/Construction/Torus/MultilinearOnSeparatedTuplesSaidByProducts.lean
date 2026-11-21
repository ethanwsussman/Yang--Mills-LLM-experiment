import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
noncomputable section
namespace YangMills.Construction.AmbientPoints
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
def IsMultilinearOnSeparated (φ : separatedTuples s E n → ℝ) : Prop :=
  TupleForm.IsMultilinear fun f => ((φ f : ℝ) : ℂ)
def MultilinearOnSeparatedIffProducts : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : Ambient) (n : ℕ), 1 ≤ n →
    ∀ φ : separatedTuples s E n → ℝ,
    IsMultilinearOnSeparated φ ↔ IsTupleMultilinear φ
end YangMills.Construction.AmbientPoints
end
