import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.RotationNotation
abbrev Point4 : Type := Fin 4 → ℝ
abbrev Point3 : Type := Fin 3 → ℝ
abbrev STuple : Type := TestSpaces.SepTuple
inductive SpaceTag where
  | real
  | realReal
  | r3
  | realR3
namespace SpaceTag
abbrev Pts : SpaceTag → Type
  | real => ℝ
  | realReal => ℝ × ℝ
  | r3 => Point3
  | realR3 => ℝ × Point3
instance (Y : SpaceTag) : TopologicalSpace Y.Pts := by
  cases Y <;> dsimp only [Pts] <;> infer_instance
instance (Y : SpaceTag) : MeasurableSpace Y.Pts := by
  cases Y <;> dsimp only [Pts] <;> infer_instance
end SpaceTag
section Preliminaries
variable {Y : Type*} [MeasurableSpace Y]
def integralC (ν : ComplexMeasure Y) (φ : Y → ℂ) : ℂ :=
  ν.integral φ (ContinuousLinearMap.mul ℝ ℂ)
end Preliminaries
end YangMills.Construction.RotationNotation
end
