import YangMills.Construction.Measurability.StandardBorelSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.BorelKernels
universe u v
abbrev IsStandardBorelSpace (Z : Type u) [MeasurableSpace Z] : Prop :=
  Measurability.StandardBorel.IsStandard Z
abbrev AdjoinPoint (Z : Type u) : Type u := Z ⊕ PUnit.{u + 1}
abbrev IsBorelMeasurable {Z : Type u} {Z' : Type v} [MeasurableSpace Z] [MeasurableSpace Z']
    (f : Z → Z') : Prop :=
  Measurable f
abbrev FiniteComplexMeasure (Z : Type u) [MeasurableSpace Z] : Type u := ComplexMeasure Z
abbrev pointMass {Z : Type u} [MeasurableSpace Z] (z : Z) : Measure Z := Measure.dirac z
end YangMills.Construction.BorelKernels
