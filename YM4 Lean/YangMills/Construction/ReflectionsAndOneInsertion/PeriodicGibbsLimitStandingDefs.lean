import YangMills.Construction.MirrorGridsOfEverySide.MirrorGridOrientationsAndReflectionProducts
import YangMills.Construction.ReflectionPositivity.FormOfAFunctionalOnSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ReflectionsAndOneInsertion
open InfiniteLattice (AmbientSpace)
abbrev InsertionData : Type := MirrorGridsAllSides.GridSetup
def gradNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : AmbientSpace → E)
    (x : AmbientSpace) : ℝ :=
  Real.sqrt (∑ μ : Fin 4, ‖fderiv ℝ g x (Pi.single μ 1)‖ ^ 2)
def spanClassNorm (σ : SeparatedTuples.TupleFunctional)
    (F : ReflectionPositivity.TupleForm.PositiveSpan) : ℝ :=
  Real.sqrt (ReflectionPositivity.TupleForm.reflectionForm σ F F).re
end ReflectionsAndOneInsertion
end YangMills.Construction
