import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ComplexTestFunctions
open InfiniteLattice (AmbientSpace)
open SeparatedTuples (RealValued)
abbrev ComplexValued : Type := AmbientSpace → ℂ
def rePart (f : ComplexValued) : RealValued := fun x => (f x).re
def imPart (f : ComplexValued) : RealValued := fun x => (f x).im
def ofRealFun (g : RealValued) : ComplexValued := fun x => (g x : ℂ)
def IsC1Complex (f : ComplexValued) : Prop :=
  TestFunctions.IsC1R4 (rePart f) ∧ TestFunctions.IsC1R4 (imPart f)
def IsC1cComplex (f : ComplexValued) : Prop :=
  IsC1Complex f ∧ HasCompactSupport f
@[simp] theorem rePart_ofRealFun (g : RealValued) : rePart (ofRealFun g) = g := by
  funext x
  simp [rePart, ofRealFun]
end YangMills.Construction.ComplexTestFunctions
