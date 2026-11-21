import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Matrices.HaarPositivity
open ComplexMatrix2
def OpenPositiveStatement : Prop :=
  ∀ (S : Type) [Finite S] (O : Set (S → specialUnitary)), IsOpen O → O.Nonempty →
    0 < haarPi S O
end YangMills.Construction.Matrices.HaarPositivity
