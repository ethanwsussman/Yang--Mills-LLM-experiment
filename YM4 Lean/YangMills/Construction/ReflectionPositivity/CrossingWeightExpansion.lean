import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CrossingWeight
def weightAt (b : ℝ)
    (x : YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary ×
      YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary) : ℂ :=
  ((Real.exp (b / 2 * (YangMills.Construction.Matrices.ComplexMatrix2.fullTrace
    ((x.1 * x.2⁻¹ : YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary) :
      YangMills.Construction.Matrices.ComplexMatrix2)).re) : ℝ) : ℂ)
structure CharacterFamily where
  index : Type
  countable : Countable index
  coeff : index → ℝ
  fn : index → YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary → ℂ
instance instNonemptyCharacterFamily : Nonempty CharacterFamily :=
  ⟨⟨Empty, inferInstance, fun _ => 0, fun _ _ => 0⟩⟩
namespace CharacterFamily
def summand (E : CharacterFamily) (j : E.index)
    (x : YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary ×
      YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary) : ℂ :=
  (E.coeff j : ℂ) * E.fn j x.1 * conj (E.fn j x.2)
def Expands (E : CharacterFamily) (b : ℝ) : Prop :=
  (∀ j, 0 ≤ E.coeff j) ∧
  HasSum E.coeff (Real.exp (2 * b)) ∧
  (∀ j, Continuous (E.fn j)) ∧
  (∀ j g, ‖E.fn j g‖ ≤ 1) ∧
  (∀ x, HasSum (fun j => E.summand j x) (weightAt b x)) ∧
  (∀ x, Summable (fun j => ‖E.summand j x‖)) ∧
  HasSumUniformlyOn E.summand (weightAt b) Set.univ
end CharacterFamily
def chosenExpansion (b : ℝ) : CharacterFamily :=
  Classical.epsilon fun E : CharacterFamily => E.Expands b
def PositiveTypeStatement : Prop :=
  ∀ b : ℝ, 0 ≤ b → (chosenExpansion b).Expands b
end YangMills.Construction.ReflectionPositivity.CrossingWeight
end
