import YangMills.Construction.ReflectionPositivity.FormOfAFunctionalOnSeparatedTuples
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositiveForm
open SeparatedTuples ReflectionPositivity.TupleForm HilbertSpaceBasics
section Quotient
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (b : V → V → ℂ)
def selfNullSet : Set V := {F | b F F = 0}
def selfNullSpan : Submodule ℂ V := Submodule.span ℂ (selfNullSet b)
abbrev NullQuotient : Type _ := V ⧸ selfNullSpan b
def nullClass (F : V) : NullQuotient b := Submodule.Quotient.mk F
def descendedForm (u v : NullQuotient b) : ℂ :=
  b (Function.surjInv (Submodule.Quotient.mk_surjective (selfNullSpan b)) u)
    (Function.surjInv (Submodule.Quotient.mk_surjective (selfNullSpan b)) v)
end Quotient
variable (σ : TupleFunctional)
abbrev NullVectors : Set PositiveSpan := selfNullSet (reflectionForm σ)
def IsPositiveSesquilinear : Prop :=
  IsSesquilinear (reflectionForm σ) ∧ ∀ F, 0 ≤ reflectionForm σ F F
def IsHermitianCauchySchwarz : Prop :=
  IsHermitianForm (reflectionForm σ) ∧
    ∀ F F', ((‖reflectionForm σ F F'‖ ^ 2 : ℝ) : ℂ) ≤ reflectionForm σ F F * reflectionForm σ F' F'
def DescendsToInnerProduct : Prop :=
  (selfNullSpan (reflectionForm σ) : Set PositiveSpan) = NullVectors σ ∧
    (∀ F F' N N', N ∈ NullVectors σ → N' ∈ NullVectors σ →
      reflectionForm σ (F + N) (F' + N') = reflectionForm σ F F') ∧
    (∀ F F', descendedForm (reflectionForm σ) (nullClass (reflectionForm σ) F)
      (nullClass (reflectionForm σ) F') = reflectionForm σ F F') ∧
    IsInnerProductForm (descendedForm (reflectionForm σ))
def FormPropertiesStatement : Prop :=
  ∀ σ : TupleFunctional,
    σ.IsReflectionPositive (Mirrors.axialHyperplane TimeAxis.timeIdx 0) →
      IsPositiveSesquilinear σ ∧ IsHermitianCauchySchwarz σ ∧ DescendsToInnerProduct σ
end YangMills.Construction.ReflectionPositiveForm
end
