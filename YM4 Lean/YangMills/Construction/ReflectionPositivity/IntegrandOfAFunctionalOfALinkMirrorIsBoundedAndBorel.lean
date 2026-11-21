import YangMills.Construction.ReflectionPositivity.CoordinatesDoubledSpaceAndFunctionalsOfALinkMirror
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.IntegrandBounded
variable {D : MirrorData} (C : LinkLevel D)
def linkIntegrand {n : ℕ} (γ : Fin n → C.KernelLabel) (F : D.FieldSpace → ℂ)
    (ω : C.DoubleSpace) : ℂ :=
  C.halfFunction .pos F ω.1 * (Real.exp (-D.coupling * C.halfAction ω.1) : ℂ) *
    C.kernelProd γ ω
theorem transferFunctional_eq_integral {n : ℕ} (γ : Fin n → C.KernelLabel)
    (F : D.FieldSpace → ℂ) :
    C.transferFunctional γ F = ∫ ω, linkIntegrand C γ F ω ∂C.doubleHaar :=
  rfl
def LinkIntegrandBoundedMeasurable : Prop :=
  ∀ {n : ℕ} (γ : Fin n → C.KernelLabel), ∀ F ∈ C.halfAlgebra .pos,
    TestFunctions.IsBoundedFun (linkIntegrand C γ F) ∧
      Measurable[borel C.DoubleSpace] (linkIntegrand C γ F)
def ReflectPreservesBoundedMeasurable : Prop :=
  ∀ F : D.FieldSpace → ℂ,
    TestFunctions.IsBoundedFun F → Measurable[borel D.FieldSpace] F →
      TestFunctions.IsBoundedFun (F ∘ C.reflectField) ∧
        Measurable[borel D.FieldSpace] (F ∘ C.reflectField)
def BoundedMeasurableFacts : Prop :=
  ∀ (D : MirrorData) (C : LinkLevel D),
    LinkIntegrandBoundedMeasurable C ∧ ReflectPreservesBoundedMeasurable C
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.IntegrandBounded
end
