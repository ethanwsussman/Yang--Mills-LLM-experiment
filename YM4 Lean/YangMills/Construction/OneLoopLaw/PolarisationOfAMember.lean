import YangMills.Construction.PeriodicOperators.TemperedFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.ComplexHessianOfMember
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators.Tempered
structure Properties {L : ℕ} (F : FieldFamily L) (n : ℕ) : Prop where
  linear_left : ∀ (c : ℂ), ∀ B₁ ∈ complexEdgeForms L n 0 0, ∀ B₂ ∈ complexEdgeForms L n 0 0,
    ∀ B' ∈ complexEdgeForms L n 0 0,
      complexHessian F n (c • B₁ + B₂) B' = c * complexHessian F n B₁ B' + complexHessian F n B₂ B'
  symm : ∀ B ∈ complexEdgeForms L n 0 0, ∀ B' ∈ complexEdgeForms L n 0 0,
    complexHessian F n B B' = complexHessian F n B' B
  ofReal : ∀ B ∈ edgeFormSpace L n 0 0, ∀ B' ∈ edgeFormSpace L n 0 0,
    complexHessian F n B B' = (hessianAtIdentity F n B B' : ℂ)
def Statement : Prop :=
  ∀ L n : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → ∀ F : FieldFamily L,
    IsAdmissibleMember (F n) → Properties F n
end YangMills.Construction.OneLoopLaw.ComplexHessianOfMember
end
