import YangMills.Construction.Towers.SecondDifferentialOfTheActionAsAKernel
import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.HessianLaplacian
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.FullSpace.FieldValueFunctions (hessianBilinear rawHessianKernel)
open YangMills.Construction.Tower.HessianKernel (finiteSupportComplexForms)
variable {L k : ℕ}
def IsComplexBilinearOn {α : Type} (S : Set (α → ComplexMatrix2))
    (Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ) : Prop :=
  ∀ z : ℂ, ∀ A₁ ∈ S, ∀ A₂ ∈ S, ∀ A₃ ∈ S,
    Q (z • A₁ + A₂) A₃ = z * Q A₁ A₃ + Q A₂ A₃ ∧ Q A₃ (z • A₁ + A₂) = z * Q A₃ A₁ + Q A₃ A₂
def symmHessianKernel (U J : Edge L k 0 → ComplexMatrix2) (μ : Edge L k k → ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge (meshAt L k 0))
      (Fin 3 × PositiveEdge (meshAt L k 0)) :=
  (1 / 2 : ℂ) • (rawHessianKernel U J μ +
    swapKernel (rawHessianKernel U J μ))
def HessianKernelWellDefined (U J : Edge L k 0 → ComplexMatrix2)
    (μ : Edge L k k → ComplexMatrix2) : Prop :=
  IsComplexBilinearOn (finiteSupportComplexForms L k 0) (hessianBilinear U J μ) ∧
    (∀ B ∈ finiteSupportComplexForms L k 0,
      hessianBilinear U J μ B B = hessianForm U J μ B) ∧
    IsHessianKernel U J μ (symmHessianKernel U J μ) ∧
    (∀ X, IsHessianKernel U J μ X → X = symmHessianKernel U J μ) ∧
    hessianKernel U J μ = symmHessianKernel U J μ
def CovLaplacianWellDefined (U : Edge L k 0 → ComplexMatrix2) : Prop :=
  (∀ i' i, CompSummableAt (swapKernel (covDiffKernel L k 0 U))
    (covDiffKernel L k 0 U) i' i) ∧
  Represents
    (compKernel (swapKernel (covDiffKernel L k 0 U))
      (covDiffKernel L k 0 U))
    ((vertexCoordinate (Vertex L k 0)).mapOnCoeffs (vertexCoordinate (Vertex L k 0))
      fun f => covDiffTranspose L k U (covDiff U f))
def HessianKernelAndLaplacianExist : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ U ∈ smallIterateFields L k,
      (∀ J ∈ complexEdgeForms (meshAt L k 0), ∀ μ ∈ complexEdgeForms (meshAt L k k),
        HessianKernelWellDefined U J μ) ∧
      CovLaplacianWellDefined U
end YangMills.Construction.Tower.FullSpace.HessianLaplacian
end
