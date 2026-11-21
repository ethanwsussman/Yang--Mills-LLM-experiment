import YangMills.Construction.Towers.TheSignsOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.GaussianConstraint
section Spaces
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
def kernelGaussianIntegral (M : E →ₗ[ℝ] F) (T : QuadraticForm ℝ (LinearMap.ker M)) : ℝ :=
  letI : MeasurableSpace (LinearMap.ker M) := borel _
  haveI : BorelSpace (LinearMap.ker M) := ⟨rfl⟩
  ∫ B : LinearMap.ker M, Real.exp (-(1 / 2) * T B)
def constrainedGaussianNumber (M : E →ₗ[ℝ] F) (T : QuadraticForm ℝ (LinearMap.ker M)) : ℝ :=
  LinearMap.det (M ∘ₗ LinearMap.adjoint M) ^ (-(1 / 2) : ℝ) * kernelGaussianIntegral M T
def saddlePointOperator (X : E →ₗ[ℝ] E) (M : E →ₗ[ℝ] F) : (E × F) →ₗ[ℝ] E × F :=
  (X.coprod (LinearMap.adjoint M)).prod (M ∘ₗ LinearMap.fst ℝ E F)
end Spaces
def constrainedGaussianNumberOfCores {V V' : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup V'] [Module ℝ V'] [FiniteDimensional ℝ V']
    (c : InnerProductSpace.Core ℝ V) (c' : InnerProductSpace.Core ℝ V') (M : V →ₗ[ℝ] V')
    (T : QuadraticForm ℝ (LinearMap.ker M)) : ℝ :=
  letI := c.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c.toCore
  letI := c'.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c'.toCore
  constrainedGaussianNumber M T
end YangMills.Construction.GaussianConstraint
namespace YangMills.Construction.Tower
variable {L n k j j' : ℕ}
def IsEdgePairingCore (c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)) : Prop :=
  ∀ B B' : edgeFormSpace L n k j,
    c.inner B B' = (edgeFormPairing (B : Edge L n k j → Matrices.ComplexMatrix2)
      (B' : Edge L n k j → Matrices.ComplexMatrix2)).re
def EdgeFormsEuclidean (L n k j : ℕ) : Prop :=
  FiniteDimensional ℝ (edgeFormSpace L n k j) ∧
    ∃ c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j), IsEdgePairingCore c
def constrainedGaussianOnEdgeForms (M : edgeFormSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j')
    (T : QuadraticForm ℝ (LinearMap.ker M)) : ℝ :=
  open Classical in
  if h : EdgeFormsEuclidean L n k j ∧ EdgeFormsEuclidean L n k j' then
    haveI := h.1.1
    haveI := h.2.1
    GaussianConstraint.constrainedGaussianNumberOfCores h.1.2.choose h.2.2.choose M T
  else 0
def constraintDifferential (L n k i : ℕ) (W : Edge L n k (i + 1) → Matrices.ComplexMatrix2) :
    edgeFormSpace L n k i →ₗ[ℝ] edgeFormSpace L n k (i + 1) :=
  leftDifferentialLinear (smoothingStep L n k i) (chosenProlong L n k i W)
def fibreHessianForm (L n k i : ℕ) (W : Edge L n k (i + 1) → Matrices.ComplexMatrix2) :
    QuadraticForm ℝ (LinearMap.ker (constraintDifferential L n k i W)) :=
  (fieldCurveData L n k i).hessianForm (S := LinearMap.ker (constraintDifferential L n k i W))
    (fun B => B.1.1) (chosenLevelFibre L n k i W) (chosenGaugeFixedEnergy L n k i)
    (chosenProlong L n k i W)
def gaussianNormaliser (L n k i : ℕ) (W : Edge L n k (i + 1) → Matrices.ComplexMatrix2) : ℝ :=
  constrainedGaussianOnEdgeForms (constraintDifferential L n k i W) (fibreHessianForm L n k i W)
def logNormaliserRatio (L n k i : ℕ) (W : Edge L n k (i + 1) → Matrices.ComplexMatrix2) : ℝ :=
  Real.log (gaussianNormaliser L n k i W) -
    Real.log (gaussianNormaliser L n k i (trivialField L n k (i + 1)))
end YangMills.Construction.Tower
end
