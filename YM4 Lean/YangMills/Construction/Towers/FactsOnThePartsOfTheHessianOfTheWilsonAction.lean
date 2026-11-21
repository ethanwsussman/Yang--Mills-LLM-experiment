import YangMills.Construction.Towers.PartsOfTheHessianOfTheWilsonAction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.CurvatureHessianFacts
open PeriodicOperators (finsuppFunctions)
def OnPeriodicSide (L n k : ℕ) : Prop :=
  (∀ U : Edge L n k 0 → Matrices.ComplexMatrix2,
    (∃ β : finsuppFunctions (Fin 3 × PositiveEdge L n k 0) →ₗ[ℂ]
        finsuppFunctions (Fin 3 × PositiveEdge L n k 0) →ₗ[ℂ] ℂ,
      ∀ f f' : finsuppFunctions (Fin 3 × PositiveEdge L n k 0),
        β f f' = curvatureBilinear U
          ((edgePauliCoordinates L n k 0).ofCoeffs (f : Fin 3 × PositiveEdge L n k 0 → ℂ))
          ((edgePauliCoordinates L n k 0).ofCoeffs (f' : Fin 3 × PositiveEdge L n k 0 → ℂ))) ∧
    IsCurvatureKernel U (curvatureKernel U) ∧
    ∀ X, IsCurvatureKernel U X → X = curvatureKernel U) ∧
  ∀ U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup, ∀ c ∈ complexEdgeForms L n k 0,
    ∀ p : Face L n k 0, holonomyDefect U c p ∈ Matrices.ComplexMatrix2.traceless
def OnFullSpace (L k : ℕ) : Prop :=
  (∀ U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2,
    (∃ β : finsuppFunctions (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)) →ₗ[ℂ]
        finsuppFunctions (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)) →ₗ[ℂ] ℂ,
      ∀ f f' : finsuppFunctions (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)),
        β f f' = FullSpace.curvatureBilinear U
          ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs
            (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ))
          ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs
            (f' : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ))) ∧
    FullSpace.IsCurvatureKernel U (FullSpace.curvatureKernel U) ∧
    ∀ X, FullSpace.IsCurvatureKernel U X → X = FullSpace.curvatureKernel U) ∧
  ∀ U ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
    ∀ c ∈ FullSpace.complexEdgeForms (meshAt L k 0),
    ∀ p : FullSpace.Face L k 0, FullSpace.holonomyDefect U c p ∈ Matrices.ComplexMatrix2.traceless
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ n : ℕ, 0 < n → OnPeriodicSide L n k) ∧ OnFullSpace L k
end YangMills.Construction.Tower.CurvatureHessianFacts
end
