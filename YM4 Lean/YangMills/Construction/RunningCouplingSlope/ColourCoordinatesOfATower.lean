import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def PauliCoordsOrthonormal : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    (∀ [Fintype (Fin 3 × Tower.PositiveEdge L n k j)],
      ∃ Ψ : Tower.edgeFormSpace L n k j ≃ₗ[ℝ] (Fin 3 × Tower.PositiveEdge L n k j → ℝ),
        (∀ (f : Tower.edgeFormSpace L n k j) ι,
          Tower.toPauliCoeffs
              (Tower.restrictToPositiveEdges (f : Tower.Edge L n k j → Matrices.ComplexMatrix2)) ι =
            ((Ψ f ι : ℝ) : ℂ)) ∧
        ∀ f g : Tower.edgeFormSpace L n k j,
          Tower.edgeFormPairing (f : Tower.Edge L n k j → Matrices.ComplexMatrix2)
              (g : Tower.Edge L n k j → Matrices.ComplexMatrix2) =
            ((∑ ι, Ψ f ι * Ψ g ι : ℝ) : ℂ)) ∧
    (∀ [Fintype (Fin 3 × Tower.Vertex L n k j)],
      ∃ Ψ : Tower.vertexFunctionSpace L n k j ≃ₗ[ℝ] (Fin 3 × Tower.Vertex L n k j → ℝ),
        (∀ (f : Tower.vertexFunctionSpace L n k j) ι,
          Tower.toPauliCoeffs (f : Tower.Vertex L n k j → Matrices.ComplexMatrix2) ι =
            ((Ψ f ι : ℝ) : ℂ)) ∧
        ∀ f g : Tower.vertexFunctionSpace L n k j,
          Tower.traceFinsumPairing (f : Tower.Vertex L n k j → Matrices.ComplexMatrix2)
              (g : Tower.Vertex L n k j → Matrices.ComplexMatrix2) =
            ((∑ ι, Ψ f ι * Ψ g ι : ℝ) : ℂ))
end YangMills.Construction.RunningCouplingSlope
end
