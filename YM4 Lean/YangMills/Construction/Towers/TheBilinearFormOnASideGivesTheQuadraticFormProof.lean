import YangMills.Construction.Towers.BackgroundFormOfTheFunctionalOnASide
import YangMills.Construction.Towers.QuadraticFormsAndTransposesOnTheRealSpaces
import YangMills.Construction.Towers.TheBilinearFormOnASideGivesTheQuadraticForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.BilinearOnDiagonal
open RealQuadraticTransposes
theorem diagonalIsHessianForm_holds (hQ : RealQuadraticTransposes.Statement)
    (hZ : RescaledBackgroundFormFiniteSide.Statement)
    (hC : AsDifferentials.CovariantMeansAreDerivatives) : DiagonalIsHessianForm := by
  intro L hL k hk n hn
  obtain ⟨-, hN⟩ := hQ L n k hL hn hk
  have hA := ((hC L hL k hk).1 n hn).2.2
  have hB := hZ L hL k hk n hn
  unfold RescaledConditions.BackgroundFormMatchesHessian at hB
  refine Filter.Eventually.mp (hN.and (hA.and hB)) ?_
  refine Filter.Eventually.of_forall ?_
  rintro U ⟨⟨-, -, hO⟩, ⟨-, hq⟩, hz⟩ J μ B
  have e0 : sourceQuadraticForm U 0 0 B = 0 := by
    simp [sourceQuadraticForm, edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges,
      Matrices.ComplexMatrix2.halfTrace, Matrices.ComplexMatrix2.fullTrace]
  have e1 : backgroundForm L n k U B B =
      ((leftSecondDeriv (plaquetteAction L n k) U B B : ℝ) : ℂ) +
        ((traceFinsumNorm (gaugeSliceResidual U B : Vertex L n k 0 → Matrices.ComplexMatrix2) ^ 2 : ℝ) : ℂ) := by
    rw [hz B]
    unfold backgroundHessianForm
    rw [e0]
    push_cast
    ring
  have e2 : AsDifferentials.complexQuadraticTerm L n k U
      ((B : Edge L n k 0 → Matrices.ComplexMatrix2) + covDiff U (backgroundGaugeParameter U B))
      ((B : Edge L n k 0 → Matrices.ComplexMatrix2) + covDiff U (backgroundGaugeParameter U B)) =
      iterQuadraticTerm U (backgroundShift L n k U B) (backgroundShift L n k U B) := by
    rw [← hO.backgroundShift_apply B]
    exact hq _ _
  rw [← hO.hessianFunction_eq J μ B]
  unfold backgroundBilinear hessianFunction
  rw [e1, e2, levelBracketTerm_zero, levelBracketTerm_zero]
  ring
end YangMills.Construction.Tower.BilinearOnDiagonal
end
