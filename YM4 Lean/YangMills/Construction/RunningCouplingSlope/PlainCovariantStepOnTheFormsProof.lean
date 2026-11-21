import YangMills.Construction.RunningCouplingSlope.PlainCovariantStepOnTheForms
import YangMills.Construction.RunningCouplingSlope.PlainStepOnTheForms
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSitesProof
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATowerProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace MeanCovariantStep
open Tower Matrices
variable {L n k j : ℕ}
private theorem extendOddly_opposite
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.extendOddly_opposite <;> assumption
private theorem covDiff_of_positive (W : Edge L n k j → ComplexMatrix2)
    (l : Vertex L n k j → ComplexMatrix2) (b : Edge L n k j) (hb : b.IsPositivelyOriented) :
    covDiff W l b = ComplexMatrix2.conjugateBy (W b) (l b.target) - l b.source := by apply _root_.YangMills.Construction.Tower.Translations.covDiff_of_pos <;> assumption
private theorem conjugateBy_mem_traceless {W X : ComplexMatrix2} (hW : Matrix.det W = 1)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy W X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
private theorem conjugateBy_mem_hermitianTraceless {W X : ComplexMatrix2}
    (hW : W ∈ ComplexMatrix2.specialUnitary) (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy W X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.conjugateBy_mem_hermitianTraceless <;> assumption
private theorem covDiff_smul_add (W : Edge L n k j → ComplexMatrix2)
    (l l' : Vertex L n k j → ComplexMatrix2) (w : ℂ) :
    covDiff W (w • l + l') = w • covDiff W l + covDiff W l' := by
  classical
  funext b
  simp only [covDiff, extendOddly, Pi.add_apply, Pi.smul_apply, ComplexMatrix2.conjugateBy]
  split_ifs
  · simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    abel
  · simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg,
      smul_sub]
    abel
private theorem covDiff_sub (W : Edge L n k j → ComplexMatrix2)
    (l l' : Vertex L n k j → ComplexMatrix2) :
    covDiff W (l - l') = covDiff W l - covDiff W l' := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.covDiff_sub <;> assumption
end MeanCovariantStep
open MeanCovariantStep Tower Matrices in
theorem meanCovariantStepOnForms_holds (hS : MeanDerivOnForms.Claim)
    (hLin : Tower.StepMapsComplexLinear.Claim)
    (hRel : Tower.CovDiffStepRelations)
    (hReal : Tower.RealLinearMaps.RealLinearMapsStatement) :
    MeanCovariantStepOnForms := by
  intro L hL n k j hn hk hj
  classical
  have e₁ := hS L hL n k j hn hj
  have hstep := (hReal L n k hL hn hk).1 j hj
  have e₂ := hstep.contourLogDrift_isLinear
  have e₃ := hstep.adjointCubeAverage_isLinear
  unfold EventuallyNearIdentity at e₁ e₂ e₃ ⊢
  filter_upwards [e₁, e₂, e₃] with V f₁ f₂ f₃
  obtain ⟨hsmall, hreal, hcm, hlin, hrm, -, horb⟩ := f₁
  obtain ⟨hL1, hL2, hL3, hL4⟩ := hLin L hL n k j hn hj V hsmall
  have hL2' : 2 ≤ L := by
    have := hL.2
    omega
  have hX : ∀ b : Edge L n k (j + 1),
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun b =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2'
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  have hdet : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      Matrix.det (normalizedMean V c) = 1 := fun c hc =>
    (Matrix.mem_specialUnitaryGroup_iff.1 (hreal c hc).2.2).2
  have hDc : ∀ g : Vertex L n k (j + 1) → ComplexMatrix2,
      (∀ y, g y ∈ ComplexMatrix2.traceless) →
      covDiff (normalizedMean V) g ∈ complexEdgeForms L n k (j + 1) := by
    intro g hg
    refine ⟨fun c hc => ?_, fun c => extendOddly_opposite hX _ c⟩
    rw [covDiff_of_positive _ _ _ hc]
    exact ComplexMatrix2.traceless.sub_mem (conjugateBy_mem_traceless (hdet c hc) (hg _)) (hg _)
  have hDr : ∀ g : Vertex L n k (j + 1) → ComplexMatrix2,
      (∀ y, g y ∈ ComplexMatrix2.hermitianTraceless) →
      covDiff (normalizedMean V) g ∈ edgeFormSpace L n k (j + 1) := by
    intro g hg
    refine ⟨fun c hc => ?_, fun c => extendOddly_opposite hX _ c⟩
    rw [covDiff_of_positive _ _ _ hc]
    exact ComplexMatrix2.hermitianTraceless.sub_mem
      (conjugateBy_mem_hermitianTraceless (hreal c hc).2.2 (hg _)) (hg _)
  obtain ⟨T₂, hT₂⟩ := f₂
  obtain ⟨T₃, hT₃⟩ := f₃
  have hnr : ∀ B ∈ edgeFormSpace L n k j, ∀ y,
      contourLogDrift V B y ∈ ComplexMatrix2.hermitianTraceless := by
    intro B hB y
    have := (T₂ ⟨B, hB⟩).2 y (Set.mem_univ y)
    rwa [hT₂ ⟨B, hB⟩] at this
  have har : ∀ l : Vertex L n k j → ComplexMatrix2,
      (∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) → ∀ y,
      adjointCubeAverage V l y ∈ ComplexMatrix2.hermitianTraceless := by
    intro l hl y
    have hm : l ∈ vertexFunctionSpace L n k j := fun x _ => hl x
    have := (T₃ ⟨l, hm⟩).2 y (Set.mem_univ y)
    rwa [hT₃ ⟨l, hm⟩] at this
  refine ⟨?_, ?_, ?_, hnr, har, fun l hl y => (hL3 l hl).2 y,
    fun l l' hl hl' w => (hL4 l l' hl hl' w).2, ?_⟩
  · intro B hB
    exact (complexEdgeForms L n k (j + 1)).add_mem (hcm B hB) (hDc _ (hL1 B hB).2)
  · intro B hB B' hB' w
    simp only [meanCovariantStep]
    rw [hlin B hB B' hB' w, (hL2 B hB B' hB' w).2, covDiff_smul_add]
    simp only [smul_add]
    abel
  · intro B hB
    exact (edgeFormSpace L n k (j + 1)).add_mem (hrm B hB) (hDr _ (hnr B hB))
  · intro l hl
    have hr := ((hRel L hL n k j hn hj V hsmall l hl).2.1)
    simp only [meanCovariantStep]
    rw [horb l hl, hr, covDiff_sub]
    abel
end YangMills.Construction.RunningCouplingSlope
end
