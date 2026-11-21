import YangMills.Construction.Towers.DerivativeOfTheActionAtAnAbelianField
import YangMills.Construction.Towers.DerivativesOfAPlaquetteTerm
import YangMills.Construction.Towers.PlaquettesOfAnAbelianField
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.AbelianActionGradient
open AbelianFieldFacts FaceTermDerivatives
theorem cartanPhase_eq_diagonal (t : ℝ) :
    cartanPhase t = !![Complex.exp (Complex.I * t), 0; 0, Complex.exp (-(Complex.I * t))] := by
  have hdiag : Complex.I • ((t : ℂ) • ComplexMatrix2.pauliFamily 2) =
      Matrix.diagonal ![Complex.I * t, -(Complex.I * t)] := by
    rw [ComplexMatrix2.pauliFamily_apply.2.2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [cartanPhase, hdiag, ComplexMatrix2.matExp, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.exp_eq_exp_ℂ, Pi.exp_def]
theorem firstDerivExpr_cartanPhase (M : Fin 4 → ComplexMatrix2) (t c : ℝ) (z w : ℂ)
    (hM : ∑ i, M i = (c : ℂ) • ComplexMatrix2.pauliFamily 2 + z • raisingPauli + w • loweringPauli) :
    firstDerivExpr M (cartanPhase t) = ((Real.sin t * c : ℝ) : ℂ) := by
  have hsum : ∑ i, M i = !![(c : ℂ), z; w, -(c : ℂ)] := by
    rw [hM, raisingPauli, loweringPauli, ComplexMatrix2.pauliFamily_apply.1,
      ComplexMatrix2.pauliFamily_apply.2.1, ComplexMatrix2.pauliFamily_apply.2.2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring_nf
  rw [firstDerivExpr, hsum, cartanPhase_eq_diagonal]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  rw [Complex.sin, show Complex.I * (t : ℂ) = t * Complex.I by ring,
    show -((t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I by ring]
  ring
theorem sum_transportSign_diagonalComponent {a : ℝ} (g : FullSpace.PositiveEdge a → ℝ)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    ∑ i, transportSign i * ((g (facePositiveEdge p i) : ℝ) : ℂ) =
      ((FullSpace.edgeDifference g p : ℝ) : ℂ) := by
  simp [Fin.sum_univ_four, transportSign, facePositiveEdge, FullSpace.edgeDifference]
  ring
theorem holds (hDer : FaceTermDerivatives.Statement)
    (hFace : AbelianFieldPlaquettes.Claim)
    (hAdj : ScalarDifferenceAdjoints) : AbelianActionGradient.Statement := by
  intro L hL θ B hB hfin
  have hF := hFace L hL θ
  have hdiagFin : (Function.support (FullSpace.diagonalComponent B)).Finite := by
    refine (Set.Finite.preimage Subtype.val_injective.injOn hfin).subset ?_
    intro e he
    refine ⟨e.2, fun hz => he ?_⟩
    simp [FullSpace.diagonalComponent, hz, ComplexMatrix2.halfTrace]
  have hdiffFin : (Function.support
      (FullSpace.edgeDifference (FullSpace.diagonalComponent B))).Finite :=
    (hAdj L hL).2.2.2.2.2.2.2.1 _ hdiagFin
  have hsupp : (Function.support fun p : FullSpace.Face L 0 0 =>
      Real.sin (FullSpace.faceAngle θ p) *
        FullSpace.edgeDifference (FullSpace.diagonalComponent B) p).Finite := by
    refine hdiffFin.subset fun p hp hz => hp ?_
    simp only [hz, mul_zero]
  have hField : FullSpace.abelianLinkField θ ∈
      FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup :=
    ⟨fun e => (Matrix.mem_specialUnitaryGroup_iff.1 (hF.abelianLinkField_mem.1 e)).2,
      hF.abelianLinkField_mem.2⟩
  have hBc : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) :=
    ⟨fun e he => (hB.1 e he).2, hB.2⟩
  have hface : ∀ p : FullSpace.Face L 0 0,
      firstDerivExpr (FullSpace.transportedForm (FullSpace.abelianLinkField θ) B p)
          (FullSpace.faceVariable (FullSpace.abelianLinkField θ) p) =
        ((Real.sin (FullSpace.faceAngle θ p) *
          FullSpace.edgeDifference (FullSpace.diagonalComponent B) p : ℝ) : ℂ) := by
    intro p
    rw [hF.faceVariable_eq p]
    refine firstDerivExpr_cartanPhase _ _ _
      (∑ i, FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i)
      (∑ i, conj (FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i)) ?_
    simp only [hF.transportedForm_eq B hB p, Finset.sum_add_distrib, ← Finset.sum_smul,
      sum_transportSign_diagonalComponent]
  have htotal := ((((hDer L hL 0 0 le_rfl).2 B hBc).2 hfin).1 _ hField).2
  refine ⟨hsupp, ?_⟩
  rw [← htotal, finsum_congr hface]
  exact (Complex.ofRealHom.toAddMonoidHom.map_finsum hsupp).symm
end Tower.AbelianActionGradient
end YangMills.Construction
end
