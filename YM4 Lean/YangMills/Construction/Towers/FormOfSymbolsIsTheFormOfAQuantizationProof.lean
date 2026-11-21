import YangMills.Construction.Towers.AlgebraOfMatricesTimesUnitaryOperators
import YangMills.Construction.Towers.CoefficientsOfASymbol
import YangMills.Construction.Towers.FormOfSymbolsIsTheFormOfAQuantization
import YangMills.Construction.Towers.QuantizationIsTheSumOfItsSeries
import YangMills.Construction.Towers.RelationsOfTheWeylOperators
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
open MagneticWeyl
def trigMatrixSumCoeff {ι : Type} [Fintype ι] (c : ι → ℝ) (n : ι → Fin 4 → ℤ)
    (M : ι → Matrix (Fin 4) (Fin 4) ℂ) (φ : ℝ) (m : Fin 4 → ℤ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ k, if m = n k then Complex.exp (Complex.I * ((c k * φ : ℝ) : ℂ)) • M k else 0
theorem hasFourierExpansion_trigMatrixSumCoeff {ι : Type} [Fintype ι] (c : ι → ℝ)
    (n : ι → Fin 4 → ℤ) (M : ι → Matrix (Fin 4) (Fin 4) ℂ) (φ : ℝ) :
    HasFourierExpansion (trigMatrixSumCoeff c n M φ) (trigMatrixSum c n M φ) := by
  intro q
  have h : ∀ k ∈ (Finset.univ : Finset ι), HasSum
      (fun m => if m = n k then
        (Complex.exp (Complex.I * ((c k * φ : ℝ) : ℂ)) * fourierChar (n k) q) • M k else 0)
      ((Complex.exp (Complex.I * ((c k * φ : ℝ) : ℂ)) * fourierChar (n k) q) • M k) :=
    fun k _ => hasSum_ite_eq _ _
  have hs := hasSum_sum h
  have he : (fun m => fourierChar m q • trigMatrixSumCoeff c n M φ m) = fun m => ∑ k,
      if m = n k then
        (Complex.exp (Complex.I * ((c k * φ : ℝ) : ℂ)) * fourierChar (n k) q) • M k else 0 := by
    funext m
    rw [trigMatrixSumCoeff, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · subst hk
      rw [smul_smul, mul_comm]
    · simp
  rw [he]
  exact hs
theorem summable_opNorm_trigMatrixSumCoeff {ι : Type} [Fintype ι] (c : ι → ℝ)
    (n : ι → Fin 4 → ℤ) (M : ι → Matrix (Fin 4) (Fin 4) ℂ) (φ : ℝ) :
    Summable fun m => Matrices.RectangularMatrix.opNormValue (trigMatrixSumCoeff c n M φ m) := by
  classical
  refine summable_of_ne_finset_zero (s := Finset.univ.image n) fun m hm => ?_
  have h0 : trigMatrixSumCoeff c n M φ m = 0 := by
    refine Finset.sum_eq_zero fun k _ => if_neg ?_
    rintro rfl
    exact hm (Finset.mem_image_of_mem n (Finset.mem_univ k))
  rw [h0]
  simp [Matrices.RectangularMatrix.opNormValue, OneLoopNotation.opNormOf]
theorem isLinearMap_matMulUnitaryOp (hAlg : MatMulUnitaryOpAlgebra)
    {L : ℕ} {V : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hV : IsUnitaryOp V) :
    IsLinearMap ℂ fun X : Matrix (Fin 4) (Fin 4) ℂ => matMulUnitaryOp X V := by
  have h := (hAlg L 4 4 V hV).1
  have hadd : ∀ X Y : Matrix (Fin 4) (Fin 4) ℂ, matMulUnitaryOp (X + Y) V =
      matMulUnitaryOp X V + matMulUnitaryOp Y V := fun X Y => by
    simpa using h 1 X Y
  have hzero : matMulUnitaryOp (0 : Matrix (Fin 4) (Fin 4) ℂ) V = 0 := by
    simpa using hadd 0 0
  refine ⟨hadd, fun s X => ?_⟩
  simpa [hzero] using h s X 0
theorem inner_matMulUnitaryOp_single {L : ℕ} (hBdd : MatMulUnitaryBounded L 4 4)
    {V : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hV : IsUnitaryOp V)
    (w : VectorL2 L 4) (a b : Fin 4) :
    inner ℂ w (matMulUnitaryOp (Matrix.single a b (1 : ℂ)) V w) =
      inner ℂ (coord w a) (V (coord w b)) := by
  have hv := (hBdd (Matrix.single a b (1 : ℂ)) V hV).1 w
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun x => ?_
  rw [hv x]
  change _ = inner ℂ (EuclideanSpace.single 0 (w x a) : EuclideanSpace ℂ (Fin 1)) _
  rw [EuclideanSpace.inner_single_left, PiLp.inner_apply]
  simp [matMulUnitary, applyCoordwise, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.single_apply, mul_comm]
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
  simp [mul_comm]
theorem termPair_inner_eq (hRel : MagneticWeylRelations) (P : TermPair) (L : ℕ)
    (φ : ℝ) (w : VectorL2 L 4) :
    (P.coeff * Complex.exp (Complex.I * ((P.freq * φ : ℝ) : ℂ))) *
        inner ℂ (P.conjTerm.eval L φ w) (P.term.eval L φ w) =
      (Complex.exp (Complex.I * ((P.totalFreq * φ : ℝ) : ℂ)) *
          (P.coeff * conj P.conjTerm.coeff * P.term.coeff)) *
        inner ℂ (coord w P.conjTerm.comp)
          (magneticWeyl L φ P.offset (coord w P.term.comp)) := by
  obtain ⟨hmul, -, hadj, -⟩ := hRel L φ (-P.conjTerm.offset) P.term.offset
  have hW : inner ℂ (magneticWeyl L φ P.conjTerm.offset (coord w P.conjTerm.comp))
      (magneticWeyl L φ P.term.offset (coord w P.term.comp)) =
      Complex.exp (Complex.I / 2 * (φ : ℂ) * (symplecticForm (-P.conjTerm.offset) P.term.offset : ℂ)) *
        inner ℂ (coord w P.conjTerm.comp)
          (magneticWeyl L φ P.offset (coord w P.term.comp)) := by
    have h := hadj (coord w P.conjTerm.comp)
      (magneticWeyl L φ P.term.offset (coord w P.term.comp))
    rw [neg_neg] at h
    rw [h, hmul, inner_smul_right, TermPair.offset, neg_add_eq_sub]
  have hconj : conj (Complex.exp (Complex.I * ((P.conjTerm.freq * φ : ℝ) : ℂ))) =
      Complex.exp (-(Complex.I * ((P.conjTerm.freq * φ : ℝ) : ℂ))) := by
    rw [← Complex.exp_conj]
    simp
  have hfreq : Complex.I * ((P.totalFreq * φ : ℝ) : ℂ) =
      Complex.I * ((P.freq * φ : ℝ) : ℂ) + Complex.I * ((P.term.freq * φ : ℝ) : ℂ) +
        -(Complex.I * ((P.conjTerm.freq * φ : ℝ) : ℂ)) +
        Complex.I / 2 * (φ : ℂ) * (symplecticForm (-P.conjTerm.offset) P.term.offset : ℂ) := by
    simp only [TermPair.totalFreq]
    push_cast
    ring
  simp only [WeylTerm.eval]
  rw [inner_smul_left, inner_smul_right, hW, hfreq, Complex.exp_add, Complex.exp_add,
    Complex.exp_add, map_mul, hconj]
  ring
theorem pairsFormIsWeylForm_holds
    (hCoeffs : FourierCoeffsOfSymbol)
    (hQuant : WeylQuantHasSum)
    (hRel : MagneticWeylRelations)
    (hAlg : MatMulUnitaryOpAlgebra)
    (hSeries : UnitaryOperatorSeriesClaim) :
    PairsFormIsWeylForm := by
  intro ι _ P L φ w
  have hU : ∀ m, IsUnitaryOp (magneticWeyl L φ m) :=
    fun m => magneticWeyl_isUnitary φ m
  have hc : HasFourierExpansion (trigMatrixSumCoeff (fun k => (P k).totalFreq)
      (fun k => (P k).offset) (fun k => (P k).coeffMatrix) φ) (pairsSymbol P φ) :=
    hasFourierExpansion_trigMatrixSumCoeff _ _ _ φ
  have hs := summable_opNorm_trigMatrixSumCoeff (fun k => (P k).totalFreq)
    (fun k => (P k).offset) (fun k => (P k).coeffMatrix) φ
  have hSummable : HasAbsSummableFourier (pairsSymbol P φ) := ⟨_, hc, hs⟩
  have hCoeff := ((hCoeffs 4 4 (pairsSymbol P φ)).1 hSummable).2.2 _ hc hs
  have hSum := (hQuant L φ 4 4 (pairsSymbol P φ) hSummable).1
  rw [← hCoeff] at hSum
  have hTerm : ∀ m, matMulUnitaryOp (trigMatrixSumCoeff (fun k => (P k).totalFreq)
      (fun k => (P k).offset) (fun k => (P k).coeffMatrix) φ m) (magneticWeyl L φ m) = ∑ k,
      if m = (P k).offset then matMulUnitaryOp
        (Complex.exp (Complex.I * (((P k).totalFreq * φ : ℝ) : ℂ)) • (P k).coeffMatrix)
        (magneticWeyl L φ (P k).offset) else 0 := fun m => by
    have hlin := isLinearMap_matMulUnitaryOp hAlg (hU m)
    have hsum := map_sum hlin.mk' (fun k => if m = (P k).offset then
      Complex.exp (Complex.I * (((P k).totalFreq * φ : ℝ) : ℂ)) • (P k).coeffMatrix else 0)
      Finset.univ
    simp only [IsLinearMap.mk'_apply] at hsum
    rw [trigMatrixSumCoeff, hsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rw [hk]
    · exact hlin.map_zero
  have hFinite := hasSum_sum (s := (Finset.univ : Finset ι)) (fun k _ => hasSum_ite_eq (P k).offset
    (matMulUnitaryOp
      (Complex.exp (Complex.I * (((P k).totalFreq * φ : ℝ) : ℂ)) • (P k).coeffMatrix)
      (magneticWeyl L φ (P k).offset)))
  have hOp := hSum.unique ((funext hTerm : _ = _) ▸ hFinite)
  rw [pairsForm, hOp, _root_.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlin := isLinearMap_matMulUnitaryOp hAlg (hU (P k).offset)
  rw [termPair_inner_eq hRel, TermPair.coeffMatrix, hlin.map_smul, hlin.map_smul,
    _root_.smul_apply, _root_.smul_apply, inner_smul_right,
    inner_smul_right, inner_matMulUnitaryOp_single (hSeries L 4 4).1 (hU _)]
  ring
end YangMills.Construction.Tower.ConstantFieldSymbols
end
