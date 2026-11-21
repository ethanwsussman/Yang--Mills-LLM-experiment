import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNormProof
import YangMills.Construction.PeriodicOperators.SeriesOfTheSymbol
import YangMills.Construction.PeriodicOperators.TransposeOfAPeriodicOperator
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TransposeProof
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
variable {I J : PeriodicData}
theorem euclidNormVec_neg (y : AmbientSpace) : euclidNormVec (-y) = euclidNormVec y := by
  simp [euclidNormVec]
theorem weightOf_translate (h : IsPeriodic I) (m : Fin 4 → ℤ) (i : I.Carrier) :
    I.weightOf (I.translate m i) = I.weightOf i := by apply _root_.YangMills.Construction.PeriodicOperators.Quotients.weightOf_translate <;> assumption
theorem translate_neg_translate (h : IsPeriodic I) (m : Fin 4 → ℤ) (i : I.Carrier) :
    I.translate (-m) (I.translate m i) = i := by
  rw [← h.translate_add, add_neg_cancel, h.translate_zero]
theorem exists_weight_ratio_bound (h : IsPeriodic I) (h' : IsPeriodic J) :
    ∃ B : ℝ, 0 < B ∧ ∀ (i : I.Carrier) (j : J.Carrier), J.weightOf j / I.weightOf i ≤ B := by
  have := h.finite_components
  have := h'.finite_components
  cases nonempty_fintype I.Component
  cases nonempty_fintype J.Component
  have hs' : 0 ≤ ∑ p, J.weight p := Finset.sum_nonneg fun p _ => (h'.weight_pos p).le
  have hs : 0 ≤ ∑ p, (I.weight p)⁻¹ :=
    Finset.sum_nonneg fun p _ => (inv_pos.mpr (h.weight_pos p)).le
  refine ⟨(1 + ∑ p, J.weight p) * (1 + ∑ p, (I.weight p)⁻¹), by positivity, fun i j => ?_⟩
  have h1 : J.weightOf j ≤ 1 + ∑ p, J.weight p := by
    have := Finset.single_le_sum (f := J.weight) (fun p _ => (h'.weight_pos p).le)
      (Finset.mem_univ (J.componentOf j))
    simp only [PeriodicData.weightOf]
    linarith
  have h2 : (I.weightOf i)⁻¹ ≤ 1 + ∑ p, (I.weight p)⁻¹ := by
    have := Finset.single_le_sum (f := fun p => (I.weight p)⁻¹)
      (fun p _ => (inv_pos.mpr (h.weight_pos p)).le) (Finset.mem_univ (I.componentOf i))
    simp only [PeriodicData.weightOf]
    linarith
  rw [div_eq_mul_inv]
  exact mul_le_mul h1 h2 (inv_pos.mpr (h.weight_pos _)).le (by positivity)
theorem kernelTranspose_apply (T : J.Carrier → I.Carrier → ℂ) (i : I.Carrier) (j : J.Carrier) :
    kernelTranspose I J T i j = ((J.weightOf j / I.weightOf i : ℝ) : ℂ) * T j i :=
  rfl
theorem expDecay_kernelTranspose (h : IsPeriodic I) (h' : IsPeriodic J)
    {T : J.Carrier → I.Carrier → ℂ} {B C δ : ℝ}
    (hB : ∀ (i : I.Carrier) (j : J.Carrier), J.weightOf j / I.weightOf i ≤ B)
    (hT : ExpDecay I J T C δ) : ExpDecay J I (kernelTranspose I J T) (B * C) δ := by
  intro i j
  have hr : 0 ≤ J.weightOf j / I.weightOf i :=
    (div_pos (h'.weight_pos _) (h.weight_pos _)).le
  have hy : euclidNormVec (I.pos i - J.pos j) =
      euclidNormVec (J.pos j - I.pos i) := by
    rw [← neg_sub, euclidNormVec_neg]
  rw [kernelTranspose_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, hy, mul_assoc]
  exact mul_le_mul (hB i j) (hT j i) (norm_nonneg _) (hr.trans (hB i j))
theorem isShiftInvariant_kernelTranspose (h : IsPeriodic I) (h' : IsPeriodic J)
    {T : J.Carrier → I.Carrier → ℂ} (hT : IsShiftInvariant I J T) :
    IsShiftInvariant J I (kernelTranspose I J T) := by
  intro m i j
  rw [kernelTranspose_apply, kernelTranspose_apply, weightOf_translate h, weightOf_translate h', hT]
theorem symbolSummand_kernelTranspose (h : IsPeriodic I) (h' : IsPeriodic J)
    {T : J.Carrier → I.Carrier → ℂ} (hT : IsShiftInvariant I J T) (κ : Fin 4 → ℂ) (i : I.Carrier)
    (j : J.Carrier) (m : Fin 4 → ℤ) :
    symbolSummand J I (kernelTranspose I J T) κ i j m =
      ((J.weightOf j / I.weightOf i : ℝ) : ℂ) * symbolSummand I J T (-κ) j i (-m) := by
  have hker : T (J.translate m j) i = T j (I.translate (-m) i) := by
    rw [← hT (-m) (J.translate m j) i, translate_neg_translate h']
  have hdot : bilinDot κ (toComplexVec (J.pos (J.translate m j) - I.pos i)) =
      bilinDot (-κ) (toComplexVec (I.pos (I.translate (-m) i) - J.pos j)) := by
    simp only [bilinDot, h.pos_translate, h'.pos_translate]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [toComplexVec, castVec, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
    push_cast
    ring
  simp only [symbolSummand]
  rw [kernelTranspose_apply, weightOf_translate h', hker, hdot, mul_assoc]
theorem fourierSymbol_kernelTranspose (h : IsPeriodic I) (h' : IsPeriodic J)
    {T : J.Carrier → I.Carrier → ℂ} (hT : IsShiftInvariant I J T) (κ : Fin 4 → ℂ) (i : I.Carrier)
    (j : J.Carrier) :
    fourierSymbol J I (kernelTranspose I J T) κ i j =
      ((J.weightOf j / I.weightOf i : ℝ) : ℂ) * fourierSymbol I J T (-κ) j i := by
  simp only [fourierSymbol]
  simp_rw [symbolSummand_kernelTranspose h h' hT κ i j]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.neg (Fin 4 → ℤ)).tsum_eq fun m => symbolSummand I J T (-κ) j i m
theorem symbolSummableAt_kernelTranspose (h : IsPeriodic I) (h' : IsPeriodic J)
    {T : J.Carrier → I.Carrier → ℂ} (hT : IsShiftInvariant I J T) {κ : Fin 4 → ℂ}
    (hf : SymbolSummableAt I J T (-κ)) : SymbolSummableAt J I (kernelTranspose I J T) κ := by
  intro i j
  simp_rw [symbolSummand_kernelTranspose h h' hT κ i j, norm_mul]
  exact ((hf j i).comp_injective neg_injective).mul_left _
theorem neg_mem_imStrip {δ : ℝ} {κ : Fin 4 → ℂ} (hκ : κ ∈ strictImStrip δ) :
    -κ ∈ strictImStrip δ := by
  have e : imVec (-κ) = -imVec κ := by
    funext μ
    simp [imVec]
  show euclidNormVec (imVec (-κ)) < δ
  rw [e, euclidNormVec_neg]
  exact hκ
theorem toComplexVec_mem_imStrip {δ : ℝ} (hδ : 0 < δ) (κ : AmbientSpace) :
    toComplexVec κ ∈ strictImStrip δ := by
  have e : imVec (toComplexVec κ) = 0 := by
    funext μ
    simp [imVec, toComplexVec]
  simpa [strictImStrip, e, euclidNormVec] using hδ
theorem bilinDot_toComplexVec (a b : AmbientSpace) :
    bilinDot (toComplexVec a) (toComplexVec b) = ((∑ μ, a μ * b μ : ℝ) : ℂ) := by
  simp [bilinDot, toComplexVec]
theorem conj_symbolSummand {T : J.Carrier → I.Carrier → ℂ} (hre : ∀ j i, (T j i).im = 0)
    (κ : AmbientSpace) (j : J.Carrier) (i : I.Carrier) (m : Fin 4 → ℤ) :
    conj (symbolSummand I J T (toComplexVec κ) j i m) =
      symbolSummand I J T (-toComplexVec κ) j i m := by
  have hneg : ∀ y, bilinDot (-toComplexVec κ) y = -bilinDot (toComplexVec κ) y := fun y => by
    simp [bilinDot]
  simp only [symbolSummand, map_mul, ← Complex.exp_conj, hneg, bilinDot_toComplexVec,
    Complex.conj_I, Complex.conj_ofReal, Complex.conj_eq_iff_im.mpr (hre _ _)]
  congr 2
  ring
theorem conj_fourierSymbol {T : J.Carrier → I.Carrier → ℂ} (hre : ∀ j i, (T j i).im = 0)
    (κ : AmbientSpace) (j : J.Carrier) (i : I.Carrier) :
    conj (fourierSymbol I J T (toComplexVec κ) j i) = fourierSymbol I J T (-toComplexVec κ) j i := by
  simp only [fourierSymbol]
  rw [Complex.conj_tsum]
  simp_rw [conj_symbolSummand hre]
theorem transpose_claim (hseries : SymbolSeriesClaim)
    (hclasses : SymbolOnQuotients.Claim)
    (hquot : Quotients.QuotientTransposeNorm) : Transpose.Claim := by
  intro I J h h' T δ hper hrate
  obtain ⟨hcov, -⟩ := id hper
  obtain ⟨hδ, C, hC, hbound⟩ := id hrate
  obtain ⟨B, hB, hratio⟩ := exists_weight_ratio_bound h h'
  have htb := expDecay_kernelTranspose h h' hratio hbound
  have hrateT : IsDecayRate J I (kernelTranspose I J T) δ := ⟨hδ, B * C, mul_pos hB hC, htb⟩
  have hperT : IsPeriodicKernel J I (kernelTranspose I J T) :=
    ⟨isShiftInvariant_kernelTranspose h h' hcov, B * C, δ, mul_pos hB hC, hδ, htb⟩
  have hformed := (hseries I J h h' T δ hrate).summableOn_strip
  have hent := (hclasses I J h h' T hper).quotSymbol_mkQuot
  have hentT := (hclasses J I h' h _ hperT).quotSymbol_mkQuot
  obtain ⟨-, hw, hdual⟩ := hquot I J h h' 1 one_pos
  have hw₁ := (hw 1 (Or.inl rfl)).1.2
  obtain ⟨-, hw', -⟩ := hquot J I h' h 1 one_pos
  have hw₂ := (hw' 1 (Or.inl rfl)).1.2
  refine ⟨hperT, hrateT, fun κ hκ => ?_, fun hre κ f g => ?_⟩
  · have hfT := symbolSummableAt_kernelTranspose h h' hcov (hformed _ (neg_mem_imStrip hκ))
    refine ⟨hfT, ?_⟩
    funext c c'
    obtain ⟨i, rfl⟩ := Quot.exists_rep c
    obtain ⟨j, rfl⟩ := Quot.exists_rep c'
    have e₁ := hentT κ hfT i j
    have e₂ := hent (-κ) (hformed _ (neg_mem_imStrip hκ)) j i
    have w₁ := hw₁ i
    have w₂ := hw₂ j
    show quotSymbol J I (kernelTranspose I J T) κ (I.mkQuot 1 i) (J.mkQuot 1 j) =
      ((J.quotWeight 1 (J.mkQuot 1 j) / I.quotWeight 1 (I.mkQuot 1 i) : ℝ) : ℂ) *
        quotSymbol I J T (-κ) (J.mkQuot 1 j) (I.mkQuot 1 i)
    rw [e₁, e₂, w₁, w₂, fourierSymbol_kernelTranspose h h' hcov]
  · have hmem := toComplexVec_mem_imStrip hδ κ
    have hconj : quotSymbol I J T (-toComplexVec κ) =
        Quotients.conjKernel (quotSymbol I J T (toComplexVec κ)) := by
      funext c' c
      obtain ⟨j, rfl⟩ := Quot.exists_rep c'
      obtain ⟨i, rfl⟩ := Quot.exists_rep c
      have e₁ := hent _ (hformed _ hmem) j i
      have e₂ := hent _ (hformed _ (neg_mem_imStrip hmem)) j i
      show quotSymbol I J T (-toComplexVec κ) (J.mkQuot 1 j) (I.mkQuot 1 i) =
        conj (quotSymbol I J T (toComplexVec κ) (J.mkQuot 1 j) (I.mkQuot 1 i))
      rw [e₁, e₂, conj_fourierSymbol hre]
    have key := ((hdual.1 1 1 (Or.inl rfl) (Or.inl rfl)).2.2.1)
      (quotSymbol I J T (toComplexVec κ)) f g
    rw [hconj]
    exact key
end YangMills.Construction.PeriodicOperators.TransposeProof
end
