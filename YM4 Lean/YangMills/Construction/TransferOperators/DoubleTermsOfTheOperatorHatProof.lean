import YangMills.Construction.Matrices.ProjectionsOntoSpacesOfSeveralVariables
import YangMills.Construction.Matrices.TensorOperatorsOfDisjointPartsCommuteProof
import YangMills.Construction.TransferOperators.ComponentFunctionsOfTheProjections
import YangMills.Construction.TransferOperators.ComponentsOfAProductWithAPolynomial
import YangMills.Construction.TransferOperators.DoubleTermsOfTheOperatorHat
import YangMills.Construction.TransferOperators.FieldsKeepProductCoefficientSpaces
import YangMills.Construction.TransferOperators.InverseWeightSumConverges
import YangMills.Construction.TransferOperators.RatiosOfCoefficientsOnAdmissiblePairs
import YangMills.Construction.TransferOperators.SmoothFunctionsDecayRapidly
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SpinHarmonics.HatDoubleTerms
theorem norm_le_of_idempotent_selfAdjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : H →L[ℂ] H) (hP : P = star P ∧ P = P * P) (x : H) : ‖P x‖ ≤ ‖x‖ := by
  have hs : inner ℂ (P x) (P x) = inner ℂ x (P (P x)) := by
    have e := ContinuousLinearMap.adjoint_inner_right P x (P x)
    rw [← ContinuousLinearMap.star_eq_adjoint, ← hP.1] at e
    exact e.symm
  have hi : P (P x) = P x := by
    exact show (P * P) x = P x from by rw [← hP.2]
  rw [hi] at hs
  have hn : ‖P x‖ ^ 2 ≤ ‖x‖ * ‖P x‖ := by
    have e : ‖inner ℂ (P x) (P x)‖ = ‖P x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [← e, hs]
    exact norm_inner_le_norm _ _
  by_cases h0 : ‖P x‖ = 0
  · rw [h0]
    exact norm_nonneg x
  · have hpos : 0 < ‖P x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith
theorem exists_finset_near_halfNatural (t : HalfNatural) (d : ℕ) :
    ∃ s : Finset HalfNatural, s.card ≤ 2 * d + 1 ∧
      ∀ r : HalfNatural, |r.toReal - t.toReal| ≤ (d : ℝ) / 2 → r ∈ s := by
  classical
  refine ⟨(Finset.Icc (t.doubled - d) (t.doubled + d)).image fun n => (⟨n⟩ : HalfNatural), ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp only [Nat.card_Icc]
    omega
  · intro r hr
    have hab := abs_le.mp hr
    have hup : (r.doubled : ℝ) ≤ t.doubled + d := by
      have e := hab.2
      simp only [HalfNatural.toReal] at e
      linarith
    have hlo : (t.doubled : ℝ) ≤ r.doubled + d := by
      have e := hab.1
      simp only [HalfNatural.toReal] at e
      linarith
    have hup' : r.doubled ≤ t.doubled + d := by exact_mod_cast hup
    have hlo' : t.doubled ≤ r.doubled + d := by exact_mod_cast hlo
    exact Finset.mem_image.mpr ⟨r.doubled, Finset.mem_Icc.mpr ⟨by omega, hup'⟩, rfl⟩
section Functions
variable {J : Type} [Finite J]
theorem finite_and_ncard_le_of_near (B : Set J) (D : ↥B → ℕ) (x : J → HalfNatural)
    {S₀ : Set (J → HalfNatural)}
    (hS₀ : ∀ y ∈ S₀, (∀ b, b ∉ B → y b = x b) ∧
      ∀ b : ↥B, |(y b).toReal - (x b).toReal| ≤ (D b : ℝ) / 2) :
    S₀.Finite ∧ S₀.ncard ≤ ∏ᶠ b, (2 * D b + 1) := by
  classical
  let _ : Fintype ↥B := Fintype.ofFinite _
  choose s hcard hs using fun b : ↥B => exists_finset_near_halfNatural (x b) (D b)
  let S : Finset (↥B → HalfNatural) := Fintype.piFinset s
  have hinj : Set.InjOn (restrictTo B : (J → HalfNatural) → ↥B → HalfNatural) S₀ := by
    intro y hy y' hy' e
    funext b
    by_cases hb : b ∈ B
    · exact congrFun e ⟨b, hb⟩
    · rw [(hS₀ y hy).1 b hb, (hS₀ y' hy').1 b hb]
  have hmaps : (restrictTo B : (J → HalfNatural) → ↥B → HalfNatural) '' S₀ ⊆ (S : Set _) := by
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr fun b => hs b _ ((hS₀ y hy).2 b))
  have hfin : S₀.Finite := Set.Finite.of_finite_image (S.finite_toSet.subset hmaps) hinj
  refine ⟨hfin, ?_⟩
  calc S₀.ncard = ((restrictTo B : (J → HalfNatural) → ↥B → HalfNatural) '' S₀).ncard :=
        hinj.ncard_image.symm
    _ ≤ (S : Set _).ncard := Set.ncard_le_ncard hmaps S.finite_toSet
    _ = S.card := Set.ncard_coe_finset S
    _ = ∏ b, (s b).card := Fintype.card_piFinset _
    _ ≤ ∏ b, (2 * D b + 1) := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun b _ => hcard b
    _ = ∏ᶠ b, (2 * D b + 1) := (finprod_eq_prod_of_fintype _).symm
theorem weightSum_eq_restrictTo_add (B : Set J) (l : J → HalfNatural) :
    weightSum l = weightSum (restrictTo B l) + ∑ᶠ b : ↥Bᶜ, (l b).toReal := by
  have hu : ∑ᶠ b, (l b).toReal = ∑ᶠ b ∈ B ∪ Bᶜ, (l b).toReal := by
    rw [Set.union_compl_self, finsum_mem_univ]
  have hr : weightSum (restrictTo B l) = ∑ᶠ b ∈ B, (l b).toReal :=
    finsum_set_coe_eq_finsum_mem (f := fun b => (l b).toReal) B
  rw [hr, weightSum, hu, finsum_mem_union disjoint_compl_right (Set.toFinite _) (Set.toFinite _),
    finsum_set_coe_eq_finsum_mem (f := fun b => (l b).toReal) Bᶜ]
theorem weightSum_nonneg {K : Type} (l : K → HalfNatural) : 0 ≤ weightSum l :=
  finsum_nonneg fun b => div_nonneg (Nat.cast_nonneg _) (by norm_num)
theorem memLp_two_of_continuousMap (H : C(J → specialUnitary, ℂ)) :
    MemLp (H : (J → specialUnitary) → ℂ) 2 (haarPi J) := by apply _root_.YangMills.Construction.SpinHarmonics.DisjointParts.memLp_two_continuous <;> assumption
theorem norm_toHaarL2_le_mul {H G : C(J → specialUnitary, ℂ)} {c : ℝ} (hle : ∀ u, ‖H u‖ ≤ c * ‖G u‖) :
    ‖toHaarL2 (H : (J → specialUnitary) → ℂ)‖ ≤ c * ‖toHaarL2 (G : (J → specialUnitary) → ℂ)‖ := by
  have hH := memLp_two_of_continuousMap H
  have hG := memLp_two_of_continuousMap G
  have eH : toHaarL2 (H : (J → specialUnitary) → ℂ) = hH.toLp H := dif_pos hH
  have eG : toHaarL2 (G : (J → specialUnitary) → ℂ) = hG.toLp G := dif_pos hG
  rw [eH, eG]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [hH.coeFn_toLp, hG.coeFn_toLp] with u e₁ e₂
  rw [e₁, e₂]
  exact hle u
theorem norm_toHaarL2_zero :
    ‖toHaarL2 (((0 : C(J → specialUnitary, ℂ))) : (J → specialUnitary) → ℂ)‖ = 0 := by
  have hz := norm_toHaarL2_le_mul (H := (0 : C(J → specialUnitary, ℂ))) (G := 0) (c := 0) (by simp)
  exact le_antisymm (by simpa using hz) (norm_nonneg _)
end Functions
theorem norm_le_esupNorm_toReal {K : Type} {f : (K → specialUnitary) → ℂ} (hf : Continuous f)
    (v : K → specialUnitary) : ‖f v‖ ≤ (esupNorm f).toReal := by
  have hfin : esupNorm f ≠ ∞ := by
    let g : C(K → specialUnitary, ℂ) := ⟨f, hf⟩
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ‖g‖)) (iSup_le fun x => ?_)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (g.norm_coe_le_norm x)
  have hv : ‖f v‖ₑ ≤ esupNorm f := le_iSup (fun x => ‖f x‖ₑ) v
  calc ‖f v‖ = ‖f v‖ₑ.toReal := (toReal_enorm _).symm
    _ ≤ _ := ENNReal.toReal_mono hfin hv
theorem mulConst_eq_card_mul_prod (β : ℝ) {K : Type} [Finite K] (D : K → ℕ) :
    mulConst β D = ((∏ᶠ b, (2 * D b + 1) : ℕ) : ℝ) *
      ∏ᶠ b, (besselRatioBound β * (1 + (D b : ℝ))) ^ D b := by
  let _ : Fintype K := Fintype.ofFinite K
  simp only [mulConst, finprod_eq_prod_of_fintype, Finset.prod_mul_distrib]
  push_cast
  rfl
theorem statement_holds
    (hComponents : IsotypicPartSums.Statement)
    (hFields : FieldsPreserveIsotypicSpans.Statement)
    (hMultiplication : MulPullbackComponents.Statement)
    (hRatio : CharCoeffRatioBoundStatement)
    (hDecay : SmoothToSobolevDecayStatement)
    (hWeight : WeightDecaySum.Statement)
    (hProjections : IsotypicProjProperties) :
    Statement := by
  intro J _ _ β B f hf D F hβ hB hD hF
  have hM : ∀ v, ‖f v‖ ≤ (esupNorm f).toReal :=
    norm_le_esupNorm_toReal hf.1.continuous
  have hM0 : 0 ≤ (esupNorm f).toReal := ENNReal.toReal_nonneg
  have hmem : ∀ μ' μ : J → HalfNatural,
      hatDoubleTerm β B f hf F μ' μ ∈ prodCoeffSpan μ' := fun μ' μ =>
    Submodule.smul_mem _ _ ((hComponents J).1 μ' _).1
  have hsupp : ∀ μ' μ : J → HalfNatural, hatDoubleTerm β B f hf F μ' μ ≠ 0 →
      (∀ b, b ∉ B → μ' b = μ b) ∧
        IsDegreeCompatible D (restrictTo B μ) (restrictTo B μ') := by
    intro μ' μ hne
    have hne' : isotypicPartSum μ' (toHaarL2 (mulPullback B f hf
        (isotypicPartSum μ (toHaarL2 (F : (J → specialUnitary) → ℂ))) :
          (J → specialUnitary) → ℂ)) ≠ 0 := by
      intro h0
      apply hne
      simp only [hatDoubleTerm]
      rw [h0, smul_zero]
    exact (hMultiplication J B f hf D μ _ hB hD ((hComponents J).1 μ _).1).2.1 μ' hne'
  have hrow : ∀ μ' : J → HalfNatural,
      {μ : J → HalfNatural | hatDoubleTerm β B f hf F μ' μ ≠ 0}.Finite ∧
      {μ : J → HalfNatural | hatDoubleTerm β B f hf F μ' μ ≠ 0}.ncard ≤ ∏ᶠ b, (2 * D b + 1) :=
    fun μ' => finite_and_ncard_le_of_near B D μ' fun μ hne =>
      ⟨fun b hb => ((hsupp μ' μ hne).1 b hb).symm,
        fun b => (abs_sub_comm _ _).trans_le ((hsupp μ' μ hne).2 b)⟩
  have hcol : ∀ μ : J → HalfNatural,
      {μ' : J → HalfNatural | hatDoubleTerm β B f hf F μ' μ ≠ 0}.Finite ∧
      {μ' : J → HalfNatural | hatDoubleTerm β B f hf F μ' μ ≠ 0}.ncard ≤ ∏ᶠ b, (2 * D b + 1) :=
    fun μ => finite_and_ncard_le_of_near B D μ fun μ' hne => ⟨(hsupp μ' μ hne).1, (hsupp μ' μ hne).2⟩
  have hterm : ∀ μ' μ : J → HalfNatural,
      ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖ ≤
        ‖charCoeffRatio β (restrictTo B μ) (restrictTo B μ')‖ *
          ((esupNorm f).toReal *
            ‖isotypicProj μ (toHaarL2 (F : (J → specialUnitary) → ℂ))‖) := by
    intro μ' μ
    set ψ := isotypicPartSum μ (toHaarL2 (F : (J → specialUnitary) → ℂ)) with hψ
    set X := toHaarL2 (mulPullback B f hf ψ : (J → specialUnitary) → ℂ) with hX
    have e₁ : ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖ ≤
        ‖charCoeffRatio β (restrictTo B μ) (restrictTo B μ')‖ *
          ‖toHaarL2 (isotypicPartSum μ' X : (J → specialUnitary) → ℂ)‖ :=
      norm_toHaarL2_le_mul fun u => by
        simp only [hatDoubleTerm, ContinuousMap.coe_smul, Pi.smul_apply, norm_smul]
        exact le_rfl
    have e₂ : toHaarL2 (isotypicPartSum μ' X : (J → specialUnitary) → ℂ) = isotypicProj μ' X :=
      ((hComponents J).1 μ' X).2.2
    have e₃ : ‖isotypicProj μ' X‖ ≤ ‖X‖ :=
      norm_le_of_idempotent_selfAdjoint _ (hProjections J μ' ⟨0⟩).2.1.1 X
    have e₄ : ‖X‖ ≤ (esupNorm f).toReal * ‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖ :=
      norm_toHaarL2_le_mul fun u => by
        change ‖f (restrictTo B u) * ψ u‖ ≤ _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    have e₅ : toHaarL2 (ψ : (J → specialUnitary) → ℂ) =
        isotypicProj μ (toHaarL2 (F : (J → specialUnitary) → ℂ)) :=
      ((hComponents J).1 μ _).2.2
    rw [e₂] at e₁
    rw [e₅] at e₄
    exact e₁.trans (mul_le_mul_of_nonneg_left (e₃.trans e₄) (norm_nonneg _))
  have hPos : 0 ≤ ∏ᶠ b, (besselRatioBound β * (1 + (D b : ℝ))) ^ D b := by
    refine finprod_nonneg fun b => pow_nonneg (mul_nonneg ?_ (by positivity)) _
    simp only [besselRatioBound]
    positivity
  have hfinite : ∀ p, sobolevDecay p (toHaarL2 (F : (J → specialUnitary) → ℂ)) ≠ ∞ := fun p =>
    ((hDecay J F hF).1 p).ne
  have hA : ∀ l : J → HalfNatural, 0 < 1 + weightSum l := fun l => by
    have := weightSum_nonneg l
    linarith
  have hd0 : (0 : ℝ) ≤ (degreeTotal D : ℝ) / 2 := by positivity
  have hkey : ∀ (p : ℕ) (μ' μ : J → HalfNatural), hatDoubleTerm β B f hf F μ' μ ≠ 0 →
      (1 + weightSum μ') ^ p *
          ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖ ≤
        (∏ᶠ b, (besselRatioBound β * (1 + (D b : ℝ))) ^ D b) *
          (1 + weightSum μ') ^ degreeTotal D * (esupNorm f).toReal *
            (1 + (degreeTotal D : ℝ) / 2) ^ p *
              (sobolevDecay p (toHaarL2 (F : (J → specialUnitary) → ℂ))).toReal := by
    intro p μ' μ hne
    obtain ⟨h₁, h₂⟩ := hsupp μ' μ hne
    obtain ⟨r₁, r₂⟩ := hRatio β ↥B D (restrictTo B μ) (restrictTo B μ') hβ h₂
    have hR : ∑ᶠ b : ↥Bᶜ, (μ' b).toReal = ∑ᶠ b : ↥Bᶜ, (μ b).toReal :=
      finsum_congr fun b => by rw [h₁ b b.2]
    have hR0 : 0 ≤ ∑ᶠ b : ↥Bᶜ, (μ b).toReal :=
      finsum_nonneg fun b => div_nonneg (Nat.cast_nonneg _) (by norm_num)
    have hs' := weightSum_eq_restrictTo_add B μ'
    have hs := weightSum_eq_restrictTo_add B μ
    rw [hR] at hs'
    have w₁ : 1 + weightSum (restrictTo B μ') ≤ 1 + weightSum μ' := by
      rw [hs']
      linarith
    have w₂ : 1 + weightSum μ' ≤ (1 + (degreeTotal D : ℝ) / 2) * (1 + weightSum μ) := by
      rw [hs', hs]
      nlinarith [mul_nonneg hd0 hR0]
    have hl0 : 0 ≤ 1 + weightSum (restrictTo B μ') := by
      have := weightSum_nonneg (restrictTo B μ')
      linarith
    set P := ∏ᶠ b, (besselRatioBound β * (1 + (D b : ℝ))) ^ D b with hP
    set E := ‖isotypicProj μ (toHaarL2 (F : (J → specialUnitary) → ℂ))‖ with hE
    set N := (sobolevDecay p (toHaarL2 (F : (J → specialUnitary) → ℂ))).toReal with hN
    set M := (esupNorm f).toReal with hMdef
    set A := 1 + weightSum μ' with hAdef
    have hQ : ‖charCoeffRatio β (restrictTo B μ) (restrictTo B μ')‖ ≤
        P * A ^ degreeTotal D :=
      r₁.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 w₁ _) hPos)
    have hAp : A ^ p ≤ (1 + (degreeTotal D : ℝ) / 2) ^ p * (1 + weightSum μ) ^ p := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (hA μ').le w₂ _
    have hEN : (1 + weightSum μ) ^ p * E ≤ N := by
      have h₀ : ENNReal.ofReal ((1 + weightSum μ) ^ p * E) ≤
          sobolevDecay p (toHaarL2 (F : (J → specialUnitary) → ℂ)) :=
        le_iSup (fun l : J → HalfNatural => ENNReal.ofReal ((1 + weightSum l) ^ p *
          ‖isotypicProj l (toHaarL2 (F : (J → specialUnitary) → ℂ))‖)) μ
      exact (ENNReal.ofReal_le_iff_le_toReal (hfinite p)).1 h₀
    have hA0 : 0 ≤ A ^ p := pow_nonneg (hA μ').le _
    have hQ0 : 0 ≤ P * A ^ degreeTotal D := mul_nonneg hPos (pow_nonneg (hA μ').le _)
    have hE0 : 0 ≤ E := norm_nonneg _
    have hd1 : 0 ≤ (1 + (degreeTotal D : ℝ) / 2) ^ p := by positivity
    calc A ^ p * ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖
        ≤ A ^ p * (‖charCoeffRatio β (restrictTo B μ) (restrictTo B μ')‖ * (M * E)) :=
          mul_le_mul_of_nonneg_left (hterm μ' μ) hA0
      _ ≤ A ^ p * ((P * A ^ degreeTotal D) * (M * E)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hQ (mul_nonneg hM0 hE0)) hA0
      _ ≤ ((1 + (degreeTotal D : ℝ) / 2) ^ p * (1 + weightSum μ) ^ p) *
            ((P * A ^ degreeTotal D) * (M * E)) :=
          mul_le_mul_of_nonneg_right hAp (mul_nonneg hQ0 (mul_nonneg hM0 hE0))
      _ = P * A ^ degreeTotal D * M * (1 + (degreeTotal D : ℝ) / 2) ^ p *
            ((1 + weightSum μ) ^ p * E) := by ring
      _ ≤ P * A ^ degreeTotal D * M * (1 + (degreeTotal D : ℝ) / 2) ^ p * N :=
          mul_le_mul_of_nonneg_left hEN (mul_nonneg (mul_nonneg hQ0 hM0) hd1)
  have hzero : ∀ μ' μ : J → HalfNatural, hatDoubleTerm β B f hf F μ' μ = 0 →
      ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖ = 0 := by
    intro μ' μ h0
    rw [h0]
    exact norm_toHaarL2_zero
  have hbound : ∀ (p : ℕ) (μ' : J → HalfNatural), (1 + weightSum μ') ^ p *
        ∑' μ : J → HalfNatural,
          ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖ ≤
      mulConst β D * (esupNorm f).toReal *
        (1 + (degreeTotal D : ℝ) / 2) ^ p *
        (sobolevDecay p (toHaarL2 (F : (J → specialUnitary) → ℂ))).toReal *
        (1 + weightSum μ') ^ degreeTotal D := by
    intro p μ'
    classical
    obtain ⟨hfin, hcard⟩ := hrow μ'
    have htsum : ∑' μ : J → HalfNatural,
        ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖ =
        ∑ μ ∈ hfin.toFinset,
          ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖ :=
      tsum_eq_sum fun μ hl => hzero μ' μ (by simpa using hl)
    set K := (∏ᶠ b, (besselRatioBound β * (1 + (D b : ℝ))) ^ D b) *
      (1 + weightSum μ') ^ degreeTotal D * (esupNorm f).toReal *
        (1 + (degreeTotal D : ℝ) / 2) ^ p *
          (sobolevDecay p (toHaarL2 (F : (J → specialUnitary) → ℂ))).toReal with hK
    have hK0 : 0 ≤ K := by
      have h₁ : 0 ≤ (1 + weightSum μ') ^ degreeTotal D := pow_nonneg (hA μ').le _
      have h₂ : 0 ≤ (1 + (degreeTotal D : ℝ) / 2) ^ p := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hPos h₁) hM0) h₂)
        ENNReal.toReal_nonneg
    have hcard' : (hfin.toFinset.card : ℝ) ≤ ((∏ᶠ b, (2 * D b + 1) : ℕ) : ℝ) := by
      rw [← Set.ncard_eq_toFinset_card _ hfin]
      exact_mod_cast hcard
    rw [htsum, Finset.mul_sum]
    calc ∑ μ ∈ hfin.toFinset, (1 + weightSum μ') ^ p *
          ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖
        ≤ ∑ _μ ∈ hfin.toFinset, K :=
          Finset.sum_le_sum fun μ hl => hkey p μ' μ (by simpa using hl)
      _ = (hfin.toFinset.card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((∏ᶠ b, (2 * D b + 1) : ℕ) : ℝ) * K := mul_le_mul_of_nonneg_right hcard' hK0
      _ = _ := by
          rw [mulConst_eq_card_mul_prod, hK]
          ring
  refine ⟨hmem, fun μ' μ hne => hsupp μ' μ hne, hrow, hcol, hbound, ?_⟩
  intro w
  have hW : ∀ l : J → HalfNatural, 0 ≤ ∏ᶠ b, (2 * (l b).toReal + 1) := fun l =>
    finprod_nonneg fun b => by
      have : 0 ≤ (l b).toReal := div_nonneg (Nat.cast_nonneg _) (by norm_num)
      linarith
  have hS0 : ∀ μ' μ : J → HalfNatural,
      0 ≤ supNorm (fieldWord w (hatDoubleTerm β B f hf F μ' μ)) :=
    fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hSle : ∀ μ' μ : J → HalfNatural,
      supNorm (fieldWord w (hatDoubleTerm β B f hf F μ' μ)) ≤
        (∏ᶠ b, (2 * (μ' b).toReal + 1)) * (1 + weightSum μ') ^ w.length *
          ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖ := by
    intro μ' μ
    obtain ⟨hEx, -, -, hL2⟩ := hFields J μ' _ (hmem μ' μ)
    obtain ⟨φ, hφ, hφe⟩ := hEx w
    have a₁ := (hFields J μ' φ hφ).2.2.1
    have a₂ := hL2 w
    rw [← hφe] at a₂
    have hP0 : 0 ≤ (1 + weightSum μ') ^ w.length := pow_nonneg (hA μ').le _
    unfold supNorm
    rw [← hφe]
    refine Real.iSup_le (fun u => ?_)
      (mul_nonneg (mul_nonneg (hW μ') hP0) (norm_nonneg _))
    calc ‖φ u‖ ≤ ‖φ‖ := φ.norm_coe_le_norm u
      _ ≤ _ := a₁
      _ ≤ (∏ᶠ b, (2 * (μ' b).toReal + 1)) * ((1 + weightSum μ') ^ w.length *
            ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖) :=
          mul_le_mul_of_nonneg_left a₂ (hW μ')
      _ = _ := by ring
  have hSzero : ∀ μ' μ : J → HalfNatural, hatDoubleTerm β B f hf F μ' μ = 0 →
      supNorm (fieldWord w (hatDoubleTerm β B f hf F μ' μ)) = 0 := by
    intro μ' μ h0
    refine le_antisymm ?_ (hS0 μ' μ)
    have h₁ := hSle μ' μ
    rwa [hzero μ' μ h0, mul_zero] at h₁
  have hSrow : ∀ μ' : J → HalfNatural, Summable fun μ : J → HalfNatural =>
      supNorm (fieldWord w (hatDoubleTerm β B f hf F μ' μ)) := fun μ' =>
    summable_of_hasFiniteSupport ((hrow μ').1.subset fun μ hl h0 => hl (hSzero μ' μ h0))
  have hTrow : ∀ μ' : J → HalfNatural, Summable fun μ : J → HalfNatural =>
      ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖ := fun μ' =>
    summable_of_hasFiniteSupport ((hrow μ').1.subset fun μ hl h0 => hl (hzero μ' μ h0))
  set q₀ := 2 * Nat.card J + 1 with hq₀
  set p := w.length + degreeTotal D + q₀ with hp
  set K := mulConst β D * (esupNorm f).toReal *
    (1 + (degreeTotal D : ℝ) / 2) ^ p *
    (sobolevDecay p (toHaarL2 (F : (J → specialUnitary) → ℂ))).toReal with hK
  have hle : ∀ μ' : J → HalfNatural,
      ∑' μ : J → HalfNatural, supNorm (fieldWord w (hatDoubleTerm β B f hf F μ' μ)) ≤
        K * weightDecayTerm q₀ μ' := by
    intro μ'
    set T := ∑' μ : J → HalfNatural,
      ‖toHaarL2 (hatDoubleTerm β B f hf F μ' μ : (J → specialUnitary) → ℂ)‖ with hT
    set A := 1 + weightSum μ' with hAdef
    have hA0 : 0 < A := hA μ'
    have h₁ : ∑' μ : J → HalfNatural,
        supNorm (fieldWord w (hatDoubleTerm β B f hf F μ' μ)) ≤
        (∏ᶠ b, (2 * (μ' b).toReal + 1)) * A ^ w.length * T := by
      rw [hT, ← tsum_mul_left]
      exact (hSrow μ').tsum_le_tsum (fun μ => hSle μ' μ) ((hTrow μ').mul_left _)
    have h₂ : A ^ p * T ≤ K * A ^ degreeTotal D := hbound p μ'
    have h₃ : A ^ w.length * T ≤ K * (A ^ q₀)⁻¹ := by
      have hq : 0 < A ^ q₀ := pow_pos hA0 _
      have hd : 0 < A ^ degreeTotal D := pow_pos hA0 _
      rw [← div_eq_mul_inv, le_div_iff₀ hq]
      refine le_of_mul_le_mul_right ?_ hd
      calc A ^ w.length * T * A ^ q₀ * A ^ degreeTotal D = A ^ p * T := by
            rw [hp, pow_add, pow_add]
            ring
        _ ≤ K * A ^ degreeTotal D := h₂
    calc _ ≤ (∏ᶠ b, (2 * (μ' b).toReal + 1)) * A ^ w.length * T := h₁
      _ = (∏ᶠ b, (2 * (μ' b).toReal + 1)) * (A ^ w.length * T) := by ring
      _ ≤ (∏ᶠ b, (2 * (μ' b).toReal + 1)) * (K * (A ^ q₀)⁻¹) :=
          mul_le_mul_of_nonneg_left h₃ (hW μ')
      _ = K * weightDecayTerm q₀ μ' := by
          simp only [weightDecayTerm]
          ring
  refine (summable_prod_of_nonneg (fun q => hS0 q.1 q.2)).2 ⟨hSrow, ?_⟩
  exact Summable.of_nonneg_of_le (fun μ' => tsum_nonneg fun μ => hS0 μ' μ) hle
    (((hWeight J).1 q₀ le_rfl).mul_left K)
end YangMills.Construction.SpinHarmonics.HatDoubleTerms
end
