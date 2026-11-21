import YangMills.Construction.FourPointCondition.RiemannSumOfTheBareTracesProof
import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBounded
import YangMills.Construction.FreeEnergiesOfTheFlow.FittedResponsesAreMeans
import YangMills.Construction.InfiniteLattice.MomentsAndCumulantsUnderTwoMeasures
import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOnACircle
import YangMills.Construction.LawByMomentsOfTheFlow.LawAtLimitPointsProof
import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevelProof
import YangMills.Construction.ReflectionPositivity.CentredMomentsAreSumsOfCumulantsProof
import YangMills.Construction.ResponseInTheExpansion.LevelsBelowATuple
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheMarksBelowALevel
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheMeanScores
import YangMills.Construction.ResponseInTheExpansion.SitesOfAFunctionAtALevel
import YangMills.Construction.ResponseInTheExpansion.TheWeightsOfATupleAreLocalProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open CutoffLimits WeightedResponses
section
private theorem norm_prod_sub_prod_le {ι 𝕜 : Type} [NormedField 𝕜] [DecidableEq ι] (P : Finset ι) (a b : ι → 𝕜) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 1 ≤ B)
    (hd : ∀ I ∈ P, ‖a I - b I‖ ≤ δ) (hb : ∀ I ∈ P, ‖b I‖ ≤ B) :
    ‖∏ I ∈ P, a I - ∏ I ∈ P, b I‖ ≤ (P.card : ℝ) * (B + δ) ^ P.card * δ ∧ ‖∏ I ∈ P, b I‖ ≤ (B + δ) ^ P.card := by
  have h1 : 1 ≤ B + δ := by linarith
  induction P using Finset.induction_on with
  | empty => simp
  | insert I P hI ih =>
    obtain ⟨i1, i2⟩ := ih (fun J hJ => hd J (Finset.mem_insert_of_mem hJ)) (fun J hJ => hb J (Finset.mem_insert_of_mem hJ))
    have hdI := hd I (Finset.mem_insert_self I P)
    have hbI := hb I (Finset.mem_insert_self I P)
    have haI : ‖a I‖ ≤ B + δ := by
      have : a I = (a I - b I) + b I := by ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      linarith
    rw [Finset.prod_insert hI, Finset.prod_insert hI, Finset.card_insert_of_notMem hI]
    have e : a I * ∏ J ∈ P, a J - b I * ∏ J ∈ P, b J =
        a I * (∏ J ∈ P, a J - ∏ J ∈ P, b J) + (a I - b I) * ∏ J ∈ P, b J := by ring
    have hp : (1 : ℝ) ≤ (B + δ) ^ P.card := one_le_pow₀ h1
    constructor
    · rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have t1 : ‖a I‖ * ‖∏ J ∈ P, a J - ∏ J ∈ P, b J‖ ≤ (B + δ) * ((P.card : ℝ) * (B + δ) ^ P.card * δ) :=
        mul_le_mul haI i1 (norm_nonneg _) (by linarith)
      have t2 : ‖a I - b I‖ * ‖∏ J ∈ P, b J‖ ≤ δ * (B + δ) ^ P.card :=
        mul_le_mul hdI i2 (norm_nonneg _) hδ
      have t3 : δ * (B + δ) ^ P.card ≤ δ * (B + δ) ^ (P.card + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hδ
        rw [pow_succ]
        nlinarith
      push_cast
      rw [pow_succ]
      rw [pow_succ] at t3
      nlinarith
    · rw [norm_mul, pow_succ, mul_comm]
      exact mul_le_mul i2 (by linarith) (norm_nonneg _) (by linarith)
private def maxBlockCount (n : ℕ) : ℕ := Finset.univ.sup fun π : SetPartition.PartitionsFin n => SetPartition.blockCount π
private def cumulantComparisonConstant (n : ℕ) : ℝ :=
  ∑ π : SetPartition.PartitionsFin n, ((SetPartition.blockCount π - 1).factorial : ℝ) * (SetPartition.blockCount π : ℝ)
private theorem blockMean_eq_integral {𝒳 : Type} [MeasurableSpace 𝒳] (ν : Measure 𝒳) {n : ℕ} (Y : Fin n → 𝒳 → ℝ)
    (I : Finset (Fin n)) : CutoffLimits.TwoMeasures.blockMean ν Y I = ((∫ x, ∏ i ∈ I, Y i x ∂ν : ℝ) : ℂ) := by
  unfold CutoffLimits.TwoMeasures.blockMean CutoffLimits.TwoMeasures.blockProduct Probability.complexExpectation
  exact integral_ofReal
private theorem norm_mixedCumulant_sub_le (hC : CutoffLimits.TwoMeasures.CumulantComparison) {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (μ : Measure Ω₁) (ν : Measure Ω₂) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (hn : 1 ≤ n) (X : Fin n → Ω₁ → ℝ) (Y : Fin n → Ω₂ → ℝ) (hX : ∀ i, Probability.IsBoundedRealRV (X i))
    (hY : ∀ i, Probability.IsBoundedRealRV (Y i)) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 1 ≤ B)
    (hd : ∀ I : Finset (Fin n), |∫ x, ∏ i ∈ I, X i x ∂μ - ∫ x, ∏ i ∈ I, Y i x ∂ν| ≤ δ)
    (hb : ∀ I : Finset (Fin n), |∫ x, ∏ i ∈ I, Y i x ∂ν| ≤ B) :
    ‖Cumulants.mixedCumulant μ X - Cumulants.mixedCumulant ν Y‖ ≤ cumulantComparisonConstant n * (B + δ) ^ maxBlockCount n * δ := by
  have h1 : 1 ≤ B + δ := by linarith
  have hμ := (hC.1 Ω₁ μ μ n X hn hX).2.1
  have hν := (hC.1 Ω₂ ν ν n Y hn hY).2.1
  rw [hμ, hν, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [cumulantComparisonConstant, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun π _ => ?_
  rw [← mul_sub, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
  have hp := (norm_prod_sub_prod_le π.parts (CutoffLimits.TwoMeasures.blockMean μ X) (CutoffLimits.TwoMeasures.blockMean ν Y) δ B hδ hB
    (fun I _ => by
      rw [blockMean_eq_integral, blockMean_eq_integral, ← Complex.ofReal_sub, Complex.norm_real]
      exact hd I)
    (fun I _ => by
      rw [blockMean_eq_integral, Complex.norm_real]
      exact hb I)).1
  have hle : (B + δ) ^ π.parts.card ≤ (B + δ) ^ maxBlockCount n :=
    pow_le_pow_right₀ h1 (Finset.le_sup (f := fun π : SetPartition.PartitionsFin n => SetPartition.blockCount π) (Finset.mem_univ π))
  have hc : (SetPartition.blockCount π : ℝ) = (π.parts.card : ℝ) := rfl
  rw [hc]
  calc ((SetPartition.blockCount π - 1).factorial : ℝ) * ‖∏ I ∈ π.parts, CutoffLimits.TwoMeasures.blockMean μ X I - ∏ I ∈ π.parts, CutoffLimits.TwoMeasures.blockMean ν Y I‖
      ≤ ((SetPartition.blockCount π - 1).factorial : ℝ) * ((π.parts.card : ℝ) * (B + δ) ^ π.parts.card * δ) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ ((SetPartition.blockCount π - 1).factorial : ℝ) * ((π.parts.card : ℝ) * (B + δ) ^ maxBlockCount n * δ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ hδ
        exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = ((SetPartition.blockCount π - 1).factorial : ℝ) * (π.parts.card : ℝ) * (B + δ) ^ maxBlockCount n * δ := by ring
private theorem mixedCumulant_congr_ae {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ} (X X' : Fin n → Ω → ℝ)
    (h : ∀ i, X i =ᵐ[μ] X' i) : Cumulants.mixedCumulant μ X = Cumulants.mixedCumulant μ X' := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.CentredMomentExpansion.mixedCumulant_congr_ae <;> assumption
private theorem exists_bounded_ae_eq {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (F : Ω → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ᵐ ω ∂μ, |F ω| ≤ C) :
    ∃ F' : Ω → ℝ, Probability.IsBoundedRealRV F' ∧ F =ᵐ[μ] F' := by
  refine ⟨fun ω => max (-|C|) (min |C| (F ω)), ⟨measurable_const.max (measurable_const.min hF), |C|, fun ω => ?_⟩, ?_⟩
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith [abs_nonneg C]) (min_le_left _ _)⟩
  · filter_upwards [hC] with ω hω
    have h := abs_le.1 (hω.trans (le_abs_self C))
    rw [min_eq_right h.2, max_eq_right h.1]
private theorem mixedCumulant_comparison_of_conditional (hC : CutoffLimits.TwoMeasures.CumulantComparison)
    (hS : Cumulants.MomentCumulantRelations.Holds) {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ : Measure Ω₁) (ν : Measure Ω₂) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (p : ℕ) (hp : 2 ≤ p)
    (O : Fin p → Ω₁ → ℝ) (F Φ Nn : Fin p → Ω₂ → ℝ) (κ : Fin p → ℝ) (G : Finset (Fin p) → Ω₂ → ℝ) (ε A E : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A) (hE : 1 ≤ E)
    (hO : ∀ i, Probability.IsBoundedRealRV (O i)) (hFm : ∀ i, Measurable (F i))
    (hFb : ∀ i, ∃ C : ℝ, ∀ᵐ u ∂ν, |F i u| ≤ C)
    (hN1 : ∀ i, ∀ᵐ u ∂ν, 1 ≤ Nn i u)
    (hG : ∀ I, Integrable (G I) ν) (hNi : ∀ I : Finset (Fin p), Integrable (fun u => ∏ i ∈ I, Nn i u) ν)
    (hNE : ∀ I : Finset (Fin p), ∫ u, ∏ i ∈ I, Nn i u ∂ν ≤ E)
    (h1 : ∀ I : Finset (Fin p), I.Nonempty → ∫ x, ∏ i ∈ I, (O i x - κ i) ∂μ = ∫ u, G I u ∂ν)
    (h2 : ∀ I : Finset (Fin p), I.Nonempty → ∀ᵐ u ∂ν, |G I u - ∏ i ∈ I, Φ i u| ≤ ε * ∏ i ∈ I, Nn i u)
    (h3 : ∀ i, ∀ᵐ u ∂ν, |F i u - κ i - Φ i u| ≤ ε * Nn i u)
    (h4 : ∀ i, ∀ᵐ u ∂ν, |Φ i u| ≤ A * Nn i u) :
    ‖Cumulants.mixedCumulant μ O - Cumulants.mixedCumulant ν F‖ ≤
      cumulantComparisonConstant p * ((A + 1) ^ p * E + 1 + ε * (1 + p * (A + 2) ^ p) * E) ^ maxBlockCount p *
        (ε * (1 + p * (A + 2) ^ p) * E) := by
  classical
  obtain ⟨hprob₁, -⟩ := And.intro (inferInstance : IsProbabilityMeasure μ) True.intro
  have hver : ∀ i, ∃ F' : Ω₂ → ℝ, Probability.IsBoundedRealRV F' ∧ F i =ᵐ[ν] F' := fun i => by
    obtain ⟨C, hC'⟩ := hFb i
    exact exists_bounded_ae_eq ν (F i) (hFm i) C hC'
  choose F' hF'b hF'e using hver
  let X : Fin p → Ω₁ → ℝ := fun i x => O i x + (-κ i)
  let Y : Fin p → Ω₂ → ℝ := fun i u => F' i u + (-κ i)
  have hXb : ∀ i, Probability.IsBoundedRealRV (X i) := fun i => by
    obtain ⟨C, hC'⟩ := (hO i).bounded
    exact ⟨(hO i).measurable.add_const _, C + |κ i|, fun ω => (abs_add_le _ _).trans (by
      rw [abs_neg]; linarith [hC' ω])⟩
  have hYb : ∀ i, Probability.IsBoundedRealRV (Y i) := fun i => by
    obtain ⟨C, hC'⟩ := (hF'b i).bounded
    exact ⟨(hF'b i).measurable.add_const _, C + |κ i|, fun ω => (abs_add_le _ _).trans (by
      rw [abs_neg]; linarith [hC' ω])⟩
  have hshift₁ : Cumulants.mixedCumulant μ X = Cumulants.mixedCumulant μ O :=
    (hS Ω₁ μ).2.2.1 p O (fun i => -κ i) hp fun i => hO i
  have hshift₂ : Cumulants.mixedCumulant ν Y = Cumulants.mixedCumulant ν F' :=
    (hS Ω₂ ν).2.2.1 p F' (fun i => -κ i) hp fun i => hF'b i
  have hcongr : Cumulants.mixedCumulant ν F = Cumulants.mixedCumulant ν F' := mixedCumulant_congr_ae ν F F' hF'e
  rw [← hshift₁, hcongr, ← hshift₂]
  have hall : ∀ᵐ u ∂ν, ∀ i, 1 ≤ Nn i u ∧ |Y i u - Φ i u| ≤ ε * Nn i u ∧ |Φ i u| ≤ A * Nn i u := by
    refine ae_all_iff.2 fun i => ?_
    filter_upwards [hN1 i, h3 i, h4 i, hF'e i] with u a b c d
    refine ⟨a, ?_, c⟩
    show |F' i u + -κ i - Φ i u| ≤ _
    rw [← d]
    have : F i u + -κ i - Φ i u = F i u - κ i - Φ i u := by ring
    rw [this]
    exact b
  have hYN : ∀ᵐ u ∂ν, ∀ i, |Y i u| ≤ (A + 1) * Nn i u := by
    filter_upwards [hall] with u hu i
    obtain ⟨a, b, c⟩ := hu i
    have e : Y i u = (Y i u - Φ i u) + Φ i u := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    nlinarith
  have hprodpos : ∀ᵐ u ∂ν, ∀ I : Finset (Fin p), 1 ≤ ∏ i ∈ I, Nn i u := by
    filter_upwards [hall] with u hu I
    exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      fun i _ => (hu i).1
  have hYint : ∀ I : Finset (Fin p), Integrable (fun u => ∏ i ∈ I, Y i u) ν := fun I => by
    have hm : Measurable fun u => ∏ i ∈ I, Y i u := Finset.measurable_fun_prod _ fun i _ => (hYb i).measurable
    choose Cy hCy using fun i => (hYb i).bounded
    refine Integrable.of_bound hm.aestronglyMeasurable (∏ i ∈ I, Cy i) (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => hCy i u
  have hAp : ∀ I : Finset (Fin p), (A + 1) ^ I.card ≤ (A + 1) ^ p := fun I =>
    pow_le_pow_right₀ (by linarith) (by simpa using Finset.card_le_univ I)
  have hAp2 : ∀ I : Finset (Fin p), (A + 2) ^ I.card ≤ (A + 2) ^ p := fun I =>
    pow_le_pow_right₀ (by linarith) (by simpa using Finset.card_le_univ I)
  have hmom : ∀ I : Finset (Fin p), |∫ u, ∏ i ∈ I, Y i u ∂ν| ≤ (A + 1) ^ p * E + 1 := by
    intro I
    have hb : ∀ᵐ u ∂ν, ‖∏ i ∈ I, Y i u‖ ≤ (A + 1) ^ p * ∏ i ∈ I, Nn i u := by
      filter_upwards [hYN, hall, hprodpos] with u hu hu' hpos
      rw [Real.norm_eq_abs, Finset.abs_prod]
      calc ∏ i ∈ I, |Y i u| ≤ ∏ i ∈ I, ((A + 1) * Nn i u) :=
            Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => hu i
        _ = (A + 1) ^ I.card * ∏ i ∈ I, Nn i u := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
        _ ≤ (A + 1) ^ p * ∏ i ∈ I, Nn i u :=
            mul_le_mul_of_nonneg_right (hAp I) (by linarith [hpos I])
    have h5 := norm_integral_le_of_norm_le ((hNi I).const_mul ((A + 1) ^ p)) hb
    rw [integral_const_mul, Real.norm_eq_abs] at h5
    have h6 := mul_le_mul_of_nonneg_left (hNE I) (by positivity : 0 ≤ (A + 1) ^ p)
    linarith
  have hdiff : ∀ I : Finset (Fin p), |∫ x, ∏ i ∈ I, X i x ∂μ - ∫ u, ∏ i ∈ I, Y i u ∂ν| ≤
      ε * (1 + p * (A + 2) ^ p) * E := by
    intro I
    have hnn : 0 ≤ ε * (1 + p * (A + 2) ^ p) * E := by positivity
    rcases I.eq_empty_or_nonempty with rfl | hI
    · simpa using hnn
    have hX : ∫ x, ∏ i ∈ I, X i x ∂μ = ∫ u, G I u ∂ν := by
      rw [← h1 I hI]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      refine Finset.prod_congr rfl fun i _ => ?_
      show O i x + -κ i = O i x - κ i
      ring
    rw [hX, ← integral_sub (hG I) (hYint I)]
    have hb : ∀ᵐ u ∂ν, ‖G I u - ∏ i ∈ I, Y i u‖ ≤ (ε * (1 + p * (A + 2) ^ p)) * ∏ i ∈ I, Nn i u := by
      filter_upwards [h2 I hI, hall, hprodpos] with u hu hu' hpos
      have hne : ∀ i, Nn i u ≠ 0 := fun i => by linarith [(hu' i).1]
      let a : Fin p → ℝ := fun i => Φ i u / Nn i u
      let b : Fin p → ℝ := fun i => Y i u / Nn i u
      have hNp : ∀ i, 0 < Nn i u := fun i => by linarith [(hu' i).1]
      have hab := norm_prod_sub_prod_le I b a ε A hε hA
        (fun i _ => by
          have e : b i - a i = (Y i u - Φ i u) / Nn i u := by simp only [a, b]; ring
          rw [e, Real.norm_eq_abs, abs_div, abs_of_pos (hNp i), div_le_iff₀ (hNp i)]
          exact (hu' i).2.1)
        (fun i _ => by
          show ‖Φ i u / Nn i u‖ ≤ A
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (hNp i), div_le_iff₀ (hNp i)]
          exact (hu' i).2.2)
      have hprodb : ∏ i ∈ I, Y i u = (∏ i ∈ I, b i) * ∏ i ∈ I, Nn i u := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp only [b]
        field_simp [hne i]
      have hproda : ∏ i ∈ I, Φ i u = (∏ i ∈ I, a i) * ∏ i ∈ I, Nn i u := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp only [a]
        field_simp [hne i]
      have hPN : 0 ≤ ∏ i ∈ I, Nn i u := by linarith [hpos I]
      have hsub : |∏ i ∈ I, Φ i u - ∏ i ∈ I, Y i u| ≤ ε * (p * (A + 2) ^ p) * ∏ i ∈ I, Nn i u := by
        rw [hprodb, hproda, ← sub_mul, abs_mul, abs_of_nonneg hPN, abs_sub_comm]
        refine mul_le_mul_of_nonneg_right ?_ hPN
        have h0 := hab.1
        rw [Real.norm_eq_abs] at h0
        refine h0.trans ?_
        have hc : (I.card : ℝ) ≤ p := by exact_mod_cast (by simpa using Finset.card_le_univ I)
        have hpw : (A + ε) ^ I.card ≤ (A + 2) ^ p :=
          (pow_le_pow_left₀ (by linarith) (by linarith) _).trans (hAp2 I)
        have : (I.card : ℝ) * (A + ε) ^ I.card ≤ p * (A + 2) ^ p :=
          mul_le_mul hc hpw (by positivity) (by positivity)
        nlinarith
      rw [Real.norm_eq_abs]
      have e : G I u - ∏ i ∈ I, Y i u = (G I u - ∏ i ∈ I, Φ i u) + (∏ i ∈ I, Φ i u - ∏ i ∈ I, Y i u) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have e2 : ε * (1 + p * (A + 2) ^ p) * ∏ i ∈ I, Nn i u =
          ε * ∏ i ∈ I, Nn i u + ε * (p * (A + 2) ^ p) * ∏ i ∈ I, Nn i u := by ring
      rw [e2]
      exact add_le_add hu hsub
    have h5 := norm_integral_le_of_norm_le ((hNi I).const_mul (ε * (1 + p * (A + 2) ^ p))) hb
    rw [integral_const_mul, Real.norm_eq_abs] at h5
    refine h5.trans ?_
    exact mul_le_mul_of_nonneg_left (hNE I) (by positivity)
  exact norm_mixedCumulant_sub_le hC μ ν p (by omega) X Y hXb hYb _ _ (by positivity) (by nlinarith [pow_pos (by linarith : (0:ℝ) < A + 1) p]) hdiff hmom
end
section
open TorusFields TorusLumps FreeEnergies TorusMetric
private def fineFunctionOf (L k m : ℕ) (f : PeriodicLattice.FourTorus L m → ℝ) : FinePlaquetteFunction :=
  fun x => f (torusProj (PeriodicLattice.torusSide L m) fun i => x i / (L : ℝ) ^ k)
private theorem fineSide_cast_eq (L k m : ℕ) :
    ((fineSide L k (2 * L ^ m) : ℕ) : ℝ) = PeriodicLattice.torusSide L m * (L : ℝ) ^ k := by
  simp only [fineSide_eq, PeriodicLattice.torusSide]
  push_cast
  ring
private theorem torusSide_pos (L m : ℕ) (hL : 0 < L) : 0 < PeriodicLattice.torusSide L m := by apply _root_.YangMills.SharedProofs.p16249 <;> assumption
private theorem euclidNormVec_mul (v : Fin 4 → ℝ) {M : ℝ} (hM : 0 ≤ M) :
    euclidNormVec (fun a => v a * M) = M * euclidNormVec v := by
  unfold euclidNormVec
  have : ∑ μ, (v μ * M) ^ 2 = M ^ 2 * ∑ μ, v μ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [this, Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]
private theorem coe_circleRep (c t : ℝ) : ((LevelTestFunctions.circleRep c t : ℝ) : AddCircle c) = (t : AddCircle c) := by
  unfold LevelTestFunctions.circleRep
  rw [AddCircle.coe_sub]
  have : ((c * (round (t / c) : ℝ) : ℝ) : AddCircle c) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨round (t / c), by rw [zsmul_eq_mul]; ring⟩
  rw [this, sub_zero]
private theorem pow_mul_euclidDistTorus_le_fineDist (hC : LevelTestFunctions.CircleRepProperties) (L k m : ℕ) (hL : 0 < L) (x z : Fin 4 → ℝ) :
    (L : ℝ) ^ k * TestFunctions.euclidDistTorus (torusProj (PeriodicLattice.torusSide L m) fun i => x i / (L : ℝ) ^ k)
        (torusProj (PeriodicLattice.torusSide L m) fun i => z i / (L : ℝ) ^ k) ≤
      MomentSetup.fineDist (fineSide L k (2 * L ^ m)) x z := by
  obtain ⟨-, -, -, -, -, hsc, -⟩ := hC
  have hM : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  have hc := torusSide_pos L m hL
  set c := PeriodicLattice.torusSide L m with hcdef
  let v : Fin 4 → ℝ := fun a => LevelTestFunctions.circleRep c ((x a - z a) / (L : ℝ) ^ k)
  have hcover : torusProj c v = (torusProj c fun i => x i / (L : ℝ) ^ k) - torusProj c fun i => z i / (L : ℝ) ^ k := by
    funext a
    show ((v a : ℝ) : AddCircle c) = ((x a / (L : ℝ) ^ k : ℝ) : AddCircle c) - ((z a / (L : ℝ) ^ k : ℝ) : AddCircle c)
    rw [coe_circleRep, ← AddCircle.coe_sub, sub_div]
  have hle : TestFunctions.euclidDistTorus (torusProj c fun i => x i / (L : ℝ) ^ k) (torusProj c fun i => z i / (L : ℝ) ^ k) ≤
      euclidNormVec v := by
    unfold TestFunctions.euclidDistTorus torusEuclidNorm
    refine csInf_le ⟨0, ?_⟩ ⟨v, hcover, rfl⟩
    rintro _ ⟨w, -, rfl⟩
    exact Real.sqrt_nonneg _
  have e : MomentSetup.fineDist (fineSide L k (2 * L ^ m)) x z = euclidNormVec fun a => v a * (L : ℝ) ^ k := by
    unfold MomentSetup.fineDist
    congr 1
    funext a
    rw [fineSide_cast_eq, ← hcdef]
    simp only [v]
    rw [← hsc c _ hc hM]
    congr 1
    field_simp
  rw [e, euclidNormVec_mul v hM.le]
  exact mul_le_mul_of_nonneg_left hle hM.le
private theorem abs_circleRep_le (hC : LevelTestFunctions.CircleRepProperties) (L k m : ℕ) (hL : 0 < L) (x z : Fin 4 → ℝ) (q : Fin 4) :
    |LevelTestFunctions.circleRep (fineSide L k (2 * L ^ m)) (x q - z q)| ≤
      (L : ℝ) ^ k * TestFunctions.euclidDistTorus (torusProj (PeriodicLattice.torusSide L m) fun i => x i / (L : ℝ) ^ k)
        (torusProj (PeriodicLattice.torusSide L m) fun i => z i / (L : ℝ) ^ k) := by
  obtain ⟨hper, hsh, -, -, -, hsc, -⟩ := hC
  have hM : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  have hc := torusSide_pos L m hL
  set c := PeriodicLattice.torusSide L m with hcdef
  set t : ℝ := (x q - z q) / (L : ℝ) ^ k with ht
  have e : LevelTestFunctions.circleRep (fineSide L k (2 * L ^ m)) (x q - z q) = LevelTestFunctions.circleRep c t * (L : ℝ) ^ k := by
    rw [fineSide_cast_eq, ← hcdef, ← hsc c _ hc hM]
    congr 1
    rw [ht]
    field_simp
  rw [e, abs_mul, abs_of_pos hM, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hM.le
  unfold TestFunctions.euclidDistTorus torusEuclidNorm
  refine le_csInf ⟨_, (fun i => x i / (L : ℝ) ^ k) - (fun i => z i / (L : ℝ) ^ k), ?_, rfl⟩ ?_
  · show torusProj c _ = _
    funext a
    show (((x a / (L : ℝ) ^ k - z a / (L : ℝ) ^ k : ℝ)) : AddCircle c) = _ - _
    rw [AddCircle.coe_sub]
    rfl
  · rintro _ ⟨v, hv, rfl⟩
    have hv' : ((v q : ℝ) : AddCircle c) = ((x q / (L : ℝ) ^ k : ℝ) : AddCircle c) - ((z q / (L : ℝ) ^ k : ℝ) : AddCircle c) :=
      congrFun hv q
    have h0 : ((v q - t : ℝ) : AddCircle c) = 0 := by
      rw [AddCircle.coe_sub, hv', ht, sub_div, AddCircle.coe_sub, sub_self]
    obtain ⟨e', he⟩ := (AddCircle.coe_eq_zero_iff c).1 h0
    have hv2 : v q = t + c * e' := by
      rw [zsmul_eq_mul] at he
      linarith
    have h1 : LevelTestFunctions.circleRep c t = LevelTestFunctions.circleRep c (v q) := by rw [hv2, hper c hc]
    rw [h1]
    refine (hsh c hc _).trans ?_
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun μ => v μ ^ 2) (fun μ _ => sq_nonneg (v μ)) (Finset.mem_univ q))
private theorem euclidNormVec_le_two_mul {v : Fin 4 → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ a, |v a| ≤ B) :
    euclidNormVec v ≤ 2 * B := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
private theorem euclidDistTorus_barycenter_le (L k m : ℕ) (hL : 0 < L) (p p' : TorusPlaquette (fineSide L k (2 * L ^ m))) :
    TestFunctions.euclidDistTorus (plaquetteBarycenterAt L k m p) (plaquetteBarycenterAt L k m p') ≤ 2 * barycentreDist L k p p' := by
  have hA : (0 : ℝ) < 2 * (L : ℝ) ^ k := by positivity
  set A : ℝ := 2 * (L : ℝ) ^ k with hAdef
  have hn := fineSide_cast_eq L k m
  have hBne : NeZero (2 * fineSide L k (2 * L ^ m)) := ⟨mul_ne_zero two_ne_zero (by
    rw [fineSide_eq]; positivity)⟩
  let I : TorusPlaquette (fineSide L k (2 * L ^ m)) → Fin 4 → ℕ := fun r a => 2 * (r.1 a).val + (if a = r.2.1 then 1 else 0) + (if a = r.2.2 then 1 else 0)
  let z : Fin 4 → ℤ := fun a => (doubledBarycentre p a - doubledBarycentre p' a).valMinAbs
  let v : Fin 4 → ℝ := fun a => (z a : ℝ) / A
  have hcoord : ∀ (r : TorusPlaquette (fineSide L k (2 * L ^ m))) (a : Fin 4),
      (((r.1 a).val : ℝ) + (if a = r.2.1 then 1 / 2 else 0) + (if a = r.2.2 then 1 / 2 else 0)) / (L : ℝ) ^ k =
        (I r a : ℝ) / A := by
    intro r a
    simp only [I, hAdef]
    push_cast
    have hp : (L : ℝ) ^ k ≠ 0 := by positivity
    split_ifs <;> field_simp <;> ring
  have hcover : torusProj (PeriodicLattice.torusSide L m) v = plaquetteBarycenterAt L k m p - plaquetteBarycenterAt L k m p' := by
    funext a
    have hdvd : ((2 * fineSide L k (2 * L ^ m) : ℕ) : ℤ) ∣ ((I p a : ℤ) - (I p' a : ℤ)) - z a := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [z, I, doubledBarycentre]
      simp [ZMod.coe_valMinAbs]
    obtain ⟨c, hc⟩ := hdvd
    have hc' : (I p a : ℝ) - (I p' a : ℝ) - (z a : ℝ) = 2 * (fineSide L k (2 * L ^ m) : ℝ) * (c : ℝ) := by
      exact_mod_cast hc
    have hzero : ((((I p a : ℝ) / A - (I p' a : ℝ) / A - v a : ℝ)) : AddCircle (PeriodicLattice.torusSide L m)) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      refine ⟨c, ?_⟩
      have e : (I p a : ℝ) / A - (I p' a : ℝ) / A - v a = ((I p a : ℝ) - (I p' a : ℝ) - (z a : ℝ)) / A := by
        simp only [v]
        ring
      rw [e, hc', hn, hAdef, zsmul_eq_mul]
      have hp : (L : ℝ) ^ k ≠ 0 := by positivity
      field_simp
    have hcoe : ((((I p a : ℝ) / A - (I p' a : ℝ) / A : ℝ)) : AddCircle (PeriodicLattice.torusSide L m)) =
        (v a : AddCircle (PeriodicLattice.torusSide L m)) := by
      rw [AddCircle.coe_sub] at hzero
      exact sub_eq_zero.mp hzero
    rw [AddCircle.coe_sub] at hcoe
    show ((v a : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) = _
    rw [← hcoe, ← hcoord p a, ← hcoord p' a]
    rfl
  have hbound : ∀ a, |v a| ≤ barycentreDist L k p p' := by
    intro a
    have hle : (z a).natAbs ≤ supDist (doubledBarycentre p) (doubledBarycentre p') :=
      Finset.le_sup (f := fun i => ((doubledBarycentre p i - doubledBarycentre p' i).valMinAbs).natAbs) (Finset.mem_univ a)
    have hle' : |(z a : ℝ)| ≤ (supDist (doubledBarycentre p) (doubledBarycentre p') : ℝ) := by
      have : ((z a).natAbs : ℝ) ≤ (supDist (doubledBarycentre p) (doubledBarycentre p') : ℝ) := by exact_mod_cast hle
      simpa [Nat.cast_natAbs] using this
    simp only [v, barycentreDist, abs_div, abs_of_pos hA]
    exact div_le_div_of_nonneg_right hle' hA.le
  have hnonneg : 0 ≤ barycentreDist L k p p' := by
    unfold barycentreDist
    positivity
  calc TestFunctions.euclidDistTorus (plaquetteBarycenterAt L k m p) (plaquetteBarycenterAt L k m p')
      ≤ euclidNormVec v := by
        unfold TestFunctions.euclidDistTorus torusEuclidNorm
        refine csInf_le ⟨0, ?_⟩ ⟨v, hcover, rfl⟩
        rintro _ ⟨w, -, rfl⟩
        exact Real.sqrt_nonneg _
    _ ≤ 2 * barycentreDist L k p p' := euclidNormVec_le_two_mul hnonneg hbound
private theorem euclidDistTorus_nonneg {c : ℝ} (x y : Torus4 c) : 0 ≤ TestFunctions.euclidDistTorus x y := by apply _root_.YangMills.SharedProofs.p31350 <;> assumption
private theorem abs_sub_le_lipConstTorus_mul {c : ℝ} (f : Torus4 c → ℝ) (hf : TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus f)
    (x y : Torus4 c) : |f x - f y| ≤ TestFunctions.lipConstTorus f * TestFunctions.euclidDistTorus x y := by apply _root_.YangMills.SharedProofs.p26625 <;> assumption
private theorem abs_le_of_uniformNorm_eq_one {X : Type} (f : X → ℝ) (h : TestFunctions.uniformNorm f = 1) (x : X) : |f x| ≤ 1 := by apply _root_.YangMills.SharedProofs.p64038 <;> assumption
private theorem weightNorm_testWeight_le_one (L k m : ℕ) (hL : 0 < L) (f : PeriodicLattice.FourTorus L m → ℝ) (n vt : ℝ) (hvn : 2 ≤ vt * n)
    (hs : TestFunctions.uniformNorm f = 1) (hl : TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus f)
    (hlip : TestFunctions.lipConstTorus f ≤ 1 / (vt * n)) : weightNorm L k (testWeight L k m f) ≤ 1 := by
  refine max_le (Real.iSup_le (fun p => abs_le_of_uniformNorm_eq_one f hs _) zero_le_one) (Real.iSup_le (fun pp => ?_) zero_le_one)
  have hd0 : 0 ≤ barycentreDist L k pp.1.1 pp.2.1 := by
    unfold barycentreDist
    positivity
  rcases hd0.eq_or_lt with h0 | hd
  · rw [← h0, div_zero]
    exact zero_le_one
  rw [div_le_one hd]
  have h1 := abs_sub_le_lipConstTorus_mul f hl (plaquetteBarycenterAt L k m pp.1.1) (plaquetteBarycenterAt L k m pp.2.1)
  have h2 := euclidDistTorus_barycenter_le L k m hL pp.1.1 pp.2.1
  have h4 := euclidDistTorus_nonneg (plaquetteBarycenterAt L k m pp.1.1) (plaquetteBarycenterAt L k m pp.2.1)
  have h5 : 1 / (vt * n) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hvn
  show |f (plaquetteBarycenterAt L k m pp.1.1) - f (plaquetteBarycenterAt L k m pp.2.1)| ≤ _
  calc _ ≤ TestFunctions.lipConstTorus f * TestFunctions.euclidDistTorus (plaquetteBarycenterAt L k m pp.1.1) (plaquetteBarycenterAt L k m pp.2.1) := h1
    _ ≤ (1 / 2) * (2 * barycentreDist L k pp.1.1 pp.2.1) := mul_le_mul (hlip.trans h5) h2 h4 (by norm_num)
    _ = barycentreDist L k pp.1.1 pp.2.1 := by ring
end
section
open TorusFields TorusLumps FreeEnergies TorusMetric TransfersOffTheWalk
variable {ℓ : TorusLumps.StepParameters}
private theorem separatedAlongTower_of_fineDist (hS : levelSitesStatement) (hodd : Odd ℓ.side) (x : ℕ → ℝ) {p : ℕ}
    (g : Fin p → FinePlaquetteFunction) (W : ℝ) (D : ℕ → ℝ) (hD : ∀ u, D u = W / (2 * (ℓ.side : ℝ) ^ (u + 1)) - 5) :
    ∀ (s n : ℕ) [NeZero n],
      (∀ i j, i ≠ j → ∀ P P' : OrientedPlaquette (fineSide ℓ.side s n), g i (LevelTestFunctions.barycenterCoord P.1) ≠ 0 →
        g j (LevelTestFunctions.barycenterCoord P'.1) ≠ 0 →
        W ≤ MomentSetup.fineDist (fineSide ℓ.side s n) (LevelTestFunctions.barycenterCoord P.1)
          (LevelTestFunctions.barycenterCoord P'.1)) →
      (∀ u < s, 2 ^ 10 * (clusterRange (x u) : ℝ) ≤ D u ∧ 8 < D u) →
      SeparatedAlongTower ℓ x D s n (fun i => fineWeight (g i) (fineSide ℓ.side s n)) := by
  intro s
  induction s with
  | zero =>
    intro n _ _ _
    exact trivial
  | succ s ih =>
    intro n _ hW hr
    refine ⟨⟨(hr s (Nat.lt_succ_self s)).1, (hr s (Nat.lt_succ_self s)).2, ?_⟩, ih (n * ℓ.side) hW fun u hu => hr u (by omega)⟩
    intro i j hij a ha a' ha'
    have h1 := (hS ℓ.side hodd (s + 1) n).1 (g i) (g j) W (hW i j hij) a ha a' ha'
    have hL : (0 : ℝ) < (ℓ.side : ℝ) ^ (s + 1) := by
      have : (0 : ℝ) < (ℓ.side : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
      positivity
    rw [hD s]
    have h2 : W / (2 * (ℓ.side : ℝ) ^ (s + 1)) ≤ (supDist a a' : ℝ) + 1 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
private def levelErrorTerm (ℓ : TorusLumps.StepParameters) (Cp C₀ : ℝ) (D a : ℕ → ℝ) (p u : ℕ) : ℝ :=
  Cp * ((p : ℝ) * a u) ^ 2 * Real.exp (-(ℓ.rt * D u / 2 ^ 8)) * (4 * C₀ * a u) ^ p
private theorem separationError_le_sum (Cp C₀ : ℝ) (hCp : 0 ≤ Cp) (hC₀ : 0 ≤ C₀) (D a : ℕ → ℝ) {p : ℕ} (g : Fin p → FinePlaquetteFunction) :
    ∀ (s n : ℕ) [NeZero n],
      (∀ u < s, ∀ (n' : ℕ) [NeZero n'], fineSide ℓ.side u n' = fineSide ℓ.side s n → ∀ i,
        ((weightSupportSites ℓ.side u n' (fineWeight (g i) (fineSide ℓ.side u n'))).card : ℝ) ≤ a u) →
      separationError ℓ Cp C₀ D s n (fun i => fineWeight (g i) (fineSide ℓ.side s n)) ≤
        ∑ u ∈ Finset.range s, levelErrorTerm ℓ Cp C₀ D a p u := by
  intro s
  induction s with
  | zero =>
    intro n _ _
    simp [separationError]
  | succ s ih =>
    intro n _ hc
    rw [Finset.sum_range_succ]
    have hcs := hc s (Nat.lt_succ_self s) (n * ℓ.side) rfl
    refine add_le_add (ih (n * ℓ.side) fun u hu n' _ he i => hc u (by omega) n' he i) ?_
    have hcard : ∀ i, 0 ≤ ((weightSupportSites ℓ.side s (n * ℓ.side) (fineWeight (g i) (fineSide ℓ.side s (n * ℓ.side)))).card : ℝ) :=
      fun i => by positivity
    have ha : p = 0 ∨ 0 ≤ a s := by
      rcases Nat.eq_zero_or_pos p with h | h
      · exact Or.inl h
      · exact Or.inr ((hcard ⟨0, h⟩).trans (hcs ⟨0, h⟩))
    rcases ha with rfl | ha
    · simp [levelErrorTerm]
    have hsum : ∑ i, ((weightSupportSites ℓ.side s (n * ℓ.side) (fineWeight (g i) (fineSide ℓ.side s (n * ℓ.side)))).card : ℝ) ≤ (p : ℝ) * a s := by
      calc _ ≤ ∑ _i : Fin p, a s := Finset.sum_le_sum fun i _ => hcs i
        _ = (p : ℝ) * a s := by simp
    have hsq := pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => hcard i) hsum 2
    have hprod : ∏ i, (4 * C₀ * ((weightSupportSites ℓ.side s (n * ℓ.side) (fineWeight (g i) (fineSide ℓ.side s (n * ℓ.side)))).card : ℝ)) ≤
        (4 * C₀ * a s) ^ p := by
      calc _ ≤ ∏ _i : Fin p, (4 * C₀ * a s) := Finset.prod_le_prod (fun i _ => by positivity)
            fun i _ => mul_le_mul_of_nonneg_left (hcs i) (by positivity)
        _ = (4 * C₀ * a s) ^ p := by simp
    unfold levelErrorTerm
    have he := Real.exp_pos (-(ℓ.rt * D s / 2 ^ 8))
    have hp0 : 0 ≤ ∏ i, (4 * C₀ * ((weightSupportSites ℓ.side s (n * ℓ.side) (fineWeight (g i) (fineSide ℓ.side s (n * ℓ.side)))).card : ℝ)) :=
      Finset.prod_nonneg fun i _ => by positivity
    refine mul_le_mul ?_ hprod hp0 (by positivity)
    refine mul_le_mul_of_nonneg_right ?_ he.le
    exact mul_le_mul_of_nonneg_left hsq hCp
end
section
private theorem sum_pow_mul_exp_le (K b L n : ℝ) (a k : ℕ) (hK : 0 ≤ K) (hb : 0 < b) (hL : 2 ≤ L) (hn : 1 ≤ n) :
    ∑ u ∈ Finset.range k, K * (n * L ^ (k - 1 - u)) ^ a * Real.exp (-(b * (n * L ^ (k - 1 - u)))) ≤
      K * ((a.factorial : ℝ) * (2 / b) ^ a) / (1 - Real.exp (-(b / 2))) * Real.exp (-(b / 2 * n)) := by
  have hr : Real.exp (-(b / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hr0 : 0 ≤ Real.exp (-(b / 2)) := (Real.exp_pos _).le
  have hterm : ∀ j : ℕ, K * (n * L ^ j) ^ a * Real.exp (-(b * (n * L ^ j))) ≤
      K * ((a.factorial : ℝ) * (2 / b) ^ a) * Real.exp (-(b / 2 * n)) * Real.exp (-(b / 2)) ^ j := by
    intro j
    set z := n * L ^ j with hz
    have hz0 : 0 ≤ z := by positivity
    have hLj : 1 + (j : ℝ) ≤ L ^ j := by
      have := one_add_mul_le_pow (a := L - 1) (by linarith) j
      have e : 1 + (L - 1) = L := by ring
      rw [e] at this
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hzj : n + j ≤ z := by
      rw [hz]
      nlinarith
    have h1 := Real.pow_div_factorial_le_exp (b / 2 * z) (by positivity) a
    have hf : (0 : ℝ) < a.factorial := by exact_mod_cast a.factorial_pos
    have h2 : z ^ a * Real.exp (-(b / 2 * z)) ≤ (a.factorial : ℝ) * (2 / b) ^ a := by
      rw [div_le_iff₀ hf, mul_pow] at h1
      have hb2 : (0 : ℝ) < (b / 2) ^ a := by positivity
      have h3 : z ^ a ≤ (a.factorial : ℝ) * (2 / b) ^ a * Real.exp (b / 2 * z) := by
        have e : (2 / b) ^ a * (b / 2) ^ a = 1 := by
          rw [← mul_pow]
          have : 2 / b * (b / 2) = 1 := by field_simp
          rw [this, one_pow]
        calc z ^ a = (2 / b) ^ a * ((b / 2) ^ a * z ^ a) := by rw [← mul_assoc, e, one_mul]
          _ ≤ (2 / b) ^ a * (Real.exp (b / 2 * z) * a.factorial) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = _ := by ring
      calc z ^ a * Real.exp (-(b / 2 * z)) ≤ (a.factorial : ℝ) * (2 / b) ^ a * Real.exp (b / 2 * z) * Real.exp (-(b / 2 * z)) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = (a.factorial : ℝ) * (2 / b) ^ a := by
            rw [mul_assoc, ← Real.exp_add]
            simp
    have h4 : Real.exp (-(b * z)) = Real.exp (-(b / 2 * z)) * Real.exp (-(b / 2 * z)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h5 : Real.exp (-(b / 2 * z)) ≤ Real.exp (-(b / 2 * n)) * Real.exp (-(b / 2)) ^ j := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : b / 2 * (n + j) ≤ b / 2 * z := mul_le_mul_of_nonneg_left hzj (by positivity)
      nlinarith
    rw [h4]
    calc K * z ^ a * (Real.exp (-(b / 2 * z)) * Real.exp (-(b / 2 * z)))
        = K * (z ^ a * Real.exp (-(b / 2 * z))) * Real.exp (-(b / 2 * z)) := by ring
      _ ≤ K * ((a.factorial : ℝ) * (2 / b) ^ a) * (Real.exp (-(b / 2 * n)) * Real.exp (-(b / 2)) ^ j) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h2 hK) h5 (Real.exp_pos _).le ?_
          positivity
      _ = _ := by ring
  have hsum : ∑ u ∈ Finset.range k, K * (n * L ^ (k - 1 - u)) ^ a * Real.exp (-(b * (n * L ^ (k - 1 - u)))) =
      ∑ j ∈ Finset.range k, K * (n * L ^ j) ^ a * Real.exp (-(b * (n * L ^ j))) :=
    Finset.sum_range_reflect (fun j => K * (n * L ^ j) ^ a * Real.exp (-(b * (n * L ^ j)))) k
  rw [hsum]
  refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
  rw [← Finset.mul_sum]
  have hgeom : ∑ j ∈ Finset.range k, Real.exp (-(b / 2)) ^ j ≤ (1 - Real.exp (-(b / 2)))⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr]
    exact (summable_geometric_of_lt_one hr0 hr).sum_le_tsum _ fun i _ => by positivity
  have hc : 0 ≤ K * ((a.factorial : ℝ) * (2 / b) ^ a) * Real.exp (-(b / 2 * n)) := by positivity
  calc _ ≤ K * ((a.factorial : ℝ) * (2 / b) ^ a) * Real.exp (-(b / 2 * n)) * (1 - Real.exp (-(b / 2)))⁻¹ :=
        mul_le_mul_of_nonneg_left hgeom hc
    _ = _ := by rw [div_eq_mul_inv]; ring
private theorem exists_pow_mul_exp_le_rpow (K c : ℝ) (a : ℕ) (hK : 0 ≤ K) (hc : 0 < c) : ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
    K * x ^ a * Real.exp (-(c * x ^ ((1 : ℝ) / 100))) ≤ x ^ (-(20 : ℝ)) := by
  set N : ℕ := 100 * a + 2000 with hN
  set T : ℝ := max 1 (K * ((N + 1).factorial : ℝ) / c ^ (N + 1)) with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  refine ⟨T ^ 100, one_le_pow₀ hT1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (one_le_pow₀ hT1).trans hx
  have hx0 : 0 < x := by linarith
  set t : ℝ := x ^ ((1 : ℝ) / 100) with ht
  have hxt : x = t ^ 100 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have htT : T ≤ t := by
    have h1 : (T ^ 100) ^ ((1 : ℝ) / 100) ≤ t := Real.rpow_le_rpow (by positivity) hx (by norm_num)
    have h2 : (T ^ 100) ^ ((1 : ℝ) / 100) = T := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rwa [h2] at h1
  have h1 := Real.pow_div_factorial_le_exp (c * t) (by positivity) (N + 1)
  have hf : (0 : ℝ) < (N + 1).factorial := by exact_mod_cast (N + 1).factorial_pos
  have hcN : 0 < c ^ (N + 1) := by positivity
  have hKt : K * ((N + 1).factorial : ℝ) / c ^ (N + 1) ≤ t := (le_max_right _ _).trans htT
  rw [div_le_iff₀ hcN] at hKt
  rw [div_le_iff₀ hf, mul_pow] at h1
  have hxn : x ^ (-(20 : ℝ)) = (t ^ 2000)⁻¹ := by
    rw [hxt, Real.rpow_neg (by positivity), show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]
  rw [hxn, hxt, ← pow_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  rw [← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  have e1 : K * t ^ (100 * a) * t ^ 2000 = K * t ^ N := by
    rw [hN, pow_add]
    ring
  rw [e1]
  have h2 : K * ((N + 1).factorial : ℝ) * t ^ N ≤ t * c ^ (N + 1) * t ^ N :=
    mul_le_mul_of_nonneg_right hKt (by positivity)
  have h3 : K * t ^ N * ((N + 1).factorial : ℝ) ≤ Real.exp (c * t) * ((N + 1).factorial : ℝ) := by
    calc K * t ^ N * ((N + 1).factorial : ℝ) = K * ((N + 1).factorial : ℝ) * t ^ N := by ring
      _ ≤ t * c ^ (N + 1) * t ^ N := h2
      _ = c ^ (N + 1) * t ^ (N + 1) := by rw [pow_succ t N]; ring
      _ ≤ _ := h1
  exact le_of_mul_le_mul_right h3 hf
end
section
variable {ℓ : TorusLumps.StepParameters}
open TorusFields TorusLumps FreeEnergies TorusMetric
private theorem isBoundedRealRV_curvatureObservable {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    Probability.IsBoundedRealRV (curvatureObservable h) := by apply _root_.YangMills.SharedProofs.p42321 <;> assumption
private theorem sum_mul_sum_bond_ends {n : ℕ} [NeZero n] (h : TorusSite n → ℝ) (A : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, h Y * ∑ i : Fin 4, (A (Y, i) + A (Y - unitStep n i, i)) =
      ∑ c : TorusBond n, (h c.1 + h (c.1 + unitStep n c.2)) * A c := by apply _root_.YangMills.SharedProofs.p11136 <;> assumption
private theorem finalField_forgetMarks (s n : ℕ) (u : MarkedSample ℓ s n) :
    finalField ℓ s n (forgetMarks ℓ s n u) = topField ℓ s n u := by apply _root_.YangMills.SharedProofs.p8091 <;> assumption
private theorem chainMark_forgetMarks (T : StageTower ℓ) (al : ℕ → ℝ) : (s n : ℕ) → [NeZero n] → (h : PlaquetteWeight (fineSide ℓ.side s n)) →
    (u : MarkedSample ℓ s n) →
    chainMark ℓ (fun j => (T.stage j).coupling) al s n h (forgetMarks ℓ s n u) = completedObservable T al s n h u
  | 0, _, _, h, u => by
    show curvatureObservable h u = curvatureObservable h u + 0
    rw [add_zero]
  | s + 1, n, _, h, u => by
    have ih := chainMark_forgetMarks T al s (n * ℓ.side) h u.1
    have e : completedObservable T al (s + 1) n h u =
        completedObservable T al s (n * ℓ.side) h u.1 + sourceTerm T al s n h u := by
      show curvatureObservable h (bottomField ℓ s (n * ℓ.side) u.1) +
        (cumulativeSource T al s (n * ℓ.side) h u.1 + sourceTerm T al s n h u) = _
      unfold completedObservable
      exact (add_assoc _ _ _).symm
    rw [e, ← ih]
    show chainMark ℓ (fun j => (T.stage j).coupling) al s (n * ℓ.side) h (forgetMarks ℓ s (n * ℓ.side) u.1) +
      ∑ c : TorusBond n, ℓ.coupling * al s * bondBlockMean ℓ.side (s + 1) n h c *
        bondScore ℓ (T.stage s).coupling (finalField ℓ s (n * ℓ.side) (forgetMarks ℓ s (n * ℓ.side) u.1)) u.2.2.1 u.2.1 c = _
    rw [finalField_forgetMarks]
    congr 1
    show _ = ℓ.coupling / 2 * al s * ∑ Y : TorusSite n, blockMean ℓ.side (s + 1) n Y h *
      ∑ i : Fin 4, (bondScore ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) u.1) u.2.2.1 u.2.1 (Y, i) +
        bondScore ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) u.1) u.2.2.1 u.2.1 (Y - unitStep n i, i))
    rw [sum_mul_sum_bond_ends (fun Y => blockMean ℓ.side (s + 1) n Y h)
      (fun c => bondScore ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) u.1) u.2.2.1 u.2.1 c), Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold bondBlockMean
    ring
private theorem prod_equivFin_symm {P : ℕ} (J : Finset (Fin P)) (g : Fin P → ℝ) :
    ∏ j : Fin J.card, g (J.equivFin.symm j).1 = ∏ i ∈ J, g i := by
  rw [← Finset.prod_coe_sort J g]
  exact Equiv.prod_comp J.equivFin.symm fun i : {i // i ∈ J} => g i.1
end
section
open TorusFields TorusLumps FreeEnergies TorusMetric
private theorem fineDist_ge_of_separatedTuple (hC : LevelTestFunctions.CircleRepProperties) {ℓ : TorusLumps.StepParameters} (hL : 0 < ℓ.side) {k m P : ℕ} {n vt : ℝ}
    {f : Fin P → PeriodicLattice.FourTorus ℓ.side m → ℝ} (hf : IsSeparatedTestTuple ℓ m n vt f) (i j : Fin P) (hij : i ≠ j)
    (q q' : OrientedPlaquette (fineSide ℓ.side k (2 * ℓ.side ^ m)))
    (h1 : fineFunctionOf ℓ.side k m (f i) (LevelTestFunctions.barycenterCoord q.1) ≠ 0)
    (h2 : fineFunctionOf ℓ.side k m (f j) (LevelTestFunctions.barycenterCoord q'.1) ≠ 0) :
    n * (ℓ.side : ℝ) ^ k ≤ MomentSetup.fineDist (fineSide ℓ.side k (2 * ℓ.side ^ m))
      (LevelTestFunctions.barycenterCoord q.1) (LevelTestFunctions.barycenterCoord q'.1) := by
  have hx : (torusProj (PeriodicLattice.torusSide ℓ.side m) fun a => LevelTestFunctions.barycenterCoord q.1 a / (ℓ.side : ℝ) ^ k) ∈
      tsupport (f i) := subset_tsupport (f i) h1
  have hy : (torusProj (PeriodicLattice.torusSide ℓ.side m) fun a => LevelTestFunctions.barycenterCoord q'.1 a / (ℓ.side : ℝ) ^ k) ∈
      tsupport (f j) := subset_tsupport (f j) h2
  have hsep := hf.separated
  have h3 : ENNReal.ofReal n ≤ ENNReal.ofReal (TestFunctions.euclidDistTorus
      (torusProj (PeriodicLattice.torusSide ℓ.side m) fun a => LevelTestFunctions.barycenterCoord q.1 a / (ℓ.side : ℝ) ^ k)
      (torusProj (PeriodicLattice.torusSide ℓ.side m) fun a => LevelTestFunctions.barycenterCoord q'.1 a / (ℓ.side : ℝ) ^ k)) :=
    (hsep.2 i j hij).trans (iInf₂_le_of_le _ hx (iInf₂_le _ hy))
  have h4 : n ≤ TestFunctions.euclidDistTorus
      (torusProj (PeriodicLattice.torusSide ℓ.side m) fun a => LevelTestFunctions.barycenterCoord q.1 a / (ℓ.side : ℝ) ^ k)
      (torusProj (PeriodicLattice.torusSide ℓ.side m) fun a => LevelTestFunctions.barycenterCoord q'.1 a / (ℓ.side : ℝ) ^ k) := by
    rcases ENNReal.ofReal_le_ofReal_iff'.mp h3 with h | h
    · exact h
    · exact absurd hsep.1 (not_lt.mpr h)
  have h5 := pow_mul_euclidDistTorus_le_fineDist hC ℓ.side k m hL (LevelTestFunctions.barycenterCoord q.1) (LevelTestFunctions.barycenterCoord q'.1)
  have hM : (0 : ℝ) ≤ (ℓ.side : ℝ) ^ k := by positivity
  calc n * (ℓ.side : ℝ) ^ k ≤ (ℓ.side : ℝ) ^ k * _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left h4 hM
    _ ≤ _ := h5
private theorem abs_circleRep_le_of_tuple (hC : LevelTestFunctions.CircleRepProperties) {ℓ : TorusLumps.StepParameters} (hL : 0 < ℓ.side) {k m P : ℕ} {n vt : ℝ}
    {f : Fin P → PeriodicLattice.FourTorus ℓ.side m → ℝ} (hf : IsSeparatedTestTuple ℓ m n vt f) (i : Fin P) :
    ∀ M : ℕ, M = fineSide ℓ.side k (2 * ℓ.side ^ m) → ∀ q q' : OrientedPlaquette M,
      fineFunctionOf ℓ.side k m (f i) (LevelTestFunctions.barycenterCoord q.1) ≠ 0 →
      fineFunctionOf ℓ.side k m (f i) (LevelTestFunctions.barycenterCoord q'.1) ≠ 0 → ∀ a : Fin 4,
      |LevelTestFunctions.circleRep M (LevelTestFunctions.barycenterCoord q.1 a - LevelTestFunctions.barycenterCoord q'.1 a)| ≤
        10 * n * (ℓ.side : ℝ) ^ k := by
  rintro M rfl q q' h1 h2 a
  have hx : (torusProj (PeriodicLattice.torusSide ℓ.side m) fun a => LevelTestFunctions.barycenterCoord q.1 a / (ℓ.side : ℝ) ^ k) ∈
      tsupport (f i) := subset_tsupport (f i) h1
  have hy : (torusProj (PeriodicLattice.torusSide ℓ.side m) fun a => LevelTestFunctions.barycenterCoord q'.1 a / (ℓ.side : ℝ) ^ k) ∈
      tsupport (f i) := subset_tsupport (f i) h2
  have h3 := hf.dist_le i i _ hx _ hy
  have h5 := abs_circleRep_le hC ℓ.side k m hL (LevelTestFunctions.barycenterCoord q.1) (LevelTestFunctions.barycenterCoord q'.1) a
  have hM : (0 : ℝ) ≤ (ℓ.side : ℝ) ^ k := by positivity
  refine h5.trans ?_
  calc _ ≤ (ℓ.side : ℝ) ^ k * (10 * n) := mul_le_mul_of_nonneg_left h3 hM
    _ = _ := by ring
private theorem card_weightSupportSites_le (hC : LevelTestFunctions.CircleRepProperties) (hS : levelSitesStatement) {ℓ : TorusLumps.StepParameters}
    (hodd : Odd ℓ.side) {k m P : ℕ} {n vt : ℝ} (hn : 1 ≤ n) {f : Fin P → PeriodicLattice.FourTorus ℓ.side m → ℝ}
    (hf : IsSeparatedTestTuple ℓ m n vt f) (i : Fin P) (u n' : ℕ) [NeZero n'] (hu : u ≤ k)
    (he : fineSide ℓ.side u n' = fineSide ℓ.side k (2 * ℓ.side ^ m)) :
    ((weightSupportSites ℓ.side u n' (fineWeight (fineFunctionOf ℓ.side k m (f i)) (fineSide ℓ.side u n'))).card : ℝ) ≤
      (25 * (n * (ℓ.side : ℝ) ^ (k - u))) ^ 4 := by
  have hL : 0 < ℓ.side := hodd.pos
  have hLr : (1 : ℝ) ≤ (ℓ.side : ℝ) := by exact_mod_cast hL
  have hLu : (0 : ℝ) < (ℓ.side : ℝ) ^ u := by positivity
  set z : ℝ := n * (ℓ.side : ℝ) ^ (k - u) with hz
  have hz1 : 1 ≤ z := by
    have := one_le_pow₀ hLr (n := k - u)
    rw [hz]
    nlinarith
  have hball := fun a' a'' h1 h2 => abs_circleRep_le_of_tuple hC hL hf i _ he a' a'' h1 h2
  have hd := (hS ℓ.side hodd u n').2.1 (fineFunctionOf ℓ.side k m (f i)) (10 * n * (ℓ.side : ℝ) ^ k) hball
  set A := weightSupportSites ℓ.side u n' (fineWeight (fineFunctionOf ℓ.side k m (f i)) (fineSide ℓ.side u n')) with hA
  have hpow : (ℓ.side : ℝ) ^ k = (ℓ.side : ℝ) ^ u * (ℓ.side : ℝ) ^ (k - u) := by
    rw [← pow_add]
    congr 1
    omega
  have hRn : ∀ a ∈ A, ∀ a' ∈ A, supDist a a' ≤ ⌈10 * z⌉₊ + 1 := by
    intro a ha a' ha'
    have h1 := hd a ha a' ha'
    have h2 : (supDist a a' : ℝ) ≤ 10 * z + 1 := by
      have e : 10 * n * (ℓ.side : ℝ) ^ k = (ℓ.side : ℝ) ^ u * (10 * z) := by rw [hpow, hz]; ring
      rw [e] at h1
      have h3 : (ℓ.side : ℝ) ^ u * (supDist a a' : ℝ) ≤ (ℓ.side : ℝ) ^ u * (10 * z + 1) := by linarith
      exact le_of_mul_le_mul_left h3 hLu
    have h4 : (supDist a a' : ℝ) ≤ ((⌈10 * z⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil (10 * z)]
    exact_mod_cast h4
  have hc := (hS ℓ.side hodd u n').2.2 A _ hRn
  have hc' : (A.card : ℝ) ≤ ((2 * (⌈10 * z⌉₊ + 1) + 1 : ℕ) : ℝ) ^ 4 := by exact_mod_cast hc
  refine hc'.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
  have hceil : (⌈10 * z⌉₊ : ℝ) ≤ 10 * z + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  push_cast
  linarith
end
section
open TorusFields TorusLumps FreeEnergies TorusMetric TransfersOffTheWalk
private theorem gap_bounds (L n r : ℝ) (j : ℕ) (hL : 2 ^ 16 ≤ L) (hr : 1 ≤ r) (hn : 2 ^ 12 * L * r ≤ n) :
    2 ^ 10 * (r + j + 1) ≤ n / 2 * L ^ j - 5 ∧ 8 < n / 2 * L ^ j - 5 := by
  have hLj : 1 + (j : ℝ) ≤ L ^ j := by
    have := one_add_mul_le_pow (a := L - 1) (by linarith) j
    have e : 1 + (L - 1) = L := by ring
    rw [e] at this
    nlinarith
  have h0 : 0 ≤ 2 ^ 11 * L * r := by positivity
  have h1 : 2 ^ 11 * L * r * (1 + j) ≤ n / 2 * L ^ j :=
    mul_le_mul (by linarith) hLj (by positivity) (by linarith)
  have h2 : (2 : ℝ) ^ 27 * r * (1 + j) ≤ 2 ^ 11 * L * r * (1 + j) := by
    have : (0 : ℝ) ≤ r * (1 + j) := by positivity
    nlinarith
  have h3 : r + j ≤ r * (1 + j) := by nlinarith
  constructor <;> nlinarith
variable {Tb : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
private theorem clusterRange_flowCoupling_sub_le {T : StageTower (Tb.stepParameters y)} {S : ScoredStageTower T} {β : ℝ} {k : ℕ} (hS : S.FollowsFlow β k) :
    ∀ j : ℕ, j ≤ k → (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β (k - j)) : ℝ) ≤
      (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k) : ℝ) + j := by
  intro j
  induction j with
  | zero =>
    intro _
    simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have hu : k - (j + 1) ≤ k := by omega
    have hs := hS.isFlowStep _ hu
    have h2 := hs.onFamily.isStep.2.2
    have e1 : (T.stage (k - (j + 1))).toStepSetup.range = clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β (k - (j + 1))) := by
      show clusterRange (T.stage (k - (j + 1))).toStepSetup.coupling = _
      rw [hs.coupling_eq]
    have e2 : (T.stage (k - (j + 1))).toStepSetup.nextRange = clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β (k - j)) := by
      show clusterRange (T.stage (k - (j + 1))).toStepSetup.nextCoupling = _
      rw [hs.nextCoupling_eq]
      congr 2
      omega
    rw [e1, e2] at h2
    have h3 : (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β (k - (j + 1))) : ℝ) ≤
        (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β (k - j)) : ℝ) + 1 := by exact_mod_cast h2
    push_cast
    linarith
private def levelGap (L k : ℕ) (n : ℝ) (u : ℕ) : ℝ := n * (L : ℝ) ^ k / (2 * (L : ℝ) ^ (u + 1)) - 5
private theorem levelGap_eq (L k : ℕ) (hL : 0 < L) (n : ℝ) (u : ℕ) (hu : u < k) :
    levelGap L k n u = n / 2 * (L : ℝ) ^ (k - 1 - u) - 5 := by
  have e : (L : ℝ) ^ k = (L : ℝ) ^ (u + 1) * (L : ℝ) ^ (k - 1 - u) := by
    rw [← pow_add]
    congr 1
    omega
  unfold levelGap
  rw [e]
  field_simp
private theorem separatedAlongTower_of_tuple (hC : LevelTestFunctions.CircleRepProperties) (hSi : levelSitesStatement)
    (hfit : (Tb.stepParameters y).Admissible) {T : StageTower (Tb.stepParameters y)} {S : ScoredStageTower T} {β : ℝ} {k m P p : ℕ} {n vt : ℝ}
    (hS : S.FollowsFlow β k) (hr : (1 : ℝ) ≤ clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k))
    (hn : 2 ^ 12 * ((Tb.stepParameters y).side : ℝ) * (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k) : ℝ) ≤ n)
    {f : Fin P → PeriodicLattice.FourTorus (Tb.stepParameters y).side m → ℝ} (hf : IsSeparatedTestTuple (Tb.stepParameters y) m n vt f)
    (e : Fin p → Fin P) (he : Function.Injective e) :
    SeparatedAlongTower (Tb.stepParameters y) (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β) (levelGap (Tb.stepParameters y).side k n) k
      (2 * (Tb.stepParameters y).side ^ m)
      (fun i => fineWeight (fineFunctionOf (Tb.stepParameters y).side k m (f (e i))) (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ m))) := by
  have hL0 : 0 < (Tb.stepParameters y).side := hfit.L_odd.pos
  have hL16 : (2 : ℝ) ^ 16 ≤ ((Tb.stepParameters y).side : ℝ) := by exact_mod_cast hfit.L_ge
  refine separatedAlongTower_of_fineDist hSi hfit.L_odd _ (fun i => fineFunctionOf (Tb.stepParameters y).side k m (f (e i))) (n * ((Tb.stepParameters y).side : ℝ) ^ k) _
    (fun u => rfl) k _ (fun i j hij q q' h1 h2 => fineDist_ge_of_separatedTuple hC hL0 hf (e i) (e j) (fun h => hij (he h)) q q' h1 h2) ?_
  intro u hu
  show 2 ^ 10 * (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β u) : ℝ) ≤ levelGap (Tb.stepParameters y).side k n u ∧
    8 < levelGap (Tb.stepParameters y).side k n u
  rw [levelGap_eq _ _ hL0 n u hu]
  obtain ⟨g1, g2⟩ := gap_bounds _ n _ (k - 1 - u) hL16 hr hn
  refine ⟨?_, g2⟩
  have h1 := clusterRange_flowCoupling_sub_le hS (k - u) (by omega)
  have e1 : k - (k - u) = u := by omega
  rw [e1] at h1
  have e2 : ((k - u : ℕ) : ℝ) = ((k - 1 - u : ℕ) : ℝ) + 1 := by
    have : k - u = (k - 1 - u) + 1 := by omega
    rw [this]
    push_cast
    simp
  rw [e2] at h1
  refine le_trans ?_ g1
  have h2 : (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β u) : ℝ) ≤
      (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k) : ℝ) + ((k - 1 - u : ℕ) : ℝ) + 1 := by linarith
  linarith
private def separationErrorConstant (ℓ : TorusLumps.StepParameters) (C₀ Cp : ℝ) (p : ℕ) : ℝ :=
  (Cp * (p : ℝ) ^ 2 * (25 * (ℓ.side : ℝ)) ^ 8 * Real.exp (5 * ℓ.rt / 2 ^ 8) * (4 * C₀ * (25 * (ℓ.side : ℝ)) ^ 4) ^ p) *
      (((8 + 4 * p).factorial : ℝ) * (2 / (ℓ.rt / 2 ^ 9)) ^ (8 + 4 * p)) / (1 - Real.exp (-(ℓ.rt / 2 ^ 9 / 2)))
private theorem separationError_of_tuple_le (hC : LevelTestFunctions.CircleRepProperties) (hSi : levelSitesStatement)
    {ℓ : TorusLumps.StepParameters} (hfit : ℓ.Admissible) (C₀ Cp : ℝ) (hC₀ : 0 ≤ C₀) (hCp : 0 ≤ Cp) {k m P p : ℕ} {n vt : ℝ} (hn : 1 ≤ n)
    {f : Fin P → PeriodicLattice.FourTorus ℓ.side m → ℝ} (hf : IsSeparatedTestTuple ℓ m n vt f) (e : Fin p → Fin P) :
    separationError ℓ Cp C₀ (levelGap ℓ.side k n) k (2 * ℓ.side ^ m)
        (fun i => fineWeight (fineFunctionOf ℓ.side k m (f (e i))) (fineSide ℓ.side k (2 * ℓ.side ^ m))) ≤
      separationErrorConstant ℓ C₀ Cp p * Real.exp (-(ℓ.rt / 2 ^ 9 / 2 * n)) := by
  have hL0 : 0 < ℓ.side := hfit.L_odd.pos
  have hL2 : (2 : ℝ) ≤ (ℓ.side : ℝ) := by
    have : (2 : ℝ) ^ 16 ≤ (ℓ.side : ℝ) := by exact_mod_cast hfit.L_ge
    linarith
  have hrt := hfit.rt_pos
  have h1 := separationError_le_sum (ℓ := ℓ) Cp C₀ hCp hC₀ (levelGap ℓ.side k n) (fun u => (25 * (n * (ℓ.side : ℝ) ^ (k - u))) ^ 4)
    (fun i => fineFunctionOf ℓ.side k m (f (e i))) k (2 * ℓ.side ^ m)
    (fun u hu n' _ he' i => card_weightSupportSites_le hC hSi hfit.L_odd hn hf (e i) u n' hu.le he')
  refine h1.trans ?_
  set K : ℝ := Cp * (p : ℝ) ^ 2 * (25 * (ℓ.side : ℝ)) ^ 8 * Real.exp (5 * ℓ.rt / 2 ^ 8) * (4 * C₀ * (25 * (ℓ.side : ℝ)) ^ 4) ^ p with hK
  have hK0 : 0 ≤ K := by positivity
  have hterm : ∀ u ∈ Finset.range k, levelErrorTerm ℓ Cp C₀ (levelGap ℓ.side k n) (fun u => (25 * (n * (ℓ.side : ℝ) ^ (k - u))) ^ 4) p u =
      K * (n * (ℓ.side : ℝ) ^ (k - 1 - u)) ^ (8 + 4 * p) * Real.exp (-(ℓ.rt / 2 ^ 9 * (n * (ℓ.side : ℝ) ^ (k - 1 - u)))) := by
    intro u hu
    have hu' := Finset.mem_range.1 hu
    unfold levelErrorTerm
    rw [levelGap_eq _ _ hL0 n u hu']
    have e1 : (ℓ.side : ℝ) ^ (k - u) = (ℓ.side : ℝ) * (ℓ.side : ℝ) ^ (k - 1 - u) := by
      rw [← pow_succ']
      congr 1
      omega
    simp only [e1]
    set z := n * (ℓ.side : ℝ) ^ (k - 1 - u) with hz
    have e2 : n * ((ℓ.side : ℝ) * (ℓ.side : ℝ) ^ (k - 1 - u)) = (ℓ.side : ℝ) * z := by rw [hz]; ring
    have e3 : n / 2 * (ℓ.side : ℝ) ^ (k - 1 - u) = z / 2 := by rw [hz]; ring
    rw [e2, e3]
    have e4 : Real.exp (-(ℓ.rt * (z / 2 - 5) / 2 ^ 8)) = Real.exp (5 * ℓ.rt / 2 ^ 8) * Real.exp (-(ℓ.rt / 2 ^ 9 * z)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e4, hK]
    have e5 : (4 * C₀ * (25 * ((ℓ.side : ℝ) * z)) ^ 4) ^ p = (4 * C₀ * (25 * (ℓ.side : ℝ)) ^ 4) ^ p * z ^ (4 * p) := by
      rw [pow_mul, ← mul_pow]
      congr 1
      ring
    rw [e5, pow_add]
    ring
  rw [Finset.sum_congr rfl hterm]
  refine (sum_pow_mul_exp_le K (ℓ.rt / 2 ^ 9) ℓ.side n (8 + 4 * p) k hK0 (by positivity) hL2 hn).trans ?_
  exact le_of_eq rfl
end
section
open TorusFields TorusLumps FreeEnergies TorusMetric TransfersOffTheWalk
open ProbabilityTheory
variable {Tb : RenormalizationStepParameters.ParameterAssignment} {Kr : ResponseParameters} {y : ℝ}
private def ConditionalProductBounds (Tb : RenormalizationStepParameters.ParameterAssignment) (Kr : ResponseParameters) (y : ℝ) (Cpf : ℕ → ℝ) : Prop :=
  ∀ (p : ℕ) (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T) (β : ℝ) (s n : ℕ) [NeZero n] (D : ℕ → ℝ) (f : Fin p → FinePlaquetteFunction),
    S.params = Kr → S.FollowsFlow β s → CouplingsAboveFloor (Tb.stepParameters y) β s → IsBlockTorusSide (Tb.stepParameters y) n →
    (∀ i, weightNorm (Tb.stepParameters y).side s (fineWeight (f i) (fineSide (Tb.stepParameters y).side s n)) ≤ 1) →
    SeparatedAlongTower (Tb.stepParameters y) (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β) D s n (fun i => fineWeight (f i) _) →
    HasConditionalMean T β s n (fun u => ∏ i, completedCentered S (f i) s n u) ∧
    ∀ᵐ u ∂(markedSampleLaw T β s n),
      |conditionalProduct S β f Finset.univ s n u - ∏ i, fittedResponse S (f i) s n (stageState T s n u)| ≤
        separationError (Tb.stepParameters y) (Cpf p) Kr.C₀ D s n (fun i => fineWeight (f i) _) *
          ∏ i, scoreMeanOver S (f i) s n (stageState T s n u)
private theorem one_le_scoreMeanOver {ℓ : TorusLumps.StepParameters} {T : StageTower ℓ} (S : ScoredStageTower T) (s n : ℕ) [NeZero n] (g : FinePlaquetteFunction)
    (hs : ∀ w, 0 ≤ (S.setup s).score w) (q : StageState T s n) : 1 ≤ scoreMeanOver S g s n q := by
  unfold scoreMeanOver meanSiteScore
  have : 0 ≤ ∑ z ∈ functionSites ℓ.side g s n, siteScore (S.setup s).score q.2.1 q.2.2 z := by
    refine Finset.sum_nonneg fun z _ => ?_
    unfold siteScore
    split_ifs
    · exact hs _
    · exact le_rfl
  have h2 : 0 ≤ (((functionSites ℓ.side g s n).card : ℝ))⁻¹ * ∑ z ∈ functionSites ℓ.side g s n, siteScore (S.setup s).score q.2.1 q.2.2 z := by
    positivity
  linarith
private theorem conditionalProduct_of_tuple (hC : LevelTestFunctions.CircleRepProperties) (hSi : levelSitesStatement)
    (hfit : (Tb.stepParameters y).Admissible) (hK0 : 0 ≤ Kr.C₀) (Cpf : ℕ → ℝ) (hCpf0 : ∀ p, 0 ≤ Cpf p) (hCpf : ConditionalProductBounds Tb Kr y Cpf)
    {T : StageTower (Tb.stepParameters y)} (S : ScoredStageTower T) {β : ℝ} {k m P : ℕ} {n vt ε : ℝ}
    (hK : S.params = Kr) (hS : S.FollowsFlow β k) (hR : CouplingsAboveFloor (Tb.stepParameters y) β k) (hB : IsBlockTorusSide (Tb.stepParameters y) (2 * (Tb.stepParameters y).side ^ m))
    (hn1 : 1 ≤ n) (hr : (1 : ℝ) ≤ clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k))
    (hn : 2 ^ 12 * ((Tb.stepParameters y).side : ℝ) * (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k) : ℝ) ≤ n) (hvn : 2 ≤ vt * n)
    {f : Fin P → PeriodicLattice.FourTorus (Tb.stepParameters y).side m → ℝ} (hf : IsSeparatedTestTuple (Tb.stepParameters y) m n vt f)
    (hs : ∀ w, 0 ≤ (S.setup k).score w) (I : Finset (Fin P))
    (hεb : separationErrorConstant (Tb.stepParameters y) Kr.C₀ (Cpf I.card) I.card * Real.exp (-((Tb.stepParameters y).rt / 2 ^ 9 / 2 * n)) ≤ ε) :
    Integrable (fun u => ∏ i ∈ I, completedCentered S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) u)
      (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) ∧
    ∀ᵐ u ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)),
      |conditionalProduct S β (fun i => fineFunctionOf (Tb.stepParameters y).side k m (f i)) I k (2 * (Tb.stepParameters y).side ^ m) u -
          ∏ i ∈ I, fittedResponse S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u)| ≤
        ε * ∏ i ∈ I, scoreMeanOver S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) := by
  classical
  let e : Fin I.card → Fin P := fun j => (I.equivFin.symm j).1
  have he : Function.Injective e := fun a b h => I.equivFin.symm.injective (Subtype.ext h)
  have hL0 : 0 < (Tb.stepParameters y).side := hfit.L_odd.pos
  have hsize : ∀ j, weightNorm (Tb.stepParameters y).side k (fineWeight (fineFunctionOf (Tb.stepParameters y).side k m (f (e j))) (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ m))) ≤ 1 := fun j =>
    weightNorm_testWeight_le_one (Tb.stepParameters y).side k m hL0 (f (e j)) n vt hvn (hf.uniformNorm_eq _) (hf.lipschitz _) (hf.lipConst_le _)
  have hap := separatedAlongTower_of_tuple hC hSi hfit hS hr hn hf e he
  obtain ⟨hhad, hae⟩ := hCpf I.card T S β k (2 * (Tb.stepParameters y).side ^ m) (levelGap (Tb.stepParameters y).side k n) (fun j => fineFunctionOf (Tb.stepParameters y).side k m (f (e j)))
    hK hS hR hB hsize hap
  have herr := separationError_of_tuple_le hC hSi hfit Kr.C₀ (Cpf I.card) hK0 (hCpf0 _) (k := k) hn1 hf e
  have hprodfun : (fun u => ∏ j, completedCentered S (fineFunctionOf (Tb.stepParameters y).side k m (f (e j))) k (2 * (Tb.stepParameters y).side ^ m) u) =
      fun u => ∏ i ∈ I, completedCentered S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) u := by
    funext u
    exact prod_equivFin_symm I fun i => completedCentered S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) u
  refine ⟨hprodfun ▸ hhad.1, ?_⟩
  filter_upwards [hae] with u hu
  have e1 : conditionalProduct S β (fun j => fineFunctionOf (Tb.stepParameters y).side k m (f (e j))) Finset.univ k (2 * (Tb.stepParameters y).side ^ m) u =
      conditionalProduct S β (fun i => fineFunctionOf (Tb.stepParameters y).side k m (f i)) I k (2 * (Tb.stepParameters y).side ^ m) u := by
    unfold conditionalProduct
    rw [hprodfun]
  have e2 : ∏ j, fittedResponse S (fineFunctionOf (Tb.stepParameters y).side k m (f (e j))) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) =
      ∏ i ∈ I, fittedResponse S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) :=
    prod_equivFin_symm I fun i => fittedResponse S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u)
  have e3 : ∏ j, scoreMeanOver S (fineFunctionOf (Tb.stepParameters y).side k m (f (e j))) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) =
      ∏ i ∈ I, scoreMeanOver S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) :=
    prod_equivFin_symm I fun i => scoreMeanOver S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u)
  rw [e1, e2, e3] at hu
  refine hu.trans (mul_le_mul_of_nonneg_right (herr.trans hεb) ?_)
  exact Finset.prod_nonneg fun i _ => zero_le_one.trans (one_le_scoreMeanOver S k _ _ hs _)
private theorem integral_prod_centered_eq (hC : LevelTestFunctions.CircleRepProperties) (hSi : levelSitesStatement)
    (hT1 : separatedMarkedMomentsStatement) (hfit : (Tb.stepParameters y).Admissible)
    {T : StageTower (Tb.stepParameters y)} (S : ScoredStageTower T) {β : ℝ} {k m P : ℕ} {n vt : ℝ}
    (hS : S.FollowsFlow β k) (hr : (1 : ℝ) ≤ clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k))
    (hn : 2 ^ 12 * ((Tb.stepParameters y).side : ℝ) * (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k) : ℝ) ≤ n)
    {f : Fin P → PeriodicLattice.FourTorus (Tb.stepParameters y).side m → ℝ} (hf : IsSeparatedTestTuple (Tb.stepParameters y) m n vt f)
    (hmap : Measure.map (bottomField (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m)) (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) =
      wilsonLaw β (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ m)))
    (hbot : Measurable (bottomField (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m)))
    (hle : stageSigma T k (2 * (Tb.stepParameters y).side ^ m) ≤ markedSampleMeasurableSpace (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m))
    [hfin : SigmaFinite ((markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)).trim hle)]
    (I : Finset (Fin P)) :
    ∫ W, ∏ i ∈ I, (curvatureObservable (testWeight (Tb.stepParameters y).side k m (f i)) W -
        centering S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m)) ∂(wilsonLaw β (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ m))) =
      ∫ u, conditionalProduct S β (fun i => fineFunctionOf (Tb.stepParameters y).side k m (f i)) I k (2 * (Tb.stepParameters y).side ^ m) u
        ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) := by
  classical
  let e : Fin I.card → Fin P := fun j => (I.equivFin.symm j).1
  have he : Function.Injective e := fun a b h => I.equivFin.symm.injective (Subtype.ext h)
  have hap := separatedAlongTower_of_tuple hC hSi hfit hS hr hn hf e he
  have h1 := hT1 (Tb.stepParameters y) hfit T hS.isCutoff_bottom hS.marksMeasurable I.card k (2 * (Tb.stepParameters y).side ^ m) β S.coeffs
    (fun j => centering S (fineFunctionOf (Tb.stepParameters y).side k m (f (e j))) k (2 * (Tb.stepParameters y).side ^ m)) _ _ _ hap
  have hmeas : Measurable fun W => ∏ i ∈ I, (curvatureObservable (testWeight (Tb.stepParameters y).side k m (f i)) W -
      centering S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m)) :=
    Finset.measurable_fun_prod _ fun i _ => (isBoundedRealRV_curvatureObservable _).measurable.sub measurable_const
  rw [← hmap, integral_map hbot.aemeasurable hmeas.aestronglyMeasurable]
  unfold conditionalProduct
  rw [integral_condExp hle]
  have l1 : ∀ u, ∏ i ∈ I, (curvatureObservable (testWeight (Tb.stepParameters y).side k m (f i)) (bottomField (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m) u) -
      centering S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m)) =
      ∏ j, (curvatureObservable (fineWeight (fineFunctionOf (Tb.stepParameters y).side k m (f (e j))) _) (bottomField (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m) u) -
        centering S (fineFunctionOf (Tb.stepParameters y).side k m (f (e j))) k (2 * (Tb.stepParameters y).side ^ m)) := fun u =>
    (prod_equivFin_symm I fun i => curvatureObservable (testWeight (Tb.stepParameters y).side k m (f i)) (bottomField (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m) u) -
      centering S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m)).symm
  have l2 : ∀ u, ∏ i ∈ I, completedCentered S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) u =
      ∏ j, (completedObservable T S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (fineWeight (fineFunctionOf (Tb.stepParameters y).side k m (f (e j))) _) u -
        centering S (fineFunctionOf (Tb.stepParameters y).side k m (f (e j))) k (2 * (Tb.stepParameters y).side ^ m)) := fun u =>
    (prod_equivFin_symm I fun i => completedCentered S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) u).symm
  simp only [l1, l2]
  exact h1
private def ScoreMeanMomentBounds (Tb : RenormalizationStepParameters.ParameterAssignment) (Kr : ResponseParameters) (y : ℝ) : Prop :=
  ∃ x₁ : ℝ, ∀ P : ℕ, 1 ≤ P → ∃ C : ℝ, 1 ≤ C ∧ ∀ (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T) (β : ℝ) (k m : ℕ) (g : FinePlaquetteFunction),
    S.params = Kr → S.FollowsFlow β k → CouplingsAboveFloor (Tb.stepParameters y) β k → x₁ ≤ ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k →
    (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ 2 * (Tb.stepParameters y).side ^ m →
    ∫⁻ u, ENNReal.ofReal (scoreMeanOver S g k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) ^ P)
        ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) ≤
      ENNReal.ofReal ((C * (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k) : ℝ) ^ 4 *
        Real.log (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k)) ^ P)
private theorem measurable_bottomField {ℓ : TorusLumps.StepParameters} (s : ℕ) : ∀ n : ℕ, Measurable (bottomField ℓ s n) := by apply _root_.YangMills.SharedProofs.p4086 <;> assumption
private theorem measurable_scoreMeanOver (hSt : StageStatesMeasurableStatement) (hfit : (Tb.stepParameters y).Admissible)
    {T : StageTower (Tb.stepParameters y)} (S : ScoredStageTower T) (k n : ℕ) [NeZero n] (g : FinePlaquetteFunction) (hs : Measurable (S.setup k).score) :
    Measurable fun u : MarkedSample (Tb.stepParameters y) k n => scoreMeanOver S g k n (stageState T k n u) := by
  have hsig : Measurable fun q : (Σ Y : Finset (TorusSite n), (Y → (T.stage k).labels.Ω)) =>
      meanSiteScore (S.setup k).score (functionSites (Tb.stepParameters y).side g k n) q.1 q.2 := by
    refine fun _ ht => MeasurableSpace.measurableSet_iInf.2 fun Y => ?_
    have hY : Measurable fun ω : Y → (T.stage k).labels.Ω => meanSiteScore (S.setup k).score (functionSites (Tb.stepParameters y).side g k n) Y ω := by
      unfold meanSiteScore
      refine measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun z _ => ?_))
      by_cases hz : z ∈ Y
      · have e : (fun ω : Y → (T.stage k).labels.Ω => siteScore (S.setup k).score Y ω z) = fun ω => (S.setup k).score (ω ⟨z, hz⟩) := by
          funext ω
          simp [siteScore, hz]
        rw [e]
        exact hs.comp (measurable_pi_apply _)
      · have e : (fun ω : Y → (T.stage k).labels.Ω => siteScore (S.setup k).score Y ω z) = fun _ => 0 := by
          funext ω
          simp [siteScore, hz]
        rw [e]
        exact measurable_const
    exact hY ht
  have h2 : Measurable fun u : MarkedSample (Tb.stepParameters y) k n => (stageState T k n u).2 :=
    measurable_snd.comp (hSt (Tb.stepParameters y) hfit T k n)
  exact hsig.comp h2
private theorem abs_fittedResponse_le {ℓ : TorusLumps.StepParameters} {T : StageTower ℓ} (S : ScoredStageTower T) (k n : ℕ) [NeZero n] (g : FinePlaquetteFunction)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (hs : ∀ w, 0 ≤ (S.setup k).score w) (q : StageState T k n)
    (hb : ∀ z, |centeredHullResponse (S.setup k).cold (S.setup k).hull n z q.1 q.2.1 q.2.2 (fineWeight g _)| ≤
      C₀ + siteScore (S.setup k).score q.2.1 q.2.2 z) :
    |fittedResponse S g k n q| ≤ C₀ * ((functionSites ℓ.side g k n).card : ℝ) * scoreMeanOver S g k n q := by
  set A := functionSites ℓ.side g k n with hA
  have hsum : 0 ≤ ∑ z ∈ A, siteScore (S.setup k).score q.2.1 q.2.2 z := by
    refine Finset.sum_nonneg fun z _ => ?_
    unfold siteScore
    split_ifs
    · exact hs _
    · exact le_rfl
  have h1 : |fittedResponse S g k n q| ≤ ∑ z ∈ A, (C₀ + siteScore (S.setup k).score q.2.1 q.2.2 z) := by
    unfold fittedResponse
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => hb z)
  refine h1.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  unfold scoreMeanOver meanSiteScore
  rw [← hA]
  rcases A.eq_empty_or_nonempty with h0 | hne
  · simp [h0]
  have e : C₀ * (A.card : ℝ) * (1 + (A.card : ℝ)⁻¹ * ∑ z ∈ A, siteScore (S.setup k).score q.2.1 q.2.2 z) =
      (A.card : ℝ) * C₀ + C₀ * ∑ z ∈ A, siteScore (S.setup k).score q.2.1 q.2.2 z := by
    field_simp
  rw [e]
  nlinarith
private theorem prod_le_sum_pow_card {ι : Type} (I : Finset ι) (hI : I.Nonempty) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∏ i ∈ I, a i ≤ ∑ i ∈ I, a i ^ I.card := by
  obtain ⟨i₀, hi₀, hmax⟩ := I.exists_max_image a hI
  calc ∏ i ∈ I, a i ≤ ∏ _i ∈ I, a i₀ := Finset.prod_le_prod (fun i _ => ha i) hmax
    _ = a i₀ ^ I.card := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun i => a i ^ I.card) (fun i _ => pow_nonneg (ha i) _) hi₀
private theorem cumulantComparisonConstant_nonneg (p : ℕ) : 0 ≤ cumulantComparisonConstant p := by
  unfold cumulantComparisonConstant
  exact Finset.sum_nonneg fun π _ => by positivity
private theorem cumulant_bound_le_rpow (p mb : ℕ) (hp1 : 1 ≤ p) (hp : p ≤ 4) (cc A A₁ E E₁ ε Ke x c : ℝ) (hcc : 0 ≤ cc) (hA : 1 ≤ A)
    (hx : 1 ≤ x) (hA₁ : A + 2 ≤ A₁ * x) (hE : 1 ≤ E) (hE₁ : E ≤ E₁ * x ^ 20) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεK : ε ≤ Ke * Real.exp (-(c * x ^ ((1 : ℝ) / 100))))
    (hbeat : cc * 3 ^ mb * (5 * A₁ ^ 4 * E₁) ^ (mb + 1) * Ke * x ^ (24 * (mb + 1)) * Real.exp (-(c * x ^ ((1 : ℝ) / 100))) ≤
      x ^ (-(20 : ℝ))) :
    cc * ((A + 1) ^ p * E + 1 + ε * (1 + p * (A + 2) ^ p) * E) ^ mb * (ε * (1 + p * (A + 2) ^ p) * E) ≤ x ^ (-(20 : ℝ)) := by
  have hA₁x : 1 ≤ A₁ * x := by linarith
  have hx0 : 0 < x := by linarith
  have hA₁0 : 0 < A₁ := by
    by_contra h
    have : A₁ * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) hx0.le
    linarith
  have hE₁0 : 0 ≤ E₁ := by
    by_contra h
    have : E₁ * x ^ 20 < 0 := mul_neg_of_neg_of_pos (not_le.1 h) (by positivity)
    linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  have hp1r : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hp4 : (p : ℝ) ≤ 4 := by exact_mod_cast hp
  have hA2 : 1 ≤ A + 2 := by linarith
  have hpw : (A + 2) ^ p ≤ (A₁ * x) ^ 4 :=
    (pow_le_pow_left₀ (by linarith) hA₁ p).trans (pow_le_pow_right₀ hA₁x hp)
  have hpw1 : 1 ≤ (A + 2) ^ p := one_le_pow₀ hA2
  set Q := (1 + (p : ℝ) * (A + 2) ^ p) with hQ
  have hQ1 : 1 ≤ Q := by
    have : 0 ≤ (p : ℝ) * (A + 2) ^ p := by positivity
    linarith
  have hQ5 : Q ≤ 5 * (A₁ * x) ^ 4 := by
    have h1 : (p : ℝ) * (A + 2) ^ p ≤ 4 * (A₁ * x) ^ 4 := mul_le_mul hp4 hpw (by positivity) (by norm_num)
    have h2 : 1 ≤ (A₁ * x) ^ 4 := one_le_pow₀ hA₁x
    linarith
  set Z := Q * E with hZ
  have hZ1 : 1 ≤ Z := by nlinarith
  have hZb : Z ≤ (5 * A₁ ^ 4 * E₁) * x ^ 24 := by
    calc Z ≤ (5 * (A₁ * x) ^ 4) * (E₁ * x ^ 20) := mul_le_mul hQ5 hE₁ (by linarith) (by positivity)
      _ = _ := by ring
  have hε' : ε * Q * E = ε * Z := by rw [hZ]; ring
  rw [hε']
  have h1 : (A + 1) ^ p * E ≤ Z := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    have h2 : (A + 1) ^ p ≤ (A + 2) ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
    have h3 : (A + 2) ^ p ≤ (p : ℝ) * (A + 2) ^ p := by nlinarith
    rw [hQ]
    linarith
  have h2 : ε * Z ≤ Z := by nlinarith
  have hbase : (A + 1) ^ p * E + 1 + ε * Z ≤ 3 * ((5 * A₁ ^ 4 * E₁) * x ^ 24) := by linarith
  have hbase0 : 0 ≤ (A + 1) ^ p * E + 1 + ε * Z := by positivity
  have hpow := pow_le_pow_left₀ hbase0 hbase mb
  have hZ0 : 0 ≤ ε * Z := by positivity
  set W := (5 * A₁ ^ 4 * E₁) with hW
  have hεZ : ε * Z ≤ (Ke * Real.exp (-(c * x ^ ((1 : ℝ) / 100)))) * (W * x ^ 24) :=
    mul_le_mul hεK hZb (by linarith) (hε.trans hεK)
  calc cc * ((A + 1) ^ p * E + 1 + ε * Z) ^ mb * (ε * Z)
      ≤ cc * (3 * (W * x ^ 24)) ^ mb * ((Ke * Real.exp (-(c * x ^ ((1 : ℝ) / 100)))) * (W * x ^ 24)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hcc) hεZ hZ0 (by positivity)
    _ = cc * 3 ^ mb * W ^ (mb + 1) * Ke * x ^ (24 * (mb + 1)) * Real.exp (-(c * x ^ ((1 : ℝ) / 100))) := by
        rw [mul_pow, mul_pow, pow_succ W mb, pow_mul x 24 (mb + 1), pow_succ (x ^ 24) mb, ← pow_mul]
        ring
    _ ≤ _ := hbeat
/-- Comparison of the actual Wilson covariance with the covariance of two fitted
responses, at a single separated level of a scored tower. -/
private theorem wilsonCovariance_sub_fitted_at_separated_level
    (hC : LevelTestFunctions.CircleRepProperties) (hSi : levelSitesStatement)
    (hT1 : separatedMarkedMomentsStatement) (hTwo : TwoPointByTotalCovarianceStatement)
    (hcomp : completedObservablesBounded)
    (hfit : (Tb.stepParameters y).Admissible) (Cpf : ℕ → ℝ) (hCpf : ConditionalProductBounds Tb Kr y Cpf)
    {T : StageTower (Tb.stepParameters y)} (S : ScoredStageTower T) {β : ℝ} {k m : ℕ} {n vt : ℝ}
    (hK : S.params = Kr) (hS : S.FollowsFlow β k) (hR : CouplingsAboveFloor (Tb.stepParameters y) β k)
    (hB : IsBlockTorusSide (Tb.stepParameters y) (2 * (Tb.stepParameters y).side ^ m))
    (hr : (1 : ℝ) ≤ clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k))
    (hn : 2 ^ 12 * ((Tb.stepParameters y).side : ℝ) * (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k) : ℝ) ≤ n)
    (hvn : 2 ≤ vt * n)
    {f : Fin 2 → PeriodicLattice.FourTorus (Tb.stepParameters y).side m → ℝ}
    (hf : IsSeparatedTestTuple (Tb.stepParameters y) m n vt f) :
    let ℓ := Tb.stepParameters y
    let N := 2 * ℓ.side ^ m
    let g (i : Fin 2) := fineFunctionOf ℓ.side k m (f i)
    let w (i : Fin 2) := fineWeight (g i) (fineSide ℓ.side k N)
    let μ := markedSampleLaw T β k N
    let F (i : Fin 2) u := fittedResponse S (g i) k N (stageState T k N u)
    let Q (i : Fin 2) u := scoreMeanOver S (g i) k N (stageState T k N u)
    (∀ i, F i =ᵐ[μ] μ[completedCentered S (g i) k N | stageSigma T k N]) →
    Integrable (fun u => Q 0 u * Q 1 u) μ →
    let error := separationError ℓ (Cpf 2) Kr.C₀ (levelGap ℓ.side k n) k N w * ∫ u, Q 0 u * Q 1 u ∂μ
    let covW := cov[curvatureObservable (w 0), curvatureObservable (w 1); wilsonLaw β (fineSide ℓ.side k N)]
    |covW - cov[F 0, F 1; μ]| ≤ error ∧
      |covW| ≤ ((∫ u, F 0 u ^ 2 ∂μ) + ∫ u, F 1 u ^ 2 ∂μ) / 2 + error := by
  classical
  intro ℓ N g w μ F Q hF hQI
  let W := wilsonLaw β (fineSide ℓ.side k N)
  let A (i : Fin 2) := curvatureObservable (w i)
  let c (i : Fin 2) := centering S (g i) k N
  let cent (i : Fin 2) v := A i v - c i
  let E := separationError ℓ (Cpf 2) Kr.C₀ (levelGap ℓ.side k n) k N w
  obtain ⟨hprob, hle, hmap, -, -, -⟩ := hTwo _ hfit hfit.depth_lt T hS.isCutoff_bottom hS.marksMeasurable β S.coeffs k N
  let : IsProbabilityMeasure μ := hprob
  have hbot := measurable_bottomField (ℓ := ℓ) k N
  let : IsProbabilityMeasure W := by
    change IsProbabilityMeasure (wilsonLaw β (fineSide ℓ.side k N))
    rw [← hmap]
    exact Measure.isProbabilityMeasure_map hbot.aemeasurable
  let : IsFiniteMeasure ((markedSampleLaw T β k N).trim hle) := isFiniteMeasure_trim hle
  have hA (i : Fin 2) : MemLp (A i) 2 W := by
    obtain ⟨hm, B, hB⟩ := isBoundedRealRV_curvatureObservable (w i)
    exact MemLp.of_bound hm.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have hcent (i : Fin 2) : MemLp (cent i) 2 W := (hA i).sub (memLp_const _)
  have hF2 (i : Fin 2) : MemLp (F i) 2 μ := by
    obtain ⟨hm, B, hb⟩ := (hcomp ℓ hfit T S.coeffs k N).1 (w i)
    have hO : MemLp (completedObservable T S.coeffs k N (w i)) 2 μ :=
      MemLp.of_bound hm.aestronglyMeasurable B (Filter.Eventually.of_forall hb)
    have hZ : MemLp (completedCentered S (g i) k N) 2 μ := hO.sub (memLp_const _)
    exact (memLp_congr_ae (hF i)).2 (hZ.condExp (m := stageSigma T k N) (by norm_num))
  have hsets (I : Finset (Fin 2)) :
      ∫ v, ∏ i ∈ I, cent i v ∂W = ∫ u, conditionalProduct S β g I k N u ∂μ :=
    integral_prod_centered_eq hC hSi hT1 hfit S hS hr hn hf hmap hbot hle I
  have hmean (i : Fin 2) : ∫ v, cent i v ∂W = ∫ u, F i u ∂μ := by
    have he := hsets {i}
    simpa only [Finset.prod_singleton, conditionalProduct] using he.trans (by
      apply integral_congr_ae
      simpa only [conditionalProduct, Finset.prod_singleton] using (hF i).symm)
  have hsep := separatedAlongTower_of_tuple hC hSi hfit hS hr hn hf (fun i => i) Function.injective_id
  have hsize (i : Fin 2) : weightNorm ℓ.side k (w i) ≤ 1 :=
    weightNorm_testWeight_le_one ℓ.side k m hfit.L_odd.pos (f i) n vt hvn
      (hf.uniformNorm_eq _) (hf.lipschitz _) (hf.lipConst_le _)
  have hprod := (hCpf 2 T S β k N (levelGap ℓ.side k n) g hK hS hR hB hsize hsep).2
  have hi : Integrable (fun u => F 0 u * F 1 u) μ := (hF2 0).integrable_mul (hF2 1)
  have herr : |(∫ v, cent 0 v * cent 1 v ∂W) - ∫ u, F 0 u * F 1 u ∂μ| ≤ E * ∫ u, Q 0 u * Q 1 u ∂μ := by
    rw [show (∫ v, cent 0 v * cent 1 v ∂W) = ∫ u, conditionalProduct S β g Finset.univ k N u ∂μ by
      simpa only [Fin.prod_univ_two] using hsets Finset.univ]
    have hI : Integrable (conditionalProduct S β g Finset.univ k N) μ := integrable_condExp
    rw [← integral_sub hI hi, ← integral_const_mul, ← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le (hQI.const_mul E)
    simpa only [Real.norm_eq_abs, Fin.prod_univ_two] using hprod
  have hcov : |cov[A 0, A 1; W] - cov[F 0, F 1; μ]| ≤ E * ∫ u, Q 0 u * Q 1 u ∂μ := by
    rw [← covariance_sub_const_left ((hA 0).integrable (by norm_num)) (c 0),
        ← covariance_sub_const_right ((hA 1).integrable (by norm_num)) (c 1),
        covariance_eq_sub (hcent 0) (hcent 1), covariance_eq_sub (hF2 0) (hF2 1)]
    change |((∫ v, cent 0 v * cent 1 v ∂W) - _ * _) - ((∫ u, F 0 u * F 1 u ∂μ) - _ * _)| ≤ _
    rw [hmean, hmean, sub_sub_sub_cancel_right]
    exact herr
  have hsum := variance_nonneg (F 0 + F 1) μ
  have hdiff := variance_nonneg (F 0 - F 1) μ
  rw [variance_add (hF2 0) (hF2 1)] at hsum
  rw [variance_sub (hF2 0) (hF2 1)] at hdiff
  have hs (i : Fin 2) : Var[F i; μ] ≤ ∫ u, F i u ^ 2 ∂μ :=
    variance_le_expectation_sq (hF2 i).aestronglyMeasurable
  have hraw : |cov[F 0, F 1; μ]| ≤ ((∫ u, F 0 u ^ 2 ∂μ) + ∫ u, F 1 u ^ 2 ∂μ) / 2 :=
    abs_le.mpr ⟨by linarith [hs 0, hs 1], by linarith [hs 0, hs 1]⟩
  obtain ⟨hlo, hhi⟩ := abs_le.mp hcov
  exact ⟨hcov, abs_le.mpr ⟨by linarith [(abs_le.mp hraw).1], by linarith [(abs_le.mp hraw).2]⟩⟩

private theorem mixedCumulant_bounds_of_tuple (hCum : CutoffLimits.TwoMeasures.CumulantComparison)
    (hSh : Cumulants.MomentCumulantRelations.Holds) (hC : LevelTestFunctions.CircleRepProperties)
    (hSi : levelSitesStatement) (hT1 : separatedMarkedMomentsStatement)
    (hMean : ResponseIsConditionalExpectation) (hTwo : TwoPointByTotalCovarianceStatement)
    (hBd : ResponsesBounded)
    (hfit : (Tb.stepParameters y).Admissible) (hK1 : 1 ≤ Kr.C₀) (Cpf : ℕ → ℝ) (hCpf0 : ∀ p, 0 ≤ Cpf p) (hCpf : ConditionalProductBounds Tb Kr y Cpf)
    {T : StageTower (Tb.stepParameters y)} (S : ScoredStageTower T) {β : ℝ} {k m q : ℕ} {n vt ε E : ℝ}
    (hq : 1 ≤ q) (hK : S.params = Kr) (hS : S.FollowsFlow β k) (hR : CouplingsAboveFloor (Tb.stepParameters y) β k) (hB : IsBlockTorusSide (Tb.stepParameters y) (2 * (Tb.stepParameters y).side ^ m))
    (hn1 : 1 ≤ n) (hr : (1 : ℝ) ≤ clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k))
    (hn : 2 ^ 12 * ((Tb.stepParameters y).side : ℝ) * (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k) : ℝ) ≤ n) (hvn : 2 ≤ vt * n)
    {f : Fin (q + 1) → PeriodicLattice.FourTorus (Tb.stepParameters y).side m → ℝ} (hf : IsSeparatedTestTuple (Tb.stepParameters y) m n vt f)
    (hs : ∀ w, 0 ≤ (S.setup k).score w) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hE : 1 ≤ E)
    (hεb : ∀ I : Finset (Fin (q + 1)), separationErrorConstant (Tb.stepParameters y) Kr.C₀ (Cpf I.card) I.card * Real.exp (-((Tb.stepParameters y).rt / 2 ^ 9 / 2 * n)) ≤ ε)
    (hlive : ∀ᵐ u ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)), ∀ i z,
      |centeredHullResponse (S.setup k).cold (S.setup k).hull (2 * (Tb.stepParameters y).side ^ m) z (stageState T k _ u).1 (stageState T k _ u).2.1
        (stageState T k _ u).2.2 (fineWeight (fineFunctionOf (Tb.stepParameters y).side k m (f i)) _)| ≤
      Kr.C₀ + siteScore (S.setup k).score (stageState T k _ u).2.1 (stageState T k _ u).2.2 z)
    (hNi : ∀ I : Finset (Fin (q + 1)), Integrable (fun u => ∏ i ∈ I,
      scoreMeanOver S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u)) (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)))
    (hNE : ∀ I : Finset (Fin (q + 1)), ∫ u, ∏ i ∈ I,
      scoreMeanOver S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) ≤ E) :
    ‖connectedCurvature β (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ m)) (fun i => testWeight (Tb.stepParameters y).side k m (f i)) -
        Cumulants.mixedCumulant (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m))
          (fun i => response T β S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (testWeight (Tb.stepParameters y).side k m (f i)))‖ ≤
      cumulantComparisonConstant (q + 1) * ((Kr.C₀ * (25 * n) ^ 4 + 1) ^ (q + 1) * E + 1 +
        ε * (1 + ((q + 1 : ℕ) : ℝ) * (Kr.C₀ * (25 * n) ^ 4 + 2) ^ (q + 1)) * E) ^ maxBlockCount (q + 1) *
        (ε * (1 + ((q + 1 : ℕ) : ℝ) * (Kr.C₀ * (25 * n) ^ 4 + 2) ^ (q + 1)) * E) ∧
    ∀ i, ∀ᵐ u ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)),
      |response T β S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (testWeight (Tb.stepParameters y).side k m (f i)) u -
          centering S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m)| ≤
        (Kr.C₀ * (25 * n) ^ 4 + 1) * scoreMeanOver S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) := by
  classical
  obtain ⟨hprob, hle, hmap, -, -, -⟩ := hTwo (Tb.stepParameters y) hfit hfit.depth_lt T hS.isCutoff_bottom hS.marksMeasurable β S.coeffs k (2 * (Tb.stepParameters y).side ^ m)
  have hbot : Measurable (bottomField (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m)) := measurable_bottomField k _
  have : IsProbabilityMeasure (wilsonLaw β (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ m))) := by
    rw [← hmap]
    exact Measure.isProbabilityMeasure_map hbot.aemeasurable
  have : IsFiniteMeasure ((markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)).trim hle) := isFiniteMeasure_trim hle
  set g : Fin (q + 1) → FinePlaquetteFunction := fun i => fineFunctionOf (Tb.stepParameters y).side k m (f i) with hg
  set A : ℝ := Kr.C₀ * (25 * n) ^ 4 with hAdef
  have hA1 : 1 ≤ A := by
    have : (1 : ℝ) ≤ (25 * n) ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  have hones : ∀ i (u : MarkedSample (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m)),
      1 ≤ scoreMeanOver S (g i) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) := fun i u => one_le_scoreMeanOver S k _ _ hs _
  have hcard : ∀ i, ((functionSites (Tb.stepParameters y).side (g i) k (2 * (Tb.stepParameters y).side ^ m)).card : ℝ) ≤ (25 * n) ^ 4 := fun i => by
    have h := card_weightSupportSites_le hC hSi hfit.L_odd hn1 hf i k (2 * (Tb.stepParameters y).side ^ m) le_rfl rfl
    rw [Nat.sub_self, pow_zero, mul_one] at h
    exact h
  have h4 : ∀ i, ∀ᵐ u ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)),
      |fittedResponse S (g i) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u)| ≤
        A * scoreMeanOver S (g i) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) := by
    intro i
    filter_upwards [hlive] with u hu
    refine (abs_fittedResponse_le S k _ (g i) Kr.C₀ hK1 hs _ (hu i)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (zero_le_one.trans (hones i u))
    rw [hAdef]
    exact mul_le_mul_of_nonneg_left (hcard i) (by linarith)
  have h2 : ∀ I : Finset (Fin (q + 1)), ∀ᵐ u ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)),
      |conditionalProduct S β g I k (2 * (Tb.stepParameters y).side ^ m) u - ∏ i ∈ I, fittedResponse S (g i) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u)| ≤
        ε * ∏ i ∈ I, scoreMeanOver S (g i) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) := fun I =>
    (conditionalProduct_of_tuple hC hSi hfit (by linarith) Cpf hCpf0 hCpf S hK hS hR hB hn1 hr hn hvn hf hs I (hεb I)).2
  have hsing : ∀ i, conditionalProduct S β g {i} k (2 * (Tb.stepParameters y).side ^ m) =ᵐ[markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)]
      fun u => response T β S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (testWeight (Tb.stepParameters y).side k m (f i)) u -
        centering S (g i) k (2 * (Tb.stepParameters y).side ^ m) := by
    intro i
    have hint := (conditionalProduct_of_tuple hC hSi hfit (by linarith) Cpf hCpf0 hCpf S hK hS hR hB hn1 hr hn hvn hf hs {i} (hεb {i})).1
    have e1 : (fun u => ∏ j ∈ ({i} : Finset (Fin (q + 1))), completedCentered S (fineFunctionOf (Tb.stepParameters y).side k m (f j)) k (2 * (Tb.stepParameters y).side ^ m) u) =
        fun u => completedObservable T S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (fineWeight (g i) _) u - centering S (g i) k (2 * (Tb.stepParameters y).side ^ m) := by
      funext u
      rw [Finset.prod_singleton]
      rfl
    rw [e1] at hint
    have hO : Integrable (fun u => completedObservable T S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (fineWeight (g i) _) u)
        (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) := by
      have e : (fun u => completedObservable T S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (fineWeight (g i) _) u) =
          fun u => (completedObservable T S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (fineWeight (g i) _) u -
            centering S (g i) k (2 * (Tb.stepParameters y).side ^ m)) + centering S (g i) k (2 * (Tb.stepParameters y).side ^ m) := by
        funext u
        ring
      rw [e]
      exact hint.add (integrable_const _)
    have hm := hMean (Tb.stepParameters y) hfit hfit.depth_lt T hS.isCutoff_bottom hS.marksMeasurable β S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (testWeight (Tb.stepParameters y).side k m (f i))
    have e2 : (fun u => chainMark (Tb.stepParameters y) (fun j => (T.stage j).coupling) S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (testWeight (Tb.stepParameters y).side k m (f i))
        (forgetMarks (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m) u)) =
        fun u => completedObservable T S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (fineWeight (g i) _) u := by
      funext u
      exact chainMark_forgetMarks T S.coeffs k _ _ u
    rw [e2] at hm
    have h3 := condExp_sub (m := stageSigma T k (2 * (Tb.stepParameters y).side ^ m)) hO
      (integrable_const (μ := markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) (centering S (g i) k (2 * (Tb.stepParameters y).side ^ m)))
    rw [condExp_const hle] at h3
    have e3 : conditionalProduct S β g {i} k (2 * (Tb.stepParameters y).side ^ m) =
        (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m))[(fun u => completedObservable T S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (fineWeight (g i) _) u) -
          fun _ => centering S (g i) k (2 * (Tb.stepParameters y).side ^ m) | stageSigma T k (2 * (Tb.stepParameters y).side ^ m)] := by
      unfold conditionalProduct
      congr 1
    rw [e3]
    filter_upwards [h3, hm] with u a b
    rw [a, b]
    rfl
  have h3 : ∀ i, ∀ᵐ u ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)),
      |response T β S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (testWeight (Tb.stepParameters y).side k m (f i)) u - centering S (g i) k (2 * (Tb.stepParameters y).side ^ m) -
          fittedResponse S (g i) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u)| ≤
        ε * scoreMeanOver S (g i) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) := by
    intro i
    filter_upwards [h2 {i}, hsing i] with u a b
    rw [b] at a
    simpa using a
  refine ⟨?_, fun i => ?_⟩
  · refine mixedCumulant_comparison_of_conditional hCum hSh (wilsonLaw β (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ m)))
      (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) (q + 1) (by omega) (fun i => curvatureObservable (testWeight (Tb.stepParameters y).side k m (f i)))
      (fun i => response T β S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (testWeight (Tb.stepParameters y).side k m (f i)))
      (fun i u => fittedResponse S (g i) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u))
      (fun i u => scoreMeanOver S (g i) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u))
      (fun i => centering S (g i) k (2 * (Tb.stepParameters y).side ^ m))
      (fun I => conditionalProduct S β g I k (2 * (Tb.stepParameters y).side ^ m)) ε A E hε0 hε1 hA1 hE
      (fun i => isBoundedRealRV_curvatureObservable _)
      (fun i => (hBd (Tb.stepParameters y) hfit hfit.depth_lt T hS.isCutoff_bottom hS.marksMeasurable β S.coeffs k (2 * (Tb.stepParameters y).side ^ m) _).1)
      (fun i => (hBd (Tb.stepParameters y) hfit hfit.depth_lt T hS.isCutoff_bottom hS.marksMeasurable β S.coeffs k (2 * (Tb.stepParameters y).side ^ m) _).2)
      (fun i => Filter.Eventually.of_forall fun u => hones i u)
      (fun I => integrable_condExp) hNi hNE
      (fun I _ => integral_prod_centered_eq hC hSi hT1 hfit S hS hr hn hf hmap hbot hle I)
      (fun I _ => h2 I) h3 h4
  · filter_upwards [h3 i, h4 i] with u a b
    have e : response T β S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (testWeight (Tb.stepParameters y).side k m (f i)) u - centering S (g i) k (2 * (Tb.stepParameters y).side ^ m) =
        (response T β S.coeffs k (2 * (Tb.stepParameters y).side ^ m) (testWeight (Tb.stepParameters y).side k m (f i)) u - centering S (g i) k (2 * (Tb.stepParameters y).side ^ m) -
          fittedResponse S (g i) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u)) + fittedResponse S (g i) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) := by
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h5 := hones i u
    nlinarith
private theorem integrable_and_integral_le_of_lintegral_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (F : Ω → ℝ) (hm : Measurable F)
    (h0 : ∀ u, 0 ≤ F u) (c : ℝ) (hc : 0 ≤ c) (hb : ∫⁻ u, ENNReal.ofReal (F u) ∂μ ≤ ENNReal.ofReal c) :
    Integrable F μ ∧ ∫ u, F u ∂μ ≤ c := by
  have hfin : ∫⁻ u, ENNReal.ofReal (F u) ∂μ < ⊤ := hb.trans_lt ENNReal.ofReal_lt_top
  refine ⟨⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h0)).2 hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hc hb
abbrev _root_.YangMills.SharedProofs.p45438 := @integrable_and_integral_le_of_lintegral_le
private theorem window_bounds {x n vt L : ℝ} (hx : Real.exp 1 ≤ x) (hL : (2 : ℝ) ^ 16 ≤ L)
    (ha : 2 ^ 12 * L * (clusterRange x : ℝ) ≤ n) (hb : n ≤ x ^ ((1 : ℝ) / 90)) (hv : (2 / vt) ^ 100 ≤ x) (hvt : 0 < vt) :
    1 ≤ (clusterRange x : ℝ) ∧ x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) ∧ x ^ ((1 : ℝ) / 100) ≤ n ∧ 1 ≤ n ∧ n ^ 4 ≤ x ∧ 2 ≤ vt * n ∧
      1 ≤ Real.log x := by
  have hx1 : 1 ≤ x := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hx0 : 0 < x := by linarith
  have hrx : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) := Nat.le_ceil _
  have hpw1 : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx1 (by norm_num)
  have hr1 : 1 ≤ (clusterRange x : ℝ) := hpw1.trans hrx
  have hc1 : (1 : ℝ) ≤ 2 ^ 12 * L := by linarith
  have hrn : (clusterRange x : ℝ) ≤ n := by
    calc (clusterRange x : ℝ) = 1 * (clusterRange x : ℝ) := (one_mul _).symm
      _ ≤ 2 ^ 12 * L * (clusterRange x : ℝ) := mul_le_mul_of_nonneg_right hc1 (by linarith)
      _ ≤ n := ha
  have hxn : x ^ ((1 : ℝ) / 100) ≤ n := hrx.trans hrn
  have hn1 : 1 ≤ n := hr1.trans hrn
  have hn4 : n ^ 4 ≤ x := by
    have h1 : n ^ 4 ≤ (x ^ ((1 : ℝ) / 90)) ^ 4 := pow_le_pow_left₀ (by linarith) hb 4
    have h2 : (x ^ ((1 : ℝ) / 90)) ^ 4 = x ^ ((4 : ℝ) / 90) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have h3 : x ^ ((4 : ℝ) / 90) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at h3
    linarith
  have hvn : 2 ≤ vt * n := by
    have h2 : ((2 / vt) ^ 100) ^ ((1 : ℝ) / 100) ≤ x ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by positivity) hv (by norm_num)
    have h3 : ((2 / vt) ^ 100) ^ ((1 : ℝ) / 100) = 2 / vt := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [h3] at h2
    have h4 : 2 / vt ≤ n := h2.trans hxn
    rw [div_le_iff₀ hvt] at h4
    linarith [mul_comm vt n]
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact hx
  exact ⟨hr1, hrx, hxn, hn1, hn4, hvn, hlog1⟩
private theorem blockSide_of_window {ℓ : TorusLumps.StepParameters} {x : ℝ} {m : ℕ} (hx0 : 0 < x) (hlog1 : 1 ≤ Real.log x)
    (hs : Real.exp (Real.log x ^ 3) ≤ 2 * (ℓ.side : ℝ) ^ m) (hLn : ((ℓ.side * ℓ.n₀ : ℕ) : ℝ) + 3 ≤ x) :
    ℓ.side * ℓ.n₀ ≤ 2 * ℓ.side ^ m ∧ IsBlockTorusSide ℓ (2 * ℓ.side ^ m) := by
  have hside : x ≤ 2 * (ℓ.side : ℝ) ^ m := by
    have h2 : Real.log x ≤ Real.log x ^ 3 := by
      have h3 : (1 : ℝ) ≤ Real.log x ^ 2 := one_le_pow₀ hlog1
      calc Real.log x = Real.log x * 1 := (mul_one _).symm
        _ ≤ Real.log x * Real.log x ^ 2 := mul_le_mul_of_nonneg_left h3 (by linarith)
        _ = _ := by ring
    have h3 : x ≤ Real.exp (Real.log x ^ 3) := by
      calc x = Real.exp (Real.log x) := (Real.exp_log hx0).symm
        _ ≤ _ := Real.exp_le_exp.2 h2
    exact h3.trans hs
  have hsideN : ℓ.side * ℓ.n₀ ≤ 2 * ℓ.side ^ m := by
    have : ((ℓ.side * ℓ.n₀ : ℕ) : ℝ) ≤ ((2 * ℓ.side ^ m : ℕ) : ℝ) := by
      have e : ((2 * ℓ.side ^ m : ℕ) : ℝ) = 2 * (ℓ.side : ℝ) ^ m := by push_cast; ring
      rw [e]
      linarith
    exact_mod_cast this
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hside
    have : (0 : ℝ) ≤ ((ℓ.side * ℓ.n₀ : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  exact ⟨hsideN, Dvd.dvd.mul_left (dvd_pow_self _ hm0) 2, hsideN⟩
private theorem moment_bound_le_pow {x r C Cm : ℝ} {P : ℕ} (hx1 : 1 ≤ x) (hr1 : 1 ≤ r)
    (hrx : (r - 1) ≤ x ^ ((1 : ℝ) / 100) + 0) (hlog1 : 1 ≤ Real.log x) (hCm1 : 1 ≤ Cm) (hC1 : 1 ≤ C) (hC : C ≤ Cm) (hP : P ≤ 4) :
    (C * r ^ 4 * Real.log x) ^ P ≤ (16 * Cm) ^ 4 * x ^ 20 := by
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hr2 : r ≤ 2 * x := by
    have h2 : x ^ ((1 : ℝ) / 100) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at h2
    linarith
  have hb5 : r ^ 4 * Real.log x ≤ 16 * x ^ 5 := by
    have h1 : r ^ 4 ≤ (2 * x) ^ 4 := pow_le_pow_left₀ (by linarith) hr2 4
    have h2 : Real.log x ≤ x := Real.log_le_self hx0.le
    calc r ^ 4 * Real.log x ≤ (2 * x) ^ 4 * x := mul_le_mul h1 h2 hlog0 (by positivity)
      _ = 16 * x ^ 5 := by ring
  have h0 : 0 ≤ r ^ 4 * Real.log x := by positivity
  have h1 : C * r ^ 4 * Real.log x ≤ Cm * 16 * x ^ 5 := by
    calc C * r ^ 4 * Real.log x = C * (r ^ 4 * Real.log x) := by ring
      _ ≤ Cm * (16 * x ^ 5) := mul_le_mul hC hb5 h0 (by linarith)
      _ = _ := by ring
  have h2 : 1 ≤ Cm * 16 * x ^ 5 := by
    have h3 : (1 : ℝ) ≤ x ^ 5 := one_le_pow₀ hx1
    have h4 : (1 : ℝ) ≤ Cm * 16 := by linarith
    exact one_le_mul_of_one_le_of_one_le h4 h3
  have hC0 : 0 ≤ C * r ^ 4 * Real.log x := by positivity
  calc (C * r ^ 4 * Real.log x) ^ P ≤ (Cm * 16 * x ^ 5) ^ P := pow_le_pow_left₀ hC0 h1 P
    _ ≤ (Cm * 16 * x ^ 5) ^ 4 := pow_le_pow_right₀ h2 hP
    _ = _ := by ring
private theorem majorant_products_bounds {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] {q : ℕ}
    (N : Fin (q + 1) → Ω → ℝ) (hq : q + 1 ≤ 4) (h1 : ∀ i u, 1 ≤ N i u) (hm : ∀ i, Measurable (N i))
    {bd : ℕ → ℝ} (hNm : ∀ i (P : ℕ), 1 ≤ P → Integrable (fun u => N i u ^ P) ν ∧ ∫ u, N i u ^ P ∂ν ≤ bd P)
    (B : ℝ) (hb : ∀ P, 1 ≤ P → P ≤ 4 → bd P ≤ B) (E : ℝ) (hE : 4 * B ≤ E) (hE1 : 1 ≤ E) :
    (∀ I : Finset (Fin (q + 1)), Integrable (fun u => ∏ i ∈ I, N i u) ν) ∧
    ∀ I : Finset (Fin (q + 1)), ∫ u, ∏ i ∈ I, N i u ∂ν ≤ E := by
  have hsum : ∀ I : Finset (Fin (q + 1)), I.Nonempty → Integrable (fun u => ∑ i ∈ I, N i u ^ I.card) ν := fun I hI =>
    integrable_finsetSum _ fun i _ => (hNm i _ hI.card_pos).1
  have hle : ∀ I : Finset (Fin (q + 1)), I.Nonempty → ∀ u, ∏ i ∈ I, N i u ≤ ∑ i ∈ I, N i u ^ I.card := fun I hI u =>
    prod_le_sum_pow_card I hI _ fun i => zero_le_one.trans (h1 i u)
  have hi : ∀ I : Finset (Fin (q + 1)), Integrable (fun u => ∏ i ∈ I, N i u) ν := by
    intro I
    rcases I.eq_empty_or_nonempty with rfl | hI
    · simp
    refine Integrable.mono' (hsum I hI) (Finset.measurable_fun_prod _ fun i _ => hm i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ => zero_le_one.trans (h1 i u))]
    exact hle I hI u
  refine ⟨hi, fun I => ?_⟩
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simpa using hE1
  have hc4 : I.card ≤ 4 := by
    have : I.card ≤ q + 1 := by simpa using Finset.card_le_univ I
    omega
  have hc4r : (I.card : ℝ) ≤ 4 := by exact_mod_cast hc4
  have hB0 : 0 ≤ B := by
    obtain ⟨i, -⟩ := hI
    have h2 := (hNm i 1 le_rfl).2
    have h3 := hb 1 le_rfl (by omega)
    have h4 : 0 ≤ ∫ u, N i u ^ 1 ∂ν := integral_nonneg fun u => pow_nonneg (zero_le_one.trans (h1 i u)) 1
    linarith
  calc _ ≤ ∫ u, ∑ i ∈ I, N i u ^ I.card ∂ν := integral_mono (hi I) (hsum I hI) fun u => hle I hI u
    _ = ∑ i ∈ I, ∫ u, N i u ^ I.card ∂ν := integral_finsetSum _ fun i _ => (hNm i _ hI.card_pos).1
    _ ≤ ∑ _i ∈ I, B := Finset.sum_le_sum fun i _ => (hNm i _ hI.card_pos).2.trans (hb _ hI.card_pos hc4)
    _ = (I.card : ℝ) * B := by simp
    _ ≤ 4 * B := mul_le_mul_of_nonneg_right hc4r hB0
    _ ≤ E := hE
private theorem integral_abs_pow_le_of_majorant {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (F N : Ω → ℝ) (P : ℕ)
    {C₀ n r lg CNP : ℝ} (hi : Integrable (fun u => N u ^ P) ν) (hb : ∫ u, N u ^ P ∂ν ≤ (CNP * r ^ 4 * lg) ^ P)
    (hFN : ∀ᵐ u ∂ν, |F u| ≤ (C₀ * (25 * n) ^ 4 + 1) * N u) (hK1 : 1 ≤ C₀) (hn1 : 1 ≤ n) (hr1 : 1 ≤ r) (hlg : 0 ≤ lg)
    (hC : 1 ≤ CNP) (hN : ∀ u, 0 ≤ N u) :
    ∫ u, |F u| ^ P ∂ν ≤ ((|C₀| * 25 ^ 4 + 2) * CNP * n ^ 4 * r ^ 4 * lg) ^ P := by
  have hn41 : (1 : ℝ) ≤ n ^ 4 := one_le_pow₀ hn1
  have h1 : ∫ u, |F u| ^ P ∂ν ≤ ∫ u, (C₀ * (25 * n) ^ 4 + 1) ^ P * N u ^ P ∂ν := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => by positivity) (hi.const_mul _) ?_
    filter_upwards [hFN] with u hu
    rw [← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hu _
  rw [integral_const_mul] at h1
  have hQ : 0 ≤ CNP * r ^ 4 * lg := by positivity
  refine h1.trans ?_
  have hC₀abs : |C₀| = C₀ := abs_of_pos (by linarith)
  have h2 : C₀ * (25 * n) ^ 4 + 1 ≤ (|C₀| * 25 ^ 4 + 2) * n ^ 4 := by
    rw [hC₀abs]
    have e : (C₀ * 25 ^ 4 + 2) * n ^ 4 = C₀ * (25 * n) ^ 4 + 2 * n ^ 4 := by ring
    rw [e]
    linarith
  calc _ ≤ (C₀ * (25 * n) ^ 4 + 1) ^ P * (CNP * r ^ 4 * lg) ^ P := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ((C₀ * (25 * n) ^ 4 + 1) * (CNP * r ^ 4 * lg)) ^ P := (mul_pow _ _ _).symm
    _ ≤ _ := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        calc _ ≤ (|C₀| * 25 ^ 4 + 2) * n ^ 4 * (CNP * r ^ 4 * lg) := mul_le_mul_of_nonneg_right h2 hQ
          _ = _ := by ring
set_option maxHeartbeats 1600000 in
private theorem tupleCumulantApproxAt_of_bounds (hCum : CutoffLimits.TwoMeasures.CumulantComparison)
    (hSh : Cumulants.MomentCumulantRelations.Holds) (hC : LevelTestFunctions.CircleRepProperties)
    (hSi : levelSitesStatement) (hT1 : separatedMarkedMomentsStatement)
    (hMean : ResponseIsConditionalExpectation) (hTwo : TwoPointByTotalCovarianceStatement)
    (hBd : ResponsesBounded) (hSt : StageStatesMeasurableStatement)
    (hfit : (Tb.stepParameters y).Admissible) (Cpf : ℕ → ℝ) (hCpf0 : ∀ p, 0 ≤ Cpf p) (hCpf : ConditionalProductBounds Tb Kr y Cpf)
    (hGa : ∀ (β : ℝ) (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T) (tp : ℕ),
      S.params = Kr → S.FollowsFlow β tp → CouplingsAboveFloor (Tb.stepParameters y) β tp →
      (∀ u < tp, (T.stage u).toStepSetup.IsWellPosed ∧ |(T.stage u).toStepSetup.nextCoupling - (T.stage u).toStepSetup.coupling| ≤ 2 * Tb.B) ∧
      ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (Tb.stepParameters y) n →
        (∀ w ≤ tp, ∀ᵐ d ∂(markedSampleLaw T β w n), IsLiveState (Tb.stepParameters y) (T.stage w).coupling (T.stage w).labelWeight
          (stageState T w n d).1 (stageState T w n d).2.1 (stageState T w n d).2.2) ∧
        ∀ u < tp, ∀ᵐ d ∂(markedSampleLaw T β (u + 1) n),
          (StepGas.hotCaseGround (T.stage u).toStepSetup d.2.2.1 (stageState T (u + 1) n d).2).IsAdmissibleGround)
    (hNa : ScoreMeanMomentBounds Tb Kr y) : tupleCumulantApproxAt Tb Kr y := by
  classical
  intro vt hvt hvt1
  obtain ⟨x₁, hN⟩ := hNa
  choose! CN hCN1 hCN using hN
  have hrt := hfit.rt_pos
  set c : ℝ := (Tb.stepParameters y).rt / 2 ^ 9 / 2 with hc
  have hc0 : 0 < c := by positivity
  set Ke : ℝ := ∑ p ∈ Finset.range 5, |separationErrorConstant (Tb.stepParameters y) Kr.C₀ (Cpf p) p| + 1 with hKe
  have hKe1 : 1 ≤ Ke := by
    have : 0 ≤ ∑ p ∈ Finset.range 5, |separationErrorConstant (Tb.stepParameters y) Kr.C₀ (Cpf p) p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  set A₁ : ℝ := |Kr.C₀| * 25 ^ 4 + 3 with hA₁
  set Cmax : ℝ := ∑ P ∈ Finset.range 5, |CN P| + 1 with hCmax
  have hCmax1 : 1 ≤ Cmax := by
    have : 0 ≤ ∑ P ∈ Finset.range 5, |CN P| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  set E₁ : ℝ := 4 * (16 * Cmax) ^ 4 with hE₁
  have hE₁1 : 1 ≤ E₁ := by
    have : 1 ≤ (16 * Cmax) ^ 4 := one_le_pow₀ (by linarith)
    linarith
  have hKf : ∀ p, 0 ≤ cumulantComparisonConstant p * 3 ^ maxBlockCount p * (5 * A₁ ^ 4 * E₁) ^ (maxBlockCount p + 1) * Ke := fun p => by
    have := cumulantComparisonConstant_nonneg p
    positivity
  have hb := fun p => exists_pow_mul_exp_le_rpow _ c (24 * (maxBlockCount p + 1)) (hKf p) hc0
  choose xb hxb1 hxb using hb
  obtain ⟨xe, hxe1, hxe⟩ := exists_pow_mul_exp_le_rpow Ke c 0 (by linarith) hc0
  set x₀ : ℝ := ∑ p ∈ Finset.range 5, |xb p| + |xe| + (2 / vt) ^ 100 + |x₁| + (((Tb.stepParameters y).side * (Tb.stepParameters y).n₀ : ℕ) + 3) + Real.exp 1 with hx₀
  have hsum0 : 0 ≤ ∑ p ∈ Finset.range 5, |xb p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hvp : 0 ≤ (2 / vt) ^ 100 := by positivity
  have hexp := Real.exp_pos 1
  have hxe_abs := abs_nonneg xe
  have hx₁_abs := abs_nonneg x₁
  have hb1 : ∀ p ∈ Finset.range 5, |xb p| ≤ x₀ := fun p hp => by
    have h2 := Finset.single_le_sum (f := fun p => |xb p|) (fun _ _ => abs_nonneg _) hp
    rw [hx₀]
    linarith
  have hb2 : |xe| ≤ x₀ := by rw [hx₀]; linarith
  have hb3 : (2 / vt) ^ 100 ≤ x₀ := by rw [hx₀]; linarith
  have hb4 : |x₁| ≤ x₀ := by rw [hx₀]; linarith
  have hb5 : (((Tb.stepParameters y).side * (Tb.stepParameters y).n₀ : ℕ) : ℝ) + 3 ≤ x₀ := by rw [hx₀]; linarith
  have hb6 : Real.exp 1 ≤ x₀ := by rw [hx₀]; linarith
  refine ⟨fun r => (|Kr.C₀| * 25 ^ 4 + 2) * CN (2 * r), x₀, ?_⟩
  intro q β k m n T S hq1 hq3 hW hK hS f hf
  have hxdef : ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k = (couplingFlow (Tb.stepParameters y) β k).1 := rfl
  have hfl : x₀ ≤ ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k := hW.le_coupling
  rw [← hxdef]
  generalize hxx : ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k = x at hfl
  have hxe1' : Real.exp 1 ≤ x := hb6.trans hfl
  have hx1 : 1 ≤ x := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith only [this, hxe1']
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  set r : ℝ := (clusterRange x : ℝ) with hrdef
  have hLr : (2 : ℝ) ^ 16 ≤ ((Tb.stepParameters y).side : ℝ) := by exact_mod_cast hfit.L_ge
  have habove : 2 ^ 12 * ((Tb.stepParameters y).side : ℝ) * r ≤ n := by
    have := hW.lower_le
    rw [← hxdef, hxx] at this
    exact this
  have hnb : n ≤ x ^ ((1 : ℝ) / 90) := by
    have := hW.le_upper
    rw [← hxdef, hxx] at this
    exact this
  have hvx : (2 / vt) ^ 100 ≤ x := hb3.trans hfl
  obtain ⟨hr1, hrx, hxn, hn1, hn4, hvn, hlog1⟩ := window_bounds hxe1' hLr habove hnb hvx hvt
  have hlog0 : 0 ≤ Real.log x := zero_le_one.trans hlog1
  have hLn3 : (((Tb.stepParameters y).side * (Tb.stepParameters y).n₀ : ℕ) : ℝ) + 3 ≤ x := hb5.trans hfl
  have hs3 : Real.exp (Real.log x ^ 3) ≤ 2 * ((Tb.stepParameters y).side : ℝ) ^ m := by
    have h1 := hW.side_ge
    rw [← hxdef, hxx] at h1
    exact h1
  obtain ⟨hsideN, hB⟩ := blockSide_of_window hx0 hlog1 hs3 hLn3
  have hR : CouplingsAboveFloor (Tb.stepParameters y) β k := fun j hj => hW.flow_ge j (by omega)
  have hresp := hS.isAdmissible k le_rfl
  have hlet : (S.setup k).responseParams = Kr := (hS.params_eq k).trans hK
  have hKfit : Kr.Admissible (Tb.stepParameters y) := hlet ▸ hresp.params_admissible
  have hK1 : 1 ≤ Kr.C₀ := by
    rw [hKfit.C₀_eq]
    have h1 := hfit.a_ge
    have h2 := hKfit.N₀_nonneg
    have h3 := hKfit.Kc_ge
    linarith only [h1, h2, h3]
  have hs : ∀ w, 0 ≤ (S.setup k).score w := hresp.price.nonneg
  have hsb : Measurable (S.setup k).score := hresp.price.borel
  obtain ⟨hprob, -, -, -, -, -⟩ := hTwo (Tb.stepParameters y) hfit hfit.depth_lt T hS.isCutoff_bottom hS.marksMeasurable β S.coeffs k (2 * (Tb.stepParameters y).side ^ m)
  set ε : ℝ := Ke * Real.exp (-(c * n)) with hε
  have hKe0 : 0 ≤ Ke := zero_le_one.trans hKe1
  have hε0 : 0 ≤ ε := mul_nonneg hKe0 (Real.exp_pos _).le
  have hεx : ε ≤ Ke * Real.exp (-(c * x ^ ((1 : ℝ) / 100))) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hxn hc0.le))) hKe0
  have hxe' : xe ≤ x := (le_abs_self xe).trans (hb2.trans hfl)
  have hε1 : ε ≤ 1 := by
    have h1 := hxe x hxe'
    rw [pow_zero, mul_one] at h1
    have h2 : x ^ (-(20 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    exact hεx.trans (h1.trans h2)
  have hεb : ∀ I : Finset (Fin (q + 1)), separationErrorConstant (Tb.stepParameters y) Kr.C₀ (Cpf I.card) I.card * Real.exp (-((Tb.stepParameters y).rt / 2 ^ 9 / 2 * n)) ≤ ε := by
    intro I
    have hI : I.card ∈ Finset.range 5 := by
      have : I.card ≤ q + 1 := by simpa using Finset.card_le_univ I
      exact Finset.mem_range.2 (by omega)
    have h1 : separationErrorConstant (Tb.stepParameters y) Kr.C₀ (Cpf I.card) I.card ≤ Ke := by
      have h2 := Finset.single_le_sum (f := fun p => |separationErrorConstant (Tb.stepParameters y) Kr.C₀ (Cpf p) p|) (fun _ _ => abs_nonneg _) hI
      have h3 := le_abs_self (separationErrorConstant (Tb.stepParameters y) Kr.C₀ (Cpf I.card) I.card)
      rw [hKe]
      linarith only [h2, h3]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hgr := ((hGa β T S k hK hS hR).2 (2 * (Tb.stepParameters y).side ^ m) hB).1 k le_rfl
  have hlevel := (hS.isFlowStep k le_rfl).depth_eq
  have hsz : ∀ i, ∀ t', t' = k →
      weightNorm (Tb.stepParameters y).side t' (fineWeight (fineFunctionOf (Tb.stepParameters y).side k m (f i)) (fineSide (Tb.stepParameters y).side t' (2 * (Tb.stepParameters y).side ^ m))) ≤ 1 := by
    rintro i _ rfl
    exact weightNorm_testWeight_le_one (Tb.stepParameters y).side _ m hfit.L_odd.pos (f i) n vt hvn (hf.uniformNorm_eq _) (hf.lipschitz _) (hf.lipConst_le _)
  have hlive : ∀ᵐ u ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)), ∀ i z,
      |centeredHullResponse (S.setup k).cold (S.setup k).hull (2 * (Tb.stepParameters y).side ^ m) z (stageState T k _ u).1 (stageState T k _ u).2.1
        (stageState T k _ u).2.2 (fineWeight (fineFunctionOf (Tb.stepParameters y).side k m (f i)) _)| ≤
      Kr.C₀ + siteScore (S.setup k).score (stageState T k _ u).2.1 (stageState T k _ u).2.2 z := by
    filter_upwards [hgr] with u hu i z
    have h1 := hresp.bounds.size_hull (2 * (Tb.stepParameters y).side ^ m) hB z _ _ _ hu (fineWeight (fineFunctionOf (Tb.stepParameters y).side k m (f i)) _)
    have h2 := hsz i _ hlevel
    rw [hlet] at h1
    have hsc : 0 ≤ Kr.C₀ + siteScore (S.setup k).score (stageState T k _ u).2.1 (stageState T k _ u).2.2 z := by
      have : 0 ≤ siteScore (S.setup k).score (stageState T k _ u).2.1 (stageState T k _ u).2.2 z := by
        unfold siteScore
        split_ifs
        · exact hs _
        · exact le_rfl
      linarith only [this, hK1]
    exact h1.trans (mul_le_of_le_one_right hsc h2)
  have hx₁' : x₁ ≤ ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k := by
    rw [hxx]
    exact (le_abs_self x₁).trans (hb4.trans hfl)
  have hNm : ∀ (g : FinePlaquetteFunction) (P : ℕ), 1 ≤ P →
      Integrable (fun u => scoreMeanOver S g k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) ^ P) (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) ∧
      ∫ u, scoreMeanOver S g k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u) ^ P ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) ≤
        (CN P * r ^ 4 * Real.log x) ^ P := by
    intro g P hP
    have h := hCN P hP T S β k m g hK hS hR hx₁' hsideN
    rw [hxx] at h
    have hC1 := hCN1 P hP
    refine integrable_and_integral_le_of_lintegral_le _ _ ((measurable_scoreMeanOver hSt hfit S k _ g hsb).pow_const P)
      (fun u => pow_nonneg (zero_le_one.trans (one_le_scoreMeanOver S k _ g hs _)) P) _ ?_ h
    have : 0 ≤ CN P * r ^ 4 * Real.log x := by positivity
    positivity
  set E : ℝ := E₁ * x ^ 20 with hE
  have hxp : ∀ a : ℕ, 1 ≤ x ^ a := fun a => one_le_pow₀ hx1
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le hE₁1 (hxp 20)
  have hrx' : r - 1 ≤ x ^ ((1 : ℝ) / 100) + 0 := by
    have h1 : r < x ^ ((1 : ℝ) / 100) + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hCle : ∀ P, 1 ≤ P → P ≤ 4 → CN P ≤ Cmax := by
    intro P hP1 hP4
    have h2 := Finset.single_le_sum (f := fun P => |CN P|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega : P < 5))
    have h3 := le_abs_self (CN P)
    rw [hCmax]
    linarith only [h2, h3]
  have hPb : ∀ P, 1 ≤ P → P ≤ 4 → (CN P * r ^ 4 * Real.log x) ^ P ≤ (16 * Cmax) ^ 4 * x ^ 20 := fun P hP1 hP4 =>
    moment_bound_le_pow hx1 hr1 hrx' hlog1 hCmax1 (hCN1 P hP1) (hCle P hP1 hP4) hP4
  obtain ⟨hNi, hNE⟩ := majorant_products_bounds (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m))
    (fun i u => scoreMeanOver S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u)) (by omega)
    (fun i u => one_le_scoreMeanOver S k _ _ hs _) (fun i => measurable_scoreMeanOver hSt hfit S k _ _ hsb)
    (fun i P hP => hNm _ P hP) ((16 * Cmax) ^ 4 * x ^ 20) hPb E (by rw [hE, hE₁]; ring_nf; exact le_rfl) hE1
  obtain ⟨hcum, hmom⟩ := mixedCumulant_bounds_of_tuple hCum hSh hC hSi hT1 hMean hTwo hBd hfit hK1 Cpf hCpf0 hCpf S hq1 hK hS hR hB hn1
    (by rw [hxx]; exact hr1) (by rw [hxx]; exact habove) hvn hf hs hε0 hε1 hE1 hεb hlive hNi hNE
  have hC₀abs : |Kr.C₀| = Kr.C₀ := abs_of_pos (by linarith)
  have hA1 : 1 ≤ Kr.C₀ * (25 * n) ^ 4 := by
    have h25 : (1 : ℝ) ≤ (25 * n) ^ 4 := one_le_pow₀ (by linarith only [hn1])
    exact one_le_mul_of_one_le_of_one_le hK1 h25
  refine ⟨hcum.trans ?_, fun i => ?_⟩
  · have hp : (q + 1) ∈ Finset.range 5 := Finset.mem_range.2 (by omega)
    have hxbq : xb (q + 1) ≤ x := (le_abs_self _).trans ((hb1 _ hp).trans hfl)
    refine cumulant_bound_le_rpow (q + 1) (maxBlockCount (q + 1)) (by omega) (by omega) _ _ A₁ E E₁ ε Ke x c (cumulantComparisonConstant_nonneg _)
      hA1 hx1 ?_ hE1 le_rfl hε0 hε1 hεx (hxb (q + 1) x hxbq)
    have e : Kr.C₀ * (25 * n) ^ 4 = Kr.C₀ * 25 ^ 4 * n ^ 4 := by ring
    rw [e, hA₁, hC₀abs]
    have h1 : Kr.C₀ * 25 ^ 4 * n ^ 4 ≤ Kr.C₀ * 25 ^ 4 * x := mul_le_mul_of_nonneg_left hn4 (by positivity)
    have e2 : (Kr.C₀ * 25 ^ 4 + 3) * x = Kr.C₀ * 25 ^ 4 * x + 3 * x := by ring
    rw [e2]
    linarith only [h1, hx1]
  · refine ⟨centering S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m), fun rr hrr => ?_⟩
    have hP : 1 ≤ 2 * rr := by omega
    obtain ⟨hi, hb⟩ := hNm (fineFunctionOf (Tb.stepParameters y).side k m (f i)) (2 * rr) hP
    exact integral_abs_pow_le_of_majorant (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) (fun u => response T β S.coeffs k (2 * (Tb.stepParameters y).side ^ m)
      (testWeight (Tb.stepParameters y).side k m (f i)) u - centering S (fineFunctionOf (Tb.stepParameters y).side k m (f i)) k (2 * (Tb.stepParameters y).side ^ m)) _ (2 * rr) hi hb (hmom i) hK1 hn1 hr1
      hlog0 (hCN1 _ hP) (fun u => zero_le_one.trans (one_le_scoreMeanOver S k _ _ hs _))
end
section
open TorusFields TorusLumps FreeEnergies TransfersOffTheWalk
private theorem atResponseParameters_of_three {P Q R S : RenormalizationStepParameters.ParameterAssignment → ResponseParameters → ℝ → Prop}
    (hP : AtResponseParameters P) (hQ : AtResponseParameters Q) (hR : AtResponseParameters R)
    (H : ∀ T K y, (T.stepParameters y).Admissible → P T K y → Q T K y → R T K y → S T K y) : AtResponseParameters S := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, h₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, hr₂, h₂⟩ := hQ a ha
  obtain ⟨L₃, r₃, C₃, hr₃, h₃⟩ := hR a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)), max C₁ (max C₂ C₃),
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), ?_⟩
  intro L hodd hL T hTa hTL hD hcs hOn hrt hC K
  have hL₂ : max L₂ L₃ ≤ L := (le_max_right _ _).trans hL
  have hC₂ : max C₂ C₃ ≤ T.derivBound := (le_max_right _ _).trans hC
  have hrt₂ := hrt.trans (min_le_right _ _)
  obtain ⟨y₁, hy₁⟩ := h₁ L hodd ((le_max_left _ _).trans hL) T hTa hTL hD hcs hOn
    (hrt.trans (min_le_left _ _)) ((le_max_left _ _).trans hC) K
  obtain ⟨y₂, hy₂⟩ := h₂ L hodd ((le_max_left _ _).trans hL₂) T hTa hTL hD hcs hOn
    (hrt₂.trans (min_le_left _ _)) ((le_max_left _ _).trans hC₂) K
  obtain ⟨y₃, hy₃⟩ := h₃ L hodd ((le_max_right _ _).trans hL₂) T hTa hTL hD hcs hOn
    (hrt₂.trans (min_le_right _ _)) ((le_max_right _ _).trans hC₂) K
  refine ⟨max (max y₁ y₂) (max y₃ T.floorMin), fun y hy hRs => ?_⟩
  have hA := (le_max_left _ _).trans hy
  have hB := (le_max_right _ _).trans hy
  exact H T K y (hD.fits y ((le_max_right _ _).trans hB)) (hy₁ y ((le_max_left _ _).trans hA) hRs)
    (hy₂ y ((le_max_right _ _).trans hA) hRs) (hy₃ y ((le_max_left _ _).trans hB) hRs)
open TorusFields TorusLumps FreeEnergies TorusMetric ProbabilityTheory

theorem separatedTestWeightNorm {ℓ : StepParameters} {P k m : ℕ} {n vt : ℝ} (hfit : ℓ.Admissible)
    {f : Fin P → PeriodicLattice.FourTorus ℓ.side m → ℝ} (hf : IsSeparatedTestTuple ℓ m n vt f)
    (hvn : 2 ≤ vt * n) (i : Fin P) :
    weightNorm ℓ.side k (testWeight ℓ.side k m (f i)) ≤ 1 :=
  weightNorm_testWeight_le_one ℓ.side k m hfit.L_odd.pos (f i) n vt hvn
    (hf.uniformNorm_eq _) (hf.lipschitz _) (hf.lipConst_le _)

/-- A Wilson covariance comparison uniform over separated pairs at a stopped RG level. -/
def separatedPairCovarianceAt (Tb : RenormalizationStepParameters.ParameterAssignment)
    (Kr : ResponseParameters) (y : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {T : StageTower (Tb.stepParameters y)} (S : ScoredStageTower T)
    {β : ℝ} {k m : ℕ} {n vt : ℝ}, S.params = Kr → S.FollowsFlow β k →
    CouplingsAboveFloor (Tb.stepParameters y) β k → IsBlockTorusSide (Tb.stepParameters y) (2 * Tb.side ^ m) →
    (1 : ℝ) ≤ clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k) →
    2 ^ 12 * (Tb.side : ℝ) * (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k) : ℝ) ≤ n →
    2 ≤ vt * n → ∀ {f : Fin 2 → PeriodicLattice.FourTorus Tb.side m → ℝ},
    IsSeparatedTestTuple (Tb.stepParameters y) m n vt f →
    let N := 2 * Tb.side ^ m
    let g (i : Fin 2) (x : Fin 4 → ℝ) := f i (torusProj (PeriodicLattice.torusSide Tb.side m) fun j => x j / (Tb.side : ℝ) ^ k)
    let μ := markedSampleLaw T β k N
    let F (i : Fin 2) u := fittedResponse S (g i) k N (stageState T k N u)
    let Q (i : Fin 2) u := scoreMeanOver S (g i) k N (stageState T k N u)
    Integrable (fun u => Q 0 u * Q 1 u) μ →
    |cov[curvatureObservable (testWeight Tb.side k m (f 0)), curvatureObservable (testWeight Tb.side k m (f 1));
        wilsonLaw β (fineSide Tb.side k N)]| ≤
        ((∫ u, F 0 u ^ 2 ∂μ) + ∫ u, F 1 u ^ 2 ∂μ) / 2 + C * Real.exp (-(c * n)) * ∫ u, Q 0 u * Q 1 u ∂μ

theorem separatedPairCovarianceAt_of_products (hC : LevelTestFunctions.CircleRepProperties) (hSi : levelSitesStatement)
    (hT1 : separatedMarkedMomentsStatement) (hTwo : TwoPointByTotalCovarianceStatement) (hcomp : completedObservablesBounded)
    (hM : TransfersOffTheWalk.separatedProductsStatement) (hFit : fittedResponseIsConditionalMeanStatement) :
    AtResponseParameters separatedPairCovarianceAt := by
  classical
  refine atResponseParameters_of_three hM hFit hM ?_
  intro Tb Kr y hfit hMa hFa _
  choose Cpf hCpf0 hCpf using hMa
  let d := (Tb.stepParameters y).rt / 2 ^ 9 / 2
  let A := separationErrorConstant (Tb.stepParameters y) Kr.C₀ (Cpf 2) 2
  refine ⟨|A| + 1, d, by positivity, by dsimp [d]; have := hfit.rt_pos; positivity, ?_⟩
  intro T S β k m n vt hk hS hR hB hr hn hvn f hf N g μ F Q hQ
  have ha := hS.isAdmissible k le_rfl
  have hp : (S.setup k).responseParams = Kr := (hS.params_eq k).trans hk
  have hKd : Kr.Admissible (Tb.stepParameters y) := hp ▸ ha.params_admissible
  have hK0 : 0 ≤ Kr.C₀ := by
    rw [hKd.C₀_eq]
    linarith only [hfit.a_ge, hKd.N₀_nonneg, hKd.Kc_ge]
  have hQB : 0 ≤ ∫ u, Q 0 u * Q 1 u ∂μ := integral_nonneg fun u =>
    mul_nonneg ((one_le_scoreMeanOver S k N (g 0) ha.price.nonneg _).trans' zero_le_one)
      ((one_le_scoreMeanOver S k N (g 1) ha.price.nonneg _).trans' zero_le_one)
  have hside : (1 : ℝ) ≤ Tb.side := by
    have := hfit.L_odd.pos
    exact_mod_cast (show 1 ≤ Tb.side from this)
  have hn1 : 1 ≤ n := by
    have h := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ 2 ^ 12 * Tb.side by linarith) (zero_le_one.trans hr)
    rw [one_mul] at h
    exact hr.trans (h.trans hn)
  have herror := separationError_of_tuple_le hC hSi hfit Kr.C₀ (Cpf 2) hK0 (hCpf0 2) (k:=k) hn1 hf (fun i => i)
  have he := herror.trans (mul_le_mul_of_nonneg_right (show A ≤ |A| + 1 by linarith [le_abs_self A])
    (Real.exp_pos _).le)
  have h := (wilsonCovariance_sub_fitted_at_separated_level hC hSi hT1 hTwo hcomp hfit Cpf
    (fun p T S β k n _ D f => hCpf p T S β k n D f) S hk hS hR hB hr hn hvn hf
    (fun i => (hFa β T S k hk hS hR (g i) k le_rfl N hB).2.1) hQ).2
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right he hQB))

theorem tupleCumulantApproxStatement_holds (hCum : CutoffLimits.TwoMeasures.CumulantComparison)
    (hSh : Cumulants.MomentCumulantRelations.Holds) (hC : LevelTestFunctions.CircleRepProperties)
    (hSi : levelSitesStatement) (hT1 : separatedMarkedMomentsStatement)
    (hMean : ResponseIsConditionalExpectation) (hTwo : TwoPointByTotalCovarianceStatement)
    (hBd : ResponsesBounded) (hSt : StageStatesMeasurableStatement)
    (hM : TransfersOffTheWalk.separatedProductsStatement) (hG : flowStatesAreGroundsStatement)
    (hN : meanScoreMomentsStatement) : tupleCumulantApproxStatement := by
  refine atResponseParameters_of_three hM hG hN ?_
  intro Tb Kr y hfit hMa hGa hNa
  choose Cpf hCpf0 hCpf' using hMa
  exact tupleCumulantApproxAt_of_bounds hCum hSh hC hSi hT1 hMean hTwo hBd hSt hfit Cpf hCpf0
    (fun p T S β s n _ D f => hCpf' p T S β s n D f) hGa hNa
end
end YangMills.Construction.ResponseInTheExpansion
end
