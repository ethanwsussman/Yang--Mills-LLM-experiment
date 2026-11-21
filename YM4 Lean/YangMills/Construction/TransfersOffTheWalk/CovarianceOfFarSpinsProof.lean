import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import YangMills.Construction.TransfersOffTheWalk.CovarianceOfFarSpins
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.Dobrushin
namespace CovarianceDecay
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
private theorem weightDensity_mul_of_nonneg (A : PairConstraint S) (G Y : (∀ i, S i) → ℝ) (hY : ∀ σ, 0 ≤ Y σ)
    (σ : ∀ i, S i) :
    A.weightDensity (fun σ => G σ * Y σ) σ = ENNReal.ofReal (Y σ) * A.weightDensity G σ := by
  classical
  unfold PairConstraint.weightDensity
  split_ifs with hadm
  · show ENNReal.ofReal (G σ * Y σ) = _
    rw [mul_comm (G σ), ENNReal.ofReal_mul (hY σ)]
  · simp
private theorem singleSiteLaw_mul_eq (A : PairConstraint S) (m : ∀ i, Measure (S i)) (G Y : (∀ i, S i) → ℝ)
    (hY : ∀ σ, 0 < Y σ) (i : I) (σ : ∀ i, S i) (hconst : ∀ s, Y (Function.update σ i s) = Y σ) :
    A.singleSiteLaw m (fun σ => G σ * Y σ) i σ = A.singleSiteLaw m G i σ := by
  classical
  set a := ENNReal.ofReal (Y σ) with ha
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr (hY σ)).ne'
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hd : ∀ s, A.weightDensity (fun σ => G σ * Y σ) (Function.update σ i s) =
      a * A.weightDensity G (Function.update σ i s) := by
    intro s
    rw [weightDensity_mul_of_nonneg A G Y (fun σ => (hY σ).le), hconst]
  have hmass : A.conditionalMass m (fun σ => G σ * Y σ) i σ = a * A.conditionalMass m G i σ := by
    unfold PairConstraint.conditionalMass
    simp only [hd]
    exact lintegral_const_mul' _ _ hat
  unfold PairConstraint.singleSiteLaw
  by_cases hc : 0 < A.conditionalMass m G i σ ∧ A.conditionalMass m G i σ ≠ ⊤
  · have hc' : 0 < A.conditionalMass m (fun σ => G σ * Y σ) i σ ∧
        A.conditionalMass m (fun σ => G σ * Y σ) i σ ≠ ⊤ := by
      rw [hmass]
      exact ⟨ENNReal.mul_pos ha0 hc.1.ne', ENNReal.mul_ne_top hat hc.2⟩
    rw [if_pos hc, if_pos hc', hmass]
    ext B hB
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [withDensity_apply _ hB, withDensity_apply _ hB]
    simp only [hd]
    rw [lintegral_const_mul' _ _ hat, ENNReal.mul_inv (Or.inl ha0) (Or.inl hat)]
    calc a⁻¹ * (A.conditionalMass m G i σ)⁻¹ * (a * ∫⁻ s in B, A.weightDensity G (Function.update σ i s) ∂m i)
        = (a⁻¹ * a) * ((A.conditionalMass m G i σ)⁻¹ *
            ∫⁻ s in B, A.weightDensity G (Function.update σ i s) ∂m i) := by ring
      _ = _ := by rw [ENNReal.inv_mul_cancel ha0 hat, one_mul]
  · have hc' : ¬ (0 < A.conditionalMass m (fun σ => G σ * Y σ) i σ ∧
        A.conditionalMass m (fun σ => G σ * Y σ) i σ ≠ ⊤) := by
      rw [hmass]
      rintro ⟨h1, h2⟩
      refine hc ⟨(ENNReal.mul_pos_iff.mp h1).2, fun ht => h2 ?_⟩
      rw [ht, ENNReal.mul_top ha0]
    rw [if_neg hc, if_neg hc']
private theorem measureReal_le_add_of_compl_singleton {X : Type} [MeasurableSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (a : X) (ha : MeasurableSet ({a} : Set X)) {e e' : ℝ}
    (hP : P.real {a}ᶜ ≤ e) (hQ : Q.real {a}ᶜ ≤ e') {B : Set X} (_hB : MeasurableSet B) :
    P.real B ≤ Q.real B + (e + e') := by
  have he : 0 ≤ e := measureReal_nonneg.trans hP
  have he' : 0 ≤ e' := measureReal_nonneg.trans hQ
  by_cases hm : a ∈ B
  · have h1 : Q.real {a} ≤ Q.real B := measureReal_mono (Set.singleton_subset_iff.mpr hm)
    have h2 : Q.real {a}ᶜ = 1 - Q.real {a} := probReal_compl_eq_one_sub ha
    have h3 : P.real B ≤ 1 := measureReal_le_one
    linarith
  · have h1 : P.real B ≤ P.real {a}ᶜ := measureReal_mono (fun x hx hxa => hm (by
      rw [Set.mem_singleton_iff.mp hxa] at hx
      exact hx))
    have h2 : 0 ≤ Q.real B := measureReal_nonneg
    linarith
private theorem integrable_of_abs_le {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by simpa using hB x)
end CovarianceDecay
open CovarianceDecay in
theorem covarianceDecay_of_comparison (hD : ComparisonStatement) (hC : ActivityConditionalLawsStatement) :
    CovarianceDecayStatement := by
  classical
  intro I _ _ S _ A m _ G z h c w M₁ M₂ F₁ F₂ B₁ B₂ hcol hw hm₁ hm₂ hb₁ hb₂ hr₁ hr₂
  have hB₁ : 0 ≤ B₁ := (abs_nonneg _).trans (hb₁ fun i => A.vacant i)
  have hB₂ : 0 ≤ B₂ := (abs_nonneg _).trans (hb₂ fun i => A.vacant i)
  rcases hB₂.eq_or_lt with h0 | hpos
  · have hz : ∀ σ, F₂ σ = 0 := fun σ => abs_nonpos_iff.mp (h0 ▸ hb₂ σ)
    simp [hz, ← h0]
  set Y : (∀ i, S i) → ℝ := fun σ => 2 * B₂ + F₂ σ with hYd
  have hYlo : ∀ σ, B₂ ≤ Y σ := fun σ => by
    have := (abs_le.mp (hb₂ σ)).1
    simp only [hYd]
    linarith
  have hYhi : ∀ σ, Y σ ≤ 3 * B₂ := fun σ => by
    have := (abs_le.mp (hb₂ σ)).2
    simp only [hYd]
    linarith
  have hYpos : ∀ σ, 0 < Y σ := fun σ => hpos.trans_le (hYlo σ)
  have hYm : Measurable Y := measurable_const.add hm₂
  set G' : (∀ i, S i) → ℝ := fun σ => G σ * Y σ with hG'
  have hdens : ∀ σ, A.weightDensity G' σ = ENNReal.ofReal (Y σ) * A.weightDensity G σ :=
    weightDensity_mul_of_nonneg A G Y fun σ => (hYpos σ).le
  have h' : A.IsActivityBounded m G' fun i => 3 * z i := by
    refine ⟨h.measurableSet_admissible, h.measurable.mul hYm, fun σ hσ => mul_pos (h.pos_of_admissible σ hσ) (hYpos σ),
      h.measurableSet_vacant, h.measure_vacant, fun i => mul_nonneg (by norm_num) (h.activity_nonneg i),
      fun i σ hσ => ?_⟩
    have hsm := h.lintegral_compl_vacant_le i σ hσ
    calc ∫⁻ s in {A.vacant i}ᶜ, A.weightDensity G' (Function.update σ i s) ∂m i
        ≤ ∫⁻ s in {A.vacant i}ᶜ, ENNReal.ofReal (3 * B₂) * A.weightDensity G (Function.update σ i s) ∂m i := by
          refine lintegral_mono fun s => ?_
          rw [hdens]
          gcongr
          exact hYhi _
      _ = ENNReal.ofReal (3 * B₂) * ∫⁻ s in {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (3 * B₂) * (ENNReal.ofReal (z i) * A.weightDensity G (Function.update σ i (A.vacant i))) := by
          gcongr
      _ ≤ ENNReal.ofReal (3 * z i) * (ENNReal.ofReal (Y (Function.update σ i (A.vacant i))) *
            A.weightDensity G (Function.update σ i (A.vacant i))) := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (h.activity_nonneg i))]
          gcongr ENNReal.ofReal ?_ * _
          have := hYlo (Function.update σ i (A.vacant i))
          have hz := h.activity_nonneg i
          nlinarith
      _ = _ := by rw [hdens]
  obtain ⟨hprob, hspec, hvac, -⟩ := hC I S A m G z h
  obtain ⟨hprob', hspec', hvac', -⟩ := hC I S A m G' (fun i => 3 * z i) h'
  set μ := A.gibbsLaw m G with hμ
  set μ' := A.gibbsLaw m G' with hμ'
  have hmk := hspec.isMarkovKernel
  have hmk' := hspec'.isMarkovKernel
  set b : I → ℝ := fun i => if i ∈ M₂ then 8 * z i else 0 with hb
  have hb0 : ∀ i, 0 ≤ b i := fun i => by
    simp only [hb]
    split_ifs
    · exact mul_nonneg (by norm_num) (h.activity_nonneg i)
    · exact le_rfl
  have hsite : ∀ i σ, A.IsAdmissible σ → ∀ B, MeasurableSet B →
      (A.singleSiteKernel m h.measurable_weightDensity i σ).real B ≤
        (A.singleSiteKernel m h'.measurable_weightDensity i σ).real B + b i / 2 := by
    intro i σ hσ B hB
    by_cases hi : i ∈ M₂
    · have := measureReal_le_add_of_compl_singleton (A.singleSiteKernel m h.measurable_weightDensity i σ)
        (A.singleSiteKernel m h'.measurable_weightDensity i σ) (A.vacant i) (h.measurableSet_vacant i)
        (hvac i σ hσ) (hvac' i σ hσ) hB
      simp only [hb, if_pos hi]
      linarith
    · have hconst : ∀ s, Y (Function.update σ i s) = Y σ := by
        intro s
        simp only [hYd]
        rw [hr₂ (Function.update σ i s) σ fun j hj => by
          rw [Function.update_of_ne (fun e : j = i => hi (e ▸ hj))]]
      have e : A.singleSiteKernel m h'.measurable_weightDensity i σ =
          A.singleSiteKernel m h.measurable_weightDensity i σ :=
        singleSiteLaw_mul_eq A m G Y hYpos i σ hconst
      simp only [hb, if_neg hi, e]
      simp
  obtain ⟨a, ha0, hsum, hcmp⟩ := hD I S A μ μ' _ _ c b w h.measurableSet_admissible hspec hspec'
    hcol.coeff_nonneg hb0 hcol.weight_pos hcol.kernel_le hsite hcol.column_sum_le
  set o : I → ℝ := fun i => if i ∈ M₁ then 2 * B₁ else 0 with ho
  have hosc : A.OscillationBound F₁ o := by
    refine ⟨fun i => ?_, fun i σ σ' _ _ hne => ?_⟩
    · simp only [ho]
      split_ifs
      · positivity
      · exact le_rfl
    · simp only [ho]
      split_ifs with hi
      · have h1 := abs_le.mp (hb₁ σ)
        have h2 := abs_le.mp (hb₁ σ')
        exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
      · rw [hr₁ σ σ' fun j hj => hne j fun e : j = i => hi (e ▸ hj)]
        simp
  have hmove := hcmp F₁ o hm₁ ⟨B₁, hb₁⟩ hosc
  have hw0 : ∀ i, 0 < w i := hcol.weight_pos
  have hwb : ∑ i, w i * b i = 8 * ∑ i ∈ M₂, w i * z i := by
    simp only [hb, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsumw : ∑ i, a i * o i ≤ 32 * B₁ * ∑ i ∈ M₂, w i * z i := by
    have h1 : ∑ i, a i * o i ≤ 2 * B₁ * ∑ i, w i * a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [ho]
      split_ifs with hi
      · have h2 := hw i hi
        have h3 := ha0 i
        nlinarith [mul_nonneg hB₁ h3, mul_nonneg (mul_nonneg hB₁ h3) (sub_nonneg.mpr h2)]
      · have := mul_nonneg (hw0 i).le (ha0 i)
        simp only [mul_zero]
        positivity
    have h2 : 2 * B₁ * ∑ i, w i * a i ≤ 2 * B₁ * (2 * ∑ i, w i * b i) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    rw [hwb] at h2
    linarith
  set Q := (Measure.pi m).withDensity (A.weightDensity G) with hQ
  set k : ℝ := ((∫⁻ σ, A.weightDensity G σ ∂Measure.pi m)⁻¹).toReal with hk
  set k' : ℝ := ((∫⁻ σ, A.weightDensity G' σ ∂Measure.pi m)⁻¹).toReal with hk'
  have hYf : Measurable fun σ => ENNReal.ofReal (Y σ) := ENNReal.measurable_ofReal.comp hYm
  have hWD : (Measure.pi m).withDensity (A.weightDensity G') = Q.withDensity fun σ => ENNReal.ofReal (Y σ) := by
    have e : A.weightDensity G' = A.weightDensity G * fun σ => ENNReal.ofReal (Y σ) := by
      funext σ
      rw [hdens, mul_comm]
      rfl
    rw [e, withDensity_mul _ h.measurable_weightDensity hYf]
  have hint : ∀ f : (∀ i, S i) → ℝ, ∫ σ, f σ ∂μ = k * ∫ σ, f σ ∂Q := by
    intro f
    simp only [hμ, PairConstraint.gibbsLaw]
    rw [integral_smul_measure]
    rfl
  have hint' : ∀ f : (∀ i, S i) → ℝ, ∫ σ, f σ ∂μ' = k' * ∫ σ, Y σ * f σ ∂Q := by
    intro f
    simp only [hμ', PairConstraint.gibbsLaw]
    rw [integral_smul_measure, hWD, integral_withDensity_eq_integral_toReal_smul hYf
      (Filter.Eventually.of_forall fun σ => ENNReal.ofReal_lt_top)]
    simp only [smul_eq_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    simp only [ENNReal.toReal_ofReal (hYpos σ).le]
  have hnorm : k' * ∫ σ, Y σ ∂Q = 1 := by
    have h1 := hint' fun _ => 1
    simp only [mul_one] at h1
    rw [← h1]
    simp
  have htilt : (∫ σ, F₁ σ ∂μ') * ∫ σ, Y σ ∂μ = ∫ σ, Y σ * F₁ σ ∂μ := by
    rw [hint' F₁, hint Y, hint fun σ => Y σ * F₁ σ]
    calc k' * (∫ σ, Y σ * F₁ σ ∂Q) * (k * ∫ σ, Y σ ∂Q)
        = (k' * ∫ σ, Y σ ∂Q) * (k * ∫ σ, Y σ * F₁ σ ∂Q) := by ring
      _ = _ := by rw [hnorm, one_mul]
  have hi₁ : Integrable F₁ μ := integrable_of_abs_le μ hm₁ hb₁
  have hi₂ : Integrable F₂ μ := integrable_of_abs_le μ hm₂ hb₂
  have hi₁₂ : Integrable (fun σ => F₁ σ * F₂ σ) μ :=
    integrable_of_abs_le μ (hm₁.mul hm₂) (B := B₁ * B₂) fun σ => by
      rw [abs_mul]
      exact mul_le_mul (hb₁ σ) (hb₂ σ) (abs_nonneg _) hB₁
  have hY1 : ∫ σ, Y σ ∂μ = 2 * B₂ + ∫ σ, F₂ σ ∂μ := by
    simp only [hYd]
    rw [integral_add (integrable_const _) hi₂]
    simp
  have hYF : ∫ σ, Y σ * F₁ σ ∂μ = 2 * B₂ * (∫ σ, F₁ σ ∂μ) + ∫ σ, F₁ σ * F₂ σ ∂μ := by
    have e : (fun σ => Y σ * F₁ σ) = fun σ => 2 * B₂ * F₁ σ + F₁ σ * F₂ σ := by
      funext σ
      simp only [hYd]
      ring
    rw [e, integral_add (hi₁.const_mul _) hi₁₂, integral_const_mul]
  have hcov : ∫ σ, F₁ σ * F₂ σ ∂μ - (∫ σ, F₁ σ ∂μ) * ∫ σ, F₂ σ ∂μ =
      ((∫ σ, F₁ σ ∂μ') - ∫ σ, F₁ σ ∂μ) * ∫ σ, Y σ ∂μ := by
    rw [sub_mul, htilt, hYF, hY1]
    ring
  have hYb : |∫ σ, Y σ ∂μ| ≤ 3 * B₂ := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := Y) (C := 3 * B₂)
      (Filter.Eventually.of_forall fun σ => by
        rw [Real.norm_eq_abs, abs_of_pos (hYpos σ)]
        exact hYhi σ)
    simpa using this
  rw [hcov, abs_mul]
  have hS0 : 0 ≤ 32 * B₁ * ∑ i ∈ M₂, w i * z i :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i).le (h.activity_nonneg i))
  calc |(∫ σ, F₁ σ ∂μ') - ∫ σ, F₁ σ ∂μ| * |∫ σ, Y σ ∂μ|
      ≤ (32 * B₁ * ∑ i ∈ M₂, w i * z i) * (3 * B₂) := by
        refine mul_le_mul ?_ hYb (abs_nonneg _) hS0
        rw [abs_sub_comm]
        exact hmove.trans hsumw
    _ = _ := by ring
end YangMills.Construction.Dobrushin
end
