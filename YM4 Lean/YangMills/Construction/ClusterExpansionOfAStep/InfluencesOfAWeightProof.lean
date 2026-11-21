import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeightProofForm
import YangMills.Construction.ClusterExpansionOfAStep.InfluencesOfAWeight
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.Dobrushin
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
  {A : PairConstraint S} {m : ∀ i, Measure (S i)} {G : (∀ i, S i) → ℝ} {z : I → ℝ}
theorem exp_le_one_add_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Real.exp t ≤ 1 + 2 * t := by
  have := Real.abs_exp_sub_one_sub_id_le (x := t) (by rw [abs_of_nonneg ht0]; exact ht1)
  have h2 := (abs_le.mp this).2
  nlinarith
theorem div_one_add_le_div_one_add_add {x x' r r' t a : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx0 : 0 ≤ x')
    (hr0 : 0 ≤ r) (hxr : x' ≤ r') (hra : r' ≤ a) (ha : a ≤ 1 / 2) (hx : x ≤ Real.exp t * x')
    (hr : r' ≤ Real.exp t * r) : x / (1 + r) ≤ x' / (1 + r') + 4 * a * t := by
  have he := exp_le_one_add_two_mul ht0 ht1
  have hr'0 : 0 ≤ r' := hx0.trans hxr
  have hx1 : x ≤ (1 + 2 * t) * x' := hx.trans (by gcongr)
  have hem : 1 - t ≤ Real.exp (-t) := by
    have := Real.add_one_le_exp (-t)
    linarith
  have hr1 : (1 - t) * r' ≤ r := by
    have h1 : Real.exp (-t) * r' ≤ r := by
      have := mul_le_mul_of_nonneg_left hr (Real.exp_pos (-t)).le
      rwa [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at this
    exact (mul_le_mul_of_nonneg_right hem hr'0).trans h1
  have hd : 0 < 1 + (1 - t) * r' := by nlinarith
  have hd' : 0 < 1 + r' := by linarith
  have step1 : x / (1 + r) ≤ (1 + 2 * t) * x' / (1 + (1 - t) * r') := by
    have hp : 0 ≤ (1 + 2 * t) * x' := by positivity
    calc x / (1 + r) ≤ (1 + 2 * t) * x' / (1 + r) := by gcongr
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left hp hd
        linarith
  refine step1.trans ?_
  rw [div_add' _ _ _ hd'.ne', div_le_div_iff₀ hd hd']
  have hx'a : x' ≤ a := hxr.trans hra
  have ha0 : 0 ≤ a := hx0.trans hx'a
  have h1 : x' * (t * (2 + 3 * r')) ≤ 4 * a * t * ((1 + r') * (1 + (1 - t) * r')) := by
    have h2 : x' * (t * (2 + 3 * r')) ≤ a * (t * 4) := by
      have : t * (2 + 3 * r') ≤ t * 4 := by
        apply mul_le_mul_of_nonneg_left _ ht0
        linarith
      exact mul_le_mul hx'a this (by positivity) ha0
    have h3 : 1 ≤ (1 + r') * (1 + (1 - t) * r') := by
      have : 0 ≤ (1 - t) * r' := mul_nonneg (by linarith) hr'0
      nlinarith
    have h4 : 0 ≤ 4 * a * t := by positivity
    nlinarith
  nlinarith
namespace ActivityInfluence
theorem isAdmissible_update_vacant_of_update {σ : ∀ i, S i} {i : I} {s : S i}
    (hσ : A.IsAdmissible (Function.update σ i s)) :
    A.IsAdmissible (Function.update σ i (A.vacant i)) := by apply _root_.YangMills.Construction.Dobrushin.isAdmissible_update_vacant_of_isAdmissible_update <;> assumption
theorem isAdmissible_update_vacant {σ : ∀ i, S i} {i : I} (hσ : A.IsAdmissible σ) :
    A.IsAdmissible (Function.update σ i (A.vacant i)) :=
  isAdmissible_update_vacant_of_update (s := σ i) (by simpa using hσ)
theorem weightDensity_of_admissible {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) :
    A.weightDensity G σ = ENNReal.ofReal (G σ) := by
  classical
  simp only [PairConstraint.weightDensity, if_pos hσ]
theorem weightDensity_of_not_admissible {σ : ∀ i, S i} (hσ : ¬ A.IsAdmissible σ) :
    A.weightDensity G σ = 0 := by apply _root_.YangMills.Construction.Dobrushin.weightDensity_eq_zero <;> assumption
theorem weightDensity_pos (h : A.IsActivityBounded m G z) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) :
    0 < A.weightDensity G σ := by apply _root_.YangMills.Construction.Dobrushin.weightDensity_pos <;> assumption
theorem weightDensity_ne_top (σ : ∀ i, S i) : A.weightDensity G σ ≠ ⊤ := by apply _root_.YangMills.Construction.Dobrushin.weightDensity_ne_top <;> assumption
theorem measurable_weightDensity_update (h : A.IsActivityBounded m G z) (i : I) (σ : ∀ i, S i) :
    Measurable fun s => A.weightDensity G (Function.update σ i s) :=
  h.measurable_weightDensity.comp (measurable_update σ)
theorem conditionalMass_eq_vacant_add (h : A.IsActivityBounded m G z) (i : I) (σ : ∀ i, S i) :
    A.conditionalMass m G i σ = A.weightDensity G (Function.update σ i (A.vacant i)) +
      ∫⁻ s in {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i := by apply _root_.YangMills.Construction.Dobrushin.conditionalMass_eq_add <;> assumption
def occupiedMass (A : PairConstraint S) (m : ∀ i, Measure (S i)) (G : (∀ i, S i) → ℝ) (i : I)
    (σ : ∀ i, S i) (C : Set (S i)) : ℝ≥0∞ :=
  ∫⁻ s in C, A.weightDensity G (Function.update σ i s) ∂m i
theorem occupiedMass_mono (i : I) (σ : ∀ i, S i) {C C' : Set (S i)} (hC : C ⊆ C') :
    occupiedMass A m G i σ C ≤ occupiedMass A m G i σ C' :=
  lintegral_mono_set hC
theorem occupiedMass_ne_top (h : A.IsActivityBounded m G z) (i : I) {σ : ∀ i, S i}
    (hσ : A.IsAdmissible σ) : occupiedMass A m G i σ {A.vacant i}ᶜ ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (weightDensity_ne_top _))
    (h.lintegral_compl_vacant_le i σ hσ)
theorem singleSiteLaw_real_eq (h : A.IsActivityBounded m G z) (i : I) {σ : ∀ i, S i}
    (hσ : A.IsAdmissible σ) {B : Set (S i)} (hB : MeasurableSet B) (haB : A.vacant i ∉ B) :
    (A.singleSiteLaw m G i σ).real B =
      ((occupiedMass A m G i σ B).toReal / (A.weightDensity G (Function.update σ i (A.vacant i))).toReal) /
      (1 + (occupiedMass A m G i σ {A.vacant i}ᶜ).toReal /
        (A.weightDensity G (Function.update σ i (A.vacant i))).toReal) := by
  have hda := weightDensity_pos h (isAdmissible_update_vacant (i := i) hσ)
  have hne := occupiedMass_ne_top h i hσ
  have hmass : A.conditionalMass m G i σ = A.weightDensity G (Function.update σ i (A.vacant i)) +
      occupiedMass A m G i σ {A.vacant i}ᶜ := conditionalMass_eq_vacant_add h i σ
  have hpos : 0 < A.conditionalMass m G i σ := by
    rw [hmass]
    exact lt_of_lt_of_le hda le_self_add
  have htop : A.conditionalMass m G i σ ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.add_ne_top.mpr ⟨weightDensity_ne_top _, hne⟩
  have hv : A.singleSiteLaw m G i σ B = (A.conditionalMass m G i σ)⁻¹ * occupiedMass A m G i σ B := by
    unfold PairConstraint.singleSiteLaw
    rw [if_pos ⟨hpos, htop⟩]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [withDensity_apply _ hB]
    rfl
  have hg : 0 < (A.weightDensity G (Function.update σ i (A.vacant i))).toReal :=
    ENNReal.toReal_pos hda.ne' (weightDensity_ne_top _)
  rw [Measure.real, hv, ENNReal.toReal_mul, ENNReal.toReal_inv, hmass,
    ENNReal.toReal_add (weightDensity_ne_top _) hne]
  field_simp
theorem occupiedRatio_le_activity (h : A.IsActivityBounded m G z) (i : I) {σ : ∀ i, S i}
    (hσ : A.IsAdmissible σ) :
    (occupiedMass A m G i σ {A.vacant i}ᶜ).toReal /
      (A.weightDensity G (Function.update σ i (A.vacant i))).toReal ≤ z i := by
  have hda := weightDensity_pos h (isAdmissible_update_vacant (i := i) hσ)
  have hg : 0 < (A.weightDensity G (Function.update σ i (A.vacant i))).toReal :=
    ENNReal.toReal_pos hda.ne' (weightDensity_ne_top _)
  rw [div_le_iff₀ hg]
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (weightDensity_ne_top _))
    (h.lintegral_compl_vacant_le i σ hσ)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h.activity_nonneg i)] at this
theorem isAdmissible_update_of_allCompatible {i j : I} (hij : i ≠ j) (hfar : A.AllCompatible i j)
    {σ σ' : ∀ i, S i} {s : S i} (hσ' : A.IsAdmissible σ') (hd : ∀ k, k ≠ j → σ k = σ' k)
    (hs : A.IsAdmissible (Function.update σ i s)) : A.IsAdmissible (Function.update σ' i s) := by
  intro k l hkl
  by_cases hk : k = i
  · subst hk
    simp only [Function.update_self, Function.update_of_ne hkl.symm]
    by_cases hl : l = j
    · subst hl
      exact hfar _ _
    · have := hs k l hkl
      simp only [Function.update_self, Function.update_of_ne hkl.symm] at this
      rwa [hd l hl] at this
  · by_cases hl : l = i
    · subst hl
      simp only [Function.update_self, Function.update_of_ne hk]
      by_cases hkj : k = j
      · subst hkj
        exact A.compatible_symm _ _ _ _ (hfar _ _)
      · have := hs k l hkl
        simp only [Function.update_self, Function.update_of_ne hk] at this
        rwa [hd k hkj] at this
    · simp only [Function.update_of_ne hk, Function.update_of_ne hl]
      exact hσ' k l hkl
theorem occupiedMass_mul_le (h : A.IsActivityBounded m G z) {i j : I} (hij : i ≠ j)
    (hfar : A.AllCompatible i j) {t : ℝ} (hr : A.DoubleRatioBound G i j t) {σ σ' : ∀ i, S i}
    (hσ : A.IsAdmissible σ) (hσ' : A.IsAdmissible σ') (hd : ∀ k, k ≠ j → σ k = σ' k) (C : Set (S i)) :
    occupiedMass A m G i σ C * A.weightDensity G (Function.update σ' i (A.vacant i)) ≤
      ENNReal.ofReal (Real.exp t) *
        (occupiedMass A m G i σ' C * A.weightDensity G (Function.update σ i (A.vacant i))) := by
  have hm := measurable_weightDensity_update h i σ
  have hm' := measurable_weightDensity_update h i σ'
  unfold occupiedMass
  rw [← lintegral_mul_const _ hm, ← lintegral_mul_const _ hm', ← lintegral_const_mul _ (hm'.mul_const _)]
  refine lintegral_mono fun s => ?_
  by_cases hs : A.IsAdmissible (Function.update σ i s)
  · have hs' := isAdmissible_update_of_allCompatible hij hfar hσ' hd hs
    have ha := isAdmissible_update_vacant (i := i) hσ
    have ha' := isAdmissible_update_vacant (i := i) hσ'
    rw [weightDensity_of_admissible hs, weightDensity_of_admissible hs', weightDensity_of_admissible ha,
      weightDensity_of_admissible ha']
    have hp := h.pos_of_admissible _ hs
    have hp' := h.pos_of_admissible _ hs'
    rw [← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_mul hp'.le,
      ← ENNReal.ofReal_mul (Real.exp_pos t).le]
    exact ENNReal.ofReal_le_ofReal (hr σ σ' s hs hs' hd)
  · rw [weightDensity_of_not_admissible hs, zero_mul]
    exact bot_le
theorem occupiedRatio_le_exp_mul (h : A.IsActivityBounded m G z) {i j : I} (hij : i ≠ j)
    (hfar : A.AllCompatible i j) {t : ℝ} (hr : A.DoubleRatioBound G i j t) {σ σ' : ∀ i, S i}
    (hσ : A.IsAdmissible σ) (hσ' : A.IsAdmissible σ') (hd : ∀ k, k ≠ j → σ k = σ' k) {C : Set (S i)}
    (hC : occupiedMass A m G i σ C ≠ ⊤) (hC' : occupiedMass A m G i σ' C ≠ ⊤) :
    (occupiedMass A m G i σ C).toReal / (A.weightDensity G (Function.update σ i (A.vacant i))).toReal ≤
      Real.exp t * ((occupiedMass A m G i σ' C).toReal /
        (A.weightDensity G (Function.update σ' i (A.vacant i))).toReal) := by
  have hda := weightDensity_pos h (isAdmissible_update_vacant (i := i) hσ)
  have hda' := weightDensity_pos h (isAdmissible_update_vacant (i := i) hσ')
  have hg : 0 < (A.weightDensity G (Function.update σ i (A.vacant i))).toReal :=
    ENNReal.toReal_pos hda.ne' (weightDensity_ne_top _)
  have hg' : 0 < (A.weightDensity G (Function.update σ' i (A.vacant i))).toReal :=
    ENNReal.toReal_pos hda'.ne' (weightDensity_ne_top _)
  have hb := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hC' (weightDensity_ne_top _)))
    (occupiedMass_mul_le h hij hfar hr hσ hσ' hd C)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos t).le] at hb
  generalize (A.weightDensity G (Function.update σ i (A.vacant i))).toReal = g at hg hb ⊢
  generalize (A.weightDensity G (Function.update σ' i (A.vacant i))).toReal = g' at hg' hb ⊢
  generalize (occupiedMass A m G i σ C).toReal = a at hb ⊢
  generalize (occupiedMass A m G i σ' C).toReal = a' at hb ⊢
  calc a / g = (a * g') / (g * g') := by field_simp
    _ ≤ (Real.exp t * (a' * g)) / (g * g') := by gcongr
    _ = Real.exp t * (a' / g') := by field_simp
theorem singleSiteLaw_real_le_add (h : A.IsActivityBounded m G z) (hz : ∀ i, z i ≤ 1 / 2) {i j : I}
    (hij : i ≠ j) (hfar : A.AllCompatible i j) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : A.DoubleRatioBound G i j t) {σ σ' : ∀ i, S i} (hσ : A.IsAdmissible σ)
    (hσ' : A.IsAdmissible σ') (hd : ∀ k, k ≠ j → σ k = σ' k) {B : Set (S i)}
    (hB : MeasurableSet B) (haB : A.vacant i ∉ B) :
    (A.singleSiteLaw m G i σ).real B ≤ (A.singleSiteLaw m G i σ').real B + 4 * z i * t := by
  have hd' : ∀ k, k ≠ j → σ' k = σ k := fun k hk => (hd k hk).symm
  have hsub : B ⊆ {A.vacant i}ᶜ := fun s hs hc => haB (Set.mem_singleton_iff.mp hc ▸ hs)
  have hne := occupiedMass_ne_top h i hσ
  have hne' := occupiedMass_ne_top h i hσ'
  have hBne := ne_top_of_le_ne_top hne (occupiedMass_mono i σ hsub)
  have hBne' := ne_top_of_le_ne_top hne' (occupiedMass_mono i σ' hsub)
  rw [singleSiteLaw_real_eq h i hσ hB haB, singleSiteLaw_real_eq h i hσ' hB haB]
  refine div_one_add_le_div_one_add_add ht0 ht1 (by positivity) (by positivity) ?_
    (occupiedRatio_le_activity h i hσ') (hz i)
    (occupiedRatio_le_exp_mul h hij hfar hr hσ hσ' hd hBne hBne')
    (occupiedRatio_le_exp_mul h hij hfar hr hσ' hσ hd' hne' hne)
  exact div_le_div_of_nonneg_right (ENNReal.toReal_mono hne' (occupiedMass_mono i σ' hsub))
    ENNReal.toReal_nonneg
end ActivityInfluence
open ActivityInfluence in
theorem activityInfluenceStatement_of_conditionalLaws (hc : ActivityConditionalLawsStatement) :
    ActivityInfluenceStatement := by
  intro I _ _ S _ A m _ G z h hz
  obtain ⟨hpr, hGb, hi, hlaw⟩ := hc I S A m G z h
  have hpm : ∀ i σ, IsProbabilityMeasure (A.singleSiteKernel m h.measurable_weightDensity i σ) :=
    fun i σ => (hGb.isMarkovKernel i).isProbabilityMeasure σ
  have hcompl : ∀ i σ (B : Set (S i)), MeasurableSet B →
      (A.singleSiteKernel m h.measurable_weightDensity i σ).real B =
        1 - (A.singleSiteKernel m h.measurable_weightDensity i σ).real Bᶜ := by
    intro i σ B hB
    have := hpm i σ
    rw [probReal_compl_eq_one_sub hB]
    ring
  have hnear : ∀ i σ σ', A.IsAdmissible σ → A.IsAdmissible σ' → ∀ B, MeasurableSet B →
      (A.singleSiteKernel m h.measurable_weightDensity i σ).real B ≤
        (A.singleSiteKernel m h.measurable_weightDensity i σ').real B + z i := by
    intro i σ σ' hσ hσ' B hB
    have h1 := hpm i σ
    have h2 := hpm i σ'
    by_cases ha : A.vacant i ∈ B
    · rw [hcompl i σ' B hB]
      have hsub : Bᶜ ⊆ {A.vacant i}ᶜ := fun s hs hc => hs (Set.mem_singleton_iff.mp hc ▸ ha)
      have h3 := measureReal_mono hsub
        (μ := A.singleSiteKernel m h.measurable_weightDensity i σ') (by finiteness)
      have h4 := hi i σ' hσ'
      have h5 : (A.singleSiteKernel m h.measurable_weightDensity i σ).real B ≤ 1 := measureReal_le_one
      linarith
    · have hsub : B ⊆ {A.vacant i}ᶜ := fun s hs hc => ha (Set.mem_singleton_iff.mp hc ▸ hs)
      have h3 := measureReal_mono hsub
        (μ := A.singleSiteKernel m h.measurable_weightDensity i σ) (by finiteness)
      have h4 := hi i σ hσ
      have h5 : 0 ≤ (A.singleSiteKernel m h.measurable_weightDensity i σ').real B := measureReal_nonneg
      linarith
  refine ⟨fun i j _ σ σ' hσ hσ' _ B hB => hnear i σ σ' hσ hσ' B hB, ?_, ?_⟩
  · intro i j t hij hfar ht0 hr σ σ' hσ hσ' hd B hB
    by_cases ht1 : 1 ≤ t
    · have := hnear i σ σ' hσ hσ' B hB
      rw [min_eq_left ht1]
      have := h.activity_nonneg i
      linarith
    · have ht1' : t ≤ 1 := (not_le.mp ht1).le
      rw [min_eq_right ht1']
      by_cases ha : A.vacant i ∈ B
      · have hd' : ∀ k, k ≠ j → σ' k = σ k := fun k hk => (hd k hk).symm
        have := singleSiteLaw_real_le_add h hz hij hfar ht0 ht1' hr hσ' hσ hd' hB.compl (fun hc => hc ha)
        have e1 := hcompl i σ B hB
        have e2 := hcompl i σ' B hB
        change (A.singleSiteLaw m G i σ').real Bᶜ ≤ (A.singleSiteLaw m G i σ).real Bᶜ + _ at this
        change (A.singleSiteLaw m G i σ).real B = 1 - (A.singleSiteLaw m G i σ).real Bᶜ at e1
        change (A.singleSiteLaw m G i σ').real B = 1 - (A.singleSiteLaw m G i σ').real Bᶜ at e2
        change (A.singleSiteLaw m G i σ).real B ≤ (A.singleSiteLaw m G i σ').real B + _
        linarith
      · exact singleSiteLaw_real_le_add h hz hij hfar ht0 ht1' hr hσ hσ' hd hB ha
  · intro M F hF hb h0
    have hE : MeasurableSet (⋃ i ∈ M, {σ : ∀ j, S j | σ i ≠ A.vacant i}) :=
      Finset.measurableSet_biUnion _ fun i _ => (measurable_pi_apply i (h.measurableSet_vacant i)).compl
    have hFi : Integrable F (A.gibbsLaw m G) :=
      Integrable.of_bound hF.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb)
    have hle : ∀ σ, |F σ| ≤
        Set.indicator (⋃ i ∈ M, {σ : ∀ j, S j | σ i ≠ A.vacant i}) (fun _ => (1 : ℝ)) σ := by
      intro σ
      by_cases hσ : σ ∈ ⋃ i ∈ M, {σ : ∀ j, S j | σ i ≠ A.vacant i}
      · rw [Set.indicator_of_mem hσ]
        exact hb σ
      · rw [Set.indicator_of_notMem hσ]
        have : F σ = 0 := h0 σ fun i hi' => by
          by_contra hc
          exact hσ (Set.mem_biUnion hi' hc)
        simp [this]
    calc |∫ σ, F σ ∂A.gibbsLaw m G| ≤ ∫ σ, |F σ| ∂A.gibbsLaw m G := abs_integral_le_integral_abs
      _ ≤ ∫ σ, Set.indicator (⋃ i ∈ M, {σ : ∀ j, S j | σ i ≠ A.vacant i}) (fun _ => (1 : ℝ)) σ
            ∂A.gibbsLaw m G :=
          integral_mono hFi.abs ((integrable_const _).indicator hE) hle
      _ = (A.gibbsLaw m G).real (⋃ i ∈ M, {σ : ∀ j, S j | σ i ≠ A.vacant i}) := by
          rw [integral_indicator hE]
          simp
      _ ≤ ∑ i ∈ M, (A.gibbsLaw m G).real {σ : ∀ j, S j | σ i ≠ A.vacant i} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ M, z i := Finset.sum_le_sum fun i _ => hlaw i
end YangMills.Construction.Dobrushin
end
