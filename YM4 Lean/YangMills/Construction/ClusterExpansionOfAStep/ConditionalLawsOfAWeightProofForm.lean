import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
namespace Dobrushin
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
  {A : PairConstraint S} {m : ∀ i, Measure (S i)} {G : (∀ i, S i) → ℝ} {z : I → ℝ}
theorem isAdmissible_update_vacant_of_isAdmissible_update {σ : ∀ i, S i} {i : I} {s : S i}
    (hσ : A.IsAdmissible (Function.update σ i s)) :
    A.IsAdmissible (Function.update σ i (A.vacant i)) := by
  intro k l hkl
  by_cases hk : k = i
  · subst hk
    simp only [Function.update_self, Function.update_of_ne hkl.symm]
    exact A.vacant_compatible _ _ _
  · by_cases hl : l = i
    · subst hl
      simp only [Function.update_self, Function.update_of_ne hk]
      exact A.compatible_symm _ _ _ _ (A.vacant_compatible _ _ _)
    · have := hσ k l hkl
      simpa only [Function.update_of_ne hk, Function.update_of_ne hl] using this
theorem weightDensity_pos (h : A.IsActivityBounded m G z) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) :
    0 < A.weightDensity G σ := by
  classical
  simp only [PairConstraint.weightDensity, if_pos hσ]
  exact ENNReal.ofReal_pos.mpr (h.pos_of_admissible σ hσ)
theorem weightDensity_ne_top (σ : ∀ i, S i) : A.weightDensity G σ ≠ ⊤ := by
  classical
  unfold PairConstraint.weightDensity
  split_ifs <;> simp
theorem weightDensity_eq_zero {σ : ∀ i, S i} (hσ : ¬ A.IsAdmissible σ) : A.weightDensity G σ = 0 := by
  classical
  simp only [PairConstraint.weightDensity, if_neg hσ]
theorem conditionalMass_update (i : I) (σ : ∀ i, S i) (s : S i) :
    A.conditionalMass m G i (Function.update σ i s) = A.conditionalMass m G i σ := by
  simp only [PairConstraint.conditionalMass, Function.update_idem]
theorem measurable_weightDensity_update (h : A.IsActivityBounded m G z) (i : I) (σ : ∀ i, S i) :
    Measurable fun s => A.weightDensity G (Function.update σ i s) :=
  h.measurable_weightDensity.comp (measurable_update σ)
theorem conditionalMass_eq_add (h : A.IsActivityBounded m G z) (i : I) (σ : ∀ i, S i) :
    A.conditionalMass m G i σ = A.weightDensity G (Function.update σ i (A.vacant i)) +
      ∫⁻ s in {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i := by
  unfold PairConstraint.conditionalMass
  rw [← lintegral_add_compl _ (h.measurableSet_vacant i)]
  congr 1
  rw [setLIntegral_congr_fun (g := fun _ => A.weightDensity G (Function.update σ i (A.vacant i)))
    (h.measurableSet_vacant i) (fun s hs => by rw [Set.mem_singleton_iff.mp hs]), setLIntegral_const,
    h.measure_vacant i, mul_one]
theorem conditionalMass_le (h : A.IsActivityBounded m G z) (i : I) (σ : ∀ i, S i) :
    A.conditionalMass m G i σ ≤
      (1 + ENNReal.ofReal (z i)) * A.weightDensity G (Function.update σ i (A.vacant i)) := by
  by_cases hσ : A.IsAdmissible (Function.update σ i (A.vacant i))
  · rw [← conditionalMass_update (m := m) (G := G) i σ (A.vacant i), conditionalMass_eq_add h,
      Function.update_idem, add_mul, one_mul]
    gcongr
    have := h.lintegral_compl_vacant_le i _ hσ
    simpa only [Function.update_idem] using this
  · have : A.conditionalMass m G i σ = 0 := by
      unfold PairConstraint.conditionalMass
      rw [lintegral_eq_zero_iff (measurable_weightDensity_update h i σ)]
      refine Filter.Eventually.of_forall fun s => ?_
      exact weightDensity_eq_zero fun hs => hσ (isAdmissible_update_vacant_of_isAdmissible_update hs)
    simp [this]
theorem conditionalMass_ne_top (h : A.IsActivityBounded m G z) (i : I) (σ : ∀ i, S i) :
    A.conditionalMass m G i σ ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (weightDensity_ne_top _)) (conditionalMass_le h i σ)
theorem conditionalMass_pos (h : A.IsActivityBounded m G z) (i : I) {σ : ∀ i, S i}
    (hσ : A.IsAdmissible σ) : 0 < A.conditionalMass m G i σ := by
  rw [conditionalMass_eq_add h]
  exact lt_of_lt_of_le
    (weightDensity_pos h (isAdmissible_update_vacant_of_isAdmissible_update (s := σ i) (by simpa using hσ)))
    le_self_add
theorem singleSiteLaw_of_pos (h : A.IsActivityBounded m G z) (i : I) {σ : ∀ i, S i}
    (hp : 0 < A.conditionalMass m G i σ) :
    A.singleSiteLaw m G i σ =
      (A.conditionalMass m G i σ)⁻¹ • (m i).withDensity fun s => A.weightDensity G (Function.update σ i s) := by
  unfold PairConstraint.singleSiteLaw
  rw [if_pos ⟨hp, conditionalMass_ne_top h i σ⟩]
theorem isProbabilityMeasure_singleSiteLaw (h : A.IsActivityBounded m G z) (i : I) (σ : ∀ i, S i) :
    IsProbabilityMeasure (A.singleSiteLaw m G i σ) := by
  by_cases hp : 0 < A.conditionalMass m G i σ
  · refine ⟨?_⟩
    rw [singleSiteLaw_of_pos h i hp]
    simp only [Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    exact ENNReal.inv_mul_cancel hp.ne' (conditionalMass_ne_top h i σ)
  · unfold PairConstraint.singleSiteLaw
    rw [if_neg fun c => hp c.1]
    infer_instance
theorem lintegral_singleSiteLaw (h : A.IsActivityBounded m G z) (i : I) {σ : ∀ i, S i}
    (hp : 0 < A.conditionalMass m G i σ) {f : S i → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ s, f s ∂A.singleSiteLaw m G i σ =
      (A.conditionalMass m G i σ)⁻¹ * ∫⁻ s, A.weightDensity G (Function.update σ i s) * f s ∂m i := by
  rw [singleSiteLaw_of_pos h i hp, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_weightDensity_update h i σ) hf]
  rfl
theorem singleSiteLaw_update (i : I) (σ : ∀ i, S i) (s : S i) :
    A.singleSiteLaw m G i (Function.update σ i s) = A.singleSiteLaw m G i σ := by
  unfold PairConstraint.singleSiteLaw
  simp only [conditionalMass_update, Function.update_idem]
variable [∀ i, SigmaFinite (m i)]
theorem lmarginal_weightDensity_le (h : A.IsActivityBounded m G z) (J : Finset I) (x : ∀ i, S i) :
    (∫⋯∫⁻_J, A.weightDensity G ∂m) x ≤
      (∏ i ∈ J, (1 + ENNReal.ofReal (z i))) *
        A.weightDensity G (fun i => if i ∈ J then A.vacant i else x i) := by
  induction J using Finset.induction_on generalizing x with
  | empty => simp [lmarginal_empty]
  | insert i J hi ih =>
    rw [lmarginal_insert _ h.measurable_weightDensity hi, Finset.prod_insert hi]
    set y : ∀ i, S i := fun k => if k ∈ J then A.vacant k else x k with hy
    have hup : ∀ s, (fun k => if k ∈ J then A.vacant k else Function.update x i s k) =
        Function.update y i s := by
      intro s
      funext k
      by_cases hk : k = i
      · subst hk
        simp [hy, hi]
      · simp [hy, hk]
    calc ∫⁻ s, (∫⋯∫⁻_J, A.weightDensity G ∂m) (Function.update x i s) ∂m i
        ≤ ∫⁻ s, (∏ k ∈ J, (1 + ENNReal.ofReal (z k))) * A.weightDensity G (Function.update y i s) ∂m i := by
          refine lintegral_mono fun s => ?_
          have := ih (Function.update x i s)
          rwa [hup] at this
      _ = (∏ k ∈ J, (1 + ENNReal.ofReal (z k))) * A.conditionalMass m G i y := by
          rw [lintegral_const_mul _ (measurable_weightDensity_update h i y)]
          rfl
      _ ≤ (∏ k ∈ J, (1 + ENNReal.ofReal (z k))) *
            ((1 + ENNReal.ofReal (z i)) * A.weightDensity G (Function.update y i (A.vacant i))) := by
          gcongr
          exact conditionalMass_le h i y
      _ = _ := by
          have : Function.update y i (A.vacant i) =
              fun k => if k ∈ insert i J then A.vacant k else x k := by
            funext k
            by_cases hk : k = i
            · subst hk
              simp
            · simp [hy, hk]
          rw [this]
          ring
theorem lintegral_weightDensity_ne_top (h : A.IsActivityBounded m G z) :
    ∫⁻ σ, A.weightDensity G σ ∂Measure.pi m ≠ ⊤ := by
  rw [lintegral_eq_lmarginal_univ A.vacant]
  refine ne_top_of_le_ne_top ?_ (lmarginal_weightDensity_le h Finset.univ A.vacant)
  refine ENNReal.mul_ne_top (ENNReal.prod_ne_top fun i _ => by simp) (weightDensity_ne_top _)
theorem isAdmissible_vacant : A.IsAdmissible A.vacant := fun i j _ => A.vacant_compatible i j _
theorem lintegral_weightDensity_pos (h : A.IsActivityBounded m G z) :
    0 < ∫⁻ σ, A.weightDensity G σ ∂Measure.pi m := by
  have hs : MeasurableSet (Set.univ.pi fun i => ({A.vacant i} : Set (S i))) :=
    MeasurableSet.univ_pi h.measurableSet_vacant
  have h1 : ∫⁻ σ in Set.univ.pi (fun i => ({A.vacant i} : Set (S i))), A.weightDensity G σ ∂Measure.pi m =
      A.weightDensity G A.vacant := by
    rw [setLIntegral_congr_fun (g := fun _ => A.weightDensity G A.vacant) hs (fun σ hσ => ?_),
      setLIntegral_const, Measure.pi_pi]
    · simp [h.measure_vacant]
    · congr 1
      funext i
      exact Set.mem_singleton_iff.mp (hσ i (Set.mem_univ i))
  refine lt_of_lt_of_le ?_
    (setLIntegral_le_lintegral (Set.univ.pi fun i => ({A.vacant i} : Set (S i))) _)
  rw [h1]
  exact weightDensity_pos h isAdmissible_vacant
theorem isProbabilityMeasure_gibbsLaw (h : A.IsActivityBounded m G z) :
    IsProbabilityMeasure (A.gibbsLaw m G) := by
  refine ⟨?_⟩
  simp only [PairConstraint.gibbsLaw, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (lintegral_weightDensity_pos h).ne' (lintegral_weightDensity_ne_top h)
theorem lintegral_gibbsLaw (h : A.IsActivityBounded m G z) {f : (∀ i, S i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ σ, f σ ∂A.gibbsLaw m G =
      (∫⁻ σ, A.weightDensity G σ ∂Measure.pi m)⁻¹ * ∫⁻ σ, A.weightDensity G σ * f σ ∂Measure.pi m := by
  rw [PairConstraint.gibbsLaw, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ h.measurable_weightDensity hf]
  rfl
instance isMarkovKernel_singleSiteKernel (h : A.IsActivityBounded m G z) (i : I) :
    IsMarkovKernel (A.singleSiteKernel m h.measurable_weightDensity i) :=
  ⟨fun σ => isProbabilityMeasure_singleSiteLaw h i σ⟩
theorem lintegral_gibbsLaw_eq_lintegral_singleSiteKernel (h : A.IsActivityBounded m G z) (i : I)
    {f : (∀ j, S j) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ σ, f σ ∂A.gibbsLaw m G =
      ∫⁻ σ, (∫⁻ s, f (Function.update σ i s) ∂A.singleSiteKernel m h.measurable_weightDensity i σ)
        ∂A.gibbsLaw m G := by
  have hmk := isMarkovKernel_singleSiteKernel h i
  set K := A.singleSiteKernel m h.measurable_weightDensity i with hK
  set Kf : (∀ j, S j) → ℝ≥0∞ := fun σ => ∫⁻ s, f (Function.update σ i s) ∂K σ with hKf
  have hKfm : Measurable Kf :=
    Measurable.lintegral_kernel_prod_right' (κ := K)
      (f := fun p : (∀ j, S j) × S i => f (Function.update p.1 i p.2)) (hf.comp measurable_update')
  rw [lintegral_gibbsLaw h hf, lintegral_gibbsLaw h hKfm]
  congr 1
  have hd := h.measurable_weightDensity
  rw [lintegral_eq_lmarginal_univ A.vacant, lintegral_eq_lmarginal_univ A.vacant]
  have hu : (Finset.univ : Finset I) = Finset.univ.erase i ∪ {i} := by
    ext k
    by_cases hk : k = i <;> simp [hk]
  have hdis : Disjoint (Finset.univ.erase i) ({i} : Finset I) := by simp
  have hm1 : Measurable fun σ => A.weightDensity G σ * f σ := hd.mul hf
  have hm2 : Measurable fun σ => A.weightDensity G σ * Kf σ := hd.mul hKfm
  rw [hu, lmarginal_union m _ hm1 hdis, lmarginal_union m _ hm2 hdis]
  congr 1
  funext σ
  rw [lmarginal_singleton, lmarginal_singleton]
  simp only [Pi.mul_apply]
  have hKfu : ∀ s, Kf (Function.update σ i s) = Kf σ := by
    intro s
    have hk : K (Function.update σ i s) = K σ := singleSiteLaw_update i σ s
    change ∫⁻ s', f (Function.update (Function.update σ i s) i s') ∂K (Function.update σ i s) =
      ∫⁻ s', f (Function.update σ i s') ∂K σ
    rw [hk]
    simp only [Function.update_idem]
  simp only [hKfu]
  rw [lintegral_mul_const _ (measurable_weightDensity_update h i σ)]
  change _ = A.conditionalMass m G i σ * Kf σ
  by_cases hp : 0 < A.conditionalMass m G i σ
  · have : Kf σ = (A.conditionalMass m G i σ)⁻¹ *
        ∫⁻ s, A.weightDensity G (Function.update σ i s) * f (Function.update σ i s) ∂m i := by
      exact lintegral_singleSiteLaw h i hp (f := fun s => f (Function.update σ i s))
        (hf.comp (measurable_update σ))
    rw [this, ← mul_assoc, ENNReal.mul_inv_cancel hp.ne' (conditionalMass_ne_top h i σ), one_mul]
  · have h0 : A.conditionalMass m G i σ = 0 := le_antisymm (not_lt.mp hp) bot_le
    rw [h0, zero_mul]
    have h1 : (fun s => A.weightDensity G (Function.update σ i s)) =ᵐ[m i] 0 :=
      (lintegral_eq_zero_iff (measurable_weightDensity_update h i σ)).mp h0
    have hm3 : Measurable fun s =>
        A.weightDensity G (Function.update σ i s) * f (Function.update σ i s) :=
      (measurable_weightDensity_update h i σ).mul (hf.comp (measurable_update σ))
    rw [lintegral_eq_zero_iff hm3]
    filter_upwards [h1] with s hs
    simp only [Pi.zero_apply] at hs ⊢
    simp [hs]
theorem integral_gibbsLaw_eq_integral_singleSiteKernel (h : A.IsActivityBounded m G z) (i : I)
    {F : (∀ j, S j) → ℝ} (hF : Measurable F) (hb : ∃ C, ∀ σ, |F σ| ≤ C) :
    ∫ σ, F σ ∂A.gibbsLaw m G =
      ∫ σ, (∫ s, F (Function.update σ i s) ∂A.singleSiteKernel m h.measurable_weightDensity i σ)
        ∂A.gibbsLaw m G := by
  have hmk := isMarkovKernel_singleSiteKernel h i
  have hpr := isProbabilityMeasure_gibbsLaw h
  set K := A.singleSiteKernel m h.measurable_weightDensity i with hK
  obtain ⟨C, hC⟩ := hb
  set g : (∀ j, S j) → ℝ := fun σ => F σ + C with hg
  have hgm : Measurable g := hF.add measurable_const
  have hg0 : ∀ σ, 0 ≤ g σ := fun σ => by
    have := abs_le.mp (hC σ)
    simp only [hg]
    linarith [this.1]
  have hgb : ∀ σ, |g σ| ≤ 2 * C := fun σ => by
    have := abs_le.mp (hC σ)
    rw [abs_of_nonneg (hg0 σ)]
    simp only [hg]
    linarith [this.2]
  have hFint : ∀ (ν : Measure (∀ j, S j)) [IsProbabilityMeasure ν], Integrable F ν := fun ν _ =>
    Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have hup : ∀ σ : ∀ j, S j, Measurable fun s : S i => Function.update σ i s :=
    fun σ => measurable_update σ
  have hin : ∀ σ, Integrable (fun s => g (Function.update σ i s)) (K σ) := fun σ =>
    Integrable.of_bound (hgm.comp (hup σ)).aestronglyMeasurable (2 * C)
      (Filter.Eventually.of_forall fun s => hgb _)
  have hinF : ∀ σ, Integrable (fun s => F (Function.update σ i s)) (K σ) := fun σ =>
    Integrable.of_bound (hF.comp (hup σ)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun s => hC _)
  have hHg : ∀ σ, ∫ s, g (Function.update σ i s) ∂K σ =
      ∫ s, F (Function.update σ i s) ∂K σ + C := by
    intro σ
    simp only [hg]
    rw [integral_add (hinF σ) (integrable_const _)]
    simp
  set Lg : (∀ j, S j) → ℝ≥0∞ := fun σ => ∫⁻ s, ENNReal.ofReal (g (Function.update σ i s)) ∂K σ with hLg
  have hLgm : Measurable Lg :=
    Measurable.lintegral_kernel_prod_right' (κ := K)
      (f := fun p : (∀ j, S j) × S i => ENNReal.ofReal (g (Function.update p.1 i p.2)))
      (ENNReal.measurable_ofReal.comp (hgm.comp measurable_update'))
  have hL : ∀ σ, ∫ s, g (Function.update σ i s) ∂K σ = (Lg σ).toReal := by
    intro σ
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun s => hg0 _)
      (hgm.comp (hup σ)).aestronglyMeasurable]
  have hLb : ∀ σ, (Lg σ).toReal ≤ 2 * C := by
    intro σ
    rw [← hL]
    calc ∫ s, g (Function.update σ i s) ∂K σ ≤ ∫ _, 2 * C ∂K σ :=
          integral_mono (hin σ) (integrable_const _) fun s => (le_abs_self _).trans (hgb _)
      _ = 2 * C := by simp
  have hLne : ∀ σ, Lg σ ≠ ⊤ := by
    intro σ
    have : Lg σ ≤ ∫⁻ _, ENNReal.ofReal (2 * C) ∂K σ :=
      lintegral_mono fun s => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hgb _))
    refine ne_top_of_le_ne_top ?_ this
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_ne_top
  have hkey := lintegral_gibbsLaw_eq_lintegral_singleSiteKernel h i (ENNReal.measurable_ofReal.comp hgm)
  have h1 : ∫ σ, g σ ∂A.gibbsLaw m G = ∫ σ, (Lg σ).toReal ∂A.gibbsLaw m G := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0) hgm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        hLgm.ennreal_toReal.aestronglyMeasurable]
    congr 1
    have : ∀ σ, ENNReal.ofReal (Lg σ).toReal = Lg σ := fun σ => ENNReal.ofReal_toReal (hLne σ)
    simp only [this]
    exact hkey
  have h2 : ∫ σ, g σ ∂A.gibbsLaw m G = ∫ σ, F σ ∂A.gibbsLaw m G + C := by
    simp only [hg]
    rw [integral_add (hFint _) (integrable_const _)]
    simp
  have h3 : ∀ σ, ∫ s, F (Function.update σ i s) ∂K σ = (Lg σ).toReal - C := fun σ => by
    rw [← hL, hHg]
    ring
  have hLint : Integrable (fun σ => (Lg σ).toReal) (A.gibbsLaw m G) :=
    Integrable.of_bound hLgm.ennreal_toReal.aestronglyMeasurable (2 * C)
      (Filter.Eventually.of_forall fun σ => by
        rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
        exact hLb σ)
  simp only [h3]
  rw [integral_sub hLint (integrable_const _)]
  have hc : ∫ _ : ∀ j, S j, C ∂A.gibbsLaw m G = C := by simp
  rw [hc]
  linarith
theorem singleSiteLaw_compl_vacant_le (h : A.IsActivityBounded m G z) (i : I) {σ : ∀ i, S i}
    (hσ : A.IsAdmissible σ) : A.singleSiteLaw m G i σ {A.vacant i}ᶜ ≤ ENNReal.ofReal (z i) := by
  have hp := conditionalMass_pos h i hσ
  rw [singleSiteLaw_of_pos h i hp]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [withDensity_apply _ (h.measurableSet_vacant i).compl]
  have hs := h.lintegral_compl_vacant_le i σ hσ
  have hd : A.weightDensity G (Function.update σ i (A.vacant i)) ≤ A.conditionalMass m G i σ := by
    rw [conditionalMass_eq_add h]
    exact le_self_add
  calc (A.conditionalMass m G i σ)⁻¹ *
        ∫⁻ s in {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i
      ≤ (A.conditionalMass m G i σ)⁻¹ * (ENNReal.ofReal (z i) * A.conditionalMass m G i σ) := by
        gcongr
        exact hs.trans (by gcongr)
    _ = ENNReal.ofReal (z i) := by
        rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel hp.ne' (conditionalMass_ne_top h i σ), mul_one]
theorem ae_isAdmissible_gibbsLaw (h : A.IsActivityBounded m G z) :
    ∀ᵐ σ ∂A.gibbsLaw m G, A.IsAdmissible σ := by
  rw [ae_iff]
  have hs : MeasurableSet {σ | ¬ A.IsAdmissible σ} := h.measurableSet_admissible.compl
  simp only [PairConstraint.gibbsLaw, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
  have : ∫⁻ σ in {σ | ¬ A.IsAdmissible σ}, A.weightDensity G σ ∂Measure.pi m = 0 := by
    rw [setLIntegral_congr_fun (g := fun _ => 0) hs (fun σ hσ => weightDensity_eq_zero hσ)]
    simp
  rw [this, mul_zero]
theorem activityConditionalLawsStatement_proof : ActivityConditionalLawsStatement := by
  intro I _ _ S _ A m _ G z h
  have hpr := isProbabilityMeasure_gibbsLaw h
  refine ⟨hpr, ⟨fun i => isMarkovKernel_singleSiteKernel h i, fun i σ s => ?_,
    fun i F hF hb => integral_gibbsLaw_eq_integral_singleSiteKernel h i hF hb, ?_,
    ae_isAdmissible_gibbsLaw h⟩, fun i σ hσ => ?_, fun i => ?_⟩
  · change A.singleSiteLaw m G i _ = A.singleSiteLaw m G i σ
    exact singleSiteLaw_update i σ s
  · intro i σ hσ
    have hp := conditionalMass_pos h i hσ
    have hs : MeasurableSet {s | ¬ A.IsAdmissible (Function.update σ i s)} :=
      (measurable_update σ h.measurableSet_admissible).compl
    rw [ae_iff]
    change A.singleSiteLaw m G i σ _ = 0
    rw [singleSiteLaw_of_pos h i hp]
    simp only [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
    have : ∫⁻ s in {s | ¬ A.IsAdmissible (Function.update σ i s)},
        A.weightDensity G (Function.update σ i s) ∂m i = 0 := by
      rw [setLIntegral_congr_fun (g := fun _ => 0) hs (fun s hs' => weightDensity_eq_zero hs')]
      simp
    rw [this, mul_zero]
  · have hpm := isProbabilityMeasure_singleSiteLaw h i σ
    have := singleSiteLaw_compl_vacant_le h i hσ
    change (A.singleSiteLaw m G i σ).real _ ≤ z i
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal (h.activity_nonneg i) this
  · have hE : MeasurableSet {σ : ∀ j, S j | σ i ≠ A.vacant i} :=
      (measurable_pi_apply i (h.measurableSet_vacant i)).compl
    have hind := lintegral_gibbsLaw_eq_lintegral_singleSiteKernel h i
      (f := Set.indicator {σ : ∀ j, S j | σ i ≠ A.vacant i} 1) (measurable_one.indicator hE)
    have hleft : ∫⁻ σ, Set.indicator {σ : ∀ j, S j | σ i ≠ A.vacant i} 1 σ ∂A.gibbsLaw m G =
        A.gibbsLaw m G {σ | σ i ≠ A.vacant i} := lintegral_indicator_one hE
    have hin : ∀ σ, ∫⁻ s, Set.indicator {σ : ∀ j, S j | σ i ≠ A.vacant i} 1 (Function.update σ i s)
        ∂A.singleSiteKernel m h.measurable_weightDensity i σ = A.singleSiteLaw m G i σ {A.vacant i}ᶜ := by
      intro σ
      have : (fun s => Set.indicator {σ : ∀ j, S j | σ i ≠ A.vacant i} (1 : (∀ j, S j) → ℝ≥0∞)
          (Function.update σ i s)) = Set.indicator ({A.vacant i}ᶜ : Set (S i)) 1 := by
        funext s
        by_cases hs : s = A.vacant i <;> simp [Set.indicator, hs]
      rw [this, lintegral_indicator_one (h.measurableSet_vacant i).compl]
      rfl
    simp only [hin] at hind
    rw [hleft] at hind
    have hle : A.gibbsLaw m G {σ | σ i ≠ A.vacant i} ≤ ENNReal.ofReal (z i) := by
      rw [hind]
      calc ∫⁻ σ, A.singleSiteLaw m G i σ {A.vacant i}ᶜ ∂A.gibbsLaw m G
          ≤ ∫⁻ _, ENNReal.ofReal (z i) ∂A.gibbsLaw m G :=
            lintegral_mono_ae ((ae_isAdmissible_gibbsLaw h).mono fun σ hσ =>
              singleSiteLaw_compl_vacant_le h i hσ)
        _ = ENNReal.ofReal (z i) := by simp
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal (h.activity_nonneg i) hle
end Dobrushin
end YangMills.Construction
end
