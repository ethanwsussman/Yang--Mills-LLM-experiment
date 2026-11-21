import YangMills.Construction.ClusterExpansionOfAStep.ComparisonOfHeldGases
import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
namespace Dobrushin
namespace VacantSpin
section Embedding
set_option linter.unusedSectionVars false
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {S : I → Type}
  [∀ i, MeasurableSpace (S i)] {T : J → Type} [∀ j, MeasurableSpace (T j)]
  (A : PairConstraint S) {e : J → I}
theorem embedConfig_apply (v : ∀ j, T j → S (e j)) (he : Function.Injective e) (τ : ∀ j, T j) (j : J) :
    A.embedConfig e v τ (e j) = v j (τ j) := by
  have key : ∀ (j' : J) (hj : e j' = e j), (hj ▸ v j' (τ j') : S (e j)) = v j (τ j) := by
    intro j' hj
    obtain rfl := he hj
    rfl
  unfold PairConstraint.embedConfig
  rw [dif_pos ⟨j, rfl⟩]
  exact key _ _
theorem embedConfig_of_not_mem_range (v : ∀ j, T j → S (e j)) (τ : ∀ j, T j) {i : I} (h : ∀ j, e j ≠ i) :
    A.embedConfig e v τ i = A.vacant i := by
  unfold PairConstraint.embedConfig
  rw [dif_neg]
  rintro ⟨j, hj⟩
  exact h j hj
theorem measurable_embedConfig (v : ∀ j, T j → S (e j)) (he : Function.Injective e)
    (hv : ∀ j, Measurable (v j)) : Measurable (A.embedConfig e v) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := h
    have : (fun τ : ∀ j, T j => A.embedConfig e v τ (e j)) = fun τ => v j (τ j) := by
      funext τ
      exact embedConfig_apply A v he τ j
    rw [this]
    exact (hv j).comp (measurable_pi_apply j)
  · have h' : ∀ j, e j ≠ i := fun j hj => h ⟨j, hj⟩
    have : (fun τ : ∀ j, T j => A.embedConfig e v τ i) = fun _ => A.vacant i := by
      funext τ
      exact embedConfig_of_not_mem_range A v τ h'
    rw [this]
    exact measurable_const
theorem embedConfig_update (v : ∀ j, T j → S (e j)) (he : Function.Injective e) (τ : ∀ j, T j) (j : J)
    (s : T j) :
    A.embedConfig e v (Function.update τ j s) = Function.update (A.embedConfig e v τ) (e j) (v j s) := by
  funext i
  by_cases h : ∃ j', e j' = i
  · obtain ⟨j', rfl⟩ := h
    rw [embedConfig_apply A v he]
    by_cases hj : j' = j
    · subst hj
      simp
    · rw [Function.update_of_ne hj, Function.update_of_ne (he.ne hj), embedConfig_apply A v he]
  · have h' : ∀ j', e j' ≠ i := fun j' hj => h ⟨j', hj⟩
    rw [embedConfig_of_not_mem_range A v _ h', Function.update_of_ne (fun hh => h' j hh.symm),
      embedConfig_of_not_mem_range A v _ h']
theorem isAdmissible_embedConfig_iff (A' : PairConstraint T) (v : ∀ j, T j → S (e j))
    (he : Function.Injective e)
    (hok : ∀ j j' s t, j ≠ j' → (A'.compatible j j' s t ↔ A.compatible (e j) (e j') (v j s) (v j' t)))
    (τ : ∀ j, T j) :
    A.IsAdmissible (A.embedConfig e v τ) ↔ A'.IsAdmissible τ := by
  constructor
  · intro h j j' hj
    have := h (e j) (e j') (he.ne hj)
    rw [embedConfig_apply A v he, embedConfig_apply A v he] at this
    exact (hok j j' _ _ hj).mpr this
  · intro h i i' hi
    by_cases h1 : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := h1
      by_cases h2 : ∃ j', e j' = i'
      · obtain ⟨j', rfl⟩ := h2
        have hj : j ≠ j' := fun hh => hi (by rw [hh])
        rw [embedConfig_apply A v he, embedConfig_apply A v he]
        exact (hok j j' _ _ hj).mp (h j j' hj)
      · rw [embedConfig_of_not_mem_range A v τ (fun j' hj => h2 ⟨j', hj⟩)]
        exact A.compatible_symm _ _ _ _ (A.vacant_compatible _ _ _)
    · rw [embedConfig_of_not_mem_range A v τ (fun j hj => h1 ⟨j, hj⟩)]
      exact A.vacant_compatible _ _ _
theorem map_embedConfig_pi {m m' : ∀ i, Measure (S i)} [∀ i, SigmaFinite (m' i)]
    {μ : ∀ j, Measure (T j)} [∀ j, SigmaFinite (μ j)] (v : ∀ j, T j ≃ᵐ S (e j))
    (he : Function.Injective e) (hH : A.IsVacantOffRange m m' e)
    (hmp : ∀ j, MeasurePreserving (v j) (μ j) (m (e j))) :
    Measure.map (A.embedConfig e fun j => v j) (Measure.pi μ) = Measure.pi m' := by
  classical
  have hmeas := measurable_embedConfig A (fun j => v j) he fun j => (v j).measurable
  symm
  refine Measure.pi_eq fun B hB => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hB)]
  by_cases hoff : ∀ i, (∀ j, e j ≠ i) → A.vacant i ∈ B i
  · have hpre : (A.embedConfig e fun j => v j) ⁻¹' Set.univ.pi B =
        Set.univ.pi fun j => (v j) ⁻¹' B (e j) := by
      ext τ
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro h j
        have := h (e j)
        rwa [embedConfig_apply A _ he] at this
      · intro h i
        by_cases h1 : ∃ j, e j = i
        · obtain ⟨j, rfl⟩ := h1
          rw [embedConfig_apply A _ he]
          exact h j
        · have h' : ∀ j, e j ≠ i := fun j hj => h1 ⟨j, hj⟩
          rw [embedConfig_of_not_mem_range A _ τ h']
          exact hoff i h'
    rw [hpre, Measure.pi_pi]
    refine Fintype.prod_of_injective e he _ _ ?_ ?_
    · intro i hi
      have h' : ∀ j, e j ≠ i := fun j hj => hi ⟨j, hj⟩
      rw [hH.eq_dirac_off_range i h', Measure.dirac_apply' _ (hB i)]
      simp [hoff i h']
    · intro j
      rw [hH.eq_on_range j]
      exact (hmp j).measure_preimage (hB (e j)).nullMeasurableSet
  · simp only [not_forall] at hoff
    obtain ⟨i, hi, hiB⟩ := hoff
    have hpre : (A.embedConfig e fun j => v j) ⁻¹' Set.univ.pi B = ∅ := by
      ext τ
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_empty_iff_false,
        iff_false, not_forall]
      exact ⟨i, by rw [embedConfig_of_not_mem_range A _ τ hi]; exact hiB⟩
    rw [hpre, measure_empty]
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [hH.eq_dirac_off_range i hi, Measure.dirac_apply' _ (hB i)]
    simp [hiB]
theorem weightDensity_embedConfig (A' : PairConstraint T) (v : ∀ j, T j → S (e j))
    (he : Function.Injective e)
    (hok : ∀ j j' s t, j ≠ j' → (A'.compatible j j' s t ↔ A.compatible (e j) (e j') (v j s) (v j' t)))
    (G : (∀ i, S i) → ℝ) (τ : ∀ j, T j) :
    A'.weightDensity (fun τ => G (A.embedConfig e v τ)) τ = A.weightDensity G (A.embedConfig e v τ) := by
  classical
  unfold PairConstraint.weightDensity
  by_cases h : A'.IsAdmissible τ
  · rw [if_pos h, if_pos ((isAdmissible_embedConfig_iff A A' v he hok τ).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((isAdmissible_embedConfig_iff A A' v he hok τ).mp h'))]
theorem map_gibbsLaw_embedConfig (A' : PairConstraint T) {m m' : ∀ i, Measure (S i)}
    [∀ i, SigmaFinite (m' i)] {μ : ∀ j, Measure (T j)} [∀ j, SigmaFinite (μ j)]
    (v : ∀ j, T j ≃ᵐ S (e j)) (he : Function.Injective e) (hH : A.IsVacantOffRange m m' e)
    (hmp : ∀ j, MeasurePreserving (v j) (μ j) (m (e j)))
    (hok : ∀ j j' s t, j ≠ j' → (A'.compatible j j' s t ↔ A.compatible (e j) (e j') (v j s) (v j' t)))
    (G : (∀ i, S i) → ℝ) (hd : Measurable (A.weightDensity G)) :
    Measure.map (A.embedConfig e fun j => v j)
        (A'.gibbsLaw μ fun τ => G (A.embedConfig e (fun j => v j) τ)) =
      A.gibbsLaw m' G := by
  have hmeas := measurable_embedConfig A (fun j => v j) he fun j => (v j).measurable
  have hmap := map_embedConfig_pi A v he hH hmp
  have hden := weightDensity_embedConfig A A' (fun j => v j) he hok G
  have hZ : ∫⁻ τ, A'.weightDensity (fun τ => G (A.embedConfig e (fun j => v j) τ)) τ ∂Measure.pi μ =
      ∫⁻ σ, A.weightDensity G σ ∂Measure.pi m' := by
    rw [← hmap, lintegral_map hd hmeas]
    simp_rw [hden]
  unfold PairConstraint.gibbsLaw
  rw [hZ, Measure.map_smul]
  congr 1
  ext B hB
  rw [Measure.map_apply hmeas hB, withDensity_apply _ (hmeas hB), withDensity_apply _ hB, ← hmap,
    setLIntegral_map hB hd hmeas]
  simp_rw [hden]
theorem singleSiteLaw_embedConfig (A' : PairConstraint T) {m : ∀ i, Measure (S i)}
    {μ : ∀ j, Measure (T j)} (v : ∀ j, T j ≃ᵐ S (e j)) (he : Function.Injective e)
    (hmp : ∀ j, MeasurePreserving (v j) (μ j) (m (e j)))
    (hok : ∀ j j' s t, j ≠ j' → (A'.compatible j j' s t ↔ A.compatible (e j) (e j') (v j s) (v j' t)))
    (hv : ∀ j, v j (A'.vacant j) = A.vacant (e j))
    (G : (∀ i, S i) → ℝ) (hd : Measurable (A.weightDensity G)) (τ : ∀ j, T j) (j : J) :
    A'.singleSiteLaw μ (fun τ => G (A.embedConfig e (fun j => v j) τ)) j τ =
      Measure.map (v j).symm (A.singleSiteLaw m G (e j) (A.embedConfig e (fun j => v j) τ)) := by
  classical
  have hden := weightDensity_embedConfig A A' (fun j => v j) he hok G
  have hs : ∀ s, A'.weightDensity (fun τ => G (A.embedConfig e (fun j => v j) τ)) (Function.update τ j s) =
      A.weightDensity G (Function.update (A.embedConfig e (fun j => v j) τ) (e j) (v j s)) := by
    intro s
    rw [hden, embedConfig_update A (fun j => v j) he]
  have hf : Measurable fun t =>
      A.weightDensity G (Function.update (A.embedConfig e (fun j => v j) τ) (e j) t) :=
    hd.comp (measurable_update _)
  have hmass : A'.conditionalMass μ (fun τ => G (A.embedConfig e (fun j => v j) τ)) j τ =
      A.conditionalMass m G (e j) (A.embedConfig e (fun j => v j) τ) := by
    unfold PairConstraint.conditionalMass
    simp_rw [hs]
    exact (hmp j).lintegral_comp hf
  unfold PairConstraint.singleSiteLaw
  rw [hmass]
  split_ifs with h
  · ext B hB
    have hB' := (v j).symm.measurable hB
    rw [Measure.map_apply (v j).symm.measurable hB, Measure.smul_apply, Measure.smul_apply,
      withDensity_apply _ hB, withDensity_apply _ hB']
    congr 1
    simp_rw [hs]
    rw [← (hmp j).map_eq, setLIntegral_map hB' hf (v j).measurable]
    have : (v j) ⁻¹' ((v j).symm ⁻¹' B) = B := by
      ext s
      simp
    rw [this]
  · rw [Measure.map_dirac' (v j).symm.measurable, ← hv j]
    simp
end Embedding
theorem singleSiteLaw_congr_measure {I : Type} [Fintype I] [DecidableEq I] {S : I → Type}
    [∀ i, MeasurableSpace (S i)] (A : PairConstraint S) {m m' : ∀ i, Measure (S i)} {i : I}
    (hi : m' i = m i) (G : (∀ i, S i) → ℝ) (σ : ∀ i, S i) :
    A.singleSiteLaw m' G i σ = A.singleSiteLaw m G i σ := by
  unfold PairConstraint.singleSiteLaw PairConstraint.conditionalMass
  rw [hi]
section OffRange
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
  (A : PairConstraint S)
theorem singleSiteLaw_eq_dirac {m' : ∀ i, Measure (S i)} {G : (∀ i, S i) → ℝ}
    (hd : Measurable (A.weightDensity G)) {i : I}
    (hi : m' i = Measure.dirac (A.vacant i)) (σ : ∀ i, S i) :
    A.singleSiteLaw m' G i σ = Measure.dirac (A.vacant i) := by
  classical
  have hf : Measurable fun s => A.weightDensity G (Function.update σ i s) := hd.comp (measurable_update _)
  unfold PairConstraint.singleSiteLaw
  split_ifs with h
  · have hmass : A.conditionalMass m' G i σ = A.weightDensity G (Function.update σ i (A.vacant i)) := by
      unfold PairConstraint.conditionalMass
      rw [hi, lintegral_dirac' _ hf]
    ext B hB
    rw [Measure.smul_apply, withDensity_apply _ hB, hi, ← lintegral_indicator hB,
      lintegral_dirac' _ (hf.indicator hB), smul_eq_mul, Measure.dirac_apply' _ hB]
    rw [hmass] at h ⊢
    by_cases ha : A.vacant i ∈ B
    · simp only [Set.indicator_of_mem ha, Pi.one_apply]
      exact ENNReal.inv_mul_cancel h.1.ne' h.2
    · simp only [Set.indicator_of_notMem ha, mul_zero]
  · rfl
theorem isActivityBounded_of_vacantOffRange {J : Type} {m m' : ∀ i, Measure (S i)}
    {G : (∀ i, S i) → ℝ} {z : I → ℝ}
    (h : A.IsActivityBounded m G z) {e : J → I} (hH : A.IsVacantOffRange m m' e) :
    A.IsActivityBounded m' G z where
  measurableSet_admissible := h.measurableSet_admissible
  measurable := h.measurable
  pos_of_admissible := h.pos_of_admissible
  measurableSet_vacant := h.measurableSet_vacant
  measure_vacant i := by
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [hH.eq_on_range j]
      exact h.measure_vacant _
    · rw [hH.eq_dirac_off_range i (fun j hj => hi ⟨j, hj⟩), Measure.dirac_apply' _ (h.measurableSet_vacant i)]
      simp
  activity_nonneg := h.activity_nonneg
  lintegral_compl_vacant_le i σ hσ := by
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [hH.eq_on_range j]
      exact h.lintegral_compl_vacant_le _ σ hσ
    · rw [hH.eq_dirac_off_range i (fun j hj => hi ⟨j, hj⟩)]
      have : (Measure.dirac (A.vacant i)).restrict {A.vacant i}ᶜ = 0 := by
        rw [Measure.restrict_eq_zero, Measure.dirac_apply' _ (h.measurableSet_vacant i).compl]
        simp
      rw [this, lintegral_zero_measure]
      exact zero_le
theorem measureReal_le_dirac_add_compl {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {a : X}
    (ha : MeasurableSet ({a} : Set X)) {B : Set X} (hB : MeasurableSet B) :
    ν.real B ≤ (Measure.dirac a).real B + ν.real {a}ᶜ := by
  by_cases hB' : a ∈ B
  · have h1 : (Measure.dirac a).real B = 1 := by
      rw [Measure.real, Measure.dirac_apply' _ hB]
      simp [hB']
    have h2 : ν.real B ≤ 1 := measureReal_le_one
    have h3 : 0 ≤ ν.real {a}ᶜ := measureReal_nonneg
    linarith
  · have h1 : (Measure.dirac a).real B = 0 := by
      rw [Measure.real, Measure.dirac_apply' _ hB]
      simp [hB']
    have h2 : ν.real B ≤ ν.real {a}ᶜ := measureReal_mono (fun x hx hx' => hB' (hx' ▸ hx))
    linarith
theorem dirac_measureReal_le_add_compl {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {a : X}
    (ha : MeasurableSet ({a} : Set X)) {B : Set X} (hB : MeasurableSet B) :
    (Measure.dirac a).real B ≤ ν.real B + ν.real {a}ᶜ := by
  by_cases hB' : a ∈ B
  · have h1 : (Measure.dirac a).real B = 1 := by
      rw [Measure.real, Measure.dirac_apply' _ hB]
      simp [hB']
    have h2 : ν.real ({a} : Set X) ≤ ν.real B := measureReal_mono (by simpa using hB')
    have h3 : ν.real ({a} : Set X) + ν.real {a}ᶜ = 1 := by
      rw [measureReal_add_measureReal_compl ha]
      simp
    linarith
  · have h1 : (Measure.dirac a).real B = 0 := by
      rw [Measure.real, Measure.dirac_apply' _ hB]
      simp [hB']
    have h2 : 0 ≤ ν.real B := measureReal_nonneg
    have h3 : 0 ≤ ν.real {a}ᶜ := measureReal_nonneg
    linarith
theorem abs_integral_sub_le_of_kernel_bounds (hD : ComparisonStatement) (μ μ' : Measure (∀ i, S i))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (K K' : ∀ i, Kernel (∀ j, S j) (S i))
    (c : I → I → ℝ) (b w : I → ℝ) (hadm : MeasurableSet {σ | A.IsAdmissible σ})
    (hG : A.IsSpecification μ K)
    (hG' : A.IsSpecification μ' K') (hc0 : ∀ i j, 0 ≤ c i j) (hb0 : ∀ i, 0 ≤ b i) (hw : ∀ i, 0 < w i)
    (hcm : ∀ i j, i ≠ j → ∀ σ σ', A.IsAdmissible σ → A.IsAdmissible σ' → (∀ k, k ≠ j → σ k = σ' k) →
      ∀ B, MeasurableSet B → (K i σ).real B ≤ (K i σ').real B + c i j / 2)
    (hbm : ∀ i σ, A.IsAdmissible σ → ∀ B, MeasurableSet B → (K i σ).real B ≤ (K' i σ).real B + b i / 2)
    (hcol : ∀ j, ∑ i, w i * c i j ≤ w j / 2) (M : Finset I) (F : (∀ i, S i) → ℝ)
    (hF : A.IsLocalObservable M w F) :
    |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ 4 * ∑ i, w i * b i := by
  obtain ⟨a, ha0, hsum, hall⟩ := hD I S A μ μ' K K' c b w hadm hG hG' hc0 hb0 hw hcm hbm hcol
  have h1 := hall F _ hF.measurable ⟨1, hF.abs_le_one⟩ hF.oscillation
  have h2 : ∑ i, a i * (if i ∈ M then (2 : ℝ) else 0) ≤ 2 * ∑ i, w i * a i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h3 := ha0 i
    have h4 := hw i
    split_ifs with hi
    · nlinarith [hF.one_le_weight i hi]
    · nlinarith [mul_nonneg h4.le h3]
  linarith
theorem abs_integral_sub_le_vacant (hD : ComparisonStatement) (hC : ActivityConditionalLawsStatement)
    {J : Type} [Fintype J] {m m' : ∀ i, Measure (S i)} [∀ i, SigmaFinite (m i)]
    [∀ i, SigmaFinite (m' i)]
    {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded m G z) {e : J → I}
    (hH : A.IsVacantOffRange m m' e)
    {c : I → I → ℝ} {w : I → ℝ} (hc : A.HasDobrushinColumns m h.measurable_weightDensity c w)
    {M Hs : Finset I}
    (hs : ∀ i ∈ Hs, m i = Measure.dirac (A.vacant i))
    {F : (∀ i, S i) → ℝ} (hF : A.IsLocalObservable M w F) :
    |∫ σ, F σ ∂A.gibbsLaw m G - ∫ σ, F σ ∂A.gibbsLaw m' G| ≤
      8 * ∑ i ∈ Finset.univ.filter (fun i => (∀ j, e j ≠ i) ∧ i ∉ Hs), w i * z i := by
  classical
  have h' := isActivityBounded_of_vacantOffRange A h hH
  obtain ⟨p, g, hz, -⟩ := hC I S A m G z h
  obtain ⟨p', g', -, -⟩ := hC I S A m' G z h'
  haveI := p
  haveI := p'
  let b : I → ℝ := fun i => if (∀ j, e j ≠ i) ∧ i ∉ Hs then 2 * z i else 0
  have hb0 : ∀ i, 0 ≤ b i := by
    intro i
    simp only [b]
    split_ifs
    · have := h.activity_nonneg i
      linarith
    · exact le_rfl
  have hbm : ∀ i σ, A.IsAdmissible σ → ∀ B, MeasurableSet B →
      (A.singleSiteKernel m h.measurable_weightDensity i σ).real B ≤
        (A.singleSiteKernel m' h'.measurable_weightDensity i σ).real B + b i / 2 := by
    intro i σ hσ B hB
    haveI := g.isMarkovKernel i
    by_cases hi : ∀ j, e j ≠ i
    · have h1 : A.singleSiteKernel m' h'.measurable_weightDensity i σ = Measure.dirac (A.vacant i) :=
        singleSiteLaw_eq_dirac A h'.measurable_weightDensity (hH.eq_dirac_off_range i hi) σ
      rw [h1]
      by_cases hin : i ∈ Hs
      · have h4 : A.singleSiteKernel m h.measurable_weightDensity i σ = Measure.dirac (A.vacant i) :=
          singleSiteLaw_eq_dirac A h.measurable_weightDensity (hs i hin) σ
        rw [h4]
        have := hb0 i
        linarith
      · have h2 := measureReal_le_dirac_add_compl (A.singleSiteKernel m h.measurable_weightDensity i σ)
          (h.measurableSet_vacant i) hB
        have h3 := hz i σ hσ
        simp only [b, if_pos (And.intro hi hin)]
        linarith
    · simp only [not_forall, not_not] at hi
      obtain ⟨j, rfl⟩ := hi
      have h1 : A.singleSiteKernel m' h'.measurable_weightDensity (e j) σ =
          A.singleSiteKernel m h.measurable_weightDensity (e j) σ :=
        singleSiteLaw_congr_measure A (hH.eq_on_range j) G σ
      rw [h1]
      have := hb0 (e j)
      linarith
  have key := abs_integral_sub_le_of_kernel_bounds A hD _ _ (A.singleSiteKernel m h.measurable_weightDensity)
    (A.singleSiteKernel m' h'.measurable_weightDensity) c b w h.measurableSet_admissible g g'
    hc.coeff_nonneg hb0 hc.weight_pos hc.kernel_le hbm hc.column_sum_le M F hF
  have hsum : ∑ i, w i * b i =
      2 * ∑ i ∈ Finset.univ.filter (fun i => (∀ j, e j ≠ i) ∧ i ∉ Hs), w i * z i := by
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [b]
    split_ifs <;> ring
  rw [hsum] at key
  linarith
end OffRange
section Ratio
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
  (A : PairConstraint S)
theorem isAdmissible_update_vacant {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) (i : I) :
    A.IsAdmissible (Function.update σ i (A.vacant i)) := by
  intro k l hkl
  by_cases hk : k = i
  · subst hk
    rw [Function.update_self]
    exact A.vacant_compatible _ _ _
  · by_cases hl : l = i
    · subst hl
      rw [Function.update_self]
      exact A.compatible_symm _ _ _ _ (A.vacant_compatible _ _ _)
    · rw [Function.update_of_ne hk, Function.update_of_ne hl]
      exact hσ k l hkl
theorem setLIntegral_compl_vacant_ne_top {m : ∀ i, Measure (S i)} {G : (∀ i, S i) → ℝ} {z : I → ℝ}
    (h : A.IsActivityBounded m G z) (i : I) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) {X : Set (S i)}
    (hX : X ⊆ {A.vacant i}ᶜ) :
    ∫⁻ s in X, A.weightDensity G (Function.update σ i s) ∂m i ≠ ⊤ := by
  classical
  have h1 := h.lintegral_compl_vacant_le i σ hσ
  have h2 : ∫⁻ s in X, A.weightDensity G (Function.update σ i s) ∂m i ≤
      ∫⁻ s in {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i :=
    lintegral_mono_set hX
  refine ne_top_of_le_ne_top ?_ (h2.trans h1)
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  unfold PairConstraint.weightDensity
  split_ifs
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top
theorem setLIntegral_eq_vacant_add {m : ∀ i, Measure (S i)} {G : (∀ i, S i) → ℝ} {z : I → ℝ}
    (h : A.IsActivityBounded m G z) (i : I) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) {X : Set (S i)} :
    ∫⁻ s in X, A.weightDensity G (Function.update σ i s) ∂m i =
      (open Classical in
        if A.vacant i ∈ X then ENNReal.ofReal (G (Function.update σ i (A.vacant i))) else 0) +
        ∫⁻ s in X ∩ {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i := by
  classical
  have hadm := isAdmissible_update_vacant A hσ i
  have h1 := lintegral_inter_add_diff (μ := m i)
    (fun s => A.weightDensity G (Function.update σ i s)) X (h.measurableSet_vacant i)
  rw [← h1, Set.diff_eq]
  congr 1
  split_ifs with ha
  · have h2 : X ∩ {A.vacant i} = {A.vacant i} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      exact ⟨fun hx => hx.2, fun hx => ⟨hx ▸ ha, hx⟩⟩
    rw [h2, setLIntegral_congr_fun (g := fun _ => ENNReal.ofReal (G (Function.update σ i (A.vacant i))))
      (h.measurableSet_vacant i), setLIntegral_const, h.measure_vacant i, mul_one]
    intro x hx
    have hx' : x = A.vacant i := hx
    simp only [hx']
    unfold PairConstraint.weightDensity
    rw [if_pos hadm]
  · have h2 : X ∩ {A.vacant i} = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hx, rfl⟩
      exact ha hx
    rw [h2]
    simp
theorem singleSiteKernel_measureReal {m : ∀ i, Measure (S i)} [∀ i, SFinite (m i)]
    {G : (∀ i, S i) → ℝ} {z : I → ℝ}
    (h : A.IsActivityBounded m G z) (i : I) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) {B : Set (S i)}
    (hB : MeasurableSet B) :
    (A.singleSiteKernel m h.measurable_weightDensity i σ).real B =
      ((open Classical in if A.vacant i ∈ B then 1 else 0) +
        (∫⁻ s in B ∩ {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i).toReal /
          G (Function.update σ i (A.vacant i))) /
      (1 + (∫⁻ s in {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i).toReal /
          G (Function.update σ i (A.vacant i))) := by
  classical
  have hadm := isAdmissible_update_vacant A hσ i
  have hg : 0 < G (Function.update σ i (A.vacant i)) := h.pos_of_admissible _ hadm
  set g := G (Function.update σ i (A.vacant i)) with hgdef
  set R := ∫⁻ s in {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i with hR
  set RB := ∫⁻ s in B ∩ {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i with hRB
  have hRf : R ≠ ⊤ := setLIntegral_compl_vacant_ne_top A h i hσ subset_rfl
  have hRBf : RB ≠ ⊤ := setLIntegral_compl_vacant_ne_top A h i hσ Set.inter_subset_right
  have hmass : A.conditionalMass m G i σ = ENNReal.ofReal g + R := by
    have := setLIntegral_eq_vacant_add A h i hσ (X := Set.univ)
    rw [Measure.restrict_univ, if_pos (Set.mem_univ _), Set.univ_inter] at this
    exact this
  have hB' : ∫⁻ s in B, A.weightDensity G (Function.update σ i s) ∂m i =
      (if A.vacant i ∈ B then ENNReal.ofReal g else 0) + RB := setLIntegral_eq_vacant_add A h i hσ
  have hpos : 0 < A.conditionalMass m G i σ := by
    rw [hmass]
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hg) le_self_add
  have hfin : A.conditionalMass m G i σ ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hRf⟩
  have hmr : (A.conditionalMass m G i σ).toReal = g + R.toReal := by
    rw [hmass, ENNReal.toReal_add ENNReal.ofReal_ne_top hRf, ENNReal.toReal_ofReal hg.le]
  have hbr : (∫⁻ s in B, A.weightDensity G (Function.update σ i s) ∂m i).toReal =
      (if A.vacant i ∈ B then g else 0) + RB.toReal := by
    rw [hB']
    split_ifs
    · rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hRBf, ENNReal.toReal_ofReal hg.le]
    · simp
  have hk : (A.singleSiteKernel m h.measurable_weightDensity i σ).real B =
      (∫⁻ s in B, A.weightDensity G (Function.update σ i s) ∂m i).toReal /
        (A.conditionalMass m G i σ).toReal := by
    change (A.singleSiteLaw m G i σ).real B = _
    unfold PairConstraint.singleSiteLaw
    rw [if_pos ⟨hpos, hfin⟩, measureReal_def, Measure.smul_apply, withDensity_apply _ hB, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]
  rw [hk, hbr, hmr]
  have hg' : g ≠ 0 := hg.ne'
  have hd : g + R.toReal ≠ 0 := by positivity
  split_ifs <;> field_simp <;> ring
theorem div_le_div_add_of_ratio {ι P₁ Q₁ P₂ Q₂ E Z : ℝ} (h0 : 0 ≤ ι) (h1 : ι ≤ 1) (hP₁ : 0 ≤ P₁)
    (hQ₁ : 0 ≤ Q₁) (hP₂ : 0 ≤ P₂)
    (hQ₂ : 0 ≤ Q₂) (hP₂Z : P₂ ≤ Z) (hQ₁Z : Q₁ ≤ Z) (hQ₂Z : Q₂ ≤ Z) (hZ : Z ≤ 1) (hE : 1 ≤ E)
    (hP : P₁ ≤ E * P₂) (hQ : Q₂ ≤ E * Q₁) :
    (ι + P₁) / (1 + Q₁) ≤ (ι + P₂) / (1 + Q₂) + 4 * (E - 1) * Z := by
  have hZ0 : 0 ≤ Z := hQ₁.trans hQ₁Z
  have hu : 0 ≤ (E - 1) * Z := mul_nonneg (by linarith) hZ0
  have hd : Q₂ - Q₁ ≤ (E - 1) * Z := by nlinarith
  have he : P₁ - P₂ ≤ (E - 1) * Z := by nlinarith
  have h3 : ι * (Q₂ - Q₁) ≤ (E - 1) * Z := by
    have : ι * (Q₂ - Q₁) ≤ ι * ((E - 1) * Z) := mul_le_mul_of_nonneg_left hd h0
    nlinarith
  have h4 : (P₁ - P₂) * Q₂ ≤ (E - 1) * Z := by
    have : (P₁ - P₂) * Q₂ ≤ ((E - 1) * Z) * Q₂ := mul_le_mul_of_nonneg_right he hQ₂
    have h5 : Q₂ ≤ 1 := hQ₂Z.trans hZ
    nlinarith
  have h5 : P₂ * (Q₂ - Q₁) ≤ (E - 1) * Z := by
    have : P₂ * (Q₂ - Q₁) ≤ P₂ * ((E - 1) * Z) := mul_le_mul_of_nonneg_left hd hP₂
    nlinarith
  have hD₁ : 0 < 1 + Q₁ := by linarith
  have hD₂ : 0 < 1 + Q₂ := by linarith
  rw [div_add' _ _ _ hD₂.ne', div_le_div_iff₀ hD₁ hD₂]
  nlinarith [mul_nonneg hu (mul_nonneg hQ₁ hQ₂), mul_nonneg hu hQ₁, mul_nonneg hu hQ₂]
theorem setLIntegral_ratio_le {m : ∀ i, Measure (S i)} {G₁ G₂ : (∀ i, S i) → ℝ} {z₁ z₂ : I → ℝ}
    (h₁ : A.IsActivityBounded m G₁ z₁) (h₂ : A.IsActivityBounded m G₂ z₂) (i : I) {σ : ∀ i, S i}
    (hσ : A.IsAdmissible σ) {E : ℝ}
    (hE : 0 ≤ E)
    (hr : ∀ s, A.IsAdmissible (Function.update σ i s) →
      G₁ (Function.update σ i s) * G₂ (Function.update σ i (A.vacant i)) ≤
        E * (G₁ (Function.update σ i (A.vacant i)) * G₂ (Function.update σ i s)))
    {X : Set (S i)} (hX' : X ⊆ {A.vacant i}ᶜ) :
    (∫⁻ s in X, A.weightDensity G₁ (Function.update σ i s) ∂m i).toReal /
        G₁ (Function.update σ i (A.vacant i)) ≤
      E * ((∫⁻ s in X, A.weightDensity G₂ (Function.update σ i s) ∂m i).toReal /
        G₂ (Function.update σ i (A.vacant i))) := by
  classical
  have hadm := isAdmissible_update_vacant A hσ i
  have hg₁ : 0 < G₁ (Function.update σ i (A.vacant i)) := h₁.pos_of_admissible _ hadm
  have hg₂ : 0 < G₂ (Function.update σ i (A.vacant i)) := h₂.pos_of_admissible _ hadm
  set g₁ := G₁ (Function.update σ i (A.vacant i))
  set g₂ := G₂ (Function.update σ i (A.vacant i))
  have hf₁ : Measurable fun s => A.weightDensity G₁ (Function.update σ i s) :=
    h₁.measurable_weightDensity.comp (measurable_update _)
  have hf₂ : Measurable fun s => A.weightDensity G₂ (Function.update σ i s) :=
    h₂.measurable_weightDensity.comp (measurable_update _)
  have hpt : ∀ s, ENNReal.ofReal g₂ * A.weightDensity G₁ (Function.update σ i s) ≤
      ENNReal.ofReal (E * g₁) * A.weightDensity G₂ (Function.update σ i s) := by
    intro s
    unfold PairConstraint.weightDensity
    by_cases hs : A.IsAdmissible (Function.update σ i s)
    · rw [if_pos hs, if_pos hs, ← ENNReal.ofReal_mul hg₂.le, ← ENNReal.ofReal_mul (mul_nonneg hE hg₁.le)]
      apply ENNReal.ofReal_le_ofReal
      have := hr s hs
      nlinarith
    · rw [if_neg hs, if_neg hs]
      simp
  have hint : ENNReal.ofReal g₂ * ∫⁻ s in X, A.weightDensity G₁ (Function.update σ i s) ∂m i ≤
      ENNReal.ofReal (E * g₁) * ∫⁻ s in X, A.weightDensity G₂ (Function.update σ i s) ∂m i := by
    rw [← lintegral_const_mul _ hf₁, ← lintegral_const_mul _ hf₂]
    exact lintegral_mono hpt
  have hfin₂ := setLIntegral_compl_vacant_ne_top A h₂ i hσ hX'
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin₂) hint
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hg₂.le,
    ENNReal.toReal_ofReal (mul_nonneg hE hg₁.le)] at hreal
  rw [div_le_iff₀ hg₁]
  have : E * ((∫⁻ s in X, A.weightDensity G₂ (Function.update σ i s) ∂m i).toReal / g₂) * g₁ =
      (E * g₁ * (∫⁻ s in X, A.weightDensity G₂ (Function.update σ i s) ∂m i).toReal) / g₂ := by
    field_simp
  rw [this, le_div_iff₀ hg₂]
  linarith
theorem singleSiteKernel_measureReal_le_of_ratio {m : ∀ i, Measure (S i)} [∀ i, SFinite (m i)]
    {G₁ G₂ : (∀ i, S i) → ℝ} {z₁ z₂ : I → ℝ}
    (h₁ : A.IsActivityBounded m G₁ z₁) (h₂ : A.IsActivityBounded m G₂ z₂) (i : I) {σ : ∀ i, S i}
    (hσ : A.IsAdmissible σ) {E Z : ℝ}
    (hE : 1 ≤ E) (hz₁ : z₁ i ≤ Z) (hz₂ : z₂ i ≤ Z) (hZ : Z ≤ 1)
    (hr : ∀ s, A.IsAdmissible (Function.update σ i s) →
      G₁ (Function.update σ i s) * G₂ (Function.update σ i (A.vacant i)) ≤
        E * (G₁ (Function.update σ i (A.vacant i)) * G₂ (Function.update σ i s)) ∧
      G₂ (Function.update σ i s) * G₁ (Function.update σ i (A.vacant i)) ≤
        E * (G₂ (Function.update σ i (A.vacant i)) * G₁ (Function.update σ i s)))
    {B : Set (S i)} (hB : MeasurableSet B) :
    (A.singleSiteKernel m h₁.measurable_weightDensity i σ).real B ≤
      (A.singleSiteKernel m h₂.measurable_weightDensity i σ).real B + 4 * (E - 1) * Z := by
  classical
  have hadm := isAdmissible_update_vacant A hσ i
  have hg₁ : 0 < G₁ (Function.update σ i (A.vacant i)) := h₁.pos_of_admissible _ hadm
  have hg₂ : 0 < G₂ (Function.update σ i (A.vacant i)) := h₂.pos_of_admissible _ hadm
  have hq : ∀ {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded m G z),
      (∫⁻ s in {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i).toReal /
        G (Function.update σ i (A.vacant i)) ≤ z i := by
    intro G z h
    have hadm' := isAdmissible_update_vacant A hσ i
    have hg : 0 < G (Function.update σ i (A.vacant i)) := h.pos_of_admissible _ hadm'
    have h1 := h.lintegral_compl_vacant_le i σ hσ
    have hd : A.weightDensity G (Function.update σ i (A.vacant i)) =
        ENNReal.ofReal (G (Function.update σ i (A.vacant i))) := by
      unfold PairConstraint.weightDensity
      rw [if_pos hadm']
    rw [hd, ← ENNReal.ofReal_mul (h.activity_nonneg i)] at h1
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal (mul_nonneg (h.activity_nonneg i) hg.le)] at h2
    rw [div_le_iff₀ hg]
    exact h2
  have hp : ∀ {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded m G z),
      (∫⁻ s in B ∩ {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i).toReal /
        G (Function.update σ i (A.vacant i)) ≤
      (∫⁻ s in {A.vacant i}ᶜ, A.weightDensity G (Function.update σ i s) ∂m i).toReal /
        G (Function.update σ i (A.vacant i)) := by
    intro G z h
    have hg : 0 < G (Function.update σ i (A.vacant i)) :=
      h.pos_of_admissible _ (isAdmissible_update_vacant A hσ i)
    refine div_le_div_of_nonneg_right ?_ hg.le
    exact ENNReal.toReal_mono (setLIntegral_compl_vacant_ne_top A h i hσ subset_rfl)
      (lintegral_mono_set Set.inter_subset_right)
  rw [singleSiteKernel_measureReal A h₁ i hσ hB, singleSiteKernel_measureReal A h₂ i hσ hB]
  refine div_le_div_add_of_ratio ?_ ?_ (by positivity) (by positivity) (by positivity) (by positivity)
    ((hp h₂).trans ((hq h₂).trans hz₂)) ((hq h₁).trans hz₁) ((hq h₂).trans hz₂) hZ hE
    (setLIntegral_ratio_le A h₁ h₂ i hσ (by linarith) (fun s hs => (hr s hs).1) Set.inter_subset_right)
    (setLIntegral_ratio_le A h₂ h₁ i hσ (by linarith) (fun s hs => (hr s hs).2) subset_rfl)
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num
end Ratio
section Pullback
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {S : I → Type}
  [∀ i, MeasurableSpace (S i)] {T : J → Type} [∀ j, MeasurableSpace (T j)]
  (A : PairConstraint S) {e : J → I}
theorem isActivityBounded_pullback (A' : PairConstraint T) {m : ∀ i, Measure (S i)}
    {μ : ∀ j, Measure (T j)}
    (v : ∀ j, T j ≃ᵐ S (e j)) (he : Function.Injective e)
    (hmp : ∀ j, MeasurePreserving (v j) (μ j) (m (e j)))
    (hok : ∀ j j' s t, j ≠ j' → (A'.compatible j j' s t ↔ A.compatible (e j) (e j') (v j s) (v j' t)))
    (hv : ∀ j, v j (A'.vacant j) = A.vacant (e j))
    {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded m G z) :
    A'.IsActivityBounded μ (fun τ => G (A.embedConfig e (fun j => v j) τ)) (fun j => z (e j)) := by
  classical
  have hmeas := measurable_embedConfig A (fun j => v j) he fun j => (v j).measurable
  have hadm := isAdmissible_embedConfig_iff A A' (fun j => v j) he hok
  have hden := weightDensity_embedConfig A A' (fun j => v j) he hok G
  have hset : ∀ j, ({A'.vacant j} : Set (T j)) = (v j) ⁻¹' {A.vacant (e j)} := by
    intro j
    ext s
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      exact hv j
    · intro hs
      exact (v j).injective (hs.trans (hv j).symm)
  refine ⟨?_, h.measurable.comp hmeas, fun τ hτ => h.pos_of_admissible _ ((hadm τ).mpr hτ), ?_, ?_,
    fun j => h.activity_nonneg _, ?_⟩
  · have : {τ | A'.IsAdmissible τ} = (A.embedConfig e fun j => v j) ⁻¹' {σ | A.IsAdmissible σ} := by
      ext τ
      exact (hadm τ).symm
    rw [this]
    exact hmeas h.measurableSet_admissible
  · intro j
    rw [hset j]
    exact (v j).measurable (h.measurableSet_vacant _)
  · intro j
    rw [hset j, (hmp j).measure_preimage (h.measurableSet_vacant _).nullMeasurableSet]
    exact h.measure_vacant _
  · intro j τ hτ
    have hf : Measurable fun t =>
        A.weightDensity G (Function.update (A.embedConfig e (fun j => v j) τ) (e j) t) :=
      h.measurable_weightDensity.comp (measurable_update _)
    have hs : ∀ s, A'.weightDensity (fun τ => G (A.embedConfig e (fun j => v j) τ)) (Function.update τ j s) =
        A.weightDensity G (Function.update (A.embedConfig e (fun j => v j) τ) (e j) (v j s)) := by
      intro s
      rw [hden, embedConfig_update A (fun j => v j) he]
    have hc : ({A'.vacant j}ᶜ : Set (T j)) = (v j) ⁻¹' {A.vacant (e j)}ᶜ := by
      rw [hset j, Set.preimage_compl]
    simp_rw [hs]
    rw [hc, (hmp j).setLIntegral_comp_preimage (h.measurableSet_vacant _).compl hf, hv j]
    exact h.lintegral_compl_vacant_le _ _ ((hadm τ).mpr hτ)
end Pullback
end VacantSpin
open VacantSpin in
theorem vacantSpinComparisonStatement_holds (hD : ComparisonStatement)
    (hC : ActivityConditionalLawsStatement) : vacantSpinComparisonStatement := by
  intro I₁ I₂ J _ _ _ _ _ _ S₁ S₂ T _ _ _ A₁ A₂ A m₁ m₁' m₂ m₂' μ _ _ _ _ _ G₁ G₂ z₁ z₂ e₁ e₂ v₁ v₂ c₁ c₂
    w₁ w₂ b E M₁ H₁ M₂ H₂ F₁ F₂ h₁ h₂ he₁ he₂ hH₁ hH₂ hs₁ hs₂ hv₁ hv₂ hok₁ hok₂ hmp₁ hmp₂ hcol₁ hcol₂
    hF₁ hF₂ hlink hb0 hb
  classical
  have d1 := abs_integral_sub_le_vacant A₁ hD hC h₁ hH₁ hcol₁ hs₁ hF₁
  have d2 := abs_integral_sub_le_vacant A₂ hD hC h₂ hH₂ hcol₂ hs₂ hF₂
  have p₁ := isActivityBounded_pullback A₁ A v₁ he₁ hmp₁ hok₁ hv₁ h₁
  have p₂ := isActivityBounded_pullback A₂ A v₂ he₂ hmp₂ hok₂ hv₂ h₂
  set x₁ := A₁.embedConfig e₁ fun j => v₁ j with hx₁
  set x₂ := A₂.embedConfig e₂ fun j => v₂ j with hx₂
  have hm₁ : Measurable x₁ := measurable_embedConfig A₁ _ he₁ fun j => (v₁ j).measurable
  have hm₂ : Measurable x₂ := measurable_embedConfig A₂ _ he₂ fun j => (v₂ j).measurable
  have hl₁ := map_gibbsLaw_embedConfig A₁ A v₁ he₁ hH₁ hmp₁ hok₁ G₁ h₁.measurable_weightDensity
  have hl₂ := map_gibbsLaw_embedConfig A₂ A v₂ he₂ hH₂ hmp₂ hok₂ G₂ h₂.measurable_weightDensity
  have i₁ : ∫ σ, F₁ σ ∂A₁.gibbsLaw m₁' G₁ = ∫ τ, F₁ (x₁ τ) ∂A.gibbsLaw μ fun τ => G₁ (x₁ τ) := by
    rw [← hl₁, integral_map hm₁.aemeasurable hF₁.measurable.aestronglyMeasurable]
  have i₂ : ∫ σ, F₂ σ ∂A₂.gibbsLaw m₂' G₂ = ∫ τ, F₁ (x₁ τ) ∂A.gibbsLaw μ fun τ => G₂ (x₂ τ) := by
    rw [← hl₂, integral_map hm₂.aemeasurable hF₂.measurable.aestronglyMeasurable]
    simp_rw [hlink]
    rfl
  obtain ⟨q₁, g₁, pz₁, -⟩ := hC J T A μ _ _ p₁
  obtain ⟨q₂, g₂, pz₂, -⟩ := hC J T A μ _ _ p₂
  haveI := q₁
  haveI := q₂
  have hadm₁ := isAdmissible_embedConfig_iff A₁ A (fun j => v₁ j) he₁ hok₁
  have hker : ∀ j τ B, MeasurableSet B → (A.singleSiteKernel μ p₁.measurable_weightDensity j τ).real B =
      (A₁.singleSiteKernel m₁ h₁.measurable_weightDensity (e₁ j) (x₁ τ)).real ((v₁ j).symm ⁻¹' B) := by
    intro j τ B hB
    have := singleSiteLaw_embedConfig A₁ A (m := m₁) v₁ he₁ hmp₁ hok₁ hv₁ G₁ h₁.measurable_weightDensity τ j
    change (A.singleSiteLaw μ _ j τ).real B = (A₁.singleSiteLaw m₁ G₁ (e₁ j) (x₁ τ)).real _
    rw [this, map_measureReal_apply (v₁ j).symm.measurable hB]
  have hdiff : ∀ (τ τ' : ∀ j, T j) (j' : J), (∀ k, k ≠ j' → τ k = τ' k) →
      ∀ k, k ≠ e₁ j' → x₁ τ k = x₁ τ' k := by
    intro τ τ' j' hτ k hk
    by_cases h1 : ∃ j, e₁ j = k
    · obtain ⟨j, rfl⟩ := h1
      have hj : j ≠ j' := fun hh => hk (by rw [hh])
      rw [hx₁, embedConfig_apply A₁ _ he₁, embedConfig_apply A₁ _ he₁, hτ j hj]
    · have h' : ∀ j, e₁ j ≠ k := fun j hj => h1 ⟨j, hj⟩
      rw [hx₁, embedConfig_of_not_mem_range A₁ _ _ h', embedConfig_of_not_mem_range A₁ _ _ h']
  have hcm : ∀ j j', j ≠ j' → ∀ τ τ', A.IsAdmissible τ → A.IsAdmissible τ' →
      (∀ k, k ≠ j' → τ k = τ' k) →
      ∀ B, MeasurableSet B → (A.singleSiteKernel μ p₁.measurable_weightDensity j τ).real B ≤
        (A.singleSiteKernel μ p₁.measurable_weightDensity j τ').real B + c₁ (e₁ j) (e₁ j') / 2 := by
    intro j j' hj τ τ' hτ hτ' hd B hB
    rw [hker j τ B hB, hker j τ' B hB]
    exact hcol₁.kernel_le (e₁ j) (e₁ j') (he₁.ne hj) _ _ ((hadm₁ τ).mpr hτ) ((hadm₁ τ').mpr hτ')
      (hdiff τ τ' j' hd) _ ((v₁ j).symm.measurable hB)
  have hbm : ∀ j τ, A.IsAdmissible τ → ∀ B, MeasurableSet B →
      (A.singleSiteKernel μ p₁.measurable_weightDensity j τ).real B ≤
        (A.singleSiteKernel μ p₂.measurable_weightDensity j τ).real B + b j / 2 := by
    intro j τ hτ B hB
    haveI := g₁.isMarkovKernel j
    haveI := g₂.isMarkovKernel j
    rcases hb j with hplain | ⟨hE, hz₁, hz₂, hbE, hr⟩
    · have n1 := measureReal_le_dirac_add_compl (A.singleSiteKernel μ p₁.measurable_weightDensity j τ)
        (p₁.measurableSet_vacant j) hB
      have n2 := dirac_measureReal_le_add_compl (A.singleSiteKernel μ p₂.measurable_weightDensity j τ)
        (p₂.measurableSet_vacant j) hB
      have n3 := pz₁ j τ hτ
      have n4 := pz₂ j τ hτ
      linarith
    · have hZ : max (z₁ (e₁ j)) (z₂ (e₂ j)) ≤ 1 := max_le hz₁ hz₂
      have := singleSiteKernel_measureReal_le_of_ratio A p₁ p₂ j hτ hE (le_max_left _ _)
        (le_max_right _ _) hZ (fun s hs => hr τ s hs) hB
      linarith
  have hcol : ∀ j', ∑ j, w₁ (e₁ j) * c₁ (e₁ j) (e₁ j') ≤ w₁ (e₁ j') / 2 := by
    intro j'
    have h1 : ∑ j, w₁ (e₁ j) * c₁ (e₁ j) (e₁ j') =
        ∑ i ∈ Finset.univ.image e₁, w₁ i * c₁ i (e₁ j') :=
      (Finset.sum_image (f := fun i => w₁ i * c₁ i (e₁ j')) fun _ _ _ _ hh => he₁ hh).symm
    rw [h1]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => ?_)
      (hcol₁.column_sum_le (e₁ j'))
    exact mul_nonneg (hcol₁.weight_pos i).le (hcol₁.coeff_nonneg _ _)
  have hread : A.IsLocalObservable (Finset.univ.filter fun j => e₁ j ∈ M₁) (fun j => w₁ (e₁ j))
      fun τ => F₁ (x₁ τ) := by
    refine ⟨hF₁.measurable.comp hm₁, fun τ => hF₁.abs_le_one _, ⟨fun j => ?_, ?_⟩, fun j hj => ?_⟩
    · dsimp only
      split_ifs <;> norm_num
    · intro j τ τ' hτ hτ' hd
      have := hF₁.oscillation.2 (e₁ j) (x₁ τ) (x₁ τ') ((hadm₁ τ).mpr hτ) ((hadm₁ τ').mpr hτ')
        (hdiff τ τ' j hd)
      simpa [Finset.mem_filter] using this
    · exact hF₁.one_le_weight _ (Finset.mem_filter.mp hj).2
  have d3 := abs_integral_sub_le_of_kernel_bounds A hD _ _ (A.singleSiteKernel μ p₁.measurable_weightDensity)
    (A.singleSiteKernel μ p₂.measurable_weightDensity) (fun j j' => c₁ (e₁ j) (e₁ j')) b
    (fun j => w₁ (e₁ j)) p₁.measurableSet_admissible g₁ g₂ (fun _ _ => hcol₁.coeff_nonneg _ _) hb0
    (fun _ => hcol₁.weight_pos _) hcm hbm hcol _ _ hread
  rw [← i₁, ← i₂] at d3
  have tri : ∀ a b c d : ℝ, |a - d| ≤ |a - b| + |b - c| + |d - c| := by
    intro a b c d
    have h1 : |a - d| ≤ |a - b| + |b - d| := abs_sub_le a b d
    have h2 : |b - d| ≤ |b - c| + |c - d| := abs_sub_le b c d
    have h3 : |c - d| = |d - c| := abs_sub_comm c d
    linarith
  have := tri (∫ σ, F₁ σ ∂A₁.gibbsLaw m₁ G₁) (∫ σ, F₁ σ ∂A₁.gibbsLaw m₁' G₁) (∫ σ, F₂ σ ∂A₂.gibbsLaw m₂' G₂)
    (∫ σ, F₂ σ ∂A₂.gibbsLaw m₂ G₂)
  linarith
end Dobrushin
end YangMills.Construction
end
