import YangMills.Construction.ClusterExpansionOfAStep.ComparisonOfHeldGasesProof
import YangMills.Construction.ResponseInTheExpansion.ComparisonAtOscillations
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.Dobrushin
namespace OscillationComparison
section Embedding
set_option linter.unusedSectionVars false
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {S : I → Type}
  [∀ i, MeasurableSpace (S i)] {T : J → Type} [∀ j, MeasurableSpace (T j)]
  (A : PairConstraint S) {e : J → I}
theorem embedConfig_apply (v : ∀ j, T j → S (e j)) (he : Function.Injective e) (τ : ∀ j, T j) (j : J) :
    A.embedConfig e v τ (e j) = v j (τ j) := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.embedConfig_apply <;> assumption
theorem embedConfig_of_not_mem_range (v : ∀ j, T j → S (e j)) (τ : ∀ j, T j) {i : I} (h : ∀ j, e j ≠ i) :
    A.embedConfig e v τ i = A.vacant i := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.embedConfig_of_not_mem_range <;> assumption
theorem measurable_embedConfig (v : ∀ j, T j → S (e j)) (he : Function.Injective e)
    (hv : ∀ j, Measurable (v j)) : Measurable (A.embedConfig e v) := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.measurable_embedConfig <;> assumption
theorem isAdmissible_embedConfig_iff (A' : PairConstraint T) (v : ∀ j, T j → S (e j)) (he : Function.Injective e)
    (hok : ∀ j j' s t, j ≠ j' → (A'.compatible j j' s t ↔ A.compatible (e j) (e j') (v j s) (v j' t)))
    (τ : ∀ j, T j) :
    A.IsAdmissible (A.embedConfig e v τ) ↔ A'.IsAdmissible τ := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.isAdmissible_embedConfig_iff <;> assumption
theorem map_gibbsLaw_embedConfig (A' : PairConstraint T) {m m' : ∀ i, Measure (S i)}
    [∀ i, SigmaFinite (m' i)]
    {μ : ∀ j, Measure (T j)} [∀ j, SigmaFinite (μ j)] (v : ∀ j, T j ≃ᵐ S (e j))
    (he : Function.Injective e) (hH : A.IsVacantOffRange m m' e)
    (hmp : ∀ j, MeasurePreserving (v j) (μ j) (m (e j)))
    (hok : ∀ j j' s t, j ≠ j' → (A'.compatible j j' s t ↔ A.compatible (e j) (e j') (v j s) (v j' t)))
    (G : (∀ i, S i) → ℝ) (hd : Measurable (A.weightDensity G)) :
    Measure.map (A.embedConfig e fun j => v j)
        (A'.gibbsLaw μ fun τ => G (A.embedConfig e (fun j => v j) τ)) =
      A.gibbsLaw m' G := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.map_gibbsLaw_embedConfig <;> assumption
theorem singleSiteLaw_comp_embedConfig (A' : PairConstraint T) {m : ∀ i, Measure (S i)}
    {μ : ∀ j, Measure (T j)}
    (v : ∀ j, T j ≃ᵐ S (e j)) (he : Function.Injective e)
    (hmp : ∀ j, MeasurePreserving (v j) (μ j) (m (e j)))
    (hok : ∀ j j' s t, j ≠ j' → (A'.compatible j j' s t ↔ A.compatible (e j) (e j') (v j s) (v j' t)))
    (hv : ∀ j, v j (A'.vacant j) = A.vacant (e j))
    (G : (∀ i, S i) → ℝ) (hd : Measurable (A.weightDensity G)) (τ : ∀ j, T j) (j : J) :
    A'.singleSiteLaw μ (fun τ => G (A.embedConfig e (fun j => v j) τ)) j τ =
      Measure.map (v j).symm (A.singleSiteLaw m G (e j) (A.embedConfig e (fun j => v j) τ)) := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.singleSiteLaw_embedConfig <;> assumption
end Embedding
theorem singleSiteLaw_congr_measure {I : Type} [Fintype I] [DecidableEq I] {S : I → Type}
    [∀ i, MeasurableSpace (S i)]
    (A : PairConstraint S) {m m' : ∀ i, Measure (S i)} {i : I} (hi : m' i = m i) (G : (∀ i, S i) → ℝ)
    (σ : ∀ i, S i) : A.singleSiteLaw m' G i σ = A.singleSiteLaw m G i σ := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.singleSiteLaw_congr_measure <;> assumption
section VacantOffRange
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
  (A : PairConstraint S)
theorem singleSiteLaw_of_dirac {m' : ∀ i, Measure (S i)} {G : (∀ i, S i) → ℝ}
    (hd : Measurable (A.weightDensity G)) {i : I}
    (hi : m' i = Measure.dirac (A.vacant i)) (σ : ∀ i, S i) :
    A.singleSiteLaw m' G i σ = Measure.dirac (A.vacant i) := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.singleSiteLaw_eq_dirac <;> assumption
theorem isActivityBounded_of_vacantOffRange {J : Type} {m m' : ∀ i, Measure (S i)} {G : (∀ i, S i) → ℝ}
    {z : I → ℝ}
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
    ν.real B ≤ (Measure.dirac a).real B + ν.real {a}ᶜ := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.measureReal_le_dirac_add_compl <;> assumption
theorem dirac_measureReal_le_add_compl {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {a : X}
    (ha : MeasurableSet ({a} : Set X)) {B : Set X} (hB : MeasurableSet B) :
    (Measure.dirac a).real B ≤ ν.real B + ν.real {a}ᶜ := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.dirac_measureReal_le_add_compl <;> assumption
theorem abs_integral_sub_le_of_oscillation (hD : ComparisonStatement) (μ μ' : Measure (∀ i, S i))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (K K' : ∀ i, Kernel (∀ j, S j) (S i))
    (c : I → I → ℝ) (b w : I → ℝ) (hadm : MeasurableSet {σ | A.IsAdmissible σ})
    (hG : A.IsSpecification μ K)
    (hG' : A.IsSpecification μ' K') (hc0 : ∀ i j, 0 ≤ c i j) (hb0 : ∀ i, 0 ≤ b i) (hw : ∀ i, 0 < w i)
    (hcm : ∀ i j, i ≠ j → ∀ σ σ', A.IsAdmissible σ → A.IsAdmissible σ' → (∀ k, k ≠ j → σ k = σ' k) →
      ∀ B, MeasurableSet B → (K i σ).real B ≤ (K i σ').real B + c i j / 2)
    (hbm : ∀ i σ, A.IsAdmissible σ → ∀ B, MeasurableSet B → (K i σ).real B ≤ (K' i σ).real B + b i / 2)
    (hcol : ∀ j, ∑ i, w i * c i j ≤ w j / 2) (Kc : ℝ) (F : (∀ i, S i) → ℝ)
    (hF : A.OscillationControlled w Kc F) :
    |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ Kc * (2 * ∑ i, w i * b i) := by
  obtain ⟨a, ha0, hsum, hall⟩ := hD I S A μ μ' K K' c b w hadm hG hG' hc0 hb0 hw hcm hbm hcol
  have h1 := hall F _ hF.measurable hF.bounded hF.oscillation
  have h2 : ∑ i, a i * (Kc * w i) = Kc * ∑ i, w i * a i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left hsum hF.nonneg)
theorem abs_integral_sub_gibbsLaw_vacantOffRange_le (hD : ComparisonStatement)
    (hC : ActivityConditionalLawsStatement)
    {J : Type} [Fintype J] {m m' : ∀ i, Measure (S i)} [∀ i, SigmaFinite (m i)] [∀ i, SigmaFinite (m' i)]
    {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded m G z) {e : J → I}
    (hH : A.IsVacantOffRange m m' e)
    {c : I → I → ℝ} {w : I → ℝ} (hc : A.HasDobrushinColumns m h.measurable_weightDensity c w) {Hs : Finset I}
    (hs : ∀ i ∈ Hs, m i = Measure.dirac (A.vacant i))
    {Kc : ℝ} {F : (∀ i, S i) → ℝ} (hF : A.OscillationControlled w Kc F) :
    |∫ σ, F σ ∂A.gibbsLaw m G - ∫ σ, F σ ∂A.gibbsLaw m' G| ≤
      Kc * (4 * ∑ i ∈ Finset.univ.filter (fun i => (∀ j, e j ≠ i) ∧ i ∉ Hs), w i * z i) := by
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
        singleSiteLaw_of_dirac A h'.measurable_weightDensity (hH.eq_dirac_off_range i hi) σ
      rw [h1]
      by_cases hin : i ∈ Hs
      · have h4 : A.singleSiteKernel m h.measurable_weightDensity i σ = Measure.dirac (A.vacant i) :=
          singleSiteLaw_of_dirac A h.measurable_weightDensity (hs i hin) σ
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
  have key := abs_integral_sub_le_of_oscillation A hD _ _ (A.singleSiteKernel m h.measurable_weightDensity)
    (A.singleSiteKernel m' h'.measurable_weightDensity) c b w h.measurableSet_admissible g g' hc.coeff_nonneg
    hb0 hc.weight_pos hc.kernel_le hbm hc.column_sum_le Kc F hF
  have hsum : ∑ i, w i * b i =
      2 * ∑ i ∈ Finset.univ.filter (fun i => (∀ j, e j ≠ i) ∧ i ∉ Hs), w i * z i := by
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [b]
    split_ifs <;> ring
  rw [hsum] at key
  refine key.trans (le_of_eq ?_)
  ring
theorem abs_integral_gibbsLaw_sub_vacant_le (hD : ComparisonStatement)
    (hC : ActivityConditionalLawsStatement)
    {m : ∀ i, Measure (S i)} [∀ i, SigmaFinite (m i)] {G : (∀ i, S i) → ℝ} {z : I → ℝ}
    (h : A.IsActivityBounded m G z)
    {c : I → I → ℝ} {w : I → ℝ} (hc : A.HasDobrushinColumns m h.measurable_weightDensity c w) {Kc : ℝ}
    {F : (∀ i, S i) → ℝ}
    (hF : A.OscillationControlled w Kc F) :
    |∫ σ, F σ ∂A.gibbsLaw m G - F A.vacant| ≤ Kc * (4 * ∑ i, w i * z i) := by
  classical
  obtain ⟨p, g, hz, -⟩ := hC I S A m G z h
  haveI := p
  let K' : ∀ i, Kernel (∀ j, S j) (S i) := fun i => Kernel.const _ (Measure.dirac (A.vacant i))
  have habs : A.IsAdmissible A.vacant := fun i j _ => A.vacant_compatible i j _
  have hset : ∀ (i : I) (σ : ∀ j, S j), MeasurableSet {s | A.IsAdmissible (Function.update σ i s)} :=
    fun i σ => (measurable_update σ) h.measurableSet_admissible
  have g' : A.IsSpecification (Measure.dirac A.vacant) K' := by
    refine ⟨fun i => ?_, fun _ _ _ => rfl, fun i F' hF' _ => ?_, fun i σ hσ => ?_, ?_⟩
    · change IsMarkovKernel (Kernel.const _ _)
      infer_instance
    · have h1 : ∀ σ, ∫ s, F' (Function.update σ i s) ∂(K' i σ) =
          F' (Function.update σ i (A.vacant i)) := by
        intro σ
        exact integral_dirac' _ _ (hF'.comp (measurable_update σ)).stronglyMeasurable
      simp_rw [h1]
      rw [integral_dirac' _ _ hF'.stronglyMeasurable,
        integral_dirac' (fun σ => F' (Function.update σ i (A.vacant i))) _
          (hF'.comp measurable_update_left).stronglyMeasurable]
      simp
    · change ∀ᵐ s ∂(Measure.dirac (A.vacant i)), _
      rw [ae_dirac_iff (hset i σ)]
      intro a b hab
      by_cases ha : a = i
      · subst ha
        rw [Function.update_self, Function.update_of_ne hab.symm]
        exact A.vacant_compatible _ _ _
      · by_cases hb : b = i
        · subst hb
          rw [Function.update_self, Function.update_of_ne ha]
          exact A.compatible_symm _ _ _ _ (A.vacant_compatible _ _ _)
        · rw [Function.update_of_ne ha, Function.update_of_ne hb]
          exact hσ a b hab
    · rw [ae_dirac_iff h.measurableSet_admissible]
      exact habs
  have hb0 : ∀ i, 0 ≤ 2 * z i := fun i => by
    have := h.activity_nonneg i
    linarith
  have hbm : ∀ i σ, A.IsAdmissible σ → ∀ B, MeasurableSet B →
      (A.singleSiteKernel m h.measurable_weightDensity i σ).real B ≤ (K' i σ).real B + 2 * z i / 2 := by
    intro i σ hσ B hB
    haveI := g.isMarkovKernel i
    have h2 := measureReal_le_dirac_add_compl (A.singleSiteKernel m h.measurable_weightDensity i σ)
      (h.measurableSet_vacant i) hB
    have h3 := hz i σ hσ
    change _ ≤ (Measure.dirac (A.vacant i)).real B + _
    linarith
  have key := abs_integral_sub_le_of_oscillation A hD _ _ (A.singleSiteKernel m h.measurable_weightDensity) K' c
    (fun i => 2 * z i) w h.measurableSet_admissible
    g g' hc.coeff_nonneg hb0 hc.weight_pos hc.kernel_le hbm hc.column_sum_le Kc F hF
  rw [integral_dirac' _ _ hF.measurable.stronglyMeasurable] at key
  refine key.trans (le_of_eq ?_)
  have : ∑ i, w i * (2 * z i) = 2 * ∑ i, w i * z i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  ring
end VacantOffRange
section Ratio
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
  (A : PairConstraint S)
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
      (A.singleSiteKernel m h₂.measurable_weightDensity i σ).real B + 4 * (E - 1) * Z := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.singleSiteKernel_measureReal_le_of_ratio <;> assumption
end Ratio
section Pullback
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {S : I → Type}
  [∀ i, MeasurableSpace (S i)] {T : J → Type} [∀ j, MeasurableSpace (T j)]
  (A : PairConstraint S) {e : J → I}
theorem isActivityBounded_comp_embedConfig (A' : PairConstraint T) {m : ∀ i, Measure (S i)}
    {μ : ∀ j, Measure (T j)}
    (v : ∀ j, T j ≃ᵐ S (e j)) (he : Function.Injective e)
    (hmp : ∀ j, MeasurePreserving (v j) (μ j) (m (e j)))
    (hok : ∀ j j' s t, j ≠ j' → (A'.compatible j j' s t ↔ A.compatible (e j) (e j') (v j s) (v j' t)))
    (hv : ∀ j, v j (A'.vacant j) = A.vacant (e j))
    {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded m G z) :
    A'.IsActivityBounded μ (fun τ => G (A.embedConfig e (fun j => v j) τ)) (fun j => z (e j)) := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.isActivityBounded_pullback <;> assumption
end Pullback
end OscillationComparison
open OscillationComparison in
theorem oscillationComparisonStatement_holds (hD : ComparisonStatement)
    (hC : ActivityConditionalLawsStatement) : oscillationComparisonStatement := by
  classical
  refine ⟨fun I _ _ S _ A m _ G z c w Kc F h hc hF => abs_integral_gibbsLaw_sub_vacant_le A hD hC h hc hF, ?_⟩
  intro I₁ I₂ J _ _ _ _ _ _ S₁ S₂ T _ _ _ A₁ A₂ A m₁ m₁' m₂ m₂' μ _ _ _ _ _ G₁ G₂ z₁ z₂ e₁ e₂ v₁ v₂ c₁ c₂ w₁ w₂
    b E D Kc H₁
    H₂ F₁ F₂ h₁ h₂ he₁ he₂ hH₁ hH₂ hs₁ hs₂ hv₁ hv₂ hok₁ hok₂ hmp₁ hmp₂ hcol₁ hcol₂ hF₁ hF₂ hD0 hDiff hb0 hb
  have d1 := abs_integral_sub_gibbsLaw_vacantOffRange_le A₁ hD hC h₁ hH₁ hcol₁ hs₁ hF₁
  have d2 := abs_integral_sub_gibbsLaw_vacantOffRange_le A₂ hD hC h₂ hH₂ hcol₂ hs₂ hF₂
  have p₁ := isActivityBounded_comp_embedConfig A₁ A v₁ he₁ hmp₁ hok₁ hv₁ h₁
  have p₂ := isActivityBounded_comp_embedConfig A₂ A v₂ he₂ hmp₂ hok₂ hv₂ h₂
  set x₁ := A₁.embedConfig e₁ fun j => v₁ j with hx₁
  set x₂ := A₂.embedConfig e₂ fun j => v₂ j with hx₂
  have hm₁ : Measurable x₁ := measurable_embedConfig A₁ _ he₁ fun j => (v₁ j).measurable
  have hm₂ : Measurable x₂ := measurable_embedConfig A₂ _ he₂ fun j => (v₂ j).measurable
  have hl₁ := map_gibbsLaw_embedConfig A₁ A v₁ he₁ hH₁ hmp₁ hok₁ G₁ h₁.measurable_weightDensity
  have hl₂ := map_gibbsLaw_embedConfig A₂ A v₂ he₂ hH₂ hmp₂ hok₂ G₂ h₂.measurable_weightDensity
  have i₁ : ∫ σ, F₁ σ ∂A₁.gibbsLaw m₁' G₁ = ∫ τ, F₁ (x₁ τ) ∂A.gibbsLaw μ fun τ => G₁ (x₁ τ) := by
    rw [← hl₁, integral_map hm₁.aemeasurable hF₁.measurable.aestronglyMeasurable]
  have i₂ : ∫ σ, F₂ σ ∂A₂.gibbsLaw m₂' G₂ = ∫ τ, F₂ (x₂ τ) ∂A.gibbsLaw μ fun τ => G₂ (x₂ τ) := by
    rw [← hl₂, integral_map hm₂.aemeasurable hF₂.measurable.aestronglyMeasurable]
  obtain ⟨q₁, g₁, pz₁, -⟩ := hC J T A μ _ _ p₁
  obtain ⟨q₂, g₂, pz₂, pl₂⟩ := hC J T A μ _ _ p₂
  haveI := q₁
  haveI := q₂
  have hadm₁ := isAdmissible_embedConfig_iff A₁ A (fun j => v₁ j) he₁ hok₁
  have hker : ∀ j τ B, MeasurableSet B → (A.singleSiteKernel μ p₁.measurable_weightDensity j τ).real B =
      (A₁.singleSiteKernel m₁ h₁.measurable_weightDensity (e₁ j) (x₁ τ)).real ((v₁ j).symm ⁻¹' B) := by
    intro j τ B hB
    have := singleSiteLaw_comp_embedConfig A₁ A (m := m₁) v₁ he₁ hmp₁ hok₁ hv₁ G₁
      h₁.measurable_weightDensity τ j
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
  have hcm : ∀ j j', j ≠ j' → ∀ τ τ', A.IsAdmissible τ → A.IsAdmissible τ' → (∀ k, k ≠ j' → τ k = τ' k) →
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
      have := singleSiteKernel_measureReal_le_of_ratio A p₁ p₂ j hτ hE (le_max_left _ _) (le_max_right _ _) hZ
        (fun s hs => hr τ s hs) hB
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
  have hread : A.OscillationControlled (fun j => w₁ (e₁ j)) Kc fun τ => F₁ (x₁ τ) := by
    obtain ⟨C, hC'⟩ := hF₁.bounded
    refine ⟨hF₁.nonneg, hF₁.measurable.comp hm₁, ⟨C, fun τ => hC' _⟩, ⟨fun j => ?_, ?_⟩⟩
    · exact hF₁.oscillation.1 _
    · intro j τ τ' hτ hτ' hd
      exact hF₁.oscillation.2 (e₁ j) (x₁ τ) (x₁ τ') ((hadm₁ τ).mpr hτ) ((hadm₁ τ').mpr hτ') (hdiff τ τ' j hd)
  have d3 := abs_integral_sub_le_of_oscillation A hD _ _ (A.singleSiteKernel μ p₁.measurable_weightDensity)
    (A.singleSiteKernel μ p₂.measurable_weightDensity) (fun j j' => c₁ (e₁ j) (e₁ j')) b (fun j => w₁ (e₁ j))
    p₁.measurableSet_admissible g₁ g₂ (fun _ _ => hcol₁.coeff_nonneg _ _) hb0 (fun _ => hcol₁.weight_pos _)
    hcm hbm hcol _ _ hread
  set ν := A.gibbsLaw μ fun τ => G₂ (x₂ τ) with hν
  obtain ⟨C₁, hC₁⟩ := hF₁.bounded
  obtain ⟨C₂, hC₂⟩ := hF₂.bounded
  have int₁ : Integrable (fun τ => F₁ (x₁ τ)) ν :=
    (integrable_const C₁).mono' (hF₁.measurable.comp hm₁).aestronglyMeasurable (ae_of_all _ fun τ => hC₁ _)
  have int₂ : Integrable (fun τ => F₂ (x₂ τ)) ν :=
    (integrable_const C₂).mono' (hF₂.measurable.comp hm₂).aestronglyMeasurable (ae_of_all _ fun τ => hC₂ _)
  have hset : ∀ j, MeasurableSet {τ : ∀ j, T j | τ j ≠ A.vacant j} := fun j =>
    ((p₂.measurableSet_vacant j).preimage (measurable_pi_apply j)).compl
  have hsum : ∀ τ : ∀ j, T j, (∑ j, if τ j = A.vacant j then 0 else D j) =
      ∑ j, D j * Set.indicator {τ : ∀ j, T j | τ j ≠ A.vacant j} (1 : (∀ j, T j) → ℝ) τ := by
    intro τ
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : τ j = A.vacant j
    · rw [if_pos hj, Set.indicator_of_notMem (by simpa using hj)]
      simp
    · rw [if_neg hj, Set.indicator_of_mem (by simpa using hj)]
      simp
  have intR : ∀ j, Integrable (fun τ => D j * Set.indicator {τ : ∀ j, T j | τ j ≠ A.vacant j}
      (1 : (∀ j, T j) → ℝ) τ) ν := fun j =>
    ((integrable_const (1 : ℝ)).indicator (hset j)).const_mul _
  have d4 : |∫ τ, F₁ (x₁ τ) ∂ν - ∫ τ, F₂ (x₂ τ) ∂ν| ≤ ∑ j, D j * z₂ (e₂ j) := by
    rw [← integral_sub int₁ int₂]
    refine (abs_integral_le_integral_abs).trans ?_
    have hle : ∫ τ, |F₁ (x₁ τ) - F₂ (x₂ τ)| ∂ν ≤
        ∫ τ, ∑ j, D j * Set.indicator {τ : ∀ j, T j | τ j ≠ A.vacant j} (1 : (∀ j, T j) → ℝ) τ ∂ν := by
      refine integral_mono_ae (int₁.sub int₂).abs (integrable_finset_sum _ fun j _ => intR j) ?_
      filter_upwards [g₂.ae_admissible] with τ hτ
      have := hDiff τ hτ
      rw [hsum τ] at this
      exact this
    refine hle.trans ?_
    rw [integral_finset_sum _ fun j _ => intR j]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [integral_const_mul, integral_indicator_one (hset j)]
    exact mul_le_mul_of_nonneg_left (pl₂ j) (hD0 j)
  rw [← i₁] at d3
  have hi₂ : ∫ σ, F₂ σ ∂A₂.gibbsLaw m₂' G₂ = ∫ τ, F₂ (x₂ τ) ∂ν := i₂
  have tri : ∀ a b c d e : ℝ, |a - e| ≤ |a - b| + |b - c| + |c - d| + |e - d| := by
    intro a b c d e
    have h1 : |a - e| ≤ |a - b| + |b - e| := abs_sub_le a b e
    have h2 : |b - e| ≤ |b - c| + |c - e| := abs_sub_le b c e
    have h3 : |c - e| ≤ |c - d| + |d - e| := abs_sub_le c d e
    have h4 : |d - e| = |e - d| := abs_sub_comm d e
    linarith
  have := tri (∫ σ, F₁ σ ∂A₁.gibbsLaw m₁ G₁) (∫ σ, F₁ σ ∂A₁.gibbsLaw m₁' G₁) (∫ τ, F₁ (x₁ τ) ∂ν)
    (∫ σ, F₂ σ ∂A₂.gibbsLaw m₂' G₂) (∫ σ, F₂ σ ∂A₂.gibbsLaw m₂ G₂)
  rw [hi₂] at this d2
  rw [mul_add, mul_add]
  linarith
end YangMills.Construction.Dobrushin
end
