import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import YangMills.Construction.ResponseInTheExpansion.MeanOfAProductOverSpins
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.Dobrushin
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
theorem PairConstraint.lintegral_singleSiteLaw_le (A : PairConstraint S) (m : ∀ i, Measure (S i))
    [∀ i, SigmaFinite (m i)]
    {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded m G z) {g : ∀ i, S i → ℝ} {e : I → ℝ}
    (hg : ∀ i, Measurable (g i)) (hg1 : ∀ i s, 1 ≤ g i s) (hga : ∀ i, g i (A.vacant i) = 1)
    (he : ∀ i, 0 ≤ e i) (hs : A.HasSmallExcess m G g e) (i : I) (σ : ∀ i, S i) (hσ : A.IsAdmissible σ) :
    ∫⁻ s, ENNReal.ofReal (g i s) ∂(A.singleSiteLaw m G i σ) ≤ ENNReal.ofReal (1 + e i) := by
  classical
  have hd := h.measurable_weightDensity
  have hdm : Measurable fun s => A.weightDensity G (Function.update σ i s) := hd.comp (measurable_update σ)
  have hgm : Measurable fun s => ENNReal.ofReal (g i s) := ENNReal.measurable_ofReal.comp (hg i)
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + e i) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [he i])
  unfold PairConstraint.singleSiteLaw
  split_ifs with hM
  · obtain ⟨hM0, hMt⟩ := hM
    have hsplit : ∀ s, ENNReal.ofReal (g i s) * A.weightDensity G (Function.update σ i s) =
        A.weightDensity G (Function.update σ i s) +
          ENNReal.ofReal (g i s - 1) * A.weightDensity G (Function.update σ i s) := by
      intro s
      have : ENNReal.ofReal (g i s) = 1 + ENNReal.ofReal (g i s - 1) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by linarith [hg1 i s])]
        congr 1
        ring
      rw [this, add_mul, one_mul]
    have hMeq : A.conditionalMass m G i σ = ∫⁻ s, A.weightDensity G (Function.update σ i s) ∂m i := rfl
    have hvac : MeasurableSet ({A.vacant i} : Set (S i)) := h.measurableSet_vacant i
    have hex : ∫⁻ s, ENNReal.ofReal (g i s - 1) * A.weightDensity G (Function.update σ i s) ∂m i ≤
        ENNReal.ofReal (e i) * A.conditionalMass m G i σ := by
      rw [← lintegral_add_compl _ hvac]
      have h0 : ∫⁻ s in {A.vacant i}, ENNReal.ofReal (g i s - 1) *
          A.weightDensity G (Function.update σ i s) ∂m i = 0 := by
        rw [setLIntegral_congr_fun hvac (g := fun _ => 0)]
        · simp
        · intro s hs'
          have : s = A.vacant i := hs'
          simp [this, hga i]
      rw [h0, zero_add]
      refine (hs i σ hσ).trans ?_
      gcongr
      have h1 : A.weightDensity G (Function.update σ i (A.vacant i)) =
          ∫⁻ s in {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i := by
        rw [setLIntegral_congr_fun hvac
          (g := fun _ => A.weightDensity G (Function.update σ i (A.vacant i)))]
        · rw [setLIntegral_const, h.measure_vacant i, mul_one]
        · intro s hs'
          have : s = A.vacant i := hs'
          simp [this]
      rw [h1, hMeq]
      exact setLIntegral_le_lintegral _ _
    have hint : ∫⁻ s, ENNReal.ofReal (g i s) * A.weightDensity G (Function.update σ i s) ∂m i ≤
        A.conditionalMass m G i σ + ENNReal.ofReal (e i) * A.conditionalMass m G i σ := by
      simp_rw [hsplit]
      rw [lintegral_add_left hdm]
      exact add_le_add le_rfl hex
    rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hdm hgm]
    have hmul : (fun s => (fun s => A.weightDensity G (Function.update σ i s)) s * ENNReal.ofReal (g i s)) =
        fun s => ENNReal.ofReal (g i s) * A.weightDensity G (Function.update σ i s) := by
      funext s
      exact mul_comm _ _
    have hmul' : ((fun s => A.weightDensity G (Function.update σ i s)) * fun s => ENNReal.ofReal (g i s)) =
        fun s => ENNReal.ofReal (g i s) * A.weightDensity G (Function.update σ i s) := hmul
    rw [hmul']
    calc (A.conditionalMass m G i σ)⁻¹ •
          ∫⁻ s, ENNReal.ofReal (g i s) * A.weightDensity G (Function.update σ i s) ∂m i
        ≤ (A.conditionalMass m G i σ)⁻¹ *
            (A.conditionalMass m G i σ + ENNReal.ofReal (e i) * A.conditionalMass m G i σ) := by
          rw [smul_eq_mul]
          gcongr
      _ = 1 + ENNReal.ofReal (e i) := by
          rw [mul_add, ENNReal.inv_mul_cancel hM0.ne' hMt, mul_comm (ENNReal.ofReal (e i)), ← mul_assoc,
            ENNReal.inv_mul_cancel hM0.ne' hMt, one_mul]
      _ = ENNReal.ofReal (1 + e i) := by
          rw [ENNReal.ofReal_add (by norm_num) (he i), ENNReal.ofReal_one]
  · rw [lintegral_dirac' _ hgm, hga i, ENNReal.ofReal_one]
    exact hone
theorem ofReal_integral_le_lintegral_of_forall_nonneg {α : Type} [MeasurableSpace α] (μ : Measure α)
    (H : α → ℝ) (hH : ∀ a, 0 ≤ H a) : ENNReal.ofReal (∫ a, H a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (H a) ∂μ := by
  by_cases hi : Integrable H μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hH)]
  · rw [integral_undef hi]
    simp
theorem meanOfProduct_holds (hC : ActivityConditionalLawsStatement) : MeanOfProductStatement := by
  intro I _ _ S _ A m _ G z h g e hg hg1 hga he hs
  classical
  obtain ⟨hp, hGb, -, -⟩ := hC I S A m G z h
  have := hp
  have hgm : ∀ i, Measurable fun σ : (∀ j, S j) => g i (σ i) := fun i => (hg i).comp (measurable_pi_apply i)
  have key : ∀ J : Finset I,
      ∫⁻ σ, ∏ i ∈ J, ENNReal.ofReal (g i (σ i)) ∂(A.gibbsLaw m G) ≤ ENNReal.ofReal (∏ i ∈ J, (1 + e i)) := by
    intro J
    induction J using Finset.induction_on with
    | empty => simp
    | insert i J hi ih =>
      have hfpos : ∀ σ : (∀ j, S j), 0 ≤ ∏ j ∈ J, g j (σ j) := fun σ =>
        Finset.prod_nonneg fun j _ => by linarith [hg1 j (σ j)]
      set f : (∀ j, S j) → ℝ := fun σ => ∏ j ∈ J, g j (σ j) with hf
      have hfm : Measurable f := Finset.measurable_fun_prod _ fun j _ => hgm j
      have hfupd : ∀ (σ : ∀ j, S j) (s : S i), f (Function.update σ i s) = f σ := fun σ s =>
        Finset.prod_congr rfl fun j hj => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
      set Fk : ℕ → (∀ j, S j) → ℝ := fun k σ => min (g i (σ i) * f σ) k with hFk
      have hFkm : ∀ k, Measurable (Fk k) := fun k => ((hgm i).mul hfm).min measurable_const
      have hFk0 : ∀ k σ, 0 ≤ Fk k σ := fun k σ =>
        le_min (mul_nonneg (by linarith [hg1 i (σ i)]) (hfpos σ)) (Nat.cast_nonneg k)
      have hFkb : ∀ k, ∃ C, ∀ σ, |Fk k σ| ≤ C := fun k =>
        ⟨k, fun σ => by rw [abs_of_nonneg (hFk0 k σ)]; exact min_le_right _ _⟩
      have hbound : ∀ k, ∫⁻ σ, ENNReal.ofReal (Fk k σ) ∂(A.gibbsLaw m G) ≤
          ENNReal.ofReal (1 + e i) * ∫⁻ σ, ENNReal.ofReal (f σ) ∂(A.gibbsLaw m G) := by
        intro k
        have hint : Integrable (Fk k) (A.gibbsLaw m G) := by
          obtain ⟨C, hCb⟩ := hFkb k
          exact Integrable.of_bound (hFkm k).aestronglyMeasurable C
            (Filter.Eventually.of_forall fun σ => by simpa using hCb σ)
        rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (hFk0 k))]
        rw [hGb.integral_eq i (Fk k) (hFkm k) (hFkb k)]
        refine (ofReal_integral_le_lintegral_of_forall_nonneg _ _
          fun σ => integral_nonneg fun s => hFk0 k _).trans ?_
        refine le_trans ?_ (le_of_eq (lintegral_const_mul (μ := A.gibbsLaw m G) (ENNReal.ofReal (1 + e i))
          (f := fun σ => ENNReal.ofReal (f σ)) (ENNReal.measurable_ofReal.comp hfm)))
        refine lintegral_mono_ae ?_
        filter_upwards [hGb.ae_admissible] with σ hσ
        refine (ofReal_integral_le_lintegral_of_forall_nonneg _ _ fun s => hFk0 k _).trans ?_
        have hKe : (A.singleSiteKernel m h.measurable_weightDensity i) σ = A.singleSiteLaw m G i σ := rfl
        rw [hKe]
        calc ∫⁻ s, ENNReal.ofReal (Fk k (Function.update σ i s)) ∂(A.singleSiteLaw m G i σ)
            ≤ ∫⁻ s, ENNReal.ofReal (g i s) * ENNReal.ofReal (f σ) ∂(A.singleSiteLaw m G i σ) := by
              refine lintegral_mono fun s => ?_
              rw [← ENNReal.ofReal_mul (by linarith [hg1 i s])]
              refine ENNReal.ofReal_le_ofReal ?_
              have h1 : Fk k (Function.update σ i s) ≤
                  g i ((Function.update σ i s) i) * f (Function.update σ i s) := min_le_left _ _
              rw [Function.update_self, hfupd] at h1
              exact h1
          _ = (∫⁻ s, ENNReal.ofReal (g i s) ∂(A.singleSiteLaw m G i σ)) * ENNReal.ofReal (f σ) :=
              lintegral_mul_const _ (ENNReal.measurable_ofReal.comp (hg i))
          _ ≤ ENNReal.ofReal (1 + e i) * ENNReal.ofReal (f σ) := by
              gcongr
              exact A.lintegral_singleSiteLaw_le m h hg hg1 hga he hs i σ hσ
      have hprodJ : ∀ σ : (∀ j, S j), ∏ j ∈ J, ENNReal.ofReal (g j (σ j)) = ENNReal.ofReal (f σ) := fun σ =>
        (ENNReal.ofReal_prod_of_nonneg fun j _ => by linarith [hg1 j (σ j)]).symm
      have hmono : Monotone fun (k : ℕ) (σ : ∀ j, S j) => ENNReal.ofReal (Fk k σ) := fun k k' hk σ =>
        ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hk))
      calc ∫⁻ σ, ∏ j ∈ insert i J, ENNReal.ofReal (g j (σ j)) ∂(A.gibbsLaw m G)
          ≤ ∫⁻ σ, ⨆ k, ENNReal.ofReal (Fk k σ) ∂(A.gibbsLaw m G) := lintegral_mono fun σ => by
            rw [Finset.prod_insert hi, hprodJ, ← ENNReal.ofReal_mul (by linarith [hg1 i (σ i)])]
            obtain ⟨k, hk⟩ := exists_nat_ge (g i (σ i) * f σ)
            exact le_iSup_of_le k (ENNReal.ofReal_le_ofReal (le_min le_rfl hk))
        _ = ⨆ k, ∫⁻ σ, ENNReal.ofReal (Fk k σ) ∂(A.gibbsLaw m G) :=
            lintegral_iSup (fun k => ENNReal.measurable_ofReal.comp (hFkm k)) hmono
        _ ≤ ENNReal.ofReal (1 + e i) * ∫⁻ σ, ENNReal.ofReal (f σ) ∂(A.gibbsLaw m G) := iSup_le hbound
        _ ≤ ENNReal.ofReal (1 + e i) * ENNReal.ofReal (∏ j ∈ J, (1 + e j)) := by
            gcongr
            simp_rw [← hprodJ]
            exact ih
        _ = ENNReal.ofReal (∏ j ∈ insert i J, (1 + e j)) := by
            rw [Finset.prod_insert hi, ENNReal.ofReal_mul (by linarith [he i])]
  exact key Finset.univ
end YangMills.Construction.Dobrushin
end
