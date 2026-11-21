import YangMills.Construction.FormsOnATorus.FactsOfTheHalfChart
import YangMills.Construction.FormsOnATorus.HaarInTheChartOfAHalfSphere
import YangMills.Construction.FormsOnATorus.HaarOfFieldsInTheChart
import YangMills.Construction.ResponseInTheExpansion.ElementsOfABond
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
open scoped Quaternion ENNReal
namespace YangMills.Construction.GaugeCharts
open BlockAverages TorusFields
private lemma lintegral_fin_pi_prod {E : Type} [MeasurableSpace E] (m : Measure E) [SigmaFinite m] :
    ∀ (n : ℕ) (f : Fin n → E → ℝ≥0∞), (∀ i, Measurable (f i)) →
      ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => m) = ∏ i, ∫⁻ x, f i x ∂m
  | 0, f, _ => by simp
  | n + 1, f, hf => by
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => m) 0).symm
    calc ∫⁻ x : Fin (n + 1) → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => m)
        = ∫⁻ x : E × (Fin n → E), f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)
            ∂(m.prod (Measure.pi fun _ => m)) := by
          rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
          refine lintegral_congr fun x => ?_
          rw [Fin.prod_univ_succ]
          simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
      _ = (∫⁻ x, f 0 x ∂m) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂m := by
          rw [← lintegral_fin_pi_prod m n (fun i : Fin n => f i.succ) (fun i => hf _)]
          exact lintegral_prod_mul (hf 0).aemeasurable
            (Finset.measurable_prod _ fun (i : Fin n) _ => (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂m := by rw [Fin.prod_univ_succ]
private lemma lintegral_fintype_pi_prod {E : Type} [MeasurableSpace E] (m : Measure E) [SigmaFinite m]
    (ι : Type) [Fintype ι] (f : ι → E → ℝ≥0∞) (hf : ∀ b, Measurable (f b)) :
    ∫⁻ x : ι → E, ∏ b, f b (x b) ∂(Measure.pi fun _ => m) = ∏ b, ∫⁻ y, f b y ∂m := by
  let e := (Fintype.equivFin ι).symm
  have hmp := measurePreserving_piCongrLeft (fun _ : ι => m) e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_pi_prod m _ (fun i => f (e i)) (fun i => hf _)
private theorem eq_haarUnit_of_isMulLeftInvariant (μ : Measure UnitQuaternion) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] : μ = haarUnit := by apply _root_.YangMills.Construction.WeightedResponses.eq_haarUnit_of_isMulLeftInvariant <;> assumption
private instance : haarUnit.IsMulRightInvariant := by
  constructor
  intro g
  have : (Measure.map (· * g) haarUnit).IsMulLeftInvariant := isMulLeftInvariant_map_mul_right g
  have : IsProbabilityMeasure (Measure.map (· * g) haarUnit) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact eq_haarUnit_of_isMulLeftInvariant _
theorem haarOnFieldsInHemisphereChart_of_haarOnHemisphereChart (hH : HaarOnHemisphereChart) :
    HaarOnFieldsInHemisphereChart := by
  intro _ _ μ _ ι _ _
  obtain ⟨c₁, hc₁, hH⟩ := hH μ
  refine ⟨c₁ ^ Fintype.card ι, pow_pos hc₁ _, fun V Φ hΦ => ?_⟩
  set ball₁ : Set imaginaryQuaternions := {y : imaginaryQuaternions | ‖y‖ < 1} with hball₁
  have hball₁m : MeasurableSet ball₁ := (isOpen_lt continuous_norm continuous_const).measurableSet
  set ρ₁ : imaginaryQuaternions → ℝ≥0∞ := fun y => ENNReal.ofReal (hemisphereDensity y) with hρ₁
  have hρ₁m : Measurable ρ₁ := by
    refine ENNReal.measurable_ofReal.comp ?_
    have : Continuous fun y : imaginaryQuaternions => 1 - ‖y‖ ^ 2 := by fun_prop
    exact (this.measurable.sqrt).inv
  have hone : ∀ (v : UnitQuaternion) (t : Set UnitQuaternion), MeasurableSet t →
      (haarUnit.restrict {g : UnitQuaternion | 0 < ((g * v⁻¹ : UnitQuaternion) : ℍ[ℝ]).re}) t =
        ENNReal.ofReal c₁ * ∫⁻ y, ({y | y ∈ ball₁ ∧ hemisphereUnit y * v ∈ t} : Set imaginaryQuaternions).indicator ρ₁ y ∂μ := by
    intro v t ht
    have hmv : Measurable fun g : UnitQuaternion => g * v := measurable_mul_const v
    have h1 := hH (fun g => ((fun g : UnitQuaternion => g * v) ⁻¹' t).indicator 1 g) (measurable_one.indicator (hmv ht))
    have hpre : MeasurableSet ((fun g : UnitQuaternion => g * v) ⁻¹' t) := hmv ht
    have hC : MeasurableSet {g : UnitQuaternion | 0 < ((g * v⁻¹ : UnitQuaternion) : ℍ[ℝ]).re} := (isOpen_lt continuous_const
      ((Quaternion.continuous_re).comp (continuous_subtype_val.comp (continuous_id.mul continuous_const)))).measurableSet
    have hl : ∫⁻ g in {g : UnitQuaternion | 0 < (g : ℍ[ℝ]).re}, ((fun g : UnitQuaternion => g * v) ⁻¹' t).indicator 1 g ∂haarUnit =
        (haarUnit.restrict {g : UnitQuaternion | 0 < ((g * v⁻¹ : UnitQuaternion) : ℍ[ℝ]).re}) t := by
      rw [lintegral_indicator_one hpre, Measure.restrict_apply hpre, Measure.restrict_apply ht]
      have hmp := measurePreserving_mul_right haarUnit v
      rw [← hmp.measure_preimage (ht.inter hC).nullMeasurableSet]
      congr 1
      ext g
      simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, mul_inv_cancel_right]
    rw [← hl, h1, ← lintegral_indicator hball₁m]
    congr 1
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ ball₁
    · by_cases ht' : hemisphereUnit y * v ∈ t
      · have h2 : y ∈ ({y | y ∈ ball₁ ∧ hemisphereUnit y * v ∈ t} : Set imaginaryQuaternions) := ⟨hy, ht'⟩
        have h3 : hemisphereUnit y ∈ (fun g : UnitQuaternion => g * v) ⁻¹' t := ht'
        simp [indicator_of_mem hy, indicator_of_mem h2, indicator_of_mem h3, hρ₁]
      · have h2 : y ∉ ({y | y ∈ ball₁ ∧ hemisphereUnit y * v ∈ t} : Set imaginaryQuaternions) := fun h => ht' h.2
        have h3 : hemisphereUnit y ∉ (fun g : UnitQuaternion => g * v) ⁻¹' t := ht'
        simp [indicator_of_mem hy, indicator_of_notMem h2, indicator_of_notMem h3]
    · have h2 : y ∉ ({y | y ∈ ball₁ ∧ hemisphereUnit y * v ∈ t} : Set imaginaryQuaternions) := fun h => hy h.1
      simp [indicator_of_notMem hy, indicator_of_notMem h2]
  set Ball : Set (ι → imaginaryQuaternions) := {y : ι → imaginaryQuaternions | ∀ b, ‖y b‖ < 1} with hBall
  have hBallm : MeasurableSet Ball := by
    have : Ball = univ.pi fun _ => ball₁ := by
      ext y
      simp [hBall, hball₁]
    rw [this]
    exact MeasurableSet.univ_pi fun _ => hball₁m
  set ρ : (ι → imaginaryQuaternions) → ℝ≥0∞ := fun y => ENNReal.ofReal (∏ b, hemisphereDensity (y b)) with hρ
  have hρ_eq : ∀ y, ρ y = ∏ b, ρ₁ (y b) := fun y =>
    ENNReal.ofReal_prod_of_nonneg fun b _ => inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hρm : Measurable ρ := by
    have : ρ = fun y => ∏ b, ρ₁ (y b) := funext hρ_eq
    rw [this]
    exact Finset.measurable_prod _ fun b _ => hρ₁m.comp (measurable_pi_apply b)
  set G : (ι → imaginaryQuaternions) → (ι → UnitQuaternion) := hemisphereChartField V with hG
  have hGm : Measurable G :=
    measurable_pi_lambda _ fun b => (measurable_hemisphereUnit.comp (measurable_pi_apply b)).mul_const _
  set lam : Measure (ι → imaginaryQuaternions) := Measure.pi fun _ : ι => μ with hlam
  set a : ℝ≥0∞ := ENNReal.ofReal (c₁ ^ Fintype.card ι) with ha
  set M : Measure (ι → UnitQuaternion) := a • (((lam.restrict Ball).withDensity ρ).map G) with hM
  have hMeq : (Measure.pi fun _ : ι => haarUnit).restrict
      {w : ι → UnitQuaternion | ∀ b, 0 < ((w b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re} = M := by
    have hC : {w : ι → UnitQuaternion | ∀ b, 0 < ((w b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re} =
        univ.pi fun b => {g : UnitQuaternion | 0 < ((g * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re} := by
      ext w
      simp
    rw [hC, Measure.restrict_pi_pi]
    have key : ∀ s : ι → Set UnitQuaternion, (∀ b, MeasurableSet (s b)) → M (univ.pi s) =
        ∏ b, (haarUnit.restrict {g : UnitQuaternion | 0 < ((g * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re}) (s b) := ?_
    · exact Measure.pi_eq key
    intro s hs
    have hms : MeasurableSet (univ.pi s) := MeasurableSet.univ_pi hs
    have hT : ∀ b, MeasurableSet ({y | y ∈ ball₁ ∧ hemisphereUnit y * V b ∈ s b} : Set imaginaryQuaternions) := fun b =>
      hball₁m.inter ((measurable_hemisphereUnit.mul_const (V b)) (hs b))
    simp only [hone _ _ (hs _)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow hc₁.le, hM,
      Measure.smul_apply, Measure.map_apply hGm hms, withDensity_apply _ (hGm hms),
      Measure.restrict_restrict (hGm hms), smul_eq_mul, ← lintegral_indicator (hGm hms |>.inter hBallm),
      ← lintegral_fintype_pi_prod μ ι _ (fun b => hρ₁m.indicator (hT b))]
    congr 1
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ G ⁻¹' univ.pi s ∩ Ball
    · rw [indicator_of_mem hy, hρ_eq]
      refine Finset.prod_congr rfl fun b _ => ?_
      have : y b ∈ ({y | y ∈ ball₁ ∧ hemisphereUnit y * V b ∈ s b} : Set imaginaryQuaternions) :=
        ⟨hy.2 b, hy.1 b (mem_univ b)⟩
      rw [indicator_of_mem this]
    · rw [indicator_of_notMem hy]
      have : ∃ b, y b ∉ ({y | y ∈ ball₁ ∧ hemisphereUnit y * V b ∈ s b} : Set imaginaryQuaternions) := by
        by_contra hno
        push_neg at hno
        exact hy ⟨fun b _ => (hno b).2, fun b => (hno b).1⟩
      obtain ⟨b, hb⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ b) (indicator_of_notMem hb _)).symm
  calc ∫⁻ w in {w : ι → UnitQuaternion | ∀ b, 0 < ((w b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re}, Φ w
        ∂(Measure.pi fun _ : ι => haarUnit)
      = ∫⁻ w, Φ w ∂M := by rw [hMeq]
    _ = a * ∫⁻ w, Φ w ∂(((lam.restrict Ball).withDensity ρ).map G) := by
        rw [hM, lintegral_smul_measure, smul_eq_mul]
    _ = a * ∫⁻ y, Φ (G y) ∂((lam.restrict Ball).withDensity ρ) := by rw [lintegral_map hΦ hGm]
    _ = a * ∫⁻ y in Ball, Φ (G y) * ρ y ∂lam := by
        congr 1
        refine (lintegral_withDensity_eq_lintegral_mul (lam.restrict Ball) hρm (hΦ.comp hGm)).trans ?_
        refine lintegral_congr fun y => ?_
        simp only [Pi.mul_apply, Function.comp_apply]
        rw [mul_comm]
end YangMills.Construction.GaugeCharts
end
