import YangMills.Construction.ComplexMeasures.UniquenessOfMeasuresAndTheIntegralOfAComplexMeasure
import YangMills.Construction.SpectralTheory.MeasuresIntegralsProductsImagesAndTransportOfAProjectionValuedMeasure
import YangMills.Construction.SpectralTheory.ProductOfTwoCommutingProjectionValuedMeasures
import YangMills.Construction.SpectralTheory.ProjectionValuedMeasureFromScalarMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal CompactlySupported InnerProductSpace
noncomputable section
namespace YangMills.Construction.SpectralProduct
section Cubes
variable {d : ℕ}
def dyadicIndex (j : ℕ) (x : Fin d → ℝ) : Fin d → ℤ := fun i => ⌊(2 : ℝ) ^ j * x i⌋
def dyadicCorner (j : ℕ) (k : Fin d → ℤ) : Fin d → ℝ := fun i => (k i : ℝ) / 2 ^ j
def snapToCorner (j : ℕ) (x : Fin d → ℝ) : Fin d → ℝ := dyadicCorner j (dyadicIndex j x)
theorem measurable_dyadicIndex (j : ℕ) : Measurable (dyadicIndex (d := d) j) :=
  measurable_pi_iff.mpr fun i => Int.measurable_floor.comp ((measurable_pi_apply i).const_mul _)
theorem measurable_snapToCorner (j : ℕ) : Measurable (snapToCorner (d := d) j) := by
  refine measurable_pi_iff.mpr fun i => ?_
  have h : Measurable fun x : Fin d → ℝ => dyadicIndex j x i :=
    (measurable_pi_apply i).comp (measurable_dyadicIndex j)
  have h' : Measurable fun x : Fin d → ℝ => ((dyadicIndex j x i : ℤ) : ℝ) :=
    (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp h
  exact h'.div_const _
theorem dist_snapToCorner_le (j : ℕ) (x : Fin d → ℝ) :
    dist (snapToCorner j x) x ≤ (1 / 2) ^ j := by
  refine (dist_pi_le_iff (by positivity)).mpr fun i => ?_
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have h₁ := Int.floor_le ((2 : ℝ) ^ j * x i)
  have h₂ := Int.lt_floor_add_one ((2 : ℝ) ^ j * x i)
  have hx : snapToCorner j x i - x i = ((⌊(2 : ℝ) ^ j * x i⌋ : ℝ) - 2 ^ j * x i) / 2 ^ j := by
    simp only [snapToCorner, dyadicCorner, dyadicIndex]
    field_simp
  rw [Real.dist_eq, hx, abs_div, abs_of_pos hp, one_div, inv_pow,
    div_le_iff₀ hp, inv_mul_cancel₀ hp.ne']
  rw [abs_le]
  constructor <;> linarith
theorem dyadicIndex_snapToCorner {j j' : ℕ} (h : j ≤ j') (x : Fin d → ℝ) :
    dyadicIndex j (snapToCorner j' x) = dyadicIndex j x := by
  funext i
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  have he : (0 : ℝ) < 2 ^ e := by positivity
  simp only [dyadicIndex, snapToCorner, dyadicCorner]
  have hs : (2 : ℝ) ^ j * ((⌊(2 : ℝ) ^ (j + e) * x i⌋ : ℝ) / 2 ^ (j + e)) =
      (⌊(2 : ℝ) ^ (j + e) * x i⌋ : ℝ) / 2 ^ e := by
    rw [pow_add]
    field_simp
  rw [hs, Int.floor_eq_iff]
  set m := ⌊(2 : ℝ) ^ j * x i⌋ with hm
  have h₁ : (m : ℝ) ≤ 2 ^ j * x i := Int.floor_le _
  have h₂ : 2 ^ j * x i < (m : ℝ) + 1 := Int.lt_floor_add_one _
  have hsplit : (2 : ℝ) ^ (j + e) * x i = 2 ^ e * (2 ^ j * x i) := by rw [pow_add]; ring
  constructor
  · rw [le_div_iff₀ he]
    have : ((m * 2 ^ e : ℤ) : ℝ) ≤ (2 : ℝ) ^ (j + e) * x i := by
      rw [hsplit]
      push_cast
      nlinarith
    have := Int.le_floor.mpr this
    exact_mod_cast this
  · rw [div_lt_iff₀ he]
    have : (2 : ℝ) ^ (j + e) * x i < (((m + 1) * 2 ^ e : ℤ) : ℝ) := by
      rw [hsplit]
      push_cast
      nlinarith
    have := Int.floor_lt.mpr this
    exact_mod_cast this
theorem snapToCorner_snapToCorner {j j' : ℕ} (h : j ≤ j') (x : Fin d → ℝ) :
    snapToCorner j (snapToCorner j' x) = snapToCorner j x := by
  simp only [snapToCorner.eq_def (j := j), dyadicIndex_snapToCorner h]
end Cubes
section SeparateMeasures
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
structure IsSeparateMeasurePair (n : Set A → Measure B) (m : Set B → Measure A) : Prop where
  finiteFst : ∀ S, IsFiniteMeasure (n S)
  finiteSnd : ∀ T, IsFiniteMeasure (m T)
  swap : ∀ S T, MeasurableSet S → MeasurableSet T → m T S = n S T
variable {n : Set A → Measure B} {m : Set B → Measure A}
theorem IsSeparateMeasurePair.map_empty (hb : IsSeparateMeasurePair n m) : n ∅ = 0 := by
  ext T hT
  rw [← hb.swap _ _ MeasurableSet.empty hT]
  simp
theorem IsSeparateMeasurePair.map_iUnion (hb : IsSeparateMeasurePair n m) (f : ℕ → Set A)
    (hf : ∀ k, MeasurableSet (f k)) (hd : Pairwise (Function.onFun Disjoint f)) :
    n (⋃ k, f k) = Measure.sum fun k => n (f k) := by
  ext T hT
  rw [Measure.sum_apply _ hT, ← hb.swap _ _ (MeasurableSet.iUnion hf) hT, measure_iUnion hd hf]
  exact tsum_congr fun k => hb.swap _ _ (hf k) hT
def IsSeparateMeasurePair.weightedMeasure (hb : IsSeparateMeasurePair n m) (F : B → ℝ≥0∞) :
    Measure A :=
  Measure.ofMeasurable (fun S _ => ∫⁻ y, F y ∂n S) (by simp [hb.map_empty])
    (by
      intro f hf hd
      rw [hb.map_iUnion f hf hd, lintegral_sum_measure])
theorem IsSeparateMeasurePair.weightedMeasure_apply (hb : IsSeparateMeasurePair n m)
    (F : B → ℝ≥0∞) {S : Set A} (hS : MeasurableSet S) :
    hb.weightedMeasure F S = ∫⁻ y, F y ∂n S :=
  Measure.ofMeasurable_apply S hS
end SeparateMeasures
section DyadicApprox
variable {a : ℕ} {B : Type*} [MeasurableSpace B]
  {n : Set (Fin a → ℝ) → Measure B} {m : Set B → Measure (Fin a → ℝ)}
def dyadicApprox (n : Set (Fin a → ℝ) → Measure B) (j : ℕ) : Measure ((Fin a → ℝ) × B) :=
  Measure.sum fun k : Fin a → ℤ => (Measure.dirac (dyadicCorner j k)).prod (n (dyadicIndex j ⁻¹' {k}))
theorem measurableSet_dyadicCell (j : ℕ) (k : Fin a → ℤ) : MeasurableSet (dyadicIndex j ⁻¹' {k}) :=
  measurable_dyadicIndex j (measurableSet_singleton k)
theorem lintegral_dyadicApprox (hb : IsSeparateMeasurePair n m) (j : ℕ)
    {F₁ : (Fin a → ℝ) → ℝ≥0∞} {F₂ : B → ℝ≥0∞} (h₁ : Measurable F₁) (h₂ : Measurable F₂) :
    ∫⁻ z, F₁ z.1 * F₂ z.2 ∂dyadicApprox n j =
      ∫⁻ x, F₁ (snapToCorner j x) ∂hb.weightedMeasure F₂ := by
  have hcov : (⋃ k : Fin a → ℤ, dyadicIndex j ⁻¹' {k}) = univ := by
    ext x
    simp
  have hdisj : Pairwise (Function.onFun Disjoint fun k : Fin a → ℤ => dyadicIndex j ⁻¹' {k}) :=
    fun k l hkl => Disjoint.preimage _ (by simpa using hkl)
  rw [dyadicApprox, lintegral_sum_measure, ← setLIntegral_univ, ← hcov,
    lintegral_iUnion (measurableSet_dyadicCell j) hdisj]
  refine tsum_congr fun k => ?_
  have := hb.finiteFst (dyadicIndex j ⁻¹' {k})
  rw [Measure.dirac_prod, lintegral_map (by fun_prop) (by fun_prop)]
  simp only []
  rw [lintegral_const_mul _ h₂]
  have hc : ∀ x ∈ dyadicIndex j ⁻¹' {k}, F₁ (snapToCorner j x) = F₁ (dyadicCorner j k) := by
    intro x hx
    have hx' : dyadicIndex j x = k := hx
    rw [snapToCorner, hx']
  rw [setLIntegral_congr_fun (measurableSet_dyadicCell j k) hc, setLIntegral_const,
    hb.weightedMeasure_apply _ (measurableSet_dyadicCell j k)]
theorem dyadicApprox_prod (hb : IsSeparateMeasurePair n m) (j : ℕ) {S : Set (Fin a → ℝ)}
    {T : Set B} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    dyadicApprox n j (S ×ˢ T) = m T (snapToCorner j ⁻¹' S) := by
  have hS' : MeasurableSet (snapToCorner j ⁻¹' S) := measurable_snapToCorner j hS
  have h := lintegral_dyadicApprox hb j (measurable_one.indicator hS) (measurable_one.indicator hT)
  have e₁ : (fun z : (Fin a → ℝ) × B => S.indicator (1 : (Fin a → ℝ) → ℝ≥0∞) z.1 *
      T.indicator (1 : B → ℝ≥0∞) z.2) = (S ×ˢ T).indicator 1 := by
    funext z
    by_cases h₁ : z.1 ∈ S <;> by_cases h₂ : z.2 ∈ T <;> simp [h₁, h₂, indicator]
  have e₂ : (fun x => S.indicator (1 : (Fin a → ℝ) → ℝ≥0∞) (snapToCorner j x)) =
      (snapToCorner j ⁻¹' S).indicator 1 := by
    funext x
    by_cases h₁ : snapToCorner j x ∈ S <;> simp [h₁, indicator]
  rw [e₁, e₂, lintegral_indicator_one (hS.prod hT), lintegral_indicator_one hS',
    hb.weightedMeasure_apply _ hS', lintegral_indicator_one hT] at h
  rw [h, hb.swap _ _ hS' hT]
theorem dyadicApprox_univ (hb : IsSeparateMeasurePair n m) (j : ℕ) :
    dyadicApprox n j univ = m univ univ := by
  rw [← univ_prod_univ, dyadicApprox_prod hb j MeasurableSet.univ MeasurableSet.univ,
    preimage_univ]
theorem isFiniteMeasure_dyadicApprox (hb : IsSeparateMeasurePair n m) (j : ℕ) :
    IsFiniteMeasure (dyadicApprox n j) := by
  have := hb.finiteSnd univ
  exact ⟨by rw [dyadicApprox_univ hb j]; exact measure_lt_top _ _⟩
theorem map_dyadicApprox (hb : IsSeparateMeasurePair n m) {j j' : ℕ} (h : j ≤ j') :
    (dyadicApprox n j').map (Prod.map (snapToCorner j) id) = dyadicApprox n j := by
  have := isFiniteMeasure_dyadicApprox hb j
  have hm : Measurable (Prod.map (snapToCorner (d := a) j) (id : B → B)) :=
    (measurable_snapToCorner j).prodMap measurable_id
  symm
  refine Measure.ext_prod fun {S T} hS hT => ?_
  have hp : Prod.map (snapToCorner (d := a) j) (id : B → B) ⁻¹' S ×ˢ T =
      (snapToCorner j ⁻¹' S) ×ˢ T := by
    ext z
    simp
  have hq : snapToCorner j' ⁻¹' (snapToCorner (d := a) j ⁻¹' S) = snapToCorner j ⁻¹' S := by
    ext x
    simp [snapToCorner_snapToCorner h]
  rw [Measure.map_apply hm (hS.prod hT), hp, dyadicApprox_prod hb j hS hT,
    dyadicApprox_prod hb j' (measurable_snapToCorner j hS) hT, hq]
end DyadicApprox
section Limit
variable {a b : ℕ} {n : Set (Fin a → ℝ) → Measure (Fin b → ℝ)}
  {m : Set (Fin b → ℝ) → Measure (Fin a → ℝ)}
theorem integrable_of_compactSupport {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (f : C_c(α, ℝ)) :
    Integrable (fun z => f z) μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
theorem cauchySeq_integral_dyadicApprox (hb : IsSeparateMeasurePair n m)
    (f : C_c((Fin a → ℝ) × (Fin b → ℝ), ℝ)) :
    CauchySeq fun j => ∫ z, f z ∂dyadicApprox n j := by
  set W := (m univ).real univ with hWdef
  have hW : ∀ j, (dyadicApprox n j).real univ = W := fun j => by
    simp only [Measure.real, dyadicApprox_univ hb, hWdef]
  have huc : UniformContinuous f :=
    f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
  have hW0 : 0 ≤ W := measureReal_nonneg
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hW1 : 0 < W + 1 := by linarith
  obtain ⟨δ, hδ, hf⟩ := Metric.uniformContinuous_iff.mp huc (ε / (W + 1)) (by positivity)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun j hj => ?_⟩
  have hj' := isFiniteMeasure_dyadicApprox hb j
  have hm : Measurable (Prod.map (snapToCorner (d := a) N) (id : (Fin b → ℝ) → Fin b → ℝ)) :=
    (measurable_snapToCorner N).prodMap measurable_id
  have hmap := map_dyadicApprox hb hj
  have hi₁ : Integrable (fun z => f z) (dyadicApprox n j) := integrable_of_compactSupport _ f
  have hi₂ : Integrable (fun z => f (Prod.map (snapToCorner N) id z)) (dyadicApprox n j) := by
    have hN' := isFiniteMeasure_dyadicApprox hb N
    have : Integrable (fun z => f z) ((dyadicApprox n j).map (Prod.map (snapToCorner N) id)) := by
      rw [hmap]
      exact integrable_of_compactSupport _ f
    exact this.comp_measurable hm
  have e : ∫ z, f z ∂dyadicApprox n N =
      ∫ z, f (Prod.map (snapToCorner N) id z) ∂dyadicApprox n j := by
    have hc : Continuous fun z => f z := f.continuous
    rw [← hmap]
    exact integral_map hm.aemeasurable hc.aestronglyMeasurable
  rw [Real.dist_eq, e, ← integral_sub hi₁ hi₂, ← Real.norm_eq_abs]
  have hbound : ∀ᵐ z ∂dyadicApprox n j,
      ‖f z - f (Prod.map (snapToCorner N) id z)‖ ≤ ε / (W + 1) := by
    refine ae_of_all _ fun z => ?_
    have hd : dist z (Prod.map (snapToCorner N) id z) < δ := by
      rw [Prod.dist_eq]
      refine max_lt ?_ (by simpa using hδ)
      rw [dist_comm]
      exact (dist_snapToCorner_le N z.1).trans_lt hN
    rw [← dist_eq_norm]
    exact (hf hd).le
  have h := norm_integral_le_of_norm_le_const hbound
  rw [hW] at h
  refine h.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ hW1]
  nlinarith
theorem tendsto_integral_dyadicApprox (hb : IsSeparateMeasurePair n m)
    (f : C_c((Fin a → ℝ) × (Fin b → ℝ), ℝ)) :
    Tendsto (fun j => ∫ z, f z ∂dyadicApprox n j) atTop
      (𝓝 (limUnder atTop fun j => ∫ z, f z ∂dyadicApprox n j)) := by
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (cauchySeq_integral_dyadicApprox hb f)
  rw [hl.limUnder_eq]
  exact hl
def limitFunctional (hb : IsSeparateMeasurePair n m) :
    C_c((Fin a → ℝ) × (Fin b → ℝ), ℝ) →ₗ[ℝ] ℝ where
  toFun f := limUnder atTop fun j => ∫ z, f z ∂dyadicApprox n j
  map_add' f g := by
    refine tendsto_nhds_unique (tendsto_integral_dyadicApprox hb (f + g)) ?_
    refine ((tendsto_integral_dyadicApprox hb f).add
      (tendsto_integral_dyadicApprox hb g)).congr fun j => ?_
    have := isFiniteMeasure_dyadicApprox hb j
    rw [← integral_add (integrable_of_compactSupport _ f) (integrable_of_compactSupport _ g)]
    rfl
  map_smul' c f := by
    refine tendsto_nhds_unique (tendsto_integral_dyadicApprox hb (c • f)) ?_
    refine ((tendsto_integral_dyadicApprox hb f).const_smul c).congr fun j => ?_
    rw [← integral_smul]
    rfl
def limitPositiveFunctional (hb : IsSeparateMeasurePair n m) :
    C_c((Fin a → ℝ) × (Fin b → ℝ), ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (limitFunctional hb) fun f hf =>
    ge_of_tendsto' (tendsto_integral_dyadicApprox hb f) fun _ =>
      integral_nonneg (CompactlySupportedContinuousMap.le_def.1 hf)
def limitOfApprox (hb : IsSeparateMeasurePair n m) : Measure ((Fin a → ℝ) × (Fin b → ℝ)) :=
  RealRMK.rieszMeasure (limitPositiveFunctional hb)
theorem tendsto_integral_limitOfApprox (hb : IsSeparateMeasurePair n m)
    (f : C_c((Fin a → ℝ) × (Fin b → ℝ), ℝ)) :
    Tendsto (fun j => ∫ z, f z ∂dyadicApprox n j) atTop (𝓝 (∫ z, f z ∂limitOfApprox hb)) := by
  have h := RealRMK.integral_rieszMeasure (limitPositiveFunctional hb) f
  rw [limitOfApprox, h]
  exact tendsto_integral_dyadicApprox hb f
theorem isFiniteMeasure_limitOfApprox (hb : IsSeparateMeasurePair n m) :
    IsFiniteMeasure (limitOfApprox hb) := by
  have hK : ∀ K : Set ((Fin a → ℝ) × (Fin b → ℝ)), IsCompact K →
      limitOfApprox hb K ≤ ENNReal.ofReal ((m univ).real univ) := by
    intro K hK
    obtain ⟨f, hf₁, -, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty
      (disjoint_empty K)
    let f' : C_c((Fin a → ℝ) × (Fin b → ℝ), ℝ) := ⟨f, hfc⟩
    have hle := RealRMK.rieszMeasure_le_of_eq_one (limitPositiveFunctional hb) (f := f')
      (fun x => (hfI x).1) hK (fun x hx => hf₁ hx)
    refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
    refine le_of_tendsto' (tendsto_integral_dyadicApprox hb f') fun j => ?_
    have hj := isFiniteMeasure_dyadicApprox hb j
    have hn : ∀ᵐ z ∂dyadicApprox n j, ‖f' z‖ ≤ 1 := ae_of_all _ fun z => by
      have := hfI z
      change ‖f z‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]
      exact this.2
    have h := norm_integral_le_of_norm_le_const hn
    have hr : (dyadicApprox n j).real univ = (m univ).real univ := by
      simp only [Measure.real, dyadicApprox_univ hb]
    rw [hr, one_mul] at h
    exact (le_abs_self _).trans h
  refine ⟨?_⟩
  have hU : (univ : Set ((Fin a → ℝ) × (Fin b → ℝ))) = ⋃ p : ℕ, Metric.closedBall 0 p :=
    (Metric.iUnion_closedBall_nat 0).symm
  have hmono : Monotone fun p : ℕ =>
      Metric.closedBall (0 : (Fin a → ℝ) × (Fin b → ℝ)) p := fun p q hpq =>
    Metric.closedBall_subset_closedBall (by exact_mod_cast hpq)
  rw [hU, hmono.measure_iUnion]
  exact (iSup_le fun p : ℕ => hK _ (isCompact_closedBall 0 (p : ℝ))).trans_lt
    ENNReal.ofReal_lt_top
def productFunction {f₁ : (Fin a → ℝ) → ℝ} {f₂ : (Fin b → ℝ) → ℝ} (c₁ : Continuous f₁)
    (c₂ : Continuous f₂) (s₁ : HasCompactSupport f₁) (s₂ : HasCompactSupport f₂) :
    C_c((Fin a → ℝ) × (Fin b → ℝ), ℝ) :=
  ⟨⟨fun z => f₁ z.1 * f₂ z.2, by fun_prop⟩, by
    refine HasCompactSupport.intro (IsCompact.prod s₁ s₂) fun z hz => ?_
    simp only [mem_prod, not_and_or] at hz
    rcases hz with hz | hz
    · simp [image_eq_zero_of_notMem_tsupport hz]
    · simp [image_eq_zero_of_notMem_tsupport hz]⟩
theorem integral_eq_lintegral_toReal {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ} (hm : Measurable f) (h0 : ∀ x, 0 ≤ f x) :
    ∫ x, f x ∂μ = (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal :=
  integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hm.aestronglyMeasurable
def IsDeterminedByCompactlySupported : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ μ μ' : Measure (Fin d → ℝ), IsFiniteMeasure μ → IsFiniteMeasure μ' →
    (∀ f : (Fin d → ℝ) → ℝ, Continuous f → HasCompactSupport f → (∀ x, 0 ≤ f x) →
      ∫ x, f x ∂μ = ∫ x, f x ∂μ') → μ = μ'
theorem map_fst_withDensity (hdet : IsDeterminedByCompactlySupported) (ha : 1 ≤ a)
    (hb : IsSeparateMeasurePair n m) {f₂ : (Fin b → ℝ) → ℝ} (c₂ : Continuous f₂)
    (s₂ : HasCompactSupport f₂) (h₂ : ∀ y, 0 ≤ f₂ y) :
    ((limitOfApprox hb).withDensity fun z => ENNReal.ofReal (f₂ z.2)).map Prod.fst =
      hb.weightedMeasure fun y => ENNReal.ofReal (f₂ y) := by
  have hρ := isFiniteMeasure_limitOfApprox hb
  have hfin := hb.finiteFst univ
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (s₂.isCompact_range c₂).isBounded
  have hC' : ∀ y, f₂ y ≤ C := fun y => (le_abs_self _).trans (hC _ (mem_range_self y))
  have hF₂ : Measurable fun y => ENNReal.ofReal (f₂ y) := c₂.measurable.ennreal_ofReal
  have hG₂ : Measurable fun z : (Fin a → ℝ) × (Fin b → ℝ) => ENNReal.ofReal (f₂ z.2) :=
    hF₂.comp measurable_snd
  have hwd : IsFiniteMeasure
      ((limitOfApprox hb).withDensity fun z => ENNReal.ofReal (f₂ z.2)) := by
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ z, ENNReal.ofReal (f₂ z.2) ∂limitOfApprox hb
        ≤ ∫⁻ _, ENNReal.ofReal C ∂limitOfApprox hb :=
          lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hC' _)
      _ < ∞ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hmix : IsFiniteMeasure (hb.weightedMeasure fun y => ENNReal.ofReal (f₂ y)) := by
    refine ⟨?_⟩
    rw [hb.weightedMeasure_apply _ MeasurableSet.univ]
    calc ∫⁻ y, ENNReal.ofReal (f₂ y) ∂n univ
        ≤ ∫⁻ _, ENNReal.ofReal C ∂n univ :=
          lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hC' _)
      _ < ∞ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  refine hdet a ha _ _ (Measure.isFiniteMeasure_map _ _) hmix fun f₁ c₁ s₁ h₁ => ?_
  have hm₁ : Measurable f₁ := c₁.measurable
  have hF₁ : Measurable fun x => ENNReal.ofReal (f₁ x) := hm₁.ennreal_ofReal
  let F := productFunction c₁ c₂ s₁ s₂
  have hF0 : ∀ z, 0 ≤ F z := fun z => mul_nonneg (h₁ _) (h₂ _)
  have hFm : Measurable fun z => F z := F.continuous.measurable
  have hofReal : ∀ z, ENNReal.ofReal (F z) =
      ENNReal.ofReal (f₁ z.1) * ENNReal.ofReal (f₂ z.2) := fun z =>
    ENNReal.ofReal_mul (h₁ _)
  have hL : ∫ x, f₁ x ∂((limitOfApprox hb).withDensity fun z => ENNReal.ofReal (f₂ z.2)).map
      Prod.fst = ∫ z, F z ∂limitOfApprox hb := by
    have e := lintegral_withDensity_eq_lintegral_mul (limitOfApprox hb) hG₂
      (hF₁.comp measurable_fst)
    simp only [Function.comp_def] at e
    rw [integral_eq_lintegral_toReal _ hm₁ h₁, integral_eq_lintegral_toReal _ hFm hF0,
      lintegral_map hF₁ measurable_fst, e]
    congr 1
    refine lintegral_congr fun z => ?_
    rw [hofReal, Pi.mul_apply, mul_comm]
  have hj : ∀ j, ∫ z, F z ∂dyadicApprox n j =
      ∫ x, f₁ (snapToCorner j x) ∂hb.weightedMeasure fun y => ENNReal.ofReal (f₂ y) := by
    intro j
    have hq : Measurable fun x => f₁ (snapToCorner j x) := hm₁.comp (measurable_snapToCorner j)
    rw [integral_eq_lintegral_toReal _ hFm hF0, integral_eq_lintegral_toReal _ hq fun x => h₁ _]
    simp only [hofReal]
    rw [lintegral_dyadicApprox hb j hF₁ hF₂]
  have hT₁ := tendsto_integral_limitOfApprox hb F
  have hT₂ : Tendsto (fun j => ∫ x, f₁ (snapToCorner j x) ∂hb.weightedMeasure fun y =>
      ENNReal.ofReal (f₂ y)) atTop
      (𝓝 (∫ x, f₁ x ∂hb.weightedMeasure fun y => ENNReal.ofReal (f₂ y))) := by
    obtain ⟨C₁, hC₁⟩ := isBounded_iff_forall_norm_le.mp (s₁.isCompact_range c₁).isBounded
    refine tendsto_integral_of_dominated_convergence (fun _ => C₁)
      (fun j => (hm₁.comp (measurable_snapToCorner j)).aestronglyMeasurable) (integrable_const _)
      (fun j => ae_of_all _ fun x => hC₁ _ (mem_range_self _)) (ae_of_all _ fun x => ?_)
    refine (c₁.tendsto x).comp ?_
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun j => dist_snapToCorner_le j x)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  rw [hL]
  refine tendsto_nhds_unique hT₁ (hT₂.congr fun j => (hj j).symm)
theorem exists_measure_of_separate (hdet : IsDeterminedByCompactlySupported) (ha : 1 ≤ a)
    (hb' : 1 ≤ b) (hb : IsSeparateMeasurePair n m) :
    ∃ ρ : Measure ((Fin a → ℝ) × (Fin b → ℝ)), IsFiniteMeasure ρ ∧
      ∀ S T, MeasurableSet S → MeasurableSet T → ρ (S ×ˢ T) = n S T := by
  have hρ := isFiniteMeasure_limitOfApprox hb
  refine ⟨limitOfApprox hb, hρ, fun S T hS hT => ?_⟩
  have hfst : MeasurableSet (Prod.fst ⁻¹' S : Set ((Fin a → ℝ) × (Fin b → ℝ))) :=
    measurable_fst hS
  have hν : ((limitOfApprox hb).restrict (Prod.fst ⁻¹' S)).map Prod.snd = n S := by
    have := hb.finiteFst S
    refine hdet b hb' _ _ (Measure.isFiniteMeasure_map _ _) this fun f₂ c₂ s₂ h₂ => ?_
    have hm₂ : Measurable f₂ := c₂.measurable
    have hF₂ : Measurable fun y => ENNReal.ofReal (f₂ y) := hm₂.ennreal_ofReal
    rw [integral_eq_lintegral_toReal _ hm₂ h₂, integral_eq_lintegral_toReal _ hm₂ h₂,
      lintegral_map hF₂ measurable_snd]
    congr 1
    have h := congrArg (fun μ => μ S) (map_fst_withDensity hdet ha hb c₂ s₂ h₂)
    rw [Measure.map_apply measurable_fst hS, withDensity_apply _ hfst,
      hb.weightedMeasure_apply _ hS] at h
    exact h
  rw [← hν, Measure.map_apply measurable_snd hT, Measure.restrict_apply (measurable_snd hT)]
  congr 1
  ext z
  simp [and_comm]
end Limit
section Vector
open YangMills.Construction.BorelSpectral YangMills.Construction.BorelSpectral.SpectralMeasure
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {a b : ℕ}
def toWholeSet {d : ℕ} {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) :
    BorelSubsets (univ : Set (Fin d → ℝ)) :=
  ⟨Subtype.val ⁻¹' S, measurable_subtype_coe hS⟩
open Classical in
def fiberMeasure (E : SpectralMeasure (univ : Set (Fin a → ℝ)) H)
    (F : SpectralMeasure (univ : Set (Fin b → ℝ)) H) (ψ : H) (S : Set (Fin a → ℝ)) :
    Measure (Fin b → ℝ) :=
  if hS : MeasurableSet S then (F.diagMeasure (E (toWholeSet hS) ψ)).map Subtype.val else 0
theorem fiberMeasure_apply (E : SpectralMeasure (univ : Set (Fin a → ℝ)) H)
    (F : SpectralMeasure (univ : Set (Fin b → ℝ)) H) (ψ : H) {S : Set (Fin a → ℝ)}
    {T : Set (Fin b → ℝ)} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    fiberMeasure E F ψ S T =
      ENNReal.ofReal (‖F (toWholeSet hT) (E (toWholeSet hS) ψ)‖ ^ 2) := by
  rw [fiberMeasure, dif_pos hS, Measure.map_apply measurable_subtype_coe hT]
  exact F.diagMeasure_apply _ (toWholeSet hT)
theorem isFiniteMeasure_fiberMeasure (E : SpectralMeasure (univ : Set (Fin a → ℝ)) H)
    (F : SpectralMeasure (univ : Set (Fin b → ℝ)) H) (ψ : H) (S : Set (Fin a → ℝ)) :
    IsFiniteMeasure (fiberMeasure E F ψ S) := by
  rw [fiberMeasure]
  split_ifs
  · exact Measure.isFiniteMeasure_map _ _
  · infer_instance
theorem isSeparateMeasurePair_fiberMeasure {E₁ : SpectralMeasure (univ : Set (Fin a → ℝ)) H}
    {E₂ : SpectralMeasure (univ : Set (Fin b → ℝ)) H} (hc : E₁.Commutes E₂) (ψ : H) :
    IsSeparateMeasurePair (fiberMeasure E₁ E₂ ψ) (fiberMeasure E₂ E₁ ψ) where
  finiteFst := isFiniteMeasure_fiberMeasure E₁ E₂ ψ
  finiteSnd := isFiniteMeasure_fiberMeasure E₂ E₁ ψ
  swap S T hS hT := by
    rw [fiberMeasure_apply _ _ _ hT hS, fiberMeasure_apply _ _ _ hS hT]
    have h : E₁ (toWholeSet hS) * E₂ (toWholeSet hT) = E₂ (toWholeSet hT) * E₁ (toWholeSet hS) :=
      (hc _ _).eq
    have h' : E₁ (toWholeSet hS) (E₂ (toWholeSet hT) ψ) =
        E₂ (toWholeSet hT) (E₁ (toWholeSet hS) ψ) :=
      congrArg (fun T : H →L[ℂ] H => T ψ) h
    rw [h']
def concatCoords (z : (Fin a → ℝ) × (Fin b → ℝ)) : (univ : Set (Fin (a + b) → ℝ)) :=
  ⟨Fin.append z.1 z.2, mem_univ _⟩
theorem measurable_concatCoords : Measurable (concatCoords (a := a) (b := b)) := by
  refine Measurable.subtype_mk (measurable_pi_iff.mpr fun i => ?_)
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact (measurable_pi_apply i).comp measurable_fst
  | right i =>
    simp only [Fin.append_right]
    exact (measurable_pi_apply i).comp measurable_snd
theorem leftCoords_concatCoords (z : (Fin a → ℝ) × (Fin b → ℝ)) :
    leftCoords (concatCoords z) = ⟨z.1, mem_univ _⟩ :=
  Subtype.ext (funext fun i => Fin.append_left _ _ i)
theorem rightCoords_concatCoords (z : (Fin a → ℝ) × (Fin b → ℝ)) :
    rightCoords (concatCoords z) = ⟨z.2, mem_univ _⟩ :=
  Subtype.ext (funext fun i => Fin.append_right _ _ i)
theorem concatCoords_leftCoords_rightCoords (y : (univ : Set (Fin (a + b) → ℝ))) :
    concatCoords ((leftCoords y).1, (rightCoords y).1) = y :=
  Subtype.ext Fin.append_castAdd_natAdd
def fromWholeSet {d : ℕ} (Δ : BorelSubsets (univ : Set (Fin d → ℝ))) : Set (Fin d → ℝ) :=
  (fun x => (⟨x, mem_univ x⟩ : (univ : Set (Fin d → ℝ)))) ⁻¹' Δ.1
theorem measurableSet_fromWholeSet {d : ℕ} (Δ : BorelSubsets (univ : Set (Fin d → ℝ))) :
    MeasurableSet (fromWholeSet Δ) :=
  (measurable_id.subtype_mk) Δ.2
theorem toWholeSet_fromWholeSet {d : ℕ} (Δ : BorelSubsets (univ : Set (Fin d → ℝ))) :
    toWholeSet (measurableSet_fromWholeSet Δ) = Δ :=
  Subtype.ext rfl
theorem exists_diagonalMeasure (hdet : IsDeterminedByCompactlySupported)
    {E₁ : SpectralMeasure (univ : Set (Fin a → ℝ)) H}
    {E₂ : SpectralMeasure (univ : Set (Fin b → ℝ)) H} (hc : E₁.Commutes E₂) (ψ : H) :
    ∃ ρ : Measure (univ : Set (Fin (a + b) → ℝ)), IsFiniteMeasure ρ ∧ ∀ Δ₁ Δ₂,
      ρ (boxSet Δ₁ Δ₂).1 = ENNReal.ofReal (‖E₁ Δ₁ (E₂ Δ₂ ψ)‖ ^ 2) := by
  obtain ⟨ρ, hfin, hρ⟩ := exists_measure_of_separate hdet E₁.one_le_dimension
    E₂.one_le_dimension (isSeparateMeasurePair_fiberMeasure hc ψ)
  refine ⟨ρ.map concatCoords, Measure.isFiniteMeasure_map _ _, fun Δ₁ Δ₂ => ?_⟩
  have hpre : concatCoords ⁻¹' (boxSet Δ₁ Δ₂).1 = fromWholeSet Δ₁ ×ˢ fromWholeSet Δ₂ := by
    ext z
    simp only [boxSet, mem_inter_iff, mem_preimage, leftCoords_concatCoords,
      rightCoords_concatCoords, mem_prod, fromWholeSet]
  rw [Measure.map_apply measurable_concatCoords (boxSet Δ₁ Δ₂).2, hpre,
    hρ _ _ (measurableSet_fromWholeSet Δ₁) (measurableSet_fromWholeSet Δ₂),
    fiberMeasure_apply _ _ _ (measurableSet_fromWholeSet Δ₁) (measurableSet_fromWholeSet Δ₂),
    toWholeSet_fromWholeSet, toWholeSet_fromWholeSet]
  have h : E₁ Δ₁ * E₂ Δ₂ = E₂ Δ₂ * E₁ Δ₁ := (hc _ _).eq
  have h' : E₁ Δ₁ (E₂ Δ₂ ψ) = E₂ Δ₂ (E₁ Δ₁ ψ) := congrArg (fun T : H →L[ℂ] H => T ψ) h
  rw [h']
theorem isStarProjection_mul_of_commute {P Q : H →L[ℂ] H} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (hc : Commute P Q) : IsStarProjection (P * Q) where
  isIdempotentElem := by
    change P * Q * (P * Q) = P * Q
    rw [hc.symm.mul_mul_mul_comm, hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]
  isSelfAdjoint := by
    rw [isSelfAdjoint_iff, star_mul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq]
    exact hc.symm.eq
theorem inner_self_apply_of_isStarProjection {T : H →L[ℂ] H} (hT : IsStarProjection T)
    (ψ : H) : ⟪ψ, T ψ⟫_ℂ = ((‖T ψ‖ ^ 2 : ℝ) : ℂ) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT.isSelfAdjoint
  have hi : T (T ψ) = T ψ :=
    congrArg (fun S : H →L[ℂ] H => S ψ) hT.isIdempotentElem.eq
  have h₁ : ⟪ψ, T ψ⟫_ℂ = ⟪T ψ, T ψ⟫_ℂ := by
    have := hs ψ (T ψ)
    simp only [ContinuousLinearMap.coe_coe, hi] at this
    exact this.symm
  rw [h₁, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
end Vector
section Boxes
open YangMills.Construction.BorelSpectral YangMills.Construction.BorelSpectral.SpectralMeasure
open YangMills.Construction.SpectralFromScalar YangMills.Construction.MeasureUniqueness
open YangMills.Construction.SetFunctions (CountablyAdditiveFn MeasurableSets)
open scoped ComplexConjugate
variable {a b : ℕ}
abbrev FullSpace (a b : ℕ) : Type := (univ : Set (Fin (a + b) → ℝ))
def boxIndicators (a b : ℕ) : Set (FullSpace a b → ℂ) :=
  {g | ∃ Δ₁ Δ₂, g = (boxSet (n₁ := a) (n₂ := b) Δ₁ Δ₂).1.indicator 1}
theorem allBoundedMeasurable_boxIndicators : AllBoundedMeasurable (boxIndicators a b) := by
  rintro g ⟨Δ₁, Δ₂, rfl⟩
  refine ⟨measurable_one.indicator (boxSet Δ₁ Δ₂).2, 1, fun x => ?_⟩
  by_cases h : x ∈ (boxSet Δ₁ Δ₂).1 <;> simp [h]
def fullSet (d : ℕ) : BorelSubsets (univ : Set (Fin d → ℝ)) := ⟨univ, MeasurableSet.univ⟩
def interSets {d : ℕ} (Δ Δ' : BorelSubsets (univ : Set (Fin d → ℝ))) :
    BorelSubsets (univ : Set (Fin d → ℝ)) :=
  ⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩
theorem boxSet_fullSet : (boxSet (fullSet a) (fullSet b)).1 = univ := by
  ext y
  simp [boxSet, fullSet]
theorem boxIndicator_mul (Δ₁ Δ₁' : BorelSubsets (univ : Set (Fin a → ℝ)))
    (Δ₂ Δ₂' : BorelSubsets (univ : Set (Fin b → ℝ))) :
    (fun x => (boxSet Δ₁ Δ₂).1.indicator (1 : FullSpace a b → ℂ) x *
      (boxSet Δ₁' Δ₂').1.indicator (1 : FullSpace a b → ℂ) x) =
      (boxSet (interSets Δ₁ Δ₁') (interSets Δ₂ Δ₂')).1.indicator 1 := by
  funext x
  have he : x ∈ (boxSet (interSets Δ₁ Δ₁') (interSets Δ₂ Δ₂')).1 ↔
      x ∈ (boxSet Δ₁ Δ₂).1 ∧ x ∈ (boxSet Δ₁' Δ₂').1 := by
    simp only [boxSet, interSets, mem_inter_iff, mem_preimage]
    tauto
  by_cases h : x ∈ (boxSet Δ₁ Δ₂).1 <;> by_cases h' : x ∈ (boxSet Δ₁' Δ₂').1 <;>
    simp [h, h', he, indicator]
theorem conj_boxIndicator (Δ₁ : BorelSubsets (univ : Set (Fin a → ℝ)))
    (Δ₂ : BorelSubsets (univ : Set (Fin b → ℝ))) :
    (fun x => conj ((boxSet Δ₁ Δ₂).1.indicator (1 : FullSpace a b → ℂ) x)) =
      (boxSet Δ₁ Δ₂).1.indicator 1 := by
  funext x
  by_cases h : x ∈ (boxSet Δ₁ Δ₂).1 <;> simp [h]
theorem isConjClosedUnital_boxIndicators : IsConjClosedUnital (boxIndicators a b) where
  contains_one := ⟨fullSet a, fullSet b, by rw [boxSet_fullSet]; simp; rfl⟩
  closed_mul := by
    rintro _ ⟨Δ₁, Δ₂, rfl⟩ _ ⟨Δ₁', Δ₂', rfl⟩
    exact ⟨_, _, boxIndicator_mul Δ₁ Δ₁' Δ₂ Δ₂'⟩
  closed_conj := by
    rintro _ ⟨Δ₁, Δ₂, rfl⟩
    exact ⟨_, _, conj_boxIndicator Δ₁ Δ₂⟩
def splitPair (y : (univ : Set (Fin (a + b) → ℝ))) :
    (k : Fin 2) → (univ : Set (Fin (![a, b] k) → ℝ))
  | 0 => leftCoords y
  | 1 => rightCoords y
theorem measurable_splitPair : Measurable (splitPair (a := a) (b := b)) :=
  measurable_pi_iff.mpr fun k => match k with
    | 0 => measurable_leftCoords
    | 1 => measurable_rightCoords
def joinSplit (p : (k : Fin 2) → (univ : Set (Fin (![a, b] k) → ℝ))) :
    (univ : Set (Fin (a + b) → ℝ)) :=
  concatCoords (((p 0).1 : Fin a → ℝ), ((p 1).1 : Fin b → ℝ))
theorem measurable_joinSplit : Measurable (joinSplit (a := a) (b := b)) := by
  have h₀ : Measurable fun p : (k : Fin 2) → (univ : Set (Fin (![a, b] k) → ℝ)) =>
      ((p 0).1 : Fin a → ℝ) := measurable_subtype_coe.comp (measurable_pi_apply (0 : Fin 2))
  have h₁ : Measurable fun p : (k : Fin 2) → (univ : Set (Fin (![a, b] k) → ℝ)) =>
      ((p 1).1 : Fin b → ℝ) := measurable_subtype_coe.comp (measurable_pi_apply (1 : Fin 2))
  exact measurable_concatCoords.comp (h₀.prodMk h₁)
theorem joinSplit_splitPair (y : (univ : Set (Fin (a + b) → ℝ))) :
    joinSplit (splitPair y) = y :=
  concatCoords_leftCoords_rightCoords y
theorem separates_boxIndicators (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : ZeroOfZeroOnBoxes) (hR : IntegralRulesBounded) :
    SeparatesComplexMeasures (boxIndicators a b) := by
  intro ν hν Δ
  have hn : 1 ≤ a + b := by omega
  have hval : ∀ Δ₁ Δ₂, ν.1 (boxSet Δ₁ Δ₂) = 0 := by
    intro Δ₁ Δ₂
    have hg : IsBoundedMeasurable ((boxSet Δ₁ Δ₂).1.indicator (1 : FullSpace a b → ℂ)) :=
      allBoundedMeasurable_boxIndicators _ ⟨Δ₁, Δ₂, rfl⟩
    have hr := (hR (a + b) (a + b) hn hn univ univ MeasurableSet.univ MeasurableSet.univ ν ν 0 _ _
      id measurable_id _ hg hg hg).integralOf_indicator (boxSet Δ₁ Δ₂)
    rw [← hr]
    exact hν _ ⟨Δ₁, Δ₂, rfl⟩
  let ν' : CountablyAdditiveFn ((k : Fin 2) → (univ : Set (Fin (![a, b] k) → ℝ))) :=
    ⟨SetFunctions.pushforward splitPair measurable_splitPair ν.1, by
      intro A hAd
      have h := ν.2 (fun j => ⟨splitPair ⁻¹' (A j).1, measurable_splitPair (A j).2⟩)
        (fun i j hij => (hAd hij).preimage _)
      have hu : SetFunctions.iUnionSets
          (fun j => (⟨splitPair ⁻¹' (A j).1, measurable_splitPair (A j).2⟩ :
            MeasurableSets _)) =
          ⟨splitPair ⁻¹' (SetFunctions.iUnionSets A).1,
            measurable_splitPair (SetFunctions.iUnionSets A).2⟩ :=
        Subtype.ext (preimage_iUnion (f := splitPair) (s := fun j => (A j).1)).symm
      rw [hu] at h
      exact h⟩
  have hz := hA 2 le_rfl ![a, b] (fun k => match k with | 0 => ha | 1 => hb)
    (fun k => (univ : Set (Fin (![a, b] k) → ℝ))) (fun _ => MeasurableSet.univ) ν' (by
      intro D
      have hset : (⟨splitPair ⁻¹' (univ.pi fun k => (D k).1),
          measurable_splitPair (MeasurableSet.univ_pi fun k => (D k).2)⟩ :
            MeasurableSets (univ : Set (Fin (a + b) → ℝ))) = boxSet (D 0) (D 1) := by
        refine Subtype.ext (Set.ext fun y => ?_)
        constructor
        · intro h
          exact ⟨h 0 (mem_univ _), h 1 (mem_univ _)⟩
        · rintro ⟨h₀, h₁⟩ k -
          match k with
          | 0 => exact h₀
          | 1 => exact h₁
      exact (congrArg ν.1 hset).trans (hval _ _))
  have hd := hz ⟨joinSplit ⁻¹' Δ.1, measurable_joinSplit Δ.2⟩
  have hset : (⟨splitPair ⁻¹' (joinSplit ⁻¹' Δ.1),
      measurable_splitPair (measurable_joinSplit Δ.2)⟩ :
        MeasurableSets (univ : Set (Fin (a + b) → ℝ))) = Δ := by
    refine Subtype.ext (Set.ext fun y => ?_)
    simp only [mem_preimage, joinSplit_splitPair]
  exact (congrArg ν.1 hset).symm.trans hd
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def boxOperator (E₁ : SpectralMeasure (univ : Set (Fin a → ℝ)) H)
    (E₂ : SpectralMeasure (univ : Set (Fin b → ℝ)) H) (g : boxIndicators a b) : H →L[ℂ] H :=
  E₁ g.2.choose * E₂ g.2.choose_spec.choose
theorem isStarProjection_boxProduct {E₁ : SpectralMeasure (univ : Set (Fin a → ℝ)) H}
    {E₂ : SpectralMeasure (univ : Set (Fin b → ℝ)) H} (hc : E₁.Commutes E₂)
    (Δ₁ : BorelSubsets (univ : Set (Fin a → ℝ))) (Δ₂ : BorelSubsets (univ : Set (Fin b → ℝ))) :
    IsStarProjection (E₁ Δ₁ * E₂ Δ₂) :=
  isStarProjection_mul_of_commute (E₁.isStarProjection _) (E₂.isStarProjection _) (hc _ _)
theorem mul_eq_of_boxSet_eq (hdet : IsDeterminedByCompactlySupported)
    {E₁ : SpectralMeasure (univ : Set (Fin a → ℝ)) H}
    {E₂ : SpectralMeasure (univ : Set (Fin b → ℝ)) H} (hc : E₁.Commutes E₂)
    {Δ₁ Δ₁' : BorelSubsets (univ : Set (Fin a → ℝ))}
    {Δ₂ Δ₂' : BorelSubsets (univ : Set (Fin b → ℝ))}
    (h : (boxSet Δ₁ Δ₂).1 = (boxSet Δ₁' Δ₂').1) :
    E₁ Δ₁ * E₂ Δ₂ = E₁ Δ₁' * E₂ Δ₂' := by
  have hn : ∀ ψ, ‖E₁ Δ₁ (E₂ Δ₂ ψ)‖ = ‖E₁ Δ₁' (E₂ Δ₂' ψ)‖ := by
    intro ψ
    obtain ⟨ρ, -, hρ⟩ := exists_diagonalMeasure hdet hc ψ
    have e := (hρ Δ₁ Δ₂).symm.trans ((congrArg ρ h).trans (hρ Δ₁' Δ₂'))
    have e' := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).mp e
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp e'
  have hi : ∀ ψ, ⟪ψ, (E₁ Δ₁ * E₂ Δ₂) ψ⟫_ℂ = ⟪ψ, (E₁ Δ₁' * E₂ Δ₂') ψ⟫_ℂ := by
    intro ψ
    rw [inner_self_apply_of_isStarProjection (isStarProjection_boxProduct hc Δ₁ Δ₂),
      inner_self_apply_of_isStarProjection (isStarProjection_boxProduct hc Δ₁' Δ₂')]
    exact congrArg (fun r : ℝ => ((r ^ 2 : ℝ) : ℂ)) (hn ψ)
  have hL := (ext_inner_map ((E₁ Δ₁ * E₂ Δ₂ : H →L[ℂ] H) : H →ₗ[ℂ] H)
    ((E₁ Δ₁' * E₂ Δ₂' : H →L[ℂ] H) : H →ₗ[ℂ] H)).mp fun ψ => by
      have := congrArg (starRingEnd ℂ) (hi ψ)
      simpa only [inner_conj_symm, ContinuousLinearMap.coe_coe] using this
  exact ContinuousLinearMap.coe_injective hL
theorem boxOperator_eq (hdet : IsDeterminedByCompactlySupported)
    {E₁ : SpectralMeasure (univ : Set (Fin a → ℝ)) H}
    {E₂ : SpectralMeasure (univ : Set (Fin b → ℝ)) H} (hc : E₁.Commutes E₂)
    (g : boxIndicators a b) {Δ₁ : BorelSubsets (univ : Set (Fin a → ℝ))}
    {Δ₂ : BorelSubsets (univ : Set (Fin b → ℝ))}
    (hg : g.1 = (boxSet Δ₁ Δ₂).1.indicator 1) :
    boxOperator E₁ E₂ g = E₁ Δ₁ * E₂ Δ₂ := by
  have hs := g.2.choose_spec.choose_spec
  exact (mul_eq_of_boxSet_eq hdet hc (Set.indicator_one_inj ℂ (hg.symm.trans hs))).symm
theorem isStarHomOn_boxOperator (hdet : IsDeterminedByCompactlySupported)
    {E₁ : SpectralMeasure (univ : Set (Fin a → ℝ)) H}
    {E₂ : SpectralMeasure (univ : Set (Fin b → ℝ)) H} (hc : E₁.Commutes E₂) :
    IsStarHomOn isConjClosedUnital_boxIndicators (boxOperator E₁ E₂) where
  preserves_one := by
    have hg : (fun _ : FullSpace a b => (1 : ℂ)) =
        (boxSet (fullSet a) (fullSet b)).1.indicator 1 := by
      rw [boxSet_fullSet]
      simp
      rfl
    rw [boxOperator_eq hdet hc _ hg]
    have h₁ : E₁ (fullSet a) = 1 := E₁.map_univ
    have h₂ : E₂ (fullSet b) = 1 := E₂.map_univ
    rw [h₁, h₂, one_mul]
  preserves_mul := by
    rintro ⟨_, Δ₁, Δ₂, rfl⟩ ⟨_, Δ₁', Δ₂', rfl⟩
    rw [boxOperator_eq hdet hc _ (boxIndicator_mul Δ₁ Δ₁' Δ₂ Δ₂'),
      boxOperator_eq hdet hc ⟨_, Δ₁, Δ₂, rfl⟩ rfl,
      boxOperator_eq hdet hc ⟨_, Δ₁', Δ₂', rfl⟩ rfl]
    have h₁ : E₁ (interSets Δ₁ Δ₁') = E₁ Δ₁ * E₁ Δ₁' := E₁.map_inter _ _
    have h₂ : E₂ (interSets Δ₂ Δ₂') = E₂ Δ₂ * E₂ Δ₂' := E₂.map_inter _ _
    rw [h₁, h₂]
    exact (hc Δ₁' Δ₂).mul_mul_mul_comm (E₁ Δ₁) (E₂ Δ₂')
  preserves_adjoint := by
    rintro ⟨_, Δ₁, Δ₂, rfl⟩ φ ψ
    have e := boxOperator_eq hdet hc
      ⟨_, isConjClosedUnital_boxIndicators.closed_conj _ ⟨Δ₁, Δ₂, rfl⟩⟩ (conj_boxIndicator Δ₁ Δ₂)
    rw [e, boxOperator_eq hdet hc ⟨_, Δ₁, Δ₂, rfl⟩ rfl]
    have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isStarProjection_boxProduct hc Δ₁ Δ₂).isSelfAdjoint
    exact (hs φ ψ).symm
theorem inner_boxProduct_eq_integral {E₁ : SpectralMeasure (univ : Set (Fin a → ℝ)) H}
    {E₂ : SpectralMeasure (univ : Set (Fin b → ℝ)) H} (hc : E₁.Commutes E₂)
    {ψ : H} {ρ : Measure (FullSpace a b)} [IsFiniteMeasure ρ]
    (hρ : ∀ Δ₁ Δ₂, ρ (boxSet Δ₁ Δ₂).1 = ENNReal.ofReal (‖E₁ Δ₁ (E₂ Δ₂ ψ)‖ ^ 2))
    (Δ₁ : BorelSubsets (univ : Set (Fin a → ℝ))) (Δ₂ : BorelSubsets (univ : Set (Fin b → ℝ))) :
    ⟪ψ, (E₁ Δ₁ * E₂ Δ₂) ψ⟫_ℂ =
      ∫ x, (boxSet Δ₁ Δ₂).1.indicator (1 : FullSpace a b → ℂ) x ∂ρ := by
  rw [inner_self_apply_of_isStarProjection (isStarProjection_boxProduct hc Δ₁ Δ₂)]
  have e : (boxSet Δ₁ Δ₂).1.indicator (1 : FullSpace a b → ℂ) =
      (boxSet Δ₁ Δ₂).1.indicator fun _ => (1 : ℂ) := rfl
  rw [e, integral_indicator_const _ (boxSet Δ₁ Δ₂).2, Measure.real, hρ,
    ENNReal.toReal_ofReal (by positivity)]
  simp
end Boxes
open YangMills.Construction.BorelSpectral YangMills.Construction.BorelSpectral.SpectralMeasure
open YangMills.Construction.SpectralFromScalar YangMills.Construction.MeasureUniqueness
theorem productTheorem_holds (hcalc : SpectralMeasureCalculus.CalculusTheorem)
    (hmeas : MeasureUniqueness.UniquenessAndIntegral)
    (hbuild : SpectralFromScalar.ScalarDeterminationTheorem) : ProductTheorem := by
  intro H _ _ _ n₁ n₂ E₁ E₂ hc
  have hdet : IsDeterminedByCompactlySupported := fun d hd μ μ' hμ hμ' h =>
    hmeas.2.1 d hd μ μ' hμ hμ' fun f hf h₀ => h f hf.1 hf.2 h₀
  have h₁ := E₁.one_le_dimension
  have h₂ := E₂.one_le_dimension
  have hn : 1 ≤ n₁ + n₂ := by omega
  obtain ⟨hA, hB, hC⟩ := hbuild H (n₁ + n₂) hn univ MeasurableSet.univ ⟨0, mem_univ _⟩
    (boxIndicators n₁ n₂) allBoundedMeasurable_boxIndicators
    (separates_boxIndicators h₁ h₂ hmeas.1 hmeas.2.2.2.2.2.1)
  have hind : ∀ (E : SpectralMeasure (univ : Set (Fin (n₁ + n₂) → ℝ)) H) Δ,
      E.integralOp (Δ.1.indicator 1) = E Δ := fun E Δ =>
    (hcalc H (n₁ + n₂) univ E).2.1.indicator Δ
  choose ρ hfin hρ using fun ψ => exists_diagonalMeasure hdet hc ψ
  have hscal : HasDiagonalMeasures (boxOperator E₁ E₂) ρ := by
    intro ψ
    refine ⟨hfin ψ, ?_⟩
    rintro ⟨_, Δ₁, Δ₂, rfl⟩
    have := hfin ψ
    rw [boxOperator_eq hdet hc ⟨_, Δ₁, Δ₂, rfl⟩ rfl]
    exact inner_boxProduct_eq_integral hc (hρ ψ) Δ₁ Δ₂
  obtain ⟨⟨E, hE, huniq⟩, -⟩ := hC isConjClosedUnital_boxIndicators (boxOperator E₁ E₂) ρ
    (isStarHomOn_boxOperator hdet hc) hscal
  have hto : ∀ E' : SpectralMeasure (univ : Set (Fin (n₁ + n₂) → ℝ)) H,
      IsProductMeasure E' E₁ E₂ → ∀ g : boxIndicators n₁ n₂,
        boxOperator E₁ E₂ g = E'.integralOp g := by
    rintro E' hE' ⟨_, Δ₁, Δ₂, rfl⟩
    rw [boxOperator_eq hdet hc ⟨_, Δ₁, Δ₂, rfl⟩ rfl, ← hE' Δ₁ Δ₂]
    exact (hind E' _).symm
  have hof : IsProductMeasure E E₁ E₂ := by
    intro Δ₁ Δ₂
    have h := hE ⟨_, Δ₁, Δ₂, rfl⟩
    rw [boxOperator_eq hdet hc ⟨_, Δ₁, Δ₂, rfl⟩ rfl] at h
    exact ((hind E _).symm.trans h.symm)
  refine ⟨⟨E, hof, fun E' hE' => huniq E' (hto E' hE')⟩, ?_⟩
  intro E' hE' B hB₁ hB₂
  refine hB E' B ?_
  rintro _ ⟨Δ₁, Δ₂, rfl⟩
  rw [hind E', hE' Δ₁ Δ₂]
  exact (hB₁ Δ₁).mul_right (hB₂ Δ₂)
end YangMills.Construction.SpectralProduct
