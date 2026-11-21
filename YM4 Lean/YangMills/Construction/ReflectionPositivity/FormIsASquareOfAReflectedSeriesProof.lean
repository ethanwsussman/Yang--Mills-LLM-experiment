import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusOfAnyShape
import YangMills.Construction.ReflectionPositivity.ActionOfASplitTorusSplits
import YangMills.Construction.ReflectionPositivity.FormIsASquareOfAReflectedSeries
import YangMills.Construction.ReflectionPositivity.IntegralOverTheTwoHalvesFactors
import YangMills.Construction.ReflectionPositivity.IntegralOverVariablesOfATorus
import YangMills.Construction.ReflectionPositivity.OneReflectionTwoMirrorsAndWhatTheyCut
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open NormalFamilies
namespace PairingSquare
section Generic
variable {Ω C : Type} [MeasurableSpace Ω]
theorem integrable_of_measurable_bdd {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℂ} {B : ℝ}
    (hf : Measurable f) (hB : ∀ x, ‖f x‖ ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ hB)
theorem hasSum_integral_mul_of_tendstoUniformly (μ : Measure Ω) [IsFiniteMeasure μ]
    {G K : Ω → ℂ} {T : C → Ω → ℂ}
    {M L : ℝ} (hG : Measurable G) (hGM : ∀ x, ‖G x‖ ≤ M) (hK : Measurable K)
    (hKL : ∀ x, ‖K x‖ ≤ L) (hT : ∀ i, Measurable (T i)) (hTB : ∀ i, ∃ B : ℝ, ∀ x, ‖T i x‖ ≤ B)
    (hu : TendstoUniformly (fun (s : Finset C) x => ∑ i ∈ s, T i x) K atTop) :
    HasSum (fun i => ∫ x, G x * T i x ∂μ) (∫ x, G x * K x ∂μ) := by
  classical
  have hM' : 0 < |M| + 1 := by positivity
  have hGM' : ∀ x, ‖G x‖ ≤ |M| + 1 := fun x =>
    (hGM x).trans ((le_abs_self M).trans (lt_add_one _).le)
  have hGT : ∀ i, Integrable (fun x => G x * T i x) μ := fun i => by
    obtain ⟨B, hB⟩ := hTB i
    refine integrable_of_measurable_bdd (B := (|M| + 1) * |B|) (hG.mul (hT i)) fun x => ?_
    rw [norm_mul]
    exact mul_le_mul (hGM' x) ((hB x).trans (le_abs_self B)) (norm_nonneg _) hM'.le
  have hGK : Integrable (fun x => G x * K x) μ := by
    refine integrable_of_measurable_bdd (B := (|M| + 1) * |L|) (hG.mul hK) fun x => ?_
    rw [norm_mul]
    exact mul_le_mul (hGM' x) ((hKL x).trans (le_abs_self L)) (norm_nonneg _) hM'.le
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_nhds]
  intro ε hε
  have hm : 0 < μ.real Set.univ + 1 := by positivity
  have hδ : 0 < ε / (2 * (|M| + 1) * (μ.real Set.univ + 1)) := by positivity
  filter_upwards [Metric.tendstoUniformly_iff.1 hu _ hδ] with s hs
  have hsum : ∑ i ∈ s, ∫ x, G x * T i x ∂μ = ∫ x, ∑ i ∈ s, G x * T i x ∂μ :=
    (integral_finsetSum s fun i _ => hGT i).symm
  have hint : Integrable (fun x => ∑ i ∈ s, G x * T i x) μ :=
    integrable_finsetSum s fun i _ => hGT i
  rw [dist_eq_norm, hsum, ← integral_sub hint hGK]
  have hpt : ∀ x, ‖(∑ i ∈ s, G x * T i x) - G x * K x‖ ≤
      (|M| + 1) * (ε / (2 * (|M| + 1) * (μ.real Set.univ + 1))) := fun x => by
    have e : (∑ i ∈ s, G x * T i x) - G x * K x = G x * ((∑ i ∈ s, T i x) - K x) := by
      rw [mul_sub, Finset.mul_sum]
    rw [e, norm_mul]
    refine mul_le_mul (hGM' x) ?_ (norm_nonneg _) hM'.le
    have := (hs x).le
    rwa [dist_comm, dist_eq_norm] at this
  have hb := norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ hpt)
  refine hb.trans_lt ?_
  have e2 : (|M| + 1) * (ε / (2 * (|M| + 1) * (μ.real Set.univ + 1))) * μ.real Set.univ =
      ε / 2 * (μ.real Set.univ / (μ.real Set.univ + 1)) := by
    field_simp
  rw [e2]
  have h3 : μ.real Set.univ / (μ.real Set.univ + 1) ≤ 1 := by
    rw [div_le_one hm]; linarith
  nlinarith [half_pos hε]
variable [MeasurableSpace C]
def indexedSumMeasure (α : C → ℝ) (μ : Measure Ω) : Measure (C × Ω) :=
  Measure.sum fun i => ENNReal.ofReal (α i) • μ.map (Prod.mk i)
theorem isFiniteMeasure_indexedSumMeasure {α : C → ℝ} {a : ℝ} (h0 : ∀ i, 0 ≤ α i)
    (ha : HasSum α a) (μ : Measure Ω) [IsFiniteMeasure μ] :
    IsFiniteMeasure (indexedSumMeasure α μ) := by
  refine ⟨?_⟩
  rw [indexedSumMeasure, Measure.sum_apply _ MeasurableSet.univ]
  have h : ∀ i, (ENNReal.ofReal (α i) • μ.map (Prod.mk i)) Set.univ =
      ENNReal.ofReal (α i) * μ Set.univ := fun i => by
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply measurable_prodMk_left MeasurableSet.univ, Set.preimage_univ]
  simp_rw [h]
  rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg h0 ha.summable]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
theorem hasSum_integral_indexedSumMeasure {α : C → ℝ} {a : ℝ} (h0 : ∀ i, 0 ≤ α i)
    (ha : HasSum α a) (μ : Measure Ω) [IsFiniteMeasure μ] {f : C × Ω → ℂ} {B : ℝ}
    (hf : Measurable f) (hB : ∀ x, ‖f x‖ ≤ B) :
    HasSum (fun i => (α i : ℂ) * ∫ U, f (i, U) ∂μ) (∫ x, f x ∂indexedSumMeasure α μ) := by
  have := isFiniteMeasure_indexedSumMeasure h0 ha μ
  have hi : Integrable f (indexedSumMeasure α μ) := integrable_of_measurable_bdd hf hB
  have h := hasSum_integral_measure (f := f)
    (μ := fun i => ENNReal.ofReal (α i) • μ.map (Prod.mk i)) hi
  have e : ∀ i, ∫ x, f x ∂(ENNReal.ofReal (α i) • μ.map (Prod.mk i)) =
      (α i : ℂ) * ∫ U, f (i, U) ∂μ := fun i => by
    rw [integral_smul_measure,
      integral_map measurable_prodMk_left.aemeasurable hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal (h0 i), Complex.real_smul]
  simp_rw [e] at h
  exact h
end Generic
section Quotient
variable (Γ : PeriodSublattice 1)
theorem boundedAlgebra_mono {S S' : Set Γ.QuotientLink} (h : S ⊆ S')
    {F : Γ.QuotientField → ℂ} (hF : F ∈ Γ.boundedAlgebra S) : F ∈ Γ.boundedAlgebra S' := by
  obtain ⟨h1, h2, h3⟩ := Γ.mem_boundedAlgebra.1 hF
  exact Γ.mem_boundedAlgebra.2 ⟨h1, h2, fun U U' hU => h3 U U' fun b hb => hU b (h hb)⟩
theorem norm_le_supNorm {S : Set Γ.QuotientLink} {F : Γ.QuotientField → ℂ}
    (hF : F ∈ Γ.boundedAlgebra S) (U : Γ.QuotientField) :
    ‖F U‖ ≤ PeriodSublattice.supNorm F := by
  obtain ⟨-, ⟨B, hB⟩, -⟩ := Γ.mem_boundedAlgebra.1 hF
  exact le_ciSup (f := fun U => ‖F U‖) ⟨B, by rintro _ ⟨U, rfl⟩; exact hB U⟩ U
theorem norm_exp_neg_mul_le_one {b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) :
    ‖((Real.exp (-b * x) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  nlinarith [mul_nonneg hb hx]
theorem exp_neg_mul_mem_boundedAlgebra {S : Set Γ.QuotientLink} {A : Γ.QuotientField → ℝ}
    (hA : Continuous A) (h0 : ∀ U, 0 ≤ A U) (hd : PeriodSublattice.DependsOnlyOn A S)
    {b : ℝ} (hb : 0 ≤ b) :
    (fun U => ((Real.exp (-b * A U) : ℝ) : ℂ)) ∈ Γ.boundedAlgebra S := by
  refine Γ.mem_boundedAlgebra.2 ⟨?_, ⟨1, fun U => norm_exp_neg_mul_le_one hb (h0 U)⟩, fun U U' h => ?_⟩
  · exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul hA))).measurable
  · simp only [hd U U' h]
theorem continuous_splitFaceWeight (hfin : Γ.QuotientLiftFacts) (β : ℝ) (n : AmbientSpace)
    (z : ℤ) (c : ℝ) : Continuous (Γ.splitFaceWeight β n z c) := by
  classical
  have := hfin.finite_quotientPlaquette
  have := Fintype.ofFinite Γ.QuotientPlaquette
  have h1 : ∀ U, (∑ᶠ (p : Γ.QuotientPlaquette) (_ : Γ.IsSplitPlaquette n z c p),
      Γ.quotientFaceEnergy U p) =
      ∑ p, if Γ.IsSplitPlaquette n z c p then Γ.quotientFaceEnergy U p else 0 := fun U => by
    rw [finsum_eq_sum_of_fintype]
    simp only [finsum_eq_if]
  have h2 : Γ.splitFaceWeight β n z c = fun U => Real.exp (-β *
      ∑ p, if Γ.IsSplitPlaquette n z c p then Γ.quotientFaceEnergy U p else 0) :=
    funext fun U => by rw [PeriodSublattice.splitFaceWeight, h1]
  rw [h2]
  refine Real.continuous_exp.comp (continuous_const.mul ?_)
  refine continuous_finsetSum _ fun p _ => ?_
  by_cases h : Γ.IsSplitPlaquette n z c p
  · simpa [h] using hfin.continuous_quotientFaceEnergy p
  · simpa [h] using continuous_const
theorem norm_splitFaceWeight_le_one (hfin : Γ.QuotientLiftFacts) {β : ℝ} (hβ : 0 ≤ β)
    (n : AmbientSpace) (z : ℤ) (c : ℝ) (U : Γ.QuotientField) :
    ‖((Γ.splitFaceWeight β n z c U : ℝ) : ℂ)‖ ≤ 1 :=
  norm_exp_neg_mul_le_one hβ
    (finsum_nonneg fun p => finsum_nonneg fun _ => (hfin.quotientFaceEnergy_mem_Icc p U).1)
end Quotient
theorem reflectionPairing_isIntegralSquare (hAction : SplitTorusActionSplits)
    (hHalves : HalvesIntegralFactorization)
    (hInt : IntegrateOutProperties)
    (hMirrors : TwoLevelsOfOneReflection)
    (hExt : PeriodicQuotient.FinitenessClaim) :
    ReflectionPairingIsIntegralSquare := by
  intro β hβ Γ n hn z hsplit c hc a P hSer
  obtain ⟨C, hCc, α, H, hα0, hαs, hHmem, hHnorm, -, hHu⟩ := hSer
  have hfin := hExt.1 Γ
  obtain ⟨A₀, Ap, hA₀c, hApc, hA₀0, hAp0, hA₀d, hApd, hW⟩ := hAction Γ n hn z hsplit c hc
  obtain ⟨hz, hMir⟩ := hMirrors Γ n hn z c hc hsplit
  obtain ⟨-, -, -, -, -, -, hTheta, -⟩ := hMir
  have hΘ : ∀ F ∈ Γ.plusAlgebra n z c, Γ.conjReflect P F ∈ Γ.minusAlgebra n z c := by
    intro F hF
    exact show Γ.conjReflect P F ∈
        (Γ.minusAlgebra n z c : Set (Γ.QuotientField → ℂ)) from
      hTheta ▸ Set.mem_image_of_mem _ hF
  have hH := hHalves Γ n hn z hsplit c hc
  obtain ⟨hAv1, hAv2, -⟩ := hInt Γ (Γ.sharedLinks n z c)ᶜ
  obtain ⟨hX1, -, hX3⟩ := hInt Γ (Γ.crossingLinks n z c)
  let _ : MeasurableSpace C := ⊤
  have : DiscreteMeasurableSpace C := ⟨fun _ => trivial⟩
  have hβ0 : 0 ≤ β := hβ.le
  have hPr : IsProbabilityMeasure Γ.quotientHaar := by
    unfold PeriodSublattice.quotientHaar
    infer_instance
  let eE : Γ.QuotientField → ℂ := fun U => ((Real.exp (-β * Ap U) : ℝ) : ℂ)
  let sq : Γ.QuotientField → ℂ := fun U => ((Real.exp (-(β / 2) * A₀ U) : ℝ) : ℂ)
  let w : Γ.QuotientField → ℂ := fun U => ((Real.exp (-β * A₀ U) : ℝ) : ℂ)
  have heE : eE ∈ Γ.plusAlgebra n z c := exp_neg_mul_mem_boundedAlgebra Γ hApc hAp0 hApd hβ0
  have hw : w ∈ Γ.boundedAlgebra (Γ.sharedLinks n z c) :=
    exp_neg_mul_mem_boundedAlgebra Γ hA₀c hA₀0 hA₀d hβ0
  have hsq : sq ∈ Γ.boundedAlgebra (Γ.sharedLinks n z c) :=
    exp_neg_mul_mem_boundedAlgebra Γ hA₀c hA₀0 hA₀d (by positivity)
  have hsqw : ∀ U, sq U * sq U = w U := fun U => by
    simp only [sq, w]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hsqr : ∀ U, conj (sq U) = sq U := fun U => Complex.conj_ofReal _
  have hsq1 : ∀ U, ‖sq U‖ ≤ 1 := fun U => norm_exp_neg_mul_le_one (by positivity) (hA₀0 U)
  have heE1 : ∀ U, ‖eE U‖ ≤ 1 := fun U => norm_exp_neg_mul_le_one hβ0 (hAp0 U)
  have hH1 : ∀ i U, ‖H i U‖ ≤ 1 := fun i U =>
    (norm_le_supNorm Γ (hHmem i) U).trans (hHnorm i)
  let Φ : (Γ.QuotientField → ℂ) → C → Γ.QuotientField → ℂ := fun F i => F * eE * H i
  let Av := Γ.integrateOut (Γ.sharedLinks n z c)ᶜ
  have hΦ : ∀ F ∈ Γ.plusAlgebra n z c, ∀ i, Φ F i ∈ Γ.plusAlgebra n z c := fun F hF i =>
    mul_mem (mul_mem hF heE) (hHmem i)
  have hΦm : ∀ F ∈ Γ.plusAlgebra n z c, ∀ i, Measurable (Φ F i) := fun F hF i =>
    (Γ.mem_boundedAlgebra.1 (hΦ F hF i)).1
  have hΦb : ∀ F ∈ Γ.plusAlgebra n z c, ∀ i U, ‖Φ F i U‖ ≤ PeriodSublattice.supNorm F := by
    intro F hF i U
    have h1 := norm_le_supNorm Γ hF U
    have h0 : 0 ≤ PeriodSublattice.supNorm F := (norm_nonneg _).trans h1
    calc ‖Φ F i U‖ = ‖F U‖ * ‖eE U‖ * ‖H i U‖ := by
          simp only [Φ, Pi.mul_apply, norm_mul]
      _ ≤ PeriodSublattice.supNorm F * 1 * 1 :=
          mul_le_mul (mul_le_mul h1 (heE1 U) (norm_nonneg _) h0) (hH1 i U) (norm_nonneg _)
            (by simpa using h0)
      _ = PeriodSublattice.supNorm F := by ring
  have hAvm : ∀ F ∈ Γ.plusAlgebra n z c, ∀ i, Measurable (Av (Φ F i)) := fun F hF i =>
    (hAv1 _ _ (hΦm F hF i) (hΦb F hF i)).1
  have hAvb : ∀ F ∈ Γ.plusAlgebra n z c, ∀ i U,
      ‖Av (Φ F i) U‖ ≤ PeriodSublattice.supNorm F := fun F hF i =>
    (hAv1 _ _ (hΦm F hF i) (hΦb F hF i)).2.1
  have hAv0 : ∀ U, Γ.integrateOut (Γ.sharedLinks n z c)ᶜ 0 U = 0 := fun U => by
    simp [PeriodSublattice.integrateOut]
  let Ψ : ↥(Γ.plusAlgebra n z c) →ₗ[ℂ] (C × Γ.QuotientField → ℂ) :=
    { toFun := fun F x => sq x.2 * Av (Φ F.1 x.1) x.2
      map_add' := by
        intro F G
        funext x
        have e : Φ (F + G).1 x.1 = (1 : ℂ) • Φ F.1 x.1 + Φ G.1 x.1 := by
          funext U
          simp only [Φ, Pi.add_apply, Pi.mul_apply, Subalgebra.coe_add, one_smul]
          ring
        have h := hAv2 (Φ F.1 x.1) (Φ G.1 x.1)
          (max (PeriodSublattice.supNorm F.1) (PeriodSublattice.supNorm G.1)) 1
          (hΦm _ F.2 _) (hΦm _ G.2 _)
          (fun U => (hΦb _ F.2 _ U).trans (le_max_left _ _))
          (fun U => (hΦb _ G.2 _ U).trans (le_max_right _ _))
        simp only [Pi.add_apply]
        rw [e]
        change sq x.2 * Av _ x.2 = _
        rw [show Av ((1 : ℂ) • Φ F.1 x.1 + Φ G.1 x.1) = _ from h]
        simp only [Pi.add_apply, one_smul]
        ring
      map_smul' := by
        intro r F
        funext x
        have e : Φ (r • F).1 x.1 = r • Φ F.1 x.1 + 0 := by
          funext U
          simp only [Φ, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Subalgebra.coe_smul,
            Pi.zero_apply, smul_eq_mul, add_zero]
          ring
        have h := hAv2 (Φ F.1 x.1) 0 (PeriodSublattice.supNorm F.1) r
          (hΦm _ F.2 _) measurable_const (hΦb _ F.2 _)
          (fun U => by
            simpa using (norm_nonneg _).trans (hΦb _ F.2 x.1 U))
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [e]
        change sq x.2 * Av _ x.2 = _
        rw [show Av (r • Φ F.1 x.1 + 0) = _ from h]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hAv0, add_zero]
        change sq x.2 * (r * Av (Φ F.1 x.1) x.2) = r * (sq x.2 * Av (Φ F.1 x.1) x.2)
        ring }
  have hΨ : ∀ (F : ↥(Γ.plusAlgebra n z c)) (x : C × Γ.QuotientField),
      Ψ F x = sq x.2 * Av (Φ F.1 x.1) x.2 := fun _ _ => rfl
  have hΨm : ∀ F, Measurable (Ψ F) := by
    intro F
    refine measurable_from_prod_countable_right fun i => ?_
    exact (Γ.mem_boundedAlgebra.1 hsq).1.mul (hAvm _ F.2 i)
  have hΨb : ∀ F x, ‖Ψ F x‖ ≤ PeriodSublattice.supNorm F.1 := by
    intro F x
    rw [hΨ, norm_mul]
    calc ‖sq x.2‖ * ‖Av (Φ F.1 x.1) x.2‖ ≤ 1 * ‖Av (Φ F.1 x.1) x.2‖ :=
          mul_le_mul_of_nonneg_right (hsq1 _) (norm_nonneg _)
      _ ≤ PeriodSublattice.supNorm F.1 := by
          rw [one_mul]; exact hAvb _ F.2 _ _
  refine ⟨C × Γ.QuotientField, inferInstance, indexedSumMeasure α Γ.quotientHaar, Ψ,
    isFiniteMeasure_indexedSumMeasure hα0 hαs _, hΨm, hΨb, ?_⟩
  intro F F'
  have hS := hasSum_integral_indexedSumMeasure hα0 hαs Γ.quotientHaar
    (f := fun x => conj (Ψ F' x) * Ψ F x)
    (B := PeriodSublattice.supNorm F'.1 * PeriodSublattice.supNorm F.1)
    ((Complex.continuous_conj.measurable.comp (hΨm F')).mul (hΨm F))
    (fun x => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (hΨb F' x) (hΨb F x) (norm_nonneg _)
        ((norm_nonneg _).trans (hΨb F' x)))
  let Kw : Γ.QuotientField → ℂ := fun U => (Γ.splitFaceWeight β n z c U : ℂ)
  let K := Γ.integrateOut (Γ.crossingLinks n z c) Kw
  let G : Γ.QuotientField → ℂ :=
    w * Γ.conjReflect P (F'.1 * eE) * (F.1 * eE)
  have hle : ∀ {f : Γ.QuotientField → ℂ}, f ∈ Γ.plusAlgebra n z c →
      f ∈ Γ.boundedAlgebra (Γ.crossingLinks n z c)ᶜ := fun hf =>
    boundedAlgebra_mono Γ (by
      rw [PeriodSublattice.crossingLinks, compl_compl]
      exact Set.subset_union_left) hf
  have hle' : ∀ {f : Γ.QuotientField → ℂ}, f ∈ Γ.minusAlgebra n z c →
      f ∈ Γ.boundedAlgebra (Γ.crossingLinks n z c)ᶜ := fun hf =>
    boundedAlgebra_mono Γ (by
      rw [PeriodSublattice.crossingLinks, compl_compl]
      exact Set.subset_union_right) hf
  have hwU : w ∈ Γ.plusAlgebra n z c :=
    boundedAlgebra_mono Γ Set.inter_subset_left hw
  have hG : G ∈ Γ.boundedAlgebra (Γ.crossingLinks n z c)ᶜ :=
    mul_mem (mul_mem (hle hwU) (hle' (hΘ _ (mul_mem F'.2 heE)))) (hle (mul_mem F.2 heE))
  obtain ⟨hGm, ⟨M, hGM⟩, hGd⟩ := Γ.mem_boundedAlgebra.1 hG
  have hKwm : Measurable Kw :=
    (Complex.continuous_ofReal.comp (continuous_splitFaceWeight Γ hfin β n z c)).measurable
  have hKw1 : ∀ U, ‖Kw U‖ ≤ 1 := norm_splitFaceWeight_le_one Γ hfin hβ0 n z c
  obtain ⟨hKm, hK1, -⟩ := hX1 Kw 1 hKwm hKw1
  have hform : Γ.reflectionPairing β P F'.1 F.1 = ∫ U, G U * K U ∂Γ.quotientHaar := by
    have h := hX3 Kw G (max 1 M) hKwm hGm (fun U => (hKw1 U).trans (le_max_left _ _))
      (fun U => (hGM U).trans (le_max_right _ _)) hGd
    refine Eq.trans ?_ h
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    simp only [G, Kw, w, eE, Pi.mul_apply, hW β U, PeriodSublattice.conjReflect,
      PeriodSublattice.compPullback, Complex.ofReal_mul, map_mul, Complex.conj_ofReal]
    ring
  let T : C → Γ.QuotientField → ℂ := fun i U =>
    (α i : ℂ) * H i U * Γ.conjReflect P (H i) U
  have hHΘ : ∀ i, (H i * Γ.conjReflect P (H i)) ∈
      Γ.boundedAlgebra (Γ.crossingLinks n z c)ᶜ := fun i =>
    mul_mem (hle (hHmem i)) (hle' (hΘ _ (hHmem i)))
  have hTm : ∀ i, Measurable (T i) := fun i => by
    have h := (Γ.mem_boundedAlgebra.1 (hHΘ i)).1
    have e : T i = fun U => (α i : ℂ) * (H i * Γ.conjReflect P (H i)) U := by
      funext U
      simp only [T, Pi.mul_apply]
      ring
    rw [e]
    exact h.const_mul _
  have hTB : ∀ i, ∃ B : ℝ, ∀ U, ‖T i U‖ ≤ B := fun i => by
    obtain ⟨-, ⟨B, hB⟩, -⟩ := Γ.mem_boundedAlgebra.1 (hHΘ i)
    refine ⟨‖(α i : ℂ)‖ * B, fun U => ?_⟩
    have e : T i U = (α i : ℂ) * (H i * Γ.conjReflect P (H i)) U := by
      simp only [T, Pi.mul_apply]
      ring
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_left (hB U) (norm_nonneg _)
  have hsum := hasSum_integral_mul_of_tendstoUniformly Γ.quotientHaar hGm hGM hKm hK1 hTm hTB hHu
  have hterm : ∀ i, ∫ U, G U * T i U ∂Γ.quotientHaar =
      (α i : ℂ) * ∫ U, conj (Ψ F' (i, U)) * Ψ F (i, U) ∂Γ.quotientHaar := by
    intro i
    have h := hH (Φ F.1 i) (hΦ _ F.2 i) (Φ F'.1 i) (hΦ _ F'.2 i) w hw
    have e1 : (fun U => conj (Ψ F' (i, U)) * Ψ F (i, U)) =
        fun U => w U * conj (Av (Φ F'.1 i) U) * Av (Φ F.1 i) U := by
      funext U
      rw [hΨ, hΨ, map_mul, hsqr, ← hsqw U]
      ring
    have e2 : (fun U => G U * T i U) = fun U => (α i : ℂ) *
        (w U * Γ.conjReflect P (Φ F'.1 i) U * Φ F.1 i U) := by
      funext U
      simp only [G, T, Φ, Pi.mul_apply, PeriodSublattice.conjReflect,
        PeriodSublattice.compPullback, map_mul]
      ring
    rw [e1, e2, integral_const_mul, h]
  rw [hform]
  simp_rw [hterm] at hsum
  exact hsum.unique hS
end PairingSquare
end YangMills.Construction.InfiniteLattice
