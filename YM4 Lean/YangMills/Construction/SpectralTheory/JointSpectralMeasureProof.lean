import YangMills.Construction.HilbertSpace.BasicFactsProofs
import YangMills.Construction.JointSpectrum.BernsteinPositivity
import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusTheorem
import YangMills.Construction.SpectralTheory.JointSpectralMeasureOfCommutingOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.JointSpectral
open BorelSpectral HilbertSpaceBasics
section Operators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
private lemma isSesquilinear_inner (T : H →L[ℂ] H) :
    HilbertSpaceBasics.IsSesquilinear fun u v : H => ⟪u, T v⟫_ℂ where
  add_left a b c := inner_add_left _ _ _
  smul_left z a b := inner_smul_left _ _ _
  add_right a b c := by simp
  smul_right z a b := by simp
private lemma inner_apply_eq_polarization (hF : HilbertSpaceFacts.Facts) (T : H →L[ℂ] H) (u v : H) :
    ⟪u, T v⟫_ℂ = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
      (-Complex.I) ^ k * ⟪u + Complex.I ^ k • v, T (u + Complex.I ^ k • v)⟫_ℂ := by
  obtain ⟨hP, -⟩ := hF
  have h : 4 * ⟪u, T v⟫_ℂ = ∑ k ∈ Finset.range 4,
      (-Complex.I) ^ k * ⟪u + Complex.I ^ k • v, T (u + Complex.I ^ k • v)⟫_ℂ :=
    hP H (fun u v : H => ⟪u, T v⟫_ℂ) (isSesquilinear_inner T) u v
  rw [← h]
  ring
private lemma tendsto_inner_of_tendsto_diag (hF : HilbertSpaceFacts.Facts) {ι : Type*}
    {l : Filter ι} (T : ι → H →L[ℂ] H) (c : H → ℂ)
    (h : ∀ v, Tendsto (fun k => ⟪v, T k v⟫_ℂ) l (𝓝 (c v))) (u v : H) :
    Tendsto (fun k => ⟪u, T k v⟫_ℂ) l
      (𝓝 ((1 / 4 : ℂ) * ∑ j ∈ Finset.range 4, (-Complex.I) ^ j * c (u + Complex.I ^ j • v))) := by
  have e : (fun k => ⟪u, T k v⟫_ℂ) = fun k => (1 / 4 : ℂ) * ∑ j ∈ Finset.range 4,
      (-Complex.I) ^ j * ⟪u + Complex.I ^ j • v, T k (u + Complex.I ^ j • v)⟫_ℂ :=
    funext fun k => inner_apply_eq_polarization hF (T k) u v
  rw [e]
  exact (tendsto_finset_sum _ fun j _ => (h _).const_mul _).const_mul _
private lemma tendsto_inner_apply_of_diag (hF : HilbertSpaceFacts.Facts) {ι : Type*}
    {l : Filter ι} (S : ι → H →L[ℂ] H) (T : H →L[ℂ] H)
    (h : ∀ v, Tendsto (fun k => ⟪v, S k v⟫_ℂ) l (𝓝 ⟪v, T v⟫_ℂ)) (u v : H) :
    Tendsto (fun k => ⟪u, S k v⟫_ℂ) l (𝓝 ⟪u, T v⟫_ℂ) := by
  have := tendsto_inner_of_tendsto_diag hF S (fun v => ⟪v, T v⟫_ℂ) h u v
  rwa [← inner_apply_eq_polarization hF] at this
private lemma norm_form_le {β : H → H → ℂ} (hβ : HilbertSpaceBasics.IsSesquilinear β)
    (hb : ∀ u v, ‖β u v‖ ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)) (u v : H) :
    ‖β u v‖ ≤ 4 * ‖u‖ * ‖v‖ := by
  by_cases h0 : u = 0
  · subst h0
    have : β 0 v = 0 := by simpa using hβ.smul_left 0 0 v
    simp [this]
  by_cases h1 : v = 0
  · subst h1
    have : β u 0 = 0 := by simpa using hβ.smul_right 0 u 0
    simp [this]
  have h := hb (((‖v‖ : ℝ) : ℂ) • u) (((‖u‖ : ℝ) : ℂ) • v)
  rw [hβ.smul_left, hβ.smul_right, norm_mul, norm_mul, norm_smul, norm_smul] at h
  simp only [RCLike.norm_conj, Complex.norm_real, norm_norm] at h
  have h2 : ‖v‖ * ‖u‖ * ‖β u v‖ ≤ ‖v‖ * ‖u‖ * (4 * ‖u‖ * ‖v‖) := by
    calc ‖v‖ * ‖u‖ * ‖β u v‖ = ‖v‖ * (‖u‖ * ‖β u v‖) := by ring
      _ ≤ 2 * ((‖v‖ * ‖u‖) ^ 2 + (‖u‖ * ‖v‖) ^ 2) := h
      _ = ‖v‖ * ‖u‖ * (4 * ‖u‖ * ‖v‖) := by ring
  exact le_of_mul_le_mul_left h2 (by positivity)
private lemma exists_op_of_tendsto_diag (hF : HilbertSpaceFacts.Facts) (T : ℕ → H →L[ℂ] H)
    (c : H → ℂ) (h : ∀ v, Tendsto (fun k => ⟪v, T k v⟫_ℂ) atTop (𝓝 (c v)))
    (hb : ∀ v, ‖c v‖ ≤ ‖v‖ ^ 2) : ∃ S : H →L[ℂ] H, ∀ v, ⟪v, S v⟫_ℂ = c v := by
  set β : H → H → ℂ := fun u v =>
    (1 / 4 : ℂ) * ∑ j ∈ Finset.range 4, (-Complex.I) ^ j * c (u + Complex.I ^ j • v) with hβ
  have ht : ∀ u v, Tendsto (fun k => ⟪u, T k v⟫_ℂ) atTop (𝓝 (β u v)) :=
    fun u v => tendsto_inner_of_tendsto_diag hF T c h u v
  have hform : HilbertSpaceBasics.IsSesquilinear β :=
    { add_left := fun a b d => tendsto_nhds_unique (ht (a + b) d) (by
        simpa only [inner_add_left] using (ht a d).add (ht b d))
      smul_left := fun z a d => tendsto_nhds_unique (ht (z • a) d) (by
        simpa only [inner_smul_left] using (ht a d).const_mul (conj z))
      add_right := fun a b d => tendsto_nhds_unique (ht a (b + d)) (by
        simpa only [map_add, inner_add_right] using (ht a b).add (ht a d))
      smul_right := fun z a d => tendsto_nhds_unique (ht a (z • d)) (by
        simpa only [map_smul, inner_smul_right] using (ht a d).const_mul z) }
  have hdiag : ∀ v, β v v = c v := fun v => tendsto_nhds_unique (ht v v) (h v)
  have hb1 : ∀ u v, ‖β u v‖ ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    intro u v
    have h1 : ∀ j : ℕ, ‖(-Complex.I) ^ j * c (u + Complex.I ^ j • v)‖ ≤
        2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      intro j
      rw [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]
      refine (hb _).trans ?_
      have h2 : ‖u + Complex.I ^ j • v‖ ≤ ‖u‖ + ‖v‖ :=
        (norm_add_le _ _).trans (by simp [norm_smul])
      have h3 : ‖u + Complex.I ^ j • v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by gcongr
      nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
    have h4 : ‖∑ j ∈ Finset.range 4, (-Complex.I) ^ j * c (u + Complex.I ^ j • v)‖ ≤
        4 * (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)) := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
      simp
    simp only [hβ, norm_mul]
    have h5 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
    rw [h5]
    linarith
  obtain ⟨hF1, -, -, -, -, -, -, -, -, -, -, hR, -⟩ := hF
  obtain ⟨B, hB, -, -⟩ := hR H β 4 (by norm_num) hform (norm_form_le hform hb1)
  exact ⟨B, fun v => by rw [← hB, hdiag]⟩
private lemma ext_of_diag (hF : HilbertSpaceFacts.Facts) {A B : H →L[ℂ] H}
    (h : ∀ v, ⟪v, A v⟫_ℂ = ⟪v, B v⟫_ℂ) : A = B := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hD, -⟩ := hF
  exact (hD H A).1 B h
private lemma isSelfAdjoint_of_diag_im (hF : HilbertSpaceFacts.Facts) {A : H →L[ℂ] H}
    (h : ∀ v, (⟪v, A v⟫_ℂ).im = 0) : IsSelfAdjoint A := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hD, -⟩ := hF
  exact (hD H A).2 h
private lemma inner_map_left_of_selfAdjoint {S : H →L[ℂ] H} (hS : IsSelfAdjoint S) (u v : H) :
    ⟪S u, v⟫_ℂ = ⟪u, S v⟫_ℂ := by
  simpa using ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS u v
private lemma im_inner_apply_self {S : H →L[ℂ] H} (hS : IsSelfAdjoint S) (v : H) :
    (⟪v, S v⟫_ℂ).im = 0 := by apply _root_.YangMills.Construction.HilbertSpaceFacts.im_inner_self_apply_eq_zero <;> assumption
private lemma commute_of_weak_limit {ι : Type*} {l : Filter ι} [l.NeBot] {B T : H →L[ℂ] H}
    {S : ι → H →L[ℂ] H} (hw : ∀ u v, Tendsto (fun k => ⟪u, S k v⟫_ℂ) l (𝓝 ⟪u, T v⟫_ℂ))
    (hc : ∀ k, Commute B (S k)) : Commute B T := by
  show B * T = T * B
  ext v
  refine ext_inner_left ℂ fun u => ?_
  have h1 : ⟪u, (B * T) v⟫_ℂ = ⟪ContinuousLinearMap.adjoint B u, T v⟫_ℂ := by
    simp [ContinuousLinearMap.adjoint_inner_left]
  rw [h1]
  refine tendsto_nhds_unique (hw _ v) ?_
  refine (hw u (B v)).congr fun k => ?_
  have h2 : S k (B v) = B (S k v) := by
    have := (hc k).eq
    exact (congrArg (fun U : H →L[ℂ] H => U v) this).symm
  rw [h2, ContinuousLinearMap.adjoint_inner_left]
end Operators
section Calculus
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
private structure IsUnitalCalculus (Φ : C(X, ℝ) →L[ℝ] H →L[ℂ] H) : Prop where
  map_one : Φ 1 = 1
  map_mul : ∀ f g, Φ (f * g) = Φ f * Φ g
  isSelfAdjoint : ∀ f, IsSelfAdjoint (Φ f)
variable {Φ : C(X, ℝ) →L[ℝ] H →L[ℂ] H}
private lemma re_inner_calc_nonneg (hΦ : IsUnitalCalculus Φ) (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (v : H) : 0 ≤ (⟪v, Φ f v⟫_ℂ).re := by
  let g : C(X, ℝ) := ⟨fun x => Real.sqrt (f x), by fun_prop⟩
  have hg : g * g = f := by
    ext x
    exact Real.mul_self_sqrt (hf x)
  have h1 : ⟪v, Φ f v⟫_ℂ = ⟪Φ g v, Φ g v⟫_ℂ := by
    rw [← hg, hΦ.map_mul, ContinuousLinearMap.mul_apply,
      inner_map_left_of_selfAdjoint (hΦ.isSelfAdjoint g)]
  rw [h1]
  exact inner_self_nonneg (𝕜 := ℂ)
private lemma exists_diag_measure (hΦ : IsUnitalCalculus Φ) (v : H) :
    ∃ m : Measure X, IsFiniteMeasure m ∧
      ∀ f : C(X, ℝ), ⟪v, Φ f v⟫_ℂ = ((∫ x, f x ∂m : ℝ) : ℂ) := by
  let Λ₀ : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun w => (⟪v, Φ (w : C(X, ℝ)) v⟫_ℂ).re
      map_add' := fun w w' => by
        have e : ((w + w' : CompactlySupportedContinuousMap X ℝ) : C(X, ℝ)) =
            (w : C(X, ℝ)) + (w' : C(X, ℝ)) := by
          ext x
          simp
        rw [e, map_add, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
      map_smul' := fun a w => by
        have e : ((a • w : CompactlySupportedContinuousMap X ℝ) : C(X, ℝ)) =
            a • (w : C(X, ℝ)) := by
          ext x
          simp
        rw [e, map_smul, ContinuousLinearMap.smul_apply, ← Complex.coe_smul, inner_smul_right]
        simp }
  let Λ := PositiveLinearMap.mk₀ Λ₀ fun w hw =>
    re_inner_calc_nonneg hΦ (w : C(X, ℝ)) (CompactlySupportedContinuousMap.le_def.1 hw) v
  let m := RealRMK.rieszMeasure Λ
  refine ⟨m, inferInstance, fun f => ?_⟩
  have h1 : ∫ x, f x ∂m = (⟪v, Φ f v⟫_ℂ).re :=
    RealRMK.integral_rieszMeasure Λ (CompactlySupportedContinuousMap.continuousMapEquiv f)
  rw [h1]
  apply Complex.ext
  · simp
  · simp [im_inner_apply_self (hΦ.isSelfAdjoint f)]
private def DiagMass (μ : H → Measure X) (Δ : Set X) (T : H →L[ℂ] H) : Prop :=
  ∀ v, ⟪v, T v⟫_ℂ = (((μ v).real Δ : ℝ) : ℂ)
variable {μ : H → Measure X} [∀ v, IsFiniteMeasure (μ v)]
private lemma hasSum_real_iUnion (m : Measure X) [IsFiniteMeasure m] {Δ : ℕ → Set X}
    (hm : ∀ k, MeasurableSet (Δ k)) (hd : Pairwise (Function.onFun Disjoint Δ)) :
    HasSum (fun k => m.real (Δ k)) (m.real (⋃ k, Δ k)) := by
  have hne : ∑' k, m (Δ k) ≠ ∞ := by
    rw [← measure_iUnion hd hm]
    exact measure_ne_top _ _
  have h := ENNReal.hasSum_toReal hne
  rw [← ENNReal.tsum_toReal_eq (fun k => measure_ne_top m _), ← measure_iUnion hd hm] at h
  exact h
private lemma measureReal_univ_eq (hΦ : IsUnitalCalculus Φ)
    (hμ : ∀ (f : C(X, ℝ)) v, ⟪v, Φ f v⟫_ℂ = ((∫ x, f x ∂μ v : ℝ) : ℂ)) (v : H) :
    (μ v).real univ = ‖v‖ ^ 2 := by
  have h := hμ 1 v
  rw [hΦ.map_one, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K] at h
  have h2 : ∫ x, (1 : C(X, ℝ)) x ∂μ v = (μ v).real univ := by simp
  rw [h2] at h
  have h3 : (((μ v).real univ : ℝ) : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h]
    push_cast
    rfl
  exact Complex.ofReal_injective h3
private lemma norm_measureReal_le (hΦ : IsUnitalCalculus Φ)
    (hμ : ∀ (f : C(X, ℝ)) v, ⟪v, Φ f v⟫_ℂ = ((∫ x, f x ∂μ v : ℝ) : ℂ)) (Δ : Set X) (v : H) :
    ‖(((μ v).real Δ : ℝ) : ℂ)‖ ≤ ‖v‖ ^ 2 := by
  rw [Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg, ← measureReal_univ_eq hΦ hμ]
  exact measureReal_mono (subset_univ _)
private lemma exists_cont_approx_indicator {C : Set X} (hC : IsClosed C) :
    ∃ f : ℕ → C(X, ℝ), (∀ k x, 0 ≤ f k x ∧ f k x ≤ 1) ∧
      ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (C.indicator (1 : X → ℝ) x)) := by
  refine ⟨fun k => ⟨fun x => ((hC.apprSeq k x : ℝ≥0) : ℝ), by fun_prop⟩, fun k x => ?_, fun x => ?_⟩
  · exact ⟨NNReal.coe_nonneg _, by exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hC k x⟩
  · have h := tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hC) x
    have e : C.indicator (1 : X → ℝ) x = ((C.indicator (fun _ => (1 : ℝ≥0)) x : ℝ≥0) : ℝ) := by
      by_cases hx : x ∈ C <;> simp [hx]
    rw [e]
    exact NNReal.tendsto_coe.mpr h
private lemma tendsto_integral_approx_mul (m : Measure X) [IsFiniteMeasure m] {C : Set X}
    {f : ℕ → C(X, ℝ)} (hf : ∀ k x, 0 ≤ f k x ∧ f k x ≤ 1)
    (hl : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (C.indicator (1 : X → ℝ) x)))
    {w : X → ℝ} (hw : Measurable w) (hw1 : ∀ x, |w x| ≤ 1) :
    Tendsto (fun k => ∫ x, f k x * w x ∂m) atTop
      (𝓝 (∫ x, C.indicator (1 : X → ℝ) x * w x ∂m)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun k => ?_)
    (integrable_const _) (fun k => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => (hl x).mul_const _)
  · exact ((f k).continuous.measurable.mul hw).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf k x).1]
    exact mul_le_one₀ (hf k x).2 (abs_nonneg _) (hw1 x)
private lemma tendsto_integral_approx (m : Measure X) [IsFiniteMeasure m] {C : Set X}
    (hC : IsClosed C) {f : ℕ → C(X, ℝ)} (hf : ∀ k x, 0 ≤ f k x ∧ f k x ≤ 1)
    (hl : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (C.indicator (1 : X → ℝ) x))) :
    Tendsto (fun k => ∫ x, f k x ∂m) atTop (𝓝 (m.real C)) := by
  have h := tendsto_integral_approx_mul m hf hl (w := fun _ => 1) measurable_const (by simp)
  simp only [mul_one] at h
  rwa [integral_indicator_one hC.measurableSet] at h
private lemma tendsto_diag_approx
    (hμ : ∀ (f : C(X, ℝ)) v, ⟪v, Φ f v⟫_ℂ = ((∫ x, f x ∂μ v : ℝ) : ℂ)) {C : Set X}
    (hC : IsClosed C) {f : ℕ → C(X, ℝ)} (hf : ∀ k x, 0 ≤ f k x ∧ f k x ≤ 1)
    (hl : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (C.indicator (1 : X → ℝ) x))) (v : H) :
    Tendsto (fun k => ⟪v, Φ (f k) v⟫_ℂ) atTop (𝓝 (((μ v).real C : ℝ) : ℂ)) := by
  simp only [hμ]
  exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_integral_approx _ hC hf hl)
private lemma tendsto_diag_partialSum {Δ : ℕ → Set X} (hm : ∀ k, MeasurableSet (Δ k))
    (hd : Pairwise (Function.onFun Disjoint Δ)) {T : ℕ → H →L[ℂ] H}
    (hT : ∀ k, DiagMass μ (Δ k) (T k)) (v : H) :
    Tendsto (fun K => ⟪v, (∑ k ∈ Finset.range K, T k) v⟫_ℂ) atTop
      (𝓝 (((μ v).real (⋃ k, Δ k) : ℝ) : ℂ)) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp
    (hasSum_real_iUnion (μ v) hm hd).tendsto_sum_nat
  refine h.congr fun K => ?_
  simp [ContinuousLinearMap.sum_apply, inner_sum, hT _ v]
private lemma exists_diagMass (hF : HilbertSpaceFacts.Facts) (hΦ : IsUnitalCalculus Φ)
    (hμ : ∀ (f : C(X, ℝ)) v, ⟪v, Φ f v⟫_ℂ = ((∫ x, f x ∂μ v : ℝ) : ℂ)) :
    ∀ Δ, MeasurableSet Δ → ∃ T, DiagMass μ Δ T := by
  refine MeasurableSpace.induction_on_inter (C := fun Δ _ => ∃ T, DiagMass μ Δ T)
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
    ⟨0, fun v => by simp⟩ ?_ ?_ ?_
  · intro C hC
    obtain ⟨f, hf, hl⟩ := exists_cont_approx_indicator (X := X) hC
    exact exists_op_of_tendsto_diag hF (fun k => Φ (f k)) _
      (tendsto_diag_approx hμ hC hf hl) (norm_measureReal_le hΦ hμ C)
  · rintro Δ hΔ ⟨T, hT⟩
    refine ⟨1 - T, fun v => ?_⟩
    have h1 : (μ v).real Δᶜ = ‖v‖ ^ 2 - (μ v).real Δ := by
      rw [measureReal_compl hΔ, measureReal_univ_eq hΦ hμ]
    rw [h1, ContinuousLinearMap.sub_apply, inner_sub_right, hT v,
      ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  · intro Δ hd hm hT
    choose T hT using hT
    exact exists_op_of_tendsto_diag hF (fun K => ∑ k ∈ Finset.range K, T k) _
      (tendsto_diag_partialSum hm hd hT) (norm_measureReal_le hΦ hμ _)
private lemma diagMass_unique (hF : HilbertSpaceFacts.Facts) {Δ : Set X} {T T' : H →L[ℂ] H}
    (h : DiagMass μ Δ T) (h' : DiagMass μ Δ T') : T = T' :=
  ext_of_diag hF fun v => by rw [h v, h' v]
private lemma DiagMass.selfAdjoint (hF : HilbertSpaceFacts.Facts) {Δ : Set X}
    {T : H →L[ℂ] H} (h : DiagMass μ Δ T) : IsSelfAdjoint T :=
  isSelfAdjoint_of_diag_im hF fun v => by rw [h v]; simp
private lemma diagMass_compl (hΦ : IsUnitalCalculus Φ)
    (hμ : ∀ (f : C(X, ℝ)) v, ⟪v, Φ f v⟫_ℂ = ((∫ x, f x ∂μ v : ℝ) : ℂ)) {Δ : Set X}
    (hΔ : MeasurableSet Δ) {T : H →L[ℂ] H} (hT : DiagMass μ Δ T) : DiagMass μ Δᶜ (1 - T) := by
  intro v
  have h1 : (μ v).real Δᶜ = ‖v‖ ^ 2 - (μ v).real Δ := by
    rw [measureReal_compl hΔ, measureReal_univ_eq hΦ hμ]
  rw [h1, ContinuousLinearMap.sub_apply, inner_sub_right, hT v,
    ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
private lemma commute_of_diagMass (hF : HilbertSpaceFacts.Facts)
    (hΦ : IsUnitalCalculus Φ)
    (hμ : ∀ (f : C(X, ℝ)) v, ⟪v, Φ f v⟫_ℂ = ((∫ x, f x ∂μ v : ℝ) : ℂ)) {B : H →L[ℂ] H}
    (hB : ∀ f, Commute B (Φ f)) :
    ∀ Δ, MeasurableSet Δ → ∀ T, DiagMass μ Δ T → Commute B T := by
  refine MeasurableSpace.induction_on_inter (C := fun Δ _ => ∀ T, DiagMass μ Δ T → Commute B T)
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
    ?_ ?_ ?_ ?_
  · intro T hT
    have : T = 0 := diagMass_unique hF hT (fun v => by simp)
    rw [this]
    exact Commute.zero_right B
  · intro C hC T hT
    obtain ⟨f, hf, hl⟩ := exists_cont_approx_indicator (X := X) hC
    refine commute_of_weak_limit (l := atTop)
      (tendsto_inner_apply_of_diag hF (fun k => Φ (f k)) T fun v => ?_) fun k => hB (f k)
    rw [hT v]
    exact tendsto_diag_approx hμ hC hf hl v
  · intro Δ hΔ ih T hT
    obtain ⟨T₀, hT₀⟩ := exists_diagMass hF hΦ hμ Δ hΔ
    have e : T = 1 - T₀ := diagMass_unique hF hT (diagMass_compl hΦ hμ hΔ hT₀)
    rw [e]
    exact (Commute.one_right B).sub_right (ih T₀ hT₀)
  · intro Δ hd hm ih T hT
    choose S hS using fun k => exists_diagMass hF hΦ hμ (Δ k) (hm k)
    refine commute_of_weak_limit (l := atTop)
      (tendsto_inner_apply_of_diag hF (fun K => ∑ k ∈ Finset.range K, S k) T fun v => ?_)
      fun K => Commute.sum_right _ _ _ fun k _ => ih k (S k) (hS k)
    rw [hT v]
    exact tendsto_diag_partialSum hm hd hS v
private lemma diagMass_mul_of_isClosed (hF : HilbertSpaceFacts.Facts) (hΦ : IsUnitalCalculus Φ)
    (hμ : ∀ (f : C(X, ℝ)) v, ⟪v, Φ f v⟫_ℂ = ((∫ x, f x ∂μ v : ℝ) : ℂ)) {C C' : Set X}
    (hC : IsClosed C) (hC' : IsClosed C') {T T' : H →L[ℂ] H} (hT : DiagMass μ C T)
    (hT' : DiagMass μ C' T') : DiagMass μ (C ∩ C') (T * T') := by
  intro v
  obtain ⟨f, hf, hl⟩ := exists_cont_approx_indicator (X := X) hC
  obtain ⟨g, hg, hl'⟩ := exists_cont_approx_indicator (X := X) hC'
  have hwT := tendsto_inner_apply_of_diag hF (fun k => Φ (f k)) T (fun v => by
    rw [hT v]
    exact tendsto_diag_approx hμ hC hf hl v)
  have hwT' := tendsto_inner_apply_of_diag hF (fun k => Φ (g k)) T' (fun v => by
    rw [hT' v]
    exact tendsto_diag_approx hμ hC' hg hl' v)
  have h1 : ∀ k, ⟪v, Φ (f k) (T' v)⟫_ℂ =
      ((∫ x, C'.indicator (1 : X → ℝ) x * f k x ∂μ v : ℝ) : ℂ) := by
    intro k
    have ha := hwT' (Φ (f k) v) v
    have hb := (Complex.continuous_ofReal.tendsto _).comp
      (tendsto_integral_approx_mul (μ v) hg hl' (f k).continuous.measurable
        (w := f k) (fun x => by
          rw [abs_of_nonneg (hf k x).1]
          exact (hf k x).2))
    rw [inner_map_left_of_selfAdjoint (hΦ.isSelfAdjoint (f k))] at ha
    refine tendsto_nhds_unique ha (hb.congr fun j => ?_)
    rw [inner_map_left_of_selfAdjoint (hΦ.isSelfAdjoint (f k)), ← ContinuousLinearMap.mul_apply,
      ← hΦ.map_mul, hμ]
    simp [mul_comm]
  have hc := (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_integral_approx_mul (μ v) hf hl (w := C'.indicator 1)
      (measurable_one.indicator hC'.measurableSet) (fun x => by
        by_cases hx : x ∈ C' <;> simp [hx]))
  have e : ∫ x, C.indicator (1 : X → ℝ) x * C'.indicator (1 : X → ℝ) x ∂μ v =
      (μ v).real (C ∩ C') := by
    have e2 : (fun x => C.indicator (1 : X → ℝ) x * C'.indicator (1 : X → ℝ) x) =
        (C ∩ C').indicator 1 := by
      funext x
      rw [inter_indicator_one]
      rfl
    rw [e2]
    exact integral_indicator_one (hC.measurableSet.inter hC'.measurableSet)
  rw [e] at hc
  refine tendsto_nhds_unique (hwT v (T' v)) (hc.congr fun k => ?_)
  rw [h1 k]
  simp [mul_comm]
private lemma diagMass_mul_of_right (hF : HilbertSpaceFacts.Facts) (hΦ : IsUnitalCalculus Φ)
    (hμ : ∀ (f : C(X, ℝ)) v, ⟪v, Φ f v⟫_ℂ = ((∫ x, f x ∂μ v : ℝ) : ℂ)) {Δ' : Set X}
    (hΔ' : MeasurableSet Δ') {T' : H →L[ℂ] H} (hT' : DiagMass μ Δ' T')
    (hb : ∀ C, IsClosed C → ∀ T, DiagMass μ C T → DiagMass μ (C ∩ Δ') (T * T')) :
    ∀ Δ, MeasurableSet Δ → ∀ T, DiagMass μ Δ T → DiagMass μ (Δ ∩ Δ') (T * T') := by
  refine MeasurableSpace.induction_on_inter
    (C := fun Δ _ => ∀ T, DiagMass μ Δ T → DiagMass μ (Δ ∩ Δ') (T * T'))
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
    ?_ hb ?_ ?_
  · intro T hT
    have : T = 0 := diagMass_unique hF hT (fun v => by simp)
    intro v
    simp [this]
  · intro Δ hΔ ih T hT
    obtain ⟨T₀, hT₀⟩ := exists_diagMass hF hΦ hμ Δ hΔ
    have e : T = 1 - T₀ := diagMass_unique hF hT (diagMass_compl hΦ hμ hΔ hT₀)
    intro v
    have h1 := ih T₀ hT₀ v
    have h2 := hT' v
    have h3 : (μ v).real (Δᶜ ∩ Δ') = (μ v).real Δ' - (μ v).real (Δ ∩ Δ') := by
      have := measureReal_inter_add_sdiff (μ := μ v) (s := Δ') hΔ
      rw [inter_comm Δ Δ', inter_comm Δᶜ Δ', ← diff_eq]
      linarith
    rw [e, sub_mul, one_mul, ContinuousLinearMap.sub_apply, inner_sub_right, h1, h2, h3]
    push_cast
    rfl
  · intro Δ hd hm ih T hT
    choose S hS using fun k => exists_diagMass hF hΦ hμ (Δ k) (hm k)
    intro v
    have hw := tendsto_inner_apply_of_diag hF (l := atTop) (fun K => ∑ k ∈ Finset.range K, S k) T
      (fun v => by
        rw [hT v]
        exact tendsto_diag_partialSum hm hd hS v) v (T' v)
    have hp := tendsto_diag_partialSum (Δ := fun k => Δ k ∩ Δ') (T := fun k => S k * T')
      (fun k => (hm k).inter hΔ')
      (fun k l hkl => (hd hkl).mono inter_subset_left inter_subset_left)
      (fun k => ih k (S k) (hS k)) v
    rw [← iUnion_inter] at hp
    refine tendsto_nhds_unique hw (hp.congr fun K => ?_)
    rw [← Finset.sum_mul]
    rfl
private lemma DiagMass.swap_mul {Δ : Set X} {T T' : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (hT' : IsSelfAdjoint T') (h : DiagMass μ Δ (T * T')) : DiagMass μ Δ (T' * T) := by
  intro v
  have h1 := h v
  rw [ContinuousLinearMap.mul_apply] at h1 ⊢
  rw [← inner_map_left_of_selfAdjoint hT', ← inner_conj_symm, inner_map_left_of_selfAdjoint hT,
    h1, Complex.conj_ofReal]
private lemma diagMass_mul (hF : HilbertSpaceFacts.Facts) (hΦ : IsUnitalCalculus Φ)
    (hμ : ∀ (f : C(X, ℝ)) v, ⟪v, Φ f v⟫_ℂ = ((∫ x, f x ∂μ v : ℝ) : ℂ)) {Δ Δ' : Set X}
    (hΔ : MeasurableSet Δ) (hΔ' : MeasurableSet Δ') {T T' : H →L[ℂ] H} (hT : DiagMass μ Δ T)
    (hT' : DiagMass μ Δ' T') : DiagMass μ (Δ ∩ Δ') (T * T') := by
  have step : ∀ C, IsClosed C → ∀ U, DiagMass μ C U → ∀ Δ₀, MeasurableSet Δ₀ → ∀ U₀,
      DiagMass μ Δ₀ U₀ → DiagMass μ (Δ₀ ∩ C) (U₀ * U) := fun C hC U hU =>
    diagMass_mul_of_right hF hΦ hμ hC.measurableSet hU fun C' hC' U' hU' =>
      diagMass_mul_of_isClosed hF hΦ hμ hC' hC hU' hU
  refine diagMass_mul_of_right hF hΦ hμ hΔ' hT' (fun C hC U hU => ?_) Δ hΔ T hT
  rw [inter_comm]
  exact (step C hC U hU Δ' hΔ' T' hT').swap_mul (hT'.selfAdjoint hF) (hU.selfAdjoint hF)
private lemma exists_spectralMeasure_of_calc (hF : HilbertSpaceFacts.Facts) {n : ℕ}
    {Y : Set (Fin n → ℝ)} [CompactSpace Y] (hn : 1 ≤ n) (hY : MeasurableSet Y)
    {Φ : C(Y, ℝ) →L[ℝ] H →L[ℂ] H} (hΦ : IsUnitalCalculus Φ) :
    ∃ F : SpectralMeasure Y H,
      (∀ (f : C(Y, ℝ)) v, ⟪v, Φ f v⟫_ℂ = ((∫ y, f y ∂F.diagMeasure v : ℝ) : ℂ)) ∧
      ∀ B : H →L[ℂ] H, (∀ f, Commute B (Φ f)) → ∀ Δ, Commute B (F Δ) := by
  choose μ hfin hμ using exists_diag_measure hΦ
  have hμ' : ∀ (f : C(Y, ℝ)) v, ⟪v, Φ f v⟫_ℂ = ((∫ x, f x ∂μ v : ℝ) : ℂ) := fun f v => hμ v f
  choose T hT using exists_diagMass hF hΦ hμ'
  have hm : ∀ (Δ Δ' : Set Y) (hΔ : MeasurableSet Δ) (hΔ' : MeasurableSet Δ'),
      T (Δ ∩ Δ') (hΔ.inter hΔ') = T Δ hΔ * T Δ' hΔ' := fun Δ Δ' hΔ hΔ' =>
    diagMass_unique hF (hT _ _) (diagMass_mul hF hΦ hμ' hΔ hΔ' (hT _ _) (hT _ _))
  let F : SpectralMeasure Y H :=
    { one_le_dimension := hn
      measurableSet_carrier := hY
      toFun := fun Δ => T Δ.1 Δ.2
      isStarProjection := fun Δ =>
        { isIdempotentElem := by
            have h := hm Δ.1 Δ.1 Δ.2 Δ.2
            have e : T (Δ.1 ∩ Δ.1) (Δ.2.inter Δ.2) = T Δ.1 Δ.2 := by
              simp only [inter_self]
            exact (h.symm.trans e)
          isSelfAdjoint := (hT _ _).selfAdjoint hF }
      map_univ := ext_of_diag hF fun v => by
        rw [hT _ _ v, measureReal_univ_eq hΦ hμ', ContinuousLinearMap.one_apply,
          inner_self_eq_norm_sq_to_K]
        push_cast
        rfl
      map_inter := fun Δ Δ' => hm Δ.1 Δ'.1 Δ.2 Δ'.2
      countablyAdditive := fun v Δ hd => by
        simp only [hT _ _ v]
        exact Complex.hasSum_ofReal.mpr (hasSum_real_iUnion (μ v) (fun k => (Δ k).2) hd) }
  have hs : ∀ v, F.diagMeasure v = μ v := by
    intro v
    refine Measure.ext fun Δ hΔ => ?_
    have h1 := F.diagMeasure_apply v ⟨Δ, hΔ⟩
    have h2 := F.inner_apply_self_eq_norm_sq ⟨Δ, hΔ⟩ v
    have h3 : ⟪v, F ⟨Δ, hΔ⟩ v⟫_ℂ = (((μ v).real Δ : ℝ) : ℂ) := hT Δ hΔ v
    have h4 : ‖F ⟨Δ, hΔ⟩ v‖ ^ 2 = (μ v).real Δ := Complex.ofReal_injective (h2.symm.trans h3)
    rw [show F.diagMeasure v Δ = _ from h1, h4]
    exact ofReal_measureReal
  refine ⟨F, fun f v => ?_, fun B hB Δ => ?_⟩
  · rw [hs v]
    exact hμ' f v
  · exact commute_of_diagMass hF hΦ hμ' hB Δ.1 Δ.2 _ (hT _ _)
end Calculus
section Polynomials
open BorelCalculus OperatorPolynomials
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
private def coordCont {Y : Set (Fin n → ℝ)} (i : Fin n) : C(Y, ℝ) :=
  ⟨fun y => y.1 i, (continuous_apply i).comp continuous_subtype_val⟩
private def polyRestrict (Y : Set (Fin n → ℝ)) : MvPolynomial (Fin n) ℝ →ₐ[ℝ] C(Y, ℝ) :=
  MvPolynomial.aeval coordCont
private lemma polyRestrict_X {Y : Set (Fin n → ℝ)} (i : Fin n) :
    polyRestrict Y (MvPolynomial.X i) = coordCont i := by
  simp [polyRestrict]
private lemma polyRestrict_apply {Y : Set (Fin n → ℝ)} (p : MvPolynomial (Fin n) ℝ) (y : Y) :
    polyRestrict Y p y = MvPolynomial.eval y.1 p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [polyRestrict]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, ContinuousMap.mul_apply, hp, polyRestrict_X, map_mul, MvPolynomial.eval_X]
    rfl
private lemma denseRange_polyRestrict (Y : Set (Fin n → ℝ)) [CompactSpace Y] :
    DenseRange (polyRestrict Y : MvPolynomial (Fin n) ℝ → C(Y, ℝ)) := by
  have hsep : (polyRestrict Y).range.SeparatesPoints := by
    intro x y hxy
    have hne : ∃ i, x.1 i ≠ y.1 i := by
      by_contra hc
      push_neg at hc
      exact hxy (Subtype.ext (funext hc))
    obtain ⟨i, hi⟩ := hne
    exact ⟨_, ⟨coordCont i, ⟨MvPolynomial.X i, polyRestrict_X i⟩, rfl⟩, hi⟩
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  intro f
  have hf : f ∈ (polyRestrict Y).range.topologicalClosure := by
    rw [h]
    trivial
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe] at hf
  simpa [AlgHom.coe_range] using hf
private def toComplexFn {X : Type} [TopologicalSpace X] (f : C(X, ℝ)) : X → ℂ :=
  fun x => ((f x : ℝ) : ℂ)
private lemma measurable_toComplexFn {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (f : C(X, ℝ)) : Measurable (toComplexFn f) :=
  Complex.measurable_ofReal.comp f.continuous.measurable
private lemma isBoundedFn_toComplexFn {X : Type} [TopologicalSpace X] [CompactSpace X]
    (f : C(X, ℝ)) : IsBoundedFn (toComplexFn f) :=
  ⟨‖f‖, fun x => by simpa [toComplexFn] using f.norm_coe_le_norm x⟩
variable {Y : Set (Fin n → ℝ)}
private lemma isDiagonalIntegral_integralOp {E : SpectralMeasure Y H}
    (hb : BoundedFunctionalCalculus E) {g : Y → ℂ} (hm : Measurable g) (hg : IsBoundedFn g) :
    E.IsDiagonalIntegral g (E.integralOp g) :=
  Classical.epsilon_spec (hb.existsUnique_op g hm hg).exists
private lemma integralOp_eq_of_isDiagonalIntegral {E : SpectralMeasure Y H}
    (hb : BoundedFunctionalCalculus E) {g : Y → ℂ} (hm : Measurable g) (hg : IsBoundedFn g)
    {T : H →L[ℂ] H} (hT : E.IsDiagonalIntegral g T) : E.integralOp g = T :=
  (hb.existsUnique_op g hm hg).unique (isDiagonalIntegral_integralOp hb hm hg) hT
private lemma integralOp_pushforward (hC : BorelCalculus.BorelCalculusTheorem)
    (E : SpectralMeasure Y H) {n' : ℕ} {Y' : Set (Fin n' → ℝ)} (hn' : 1 ≤ n')
    (hY' : MeasurableSet Y') (κ : Y → Y') (hκ : Measurable κ) {g' : Y' → ℂ} (hg' : Measurable g')
    (hbd : IsBoundedFn g') :
    (E.pushforward hn' hY' κ hκ).integralOp g' = E.integralOp (g' ∘ κ) := by
  obtain ⟨c, hc⟩ := hbd
  have hI : PushforwardProperties E := ((hC H n).1 Y E).2.2.2.2.2.1
  ext v
  have h2 := hI.integral_pushforward hn' hY' κ hκ g' hg'
  have hdom : v ∈ E.integralDom (g' ∘ κ) := by
    rw [E.integralDom_eq_univ (g := g' ∘ κ) (c := c) fun y => hc _]
    trivial
  rw [← (E.pushforward hn' hY' κ hκ).integralApply_eq_integralOp hc v, h2.2 v hdom,
    E.integralApply_eq_integralOp (g := g' ∘ κ) (fun y => hc (κ y)) v]
private def integralCLM {X : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (m : Measure X) [IsFiniteMeasure m] : C(X, ℝ) →L[ℝ] ℝ :=
  have hi : ∀ f : C(X, ℝ), Integrable f m := fun f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  LinearMap.mkContinuous
    { toFun := fun g => ∫ x, g x ∂m
      map_add' := fun g g' => integral_add (hi g) (hi g')
      map_smul' := fun a g => integral_const_mul a _ }
    (m.real univ) fun g => by
      have h := norm_integral_le_of_norm_le_const (μ := m) (f := g) (C := ‖g‖)
        (Eventually.of_forall g.norm_coe_le_norm)
      simpa [mul_comm] using h
private lemma ext_of_integralOp_coordFn (hC : BorelCalculus.BorelCalculusTheorem)
    (hF : HilbertSpaceFacts.Facts) [CompactSpace Y] {E₁ E₂ : SpectralMeasure Y H}
    (h : ∀ i, E₁.integralOp (coordFn i) = E₂.integralOp (coordFn i)) : E₁ = E₂ := by
  have hb₁ : BoundedFunctionalCalculus E₁ := ((hC H n).1 Y E₁).1
  have hb₂ : BoundedFunctionalCalculus E₂ := ((hC H n).1 Y E₂).1
  have hconst : ∀ (E : SpectralMeasure Y H), BoundedFunctionalCalculus E → ∀ a : ℝ,
      E.integralOp (toComplexFn (polyRestrict Y (MvPolynomial.C a))) = (a : ℂ) • 1 := by
    intro E hb a
    have e : toComplexFn (polyRestrict Y (MvPolynomial.C a)) =
        (a : ℂ) • (univ : Set Y).indicator 1 := by
      funext y
      simp [toComplexFn, polyRestrict_apply]
    have hm : Measurable ((univ : Set Y).indicator (1 : Y → ℂ)) :=
      measurable_one.indicator MeasurableSet.univ
    have hbd : IsBoundedFn ((univ : Set Y).indicator (1 : Y → ℂ)) :=
      ⟨1, fun y => by simp⟩
    rw [e, hb.smul a _ hm hbd, hb.indicator ⟨univ, MeasurableSet.univ⟩, E.map_univ]
  have hp : ∀ p : MvPolynomial (Fin n) ℝ, E₁.integralOp (toComplexFn (polyRestrict Y p)) =
      E₂.integralOp (toComplexFn (polyRestrict Y p)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [hconst E₁ hb₁, hconst E₂ hb₂]
    | add p q ihp ihq =>
      have e : toComplexFn (polyRestrict Y (p + q)) =
          toComplexFn (polyRestrict Y p) + toComplexFn (polyRestrict Y q) := by
        funext y
        simp [toComplexFn]
      have m₁ := measurable_toComplexFn (polyRestrict Y p)
      have m₂ := measurable_toComplexFn (polyRestrict Y q)
      have b₁ := isBoundedFn_toComplexFn (polyRestrict Y p)
      have b₂ := isBoundedFn_toComplexFn (polyRestrict Y q)
      rw [e, hb₁.add _ _ m₁ b₁ m₂ b₂, hb₂.add _ _ m₁ b₁ m₂ b₂, ihp, ihq]
    | mul_X p i ih =>
      have e : toComplexFn (polyRestrict Y (p * MvPolynomial.X i)) =
          toComplexFn (polyRestrict Y p) * toComplexFn (coordCont i) := by
        funext y
        simp [toComplexFn, polyRestrict_X]
      have m₁ := measurable_toComplexFn (polyRestrict Y p)
      have m₂ := measurable_toComplexFn (coordCont (Y := Y) i)
      have b₁ := isBoundedFn_toComplexFn (polyRestrict Y p)
      have b₂ := isBoundedFn_toComplexFn (coordCont (Y := Y) i)
      have hi : E₁.integralOp (toComplexFn (coordCont i)) =
          E₂.integralOp (toComplexFn (coordCont i)) := h i
      rw [e, hb₁.mul _ _ m₁ b₁ m₂ b₂, hb₂.mul _ _ m₁ b₁ m₂ b₂, ih, hi]
  have hint : ∀ (E : SpectralMeasure Y H), BoundedFunctionalCalculus E → ∀ (v : H) (f : C(Y, ℝ)),
      ⟪v, E.integralOp (toComplexFn f) v⟫_ℂ = ((∫ y, f y ∂E.diagMeasure v : ℝ) : ℂ) := by
    intro E hb v f
    rw [isDiagonalIntegral_integralOp hb (measurable_toComplexFn f)
      (isBoundedFn_toComplexFn f) v]
    exact integral_ofReal
  have hm : ∀ v, E₁.diagMeasure v = E₂.diagMeasure v := by
    intro v
    have hc : (integralCLM (E₁.diagMeasure v) : C(Y, ℝ) → ℝ) =
        integralCLM (E₂.diagMeasure v) := by
      refine (denseRange_polyRestrict Y).equalizer (ContinuousLinearMap.continuous _)
        (ContinuousLinearMap.continuous _) (funext fun p => ?_)
      have h1 := hint E₁ hb₁ v (polyRestrict Y p)
      rw [hp p, hint E₂ hb₂ v (polyRestrict Y p)] at h1
      exact (Complex.ofReal_injective h1).symm
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun w => ?_
    exact congrFun hc w.toContinuousMap
  refine SpectralMeasure.ext_apply fun Δ => ext_of_diag hF fun v => ?_
  rw [E₁.inner_apply_self_eq_diagMeasure, E₂.inner_apply_self_eq_diagMeasure, hm v]
private lemma list_prod_ofFn_eq_single {M : Type*} [Monoid M] : ∀ {m : ℕ} (f : Fin m → M) (i : Fin m),
    (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | m + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases (fun h => ?_) (fun i' h => ?_) i h
    · have h1 : (List.ofFn fun j : Fin m => f j.succ).prod = 1 :=
        List.prod_eq_one fun x hx => by
          obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hx
          exact h _ (Fin.succ_ne_zero j)
      rw [h1, mul_one]
    · rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact list_prod_ofFn_eq_single (fun j : Fin m => f j.succ) i' fun j hj =>
        h _ fun e => hj (Fin.succ_injective _ e)
private lemma evalOperators_monomial [NeZero n] (A : Fin n → H →L[ℂ] H) (hA : PairwiseCommute A)
    (α : Fin n →₀ ℕ) :
    evalOperators (MvPolynomial.monomial α (1 : ℝ)) A hA = orderedMonomial A α := by
  unfold evalOperators
  rw [MvPolynomial.support_monomial]
  simp
private lemma evalOperators_X [NeZero n] (A : Fin n → H →L[ℂ] H) (hA : PairwiseCommute A)
    (i : Fin n) : evalOperators (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) A hA = A i := by
  rw [MvPolynomial.X, evalOperators_monomial]
  unfold orderedMonomial
  rw [list_prod_ofFn_eq_single _ i fun j hj => by simp [Finsupp.single_apply, hj.symm]]
  simp
private lemma evalOperators_one [NeZero n] (A : Fin n → H →L[ℂ] H) (hA : PairwiseCommute A) :
    evalOperators (1 : MvPolynomial (Fin n) ℝ) A hA = 1 := by
  have e : (1 : MvPolynomial (Fin n) ℝ) = MvPolynomial.monomial 0 1 := rfl
  rw [e, evalOperators_monomial]
  unfold orderedMonomial
  rw [list_prod_ofFn_eq_single _ 0 fun j _ => by simp]
  simp
private lemma commute_evalOperators [NeZero n] (A : Fin n → H →L[ℂ] H) (hA : PairwiseCommute A)
    {B : H →L[ℂ] H} (hB : ∀ i, Commute B (A i)) (p : MvPolynomial (Fin n) ℝ) :
    Commute B (evalOperators p A hA) := by
  unfold evalOperators
  refine Commute.sum_right _ _ _ fun α _ => Commute.smul_right ?_ _
  unfold orderedMonomial
  refine Commute.list_prod_right _ _ fun x hx => ?_
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hx
  exact (hB j).pow_right _
private lemma isGE_of_le {S T : H →L[ℂ] H} (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (h : T ≤ S) : HilbertSpaceBasics.IsGE S T :=
  ⟨hS, hT, hS.sub hT, fun v => ((ContinuousLinearMap.le_def T S).mp h).inner_nonneg_right v⟩
private lemma isSelfAdjoint_ofReal_smul_one (c : ℝ) :
    IsSelfAdjoint ((c : ℂ) • (1 : H →L[ℂ] H)) :=
  IsSelfAdjoint.smul (show star (c : ℂ) = c from Complex.conj_ofReal c) (IsSelfAdjoint.one _)
private lemma isCompact_closedBox (γ γ' : Fin n → ℝ) : IsCompact (closedBox γ γ') :=
  isCompact_univ_pi fun _ => isCompact_Icc
private lemma exists_jointRepresentation
    (hB : BernsteinPositivity.BernsteinPositivityStatement)
    (hF : HilbertSpaceFacts.Facts) (hC : BorelCalculus.BorelCalculusTheorem)
    (hn : 1 ≤ n) (A : Fin n → H →L[ℂ] H) (γ γ' : Fin n → ℝ) (h : IsCommutingInBox A γ γ') :
    ∃ F : SpectralMeasure (closedBox γ γ') H, IsJointRepresentation F A ∧
      ∀ B : H →L[ℂ] H, (∀ i, Commute B (A i)) → ∀ Δ, Commute B (F Δ) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : CompactSpace (closedBox γ γ') := isCompact_iff_compactSpace.mp (isCompact_closedBox γ γ')
  have hA : PairwiseCommute A := h.commute
  have hL : BernsteinPositivity.SpectrallyBetween A γ γ' := fun i =>
    ⟨h.selfAdjoint i, h.lt i,
      isGE_of_le (h.selfAdjoint i) (isSelfAdjoint_ofReal_smul_one _) (h.lower_le i),
      isGE_of_le (isSelfAdjoint_ofReal_smul_one _) (h.selfAdjoint i) (h.le_upper i)⟩
  obtain ⟨-, hbound, hrules⟩ := hB n
  obtain ⟨hlin, hmulp, hsa⟩ := hrules H A hA
  have hbound' := hbound H A hA γ γ' hL
  let ρ := polyRestrict (closedBox γ γ')
  have hsup : ∀ p : MvPolynomial (Fin n) ℝ,
      (⨆ y : BernsteinPositivity.coordBox γ γ',
        |MvPolynomial.eval (y : Fin n → ℝ) p|) ≤ ‖ρ p‖ := by
    intro p
    haveI : Nonempty (BernsteinPositivity.coordBox γ γ') :=
      ⟨⟨γ, fun i _ => ⟨le_rfl, (h.lt i).le⟩⟩⟩
    refine ciSup_le fun y => ?_
    have h1 := (ρ p).norm_coe_le_norm ⟨y.1, y.2⟩
    rwa [polyRestrict_apply, Real.norm_eq_abs] at h1
  let L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] H →L[ℂ] H := hlin.mk' _
  have hLapply : ∀ p, L p = evalOperators p A hA := fun p => rfl
  have hnorm : ∀ p, ‖L p‖ ≤ 1 * ‖ρ p‖ := by
    intro p
    rw [one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    have hS : IsSelfAdjoint (L p) := hsa (fun i => h.selfAdjoint i) p
    have h1 : ⟪L p v, L p v⟫_ℂ = ⟪v, evalOperators (p * p) A hA v⟫_ℂ := by
      rw [hmulp, inner_map_left_of_selfAdjoint hS]
      rfl
    have h2 : ‖L p v‖ ^ 2 ≤ (‖ρ p‖ * ‖v‖) ^ 2 := by
      have h3 : ‖⟪L p v, L p v⟫_ℂ‖ = ‖L p v‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K]
        simp
      rw [← h3, h1]
      refine (hbound' (p * p) v).trans ?_
      have h4 : ‖ρ (p * p)‖ ≤ ‖ρ p‖ ^ 2 := by
        rw [map_mul, sq]
        exact norm_mul_le _ _
      rw [mul_pow]
      gcongr
      exact (hsup (p * p)).trans h4
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h2
  let Φ : C(closedBox γ γ', ℝ) →L[ℝ] H →L[ℂ] H :=
    LinearMap.extendOfNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ) L ρ.toLinearMap
  have hdense : DenseRange (ρ : MvPolynomial (Fin n) ℝ → C(closedBox γ γ', ℝ)) :=
    denseRange_polyRestrict _
  have hΦρ : ∀ p, Φ (ρ p) = evalOperators p A hA := fun p =>
    LinearMap.extendOfNorm_eq (f := L) (e := ρ.toLinearMap) hdense ⟨1, hnorm⟩ p
  have hΦ : IsUnitalCalculus Φ :=
    { map_one := by
        have := hΦρ 1
        rwa [map_one, evalOperators_one] at this
      map_mul := fun f g => hdense.induction_on₂ (p := fun f g => Φ (f * g) = Φ f * Φ g)
        (isClosed_eq (Φ.continuous.comp (continuous_fst.mul continuous_snd))
          ((Φ.continuous.comp continuous_fst).mul (Φ.continuous.comp continuous_snd)))
        (fun p q => by
          simp only [← map_mul, hΦρ]
          rw [hmulp]) f g
      isSelfAdjoint := fun f => hdense.induction_on (p := fun f => IsSelfAdjoint (Φ f)) f
        (isClosed_eq (continuous_star.comp Φ.continuous) Φ.continuous)
        (fun p => by
          show IsSelfAdjoint (Φ (ρ p))
          rw [hΦρ]
          exact hsa (fun i => h.selfAdjoint i) p) }
  obtain ⟨F, hFd, hFc⟩ :=
    exists_spectralMeasure_of_calc hF hn (measurableSet_closedBox γ γ') hΦ
  have hb : BoundedFunctionalCalculus F := ((hC H n).1 _ F).1
  refine ⟨F, fun i => ?_, fun B hBA Δ => ?_⟩
  · have hAi : A i = Φ (coordCont i) := by
      rw [← polyRestrict_X, ← evalOperators_X A hA i]
      exact (hΦρ _).symm
    rw [hAi]
    refine (integralOp_eq_of_isDiagonalIntegral hb (measurable_toComplexFn (coordCont i))
      (isBoundedFn_toComplexFn (coordCont i)) fun v => ?_).symm
    rw [hFd]
    exact integral_ofReal.symm
  · refine hFc B (fun f => ?_) Δ
    refine hdense.induction_on (p := fun f => Commute B (Φ f)) f
      (isClosed_eq (continuous_const.mul Φ.continuous) (Φ.continuous.mul continuous_const))
      fun p => ?_
    show Commute B (Φ (ρ p))
    rw [hΦρ]
    exact commute_evalOperators A hA hBA p
private lemma extendCarrier_univ_eq (hF : HilbertSpaceFacts.Facts)
    (hC : BorelCalculus.BorelCalculusTheorem) (A : Fin n → H →L[ℂ] H)
    {γ γ' γ₂ γ₂' : Fin n → ℝ} (F : SpectralMeasure (closedBox γ γ') H)
    (F₂ : SpectralMeasure (closedBox γ₂ γ₂') H) (hr : IsJointRepresentation F A)
    (hr₂ : IsJointRepresentation F₂ A) :
    F.extendCarrier (subset_univ _) MeasurableSet.univ =
      F₂.extendCarrier (subset_univ _) MeasurableSet.univ := by
  let l : Fin n → ℝ := fun i => min (γ i) (γ₂ i)
  let u : Fin n → ℝ := fun i => max (γ' i) (γ₂' i)
  have s₁ : closedBox γ γ' ⊆ closedBox l u := fun y hy i _ =>
    ⟨(min_le_left _ _).trans (hy i trivial).1, (hy i trivial).2.trans (le_max_left _ _)⟩
  have s₂ : closedBox γ₂ γ₂' ⊆ closedBox l u := fun y hy i _ =>
    ⟨(min_le_right _ _).trans (hy i trivial).1, (hy i trivial).2.trans (le_max_right _ _)⟩
  haveI : CompactSpace (closedBox l u) := isCompact_iff_compactSpace.mp (isCompact_closedBox l u)
  have hm := measurableSet_closedBox l u
  have e₁ : ∀ {K : Set (Fin n → ℝ)} (G : SpectralMeasure K H) (s : K ⊆ closedBox l u) (i : Fin n),
      (G.extendCarrier s hm).integralOp (coordFn i) = G.integralOp (coordFn i) :=
    fun G s i => integralOp_pushforward hC G _ hm _ _
      (measurable_toComplexFn (coordCont i)) (isBoundedFn_toComplexFn (coordCont i))
  have hG : F.extendCarrier s₁ hm = F₂.extendCarrier s₂ hm :=
    ext_of_integralOp_coordFn hC hF fun i => by rw [e₁, e₁, ← hr i, ← hr₂ i]
  have e₂ : ∀ {K : Set (Fin n → ℝ)} (G : SpectralMeasure K H) (s : K ⊆ closedBox l u),
      (G.extendCarrier s hm).extendCarrier (subset_univ _) MeasurableSet.univ =
        G.extendCarrier (subset_univ _) MeasurableSet.univ :=
    fun G s => SpectralMeasure.ext_apply fun Δ => rfl
  rw [← e₂ F s₁, ← e₂ F₂ s₂, hG]
private lemma ext_of_leftInverse (hF : HilbertSpaceFacts.Facts)
    (hC : BorelCalculus.BorelCalculusTheorem) (hn : 1 ≤ n) {n' : ℕ}
    {Y : Set (Fin n' → ℝ)} (E E' : SpectralMeasure Y H) (ι : Y → Fin n → ℝ)
    (κ : (Fin n → ℝ) → Y) (hι : Measurable ι) (hbd : ∃ c : ℝ, ∀ y, ‖ι y‖ ≤ c) (hκ : Measurable κ)
    (hleft : ∀ y, κ (ι y) = y)
    (heq : ∀ i, E.integralOp (fun y => ((ι y i : ℝ) : ℂ)) =
      E'.integralOp fun y => ((ι y i : ℝ) : ℂ)) : E = E' := by
  obtain ⟨c, hc⟩ := hbd
  let l : Fin n → ℝ := fun _ => -|c|
  let u : Fin n → ℝ := fun _ => |c|
  have hmem : ∀ y, ι y ∈ closedBox l u := fun y i _ => by
    have h1 : |ι y i| ≤ |c| := (norm_le_pi_norm (ι y) i).trans ((hc y).trans (le_abs_self c))
    exact abs_le.mp h1
  haveI : CompactSpace (closedBox l u) := isCompact_iff_compactSpace.mp (isCompact_closedBox l u)
  have hm := measurableSet_closedBox l u
  let ι' : Y → closedBox l u := fun y => ⟨ι y, hmem y⟩
  have hι' : Measurable ι' := hι.subtype_mk
  let κ' : closedBox l u → Y := fun y => κ y.1
  have hκ' : Measurable κ' := hκ.comp measurable_subtype_coe
  have hG : E.pushforward hn hm ι' hι' = E'.pushforward hn hm ι' hι' :=
    ext_of_integralOp_coordFn hC hF fun i => by
      have h₁ := integralOp_pushforward hC E hn hm ι' hι'
        (measurable_toComplexFn (coordCont i)) (isBoundedFn_toComplexFn (coordCont i))
      have h₂ := integralOp_pushforward hC E' hn hm ι' hι'
        (measurable_toComplexFn (coordCont i)) (isBoundedFn_toComplexFn (coordCont i))
      exact h₁.trans ((heq i).trans h₂.symm)
  have e : ∀ E₀ : SpectralMeasure Y H,
      (E₀.pushforward hn hm ι' hι').pushforward E.one_le_dimension E.measurableSet_carrier κ' hκ' =
        E₀ := by
    intro E₀
    refine SpectralMeasure.ext_apply fun Δ => ?_
    show E₀ _ = E₀ Δ
    congr 1
    refine Subtype.ext (Set.ext fun y => ?_)
    show κ (ι y) ∈ Δ.1 ↔ y ∈ Δ.1
    rw [hleft]
  rw [← e E, hG, e E']
end Polynomials
theorem jointSpectralTheorem_of_calculus
    (hB : BernsteinPositivity.BernsteinPositivityStatement)
    (hF : HilbertSpaceFacts.Facts)
    (hC : BorelCalculus.BorelCalculusTheorem) : JointSpectralTheorem := by
  intro H _ _ _ n hn
  refine ⟨fun A γ γ' h => ?_, fun n' Y E E' ι κ hι hbd hκ hleft heq =>
    ext_of_leftInverse hF hC hn E E' ι κ hι hbd hκ hleft heq⟩
  obtain ⟨F, hFr, hFc⟩ := exists_jointRepresentation hB hF hC hn A γ γ' h
  haveI : CompactSpace (closedBox γ γ') := isCompact_iff_compactSpace.mp (isCompact_closedBox γ γ')
  have huniq : ∀ F' : SpectralMeasure (closedBox γ γ') H, IsJointRepresentation F' A → F' = F :=
    fun F' h' => ext_of_integralOp_coordFn hC hF fun i => (h' i).symm.trans (hFr i)
  refine ⟨ExistsUnique.intro F hFr huniq, ?_, ?_, ?_⟩
  · exact Classical.epsilon_spec (p := fun F => IsJointRepresentation F A) ⟨F, hFr⟩
  · intro γ₂ γ₂' _ F₁ F₂ h₁ h₂
    exact extendCarrier_univ_eq hF hC A F₁ F₂ h₁ h₂
  · intro F' h' B hB' Δ
    rw [huniq F' h']
    exact hFc B hB' Δ
end YangMills.Construction.JointSpectral
