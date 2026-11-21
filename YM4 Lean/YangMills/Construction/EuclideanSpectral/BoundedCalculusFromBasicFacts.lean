import YangMills.Construction.EuclideanSpectral.ProjMeasureBoundedCalculus
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction.EuclideanSpectral
namespace ProjMeasure.BoundedCalculus
section BoundedBorelFunctions
variable {n : ℕ} [NeZero n]
theorem isBoundedBorelFn_add_smul {f g : EuclideanSpace ℝ (Fin n) → ℂ} (hf : IsBoundedBorelFn f)
    (hg : IsBoundedBorelFn g) (z : ℂ) : IsBoundedBorelFn (f + z • g) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  refine ⟨hfm.add (hgm.const_smul z), C + ‖z‖ * D, fun x => ?_⟩
  calc ‖(f + z • g) x‖ ≤ ‖f x‖ + ‖z • g x‖ := norm_add_le _ _
    _ = ‖f x‖ + ‖z‖ * ‖g x‖ := by rw [norm_smul]
    _ ≤ C + ‖z‖ * D := add_le_add (hC x) (mul_le_mul_of_nonneg_left (hD x) (norm_nonneg _))
theorem isBoundedBorelFn_mul {f g : EuclideanSpace ℝ (Fin n) → ℂ} (hf : IsBoundedBorelFn f)
    (hg : IsBoundedBorelFn g) : IsBoundedBorelFn (f * g) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  refine ⟨hfm.mul hgm, C * D, fun x => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hC x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
theorem isBoundedBorelFn_indicator {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : IsBoundedBorelFn f)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    IsBoundedBorelFn (B.indicator f) := by
  obtain ⟨hfm, C, hC⟩ := hf
  refine ⟨hfm.indicator hB, C, fun x => ?_⟩
  exact (norm_indicator_le_norm_self f x).trans (hC x)
theorem isBoundedBorelFn_indicator_one {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    IsBoundedBorelFn (B.indicator fun _ => (1 : ℂ)) :=
  isBoundedBorelFn_indicator ⟨measurable_const, 1, fun _ => by simp⟩ hB
theorem isBoundedBorelFn_conj {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : IsBoundedBorelFn f) :
    IsBoundedBorelFn fun x => conj (f x) := by
  obtain ⟨hfm, C, hC⟩ := hf
  refine ⟨Complex.continuous_conj.measurable.comp hfm, C, fun x => ?_⟩
  rw [RCLike.norm_conj]
  exact hC x
theorem induction_boundedBorelFn (P : (EuclideanSpace ℝ (Fin n) → ℂ) → Prop)
    (ind : ∀ B : BorelSubset n, P (B.1.indicator fun _ => 1))
    (lin : ∀ (f g : EuclideanSpace ℝ (Fin n) → ℂ) (z : ℂ), IsBoundedBorelFn f → IsBoundedBorelFn g →
      P f → P g → P (f + z • g))
    (lim : ∀ (fs : ℕ → EuclideanSpace ℝ (Fin n) → ℂ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (C : ℝ),
      (∀ k, Measurable (fs k)) → (∀ k x, ‖fs k x‖ ≤ C) → Measurable f →
      (∀ x, Tendsto (fun k => fs k x) atTop (𝓝 (f x))) → (∀ k, P (fs k)) → P f)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf : IsBoundedBorelFn f) : P f := by
  have hsb : ∀ s : SimpleFunc (EuclideanSpace ℝ (Fin n)) ℂ, IsBoundedBorelFn (s : _ → ℂ) :=
    fun s => ⟨s.measurable, s.exists_forall_norm_le⟩
  have hsimple : ∀ s : SimpleFunc (EuclideanSpace ℝ (Fin n)) ℂ, P s := by
    intro s
    induction s using SimpleFunc.induction with
    | @const c t ht =>
      have h0 := ind ⟨∅, MeasurableSet.empty⟩
      have h1 := ind ⟨t, ht⟩
      have := lin _ _ c (isBoundedBorelFn_indicator_one MeasurableSet.empty)
        (isBoundedBorelFn_indicator_one ht) h0 h1
      convert this using 1
      funext x
      by_cases hx : x ∈ t <;> simp [hx]
    | @add a b _ ha hb =>
      have := lin _ _ 1 (hsb a) (hsb b) ha hb
      simpa using this
  obtain ⟨hm, C, hC⟩ := hf
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hs := hm.stronglyMeasurable
  exact lim (fun k => hs.approxBounded C k) f C (fun k => (hs.approxBounded C k).measurable)
    (fun k x => hs.norm_approxBounded_le hC0 k x) hm
    (fun x => hs.tendsto_approxBounded_of_norm_le (hC x)) (fun k => hsimple _)
def cutoff (u : EuclideanSpace ℝ (Fin n) → ℂ) (k : ℕ) : EuclideanSpace ℝ (Fin n) → ℂ :=
  {x | ‖u x‖ ≤ (k : ℝ)}.indicator u
theorem isBoundedBorelFn_cutoff {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : Measurable u) (k : ℕ) :
    IsBoundedBorelFn (cutoff u k) := by
  refine ⟨hu.indicator (measurableSet_le hu.norm measurable_const), (k : ℝ), fun x => ?_⟩
  by_cases hx : ‖u x‖ ≤ (k : ℝ)
  · rw [cutoff, indicator_of_mem (show x ∈ {x | ‖u x‖ ≤ (k : ℝ)} from hx)]
    exact hx
  · rw [cutoff, indicator_of_notMem (show x ∉ {x | ‖u x‖ ≤ (k : ℝ)} from hx), norm_zero]
    exact Nat.cast_nonneg k
theorem cutoff_of_le {u : EuclideanSpace ℝ (Fin n) → ℂ} {k : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖u x‖ ≤ (k : ℝ)) : cutoff u k x = u x :=
  indicator_of_mem (show x ∈ {x | ‖u x‖ ≤ (k : ℝ)} from hx) _
theorem cutoff_of_not_le {u : EuclideanSpace ℝ (Fin n) → ℂ} {k : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : ¬ ‖u x‖ ≤ (k : ℝ)) : cutoff u k x = 0 :=
  indicator_of_notMem (show x ∉ {x | ‖u x‖ ≤ (k : ℝ)} from hx) _
theorem norm_cutoff_le (u : EuclideanSpace ℝ (Fin n) → ℂ) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖cutoff u k x‖ ≤ ‖u x‖ :=
  norm_indicator_le_norm_self u x
theorem norm_sub_cutoff_le (u : EuclideanSpace ℝ (Fin n) → ℂ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ‖u x - cutoff u k x‖ ≤ ‖u x‖ := by
  by_cases hx : ‖u x‖ ≤ (k : ℝ)
  · rw [cutoff_of_le hx, sub_self, norm_zero]
    exact norm_nonneg _
  · rw [cutoff_of_not_le hx, sub_zero]
theorem eventually_cutoff_eq (u : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    ∀ᶠ N : ℕ in atTop, cutoff u (N + 1) x = u x := by
  obtain ⟨K, hK⟩ := exists_nat_ge ‖u x‖
  filter_upwards [eventually_ge_atTop K] with N hN
  refine cutoff_of_le (hK.trans ?_)
  exact_mod_cast Nat.le_succ_of_le hN
theorem norm_cutoff_sub_cutoff_le (u : EuclideanSpace ℝ (Fin n) → ℂ) {a b N : ℕ} (ha : N ≤ a)
    (hb : N ≤ b) (x : EuclideanSpace ℝ (Fin n)) :
    ‖cutoff u (a + 1) x - cutoff u (b + 1) x‖ ≤ ‖u x - cutoff u (N + 1) x‖ := by
  by_cases hx : ‖u x‖ ≤ ((N + 1 : ℕ) : ℝ)
  · have h1 : ‖u x‖ ≤ ((a + 1 : ℕ) : ℝ) := hx.trans (by exact_mod_cast Nat.succ_le_succ ha)
    have h2 : ‖u x‖ ≤ ((b + 1 : ℕ) : ℝ) := hx.trans (by exact_mod_cast Nat.succ_le_succ hb)
    rw [cutoff_of_le h1, cutoff_of_le h2, sub_self, norm_zero]
    exact norm_nonneg _
  · rw [cutoff_of_not_le hx, sub_zero]
    by_cases h1 : ‖u x‖ ≤ ((a + 1 : ℕ) : ℝ) <;> by_cases h2 : ‖u x‖ ≤ ((b + 1 : ℕ) : ℝ)
    · rw [cutoff_of_le h1, cutoff_of_le h2, sub_self, norm_zero]
      exact norm_nonneg _
    · rw [cutoff_of_le h1, cutoff_of_not_le h2, sub_zero]
    · rw [cutoff_of_not_le h1, cutoff_of_le h2, zero_sub, norm_neg]
    · rw [cutoff_of_not_le h1, cutoff_of_not_le h2, sub_zero, norm_zero]
      exact norm_nonneg _
end BoundedBorelFunctions
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
  [NeZero n]
variable (hF : ProjMeasureBasicFacts) (E : ProjMeasure H n)
include hF E
theorem isFiniteMeasure_diagMeasure (ψ : H) : IsFiniteMeasure (E.diagMeasure ψ) :=
  ((hF H n E).2.2.1 ψ).1.1
theorem diag_eq_measureReal (ψ : H) (B : BorelSubset n) :
    E.diag ψ B = (((E.diagMeasure ψ).real B.1 : ℝ) : ℂ) :=
  ((hF H n E).2.2.1 ψ).1.2 B
theorem measureReal_eq_norm_sq (ψ : H) (B : BorelSubset n) :
    (E.diagMeasure ψ).real B.1 = ‖E B ψ‖ ^ 2 := by
  have h1 := diag_eq_measureReal hF E ψ B
  have h2 := ((hF H n E).2.2.1 ψ).2.1 B
  exact_mod_cast h1.symm.trans h2
theorem measureReal_univ_eq (ψ : H) : (E.diagMeasure ψ).real univ = ‖ψ‖ ^ 2 := by
  have h1 := diag_eq_measureReal hF E ψ (BorelSubset.univ n)
  have h2 := ((hF H n E).2.2.1 ψ).2.2
  exact_mod_cast h1.symm.trans h2
theorem isWeakIntegralOp_boundedIntegral {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : IsBoundedBorelFn f) : E.IsWeakIntegralOp f (E.boundedIntegral f) :=
  Classical.epsilon_spec ((hF H n E).2.2.2.2.2.2 f hf.1 hf.2).1.exists
theorem boundedIntegral_eq_of_isWeakIntegralOp {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : IsBoundedBorelFn f) {A : H →ₗ[ℂ] H} (hA : E.IsWeakIntegralOp f A) :
    E.boundedIntegral f = A :=
  ((hF H n E).2.2.2.2.2.2 f hf.1 hf.2).1.unique (isWeakIntegralOp_boundedIntegral hF E hf) hA
theorem norm_boundedIntegral_apply_sq {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : IsBoundedBorelFn f)
    (ψ : H) : ‖E.boundedIntegral f ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ) :=
  ((hF H n E).2.2.2.2.2.2 f hf.1 hf.2).2 _ (isWeakIntegralOp_boundedIntegral hF E hf) ψ
theorem integrable_of_isBoundedBorelFn {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : IsBoundedBorelFn f) (ψ : H) : Integrable f (E.diagMeasure ψ) := by
  haveI := isFiniteMeasure_diagMeasure hF E ψ
  obtain ⟨hm, C, hC⟩ := hf
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
theorem boundedIntegral_add_smul {f g : EuclideanSpace ℝ (Fin n) → ℂ} (hf : IsBoundedBorelFn f)
    (hg : IsBoundedBorelFn g) (z : ℂ) :
    E.boundedIntegral (f + z • g) = E.boundedIntegral f + z • E.boundedIntegral g := by
  refine boundedIntegral_eq_of_isWeakIntegralOp hF E (isBoundedBorelFn_add_smul hf hg z)
    fun ψ => ?_
  have h1 := isWeakIntegralOp_boundedIntegral hF E hf ψ
  have h2 := isWeakIntegralOp_boundedIntegral hF E hg ψ
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_right, inner_smul_right, h1, h2]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add (integrable_of_isBoundedBorelFn hF E hf ψ)
    ((integrable_of_isBoundedBorelFn hF E hg ψ).const_mul z), integral_const_mul]
theorem boundedIntegral_indicator_one (B : BorelSubset n) :
    E.boundedIntegral (B.1.indicator fun _ => 1) = E B := by
  refine boundedIntegral_eq_of_isWeakIntegralOp hF E (isBoundedBorelFn_indicator_one B.2)
    fun ψ => ?_
  haveI := isFiniteMeasure_diagMeasure hF E ψ
  have h := diag_eq_measureReal hF E ψ B
  rw [MeasureTheory.integral_indicator B.2]
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]
  simpa [diag, diagValue] using h
theorem boundedIntegral_one : E.boundedIntegral (fun _ => 1) = LinearMap.id := by
  have h := boundedIntegral_indicator_one hF E (BorelSubset.univ n)
  rw [show (BorelSubset.univ n).1 = univ from rfl, indicator_univ] at h
  rw [h]
  exact E.univ_eq_id
theorem ae_notMem_of_isNull {N : BorelSubset n} (hN : E.IsNull N) (ψ : H) :
    ∀ᵐ x ∂(E.diagMeasure ψ), x ∉ N.1 := by
  haveI := isFiniteMeasure_diagMeasure hF E ψ
  have h := measureReal_eq_norm_sq hF E ψ N
  have h0 : E N = 0 := hN
  rw [h0] at h
  simp only [LinearMap.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h
  exact measure_eq_zero_iff_ae_notMem.1 ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h)
theorem boundedIntegral_congr_off_null {f g : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : IsBoundedBorelFn f) (hg : IsBoundedBorelFn g) (N : BorelSubset n) (hN : E.IsNull N)
    (h : ∀ x, x ∉ N.1 → f x = g x) : E.boundedIntegral f = E.boundedIntegral g := by
  refine boundedIntegral_eq_of_isWeakIntegralOp hF E hf fun ψ => ?_
  rw [isWeakIntegralOp_boundedIntegral hF E hg ψ]
  exact integral_congr_ae ((ae_notMem_of_isNull hF E hN ψ).mono fun x hx => (h x hx).symm)
theorem norm_boundedIntegral_apply_le {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : IsBoundedBorelFn f)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ x, ‖f x‖ ≤ c) (ψ : H) :
    ‖E.boundedIntegral f ψ‖ ≤ c * ‖ψ‖ := by
  haveI := isFiniteMeasure_diagMeasure hF E ψ
  have h1 := norm_boundedIntegral_apply_sq hF E hf ψ
  have h2 : ‖∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ)‖ ≤ c ^ 2 * (E.diagMeasure ψ).real univ := by
    refine norm_integral_le_of_norm_le_const (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hc x) 2
  rw [← h1, measureReal_univ_eq hF E ψ, Real.norm_of_nonneg (by positivity)] at h2
  rw [← mul_pow] at h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
theorem tendsto_boundedIntegral_apply {fs : ℕ → EuclideanSpace ℝ (Fin n) → ℂ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ} {C : ℝ} (hfs : ∀ k, Measurable (fs k))
    (hb : ∀ k x, ‖fs k x‖ ≤ C) (hf : Measurable f)
    (hlim : ∀ x, Tendsto (fun k => fs k x) atTop (𝓝 (f x))) (ψ : H) :
    Tendsto (fun k => E.boundedIntegral (fs k) ψ) atTop (𝓝 (E.boundedIntegral f ψ)) := by
  haveI := isFiniteMeasure_diagMeasure hF E ψ
  have hfC : ∀ x, ‖f x‖ ≤ C := fun x =>
    le_of_tendsto ((hlim x).norm) (Eventually.of_forall fun k => hb k x)
  have hbf : IsBoundedBorelFn f := ⟨hf, C, hfC⟩
  have hbs : ∀ k, IsBoundedBorelFn (fs k) := fun k => ⟨hfs k, C, hb k⟩
  have hd : ∀ k, ‖E.boundedIntegral (fs k) ψ - E.boundedIntegral f ψ‖ ^ 2 =
      ∫ x, ‖fs k x - f x‖ ^ 2 ∂(E.diagMeasure ψ) := by
    intro k
    have h := norm_boundedIntegral_apply_sq hF E (isBoundedBorelFn_add_smul (hbs k) hbf (-1)) ψ
    rw [boundedIntegral_add_smul hF E (hbs k) hbf] at h
    simpa [sub_eq_add_neg] using h
  have h0 : Tendsto (fun k => ∫ x, ‖fs k x - f x‖ ^ 2 ∂(E.diagMeasure ψ)) atTop
      (𝓝 (∫ x, (0 : ℝ) ∂(E.diagMeasure ψ))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 * C) ^ 2)
      (fun k => (((hfs k).sub hf).norm.pow_const 2).aestronglyMeasurable)
      (integrable_const _) (fun k => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_of_nonneg (by positivity)]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      calc ‖fs k x - f x‖ ≤ ‖fs k x‖ + ‖f x‖ := norm_sub_le _ _
        _ ≤ 2 * C := by linarith [hb k x, hfC x]
    · have h1 : Tendsto (fun k => fs k x - f x) atTop (𝓝 0) := by
        simpa using (hlim x).sub_const (f x)
      simpa using h1.norm.pow 2
  rw [integral_zero] at h0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := h0.sqrt
  simp only [Real.sqrt_zero] at h1
  refine h1.congr fun k => ?_
  rw [← hd k, Real.sqrt_sq (norm_nonneg _)]
theorem tendsto_boundedIntegral_comp {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : IsBoundedBorelFn f)
    {v : ℕ → H} {w : H} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun k => E.boundedIntegral f (v k)) atTop (𝓝 (E.boundedIntegral f w)) := by
  obtain ⟨_, C, hC⟩ := id hf
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  exact (((E.boundedIntegral f).mkContinuous C
    (norm_boundedIntegral_apply_le hF E hf hC0 hC)).continuous.tendsto w).comp hv
theorem boundedIntegral_mul_indicator_one (D : BorelSubset n) {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : IsBoundedBorelFn f) :
    E.boundedIntegral (f * D.1.indicator fun _ => 1) = E.boundedIntegral f ∘ₗ E D := by
  have hD := isBoundedBorelFn_indicator_one D.2
  refine induction_boundedBorelFn
    (fun f => E.boundedIntegral (f * D.1.indicator fun _ => 1) = E.boundedIntegral f ∘ₗ E D)
    ?_ ?_ ?_ f hf
  · intro B
    have h1 : (B.1.indicator fun _ => (1 : ℂ)) * (D.1.indicator fun _ => (1 : ℂ)) =
        (B.1 ∩ D.1).indicator fun _ => 1 := by
      funext x
      by_cases hb : x ∈ B.1 <;> by_cases hc : x ∈ D.1 <;> simp [hb, hc]
    show E.boundedIntegral ((B.1.indicator fun _ => (1 : ℂ)) * (D.1.indicator fun _ => (1 : ℂ))) = _
    rw [h1, boundedIntegral_indicator_one hF E B]
    exact (boundedIntegral_indicator_one hF E ⟨B.1 ∩ D.1, B.2.inter D.2⟩).trans
      ((hF H n E).2.2.2.2.1.2.2 B D).symm
  · intro f g z hf hg h1 h2
    have h3 : (f + z • g) * D.1.indicator (fun _ => (1 : ℂ)) =
        f * D.1.indicator (fun _ => 1) + z • (g * D.1.indicator fun _ => 1) := by
      funext x
      simp [add_mul, mul_assoc]
    show E.boundedIntegral ((f + z • g) * D.1.indicator (fun _ => (1 : ℂ))) = _
    rw [h3, boundedIntegral_add_smul hF E (isBoundedBorelFn_mul hf hD) (isBoundedBorelFn_mul hg hD),
      h1, h2, boundedIntegral_add_smul hF E hf hg]
    ext ψ
    simp
  · intro fs f C hfs hb hf hlim hP
    ext ψ
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hb 0 0)
    have h1 := tendsto_boundedIntegral_apply hF E (fs := fun k => fs k * D.1.indicator fun _ => 1)
      (f := f * D.1.indicator fun _ => 1) (C := C)
      (fun k => (hfs k).mul (isBoundedBorelFn_indicator_one D.2).1)
      (fun k x => by
        by_cases hx : x ∈ D.1
        · simpa [hx] using hb k x
        · simpa [hx] using hC0)
      (hf.mul (isBoundedBorelFn_indicator_one D.2).1)
      (fun x => (hlim x).mul_const _) ψ
    have h2 := tendsto_boundedIntegral_apply hF E hfs hb hf hlim (E D ψ)
    refine tendsto_nhds_unique (h1.congr fun k => ?_) h2
    exact LinearMap.congr_fun (hP k) ψ
theorem boundedIntegral_mul {f g : EuclideanSpace ℝ (Fin n) → ℂ} (hf : IsBoundedBorelFn f)
    (hg : IsBoundedBorelFn g) :
    E.boundedIntegral (f * g) = E.boundedIntegral f ∘ₗ E.boundedIntegral g := by
  refine induction_boundedBorelFn
    (fun g => E.boundedIntegral (f * g) = E.boundedIntegral f ∘ₗ E.boundedIntegral g)
    ?_ ?_ ?_ g hg
  · intro B
    show E.boundedIntegral (f * B.1.indicator fun _ => 1) = _
    rw [boundedIntegral_mul_indicator_one hF E B hf, boundedIntegral_indicator_one hF E B]
  · intro g h z hg hh h1 h2
    have h3 : f * (g + z • h) = f * g + z • (f * h) := by
      funext x
      simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    show E.boundedIntegral (f * (g + z • h)) = _
    rw [h3, boundedIntegral_add_smul hF E (isBoundedBorelFn_mul hf hg) (isBoundedBorelFn_mul hf hh),
      h1, h2, boundedIntegral_add_smul hF E hg hh]
    ext ψ
    simp
  · intro gs g D hgs hb hg hlim hP
    ext ψ
    obtain ⟨hfm, C, hC⟩ := id hf
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    have h1 := tendsto_boundedIntegral_apply hF E (fs := fun k => f * gs k) (f := f * g)
      (C := C * D) (fun k => hfm.mul (hgs k))
      (fun k x => by
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_mul (hC x) (hb k x) (norm_nonneg _) hC0)
      (hfm.mul hg) (fun x => (hlim x).const_mul _) ψ
    have h2 := tendsto_boundedIntegral_comp hF E hf
      (tendsto_boundedIntegral_apply hF E hgs hb hg hlim ψ)
    refine tendsto_nhds_unique (h1.congr fun k => ?_) h2
    exact LinearMap.congr_fun (hP k) ψ
theorem inner_boundedIntegral_conj {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : IsBoundedBorelFn f)
    (φ ψ : H) :
    inner ℂ (E.boundedIntegral (fun x => conj (f x)) φ) ψ = inner ℂ φ (E.boundedIntegral f ψ) := by
  refine induction_boundedBorelFn (fun f => ∀ φ ψ : H,
    inner ℂ (E.boundedIntegral (fun x => conj (f x)) φ) ψ = inner ℂ φ (E.boundedIntegral f ψ))
    ?_ ?_ ?_ f hf φ ψ
  · intro B φ ψ
    have h1 : (fun x => conj (B.1.indicator (fun _ => (1 : ℂ)) x)) =
        B.1.indicator fun _ => 1 := by
      funext x
      by_cases hb : x ∈ B.1 <;> simp [hb]
    rw [h1, boundedIntegral_indicator_one hF E B]
    exact (E.isOrthProj B).symm φ ψ
  · intro f g z hf hg h1 h2 φ ψ
    have h3 : (fun x => conj ((f + z • g) x)) =
        (fun x => conj (f x)) + conj z • (fun x => conj (g x)) := by
      funext x
      simp
    rw [h3, boundedIntegral_add_smul hF E (isBoundedBorelFn_conj hf) (isBoundedBorelFn_conj hg),
      boundedIntegral_add_smul hF E hf hg]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, h1, h2]
    simp
  · intro fs f D hfs hb hf hlim hP φ ψ
    have h1 := tendsto_boundedIntegral_apply hF E (fs := fun k x => conj (fs k x))
      (f := fun x => conj (f x)) (C := D)
      (fun k => Complex.continuous_conj.measurable.comp (hfs k))
      (fun k x => by rw [RCLike.norm_conj]; exact hb k x)
      (Complex.continuous_conj.measurable.comp hf)
      (fun x => (Complex.continuous_conj.tendsto _).comp (hlim x)) φ
    have h2 := tendsto_boundedIntegral_apply hF E hfs hb hf hlim ψ
    have h3 : Tendsto (fun k => inner ℂ (E.boundedIntegral (fun x => conj (fs k x)) φ) ψ) atTop
        (𝓝 (inner ℂ (E.boundedIntegral (fun x => conj (f x)) φ) ψ)) :=
      h1.inner tendsto_const_nhds
    have h4 : Tendsto (fun k => inner ℂ φ (E.boundedIntegral (fs k) ψ)) atTop
        (𝓝 (inner ℂ φ (E.boundedIntegral f ψ))) := tendsto_const_nhds.inner h2
    exact tendsto_nhds_unique (h3.congr fun k => hP k φ ψ) h4
theorem linearAndIndicator_holds : E.LinearAndIndicator :=
  ⟨fun _ _ z hf hg => boundedIntegral_add_smul hF E hf hg z, boundedIntegral_indicator_one hF E,
    boundedIntegral_one hF E⟩
theorem normBoundsNullSets_holds : E.NormBoundsNullSets := by
  refine ⟨fun f hf ψ => norm_boundedIntegral_apply_sq hF E hf ψ, ?_, ?_⟩
  · rintro f g hf hg ⟨N, hN, h⟩
    exact boundedIntegral_congr_off_null hF E hf hg N hN h
  · intro f hf B hB
    have hfB := isBoundedBorelFn_indicator hf B.2
    have heq : E.boundedIntegral f = E.boundedIntegral (B.1.indicator f) :=
      boundedIntegral_congr_off_null hF E hf hfB B.compl hB fun x hx => by
        have hxB : x ∈ B.1 := by_contra fun hn => hx ⟨mem_univ _, hn⟩
        rw [indicator_of_mem hxB]
    refine ⟨heq, ?_⟩
    have hc0 : 0 ≤ sSup ((fun x => ‖f x‖) '' B.1) :=
      Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact norm_nonneg _)
    obtain ⟨_, C, hC⟩ := id hf
    have hbdd : BddAbove ((fun x => ‖f x‖) '' B.1) := ⟨C, by rintro _ ⟨x, _, rfl⟩; exact hC x⟩
    have hle : ∀ x, ‖B.1.indicator f x‖ ≤ sSup ((fun x => ‖f x‖) '' B.1) := by
      intro x
      by_cases hx : x ∈ B.1
      · rw [indicator_of_mem hx]
        exact le_csSup hbdd ⟨x, hx, rfl⟩
      · rw [indicator_of_notMem hx, norm_zero]
        exact hc0
    have hb : ∀ ψ, ‖E.boundedIntegral f ψ‖ ≤ sSup ((fun x => ‖f x‖) '' B.1) * ‖ψ‖ := fun ψ => by
      rw [heq]
      exact norm_boundedIntegral_apply_le hF E hfB hc0 hle ψ
    exact ⟨(E.boundedIntegral f).mkContinuous _ hb, by ext ψ; rfl,
      LinearMap.mkContinuous_norm_le _ hc0 hb⟩
theorem unitaryIntegral_holds : E.UnitaryIntegral := by
  intro f hf B hB h1
  have hc := isBoundedBorelFn_conj hf
  have hone : IsBoundedBorelFn (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℂ)) :=
    ⟨measurable_const, 1, fun _ => by simp⟩
  have hid : ∀ g : EuclideanSpace ℝ (Fin n) → ℂ, IsBoundedBorelFn g → (∀ x ∈ B.1, g x = 1) →
      E.boundedIntegral g = LinearMap.id := by
    intro g hg h
    rw [← boundedIntegral_one hF E]
    exact boundedIntegral_congr_off_null hF E hg hone B.compl hB fun x hx =>
      h x (by_contra fun hn => hx ⟨mem_univ _, hn⟩)
  have hl : E.boundedIntegral (fun x => conj (f x)) ∘ₗ E.boundedIntegral f = LinearMap.id := by
    rw [← boundedIntegral_mul hF E hc hf]
    refine hid _ (isBoundedBorelFn_mul hc hf) fun x hx => ?_
    simp [Complex.conj_mul', h1 x hx]
  have hr : E.boundedIntegral f ∘ₗ E.boundedIntegral (fun x => conj (f x)) = LinearMap.id := by
    rw [← boundedIntegral_mul hF E hf hc]
    refine hid _ (isBoundedBorelFn_mul hf hc) fun x hx => ?_
    simp [Complex.mul_conj', h1 x hx]
  have hU : IsUnitaryMap (E.boundedIntegral f) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Function.LeftInverse.injective (g := E.boundedIntegral fun x => conj (f x))
        fun ψ => LinearMap.congr_fun hl ψ
    · exact Function.RightInverse.surjective (g := E.boundedIntegral fun x => conj (f x))
        fun ψ => LinearMap.congr_fun hr ψ
    · intro ψ
      haveI := isFiniteMeasure_diagMeasure hF E ψ
      have h3 : ∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ) = ‖ψ‖ ^ 2 := by
        rw [← measureReal_univ_eq hF E ψ]
        have h4 : ∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ) = ∫ _, (1 : ℝ) ∂(E.diagMeasure ψ) :=
          integral_congr_ae ((ae_notMem_of_isNull hF E hB ψ).mono fun x hx => by
            have hxB : x ∈ B.1 := by_contra fun hn => hx ⟨mem_univ _, hn⟩
            simp [h1 x hxB])
        rw [h4]
        simp
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
        ((norm_boundedIntegral_apply_sq hF E hf ψ).trans h3)
  refine ⟨hU, ?_⟩
  ext ψ
  apply hU.bijective.1
  exact ((LinearEquiv.ofBijective _ hU.bijective).apply_symm_apply ψ).trans
    (LinearMap.congr_fun hr ψ).symm
theorem inner_inv_apply {U : H →ₗ[ℂ] H} (hU : IsUnitaryMap U) (φ χ : H) :
    inner ℂ φ (hU.inv χ) = inner ℂ (U φ) χ := by
  have h := ((hF H n E).1.2 U hU φ (hU.inv χ)).1
  have h2 : U (hU.inv χ) = χ := (LinearEquiv.ofBijective U hU.bijective).apply_symm_apply χ
  rw [h2] at h
  exact h.symm
theorem exists_homeoUnitaryTransport {U : H →ₗ[ℂ] H} (hU : IsUnitaryMap U)
    (κ : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    ∃ E' : ProjMeasure H n,
      ∀ B : BorelSubset n, E' B = hU.inv ∘ₗ E (homeoImage κ B) ∘ₗ U := by
  refine ⟨{ toFun := fun B => hU.inv ∘ₗ E (homeoImage κ B) ∘ₗ U
            isOrthProj := fun B =>
              ((hF H n E).2.1 _ (E.isOrthProj _)).2 U hU
            univ_eq_id := ?_
            hasSum_diag := ?_ }, fun _ => rfl⟩
  · have h1 : homeoImage κ (BorelSubset.univ n) = BorelSubset.univ n :=
      Subtype.ext (by simp [homeoImage, BorelSubset.univ])
    rw [h1, E.univ_eq_id]
    ext ψ
    exact (LinearEquiv.ofBijective U hU.bijective).symm_apply_apply ψ
  · intro ψ B hB
    have hd : Pairwise (fun k l => Disjoint (homeoImage κ (B k)).1
        (homeoImage κ (B l)).1) := fun k l hkl =>
      (disjoint_image_iff κ.injective).2 (hB hkl)
    have h := E.hasSum_diag (U ψ) (fun k => homeoImage κ (B k)) hd
    have hu : BorelSubset.unionSeq (fun k => homeoImage κ (B k)) =
        homeoImage κ (BorelSubset.unionSeq B) :=
      Subtype.ext (by simp [homeoImage, BorelSubset.unionSeq, image_iUnion])
    rw [hu] at h
    show HasSum (fun k => inner ℂ ψ (hU.inv (E (homeoImage κ (B k)) (U ψ))))
      (inner ℂ ψ (hU.inv (E (homeoImage κ (BorelSubset.unionSeq B)) (U ψ))))
    simp only [inner_inv_apply hF E hU]
    exact h
theorem homeoUnitaryTransport_holds : E.HomeoUnitaryTransport := by
  intro U hU κ
  obtain ⟨E', hE'⟩ := exists_homeoUnitaryTransport hF E hU κ
  have hm : ∀ (ψ : H) (B : BorelSubset n),
      E'.diag ψ B = E.diag (U ψ) (homeoImage κ B) := by
    intro ψ B
    show inner ℂ ψ (E' B ψ) = inner ℂ (U ψ) (E (homeoImage κ B) (U ψ))
    rw [hE' B]
    exact inner_inv_apply hF E hU ψ _
  have hmap : ∀ ψ : H, E'.diagMeasure ψ = Measure.map κ.symm (E.diagMeasure (U ψ)) := by
    intro ψ
    haveI := isFiniteMeasure_diagMeasure hF E' ψ
    haveI := isFiniteMeasure_diagMeasure hF E (U ψ)
    ext s hs
    rw [Measure.map_apply κ.symm.continuous.measurable hs]
    have h1 := hm ψ ⟨s, hs⟩
    rw [diag_eq_measureReal hF E' ψ, diag_eq_measureReal hF E (U ψ)] at h1
    have h2 : (E'.diagMeasure ψ).real s = (E.diagMeasure (U ψ)).real (κ '' s) := by
      exact_mod_cast h1
    have h3 : κ.symm ⁻¹' s = κ '' s := (κ.toEquiv.image_eq_preimage_symm s).symm
    rw [h3]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h2
  refine ⟨E', hE', hm, fun f hf => ?_⟩
  have hfk : IsBoundedBorelFn (f ∘ κ.symm) :=
    ⟨hf.1.comp κ.symm.continuous.measurable, hf.2.imp fun C h x => h _⟩
  refine boundedIntegral_eq_of_isWeakIntegralOp hF E' hf fun ψ => ?_
  have h1 := isWeakIntegralOp_boundedIntegral hF E hfk (U ψ)
  show inner ℂ ψ (hU.inv (E.boundedIntegral (f ∘ κ.symm) (U ψ))) = _
  rw [inner_inv_apply hF E hU, h1, hmap ψ,
    integral_map κ.symm.continuous.measurable.aemeasurable hf.1.aestronglyMeasurable]
  rfl
theorem diagMeasure_smul (z : ℂ) (ψ : H) :
    E.diagMeasure (z • ψ) = ENNReal.ofReal (‖z‖ ^ 2) • E.diagMeasure ψ := by
  haveI := isFiniteMeasure_diagMeasure hF E ψ
  haveI := isFiniteMeasure_diagMeasure hF E (z • ψ)
  ext s hs
  have h1 := ((hF H n E).2.2.2.1 ψ ψ z ⟨s, hs⟩).1
  rw [diag_eq_measureReal hF E (z • ψ), diag_eq_measureReal hF E ψ] at h1
  have h2 : (E.diagMeasure (z • ψ)).real s = ‖z‖ ^ 2 * (E.diagMeasure ψ).real s := by
    exact_mod_cast h1
  rw [Measure.smul_apply, smul_eq_mul, ← ofReal_measureReal (μ := E.diagMeasure (z • ψ)),
    ← ofReal_measureReal (μ := E.diagMeasure ψ), h2, ENNReal.ofReal_mul (by positivity)]
theorem diagMeasure_add_le (φ ψ : H) :
    E.diagMeasure (φ + ψ) ≤ (2 : ℝ≥0∞) • E.diagMeasure φ + (2 : ℝ≥0∞) • E.diagMeasure ψ := by
  haveI := isFiniteMeasure_diagMeasure hF E ψ
  haveI := isFiniteMeasure_diagMeasure hF E φ
  haveI := isFiniteMeasure_diagMeasure hF E (φ + ψ)
  refine Measure.le_iff.2 fun s hs => ?_
  have h := ((hF H n E).2.2.2.1 φ ψ 0 ⟨s, hs⟩).2
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [← ofReal_measureReal (μ := E.diagMeasure (φ + ψ)),
    ← ofReal_measureReal (μ := E.diagMeasure φ), ← ofReal_measureReal (μ := E.diagMeasure ψ)]
  refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)]
  simp
theorem exists_submodule_fnDomainSet (u : EuclideanSpace ℝ (Fin n) → ℂ) :
    ∃ S : Submodule ℂ H, (S : Set H) = E.fnDomainSet u := by
  refine ⟨{ carrier := E.fnDomainSet u, add_mem' := ?_, zero_mem' := ?_,
            smul_mem' := ?_ }, rfl⟩
  · intro φ ψ hφ hψ
    show ∫⁻ x, ‖u x‖ₑ ^ 2 ∂(E.diagMeasure (φ + ψ)) < ⊤
    refine (lintegral_mono' (diagMeasure_add_le hF E φ ψ) le_rfl).trans_lt ?_
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hφ, ENNReal.mul_lt_top (by simp) hψ⟩
  · show ∫⁻ x, ‖u x‖ₑ ^ 2 ∂(E.diagMeasure 0) < ⊤
    have h := diagMeasure_smul hF E 0 (0 : H)
    simp only [smul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      ENNReal.ofReal_zero, zero_smul] at h
    rw [h]
    simp
  · intro z ψ hψ
    show ∫⁻ x, ‖u x‖ₑ ^ 2 ∂(E.diagMeasure (z • ψ)) < ⊤
    rw [diagMeasure_smul hF E z ψ, lintegral_smul_measure]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hψ
theorem coe_fnDomain (u : EuclideanSpace ℝ (Fin n) → ℂ) :
    ((E.fnDomain u : Submodule ℂ H) : Set H) = E.fnDomainSet u :=
  Classical.epsilon_spec (exists_submodule_fnDomainSet hF E u)
theorem mem_fnDomainSet_iff {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : Measurable u) (ψ : H) :
    ψ ∈ E.fnDomainSet u ↔ Integrable (fun x => ‖u x‖ ^ 2) (E.diagMeasure ψ) := by
  have hm : AEStronglyMeasurable (fun x => ‖u x‖ ^ 2) (E.diagMeasure ψ) :=
    (hu.norm.pow_const 2).aestronglyMeasurable
  have he : ∀ x, ‖‖u x‖ ^ 2‖ₑ = ‖u x‖ₑ ^ 2 := fun x => by rw [enorm_pow, enorm_norm]
  simp only [fnDomainSet, mem_ofPred_eq, Integrable, hm, true_and, HasFiniteIntegral, he]
theorem tendsto_integral_sub_cutoff {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : Measurable u) {ψ : H}
    (hψ : Integrable (fun x => ‖u x‖ ^ 2) (E.diagMeasure ψ)) :
    Tendsto (fun N : ℕ => ∫ x, ‖u x - cutoff u (N + 1) x‖ ^ 2 ∂(E.diagMeasure ψ)) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => ∫ x, ‖u x - cutoff u (N + 1) x‖ ^ 2 ∂(E.diagMeasure ψ)) atTop
      (𝓝 (∫ _, (0 : ℝ) ∂(E.diagMeasure ψ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖u x‖ ^ 2)
      (fun N => ((hu.sub (isBoundedBorelFn_cutoff hu (N + 1)).1).norm.pow_const 2).aestronglyMeasurable)
      hψ (fun N => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_cutoff_le u _ x) 2
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_cutoff_eq u x] with N hN
      rw [hN]
      simp
  simpa using h
theorem tendsto_integral_cutoff_sq {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : Measurable u) {ψ : H}
    (hψ : Integrable (fun x => ‖u x‖ ^ 2) (E.diagMeasure ψ)) :
    Tendsto (fun N : ℕ => ∫ x, ‖cutoff u (N + 1) x‖ ^ 2 ∂(E.diagMeasure ψ)) atTop
      (𝓝 (∫ x, ‖u x‖ ^ 2 ∂(E.diagMeasure ψ))) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖u x‖ ^ 2)
    (fun N => ((isBoundedBorelFn_cutoff hu (N + 1)).1.norm.pow_const 2).aestronglyMeasurable)
    hψ (fun N => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_cutoff_le u _ x) 2
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_cutoff_eq u x] with N hN
    rw [hN]
theorem cauchySeq_boundedIntegral_cutoff {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : Measurable u)
    {ψ : H} (hψ : Integrable (fun x => ‖u x‖ ^ 2) (E.diagMeasure ψ)) :
    CauchySeq fun k : ℕ => E.boundedIntegral (cutoff u (k + 1)) ψ := by
  refine cauchySeq_of_le_tendsto_0
    (fun N : ℕ => Real.sqrt (∫ x, ‖u x - cutoff u (N + 1) x‖ ^ 2 ∂(E.diagMeasure ψ))) ?_ ?_
  · intro a b N ha hb
    have hca := isBoundedBorelFn_cutoff hu (a + 1)
    have hcb := isBoundedBorelFn_cutoff hu (b + 1)
    have h := norm_boundedIntegral_apply_sq hF E (isBoundedBorelFn_add_smul hca hcb (-1)) ψ
    rw [boundedIntegral_add_smul hF E hca hcb] at h
    have h' : ‖E.boundedIntegral (cutoff u (a + 1)) ψ - E.boundedIntegral (cutoff u (b + 1)) ψ‖ ^ 2 =
        ∫ x, ‖cutoff u (a + 1) x - cutoff u (b + 1) x‖ ^ 2 ∂(E.diagMeasure ψ) := by
      simpa [sub_eq_add_neg] using h
    rw [dist_eq_norm]
    apply Real.le_sqrt_of_sq_le
    rw [h']
    have hi2 : Integrable (fun x => ‖u x - cutoff u (N + 1) x‖ ^ 2) (E.diagMeasure ψ) :=
      hψ.mono' ((hu.sub (isBoundedBorelFn_cutoff hu (N + 1)).1).norm.pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun x => by
          rw [Real.norm_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_cutoff_le u _ x) 2)
    have hi1 : Integrable (fun x => ‖cutoff u (a + 1) x - cutoff u (b + 1) x‖ ^ 2)
        (E.diagMeasure ψ) :=
      hi2.mono' ((hca.1.sub hcb.1).norm.pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun x => by
          rw [Real.norm_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_cutoff_sub_cutoff_le u ha hb x) 2)
    exact integral_mono hi1 hi2 fun x =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_cutoff_sub_cutoff_le u ha hb x) 2
  · simpa using (tendsto_integral_sub_cutoff hF E hu hψ).sqrt
theorem exists_isTruncLimit {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : Measurable u) :
    ∃ A : E.fnDomain u →ₗ[ℂ] H, E.IsTruncLimit u A := by
  have hmem : ∀ ψ : E.fnDomain u, Integrable (fun x => ‖u x‖ ^ 2)
      (E.diagMeasure (ψ : H)) := by
    intro ψ
    have h : (ψ : H) ∈ ((E.fnDomain u : Submodule ℂ H) : Set H) := ψ.2
    rw [coe_fnDomain hF E u] at h
    exact (mem_fnDomainSet_iff hF E hu _).1 h
  have hlim : ∀ ψ : E.fnDomain u, ∃ v : H,
      Tendsto (fun k : ℕ => E.truncIntegral u (k + 1) (ψ : H)) atTop (𝓝 v) :=
    fun ψ => cauchySeq_tendsto_of_complete (cauchySeq_boundedIntegral_cutoff hF E hu (hmem ψ))
  choose L hL using hlim
  refine ⟨{ toFun := L, map_add' := ?_, map_smul' := ?_ }, hL⟩
  · intro a b
    refine tendsto_nhds_unique (hL (a + b)) ?_
    have h := (hL a).add (hL b)
    simpa only [Submodule.coe_add, map_add] using h
  · intro z a
    refine tendsto_nhds_unique (hL (z • a)) ?_
    have h := (hL a).const_smul z
    simpa only [Submodule.coe_smul, map_smul, RingHom.id_apply] using h
theorem unboundedFunctions_holds : E.UnboundedFunctions := by
  intro u hu
  have hcoe := coe_fnDomain hF E u
  have hlim : E.IsTruncLimit u (E.truncLimit u) :=
    Classical.epsilon_spec (exists_isTruncLimit hF E hu)
  refine ⟨hcoe, hlim, fun ψ => ?_, fun B hB => ?_⟩
  · have h : (ψ : H) ∈ ((E.fnDomain u : Submodule ℂ H) : Set H) := ψ.2
    rw [hcoe] at h
    have hψ := (mem_fnDomainSet_iff hF E hu _).1 h
    have h1 := (hlim ψ).norm.pow 2
    refine tendsto_nhds_unique h1 ((tendsto_integral_cutoff_sq hF E hu hψ).congr fun k => ?_)
    exact (norm_boundedIntegral_apply_sq hF E (isBoundedBorelFn_cutoff hu (k + 1)) ψ).symm
  · rintro ⟨c, hc⟩
    have hB' : ∀ (ψ : H), ∀ᵐ x ∂(E.diagMeasure ψ), x ∈ B.1 := fun ψ =>
      (ae_notMem_of_isNull hF E hB ψ).mono fun x hx => by_contra fun hn => hx ⟨mem_univ _, hn⟩
    constructor
    · refine eq_univ_of_forall fun ψ => ?_
      haveI := isFiniteMeasure_diagMeasure hF E ψ
      refine (mem_fnDomainSet_iff hF E hu ψ).2 ?_
      refine Integrable.of_bound (hu.norm.pow_const 2).aestronglyMeasurable (c ^ 2)
        ((hB' ψ).mono fun x hx => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hc x hx) 2
    · intro ψ
      have hbB : IsBoundedBorelFn (B.1.indicator u) := by
        refine ⟨hu.indicator B.2, max c 0, fun x => ?_⟩
        by_cases hx : x ∈ B.1
        · rw [indicator_of_mem hx]
          exact (hc x hx).trans (le_max_left _ _)
        · rw [indicator_of_notMem hx, norm_zero]
          exact le_max_right _ _
      refine tendsto_nhds_unique (hlim ψ) (tendsto_const_nhds.congr' ?_)
      obtain ⟨K, hK⟩ := exists_nat_ge c
      filter_upwards [eventually_ge_atTop K] with N hN
      have h2 : E.boundedIntegral (cutoff u (N + 1)) = E.boundedIntegral (B.1.indicator u) :=
        boundedIntegral_congr_off_null hF E (isBoundedBorelFn_cutoff hu (N + 1)) hbB B.compl hB
          fun x hx => by
            have hxB : x ∈ B.1 := by_contra fun hn => hx ⟨mem_univ _, hn⟩
            rw [indicator_of_mem hxB]
            refine cutoff_of_le (((hc x hxB).trans hK).trans ?_)
            exact_mod_cast Nat.le_succ_of_le hN
      exact (LinearMap.congr_fun h2 (ψ : H)).symm
end ProjMeasure.BoundedCalculus
open ProjMeasure ProjMeasure.BoundedCalculus in
theorem projMeasureBoundedCalculus_of_basicFacts (hF : ProjMeasureBasicFacts) :
    ProjMeasureBoundedCalculus := by
  intro H _ _ _ n _ E
  exact ⟨linearAndIndicator_holds hF E, normBoundsNullSets_holds hF E,
    fun _ _ hf hg => boundedIntegral_mul hF E hf hg,
    fun _ hf φ ψ => inner_boundedIntegral_conj hF E hf φ ψ, unitaryIntegral_holds hF E,
    homeoUnitaryTransport_holds hF E, unboundedFunctions_holds hF E⟩
end YangMills.Construction.EuclideanSpectral
