import YangMills.Construction.Matrices.EntrywiseHolomorphyRestriction
import YangMills.Construction.Matrices.ExpChartHolomorphyProof
import YangMills.Construction.Matrices.UnimodularArgumentHolomorphyProof
import Mathlib
open Filter Set Metric MeasureTheory
open scoped ContDiff Topology Real NNReal ENNReal Matrix.Norms.L2Operator
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
def HolomorphicInEachVariable {N : ℕ} (f : ComplexCoordinates N → E) (a : ComplexCoordinates N)
    (ρ : ℝ) : Prop :=
  ContinuousOn f (closedPolydisk a ρ) ∧ ∀ z ∈ closedPolydisk a ρ, ∀ j, ∀ t ∈ ball (a j) ρ,
    DifferentiableAt ℂ (fun s => f (Function.update z j s)) t
theorem differentiableAt_intervalIntegral_circle {u : ℂ → ℝ → E} {t₀ : ℂ} {δ M : ℝ}
    (hδ : 0 < δ)
    (hcont : ∀ t ∈ ball t₀ (2 * δ), Continuous (u t))
    (hbound : ∀ t ∈ ball t₀ (2 * δ), ∀ θ, ‖u t θ‖ ≤ M)
    (hdiff : ∀ θ, ∀ t ∈ ball t₀ (2 * δ), DifferentiableAt ℂ (fun s => u s θ) t) :
    DifferentiableAt ℂ (fun t => ∫ θ in (0 : ℝ)..2 * π, u t θ) t₀ := by
  have h0 : t₀ ∈ ball t₀ (2 * δ) := mem_ball_self (by positivity)
  have hsub : ball t₀ δ ⊆ ball t₀ (2 * δ) := ball_subset_ball (by linarith)
  have hbd : ∀ t ∈ ball t₀ δ, ∀ θ, ‖deriv (fun s => u s θ) t‖ ≤ M / δ := by
    intro t ht θ
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ ?_ ?_
    · have hclosed : closedBall t δ ⊆ ball t₀ (2 * δ) := by
        intro w hw
        rw [mem_closedBall] at hw
        rw [mem_ball] at ht ⊢
        have := dist_triangle w t t₀
        linarith
      exact DifferentiableOn.diffContOnCl_ball
        (fun w hw => (hdiff θ w hw).differentiableWithinAt) hclosed
    · intro w hw
      refine hbound w ?_ θ
      rw [mem_sphere] at hw
      rw [mem_ball] at ht ⊢
      have := dist_triangle w t t₀
      linarith
  have hmeas : AEStronglyMeasurable (fun θ => deriv (fun s => u s θ) t₀)
      (volume.restrict (Set.uIoc (0 : ℝ) (2 * π))) := by
    let v : ℕ → ℂ := fun n => ((δ / (n + 1) : ℝ) : ℂ)
    have hv0 : ∀ n, v n ≠ 0 := by
      intro n
      simp only [v]
      exact_mod_cast (by positivity : δ / ((n : ℝ) + 1) ≠ 0)
    have hvlim : Tendsto v atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hv0⟩
      have : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat δ |>.comp (tendsto_add_atTop_nat 1) |>.congr
          (fun n => by simp)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp this
      simp only [Complex.ofReal_zero] at h2
      exact h2
    have hnorm : ∀ᶠ n in atTop, t₀ + v n ∈ ball t₀ (2 * δ) := by
      have : Tendsto (fun n => t₀ + v n) atTop (𝓝 t₀) := by
        simpa using tendsto_const_nhds.add (hvlim.mono_right nhdsWithin_le_nhds)
      exact this.eventually (isOpen_ball.mem_nhds h0)
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hnorm
    refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ)
      (f := fun n θ => (v (n + n₀))⁻¹ • (u (t₀ + v (n + n₀)) θ - u t₀ θ)) ?_ ?_
    · intro n
      exact (((hcont _ (hn₀ _ (by omega))).sub (hcont _ h0)).const_smul _).aestronglyMeasurable
    · refine Eventually.of_forall fun θ => ?_
      have := hasDerivAt_iff_tendsto_slope_zero.1 (hdiff θ t₀ h0).hasDerivAt
      exact this.comp (hvlim.comp (tendsto_add_atTop_nat n₀))
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 2 * π)
    (F := u) (F' := fun t θ => deriv (fun s => u s θ) t) (x₀ := t₀) (s := ball t₀ δ)
    (bound := fun _ => M / δ) (ball_mem_nhds t₀ hδ)
    (by
      filter_upwards [isOpen_ball.mem_nhds h0] with t ht
      exact (hcont t ht).aestronglyMeasurable)
    ((hcont t₀ h0).intervalIntegrable _ _) hmeas
    (ae_of_all _ fun θ _ t ht => hbd t ht θ) intervalIntegrable_const
    (ae_of_all _ fun θ _ t ht => (hdiff θ t (hsub ht)).hasDerivAt)
  exact hmain.2.differentiableAt
theorem continuous_finCons {N : ℕ} :
    Continuous fun p : ℂ × ComplexCoordinates N =>
      (Fin.cons p.1 p.2 : ComplexCoordinates (N + 1)) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (continuous_apply j).comp continuous_snd
theorem finCons_mem_closedPolydisk {N : ℕ} {a : ComplexCoordinates (N + 1)} {ρ : ℝ} {w : ℂ}
    {z : ComplexCoordinates N} (hw : ‖w - a 0‖ ≤ ρ) (hz : z ∈ closedPolydisk (Fin.tail a) ρ) :
    (Fin.cons w z : ComplexCoordinates (N + 1)) ∈ closedPolydisk a ρ := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hw
  · simpa [Fin.tail] using hz j
theorem update_mem_closedPolydisk {N : ℕ} {a z : ComplexCoordinates N} {ρ : ℝ}
    (hz : z ∈ closedPolydisk a ρ) {j : Fin N} {t : ℂ} (ht : t ∈ ball (a j) ρ) :
    Function.update z j t ∈ closedPolydisk a ρ := by
  intro i
  by_cases h : i = j
  · subst h
    simpa [dist_eq_norm] using (mem_ball.1 ht).le
  · simpa [Function.update_of_ne h] using hz i
def sliceFirst {N : ℕ} (f : ComplexCoordinates (N + 1) → E) (z : ComplexCoordinates N)
    (w : ℂ) : E :=
  f (Fin.cons w z)
def cauchyCoeffFirst {N : ℕ} (f : ComplexCoordinates (N + 1) → E) (c : ℂ) (ρ : ℝ) (k : ℕ)
    (z : ComplexCoordinates N) : E :=
  cauchyPowerSeries (sliceFirst f z) c ρ k fun _ => 1
def cauchyIntegrand (c : ℂ) (ρ : ℝ) (k : ℕ) (θ : ℝ) : ℂ :=
  deriv (circleMap c ρ) θ * ((1 / (circleMap c ρ θ - c)) ^ k * (circleMap c ρ θ - c)⁻¹)
theorem cauchyCoeffFirst_eq_integral {N : ℕ} (f : ComplexCoordinates (N + 1) → E) (c : ℂ)
    (ρ : ℝ) (k : ℕ) (z : ComplexCoordinates N) :
    cauchyCoeffFirst f c ρ k z = (2 * π * Complex.I : ℂ)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * π, cauchyIntegrand c ρ k θ • f (Fin.cons (circleMap c ρ θ) z) := by
  rw [cauchyCoeffFirst, cauchyPowerSeries_apply, circleIntegral]
  simp only [sliceFirst, cauchyIntegrand, mul_smul]
theorem continuous_cauchyIntegrand {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    Continuous (cauchyIntegrand c ρ k) := by
  have h : ∀ θ : ℝ, circleMap 0 ρ θ ≠ 0 := fun θ => circleMap_ne_center hρ.ne'
  have hc : Continuous (circleMap 0 ρ) := continuous_circleMap 0 ρ
  have : cauchyIntegrand c ρ k =
      fun θ => (circleMap 0 ρ θ * Complex.I) *
        ((1 / circleMap 0 ρ θ) ^ k * (circleMap 0 ρ θ)⁻¹) := by
    funext θ
    simp [cauchyIntegrand, circleMap_sub_center, deriv_circleMap]
  rw [this]
  exact (hc.mul continuous_const).mul
    (((continuous_const.div hc h).pow k).mul (hc.inv₀ h))
theorem norm_cauchyIntegrand {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) (θ : ℝ) :
    ‖cauchyIntegrand c ρ k θ‖ = 1 / ρ ^ k := by
  have hn : ‖circleMap 0 ρ θ‖ = ρ := by simp [norm_circleMap_zero, abs_of_pos hρ]
  simp only [cauchyIntegrand, circleMap_sub_center, deriv_circleMap, norm_mul, norm_pow, norm_div,
    norm_inv, hn, Complex.norm_I, norm_one, mul_one]
  have h1 : 1 / ρ * ρ = 1 := by field_simp
  field_simp
  rw [← mul_pow, h1, one_pow]
theorem cauchyCoeffFirst_holomorphicInEachVariable {N : ℕ} {f : ComplexCoordinates (N + 1) → E}
    {a : ComplexCoordinates (N + 1)} {ρ M : ℝ} (hρ : 0 < ρ) (hf : HolomorphicInEachVariable f a ρ)
    (hM : ∀ z ∈ closedPolydisk a ρ, ‖f z‖ ≤ M) (k : ℕ) :
    HolomorphicInEachVariable (cauchyCoeffFirst f (a 0) ρ k) (Fin.tail a) ρ := by
  have hcircle : ∀ θ, ‖circleMap (a 0) ρ θ - a 0‖ ≤ ρ := by
    intro θ
    simp [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ]
  have hmem : ∀ θ z, z ∈ closedPolydisk (Fin.tail a) ρ →
      (Fin.cons (circleMap (a 0) ρ θ) z : ComplexCoordinates (N + 1)) ∈ closedPolydisk a ρ :=
    fun θ z hz => finCons_mem_closedPolydisk (hcircle θ) hz
  have hcθ : ∀ z ∈ closedPolydisk (Fin.tail a) ρ, Continuous fun θ =>
      cauchyIntegrand (a 0) ρ k θ • f (Fin.cons (circleMap (a 0) ρ θ) z) := by
    intro z hz
    refine (continuous_cauchyIntegrand hρ k).smul ?_
    exact hf.1.comp_continuous
      (continuous_finCons.comp ((continuous_circleMap _ _).prodMk continuous_const))
      (fun θ => hmem θ z hz)
  have hbound : ∀ z ∈ closedPolydisk (Fin.tail a) ρ, ∀ θ,
      ‖cauchyIntegrand (a 0) ρ k θ • f (Fin.cons (circleMap (a 0) ρ θ) z)‖ ≤ 1 / ρ ^ k * M := by
    intro z hz θ
    rw [norm_smul, norm_cauchyIntegrand hρ]
    exact mul_le_mul_of_nonneg_left (hM _ (hmem θ z hz)) (by positivity)
  constructor
  · intro z₀ hz₀
    have hint : ContinuousWithinAt (fun z => ∫ θ in (0 : ℝ)..2 * π,
        cauchyIntegrand (a 0) ρ k θ • f (Fin.cons (circleMap (a 0) ρ θ) z))
        (closedPolydisk (Fin.tail a) ρ) z₀ := by
      refine intervalIntegral.continuousWithinAt_of_dominated_interval
        (bound := fun _ => 1 / ρ ^ k * M) ?_ ?_ intervalIntegrable_const ?_
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact (hcθ z hz).aestronglyMeasurable
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact ae_of_all _ fun θ _ => hbound z hz θ
      · refine ae_of_all _ fun θ _ => ?_
        have hc : Continuous fun z : ComplexCoordinates N =>
            (Fin.cons (circleMap (a 0) ρ θ) z : ComplexCoordinates (N + 1)) :=
          continuous_finCons.comp (continuous_const.prodMk continuous_id)
        exact ((hf.1 _ (hmem θ z₀ hz₀)).comp hc.continuousWithinAt
          (fun z hz => hmem θ z hz)).const_smul (cauchyIntegrand (a 0) ρ k θ)
    have heq : cauchyCoeffFirst f (a 0) ρ k = fun z => (2 * π * Complex.I : ℂ)⁻¹ •
        ∫ θ in (0 : ℝ)..2 * π,
          cauchyIntegrand (a 0) ρ k θ • f (Fin.cons (circleMap (a 0) ρ θ) z) := by
      funext z
      exact cauchyCoeffFirst_eq_integral f _ _ _ _
    rw [heq]
    exact hint.const_smul _
  · intro z hz j t ht
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_ball t ht
    have hsub : ball t (2 * (ε / 2)) ⊆ ball (Fin.tail a j) ρ := by
      rwa [mul_div_cancel₀ _ (two_ne_zero)]
    have key := differentiableAt_intervalIntegral_circle
      (u := fun s θ => cauchyIntegrand (a 0) ρ k θ •
        f (Fin.cons (circleMap (a 0) ρ θ) (Function.update z j s)))
      (t₀ := t) (δ := ε / 2) (M := 1 / ρ ^ k * M) (by positivity)
      (fun s hs => hcθ _ (update_mem_closedPolydisk hz (hsub hs)))
      (fun s hs θ => hbound _ (update_mem_closedPolydisk hz (hsub hs)) θ)
      (fun θ s hs => by
        have h := hf.2 (Fin.cons (circleMap (a 0) ρ θ) z) (hmem θ z hz) j.succ s (hsub hs)
        simp only [Fin.cons_update]
        exact h.const_smul _)
    have heq : (fun s => cauchyCoeffFirst f (a 0) ρ k (Function.update z j s)) =
        fun s => (2 * π * Complex.I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
          cauchyIntegrand (a 0) ρ k θ •
            f (Fin.cons (circleMap (a 0) ρ θ) (Function.update z j s)) := by
      funext s
      exact cauchyCoeffFirst_eq_integral f _ _ _ _
    rw [heq]
    exact key.const_smul _
theorem norm_cauchyCoeffFirst_le {N : ℕ} {f : ComplexCoordinates (N + 1) → E}
    {a : ComplexCoordinates (N + 1)} {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ z ∈ closedPolydisk a ρ, ‖f z‖ ≤ M) (k : ℕ) {z : ComplexCoordinates N}
    (hz : z ∈ closedPolydisk (Fin.tail a) ρ) :
    ‖cauchyCoeffFirst f (a 0) ρ k z‖ ≤ M / ρ ^ k := by
  have hcircle : ∀ θ, ‖circleMap (a 0) ρ θ - a 0‖ ≤ ρ := by
    intro θ
    simp [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 2 * π)
    (C := 1 / ρ ^ k * M)
    (f := fun θ => cauchyIntegrand (a 0) ρ k θ • f (Fin.cons (circleMap (a 0) ρ θ) z))
    (fun θ _ => by
      rw [norm_smul, norm_cauchyIntegrand hρ]
      exact mul_le_mul_of_nonneg_left (hM _ (finCons_mem_closedPolydisk (hcircle θ) hz))
        (by positivity))
  rw [cauchyCoeffFirst_eq_integral, norm_smul]
  have hn : ‖(2 * π * Complex.I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    simp [abs_of_pos Real.pi_pos]
  rw [hn]
  have hp : (0 : ℝ) < 2 * π := by positivity
  rw [sub_zero, abs_of_pos hp] at hint
  calc (2 * π)⁻¹ * _ ≤ (2 * π)⁻¹ * (1 / ρ ^ k * M * (2 * π)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = M / ρ ^ k := by field_simp
theorem hasSum_cauchyCoeffFirst {N : ℕ} {f : ComplexCoordinates (N + 1) → E}
    {a : ComplexCoordinates (N + 1)} {ρ : ℝ} (hρ : 0 < ρ) (hf : HolomorphicInEachVariable f a ρ)
    {z : ComplexCoordinates N} (hz : z ∈ closedPolydisk (Fin.tail a) ρ) {w : ℂ}
    (hw : ‖w - a 0‖ < ρ) :
    HasSum (fun k => (w - a 0) ^ k • cauchyCoeffFirst f (a 0) ρ k z) (f (Fin.cons w z)) := by
  let R : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hmem : ∀ v ∈ closedBall (a 0) (R : ℝ),
      (Fin.cons v z : ComplexCoordinates (N + 1)) ∈ closedPolydisk a ρ := by
    intro v hv
    refine finCons_mem_closedPolydisk ?_ hz
    have hv' : dist v (a 0) ≤ ρ := hv
    simpa [dist_eq_norm] using hv'
  have hc : ContinuousOn (sliceFirst f z) (closedBall (a 0) R) := by
    have hcz : Continuous fun v : ℂ => (Fin.cons v z : ComplexCoordinates (N + 1)) :=
      continuous_finCons.comp (continuous_id.prodMk continuous_const)
    exact hf.1.comp hcz.continuousOn hmem
  have hd : ∀ v ∈ ball (a 0) (R : ℝ) \ (∅ : Set ℂ), DifferentiableAt ℂ (sliceFirst f z) v := by
    intro v hv
    have h0 : (Fin.cons (a 0) z : ComplexCoordinates (N + 1)) ∈ closedPolydisk a ρ :=
      hmem _ (mem_closedBall_self R.2)
    have h := hf.2 _ h0 0 v hv.1
    have e : sliceFirst f z = fun s => f (Function.update (Fin.cons (a 0) z) 0 s) := by
      funext s
      simp [sliceFirst, Fin.update_cons_zero]
    rw [e]
    exact h
  have hp := Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable
    countable_empty hc hd (show 0 < R from hρ)
  have hs := hp.hasSum (y := w - a 0) (by
    have h : ‖w - a 0‖ < (R : ℝ) := hw
    simpa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] using h)
  simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, add_sub_cancel] at hs
  exact hs
theorem summable_prod_pow_of_lt_one : ∀ {N : ℕ} (x : Fin N → ℝ), (∀ j, 0 ≤ x j) →
    (∀ j, x j < 1) → Summable fun m : Fin N → ℕ => ∏ j, x j ^ m j := by
  intro N
  induction N with
  | zero => intro x _ _; exact (hasSum_unique _).summable
  | succ n ih =>
    intro x h0 h1
    rw [← (Fin.consEquiv fun _ => ℕ).summable_iff]
    have h := Summable.mul_of_nonneg (summable_geometric_of_lt_one (h0 0) (h1 0))
      (ih (Fin.tail x) (fun j => h0 j.succ) (fun j => h1 j.succ)) (fun k => pow_nonneg (h0 0) k)
      (fun m => Finset.prod_nonneg fun j _ => pow_nonneg (h0 j.succ) _)
    refine h.congr fun p => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.tail]
theorem norm_monomial_smul_le {N : ℕ} {c : (Fin N → ℕ) → E} {a z : ComplexCoordinates N}
    {ρ M : ℝ} (hc : ∀ m, ‖c m‖ ≤ M / ρ ^ (∑ j, m j)) (m : Fin N → ℕ) :
    ‖(∏ j, (z j - a j) ^ m j) • c m‖ ≤ M * ∏ j, (‖z j - a j‖ / ρ) ^ m j := by
  have h1 : ∏ j, (‖z j - a j‖ / ρ) ^ m j = (∏ j, ‖z j - a j‖ ^ m j) / ρ ^ (∑ j, m j) := by
    simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rw [norm_smul, norm_prod, h1]
  simp only [norm_pow]
  calc (∏ j, ‖z j - a j‖ ^ m j) * ‖c m‖
      ≤ (∏ j, ‖z j - a j‖ ^ m j) * (M / ρ ^ (∑ j, m j)) :=
        mul_le_mul_of_nonneg_left (hc m) (Finset.prod_nonneg fun _ _ => by positivity)
    _ = M * ((∏ j, ‖z j - a j‖ ^ m j) / ρ ^ (∑ j, m j)) := by ring
theorem exists_multiPowerSeries : ∀ {N : ℕ} (f : ComplexCoordinates N → E)
    (a : ComplexCoordinates N) (ρ M : ℝ), 0 < ρ → HolomorphicInEachVariable f a ρ →
    (∀ z ∈ closedPolydisk a ρ, ‖f z‖ ≤ M) →
    ∃ c : (Fin N → ℕ) → E, (∀ m, ‖c m‖ ≤ M / ρ ^ (∑ j, m j)) ∧
      ∀ z ∈ openPolydisk a ρ, HasSum (fun m => (∏ j, (z j - a j) ^ m j) • c m) (f z) := by
  intro N
  induction N with
  | zero =>
    intro f a ρ M hρ _ hM
    refine ⟨fun _ => f a, fun m => ?_, fun z _ => ?_⟩
    · have h : a ∈ closedPolydisk a ρ := fun j => j.elim0
      simpa using hM a h
    · have hz : z = a := Subsingleton.elim _ _
      subst hz
      simp [hasSum_unique]
  | succ n ih =>
    intro f a ρ M hρ hf hM
    have hC := fun k => ih (cauchyCoeffFirst f (a 0) ρ k) (Fin.tail a) ρ (M / ρ ^ k) hρ
      (cauchyCoeffFirst_holomorphicInEachVariable hρ hf hM k)
      (fun z hz => norm_cauchyCoeffFirst_le hρ hM k hz)
    choose C hCb hCs using hC
    have hb : ∀ m : Fin (n + 1) → ℕ, ‖C (m 0) (Fin.tail m)‖ ≤ M / ρ ^ (∑ j, m j) := by
      intro m
      refine (hCb (m 0) (Fin.tail m)).trans (le_of_eq ?_)
      rw [Fin.sum_univ_succ, pow_add, div_div]
      simp [Fin.tail]
    refine ⟨fun m => C (m 0) (Fin.tail m), hb, fun z hz => ?_⟩
    have hz' : Fin.tail z ∈ openPolydisk (Fin.tail a) ρ := fun j => hz j.succ
    have hzc : Fin.tail z ∈ closedPolydisk (Fin.tail a) ρ := fun j => (hz j.succ).le
    have hfirst := hasSum_cauchyCoeffFirst hρ hf hzc (hz 0)
    rw [Fin.cons_self_tail] at hfirst
    have hsum : Summable fun m : Fin (n + 1) → ℕ =>
        (∏ j, (z j - a j) ^ m j) • C (m 0) (Fin.tail m) := by
      refine Summable.of_norm_bounded
        (((summable_prod_pow_of_lt_one (fun j => ‖z j - a j‖ / ρ) (fun j => by positivity)
          (fun j => (div_lt_one hρ).2 (hz j))).mul_left M)) (fun m => ?_)
      exact norm_monomial_smul_le (c := fun m : Fin (n + 1) → ℕ => C (m 0) (Fin.tail m)) hb m
    have hprod := ((Fin.consEquiv fun _ => ℕ).summable_iff.2 hsum).hasSum
    have hfib := hprod.prod_fiberwise (g := fun k => (z 0 - a 0) ^ k •
      cauchyCoeffFirst f (a 0) ρ k (Fin.tail z)) (fun k => by
        have h := (hCs k (Fin.tail z) hz').const_smul ((z 0 - a 0) ^ k)
        have e : (fun c => ((fun m : Fin (n + 1) → ℕ =>
            (∏ j, (z j - a j) ^ m j) • C (m 0) (Fin.tail m)) ∘
              (Fin.consEquiv fun _ => ℕ)) (k, c)) =
            fun i => (z 0 - a 0) ^ k • (∏ j, (Fin.tail z j - Fin.tail a j) ^ i j) • C k i := by
          funext i
          simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.tail, smul_smul]
        rw [e]
        exact h)
    have h2 := (Fin.consEquiv fun _ => ℕ).hasSum_iff.1 hprod
    rwa [hfib.unique hfirst] at h2
theorem isCompact_closedPolydisk {N : ℕ} (a : ComplexCoordinates N) (ρ : ℝ) :
    IsCompact (closedPolydisk a ρ) := by
  have h : closedPolydisk a ρ = Set.pi univ fun j => closedBall (a j) ρ := by
    ext z
    simp [closedPolydisk, dist_eq_norm]
  rw [h]
  exact isCompact_univ_pi fun j => isCompact_closedBall _ _
theorem update_eq_update_add_smul {N : ℕ} (z : ComplexCoordinates N) (j : Fin N) (s t : ℂ) :
    Function.update z j s = Function.update z j t + (s - t) • stdBasisVector j := by
  funext i
  by_cases h : i = j
  · subst h
    simp [stdBasisVector]
  · simp [stdBasisVector, Function.update_of_ne h, Pi.single_eq_of_ne h]
theorem holomorphicInEachVariable_of_isHolomorphicIn {N N' : ℕ}
    {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates N'}
    (hf : IsHolomorphicIn O f) {a : ComplexCoordinates N} {ρ : ℝ}
    (hsub : closedPolydisk a ρ ⊆ O) :
    HolomorphicInEachVariable f a ρ := by
  refine ⟨hf.2.1.mono hsub, fun z hz j t ht => ?_⟩
  have hb := hsub (update_mem_closedPolydisk hz ht)
  have h0 := (hf.2.2 _ hb j).self_of_nhds
  have hline : DifferentiableAt ℂ (fun s : ℂ => s - t) t :=
    differentiableAt_id.sub_const t
  have hc : DifferentiableAt ℂ
      (fun ζ : ℂ => f (Function.update z j t + ζ • stdBasisVector j))
      ((fun s : ℂ => s - t) t) := by simpa using h0
  have := DifferentiableAt.comp
    (g := fun ζ : ℂ => f (Function.update z j t + ζ • stdBasisVector j))
    (f := fun s : ℂ => s - t) t hc hline
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [Function.comp]
  rw [← update_eq_update_add_smul]
theorem exists_multiPowerSeries_of_isHolomorphicIn {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (hf : IsHolomorphicIn O f)
    {a : ComplexCoordinates N} {ρ : ℝ} (hρ : 0 < ρ) (hsub : closedPolydisk a ρ ⊆ O) :
    ∃ (M : ℝ) (c : (Fin N → ℕ) → ComplexCoordinates N'), 0 ≤ M ∧
      (∀ m, ‖c m‖ ≤ M / ρ ^ (∑ j, m j)) ∧
      ∀ z ∈ openPolydisk a ρ, HasSum (fun m => (∏ j, (z j - a j) ^ m j) • c m) (f z) := by
  obtain ⟨M, hM⟩ :=
    (isCompact_closedPolydisk a ρ).exists_bound_of_continuousOn (hf.2.1.mono hsub)
  have ha : a ∈ closedPolydisk a ρ := fun j => by simpa using hρ.le
  obtain ⟨c, hc, hs⟩ := exists_multiPowerSeries f a ρ M hρ
    (holomorphicInEachVariable_of_isHolomorphicIn hf hsub) hM
  exact ⟨M, c, (norm_nonneg _).trans (hM a ha), hc, hs⟩
theorem hasPowerSeriesSumOn_of_isHolomorphicIn {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (hf : IsHolomorphicIn O f)
    {a : ComplexCoordinates N} {ρ : ℝ} (hρ : 0 < ρ) (hsub : closedPolydisk a ρ ⊆ O) :
    HasPowerSeriesSumOn f a ρ := by
  obtain ⟨M, c, hM, hc, hs⟩ := exists_multiPowerSeries_of_isHolomorphicIn hf hρ hsub
  refine ⟨c, hs, fun ρ' hρ' => ?_⟩
  have hr1 : max ρ' 0 / ρ < 1 := (div_lt_one hρ).2 (max_lt hρ' hρ)
  have hu := (summable_prod_pow_of_lt_one (fun _ : Fin N => max ρ' 0 / ρ) (fun _ => by positivity)
    (fun _ => hr1)).mul_left M
  have hle : ∀ (m : Fin N → ℕ) (z : ComplexCoordinates N), z ∈ closedPolydisk a ρ' →
      ‖monomialTerm c a z m‖ ≤ M * ∏ j, (max ρ' 0 / ρ) ^ m j := by
    intro m z hz
    refine (norm_monomial_smul_le hc m).trans (mul_le_mul_of_nonneg_left ?_ hM)
    refine Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => ?_)
    refine pow_le_pow_left₀ (by positivity) ?_ _
    exact div_le_div_of_nonneg_right ((hz j).trans (le_max_left _ _)) hρ.le
  refine ⟨fun z hz => Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => hle m z hz) hu, ?_⟩
  refine (tendstoUniformlyOn_tsum hu (fun m z hz => hle m z hz)).congr_right fun z hz => ?_
  exact (hs z fun j => (hz j).trans_lt hρ').tsum_eq
theorem exists_index_fun_of_sum_eq {N n : ℕ} (m : Fin N → ℕ) (hm : ∑ j, m j = n) :
    ∃ σ : Fin n → Fin N, ∀ v : Fin N → ℂ, ∏ i, v (σ i) = ∏ j, v j ^ m j := by apply _root_.YangMills.SharedProofs.p39221 <;> assumption
theorem exists_monomial_multilinear {N n : ℕ} (m : Fin N → ℕ) (e : E) :
    ∃ Q : ContinuousMultilinearMap ℂ (fun _ : Fin n => ComplexCoordinates N) E, ‖Q‖ ≤ ‖e‖ ∧
      (∑ j, m j = n → ∀ y, Q (fun _ => y) = (∏ j, y j ^ m j) • e) := by
  by_cases hm : ∑ j, m j = n
  · obtain ⟨σ, hσ⟩ := exists_index_fun_of_sum_eq m hm
    let Q : ContinuousMultilinearMap ℂ (fun _ : Fin n => ComplexCoordinates N) E :=
      ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
        (fun i => ContinuousLinearMap.proj (σ i))).smulRight e
    have hQ : ∀ x, Q x = (∏ i, x i (σ i)) • e := fun x => by simp [Q]
    refine ⟨Q, ?_, fun _ y => by rw [hQ, hσ]⟩
    refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun x => ?_
    rw [hQ, norm_smul, norm_prod, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_le_pi_norm _ _)
      (norm_nonneg _)
  · exact ⟨0, by simp, fun h => absurd h hm⟩
theorem analyticAt_of_multiPowerSeries {N : ℕ} {f : ComplexCoordinates N → E}
    {a : ComplexCoordinates N} {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) {c : (Fin N → ℕ) → E}
    (hc : ∀ m, ‖c m‖ ≤ M / ρ ^ (∑ j, m j))
    (hs : ∀ z ∈ openPolydisk a ρ, HasSum (fun m => (∏ j, (z j - a j) ^ m j) • c m) (f z)) :
    AnalyticAt ℂ f a := by
  have hQ := fun (n : ℕ) (m : Fin N → ℕ) => exists_monomial_multilinear (n := n) m (c m)
  choose Q hQn hQy using hQ
  let S : ℕ → Finset (Fin N → ℕ) := fun n => Finset.piAntidiag Finset.univ n
  have hS : ∀ n m, m ∈ S n ↔ ∑ j, m j = n := fun n m => by simp [S]
  let p : FormalMultilinearSeries ℂ (ComplexCoordinates N) E := fun n => ∑ m ∈ S n, Q n m
  let r : ℝ≥0 := ⟨ρ / 2, by positivity⟩
  have hr : (r : ℝ) = ρ / 2 := rfl
  have hhalf : Summable fun m : Fin N → ℕ => M * ∏ j, ((1 : ℝ) / 2) ^ m j :=
    (summable_prod_pow_of_lt_one (fun _ : Fin N => (1 : ℝ) / 2) (fun _ => by norm_num)
      (fun _ => by norm_num)).mul_left M
  have hrad : (r : ℝ≥0∞) ≤ p.radius := by
    refine FormalMultilinearSeries.le_radius_of_bound p
      (∑' m : Fin N → ℕ, M * ∏ j, ((1 : ℝ) / 2) ^ m j) fun n => ?_
    have h1 : ‖p n‖ ≤ ∑ m ∈ S n, ‖c m‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => hQn n m)
    calc ‖p n‖ * (r : ℝ) ^ n ≤ (∑ m ∈ S n, ‖c m‖) * (r : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ ∑ m ∈ S n, M * ∏ j, ((1 : ℝ) / 2) ^ m j := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun m hm => ?_
          have hn := (hS n m).1 hm
          rw [Finset.prod_pow_eq_pow_sum, hn, hr]
          calc ‖c m‖ * (ρ / 2) ^ n ≤ M / ρ ^ n * (ρ / 2) ^ n :=
                mul_le_mul_of_nonneg_right (hn ▸ hc m) (by positivity)
            _ = M * (1 / 2) ^ n := by
                rw [div_pow, one_div, inv_pow]
                field_simp
      _ ≤ _ := hhalf.sum_le_tsum _ fun m _ => by positivity
  refine (HasFPowerSeriesOnBall.analyticAt (f := f) (p := p) (x := a) (r := r) ?_)
  refine ⟨hrad, ENNReal.coe_pos.2 (by change 0 < ρ / 2; positivity), fun {y} hy => ?_⟩
  have hy' : ‖y‖ < ρ / 2 := by
    have : ‖y‖ < (r : ℝ) := by
      simpa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] using hy
    rwa [hr] at this
  have hz : a + y ∈ openPolydisk a ρ := fun j => by
    have := norm_le_pi_norm y j
    simp only [Pi.add_apply, add_sub_cancel_left]
    linarith
  have hsum := hs _ hz
  simp only [Pi.add_apply, add_sub_cancel_left] at hsum
  have hsig := (Equiv.hasSum_iff (Equiv.sigmaFiberEquiv fun m : Fin N → ℕ => ∑ j, m j)).2 hsum
  refine hsig.sigma (g := fun n => p n fun _ => y) fun n => ?_
  have hp : (p n fun _ => y) = ∑ m ∈ S n, (∏ j, y j ^ m j) • c m := by
    simp only [p, _root_.sum_apply]
    exact Finset.sum_congr rfl fun m hm => hQy n m ((hS n m).1 hm) y
  rw [hp]
  have hind : HasSum (({m : Fin N → ℕ | ∑ j, m j = n}).indicator
      fun m : Fin N → ℕ => (∏ j, y j ^ m j) • c m) (∑ m ∈ S n, (∏ j, y j ^ m j) • c m) := by
    have hzero : ∀ m ∉ S n, ({m : Fin N → ℕ | ∑ j, m j = n}).indicator
        (fun m : Fin N → ℕ => (∏ j, y j ^ m j) • c m) m = 0 := by
      intro m hm
      have hm' : m ∉ {m : Fin N → ℕ | ∑ j, m j = n} := fun h => hm ((hS n m).2 h)
      simp only [indicator_of_notMem hm']
    have h : HasSum (({m : Fin N → ℕ | ∑ j, m j = n}).indicator
        fun m : Fin N → ℕ => (∏ j, y j ^ m j) • c m)
        (∑ m ∈ S n, ({m : Fin N → ℕ | ∑ j, m j = n}).indicator
          (fun m : Fin N → ℕ => (∏ j, y j ^ m j) • c m) m) :=
      hasSum_sum_of_ne_finset_zero hzero
    have hsame : ∑ m ∈ S n, ({m : Fin N → ℕ | ∑ j, m j = n}).indicator
        (fun m : Fin N → ℕ => (∏ j, y j ^ m j) • c m) m =
        ∑ m ∈ S n, (∏ j, y j ^ m j) • c m := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm' : m ∈ {m : Fin N → ℕ | ∑ j, m j = n} := (hS n m).1 hm
      simp only [indicator_of_mem hm']
    rwa [hsame] at h
  exact hasSum_subtype_iff_indicator.2 hind
theorem exists_closedPolydisk_subset {N : ℕ} {O : Set (ComplexCoordinates N)} (hO : IsOpen O)
    {a : ComplexCoordinates N} (ha : a ∈ O) : ∃ ρ > 0, closedPolydisk a ρ ⊆ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO a ha
  refine ⟨ε / 2, by positivity, fun z hz => hball ?_⟩
  have h : dist z a ≤ ε / 2 :=
    (dist_pi_le_iff (by positivity)).2 fun j => by simpa [dist_eq_norm] using hz j
  exact mem_ball.2 (by linarith)
theorem analyticOnNhd_of_isHolomorphicIn {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (hf : IsHolomorphicIn O f) :
    AnalyticOnNhd ℂ f O := by
  intro a ha
  obtain ⟨ρ, hρ, hsub⟩ := exists_closedPolydisk_subset hf.1 ha
  obtain ⟨M, c, hM, hc, hs⟩ := exists_multiPowerSeries_of_isHolomorphicIn hf hρ hsub
  exact analyticAt_of_multiPowerSeries hρ hM hc hs
theorem isHolomorphicIn_of_differentiableOn {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (hO : IsOpen O)
    (h : DifferentiableOn ℂ f O) : IsHolomorphicIn O f := by apply _root_.YangMills.SharedProofs.p1029 <;> assumption
theorem differentiableAt_of_comp_add {φ : ℂ → E} {ζ : ℂ}
    (h : DifferentiableAt ℂ (fun ξ => φ (ζ + ξ)) 0) : DifferentiableAt ℂ φ ζ := by
  have hline : DifferentiableAt ℂ (fun s : ℂ => s - ζ) ζ := differentiableAt_id.sub_const ζ
  have hc : DifferentiableAt ℂ (fun ξ => φ (ζ + ξ)) ((fun s : ℂ => s - ζ) ζ) := by simpa using h
  have := DifferentiableAt.comp (g := fun ξ => φ (ζ + ξ)) (f := fun s : ℂ => s - ζ) ζ hc hline
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp
theorem isHolomorphicIn_of_tendstoUniformlyOn {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    (hO : IsOpen O) {F : ℕ → ComplexCoordinates N → ComplexCoordinates N'}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (hF : ∀ m, IsHolomorphicIn O (F m))
    (hlim : TendstoUniformlyOn F f atTop O) : IsHolomorphicIn O f := by
  refine ⟨hO, hlim.continuousOn (Frequently.of_forall fun m => (hF m).2.1), fun a ha j => ?_⟩
  let ℓ : ℂ → ComplexCoordinates N := fun ζ => a + ζ • stdBasisVector j
  have hl : Continuous ℓ := by fun_prop
  have hU : IsOpen (ℓ ⁻¹' O) := hO.preimage hl
  have h0 : (0 : ℂ) ∈ ℓ ⁻¹' O := by simpa [ℓ] using ha
  have hd : DifferentiableOn ℂ (f ∘ ℓ) (ℓ ⁻¹' O) := by
    refine (hlim.comp ℓ).tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun m ζ hζ => ?_) hU
    have h1 := ((hF m).2.2 _ hζ j).self_of_nhds
    refine (differentiableAt_of_comp_add ?_).differentiableWithinAt
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun ξ => ?_)
    simp [ℓ, add_smul, add_assoc]
  filter_upwards [hU.mem_nhds h0] with ζ hζ
  exact hd.differentiableAt (hU.mem_nhds hζ)
theorem differentiable_mvPolynomial_eval {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ fun z : ComplexCoordinates n => MvPolynomial.eval z P := by apply _root_.YangMills.SharedProofs.p63145 <;> assumption
theorem isHolomorphicVia_of_isPolynomialInComponents {n n' : ℕ} {s : Fin n → Component}
    {s' : Fin n' → Component} {f : ComponentProduct s → ComponentProduct s'}
    (h : IsPolynomialInComponents s s' f) :
    IsHolomorphicVia (productEquiv s) (productEquiv s') univ f := by
  obtain ⟨P, hP⟩ := h
  have heq : (productEquiv s') ∘ f ∘ (productEquiv s).symm =
      fun z k => MvPolynomial.eval z (P k) := by
    funext z k
    simpa using hP ((productEquiv s).symm z) k
  have himg : (productEquiv s) '' univ = univ :=
    image_univ_of_surjective (productEquiv s).surjective
  rw [IsHolomorphicVia, himg, heq]
  exact isHolomorphicIn_of_differentiableOn isOpen_univ
    (differentiable_pi.2 fun k => differentiable_mvPolynomial_eval (P k)).differentiableOn
def pairMatrix (z : ComplexCoordinates (productDim matrixPairComponents)) (i : Fin 2) :
    Matrices.ComplexMatrix2 :=
  (productEquiv matrixPairComponents).symm z i
theorem pairMatrix_apply (z : ComplexCoordinates (productDim matrixPairComponents)) (i : Fin 2)
    (r s : Fin 2) :
    pairMatrix z i r s = z (finSigmaFinEquiv ⟨i, entryIndex (r, s)⟩) := rfl
theorem isHolomorphicVia_mul :
    IsHolomorphicVia matrixPairEquiv matrixEquiv univ
      (fun p : Matrices.ComplexMatrix2 × Matrices.ComplexMatrix2 => p.1 * p.2) := by
  have himg : matrixPairEquiv '' univ = univ :=
    image_univ_of_surjective matrixPairEquiv.surjective
  rw [IsHolomorphicVia, himg]
  refine isHolomorphicIn_of_differentiableOn isOpen_univ (Differentiable.differentiableOn ?_)
  refine differentiable_pi.2 fun k => ?_
  show Differentiable ℂ fun z : ComplexCoordinates (productDim matrixPairComponents) =>
    (pairMatrix z 0 * pairMatrix z 1) (entryIndex.symm k).1 (entryIndex.symm k).2
  simp only [Matrix.mul_apply, pairMatrix_apply]
  exact Differentiable.fun_sum fun l _ => (differentiable_apply _).fun_mul (differentiable_apply _)
def matrixEquivCLM : Matrices.ComplexMatrix2 →L[ℂ] ComplexCoordinates 4 :=
  LinearMap.toContinuousLinearMap
    { toFun := matrixEquiv
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
def matrixEquivSymmCLM : ComplexCoordinates 4 →L[ℂ] Matrices.ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := matrixEquiv.symm
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
theorem matrixEquivCLM_apply (X : Matrices.ComplexMatrix2) :
    matrixEquivCLM X = matrixEquiv X := rfl
theorem matrixEquivSymmCLM_apply (z : ComplexCoordinates 4) :
    matrixEquivSymmCLM z = matrixEquiv.symm z := rfl
theorem isOpen_image_matrixEquiv {U : Set Matrices.ComplexMatrix2} (hU : IsOpen U) :
    IsOpen (matrixEquiv '' U) := by
  have h : matrixEquiv '' U = matrixEquivSymmCLM ⁻¹' U := by
    rw [Equiv.image_eq_preimage_symm]
    rfl
  rw [h]
  exact hU.preimage matrixEquivSymmCLM.continuous
theorem isHolomorphicVia_of_lines {U : Set Matrices.ComplexMatrix2} (hU : IsOpen U)
    {h : Matrices.ComplexMatrix2 → Matrices.ComplexMatrix2}
    (hc : ContinuousOn h U)
    (hl : ∀ X ∈ U, ∀ B : Matrices.ComplexMatrix2, ∀ᶠ ζ in 𝓝 (0 : ℂ),
      DifferentiableAt ℂ (fun ζ : ℂ => h (X + ζ • B)) ζ) :
    IsHolomorphicVia matrixEquiv matrixEquiv U h := by
  refine ⟨isOpen_image_matrixEquiv hU, ?_, ?_⟩
  · refine matrixEquivCLM.continuous.comp_continuousOn
      (hc.comp matrixEquivSymmCLM.continuous.continuousOn ?_)
    rintro _ ⟨X, hX, rfl⟩
    simpa [matrixEquivSymmCLM_apply] using hX
  · rintro _ ⟨X, hX, rfl⟩ j
    filter_upwards [hl X hX (matrixEquivSymmCLM (stdBasisVector j))] with ζ hζ
    have hd := matrixEquivCLM.differentiableAt.comp ζ hζ
    refine hd.congr_of_eventuallyEq (Eventually.of_forall fun ξ => ?_)
    simp only [Function.comp]
    rw [← matrixEquivCLM_apply]
    congr 2
    rw [← matrixEquivSymmCLM_apply, map_add, map_smul, matrixEquivSymmCLM_apply]
    simp
theorem isHolomorphicVia_of_differentiableOn {U : Set Matrices.ComplexMatrix2} (hU : IsOpen U)
    {h : Matrices.ComplexMatrix2 → Matrices.ComplexMatrix2}
    (hd : DifferentiableOn ℂ h U) :
    IsHolomorphicVia matrixEquiv matrixEquiv U h := by
  refine isHolomorphicVia_of_lines hU hd.continuousOn fun X hX B => ?_
  have hl : Continuous fun ζ : ℂ => X + ζ • B := by fun_prop
  have hlim : Tendsto (fun ζ : ℂ => X + ζ • B) (𝓝 0) (𝓝 X) := by
    simpa using hl.tendsto 0
  filter_upwards [hlim.eventually (hU.mem_nhds hX)] with ζ hζ
  exact DifferentiableAt.comp (g := h) (f := fun ζ : ℂ => X + ζ • B) ζ
    (hd.differentiableAt (hU.mem_nhds hζ))
    ((differentiableAt_const _).add (differentiableAt_id.smul_const _))
theorem isHolomorphicVia_inv :
    IsHolomorphicVia matrixEquiv matrixEquiv {X : Matrices.ComplexMatrix2 | IsUnit X}
      (fun X => X⁻¹) := by
  refine isHolomorphicVia_of_differentiableOn Units.isOpen fun X hX => ?_
  have h : (fun X : Matrices.ComplexMatrix2 => X⁻¹) = Ring.inverse := by
    funext X
    exact Matrix.nonsing_inv_eq_ringInverse X
  rw [h]
  exact (differentiableAt_inverse (𝕜 := ℂ) hX).differentiableWithinAt
theorem isHolomorphicVia_matExp :
    IsHolomorphicVia matrixEquiv matrixEquiv univ Matrices.ComplexMatrix2.matExp := by
  refine isHolomorphicVia_of_differentiableOn isOpen_univ fun X _ => ?_
  exact (NormedSpace.exp_analytic (𝕂 := ℂ) X).differentiableAt.differentiableWithinAt
def logSeriesTerm (n : ℕ) (X : Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  ((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1)
theorem norm_logSeriesTerm_le (n : ℕ) {X : Matrices.ComplexMatrix2} {r : ℝ}
    (hX : ‖1 - X‖ ≤ r) : ‖logSeriesTerm n X‖ ≤ r ^ (n + 1) := by
  have h1 : ‖((n + 1 : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv]
    have : (1 : ℝ) ≤ ‖(n + 1 : ℂ)‖ := by
      have h : ‖(n + 1 : ℂ)‖ = (n : ℝ) + 1 := by
        exact_mod_cast Complex.norm_natCast (n + 1)
      rw [h]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact inv_le_one_of_one_le₀ this
  rw [logSeriesTerm, norm_smul]
  calc _ ≤ 1 * ‖(1 - X) ^ (n + 1)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ ‖1 - X‖ ^ (n + 1) := by rw [one_mul]; exact norm_pow_le' _ (Nat.succ_pos n)
    _ ≤ r ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg _) hX _
theorem summable_pow_succ_of_lt_one {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun n : ℕ => r ^ (n + 1) :=
  (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one h0 h1)
theorem continuousOn_tsum_logSeriesTerm {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    ContinuousOn (fun X : Matrices.ComplexMatrix2 => ∑' n, logSeriesTerm n X)
      {X | ‖1 - X‖ < r} := by
  refine continuousOn_tsum (fun n => Continuous.continuousOn ?_) (summable_pow_succ_of_lt_one h0 h1)
    (fun n X hX => norm_logSeriesTerm_le n (le_of_lt hX))
  unfold logSeriesTerm
  fun_prop
theorem isHolomorphicVia_logSeries :
    IsHolomorphicVia matrixEquiv matrixEquiv Matrices.ComplexMatrix2.logBall
      Matrices.ComplexMatrix2.logSeries := by
  have hnorm : ∀ X : Matrices.ComplexMatrix2, ‖1 - X‖ = ‖X - 1‖ := fun X => norm_sub_rev _ _
  have hopen : IsOpen Matrices.ComplexMatrix2.logBall := by
    have : Matrices.ComplexMatrix2.logBall = {X : Matrices.ComplexMatrix2 | ‖X - 1‖ < 1} := rfl
    rw [this]
    exact isOpen_lt (by fun_prop) continuous_const
  have hopen' : ∀ r : ℝ, IsOpen {X : Matrices.ComplexMatrix2 | ‖1 - X‖ < r} := fun r =>
    isOpen_lt (by fun_prop) continuous_const
  have hr : ∀ X ∈ Matrices.ComplexMatrix2.logBall, ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ‖1 - X‖ < r := by
    intro X hX
    have hX' : ‖X - 1‖ < 1 := hX
    refine ⟨(1 + ‖1 - X‖) / 2, by positivity, ?_, ?_⟩ <;> rw [hnorm] <;> linarith
  refine isHolomorphicVia_of_lines hopen ?_ fun X hX B => ?_
  · intro X hX
    obtain ⟨r, h0, h1, hXr⟩ := hr X hX
    have hat := (continuousOn_tsum_logSeriesTerm h0 h1).continuousAt ((hopen' r).mem_nhds hXr)
    have : ContinuousAt Matrices.ComplexMatrix2.logSeries X := by
      have h := hat.neg
      exact h
    exact this.continuousWithinAt
  · obtain ⟨r, h0, h1, hXr⟩ := hr X hX
    have hl : Continuous fun ζ : ℂ => X + ζ • B := by fun_prop
    have hU : IsOpen ((fun ζ : ℂ => X + ζ • B) ⁻¹' {X | ‖1 - X‖ < r}) :=
      (hopen' r).preimage hl
    have hz : (0 : ℂ) ∈ (fun ζ : ℂ => X + ζ • B) ⁻¹' {X | ‖1 - X‖ < r} := by simpa using hXr
    have hd := Complex.differentiableOn_tsum_of_summable_norm
      (F := fun (n : ℕ) (ζ : ℂ) => logSeriesTerm n (X + ζ • B)) (summable_pow_succ_of_lt_one h0 h1)
      (fun n => Differentiable.differentiableOn (by unfold logSeriesTerm; fun_prop)) hU
      (fun n ζ hζ => norm_logSeriesTerm_le n (le_of_lt hζ))
    filter_upwards [hU.mem_nhds hz] with ζ hζ
    exact (hd.differentiableAt (hU.mem_nhds hζ)).neg
theorem properties_holds : Properties := by
  refine ⟨fun N O hO => ⟨fun N' f hf => ?_, fun N' F f hF hlim =>
      isHolomorphicIn_of_tendstoUniformlyOn hO hF hlim⟩,
    fun n n' s s' f h => isHolomorphicVia_of_isPolynomialInComponents h,
    isHolomorphicVia_mul, isHolomorphicVia_inv, isHolomorphicVia_matExp,
    isHolomorphicVia_logSeries⟩
  have han := analyticOnNhd_of_isHolomorphicIn hf
  refine ⟨fun a _ ρ hρ hsub => hasPowerSeriesSumOn_of_isHolomorphicIn hf hρ hsub, ?_,
    fun b hb => ?_, fun N'' O' g hg hmaps => ?_, ⟨O, hO, rfl⟩, fun a ha => ?_⟩
  · exact (han.contDiffOn (n := ∞) hO.uniqueDiffOn).restrict_scalars ℝ
  · exact ⟨fderiv ℂ f b, (han b hb).differentiableAt.hasFDerivAt.restrictScalars ℝ⟩
  · have hgan := analyticOnNhd_of_isHolomorphicIn hg
    exact isHolomorphicIn_of_differentiableOn hg.1 fun x hx =>
      ((han _ (hmaps hx)).comp (hgan x hx)).differentiableAt.differentiableWithinAt
  · obtain ⟨ρ, hρ, hsub⟩ := exists_closedPolydisk_subset hO ha.1
    obtain ⟨M, c, -, -, hs⟩ := exists_multiPowerSeries_of_isHolomorphicIn hf hρ hsub
    refine ⟨c, eventually_nhdsWithin_of_eventually_nhds ?_⟩
    filter_upwards [ball_mem_nhds a hρ] with z hz
    refine hs z fun j => ?_
    have := dist_le_pi_dist z a j
    rw [dist_eq_norm] at this
    exact this.trans_lt hz
end YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy
