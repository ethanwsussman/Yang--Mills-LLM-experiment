import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace GibbsMeanDerivatives
variable {Ω : Type} [MeasurableSpace Ω] {k : ℕ}
theorem continuousLinearMap_eq_sum_smulRight {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (Fin k → ℝ) →L[ℝ] F) :
    L = ∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (L (Pi.single i 1)) := by
  ext x
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : Fin k → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp [map_sum]
theorem aestronglyMeasurable_fderiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ω) {B : Set (Fin k → ℝ)} (hB : IsOpen B) (G : (Fin k → ℝ) → Ω → F)
    (hm : ∀ τ ∈ B, AEStronglyMeasurable (G τ) μ) {τ : Fin k → ℝ} (hτ : τ ∈ B)
    (hd : ∀ᵐ ω ∂μ, DifferentiableAt ℝ (fun τ' => G τ' ω) τ) :
    AEStronglyMeasurable (fun ω => fderiv ℝ (fun τ' => G τ' ω) τ) μ := by
  have dir : ∀ e : Fin k → ℝ,
      AEStronglyMeasurable (fun ω => fderiv ℝ (fun τ' => G τ' ω) τ e) μ := by
    intro e
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hev : ∀ᶠ n : ℕ in atTop, τ + ((1 : ℝ) / ((n : ℝ) + 1)) • e ∈ B := by
      have h1 : Tendsto (fun n : ℕ => τ + ((1 : ℝ) / ((n : ℝ) + 1)) • e) atTop (𝓝 τ) := by
        have := (h0.smul_const e).const_add τ
        simpa using this
      exact h1.eventually (hB.mem_nhds hτ)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (n : ℕ) ω => (((1 : ℝ) / (((n + N : ℕ) : ℝ) + 1))⁻¹) •
        (G (τ + ((1 : ℝ) / (((n + N : ℕ) : ℝ) + 1)) • e) ω - G τ ω)) ?_ ?_
    · intro n
      exact ((hm _ (hN _ (by omega))).sub (hm τ hτ)).const_smul _
    · filter_upwards [hd] with ω hω
      have hl : HasDerivAt (fun t : ℝ => τ + t • e) e 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add τ
      have hf : HasFDerivAt (fun τ' => G τ' ω) (fderiv ℝ (fun τ' => G τ' ω) τ)
          (τ + (0 : ℝ) • e) := by
        simpa using hω.hasFDerivAt
      have h1 : HasDerivAt ((fun τ' => G τ' ω) ∘ fun t : ℝ => τ + t • e)
          (fderiv ℝ (fun τ' => G τ' ω) τ e) 0 := hf.comp_hasDerivAt (0 : ℝ) hl
      have h2 := h1.tendsto_slope_zero
      have h3 : Tendsto (fun n : ℕ => (1 : ℝ) / (((n + N : ℕ) : ℝ) + 1)) atTop (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · exact h0.comp (tendsto_add_atTop_nat N)
        · refine Eventually.of_forall fun n => ?_
          have : (0 : ℝ) < ((n + N : ℕ) : ℝ) + 1 := by positivity
          simp only [mem_compl_iff, mem_singleton_iff]
          exact (one_div_pos.2 this).ne'
      have h4 := h2.comp h3
      simpa [Function.comp_def] using h4
  have rep : (fun ω => fderiv ℝ (fun τ' => G τ' ω) τ) = fun ω => ∑ i,
      (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight
        (fderiv ℝ (fun τ' => G τ' ω) τ (Pi.single i 1)) := by
    funext ω
    exact continuousLinearMap_eq_sum_smulRight _
  rw [rep]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) F
    (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)).continuous.comp_aestronglyMeasurable
      (dir _)
theorem contDiffOn_integral_and_iteratedFDeriv (μ : Measure Ω) [IsFiniteMeasure μ]
    {B : Set (Fin k → ℝ)} (hB : IsOpen B) (K : ℝ) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (G : (Fin k → ℝ) → Ω → F),
      (∀ τ ∈ B, AEStronglyMeasurable (G τ) μ) →
      (∀ᵐ ω ∂μ, ContDiffOn ℝ n (fun τ => G τ ω) B) →
      (∀ᵐ ω ∂μ, ∀ j, j ≤ n → ∀ τ ∈ B, ‖iteratedFDeriv ℝ j (fun τ => G τ ω) τ‖ ≤ K) →
      ContDiffOn ℝ n (fun τ => ∫ ω, G τ ω ∂μ) B ∧
      ∀ τ ∈ B, ∀ j, j ≤ n → ∀ v : Fin j → Fin k → ℝ,
        AEStronglyMeasurable (fun ω => iteratedFDeriv ℝ j (fun τ' => G τ' ω) τ v) μ ∧
        iteratedFDeriv ℝ j (fun τ => ∫ ω, G τ ω ∂μ) τ v =
          ∫ ω, iteratedFDeriv ℝ j (fun τ' => G τ' ω) τ v ∂μ := by
  induction n with
  | zero =>
    intro F _ _ _ G hm hs hb
    have hbound : ∀ τ ∈ B, ∀ᵐ ω ∂μ, ‖G τ ω‖ ≤ K := by
      intro τ hτ
      filter_upwards [hb] with ω hω
      have := hω 0 le_rfl τ hτ
      simpa [norm_iteratedFDeriv_zero] using this
    refine ⟨?_, ?_⟩
    · simp only [Nat.cast_zero]
      rw [contDiffOn_zero]
      refine continuousOn_of_dominated hm hbound (integrable_const K) ?_
      filter_upwards [hs] with ω hω
      exact hω.continuousOn
    · intro τ hτ j hj v
      obtain rfl : j = 0 := Nat.le_zero.1 hj
      refine ⟨?_, ?_⟩
      · simpa [iteratedFDeriv_zero_apply] using hm τ hτ
      · simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro F _ _ _ G hm hs hb
    have hs1 : ∀ᵐ ω ∂μ, DifferentiableOn ℝ (fun τ => G τ ω) B ∧
        ContDiffOn ℝ n (fderiv ℝ (fun τ => G τ ω)) B := by
      filter_upwards [hs] with ω hω
      have h := (contDiffOn_succ_iff_fderiv_of_isOpen (n := (n : WithTop ℕ∞)) hB).1
        (by simpa using hω)
      exact ⟨h.1, h.2.2⟩
    have hd : ∀ᵐ ω ∂μ, ∀ τ ∈ B, HasFDerivAt (fun τ' => G τ' ω)
        (fderiv ℝ (fun τ' => G τ' ω) τ) τ := by
      filter_upwards [hs1] with ω hω τ hτ
      exact ((hω.1 τ hτ).differentiableAt (hB.mem_nhds hτ)).hasFDerivAt
    have hm' : ∀ τ ∈ B, AEStronglyMeasurable
        (fun ω => fderiv ℝ (fun τ' => G τ' ω) τ) μ := by
      intro τ hτ
      refine aestronglyMeasurable_fderiv μ hB G hm hτ ?_
      filter_upwards [hd] with ω hω
      exact (hω τ hτ).differentiableAt
    have hs' : ∀ᵐ ω ∂μ, ContDiffOn ℝ n
        (fun τ => fderiv ℝ (fun τ' => G τ' ω) τ) B := by
      filter_upwards [hs1] with ω hω
      exact hω.2
    have hb' : ∀ᵐ ω ∂μ, ∀ j, j ≤ n → ∀ τ ∈ B,
        ‖iteratedFDeriv ℝ j (fun τ => fderiv ℝ (fun τ' => G τ' ω) τ) τ‖ ≤ K := by
      filter_upwards [hb] with ω hω j hj τ hτ
      have := hω (j + 1) (by omega) τ hτ
      rwa [← norm_iteratedFDeriv_fderiv] at this
    obtain ⟨c', f'⟩ := ih ((Fin k → ℝ) →L[ℝ] F)
      (fun τ ω => fderiv ℝ (fun τ' => G τ' ω) τ) hm' hs' hb'
    have hbound : ∀ τ ∈ B, ∀ᵐ ω ∂μ, ‖G τ ω‖ ≤ K := by
      intro τ hτ
      filter_upwards [hb] with ω hω
      have := hω 0 (by omega) τ hτ
      simpa [norm_iteratedFDeriv_zero] using this
    have hbound' : ∀ᵐ ω ∂μ, ∀ τ ∈ B, ‖fderiv ℝ (fun τ' => G τ' ω) τ‖ ≤ K := by
      filter_upwards [hb'] with ω hω τ hτ
      have := hω 0 (by omega) τ hτ
      simpa [norm_iteratedFDeriv_zero] using this
    have hasF : ∀ τ ∈ B, HasFDerivAt (fun τ => ∫ ω, G τ ω ∂μ)
        (∫ ω, fderiv ℝ (fun τ' => G τ' ω) τ ∂μ) τ := by
      intro τ hτ
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := B) (bound := fun _ => K)
        (hB.mem_nhds hτ) ?_ ?_ (hm' τ hτ) hbound' (integrable_const K) hd
      · filter_upwards [hB.mem_nhds hτ] with τ' hτ'
        exact hm τ' hτ'
      · exact Integrable.of_bound (hm τ hτ) K (hbound τ hτ)
    have hfd : ∀ τ ∈ B, fderiv ℝ (fun τ => ∫ ω, G τ ω ∂μ) τ =
        ∫ ω, fderiv ℝ (fun τ' => G τ' ω) τ ∂μ := fun τ hτ => (hasF τ hτ).fderiv
    refine ⟨?_, ?_⟩
    · have hgoal : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (fun τ => ∫ ω, G τ ω ∂μ) B := by
        refine (contDiffOn_succ_iff_fderiv_of_isOpen hB).2 ⟨?_, ?_, ?_⟩
        · exact fun τ hτ => (hasF τ hτ).differentiableAt.differentiableWithinAt
        · intro h
          exact absurd h (by simp)
        · exact c'.congr hfd
      simpa using hgoal
    · intro τ hτ j hj v
      cases j with
      | zero =>
        refine ⟨?_, ?_⟩
        · simpa [iteratedFDeriv_zero_apply] using hm τ hτ
        · simp [iteratedFDeriv_zero_apply]
      | succ i =>
        obtain ⟨mm, ee⟩ := f' τ hτ i (by omega) (Fin.init v)
        have evI : (fun y => fderiv ℝ (fun τ => ∫ ω, G τ ω ∂μ) y) =ᶠ[𝓝 τ]
            fun y => ∫ ω, fderiv ℝ (fun τ' => G τ' ω) y ∂μ := by
          filter_upwards [hB.mem_nhds hτ] with y hy
          exact hfd y hy
        have hint : Integrable (fun ω => iteratedFDeriv ℝ i
            (fun τ => fderiv ℝ (fun τ' => G τ' ω) τ) τ (Fin.init v)) μ := by
          refine Integrable.of_bound mm (K * ∏ l, ‖Fin.init v l‖) ?_
          filter_upwards [hb'] with ω hω
          refine ((iteratedFDeriv ℝ i (fun τ => fderiv ℝ (fun τ' => G τ' ω) τ) τ).le_opNorm
            (Fin.init v)).trans ?_
          exact mul_le_mul_of_nonneg_right (hω i (by omega) τ hτ)
            (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        refine ⟨?_, ?_⟩
        · have : (fun ω => iteratedFDeriv ℝ (i + 1) (fun τ' => G τ' ω) τ v) = fun ω =>
              (iteratedFDeriv ℝ i (fun τ => fderiv ℝ (fun τ' => G τ' ω) τ) τ (Fin.init v))
                (v (Fin.last i)) := by
            funext ω
            exact iteratedFDeriv_succ_apply_right v
          rw [this]
          exact (ContinuousLinearMap.apply ℝ F (v (Fin.last i))).continuous.comp_aestronglyMeasurable mm
        · rw [iteratedFDeriv_succ_apply_right, (Filter.EventuallyEq.iteratedFDeriv ℝ evI i).eq_of_nhds, ee,
            ContinuousLinearMap.integral_apply hint]
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          exact (iteratedFDeriv_succ_apply_right v).symm
section Dominated
variable {μ : Measure Ω} {B : Set (Fin k → ℝ)}
def IsDominated (μ : Measure Ω) (n : ℕ) (B : Set (Fin k → ℝ)) (G : (Fin k → ℝ) → Ω → ℝ) : Prop :=
  ∃ K, IsDominatedSmoothFamily μ n B K G
omit [MeasurableSpace Ω] in
theorem paramIteratedDeriv_one (G : (Fin k → ℝ) → Ω → ℝ) (u : Fin k → ℝ) :
    paramIteratedDeriv G ![u] = fun τ ω => fderiv ℝ (fun τ' => G τ' ω) τ u := by
  funext τ ω
  simp [paramIteratedDeriv, iteratedFDeriv_one_apply]
theorem IsDominated.mono {G : (Fin k → ℝ) → Ω → ℝ} {n m : ℕ} (h : IsDominated μ n B G)
    (hmn : m ≤ n) : IsDominated μ m B G := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, hK.aestronglyMeasurable, ?_, ?_⟩
  · filter_upwards [hK.contDiffOn] with ω hω
    exact hω.of_le (by exact_mod_cast hmn)
  · filter_upwards [hK.norm_iteratedFDeriv_le] with ω hω j hj
    exact hω j (hj.trans hmn)
theorem IsDominated.paramDeriv (hB : IsOpen B) {G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (h : IsDominated μ (n + 1) B G) (u : Fin k → ℝ) :
    IsDominated μ n B (paramIteratedDeriv G ![u]) := by
  rw [paramIteratedDeriv_one]
  obtain ⟨K, hK⟩ := h
  have hs1 : ∀ᵐ ω ∂μ, DifferentiableOn ℝ (fun τ => G τ ω) B ∧
      ContDiffOn ℝ n (fderiv ℝ (fun τ => G τ ω)) B := by
    filter_upwards [hK.contDiffOn] with ω hω
    have h := (contDiffOn_succ_iff_fderiv_of_isOpen (n := (n : WithTop ℕ∞)) hB).1
      (by simpa using hω)
    exact ⟨h.1, h.2.2⟩
  let ev : ((Fin k → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ u
  refine ⟨‖ev‖ * K, ?_, ?_, ?_⟩
  · intro τ hτ
    refine ev.continuous.comp_aestronglyMeasurable
      (aestronglyMeasurable_fderiv μ hB G hK.aestronglyMeasurable hτ ?_)
    filter_upwards [hs1] with ω hω
    exact (hω.1 τ hτ).differentiableAt (hB.mem_nhds hτ)
  · filter_upwards [hs1] with ω hω
    exact ev.contDiff.comp_contDiffOn hω.2
  · filter_upwards [hs1, hK.norm_iteratedFDeriv_le] with ω hω hb j hj τ hτ
    have hat : ContDiffAt ℝ n (fderiv ℝ (fun τ => G τ ω)) τ :=
      hω.2.contDiffAt (hB.mem_nhds hτ)
    have e := ev.iteratedFDeriv_comp_left hat (i := j) (by exact_mod_cast hj)
    have e' : iteratedFDeriv ℝ j (fun τ => fderiv ℝ (fun τ' => G τ' ω) τ u) τ =
        ev.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fderiv ℝ (fun τ => G τ ω)) τ) := e
    rw [e']
    refine (ev.norm_compContinuousMultilinearMap_le _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_iteratedFDeriv_fderiv]
    exact hb (j + 1) (by omega) τ hτ
theorem IsDominated.sub (hB : IsOpen B) {G₁ G₂ : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (h₁ : IsDominated μ n B G₁) (h₂ : IsDominated μ n B G₂) :
    IsDominated μ n B (fun τ ω => G₁ τ ω - G₂ τ ω) := by
  obtain ⟨K₁, hK₁⟩ := h₁
  obtain ⟨K₂, hK₂⟩ := h₂
  refine ⟨K₁ + K₂, fun τ hτ => (hK₁.aestronglyMeasurable τ hτ).sub (hK₂.aestronglyMeasurable τ hτ),
    ?_, ?_⟩
  · filter_upwards [hK₁.contDiffOn, hK₂.contDiffOn] with ω a b
    exact a.sub b
  · filter_upwards [hK₁.contDiffOn, hK₂.contDiffOn, hK₁.norm_iteratedFDeriv_le,
      hK₂.norm_iteratedFDeriv_le] with ω a b c d j hj τ hτ
    have ca : ContDiffAt ℝ j (fun τ => G₁ τ ω) τ :=
      (a.contDiffAt (hB.mem_nhds hτ)).of_le (by exact_mod_cast hj)
    have cb : ContDiffAt ℝ j (fun τ => G₂ τ ω) τ :=
      (b.contDiffAt (hB.mem_nhds hτ)).of_le (by exact_mod_cast hj)
    have e : iteratedFDeriv ℝ j (fun τ => G₁ τ ω - G₂ τ ω) τ =
        iteratedFDeriv ℝ j (fun τ => G₁ τ ω) τ - iteratedFDeriv ℝ j (fun τ => G₂ τ ω) τ := by
      ext m
      exact iteratedFDeriv_sub_apply ca cb ▸ rfl
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (c j hj τ hτ) (d j hj τ hτ))
theorem IsDominated.mul (hB : IsOpen B) {G₁ G₂ : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (h₁ : IsDominated μ n B G₁) (h₂ : IsDominated μ n B G₂) :
    IsDominated μ n B (fun τ ω => G₁ τ ω * G₂ τ ω) := by
  obtain ⟨K₁, hK₁⟩ := h₁
  obtain ⟨K₂, hK₂⟩ := h₂
  refine ⟨∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * |K₁| * |K₂|,
    fun τ hτ => (hK₁.aestronglyMeasurable τ hτ).mul (hK₂.aestronglyMeasurable τ hτ), ?_, ?_⟩
  · filter_upwards [hK₁.contDiffOn, hK₂.contDiffOn] with ω a b
    exact a.mul b
  · filter_upwards [hK₁.contDiffOn, hK₂.contDiffOn, hK₁.norm_iteratedFDeriv_le,
      hK₂.norm_iteratedFDeriv_le] with ω a b c d j hj τ hτ
    have hle := norm_iteratedFDerivWithin_mul_le (n := j) a b hB.uniqueDiffOn hτ
      (by exact_mod_cast hj)
    rw [iteratedFDerivWithin_of_isOpen j hB hτ] at hle
    refine hle.trans ?_
    have hterm : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun τ => G₁ τ ω) B τ‖ *
          ‖iteratedFDerivWithin ℝ (j - i) (fun τ => G₂ τ ω) B τ‖ ≤
        (j.choose i : ℝ) * |K₁| * |K₂| := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [iteratedFDerivWithin_of_isOpen i hB hτ, iteratedFDerivWithin_of_isOpen (j - i) hB hτ]
      have b1 := (c i (hij.trans hj) τ hτ).trans (le_abs_self K₁)
      have b2 := (d (j - i) ((Nat.sub_le _ _).trans hj) τ hτ).trans (le_abs_self K₂)
      have hc : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
      exact mul_le_mul (mul_le_mul_of_nonneg_left b1 hc) b2 (norm_nonneg _)
        (mul_nonneg hc (abs_nonneg _))
    refine (Finset.sum_le_sum hterm).trans ?_
    exact Finset.single_le_sum (f := fun j => ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * |K₁| * |K₂|)
      (fun j _ => Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) (abs_nonneg _))
      (Finset.mem_range.2 (by omega))
theorem IsDominated.exp_neg (hB : IsOpen B) {A : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (h : IsDominated μ n B A) : IsDominated μ n B (fun τ ω => Real.exp (- A τ ω)) := by
  obtain ⟨K, hK⟩ := h
  set D : ℝ := max 1 K with hD
  refine ⟨(n.factorial : ℝ) * Real.exp K * D ^ n + ∑ j ∈ Finset.range (n + 1),
      (j.factorial : ℝ) * Real.exp K * D ^ j, ?_, ?_, ?_⟩
  · intro τ hτ
    exact Real.continuous_exp.comp_aestronglyMeasurable (hK.aestronglyMeasurable τ hτ).neg
  · filter_upwards [hK.contDiffOn] with ω a
    exact a.neg.exp
  · filter_upwards [hK.contDiffOn, hK.norm_iteratedFDeriv_le] with ω a b j hj τ hτ
    have hexp : ContDiffOn ℝ n Real.exp univ := Real.contDiff_exp.contDiffOn
    have hneg : ContDiffOn ℝ n (fun τ => - A τ ω) B := a.neg
    have hle := norm_iteratedFDerivWithin_comp_le (n := j) (N := n) (t := univ) (C := Real.exp K)
      (D := D) hexp hneg (by exact_mod_cast hj) uniqueDiffOn_univ hB.uniqueDiffOn
      (fun _ _ => mem_univ _) hτ ?_ ?_
    · rw [iteratedFDerivWithin_of_isOpen j hB hτ] at hle
      have hnn : ∀ i, 0 ≤ (i.factorial : ℝ) * Real.exp K * D ^ i := fun i =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
          (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
      refine hle.trans ?_
      refine le_trans ?_ (le_add_of_nonneg_left (hnn n))
      exact Finset.single_le_sum (f := fun j => (j.factorial : ℝ) * Real.exp K * D ^ j) (a := j)
        (fun i _ => hnn i) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    · intro i hi
      have h0 : |A τ ω| ≤ K := by
        have := b 0 (by omega) τ hτ
        simpa [norm_iteratedFDeriv_zero] using this
      have hit : iteratedDeriv i Real.exp = Real.exp := by
        rw [iteratedDeriv_eq_iterate]
        exact Real.iter_deriv_exp i
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hit,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 ((neg_le_abs _).trans h0)
    · intro i hi hij
      rw [iteratedFDerivWithin_of_isOpen i hB hτ]
      have e : iteratedFDeriv ℝ i (fun τ => - A τ ω) τ =
          - iteratedFDeriv ℝ i (fun τ => A τ ω) τ :=
        iteratedFDeriv_neg_apply (𝕜 := ℝ) (f := fun τ => A τ ω)
      rw [e, norm_neg]
      have hb := b i (hij.trans hj) τ hτ
      have h1 : (1 : ℝ) ≤ D := le_max_left _ _
      calc _ ≤ K := hb
        _ ≤ D := le_max_right _ _
        _ = D ^ 1 := (pow_one D).symm
        _ ≤ D ^ i := pow_le_pow_right₀ h1 hi
end Dominated
section Means
variable {μ : Measure Ω} {B : Set (Fin k → ℝ)}
def IsEssBounded (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  AEStronglyMeasurable f μ ∧ ∃ C, ∀ᵐ ω ∂μ, |f ω| ≤ C
theorem IsEssBounded.mul {f g : Ω → ℝ} (hf : IsEssBounded μ f) (hg : IsEssBounded μ g) :
    IsEssBounded μ (fun ω => f ω * g ω) := by
  obtain ⟨mf, C, hC⟩ := hf
  obtain ⟨mg, D, hD⟩ := hg
  refine ⟨mf.mul mg, |C| * |D|, ?_⟩
  filter_upwards [hC, hD] with ω a b
  rw [abs_mul]
  exact mul_le_mul (a.trans (le_abs_self _)) (b.trans (le_abs_self _)) (abs_nonneg _)
    (abs_nonneg _)
theorem IsEssBounded.add {f g : Ω → ℝ} (hf : IsEssBounded μ f) (hg : IsEssBounded μ g) :
    IsEssBounded μ (fun ω => f ω + g ω) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.AEBounded.add <;> assumption
theorem IsEssBounded.sub {f g : Ω → ℝ} (hf : IsEssBounded μ f) (hg : IsEssBounded μ g) :
    IsEssBounded μ (fun ω => f ω - g ω) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.AEBounded.sub <;> assumption
theorem IsEssBounded.integrable [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : IsEssBounded μ f) :
    Integrable f μ := by
  obtain ⟨mf, C, hC⟩ := hf
  exact Integrable.of_bound mf C (by simpa [Real.norm_eq_abs] using hC)
theorem IsEssBounded.exp_neg {A : Ω → ℝ} (hA : IsEssBounded μ A) :
    IsEssBounded μ (fun ω => Real.exp (- A ω)) := by
  obtain ⟨mA, C, hC⟩ := hA
  refine ⟨Real.continuous_exp.comp_aestronglyMeasurable mA.neg, Real.exp C, ?_⟩
  filter_upwards [hC] with ω a
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 ((neg_le_abs _).trans a)
theorem gibbsMean_add [IsFiniteMeasure μ] {A f g : Ω → ℝ} (hA : IsEssBounded μ A)
    (hf : IsEssBounded μ f) (hg : IsEssBounded μ g) :
    gibbsMean μ A (fun ω => f ω + g ω) = gibbsMean μ A f + gibbsMean μ A g := by
  unfold gibbsMean
  rw [← add_div, ← integral_add (hf.mul hA.exp_neg).integrable (hg.mul hA.exp_neg).integrable]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [add_mul])
theorem gibbsMean_sub [IsFiniteMeasure μ] {A f g : Ω → ℝ} (hA : IsEssBounded μ A)
    (hf : IsEssBounded μ f) (hg : IsEssBounded μ g) :
    gibbsMean μ A (fun ω => f ω - g ω) = gibbsMean μ A f - gibbsMean μ A g := by
  unfold gibbsMean
  rw [← sub_div, ← integral_sub (hf.mul hA.exp_neg).integrable (hg.mul hA.exp_neg).integrable]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [sub_mul])
theorem gibbsMean_congr_ae {A f g : Ω → ℝ} (h : f =ᵐ[μ] g) :
    gibbsMean μ A f = gibbsMean μ A g := by
  unfold gibbsMean
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with ω a
  rw [a]
theorem IsDominated.isEssBounded {G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ} (h : IsDominated μ n B G)
    {τ : Fin k → ℝ} (hτ : τ ∈ B) : IsEssBounded μ (G τ) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨hK.aestronglyMeasurable τ hτ, K, ?_⟩
  filter_upwards [hK.norm_iteratedFDeriv_le] with ω a
  have := a 0 (by omega) τ hτ
  simpa [norm_iteratedFDeriv_zero] using this
def gibbsMeanFamily (μ : Measure Ω) (A G : (Fin k → ℝ) → Ω → ℝ) : (Fin k → ℝ) → ℝ :=
  fun τ => gibbsMean μ (A τ) (G τ)
def centeredDeriv (A G : (Fin k → ℝ) → Ω → ℝ) (u : Fin k → ℝ) : (Fin k → ℝ) → Ω → ℝ :=
  fun τ ω => paramIteratedDeriv G ![u] τ ω - G τ ω * paramIteratedDeriv A ![u] τ ω
theorem IsDominated.centeredDeriv (hB : IsOpen B) {A G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ}
    (hA : IsDominated μ (n + 1) B A) (hG : IsDominated μ (n + 1) B G) (u : Fin k → ℝ) :
    IsDominated μ n B (centeredDeriv A G u) :=
  (hG.paramDeriv hB u).sub hB ((hG.mono (by omega)).mul hB (hA.paramDeriv hB u))
theorem gibbsMeanFamily_contDiffOn_and_fderiv [IsFiniteMeasure μ] (hB : IsOpen B) (hμ : μ ≠ 0)
    {A G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ} (hA : IsDominated μ (n + 1) B A)
    (hG : IsDominated μ (n + 1) B G) :
    ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (gibbsMeanFamily μ A G) B ∧
      ∀ τ ∈ B, ∀ u, fderiv ℝ (gibbsMeanFamily μ A G) τ u =
        gibbsMeanFamily μ A (centeredDeriv A G u) τ +
          gibbsMeanFamily μ A G τ * gibbsMeanFamily μ A (paramIteratedDeriv A ![u]) τ := by
  have hE : IsDominated μ (n + 1) B (fun τ ω => Real.exp (- A τ ω)) := hA.exp_neg hB
  have hP : IsDominated μ (n + 1) B (fun τ ω => G τ ω * Real.exp (- A τ ω)) := hG.mul hB hE
  obtain ⟨KE, hKE⟩ := id hE
  obtain ⟨KP, hKP⟩ := id hP
  obtain ⟨cZ, fZ⟩ := contDiffOn_integral_and_iteratedFDeriv μ hB KE (n + 1) ℝ _
    hKE.aestronglyMeasurable hKE.contDiffOn hKE.norm_iteratedFDeriv_le
  obtain ⟨cN, fN⟩ := contDiffOn_integral_and_iteratedFDeriv μ hB KP (n + 1) ℝ _
    hKP.aestronglyMeasurable hKP.contDiffOn hKP.norm_iteratedFDeriv_le
  have Zpos : ∀ τ ∈ B, 0 < ∫ ω, Real.exp (- A τ ω) ∂μ := by
    intro τ hτ
    have hi : Integrable (fun ω => Real.exp (- A τ ω)) μ :=
      (hA.isEssBounded hτ).exp_neg.integrable
    have : NeZero μ := ⟨hμ⟩
    exact integral_exp_pos hi
  have hcont : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (gibbsMeanFamily μ A G) B :=
    cN.div cZ fun τ hτ => (Zpos τ hτ).ne'
  refine ⟨hcont, fun τ hτ u => ?_⟩
  have hn0 : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have dN : DifferentiableAt ℝ (fun τ => ∫ ω, G τ ω * Real.exp (- A τ ω) ∂μ) τ :=
    (cN.differentiableOn hn0 τ hτ).differentiableAt (hB.mem_nhds hτ)
  have dZ : DifferentiableAt ℝ (fun τ => ∫ ω, Real.exp (- A τ ω) ∂μ) τ :=
    (cZ.differentiableOn hn0 τ hτ).differentiableAt (hB.mem_nhds hτ)
  have dM : DifferentiableAt ℝ (gibbsMeanFamily μ A G) τ :=
    (hcont.differentiableOn hn0 τ hτ).differentiableAt (hB.mem_nhds hτ)
  obtain ⟨KA, hKA⟩ := id hA
  obtain ⟨KG, hKG⟩ := id hG
  have diffs : ∀ᵐ ω ∂μ, DifferentiableAt ℝ (fun τ => A τ ω) τ ∧
      DifferentiableAt ℝ (fun τ => G τ ω) τ := by
    filter_upwards [hKA.contDiffOn, hKG.contDiffOn] with ω a b
    exact ⟨(a.differentiableOn hn0 τ hτ).differentiableAt (hB.mem_nhds hτ),
      (b.differentiableOn hn0 τ hτ).differentiableAt (hB.mem_nhds hτ)⟩
  have eZ : fderiv ℝ (fun τ => ∫ ω, Real.exp (- A τ ω) ∂μ) τ u =
      - ∫ ω, paramIteratedDeriv A ![u] τ ω * Real.exp (- A τ ω) ∂μ := by
    have h1 := (fZ τ hτ 1 (by omega) ![u]).2
    rw [iteratedFDeriv_one_apply] at h1
    simp only [Matrix.cons_val_zero] at h1
    rw [h1, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [diffs] with ω a
    rw [iteratedFDeriv_one_apply]
    simp only [Matrix.cons_val_zero, paramIteratedDeriv_one]
    have he : HasFDerivAt (fun τ' => Real.exp (- A τ' ω))
        (Real.exp (- A τ ω) • (- fderiv ℝ (fun τ' => A τ' ω) τ)) τ := a.1.hasFDerivAt.neg.exp
    rw [he.fderiv]
    simp [mul_comm]
  have eN : fderiv ℝ (fun τ => ∫ ω, G τ ω * Real.exp (- A τ ω) ∂μ) τ u =
      ∫ ω, centeredDeriv A G u τ ω * Real.exp (- A τ ω) ∂μ := by
    have h1 := (fN τ hτ 1 (by omega) ![u]).2
    rw [iteratedFDeriv_one_apply] at h1
    simp only [Matrix.cons_val_zero] at h1
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [diffs] with ω a
    rw [iteratedFDeriv_one_apply]
    simp only [Matrix.cons_val_zero, centeredDeriv, paramIteratedDeriv_one]
    have he : HasFDerivAt (fun τ' => Real.exp (- A τ' ω))
        (Real.exp (- A τ ω) • (- fderiv ℝ (fun τ' => A τ' ω) τ)) τ := a.1.hasFDerivAt.neg.exp
    have hm : HasFDerivAt (fun τ' => G τ' ω * Real.exp (- A τ' ω))
        (G τ ω • (Real.exp (- A τ ω) • (- fderiv ℝ (fun τ' => A τ' ω) τ)) +
          Real.exp (- A τ ω) • fderiv ℝ (fun τ' => G τ' ω) τ) τ := a.2.hasFDerivAt.mul he
    rw [hm.fderiv]
    simp
    ring
  set Nf : (Fin k → ℝ) → ℝ := fun τ => ∫ ω, G τ ω * Real.exp (- A τ ω) ∂μ with hNf
  set Zf : (Fin k → ℝ) → ℝ := fun τ => ∫ ω, Real.exp (- A τ ω) ∂μ with hZf
  have hl : HasDerivAt (fun t : ℝ => τ + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add τ
  have at0 : τ + (0 : ℝ) • u = τ := by simp
  have lN : HasDerivAt (Nf ∘ fun t : ℝ => τ + t • u) (fderiv ℝ Nf τ u) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by rw [at0]; exact dN.hasFDerivAt) hl
  have lZ : HasDerivAt (Zf ∘ fun t : ℝ => τ + t • u) (fderiv ℝ Zf τ u) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by rw [at0]; exact dZ.hasFDerivAt) hl
  have lM : HasDerivAt (gibbsMeanFamily μ A G ∘ fun t : ℝ => τ + t • u)
      (fderiv ℝ (gibbsMeanFamily μ A G) τ u) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by rw [at0]; exact dM.hasFDerivAt) hl
  have hz0 : (Zf ∘ fun t : ℝ => τ + t • u) 0 ≠ 0 := by
    simp only [Function.comp, at0]
    exact (Zpos τ hτ).ne'
  have lQ := lN.div lZ hz0
  have uniq := lM.unique lQ
  rw [uniq]
  simp only [Function.comp, at0]
  rw [eN, eZ]
  have hZ := (Zpos τ hτ).ne'
  simp only [gibbsMeanFamily, gibbsMean]
  rw [hZf]
  field_simp
  ring
end Means
section Pure
variable {B : Set (Fin k → ℝ)}
def dirDeriv1 (g : (Fin k → ℝ) → ℝ) (u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  fun τ => iteratedFDeriv ℝ 1 g τ ![u]
def dirDeriv2 (g : (Fin k → ℝ) → ℝ) (v u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  fun τ => iteratedFDeriv ℝ 2 g τ ![v, u]
def dirDeriv3 (g : (Fin k → ℝ) → ℝ) (w v u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  fun τ => iteratedFDeriv ℝ 3 g τ ![w, v, u]
theorem dirDeriv1_eq_fderiv (g : (Fin k → ℝ) → ℝ) (u τ : Fin k → ℝ) :
    dirDeriv1 g u τ = fderiv ℝ g τ u := by
  simp [dirDeriv1, iteratedFDeriv_one_apply]
theorem fderiv_iteratedFDeriv_apply_eq_cons {j : ℕ} {g : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hg : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) g τ) (w : Fin k → ℝ) (m : Fin j → Fin k → ℝ) :
    DifferentiableAt ℝ (fun τ' => iteratedFDeriv ℝ j g τ' m) τ ∧
      fderiv ℝ (fun τ' => iteratedFDeriv ℝ j g τ' m) τ w =
        iteratedFDeriv ℝ (j + 1) g τ (Fin.cons w m) := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j g) τ :=
    hg.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)
  have hh : HasFDerivAt (fun τ' => iteratedFDeriv ℝ j g τ' m)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Fin k → ℝ) ℝ m).comp
        (fderiv ℝ (iteratedFDeriv ℝ j g) τ)) τ :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Fin k → ℝ) ℝ m).hasFDerivAt.comp τ
      hd.hasFDerivAt
  refine ⟨hh.differentiableAt, ?_⟩
  rw [hh.fderiv, iteratedFDeriv_succ_apply_left]
  simp [Fin.tail_cons]
theorem dirDeriv1_differentiableAt_and_fderiv {g : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hg : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) g τ) (v u : Fin k → ℝ) :
    DifferentiableAt ℝ (dirDeriv1 g u) τ ∧ fderiv ℝ (dirDeriv1 g u) τ v = dirDeriv2 g v u τ :=
  fderiv_iteratedFDeriv_apply_eq_cons (j := 1) hg v ![u]
theorem dirDeriv2_differentiableAt_and_fderiv {g : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hg : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) g τ) (w v u : Fin k → ℝ) :
    DifferentiableAt ℝ (dirDeriv2 g v u) τ ∧
      fderiv ℝ (dirDeriv2 g v u) τ w = dirDeriv3 g w v u τ :=
  fderiv_iteratedFDeriv_apply_eq_cons (j := 2) hg w ![v, u]
def twistedDeriv (α : (Fin k → ℝ) → ℝ) (u : Fin k → ℝ) (g : (Fin k → ℝ) → ℝ) :
    (Fin k → ℝ) → ℝ :=
  dirDeriv1 g u - g * dirDeriv1 α u
def twistedDerivTwo (h α : (Fin k → ℝ) → ℝ) (v u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  dirDeriv2 h v u - dirDeriv1 h u * dirDeriv1 α v - dirDeriv1 h v * dirDeriv1 α u -
    h * dirDeriv2 α v u + h * dirDeriv1 α u * dirDeriv1 α v
def twistedDerivThree (h α : (Fin k → ℝ) → ℝ) (w v u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  dirDeriv3 h w v u - dirDeriv2 h v u * dirDeriv1 α w - dirDeriv2 h w u * dirDeriv1 α v -
    dirDeriv2 h w v * dirDeriv1 α u -
    dirDeriv1 h u * dirDeriv2 α w v - dirDeriv1 h v * dirDeriv2 α w u -
    dirDeriv1 h w * dirDeriv2 α v u +
    dirDeriv1 h u * dirDeriv1 α v * dirDeriv1 α w + dirDeriv1 h v * dirDeriv1 α u * dirDeriv1 α w +
    dirDeriv1 h w * dirDeriv1 α u * dirDeriv1 α v -
    h * dirDeriv3 α w v u + h * dirDeriv2 α v u * dirDeriv1 α w +
    h * dirDeriv2 α w u * dirDeriv1 α v + h * dirDeriv2 α w v * dirDeriv1 α u -
    h * dirDeriv1 α u * dirDeriv1 α v * dirDeriv1 α w
def twistedDerivTwoOfDeriv (α : (Fin k → ℝ) → ℝ) (w v u : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  dirDeriv3 α w v u - dirDeriv2 α v u * dirDeriv1 α w - dirDeriv2 α w u * dirDeriv1 α v -
    dirDeriv2 α w v * dirDeriv1 α u + dirDeriv1 α u * dirDeriv1 α v * dirDeriv1 α w
theorem twistedDeriv_twistedDeriv {h α : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hh : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) h τ) (hα : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) α τ)
    (v u : Fin k → ℝ) : twistedDeriv α v (twistedDeriv α u h) τ = twistedDerivTwo h α v u τ := by
  have n2 : ((2 : ℕ) : WithTop ℕ∞) ≠ 0 := by norm_num
  have H0 := (hh.differentiableAt n2).hasFDerivAt
  obtain ⟨D1, F1⟩ := dirDeriv1_differentiableAt_and_fderiv hh v u
  obtain ⟨D2, F2⟩ := dirDeriv1_differentiableAt_and_fderiv hα v u
  have e := D1.hasFDerivAt.sub (H0.mul D2.hasFDerivAt)
  have e' : dirDeriv1 (twistedDeriv α u h) v τ =
      fderiv ℝ (dirDeriv1 h u - h * dirDeriv1 α u) τ v := dirDeriv1_eq_fderiv _ _ _
  simp only [twistedDeriv, Pi.sub_apply, Pi.mul_apply] at e' ⊢
  rw [e', e.fderiv]
  simp only [sub_apply, add_apply,
    smul_apply, smul_eq_mul, F1, F2, twistedDerivTwo, Pi.add_apply, Pi.sub_apply,
    Pi.mul_apply, ← dirDeriv1_eq_fderiv]
  ring
theorem twistedDeriv_three {h α : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ} {B : Set (Fin k → ℝ)}
    (hB : IsOpen B) (hτ : τ ∈ B) (hh : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) h B)
    (hα : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) α B) (w v u : Fin k → ℝ) :
    twistedDeriv α w (twistedDeriv α v (twistedDeriv α u h)) τ = twistedDerivThree h α w v u τ := by
  have n3 : ((3 : ℕ) : WithTop ℕ∞) ≠ 0 := by norm_num
  have c3 : ∀ {g : (Fin k → ℝ) → ℝ}, ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) g B → ∀ σ ∈ B,
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) g σ := fun hg σ hσ => hg.contDiffAt (hB.mem_nhds hσ)
  have c2 : ∀ {g : (Fin k → ℝ) → ℝ}, ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) g B → ∀ σ ∈ B,
      ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) g σ := fun hg σ hσ =>
    (c3 hg σ hσ).of_le (by norm_num)
  have heq : twistedDeriv α v (twistedDeriv α u h) =ᶠ[𝓝 τ] twistedDerivTwo h α v u := by
    filter_upwards [hB.mem_nhds hτ] with σ hσ
    exact twistedDeriv_twistedDeriv (c2 hh σ hσ) (c2 hα σ hσ) v u
  have H0 := ((c3 hh τ hτ).differentiableAt n3).hasFDerivAt
  obtain ⟨Dhu, Fhu⟩ := dirDeriv1_differentiableAt_and_fderiv (c2 hh τ hτ) w u
  obtain ⟨Dhv, Fhv⟩ := dirDeriv1_differentiableAt_and_fderiv (c2 hh τ hτ) w v
  obtain ⟨Dau, Fau⟩ := dirDeriv1_differentiableAt_and_fderiv (c2 hα τ hτ) w u
  obtain ⟨Dav, Fav⟩ := dirDeriv1_differentiableAt_and_fderiv (c2 hα τ hτ) w v
  obtain ⟨Dh2, Fh2⟩ := dirDeriv2_differentiableAt_and_fderiv (c3 hh τ hτ) w v u
  obtain ⟨Da2, Fa2⟩ := dirDeriv2_differentiableAt_and_fderiv (c3 hα τ hτ) w v u
  have e := (((Dh2.hasFDerivAt.sub (Dhu.hasFDerivAt.mul Dav.hasFDerivAt)).sub
    (Dhv.hasFDerivAt.mul Dau.hasFDerivAt)).sub (H0.mul Da2.hasFDerivAt)).add
      ((H0.mul Dau.hasFDerivAt).mul Dav.hasFDerivAt)
  have e' : dirDeriv1 (twistedDeriv α v (twistedDeriv α u h)) w τ =
      fderiv ℝ (twistedDerivTwo h α v u) τ w := by
    rw [dirDeriv1_eq_fderiv, heq.fderiv_eq]
  have e0 : twistedDeriv α v (twistedDeriv α u h) τ = twistedDerivTwo h α v u τ := heq.eq_of_nhds
  have e'' : fderiv ℝ (twistedDerivTwo h α v u) τ = _ := e.fderiv
  have a1 : dirDeriv1 (twistedDeriv α v (twistedDeriv α u h)) w τ -
        twistedDeriv α v (twistedDeriv α u h) τ * dirDeriv1 α w τ =
      fderiv ℝ (twistedDerivTwo h α v u) τ w - twistedDerivTwo h α v u τ * dirDeriv1 α w τ := by
    rw [e', e0]
  change dirDeriv1 (twistedDeriv α v (twistedDeriv α u h)) w τ -
    twistedDeriv α v (twistedDeriv α u h) τ * dirDeriv1 α w τ = _
  rw [a1, e'']
  simp only [sub_apply, add_apply,
    smul_apply, smul_eq_mul, Fhu, Fhv, Fau, Fav, Fh2, Fa2, twistedDerivTwo, twistedDerivThree,
    Pi.add_apply, Pi.sub_apply, Pi.mul_apply, ← dirDeriv1_eq_fderiv]
  ring
theorem twistedDeriv_dirDeriv1 {α : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    (hα : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) α τ) (v u : Fin k → ℝ) :
    twistedDeriv α v (dirDeriv1 α u) τ = dirDeriv2 α v u τ - dirDeriv1 α u τ * dirDeriv1 α v τ := by
  simp only [twistedDeriv, Pi.sub_apply, Pi.mul_apply, dirDeriv1_eq_fderiv _ v,
    (dirDeriv1_differentiableAt_and_fderiv hα v u).2]
theorem twistedDeriv_twistedDeriv_dirDeriv1 {α : (Fin k → ℝ) → ℝ} {τ : Fin k → ℝ}
    {B : Set (Fin k → ℝ)} (hB : IsOpen B) (hτ : τ ∈ B)
    (hα : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) α B) (w v u : Fin k → ℝ) :
    twistedDeriv α w (twistedDeriv α v (dirDeriv1 α u)) τ = twistedDerivTwoOfDeriv α w v u τ := by
  have c3 : ∀ σ ∈ B, ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) α σ := fun σ hσ =>
    hα.contDiffAt (hB.mem_nhds hσ)
  have c2 : ∀ σ ∈ B, ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) α σ := fun σ hσ =>
    (c3 σ hσ).of_le (by norm_num)
  have heq : twistedDeriv α v (dirDeriv1 α u) =ᶠ[𝓝 τ]
      dirDeriv2 α v u - dirDeriv1 α u * dirDeriv1 α v := by
    filter_upwards [hB.mem_nhds hτ] with σ hσ
    exact twistedDeriv_dirDeriv1 (c2 σ hσ) v u
  obtain ⟨Dau, Fau⟩ := dirDeriv1_differentiableAt_and_fderiv (c2 τ hτ) w u
  obtain ⟨Dav, Fav⟩ := dirDeriv1_differentiableAt_and_fderiv (c2 τ hτ) w v
  obtain ⟨Da2, Fa2⟩ := dirDeriv2_differentiableAt_and_fderiv (c3 τ hτ) w v u
  have e := Da2.hasFDerivAt.sub (Dau.hasFDerivAt.mul Dav.hasFDerivAt)
  have e' : dirDeriv1 (twistedDeriv α v (dirDeriv1 α u)) w τ =
      fderiv ℝ (dirDeriv2 α v u - dirDeriv1 α u * dirDeriv1 α v) τ w := by
    rw [dirDeriv1_eq_fderiv, heq.fderiv_eq]
  have e0 : twistedDeriv α v (dirDeriv1 α u) τ =
      (dirDeriv2 α v u - dirDeriv1 α u * dirDeriv1 α v) τ := heq.eq_of_nhds
  change dirDeriv1 (twistedDeriv α v (dirDeriv1 α u)) w τ -
    twistedDeriv α v (dirDeriv1 α u) τ * dirDeriv1 α w τ = _
  rw [e', e0, e.fderiv]
  simp only [sub_apply, add_apply,
    smul_apply, smul_eq_mul, Fau, Fav, Fa2, twistedDerivTwoOfDeriv, Pi.add_apply,
    Pi.sub_apply, Pi.mul_apply, ← dirDeriv1_eq_fderiv]
  ring
end Pure
section Main
variable {μ : Measure Ω} {B : Set (Fin k → ℝ)}
theorem isEssBounded_paramIteratedDeriv [IsFiniteMeasure μ] (hB : IsOpen B)
    {G : (Fin k → ℝ) → Ω → ℝ} {n : ℕ} {K : ℝ}
    (hG : IsDominatedSmoothFamily μ n B K G) {τ : Fin k → ℝ} (hτ : τ ∈ B) {j : ℕ} (hj : j ≤ n)
    (v : Fin j → Fin k → ℝ) : IsEssBounded μ (paramIteratedDeriv G v τ) := by
  obtain ⟨_, f⟩ := contDiffOn_integral_and_iteratedFDeriv μ hB K n ℝ G hG.aestronglyMeasurable
    hG.contDiffOn hG.norm_iteratedFDeriv_le
  refine ⟨(f τ hτ j hj v).1, K * ∏ l, ‖v l‖, ?_⟩
  filter_upwards [hG.norm_iteratedFDeriv_le] with ω a
  refine ((iteratedFDeriv ℝ j (fun τ' => G τ' ω) τ).le_opNorm v).trans ?_
  exact mul_le_mul_of_nonneg_right (a j hj τ hτ) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
theorem gibbsMean_sum_five [IsFiniteMeasure μ] {A x₁ x₂ x₃ x₄ x₅ : Ω → ℝ} (hA : IsEssBounded μ A)
    (b₁ : IsEssBounded μ x₁) (b₂ : IsEssBounded μ x₂) (b₃ : IsEssBounded μ x₃)
    (b₄ : IsEssBounded μ x₄) (b₅ : IsEssBounded μ x₅) :
    gibbsMean μ A (fun ω => x₁ ω - x₂ ω - x₃ ω - x₄ ω + x₅ ω) =
      gibbsMean μ A x₁ - gibbsMean μ A x₂ - gibbsMean μ A x₃ - gibbsMean μ A x₄ +
        gibbsMean μ A x₅ := by
  have s₂ := b₁.sub b₂
  have s₃ := s₂.sub b₃
  have s₄ := s₃.sub b₄
  rw [gibbsMean_add hA s₄ b₅, gibbsMean_sub hA s₃ b₄, gibbsMean_sub hA s₂ b₃,
    gibbsMean_sub hA b₁ b₂]
theorem gibbsMean_sum_fifteen [IsFiniteMeasure μ]
    {A x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ : Ω → ℝ}
    (hA : IsEssBounded μ A) (b₁ : IsEssBounded μ x₁) (b₂ : IsEssBounded μ x₂)
    (b₃ : IsEssBounded μ x₃) (b₄ : IsEssBounded μ x₄) (b₅ : IsEssBounded μ x₅)
    (b₆ : IsEssBounded μ x₆) (b₇ : IsEssBounded μ x₇) (b₈ : IsEssBounded μ x₈)
    (b₉ : IsEssBounded μ x₉) (b₁₀ : IsEssBounded μ x₁₀) (b₁₁ : IsEssBounded μ x₁₁)
    (b₁₂ : IsEssBounded μ x₁₂) (b₁₃ : IsEssBounded μ x₁₃) (b₁₄ : IsEssBounded μ x₁₄)
    (b₁₅ : IsEssBounded μ x₁₅) :
    gibbsMean μ A (fun ω => x₁ ω - x₂ ω - x₃ ω - x₄ ω - x₅ ω - x₆ ω - x₇ ω + x₈ ω + x₉ ω +
        x₁₀ ω - x₁₁ ω + x₁₂ ω + x₁₃ ω + x₁₄ ω - x₁₅ ω) =
      gibbsMean μ A x₁ - gibbsMean μ A x₂ - gibbsMean μ A x₃ - gibbsMean μ A x₄ -
        gibbsMean μ A x₅ - gibbsMean μ A x₆ - gibbsMean μ A x₇ + gibbsMean μ A x₈ +
        gibbsMean μ A x₉ + gibbsMean μ A x₁₀ - gibbsMean μ A x₁₁ +
        gibbsMean μ A x₁₂ + gibbsMean μ A x₁₃ + gibbsMean μ A x₁₄ -
        gibbsMean μ A x₁₅ := by
  have s₂ := b₁.sub b₂
  have s₃ := s₂.sub b₃
  have s₄ := s₃.sub b₄
  have s₅ := s₄.sub b₅
  have s₆ := s₅.sub b₆
  have s₇ := s₆.sub b₇
  have s₈ := s₇.add b₈
  have s₉ := s₈.add b₉
  have s₁₀ := s₉.add b₁₀
  have s₁₁ := s₁₀.sub b₁₁
  have s₁₂ := s₁₁.add b₁₂
  have s₁₃ := s₁₂.add b₁₃
  have s₁₄ := s₁₃.add b₁₄
  rw [gibbsMean_sub hA s₁₄ b₁₅, gibbsMean_add hA s₁₃ b₁₄, gibbsMean_add hA s₁₂ b₁₃,
    gibbsMean_add hA s₁₁ b₁₂, gibbsMean_sub hA s₁₀ b₁₁, gibbsMean_add hA s₉ b₁₀,
    gibbsMean_add hA s₈ b₉, gibbsMean_add hA s₇ b₈, gibbsMean_sub hA s₆ b₇,
    gibbsMean_sub hA s₅ b₆, gibbsMean_sub hA s₄ b₅, gibbsMean_sub hA s₃ b₄,
    gibbsMean_sub hA s₂ b₃, gibbsMean_sub hA b₁ b₂]
theorem gibbsMean_iteratedFDeriv_three [IsFiniteMeasure μ] (hB : IsOpen B) (hμ : μ ≠ 0) {K : ℝ}
    {A H : (Fin k → ℝ) → Ω → ℝ} (hA : IsDominatedSmoothFamily μ 3 B K A)
    (hH : IsDominatedSmoothFamily μ 3 B K H) :
    ContDiffOn ℝ 3 (fun τ => gibbsMean μ (A τ) (H τ)) B ∧
      ∀ τ ∈ B, ∀ u v w : Fin k → ℝ,
        iteratedFDeriv ℝ 1 (fun τ => gibbsMean μ (A τ) (H τ)) τ ![u] =
          gibbsMean μ (A τ) (paramIteratedDeriv H ![u] τ) -
            gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ) ∧
        iteratedFDeriv ℝ 2 (fun τ => gibbsMean μ (A τ) (H τ)) τ ![v, u] =
          gibbsMean μ (A τ) (paramIteratedDeriv H ![v, u] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![v] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![u] τ) -
            gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![v, u] τ) +
            gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ)
              (paramIteratedDeriv A ![v] τ) ∧
        iteratedFDeriv ℝ 3 (fun τ => gibbsMean μ (A τ) (H τ)) τ ![w, v, u] =
          gibbsMean μ (A τ) (paramIteratedDeriv H ![w, v, u] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![v, u] τ) (paramIteratedDeriv A ![w] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![w, u] τ) (paramIteratedDeriv A ![v] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![w, v] τ) (paramIteratedDeriv A ![u] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![w, v] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![w, u] τ) -
            gibbsCovariance μ (A τ) (paramIteratedDeriv H ![w] τ) (paramIteratedDeriv A ![v, u] τ) +
            gibbsCumulantThree μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![v] τ)
              (paramIteratedDeriv A ![w] τ) +
            gibbsCumulantThree μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![u] τ)
              (paramIteratedDeriv A ![w] τ) +
            gibbsCumulantThree μ (A τ) (paramIteratedDeriv H ![w] τ) (paramIteratedDeriv A ![u] τ)
              (paramIteratedDeriv A ![v] τ) -
            gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![w, v, u] τ) +
            gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![v, u] τ)
              (paramIteratedDeriv A ![w] τ) +
            gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![w, u] τ)
              (paramIteratedDeriv A ![v] τ) +
            gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![w, v] τ)
              (paramIteratedDeriv A ![u] τ) -
            gibbsCumulantFour μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ)
              (paramIteratedDeriv A ![v] τ) (paramIteratedDeriv A ![w] τ) := by
  have DA : IsDominated μ 3 B A := ⟨K, hA⟩
  have DH : IsDominated μ 3 B H := ⟨K, hH⟩
  have DA2 : IsDominated μ 2 B A := DA.mono (by omega)
  have DA1 : IsDominated μ 1 B A := DA.mono (by omega)
  have Da : ∀ u, IsDominated μ 2 B (paramIteratedDeriv A ![u]) := fun u =>
    IsDominated.paramDeriv hB DA u
  have DS : ∀ u, IsDominated μ 2 B (centeredDeriv A H u) := fun u =>
    IsDominated.centeredDeriv hB DA DH u
  have DSS : ∀ u v, IsDominated μ 1 B (centeredDeriv A (centeredDeriv A H u) v) := fun u v =>
    IsDominated.centeredDeriv hB DA2 (DS u) v
  have DSa : ∀ u v, IsDominated μ 1 B (centeredDeriv A (paramIteratedDeriv A ![u]) v) :=
    fun u v => IsDominated.centeredDeriv hB DA2 (Da u) v
  have R3 := gibbsMeanFamily_contDiffOn_and_fderiv hB hμ (n := 2) DA DH
  have R2 : ∀ G, IsDominated μ 2 B G →
      ContDiffOn ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) (gibbsMeanFamily μ A G) B ∧
      ∀ τ ∈ B, ∀ u, fderiv ℝ (gibbsMeanFamily μ A G) τ u =
        gibbsMeanFamily μ A (centeredDeriv A G u) τ +
        gibbsMeanFamily μ A G τ * gibbsMeanFamily μ A (paramIteratedDeriv A ![u]) τ :=
    fun G hG => gibbsMeanFamily_contDiffOn_and_fderiv hB hμ (n := 1) DA2 hG
  have R1 : ∀ G, IsDominated μ 1 B G →
      ContDiffOn ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (gibbsMeanFamily μ A G) B ∧
      ∀ τ ∈ B, ∀ u, fderiv ℝ (gibbsMeanFamily μ A G) τ u =
        gibbsMeanFamily μ A (centeredDeriv A G u) τ +
        gibbsMeanFamily μ A G τ * gibbsMeanFamily μ A (paramIteratedDeriv A ![u]) τ :=
    fun G hG => gibbsMeanFamily_contDiffOn_and_fderiv hB hμ (n := 0) DA1 hG
  have c3 : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (gibbsMeanFamily μ A H) B := by simpa using R3.1
  have c3' : ContDiffOn ℝ 3 (gibbsMeanFamily μ A H) B := by simpa using c3
  refine ⟨c3', fun τ hτ u v w => ?_⟩
  have d3f : ∀ σ ∈ B, DifferentiableAt ℝ (gibbsMeanFamily μ A H) σ := fun σ hσ =>
    (c3.contDiffAt (hB.mem_nhds hσ)).differentiableAt (by norm_num)
  have d2f : ∀ G, IsDominated μ 2 B G → ∀ σ ∈ B, DifferentiableAt ℝ (gibbsMeanFamily μ A G) σ :=
    fun G hG σ hσ => ((R2 G hG).1.contDiffAt (hB.mem_nhds hσ)).differentiableAt (by norm_num)
  have d1f : ∀ G, IsDominated μ 1 B G → ∀ σ ∈ B, DifferentiableAt ℝ (gibbsMeanFamily μ A G) σ :=
    fun G hG σ hσ => ((R1 G hG).1.contDiffAt (hB.mem_nhds hσ)).differentiableAt (by norm_num)
  have e1 : ∀ u, ∀ σ ∈ B, iteratedFDeriv ℝ 1 (gibbsMeanFamily μ A H) σ ![u] =
      (gibbsMeanFamily μ A (centeredDeriv A H u) +
        gibbsMeanFamily μ A H * gibbsMeanFamily μ A (paramIteratedDeriv A ![u])) σ := by
    intro u σ hσ
    rw [iteratedFDeriv_one_apply]
    exact R3.2 σ hσ u
  have e2f : ∀ v u, ∀ σ ∈ B, iteratedFDeriv ℝ 2 (gibbsMeanFamily μ A H) σ ![v, u] =
      (gibbsMeanFamily μ A (centeredDeriv A (centeredDeriv A H u) v) +
          gibbsMeanFamily μ A (centeredDeriv A H u) *
            gibbsMeanFamily μ A (paramIteratedDeriv A ![v]) +
        (gibbsMeanFamily μ A (centeredDeriv A H v) +
            gibbsMeanFamily μ A H * gibbsMeanFamily μ A (paramIteratedDeriv A ![v])) *
          gibbsMeanFamily μ A (paramIteratedDeriv A ![u]) +
        gibbsMeanFamily μ A H *
          (gibbsMeanFamily μ A (centeredDeriv A (paramIteratedDeriv A ![u]) v) +
            gibbsMeanFamily μ A (paramIteratedDeriv A ![u]) *
              gibbsMeanFamily μ A (paramIteratedDeriv A ![v]))) σ := by
    intro v u σ hσ
    have ci := (fderiv_iteratedFDeriv_apply_eq_cons (j := 1) (g := gibbsMeanFamily μ A H) (τ := σ)
      ((c3.contDiffAt (hB.mem_nhds hσ)).of_le (by norm_num)) v ![u]).2
    have ev : (fun τ' => iteratedFDeriv ℝ 1 (gibbsMeanFamily μ A H) τ' ![u]) =ᶠ[𝓝 σ]
        (gibbsMeanFamily μ A (centeredDeriv A H u) +
          gibbsMeanFamily μ A H * gibbsMeanFamily μ A (paramIteratedDeriv A ![u])) := by
      filter_upwards [hB.mem_nhds hσ] with ρ hρ
      exact e1 u ρ hρ
    have hX := (d2f _ (DS u) σ hσ).hasFDerivAt.add
      ((d3f σ hσ).hasFDerivAt.mul (d2f _ (Da u) σ hσ).hasFDerivAt)
    have ci' : iteratedFDeriv ℝ 2 (gibbsMeanFamily μ A H) σ ![v, u] =
        fderiv ℝ (gibbsMeanFamily μ A (centeredDeriv A H u) +
          gibbsMeanFamily μ A H * gibbsMeanFamily μ A (paramIteratedDeriv A ![u])) σ v := by
      rw [← ev.fderiv_eq]
      exact ci.symm
    rw [ci', hX.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, Pi.add_apply, Pi.mul_apply,
      (R2 _ (DS u)).2 σ hσ v, (R2 _ (Da u)).2 σ hσ v, R3.2 σ hσ v]
    ring
  have H1 := (d1f _ (DSS u v) τ hτ).hasFDerivAt
  have H2 := (d2f _ (DS u) τ hτ).hasFDerivAt
  have H3 := (d2f _ (Da v) τ hτ).hasFDerivAt
  have H4 := (d2f _ (DS v) τ hτ).hasFDerivAt
  have H5 := (d3f τ hτ).hasFDerivAt
  have H6 := (d2f _ (Da u) τ hτ).hasFDerivAt
  have H7 := (d1f _ (DSa u v) τ hτ).hasFDerivAt
  have hQ := ((H1.add (H2.mul H3)).add ((H4.add (H5.mul H3)).mul H6)).add
    (H5.mul (H7.add (H6.mul H3)))
  have e3f : iteratedFDeriv ℝ 3 (gibbsMeanFamily μ A H) τ ![w, v, u] =
      fderiv ℝ (gibbsMeanFamily μ A (centeredDeriv A (centeredDeriv A H u) v) +
          gibbsMeanFamily μ A (centeredDeriv A H u) *
            gibbsMeanFamily μ A (paramIteratedDeriv A ![v]) +
        (gibbsMeanFamily μ A (centeredDeriv A H v) +
            gibbsMeanFamily μ A H * gibbsMeanFamily μ A (paramIteratedDeriv A ![v])) *
          gibbsMeanFamily μ A (paramIteratedDeriv A ![u]) +
        gibbsMeanFamily μ A H *
          (gibbsMeanFamily μ A (centeredDeriv A (paramIteratedDeriv A ![u]) v) +
            gibbsMeanFamily μ A (paramIteratedDeriv A ![u]) *
              gibbsMeanFamily μ A (paramIteratedDeriv A ![v]))) τ w := by
    have ci := (fderiv_iteratedFDeriv_apply_eq_cons (j := 2) (g := gibbsMeanFamily μ A H) (τ := τ)
      (c3.contDiffAt (hB.mem_nhds hτ)) w ![v, u]).2
    have ev : (fun τ' => iteratedFDeriv ℝ 2 (gibbsMeanFamily μ A H) τ' ![v, u]) =ᶠ[𝓝 τ]
        (gibbsMeanFamily μ A (centeredDeriv A (centeredDeriv A H u) v) +
          gibbsMeanFamily μ A (centeredDeriv A H u) *
            gibbsMeanFamily μ A (paramIteratedDeriv A ![v]) +
        (gibbsMeanFamily μ A (centeredDeriv A H v) +
            gibbsMeanFamily μ A H * gibbsMeanFamily μ A (paramIteratedDeriv A ![v])) *
          gibbsMeanFamily μ A (paramIteratedDeriv A ![u]) +
        gibbsMeanFamily μ A H *
          (gibbsMeanFamily μ A (centeredDeriv A (paramIteratedDeriv A ![u]) v) +
            gibbsMeanFamily μ A (paramIteratedDeriv A ![u]) *
              gibbsMeanFamily μ A (paramIteratedDeriv A ![v]))) := by
      filter_upwards [hB.mem_nhds hτ] with ρ hρ
      exact e2f v u ρ hρ
    rw [← ev.fderiv_eq]
    exact ci.symm
  have bA : IsEssBounded μ (A τ) := DA.isEssBounded hτ
  have bH : IsEssBounded μ (H τ) := DH.isEssBounded hτ
  have bh1 : ∀ u, IsEssBounded μ (paramIteratedDeriv H ![u] τ) := fun u =>
    isEssBounded_paramIteratedDeriv hB hH hτ (j := 1) (by omega) ![u]
  have ba1 : ∀ u, IsEssBounded μ (paramIteratedDeriv A ![u] τ) := fun u =>
    isEssBounded_paramIteratedDeriv hB hA hτ (j := 1) (by omega) ![u]
  have bh2 : ∀ v u, IsEssBounded μ (paramIteratedDeriv H ![v, u] τ) := fun v u =>
    isEssBounded_paramIteratedDeriv hB hH hτ (j := 2) (by omega) ![v, u]
  have ba2 : ∀ v u, IsEssBounded μ (paramIteratedDeriv A ![v, u] τ) := fun v u =>
    isEssBounded_paramIteratedDeriv hB hA hτ (j := 2) (by omega) ![v, u]
  have bh3 : IsEssBounded μ (paramIteratedDeriv H ![w, v, u] τ) :=
    isEssBounded_paramIteratedDeriv hB hH hτ (j := 3) (by omega) ![w, v, u]
  have ba3 : IsEssBounded μ (paramIteratedDeriv A ![w, v, u] τ) :=
    isEssBounded_paramIteratedDeriv hB hA hτ (j := 3) (by omega) ![w, v, u]
  have mS : ∀ u, gibbsMeanFamily μ A (centeredDeriv A H u) τ =
      gibbsMean μ (A τ) (paramIteratedDeriv H ![u] τ) -
      gibbsMean μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![u] τ ω) := fun u =>
    gibbsMean_sub bA (bh1 u) (bH.mul (ba1 u))
  have c3H : ∀ᵐ ω ∂μ, ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ => H τ ω) B ∧
      ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ => A τ ω) B := by
    filter_upwards [hH.contDiffOn, hA.contDiffOn] with ω a b
    exact ⟨a, b⟩
  have at2 : ∀ {g : (Fin k → ℝ) → ℝ}, ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) g B →
      ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) g τ := fun hg =>
    (hg.contDiffAt (hB.mem_nhds hτ)).of_le (by norm_num)
  have mSS : ∀ v u, gibbsMeanFamily μ A (centeredDeriv A (centeredDeriv A H u) v) τ =
      gibbsMean μ (A τ) (paramIteratedDeriv H ![v, u] τ) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![u] τ ω * paramIteratedDeriv A ![v] τ ω) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![v] τ ω * paramIteratedDeriv A ![u] τ ω) -
        gibbsMean μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![v, u] τ ω) +
        gibbsMean μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![u] τ ω *
          paramIteratedDeriv A ![v] τ ω) := by
    intro v u
    rw [← gibbsMean_sum_five bA (bh2 v u) ((bh1 u).mul (ba1 v)) ((bh1 v).mul (ba1 u))
      (bH.mul (ba2 v u)) ((bH.mul (ba1 u)).mul (ba1 v))]
    refine gibbsMean_congr_ae ?_
    filter_upwards [c3H] with ω a
    exact twistedDeriv_twistedDeriv (at2 a.1) (at2 a.2) v u
  have mSa : ∀ v u, gibbsMeanFamily μ A (centeredDeriv A (paramIteratedDeriv A ![u]) v) τ =
      gibbsMean μ (A τ) (paramIteratedDeriv A ![v, u] τ) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv A ![u] τ ω *
          paramIteratedDeriv A ![v] τ ω) := by
    intro v u
    rw [← gibbsMean_sub bA (ba2 v u) ((ba1 u).mul (ba1 v))]
    refine gibbsMean_congr_ae ?_
    filter_upwards [c3H] with ω a
    exact twistedDeriv_dirDeriv1 (at2 a.2) v u
  have mSSS : gibbsMeanFamily μ A (centeredDeriv A (centeredDeriv A (centeredDeriv A H u) v) w) τ =
      gibbsMean μ (A τ) (paramIteratedDeriv H ![w, v, u] τ) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![v, u] τ ω *
          paramIteratedDeriv A ![w] τ ω) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![w, u] τ ω *
          paramIteratedDeriv A ![v] τ ω) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![w, v] τ ω *
          paramIteratedDeriv A ![u] τ ω) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![u] τ ω *
          paramIteratedDeriv A ![w, v] τ ω) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![v] τ ω *
          paramIteratedDeriv A ![w, u] τ ω) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![w] τ ω *
          paramIteratedDeriv A ![v, u] τ ω) +
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![u] τ ω *
          paramIteratedDeriv A ![v] τ ω * paramIteratedDeriv A ![w] τ ω) +
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![v] τ ω *
          paramIteratedDeriv A ![u] τ ω * paramIteratedDeriv A ![w] τ ω) +
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv H ![w] τ ω *
          paramIteratedDeriv A ![u] τ ω * paramIteratedDeriv A ![v] τ ω) -
        gibbsMean μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![w, v, u] τ ω) +
        gibbsMean μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![v, u] τ ω *
          paramIteratedDeriv A ![w] τ ω) +
        gibbsMean μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![w, u] τ ω *
          paramIteratedDeriv A ![v] τ ω) +
        gibbsMean μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![w, v] τ ω *
          paramIteratedDeriv A ![u] τ ω) -
        gibbsMean μ (A τ) (fun ω => H τ ω * paramIteratedDeriv A ![u] τ ω *
          paramIteratedDeriv A ![v] τ ω * paramIteratedDeriv A ![w] τ ω) := by
    rw [← gibbsMean_sum_fifteen bA bh3 ((bh2 v u).mul (ba1 w)) ((bh2 w u).mul (ba1 v))
      ((bh2 w v).mul (ba1 u)) ((bh1 u).mul (ba2 w v)) ((bh1 v).mul (ba2 w u))
      ((bh1 w).mul (ba2 v u)) (((bh1 u).mul (ba1 v)).mul (ba1 w))
      (((bh1 v).mul (ba1 u)).mul (ba1 w)) (((bh1 w).mul (ba1 u)).mul (ba1 v)) (bH.mul ba3)
      ((bH.mul (ba2 v u)).mul (ba1 w)) ((bH.mul (ba2 w u)).mul (ba1 v))
      ((bH.mul (ba2 w v)).mul (ba1 u)) (((bH.mul (ba1 u)).mul (ba1 v)).mul (ba1 w))]
    refine gibbsMean_congr_ae ?_
    filter_upwards [c3H] with ω a
    exact twistedDeriv_three hB hτ a.1 a.2 w v u
  have mSSa : gibbsMeanFamily μ A
      (centeredDeriv A (centeredDeriv A (paramIteratedDeriv A ![u]) v) w) τ =
      gibbsMean μ (A τ) (paramIteratedDeriv A ![w, v, u] τ) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv A ![v, u] τ ω *
          paramIteratedDeriv A ![w] τ ω) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv A ![w, u] τ ω *
          paramIteratedDeriv A ![v] τ ω) -
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv A ![w, v] τ ω *
          paramIteratedDeriv A ![u] τ ω) +
        gibbsMean μ (A τ) (fun ω => paramIteratedDeriv A ![u] τ ω *
          paramIteratedDeriv A ![v] τ ω * paramIteratedDeriv A ![w] τ ω) := by
    rw [← gibbsMean_sum_five bA ba3 ((ba2 v u).mul (ba1 w)) ((ba2 w u).mul (ba1 v))
      ((ba2 w v).mul (ba1 u)) (((ba1 u).mul (ba1 v)).mul (ba1 w))]
    refine gibbsMean_congr_ae ?_
    filter_upwards [c3H] with ω a
    exact twistedDeriv_twistedDeriv_dirDeriv1 hB hτ a.2 w v u
  have hM : ∀ G : (Fin k → ℝ) → Ω → ℝ, gibbsMeanFamily μ A G τ = gibbsMean μ (A τ) (G τ) :=
    fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · have := e1 u τ hτ
    simp only [Pi.add_apply, Pi.mul_apply] at this
    change iteratedFDeriv ℝ 1 (gibbsMeanFamily μ A H) τ ![u] = _
    rw [this, mS u, hM H, hM (paramIteratedDeriv A ![u])]
    simp only [gibbsCovariance]
    ring
  · have := e2f v u τ hτ
    simp only [Pi.add_apply, Pi.mul_apply] at this
    change iteratedFDeriv ℝ 2 (gibbsMeanFamily μ A H) τ ![v, u] = _
    rw [this, mSS v u, mS u, mS v, mSa v u, hM H, hM (paramIteratedDeriv A ![u]),
      hM (paramIteratedDeriv A ![v])]
    simp only [gibbsCovariance, gibbsCumulantThree]
    ring
  · change iteratedFDeriv ℝ 3 (gibbsMeanFamily μ A H) τ ![w, v, u] = _
    rw [e3f, hQ.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, Pi.add_apply, Pi.mul_apply,
      (R1 _ (DSS u v)).2 τ hτ w, (R2 _ (DS u)).2 τ hτ w, (R2 _ (Da v)).2 τ hτ w,
      (R2 _ (DS v)).2 τ hτ w, R3.2 τ hτ w, (R2 _ (Da u)).2 τ hτ w, (R1 _ (DSa u v)).2 τ hτ w]
    rw [mSSS, mSS v u, mSS w u, mSS w v, mS u, mS v, mS w, mSa v u, mSa w u, mSa w v, mSSa, hM H,
      hM (paramIteratedDeriv A ![u]), hM (paramIteratedDeriv A ![v]),
      hM (paramIteratedDeriv A ![w])]
    simp only [gibbsCovariance, gibbsCumulantThree, gibbsCumulantFour]
    ring
end Main
end GibbsMeanDerivatives
theorem gibbsMeanDifferentiation_holds : GibbsMeanDifferentiation := by
  refine ⟨?_, ?_⟩
  · intro Ω _ μ _ k n B K G hB hG
    obtain ⟨c, f⟩ := GibbsMeanDerivatives.contDiffOn_integral_and_iteratedFDeriv μ hB K n ℝ G
      hG.aestronglyMeasurable hG.contDiffOn hG.norm_iteratedFDeriv_le
    exact ⟨c, fun τ hτ j hj v => (f τ hτ j hj v).2⟩
  · intro Ω _ μ _ k B K A H hB hμ hA hH
    exact GibbsMeanDerivatives.gibbsMean_iteratedFDeriv_three hB hμ hA hH
end YangMills.Construction.ColdStepAtMirrorFrames
end
