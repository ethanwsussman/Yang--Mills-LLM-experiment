import YangMills.Construction.ReflectionPositivity.ExponentialKernelPositivity
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.ExpSumProductKernel
variable {X Γ : Type} [MeasurableSpace X] [Fintype Γ]
private def IsBoundedFn {Y : Type} (u : Y → ℂ) : Prop := ∃ C : ℝ, ∀ y, ‖u y‖ ≤ C
private theorem measurable_sum_mul {t : Γ → X → ℝ} (hm : ∀ γ, Measurable (t γ)) :
    Measurable fun p : X × X => ∑ γ, t γ p.1 * t γ p.2 :=
  Finset.measurable_fun_sum _ fun γ _ =>
    ((hm γ).comp measurable_fst).mul ((hm γ).comp measurable_snd)
omit [MeasurableSpace X] in
private theorem abs_sum_mul_bounded {t : Γ → X → ℝ} (hb : ∀ γ, ∃ C : ℝ, ∀ x, |t γ x| ≤ C) :
    ∃ M : ℝ, ∀ p : X × X, |∑ γ, t γ p.1 * t γ p.2| ≤ M := by
  choose C hC using hb
  refine ⟨∑ γ, C γ * C γ, fun p =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun γ _ => ?_)⟩
  rw [abs_mul]
  exact mul_le_mul (hC γ _) (hC γ _) (abs_nonneg _) ((abs_nonneg _).trans (hC γ p.1))
omit [MeasurableSpace X] in
private theorem norm_pairIntegrand_le {g h : X → ℂ} {K : X × X → ℝ} {a b c : ℝ}
    (ha : ∀ x, ‖g x‖ ≤ a) (hb : ∀ x, ‖h x‖ ≤ b) (hc : ∀ p, |K p| ≤ c) (p : X × X) :
    ‖starRingEnd ℂ (g p.2) * h p.1 * (K p : ℂ)‖ ≤ a * b * c := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha p.1)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb p.1)
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (mul_le_mul (ha _) (hb _) (norm_nonneg _) ha0) (hc p) (abs_nonneg _)
    (mul_nonneg ha0 hb0)
private theorem integrable_pairIntegrand {ν : Measure X} [IsProbabilityMeasure ν] {g h : X → ℂ}
    (hg : Measurable g) (hgb : IsBoundedFn g) (hh : Measurable h) (hhb : IsBoundedFn h)
    {K : X × X → ℝ} (hK : Measurable K) (hKb : ∃ C : ℝ, ∀ p, |K p| ≤ C) :
    Integrable (fun p : X × X => starRingEnd ℂ (g p.2) * h p.1 * (K p : ℂ)) (ν.prod ν) := by
  obtain ⟨a, ha⟩ := hgb
  obtain ⟨b, hb⟩ := hhb
  obtain ⟨c, hc⟩ := hKb
  refine Integrable.of_bound ?_ (a * b * c) (Eventually.of_forall (norm_pairIntegrand_le ha hb hc))
  apply Measurable.aestronglyMeasurable
  have h1 : Measurable fun p : X × X => starRingEnd ℂ (g p.2) :=
    Complex.continuous_conj.measurable.comp (hg.comp measurable_snd)
  have h2 : Measurable fun p : X × X => h p.1 := hh.comp measurable_fst
  have h3 : Measurable fun p : X × X => (K p : ℂ) := Complex.measurable_ofReal.comp hK
  exact (h1.mul h2).mul h3
private theorem integrable_kernelForm_integrand {ν : Measure X} [IsProbabilityMeasure ν]
    {t : Γ → X → ℝ} (hm : ∀ γ, Measurable (t γ)) (hb : ∀ γ, ∃ C : ℝ, ∀ x, |t γ x| ≤ C)
    {g h : X → ℂ} (hg : Measurable g) (hgb : IsBoundedFn g) (hh : Measurable h)
    (hhb : IsBoundedFn h) :
    Integrable (fun p : X × X => starRingEnd ℂ (g p.2) * h p.1 *
      (Real.exp (∑ γ, t γ p.1 * t γ p.2) : ℂ)) (ν.prod ν) := by
  obtain ⟨M, hM⟩ := abs_sum_mul_bounded hb
  refine integrable_pairIntegrand hg hgb hh hhb (Real.measurable_exp.comp
    (measurable_sum_mul hm)) ⟨Real.exp M, fun p => ?_⟩
  simp only [Real.abs_exp]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hM p))
private theorem kernelForm_pow_nonneg {ν : Measure X} [IsProbabilityMeasure ν] {t : Γ → X → ℝ}
    (hm : ∀ γ, Measurable (t γ)) (hb : ∀ γ, ∃ C : ℝ, ∀ x, |t γ x| ≤ C) {g : X → ℂ}
    (hg : Measurable g) (hgb : IsBoundedFn g) (n : ℕ) :
    0 ≤ ∫ p : X × X, starRingEnd ℂ (g p.2) * g p.1 *
      ((∑ γ, t γ p.1 * t γ p.2 : ℝ) : ℂ) ^ n ∂ν.prod ν := by
  let T : (Fin n → Γ) → X → ℝ := fun c x => ∏ i, t (c i) x
  have hTm : ∀ c, Measurable (T c) := fun c =>
    Finset.measurable_fun_prod _ fun i _ => hm (c i)
  have hTb : ∀ c, ∃ C : ℝ, ∀ x, |T c x| ≤ C := by
    intro c
    choose C hC using hb
    refine ⟨∏ i, C (c i), fun x => ?_⟩
    simp only [T, Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hC _ _)
  have hJ : ∀ c, Integrable (fun x => g x * (T c x : ℂ)) ν := by
    intro c
    obtain ⟨a, ha⟩ := hgb
    obtain ⟨b, hb'⟩ := hTb c
    refine Integrable.of_bound (hg.mul (Complex.measurable_ofReal.comp (hTm c))).aestronglyMeasurable
      (a * b) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (ha x) (hb' x) (abs_nonneg _) ((norm_nonneg _).trans (ha x))
  have hJc : ∀ c, Integrable (fun x => starRingEnd ℂ (g x * (T c x : ℂ))) ν := fun c =>
    (hJ c).mono (Complex.continuous_conj.measurable.comp
      (hg.mul (Complex.measurable_ofReal.comp (hTm c)))).aestronglyMeasurable
      (Eventually.of_forall fun x => (RCLike.norm_conj _).le)
  have expand : ∀ p : X × X, starRingEnd ℂ (g p.2) * g p.1 *
      ((∑ γ, t γ p.1 * t γ p.2 : ℝ) : ℂ) ^ n =
      ∑ c : Fin n → Γ, (g p.1 * (T c p.1 : ℂ)) *
        starRingEnd ℂ (g p.2 * (T c p.2 : ℂ)) := by
    intro p
    rw [← Complex.ofReal_pow, Fintype.sum_pow, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [T, Finset.prod_mul_distrib, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ fun c _ => (hJ c).mul_prod (hJc c)]
  refine Finset.sum_nonneg fun c _ => ?_
  rw [integral_prod_mul (fun x => g x * (T c x : ℂ))
    (fun x => starRingEnd ℂ (g x * (T c x : ℂ))), integral_conj]
  exact mul_star_self_nonneg _
private theorem kernelForm_self_nonneg {ν : Measure X} [IsProbabilityMeasure ν] {t : Γ → X → ℝ}
    (hm : ∀ γ, Measurable (t γ)) (hb : ∀ γ, ∃ C : ℝ, ∀ x, |t γ x| ≤ C) {g : X → ℂ}
    (hg : Measurable g) (hgb : IsBoundedFn g) : 0 ≤ kernelForm ν t g g := by
  have hsm := measurable_sum_mul hm
  obtain ⟨M, hM⟩ := abs_sum_mul_bounded hb
  let s : X × X → ℝ := fun p => ∑ γ, t γ p.1 * t γ p.2
  let S : ℕ → X × X → ℝ := fun N p => ∑ n ∈ Finset.range N, s p ^ n / (n.factorial : ℝ)
  have hpow : ∀ n, Measurable fun p => s p ^ n := fun n => hsm.pow_const n
  have hpowb : ∀ n, ∃ C : ℝ, ∀ p, |s p ^ n| ≤ C := fun n => ⟨M ^ n, fun p => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM p) n⟩
  have hSm : ∀ N, Measurable (S N) := fun N =>
    Finset.measurable_fun_sum _ fun n _ => (hpow n).div_const _
  have hSb : ∀ N p, |S N p| ≤ Real.exp M := by
    intro N p
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ n ∈ Finset.range N, |s p ^ n / (n.factorial : ℝ)| =
        |s p| ^ n / (n.factorial : ℝ) := fun n _ => by
      rw [abs_div, abs_pow, Nat.abs_cast]
    rw [Finset.sum_congr rfl this]
    exact (Real.sum_le_exp_of_nonneg (abs_nonneg _) N).trans (Real.exp_le_exp.mpr (hM p))
  have hlim : ∀ p, Tendsto (fun N => S N p) atTop (𝓝 (Real.exp (s p))) := by
    intro p
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (s p)).tendsto_sum_nat
  have hterm : ∀ N, 0 ≤ ∫ p : X × X, starRingEnd ℂ (g p.2) * g p.1 * (S N p : ℂ) ∂ν.prod ν := by
    intro N
    have expand : ∀ p : X × X, starRingEnd ℂ (g p.2) * g p.1 * (S N p : ℂ) =
        ∑ n ∈ Finset.range N, (((n.factorial : ℝ)⁻¹ : ℝ) : ℂ) *
          (starRingEnd ℂ (g p.2) * g p.1 * ((s p : ℝ) : ℂ) ^ n) := by
      intro p
      simp only [S, Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast
      ring
    simp_rw [expand]
    rw [integral_finsetSum _ fun n _ => ?_]
    · refine Finset.sum_nonneg fun n _ => ?_
      rw [integral_const_mul]
      exact mul_nonneg (Complex.zero_le_real.mpr (by positivity))
        (kernelForm_pow_nonneg hm hb hg hgb n)
    · refine Integrable.const_mul ?_ _
      have := integrable_pairIntegrand (ν := ν) hg hgb hg hgb (hpow n) (hpowb n)
      simpa only [Complex.ofReal_pow] using this
  obtain ⟨a, ha⟩ := id hgb
  have hconv : Tendsto (fun N => ∫ p : X × X, starRingEnd ℂ (g p.2) * g p.1 * (S N p : ℂ) ∂ν.prod ν)
      atTop (𝓝 (kernelForm ν t g g)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => a * a * Real.exp M)
      (fun N => (integrable_pairIntegrand hg hgb hg hgb (hSm N)
        ⟨Real.exp M, hSb N⟩).aestronglyMeasurable) (integrable_const _)
      (fun N => Eventually.of_forall (norm_pairIntegrand_le ha ha (hSb N))) ?_
    refine Eventually.of_forall fun p => ?_
    exact ((Complex.continuous_ofReal.tendsto _).comp (hlim p)).const_mul _
  exact ge_of_tendsto' hconv hterm
private theorem conj_kernelForm (ν : Measure X) [IsProbabilityMeasure ν] (t : Γ → X → ℝ)
    (g h : X → ℂ) : starRingEnd ℂ (kernelForm ν t h g) = kernelForm ν t g h := by
  unfold kernelForm
  rw [← integral_conj, ← integral_prod_swap]
  refine congrArg (fun F : X × X → ℂ => ∫ p, F p ∂ν.prod ν) (funext fun p => ?_)
  have : ∑ γ, t γ p.2 * t γ p.1 = ∑ γ, t γ p.1 * t γ p.2 :=
    Finset.sum_congr rfl fun γ _ => mul_comm _ _
  simp only [Prod.fst_swap, Prod.snd_swap, map_mul, Complex.conj_conj, Complex.conj_ofReal, this]
  ring
private def boundedMeasurableFns (X : Type) [MeasurableSpace X] : Submodule ℂ (X → ℂ) where
  carrier := {g | Measurable g ∧ IsBoundedFn g}
  add_mem' := by
    rintro g h ⟨hg, a, ha⟩ ⟨hh, b, hb⟩
    exact ⟨hg.add hh, a + b, fun x => (norm_add_le _ _).trans (add_le_add (ha x) (hb x))⟩
  zero_mem' := ⟨measurable_const, 0, fun _ => by simp⟩
  smul_mem' := by
    rintro r g ⟨hg, a, ha⟩
    refine ⟨hg.const_smul r, ‖r‖ * a, fun x => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (ha x) (norm_nonneg _)
@[reducible] private def preInnerCore (ν : Measure X) [IsProbabilityMeasure ν] (t : Γ → X → ℝ)
    (hm : ∀ γ, Measurable (t γ)) (hb : ∀ γ, ∃ C : ℝ, ∀ x, |t γ x| ≤ C) :
    PreInnerProductSpace.Core ℂ (boundedMeasurableFns X) where
  inner g h := kernelForm ν t g.1 h.1
  conj_inner_symm g h := conj_kernelForm ν t g.1 h.1
  re_inner_nonneg g := (Complex.le_def.mp (kernelForm_self_nonneg hm hb g.2.1 g.2.2)).1
  add_left g g' h := by
    change kernelForm ν t (g.1 + g'.1) h.1 = kernelForm ν t g.1 h.1 + kernelForm ν t g'.1 h.1
    unfold kernelForm
    rw [← integral_add (integrable_kernelForm_integrand hm hb g.2.1 g.2.2 h.2.1 h.2.2)
      (integrable_kernelForm_integrand hm hb g'.2.1 g'.2.2 h.2.1 h.2.2)]
    refine congrArg (fun F : X × X → ℂ => ∫ p, F p ∂ν.prod ν) (funext fun p => ?_)
    simp only [Pi.add_apply, map_add]
    ring
  smul_left g h r := by
    change kernelForm ν t (r • g.1) h.1 = starRingEnd ℂ r * kernelForm ν t g.1 h.1
    unfold kernelForm
    rw [← integral_const_mul]
    refine congrArg (fun F : X × X → ℂ => ∫ p, F p ∂ν.prod ν) (funext fun p => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
theorem positivityStatement_holds : PositivityStatement := by
  intro X Γ _ _ ν _ t hm hb f f' hf hfb hf' hf'b
  refine ⟨kernelForm_self_nonneg hm hb hf hfb, ?_⟩
  have key := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ (boundedMeasurableFns X) _ _ _
    (preInnerCore ν t hm hb) ⟨f', hf', hf'b⟩ ⟨f, hf, hfb⟩
  change ‖kernelForm ν t f' f‖ * ‖kernelForm ν t f f'‖ ≤
    (kernelForm ν t f' f').re * (kernelForm ν t f f).re at key
  rw [← conj_kernelForm ν t f f', RCLike.norm_conj] at key
  rwa [sq]
end YangMills.Construction.ReflectionPositivity.ExpSumProductKernel
end
