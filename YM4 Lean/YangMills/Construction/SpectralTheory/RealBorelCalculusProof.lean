import YangMills.Construction.SpectralTheory.RealBorelCalculus
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.SpectralTheory
namespace SpectralMeasure
variable {n : ℕ} [NeZero n] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
theorem inner_apply_symm (E : SpectralMeasure n H) (B : BorelSubset n) (x y : H) :
    ⟪x, E B y⟫_ℂ = ⟪E B x, y⟫_ℂ :=
  (E.isOrthProj B).symm x y
theorem apply_apply_eq_inter (E : SpectralMeasure n H) (B B' : BorelSubset n) (y : H) :
    E B (E B' y) = E ⟨B.1 ∩ B'.1, B.2.inter B'.2⟩ y := by
  have h := E.map_inter B B'
  exact (LinearMap.congr_fun h y).symm
theorem inner_apply_apply_eq (E : SpectralMeasure n H) (B B' : BorelSubset n) (x y : H) :
    ⟪E B x, E B' y⟫_ℂ = ⟪x, E ⟨B.1 ∩ B'.1, B.2.inter B'.2⟩ y⟫_ℂ := by
  rw [← E.inner_apply_symm, E.apply_apply_eq_inter]
theorem inner_apply_apply_self (E : SpectralMeasure n H) (B B' : BorelSubset n) (y : H) :
    ⟪E B y, E B' y⟫_ℂ =
      (((E.diagMeasure y).real (B.1 ∩ B'.1) : ℝ) : ℂ) := by
  rw [E.inner_apply_apply_eq]
  exact E.diag_eq_diagMeasure_real y ⟨B.1 ∩ B'.1, B.2.inter B'.2⟩
theorem apply_univ_vec (E : SpectralMeasure n H) (y : H) :
    E ⟨univ, MeasurableSet.univ⟩ y = y :=
  LinearMap.congr_fun E.map_univ y
theorem diagMeasure_apply_vec (E : SpectralMeasure n H) (B' : BorelSubset n) (y : H) :
    E.diagMeasure (E B' y) = (E.diagMeasure y).restrict B'.1 := by
  refine Measure.ext fun s hs => ?_
  rw [E.diagMeasure_apply _ ⟨s, hs⟩, Measure.restrict_apply hs,
    E.diagMeasure_apply y ⟨s ∩ B'.1, hs.inter B'.2⟩, E.apply_apply_eq_inter]
theorem norm_apply_le_norm (E : SpectralMeasure n H) (B : BorelSubset n) (y : H) :
    ‖E B y‖ ≤ ‖y‖ := by
  have h : ‖E B y‖ ^ 2 = (⟪y, E B y⟫_ℂ).re := by
    have := congrArg Complex.re (E.diag_eq_norm_sq y B)
    rw [Complex.ofReal_re] at this
    exact this.symm
  have h₁ : (⟪y, E B y⟫_ℂ).re ≤ ‖y‖ * ‖E B y‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm y (E B y))
  by_contra hlt
  have hlt := not_le.1 hlt
  nlinarith [norm_nonneg y, norm_nonneg (E B y)]
theorem inner_toLp_eq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} {f f' : X → ℝ}
    (hf : MemLp f 2 μ) (hf' : MemLp f' 2 μ) :
    ⟪hf.toLp f, hf'.toLp f'⟫_ℝ = ∫ x, f x * f' x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hf'.coeFn_toLp] with x h₁ h₂
  rw [h₁, h₂]
  simp [mul_comm]
theorem norm_sub_toLp_sq_eq {X : Type*} [MeasurableSpace X] {μ : Measure X} {f f' : X → ℝ}
    (hf : MemLp f 2 μ) (hf' : MemLp f' 2 μ) :
    ‖hf.toLp f - hf'.toLp f'‖ ^ 2 = ∫ x, (f x - f' x) ^ 2 ∂μ := by
  rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, inner_toLp_eq_integral]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq]
def simpleFn (s : Finset ℤ) (a : ℤ → ℝ) (B : ℤ → BorelSubset n) : (Fin n → ℝ) → ℝ :=
  fun x => ∑ k ∈ s, (B k).1.indicator (fun _ => a k) x
def simpleVec (E : SpectralMeasure n H) (s : Finset ℤ) (a : ℤ → ℝ) (B : ℤ → BorelSubset n)
    (y : H) : H :=
  ∑ k ∈ s, ((a k : ℝ) : ℂ) • E (B k) y
theorem memLp_simpleFn (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] (s : Finset ℤ) (a : ℤ → ℝ)
    (B : ℤ → BorelSubset n) : MemLp (simpleFn s a B) 2 μ :=
  memLp_finsetSum s fun k _ =>
    memLp_indicator_const 2 (B k).2 (a k) (Or.inr (measure_ne_top μ _))
theorem integral_simpleFn_mul_eq_inner (E : SpectralMeasure n H) (y : H) (s t : Finset ℤ)
    (a b : ℤ → ℝ) (B B' : ℤ → BorelSubset n) :
    ((∫ x, simpleFn s a B x * simpleFn t b B' x ∂(E.diagMeasure y) : ℝ) : ℂ) =
      ⟪E.simpleVec s a B y, E.simpleVec t b B' y⟫_ℂ := by
  have h₁ : (fun x => simpleFn s a B x * simpleFn t b B' x) = fun x =>
      ∑ k ∈ s, ∑ l ∈ t, ((B k).1 ∩ (B' l).1).indicator (fun _ => a k * b l) x := by
    funext x
    simp only [simpleFn, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hk : x ∈ (B k).1 <;> by_cases hl : x ∈ (B' l).1 <;> simp [indicator, hk, hl]
  have hint : ∀ k l, Integrable (((B k).1 ∩ (B' l).1).indicator fun _ => a k * b l)
      (E.diagMeasure y) := fun k l =>
    (integrable_const _).indicator ((B k).2.inter (B' l).2)
  rw [h₁, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  simp only [simpleVec, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    E.inner_apply_apply_self, Finset.mul_sum]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_indicator_const _ ((B k).2.inter (B' l).2)]
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.conj_ofReal]
  ring
def simpleGraph (E : SpectralMeasure n H) (y : H) : Set (Lp ℝ 2 (E.diagMeasure y) × H) :=
  {p | ∃ (s : Finset ℤ) (a : ℤ → ℝ) (B : ℤ → BorelSubset n),
    p = ((memLp_simpleFn (E.diagMeasure y) s a B).toLp _, E.simpleVec s a B y)}
theorem inner_of_mem_closure_simpleGraph (E : SpectralMeasure n H) (y : H)
    {p q : Lp ℝ 2 (E.diagMeasure y) × H} (hp : p ∈ closure (E.simpleGraph y))
    (hq : q ∈ closure (E.simpleGraph y)) :
    ((⟪p.1, q.1⟫_ℝ : ℝ) : ℂ) = ⟪p.2, q.2⟫_ℂ := by
  have hc : IsClosed {z : (Lp ℝ 2 (E.diagMeasure y) × H) × (Lp ℝ 2 (E.diagMeasure y) × H) |
      ((⟪z.1.1, z.2.1⟫_ℝ : ℝ) : ℂ) = ⟪z.1.2, z.2.2⟫_ℂ} :=
    isClosed_eq (Complex.continuous_ofReal.comp
        ((continuous_fst.comp continuous_fst).inner (continuous_fst.comp continuous_snd)))
      ((continuous_snd.comp continuous_fst).inner (continuous_snd.comp continuous_snd))
  have hsub : E.simpleGraph y ×ˢ E.simpleGraph y ⊆
      {z : (Lp ℝ 2 (E.diagMeasure y) × H) × (Lp ℝ 2 (E.diagMeasure y) × H) |
        ((⟪z.1.1, z.2.1⟫_ℝ : ℝ) : ℂ) = ⟪z.1.2, z.2.2⟫_ℂ} := by
    rintro ⟨_, _⟩ ⟨⟨s, a, B, rfl⟩, ⟨t, b, B', rfl⟩⟩
    change ((⟪_, _⟫_ℝ : ℝ) : ℂ) = ⟪_, _⟫_ℂ
    rw [inner_toLp_eq_integral, E.integral_simpleFn_mul_eq_inner]
  have hm := closure_minimal hsub hc
  rw [closure_prod_eq] at hm
  exact hm (Set.mk_mem_prod hp hq)
theorem norm_sq_of_mem_closure_simpleGraph (E : SpectralMeasure n H) (y : H)
    {p : Lp ℝ 2 (E.diagMeasure y) × H} (hp : p ∈ closure (E.simpleGraph y)) :
    ‖p.1‖ ^ 2 = ‖p.2‖ ^ 2 := by
  have h := E.inner_of_mem_closure_simpleGraph y hp hp
  have h' := congrArg Complex.re h
  rw [Complex.ofReal_re, real_inner_self_eq_norm_sq] at h'
  rw [h']
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _
theorem dist_of_mem_closure_simpleGraph (E : SpectralMeasure n H) (y : H)
    {p q : Lp ℝ 2 (E.diagMeasure y) × H} (hp : p ∈ closure (E.simpleGraph y))
    (hq : q ∈ closure (E.simpleGraph y)) : dist p.1 q.1 = dist p.2 q.2 := by
  have h := E.inner_of_mem_closure_simpleGraph y hp hq
  have h₁ : ⟪p.1, q.1⟫_ℝ = (⟪p.2, q.2⟫_ℂ).re := by
    rw [← h, Complex.ofReal_re]
  have h₂ : ‖p.1 - q.1‖ ^ 2 = ‖p.2 - q.2‖ ^ 2 := by
    rw [norm_sub_sq_real, @norm_sub_sq ℂ, E.norm_sq_of_mem_closure_simpleGraph y hp,
      E.norm_sq_of_mem_closure_simpleGraph y hq, h₁]
    rfl
  rw [dist_eq_norm, dist_eq_norm]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h₂
theorem exists_tendsto_of_mem_closure_simpleGraph (E : SpectralMeasure n H) (y : H)
    {u : ℕ → Lp ℝ 2 (E.diagMeasure y)} {v : ℕ → H} {w : Lp ℝ 2 (E.diagMeasure y)}
    (hm : ∀ m, (u m, v m) ∈ closure (E.simpleGraph y)) (hu : Tendsto u atTop (𝓝 w)) :
    ∃ z, Tendsto v atTop (𝓝 z) ∧ (w, z) ∈ closure (E.simpleGraph y) := by
  have hc : CauchySeq v := by
    have hcu := hu.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun m hm' l hl => ?_⟩
    have := E.dist_of_mem_closure_simpleGraph y (hm m) (hm l)
    simp only at this
    rw [← this]
    exact hN m hm' l hl
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨z, hz, ?_⟩
  have ht : Tendsto (fun m => (u m, v m)) atTop (𝓝 (w, z)) := hu.prodMk_nhds hz
  exact isClosed_closure.mem_of_tendsto ht (Eventually.of_forall hm)
def floorIndex (g : (Fin n → ℝ) → ℝ) (j : ℕ) (x : Fin n → ℝ) : ℤ := ⌊g x * 2 ^ j⌋
def dyadicLower (g : (Fin n → ℝ) → ℝ) (j : ℕ) (x : Fin n → ℝ) : ℝ :=
  dyadic j (floorIndex g j x)
theorem mem_dyadicLevelSet_iff (g : (Fin n → ℝ) → ℝ) (hg : Measurable g) (j : ℕ) (k : ℤ)
    (x : Fin n → ℝ) : x ∈ (dyadicLevelSet g hg j k).1 ↔ floorIndex g j x = k := by
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have h : (2 : ℝ) ^ (-(j : ℤ)) = (2 ^ j)⁻¹ := by rw [zpow_neg, zpow_natCast]
  change dyadic j k ≤ g x ∧ g x < dyadic j (k + 1) ↔ _
  simp only [dyadic, h, floorIndex, Int.floor_eq_iff]
  rw [mul_inv_le_iff₀ hp, lt_mul_inv_iff₀ hp]
  push_cast
  rfl
theorem abs_dyadicLower_sub_le (g : (Fin n → ℝ) → ℝ) (hg : Measurable g) (j : ℕ)
    (x : Fin n → ℝ) : |dyadicLower g j x - g x| ≤ (1 / 2 : ℝ) ^ j := by
  have h := (mem_dyadicLevelSet_iff g hg j (floorIndex g j x) x).2 rfl
  obtain ⟨h₁, h₂⟩ : dyadic j (floorIndex g j x) ≤ g x ∧
      g x < dyadic j (floorIndex g j x + 1) := h
  have h₃ : dyadic j (floorIndex g j x + 1) =
      dyadic j (floorIndex g j x) + (1 / 2 : ℝ) ^ j := by
    have h₄ : (2 : ℝ) ^ (-(j : ℤ)) = (1 / 2 : ℝ) ^ j := by
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    simp only [dyadic, h₄]
    push_cast
    ring
  rw [abs_le]
  unfold dyadicLower
  constructor <;> linarith
theorem measurable_dyadicLower {g : (Fin n → ℝ) → ℝ} (hg : Measurable g) (j : ℕ) :
    Measurable (dyadicLower g j) :=
  (Measurable.of_discrete (f := dyadic j)).comp (hg.mul_const _).floor
theorem simpleFn_dyadicLevelSet (g : (Fin n → ℝ) → ℝ) (hg : Measurable g) (j : ℕ)
    (s : Finset ℤ) (x : Fin n → ℝ) :
    simpleFn s (dyadic j) (dyadicLevelSet g hg j) x =
      if floorIndex g j x ∈ s then dyadicLower g j x else 0 := by
  have h : ∀ k, (dyadicLevelSet g hg j k).1.indicator (fun _ => dyadic j k) x =
      if k = floorIndex g j x then dyadic j k else 0 := fun k => by
    by_cases hk : k = floorIndex g j x
    · rw [if_pos hk, indicator_of_mem ((mem_dyadicLevelSet_iff g hg j k x).2 hk.symm)]
    · rw [if_neg hk,
        indicator_of_notMem fun hx => hk ((mem_dyadicLevelSet_iff g hg j k x).1 hx).symm]
  simp only [simpleFn, h]
  rw [Finset.sum_ite_eq']
  rfl
theorem mem_realDomain_iff (E : SpectralMeasure n H) {g : (Fin n → ℝ) → ℝ}
    (hg : Measurable g) (y : H) :
    y ∈ E.realDomain g ↔ MemLp g 2 (E.diagMeasure y) := by
  rw [memLp_two_iff_integrable_sq hg.aestronglyMeasurable]
  have h0 : 0 ≤ᵐ[E.diagMeasure y] fun x => g x ^ 2 := ae_of_all _ fun x => sq_nonneg _
  constructor
  · intro h
    exact ⟨(hg.pow_const 2).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal h0).2 h⟩
  · intro h
    exact (hasFiniteIntegral_iff_ofReal h0).1 h.2
theorem memLp_dyadicLower {μ : Measure (Fin n → ℝ)} [IsFiniteMeasure μ] {g : (Fin n → ℝ) → ℝ}
    (hg : Measurable g) (hm : MemLp g 2 μ) (j : ℕ) : MemLp (dyadicLower g j) 2 μ := by
  have hb : MemLp (fun x => dyadicLower g j x - g x) 2 μ :=
    MemLp.of_bound ((measurable_dyadicLower hg j).sub hg).aestronglyMeasurable ((1 / 2 : ℝ) ^ j)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        exact abs_dyadicLower_sub_le g hg j x)
  have h := hb.add hm
  have he : (fun x => dyadicLower g j x - g x) + g = dyadicLower g j := by
    funext x
    simp
  rwa [he] at h
theorem tendsto_toLp_of_integral_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : ℕ → X → ℝ} {f : X → ℝ}
    (hF : ∀ m, MemLp (F m) 2 μ) (hf : MemLp f 2 μ)
    (h : Tendsto (fun m => ∫ x, (F m x - f x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun m => (hF m).toLp (F m)) atTop (𝓝 (hf.toLp f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h₂ := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h₂
  refine h₂.congr fun m => ?_
  rw [Function.comp_apply, ← norm_sub_toLp_sq_eq (hF m) hf, Real.sqrt_sq (norm_nonneg _)]
theorem tendsto_integral_simpleFn_sub_sq {μ : Measure (Fin n → ℝ)} [IsFiniteMeasure μ]
    {g : (Fin n → ℝ) → ℝ} (hg : Measurable g) (j : ℕ) (hm : MemLp (dyadicLower g j) 2 μ) :
    Tendsto (fun ϰ : ℕ => ∫ x, (simpleFn (Finset.Icc (-(ϰ : ℤ)) (ϰ : ℤ)) (dyadic j)
      (dyadicLevelSet g hg j) x - dyadicLower g j x) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun (ϰ : ℕ) x => (simpleFn (Finset.Icc (-(ϰ : ℤ)) (ϰ : ℤ)) (dyadic j)
      (dyadicLevelSet g hg j) x - dyadicLower g j x) ^ 2)
    (f := fun _ => (0 : ℝ)) (fun x => dyadicLower g j x ^ 2)
    (fun ϰ => (((memLp_simpleFn μ _ _ _).aestronglyMeasurable).sub
      (measurable_dyadicLower hg j).aestronglyMeasurable).pow 2)
    ((memLp_two_iff_integrable_sq (measurable_dyadicLower hg j).aestronglyMeasurable).1 hm)
    (fun ϰ => ae_of_all _ fun x => by
      rw [simpleFn_dyadicLevelSet]
      split_ifs <;> simp [sq_nonneg])
    (ae_of_all _ fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (floorIndex g j x).natAbs] with ϰ hϰ
      have hi : floorIndex g j x ∈ Finset.Icc (-(ϰ : ℤ)) (ϰ : ℤ) := by
        rw [Finset.mem_Icc]
        omega
      rw [simpleFn_dyadicLevelSet, if_pos hi]
      simp)
  simpa using hlim
theorem tendsto_integral_dyadicLower_sub_sq {μ : Measure (Fin n → ℝ)} [IsFiniteMeasure μ]
    {g : (Fin n → ℝ) → ℝ} (hg : Measurable g) (hm : MemLp g 2 μ) :
    Tendsto (fun j : ℕ => ∫ x, (dyadicLower g j x - g x) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hb : Tendsto (fun j : ℕ => ((1 / 2 : ℝ) ^ j) ^ 2 * μ.real univ) atTop (𝓝 0) := by
    have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)
    simpa using (h₁.pow 2).mul_const (μ.real univ)
  refine squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg _) (fun j => ?_) hb
  have hi : Integrable (fun x => (dyadicLower g j x - g x) ^ 2) μ :=
    (memLp_two_iff_integrable_sq
      ((measurable_dyadicLower hg j).sub hg).aestronglyMeasurable).1
      ((memLp_dyadicLower hg hm j).sub hm)
  calc ∫ x, (dyadicLower g j x - g x) ^ 2 ∂μ ≤ ∫ _, ((1 / 2 : ℝ) ^ j) ^ 2 ∂μ :=
        integral_mono hi (integrable_const _) fun x => by
          have h₁ := abs_dyadicLower_sub_le g hg j x
          have h₂ := sq_le_sq' (abs_le.1 h₁).1 (abs_le.1 h₁).2
          exact h₂
    _ = ((1 / 2 : ℝ) ^ j) ^ 2 * μ.real univ := by
        rw [integral_const, smul_eq_mul, mul_comm]
theorem tendsto_of_mem_realDomain (E : SpectralMeasure n H)
    {g : (Fin n → ℝ) → ℝ} (hg : Measurable g) {y : H} (hy : y ∈ E.realDomain g) :
    (∀ j : ℕ, Tendsto (E.dyadicPartialSum g hg j y) atTop (𝓝 (E.dyadicSum g hg j y))) ∧
      Tendsto (fun j => E.dyadicSum g hg j y) atTop (𝓝 (E.realIntegralApply g hg y)) ∧
      ∀ hm : MemLp g 2 (E.diagMeasure y),
        (hm.toLp g, E.realIntegralApply g hg y) ∈ closure (E.simpleGraph y) := by
  have hm := (E.mem_realDomain_iff hg y).1 hy
  have hl := memLp_dyadicLower hg hm
  have hstep : ∀ (j ϰ : ℕ), ((memLp_simpleFn (E.diagMeasure y)
      (Finset.Icc (-(ϰ : ℤ)) (ϰ : ℤ)) (dyadic j) (dyadicLevelSet g hg j)).toLp _,
      E.dyadicPartialSum g hg j y ϰ) ∈ closure (E.simpleGraph y) := fun j ϰ =>
    subset_closure ⟨_, _, _, rfl⟩
  have hj : ∀ j : ℕ, ∃ z, Tendsto (E.dyadicPartialSum g hg j y) atTop (𝓝 z) ∧
      ((hl j).toLp _, z) ∈ closure (E.simpleGraph y) := fun j =>
    E.exists_tendsto_of_mem_closure_simpleGraph y (hstep j)
      (tendsto_toLp_of_integral_sq _ (hl j) (tendsto_integral_simpleFn_sub_sq hg j (hl j)))
  choose v hv hvm using hj
  have hsum : ∀ j, E.dyadicSum g hg j y = v j := fun j => (hv j).limUnder_eq
  obtain ⟨z, hz, hzm⟩ := E.exists_tendsto_of_mem_closure_simpleGraph y hvm
    (tendsto_toLp_of_integral_sq _ hm (tendsto_integral_dyadicLower_sub_sq hg hm))
  have hval : E.realIntegralApply g hg y = z := by
    have : (fun j => E.dyadicSum g hg j y) = v := funext hsum
    unfold realIntegralApply
    rw [this]
    exact hz.limUnder_eq
  refine ⟨fun j => by rw [hsum]; exact hv j, ?_, fun _ => by rw [hval]; exact hzm⟩
  rw [hval, funext hsum]
  exact hz
theorem vec_mem_closure_simpleGraph (E : SpectralMeasure n H) (y : H) :
    ((memLp_simpleFn (E.diagMeasure y) {0} (fun _ => 1)
      (fun _ => ⟨univ, MeasurableSet.univ⟩)).toLp _, y) ∈ closure (E.simpleGraph y) := by
  refine subset_closure ⟨{0}, fun _ => 1, fun _ => ⟨univ, MeasurableSet.univ⟩, ?_⟩
  simp [simpleVec, E.apply_univ_vec]
theorem inner_realIntegralApply (E : SpectralMeasure n H) {g : (Fin n → ℝ) → ℝ}
    (hg : Measurable g) {y : H} (hy : y ∈ E.realDomain g) :
    ⟪y, E.realIntegralApply g hg y⟫_ℂ = ((E.integral y g : ℝ) : ℂ) := by
  have hm := (E.mem_realDomain_iff hg y).1 hy
  have h := E.inner_of_mem_closure_simpleGraph y (E.vec_mem_closure_simpleGraph y)
    ((E.tendsto_of_mem_realDomain hg hy).2.2 hm)
  simp only at h
  rw [← h, inner_toLp_eq_integral]
  simp [simpleFn, SpectralMeasure.integral]
theorem dyadicPartialSum_add (E : SpectralMeasure n H) (g : (Fin n → ℝ) → ℝ)
    (hg : Measurable g) (j : ℕ) (x y : H) (ϰ : ℕ) :
    E.dyadicPartialSum g hg j (x + y) ϰ =
      E.dyadicPartialSum g hg j x ϰ + E.dyadicPartialSum g hg j y ϰ := by
  simp only [dyadicPartialSum, map_add, smul_add, Finset.sum_add_distrib]
theorem dyadicPartialSum_smul (E : SpectralMeasure n H) (g : (Fin n → ℝ) → ℝ)
    (hg : Measurable g) (j : ℕ) (c : ℂ) (y : H) (ϰ : ℕ) :
    E.dyadicPartialSum g hg j (c • y) ϰ = c • E.dyadicPartialSum g hg j y ϰ := by
  simp only [dyadicPartialSum, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
theorem norm_apply_add_sq_le (E : SpectralMeasure n H) (B : BorelSubset n) (x y : H) :
    ‖E B (y + x)‖ ^ 2 ≤ 2 * ‖E B y‖ ^ 2 + 2 * ‖E B x‖ ^ 2 := by
  rw [map_add]
  have h₁ := norm_add_le (E B y) (E B x)
  have h₂ : ‖E B y + E B x‖ ^ 2 ≤ (‖E B y‖ + ‖E B x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  nlinarith [sq_nonneg (‖E B y‖ - ‖E B x‖)]
theorem diagMeasure_add_le (E : SpectralMeasure n H) (x y : H) :
    E.diagMeasure (y + x) ≤ (2 : ℝ≥0∞) • E.diagMeasure y + (2 : ℝ≥0∞) • E.diagMeasure x := by
  rw [Measure.le_iff]
  intro s hs
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [E.diagMeasure_apply _ ⟨s, hs⟩, E.diagMeasure_apply y ⟨s, hs⟩,
    E.diagMeasure_apply x ⟨s, hs⟩]
  calc ENNReal.ofReal (‖E ⟨s, hs⟩ (y + x)‖ ^ 2)
      ≤ ENNReal.ofReal (2 * ‖E ⟨s, hs⟩ y‖ ^ 2 + 2 * ‖E ⟨s, hs⟩ x‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (E.norm_apply_add_sq_le _ x y)
    _ = 2 * ENNReal.ofReal (‖E ⟨s, hs⟩ y‖ ^ 2) + 2 * ENNReal.ofReal (‖E ⟨s, hs⟩ x‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        simp
theorem diagMeasure_smul (E : SpectralMeasure n H) (c : ℂ) (y : H) :
    E.diagMeasure (c • y) = ENNReal.ofReal (‖c‖ ^ 2) • E.diagMeasure y := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.smul_apply, E.diagMeasure_apply _ ⟨s, hs⟩, E.diagMeasure_apply y ⟨s, hs⟩,
    map_smul, norm_smul, mul_pow, ENNReal.ofReal_mul (by positivity), smul_eq_mul]
theorem add_mem_realDomain (E : SpectralMeasure n H) {g : (Fin n → ℝ) → ℝ} {x y : H}
    (hx : x ∈ E.realDomain g) (hy : y ∈ E.realDomain g) :
    y + x ∈ E.realDomain g := by
  change ∫⁻ z, ENNReal.ofReal (g z ^ 2) ∂(E.diagMeasure (y + x)) < ⊤
  have hx' : ∫⁻ z, ENNReal.ofReal (g z ^ 2) ∂(E.diagMeasure x) < ⊤ := hx
  have hy' : ∫⁻ z, ENNReal.ofReal (g z ^ 2) ∂(E.diagMeasure y) < ⊤ := hy
  refine lt_of_le_of_lt (lintegral_mono' (E.diagMeasure_add_le x y) le_rfl) ?_
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hy', ENNReal.mul_lt_top (by simp) hx'⟩
theorem smul_mem_realDomain (E : SpectralMeasure n H) {g : (Fin n → ℝ) → ℝ} (c : ℂ)
    {y : H} (hy : y ∈ E.realDomain g) : c • y ∈ E.realDomain g := by
  change ∫⁻ z, ENNReal.ofReal (g z ^ 2) ∂(E.diagMeasure (c • y)) < ⊤
  have hy' : ∫⁻ z, ENNReal.ofReal (g z ^ 2) ∂(E.diagMeasure y) < ⊤ := hy
  rw [E.diagMeasure_smul, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hy'
theorem realIntegralApply_add (E : SpectralMeasure n H) {g : (Fin n → ℝ) → ℝ}
    (hg : Measurable g) {x y : H} (hx : x ∈ E.realDomain g) (hy : y ∈ E.realDomain g) :
    E.realIntegralApply g hg (x + y) = E.realIntegralApply g hg x + E.realIntegralApply g hg y := by
  obtain ⟨hx₁, hx₂, -⟩ := E.tendsto_of_mem_realDomain hg hx
  obtain ⟨hy₁, hy₂, -⟩ := E.tendsto_of_mem_realDomain hg hy
  obtain ⟨h₁, h₂, -⟩ := E.tendsto_of_mem_realDomain hg (E.add_mem_realDomain hy hx)
  have hs : ∀ j, E.dyadicSum g hg j (x + y) = E.dyadicSum g hg j x + E.dyadicSum g hg j y :=
    fun j => tendsto_nhds_unique (h₁ j)
      (((hx₁ j).add (hy₁ j)).congr fun ϰ => (E.dyadicPartialSum_add g hg j x y ϰ).symm)
  exact tendsto_nhds_unique h₂ ((hx₂.add hy₂).congr fun j => (hs j).symm)
theorem realIntegralApply_smul (E : SpectralMeasure n H) {g : (Fin n → ℝ) → ℝ}
    (hg : Measurable g) (c : ℂ) {y : H} (hy : y ∈ E.realDomain g) :
    E.realIntegralApply g hg (c • y) = c • E.realIntegralApply g hg y := by
  obtain ⟨hy₁, hy₂, -⟩ := E.tendsto_of_mem_realDomain hg hy
  obtain ⟨h₁, h₂, -⟩ := E.tendsto_of_mem_realDomain hg (E.smul_mem_realDomain c hy)
  have hs : ∀ j, E.dyadicSum g hg j (c • y) = c • E.dyadicSum g hg j y := fun j =>
    tendsto_nhds_unique (h₁ j)
      (((hy₁ j).const_smul c).congr fun ϰ => (E.dyadicPartialSum_smul g hg j c y ϰ).symm)
  exact tendsto_nhds_unique h₂ ((hy₂.const_smul c).congr fun j => (hs j).symm)
theorem isNull_iff_diagMeasure (E : SpectralMeasure n H) (B : BorelSubset n) :
    E.IsNull B ↔ ∀ y, E.diagMeasure y B.1 = 0 := by
  constructor
  · intro h y
    have h₀ : E B = 0 := h
    rw [E.diagMeasure_apply, h₀]
    simp
  · intro h
    refine LinearMap.ext fun y => ?_
    have h₁ := h y
    rw [E.diagMeasure_apply, ENNReal.ofReal_eq_zero] at h₁
    have h₂ : ‖E B y‖ = 0 := by
      nlinarith [norm_nonneg (E B y)]
    simpa using h₂
end SpectralMeasure
open SpectralMeasure in
theorem realBorelCalculus_holds : RealBorelCalculus := by
  intro H _ _ _ n _ E g hg
  exact ⟨fun x hx y hy c => ⟨E.realIntegralApply_add hg hx hy, E.realIntegralApply_smul hg c hy⟩,
    fun y hy => E.inner_realIntegralApply hg hy⟩
end YangMills.Construction.SpectralTheory
