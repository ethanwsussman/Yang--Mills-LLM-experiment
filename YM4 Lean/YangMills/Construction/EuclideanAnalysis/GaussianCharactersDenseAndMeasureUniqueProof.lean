import YangMills.Construction.EuclideanAnalysis.GaussianCharactersDenseAndMeasureUnique
import YangMills.Construction.EuclideanAnalysis.GaussianWeightsAndTheirTransforms
import YangMills.Construction.FreeKernel.LineIntegrationByPartsProof
import Mathlib
open Filter Topology MeasureTheory OnePoint
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis.Strip.ModulatedDensity
theorem unitStripPow_natCast (ξ : Set.Icc (0 : ℝ) 1) (k : ℕ) :
    unitStripPow ξ k = (ξ : ℝ) ^ k := by
  unfold unitStripPow RealPower.rpowPos
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [if_neg hk']
    by_cases hξ : 0 < (ξ : ℝ)
    · rw [if_pos hξ, ← Real.rpow_natCast, Real.rpow_def_of_pos hξ, mul_comm]
    · have h0 : (ξ : ℝ) = 0 := le_antisymm (not_lt.1 hξ) ξ.2.1
      rw [if_neg hξ, h0, zero_pow hk]
theorem continuous_unitStripPow (k : ℕ) :
    Continuous fun ξ : Set.Icc (0 : ℝ) 1 => unitStripPow ξ k := by
  simp_rw [unitStripPow_natCast]
  fun_prop
theorem norm_unitStripPow_le (ξ : Set.Icc (0 : ℝ) 1) (k : ℕ) : ‖(unitStripPow ξ k : ℂ)‖ ≤ 1 := by
  rw [unitStripPow_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg ξ.2.1 k)]
  exact pow_le_one₀ ξ.2.1 ξ.2.2
theorem norm_exp_I_mul_real_mul (s q : ℝ) : ‖Complex.exp (Complex.I * s * q)‖ = 1 := by apply _root_.YangMills.Construction.FreeKernel.LineIntegration.norm_character <;> assumption
theorem gaussianModulatedMonomial_apply (k : ℕ) (s σ : ℝ) (x : UnitStrip) :
    gaussianModulatedMonomial k s σ x =
      ((x.1 : ℝ) : ℂ) ^ k * Complex.exp (Complex.I * s * x.2 - σ * (x.2 : ℂ) ^ 2 / 2) := by
  simp [gaussianModulatedMonomial, unitStripPow_natCast]
theorem continuous_gaussianModulatedMonomial (k : ℕ) (s σ : ℝ) :
    Continuous (gaussianModulatedMonomial k s σ) := by
  have : gaussianModulatedMonomial k s σ = fun x : UnitStrip =>
      ((x.1 : ℝ) : ℂ) ^ k * Complex.exp (Complex.I * s * x.2 - σ * (x.2 : ℂ) ^ 2 / 2) :=
    funext (gaussianModulatedMonomial_apply k s σ)
  rw [this]
  fun_prop
theorem norm_gaussianModulatedMonomial_le (k : ℕ) (s σ : ℝ) (x : UnitStrip) :
    ‖gaussianModulatedMonomial k s σ x‖ ≤ Real.exp (-(σ / 2 * x.2 ^ 2)) := by
  have h1 : Complex.I * s * x.2 - σ * (x.2 : ℂ) ^ 2 / 2 =
      ((-(σ / 2 * x.2 ^ 2) : ℝ) : ℂ) + ((s * x.2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  unfold gaussianModulatedMonomial
  rw [norm_mul, h1, Complex.exp_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_exp]
  simp only [Complex.ofReal_re]
  calc _ ≤ 1 * Real.exp (-(σ / 2 * x.2 ^ 2)) :=
        mul_le_mul_of_nonneg_right (norm_unitStripPow_le _ _) (Real.exp_pos _).le
    _ = _ := one_mul _
theorem tendsto_zero_of_forall_abs_snd_ge (g : UnitStrip → ℂ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : UnitStrip, R ≤ |x.2| → ‖g x‖ < ε) :
    Tendsto g (coclosedCompact UnitStrip) (𝓝 0) := by
  rw [coclosedCompact_eq_cocompact, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR⟩ := h ε hε
  have hK : IsCompact ((Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ Set.Icc (-|R|) |R|) :=
    isCompact_univ.prod isCompact_Icc
  refine Filter.mem_cocompact.2 ⟨_, hK, fun x hx => ?_⟩
  have hq : R ≤ |x.2| := by
    by_contra hc
    have hlt : |x.2| < R := not_le.1 hc
    have hle : |x.2| ≤ |R| := hlt.le.trans (le_abs_self R)
    exact hx ⟨Set.mem_univ _, abs_le.1 hle⟩
  simpa using hR x hq
theorem tendsto_zero_of_mem_stripZeroAtInfty (f : UnitStrip → ℂ) (hf : f ∈ stripZeroAtInfty) :
    Tendsto f (coclosedCompact UnitStrip) (𝓝 0) := by
  refine tendsto_zero_of_forall_abs_snd_ge f fun ε hε => ?_
  obtain ⟨R, hR⟩ := (hf.2.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  refine ⟨R, fun x hx => ?_⟩
  have h1 : ‖f x‖ₑ ≤ ⨆ x : UnitStrip, ⨆ _ : R ≤ |x.2|, ‖f x‖ₑ :=
    le_iSup₂_of_le x hx le_rfl
  have h2 : ENNReal.ofReal ‖f x‖ < ENNReal.ofReal ε := by
    rw [ofReal_norm]
    exact h1.trans_lt hR
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 h2
theorem tendsto_gaussianModulatedMonomial (k : ℕ) (s : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (gaussianModulatedMonomial k s σ) (coclosedCompact UnitStrip) (𝓝 0) := by
  refine tendsto_zero_of_forall_abs_snd_ge _ fun ε hε => ?_
  have hlim : Tendsto (fun R : ℝ => Real.exp (-(σ / 2 * R ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop (by positivity) (tendsto_pow_atTop two_ne_zero))
  obtain ⟨R, hR, hR0⟩ :=
    ((hlim.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop (0 : ℝ))).exists
  refine ⟨R, fun x hx => lt_of_le_of_lt ((norm_gaussianModulatedMonomial_le k s σ x).trans ?_) hR⟩
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have h2 : R ^ 2 ≤ x.2 ^ 2 := by
    have := pow_le_pow_left₀ hR0 hx 2
    rwa [sq_abs] at this
  exact mul_le_mul_of_nonneg_left h2 (by positivity)
theorem exists_onePoint_extension (g : UnitStrip → ℂ) (hc : Continuous g)
    (h : Tendsto g (coclosedCompact UnitStrip) (𝓝 0)) :
    ∃ G : C(OnePoint UnitStrip, ℂ), G ∞ = 0 ∧ ∀ x : UnitStrip, G (x : OnePoint UnitStrip) = g x :=
  ⟨continuousMapMk ⟨g, hc⟩ 0 h, rfl, fun _ => rfl⟩
theorem gaussianModulatedMonomial_mul (k k' : ℕ) (s s' σ σ' : ℝ) :
    gaussianModulatedMonomial k s σ * gaussianModulatedMonomial k' s' σ' =
      gaussianModulatedMonomial (k + k') (s + s') (σ + σ') := by
  funext x
  simp only [Pi.mul_apply, gaussianModulatedMonomial_apply]
  rw [mul_mul_mul_comm, ← Complex.exp_add, pow_add]
  congr 2
  push_cast
  ring
theorem mul_mem_gaussianModulatedSpan {f g : UnitStrip → ℂ} (hf : f ∈ gaussianModulatedSpan)
    (hg : g ∈ gaussianModulatedSpan) : f * g ∈ gaussianModulatedSpan := by
  unfold gaussianModulatedSpan at hf hg ⊢
  induction hf using Submodule.span_induction with
  | mem f hf =>
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨k, s, σ, hσ, rfl⟩ := hf
      obtain ⟨k', s', σ', hσ', rfl⟩ := hg
      rw [gaussianModulatedMonomial_mul]
      exact Submodule.subset_span ⟨_, _, _, add_pos hσ hσ', rfl⟩
    | zero => simp
    | add a b _ _ iha ihb => rw [mul_add]; exact add_mem iha ihb
    | smul c a _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih
  | zero => simp
  | add a b _ _ iha ihb => rw [add_mul]; exact add_mem iha ihb
  | smul c a _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ih
theorem star_gaussianModulatedMonomial (k : ℕ) (s σ : ℝ) :
    star (gaussianModulatedMonomial k s σ) = gaussianModulatedMonomial k (-s) σ := by
  funext x
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  simp only [Pi.star_apply, gaussianModulatedMonomial_apply, Complex.star_def, map_mul, map_pow,
    Complex.conj_ofReal, ← Complex.exp_conj, map_sub, map_div₀, Complex.conj_I, h2]
  congr 2
  push_cast
  ring
theorem star_mem_gaussianModulatedSpan {f : UnitStrip → ℂ} (hf : f ∈ gaussianModulatedSpan) :
    star f ∈ gaussianModulatedSpan := by
  unfold gaussianModulatedSpan at hf ⊢
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, s, σ, hσ, rfl⟩ := hf
    rw [star_gaussianModulatedMonomial]
    exact Submodule.subset_span ⟨_, _, _, hσ, rfl⟩
  | zero => simp
  | add a b _ _ iha ihb => rw [star_add]; exact add_mem iha ihb
  | smul c a _ ih => rw [star_smul]; exact Submodule.smul_mem _ _ ih
def offsetAtInfty (G : C(OnePoint UnitStrip, ℂ)) : UnitStrip → ℂ :=
  fun x => G (x : OnePoint UnitStrip) - G ∞
def onePointModulatedAlgebra : StarSubalgebra ℂ C(OnePoint UnitStrip, ℂ) where
  carrier := {G | offsetAtInfty G ∈ gaussianModulatedSpan}
  mul_mem' := by
    intro G H hG hH
    change offsetAtInfty G ∈ gaussianModulatedSpan at hG
    change offsetAtInfty H ∈ gaussianModulatedSpan at hH
    change offsetAtInfty (G * H) ∈ gaussianModulatedSpan
    have h1 := Submodule.smul_mem gaussianModulatedSpan (G ∞) hH
    have h2 := Submodule.smul_mem gaussianModulatedSpan (H ∞) hG
    have := add_mem (add_mem (mul_mem_gaussianModulatedSpan hG hH) h1) h2
    convert this using 1
    funext x
    simp only [offsetAtInfty, ContinuousMap.mul_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  add_mem' := by
    intro G H hG hH
    change offsetAtInfty G ∈ gaussianModulatedSpan at hG
    change offsetAtInfty H ∈ gaussianModulatedSpan at hH
    change offsetAtInfty (G + H) ∈ gaussianModulatedSpan
    have := add_mem hG hH
    convert this using 1
    funext x
    simp only [offsetAtInfty, ContinuousMap.add_apply, Pi.add_apply]
    ring
  algebraMap_mem' := by
    intro c
    change offsetAtInfty (algebraMap ℂ C(OnePoint UnitStrip, ℂ) c) ∈ gaussianModulatedSpan
    have hconst : ∀ y : OnePoint UnitStrip,
        (algebraMap ℂ C(OnePoint UnitStrip, ℂ) c) y = c := fun y => by
      simp [Algebra.algebraMap_eq_smul_one]
    have : offsetAtInfty (algebraMap ℂ C(OnePoint UnitStrip, ℂ) c) = 0 := by
      funext x
      simp only [offsetAtInfty, hconst, sub_self, Pi.zero_apply]
    rw [this]
    exact zero_mem _
  star_mem' := by
    intro G hG
    change offsetAtInfty G ∈ gaussianModulatedSpan at hG
    change offsetAtInfty (star G) ∈ gaussianModulatedSpan
    have := star_mem_gaussianModulatedSpan hG
    convert this using 1
    funext x
    simp [offsetAtInfty, ContinuousMap.star_apply]
theorem exists_mem_onePointModulatedAlgebra_extends (k : ℕ) (s : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ G ∈ onePointModulatedAlgebra, G ∞ = 0 ∧ ∀ x : UnitStrip,
      G (x : OnePoint UnitStrip) = gaussianModulatedMonomial k s σ x := by
  obtain ⟨G, h0, h1⟩ := exists_onePoint_extension _ (continuous_gaussianModulatedMonomial k s σ)
    (tendsto_gaussianModulatedMonomial k s hσ)
  refine ⟨G, ?_, h0, h1⟩
  change offsetAtInfty G ∈ gaussianModulatedSpan
  have : offsetAtInfty G = gaussianModulatedMonomial k s σ := by
    funext x
    rw [offsetAtInfty, h0, h1, sub_zero]
  rw [this]
  exact Submodule.subset_span ⟨k, s, σ, hσ, rfl⟩
theorem gaussianModulatedMonomial_zero_zero_one_ne_zero (x : UnitStrip) :
    gaussianModulatedMonomial 0 0 1 x ≠ 0 := by
  rw [gaussianModulatedMonomial_apply, pow_zero, one_mul]
  exact Complex.exp_ne_zero _
theorem exists_gaussianModulatedMonomial_ne {x y : UnitStrip} (hxy : x ≠ y) :
    ∃ (k : ℕ) (s σ : ℝ), 0 < σ ∧
      gaussianModulatedMonomial k s σ x ≠ gaussianModulatedMonomial k s σ y := by
  by_cases hsq : x.2 ^ 2 = y.2 ^ 2
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hq | hq
    · have hξ : (x.1 : ℝ) ≠ (y.1 : ℝ) := fun h => hxy (Prod.ext (Subtype.ext h) hq)
      refine ⟨1, 0, 1, one_pos, fun h => hξ ?_⟩
      rw [gaussianModulatedMonomial_apply, gaussianModulatedMonomial_apply, pow_one, pow_one,
        hq] at h
      exact_mod_cast mul_right_cancel₀ (Complex.exp_ne_zero _) h
    · by_cases hq0 : x.2 = 0
      · have hy0 : y.2 = 0 := by rw [hq0] at hq; linarith
        have hξ : (x.1 : ℝ) ≠ (y.1 : ℝ) :=
          fun h => hxy (Prod.ext (Subtype.ext h) (hq0.trans hy0.symm))
        refine ⟨1, 0, 1, one_pos, fun h => hξ ?_⟩
        rw [gaussianModulatedMonomial_apply, gaussianModulatedMonomial_apply, pow_one, pow_one,
          hq0, hy0] at h
        exact_mod_cast mul_right_cancel₀ (Complex.exp_ne_zero _) h
      · refine ⟨0, Real.pi / (2 * x.2), 1, one_pos, fun h => ?_⟩
        rw [gaussianModulatedMonomial_apply, gaussianModulatedMonomial_apply, pow_zero, one_mul,
          pow_zero, one_mul] at h
        have hy : y.2 = -x.2 := by linarith
        have hx' : (x.2 : ℂ) ≠ 0 := by exact_mod_cast hq0
        have hexp : Complex.I * ((Real.pi / (2 * x.2) : ℝ) : ℂ) * (x.2 : ℂ) -
              ((1 : ℝ) : ℂ) * (x.2 : ℂ) ^ 2 / 2 =
            (Complex.I * ((Real.pi / (2 * x.2) : ℝ) : ℂ) * (y.2 : ℂ) -
              ((1 : ℝ) : ℂ) * (y.2 : ℂ) ^ 2 / 2) + Real.pi * Complex.I := by
          rw [hy]
          push_cast
          field_simp
          ring
        rw [hexp, Complex.exp_add, Complex.exp_pi_mul_I] at h
        have hne := Complex.exp_ne_zero (Complex.I * ((Real.pi / (2 * x.2) : ℝ) : ℂ) * (y.2 : ℂ) -
              ((1 : ℝ) : ℂ) * (y.2 : ℂ) ^ 2 / 2)
        have h2 : (-1 : ℂ) = 1 := by
          apply mul_left_cancel₀ hne
          rw [h, mul_one]
        norm_num at h2
  · refine ⟨0, 0, 1, one_pos, fun h => hsq ?_⟩
    rw [gaussianModulatedMonomial_apply, gaussianModulatedMonomial_apply, pow_zero, one_mul,
      pow_zero, one_mul] at h
    have h1 : ∀ q : ℝ, Complex.I * ((0 : ℝ) : ℂ) * (q : ℂ) - ((1 : ℝ) : ℂ) * (q : ℂ) ^ 2 / 2 =
        ((-(q ^ 2 / 2) : ℝ) : ℂ) := by
      intro q
      push_cast
      ring
    rw [h1, h1, ← Complex.ofReal_exp, ← Complex.ofReal_exp] at h
    have h2 := Real.exp_injective (Complex.ofReal_injective h)
    linarith
theorem onePointModulatedAlgebra_separatesPoints :
    onePointModulatedAlgebra.toSubalgebra.SeparatesPoints := by
  intro a b hab
  have key : ∀ x : UnitStrip, ∃ f ∈ (fun f : C(OnePoint UnitStrip, ℂ) =>
      (f : OnePoint UnitStrip → ℂ)) ''
        (onePointModulatedAlgebra.toSubalgebra : Set C(OnePoint UnitStrip, ℂ)),
      f ∞ ≠ f (x : OnePoint UnitStrip) := by
    intro x
    obtain ⟨G, hG, h0, h1⟩ := exists_mem_onePointModulatedAlgebra_extends 0 0 (σ := 1) one_pos
    refine ⟨G, ⟨G, hG, rfl⟩, ?_⟩
    rw [h0, h1]
    exact (gaussianModulatedMonomial_zero_zero_one_ne_zero x).symm
  induction a using OnePoint.rec with
  | infty =>
    induction b using OnePoint.rec with
    | infty => exact absurd rfl hab
    | coe y => exact key y
  | coe x =>
    induction b using OnePoint.rec with
    | infty =>
      obtain ⟨f, hf, hne⟩ := key x
      exact ⟨f, hf, hne.symm⟩
    | coe y =>
      have hxy : x ≠ y := fun h => hab (by rw [h])
      obtain ⟨k, s, σ, hσ, hne⟩ := exists_gaussianModulatedMonomial_ne hxy
      obtain ⟨G, hG, _, h1⟩ := exists_mem_onePointModulatedAlgebra_extends k s hσ
      refine ⟨G, ⟨G, hG, rfl⟩, ?_⟩
      rw [h1, h1]
      exact hne
theorem exists_mem_span_norm_sub_le (f : UnitStrip → ℂ) (hf : f ∈ stripZeroAtInfty) {ε : ℝ}
    (hε : 0 < ε) : ∃ f' ∈ gaussianModulatedSpan, ∀ x, ‖f x - f' x‖ ≤ ε := by
  obtain ⟨F, hF0, hF⟩ := exists_onePoint_extension f hf.1 (tendsto_zero_of_mem_stripZeroAtInfty f hf)
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    onePointModulatedAlgebra onePointModulatedAlgebra_separatesPoints
  have hmem : F ∈ closure (onePointModulatedAlgebra : Set C(OnePoint UnitStrip, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, htop]
    trivial
  obtain ⟨G, hG, hd⟩ := Metric.mem_closure_iff.1 hmem (ε / 2) (half_pos hε)
  refine ⟨fun x => G (x : OnePoint UnitStrip) - G ∞, hG, fun x => ?_⟩
  have h1 : ‖F (x : OnePoint UnitStrip) - G (x : OnePoint UnitStrip)‖ ≤ ε / 2 := by
    have := (ContinuousMap.dist_apply_le_dist (f := F) (g := G) (x : OnePoint UnitStrip))
    rw [dist_eq_norm] at this
    exact this.trans hd.le
  have h2 : ‖F ∞ - G ∞‖ ≤ ε / 2 := by
    have := (ContinuousMap.dist_apply_le_dist (f := F) (g := G) (∞ : OnePoint UnitStrip))
    rw [dist_eq_norm] at this
    exact this.trans hd.le
  have h3 : f x - (G (x : OnePoint UnitStrip) - G ∞) =
      (F (x : OnePoint UnitStrip) - G (x : OnePoint UnitStrip)) - (F ∞ - G ∞) := by
    rw [hF, hF0]
    ring
  rw [h3]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := add_halves ε
theorem exists_norm_le_of_mem (f : UnitStrip → ℂ) (hf : f ∈ stripZeroAtInfty) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨F, _, hF⟩ := exists_onePoint_extension f hf.1 (tendsto_zero_of_mem_stripZeroAtInfty f hf)
  exact ⟨‖F‖, fun x => by rw [← hF]; exact F.norm_coe_le_norm _⟩
theorem integrable_of_mem_stripZeroAtInfty {μ : Measure UnitStrip} [IsFiniteMeasure μ]
    (f : UnitStrip → ℂ) (hf : f ∈ stripZeroAtInfty) : Integrable f μ := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem f hf
  exact Integrable.of_bound hf.1.aestronglyMeasurable C (ae_of_all _ hC)
theorem integral_gaussianModulatedMonomial_eq (hG : GaussianDensityTransforms)
    (μ : Measure UnitStrip) [IsFiniteMeasure μ] (k : ℕ) (s' : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∫ x, gaussianModulatedMonomial k s' σ x ∂μ =
      ∫ s : ℝ, (gaussianDensity σ s' s : ℂ) *
        ∫ x : UnitStrip, (unitStripPow x.1 k : ℂ) * Complex.exp (Complex.I * s * x.2) ∂μ := by
  obtain ⟨hmass, htrans, -⟩ := (hG s').1 σ hσ
  have hint : Integrable (gaussianDensity σ s') := by
    by_contra hc
    rw [integral_undef hc] at hmass
    norm_num at hmass
  have hcw : Continuous (gaussianDensity σ s') := by
    unfold gaussianDensity
    fun_prop
  have hcp := continuous_unitStripPow k
  have hprod : Integrable (Function.uncurry fun (s : ℝ) (x : UnitStrip) =>
      (gaussianDensity σ s' s : ℂ) * ((unitStripPow x.1 k : ℂ) *
        Complex.exp (Complex.I * s * x.2))) (volume.prod μ) := by
    have h0 : Integrable (fun r : ℝ => (gaussianDensity σ s' r : ℂ)) := hint.ofReal
    have hI : Integrable (fun z : ℝ × UnitStrip => (gaussianDensity σ s' z.1 : ℂ))
        (volume.prod μ) := h0.comp_fst μ
    refine hI.mono ?_ (ae_of_all _ fun z => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      unfold Function.uncurry
      have h1 : Continuous fun z : ℝ × UnitStrip => (unitStripPow z.2.1 k : ℂ) :=
        Complex.continuous_ofReal.comp (hcp.comp (continuous_fst.comp continuous_snd))
      have h2 : Continuous fun z : ℝ × UnitStrip => (gaussianDensity σ s' z.1 : ℂ) :=
        Complex.continuous_ofReal.comp (hcw.comp continuous_fst)
      exact h2.mul (h1.mul (by fun_prop))
    · simp only [Function.uncurry, norm_mul, norm_exp_I_mul_real_mul, mul_one]
      calc _ ≤ ‖(gaussianDensity σ s' z.1 : ℂ)‖ * 1 :=
            mul_le_mul_of_nonneg_left (norm_unitStripPow_le _ _) (norm_nonneg _)
        _ = _ := mul_one _
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hprod]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show gaussianModulatedMonomial k s' σ x = _
  have h1 : ∀ s : ℝ, (gaussianDensity σ s' s : ℂ) * ((unitStripPow x.1 k : ℂ) *
      Complex.exp (Complex.I * s * x.2)) = (unitStripPow x.1 k : ℂ) *
        ((gaussianDensity σ s' s : ℂ) * Complex.exp (Complex.I * s * x.2)) := fun s => by ring
  simp_rw [h1]
  rw [integral_const_mul, htrans]
  rfl
theorem integral_eq_on_gaussianModulatedSpan {m m' : Measure UnitStrip} [IsFiniteMeasure m]
    [IsFiniteMeasure m']
    (h : ∀ (k : ℕ) (s σ : ℝ), 0 < σ →
      ∫ x, gaussianModulatedMonomial k s σ x ∂m = ∫ x, gaussianModulatedMonomial k s σ x ∂m')
    (g : UnitStrip → ℂ) (hg : g ∈ gaussianModulatedSpan) :
    Integrable g m ∧ Integrable g m' ∧ ∫ x, g x ∂m = ∫ x, g x ∂m' := by
  unfold gaussianModulatedSpan at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, s, σ, hσ, rfl⟩ := hg
    have hb : ∀ x, ‖gaussianModulatedMonomial k s σ x‖ ≤ 1 := fun x =>
      (norm_gaussianModulatedMonomial_le k s σ x).trans (Real.exp_le_one_iff.2 (by
        have : 0 ≤ σ / 2 * x.2 ^ 2 := by positivity
        linarith))
    exact ⟨Integrable.of_bound (continuous_gaussianModulatedMonomial k s σ).aestronglyMeasurable 1
        (ae_of_all _ hb),
      Integrable.of_bound (continuous_gaussianModulatedMonomial k s σ).aestronglyMeasurable 1
        (ae_of_all _ hb),
      h k s σ hσ⟩
  | zero => simp [integrable_zero]
  | add a b _ _ iha ihb =>
    refine ⟨iha.1.add ihb.1, iha.2.1.add ihb.2.1, ?_⟩
    simp only [Pi.add_apply]
    rw [integral_add iha.1 ihb.1, integral_add iha.2.1 ihb.2.1, iha.2.2, ihb.2.2]
  | smul c a _ ih =>
    refine ⟨ih.1.smul c, ih.2.1.smul c, ?_⟩
    simp only [Pi.smul_apply]
    rw [integral_smul, integral_smul, ih.2.2]
theorem integral_eq_on_stripZeroAtInfty {m m' : Measure UnitStrip} [IsFiniteMeasure m]
    [IsFiniteMeasure m']
    (h : ∀ (k : ℕ) (s σ : ℝ), 0 < σ →
      ∫ x, gaussianModulatedMonomial k s σ x ∂m = ∫ x, gaussianModulatedMonomial k s σ x ∂m')
    (f : UnitStrip → ℂ) (hf : f ∈ stripZeroAtInfty) :
    ∫ x, f x ∂m = ∫ x, f x ∂m' := by
  have hfm : Integrable f m := integrable_of_mem_stripZeroAtInfty f hf
  have hfm' : Integrable f m' := integrable_of_mem_stripZeroAtInfty f hf
  refine sub_eq_zero.1 (norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_))
  set T : ℝ := m.real Set.univ + m'.real Set.univ + 1 with hT
  have hTpos : 0 < T := by positivity
  obtain ⟨f', hf', hclose⟩ := exists_mem_span_norm_sub_le f hf (div_pos hδ hTpos)
  obtain ⟨hi, hi', heq⟩ := integral_eq_on_gaussianModulatedSpan h f' hf'
  have hd : ∫ x, f x ∂m - ∫ x, f x ∂m' =
      ∫ x, (f x - f' x) ∂m - ∫ x, (f x - f' x) ∂m' := by
    rw [integral_sub hfm hi, integral_sub hfm' hi', heq]
    ring
  have b1 := norm_integral_le_of_norm_le_const (μ := m) (ae_of_all _ hclose)
  have b2 := norm_integral_le_of_norm_le_const (μ := m') (ae_of_all _ hclose)
  rw [hd, zero_add]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ δ / T * m.real Set.univ + δ / T * m'.real Set.univ := add_le_add b1 b2
    _ ≤ δ / T * T := by
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hT]
      linarith
    _ = δ := div_mul_cancel₀ _ hTpos.ne'
theorem ofReal_compactlySupported_mem (f : CompactlySupportedContinuousMap UnitStrip ℝ) :
    (fun x => ((f x : ℝ) : ℂ)) ∈ stripZeroAtInfty := by
  refine ⟨Complex.continuous_ofReal.comp f.continuous, ?_⟩
  obtain ⟨C, hC⟩ := (HasCompactSupport.isCompact f.hasCompactSupport).exists_bound_of_continuousOn
    (f := fun x : UnitStrip => x.2) continuous_snd.continuousOn
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop C] with R hR
  symm
  simp only [ENNReal.iSup_eq_zero]
  intro x hx
  have hnot : x ∉ tsupport f := fun hmem => by
    have := hC x hmem
    rw [Real.norm_eq_abs] at this
    linarith
  simp [image_eq_zero_of_notMem_tsupport hnot]
theorem measure_eq_of_integral_gaussianModulatedMonomial_eq {m m' : Measure UnitStrip}
    [IsFiniteMeasure m] [IsFiniteMeasure m']
    (h : ∀ (k : ℕ) (s σ : ℝ), 0 < σ →
      ∫ x, gaussianModulatedMonomial k s σ x ∂m = ∫ x, gaussianModulatedMonomial k s σ x ∂m') :
    m = m' := by
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  have := integral_eq_on_stripZeroAtInfty h _ (ofReal_compactlySupported_mem f)
  rw [integral_complex_ofReal, integral_complex_ofReal] at this
  exact_mod_cast this
theorem measure_eq_of_integral_pow_mul_exp_eq (hG : GaussianDensityTransforms)
    (m m' : Measure UnitStrip) [IsFiniteMeasure m] [IsFiniteMeasure m']
    (h : ∀ (k : ℕ) (s : ℝ),
      ∫ x, (unitStripPow x.1 k : ℂ) * Complex.exp (Complex.I * s * x.2) ∂m =
        ∫ x, (unitStripPow x.1 k : ℂ) * Complex.exp (Complex.I * s * x.2) ∂m') : m = m' := by
  refine measure_eq_of_integral_gaussianModulatedMonomial_eq fun k s σ hσ => ?_
  rw [integral_gaussianModulatedMonomial_eq hG m k s hσ,
    integral_gaussianModulatedMonomial_eq hG m' k s hσ]
  simp_rw [h k]
def expNegToStrip (x : Set.Ici (0 : ℝ) × ℝ) : UnitStrip :=
  (⟨Real.exp (-(x.1 : ℝ)), (Real.exp_pos _).le, Real.exp_le_one_iff.2 (by
    have : (0 : ℝ) ≤ x.1 := x.1.2
    linarith)⟩, x.2)
def negLogFromStrip (y : UnitStrip) : Set.Ici (0 : ℝ) × ℝ :=
  (⟨max 0 (-Real.log y.1), Set.mem_Ici.2 (le_max_left _ _)⟩, y.2)
theorem negLogFromStrip_comp_expNegToStrip : negLogFromStrip ∘ expNegToStrip = id := by
  funext x
  refine Prod.ext (Subtype.ext ?_) ?_
  swap
  · rfl
  simp only [Function.comp, negLogFromStrip, expNegToStrip, Real.log_exp, neg_neg, id]
  exact max_eq_right x.1.2
theorem measurable_expNegToStrip : Measurable expNegToStrip := by
  refine Continuous.measurable ?_
  unfold expNegToStrip
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_snd
  fun_prop
theorem measurable_negLogFromStrip : Measurable negLogFromStrip := by
  unfold negLogFromStrip
  refine Measurable.prodMk (Measurable.subtype_mk ?_) measurable_snd
  exact measurable_const.max
    (Real.measurable_log.comp (measurable_subtype_coe.comp measurable_fst)).neg
theorem measure_eq_of_integral_exp_eq_halfPlane (hG : GaussianDensityTransforms)
    (m m' : Measure (Set.Ici (0 : ℝ) × ℝ)) [IsFiniteMeasure m] [IsFiniteMeasure m']
    (h : ∀ (k : ℕ) (s : ℝ),
      ∫ x, Complex.exp (-(k : ℂ) * (x.1 : ℝ) + Complex.I * s * x.2) ∂m =
        ∫ x, Complex.exp (-(k : ℂ) * (x.1 : ℝ) + Complex.I * s * x.2) ∂m') : m = m' := by
  have hmap : ∀ (μ : Measure (Set.Ici (0 : ℝ) × ℝ)) (k : ℕ) (s : ℝ),
      ∫ x, (unitStripPow x.1 k : ℂ) * Complex.exp (Complex.I * s * x.2) ∂(μ.map expNegToStrip) =
        ∫ x, Complex.exp (-(k : ℂ) * (x.1 : ℝ) + Complex.I * s * x.2) ∂μ := by
    intro μ k s
    have hc : Continuous fun x : UnitStrip =>
        (unitStripPow x.1 k : ℂ) * Complex.exp (Complex.I * s * x.2) := by
      have h1 : Continuous fun x : UnitStrip => (unitStripPow x.1 k : ℂ) :=
        Complex.continuous_ofReal.comp ((continuous_unitStripPow k).comp continuous_fst)
      exact h1.mul (by fun_prop)
    rw [integral_map measurable_expNegToStrip.aemeasurable hc.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show (unitStripPow (expNegToStrip x).1 k : ℂ) *
        Complex.exp (Complex.I * s * (expNegToStrip x).2) =
      Complex.exp (-(k : ℂ) * ((x.1 : ℝ) : ℂ) + Complex.I * s * x.2)
    rw [unitStripPow_natCast, Complex.exp_add]
    simp only [expNegToStrip]
    congr 1
    push_cast
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have heq : m.map expNegToStrip = m'.map expNegToStrip :=
    measure_eq_of_integral_pow_mul_exp_eq hG _ _ fun k s => by rw [hmap, hmap, h]
  have hback : ∀ μ : Measure (Set.Ici (0 : ℝ) × ℝ),
      (μ.map expNegToStrip).map negLogFromStrip = μ := by
    intro μ
    rw [Measure.map_map measurable_negLogFromStrip measurable_expNegToStrip,
      negLogFromStrip_comp_expNegToStrip, Measure.map_id]
  rw [← hback m, heq, hback m']
theorem _root_.YangMills.Construction.EuclideanAnalysis.Strip.modulatedDenseAndMeasureUnique_of_gaussianDensityTransforms
    (hG : GaussianDensityTransforms) :
    ModulatedDenseAndMeasureUnique := by
  refine ⟨fun f hf ε hε => ?_, fun m m' _ _ h => measure_eq_of_integral_pow_mul_exp_eq hG m m' h,
    fun m m' _ _ h => measure_eq_of_integral_exp_eq_halfPlane hG m m' h⟩
  obtain ⟨f', hf', hclose⟩ := exists_mem_span_norm_sub_le f hf hε
  exact ⟨f', hf', ciSup_le hclose⟩
end YangMills.Construction.EuclideanAnalysis.Strip.ModulatedDensity
