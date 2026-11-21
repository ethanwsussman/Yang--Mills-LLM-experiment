import YangMills.Construction.Towers.LogarithmOfAShiftedOperatorAndIntertwiners
import Mathlib
set_option autoImplicit false
open Set Filter Topology YangMills.Construction.OperatorCalculus YangMills.Construction.OneLoopNotation YangMills.Construction.Tower.UnitLatticeL2
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
namespace ShiftedLog
section UniformSums
def uniformRiemannSum {E : Type} [AddCommGroup E] [Module ℝ E] (T : ℝ → E) (y : ℝ) (p : ℕ) : E :=
  ∑ l ∈ Finset.range (p + 1), (y / ((p : ℝ) + 1)) • T (((l : ℝ) + 1) * (y / ((p : ℝ) + 1)))
def uniformPartition (y : ℝ) (hy : 0 < y) (p : ℕ) : MarkedPartition 0 y where
  card := p + 1
  node i := ((i : ℕ) : ℝ) * (y / ((p : ℝ) + 1))
  sample i := (((i : ℕ) : ℝ) + 1) * (y / ((p : ℝ) + 1))
  node_mono := by
    intro i j hij
    have hd : 0 ≤ y / ((p : ℝ) + 1) := by positivity
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) hd
  node_zero := by simp
  node_last := by
    have : ((p : ℝ) + 1) ≠ 0 := by positivity
    simp only [Fin.val_last]
    push_cast
    field_simp
  sample_mem := by
    intro i
    have hd : 0 ≤ y / ((p : ℝ) + 1) := by positivity
    constructor
    · simp only [Fin.val_castSucc]
      exact mul_le_mul_of_nonneg_right (by linarith) hd
    · simp only [Fin.val_succ]
      push_cast
      exact le_refl _
theorem uniformPartition_node_sub (y : ℝ) (hy : 0 < y) (p : ℕ) (i : Fin (uniformPartition y hy p).card) :
    (uniformPartition y hy p).node i.succ - (uniformPartition y hy p).node i.castSucc =
      y / ((p : ℝ) + 1) := by
  show (((i.succ : Fin ((uniformPartition y hy p).card + 1)) : ℕ) : ℝ) * (y / ((p : ℝ) + 1)) -
    (((i.castSucc : Fin ((uniformPartition y hy p).card + 1)) : ℕ) : ℝ) * (y / ((p : ℝ) + 1)) = _
  rw [Fin.val_succ, Fin.val_castSucc]
  push_cast
  ring
theorem sum_uniformPartition {E : Type} [AddCommGroup E] [Module ℝ E] (T : ℝ → E) (y : ℝ)
    (hy : 0 < y) (p : ℕ) : (uniformPartition y hy p).sum T = uniformRiemannSum T y p := by
  unfold MarkedPartition.sum uniformRiemannSum
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [uniformPartition_node_sub]
  rfl
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem tendsto_uniformRiemannSum {T : ℝ → BddOp H} {y : ℝ} (hy : 0 < y) {X : BddOp H}
    (h : RiemannSumsTendsto T 0 y X) : Tendsto (uniformRiemannSum T y) atTop (𝓝 X) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨υ, hυ, hh⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_gt (y / υ)
  refine ⟨N, fun p hp => ?_⟩
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hmesh : y / ((p : ℝ) + 1) ≤ υ := by
    rw [div_le_iff₀ hp1]
    have h1 : y / υ < (p : ℝ) + 1 := by
      have : (N : ℝ) ≤ p := Nat.cast_le.2 hp
      linarith
    rw [div_lt_iff₀ hυ] at h1
    linarith
  have hd : 0 < y / ((p : ℝ) + 1) := by positivity
  have key : IsRiemannSumWithMeshLE T 0 y υ (uniformRiemannSum T y p) := by
    refine ⟨uniformPartition y hy p, ?_, ?_, ?_, (sum_uniformPartition T y hy p).symm⟩
    · show 1 ≤ p + 1
      omega
    · intro i j hij
      exact mul_lt_mul_of_pos_right (Nat.cast_lt.2 hij) hd
    · intro i
      rw [uniformPartition_node_sub]
      exact hmesh
  have := hh _ key
  rw [dist_eq_norm]
  linarith
theorem tendsto_uniformRiemannSum_integral {h : ℝ → ℝ} {y : ℝ} (hy : 0 < y)
    (hc : ContinuousOn h (Icc 0 y)) :
    Tendsto (uniformRiemannSum h y) atTop (𝓝 (∫ w in (0 : ℝ)..y, h w)) := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hc
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := huc (ε / (2 * y)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (y / δ)
  refine ⟨N, fun p hp => ?_⟩
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  set d : ℝ := y / ((p : ℝ) + 1) with hd_def
  have hd : 0 < d := by positivity
  have hdδ : d < δ := by
    rw [hd_def, div_lt_iff₀ hp1]
    have h1 : y / δ < (p : ℝ) + 1 := by
      have : (N : ℝ) ≤ p := Nat.cast_le.2 hp
      linarith
    rw [div_lt_iff₀ hδ] at h1
    linarith
  have hpd : ((p : ℝ) + 1) * d = y := by
    rw [hd_def]
    field_simp
  set a : ℕ → ℝ := fun k => (k : ℝ) * d with ha_def
  have hmem : ∀ k : ℕ, k < p + 1 → ∀ w ∈ Icc (a k) (a (k + 1)), w ∈ Icc (0 : ℝ) y := by
    intro k hk w hw
    have h1 : 0 ≤ a k := by positivity
    have h2 : a (k + 1) ≤ y := by
      have : ((k + 1 : ℕ) : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast hk
      calc a (k + 1) ≤ ((p : ℝ) + 1) * d := mul_le_mul_of_nonneg_right this hd.le
        _ = y := hpd
    exact ⟨h1.trans hw.1, hw.2.trans h2⟩
  have hstep : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k
    simp only [ha_def]
    push_cast
    nlinarith
  have hint : ∀ k : ℕ, k < p + 1 → IntervalIntegrable h MeasureTheory.volume (a k) (a (k + 1)) := by
    intro k hk
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (hstep k)]
    exact hc.mono (hmem k hk)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [ha_def]
  have halast : a (p + 1) = y := by
    simp only [ha_def]
    push_cast
    exact hpd
  rw [ha0, halast] at hsum
  have hterm : ∀ k ∈ Finset.range (p + 1),
      ‖d • h (((k : ℝ) + 1) * d) - ∫ w in (a k)..(a (k + 1)), h w‖ ≤ ε / (2 * y) * d := by
    intro k hk
    have hk' : k < p + 1 := Finset.mem_range.1 hk
    have hlen : a (k + 1) - a k = d := by
      simp only [ha_def]
      push_cast
      ring
    have htag : ((k : ℝ) + 1) * d = a (k + 1) := by
      simp only [ha_def]
      push_cast
      ring
    have hconst : d • h (a (k + 1)) = ∫ _w in (a k)..(a (k + 1)), h (a (k + 1)) := by
      rw [intervalIntegral.integral_const, hlen]
    rw [htag, hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hint k hk')]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a k) (b := a (k + 1))
      (f := fun w => h (a (k + 1)) - h w) (C := ε / (2 * y)) ?_
    · rw [hlen, abs_of_pos hd] at hb
      exact hb
    · intro w hw
      rw [uIoc_of_le (hstep k)] at hw
      have hw' : w ∈ Icc (a k) (a (k + 1)) := ⟨hw.1.le, hw.2⟩
      have hend : a (k + 1) ∈ Icc (a k) (a (k + 1)) := ⟨hstep k, le_refl _⟩
      have hdist : dist (a (k + 1)) w < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hw.2])]
        linarith [hw.1]
      have := hh _ (hmem k hk' _ hend) _ (hmem k hk' _ hw') hdist
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]
      exact this.le
  have htotal : ‖uniformRiemannSum h y p - ∫ w in (0 : ℝ)..y, h w‖ ≤ ε / 2 := by
    rw [← hsum]
    unfold uniformRiemannSum
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ k ∈ Finset.range (p + 1), (d • h (((k : ℝ) + 1) * d) -
            ∫ w in (a k)..(a (k + 1)), h w)‖
        ≤ ∑ k ∈ Finset.range (p + 1), ‖d • h (((k : ℝ) + 1) * d) -
            ∫ w in (a k)..(a (k + 1)), h w‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range (p + 1), ε / (2 * y) * d := Finset.sum_le_sum hterm
      _ = ε / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        calc ((p : ℝ) + 1) * (ε / (2 * y) * d) = ε / (2 * y) * (((p : ℝ) + 1) * d) := by ring
          _ = ε / 2 := by
            rw [hpd]
            field_simp
  rw [dist_eq_norm]
  linarith
end UniformSums
section Transfer
variable {E E' G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
structure IsContinuousRealLinear (Φ : E → G) : Prop where
  map_add : ∀ a b, Φ (a + b) = Φ a + Φ b
  map_smul : ∀ (r : ℝ) a, Φ (r • a) = r • Φ a
  continuous : Continuous Φ
theorem map_uniformRiemannSum {Φ : E → G} (hΦ : IsContinuousRealLinear Φ) (T : ℝ → E) (y : ℝ) (p : ℕ) :
    Φ (uniformRiemannSum T y p) = uniformRiemannSum (fun w => Φ (T w)) y p := by
  unfold uniformRiemannSum
  have := map_sum (AddMonoidHom.mk' Φ hΦ.map_add)
    (fun l : ℕ => (y / ((p : ℝ) + 1)) • T (((l : ℝ) + 1) * (y / ((p : ℝ) + 1))))
    (Finset.range (p + 1))
  simp only [AddMonoidHom.mk'_apply] at this
  rw [this]
  exact Finset.sum_congr rfl fun l _ => hΦ.map_smul _ _
theorem eq_of_tendsto_uniformRiemannSum {Φ : E → G} {Ψ : E' → G} (hΦ : IsContinuousRealLinear Φ)
    (hΨ : IsContinuousRealLinear Ψ) {T : ℝ → E} {T' : ℝ → E'} {y : ℝ} (hy : 0 < y)
    (hT : ∀ w, 0 ≤ w → Φ (T w) = Ψ (T' w)) {X : E} {X' : E'}
    (h : Tendsto (uniformRiemannSum T y) atTop (𝓝 X))
    (h' : Tendsto (uniformRiemannSum T' y) atTop (𝓝 X')) :
    Φ X = Ψ X' := by
  have e : ∀ p, Φ (uniformRiemannSum T y p) = Ψ (uniformRiemannSum T' y p) := by
    intro p
    rw [map_uniformRiemannSum hΦ, map_uniformRiemannSum hΨ]
    unfold uniformRiemannSum
    refine Finset.sum_congr rfl fun l _ => ?_
    have hw : 0 ≤ ((l : ℝ) + 1) * (y / ((p : ℝ) + 1)) := by positivity
    beta_reduce
    rw [hT _ hw]
  have a := (hΦ.continuous.tendsto X).comp h
  have b := (hΨ.continuous.tendsto X').comp h'
  exact tendsto_nhds_unique a (b.congr fun p => (e p).symm)
theorem eq_of_tendsto_of_eq_pos {Φ : E → G} {Ψ : E' → G} (hΦ : IsContinuousRealLinear Φ)
    (hΨ : IsContinuousRealLinear Ψ) {Z : ℝ → E} {Z' : ℝ → E'}
    (he : ∀ m, 0 < m → Φ (Z m) = Ψ (Z' m)) {X : E} {X' : E'}
    (h : Tendsto Z atTop (𝓝 X)) (h' : Tendsto Z' atTop (𝓝 X')) : Φ X = Ψ X' := by
  have a := (hΦ.continuous.tendsto X).comp h
  have b := (hΨ.continuous.tendsto X').comp h'
  exact tendsto_nhds_unique_of_eventuallyEq a b ((eventually_gt_atTop 0).mono he)
end Transfer
section Operators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem addScalar_apply (T : BddOp H) (s : ℝ) (f : H) :
    addScalar T s f = T f + (s : ℂ) • f := by
  simp [addScalar, scalarOp]
theorem resolventDiff_apply (S : BddOp H) (w : ℝ) (f : H) :
    resolventDiff S w f =
      (((1 + w)⁻¹ : ℝ) : ℂ) • f - inverseOp (addScalar S w) f := by
  simp [resolventDiff, scalarOp]
theorem inverse_apply_left {A B : BddOp H} (h : IsTwoSidedInverse A B) (f : H) : A (B f) = f :=
  DFunLike.congr_fun h.1 f
theorem inverse_apply_right {A B : BddOp H} (h : IsTwoSidedInverse A B) (f : H) : B (A f) = f :=
  DFunLike.congr_fun h.2 f
theorem isContinuousRealLinear_eval (f : H) :
    IsContinuousRealLinear (fun X : BddOp H => X f) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, by fun_prop⟩
theorem isContinuousRealLinear_inner_left (f f' : H) :
    IsContinuousRealLinear (fun X : BddOp H => inner ℂ (X f) f') := by
  refine ⟨fun a b => ?_, fun r a => ?_, by fun_prop⟩
  · simp
  · show inner ℂ (r • a f) f' = r • inner ℂ (a f) f'
    rw [← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, Complex.real_smul]
theorem isContinuousRealLinear_inner_right (f f' : H) :
    IsContinuousRealLinear (fun X : BddOp H => inner ℂ f (X f')) := by
  refine ⟨fun a b => ?_, fun r a => ?_, by fun_prop⟩
  · simp
  · show inner ℂ f (r • a f') = r • inner ℂ f (a f')
    rw [← Complex.coe_smul, inner_smul_right, Complex.real_smul]
theorem isContinuousRealLinear_ofReal_smul (f : H) :
    IsContinuousRealLinear (fun r : ℝ => (r : ℂ) • f) := by
  refine ⟨fun a b => ?_, fun r a => ?_, ?_⟩
  · simp [add_smul]
  · simp only [smul_eq_mul, Complex.ofReal_mul, mul_smul, Complex.coe_smul]
  · exact Complex.continuous_ofReal.smul continuous_const
theorem riemannSumsTendsto_opIntegral {T : ℝ → BddOp H} {m : ℝ}
    (h : ∃ X, RiemannSumsTendsto T 0 m X) :
    RiemannSumsTendsto T 0 m (opIntegral T 0 m) :=
  Classical.epsilon_spec h
theorem integral_inv_sub_inv {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    ∫ w in (0 : ℝ)..m, ((1 + w)⁻¹ - (a + w)⁻¹) =
      Real.log (1 + m) - Real.log (a + m) + Real.log a := by
  have hne : ∀ w ∈ uIcc 0 m, 1 + w ≠ 0 ∧ a + w ≠ 0 := by
    intro w hw
    rw [uIcc_of_le hm.le] at hw
    have := hw.1
    exact ⟨by linarith, by linarith⟩
  have hd : ∀ w ∈ uIcc 0 m, HasDerivAt (fun w => Real.log (1 + w) - Real.log (a + w))
      ((1 + w)⁻¹ - (a + w)⁻¹) w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hne w hw
    have d1 : HasDerivAt (fun w : ℝ => 1 + w) 1 w := by
      simpa using (hasDerivAt_id w).const_add 1
    have d2 : HasDerivAt (fun w : ℝ => a + w) 1 w := by
      simpa using (hasDerivAt_id w).const_add a
    have e := (d1.log h1).sub (d2.log h2)
    simp only [one_div] at e
    exact e
  have hc : ContinuousOn (fun w : ℝ => (1 + w)⁻¹ - (a + w)⁻¹) (uIcc 0 m) := by
    refine ContinuousOn.sub (ContinuousOn.inv₀ (by fun_prop) fun w hw => (hne w hw).1)
      (ContinuousOn.inv₀ (by fun_prop) fun w hw => (hne w hw).2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp
theorem tendsto_log_sub_log_add_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun m : ℝ => Real.log (1 + m) - Real.log (a + m) + Real.log a) atTop
      (𝓝 (Real.log a)) := by
  have i : Tendsto (fun m : ℝ => (a + m)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop a tendsto_id)
  have j : Tendsto (fun m : ℝ => 1 - (a - 1) * (a + m)⁻¹) atTop (𝓝 (1 - (a - 1) * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul i)
  rw [mul_zero, sub_zero] at j
  have k : Tendsto (fun m : ℝ => Real.log (1 - (a - 1) * (a + m)⁻¹)) atTop (𝓝 (Real.log 1)) :=
    ((Real.continuousAt_log one_ne_zero).tendsto).comp j
  rw [Real.log_one] at k
  have l := k.add_const (Real.log a)
  rw [zero_add] at l
  refine l.congr' ((eventually_gt_atTop 0).mono fun m hm => ?_)
  have h1 : 1 + m ≠ 0 := by positivity
  have h2 : a + m ≠ 0 := by positivity
  have e : 1 - (a - 1) * (a + m)⁻¹ = (1 + m) / (a + m) := by
    field_simp
    ring
  simp only [e]
  rw [Real.log_div h1 h2]
theorem eigenvalue_add_shift_real_and_ge [CompleteSpace H] {z : ℝ} {T : BddOp H}
    (hT : ShiftedHalfPositive z T) {f : H} {s : ℂ} (hf : f ≠ 0) (hTf : T f = s • f) :
    (s + (z : ℂ)).im = 0 ∧ z / 2 ≤ (s + (z : ℂ)).re := by
  have hn : 0 < ‖f‖ ^ 2 := pow_pos (norm_pos_iff.2 hf) 2
  obtain ⟨h1, h2⟩ := hT.2 f
  have hff : (inner ℂ f f : ℂ) = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have e : inner ℂ f (addScalar T z f) - ((z / 2 : ℝ) : ℂ) * inner ℂ f f =
      (s + ((z / 2 : ℝ) : ℂ)) * ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [addScalar_apply, hTf, ← add_smul, inner_smul_right, hff]
    push_cast
    ring
  rw [e] at h1 h2
  rw [Complex.im_mul_ofReal] at h1
  rw [Complex.re_mul_ofReal] at h2
  have him : (s + ((z / 2 : ℝ) : ℂ)).im = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd h hn.ne'
  have hre : 0 ≤ (s + ((z / 2 : ℝ) : ℂ)).re := nonneg_of_mul_nonneg_left h2 hn
  simp only [Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re, add_zero]
    at him hre ⊢
  exact ⟨him, by linarith⟩
variable [CompleteSpace H]
theorem isSelfAdjointOp_of_inverse {A B : BddOp H} (hA : IsSelfAdjointOp A)
    (h : IsTwoSidedInverse A B) : IsSelfAdjointOp B := by
  have hA' : star A = A := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact hA
  have h1 : star B * A = 1 := by
    have := congrArg star h.1
    rwa [star_mul, hA', star_one] at this
  have h2 : star B = B := calc
    star B = star B * (A * B) := by rw [h.1, mul_one]
    _ = (star B * A) * B := by rw [mul_assoc]
    _ = B := by rw [h1, one_mul]
  rw [ContinuousLinearMap.star_eq_adjoint] at h2
  exact h2
theorem isSelfAdjointOp_opLog (hs : AddScalarClaim H) (hl : OperatorCalculus.LogExists H)
    {S : BddOp H} {c : ℝ} (hS : IsSelfAdjointOp S) (hc : 0 < c)
    (hge : IsBoundedBelowBy S c) : IsSelfAdjointOp (opLog S) := by
  obtain ⟨g1, _, _, _, g5, _, g7⟩ := hl S c hS hc hge
  have hint : ∀ m : ℝ, 0 < m → RiemannSumsTendsto (resolventDiff S) 0 m
      (opIntegral (resolventDiff S) 0 m) :=
    fun m hm => riemannSumsTendsto_opIntegral (g5 m hm).exists
  have hF : ∀ w : ℝ, 0 ≤ w → ∀ f f' : H,
      inner ℂ (resolventDiff S w f) f' = inner ℂ f (resolventDiff S w f') := by
    intro w hw f f'
    have hR : ContinuousLinearMap.adjoint (inverseOp (addScalar S w)) =
        inverseOp (addScalar S w) :=
      isSelfAdjointOp_of_inverse (hs S hS w 0).1 (g1 w hw).1
    have e := ContinuousLinearMap.adjoint_inner_left (inverseOp (addScalar S w)) f' f
    rw [hR] at e
    rw [resolventDiff_apply, resolventDiff_apply, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal, e]
  have key : ∀ f f' : H, inner ℂ (opLog S f) f' =
      inner ℂ f (opLog S f') := by
    intro f f'
    have hΦ := isContinuousRealLinear_inner_left (H := H) f f'
    have hΨ := isContinuousRealLinear_inner_right (H := H) f f'
    exact eq_of_tendsto_of_eq_pos hΦ hΨ (fun m hm => eq_of_tendsto_uniformRiemannSum hΦ hΨ hm
      (fun w hw => hF w hw f f')
      (tendsto_uniformRiemannSum hm (hint m hm)) (tendsto_uniformRiemannSum hm (hint m hm))) g7 g7
  exact ((ContinuousLinearMap.eq_adjoint_iff _ _).2 key).symm
theorem opLog_apply_of_eigenvector (hl : OperatorCalculus.LogExists H) {S : BddOp H} {c a : ℝ}
    (hS : IsSelfAdjointOp S) (hc : 0 < c) (hge : IsBoundedBelowBy S c) (ha : 0 < a) {f : H}
    (hf : S f = (a : ℂ) • f) : opLog S f = ((Real.log a : ℝ) : ℂ) • f := by
  obtain ⟨g1, _, _, _, g5, _, g7⟩ := hl S c hS hc hge
  have hint : ∀ m : ℝ, 0 < m → RiemannSumsTendsto (resolventDiff S) 0 m
      (opIntegral (resolventDiff S) 0 m) :=
    fun m hm => riemannSumsTendsto_opIntegral (g5 m hm).exists
  have hF : ∀ w : ℝ, 0 ≤ w → resolventDiff S w f =
      (((1 + w)⁻¹ - (a + w)⁻¹ : ℝ) : ℂ) • f := by
    intro w hw
    have hne : ((a + w : ℝ) : ℂ) ≠ 0 := by
      have : a + w ≠ 0 := by positivity
      exact_mod_cast this
    have hA : addScalar S w f = ((a + w : ℝ) : ℂ) • f := by
      rw [addScalar_apply, hf, ← add_smul]
      push_cast
      rfl
    have hR := inverse_apply_right (g1 w hw).1 f
    rw [hA, map_smul] at hR
    have hR' := (eq_inv_smul_iff₀ hne).2 hR
    rw [resolventDiff_apply, hR', Complex.ofReal_sub, sub_smul]
    push_cast
    rfl
  have hΦ := isContinuousRealLinear_eval (H := H) f
  have hΨ := isContinuousRealLinear_ofReal_smul f
  have hZ : ∀ m : ℝ, 0 < m → opIntegral (resolventDiff S) 0 m f =
      ((Real.log (1 + m) - Real.log (a + m) + Real.log a : ℝ) : ℂ) • f := by
    intro m hm
    have hcont : ContinuousOn (fun w : ℝ => (1 + w)⁻¹ - (a + w)⁻¹) (Icc 0 m) := by
      refine ContinuousOn.sub (ContinuousOn.inv₀ (by fun_prop) fun w hw => ?_)
        (ContinuousOn.inv₀ (by fun_prop) fun w hw => ?_)
      · have := hw.1
        positivity
      · have := hw.1
        positivity
    rw [← integral_inv_sub_inv ha hm]
    exact eq_of_tendsto_uniformRiemannSum hΦ hΨ hm hF (tendsto_uniformRiemannSum hm (hint m hm))
      (tendsto_uniformRiemannSum_integral hm hcont)
  have t1 := (hΦ.continuous.tendsto _).comp g7
  have t2 := (hΨ.continuous.tendsto _).comp (tendsto_log_sub_log_add_log ha)
  exact tendsto_nhds_unique_of_eventuallyEq t1 t2 ((eventually_gt_atTop 0).mono hZ)
theorem logShiftedProps_of_calculus (hs : AddScalarClaim H) (hl : OperatorCalculus.LogExists H)
    {z : ℝ} (hz : 0 < z) : LogShiftedProps H z := by
  intro T hT
  have hS : IsSelfAdjointOp (addScalar T z) := (hs T hT.1 z 0).1
  have hc : 0 < z / 2 := half_pos hz
  obtain ⟨g1, g2, _, g4, g5, _, g7⟩ := hl _ _ hS hc hT.2
  refine ⟨g1, isSelfAdjointOp_opLog hs hl hS hc hT.2, g2, g4,
    fun m hm => riemannSumsTendsto_opIntegral (g5 m hm).exists, g7, ?_⟩
  intro f s hf hTf
  obtain ⟨him, hre⟩ := eigenvalue_add_shift_real_and_ge hT hf hTf
  refine ⟨him, hre, ?_⟩
  have hsz : s + (z : ℂ) = (((s + (z : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  refine opLog_apply_of_eigenvector hl hS hc hT.2 (by linarith) ?_
  rw [addScalar_apply, hTf, ← add_smul, ← hsz]
variable {H' : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
theorem logCommIntertwiner_of_calculus (hs : AddScalarClaim H) (hl : OperatorCalculus.LogExists H)
    (hs' : AddScalarClaim H') (hl' : OperatorCalculus.LogExists H') {z : ℝ} (hz : 0 < z) :
    LogCommIntertwiner H H' z := by
  intro T T' V hT hT' hV hb hVT f
  obtain ⟨ς, _, hbd⟩ := hb
  have hadd : ∀ f g, V (f + g) = V f + V g := by
    rcases hV with h | h
    · exact h.map_add
    · exact h.1
  have hreal : ∀ (r : ℝ) (f : H), V ((r : ℂ) • f) = (r : ℂ) • V f := by
    rcases hV with h | h
    · exact fun r f => h.map_smul _ _
    · intro r f
      rw [h.2, Complex.conj_ofReal]
  have hcont : Continuous V :=
    AddMonoidHomClass.continuous_of_bound (AddMonoidHom.mk' V hadd) ς hbd
  have hsub : ∀ f g, V (f - g) = V f - V g := fun f g => (AddMonoidHom.mk' V hadd).map_sub f g
  have hnum : ∀ (A : BddOp H) (A' : BddOp H') (r : ℝ),
      (∀ g, V (A g) = A' (V g)) → ∀ g, V (addScalar A r g) = addScalar A' r (V g) := by
    intro A A' r h g
    rw [addScalar_apply, addScalar_apply, hadd, hreal, h]
  have hS : IsSelfAdjointOp (addScalar T z) := (hs T hT.1 z 0).1
  have hS' : IsSelfAdjointOp (addScalar T' z) := (hs' T' hT'.1 z 0).1
  have hc : 0 < z / 2 := half_pos hz
  obtain ⟨g1, _, _, _, g5, _, g7⟩ := hl _ _ hS hc hT.2
  obtain ⟨g1', _, _, _, g5', _, g7'⟩ := hl' _ _ hS' hc hT'.2
  have h1 := hnum T T' z hVT
  have hR : ∀ w : ℝ, 0 ≤ w → ∀ g, V (inverseOp (addScalar (addScalar T z) w) g) =
      inverseOp (addScalar (addScalar T' z) w) (V g) := by
    intro w hw g
    have h2 := hnum _ _ w h1
    calc V (inverseOp (addScalar (addScalar T z) w) g)
        = inverseOp (addScalar (addScalar T' z) w) (addScalar (addScalar T' z) w
            (V (inverseOp (addScalar (addScalar T z) w) g))) :=
          (inverse_apply_right (g1' w hw).1 _).symm
      _ = inverseOp (addScalar (addScalar T' z) w) (V (addScalar (addScalar T z) w
            (inverseOp (addScalar (addScalar T z) w) g))) := by rw [h2]
      _ = inverseOp (addScalar (addScalar T' z) w) (V g) := by
          rw [inverse_apply_left (g1 w hw).1]
  have hF : ∀ w : ℝ, 0 ≤ w → V (resolventDiff (addScalar T z) w f) =
      resolventDiff (addScalar T' z) w (V f) := by
    intro w hw
    rw [resolventDiff_apply, resolventDiff_apply, hsub, hreal, hR w hw]
  have hΦ : IsContinuousRealLinear (fun X : BddOp H => V (X f)) := by
    refine ⟨fun a b => hadd _ _, fun r a => ?_, hcont.comp (by fun_prop)⟩
    show V (r • a f) = r • V (a f)
    rw [← Complex.coe_smul, hreal, Complex.coe_smul]
  have hΨ := isContinuousRealLinear_eval (H := H') (V f)
  exact eq_of_tendsto_of_eq_pos hΦ hΨ (fun m hm => eq_of_tendsto_uniformRiemannSum hΦ hΨ hm hF
    (tendsto_uniformRiemannSum hm (riemannSumsTendsto_opIntegral (g5 m hm).exists))
    (tendsto_uniformRiemannSum hm (riemannSumsTendsto_opIntegral (g5' m hm).exists))) g7 g7'
end Operators
end ShiftedLog
open ShiftedLog in
theorem logShiftedAndIntertwiners_of_calculus
    (h : OperatorCalculus.Calculus.Statement) :
    LogShiftedAndIntertwiners := by
  intro H H' _ _ _ _ _ _ z hz
  obtain ⟨hs, _, _, _, _, _, hl⟩ := h H H'
  obtain ⟨hs', _, _, _, _, _, hl'⟩ := h H' H
  exact ⟨logShiftedProps_of_calculus hs hl hz, fun _ _ => rfl,
    logCommIntertwiner_of_calculus hs hl hs' hl' hz⟩
end YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
end
