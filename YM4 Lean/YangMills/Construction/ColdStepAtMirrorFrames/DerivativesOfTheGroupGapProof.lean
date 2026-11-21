import YangMills.Construction.ColdStepAtMirrorFrames.GroupGapIsSmoothProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory intervalIntegral
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace HaarGapDeriv
def laplaceMoment (j : ℕ) (s : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..2, v ^ j * Real.exp (-(s * v)) * haarRealPartDensity v
theorem haarRealPartDensity_continuous : Continuous haarRealPartDensity := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianSlope.continuous_haarRealPartDensity <;> assumption
theorem haarRealPartDensity_nonneg (v : ℝ) : 0 ≤ haarRealPartDensity v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianSlope.haarRealPartDensity_nonneg <;> assumption
theorem haarRealPartDensity_pos {v : ℝ} (hv0 : 0 < v) (hv2 : v < 2) : 0 < haarRealPartDensity v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HaarGap.haarRealPartDensity_pos <;> assumption
theorem haarRealPartDensity_le_two {v : ℝ} (_hv0 : 0 ≤ v) (hv2 : v ≤ 2) : haarRealPartDensity v ≤ 2 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HaarGap.haarRealPartDensity_le_two <;> assumption
theorem continuous_momentIntegrand (j : ℕ) (s : ℝ) :
    Continuous fun v : ℝ => v ^ j * Real.exp (-(s * v)) * haarRealPartDensity v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HaarGap.momentIntegrand_continuous <;> assumption
theorem laplaceMoment_zero_pos (s : ℝ) : 0 < laplaceMoment 0 s := by
  unfold laplaceMoment
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (continuous_momentIntegrand 0 s).intervalIntegrable _ _
  · intro v hv
    have := haarRealPartDensity_pos hv.1 hv.2
    have := Real.exp_pos (-(s * v))
    simp only [pow_zero, one_mul]
    positivity
  · norm_num
theorem laplaceMoment_zero_eq (s : ℝ) : laplaceMoment 0 s = haarLaplace s := by
  unfold laplaceMoment haarLaplace
  simp
theorem hasDerivAt_laplaceMoment (j : ℕ) (s : ℝ) :
    HasDerivAt (laplaceMoment j) (-(laplaceMoment (j + 1) s)) s := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 2) (s := Metric.ball s 1)
    (F := fun (x v : ℝ) => v ^ j * Real.exp (-(x * v)) * haarRealPartDensity v)
    (F' := fun (x v : ℝ) => -(v ^ (j + 1) * Real.exp (-(x * v)) * haarRealPartDensity v))
    (x₀ := s) (bound := fun _ => 2 ^ (j + 1) * Real.exp (2 * (|s| + 1)) * 2)
    (Metric.ball_mem_nhds s one_pos)
    (Filter.Eventually.of_forall fun x =>
      ((continuous_momentIntegrand j x).aestronglyMeasurable).restrict)
    ((continuous_momentIntegrand j s).intervalIntegrable _ _)
    (((continuous_momentIntegrand (j + 1) s).neg).aestronglyMeasurable.restrict)
    ?_ (by exact intervalIntegrable_const) ?_
  · have h := key.2
    rw [intervalIntegral.integral_neg] at h
    exact h
  · refine Filter.Eventually.of_forall fun v hv x hx => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hv
    have hv0 : 0 ≤ v := hv.1.le
    have hv2 : v ≤ 2 := hv.2
    have hx' : |x| ≤ |s| + 1 := by
      have h1 : |x - s| < 1 := by simpa [Real.dist_eq] using hx
      have h2 := abs_sub_abs_le_abs_sub x s
      linarith
    have he : Real.exp (-(x * v)) ≤ Real.exp (2 * (|s| + 1)) := by
      apply Real.exp_le_exp.mpr
      have h3 : -(x * v) ≤ |x| * v := by
        have := neg_abs_le x
        nlinarith
      nlinarith [abs_nonneg x]
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by
      have := haarRealPartDensity_nonneg v
      positivity)]
    have h1 : v ^ (j + 1) ≤ 2 ^ (j + 1) := pow_le_pow_left₀ hv0 hv2 _
    have h2 := haarRealPartDensity_le_two hv0 hv2
    have h3 := haarRealPartDensity_nonneg v
    exact show v ^ (j + 1) * Real.exp (-(x * v)) * haarRealPartDensity v
        ≤ 2 ^ (j + 1) * Real.exp (2 * (|s| + 1)) * 2 from by gcongr
  · refine Filter.Eventually.of_forall fun v _ x _ => ?_
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-(y * v))) (Real.exp (-(x * v)) * (-v)) x := by
      have : HasDerivAt (fun y : ℝ => -(y * v)) (-v) x :=
        HasDerivAt.congr_deriv ((hasDerivAt_id x).mul_const v).neg (by ring)
      exact this.exp
    have h2 := (h1.const_mul (v ^ j)).mul_const (haarRealPartDensity v)
    refine HasDerivAt.congr_deriv h2 ?_
    ring
def momentRatio (j : ℕ) (s : ℝ) : ℝ := laplaceMoment j s / laplaceMoment 0 s
theorem hasDerivAt_momentRatio (j : ℕ) (s : ℝ) :
    HasDerivAt (momentRatio j) (-(momentRatio (j + 1) s) + momentRatio j s * momentRatio 1 s) s := by
  have h0 := hasDerivAt_laplaceMoment 0 s
  have hj := hasDerivAt_laplaceMoment j s
  have hp := (laplaceMoment_zero_pos s).ne'
  have h := hj.div h0 hp
  refine HasDerivAt.congr_deriv h ?_
  unfold momentRatio
  simp only [zero_add]
  field_simp
  ring
inductive IsWeightedPoly : ℕ → (ℝ → ℝ) → Prop
  | base (j : ℕ) : IsWeightedPoly j (momentRatio j)
  | neg {k f} : IsWeightedPoly k f → IsWeightedPoly k (fun s => - f s)
  | add {k f g} : IsWeightedPoly k f → IsWeightedPoly k g → IsWeightedPoly k (fun s => f s + g s)
  | mul {k l f g} : IsWeightedPoly k f → IsWeightedPoly l g → IsWeightedPoly (k + l) (fun s => f s * g s)
theorem IsWeightedPoly.exists_hasDerivAt {k : ℕ} {f : ℝ → ℝ} (h : IsWeightedPoly k f) :
    ∃ g, IsWeightedPoly (k + 1) g ∧ ∀ s, HasDerivAt f (g s) s := by
  induction h with
  | base j =>
    exact ⟨_, IsWeightedPoly.add (IsWeightedPoly.neg (IsWeightedPoly.base (j + 1)))
      (IsWeightedPoly.mul (IsWeightedPoly.base j) (IsWeightedPoly.base 1)),
      fun s => hasDerivAt_momentRatio j s⟩
  | neg _ ih =>
    obtain ⟨g, hg, hd⟩ := ih
    exact ⟨_, IsWeightedPoly.neg hg, fun s => (hd s).neg⟩
  | add _ _ ih1 ih2 =>
    obtain ⟨g1, hg1, hd1⟩ := ih1
    obtain ⟨g2, hg2, hd2⟩ := ih2
    exact ⟨_, IsWeightedPoly.add hg1 hg2, fun s => (hd1 s).add (hd2 s)⟩
  | @mul k l f g hf hg ih1 ih2 =>
    obtain ⟨g1, hg1, hd1⟩ := ih1
    obtain ⟨g2, hg2, hd2⟩ := ih2
    have a1 : IsWeightedPoly (k + l + 1) fun s => g1 s * g s := by
      have := IsWeightedPoly.mul hg1 hg
      rwa [show k + 1 + l = k + l + 1 by omega] at this
    have a2 : IsWeightedPoly (k + l + 1) fun s => f s * g2 s := by
      have := IsWeightedPoly.mul hf hg2
      rwa [show k + (l + 1) = k + l + 1 by omega] at this
    exact ⟨_, IsWeightedPoly.add a1 a2, fun s => (hd1 s).mul (hd2 s)⟩
theorem laplaceMoment_zero_half_le (s : ℝ) : laplaceMoment 0 (s / 2) ≤ 4 * laplaceMoment 0 s := by
  have e1 : laplaceMoment 0 (s / 2) =
      2 * ∫ u in (0 : ℝ)..1, Real.exp (-(s * u)) * haarRealPartDensity (2 * u) := by
    unfold laplaceMoment
    have := intervalIntegral.mul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
      (f := fun v : ℝ => v ^ 0 * Real.exp (-(s / 2 * v)) * haarRealPartDensity v) 2
    simp only [mul_zero, mul_one] at this
    rw [← this]
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    simp only [pow_zero, one_mul]
    congr 3
    ring
  have e2 : (∫ u in (0 : ℝ)..1, Real.exp (-(s * u)) * haarRealPartDensity (2 * u)) ≤
      2 * ∫ u in (0 : ℝ)..1, Real.exp (-(s * u)) * haarRealPartDensity u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ((by have := haarRealPartDensity_continuous; fun_prop :
        Continuous fun u : ℝ => Real.exp (-(s * u)) * haarRealPartDensity (2 * u))).intervalIntegrable _ _
    · exact ((by have := haarRealPartDensity_continuous; fun_prop :
        Continuous fun u : ℝ => 2 * (Real.exp (-(s * u)) * haarRealPartDensity u))).intervalIntegrable _ _
    · intro u hu
      have h : haarRealPartDensity (2 * u) ≤ 2 * haarRealPartDensity u := by
        unfold haarRealPartDensity
        have hp := Real.pi_pos
        have h1 : Real.sqrt (2 * (2 * u) - (2 * u) ^ 2) ≤ 2 * Real.sqrt (2 * u - u ^ 2) := by
          rw [show (2 : ℝ) * Real.sqrt (2 * u - u ^ 2) = Real.sqrt (4 * (2 * u - u ^ 2)) by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]]
          apply Real.sqrt_le_sqrt
          nlinarith [hu.1, hu.2]
        have h2 : 0 ≤ 2 / Real.pi := by positivity
        nlinarith
      have := Real.exp_pos (-(s * u))
      nlinarith
  have e3 : (∫ u in (0 : ℝ)..1, Real.exp (-(s * u)) * haarRealPartDensity u) ≤ laplaceMoment 0 s := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (a := (0 : ℝ)) (b := 1) (c := 2) (μ := volume)
      (f := fun v : ℝ => Real.exp (-(s * v)) * haarRealPartDensity v)
      (((by have := haarRealPartDensity_continuous; fun_prop :
        Continuous fun v : ℝ => Real.exp (-(s * v)) * haarRealPartDensity v)).intervalIntegrable _ _)
      (((by have := haarRealPartDensity_continuous; fun_prop :
        Continuous fun v : ℝ => Real.exp (-(s * v)) * haarRealPartDensity v)).intervalIntegrable _ _)
    have hnn : 0 ≤ ∫ v in (1 : ℝ)..2, Real.exp (-(s * v)) * haarRealPartDensity v := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro v _
      have := haarRealPartDensity_nonneg v
      positivity
    have hm : laplaceMoment 0 s = ∫ v in (0 : ℝ)..2, Real.exp (-(s * v)) * haarRealPartDensity v := by
      unfold laplaceMoment
      simp
    rw [hm, ← hsplit]
    linarith
  rw [e1]
  linarith
theorem abs_momentRatio_mul_pow_le (j : ℕ) (s : ℝ) (hs : 0 < s) :
    |momentRatio j s| * s ^ j ≤ 2 ^ j * j.factorial * 4 := by
  have hm := laplaceMoment_zero_pos s
  have hnn : 0 ≤ laplaceMoment j s := by
    unfold laplaceMoment
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro v hv
    have := haarRealPartDensity_nonneg v
    have h0 : 0 ≤ v := hv.1
    positivity
  have hb : laplaceMoment j s * s ^ j ≤ 2 ^ j * j.factorial * laplaceMoment 0 (s / 2) := by
    have e : laplaceMoment 0 (s / 2) =
        ∫ v in (0 : ℝ)..2, Real.exp (-(s / 2 * v)) * haarRealPartDensity v := by
      unfold laplaceMoment
      simp
    rw [e, ← intervalIntegral.integral_const_mul]
    unfold laplaceMoment
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ((by have := haarRealPartDensity_continuous; fun_prop :
        Continuous fun v : ℝ => v ^ j * Real.exp (-(s * v)) * haarRealPartDensity v * s ^ j)).intervalIntegrable _ _
    · exact ((by have := haarRealPartDensity_continuous; fun_prop :
        Continuous fun v : ℝ => 2 ^ j * (j.factorial : ℝ) *
          (Real.exp (-(s / 2 * v)) * haarRealPartDensity v))).intervalIntegrable _ _
    · intro v hv
      have h0 : 0 ≤ v := hv.1
      have hd := haarRealPartDensity_nonneg v
      have h1 := Real.pow_div_factorial_le_exp (s / 2 * v) (by positivity) j
      have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
      rw [div_le_iff₀ hf] at h1
      have h2 : (s * v) ^ j ≤ 2 ^ j * j.factorial * Real.exp (s / 2 * v) := by
        have e1 : (s * v) ^ j = 2 ^ j * (s / 2 * v) ^ j := by
          rw [← mul_pow]
          congr 1
          ring
        rw [e1]
        have : (0 : ℝ) ≤ 2 ^ j := by positivity
        nlinarith
      have e2 : Real.exp (-(s * v)) * Real.exp (s / 2 * v) = Real.exp (-(s / 2 * v)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hE := Real.exp_pos (-(s * v))
      calc v ^ j * Real.exp (-(s * v)) * haarRealPartDensity v * s ^ j
          = (s * v) ^ j * (Real.exp (-(s * v)) * haarRealPartDensity v) := by
            rw [mul_pow]
            ring
        _ ≤ (2 ^ j * j.factorial * Real.exp (s / 2 * v)) *
              (Real.exp (-(s * v)) * haarRealPartDensity v) := by
            apply mul_le_mul_of_nonneg_right h2
            positivity
        _ = 2 ^ j * (j.factorial : ℝ) * ((Real.exp (-(s * v)) * Real.exp (s / 2 * v)) *
              haarRealPartDensity v) := by ring
        _ = 2 ^ j * (j.factorial : ℝ) * (Real.exp (-(s / 2 * v)) * haarRealPartDensity v) := by
            rw [e2]
  have h4 := laplaceMoment_zero_half_le s
  unfold momentRatio
  rw [abs_of_nonneg (div_nonneg hnn hm.le), div_mul_eq_mul_div, div_le_iff₀ hm]
  have hc : (0 : ℝ) ≤ 2 ^ j * j.factorial := by positivity
  nlinarith
theorem IsWeightedPoly.exists_bound {k : ℕ} {f : ℝ → ℝ} (h : IsWeightedPoly k f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 < s → |f s| * s ^ k ≤ C := by
  induction h with
  | base j =>
    exact ⟨2 ^ j * j.factorial * 4, by positivity, fun s hs => abs_momentRatio_mul_pow_le j s hs⟩
  | neg _ ih =>
    obtain ⟨C, hC, hb⟩ := ih
    exact ⟨C, hC, fun s hs => by simpa using hb s hs⟩
  | @add k f g _ _ ih1 ih2 =>
    obtain ⟨C1, hC1, hb1⟩ := ih1
    obtain ⟨C2, hC2, hb2⟩ := ih2
    refine ⟨C1 + C2, by positivity, fun s hs => ?_⟩
    have h1 := hb1 s hs
    have h2 := hb2 s hs
    have h3 := abs_add_le (f s) (g s)
    have hp : 0 ≤ s ^ k := by positivity
    nlinarith
  | @mul k l f g _ _ ih1 ih2 =>
    obtain ⟨C1, hC1, hb1⟩ := ih1
    obtain ⟨C2, hC2, hb2⟩ := ih2
    refine ⟨C1 * C2, by positivity, fun s hs => ?_⟩
    have h1 := hb1 s hs
    have h2 := hb2 s hs
    rw [abs_mul, pow_add]
    calc |f s| * |g s| * (s ^ k * s ^ l) = (|f s| * s ^ k) * (|g s| * s ^ l) := by ring
      _ ≤ C1 * C2 := by
        apply mul_le_mul h1 h2 (by positivity) hC1
theorem haarGap_eq_neg_log (s : ℝ) : haarGap s = - Real.log (laplaceMoment 0 s) := by
  unfold haarGap haarCharacterMean
  rw [laplaceMoment_zero_eq]
  have hm : 0 < haarLaplace s := by
    rw [← laplaceMoment_zero_eq]
    exact laplaceMoment_zero_pos s
  rw [Real.log_mul (Real.exp_pos s).ne' hm.ne', Real.log_exp]
  ring
theorem hasDerivAt_haarGap (s : ℝ) : HasDerivAt haarGap (momentRatio 1 s) s := by
  have h : haarGap = fun s => - Real.log (laplaceMoment 0 s) := funext haarGap_eq_neg_log
  rw [h]
  have h2 := ((hasDerivAt_laplaceMoment 0 s).log (laplaceMoment_zero_pos s).ne').neg
  refine HasDerivAt.congr_deriv h2 ?_
  unfold momentRatio
  simp only [zero_add]
  ring
theorem isWeightedPoly_iteratedDeriv_haarGap (k : ℕ) :
    IsWeightedPoly (k + 1) (iteratedDeriv (k + 1) haarGap) := by
  induction k with
  | zero =>
    have : iteratedDeriv 1 haarGap = momentRatio 1 := by
      rw [iteratedDeriv_one]
      exact funext fun s => (hasDerivAt_haarGap s).deriv
    rw [zero_add, this]
    exact IsWeightedPoly.base 1
  | succ k ih =>
    obtain ⟨g, hg, hd⟩ := ih.exists_hasDerivAt
    have : iteratedDeriv (k + 1 + 1) haarGap = g := by
      rw [iteratedDeriv_succ]
      exact funext fun s => (hd s).deriv
    rw [this]
    exact hg
end HaarGapDeriv
open HaarGapDeriv in
theorem haarGapDerivBound_holds : HaarGapDerivBound := by
  intro k hk
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨C, _, hb⟩ := (isWeightedPoly_iteratedDeriv_haarGap k').exists_bound
  refine ⟨C, fun s hs => ?_⟩
  have hs0 : 0 < s := by linarith
  have := hb s hs0
  rw [abs_mul, abs_of_pos (by positivity : 0 < s ^ (k' + 1)), mul_comm]
  exact this
end YangMills.Construction.ColdStepAtMirrorFrames
end
