import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfTheGroupGap
import YangMills.Construction.ColdStepAtMirrorFrames.GapOfANormNearOne
import YangMills.Construction.ColdStepAtMirrorFrames.GroupGapIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
namespace NormNearOne
abbrev smoothTop : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)
theorem natCast_le_smoothTop (j : ℕ) : (j : WithTop ℕ∞) ≤ smoothTop := by
  rw [← WithTop.coe_natCast]
  exact WithTop.coe_le_coe.2 le_top
section Calculus
variable {P Q R : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
theorem fderiv_fderiv_comp_apply {Φ : Q → R} {T : P → Q} {x : P} (hΦ : ContDiffAt ℝ 3 Φ (T x))
    (hT : ContDiffAt ℝ 3 T x) (u v : P) :
    fderiv ℝ (fun ζ => fderiv ℝ (Φ ∘ T) ζ u) x v =
      fderiv ℝ (fderiv ℝ Φ) (T x) (fderiv ℝ T x v) (fderiv ℝ T x u) +
        fderiv ℝ Φ (T x) (fderiv ℝ (fun ζ => fderiv ℝ T ζ u) x v) := by
  have hTc : ContinuousAt T x := hT.continuousAt
  have e1 : ∀ᶠ ζ in 𝓝 x, ContDiffAt ℝ 3 T ζ := hT.eventually (by simp)
  have e2 : ∀ᶠ ζ in 𝓝 x, ContDiffAt ℝ 3 Φ (T ζ) := hTc.eventually (hΦ.eventually (by simp))
  have he : (fun ζ => fderiv ℝ (Φ ∘ T) ζ u) =ᶠ[𝓝 x]
      fun ζ => (fderiv ℝ Φ (T ζ)) (fderiv ℝ T ζ u) := by
    filter_upwards [e1, e2] with ζ h1 h2
    have d1 : DifferentiableAt ℝ T ζ := h1.differentiableAt (by norm_num)
    have d2 : DifferentiableAt ℝ Φ (T ζ) := h2.differentiableAt (by norm_num)
    rw [fderiv_comp ζ d2 d1]
    rfl
  rw [he.fderiv_eq]
  have h2Φ : ContDiffAt ℝ 2 (fderiv ℝ Φ) (T x) := hΦ.fderiv_right (by norm_num)
  have hdΦ : DifferentiableAt ℝ (fderiv ℝ Φ) (T x) := h2Φ.differentiableAt (by norm_num)
  have hdT : DifferentiableAt ℝ T x := hT.differentiableAt (by norm_num)
  have h2T : ContDiffAt ℝ 2 (fderiv ℝ T) x := hT.fderiv_right (by norm_num)
  have hdTu : DifferentiableAt ℝ (fun ζ => fderiv ℝ T ζ u) x :=
    (h2T.differentiableAt (by norm_num)).clm_apply (differentiableAt_const u)
  have hc : HasFDerivAt (fun ζ => fderiv ℝ Φ (T ζ))
      ((fderiv ℝ (fderiv ℝ Φ) (T x)).comp (fderiv ℝ T x)) x :=
    hdΦ.hasFDerivAt.comp x hdT.hasFDerivAt
  have := (hc.clm_apply hdTu.hasFDerivAt).fderiv
  rw [this]
  simp [add_comm]
end Calculus
def quatNorm (q : ℍ[ℝ]) : ℝ := ‖q‖
theorem contDiffAt_quatNorm {q : ℍ[ℝ]} (hq : q ≠ 0) : ContDiffAt ℝ smoothTop quatNorm q :=
  contDiffAt_norm ℝ hq
def unitShell : Set ℍ[ℝ] := {q | 1 / 2 ≤ ‖q‖ ∧ ‖q‖ ≤ 1}
theorem isCompact_unitShell : IsCompact unitShell := by
  refine (isCompact_closedBall (0 : ℍ[ℝ]) 1).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro q hq
    simpa using hq.2
theorem ne_zero_of_mem_unitShell {q : ℍ[ℝ]} (hq : q ∈ unitShell) : q ≠ 0 := by
  intro h
  have := hq.1
  simp [h] at this
  linarith
theorem exists_iteratedFDeriv_quatNorm_le (j : ℕ) :
    ∃ C : ℝ, ∀ q ∈ unitShell, ‖iteratedFDeriv ℝ j quatNorm q‖ ≤ C := by
  have hc : ContinuousOn (fun q : ℍ[ℝ] => ‖iteratedFDeriv ℝ j quatNorm q‖) unitShell := by
    intro q hq
    have h1 : ContDiffAt ℝ 0 (iteratedFDeriv ℝ j quatNorm) q :=
      (contDiffAt_quatNorm (ne_zero_of_mem_unitShell hq)).iteratedFDeriv_right (m := 0) (i := j) (by
        simp only [zero_add]
        exact natCast_le_smoothTop j)
    have h5 : ContinuousAt (fun q : ℍ[ℝ] => ‖iteratedFDeriv ℝ j quatNorm q‖) q :=
      ContinuousAt.comp (f := iteratedFDeriv ℝ j quatNorm) (g := fun A => ‖A‖)
        (continuous_norm (E := ContinuousMultilinearMap ℝ (fun _ : Fin j => ℍ[ℝ]) ℝ)).continuousAt
        h1.continuousAt
    exact h5.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_unitShell.exists_bound_of_continuousOn hc
  exact ⟨C, fun q hq => (le_abs_self _).trans (by simpa using hC q hq)⟩
theorem haarGapOfNormNearOne_of_contDiff_of_derivBound (hs : HaarGapContDiff)
    (hd : HaarGapDerivBound) : HaarGapOfNormNearOne := by
  obtain ⟨Cn1, hn1⟩ := exists_iteratedFDeriv_quatNorm_le 1
  obtain ⟨Cn2, hn2⟩ := exists_iteratedFDeriv_quatNorm_le 2
  obtain ⟨C1, hC1⟩ := hd 1 le_rfl
  obtain ⟨C2, hC2⟩ := hd 2 (by norm_num)
  set N : ℝ := |Cn1| + |Cn2| + 1 with hN
  set D : ℝ := 2 * |C1| + 4 * |C2| + 1 with hDd
  have hNpos : 0 < N := by positivity
  have hDpos : 0 < D := by positivity
  refine ⟨D * N * (N + 1) + D * N * N * N, by positivity, ?_⟩
  intro P _ _ M A hA hM h1 h2
  have hq : M 0 ∈ unitShell := ⟨h1, h2⟩
  have hne : M 0 ≠ 0 := ne_zero_of_mem_unitShell hq
  have hn3 : ContDiffAt ℝ 3 quatNorm (M 0) :=
    (contDiffAt_quatNorm hne).of_le (by exact_mod_cast natCast_le_smoothTop 3)
  set p : P → ℝ := quatNorm ∘ M with hp
  have hpc : ContDiffAt ℝ 3 p 0 := ContDiffAt.comp 0 hn3 hM
  have hp0 : p 0 = ‖M 0‖ := rfl
  have hs3 : ContDiff ℝ 3 haarGap := hs
  set φ : ℝ → ℝ := fun r => haarGap (A * r) - haarGap A with hφ
  have hφc : ContDiff ℝ 3 φ := (hs3.comp (contDiff_const.mul contDiff_id)).sub contDiff_const
  have hgeq : (fun ζ => haarGap (A * ‖M ζ‖) - haarGap A) = φ ∘ p := rfl
  rw [hgeq]
  have hgc : ContDiffAt ℝ 3 (φ ∘ p) 0 := ContDiffAt.comp 0 hφc.contDiffAt hpc
  refine ⟨hgc, fun u v => ?_⟩
  have hω1 : Differentiable ℝ haarGap := hs3.differentiable (by norm_num)
  have hω2 : ContDiff ℝ 2 (deriv haarGap) := by
    have h2 : ContDiff ℝ 2 (fderiv ℝ haarGap) := hs3.fderiv_right (by norm_num)
    have e : deriv haarGap = fun x => fderiv ℝ haarGap x 1 := rfl
    rw [e]
    exact h2.clm_apply contDiff_const
  have hω2d : Differentiable ℝ (deriv haarGap) := hω2.differentiable (by norm_num)
  have hφ1 : ∀ r, HasDerivAt φ (A * deriv haarGap (A * r)) r := by
    intro r
    have h3 : HasDerivAt (fun r => A * r) A r := by
      simpa using (hasDerivAt_id r).const_mul A
    have h4 := ((hω1 (A * r)).hasDerivAt.comp r h3).sub_const (haarGap A)
    refine h4.congr_deriv ?_
    ring
  have hdφ : deriv φ = fun r => A * deriv haarGap (A * r) := funext fun r => (hφ1 r).deriv
  have hφ2 : ∀ r, HasDerivAt (deriv φ) (A ^ 2 * deriv (deriv haarGap) (A * r)) r := by
    intro r
    rw [hdφ]
    have h3 : HasDerivAt (fun r => A * r) A r := by
      simpa using (hasDerivAt_id r).const_mul A
    have h4 := ((hω2d (A * r)).hasDerivAt.comp r h3).const_mul A
    refine h4.congr_deriv ?_
    ring
  set r₀ : ℝ := p 0 with hr₀
  have hr1 : 1 / 2 ≤ r₀ := h1
  have hs1 : 1 ≤ A * r₀ := by nlinarith
  have hA0 : 0 < A := by linarith
  have hb1 : |deriv φ r₀| ≤ D := by
    rw [hdφ]
    have h3 := hC1 (A * r₀) hs1
    rw [pow_one, iteratedDeriv_one, abs_mul, abs_of_pos (by positivity : 0 < A * r₀)] at h3
    have h4 : A * |deriv haarGap (A * r₀)| ≤ 2 * C1 := by
      have : A * r₀ * |deriv haarGap (A * r₀)| ≥ A * (1 / 2) * |deriv haarGap (A * r₀)| := by
        have := abs_nonneg (deriv haarGap (A * r₀))
        have h5 : A * (1 / 2) ≤ A * r₀ := by nlinarith
        exact mul_le_mul_of_nonneg_right h5 this
      linarith
    simp only []
    rw [abs_mul, abs_of_pos hA0]
    have := le_abs_self C1
    have := abs_nonneg C2
    linarith [hDd]
  have hb2 : |A ^ 2 * deriv (deriv haarGap) (A * r₀)| ≤ D := by
    have h3 := hC2 (A * r₀) hs1
    have h6 : iteratedDeriv 2 haarGap = deriv (deriv haarGap) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [h6, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (A * r₀) ^ 2)] at h3
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ A ^ 2)]
    have h7 : A ^ 2 * (1 / 4) ≤ (A * r₀) ^ 2 := by
      have : (1 / 2 : ℝ) ^ 2 ≤ r₀ ^ 2 := pow_le_pow_left₀ (by norm_num) hr1 2
      rw [mul_pow]
      nlinarith [sq_nonneg A]
    have h8 := mul_le_mul_of_nonneg_right h7 (abs_nonneg (deriv (deriv haarGap) (A * r₀)))
    have := le_abs_self C2
    have := abs_nonneg C1
    linarith [hDd]
  have hnb1 : ‖fderiv ℝ quatNorm (M 0)‖ ≤ N := by
    have h3 := hn1 (M 0) hq
    rw [norm_iteratedFDeriv_one] at h3
    linarith [le_abs_self Cn1, abs_nonneg Cn2]
  have hp1 : ∀ w : P, fderiv ℝ p 0 w = fderiv ℝ quatNorm (M 0) (fderiv ℝ M 0 w) := by
    intro w
    have d1 : DifferentiableAt ℝ M 0 := hM.differentiableAt (by norm_num)
    have d2 : DifferentiableAt ℝ quatNorm (M 0) := hn3.differentiableAt (by norm_num)
    rw [hp, fderiv_comp 0 d2 d1]
    rfl
  have hpb : ∀ w : P, |fderiv ℝ p 0 w| ≤ N * ‖fderiv ℝ M 0 w‖ := by
    intro w
    rw [hp1, ← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hnb1 (norm_nonneg _))
  have hp2 : |fderiv ℝ (fun ζ => fderiv ℝ p ζ u) 0 v| ≤
      N * (‖fderiv ℝ M 0 u‖ * ‖fderiv ℝ M 0 v‖ + ‖fderiv ℝ (fun ζ => fderiv ℝ M ζ u) 0 v‖) := by
    have h3 := fderiv_fderiv_comp_apply (Φ := quatNorm) (T := M) hn3 hM u v
    have e1 : fderiv ℝ (fderiv ℝ quatNorm) (M 0) (fderiv ℝ M 0 v) (fderiv ℝ M 0 u) =
        iteratedFDeriv ℝ 2 quatNorm (M 0) ![fderiv ℝ M 0 v, fderiv ℝ M 0 u] := by
      rw [iteratedFDeriv_two_apply]
      simp
    have h4 := (iteratedFDeriv ℝ 2 quatNorm (M 0)).le_opNorm ![fderiv ℝ M 0 v, fderiv ℝ M 0 u]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h4
    have h5 : ‖iteratedFDeriv ℝ 2 quatNorm (M 0)‖ ≤ N := by
      have := hn2 (M 0) hq
      linarith [le_abs_self Cn2, abs_nonneg Cn1]
    have n3 := norm_nonneg (fderiv ℝ (fun ζ => fderiv ℝ M ζ u) 0 v)
    have h6 : ‖fderiv ℝ quatNorm (M 0) (fderiv ℝ (fun ζ => fderiv ℝ M ζ u) 0 v)‖ ≤
        N * ‖fderiv ℝ (fun ζ => fderiv ℝ M ζ u) 0 v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hnb1 n3)
    have h7 : ‖iteratedFDeriv ℝ 2 quatNorm (M 0) ![fderiv ℝ M 0 v, fderiv ℝ M 0 u]‖ ≤
        N * (‖fderiv ℝ M 0 v‖ * ‖fderiv ℝ M 0 u‖) :=
      h4.trans (mul_le_mul_of_nonneg_right h5 (by positivity))
    rw [hp, h3, e1, ← Real.norm_eq_abs]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ N * (‖fderiv ℝ M 0 v‖ * ‖fderiv ℝ M 0 u‖) +
          N * ‖fderiv ℝ (fun ζ => fderiv ℝ M ζ u) 0 v‖ := add_le_add h7 h6
      _ = _ := by ring
  have hev : ∀ᶠ ζ in 𝓝 (0 : P), DifferentiableAt ℝ p ζ := by
    filter_upwards [hpc.eventually (by simp)] with ζ hζ using hζ.differentiableAt (by norm_num)
  have hg1 : ∀ ζ, DifferentiableAt ℝ p ζ → ∀ w : P,
      fderiv ℝ (φ ∘ p) ζ w = deriv φ (p ζ) * fderiv ℝ p ζ w := by
    intro ζ hζ w
    have h3 := (hφ1 (p ζ)).comp_hasFDerivAt ζ hζ.hasFDerivAt
    rw [← (hφ1 (p ζ)).deriv] at h3
    rw [h3.fderiv]
    simp
  have hdp0 : DifferentiableAt ℝ p 0 := hpc.differentiableAt (by norm_num)
  have nu := norm_nonneg (fderiv ℝ M 0 u)
  constructor
  · rw [hg1 0 hdp0, abs_mul]
    have h3 := hpb u
    calc _ ≤ D * (N * ‖fderiv ℝ M 0 u‖) :=
          mul_le_mul hb1 h3 (abs_nonneg _) hDpos.le
      _ ≤ _ := by
          have : 0 ≤ D * N * N * N * ‖fderiv ℝ M 0 u‖ := by positivity
          nlinarith [mul_nonneg (mul_nonneg hDpos.le hNpos.le) nu]
  · have he : (fun ζ => fderiv ℝ (φ ∘ p) ζ u) =ᶠ[𝓝 (0 : P)]
        fun ζ => deriv φ (p ζ) * fderiv ℝ p ζ u := by
      filter_upwards [hev] with ζ hζ using hg1 ζ hζ u
    rw [he.fderiv_eq]
    have hc1 : HasFDerivAt (fun ζ => deriv φ (p ζ))
        ((A ^ 2 * deriv (deriv haarGap) (A * r₀)) • fderiv ℝ p 0) 0 :=
      (hφ2 (p 0)).comp_hasFDerivAt 0 hdp0.hasFDerivAt
    have h2p : ContDiffAt ℝ 2 (fderiv ℝ p) 0 := hpc.fderiv_right (by norm_num)
    have hdu : DifferentiableAt ℝ (fun ζ => fderiv ℝ p ζ u) 0 :=
      (h2p.differentiableAt (by norm_num)).clm_apply (differentiableAt_const u)
    have hprod := hc1.mul hdu.hasFDerivAt
    have hval : fderiv ℝ (fun ζ => deriv φ (p ζ) * fderiv ℝ p ζ u) 0 v =
        deriv φ r₀ * fderiv ℝ (fun ζ => fderiv ℝ p ζ u) 0 v +
          (A ^ 2 * deriv (deriv haarGap) (A * r₀)) * fderiv ℝ p 0 v * fderiv ℝ p 0 u := by
      have : HasFDerivAt (fun ζ => deriv φ (p ζ) * fderiv ℝ p ζ u) _ 0 := hprod
      rw [this.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hval]
    have h3 := hpb u
    have h4 := hpb v
    have a1 : |deriv φ r₀ * fderiv ℝ (fun ζ => fderiv ℝ p ζ u) 0 v| ≤
        D * (N * (‖fderiv ℝ M 0 u‖ * ‖fderiv ℝ M 0 v‖ + ‖fderiv ℝ (fun ζ => fderiv ℝ M ζ u) 0 v‖)) := by
      rw [abs_mul]
      exact mul_le_mul hb1 hp2 (abs_nonneg _) hDpos.le
    have a2 : |(A ^ 2 * deriv (deriv haarGap) (A * r₀)) * fderiv ℝ p 0 v * fderiv ℝ p 0 u| ≤
        D * (N * ‖fderiv ℝ M 0 v‖) * (N * ‖fderiv ℝ M 0 u‖) := by
      rw [abs_mul, abs_mul]
      have b1 : |A ^ 2 * deriv (deriv haarGap) (A * r₀)| * |fderiv ℝ p 0 v| ≤
          D * (N * ‖fderiv ℝ M 0 v‖) := mul_le_mul hb2 h4 (abs_nonneg _) hDpos.le
      exact mul_le_mul b1 h3 (abs_nonneg _) (by positivity)
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ D * (N * (‖fderiv ℝ M 0 u‖ * ‖fderiv ℝ M 0 v‖ + ‖fderiv ℝ (fun ζ => fderiv ℝ M ζ u) 0 v‖)) +
          D * (N * ‖fderiv ℝ M 0 v‖) * (N * ‖fderiv ℝ M 0 u‖) := add_le_add a1 a2
      _ ≤ _ := by
          set P₁ : ℝ := ‖fderiv ℝ M 0 u‖ * ‖fderiv ℝ M 0 v‖ with hP₁
          set S₁ : ℝ := ‖fderiv ℝ (fun ζ => fderiv ℝ M ζ u) 0 v‖ with hS₁
          have t1 : 0 ≤ D * N * N * N * (P₁ + S₁) + D * N * N * S₁ := by positivity
          have e : (D * N * (N + 1) + D * N * N * N) * (P₁ + S₁) -
              (D * (N * (P₁ + S₁)) + D * (N * ‖fderiv ℝ M 0 v‖) * (N * ‖fderiv ℝ M 0 u‖)) =
              D * N * N * N * (P₁ + S₁) + D * N * N * S₁ := by
            rw [hP₁]
            ring
          linarith
end NormNearOne
end ColdStepAtMirrorFrames
end YangMills.Construction
end
