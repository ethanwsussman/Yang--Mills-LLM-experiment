import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Towers.TaylorExpansionOfTheEntriesAlongAField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies.TaylorAlongField
section Ray
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
theorem norm_iteratedDeriv_comp_smul_le {Q : V → ℂ} {v : V} {C : ℝ} (hQ : ContDiff ℝ 3 Q)
    (hbd : ∀ k : ℕ, k ≤ 3 → ∀ φ, ‖iteratedFDeriv ℝ k Q φ‖ ≤ C) (k : ℕ) (hk : k ≤ 3) (t : ℝ) :
    ‖iteratedDeriv k (fun s : ℝ => Q (s • v)) t‖ ≤ C * ‖v‖ ^ k := by
  let L : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hL : ∀ s : ℝ, L s = s • v := fun s => by simp [L]
  have hcomp : (fun s : ℝ => Q (s • v)) = Q ∘ L := by
    funext s
    simp [hL]
  have hk' : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  rw [iteratedDeriv_eq_iteratedFDeriv, hcomp, L.iteratedFDeriv_comp_right hQ t hk',
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hone : L 1 = v := by simp [hL]
  calc _ ≤ ‖iteratedFDeriv ℝ k Q (L t)‖ *
        ∏ i : Fin k, ‖(fun _ : Fin k => (L : ℝ →L[ℝ] V)) i ((fun _ : Fin k => (1 : ℝ)) i)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ k Q (L t)‖ * ‖v‖ ^ k := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hone]
    _ ≤ C * ‖v‖ ^ k := by
        gcongr
        exact hbd k hk _
theorem norm_sub_le_mul_abs_pow_of_deriv_le {F F' : ℝ → ℂ} (hF : ∀ t, HasDerivAt F (F' t) t)
    {K : ℝ} (hK : 0 ≤ K) {n : ℕ} (hbd : ∀ t, ‖F' t‖ ≤ K * |t| ^ n) (t : ℝ) :
    ‖F t - F 0‖ ≤ K * |t| ^ (n + 1) := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := F) (f' := F')
    (s := Metric.closedBall (0 : ℝ) |t|) (C := K * |t| ^ n) (x := 0) (y := t)
    (fun x _ => (hF x).hasDerivWithinAt)
    (fun x hx => by
      have hx' : |x| ≤ |t| := by simpa [Real.norm_eq_abs] using hx
      exact (hbd x).trans (by gcongr))
    (convex_closedBall _ _) (by simp) (by simp [Real.norm_eq_abs])
  calc ‖F t - F 0‖ ≤ K * |t| ^ n * ‖t - 0‖ := h
    _ = K * |t| ^ (n + 1) := by
      rw [sub_zero, Real.norm_eq_abs, pow_succ]
      ring
theorem quadraticTaylor_along_ray {Q : V → ℂ} {C : ℝ} (hC : 0 ≤ C) (hQ : ContDiff ℝ 3 Q)
    (hbd : ∀ k : ℕ, k ≤ 3 → ∀ φ, ‖iteratedFDeriv ℝ k Q φ‖ ≤ C) (v : V) :
    ‖deriv (fun s : ℝ => Q (s • v)) 0‖ ≤ C * ‖v‖ ∧
    ‖deriv (deriv (fun s : ℝ => Q (s • v))) 0‖ ≤ C * ‖v‖ ^ 2 ∧
    ∀ s : ℝ, ‖Q (s • v) - Q ((0 : ℝ) • v) - (s : ℂ) * deriv (fun s : ℝ => Q (s • v)) 0 -
        ((1 / 2 * s ^ 2 : ℝ) : ℂ) * deriv (deriv (fun s : ℝ => Q (s • v))) 0‖ ≤
      C * ‖v‖ ^ 3 * |s| ^ 3 := by
  set g : ℝ → ℂ := fun s : ℝ => Q (s • v) with hg
  have hgc : ContDiff ℝ 3 g := hQ.comp (contDiff_id.smul contDiff_const)
  have e1 : iteratedDeriv 1 g = deriv g := iteratedDeriv_one
  have e2 : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [iteratedDeriv_succ, e1]
  have e3 : iteratedDeriv 3 g = deriv (deriv (deriv g)) := by
    rw [iteratedDeriv_succ, e2]
  have d0 : Differentiable ℝ g := hgc.differentiable (by norm_num)
  have d1 : Differentiable ℝ (deriv g) := by
    rw [← e1]
    exact hgc.differentiable_iteratedDeriv 1 (by norm_num)
  have d2 : Differentiable ℝ (deriv (deriv g)) := by
    rw [← e2]
    exact hgc.differentiable_iteratedDeriv 2 (by norm_num)
  have b1 : ∀ t, ‖deriv g t‖ ≤ C * ‖v‖ := fun t => by
    have := norm_iteratedDeriv_comp_smul_le hQ hbd (v := v) 1 (by norm_num) t
    rwa [← hg, e1, pow_one] at this
  have b2 : ∀ t, ‖deriv (deriv g) t‖ ≤ C * ‖v‖ ^ 2 := fun t => by
    have := norm_iteratedDeriv_comp_smul_le hQ hbd (v := v) 2 (by norm_num) t
    rwa [← hg, e2] at this
  have b3 : ∀ t, ‖deriv (deriv (deriv g)) t‖ ≤ C * ‖v‖ ^ 3 := fun t => by
    have := norm_iteratedDeriv_comp_smul_le hQ hbd (v := v) 3 (by norm_num) t
    rwa [← hg, e3] at this
  refine ⟨b1 0, b2 0, fun s => ?_⟩
  have hM : 0 ≤ C * ‖v‖ ^ 3 := by positivity
  have s2 : ∀ t, ‖deriv (deriv g) t - deriv (deriv g) 0‖ ≤ C * ‖v‖ ^ 3 * |t| ^ 1 :=
    norm_sub_le_mul_abs_pow_of_deriv_le (n := 0) (fun t => (d2 t).hasDerivAt) hM
      (fun t => by simpa using b3 t)
  let r1 : ℝ → ℂ := fun t => deriv g t - deriv g 0 - t • deriv (deriv g) 0
  have hr1 : ∀ t, HasDerivAt r1 (deriv (deriv g) t - deriv (deriv g) 0) t := fun t => by
    have := ((d1 t).hasDerivAt.sub_const (deriv g 0)).sub
      ((hasDerivAt_id t).smul_const (deriv (deriv g) 0))
    exact this.congr_deriv (by simp)
  have s1 : ∀ t, ‖r1 t - r1 0‖ ≤ C * ‖v‖ ^ 3 * |t| ^ 2 :=
    norm_sub_le_mul_abs_pow_of_deriv_le (n := 1) hr1 hM s2
  have z1 : r1 0 = 0 := by simp [r1]
  let r0 : ℝ → ℂ := fun t => g t - g 0 - t • deriv g 0 - (1 / 2 * t ^ 2) • deriv (deriv g) 0
  have hr0 : ∀ t, HasDerivAt r0 (r1 t) t := fun t => by
    have hq : HasDerivAt (fun u : ℝ => 1 / 2 * u ^ 2) t t := by
      have := ((hasDerivAt_id t).pow 2).const_mul (1 / 2 : ℝ)
      simpa using this
    have := (((d0 t).hasDerivAt.sub_const (g 0)).sub
      ((hasDerivAt_id t).smul_const (deriv g 0))).sub (hq.smul_const (deriv (deriv g) 0))
    exact this.congr_deriv (by simp [r1])
  have s0 := norm_sub_le_mul_abs_pow_of_deriv_le (n := 2) hr0 hM (fun t => by
    have := s1 t
    rwa [z1, sub_zero] at this) s
  have z0 : r0 0 = 0 := by simp [r0]
  rw [z0, sub_zero] at s0
  have hs : r0 s = g s - g 0 - (s : ℂ) * deriv g 0 -
      ((1 / 2 * s ^ 2 : ℝ) : ℂ) * deriv (deriv g) 0 := by
    simp only [r0, Complex.real_smul]
  rw [hs] at s0
  exact s0
end Ray
theorem euclidNormVec_add_le (u w : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (u + w) ≤
      TorusMetric.euclidNormVec u + TorusMetric.euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem variationKernels_bounds {J B : Type} {pos : J → InfiniteLattice.AmbientSpace}
    {src : B → InfiniteLattice.AmbientSpace} {C : ℝ}
    {T : (B → ℝ) → OneLoopNotation.BddOp (IndexL2 J)}
    (hC : 0 < C) (hfam : IsLocallySmoothFamily pos src C T) {ξ : B → ℝ}
    (hξ : ∀ b, |ξ b| ≤ 2 + TorusMetric.euclidNormVec (src b)) (i j : J) :
    ‖firstVariationKernel T ξ i j‖ ≤ 4 * C * (1 + TorusMetric.euclidNormVec (pos i)) ^ 3 ∧
    ‖secondVariationKernel T ξ i j‖ ≤ 16 * C * (1 + TorusMetric.euclidNormVec (pos i)) ^ 3 ∧
    ∀ s : ℝ, ‖taylorRemainderKernel T ξ s i j‖ ≤
      64 * C * |s| ^ 3 * (1 + TorusMetric.euclidNormVec (pos i)) ^ 3 := by
  obtain ⟨E, Q, hE, hQ, hQb, hQe⟩ := hfam.entry_smooth i j
  set r := TorusMetric.euclidNormVec (pos i) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  let v : E → ℝ := fun b => ξ b.1
  have hg : entryAlong T ξ i j = fun s : ℝ => Q (s • v) := by
    funext s
    simp only [entryAlong]
    rw [hQe]
    rfl
  have hu : (1 : ℝ) ≤ 1 + r := by linarith
  have hv : ‖v‖ ≤ 4 * (1 + r) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
    have h1 := hE b.1 b.2
    have h2 := euclidNormVec_add_le (src b.1 - pos i) (pos i)
    rw [sub_add_cancel] at h2
    have h3 := hξ b.1
    rw [Real.norm_eq_abs]
    show |ξ b.1| ≤ _
    linarith
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
  obtain ⟨k1, k2, k3⟩ := quadraticTaylor_along_ray hC.le hQ hQb v
  have p2 : (1 + r) ^ 2 ≤ (1 + r) ^ 3 := pow_le_pow_right₀ hu (by norm_num)
  have p1 : (1 + r) ≤ (1 + r) ^ 3 := le_self_pow₀ hu (by norm_num)
  refine ⟨?_, ?_, fun s => ?_⟩
  · simp only [firstVariationKernel, hg]
    calc _ ≤ C * ‖v‖ := k1
      _ ≤ C * (4 * (1 + r)) := by gcongr
      _ ≤ C * (4 * (1 + r) ^ 3) := by gcongr
      _ = _ := by ring
  · simp only [secondVariationKernel, hg]
    calc _ ≤ C * ‖v‖ ^ 2 := k2
      _ ≤ C * (4 * (1 + r)) ^ 2 := by gcongr
      _ = 16 * C * (1 + r) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · simp only [taylorRemainderKernel, firstVariationKernel, secondVariationKernel, hg]
    calc _ ≤ C * ‖v‖ ^ 3 * |s| ^ 3 := k3 s
      _ ≤ C * (4 * (1 + r)) ^ 3 * |s| ^ 3 := by gcongr
      _ = _ := by ring
theorem taylorKernels_cubicGrowth_holds : taylorKernels_cubicGrowth := by
  intro J B pos src m m' z C T _ hC hset ξ hξ
  have hfam := hset.family
  have hzero : ∀ i j, ¬ TorusMetric.euclidNormVec (pos i - pos j) ≤ 2 →
      entryAlong T ξ i j = fun _ => 0 :=
    fun i j h => funext fun s => hfam.finite_range _ i j h
  have hk := variationKernels_bounds hC hfam hξ
  refine ⟨⟨fun i j h => ?_, fun i j => (hk i j).1⟩,
    ⟨fun i j h => ?_, fun i j => (hk i j).2.1⟩, fun s => ⟨fun i j h => ?_, fun i j => (hk i j).2.2 s⟩⟩
  · simp [firstVariationKernel, hzero i j h]
  · simp [secondVariationKernel, hzero i j h]
  · simp [taylorRemainderKernel, firstVariationKernel, secondVariationKernel, hzero i j h]
end YangMills.Construction.Tower.LocalFamilies.TaylorAlongField
end
