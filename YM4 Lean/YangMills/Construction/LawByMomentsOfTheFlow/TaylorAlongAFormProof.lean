import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.LawByMomentsOfTheFlow.TaylorAlongAForm
import YangMills.Construction.LawInAState.SecondOrderOfAFunctionOfTheFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TorusFields BlockAverages WeightedResponses
section Calculus
private theorem contDiffAt_deriv_of_succ {f : ℝ → ℝ} {v : ℝ} {m : ℕ} (h : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f v) :
    ContDiffAt ℝ (m : WithTop ℕ∞) (deriv f) v := by
  have h1 : ContDiffAt ℝ (m : WithTop ℕ∞) (fderiv ℝ f) v := h.fderiv_right (by norm_cast)
  exact show ContDiffAt ℝ (m : WithTop ℕ∞) (fun x => fderiv ℝ f x (1 : ℝ)) v from h1.clm_apply contDiffAt_const
private theorem hasDerivAt_deriv_of_contDiffAt {f : ℝ → ℝ} {v : ℝ} {m : ℕ} (h : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f v) :
    HasDerivAt f (deriv f v) v :=
  (h.differentiableAt (by simp)).hasDerivAt
private theorem abs_taylor_remainder_three_le {f : ℝ → ℝ} {M : ℝ} (hf : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) f v)
    (hM : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → |iteratedDeriv 3 f v| ≤ M) :
    |f 1 - f 0 - iteratedDeriv 1 f 0 - 1 / 2 * iteratedDeriv 2 f 0| ≤ M := by
  have e1 : iteratedDeriv 1 f = deriv f := by simp [iteratedDeriv_succ]
  have e2 : iteratedDeriv 2 f = deriv (deriv f) := by simp [iteratedDeriv_succ]
  have e3 : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by simp [iteratedDeriv_succ]
  rw [e1, e2]
  rw [e3] at hM
  have c0 : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (deriv f v) v := fun v hv =>
    hasDerivAt_deriv_of_contDiffAt (m := 2) (hf v hv.1 hv.2)
  have c1 : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (deriv f) (deriv (deriv f) v) v := fun v hv =>
    hasDerivAt_deriv_of_contDiffAt (m := 1) (contDiffAt_deriv_of_succ (m := 2) (hf v hv.1 hv.2))
  have c2 : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) v) v := fun v hv =>
    hasDerivAt_deriv_of_contDiffAt (m := 0) (contDiffAt_deriv_of_succ (m := 1) (contDiffAt_deriv_of_succ (m := 2) (hf v hv.1 hv.2)))
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 le_rfl zero_le_one)
  have z0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have z1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have b2 : ∀ v ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv f) v - deriv (deriv f) 0| ≤ M := by
    intro v hv
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := deriv (deriv f))
      (f' := deriv (deriv (deriv f))) (C := M) (s := Set.Icc (0 : ℝ) 1) (x := 0) (y := v)
      (fun u hu => (c2 u hu).hasDerivWithinAt) (fun u hu => by simpa using hM u hu.1 hu.2) (convex_Icc 0 1) z0 hv
    simp only [Real.norm_eq_abs, sub_zero] at this
    calc _ ≤ M * |v| := this
      _ ≤ M * 1 := by
        apply mul_le_mul_of_nonneg_left _ hM0
        rw [abs_of_nonneg hv.1]; exact hv.2
      _ = M := mul_one M
  have b1 : ∀ v ∈ Set.Icc (0 : ℝ) 1, |deriv f v - deriv f 0 - v * deriv (deriv f) 0| ≤ M := by
    intro v hv
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => deriv f u - u * deriv (deriv f) 0)
      (f' := fun u => deriv (deriv f) u - deriv (deriv f) 0) (C := M) (s := Set.Icc (0 : ℝ) 1) (x := 0) (y := v)
      (fun u hu => by
        have h : HasDerivAt (fun u => deriv f u - u * deriv (deriv f) 0)
            (deriv (deriv f) u - 1 * deriv (deriv f) 0) u :=
          (c1 u hu).sub ((hasDerivAt_id' u).mul_const (deriv (deriv f) 0))
        rw [one_mul] at h
        exact h.hasDerivWithinAt)
      (fun u hu => by simpa using b2 u hu) (convex_Icc 0 1) z0 hv
    simp only [Real.norm_eq_abs, sub_zero, zero_mul] at this
    calc |deriv f v - deriv f 0 - v * deriv (deriv f) 0|
        = |deriv f v - v * deriv (deriv f) 0 - deriv f 0| := by ring_nf
      _ ≤ M * |v| := this
      _ ≤ M * 1 := by
        apply mul_le_mul_of_nonneg_left _ hM0
        rw [abs_of_nonneg hv.1]; exact hv.2
      _ = M := mul_one M
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => f u - u * deriv f 0 - u ^ 2 / 2 * deriv (deriv f) 0)
    (f' := fun u => deriv f u - deriv f 0 - u * deriv (deriv f) 0) (C := M) (s := Set.Icc (0 : ℝ) 1) (x := 0) (y := 1)
    (fun u hu => by
      have h3 : HasDerivAt (fun u : ℝ => u ^ 2 / 2 * deriv (deriv f) 0) (u * deriv (deriv f) 0) u := by
        exact (((hasDerivAt_pow 2 u)).div_const 2).mul_const (deriv (deriv f) 0) |>.congr_deriv (by norm_num <;> ring)
      have h : HasDerivAt (fun u => f u - u * deriv f 0 - u ^ 2 / 2 * deriv (deriv f) 0)
          (deriv f u - 1 * deriv f 0 - u * deriv (deriv f) 0) u :=
        ((c0 u hu).sub ((hasDerivAt_id' u).mul_const (deriv f 0))).sub h3
      rw [one_mul] at h
      exact h.hasDerivWithinAt)
    (fun u hu => by simpa using b1 u hu) (convex_Icc 0 1) z0 z1
  simp only [Real.norm_eq_abs, sub_zero] at this
  norm_num at this
  have e : f 1 - f 0 - deriv f 0 - 1 / 2 * deriv (deriv f) 0 = f 1 - deriv f 0 - 1 / 2 * deriv (deriv f) 0 - f 0 := by ring
  rw [e]
  exact this
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
private theorem iteratedFDeriv_comp_clm_of_contDiffAt {f : E → ℝ} (g : F →L[ℝ] E) {x : F} {j : ℕ} (hj : j ≤ 3)
    (hf : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) f (g x)) :
    iteratedFDeriv ℝ j (f ∘ g) x = (iteratedFDeriv ℝ j f (g x)).compContinuousLinearMap fun _ => g := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := ((3 : ℕ) : WithTop ℕ∞)) le_rfl (by simp)
  obtain ⟨s, hsu, hso, hxs⟩ := mem_nhds_iff.1 hu
  have hfs := hfu.mono hsu
  have hs' : IsOpen (g ⁻¹' s) := hso.preimage g.continuous
  have h := g.iteratedFDerivWithin_comp_right hfs hso.uniqueDiffOn hs'.uniqueDiffOn hxs (i := j) (by exact_mod_cast hj)
  have e1 : iteratedFDerivWithin ℝ j (f ∘ g) (g ⁻¹' s) x = iteratedFDeriv ℝ j (f ∘ g) x :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f ∘ g) j hs' hxs
  have e2 : iteratedFDerivWithin ℝ j f s (g x) = iteratedFDeriv ℝ j f (g x) :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) j hso hxs
  rw [← e1, h, e2]
private theorem multilinear_apply_const_eq_sum {k j : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin k → ℝ) ℝ)
    (a : Fin k → ℝ) :
    f (fun _ => a) = ∑ l : Fin j → Fin k, (∏ m, a (l m)) * f (fun m => Pi.single (l m) 1) := by apply _root_.YangMills.SharedProofs.p104744 <;> assumption
end Calculus
section Fields
variable {n : ℕ} [NeZero n]
private theorem norm_unitGenerator : ‖unitGenerator‖ = 1 := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.norm_unitGenerator <;> assumption
private def unitDirection (w : imaginaryQuaternions) : imaginaryQuaternions :=
  open Classical in if w = 0 then unitGenerator else (‖w‖⁻¹ : ℝ) • w
private theorem norm_unitDirection (w : imaginaryQuaternions) : ‖unitDirection w‖ = 1 := by
  unfold unitDirection
  split_ifs with h
  · exact norm_unitGenerator
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 h)
private theorem norm_smul_unitDirection (w : imaginaryQuaternions) : ‖w‖ • unitDirection w = w := by
  unfold unitDirection
  split_ifs with h
  · simp [h]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_smul]
private theorem expUnit_zero_eq_one : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem expUnit_smul_mul_expUnit_smul (s t : ℝ) (X : imaginaryQuaternions) :
    expUnit (s • X) * expUnit (t • X) = expUnit ((s + t) • X) := by
  apply Subtype.ext
  show NormedSpace.exp ((s • X : imaginaryQuaternions) : Quaternion ℝ) * NormedSpace.exp ((t • X : imaginaryQuaternions) : Quaternion ℝ) =
    NormedSpace.exp (((s + t) • X : imaginaryQuaternions) : Quaternion ℝ)
  have hc : Commute ((s • X : imaginaryQuaternions) : Quaternion ℝ) ((t • X : imaginaryQuaternions) : Quaternion ℝ) := by
    simp only [Submodule.coe_smul]
    exact ((Commute.refl _).smul_left s).smul_right t
  letI : NormedAlgebra ℚ (Quaternion ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  rw [← NormedSpace.exp_add_of_commute hc]
  congr 1
  simp [add_smul]
variable {k : ℕ} (e : Fin k ≃ TorusBond n) (X : Fin k → imaginaryQuaternions)
private theorem perturb_apply (σ : Fin k → ℝ) (W : TorusField n) (x : TorusSite n) (i : Fin 4) :
    perturb e X σ W x i = expUnit (σ (e.symm (x, i)) • X (e.symm (x, i))) * W x i := by
  unfold perturb
  congr 2
  rw [Finset.sum_eq_single (e.symm (x, i))]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (by rw [← h]; simp)
  · simp
private theorem perturb_of_zero (W : TorusField n) : perturb e X 0 W = W := by
  funext x i
  rw [perturb_apply]
  simp [expUnit_zero_eq_one]
variable {e X}
private theorem perturb_expField {B : TorusBond n → imaginaryQuaternions} {a : Fin k → ℝ}
    (hX : ∀ l, a l • X l = B (e l)) (v : ℝ)
    (σ : Fin k → ℝ) : perturb e X σ (expField v B) = perturb e X (σ + v • a) (trivialField n) := by
  funext x i
  rw [perturb_apply, perturb_apply]
  have h : B (x, i) = a (e.symm (x, i)) • X (e.symm (x, i)) := by rw [hX]; simp
  simp only [expField, trivialField, mul_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h, smul_smul, expUnit_smul_mul_expUnit_smul]
variable (e X)
private def alongPerturb (G : TorusField n → ℝ) (W : TorusField n) (σ : Fin k → ℝ) : ℝ := G (perturb e X σ W)
variable {e X}
private def collect {j : ℕ} (l : Fin j → Fin k) : (Fin j → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun p => ∑ m, if l m = p then ContinuousLinearMap.proj m else 0
private theorem collect_apply {j : ℕ} (l : Fin j → Fin k) (τ : Fin j → ℝ) (p : Fin k) :
    collect l τ p = ∑ m, if l m = p then τ m else 0 := by
  simp only [collect, ContinuousLinearMap.coe_pi', ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp
private theorem collect_single {j : ℕ} (l : Fin j → Fin k) (m : Fin j) :
    collect l (Pi.single m 1) = Pi.single (l m) 1 := by
  ext p
  rw [collect_apply, Finset.sum_eq_single m]
  · by_cases h : l m = p
    · subst h; simp
    · rw [if_neg h, Pi.single_apply, if_neg (Ne.symm h)]
  · intro b _ hb
    split_ifs <;> simp [hb]
  · simp
private theorem perturb_comp_eq_perturb_collect {j : ℕ} (l : Fin j → Fin k) (τ : Fin j → ℝ) (W : TorusField n) :
    perturb (fun m => e (l m)) (fun m => X (l m)) τ W = perturb e X (collect l τ) W := by
  funext x i
  rw [perturb_apply]
  unfold perturb
  congr 2
  rw [collect_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : l m = e.symm (x, i)
  · have h' : e (l m) = (x, i) := by rw [h]; simp
    rw [if_pos h, if_pos h']
    show τ m • X (l m) = τ m • X (e.symm (x, i))
    rw [h]
  · have h' : ¬ e (l m) = (x, i) := fun h' => h (by rw [← h']; simp)
    rw [if_neg h, if_neg h', zero_smul]
private theorem mixedDeriv_eq_iteratedFDeriv (G : TorusField n → ℝ) (W : TorusField n) {j : ℕ} (hj : j ≤ 3)
    (l : Fin j → Fin k)
    (hc : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (alongPerturb e X G W) 0) :
    mixedDeriv G W (fun m => e (l m)) (fun m => X (l m)) =
      iteratedFDeriv ℝ j (alongPerturb e X G W) 0 (fun m => Pi.single (l m) 1) := by
  have h0 : collect l 0 = (0 : Fin k → ℝ) := map_zero _
  have hf : (fun τ : Fin j → ℝ => G (perturb (fun m => e (l m)) (fun m => X (l m)) τ W)) =
      alongPerturb e X G W ∘ collect l := by
    funext τ
    simp only [Function.comp, alongPerturb]
    rw [perturb_comp_eq_perturb_collect]
  unfold mixedDeriv
  rw [hf, iteratedFDeriv_comp_clm_of_contDiffAt (collect l) hj (by rwa [h0]), h0]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, collect_single]
end Fields
theorem taylorAlongForm : taylorAlongFormStatement := by
  intro n _ G B D hC hD hF
  obtain ⟨h1, q, -, -, hq⟩ := hF
  have hess : hessianAtIdentity G = q := by
    funext b b'
    unfold hessianAtIdentity
    rw [hq b b' unitGenerator unitGenerator]
    simp [Fin.sum_univ_three, imaginaryComponent, unitGenerator]
  rw [hess]
  set k := Fintype.card (TorusBond n) with hk
  let e : Fin k ≃ TorusBond n := (Fintype.equivFin (TorusBond n)).symm
  let X : Fin k → imaginaryQuaternions := fun l => unitDirection (B (e l))
  let a : Fin k → ℝ := fun l => ‖B (e l)‖
  have hX : ∀ l, a l • X l = B (e l) := fun l => norm_smul_unitDirection _
  have hU : ∀ l, ‖X l‖ = 1 := fun l => norm_unitDirection _
  let ψ : (Fin k → ℝ) → ℝ := alongPerturb e X G (trivialField n)
  have hsh : ∀ v : ℝ, alongPerturb e X G (expField v B) = fun σ => ψ (σ + v • a) := by
    intro v
    funext σ
    simp only [alongPerturb, ψ]
    rw [perturb_expField hX]
  have hfield : ∀ v : ℝ, G (expField v B) = ψ (v • a) := by
    intro v
    have := congrFun (hsh v) 0
    simpa [alongPerturb, perturb_of_zero] using this
  have hcv : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (alongPerturb e X G (expField v B)) 0 := by
    intro v h0 h1
    have := hC v h0 h1 k e X
    rw [show ((3 : ℕ) : WithTop ℕ∞) = 3 from rfl]
    exact this
  have hψ : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) ψ (v • a) := by
    intro v h0 h1
    have h2 := hcv v h0 h1
    rw [hsh] at h2
    have h3 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun σ : Fin k → ℝ => σ - v • a) (v • a) :=
      contDiffAt_id.sub contDiffAt_const
    have h4 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun σ : Fin k → ℝ => σ - v • a) (v • a) := h3
    have h5 := ContDiffAt.comp (v • a) (g := fun σ => ψ (σ + v • a)) (f := fun σ : Fin k → ℝ => σ - v • a)
      (by simpa using h2) h4
    refine h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun σ => ?_)
    simp
  let g : ℝ →L[ℝ] (Fin k → ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight a
  have hg : ∀ v, g v = v • a := fun v => by simp [g]
  let φ : ℝ → ℝ := ψ ∘ g
  have hφv : ∀ v, φ v = G (expField v B) := fun v => by
    simp only [φ, Function.comp, hg]
    exact (hfield v).symm
  have hφ : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) φ v := by
    intro v h0 h1
    exact ContDiffAt.comp v (by rw [hg]; exact hψ v h0 h1) g.contDiff.contDiffAt
  have hline : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ∀ j ≤ 3, iteratedDeriv j φ v =
      ∑ l : Fin j → Fin k, (∏ m, a (l m)) * iteratedFDeriv ℝ j ψ (v • a) (fun m => Pi.single (l m) 1) := by
    intro v h0 h1 j hj
    rw [iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_comp_clm_of_contDiffAt g hj (by rw [hg]; exact hψ v h0 h1), hg,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, ← multilinear_apply_const_eq_sum]
    simp [hg]
  have hat : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ∀ j, j ≤ 3 → ∀ l : Fin j → Fin k,
      iteratedFDeriv ℝ j ψ (v • a) (fun m => Pi.single (l m) 1) =
        mixedDeriv G (expField v B) (fun m => e (l m)) (fun m => X (l m)) := by
    intro v h0 h1 j hj l
    rw [mixedDeriv_eq_iteratedFDeriv G _ hj l (hcv v h0 h1), hsh]
    have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := ψ) j (v • a) (x := (0 : Fin k → ℝ))
    simp only [zero_add] at this
    rw [this]
  have f0 : expField 0 B = trivialField n := by
    funext x i
    simp [expField, trivialField, expUnit_zero_eq_one]
  have h3 : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → |iteratedDeriv 3 φ v| ≤ ∑ c : Fin 3 → TorusBond n, (∏ l, ‖B (c l)‖) * D c := by
    intro v h0 h1
    rw [hline v h0 h1 3 le_rfl]
    have e3 : ∑ c : Fin 3 → TorusBond n, (∏ l, ‖B (c l)‖) * D c =
        ∑ l : Fin 3 → Fin k, (∏ m, a (l m)) * D fun m => e (l m) :=
      (Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl (Fin 3)) e) _).symm
    rw [e3]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul, hat v h0 h1 3 le_rfl l, abs_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hD v h0 h1 _ _ fun m => hU _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have t := abs_taylor_remainder_three_le hφ h3
  have d1 : iteratedDeriv 1 φ 0 = 0 := by
    rw [hline 0 le_rfl zero_le_one 1 (by norm_num)]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hat 0 le_rfl zero_le_one 1 (by norm_num) l, f0]
    have ec : (fun m => e (l m)) = ![e (l 0)] := by
      funext m; fin_cases m; rfl
    have eX : (fun m => X (l m)) = ![X (l 0)] := by
      funext m; fin_cases m; rfl
    rw [ec, eX, h1, mul_zero]
  have d2 : iteratedDeriv 2 φ 0 = colourEval q (toColourForm B) (toColourForm B) := by
    rw [hline 0 le_rfl zero_le_one 2 (by norm_num)]
    have hterm : ∀ l : Fin 2 → Fin k, (∏ m, a (l m)) * iteratedFDeriv ℝ 2 ψ ((0 : ℝ) • a) (fun m => Pi.single (l m) 1) =
        ∑ c : Fin 3, imaginaryComponent c (B (e (l 0))) * q (e (l 0)) (e (l 1)) * imaginaryComponent c (B (e (l 1))) := by
      intro l
      rw [hat 0 le_rfl zero_le_one 2 (by norm_num) l, f0]
      have ec : (fun m => e (l m)) = ![e (l 0), e (l 1)] := by
        funext m; fin_cases m <;> rfl
      have eX : (fun m => X (l m)) = ![X (l 0), X (l 1)] := by
        funext m; fin_cases m <;> rfl
      rw [ec, eX, hq, Fin.prod_univ_two, ← hX (l 0), ← hX (l 1), Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hs : ∀ (s : ℝ) (w : imaginaryQuaternions), imaginaryComponent c (s • w) = s * imaginaryComponent c w := by
        intro s w
        fin_cases c <;> simp [imaginaryComponent]
      rw [hs, hs]
      ring
    have hE : ∀ f : TorusBond n → TorusBond n → ℝ, ∑ l : Fin 2 → Fin k, f (e (l 0)) (e (l 1)) = ∑ b, ∑ b', f b b' := by
      intro f
      rw [← Fintype.sum_prod_type' (f := fun b b' => f b b')]
      exact Equiv.sum_comp ((finTwoArrowEquiv (Fin k)).trans (Equiv.prodCongr e e)) (fun p => f p.1 p.2)
    simp only [hterm]
    rw [Finset.sum_comm]
    unfold colourEval bilinearEval toColourForm
    exact Finset.sum_congr rfl fun c _ => hE fun b b' => imaginaryComponent c (B b) * q b b' * imaginaryComponent c (B b')
  rw [hφv 1, hφv 0, f0, d1, d2] at t
  simpa using t
end YangMills.Construction.MomentLaw
end
