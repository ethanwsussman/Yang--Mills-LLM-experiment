import YangMills.Construction.Cumulants.JointCumulantsOfBoundedVariables
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.Cumulants.BoundedComplexCumulants
section IteratedDerivatives
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {f : E → ℂ}
private def dirDeriv (v : E) (f : E → ℂ) : E → ℂ := fun y => fderiv ℂ f y v
private def dirDerivList (l : List E) (f : E → ℂ) : E → ℂ := l.foldr dirDeriv f
private theorem contDiffOn_dirDeriv (hU : IsOpen U) {g : E → ℂ} (hg : ContDiffOn ℂ ∞ g U)
    (v : E) : ContDiffOn ℂ ∞ (dirDeriv v g) U :=
  (hg.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
private theorem contDiffOn_dirDerivList (hU : IsOpen U) (hf : ContDiffOn ℂ ∞ f U) (l : List E) :
    ContDiffOn ℂ ∞ (dirDerivList l f) U := by
  induction l with
  | nil => exact hf
  | cons a l ih => exact contDiffOn_dirDeriv hU ih a
private theorem dirDeriv_comm (hU : IsOpen U) {g : E → ℂ} (hg : ContDiffOn ℂ ∞ g U) (a b : E)
    {x : E} (hx : x ∈ U) :
    dirDeriv a (dirDeriv b g) x = dirDeriv b (dirDeriv a g) x := by
  have hc : ContDiffAt ℂ ∞ g x := hg.contDiffAt (hU.mem_nhds hx)
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by
    exact show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.2 le_top
  have hs : IsSymmSndFDerivAt ℂ g x := hc.isSymmSndFDerivAt (by simpa using h2)
  have hd : DifferentiableAt ℂ (fderiv ℂ g) x :=
    (hc.fderiv_right (m := 1) (by rw [one_add_one_eq_two]; exact h2)).differentiableAt
      (by simp)
  have key : ∀ a b : E, dirDeriv a (dirDeriv b g) x = fderiv ℂ (fderiv ℂ g) x a b := by
    intro a b
    have h := (ContinuousLinearMap.apply ℂ ℂ b).hasFDerivAt.comp x hd.hasFDerivAt
    change fderiv ℂ (⇑(ContinuousLinearMap.apply ℂ ℂ b) ∘ fderiv ℂ g) x a = _
    rw [h.fderiv]
    rfl
  rw [key, key, hs a b]
private theorem dirDerivList_perm (hU : IsOpen U) (hf : ContDiffOn ℂ ∞ f U) {l l' : List E}
    (h : l.Perm l') : EqOn (dirDerivList l f) (dirDerivList l' f) U := by
  induction h with
  | nil => exact fun _ _ => rfl
  | @cons a l₁ l₂ _ ih =>
    intro x hx
    have he := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) ih
    change fderiv ℂ (dirDerivList l₁ f) x a = fderiv ℂ (dirDerivList l₂ f) x a
    rw [he.fderiv_eq]
  | swap a b l =>
    intro x hx
    exact dirDeriv_comm hU (contDiffOn_dirDerivList hU hf l) b a hx
  | trans _ _ ih₁ ih₂ => exact fun x hx => (ih₁ hx).trans (ih₂ hx)
private theorem iteratedFDeriv_eq_dirDerivList (hU : IsOpen U) (hf : ContDiffOn ℂ ∞ f U)
    (n : ℕ) (v : Fin n → E) :
    EqOn (fun y => iteratedFDeriv ℂ n f y v) (dirDerivList (List.ofFn v) f) U := by
  induction n with
  | zero =>
    intro x _
    simp [dirDerivList]
  | succ n ih =>
    intro x hx
    have hc : ContDiffAt ℂ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ n f) x :=
      hc.differentiableAt_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
    have h := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) ℂ
      (Fin.tail v)).hasFDerivAt.comp x hd.hasFDerivAt
    have he := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) (ih (Fin.tail v))
    rw [List.ofFn_succ]
    change iteratedFDeriv ℂ (n + 1) f x v =
      fderiv ℂ (dirDerivList (List.ofFn (Fin.tail v)) f) x (v 0)
    rw [iteratedFDeriv_succ_apply_left, ← he.fderiv_eq]
    change _ = fderiv ℂ (⇑(ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) ℂ (Fin.tail v)) ∘
      iteratedFDeriv ℂ n f) x (v 0)
    rw [h.fderiv]
    rfl
private theorem iteratedFDeriv_apply_perm (hU : IsOpen U) (hf : ContDiffOn ℂ ∞ f U) {x : E}
    (hx : x ∈ U) {n : ℕ} (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℂ n f x (v ∘ σ) = iteratedFDeriv ℂ n f x v :=
  (iteratedFDeriv_eq_dirDerivList hU hf n (v ∘ σ) hx).trans
    ((dirDerivList_perm hU hf (Equiv.Perm.ofFn_comp_perm σ v) hx).trans
      (iteratedFDeriv_eq_dirDerivList hU hf n v hx).symm)
end IteratedDerivatives
section Transform
variable {W : Type} [MeasurableSpace W] {ν : Measure W} [IsProbabilityMeasure ν] {P : Type}
  [Fintype P] {X : P → W → ℂ}
private def weightedLaplace (ν : Measure W) (X : P → W → ℂ) (Z : W → ℂ) (t : P → ℂ) : ℂ :=
  ∫ w, Z w * Complex.exp (∑ p, t p * X p w) ∂ν
private def laplace (ν : Measure W) (X : P → W → ℂ) : (P → ℂ) → ℂ :=
  weightedLaplace ν X fun _ => 1
private theorem measurable_cexp_pairing (hXm : ∀ p, Measurable (X p)) (t : P → ℂ) :
    Measurable fun w => Complex.exp (∑ p, t p * X p w) :=
  Complex.measurable_exp.comp (Finset.measurable_sum _ fun p _ => measurable_const.mul (hXm p))
omit [MeasurableSpace W] in
private theorem norm_cexp_pairing_le {C : P → ℝ} (hC : ∀ p w, ‖X p w‖ ≤ C p) {R : ℝ}
    {t : P → ℂ} (ht : ‖t‖ ≤ R) (w : W) :
    ‖Complex.exp (∑ p, t p * X p w)‖ ≤ Real.exp (∑ p, R * C p) := by
  refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul]
  have h1 : ‖t p‖ ≤ R := (norm_le_pi_norm t p).trans ht
  exact mul_le_mul h1 (hC p w) (norm_nonneg _) ((norm_nonneg _).trans h1)
private theorem integrable_weightedLaplace {C : P → ℝ} (hXm : ∀ p, Measurable (X p))
    (hC : ∀ p w, ‖X p w‖ ≤ C p) {Z : W → ℂ} (hZm : Measurable Z) {D : ℝ}
    (hZ : ∀ w, ‖Z w‖ ≤ D) (t : P → ℂ) :
    Integrable (fun w => Z w * Complex.exp (∑ p, t p * X p w)) ν := by
  refine Integrable.of_bound (hZm.mul (measurable_cexp_pairing hXm t)).aestronglyMeasurable
    (D * Real.exp (∑ p, ‖t‖ * C p)) (ae_of_all _ fun w => ?_)
  rw [norm_mul]
  exact mul_le_mul (hZ w) (norm_cexp_pairing_le hC le_rfl w) (norm_nonneg _)
    ((norm_nonneg _).trans (hZ w))
private theorem hasFDerivAt_weightedLaplace {C : P → ℝ} (hXm : ∀ p, Measurable (X p))
    (hC : ∀ p w, ‖X p w‖ ≤ C p) {Z : W → ℂ} (hZm : Measurable Z) {D : ℝ}
    (hZ : ∀ w, ‖Z w‖ ≤ D) (x₀ : P → ℂ) :
    HasFDerivAt (weightedLaplace ν X Z)
      (∑ p, weightedLaplace ν X (fun w => Z w * X p w) x₀ •
        (ContinuousLinearMap.proj p : (P → ℂ) →L[ℂ] ℂ)) x₀ := by
  let e : P → ((P → ℂ) →L[ℂ] ℂ) := fun p => ContinuousLinearMap.proj p
  let F' : (P → ℂ) → W → ((P → ℂ) →L[ℂ] ℂ) := fun t w =>
    ∑ p, (Z w * X p w * Complex.exp (∑ j, t j * X j w)) • e p
  have hZXm : ∀ p, Measurable fun w => Z w * X p w := fun p => hZm.mul (hXm p)
  have hZXb : ∀ p w, ‖Z w * X p w‖ ≤ D * C p := fun p w => by
    rw [norm_mul]
    exact mul_le_mul (hZ w) (hC p w) (norm_nonneg _) ((norm_nonneg _).trans (hZ w))
  have hI : ∀ p, Integrable
      (fun w => Z w * X p w * Complex.exp (∑ j, x₀ j * X j w)) ν := fun p =>
    integrable_weightedLaplace hXm hC (hZXm p) (hZXb p) x₀
  have hint : ∫ w, F' x₀ w ∂ν = ∑ p, weightedLaplace ν X (fun w => Z w * X p w) x₀ • e p := by
    simp only [F']
    rw [integral_finsetSum _ fun p _ => (hI p).smul_const _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_smul_const]
    rfl
  have hdiff : ∀ (w : W) (t : P → ℂ),
      HasFDerivAt (fun s : P → ℂ => Z w * Complex.exp (∑ p, s p * X p w)) (F' t w) t := by
    intro w t
    have hA : HasFDerivAt (fun s : P → ℂ => ∑ p, s p * X p w) (∑ p, X p w • e p) t := by
      have h := (∑ p, X p w • e p).hasFDerivAt (x := t)
      convert h using 1
      ext s
      simp [e, mul_comm]
    have h := hA.cexp.const_mul (Z w)
    have hF : F' t w = Z w • Complex.exp (∑ p, t p * X p w) • ∑ p, X p w • e p := by
      simp only [F', Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      ring
    rw [hF]
    exact h
  have hbound : ∀ w, ∀ t ∈ Metric.ball x₀ 1, ‖F' t w‖ ≤
      ∑ p, D * C p * Real.exp (∑ j, (‖x₀‖ + 1) * C j) * ‖e p‖ := by
    intro w t ht
    have hnorm : ‖t‖ ≤ ‖x₀‖ + 1 := by
      have h1 : ‖t - x₀‖ < 1 := by simpa [dist_eq_norm] using ht
      have h2 : ‖t‖ ≤ ‖t - x₀‖ + ‖x₀‖ := by simpa using norm_add_le (t - x₀) x₀
      linarith
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_smul, norm_mul]
    have hDC : 0 ≤ D * C p := (norm_nonneg _).trans (hZXb p w)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hZXb p w) (norm_cexp_pairing_le hC hnorm w) (norm_nonneg _) hDC)
      (norm_nonneg _)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (𝕜 := ℂ)
    (F := fun (t : P → ℂ) w => Z w * Complex.exp (∑ p, t p * X p w)) (F' := F')
    (x₀ := x₀) (s := Metric.ball x₀ 1)
    (bound := fun _ => ∑ p, D * C p * Real.exp (∑ j, (‖x₀‖ + 1) * C j) * ‖e p‖)
    (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun t =>
      (hZm.mul (measurable_cexp_pairing hXm t)).aestronglyMeasurable)
    (integrable_weightedLaplace hXm hC hZm hZ x₀)
    (by
      have hF' : F' x₀ = fun w => ∑ p, (Z w * X p w * Complex.exp (∑ j, x₀ j * X j w)) • e p :=
        rfl
      rw [hF']
      exact Finset.aestronglyMeasurable_fun_sum _ fun p _ =>
        (hI p).aestronglyMeasurable.smul_const _)
    (ae_of_all _ hbound) (integrable_const _) (ae_of_all _ fun w t _ => hdiff w t)
  rw [hint] at key
  exact key
private theorem contDiff_weightedLaplace {C : P → ℝ} (hXm : ∀ p, Measurable (X p))
    (hC : ∀ p w, ‖X p w‖ ≤ C p) (k : ℕ) :
    ∀ (Z : W → ℂ), Measurable Z → (∃ D, ∀ w, ‖Z w‖ ≤ D) →
      ContDiff ℂ k (weightedLaplace ν X Z) := by
  induction k with
  | zero =>
    rintro Z hZm ⟨D, hZ⟩
    have hcont : Continuous (weightedLaplace ν X Z) := continuous_iff_continuousAt.2 fun t =>
      (hasFDerivAt_weightedLaplace hXm hC hZm hZ t).continuousAt
    have h0 : ContDiff ℂ 0 (weightedLaplace ν X Z) := contDiff_zero.2 hcont
    simpa using h0
  | succ k ih =>
    rintro Z hZm ⟨D, hZ⟩
    have hd := fun t => hasFDerivAt_weightedLaplace (ν := ν) hXm hC hZm hZ t
    have hf : fderiv ℂ (weightedLaplace ν X Z) = fun t =>
        ∑ p, weightedLaplace ν X (fun w => Z w * X p w) t •
          (ContinuousLinearMap.proj p : (P → ℂ) →L[ℂ] ℂ) := funext fun t => (hd t).fderiv
    push_cast
    rw [contDiff_succ_iff_fderiv]
    refine ⟨fun t => (hd t).differentiableAt, by simp, ?_⟩
    rw [hf]
    refine ContDiff.sum fun p _ => ContDiff.fun_smul ?_ contDiff_const
    refine ih _ (hZm.mul (hXm p)) ⟨D * C p, fun w => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hZ w) (hC p w) (norm_nonneg _) ((norm_nonneg _).trans (hZ w))
private theorem differentiable_laplace (hX : ∀ p, IsBoundedComplexObservable (X p)) :
    Differentiable ℂ (laplace ν X) := by
  choose C hC using fun p => (hX p).2
  exact fun t => (hasFDerivAt_weightedLaplace (fun p => (hX p).1) hC measurable_const
    (D := 1) (fun _ => by simp) t).differentiableAt
private theorem contDiff_laplace (hX : ∀ p, IsBoundedComplexObservable (X p)) :
    ContDiff ℂ ∞ (laplace ν X) := by
  choose C hC using fun p => (hX p).2
  exact contDiff_infty.2 fun k =>
    contDiff_weightedLaplace (fun p => (hX p).1) hC k _ measurable_const ⟨1, fun _ => by simp⟩
private theorem laplace_zero : laplace ν X 0 = 1 := by
  simp [laplace, weightedLaplace]
private def slitPreimage (ν : Measure W) (X : P → W → ℂ) : Set (P → ℂ) :=
  laplace ν X ⁻¹' Complex.slitPlane
private theorem isOpen_slitPreimage (hX : ∀ p, IsBoundedComplexObservable (X p)) :
    IsOpen (slitPreimage ν X) :=
  Complex.isOpen_slitPlane.preimage (contDiff_laplace hX).continuous
private theorem zero_mem_slitPreimage : (0 : P → ℂ) ∈ slitPreimage ν X := by
  simp [slitPreimage, laplace_zero]
private theorem contDiffOn_log_laplace (hX : ∀ p, IsBoundedComplexObservable (X p)) :
    ContDiffOn ℂ ∞ (fun t => Complex.log (laplace ν X t)) (slitPreimage ν X) := fun t ht =>
  ((Complex.contDiffAt_log ht).comp t (contDiff_laplace hX).contDiffAt).contDiffWithinAt
private def logDerivForm (ν : Measure W) (X : P → W → ℂ) (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => P → ℂ) ℂ :=
  iteratedFDeriv ℂ n (fun t => Complex.log (laplace ν X t)) 0
omit [IsProbabilityMeasure ν] in
private theorem mgf_eq_laplace {n : ℕ} (Y : Fin n → W → ℂ) :
    complexMomentGeneratingFunction ν Y = laplace ν Y := by
  funext z
  simp [complexMomentGeneratingFunction, laplace, weightedLaplace]
private theorem cumulant_eq_logDerivForm (hX : ∀ p, IsBoundedComplexObservable (X p)) {n : ℕ}
    (M : Fin n → P → ℂ) {Y : Fin n → W → ℂ} (hY : ∀ i w, Y i w = ∑ p, M i p * X p w) :
    complexJointCumulant ν Y = logDerivForm ν X n M := by
  let T : (Fin n → ℂ) →L[ℂ] (P → ℂ) :=
    ∑ i, (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).smulRight (M i)
  have hTz : ∀ z p, T z p = ∑ i, z i * M i p := by
    intro z p
    simp [T, Finset.sum_apply]
  have hTe : ∀ i, T (Pi.single i 1) = M i := by
    intro i
    ext p
    rw [hTz]
    simp [Pi.single_apply]
  have hΓ : ∀ z, complexMomentGeneratingFunction ν Y z = laplace ν X (T z) := by
    intro z
    simp only [complexMomentGeneratingFunction, laplace, weightedLaplace, one_mul]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only
    congr 1
    simp only [hY, hTz, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => by ring
  have hU := isOpen_slitPreimage (ν := ν) hX
  have hV := hU.preimage T.continuous
  have h0 : T 0 ∈ slitPreimage ν X := by
    rw [map_zero]
    exact zero_mem_slitPreimage
  have hcomp := T.iteratedFDerivWithin_comp_right (contDiffOn_log_laplace (ν := ν) hX)
    hU.uniqueDiffOn hV.uniqueDiffOn h0 (i := n) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen n hV (show (0 : Fin n → ℂ) ∈ T ⁻¹' _ from h0),
    iteratedFDerivWithin_of_isOpen n hU h0] at hcomp
  have hfun : (fun z => Complex.log (complexMomentGeneratingFunction ν Y z)) =
      (fun t => Complex.log (laplace ν X t)) ∘ T := funext fun z => by simp [hΓ]
  rw [complexJointCumulant, hfun, hcomp, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [hTe, map_zero]
  rfl
private theorem sum_single_mul [DecidableEq P] (x : P → ℂ) (q : P) :
    ∑ p, (Pi.single q (1 : ℂ) : P → ℂ) p * x p = x q := by
  simp [Pi.single_apply]
private theorem cumulant_of_index_map [DecidableEq P]
    (hX : ∀ p, IsBoundedComplexObservable (X p)) {n : ℕ} (r : Fin n → P) :
    complexJointCumulant ν (fun i => X (r i)) =
      logDerivForm ν X n fun i => Pi.single (r i) 1 :=
  cumulant_eq_logDerivForm hX _ fun i w => (sum_single_mul (fun p => X p w) (r i)).symm
private theorem cumulant_linear_combination {n Q : ℕ} {X : Fin Q → W → ℂ}
    (hX : ∀ q, IsBoundedComplexObservable (X q)) (l : Fin n → Fin Q → ℂ) {Y : Fin n → W → ℂ}
    (hY : ∀ i w, Y i w = ∑ q, l i q * X q w) :
    complexJointCumulant ν Y =
      ∑ r : Fin n → Fin Q, (∏ i, l i (r i)) * complexJointCumulant ν fun i => X (r i) := by
  rw [cumulant_eq_logDerivForm hX l hY]
  have hl : l = fun i => ∑ q, l i q • (Pi.single q 1 : Fin Q → ℂ) := by
    ext i p
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hl]
  rw [ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, cumulant_of_index_map hX]
private theorem cumulant_comp_perm {n : ℕ} {Y : Fin n → W → ℂ}
    (hY : ∀ i, IsBoundedComplexObservable (Y i)) (ρ : Equiv.Perm (Fin n)) :
    complexJointCumulant ν (fun i => Y (ρ i)) = complexJointCumulant ν Y := by
  have h1 := cumulant_of_index_map (ν := ν) hY (fun i => ρ i)
  have h2 := cumulant_of_index_map (ν := ν) hY (fun i => i)
  rw [h1, h2]
  exact iteratedFDeriv_apply_perm (isOpen_slitPreimage hY) (contDiffOn_log_laplace hY)
    zero_mem_slitPreimage (fun i => Pi.single i 1) ρ
private theorem cumulant_update_linear {n : ℕ} {Y : Fin n → W → ℂ}
    (hY : ∀ i, IsBoundedComplexObservable (Y i)) (i : Fin n) (l' l'' : ℂ) {Y' Y'' : W → ℂ}
    (hY' : IsBoundedComplexObservable Y') (hY'' : IsBoundedComplexObservable Y'')
    (hi : ∀ w, Y i w = l' * Y' w + l'' * Y'' w) :
    complexJointCumulant ν Y =
      l' * complexJointCumulant ν (Function.update Y i Y') +
        l'' * complexJointCumulant ν (Function.update Y i Y'') := by
  let Z : Fin n ⊕ Bool → W → ℂ := Sum.elim Y fun b => cond b Y' Y''
  have hZ : ∀ p, IsBoundedComplexObservable (Z p) := by
    rintro (k | b)
    · exact hY k
    · cases b
      · exact hY''
      · exact hY'
  obtain ⟨a, ha⟩ : ∃ a : Fin n ⊕ Bool → ℂ, a = Pi.single (Sum.inr true) 1 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n ⊕ Bool → ℂ, b = Pi.single (Sum.inr false) 1 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Fin n → Fin n ⊕ Bool → ℂ, M = fun k => Pi.single (Sum.inl k) 1 :=
    ⟨_, rfl⟩
  have sa : ∀ w, ∑ p, a p * Z p w = Y' w := fun w => by
    rw [ha]
    exact sum_single_mul (fun p => Z p w) _
  have sb : ∀ w, ∑ p, b p * Z p w = Y'' w := fun w => by
    rw [hb]
    exact sum_single_mul (fun p => Z p w) _
  have sm : ∀ k w, ∑ p, M k p * Z p w = Y k w := fun k w => by
    rw [hM]
    exact sum_single_mul (fun p => Z p w) _
  have sab : ∀ w, ∑ p, (l' • a + l'' • b) p * Z p w = Y i w := fun w => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum]
    rw [sa, sb, hi]
  have e1 : complexJointCumulant ν Y =
      logDerivForm ν Z n (Function.update M i (l' • a + l'' • b)) :=
    cumulant_eq_logDerivForm hZ _ fun k w => by
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, sab]
      · rw [Function.update_of_ne hk, sm]
  have e2 : complexJointCumulant ν (Function.update Y i Y') =
      logDerivForm ν Z n (Function.update M i a) :=
    cumulant_eq_logDerivForm hZ _ fun k w => by
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, Function.update_self, sa]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk, sm]
  have e3 : complexJointCumulant ν (Function.update Y i Y'') =
      logDerivForm ν Z n (Function.update M i b) :=
    cumulant_eq_logDerivForm hZ _ fun k w => by
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, Function.update_self, sb]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk, sm]
  rw [e1, e2, e3, ContinuousMultilinearMap.map_update_add,
    ContinuousMultilinearMap.map_update_smul, ContinuousMultilinearMap.map_update_smul,
    smul_eq_mul, smul_eq_mul]
end Transform
section Invariance
variable {W : Type} [MeasurableSpace W] {ν : Measure W} {ψ : W → W}
private theorem map_eq_self_of_preimage (hψ : Measurable ψ)
    (h : ∀ E, MeasurableSet E → ν (ψ ⁻¹' E) = ν E) : ν.map ψ = ν :=
  Measure.ext fun E hE => by rw [Measure.map_apply hψ hE, h E hE]
private theorem integral_comp_of_preimage (hψ : Measurable ψ)
    (h : ∀ E, MeasurableSet E → ν (ψ ⁻¹' E) = ν E) {F : W → ℂ} (hF : Measurable F) :
    ∫ w, F (ψ w) ∂ν = ∫ w, F w ∂ν := by
  rw [← integral_map hψ.aemeasurable hF.aestronglyMeasurable, map_eq_self_of_preimage hψ h]
private theorem cumulant_invariance [IsProbabilityMeasure ν] {n : ℕ} {Y : Fin n → W → ℂ}
    (hY : ∀ i, IsBoundedComplexObservable (Y i)) (hψ : Measurable ψ)
    (h : ∀ E, MeasurableSet E → ν (ψ ⁻¹' E) = ν E) :
    complexJointCumulant ν (fun i => Y i ∘ ψ) = complexJointCumulant ν Y ∧
      Measures.Pushforward.jointDistribution ν (fun i => Y i ∘ ψ)
          (fun i => (hY i).1.comp hψ) =
        Measures.Pushforward.jointDistribution ν Y (fun i => (hY i).1) ∧
      ∫ w, ∏ i, ((Y i ∘ ψ) w - ∫ w', (Y i ∘ ψ) w' ∂ν) ∂ν =
        ∫ w, ∏ i, (Y i w - ∫ w', Y i w' ∂ν) ∂ν := by
  have hm : ∀ i, Measurable (Y i) := fun i => (hY i).1
  refine ⟨?_, ?_, ?_⟩
  · have hΓ : ∀ z, complexMomentGeneratingFunction ν (fun i => Y i ∘ ψ) z =
        complexMomentGeneratingFunction ν Y z := fun z =>
      integral_comp_of_preimage hψ h (F := fun w => Complex.exp (∑ i, z i * Y i w))
        (Complex.measurable_exp.comp
          (Finset.measurable_sum _ fun i _ => measurable_const.mul (hm i)))
    simp only [complexJointCumulant, hΓ]
  · simp only [Measures.Pushforward.jointDistribution, Measures.Pushforward.pushforward]
    have ht : Measures.Pushforward.vectorOf (fun i => Y i ∘ ψ) =
        Measures.Pushforward.vectorOf Y ∘ ψ := rfl
    rw [ht, ← Measure.map_map (show Measurable (Measures.Pushforward.vectorOf Y) from
      measurable_pi_lambda _ hm) hψ, map_eq_self_of_preimage hψ h]
  · have hc : ∀ i, ∫ w', (Y i ∘ ψ) w' ∂ν = ∫ w', Y i w' ∂ν := fun i =>
      integral_comp_of_preimage hψ h (hm i)
    simp only [hc]
    exact integral_comp_of_preimage hψ h (F := fun w => ∏ i, (Y i w - ∫ w', Y i w' ∂ν))
      (Finset.measurable_prod _ fun i _ => (hm i).sub_const _)
end Invariance
private theorem isHolomorphicIn_of_differentiableOn {n : ℕ}
    {O : Set (Coordinates.ComplexCoordinates n)} (hO : IsOpen O)
    {h : Coordinates.ComplexCoordinates n → ℂ} (hd : DifferentiableOn ℂ h O) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => h z := by
  refine ⟨hO, continuousOn_pi.2 fun _ => hd.continuousOn, fun a ha j => ?_⟩
  have hl : Continuous fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by
    fun_prop
  have hm := hl.continuousAt (x := 0) |>.preimage_mem_nhds
    (hO.mem_nhds (show a + (0 : ℂ) • Coordinates.ComplexCoordinates.stdBasisVector j ∈ O by
      simpa using ha))
  filter_upwards [hm] with ζ hζ
  have hg : DifferentiableAt ℂ
      (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ζ := by
    fun_prop
  have hf := (hd.differentiableAt (hO.mem_nhds hζ)).comp ζ hg
  exact differentiableAt_pi.2 fun _ => hf
abbrev _root_.YangMills.SharedProofs.p41626 := @isHolomorphicIn_of_differentiableOn
theorem cumulantProperties_holds : CumulantProperties := by
  intro W _ ν _ n Y hY _
  have he := mgf_eq_laplace (ν := ν) Y
  have hd : Differentiable ℂ (complexMomentGeneratingFunction ν Y) := by
    rw [he]
    exact differentiable_laplace hY
  have h0 : complexMomentGeneratingFunction ν Y 0 = 1 := by
    rw [he]
    exact laplace_zero
  have hopen : IsOpen (mgfNearOneSet ν Y) :=
    isOpen_lt (hd.continuous.sub continuous_const).norm continuous_const
  have h1 : (0 : Coordinates.ComplexCoordinates n) ∈ mgfNearOneSet ν Y := by
    simp [mgfNearOneSet, h0]
  have hent := isHolomorphicIn_of_differentiableOn isOpen_univ hd.differentiableOn
  refine ⟨⟨hent, h0, hopen, h1, isHolomorphicIn_of_differentiableOn hopen ?_,
    ⟨univ, mem_univ _, hent⟩, h0⟩, fun ψ hψ h => cumulant_invariance hY hψ h,
    fun Q X l _ hX hYl => cumulant_linear_combination hX l hYl, cumulant_comp_perm hY,
    fun i l' l'' Y' Y'' h' h'' hi => cumulant_update_linear hY i l' l'' h' h'' hi⟩
  intro z hz
  have hs : complexMomentGeneratingFunction ν Y z ∈ Complex.slitPlane := by
    have h2 := Complex.mem_slitPlane_of_norm_lt_one
      (z := complexMomentGeneratingFunction ν Y z - 1) hz
    simpa using h2
  exact ((hd z).clog hs).differentiableWithinAt
end YangMills.Construction.Cumulants.BoundedComplexCumulants
