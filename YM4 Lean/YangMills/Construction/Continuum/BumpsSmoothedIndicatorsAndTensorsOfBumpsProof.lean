import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumps
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff ENNReal Convolution
noncomputable section
namespace YangMills.Construction.TestSpaces.BumpApprox
section Iterated
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
private def iterDeriv (L : List E) (g : E → F) : E → F :=
  L.foldr (fun v h => fun x => lineDeriv ℝ h x v) g
private theorem iterDeriv_nil (g : E → F) : iterDeriv ([] : List E) g = g := rfl
private theorem iterDeriv_cons (v : E) (L : List E) (g : E → F) :
    iterDeriv (v :: L) g = fun x => lineDeriv ℝ (iterDeriv L g) x v := rfl
private theorem iterDeriv_append (L L' : List E) (g : E → F) :
    iterDeriv (L ++ L') g = iterDeriv L (iterDeriv L' g) := by
  simp [iterDeriv, List.foldr_append]
private theorem lineDeriv_eq_fderiv_of_smooth {g : E → F} (hg : ContDiff ℝ ∞ g) (x v : E) :
    lineDeriv ℝ g x v = fderiv ℝ g x v :=
  ((hg.differentiable (by simp)) x).lineDeriv_eq_fderiv
private theorem smooth_lineDeriv {g : E → F} (hg : ContDiff ℝ ∞ g) (v : E) :
    ContDiff ℝ ∞ fun x => lineDeriv ℝ g x v := by
  have h : (fun x => lineDeriv ℝ g x v) = fun x => fderiv ℝ g x v := by
    funext x; exact lineDeriv_eq_fderiv_of_smooth hg x v
  rw [h]
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
private theorem smooth_iterDeriv (L : List E) {g : E → F} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (iterDeriv L g) := by
  induction L with
  | nil => exact hg
  | cons v L ih => exact smooth_lineDeriv ih v
private theorem compactSupport_iterDeriv (L : List E) {g : E → F} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : HasCompactSupport (iterDeriv L g) := by
  induction L with
  | nil => exact hc
  | cons v L ih =>
    have h : iterDeriv (v :: L) g = fun x => fderiv ℝ (iterDeriv L g) x v := by
      funext x; exact lineDeriv_eq_fderiv_of_smooth (smooth_iterDeriv L hg) x v
    rw [h]
    exact ih.fderiv_apply (𝕜 := ℝ) v
private theorem iterDeriv_sub (L : List E) {g g' : E → F} (hg : ContDiff ℝ ∞ g)
    (hg' : ContDiff ℝ ∞ g') : iterDeriv L (g - g') = iterDeriv L g - iterDeriv L g' := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    funext x
    have h1 := smooth_iterDeriv L hg
    have h2 := smooth_iterDeriv L hg'
    simp only [iterDeriv_cons, ih, Pi.sub_apply]
    have h3 : ContDiff ℝ ∞ (iterDeriv L g - iterDeriv L g') := h1.sub h2
    rw [lineDeriv_eq_fderiv_of_smooth h3, lineDeriv_eq_fderiv_of_smooth h1,
      lineDeriv_eq_fderiv_of_smooth h2,
      fderiv_sub (h1.differentiable (by simp) x) (h2.differentiable (by simp) x)]
    rfl
private theorem iterDeriv_sum {ι : Type*} (S : Finset ι) (L : List E) {g : ι → E → F}
    (hg : ∀ s, ContDiff ℝ ∞ (g s)) :
    iterDeriv L (fun x => ∑ s ∈ S, g s x) = fun x => ∑ s ∈ S, iterDeriv L (g s) x := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    funext x
    have h1 := fun s => smooth_iterDeriv L (hg s)
    simp only [iterDeriv_cons, ih]
    rw [lineDeriv_eq_fderiv_of_smooth (ContDiff.sum fun s _ => h1 s),
      fderiv_fun_sum (fun s _ => (h1 s).differentiable (by simp) x)]
    simp only [_root_.sum_apply]
    exact Finset.sum_congr rfl fun s _ => (lineDeriv_eq_fderiv_of_smooth (h1 s) x v).symm
private theorem iterDeriv_const_smul {R : Type*} [Semiring R] [Module R F] [SMulCommClass ℝ R F]
    [ContinuousConstSMul R F] (L : List E) (c : R) {g : E → F} (hg : ContDiff ℝ ∞ g) :
    iterDeriv L (fun x => c • g x) = fun x => c • iterDeriv L g x := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    funext x
    have h1 := smooth_iterDeriv L hg
    simp only [iterDeriv_cons, ih]
    have h3 : ContDiff ℝ ∞ (fun x => c • iterDeriv L g x) := h1.const_smul c
    rw [lineDeriv_eq_fderiv_of_smooth h3, lineDeriv_eq_fderiv_of_smooth h1,
      fderiv_fun_const_smul (h1.differentiable (by simp) x)]
    rfl
private theorem iterDeriv_comp_sub (L : List E) (a : E) (g : E → F) :
    iterDeriv L (fun x => g (x - a)) = fun x => iterDeriv L g (x - a) := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    funext x
    simp only [iterDeriv_cons, ih]
    unfold lineDeriv
    congr 1
    funext t
    show iterDeriv L g (x + t • v - a) = _
    rw [add_sub_right_comm]
private theorem iterDeriv_comp_smul (L : List E) (c : ℝ) {g : E → F} (hg : ContDiff ℝ ∞ g) :
    iterDeriv L (fun y => g (c • y)) = fun y => (c ^ L.length) • iterDeriv L g (c • y) := by
  induction L with
  | nil => funext y; simp [iterDeriv_nil]
  | cons v L ih =>
    funext y
    have h1 := smooth_iterDeriv L hg
    have h2 : ContDiff ℝ ∞ fun y : E => iterDeriv L g (c • y) :=
      h1.comp (contDiff_const.smul contDiff_id)
    simp only [iterDeriv_cons, ih, List.length_cons]
    have h3 : ContDiff ℝ ∞ (fun y => c ^ L.length • iterDeriv L g (c • y)) :=
      contDiff_const.smul h2
    rw [lineDeriv_eq_fderiv_of_smooth h3, lineDeriv_eq_fderiv_of_smooth h1,
      fderiv_fun_const_smul (h2.differentiable (by simp) y)]
    have := fderiv_comp_smul (𝕜 := ℝ) (f := iterDeriv L g) (x := y) c
    simp only [_root_.smul_apply]
    rw [show (fun y : E => iterDeriv L g (c • y)) = (iterDeriv L g <| c • ·) from rfl, this]
    simp only [_root_.smul_apply, smul_smul, pow_succ]
end Iterated
section Coordinates
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
private def dirList (α : MultiIdx4 n) : List (PointTuple n) :=
  (List.finRange n).flatMap fun i => (List.finRange 4).flatMap fun μ =>
    List.replicate (α i μ) (Pi.single i (Pi.single μ 1))
private theorem iterate_eq_iterDeriv (v : PointTuple n) (k : ℕ) (g : PointTuple n → F) :
    (fun (h : PointTuple n → F) => fun x => lineDeriv ℝ h x v)^[k] g =
      iterDeriv (List.replicate k v) g := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl
private theorem multiDeriv_eq_iterDeriv (α : MultiIdx4 n) (g : PointTuple n → F) :
    multiDeriv α g = iterDeriv (dirList α) g := by
  have inner : ∀ (i : Fin n) (l : List (Fin 4)) (h : PointTuple n → F),
      l.foldr (fun μ h' => (coordDeriv i μ)^[α i μ] h') h =
        iterDeriv (l.flatMap fun μ => List.replicate (α i μ) (Pi.single i (Pi.single μ 1))) h := by
    intro i l h
    induction l with
    | nil => rfl
    | cons μ l ih =>
      simp only [List.foldr_cons, List.flatMap_cons, iterDeriv_append, ih]
      exact iterate_eq_iterDeriv _ _ _
  have outer : ∀ (l : List (Fin n)),
      l.foldr (fun i h => (List.finRange 4).foldr
        (fun μ h' => (coordDeriv i μ)^[α i μ] h') h) g =
        iterDeriv (l.flatMap fun i => (List.finRange 4).flatMap fun μ =>
          List.replicate (α i μ) (Pi.single i (Pi.single μ 1))) g := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldr_cons, ih, List.flatMap_cons, iterDeriv_append, inner]
  exact outer _
private theorem length_dirList (α : MultiIdx4 n) : (dirList α).length = idxOrder α := by
  simp [dirList, idxOrder, List.length_flatMap, Fin.sum_univ_def]
end Coordinates
section Convolve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {𝕂 : Type*} [RCLike 𝕂]
  (μ : Measure E) [μ.IsAddHaarMeasure]
private def convolveAt (f k : E → 𝕂) : E → 𝕂 := fun x => ∫ t, f t * k (x - t) ∂μ
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem convolveAt_eq (f k : E → 𝕂) :
    convolveAt μ f k = f ⋆[ContinuousLinearMap.mul ℝ 𝕂, μ] k := rfl
private theorem smooth_convolveAt {f k : E → 𝕂} (hf : LocallyIntegrable f μ)
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) : ContDiff ℝ ∞ (convolveAt μ f k) := by
  rw [convolveAt_eq]
  exact hc.contDiff_convolution_right _ hf hk
private theorem lineDeriv_convolveAt {f k : E → 𝕂} (hf : LocallyIntegrable f μ)
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) (v x : E) :
    lineDeriv ℝ (convolveAt μ f k) x v = convolveAt μ f (fun y => lineDeriv ℝ k y v) x := by
  have h1 := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ 𝕂) hf
    (hk.of_le (by simp)) x
  rw [convolveAt_eq, h1.differentiableAt.lineDeriv_eq_fderiv, h1.fderiv,
    convolution_precompR_apply _ hf (hc.fderiv (𝕜 := ℝ)) (hk.continuous_fderiv (by simp))]
  have h2 : (fun y => lineDeriv ℝ k y v) = fun y => fderiv ℝ k y v := by
    funext y; exact lineDeriv_eq_fderiv_of_smooth hk y v
  rw [h2, convolveAt_eq]
private theorem iterDeriv_convolveAt (L : List E) {f k : E → 𝕂} (hf : LocallyIntegrable f μ)
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    iterDeriv L (convolveAt μ f k) = convolveAt μ f (iterDeriv L k) := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    funext x
    simp only [iterDeriv_cons, ih]
    exact lineDeriv_convolveAt μ hf (smooth_iterDeriv L hk) (compactSupport_iterDeriv L hk hc) v x
end Convolve
section Norms
variable {n : ℕ}
private theorem abs_apply_le_tupleNorm (x : PointTuple n) (i : Fin n) (μ : Fin 4) :
    |x i μ| ≤ tupleNorm x := by
  unfold tupleNorm
  apply Real.abs_le_sqrt
  calc x i μ ^ 2 ≤ ∑ μ', x i μ' ^ 2 :=
        Finset.single_le_sum (f := fun μ' => x i μ' ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ μ)
    _ ≤ ∑ i', ∑ μ', x i' μ' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ μ', x i' μ' ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
abbrev _root_.YangMills.DeltaSharedProofs.p501753 := @abs_apply_le_tupleNorm
abbrev _root_.YangMills.SharedProofs.p97156 := @abs_apply_le_tupleNorm
private theorem norm_le_tupleNorm (x : PointTuple n) : ‖x‖ ≤ tupleNorm x := by
  have h0 : 0 ≤ tupleNorm x := Real.sqrt_nonneg _
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun μ => ?_
  simpa using abs_apply_le_tupleNorm x i μ
abbrev _root_.YangMills.SharedProofs.p25561 := @norm_le_tupleNorm
private theorem tupleNorm_smul (c : ℝ) (x : PointTuple n) :
    tupleNorm (c • x) = |c| * tupleNorm x := by
  unfold tupleNorm
  have : ∑ i, ∑ μ, (c • x) i μ ^ 2 = c ^ 2 * ∑ i, ∑ μ, x i μ ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
abbrev _root_.YangMills.DeltaSharedProofs.p501995 := @tupleNorm_smul
private theorem tupleNorm_sub_comm (x y : PointTuple n) :
    tupleNorm (x - y) = tupleNorm (y - x) := by
  have := tupleNorm_smul (-1) (y - x)
  simpa using this
abbrev _root_.YangMills.SharedProofs.p39081 := @tupleNorm_sub_comm
private theorem tupleNorm_single (u : Fin 4 → ℝ) :
    tupleNorm (n := 1) (fun _ => u) = TorusMetric.euclidNormVec u := by
  simp [tupleNorm, TorusMetric.euclidNormVec]
private theorem euclidNormVec_smul (c : ℝ) (u : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (c • u) = |c| * TorusMetric.euclidNormVec u := by
  rw [← tupleNorm_single, ← tupleNorm_single, ← tupleNorm_smul]
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p501477 := @euclidNormVec_smul
abbrev _root_.YangMills.SharedProofs.p37834 := @euclidNormVec_smul
private theorem norm_le_euclidNormVec (u : Fin 4 → ℝ) : ‖u‖ ≤ TorusMetric.euclidNormVec u := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
private theorem continuous_euclidNormVec : Continuous TorusMetric.euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
end Norms
section Bump
variable {n : ℕ}
private theorem exists_standardBump (n : ℕ) : ∃ j : PointTuple n → ℝ, IsStandardBump j := by
  set b : PointTuple n → ℝ := fun x => expNegInvGlue (1 - ∑ i, ∑ μ, x i μ ^ 2) with hb
  have hsm : ContDiff ℝ ∞ b := by
    refine expNegInvGlue.contDiff.comp (contDiff_const.sub (ContDiff.sum fun i _ =>
      ContDiff.sum fun μ _ => ContDiff.pow ?_ 2))
    exact contDiff_apply_apply ℝ ℝ i μ
  have hzero : ∀ x, 1 ≤ tupleNorm x → b x = 0 := by
    intro x hx
    refine expNegInvGlue.zero_of_nonpos ?_
    have := Real.one_le_sqrt.1 hx
    linarith
  have hcomp : HasCompactSupport b := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : PointTuple n) 1) fun x hx => hzero x ?_
    have h1 : 1 < ‖x‖ := by simpa using hx
    exact h1.le.trans (norm_le_tupleNorm x)
  have hnn : ∀ x, 0 ≤ b x := fun x => expNegInvGlue.nonneg _
  have hpos : 0 < ∫ x, b x := by
    refine hsm.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcomp hnn
      (x := 0) ?_
    simp [hb]
  refine ⟨fun x => (∫ x, b x)⁻¹ * b x, ⟨contDiff_const.mul hsm, ?_, Set.subset_univ _⟩,
    fun x => mul_nonneg (inv_nonneg.2 hpos.le) (hnn x), fun x hx => by simp [hzero x hx], ?_⟩
  · exact hcomp.mul_left
  · rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']
end Bump
section Scaling
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
private theorem integral_rescale (g : E → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ u, (ε ^ Module.finrank ℝ E)⁻¹ * g (ε⁻¹ • u) ∂μ = ∫ u, g u ∂μ := by
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg μ g hε.le, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (pow_pos hε _).ne', one_mul]
end Scaling
private theorem finrank_pointTuple (n : ℕ) : Module.finrank ℝ (PointTuple n) = 4 * n := by
  show Module.finrank ℝ (Fin n → Fin 4 → ℝ) = _
  rw [Module.finrank_pi_fintype]
  simp [mul_comm]
private theorem finrank_R4 : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
  simp
section Smoothed
variable {n : ℕ}
private def moll (j : PointTuple n → ℝ) (ε : ℝ) (y : PointTuple n) : ℝ :=
  (ε ^ (4 * n))⁻¹ * j (ε⁻¹ • y)
private theorem mollifierKernel_eq_moll (j : PointTuple n → ℝ) (ε : ℝ) (x z : PointTuple n) :
    mollifierKernel j ε x z = moll j ε (x - z) := rfl
private theorem smooth_of_bump {j : PointTuple n → ℝ} (hj : IsStandardBump j) :
    ContDiff ℝ ∞ j := hj.1.1
private theorem compactSupport_of_bump {j : PointTuple n → ℝ} (hj : IsStandardBump j) :
    HasCompactSupport j := hj.1.2.1
private theorem smooth_moll {j : PointTuple n → ℝ} (hj : ContDiff ℝ ∞ j) (ε : ℝ) :
    ContDiff ℝ ∞ (moll j ε) :=
  contDiff_const.mul (hj.comp (contDiff_id.const_smul _))
private theorem compactSupport_moll {j : PointTuple n → ℝ} (hj : HasCompactSupport j) {ε : ℝ}
    (hε : 0 < ε) : HasCompactSupport (moll j ε) := by
  have h := hj.comp_homeomorph (Homeomorph.smulOfNeZero ε⁻¹ (inv_pos.2 hε).ne')
  exact h.mul_left
private theorem integrable_of_smooth_compact {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : PointTuple n → F} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    Integrable g :=
  hg.continuous.integrable_of_hasCompactSupport hc
private theorem integral_moll_sub {g : PointTuple n → ℝ} {ε : ℝ} (hε : 0 < ε) (x : PointTuple n) :
    ∫ z, moll g ε (x - z) = ∫ u, g u := by
  rw [integral_sub_left_eq_self (moll g ε) volume x]
  have := integral_rescale (volume : Measure (PointTuple n)) g hε
  rwa [finrank_pointTuple] at this
private theorem moll_eq_zero {j : PointTuple n → ℝ} (hj : IsStandardBump j) {ε : ℝ} (hε : 0 < ε)
    {x z : PointTuple n} (h : ε ≤ tupleNorm (z - x)) : moll j ε (x - z) = 0 := by
  have h1 : 1 ≤ tupleNorm (ε⁻¹ • (x - z)) := by
    rw [tupleNorm_smul, abs_of_pos (inv_pos.2 hε), tupleNorm_sub_comm x z,
      inv_mul_eq_div, one_le_div hε]
    exact h
  simp [moll, hj.2.2.1 _ h1]
private theorem moll_nonneg {j : PointTuple n → ℝ} (hj : IsStandardBump j) {ε : ℝ} (hε : 0 < ε)
    (y : PointTuple n) : 0 ≤ moll j ε y :=
  mul_nonneg (inv_nonneg.2 (pow_pos hε _).le) (hj.2.1 _)
private theorem regularizedIndicator_eq_convolveAt (j : PointTuple n → ℝ) {Z : Set (PointTuple n)}
    (hZ : MeasurableSet Z) (ε : ℝ) :
    regularizedIndicator j Z ε =
      convolveAt volume (Z.indicator fun _ => (1 : ℝ)) (moll j ε) := by
  funext x
  unfold regularizedIndicator convolveAt
  rw [← integral_indicator hZ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Z <;> simp [hz, mollifierKernel_eq_moll]
private theorem iterDeriv_moll (L : List (PointTuple n)) {j : PointTuple n → ℝ}
    (hj : ContDiff ℝ ∞ j) (ε : ℝ) : iterDeriv L (moll j ε) = fun y =>
      (ε⁻¹ ^ L.length) * moll (iterDeriv L j) ε y := by
  have h2 : ContDiff ℝ ∞ fun y : PointTuple n => j (ε⁻¹ • y) :=
    hj.comp (contDiff_id.const_smul _)
  have h1 : moll j ε = fun y => (ε ^ (4 * n))⁻¹ • j (ε⁻¹ • y) := rfl
  rw [h1, iterDeriv_const_smul L _ h2, iterDeriv_comp_smul L _ hj]
  funext y
  simp only [moll, smul_eq_mul]
  ring
private theorem regularizedIndicator_props {j : PointTuple n → ℝ} (hj : IsStandardBump j)
    {Z : Set (PointTuple n)} (hZ : MeasurableSet Z) {ε : ℝ} (hε : 0 < ε) :
    RegularizedIndicatorProps j Z ε := by
  have hsm := smooth_of_bump hj
  have hcs := compactSupport_of_bump hj
  have hk := smooth_moll hsm ε
  have hkc := compactSupport_moll hcs hε
  have hki : Integrable (moll j ε) := integrable_of_smooth_compact hk hkc
  have hsub : ∀ x, Integrable fun z => moll j ε (x - z) := fun x => hki.comp_sub_left x
  have hone : ∀ x, ∫ z, moll j ε (x - z) = 1 := fun x => by
    rw [integral_moll_sub hε, hj.2.2.2]
  have hloc : LocallyIntegrable (Z.indicator fun _ => (1 : ℝ))
      (volume : Measure (PointTuple n)) :=
    (locallyIntegrable_const (1 : ℝ)).indicator hZ
  have hconv := regularizedIndicator_eq_convolveAt j hZ ε
  refine ⟨fun x => (hsub x).integrableOn, ?_, fun x => ⟨?_, ?_⟩, fun x hx => ?_, fun x hx => ?_,
    fun γ => ⟨?_, fun x => ?_⟩⟩
  · rw [hconv]
    exact smooth_convolveAt volume hloc hk hkc
  · exact setIntegral_nonneg hZ fun z _ => moll_nonneg hj hε _
  · have := setIntegral_le_integral (s := Z) (hsub x)
      (Filter.Eventually.of_forall fun z => moll_nonneg hj hε (x - z))
    rw [hone x] at this
    exact this
  · unfold regularizedIndicator
    simp only [mollifierKernel_eq_moll]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hone x]
    intro z hz
    refine moll_eq_zero hj hε (not_lt.1 fun h => hz (hx h))
  · unfold regularizedIndicator
    simp only [mollifierKernel_eq_moll]
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => moll_eq_zero hj hε ?_
    refine not_lt.1 fun h => ?_
    have : z ∈ {z | tupleNorm (z - x) < ε} ∩ Z := ⟨h, hz⟩
    rw [hx] at this
    exact this
  · have := integrable_of_smooth_compact (smooth_iterDeriv (dirList γ) hsm)
      (compactSupport_iterDeriv (dirList γ) hsm hcs)
    rw [multiDeriv_eq_iterDeriv]
    exact this.abs
  · rw [multiDeriv_eq_iterDeriv, hconv, iterDeriv_convolveAt volume _ hloc hk hkc,
      iterDeriv_moll _ hsm, length_dirList]
    set D := iterDeriv (dirList γ) j with hD
    have hDi : Integrable D := integrable_of_smooth_compact (smooth_iterDeriv _ hsm)
      (compactSupport_iterDeriv _ hsm hcs)
    have hmass : derivL1Mass j γ = ∫ u, |D u| := by
      unfold derivL1Mass
      rw [multiDeriv_eq_iterDeriv]
    have habs : Integrable fun u => |D u| := hDi.abs
    have hc : Integrable (moll (fun u => |D u|) ε) := by
      have : Integrable fun y : PointTuple n => (ε ^ (4 * n))⁻¹ * |D (ε⁻¹ • y)| :=
        (habs.comp_smul (inv_pos.2 hε).ne').const_mul _
      exact this
    have hbound : ∀ t, ‖(Z.indicator (fun _ => (1 : ℝ)) t) *
        ((ε⁻¹ ^ idxOrder γ) * moll D ε (x - t))‖ ≤
        (ε⁻¹ ^ idxOrder γ) * moll (fun u => |D u|) ε (x - t) := by
      intro t
      have hp : 0 < (ε ^ (4 * n))⁻¹ := inv_pos.2 (pow_pos hε _)
      have hq : 0 < ε⁻¹ ^ idxOrder γ := pow_pos (inv_pos.2 hε) _
      have h1 : ‖(ε⁻¹ ^ idxOrder γ) * moll D ε (x - t)‖ =
          (ε⁻¹ ^ idxOrder γ) * moll (fun u => |D u|) ε (x - t) := by
        simp only [moll, norm_mul, Real.norm_eq_abs, abs_of_pos hq, abs_of_pos hp]
      by_cases ht : t ∈ Z
      · simpa [ht] using h1.le
      · simp only [ht, not_false_eq_true, Set.indicator_of_notMem, zero_mul, norm_zero]
        exact mul_nonneg hq.le (mul_nonneg hp.le (abs_nonneg _))
    have h3 := norm_integral_le_of_norm_le
      ((hc.comp_sub_left x).const_mul (ε⁻¹ ^ idxOrder γ)) (Filter.Eventually.of_forall hbound)
    rw [integral_const_mul, integral_moll_sub hε, ← hmass] at h3
    rw [inv_pow, mul_comm] at h3
    simpa [convolveAt, Real.norm_eq_abs, inv_pow] using h3
end Smoothed
section Scaled
private structure BumpR4Data (j₁ : (Fin 4 → ℝ) → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ j₁
  compact : HasCompactSupport j₁
  nonneg : ∀ u, 0 ≤ j₁ u
  zero : ∀ u, 1 ≤ TorusMetric.euclidNormVec u → j₁ u = 0
  mass : ∫ u, j₁ u = 1
private theorem bumpR4Data_of {j₁ : (Fin 4 → ℝ) → ℝ} (hj : IsStandardBumpR4 j₁) :
    BumpR4Data j₁ := by
  obtain ⟨⟨h1, -, -⟩, h2, h3, h4⟩ := hj
  have hzero : ∀ u, 1 ≤ TorusMetric.euclidNormVec u → j₁ u = 0 := fun u hu =>
    h3 (fun _ => u) (by rwa [tupleNorm_single])
  refine ⟨?_, ?_, fun u => h2 fun _ => u, hzero, ?_⟩
  · exact h1.comp (contDiff_pi.2 fun _ => contDiff_id)
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 4 → ℝ) 1) fun u hu => hzero u ?_
    have : 1 < ‖u‖ := by simpa using hu
    exact this.le.trans (norm_le_euclidNormVec u)
  · have := (volume_preserving_funUnique (Fin 1) (Fin 4 → ℝ)).integral_comp' j₁
    rw [← this]
    exact h4
variable {j₁ : (Fin 4 → ℝ) → ℝ}
private theorem smooth_rescaledBump (hj : BumpR4Data j₁) (ε : ℝ) (v : Fin 4 → ℝ) :
    ContDiff ℝ ∞ (rescaledBump j₁ ε v) :=
  contDiff_const.mul (hj.smooth.comp ((contDiff_id.sub contDiff_const).const_smul _))
private theorem rescaledBump_eq_zero (hj : BumpR4Data j₁) {ε : ℝ} (hε : 0 < ε)
    {v u : Fin 4 → ℝ} (h : ε ≤ TorusMetric.euclidNormVec (u - v)) :
    rescaledBump j₁ ε v u = 0 := by
  have h1 : 1 ≤ TorusMetric.euclidNormVec (ε⁻¹ • (u - v)) := by
    rw [euclidNormVec_smul, abs_of_pos (inv_pos.2 hε), inv_mul_eq_div, one_le_div hε]
    exact h
  simp [rescaledBump, hj.zero _ h1]
private theorem compactSupport_rescaledBump (hj : BumpR4Data j₁) {ε : ℝ} (hε : 0 < ε)
    (v : Fin 4 → ℝ) : HasCompactSupport (rescaledBump j₁ ε v) := by
  refine HasCompactSupport.intro (isCompact_closedBall v ε) fun u hu =>
    rescaledBump_eq_zero hj hε ?_
  have : ε < ‖u - v‖ := by simpa [dist_eq_norm] using hu
  exact this.le.trans (norm_le_euclidNormVec _)
private theorem tsupport_rescaledBump_subset (hj : BumpR4Data j₁) {ε : ℝ} (hε : 0 < ε)
    (v : Fin 4 → ℝ) :
    tsupport (rescaledBump j₁ ε v) ⊆ {u | TorusMetric.euclidNormVec (u - v) ≤ ε} := by
  refine closure_minimal (fun u hu => ?_)
    (isClosed_le (continuous_euclidNormVec.comp (continuous_id.sub continuous_const))
      continuous_const)
  by_contra h
  exact hu (rescaledBump_eq_zero hj hε (not_le.1 h).le)
private theorem integral_rescaledBump (hj : BumpR4Data j₁) {ε : ℝ} (hε : 0 < ε) :
    ∫ u, rescaledBump j₁ ε 0 u = 1 := by
  have := integral_rescale (volume : Measure (Fin 4 → ℝ)) j₁ hε
  rw [finrank_R4, hj.mass] at this
  simpa [rescaledBump] using this
end Scaled
section Grid
variable {n : ℕ}
private def cellCorner (h : ℝ) (w : PointTuple n) : PointTuple n := fun i μ => h * ⌊w i μ / h⌋
private def gridCell (h : ℝ) (z : PointTuple n) : Set (PointTuple n) :=
  Set.pi Set.univ fun i => Set.pi Set.univ fun μ => Set.Ico (z i μ) (z i μ + h)
private theorem measurableSet_gridCell (h : ℝ) (z : PointTuple n) : MeasurableSet (gridCell h z) :=
  MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Ico
private theorem volume_gridCell {h : ℝ} (hh : 0 < h) (z : PointTuple n) :
    (volume : Measure (PointTuple n)).real (gridCell h z) = h ^ (4 * n) := by
  have : (volume : Measure (PointTuple n)) (gridCell h z) = (ENNReal.ofReal h ^ 4) ^ n := by
    unfold gridCell
    rw [volume_pi_pi]
    simp_rw [volume_pi_pi, Real.volume_Ico, add_sub_cancel_left]
    simp
  rw [Measure.real, this, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofReal hh.le,
    pow_mul]
private theorem mem_gridCell_cellCorner {h : ℝ} (hh : 0 < h) (w : PointTuple n) :
    w ∈ gridCell h (cellCorner h w) := by
  intro i _ μ _
  have h1 := Int.floor_le (w i μ / h)
  have h2 := Int.lt_floor_add_one (w i μ / h)
  constructor
  · show h * (⌊w i μ / h⌋ : ℝ) ≤ w i μ
    have := mul_le_mul_of_nonneg_left h1 hh.le
    rwa [mul_div_cancel₀ _ hh.ne'] at this
  · show w i μ < h * (⌊w i μ / h⌋ : ℝ) + h
    have := mul_lt_mul_of_pos_left h2 hh
    rw [mul_div_cancel₀ _ hh.ne'] at this
    linarith
private theorem cellCorner_eq {h : ℝ} (hh : 0 < h) {z w : PointTuple n} (hz : z ∈ latticeGrid n h)
    (hw : w ∈ gridCell h z) : cellCorner h w = z := by
  obtain ⟨m, hm⟩ := hz
  funext i μ
  have hwi : w i μ ∈ Set.Ico (z i μ) (z i μ + h) := hw i (Set.mem_univ i) μ (Set.mem_univ μ)
  rw [hm i μ] at hwi ⊢
  have : ⌊w i μ / h⌋ = m i μ := by
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hh]; linarith [hwi.1]
    · rw [div_lt_iff₀ hh]; linarith [hwi.2]
  simp [cellCorner, this]
private theorem cellCorner_mem (h : ℝ) (w : PointTuple n) : cellCorner h w ∈ latticeGrid n h :=
  ⟨fun i μ => ⌊w i μ / h⌋, fun _ _ => rfl⟩
private theorem norm_sub_cellCorner_le {h : ℝ} (hh : 0 < h) (w : PointTuple n) :
    ‖w - cellCorner h w‖ ≤ h := by
  refine (pi_norm_le_iff_of_nonneg hh.le).2 fun i => (pi_norm_le_iff_of_nonneg hh.le).2 fun μ => ?_
  have hw := mem_gridCell_cellCorner hh w i (Set.mem_univ i) μ (Set.mem_univ μ)
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [hw.1, hw.2]
private theorem finite_latticeGrid_ball {h : ℝ} (hh : 0 < h) (ρ : ℝ) :
    {z : PointTuple n | z ∈ latticeGrid n h ∧ ‖z‖ ≤ ρ}.Finite := by
  set M : ℤ := ⌈ρ / h⌉ with hM
  refine ((Set.finite_Icc (fun (_ : Fin n) (_ : Fin 4) => -M) fun _ _ => M).image
    fun m i μ => h * (m i μ : ℝ)).subset ?_
  rintro z ⟨⟨m, hm⟩, hz⟩
  refine ⟨m, ⟨fun i μ => ?_, fun i μ => ?_⟩, funext fun i => funext fun μ => (hm i μ).symm⟩
  all_goals
    have h1 : |z i μ| ≤ ρ := by
      have := (norm_le_pi_norm (z i) μ).trans (norm_le_pi_norm z i)
      exact this.trans hz
    rw [hm, abs_mul, abs_of_pos hh] at h1
    have h2 : |(m i μ : ℝ)| ≤ ρ / h := by
      rw [le_div_iff₀ hh, mul_comm]; exact h1
    have h3 : ρ / h ≤ M := Int.le_ceil _
    have h4 := abs_le.1 (h2.trans h3)
  · have : ((-M : ℤ) : ℝ) ≤ (m i μ : ℝ) := by push_cast; linarith [h4.1]
    exact_mod_cast this
  · have : (m i μ : ℝ) ≤ (M : ℝ) := h4.2
    exact_mod_cast this
private theorem riemannSum_error {g : PointTuple n → ℂ} {K ρ h : ℝ} (hK : 0 ≤ K) (hh : 0 < h)
    (hh1 : h ≤ 1) (hcont : Continuous g) (hL : ∀ a b, ‖g a - g b‖ ≤ K * ‖a - b‖)
    (hz : ∀ a, ρ < ‖a‖ → g a = 0) {S : Finset (PointTuple n)}
    (hS : ∀ z ∈ S, z ∈ latticeGrid n h)
    (hS' : ∀ z ∈ latticeGrid n h, ‖z‖ ≤ ρ → z ∈ S) :
    ‖(∫ w, g w) - ∑ z ∈ S, ((h ^ (4 * n) : ℝ) : ℂ) * g z‖ ≤
      K * h * (volume : Measure (PointTuple n)).real (Metric.closedBall 0 (ρ + 1)) := by
  set s : PointTuple n → ℂ := fun w => ∑ z ∈ S, (gridCell h z).indicator (fun _ => g z) w with hs
  have hsw : ∀ w, s w = g (cellCorner h w) := by
    intro w
    by_cases hw : cellCorner h w ∈ S
    · rw [hs]
      simp only
      rw [Finset.sum_eq_single_of_mem _ hw, Set.indicator_of_mem (mem_gridCell_cellCorner hh w)]
      intro z hzS hne
      refine Set.indicator_of_notMem (fun hwz => hne ?_) _
      exact (cellCorner_eq hh (hS z hzS) hwz).symm
    · have h1 : s w = 0 := by
        refine Finset.sum_eq_zero fun z hzS => Set.indicator_of_notMem (fun hwz => hw ?_) _
        rwa [cellCorner_eq hh (hS z hzS) hwz]
      rw [h1, hz]
      by_contra hn
      exact hw (hS' _ (cellCorner_mem h w) (not_lt.1 hn))
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_closedBall (0 : PointTuple n) ρ) fun a ha =>
      hz a (by simpa using ha)
  have hgi : Integrable g := hcont.integrable_of_hasCompactSupport hgc
  have hterm : ∀ z, Integrable ((gridCell h z).indicator fun _ => g z) := fun z =>
    (integrable_indicator_iff (measurableSet_gridCell h z)).2
      (integrableOn_const (by
        have := volume_gridCell hh z
        intro htop
        rw [Measure.real, htop] at this
        simp at this
        exact (pow_pos hh _).ne this))
  have hsi : Integrable s := integrable_finsetSum _ fun z _ => hterm z
  have hsum : ∫ w, s w = ∑ z ∈ S, ((h ^ (4 * n) : ℝ) : ℂ) * g z := by
    rw [hs]
    simp only
    rw [integral_finsetSum _ fun z _ => hterm z]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [integral_indicator_const _ (measurableSet_gridCell h z), volume_gridCell hh,
      Complex.real_smul]
  rw [← hsum, ← integral_sub hgi hsi]
  have hout : ∀ w, w ∉ Metric.closedBall (0 : PointTuple n) (ρ + 1) → g w - s w = 0 := by
    intro w hw
    have h1 : ρ + 1 < ‖w‖ := by simpa using hw
    have h2 : ‖w‖ - h ≤ ‖cellCorner h w‖ := by
      have h3 := norm_sub_norm_le w (cellCorner h w)
      linarith [norm_sub_cellCorner_le hh w]
    rw [hsw, hz w (by linarith), hz _ (by linarith), sub_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  refine norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top fun w _ => ?_
  rw [hsw]
  exact (hL _ _).trans (mul_le_mul_of_nonneg_left (norm_sub_cellCorner_le hh w) hK)
end Grid
section Tensors
variable {n : ℕ} {j₁ : (Fin 4 → ℝ) → ℝ}
private def prodBump (j₁ : (Fin 4 → ℝ) → ℝ) (ε : ℝ) : PointTuple n → ℝ :=
  fun w => ∏ i, rescaledBump j₁ ε 0 (w i)
private def prodBumpC (j₁ : (Fin 4 → ℝ) → ℝ) (ε : ℝ) : PointTuple n → ℂ :=
  fun w => ((prodBump j₁ ε w : ℝ) : ℂ)
private theorem tensorProd_rescaledBump (j₁ : (Fin 4 → ℝ) → ℝ) (ε : ℝ) (z x : PointTuple n) :
    tensorProd (fun i => rescaledBump j₁ ε (z i)) x = prodBump j₁ ε (x - z) := by
  simp [tensorProd, prodBump, rescaledBump]
private theorem smooth_prodBump (hj : BumpR4Data j₁) (ε : ℝ) :
    ContDiff ℝ ∞ (prodBump (n := n) j₁ ε) :=
  contDiff_prod fun i _ => (smooth_rescaledBump hj ε 0).comp (contDiff_apply ℝ _ i)
private theorem prodBump_nonneg (hj : BumpR4Data j₁) {ε : ℝ} (hε : 0 < ε) (w : PointTuple n) :
    0 ≤ prodBump j₁ ε w :=
  Finset.prod_nonneg fun _ _ =>
    mul_nonneg (inv_nonneg.2 (pow_pos hε _).le) (hj.nonneg _)
private theorem prodBump_eq_zero (hj : BumpR4Data j₁) {ε : ℝ} (hε : 0 < ε) {w : PointTuple n}
    (hw : ε < ‖w‖) : prodBump j₁ ε w = 0 := by
  have : ∃ i, ε < ‖w i‖ := by
    by_contra hn
    push Not at hn
    exact absurd ((pi_norm_le_iff_of_nonneg hε.le).2 hn) (not_le.2 hw)
  obtain ⟨i, hi⟩ := this
  refine Finset.prod_eq_zero (Finset.mem_univ i) (rescaledBump_eq_zero hj hε ?_)
  rw [sub_zero]
  exact hi.le.trans (norm_le_euclidNormVec _)
private theorem compactSupport_prodBump (hj : BumpR4Data j₁) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (prodBump (n := n) j₁ ε) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : PointTuple n) ε) fun _ hw =>
    prodBump_eq_zero hj hε (by simpa using hw)
private theorem integral_prodBump (hj : BumpR4Data j₁) {ε : ℝ} (hε : 0 < ε) :
    ∫ w, prodBump (n := n) j₁ ε w = 1 := by
  unfold prodBump
  rw [integral_fintype_prod_volume_eq_prod (fun _ => rescaledBump j₁ ε 0)]
  simp [integral_rescaledBump hj hε]
private theorem smooth_prodBumpC (hj : BumpR4Data j₁) (ε : ℝ) :
    ContDiff ℝ ∞ (prodBumpC (n := n) j₁ ε) :=
  Complex.ofRealCLM.contDiff.comp (smooth_prodBump hj ε)
private theorem compactSupport_prodBumpC (hj : BumpR4Data j₁) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (prodBumpC (n := n) j₁ ε) :=
  (compactSupport_prodBump hj hε).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
end Tensors
section Bounds
variable {n : ℕ}
private theorem lipschitz_bound_of_smooth {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ a b, ‖g a - g b‖ ≤ C * ‖a - b‖) ∧ ∀ a, ‖g a‖ ≤ C := by
  obtain ⟨C₁, h₁⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) hc hg (by simp)
  obtain ⟨C₂, h₂⟩ := hc.exists_bound_of_continuous hg.continuous
  refine ⟨max (C₁ : ℝ) C₂, le_max_of_le_left C₁.2, fun a b => ?_, fun a =>
    (h₂ a).trans (le_max_right _ _)⟩
  have := h₁.dist_le_mul a b
  rw [dist_eq_norm, dist_eq_norm] at this
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
private theorem entry_le_idxOrder (α : MultiIdx4 n) (i : Fin n) (μ : Fin 4) :
    α i μ ≤ idxOrder α :=
  calc α i μ ≤ ∑ μ', α i μ' :=
        Finset.single_le_sum (f := fun μ' => α i μ') (fun _ _ => Nat.zero_le _) (Finset.mem_univ μ)
    _ ≤ idxOrder α :=
        Finset.single_le_sum (f := fun i' => ∑ μ', α i' μ') (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
private theorem uniform_deriv_bounds {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : MultiIdx4 n, idxOrder α ≤ p →
      (∀ a b, ‖iterDeriv (dirList α) g a - iterDeriv (dirList α) g b‖ ≤ C * ‖a - b‖) ∧
      ∀ a, ‖iterDeriv (dirList α) g a‖ ≤ C := by
  have h := fun α : MultiIdx4 n =>
    lipschitz_bound_of_smooth (smooth_iterDeriv (dirList α) hg)
      (compactSupport_iterDeriv (dirList α) hg hc)
  choose C hC0 hCL hCB using h
  set S : Finset (MultiIdx4 n) := Finset.Icc 0 fun _ _ => p with hS
  refine ⟨∑ α ∈ S, C α, Finset.sum_nonneg fun α _ => hC0 α, fun α hα => ?_⟩
  have hmem : α ∈ S := Finset.mem_Icc.2
    ⟨fun _ _ => Nat.zero_le _, fun i μ => (entry_le_idxOrder α i μ).trans hα⟩
  have hle : C α ≤ ∑ α ∈ S, C α :=
    Finset.single_le_sum (f := C) (fun α _ => hC0 α) hmem
  exact ⟨fun a b => (hCL α a b).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _)),
    fun a => (hCB α a).trans hle⟩
private theorem convolveAt_comm (f k : PointTuple n → ℂ) (x : PointTuple n) :
    convolveAt volume f k x = convolveAt volume k f x := by
  unfold convolveAt
  have := integral_sub_left_eq_self (fun s => f (x - s) * k s) (volume : Measure (PointTuple n)) x
  simp only [sub_sub_cancel] at this
  rw [this]
  exact integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
private theorem norm_convolveAt_sub_le {J : PointTuple n → ℝ} {D : PointTuple n → ℂ} {C ε : ℝ}
    (hJc : Continuous J) (hJi : Integrable J) (hJ0 : ∀ w, 0 ≤ J w) (hJ1 : ∫ w, J w = 1)
    (hsupp : ∀ w, ε < ‖w‖ → J w = 0) (hC : 0 ≤ C) (hDc : Continuous D)
    (hD : ∀ a b, ‖D a - D b‖ ≤ C * ‖a - b‖) (x : PointTuple n) :
    ‖convolveAt volume (fun w => (J w : ℂ)) D x - D x‖ ≤ C * ε := by
  have hbound : ∀ t, ‖(J t : ℂ) * (D (x - t) - D x)‖ ≤ J t * (C * ε) := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hJ0 t)]
    by_cases ht : ε < ‖t‖
    · simp [hsupp t ht]
    · refine mul_le_mul_of_nonneg_left ?_ (hJ0 t)
      have h1 := hD (x - t) x
      have h2 : ‖x - t - x‖ = ‖t‖ := by simp
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (not_lt.1 ht) hC)
  have hint : Integrable fun t => (J t : ℂ) * (D (x - t) - D x) := by
    refine Integrable.mono' (hJi.mul_const (C * ε)) ?_ (Filter.Eventually.of_forall hbound)
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  have hI2 : Integrable fun t => (J t : ℂ) * D x := hJi.ofReal.mul_const _
  have hsplit : convolveAt volume (fun w => (J w : ℂ)) D x - D x =
      ∫ t, (J t : ℂ) * (D (x - t) - D x) := by
    have h1 : (fun t => (J t : ℂ) * D (x - t)) =
        fun t => (J t : ℂ) * (D (x - t) - D x) + (J t : ℂ) * D x := by
      funext t; ring
    unfold convolveAt
    rw [h1, integral_add hint hI2, integral_mul_const, integral_complex_ofReal, hJ1]
    simp
  rw [hsplit]
  have := norm_integral_le_of_norm_le (hJi.mul_const (C * ε))
    (Filter.Eventually.of_forall hbound)
  rwa [integral_mul_const, hJ1, one_mul] at this
end Bounds
private theorem tensorBumpApproximation_holds (n : ℕ) : TensorBumpApproximation n := by
  intro φ hφ p ϵ hϵ
  obtain ⟨hsm, hcs, -⟩ := hφ
  obtain ⟨C, hC0, hC⟩ := uniform_deriv_bounds hsm hcs p
  refine ⟨ϵ / (2 * (C + 1)), by positivity, fun j₁ hj₁ ε hε hε₁ => ?_⟩
  have hj := bumpR4Data_of hj₁
  have hJsm := smooth_prodBumpC (n := n) hj ε
  have hJcs := compactSupport_prodBumpC (n := n) hj hε
  obtain ⟨CJ, hCJ0, hCJ⟩ := uniform_deriv_bounds hJsm hJcs p
  obtain ⟨Cφ, hCφ0, hLφ, hBφ⟩ := lipschitz_bound_of_smooth hsm hcs
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ a, ρ < ‖a‖ → φ a = 0 := by
    obtain ⟨r, hr⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : PointTuple n)
    refine ⟨max r 0, le_max_right _ _, fun a ha => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
    have h1 : ‖a‖ ≤ r := by simpa using hr hmem
    exact absurd (h1.trans (le_max_left _ _)) (not_le.2 ha)
  set V := (volume : Measure (PointTuple n)).real (Metric.closedBall 0 (ρ + 1)) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  set K := Cφ * CJ + Cφ * CJ with hK
  have hK0 : 0 ≤ K := by positivity
  set h := min 1 (ϵ / (2 * (K * V + 1))) with hh
  have hh0 : 0 < h := lt_min one_pos (by positivity)
  have hh1 : h ≤ 1 := min_le_left _ _
  have hh2 : h ≤ ϵ / (2 * (K * V + 1)) := min_le_right _ _
  set S := (finite_latticeGrid_ball (n := n) hh0 ρ).toFinset with hS
  have hSmem : ∀ z, z ∈ S ↔ z ∈ latticeGrid n h ∧ ‖z‖ ≤ ρ := fun z => by simp [hS]
  have hterm0 : ∀ z, φ z = 0 → gridSummand j₁ φ ε h z = 0 := by
    intro z hz
    funext x
    simp [gridSummand, hz]
  have hsumeq : gridApprox j₁ φ ε h = fun x =>
      ∑ z ∈ S, (((h ^ (4 * n) : ℝ) : ℂ) * φ z) • prodBumpC j₁ ε (x - z) := by
    unfold gridApprox
    rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := S)]
    · funext x
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp [gridSummand, prodBumpC, tensorProd_rescaledBump]
    · ext z
      simp only [Set.mem_inter_iff, Finset.mem_coe, Function.mem_support]
      constructor
      · rintro ⟨hz, hne⟩
        refine ⟨(hSmem z).2 ⟨hz, ?_⟩, hne⟩
        by_contra hn
        exact hne (hterm0 z (hρ z (not_le.1 hn)))
      · rintro ⟨hz, hne⟩
        exact ⟨((hSmem z).1 hz).1, hne⟩
  refine ⟨h, hh0, (finite_latticeGrid_ball (n := n) hh0 ρ).subset ?_, ?_⟩
  · rintro z ⟨hz, hne⟩
    refine ⟨hz, ?_⟩
    by_contra hn
    exact hne (hterm0 z (hρ z (not_le.1 hn)))
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ENNReal.ofReal_le_ofReal ?_
  set L := dirList α with hL
  have hshift : ∀ z : PointTuple n, ContDiff ℝ ∞ fun x => prodBumpC (n := n) j₁ ε (x - z) :=
    fun z => hJsm.comp (contDiff_id.sub contDiff_const)
  have hterms : ∀ z : PointTuple n, ContDiff ℝ ∞
      fun x => (((h ^ (4 * n) : ℝ) : ℂ) * φ z) • prodBumpC (n := n) j₁ ε (x - z) := fun z =>
    (hshift z).const_smul _
  have hRsm : ContDiff ℝ ∞ (gridApprox j₁ φ ε h) := by
    rw [hsumeq]
    exact ContDiff.sum fun z _ => hterms z
  set D := iterDeriv L (prodBumpC (n := n) j₁ ε) with hD
  have hDsm : ContDiff ℝ ∞ D := smooth_iterDeriv L hJsm
  have hR : iterDeriv L (gridApprox j₁ φ ε h) x =
      ∑ z ∈ S, ((h ^ (4 * n) : ℝ) : ℂ) * (φ z * D (x - z)) := by
    rw [hsumeq, iterDeriv_sum S L hterms]
    simp only
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [iterDeriv_const_smul L _ (hshift z), iterDeriv_comp_sub]
    show (((h ^ (4 * n) : ℝ) : ℂ) * φ z) • iterDeriv L (prodBumpC j₁ ε) (x - z) = _
    rw [smul_eq_mul, mul_assoc]
  rw [multiDeriv_eq_iterDeriv, ← hL, iterDeriv_sub L hsm hRsm, Pi.sub_apply, hR]
  have hlocφ : LocallyIntegrable φ (volume : Measure (PointTuple n)) :=
    hsm.continuous.locallyIntegrable
  have hlocJ : LocallyIntegrable (prodBumpC (n := n) j₁ ε) (volume : Measure (PointTuple n)) :=
    hJsm.continuous.locallyIntegrable
  have hB1 : convolveAt volume φ D x =
      iterDeriv L (convolveAt volume φ (prodBumpC j₁ ε)) x := by
    rw [iterDeriv_convolveAt volume L hlocφ hJsm hJcs]
  have hB2 : convolveAt volume (prodBumpC j₁ ε) (iterDeriv L φ) x =
      iterDeriv L (convolveAt volume φ (prodBumpC j₁ ε)) x := by
    have : convolveAt volume φ (prodBumpC (n := n) j₁ ε) =
        convolveAt volume (prodBumpC j₁ ε) φ := funext fun y => convolveAt_comm _ _ y
    rw [this, iterDeriv_convolveAt volume L hlocJ hsm hcs]
  have hfirst : ‖convolveAt volume (prodBumpC j₁ ε) (iterDeriv L φ) x - iterDeriv L φ x‖ ≤
      C * ε :=
    norm_convolveAt_sub_le (J := prodBump j₁ ε) (smooth_prodBump hj ε).continuous
      ((smooth_prodBump hj ε).continuous.integrable_of_hasCompactSupport
        (compactSupport_prodBump hj hε))
      (prodBump_nonneg hj hε) (integral_prodBump hj hε)
      (fun _ hw => prodBump_eq_zero hj hε hw) hC0 (smooth_iterDeriv L hsm).continuous
      (hC α hα).1 x
  have hsecond : ‖convolveAt volume φ D x -
      ∑ z ∈ S, ((h ^ (4 * n) : ℝ) : ℂ) * (φ z * D (x - z))‖ ≤ K * h * V := by
    refine riemannSum_error (g := fun w => φ w * D (x - w)) hK0 hh0 hh1
      (hsm.continuous.mul (hDsm.continuous.comp (continuous_const.sub continuous_id)))
      (fun a b => ?_) (fun a ha => by simp [hρ a ha]) (fun z hz => ((hSmem z).1 hz).1)
      (fun z hz hz' => (hSmem z).2 ⟨hz, hz'⟩)
    have h1 : φ a * D (x - a) - φ b * D (x - b) =
        (φ a - φ b) * D (x - a) + φ b * (D (x - a) - D (x - b)) := by ring
    have h2 := (hCJ α hα).1 (x - a) (x - b)
    have h3 : ‖x - a - (x - b)‖ = ‖a - b‖ := by
      rw [show x - a - (x - b) = b - a by abel, norm_sub_rev]
    rw [h3] at h2
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h4 := mul_le_mul (hLφ a b) ((hCJ α hα).2 (x - a)) (norm_nonneg _)
      (mul_nonneg hCφ0 (norm_nonneg _))
    have h5 := mul_le_mul (hBφ b) h2 (norm_nonneg _) hCφ0
    have : K * ‖a - b‖ = Cφ * ‖a - b‖ * CJ + Cφ * (CJ * ‖a - b‖) := by
      rw [hK]; ring
    rw [this]
    exact add_le_add h4 h5
  have hεC : C * ε ≤ ϵ / 2 := by
    have h1 := (le_div_iff₀ (by positivity)).1 hε₁
    nlinarith
  have hhK : K * h * V ≤ ϵ / 2 := by
    have h1 := (le_div_iff₀ (by positivity)).1 hh2
    nlinarith [mul_nonneg hK0 hV0]
  have hfinal : iterDeriv L φ x - ∑ z ∈ S, ((h ^ (4 * n) : ℝ) : ℂ) * (φ z * D (x - z)) =
      -(convolveAt volume (prodBumpC j₁ ε) (iterDeriv L φ) x - iterDeriv L φ x) +
      (convolveAt volume φ D x - ∑ z ∈ S, ((h ^ (4 * n) : ℝ) : ℂ) * (φ z * D (x - z))) := by
    rw [hB1, hB2]; ring
  rw [hfinal]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  linarith
theorem bumpLemma_holds : BumpLemma := by
  intro n _
  refine ⟨exists_standardBump n, fun j hj Z hZ ε hε => regularizedIndicator_props hj hZ hε,
    fun j₁ hj₁ ε v hε => ?_, tensorBumpApproximation_holds n⟩
  have hj := bumpR4Data_of hj₁
  exact ⟨⟨smooth_rescaledBump hj ε v, compactSupport_rescaledBump hj hε v, Set.subset_univ _⟩,
    tsupport_rescaledBump_subset hj hε v⟩
end YangMills.Construction.TestSpaces.BumpApprox
