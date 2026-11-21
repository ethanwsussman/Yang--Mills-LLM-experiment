import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.ConvexityOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.SecondDerivativesAlongLines
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology RealInnerProductSpace
open Filter
namespace YangMills.Construction.StepSettings
open BlockAverages LumpContours ColdStepAtMirrorFrames LineCalculus TorusFields RenormalizationStepParameters TorusLumps
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem fderiv_fderiv_add {f g : E → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p) :
    fderiv ℝ (fderiv ℝ fun q => f q + g q) p = fderiv ℝ (fderiv ℝ f) p + fderiv ℝ (fderiv ℝ g) p := by
  have he : fderiv ℝ (fun q => f q + g q) =ᶠ[𝓝 p] fun q => fderiv ℝ f q + fderiv ℝ g q := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt_two hf,
      eventually_differentiableAt_of_contDiffAt_two hg] with q h1 h2
    exact fderiv_fun_add h1 h2
  rw [he.fderiv_eq]
  exact ((hasFDerivAt_fderiv_of_contDiffAt_two hf).add (hasFDerivAt_fderiv_of_contDiffAt_two hg)).fderiv
theorem fderiv_fderiv_const_mul {f : E → ℝ} {p : E} (a : ℝ) (hf : ContDiffAt ℝ 2 f p) :
    fderiv ℝ (fderiv ℝ fun q => a * f q) p = a • fderiv ℝ (fderiv ℝ f) p := by
  have he : fderiv ℝ (fun q => a * f q) =ᶠ[𝓝 p] fun q => a • fderiv ℝ f q := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt_two hf] with q h1
    exact fderiv_const_mul h1 a
  rw [he.fderiv_eq]
  exact ((hasFDerivAt_fderiv_of_contDiffAt_two hf).const_smul a).fderiv
theorem fderiv_fderiv_comp_clm_apply {f : E → ℝ} (P : E →L[ℝ] E) {p : E} (hf : ContDiffAt ℝ 2 f (P p))
    (v w : E) :
    fderiv ℝ (fderiv ℝ fun q => f (P q)) p v w = fderiv ℝ (fderiv ℝ f) (P p) (P v) (P w) := by
  have h := second_fderiv_of_eventuallyEq_comp (f := fun q => f (P q)) (g := f) (h := (P : E → E)) (x := p)
    EventuallyEq.rfl hf P.contDiff.contDiffAt v w
  have h1 : fderiv ℝ (P : E → E) = fun _ => P := funext fun q => P.fderiv
  rw [h]
  simp [h1]
end Calculus
section SquaredNorms
variable {ι : Type*} [Fintype ι]
abbrev ImCoords : Type := EuclideanSpace ℝ (Fin 3)
def sqNormForm (A : Finset ι) : (ι → ImCoords) →L[ℝ] (ι → ImCoords) →L[ℝ] ℝ :=
  ∑ b ∈ A, (2 : ℝ) • (innerSL ℝ : ImCoords →L[ℝ] ImCoords →L[ℝ] ℝ).bilinearComp
    (ContinuousLinearMap.proj b) (ContinuousLinearMap.proj b)
theorem sqNormForm_apply (A : Finset ι) (e e' : ι → ImCoords) :
    sqNormForm A e e' = 2 * ∑ b ∈ A, ⟪e b, e' b⟫ := by
  simp [sqNormForm, Finset.mul_sum]
theorem hasFDerivAt_sum_sq_norm (A : Finset ι) (η : ι → ImCoords) :
    HasFDerivAt (fun η : ι → ImCoords => ∑ b ∈ A, ‖η b‖ ^ 2) (sqNormForm A η) η := by
  have h : ∀ b ∈ A, HasFDerivAt (fun η : ι → ImCoords => ‖η b‖ ^ 2)
      (2 • (innerSL ℝ (η b)).comp (ContinuousLinearMap.proj b : (ι → ImCoords) →L[ℝ] ImCoords)) η :=
    fun b _ => (ContinuousLinearMap.proj b : (ι → ImCoords) →L[ℝ] ImCoords).hasFDerivAt.norm_sq
  have h2 := HasFDerivAt.fun_sum h
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun e => ?_)
  rw [sqNormForm_apply]
  simp [Finset.mul_sum]
theorem fderiv_sum_sq_norm (A : Finset ι) :
    fderiv ℝ (fun η : ι → ImCoords => ∑ b ∈ A, ‖η b‖ ^ 2) = fun η => sqNormForm A η :=
  funext fun η => (hasFDerivAt_sum_sq_norm A η).fderiv
theorem fderiv_fderiv_sum_sq_norm (A : Finset ι) (η : ι → ImCoords) :
    fderiv ℝ (fderiv ℝ fun η : ι → ImCoords => ∑ b ∈ A, ‖η b‖ ^ 2) η = sqNormForm A := by
  rw [fderiv_sum_sq_norm]
  exact (sqNormForm A).hasFDerivAt.fderiv
theorem contDiff_sum_sq_norm (A : Finset ι) :
    ContDiff ℝ 3 (fun η : ι → ImCoords => ∑ b ∈ A, ‖η b‖ ^ 2) := by
  refine ContDiff.sum fun b _ => ?_
  exact (contDiff_apply ℝ ImCoords b).norm_sq ℝ
end SquaredNorms
section Chart
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n} {u w : FreeCoords s.free → ℝ} {lam C : ℝ}
theorem update_add_smul_eq_add_single (η : FreeCoords s.free) (b : s.free) (X : ImCoords) (τ : ℝ) :
    Function.update η b (η b + τ • X) = η + τ • (Pi.single b X : FreeCoords s.free) := by
  classical
  funext c
  by_cases h : c = b
  · subst h
    simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
theorem mixedSecondDeriv_eq_fderiv_fderiv {η : FreeCoords s.free} (hu : ContDiffAt ℝ 2 u η) (b b' : s.free)
    (X X' : ImCoords) :
    mixedSecondDeriv u η b b' X X' =
      fderiv ℝ (fderiv ℝ u) η (Pi.single b X) (Pi.single b' X') := by
  unfold mixedSecondDeriv
  simp only [update_add_smul_eq_add_single]
  exact mixed_second_deriv_along_lines hu
theorem deriv_update_eq_fderiv {η : FreeCoords s.free} (hu : DifferentiableAt ℝ u η) (b : s.free)
    (X : ImCoords) :
    deriv (fun τ : ℝ => u (Function.update η b (η b + τ • X))) 0 = fderiv ℝ u η (Pi.single b X) := by
  simp only [update_add_smul_eq_add_single]
  exact deriv_along_line hu
structure ChartSetting.HasHessianDecay (s : ChartSetting R n) (u : FreeCoords s.free → ℝ) (lam C : ℝ) :
    Prop where
  contDiffOn : ∃ U : Set (FreeCoords s.free), IsOpen U ∧ (∀ η, s.InBalls η → η ∈ U) ∧ ContDiffOn ℝ 3 u U
  lower : ∀ η, s.InBalls η → ∀ v : FreeCoords s.free,
    R.coupling * lam / 4 * ∑ b, ‖v b‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ u) η v v
  decay : ∃ M : s.free → s.free → ℝ, (∀ η, s.InBalls η → ∀ b b' (X X' : ImCoords), ‖X‖ = 1 → ‖X'‖ = 1 →
      |fderiv ℝ (fderiv ℝ u) η (Pi.single b X) (Pi.single b' X')| ≤ M b b') ∧
    ∀ b, ∑ b', M b b' * (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) ≤
      R.coupling * lam / 8
  fderiv_le : ∀ η, s.InBalls η → ∀ b (X : ImCoords), ‖X‖ = 1 →
    |fderiv ℝ u η (Pi.single b X)| ≤ C * R.coupling
  fderiv_fderiv_le : ∀ η, s.InBalls η → ∀ b b' (X X' : ImCoords), ‖X‖ = 1 → ‖X'‖ = 1 →
    |fderiv ℝ (fderiv ℝ u) η (Pi.single b X) (Pi.single b' X')| ≤ C * R.coupling
theorem contDiffAt_of_exists_open (h : ∃ U : Set (FreeCoords s.free), IsOpen U ∧ (∀ η, s.InBalls η → η ∈ U) ∧
    ContDiffOn ℝ 3 u U) {η : FreeCoords s.free} (hη : s.InBalls η) : ContDiffAt ℝ 3 u η := by
  obtain ⟨U, hU, hb, hc⟩ := h
  exact hc.contDiffAt (hU.mem_nhds (hb η hη))
theorem ChartSetting.HasHessianDecay.contDiffAt (h : s.HasHessianDecay u lam C) {η : FreeCoords s.free}
    (hη : s.InBalls η) : ContDiffAt ℝ 3 u η := contDiffAt_of_exists_open h.contDiffOn hη
theorem hasFullDecay_iff_hasHessianDecay : s.HasFullDecay u lam C ↔ s.HasHessianDecay u lam C := by
  have two : ∀ {η : FreeCoords s.free}, ContDiffAt ℝ 3 u η → ContDiffAt ℝ 2 u η := fun h =>
    h.of_le (by norm_num)
  have one : ∀ {η : FreeCoords s.free}, ContDiffAt ℝ 3 u η → DifferentiableAt ℝ u η := fun h =>
    h.differentiableAt (by norm_num)
  constructor
  · intro h
    have hs := h.contDiffOn_nhds
    refine ⟨h.contDiffOn_nhds, fun η hη v => ?_, ?_, fun η hη b X hX => ?_, fun η hη b b' X X' hX hX' => ?_⟩
    · have := h.hessian_ge η hη v
      rwa [second_deriv_along_line (two (contDiffAt_of_exists_open hs hη))] at this
    · obtain ⟨M, hM, hr⟩ := h.decay
      refine ⟨M, fun η hη b b' X X' hX hX' => ?_, hr⟩
      have := hM η hη b b' X X' hX hX'
      rwa [mixedSecondDeriv_eq_fderiv_fderiv (two (contDiffAt_of_exists_open hs hη))] at this
    · have := h.firstDeriv_le η hη b X hX
      rwa [deriv_update_eq_fderiv (one (contDiffAt_of_exists_open hs hη))] at this
    · have := h.mixedSecondDeriv_le η hη b b' X X' hX hX'
      rwa [mixedSecondDeriv_eq_fderiv_fderiv (two (contDiffAt_of_exists_open hs hη))] at this
  · intro h
    have hc : ∀ {η : FreeCoords s.free}, s.InBalls η → ContDiffAt ℝ 3 u η := fun hη => h.contDiffAt hη
    refine ⟨⟨fun η hη v => ?_, ?_, fun η hη b X hX => ?_⟩, h.contDiffOn, fun η hη b b' X X' hX hX' => ?_⟩
    · rw [second_deriv_along_line (two (hc hη))]
      exact h.lower η hη v
    · obtain ⟨M, hM, hr⟩ := h.decay
      refine ⟨M, fun η hη b b' X X' hX hX' => ?_, hr⟩
      rw [mixedSecondDeriv_eq_fderiv_fderiv (two (hc hη))]
      exact hM η hη b b' X X' hX hX'
    · rw [deriv_update_eq_fderiv (one (hc hη))]
      exact h.fderiv_le η hη b X hX
    · rw [mixedSecondDeriv_eq_fderiv_fderiv (two (hc hη))]
      exact h.fderiv_fderiv_le η hη b b' X X' hX hX'
theorem abs_convex_comb_le {c a b A B : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |c * a + (1 - c) * b| ≤ c * A + (1 - c) * B := by
  have h2 : 0 ≤ 1 - c := sub_nonneg.2 h1
  calc |c * a + (1 - c) * b| ≤ |c * a| + |(1 - c) * b| := abs_add_le _ _
    _ = c * |a| + (1 - c) * |b| := by rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h2]
    _ ≤ c * A + (1 - c) * B := by gcongr
theorem ChartSetting.HasHessianDecay.convexComb (hu : s.HasHessianDecay u lam C)
    (hw : s.HasHessianDecay w lam C) {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    s.HasHessianDecay (fun η => c * u η + (1 - c) * w η) lam C := by
  have h2 : 0 ≤ 1 - c := sub_nonneg.2 h1
  have hH : ∀ η, s.InBalls η → fderiv ℝ (fderiv ℝ fun η => c * u η + (1 - c) * w η) η =
      c • fderiv ℝ (fderiv ℝ u) η + (1 - c) • fderiv ℝ (fderiv ℝ w) η := by
    intro η hη
    have hu2 : ContDiffAt ℝ 2 u η := (hu.contDiffAt hη).of_le (by norm_num)
    have hw2 : ContDiffAt ℝ 2 w η := (hw.contDiffAt hη).of_le (by norm_num)
    rw [fderiv_fderiv_add (contDiffAt_const.mul hu2) (contDiffAt_const.mul hw2),
      fderiv_fderiv_const_mul c hu2, fderiv_fderiv_const_mul (1 - c) hw2]
  have hF : ∀ η, s.InBalls η → fderiv ℝ (fun η => c * u η + (1 - c) * w η) η =
      c • fderiv ℝ u η + (1 - c) • fderiv ℝ w η := by
    intro η hη
    have hu1 : DifferentiableAt ℝ u η := (hu.contDiffAt hη).differentiableAt (by norm_num)
    have hw1 : DifferentiableAt ℝ w η := (hw.contDiffAt hη).differentiableAt (by norm_num)
    rw [fderiv_fun_add (hu1.const_mul c) (hw1.const_mul (1 - c)), fderiv_const_mul hu1,
      fderiv_const_mul hw1]
  refine ⟨?_, fun η hη v => ?_, ?_, fun η hη b X hX => ?_, fun η hη b b' X X' hX hX' => ?_⟩
  · obtain ⟨U, hU, hb, hc⟩ := hu.contDiffOn
    obtain ⟨U', hU', hb', hc'⟩ := hw.contDiffOn
    refine ⟨U ∩ U', hU.inter hU', fun η hη => ⟨hb η hη, hb' η hη⟩, ?_⟩
    exact (contDiffOn_const.mul (hc.mono Set.inter_subset_left)).add
      (contDiffOn_const.mul (hc'.mono Set.inter_subset_right))
  · rw [hH η hη]
    have a1 := hu.lower η hη v
    have a2 := hw.lower η hη v
    simp only [add_apply, smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left a1 h0, mul_le_mul_of_nonneg_left a2 h2]
  · obtain ⟨M, hM, hr⟩ := hu.decay
    obtain ⟨M', hM', hr'⟩ := hw.decay
    refine ⟨fun b b' => c * M b b' + (1 - c) * M' b b', fun η hη b b' X X' hX hX' => ?_, fun b => ?_⟩
    · rw [hH η hη]
      simp only [add_apply, smul_apply, smul_eq_mul]
      exact abs_convex_comb_le h0 h1 (hM η hη b b' X X' hX hX') (hM' η hη b b' X X' hX hX')
    · have e : ∑ b', (c * M b b' + (1 - c) * M' b b') *
            (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) =
          c * ∑ b', M b b' * (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) +
            (1 - c) * ∑ b', M' b b' *
              (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b' _ => by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left (hr b) h0, mul_le_mul_of_nonneg_left (hr' b) h2]
  · rw [hF η hη]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have := abs_convex_comb_le h0 h1 (hu.fderiv_le η hη b X hX) (hw.fderiv_le η hη b X hX)
    linarith
  · rw [hH η hη]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have := abs_convex_comb_le h0 h1 (hu.fderiv_fderiv_le η hη b b' X X' hX hX')
      (hw.fderiv_fderiv_le η hη b b' X X' hX hX')
    linarith
theorem sqNormForm_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) (e : ι → ImCoords) (b : ι)
    (X : ImCoords) :
    sqNormForm A e (Pi.single b X) = if b ∈ A then 2 * ⟪e b, X⟫ else 0 := by
  have h : ∀ c, ⟪e c, (Pi.single b X : ι → ImCoords) c⟫ = if c = b then ⟪e c, X⟫ else 0 := by
    intro c
    by_cases hb : c = b
    · subst hb
      simp
    · simp [hb]
  rw [sqNormForm_apply]
  simp_rw [h]
  rw [Finset.sum_ite_eq']
  split_ifs <;> simp
theorem abs_sqNormForm_single_single_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) (b b' : ι)
    {X X' : ImCoords} (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    |sqNormForm A (Pi.single b X) (Pi.single b' X')| ≤ if b = b' then 2 else 0 := by
  rw [sqNormForm_single]
  by_cases hA : b' ∈ A
  · by_cases hb : b = b'
    · subst hb
      have h := abs_real_inner_le_norm X X'
      rw [hX, hX', one_mul] at h
      simp only [hA, if_true, Pi.single_eq_same, abs_mul, abs_two]
      linarith
    · simp [hA, hb]
  · by_cases hb : b = b' <;> simp [hA, hb]
theorem bondBlockDist_self (b : TorusBond (n * R.params.side)) : bondBlockDist (R := R) (n := n) b b = 0 := by
  simp [bondBlockDist, TorusFields.supDist]
theorem sum_diag_mul_weight_eq_zero (a : ℝ) (b : s.free) :
    ∑ b', (if b = b' then a else 0) *
      (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) = 0 := by
  refine Finset.sum_eq_zero fun b' _ => ?_
  by_cases h : b = b'
  · subst h
    simp [bondBlockDist_self]
  · simp [h]
theorem coordNorm_eq_norm (v : ImCoords) : coordNorm v = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
theorem norm_le_ballRadius_of_inBalls {η : FreeCoords s.free} (hη : s.InBalls η) (b : s.free) :
    ‖η b‖ ≤ R.ballRadius := by
  rw [← coordNorm_eq_norm]
  exact hη b
theorem hasHessianDecay_gaussian (hx : 0 ≤ R.coupling) (hlam : 0 ≤ lam) (hρ : 0 ≤ R.ballRadius)
    (hC : lam * (1 + R.ballRadius) ≤ C) :
    s.HasHessianDecay (fun η => R.coupling * lam / 2 * ∑ b, ‖η b‖ ^ 2) lam C := by
  have hxl : 0 ≤ R.coupling * lam := mul_nonneg hx hlam
  have hlC : lam ≤ C := by nlinarith [mul_nonneg hlam hρ]
  have hsq : ContDiff ℝ 3 (fun η : FreeCoords s.free => ∑ b, ‖η b‖ ^ 2) := contDiff_sum_sq_norm Finset.univ
  have hH : ∀ η : FreeCoords s.free, fderiv ℝ (fderiv ℝ fun η : FreeCoords s.free =>
      R.coupling * lam / 2 * ∑ b, ‖η b‖ ^ 2) η = (R.coupling * lam / 2) • sqNormForm Finset.univ := by
    intro η
    rw [fderiv_fderiv_const_mul _ (hsq.contDiffAt.of_le (by norm_num)), fderiv_fderiv_sum_sq_norm]
  have hF : ∀ η : FreeCoords s.free, fderiv ℝ (fun η : FreeCoords s.free =>
      R.coupling * lam / 2 * ∑ b, ‖η b‖ ^ 2) η = (R.coupling * lam / 2) • sqNormForm Finset.univ η := by
    intro η
    rw [fderiv_const_mul (hsq.contDiffAt.differentiableAt (by norm_num)), fderiv_sum_sq_norm]
  refine ⟨⟨Set.univ, isOpen_univ, fun _ _ => trivial, (contDiff_const.mul hsq).contDiffOn⟩,
    fun η _ v => ?_, ⟨fun b b' => if b = b' then R.coupling * lam else 0, fun η _ b b' X X' hX hX' => ?_,
      fun b => ?_⟩, fun η hη b X hX => ?_, fun η _ b b' X X' hX hX' => ?_⟩
  · rw [hH η]
    simp only [smul_apply, smul_eq_mul, sqNormForm_apply, real_inner_self_eq_norm_sq]
    have : 0 ≤ ∑ b, ‖v b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    nlinarith [mul_nonneg hxl this]
  · rw [hH η]
    simp only [smul_apply, smul_eq_mul]
    have h := abs_sqNormForm_single_single_le Finset.univ b b' hX hX'
    rw [abs_mul, abs_of_nonneg (by positivity)]
    by_cases hb : b = b'
    · simp only [hb, if_true] at h ⊢
      nlinarith
    · simp only [hb, if_false] at h ⊢
      have h0 := abs_nonneg (sqNormForm (Finset.univ : Finset s.free) (Pi.single b X) (Pi.single b' X'))
      have : |sqNormForm (Finset.univ : Finset s.free) (Pi.single b X) (Pi.single b' X')| = 0 :=
        le_antisymm h h0
      rw [this]
      simp
  · rw [sum_diag_mul_weight_eq_zero]
    positivity
  · rw [hF η]
    simp only [smul_apply, smul_eq_mul, sqNormForm_single, Finset.mem_univ, if_true]
    have h := abs_real_inner_le_norm (η b) X
    rw [hX, mul_one] at h
    have h2 := norm_le_ballRadius_of_inBalls hη b
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ R.coupling * lam / 2), abs_two]
    have h3 : |⟪η b, X⟫| ≤ R.ballRadius := h.trans h2
    have h4 : R.coupling * lam * R.ballRadius ≤ C * R.coupling := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hxl]
  · rw [hH η]
    simp only [smul_apply, smul_eq_mul]
    have h := abs_sqNormForm_single_single_le Finset.univ b b' hX hX'
    have h2 : |sqNormForm (Finset.univ : Finset s.free) (Pi.single b X) (Pi.single b' X')| ≤ 2 := by
      refine h.trans ?_
      split_ifs <;> norm_num
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ R.coupling * lam / 2)]
    have h4 : R.coupling * lam ≤ C * R.coupling := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hxl]
open Classical in
def restrictMap {ι : Type*} [Fintype ι] (X : Finset ι) : (ι → ImCoords) →L[ℝ] (ι → ImCoords) :=
  ContinuousLinearMap.pi fun b => if b ∈ X then ContinuousLinearMap.proj b else 0
open Classical in
theorem restrictMap_apply {ι : Type*} [Fintype ι] (X : Finset ι) (e : ι → ImCoords) (b : ι) :
    restrictMap X e b = if b ∈ X then e b else 0 := by
  by_cases h : b ∈ X <;> simp [restrictMap, h]
theorem restrictTo_eq_restrictMap (X : Finset s.free) (η : FreeCoords s.free) :
    s.restrictTo X η = restrictMap X η := by
  funext b
  rw [restrictMap_apply]
  by_cases h : b ∈ X <;> simp [ChartSetting.restrictTo, h]
theorem restrictMap_single_of_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Finset ι} {b : ι} (h : b ∈ X)
    (Y : ImCoords) : restrictMap X (Pi.single b Y) = Pi.single b Y := by
  funext c
  rw [restrictMap_apply]
  by_cases h2 : c = b
  · subst h2
    simp [h]
  · simp [h2]
theorem restrictMap_single_of_not_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Finset ι} {b : ι}
    (h : b ∉ X) (Y : ImCoords) : restrictMap X (Pi.single b Y) = 0 := by
  funext c
  rw [restrictMap_apply]
  by_cases h2 : c = b
  · subst h2
    simp [h]
  · simp [h2]
theorem inBalls_restrictMap (hρ : 0 ≤ R.ballRadius) (X : Finset s.free) {η : FreeCoords s.free}
    (hη : s.InBalls η) : s.InBalls (restrictMap X η) := by
  intro b
  rw [restrictMap_apply]
  split_ifs
  · exact hη b
  · rw [coordNorm_eq_norm, norm_zero]
    exact hρ
open Classical in
theorem ChartSetting.HasHessianDecay.restrict_add_gaussian (hu : s.HasHessianDecay u lam C)
    (hx : 0 ≤ R.coupling) (hlam : 0 ≤ lam) (hρ : 0 ≤ R.ballRadius) (hC : lam * (1 + R.ballRadius) ≤ C)
    (X : Finset s.free) :
    s.HasHessianDecay (fun η => u (s.restrictTo X η) +
      R.coupling * lam / 2 * ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2) lam C := by
  have hxl : 0 ≤ R.coupling * lam := mul_nonneg hx hlam
  have hlC : lam ≤ C := by nlinarith [mul_nonneg hlam hρ]
  set A : Finset s.free := Finset.univ \ X with hA
  have hmem : ∀ b, b ∈ A ↔ b ∉ X := fun b => by simp [hA]
  simp only [restrictTo_eq_restrictMap]
  set P : FreeCoords s.free →L[ℝ] FreeCoords s.free := restrictMap X with hP
  have hsq : ContDiff ℝ 3 (fun η : FreeCoords s.free => ∑ b ∈ A, ‖η b‖ ^ 2) := contDiff_sum_sq_norm A
  have hsq2 : ∀ η : FreeCoords s.free, ContDiffAt ℝ 2 (fun η : FreeCoords s.free =>
      R.coupling * lam / 2 * ∑ b ∈ A, ‖η b‖ ^ 2) η := fun η =>
    contDiffAt_const.mul (hsq.contDiffAt.of_le (by norm_num))
  have hcomp : ∀ {η : FreeCoords s.free}, s.InBalls η → ContDiffAt ℝ 3 (fun q => u (P q)) η := fun hη =>
    ContDiffAt.comp _ (hu.contDiffAt (inBalls_restrictMap hρ X hη)) P.contDiff.contDiffAt
  have hH : ∀ η, s.InBalls η → ∀ e e' : FreeCoords s.free,
      fderiv ℝ (fderiv ℝ fun η => u (P η) + R.coupling * lam / 2 * ∑ b ∈ A, ‖η b‖ ^ 2) η e e' =
        fderiv ℝ (fderiv ℝ u) (P η) (P e) (P e') + R.coupling * lam / 2 * sqNormForm A e e' := by
    intro η hη e e'
    have h2 : ContDiffAt ℝ 2 u (P η) := (hu.contDiffAt (inBalls_restrictMap hρ X hη)).of_le (by norm_num)
    rw [fderiv_fderiv_add ((hcomp hη).of_le (by norm_num)) (hsq2 η),
      fderiv_fderiv_const_mul _ (hsq.contDiffAt.of_le (by norm_num)), fderiv_fderiv_sum_sq_norm]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [fderiv_fderiv_comp_clm_apply P h2]
  have hF : ∀ η, s.InBalls η → ∀ e : FreeCoords s.free,
      fderiv ℝ (fun η => u (P η) + R.coupling * lam / 2 * ∑ b ∈ A, ‖η b‖ ^ 2) η e =
        fderiv ℝ u (P η) (P e) + R.coupling * lam / 2 * sqNormForm A η e := by
    intro η hη e
    have h1 : DifferentiableAt ℝ u (P η) :=
      (hu.contDiffAt (inBalls_restrictMap hρ X hη)).differentiableAt (by norm_num)
    have h3 : HasFDerivAt (fun q => u (P q)) ((fderiv ℝ u (P η)).comp P) η :=
      h1.hasFDerivAt.comp η P.hasFDerivAt
    have h4 : HasFDerivAt (fun η : FreeCoords s.free => R.coupling * lam / 2 * ∑ b ∈ A, ‖η b‖ ^ 2)
        ((R.coupling * lam / 2) • sqNormForm A η) η := (hasFDerivAt_sum_sq_norm A η).const_mul _
    have h5 : HasFDerivAt (fun η => u (P η) + R.coupling * lam / 2 * ∑ b ∈ A, ‖η b‖ ^ 2)
        ((fderiv ℝ u (P η)).comp P + (R.coupling * lam / 2) • sqNormForm A η) η := h3.add h4
    rw [h5.fderiv]
    simp
  have hPs : ∀ (b : s.free) (Y : ImCoords), b ∈ X → P (Pi.single b Y) = Pi.single b Y := fun b Y h =>
    restrictMap_single_of_mem h Y
  have hPz : ∀ (b : s.free) (Y : ImCoords), b ∉ X → P (Pi.single b Y) = 0 := fun b Y h =>
    restrictMap_single_of_not_mem h Y
  refine ⟨?_, fun η hη v => ?_, ?_, fun η hη b Y hY => ?_, fun η hη b b' Y Y' hY hY' => ?_⟩
  · obtain ⟨U, hU, hb, hc⟩ := hu.contDiffOn
    refine ⟨P ⁻¹' U, hU.preimage P.continuous, fun η hη => hb _ (inBalls_restrictMap hρ X hη), ?_⟩
    refine ContDiffOn.add ?_ (contDiff_const.mul hsq).contDiffOn
    exact hc.comp P.contDiff.contDiffOn fun _ h => h
  · rw [hH η hη]
    have a1 := hu.lower (P η) (inBalls_restrictMap hρ X hη) (P v)
    have e1 : ∑ b, ‖P v b‖ ^ 2 = ∑ b ∈ X, ‖v b‖ ^ 2 := by
      have : ∀ b, ‖P v b‖ ^ 2 = if b ∈ X then ‖v b‖ ^ 2 else 0 := by
        intro b
        rw [hP, restrictMap_apply]
        split_ifs <;> simp
      simp_rw [this]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have e2 : sqNormForm A v v = 2 * ∑ b ∈ A, ‖v b‖ ^ 2 := by
      simp only [sqNormForm_apply, real_inner_self_eq_norm_sq]
    have e3 : ∑ b ∈ A, ‖v b‖ ^ 2 + ∑ b ∈ X, ‖v b‖ ^ 2 = ∑ b, ‖v b‖ ^ 2 :=
      Finset.sum_sdiff (Finset.subset_univ X)
    have hA0 : 0 ≤ ∑ b ∈ A, ‖v b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    rw [e1] at a1
    rw [e2, ← e3]
    nlinarith [mul_nonneg hxl hA0]
  · obtain ⟨M, hM, hr⟩ := hu.decay
    refine ⟨fun b b' => M b b' + if b = b' then R.coupling * lam else 0, fun η hη b b' Y Y' hY hY' => ?_,
      fun b => ?_⟩
    · have hPη := inBalls_restrictMap hρ X hη
      have hM0 : 0 ≤ M b b' := (abs_nonneg _).trans (hM η hη b b' Y Y' hY hY')
      rw [hH η hη]
      have h1 : |fderiv ℝ (fderiv ℝ u) (P η) (P (Pi.single b Y)) (P (Pi.single b' Y'))| ≤ M b b' := by
        by_cases hb : b ∈ X
        · by_cases hb' : b' ∈ X
          · rw [hPs b Y hb, hPs b' Y' hb']
            exact hM _ hPη b b' Y Y' hY hY'
          · rw [hPz b' Y' hb']
            simpa using hM0
        · rw [hPz b Y hb]
          simpa using hM0
      have h2 : |R.coupling * lam / 2 * sqNormForm A (Pi.single b Y) (Pi.single b' Y')| ≤
          if b = b' then R.coupling * lam else 0 := by
        have h := abs_sqNormForm_single_single_le A b b' hY hY'
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ R.coupling * lam / 2)]
        split_ifs at h ⊢ with hb
        · nlinarith
        · have h' : |sqNormForm A (Pi.single b Y) (Pi.single b' Y')| = 0 := le_antisymm h (abs_nonneg _)
          rw [h']
          simp
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
    · have e : ∑ b', (M b b' + if b = b' then R.coupling * lam else 0) *
            (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) =
          ∑ b', M b b' * (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) +
            ∑ b', (if b = b' then R.coupling * lam else 0) *
              (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b' _ => by ring
      rw [e, sum_diag_mul_weight_eq_zero, add_zero]
      exact hr b
  · rw [hF η hη]
    by_cases hb : b ∈ X
    · have hnA : b ∉ A := fun h => (hmem b).1 h hb
      rw [hPs b Y hb, sqNormForm_single, if_neg hnA, mul_zero, add_zero]
      exact hu.fderiv_le _ (inBalls_restrictMap hρ X hη) b Y hY
    · have hAb : b ∈ A := (hmem b).2 hb
      rw [hPz b Y hb, sqNormForm_single, if_pos hAb, map_zero, zero_add]
      have h := abs_real_inner_le_norm (η b) Y
      rw [hY, mul_one] at h
      have h3 : |⟪η b, Y⟫| ≤ R.ballRadius := h.trans (norm_le_ballRadius_of_inBalls hη b)
      have h4 : R.coupling * lam * R.ballRadius ≤ C * R.coupling := by nlinarith
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ R.coupling * lam / 2), abs_two]
      nlinarith [mul_le_mul_of_nonneg_left h3 hxl]
  · rw [hH η hη]
    have hC0 : 0 ≤ C * R.coupling := mul_nonneg (hlam.trans hlC) hx
    by_cases hb' : b' ∈ X
    · have hnA : b' ∉ A := fun h => (hmem b').1 h hb'
      rw [hPs b' Y' hb', sqNormForm_single, if_neg hnA, mul_zero, add_zero]
      by_cases hb : b ∈ X
      · rw [hPs b Y hb]
        exact hu.fderiv_fderiv_le _ (inBalls_restrictMap hρ X hη) b b' Y Y' hY hY'
      · rw [hPz b Y hb]
        simpa using hC0
    · rw [hPz b' Y' hb']
      simp only [map_zero, zero_add]
      have h := abs_sqNormForm_single_single_le A b b' hY hY'
      have h2 : |sqNormForm A (Pi.single b Y) (Pi.single b' Y')| ≤ 2 := by
        refine h.trans ?_
        split_ifs <;> norm_num
      have h4 : R.coupling * lam ≤ C * R.coupling := by nlinarith
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ R.coupling * lam / 2)]
      nlinarith [mul_le_mul_of_nonneg_left h2 hxl]
theorem ChartSetting.HasFullDecay.convexComb (hu : s.HasFullDecay u lam C) (hw : s.HasFullDecay w lam C)
    {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : s.HasFullDecay (fun η => c * u η + (1 - c) * w η) lam C :=
  hasFullDecay_iff_hasHessianDecay.2
    ((hasFullDecay_iff_hasHessianDecay.1 hu).convexComb (hasFullDecay_iff_hasHessianDecay.1 hw) h0 h1)
open Classical in
theorem ChartSetting.HasFullDecay.restrict (hu : s.HasFullDecay u lam C) (hx : 0 ≤ R.coupling) (hlam : 0 ≤ lam)
    (hρ : 0 ≤ R.ballRadius) (hC : lam * (1 + R.ballRadius) ≤ C) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1)
    (X : Finset s.free) :
    s.HasFullDecay (fun η => v * u η + (1 - v) * (u (s.restrictTo X η) +
      R.coupling * lam / 2 * ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2)) lam C :=
  hasFullDecay_iff_hasHessianDecay.2 ((hasFullDecay_iff_hasHessianDecay.1 hu).convexComb
    ((hasFullDecay_iff_hasHessianDecay.1 hu).restrict_add_gaussian hx hlam hρ hC X) h0 h1)
theorem hasFullDecay_gaussian (hx : 0 ≤ R.coupling) (hlam : 0 ≤ lam) (hρ : 0 ≤ R.ballRadius)
    (hC : lam * (1 + R.ballRadius) ≤ C) :
    s.HasFullDecay (fun η => R.coupling * lam / 2 * ∑ b, ‖η b‖ ^ 2) lam C :=
  hasFullDecay_iff_hasHessianDecay.2 (hasHessianDecay_gaussian hx hlam hρ hC)
end Chart
end YangMills.Construction.StepSettings
end
