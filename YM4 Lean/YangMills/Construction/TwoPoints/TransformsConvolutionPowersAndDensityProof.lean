import YangMills.Construction.Splines.CubicSplineBasicFactsProofs
import YangMills.Construction.Torus.CollinearQuadruplesProof
import YangMills.Construction.Analysis.PlancherelLine
import YangMills.Construction.HilbertSpaces.PositiveSpectralMeasureOfAVectorProof
import YangMills.Construction.TwoPoints.SmearedGroupAndTheTwoBoundsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology ENNReal Convolution
noncomputable section
namespace YangMills.Construction.TwoPoints.LineTransforms
def phaseFn (q s : ℝ) : ℂ := Complex.exp (Complex.I * (s : ℂ) * (q : ℂ))
theorem norm_phaseFn (q s : ℝ) : ‖phaseFn q s‖ = 1 := by apply _root_.YangMills.Construction.Splines.CubicSplineLemmas.norm_fourierPhase <;> assumption
theorem continuous_phaseFn (q : ℝ) : Continuous (phaseFn q) := by apply _root_.YangMills.Construction.Splines.CubicSplineLemmas.continuous_fourierPhase <;> assumption
theorem phaseFn_add (q s t : ℝ) : phaseFn q (s + t) = phaseFn q s * phaseFn q t := by
  unfold phaseFn
  rw [← Complex.exp_add]
  push_cast
  ring_nf
theorem lineTransform_eq_integral (f : ℝ → ℂ) (q : ℝ) :
    lineTransform f q = ∫ s : ℝ, f s * phaseFn q s := rfl
theorem continuous_of_mem_ccIn {f : ℝ → ℂ} (hf : f ∈ ccIn (Set.univ : Set ℝ)) :
    Continuous f := ((mem_ccIn_iff _ _).mp hf).1
theorem hasCompactSupport_of_mem_ccIn {f : ℝ → ℂ} (hf : f ∈ ccIn (Set.univ : Set ℝ)) :
    HasCompactSupport f := ((mem_ccIn_iff _ _).mp hf).2.1
theorem mem_ccIn_of {f : ℝ → ℂ} (h1 : Continuous f) (h2 : HasCompactSupport f) :
    f ∈ ccIn (Set.univ : Set ℝ) :=
  (mem_ccIn_iff _ _).mpr ⟨h1, h2, Set.subset_univ _⟩
theorem contDiff_of_mem_c1 {f : ℝ → ℂ} (hf : f ∈ c1Functions) : ContDiff ℝ 1 f := hf.1
theorem hasCompactSupport_of_mem_c1 {f : ℝ → ℂ} (hf : f ∈ c1Functions) :
    HasCompactSupport f := hf.2.1
theorem mem_c1_of {f : ℝ → ℂ} (h1 : ContDiff ℝ 1 f) (h2 : HasCompactSupport f) :
    f ∈ c1Functions := ⟨h1, h2, Set.subset_univ _⟩
theorem mem_ccIn_of_mem_c1 {f : ℝ → ℂ} (hf : f ∈ c1Functions) :
    f ∈ ccIn (Set.univ : Set ℝ) :=
  mem_ccIn_of (contDiff_of_mem_c1 hf).continuous (hasCompactSupport_of_mem_c1 hf)
theorem integrable_of_continuous_of_compact {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (h1 : Continuous f) (h2 : HasCompactSupport f) : Integrable f :=
  h1.integrable_of_hasCompactSupport h2
theorem l1Norm_eq_integral {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (h : AEStronglyMeasurable f volume) : l1Norm f = ∫ s, ‖f s‖ := by
  rw [integral_norm_eq_lintegral_enorm h]
  rfl
theorem mul_coord_mem_ccIn {f : ℝ → ℂ} (hf : f ∈ ccIn (Set.univ : Set ℝ)) :
    (fun s : ℝ => Complex.I * (s : ℂ) * f s) ∈ ccIn (Set.univ : Set ℝ) := by
  refine mem_ccIn_of (by have := continuous_of_mem_ccIn hf; fun_prop) ?_
  exact (hasCompactSupport_of_mem_ccIn hf).mul_left
theorem integrable_mul_phaseFn {f : ℝ → ℂ} (hf : f ∈ ccIn (Set.univ : Set ℝ))
    (q : ℝ) : Integrable fun s => f s * phaseFn q s :=
  integrable_of_continuous_of_compact ((continuous_of_mem_ccIn hf).mul (continuous_phaseFn q))
    (hasCompactSupport_of_mem_ccIn hf).mul_right
theorem continuous_lineTransform {f : ℝ → ℂ} (hf : f ∈ ccIn (Set.univ : Set ℝ)) :
    Continuous (lineTransform f) := by
  have hc := continuous_of_mem_ccIn hf
  have hi : Integrable fun s => ‖f s‖ :=
    (integrable_of_continuous_of_compact hc (hasCompactSupport_of_mem_ccIn hf)).norm
  refine continuous_of_dominated (bound := fun s => ‖f s‖) ?_ ?_ hi ?_
  · intro q
    exact (hc.mul (continuous_phaseFn q)).aestronglyMeasurable
  · intro q
    refine Eventually.of_forall fun s => ?_
    change ‖f s * phaseFn q s‖ ≤ ‖f s‖
    rw [norm_mul, norm_phaseFn, mul_one]
  · refine Eventually.of_forall fun s => ?_
    fun_prop
theorem norm_lineTransform_le {f : ℝ → ℂ} (hf : f ∈ ccIn (Set.univ : Set ℝ))
    (q : ℝ) : ‖lineTransform f q‖ ≤ l1Norm f := by
  rw [l1Norm_eq_integral (continuous_of_mem_ccIn hf).aestronglyMeasurable, lineTransform_eq_integral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext s
  rw [norm_mul, norm_phaseFn, mul_one]
theorem hasDerivAt_lineTransform {f : ℝ → ℂ} (hf : f ∈ ccIn (Set.univ : Set ℝ))
    (q : ℝ) : HasDerivAt (lineTransform f)
      (lineTransform (fun s : ℝ => Complex.I * (s : ℂ) * f s) q) q := by
  have hc := continuous_of_mem_ccIn hf
  have hm := mul_coord_mem_ccIn hf
  have hbound : Integrable fun s : ℝ => ‖Complex.I * (s : ℂ) * f s‖ :=
    (integrable_of_continuous_of_compact (continuous_of_mem_ccIn hm)
      (hasCompactSupport_of_mem_ccIn hm)).norm
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (x : ℝ) (s : ℝ) => f s * phaseFn x s)
    (F' := fun (x : ℝ) (s : ℝ) => (Complex.I * (s : ℂ) * f s) * phaseFn x s)
    (x₀ := q) (s := Set.univ) (bound := fun s : ℝ => ‖Complex.I * (s : ℂ) * f s‖)
    Filter.univ_mem
    (Eventually.of_forall fun x => (hc.mul (continuous_phaseFn x)).aestronglyMeasurable)
    (integrable_mul_phaseFn hf q)
    ((continuous_of_mem_ccIn hm).mul (continuous_phaseFn q)).aestronglyMeasurable
    (Eventually.of_forall fun s x _ => by rw [norm_mul, norm_phaseFn, mul_one])
    hbound
    (Eventually.of_forall fun s x _ => by
      have h1 : HasDerivAt (fun y : ℝ => Complex.I * (s : ℂ) * (y : ℂ)) (Complex.I * (s : ℂ)) x := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (Complex.I * (s : ℂ))
      have h2 := h1.cexp.const_mul (f s)
      have e : f s * (Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) * (Complex.I * (s : ℂ))) =
          (Complex.I * (s : ℂ) * f s) * phaseFn x s := by
        unfold phaseFn
        ring
      rw [← e]
      exact h2)
  exact key.2
theorem transformDerivBound_proof : TransformDerivBound := by
  intro f hf
  have hd : deriv (lineTransform f) = lineTransform (fun s : ℝ => Complex.I * (s : ℂ) * f s) :=
    funext fun q => (hasDerivAt_lineTransform hf q).deriv
  refine ⟨?_, ?_, hd, norm_lineTransform_le hf⟩
  · refine contDiff_one_iff_deriv.mpr ⟨fun q => (hasDerivAt_lineTransform hf q).differentiableAt, ?_⟩
    rw [hd]
    exact continuous_lineTransform (mul_coord_mem_ccIn hf)
  · intro q
    rw [hd]
    rfl
theorem convolve_eq_convolution (f g : ℝ → ℂ) :
    convolve f g = f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] g := by
  funext x
  rfl
theorem convolve_mem_c1 {f g : ℝ → ℂ} (hf : f ∈ c1Functions)
    (hg : g ∈ c1Functions) : convolve f g ∈ c1Functions := by
  rw [convolve_eq_convolution]
  refine mem_c1_of ?_ ?_
  · exact (hasCompactSupport_of_mem_c1 hg).contDiff_convolution_right _
      (contDiff_of_mem_c1 hf).continuous.locallyIntegrable (contDiff_of_mem_c1 hg)
  · exact (hasCompactSupport_of_mem_c1 hf).convolution _ (hasCompactSupport_of_mem_c1 hg)
theorem l1Norm_convolve_le {f g : ℝ → ℂ} (hf : f ∈ c1Functions)
    (hg : g ∈ c1Functions) :
    l1Norm (convolve f g) ≤ l1Norm f * l1Norm g := by
  have hfc := (contDiff_of_mem_c1 hf).continuous
  have hgc := (contDiff_of_mem_c1 hg).continuous
  have hif : Integrable fun s => ‖f s‖ :=
    (integrable_of_continuous_of_compact hfc (hasCompactSupport_of_mem_c1 hf)).norm
  have hig : Integrable fun s => ‖g s‖ :=
    (integrable_of_continuous_of_compact hgc (hasCompactSupport_of_mem_c1 hg)).norm
  have hconv := contDiff_of_mem_c1 (convolve_mem_c1 hf hg)
  rw [l1Norm_eq_integral hconv.continuous.aestronglyMeasurable,
    l1Norm_eq_integral hfc.aestronglyMeasurable, l1Norm_eq_integral hgc.aestronglyMeasurable]
  have hI := hif.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hig
  have hE := integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) (ν := volume)
    hif hig
  simp only [ContinuousLinearMap.mul_apply'] at hE
  rw [← hE]
  refine integral_mono (integrable_of_continuous_of_compact hconv.continuous
    (hasCompactSupport_of_mem_c1 (convolve_mem_c1 hf hg))).norm hI fun x => ?_
  change ‖∫ z, f z * g (x - z)‖ ≤ ∫ z, ‖f z‖ * ‖g (x - z)‖
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_mul]
theorem lineTransform_convolve {f g : ℝ → ℂ} (hf : f ∈ c1Functions)
    (hg : g ∈ c1Functions) :
    lineTransform (convolve f g) = lineTransform f * lineTransform g := by
  funext q
  have hif := integrable_mul_phaseFn (mem_ccIn_of_mem_c1 hf) q
  have hig := integrable_mul_phaseFn (mem_ccIn_of_mem_c1 hg) q
  have hE := integral_convolution (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume) (ν := volume)
    hif hig
  simp only [ContinuousLinearMap.mul_apply'] at hE
  have hfun : (fun s => convolve f g s * phaseFn q s) =
      (fun s => f s * phaseFn q s) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
        (fun s => g s * phaseFn q s) := by
    funext s
    change (∫ z, f z * g (s - z)) * phaseFn q s =
      ∫ z, (f z * phaseFn q z) * (g (s - z) * phaseFn q (s - z))
    rw [← integral_mul_const]
    congr 1
    funext z
    have e : phaseFn q s = phaseFn q z * phaseFn q (s - z) := by
      rw [← phaseFn_add]
      congr 1
      ring
    rw [e]
    ring
  rw [lineTransform_eq_integral, hfun, hE]
  rfl
theorem conj_phaseFn (q s : ℝ) : (starRingEnd ℂ) (phaseFn q s) = phaseFn q (-s) := by
  unfold phaseFn
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]
theorem reflectConj_mem_c1 {f : ℝ → ℂ} (hf : f ∈ c1Functions) :
    reflectConj f ∈ c1Functions := by
  refine mem_c1_of ?_ ?_
  · have h1 : ContDiff ℝ 1 (fun s : ℝ => f (-s)) := (contDiff_of_mem_c1 hf).comp contDiff_neg
    exact Complex.conjCLE.contDiff.comp h1
  · have h1 := (hasCompactSupport_of_mem_c1 hf).comp_homeomorph (Homeomorph.neg ℝ)
    exact h1.comp_left (g := starRingEnd ℂ) (map_zero _)
theorem lineTransform_reflectConj (f : ℝ → ℂ) :
    lineTransform (reflectConj f) = conjFun (lineTransform f) := by
  funext q
  change ∫ s, (starRingEnd ℂ) (f (-s)) * phaseFn q s = (starRingEnd ℂ) (∫ s, f s * phaseFn q s)
  rw [← integral_conj, ← integral_neg_eq_self (fun s => (starRingEnd ℂ) (f s * phaseFn q s)) volume]
  congr 1
  funext s
  rw [map_mul, conj_phaseFn, neg_neg]
theorem convTransformRules_proof : ConvTransformRules := fun _ hf _ hg =>
  ⟨convolve_mem_c1 hf hg, reflectConj_mem_c1 hf, l1Norm_convolve_le hf hg,
    lineTransform_convolve hf hg, lineTransform_reflectConj _⟩
theorem continuous_deriv_of_mem_c1 {f : ℝ → ℂ} (hf : f ∈ c1Functions) :
    Continuous (deriv f) := (contDiff_of_mem_c1 hf).continuous_deriv le_rfl
theorem hasCompactSupport_deriv_of_mem_c1 {f : ℝ → ℂ} (hf : f ∈ c1Functions) :
    HasCompactSupport (deriv f) := (hasCompactSupport_of_mem_c1 hf).deriv
theorem transformDecay_proof : TransformDecay := by
  intro f hf q hq
  have hc := (contDiff_of_mem_c1 hf).continuous
  have hcs := hasCompactSupport_of_mem_c1 hf
  have hd := continuous_deriv_of_mem_c1 hf
  have hds := hasCompactSupport_deriv_of_mem_c1 hf
  have hdiff : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    ((contDiff_of_mem_c1 hf).differentiable (by norm_num) x).hasDerivAt
  have hph : ∀ x : ℝ, HasDerivAt (phaseFn q) (phaseFn q x * (Complex.I * (q : ℂ))) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => Complex.I * (y : ℂ) * (q : ℂ)) (Complex.I * (q : ℂ)) x := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul Complex.I).mul_const (q : ℂ)
      simpa using this
    exact h1.cexp
  have hw : Continuous fun x => phaseFn q x * (Complex.I * (q : ℂ)) :=
    (continuous_phaseFn q).mul continuous_const
  have parts := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f) (v := phaseFn q)
    (u' := deriv f) (v' := fun x => phaseFn q x * (Complex.I * (q : ℂ)))
    (fun x _ => hdiff x) (fun x _ => hph x)
    (integrable_of_continuous_of_compact (hc.mul hw) hcs.mul_right)
    (integrable_of_continuous_of_compact (hd.mul (continuous_phaseFn q)) hds.mul_right)
    (integrable_of_continuous_of_compact (hc.mul (continuous_phaseFn q)) hcs.mul_right)
  have e1 : ∫ x, f x * (phaseFn q x * (Complex.I * (q : ℂ))) =
      lineTransform f q * (Complex.I * (q : ℂ)) := by
    rw [lineTransform_eq_integral, ← integral_mul_const]
    congr 1
    funext x
    ring
  rw [e1] at parts
  have hn : ‖lineTransform f q‖ * |q| ≤ l1Norm (deriv f) := by
    have h2 : ‖lineTransform f q * (Complex.I * (q : ℂ))‖ = ‖lineTransform f q‖ * |q| := by
      simp
    rw [← h2, parts, norm_neg, l1Norm_eq_integral hd.aestronglyMeasurable]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext x
    rw [norm_mul, norm_phaseFn, mul_one]
  rwa [le_div_iff₀ (abs_pos.mpr hq)]
theorem l1Norm_le_sqrt_pi_mul_weighted {k : ℝ → ℂ} (hk : k ∈ ccIn (Set.univ : Set ℝ)) :
    l1Norm k ≤ Real.sqrt Real.pi * Real.sqrt (∫ s : ℝ, (1 + s ^ 2) * ‖k s‖ ^ 2) := by
  have hc := continuous_of_mem_ccIn hk
  have hcs := hasCompactSupport_of_mem_ccIn hk
  have hpos : ∀ s : ℝ, 0 < 1 + s ^ 2 := fun s => by positivity
  set u : ℝ → ℝ := fun s => Real.sqrt ((1 + s ^ 2)⁻¹) with hu
  set v : ℝ → ℝ := fun s => Real.sqrt (1 + s ^ 2) * ‖k s‖ with hv
  have huc : Continuous u := by
    refine Real.continuous_sqrt.comp (Continuous.inv₀ (by fun_prop) fun s => (hpos s).ne')
  have hvc : Continuous v := by
    have : Continuous fun s : ℝ => Real.sqrt (1 + s ^ 2) :=
      Real.continuous_sqrt.comp (by fun_prop)
    exact this.mul hc.norm
  have hu2 : ∀ s, u s ^ 2 = (1 + s ^ 2)⁻¹ := fun s =>
    Real.sq_sqrt (inv_nonneg.mpr (hpos s).le)
  have hv2 : ∀ s, v s ^ 2 = (1 + s ^ 2) * ‖k s‖ ^ 2 := fun s => by
    rw [hv, mul_pow, Real.sq_sqrt (hpos s).le]
  have huv : ∀ s, u s * v s = ‖k s‖ := fun s => by
    have h1 : Real.sqrt ((1 + s ^ 2)⁻¹) * Real.sqrt (1 + s ^ 2) = 1 := by
      rw [← Real.sqrt_mul (inv_nonneg.mpr (hpos s).le), inv_mul_cancel₀ (hpos s).ne', Real.sqrt_one]
    simp only [hu, hv]
    rw [← mul_assoc, h1, one_mul]
  have hvi : Integrable fun s => v s ^ 2 := by
    refine integrable_of_continuous_of_compact (hvc.pow 2) ?_
    have : HasCompactSupport v := hcs.norm.mul_left
    exact this.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  have hum : MemLp u (ENNReal.ofReal 2) := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq huc.aestronglyMeasurable]
    simpa only [hu2] using integrable_inv_one_add_sq
  have hvm : MemLp v (ENNReal.ofReal 2) := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq hvc.aestronglyMeasurable]
    exact hvi
  have hH : ∫ a, u a * v a ≤ (∫ a, u a ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
      (∫ a, v a ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
      (Eventually.of_forall fun s => Real.sqrt_nonneg _)
      (Eventually.of_forall fun s => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hum hvm
  simp only [huv, Real.rpow_two, hu2, hv2, integral_univ_inv_one_add_sq] at hH
  rw [l1Norm_eq_integral hc.aestronglyMeasurable, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hH
theorem weight_mul_norm_sq (k : ℝ → ℂ) (s : ℝ) :
    (1 + s ^ 2) * ‖k s‖ ^ 2 = ‖k s‖ ^ 2 + ‖Complex.I * (s : ℂ) * k s‖ ^ 2 := by
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, one_mul, Real.norm_eq_abs, mul_pow,
    sq_abs]
  ring
theorem weighted_l2_eq (hP : Analysis.PlancherelRealLine) {k : ℝ → ℂ}
    (hk : k ∈ ccIn (Set.univ : Set ℝ)) :
    Integrable (fun q => ‖lineTransform k q‖ ^ 2) ∧
    Integrable (fun q => ‖lineTransform (fun s : ℝ => Complex.I * (s : ℂ) * k s) q‖ ^ 2) ∧
    ∫ s : ℝ, (1 + s ^ 2) * ‖k s‖ ^ 2 = (2 * Real.pi)⁻¹ *
      ((∫ q, ‖lineTransform k q‖ ^ 2) +
        ∫ q, ‖lineTransform (fun s : ℝ => Complex.I * (s : ℂ) * k s) q‖ ^ 2) := by
  have hm := mul_coord_mem_ccIn hk
  have h1 := hP k (continuous_of_mem_ccIn hk) (hasCompactSupport_of_mem_ccIn hk)
  have h2 := hP _ (continuous_of_mem_ccIn hm) (hasCompactSupport_of_mem_ccIn hm)
  have i1 : Integrable fun s => ‖k s‖ ^ 2 := by
    refine integrable_of_continuous_of_compact ((continuous_of_mem_ccIn hk).norm.pow 2) ?_
    exact (hasCompactSupport_of_mem_ccIn hk).norm.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  have i2 : Integrable fun s : ℝ => ‖Complex.I * (s : ℂ) * k s‖ ^ 2 := by
    refine integrable_of_continuous_of_compact ((continuous_of_mem_ccIn hm).norm.pow 2) ?_
    exact (hasCompactSupport_of_mem_ccIn hm).norm.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  refine ⟨h1.1, h2.1, ?_⟩
  simp only [weight_mul_norm_sq k]
  rw [integral_add i1 i2, h1.2, h2.2, mul_add]
  rfl
theorem convPow_mem_c1 {f : ℝ → ℂ} (hf : f ∈ c1Functions) {n : ℕ} (hn : 1 ≤ n) :
    convPow f n ∈ c1Functions := by
  induction n, hn using Nat.le_induction with
  | base => exact hf
  | succ n hn ih =>
    rw [convPow_succ f hn]
    exact convolve_mem_c1 ih hf
theorem lineTransform_convPow {f : ℝ → ℂ} (hf : f ∈ c1Functions) {n : ℕ}
    (hn : 1 ≤ n) : lineTransform (convPow f n) = lineTransform f ^ n := by
  induction n, hn using Nat.le_induction with
  | base => simp [convPow_one]
  | succ n hn ih =>
    rw [convPow_succ f hn, lineTransform_convolve (convPow_mem_c1 hf hn) hf, ih, pow_succ]
theorem bddAbove_norm_lineTransform {f : ℝ → ℂ} (hf : f ∈ ccIn (Set.univ : Set ℝ)) :
    BddAbove (Set.range fun q => ‖lineTransform f q‖) :=
  ⟨l1Norm f, by rintro _ ⟨q, rfl⟩; exact norm_lineTransform_le hf q⟩
theorem convPowBound_proof (hP : Analysis.PlancherelRealLine) : ConvPowBound := by
  intro f hf n hn
  have hfc := mem_ccIn_of_mem_c1 hf
  have hkc1 := convPow_mem_c1 hf hn
  have hk := mem_ccIn_of_mem_c1 hkc1
  set k := convPow f n with hkdef
  set M := TestFunctions.uniformNorm (lineTransform f) with hM
  have hle : ∀ q, ‖lineTransform f q‖ ≤ M := fun q => le_ciSup (bddAbove_norm_lineTransform hfc) q
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hle 0)
  have hT : lineTransform k = lineTransform f ^ n := lineTransform_convPow hf hn
  set c : ℝ := (n : ℝ) * M ^ (n - 1) with hc
  have hc0 : 0 ≤ c := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : ∀ q, ‖lineTransform f q‖ ^ (n - 1) ≤ M ^ (n - 1) := fun q =>
    pow_le_pow_left₀ (norm_nonneg _) (hle q) _
  have b1 : ∀ q, ‖lineTransform k q‖ ≤ c * ‖lineTransform f q‖ := by
    intro q
    have e : ‖lineTransform k q‖ = ‖lineTransform f q‖ ^ (n - 1) * ‖lineTransform f q‖ := by
      rw [hT, Pi.pow_apply, norm_pow, ← pow_succ, Nat.sub_add_cancel hn]
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖lineTransform f q‖ ^ (n - 1) ≤ M ^ (n - 1) := hpow q
      _ ≤ (n : ℝ) * M ^ (n - 1) := le_mul_of_one_le_left (by positivity) hn1
  have hderiv : ∀ q, lineTransform (fun s : ℝ => Complex.I * (s : ℂ) * k s) q =
      (n : ℂ) * lineTransform f q ^ (n - 1) *
        lineTransform (fun s : ℝ => Complex.I * (s : ℂ) * f s) q := by
    intro q
    have d1 := hasDerivAt_lineTransform hk q
    have d2 := (hasDerivAt_lineTransform hfc q).pow n
    rw [← hT] at d2
    exact d1.unique d2
  have b2 : ∀ q, ‖lineTransform (fun s : ℝ => Complex.I * (s : ℂ) * k s) q‖ ≤
      c * ‖lineTransform (fun s : ℝ => Complex.I * (s : ℂ) * f s) q‖ := by
    intro q
    rw [hderiv q, norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (hpow q) (by positivity)
  obtain ⟨ik1, ik2, ek⟩ := weighted_l2_eq hP hk
  obtain ⟨if1, if2, ef⟩ := weighted_l2_eq hP hfc
  have sq : ∀ {x y : ℝ}, 0 ≤ x → x ≤ c * y → x ^ 2 ≤ c ^ 2 * y ^ 2 := by
    intro x y hx hxy
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx hxy 2
  have m1 : ∫ q, ‖lineTransform k q‖ ^ 2 ≤ c ^ 2 * ∫ q, ‖lineTransform f q‖ ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono ik1 (if1.const_mul _) fun q => sq (norm_nonneg _) (b1 q)
  have m2 : ∫ q, ‖lineTransform (fun s : ℝ => Complex.I * (s : ℂ) * k s) q‖ ^ 2 ≤
      c ^ 2 * ∫ q, ‖lineTransform (fun s : ℝ => Complex.I * (s : ℂ) * f s) q‖ ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono ik2 (if2.const_mul _) fun q => sq (norm_nonneg _) (b2 q)
  have hB : ∫ s : ℝ, (1 + s ^ 2) * ‖k s‖ ^ 2 ≤ c ^ 2 * ∫ s : ℝ, (1 + s ^ 2) * ‖f s‖ ^ 2 := by
    rw [ek, ef]
    have hp : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
    calc _ ≤ (2 * Real.pi)⁻¹ * (c ^ 2 * (∫ q, ‖lineTransform f q‖ ^ 2) +
          c ^ 2 * ∫ q, ‖lineTransform (fun s : ℝ => Complex.I * (s : ℂ) * f s) q‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add m1 m2) hp
      _ = _ := by ring
  calc l1Norm k ≤ Real.sqrt Real.pi * Real.sqrt (∫ s : ℝ, (1 + s ^ 2) * ‖k s‖ ^ 2) :=
        l1Norm_le_sqrt_pi_mul_weighted hk
    _ ≤ Real.sqrt Real.pi * Real.sqrt (c ^ 2 * ∫ s : ℝ, (1 + s ^ 2) * ‖f s‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
    _ = convPowConst f * (n : ℝ) * M ^ (n - 1) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0, convPowConst, hc]
        ring
def posPartSq (u : ℝ) : ℝ := max u 0 ^ 2
theorem hasDerivAt_posPartSq (u : ℝ) : HasDerivAt posPartSq (2 * max u 0) u := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.hasDerivAt_sq_max_zero <;> assumption
theorem contDiff_posPartSq : ContDiff ℝ 1 posPartSq := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.contDiff_sq_max_zero <;> assumption
def bumpFnReal (s : ℝ) : ℝ := 15 / 16 * posPartSq (1 - s ^ 2)
theorem bumpFn_eq_ofReal (s : ℝ) : bumpFn s = (bumpFnReal s : ℂ) := by
  unfold bumpFn bumpFnReal posPartSq
  split_ifs with h
  · have : 0 ≤ 1 - s ^ 2 := by
      have := sq_le_one_iff_abs_le_one s |>.mpr h
      linarith
    rw [max_eq_left this]
  · have : 1 - s ^ 2 ≤ 0 := by
      have := (sq_le_one_iff_abs_le_one s).not.mpr h
      linarith
    simp [max_eq_right this]
theorem bumpFnReal_nonneg (s : ℝ) : 0 ≤ bumpFnReal s := by
  unfold bumpFnReal posPartSq
  positivity
theorem bumpFn_eq_zero {s : ℝ} (h : 1 < |s|) : bumpFn s = 0 := by
  simp [bumpFn, not_le.mpr h]
theorem contDiff_bumpFnReal : ContDiff ℝ 1 bumpFnReal :=
  contDiff_const.mul (contDiff_posPartSq.comp (contDiff_const.sub (contDiff_id.pow 2)))
theorem contDiff_bumpFn : ContDiff ℝ 1 bumpFn := by
  have : bumpFn = fun s => ((bumpFnReal s : ℝ) : ℂ) := funext bumpFn_eq_ofReal
  rw [this]
  exact Complex.ofRealCLM.contDiff.comp contDiff_bumpFnReal
theorem hasCompactSupport_bumpFn : HasCompactSupport bumpFn := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun s hs => ?_
  refine bumpFn_eq_zero ?_
  by_contra h
  exact hs (abs_le.mp (not_lt.mp h))
theorem bumpFn_mem_c1 : bumpFn ∈ c1Functions :=
  mem_c1_of contDiff_bumpFn hasCompactSupport_bumpFn
theorem integral_bumpFnReal : ∫ s, bumpFnReal s = 1 := by
  have hz : ∀ s, s ∉ Set.Ioc (-1 : ℝ) 1 → bumpFnReal s = 0 := by
    intro s hs
    have h1 : 1 - s ^ 2 ≤ 0 := by
      by_contra h
      have : s ^ 2 < 1 := by linarith
      have := abs_lt.mp ((sq_lt_one_iff_abs_lt_one s).mp this)
      exact hs ⟨this.1, this.2.le⟩
    simp [bumpFnReal, posPartSq, max_eq_right h1]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have hcongr : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, bumpFnReal s = 15 / 16 * (1 - s ^ 2) ^ 2 := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have : 0 ≤ 1 - s ^ 2 := by
      have := (sq_le_one_iff_abs_le_one s).mpr (abs_le.mpr hs)
      linarith
    simp [bumpFnReal, posPartSq, max_eq_left this]
  rw [intervalIntegral.integral_congr hcongr]
  have hprim : ∀ x ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun x : ℝ => 15 / 16 * (x - 2 / 3 * x ^ 3 + 1 / 5 * x ^ 5))
        (15 / 16 * (1 - x ^ 2) ^ 2) x := by
    intro x _
    have h := (((hasDerivAt_id' x).sub ((hasDerivAt_pow 3 x).const_mul (2 / 3 : ℝ))).add
      ((hasDerivAt_pow 5 x).const_mul (1 / 5 : ℝ))).const_mul (15 / 16 : ℝ)
    exact HasDerivAt.congr_deriv h (by norm_num; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprim
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num
theorem lebesgueIntegral_bumpFn : lebesgueIntegral bumpFn = 1 := by
  change ∫ s, bumpFn s = 1
  simp only [bumpFn_eq_ofReal]
  rw [integral_complex_ofReal, integral_bumpFnReal]
  simp
theorem l1Norm_bumpFn : l1Norm bumpFn = 1 := by
  rw [l1Norm_eq_integral contDiff_bumpFn.continuous.aestronglyMeasurable, ← integral_bumpFnReal]
  congr 1
  funext s
  rw [bumpFn_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bumpFnReal_nonneg s)]
theorem lineTransform_bumpFn_zero : lineTransform bumpFn 0 = 1 := by
  rw [lineTransform_eq_integral, ← lebesgueIntegral_bumpFn]
  change _ = ∫ s, bumpFn s
  congr 1
  funext s
  simp [phaseFn]
theorem lineTransform_scaledBump {n : ℕ} (hn : 1 ≤ n) (s₀ q : ℝ) :
    lineTransform (scaledBump n s₀) q = phaseFn q s₀ * lineTransform bumpFn (q / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  set G : ℝ → ℂ := fun u => bumpFn u * phaseFn (q / n) u with hG
  have hpt : ∀ s, scaledBump n s₀ s * phaseFn q s =
      (n : ℂ) * phaseFn q s₀ * G ((n : ℝ) * (s - s₀)) := by
    intro s
    have e1 : phaseFn q s = phaseFn q s₀ * phaseFn q (s - s₀) := by
      rw [← phaseFn_add]
      congr 1
      ring
    have e2 : phaseFn (q / n) ((n : ℝ) * (s - s₀)) = phaseFn q (s - s₀) := by
      unfold phaseFn
      congr 1
      push_cast
      field_simp
    simp only [hG, scaledBump, e2, e1]
    ring
  have hint : ∫ s : ℝ, G ((n : ℝ) * (s - s₀)) = ((n : ℂ))⁻¹ * ∫ u, G u := by
    rw [integral_sub_right_eq_self (fun x : ℝ => G ((n : ℝ) * x)) s₀,
      Measure.integral_comp_mul_left G (n : ℝ), abs_of_pos (by positivity), Complex.real_smul]
    push_cast
    rfl
  rw [lineTransform_eq_integral]
  simp only [hpt]
  rw [integral_const_mul, hint, lineTransform_eq_integral]
  field_simp
  rfl
theorem scaledBump_eq_ofReal (n : ℕ) (s₀ s : ℝ) :
    scaledBump n s₀ s = (((n : ℝ) * bumpFnReal ((n : ℝ) * (s - s₀)) : ℝ) : ℂ) := by
  simp [scaledBump, bumpFn_eq_ofReal]
theorem scaledBump_eq_zero_of_not_mem {n : ℕ} (hn : 1 ≤ n) (s₀ s : ℝ)
    (hs : s ∉ Set.Icc (s₀ - 1 / (n : ℝ)) (s₀ + 1 / (n : ℝ))) : scaledBump n s₀ s = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 1 < |(n : ℝ) * (s - s₀)| := by
    by_contra h
    obtain ⟨h2, h3⟩ := abs_le.mp (not_lt.mp h)
    have h4 : (-1 : ℝ) / n ≤ s - s₀ := (div_le_iff₀' hn0).mpr h2
    have h5 : s - s₀ ≤ 1 / n := (le_div_iff₀' hn0).mpr h3
    have h6 : (-1 : ℝ) / n = -(1 / n) := by ring
    exact hs ⟨by linarith, by linarith⟩
  simp [scaledBump, bumpFn_eq_zero h1]
theorem scaledBump_mem_c1 {n : ℕ} (hn : 1 ≤ n) (s₀ : ℝ) :
    scaledBump n s₀ ∈ c1Functions := by
  refine mem_c1_of ?_ ?_
  · exact contDiff_const.mul (contDiff_bumpFn.comp
      (contDiff_const.mul (contDiff_id.sub contDiff_const)))
  · exact HasCompactSupport.intro isCompact_Icc (scaledBump_eq_zero_of_not_mem hn s₀)
theorem norm_phaseFn_mul (q s₀ : ℝ) (z : ℂ) : ‖phaseFn q s₀ * z‖ = ‖z‖ := by
  rw [norm_mul, norm_phaseFn, one_mul]
theorem norm_lineTransform_bumpFn_le (q : ℝ) : ‖lineTransform bumpFn q‖ ≤ 1 := by
  have := norm_lineTransform_le (mem_ccIn_of_mem_c1 bumpFn_mem_c1) q
  rwa [l1Norm_bumpFn] at this
theorem tendsto_lineTransform_scaledBump (s₀ q : ℝ) :
    Tendsto (fun n : ℕ => lineTransform (scaledBump n s₀) q) atTop
      (𝓝 (Complex.exp (Complex.I * (s₀ : ℂ) * (q : ℂ)))) := by
  have h0 : Tendsto (fun n : ℕ => q / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => phaseFn q s₀ * lineTransform bumpFn (q / n)) atTop
      (𝓝 (phaseFn q s₀ * 1)) := by
    refine Tendsto.const_mul _ ?_
    have := ((continuous_lineTransform (mem_ccIn_of_mem_c1 bumpFn_mem_c1)).tendsto 0).comp h0
    rwa [lineTransform_bumpFn_zero] at this
  rw [mul_one] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (lineTransform_scaledBump hn s₀ q).symm
theorem bumpProperties_proof : BumpProperties := by
  refine ⟨⟨bumpFn_mem_c1, fun s => ?_⟩, fun s => ?_, lebesgueIntegral_bumpFn, ?_,
    tendsto_lineTransform_scaledBump⟩
  · rw [bumpFn_eq_ofReal]
    simp
  · rw [bumpFn_eq_ofReal]
    exact ⟨by simp, by simpa using bumpFnReal_nonneg s⟩
  · intro n hn s₀
    refine ⟨scaledBump_mem_c1 hn s₀, fun s => ?_, ?_, scaledBump_eq_zero_of_not_mem hn s₀,
      fun q => ?_⟩
    · rw [scaledBump_eq_ofReal]
      exact ⟨by simp, by
        have := bumpFnReal_nonneg ((n : ℝ) * (s - s₀))
        simpa using mul_nonneg (Nat.cast_nonneg n) this⟩
    · have h := lineTransform_scaledBump hn s₀ 0
      have e : lineTransform (scaledBump n s₀) 0 = lebesgueIntegral (scaledBump n s₀) := by
        rw [lineTransform_eq_integral]
        change _ = ∫ s, scaledBump n s₀ s
        congr 1
        funext s
        simp [phaseFn]
      rw [← e, h]
      simp [phaseFn, lineTransform_bumpFn_zero]
    · rw [lineTransform_scaledBump hn, norm_phaseFn_mul]
      exact norm_lineTransform_bumpFn_le _
open OnePoint
open scoped NNReal
theorem continuous_intervalRpow (t : ℝ≥0) : Continuous (intervalRpow t) := by
  unfold intervalRpow
  exact Continuous.rpow_const continuous_subtype_val fun _ => Or.inr t.2
theorem intervalRpow_nonneg (t : ℝ≥0) (a : unitInterval) : 0 ≤ intervalRpow t a :=
  Real.rpow_nonneg a.2.1 _
theorem intervalRpow_le_one (t : ℝ≥0) (a : unitInterval) : intervalRpow t a ≤ 1 :=
  Real.rpow_le_one a.2.1 a.2.2 t.2
theorem intervalRpow_add (t t' : ℝ≥0) (a : unitInterval) :
    intervalRpow (t + t') a = intervalRpow t a * intervalRpow t' a := by apply _root_.YangMills.Construction.TwoPoints.LineTransforms.SmearedPairBoundsProof.intervalRpow_add <;> assumption
theorem add_mem_dyadics {t t' : ℝ≥0} (ht : t ∈ dyadics) (ht' : t' ∈ dyadics) :
    t + t' ∈ dyadics := by
  obtain ⟨i, j, h⟩ := ht
  obtain ⟨i', j', h'⟩ := ht'
  refine ⟨i + i', j * 2 ^ i' + j' * 2 ^ i, ?_⟩
  rw [NNReal.coe_add, h, h']
  have e : ∀ k : ℕ, (2 : ℝ) ^ (-(k : ℤ)) = ((2 : ℝ) ^ k)⁻¹ := fun k => by
    rw [zpow_neg, zpow_natCast]
  have e' : (2 : ℝ) ^ (-((i + i' : ℕ) : ℤ)) = ((2 : ℝ) ^ (i + i'))⁻¹ := e _
  rw [e, e]
  push_cast at e' ⊢
  rw [e', pow_add]
  field_simp
def stripGenerator (t : ℝ≥0) (f : ℝ → ℂ) : UnitStrip → ℂ :=
  fun p => (intervalRpow t p.1 : ℂ) * lineTransform f p.2
theorem stripGenerator_mem {t : ℝ≥0} (ht : t ∈ dyadics) {f : ℝ → ℂ}
    (hf : f ∈ c1Functions) : stripGenerator t f ∈ stripAlgebra :=
  Submodule.subset_span ⟨t, ht, f, hf, rfl⟩
theorem stripGenerator_mem_stripC0 (t : ℝ≥0) {f : ℝ → ℂ} (hf : f ∈ c1Functions) :
    stripGenerator t f ∈ stripC0 := by
  refine ⟨?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp ((continuous_intervalRpow t).comp continuous_fst)).mul
      ((continuous_lineTransform (mem_ccIn_of_mem_c1 hf)).comp continuous_snd)
  · have h0 : Tendsto (fun q : ℝ => l1Norm (deriv f) / |q|)
        (comap (fun q : ℝ => |q|) atTop) (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_comap
    have hdec : Tendsto (fun q : ℝ => ENNReal.ofReal (l1Norm (deriv f) / |q|))
        (comap (fun q : ℝ => |q|) atTop) (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdec
      (Eventually.of_forall fun _ => zero_le) ?_
    have hq : ∀ᶠ q : ℝ in comap (fun q : ℝ => |q|) atTop, 0 < |q| :=
      tendsto_comap.eventually (eventually_gt_atTop 0)
    filter_upwards [hq] with q hq
    refine iSup_le fun a => ?_
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := transformDecay_proof f hf q (abs_pos.mp hq)
    have h2 : ‖(intervalRpow t a : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (intervalRpow_nonneg t a)]
      exact intervalRpow_le_one t a
    change ‖(intervalRpow t a : ℂ) * lineTransform f q‖ ≤ _
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) h2).trans h1
theorem stripAlgebra_le_stripC0 : stripAlgebra ≤ stripC0 := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨t, _, f, hf, rfl⟩
  exact stripGenerator_mem_stripC0 t hf
theorem mul_mem_stripAlgebra {F F' : UnitStrip → ℂ} (hF : F ∈ stripAlgebra)
    (hF' : F' ∈ stripAlgebra) : F * F' ∈ stripAlgebra := by
  have key : stripAlgebra * stripAlgebra ≤ stripAlgebra := by
    unfold stripAlgebra
    rw [Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨t, ht, f, hf, rfl⟩, _, ⟨t', ht', g, hg, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨t + t', add_mem_dyadics ht ht', convolve f g,
      convolve_mem_c1 hf hg, ?_⟩
    funext p
    simp only [Pi.mul_apply, lineTransform_convolve hf hg, intervalRpow_add]
    push_cast
    ring
  exact key (Submodule.mul_mem_mul hF hF')
theorem conjFun_mem_stripAlgebra {F : UnitStrip → ℂ} (hF : F ∈ stripAlgebra) :
    conjFun F ∈ stripAlgebra := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, f, hf, rfl⟩ := hx
    have e : conjFun (fun p : UnitStrip => (intervalRpow t p.1 : ℂ) * lineTransform f p.2) =
        stripGenerator t (reflectConj f) := by
      funext p
      simp [conjFun, stripGenerator, lineTransform_reflectConj]
    rw [e]
    exact stripGenerator_mem ht (reflectConj_mem_c1 hf)
  | zero =>
    have e : conjFun (0 : UnitStrip → ℂ) = 0 := by
      funext p
      simp [conjFun]
    rw [e]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have e : conjFun (x + y) = conjFun x + conjFun y := by
      funext p
      simp [conjFun]
    rw [e]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have e : conjFun (c • x) = (starRingEnd ℂ) c • conjFun x := by
      funext p
      simp [conjFun]
    rw [e]
    exact Submodule.smul_mem _ _ hx
theorem stripAlgebraClosed_proof : StripAlgebraClosed :=
  ⟨stripAlgebra_le_stripC0, fun _ hF _ hF' =>
    ⟨mul_mem_stripAlgebra hF hF', conjFun_mem_stripAlgebra hF⟩⟩
theorem tendsto_cocompact_of_mem_stripC0 {F : UnitStrip → ℂ} (hF : F ∈ stripC0) :
    Tendsto F (Filter.cocompact UnitStrip) (𝓝 0) := by apply _root_.YangMills.Construction.TwoPoints.LineTransforms.VectorMeasure.tendsto_cocompact_of_mem_stripC0 <;> assumption
def extendToOnePoint (F : UnitStrip → ℂ) (hF : F ∈ stripC0) : C(OnePoint UnitStrip, ℂ) where
  toFun x := x.elim 0 F
  continuous_toFun := by
    rw [OnePoint.continuous_iff]
    refine ⟨?_, hF.1⟩
    rw [Filter.coclosedCompact_eq_cocompact]
    exact tendsto_cocompact_of_mem_stripC0 hF
def onePointAlgebra : StarSubalgebra ℂ C(OnePoint UnitStrip, ℂ) where
  carrier := {f | ∃ c : ℂ, ∃ F ∈ stripAlgebra,
    f ∞ = c ∧ ∀ p : UnitStrip, f (p : OnePoint UnitStrip) = c + F p}
  mul_mem' := by
    rintro f f' ⟨c, F, hF, h1, h2⟩ ⟨c', F', hF', h1', h2'⟩
    refine ⟨c * c', c • F' + c' • F + F * F', ?_, ?_, ?_⟩
    · exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hF')
        (Submodule.smul_mem _ _ hF)) (mul_mem_stripAlgebra hF hF')
    · simp [h1, h1']
    · intro p
      simp only [ContinuousMap.mul_apply, h2, h2', Pi.add_apply, Pi.smul_apply, Pi.mul_apply,
        smul_eq_mul]
      ring
  add_mem' := by
    rintro f f' ⟨c, F, hF, h1, h2⟩ ⟨c', F', hF', h1', h2'⟩
    refine ⟨c + c', F + F', Submodule.add_mem _ hF hF', ?_, ?_⟩
    · simp [h1, h1']
    · intro p
      simp only [ContinuousMap.add_apply, h2, h2', Pi.add_apply]
      ring
  algebraMap_mem' := by
    intro c
    refine ⟨c, 0, Submodule.zero_mem _, ?_, ?_⟩
    · simp [Algebra.algebraMap_eq_smul_one]
    · intro p
      simp [Algebra.algebraMap_eq_smul_one]
  star_mem' := by
    rintro f ⟨c, F, hF, h1, h2⟩
    refine ⟨(starRingEnd ℂ) c, conjFun F, conjFun_mem_stripAlgebra hF, ?_, ?_⟩
    · simp [h1]
    · intro p
      simp [h2, conjFun]
theorem extendToOnePoint_stripGenerator_mem {t : ℝ≥0} (ht : t ∈ dyadics) {f : ℝ → ℂ}
    (hf : f ∈ c1Functions) :
    extendToOnePoint (stripGenerator t f) (stripGenerator_mem_stripC0 t hf) ∈ onePointAlgebra :=
  ⟨0, stripGenerator t f, stripGenerator_mem ht hf, rfl, fun p => by simp [extendToOnePoint]⟩
theorem zero_mem_dyadics : (0 : ℝ≥0) ∈ dyadics := ⟨0, 0, by simp⟩
theorem one_mem_dyadics : (1 : ℝ≥0) ∈ dyadics := ⟨0, 1, by simp⟩
theorem exists_lineTransform_ne_zero (q : ℝ) :
    ∃ f ∈ c1Functions, lineTransform f q ≠ 0 := by
  have h := tendsto_lineTransform_scaledBump 0 q
  have h0 : Complex.exp (Complex.I * ((0 : ℝ) : ℂ) * (q : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨n, hn, hn1⟩ := ((h.eventually_ne h0).and (eventually_ge_atTop 1)).exists
  exact ⟨_, scaledBump_mem_c1 hn1 0, hn⟩
theorem exists_lineTransform_ne {q q' : ℝ} (hq : q ≠ q') :
    ∃ f ∈ c1Functions, lineTransform f q ≠ lineTransform f q' := by
  have hd : q - q' ≠ 0 := sub_ne_zero.mpr hq
  set s₀ : ℝ := Real.pi / (q - q') with hs
  have h := (tendsto_lineTransform_scaledBump s₀ q).sub (tendsto_lineTransform_scaledBump s₀ q')
  have hne : Complex.exp (Complex.I * (s₀ : ℂ) * (q : ℂ)) -
      Complex.exp (Complex.I * (s₀ : ℂ) * (q' : ℂ)) ≠ 0 := by
    intro h0
    have e : Complex.I * (s₀ : ℂ) * (q : ℂ) =
        Complex.I * (s₀ : ℂ) * (q' : ℂ) + (Real.pi : ℂ) * Complex.I := by
      have hdc : ((q : ℂ) - (q' : ℂ)) ≠ 0 := by exact_mod_cast hd
      simp only [hs]
      push_cast
      field_simp
      ring
    rw [e, Complex.exp_add, Complex.exp_pi_mul_I] at h0
    have h1 := Complex.exp_ne_zero (Complex.I * (s₀ : ℂ) * (q' : ℂ))
    apply h1
    linear_combination (-1 / 2 : ℂ) * h0
  obtain ⟨n, hn, hn1⟩ := ((h.eventually_ne hne).and (eventually_ge_atTop 1)).exists
  exact ⟨_, scaledBump_mem_c1 hn1 s₀, sub_ne_zero.mp hn⟩
theorem onePointAlgebra_separatesPoints :
    Set.SeparatesPoints ((fun f : C(OnePoint UnitStrip, ℂ) => (f : OnePoint UnitStrip → ℂ)) ''
      (onePointAlgebra : Set C(OnePoint UnitStrip, ℂ))) := by
  have sepInfty : ∀ p : UnitStrip, ∃ f ∈ onePointAlgebra,
      f (∞ : OnePoint UnitStrip) ≠ f (p : OnePoint UnitStrip) := by
    rintro ⟨a, q⟩
    obtain ⟨g, hg, hne⟩ := exists_lineTransform_ne_zero q
    refine ⟨_, extendToOnePoint_stripGenerator_mem zero_mem_dyadics hg, ?_⟩
    simpa [extendToOnePoint, stripGenerator, intervalRpow] using hne.symm
  intro x y hxy
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty => exact absurd rfl hxy
    | coe p =>
      obtain ⟨f, hf, hne⟩ := sepInfty p
      exact ⟨_, ⟨f, hf, rfl⟩, hne⟩
  | coe p =>
    induction y using OnePoint.rec with
    | infty =>
      obtain ⟨f, hf, hne⟩ := sepInfty p
      exact ⟨_, ⟨f, hf, rfl⟩, hne.symm⟩
    | coe p' =>
      obtain ⟨a, q⟩ := p
      obtain ⟨a', q'⟩ := p'
      by_cases hq : q = q'
      · subst hq
        have ha : a ≠ a' := fun h => hxy (by rw [h])
        obtain ⟨g, hg, hne⟩ := exists_lineTransform_ne_zero q
        refine ⟨_, ⟨_, extendToOnePoint_stripGenerator_mem one_mem_dyadics hg, rfl⟩, ?_⟩
        intro h
        have h1 : (a : ℂ) * lineTransform g q = (a' : ℂ) * lineTransform g q := by
          simpa [extendToOnePoint, stripGenerator, intervalRpow] using h
        have h2 : ((a : ℝ) : ℂ) = ((a' : ℝ) : ℂ) := mul_right_cancel₀ hne h1
        exact ha (Subtype.ext (by exact_mod_cast h2))
      · obtain ⟨g, hg, hne⟩ := exists_lineTransform_ne hq
        refine ⟨_, ⟨_, extendToOnePoint_stripGenerator_mem zero_mem_dyadics hg, rfl⟩, ?_⟩
        simpa [extendToOnePoint, stripGenerator, intervalRpow] using hne
theorem stripAlgebraDense_proof : StripAlgebraDense := by
  intro F hF
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    onePointAlgebra onePointAlgebra_separatesPoints
  have hcl : extendToOnePoint F hF ∈ closure (onePointAlgebra : Set C(OnePoint UnitStrip, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, htop]
    trivial
  have hε : ∀ n : ℕ, ∃ F' ∈ stripAlgebra, ∀ p, ‖(F - F') p‖ ≤ 2 * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨u, ⟨c, F', hF', h1, h2⟩, hd⟩ := Metric.mem_closure_iff.mp hcl _ hpos
    have hpt := (ContinuousMap.dist_lt_iff hpos).mp hd
    refine ⟨F', hF', fun p => ?_⟩
    have hc : ‖c‖ < 1 / ((n : ℝ) + 1) := by
      have := hpt ∞
      rw [h1, dist_eq_norm] at this
      simpa [extendToOnePoint] using this
    have hp : ‖F p - (c + F' p)‖ < 1 / ((n : ℝ) + 1) := by
      have := hpt (p : OnePoint UnitStrip)
      rw [h2, dist_eq_norm] at this
      simpa [extendToOnePoint] using this
    have e : (F - F') p = (F p - (c + F' p)) + c := by
      simp only [Pi.sub_apply]
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    linarith
  choose Fn hFn hb using hε
  refine ⟨Fn, hFn, ?_⟩
  have hlim : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => ?_)
    fun n => ?_
  · exact Real.iSup_nonneg fun _ => norm_nonneg _
  · exact ciSup_le (hb n)
theorem ConvPowDensity.proof (hP : Analysis.PlancherelRealLine) :
    ConvPowDensity.Statement :=
  ⟨convTransformRules_proof, transformDerivBound_proof, transformDecay_proof,
    convPowBound_proof hP, bumpProperties_proof, stripAlgebraClosed_proof,
    stripAlgebraDense_proof⟩
end YangMills.Construction.TwoPoints.LineTransforms
end
