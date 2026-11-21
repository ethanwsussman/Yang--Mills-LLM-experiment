import YangMills.Construction.TwoPoints.FormAtRiemannSumsIsADoubleRiemannSumProof
import YangMills.Construction.TwoPoints.LocalKernelOfAForm
import YangMills.Construction.TwoPoints.ParametrixOfTheCubedLaplacian
import YangMills.Construction.TwoPoints.TranslatePairingIsAnalyticNearAPoint
import YangMills.Construction.TwoPoints.TranslatesAndSuperpositionsInTheSharpNorm
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TestFunctions (laplacianR4 partialDerivR4)
namespace LocalFormKernel
theorem euclidNorm_add_le (x y : AmbientSpace) :
    euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.euclidNorm_add_le <;> assumption
theorem euclidNorm_neg (x : AmbientSpace) : euclidNorm (-x) = euclidNorm x := by
  simp [euclidNorm]
theorem euclidNorm_pos {v : AmbientSpace} (hv : v ≠ 0) : 0 < euclidNorm v := by apply _root_.YangMills.Construction.TwoPoints.MollifierBump.euclidNorm_pos <;> assumption
theorem continuous_euclidNorm : Continuous (euclidNorm : AmbientSpace → ℝ) := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.continuous_euclidNorm <;> assumption
theorem isOpen_euclidOpenBall (x : AmbientSpace) (r : ℝ) : IsOpen (euclidOpenBall x r) :=
  isOpen_lt (continuous_euclidNorm.comp (continuous_id.sub continuous_const)) continuous_const
theorem mem_euclidClosedBall_of_mem_euclidOpenBall {x c : AmbientSpace} {r : ℝ}
    (h : x ∈ euclidOpenBall c r) : x ∈ euclidClosedBall c r :=
  le_of_lt (show euclidNorm (x - c) < r from h)
theorem isClosed_euclidClosedBall (x : AmbientSpace) (r : ℝ) :
    IsClosed (euclidClosedBall x r) :=
  isClosed_le (continuous_euclidNorm.comp (continuous_id.sub continuous_const)) continuous_const
theorem partialDerivR4_eq_fderiv {f : AmbientSpace → ℂ} {x : AmbientSpace}
    (h : DifferentiableAt ℝ f x) (i : Fin 4) :
    partialDerivR4 i f x = fderiv ℝ f x (Pi.single i (1 : ℝ)) := by
  have h1 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (Pi.single i (1 : ℝ) : AmbientSpace)) := by
    simpa using h.hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : AmbientSpace))
      (Pi.single i (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : AmbientSpace)).const_add x
  exact (h1.comp_hasDerivAt (0 : ℝ) h2).deriv
theorem partialDerivR4_eq_fun {f : AmbientSpace → ℂ} (h : ContDiff ℝ ∞ f) (i : Fin 4) :
    partialDerivR4 i f = fun x => fderiv ℝ f x (Pi.single i (1 : ℝ)) :=
  funext fun x => partialDerivR4_eq_fderiv (h.differentiable (by simp) x) i
theorem contDiff_partialDerivR4 {f : AmbientSpace → ℂ} (h : ContDiff ℝ ∞ f) (i : Fin 4) :
    ContDiff ℝ ∞ (partialDerivR4 i f) := by
  rw [partialDerivR4_eq_fun h i]
  exact (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem tsupport_partialDerivR4_subset {f : AmbientSpace → ℂ} (h : ContDiff ℝ ∞ f) (i : Fin 4) :
    tsupport (partialDerivR4 i f) ⊆ tsupport f := by
  rw [partialDerivR4_eq_fun h i]
  exact tsupport_fderiv_apply_subset ℝ _
theorem contDiff_laplacianR4 {f : AmbientSpace → ℂ} (h : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (laplacianR4 f) := by
  unfold laplacianR4
  exact ContDiff.sum fun i _ => contDiff_partialDerivR4 (contDiff_partialDerivR4 h i) i
theorem tsupport_laplacianR4_subset {f : AmbientSpace → ℂ} (h : ContDiff ℝ ∞ f) :
    tsupport (laplacianR4 f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport _)
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  exact tsupport_partialDerivR4_subset h i
    (tsupport_partialDerivR4_subset (contDiff_partialDerivR4 h i) i (subset_tsupport _ hi))
abbrev triLap (f : AmbientSpace → ℂ) : AmbientSpace → ℂ :=
  laplacianR4 (laplacianR4 (laplacianR4 f))
theorem contDiff_triLap {f : AmbientSpace → ℂ} (h : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (triLap f) :=
  contDiff_laplacianR4 (contDiff_laplacianR4 (contDiff_laplacianR4 h))
theorem tsupport_triLap_subset {f : AmbientSpace → ℂ} (h : ContDiff ℝ ∞ f) :
    tsupport (triLap f) ⊆ tsupport f :=
  (tsupport_laplacianR4_subset (contDiff_laplacianR4 (contDiff_laplacianR4 h))).trans
    ((tsupport_laplacianR4_subset (contDiff_laplacianR4 h)).trans (tsupport_laplacianR4_subset h))
theorem partialDerivR4_apply_congr {f g : AmbientSpace → ℂ} {x : AmbientSpace}
    (h : f =ᶠ[𝓝 x] g) (i : Fin 4) : partialDerivR4 i f x = partialDerivR4 i g x := by
  have hc : Tendsto (fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : AmbientSpace)) (𝓝 0) (𝓝 x) := by
    have : Continuous fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : AmbientSpace) := by fun_prop
    simpa using this.tendsto 0
  exact Filter.EventuallyEq.deriv_eq (hc.eventually h)
theorem partialDerivR4_congr {f g : AmbientSpace → ℂ} {x : AmbientSpace} (h : f =ᶠ[𝓝 x] g)
    (i : Fin 4) : partialDerivR4 i f =ᶠ[𝓝 x] partialDerivR4 i g :=
  h.eventuallyEq_nhds.mono fun _ hy => partialDerivR4_apply_congr hy i
theorem laplacianR4_congr {f g : AmbientSpace → ℂ} {x : AmbientSpace} (h : f =ᶠ[𝓝 x] g) :
    laplacianR4 f =ᶠ[𝓝 x] laplacianR4 g := by
  have h2 : ∀ i : Fin 4, partialDerivR4 i (partialDerivR4 i f) =ᶠ[𝓝 x]
      partialDerivR4 i (partialDerivR4 i g) :=
    fun i => partialDerivR4_congr (partialDerivR4_congr h i) i
  filter_upwards [eventually_all.2 h2] with y hy
  exact Finset.sum_congr rfl fun i _ => hy i
theorem triLap_congr {f g : AmbientSpace → ℂ} {x : AmbientSpace} (h : f =ᶠ[𝓝 x] g) :
    triLap f =ᶠ[𝓝 x] triLap g :=
  laplacianR4_congr (laplacianR4_congr (laplacianR4_congr h))
theorem analyticOnNhd_partialDerivR4 {W : AmbientSpace → ℂ} {U : Set AmbientSpace}
    (hU : IsOpen U) (hW : AnalyticOnNhd ℝ W U) (i : Fin 4) :
    AnalyticOnNhd ℝ (partialDerivR4 i W) U := by
  intro x hx
  have h1 : AnalyticAt ℝ (fun y => fderiv ℝ W y (Pi.single i (1 : ℝ))) x :=
    ((ContinuousLinearMap.apply ℝ ℂ (Pi.single i (1 : ℝ) : AmbientSpace)).analyticAt _).comp
      (hW.fderiv x hx)
  refine h1.congr ?_
  filter_upwards [hU.mem_nhds hx] with y hy
  exact (partialDerivR4_eq_fderiv (hW y hy).differentiableAt i).symm
theorem analyticOnNhd_laplacianR4 {W : AmbientSpace → ℂ} {U : Set AmbientSpace} (hU : IsOpen U)
    (hW : AnalyticOnNhd ℝ W U) : AnalyticOnNhd ℝ (laplacianR4 W) U := by
  intro x hx
  have h : ∀ i : Fin 4, AnalyticAt ℝ (partialDerivR4 i (partialDerivR4 i W)) x := fun i =>
    analyticOnNhd_partialDerivR4 hU (analyticOnNhd_partialDerivR4 hU hW i) i x hx
  have e : laplacianR4 W = partialDerivR4 0 (partialDerivR4 0 W) +
      partialDerivR4 1 (partialDerivR4 1 W) + partialDerivR4 2 (partialDerivR4 2 W) +
      partialDerivR4 3 (partialDerivR4 3 W) := by
    funext y
    simp [laplacianR4, Fin.sum_univ_four]
  rw [e]
  exact (((h 0).add (h 1)).add (h 2)).add (h 3)
theorem analyticOnNhd_triLap {W : AmbientSpace → ℂ} {U : Set AmbientSpace} (hU : IsOpen U)
    (hW : AnalyticOnNhd ℝ W U) : AnalyticOnNhd ℝ (triLap W) U :=
  analyticOnNhd_laplacianR4 hU (analyticOnNhd_laplacianR4 hU (analyticOnNhd_laplacianR4 hU hW))
theorem exists_smooth_bump {K : Set AmbientSpace} (hK : IsCompact K) {c : AmbientSpace} {r : ℝ}
    (hKr : K ⊆ euclidOpenBall c r) :
    ∃ ρ : AmbientSpace → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ᶠ x in 𝓝ˢ K, ρ x = 1) ∧
      ∀ x, x ∉ euclidOpenBall c r → ρ x = 0 := by
  have hd : K ⊆ interior (euclidOpenBall c r) := by
    rw [(isOpen_euclidOpenBall c r).interior_eq]
    exact hKr
  obtain ⟨f, h1, h0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, Fin 4 → ℝ)) (n := (⊤ : ℕ∞)) hK.isClosed hd
  exact ⟨f, f.contMDiff.contDiff, h1, h0⟩
def bumpMul (ρ : AmbientSpace → ℝ) (W : AmbientSpace → ℂ) : AmbientSpace → ℂ :=
  fun x => (ρ x : ℂ) * W x
theorem contDiff_bumpMul {ρ : AmbientSpace → ℝ} {W : AmbientSpace → ℂ} {U : Set AmbientSpace}
    {c : AmbientSpace} {r : ℝ} (hρ : ContDiff ℝ ∞ ρ) (h0 : ∀ x, x ∉ euclidOpenBall c r → ρ x = 0)
    (hB : euclidClosedBall c r ⊆ U) (hW : AnalyticOnNhd ℝ W U) : ContDiff ℝ ∞ (bumpMul ρ W) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (Complex.ofRealCLM.contDiff.comp hρ).contDiffAt.mul (hW x hx).contDiffAt
  · have hxB : x ∈ (euclidClosedBall c r)ᶜ := fun h => hx (hB h)
    have e : bumpMul ρ W =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_euclidClosedBall c r).isOpen_compl.mem_nhds hxB] with y hy
      have hy' : y ∉ euclidOpenBall c r :=
        fun h => hy (mem_euclidClosedBall_of_mem_euclidOpenBall h)
      simp [bumpMul, h0 y hy']
    exact contDiffAt_const.congr_of_eventuallyEq e
theorem bumpMul_eventuallyEq {ρ : AmbientSpace → ℝ} {W : AmbientSpace → ℂ} {K : Set AmbientSpace}
    (h1 : ∀ᶠ x in 𝓝ˢ K, ρ x = 1) {x : AmbientSpace} (hx : x ∈ K) : bumpMul ρ W =ᶠ[𝓝 x] W :=
  (h1.filter_mono (nhds_le_nhdsSet hx)).mono fun y hy => by simp [bumpMul, hy]
structure IsSmoothCompact (a : AmbientSpace → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ a
  compact : HasCompactSupport a
theorem IsSmoothCompact.continuous {a : AmbientSpace → ℂ} (ha : IsSmoothCompact a) :
    Continuous a := ha.smooth.continuous
theorem IsSmoothCompact.partialDeriv {a : AmbientSpace → ℂ} (ha : IsSmoothCompact a) (i : Fin 4) :
    IsSmoothCompact (partialDerivR4 i a) :=
  ⟨contDiff_partialDerivR4 ha.smooth i,
    ha.compact.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialDerivR4_subset ha.smooth i)⟩
theorem IsSmoothCompact.laplacian {a : AmbientSpace → ℂ} (ha : IsSmoothCompact a) :
    IsSmoothCompact (laplacianR4 a) :=
  ⟨contDiff_laplacianR4 ha.smooth,
    ha.compact.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianR4_subset ha.smooth)⟩
theorem IsSmoothCompact.triLap {a : AmbientSpace → ℂ} (ha : IsSmoothCompact a) :
    IsSmoothCompact (triLap a) :=
  ha.laplacian.laplacian.laplacian
def doublePair (a b W : AmbientSpace → ℂ) : ℂ :=
  ∫ p : AmbientSpace × AmbientSpace, a p.2 * b p.1 * W (p.1 - p.2) ∂(volume.prod volume)
theorem integrable_doublePair {a b W : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hb : IsSmoothCompact b) (hW : Continuous W) :
    Integrable (fun p : AmbientSpace × AmbientSpace => a p.2 * b p.1 * W (p.1 - p.2))
      (volume.prod volume) := by
  have hc : Continuous fun p : AmbientSpace × AmbientSpace => a p.2 * b p.1 * W (p.1 - p.2) :=
    ((ha.continuous.comp continuous_snd).mul (hb.continuous.comp continuous_fst)).mul
      (hW.comp (continuous_fst.sub continuous_snd))
  refine hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (hb.compact.isCompact.prod ha.compact.isCompact)
      fun p hp => ?_)
  have h1 : a p.2 ≠ 0 := fun h => hp (by simp [h])
  have h2 : b p.1 ≠ 0 := fun h => hp (by simp [h])
  exact ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩
theorem doublePair_eq_integral_integral {a b W : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hb : IsSmoothCompact b) (hW : Continuous W) :
    doublePair a b W = ∫ y : AmbientSpace, ∫ x : AmbientSpace, a x * b y * W (y - x) :=
  integral_prod _ (integrable_doublePair ha hb hW)
theorem doublePair_eq_integral_integral_swap {a b W : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hb : IsSmoothCompact b) (hW : Continuous W) :
    doublePair a b W = ∫ x : AmbientSpace, ∫ y : AmbientSpace, a x * b y * W (y - x) :=
  integral_prod_symm _ (integrable_doublePair ha hb hW)
theorem doublePair_add {a b W₁ W₂ : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hb : IsSmoothCompact b) (h₁ : Continuous W₁) (h₂ : Continuous W₂) :
    doublePair a b (W₁ + W₂) = doublePair a b W₁ + doublePair a b W₂ := by
  unfold doublePair
  rw [← integral_add (integrable_doublePair ha hb h₁) (integrable_doublePair ha hb h₂)]
  congr 1
  funext p
  simp only [Pi.add_apply]
  ring
theorem integrable_mul_of_isSmoothCompact {a G : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hG : Continuous G) : Integrable fun x => a x * G x :=
  (ha.continuous.mul hG).integrable_of_hasCompactSupport ha.compact.mul_right
theorem integral_partialDerivR4_mul {a G : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hG : ContDiff ℝ ∞ G) (i : Fin 4) :
    ∫ x, partialDerivR4 i a x * G x = -∫ x, a x * partialDerivR4 i G x := by
  have i1 : Integrable fun x => fderiv ℝ a x (Pi.single i (1 : ℝ)) * G x := by
    have := integrable_mul_of_isSmoothCompact (ha.partialDeriv i) hG.continuous
    rwa [partialDerivR4_eq_fun ha.smooth i] at this
  have i2 : Integrable fun x => a x * fderiv ℝ G x (Pi.single i (1 : ℝ)) := by
    have := integrable_mul_of_isSmoothCompact ha (contDiff_partialDerivR4 hG i).continuous
    rwa [partialDerivR4_eq_fun hG i] at this
  have e := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure AmbientSpace))
    (f := a) (g := G) (v := Pi.single i (1 : ℝ)) i1 i2
    (integrable_mul_of_isSmoothCompact ha hG.continuous)
    (fun x _ => ha.smooth.differentiable (by simp) x)
    (fun x _ => hG.differentiable (by simp) x)
  rw [partialDerivR4_eq_fun ha.smooth i, partialDerivR4_eq_fun hG i, e, neg_neg]
theorem partialDerivR4_comp_sub_left (W : AmbientSpace → ℂ) (w x : AmbientSpace) (i : Fin 4) :
    partialDerivR4 i (fun y => W (w - y)) x = -partialDerivR4 i W (w - x) := by
  have e : (fun t : ℝ => W (w - (x + t • (Pi.single i (1 : ℝ) : AmbientSpace)))) =
      fun t : ℝ => (fun s : ℝ => W ((w - x) + s • (Pi.single i (1 : ℝ) : AmbientSpace))) (-t) := by
    funext t
    have : w - (x + t • (Pi.single i (1 : ℝ) : AmbientSpace)) =
        (w - x) + (-t) • (Pi.single i (1 : ℝ) : AmbientSpace) := by
      rw [neg_smul]
      abel
    simp only [this]
  unfold partialDerivR4
  rw [e]
  exact (deriv_comp_neg
    (fun s : ℝ => W ((w - x) + s • (Pi.single i (1 : ℝ) : AmbientSpace))) 0).trans
    (by rw [neg_zero])
theorem partialDerivR4_comp_sub_right (W : AmbientSpace → ℂ) (w x : AmbientSpace) (i : Fin 4) :
    partialDerivR4 i (fun y => W (y - w)) x = partialDerivR4 i W (x - w) := by
  have e : (fun t : ℝ => W (x + t • (Pi.single i (1 : ℝ) : AmbientSpace) - w)) =
      fun t : ℝ => W ((x - w) + t • (Pi.single i (1 : ℝ) : AmbientSpace)) := by
    funext t
    have : x + t • (Pi.single i (1 : ℝ) : AmbientSpace) - w =
        (x - w) + t • (Pi.single i (1 : ℝ) : AmbientSpace) := by abel
    simp only [this]
  unfold partialDerivR4
  rw [e]
theorem doublePair_partialDerivR4_left {a b W : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hb : IsSmoothCompact b) (hW : ContDiff ℝ ∞ W) (i : Fin 4) :
    doublePair (partialDerivR4 i a) b W = doublePair a b (partialDerivR4 i W) := by
  rw [doublePair_eq_integral_integral (ha.partialDeriv i) hb hW.continuous,
    doublePair_eq_integral_integral ha hb (contDiff_partialDerivR4 hW i).continuous]
  congr 1
  funext y
  have hG : ContDiff ℝ ∞ fun x => W (y - x) := hW.comp (contDiff_const.sub contDiff_id)
  have e := integral_partialDerivR4_mul ha hG i
  simp only [partialDerivR4_comp_sub_left, mul_neg, integral_neg, neg_neg] at e
  calc ∫ x, partialDerivR4 i a x * b y * W (y - x)
      = b y * ∫ x, partialDerivR4 i a x * W (y - x) := by
        rw [← integral_const_mul]
        congr 1
        funext x
        ring
    _ = b y * ∫ x, a x * partialDerivR4 i W (y - x) := by rw [e]
    _ = ∫ x, a x * b y * partialDerivR4 i W (y - x) := by
        rw [← integral_const_mul]
        congr 1
        funext x
        ring
theorem doublePair_partialDerivR4_right {a b W : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hb : IsSmoothCompact b) (hW : ContDiff ℝ ∞ W) (i : Fin 4) :
    doublePair a (partialDerivR4 i b) W = -doublePair a b (partialDerivR4 i W) := by
  rw [doublePair_eq_integral_integral_swap ha (hb.partialDeriv i) hW.continuous,
    doublePair_eq_integral_integral_swap ha hb (contDiff_partialDerivR4 hW i).continuous,
    ← integral_neg]
  congr 1
  funext x
  have hG : ContDiff ℝ ∞ fun y => W (y - x) := hW.comp (contDiff_id.sub contDiff_const)
  have e := integral_partialDerivR4_mul hb hG i
  simp only [partialDerivR4_comp_sub_right] at e
  calc ∫ y, a x * partialDerivR4 i b y * W (y - x)
      = a x * ∫ y, partialDerivR4 i b y * W (y - x) := by
        rw [← integral_const_mul]
        congr 1
        funext y
        ring
    _ = -(a x * ∫ y, b y * partialDerivR4 i W (y - x)) := by rw [e, mul_neg]
    _ = -∫ y, a x * b y * partialDerivR4 i W (y - x) := by
        rw [← integral_const_mul]
        congr 2
        funext y
        ring
theorem doublePair_laplacianR4_left {a b W : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hb : IsSmoothCompact b) (hW : ContDiff ℝ ∞ W) :
    doublePair (laplacianR4 a) b W = doublePair a b (laplacianR4 W) := by
  have hl : doublePair (laplacianR4 a) b W =
      ∑ i, doublePair (partialDerivR4 i (partialDerivR4 i a)) b W := by
    unfold doublePair
    rw [← integral_finsetSum _ fun i _ =>
      integrable_doublePair ((ha.partialDeriv i).partialDeriv i) hb hW.continuous]
    congr 1
    funext p
    simp only [laplacianR4, Finset.sum_mul]
  have hr : doublePair a b (laplacianR4 W) =
      ∑ i, doublePair a b (partialDerivR4 i (partialDerivR4 i W)) := by
    unfold doublePair
    rw [← integral_finsetSum _ fun i _ => integrable_doublePair ha hb
      (contDiff_partialDerivR4 (contDiff_partialDerivR4 hW i) i).continuous]
    congr 1
    funext p
    simp only [laplacianR4, Finset.mul_sum]
  rw [hl, hr]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [doublePair_partialDerivR4_left (ha.partialDeriv i) hb hW i,
    doublePair_partialDerivR4_left ha hb (contDiff_partialDerivR4 hW i) i]
theorem doublePair_laplacianR4_right {a b W : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hb : IsSmoothCompact b) (hW : ContDiff ℝ ∞ W) :
    doublePair a (laplacianR4 b) W = doublePair a b (laplacianR4 W) := by
  have hl : doublePair a (laplacianR4 b) W =
      ∑ i, doublePair a (partialDerivR4 i (partialDerivR4 i b)) W := by
    unfold doublePair
    rw [← integral_finsetSum _ fun i _ =>
      integrable_doublePair ha ((hb.partialDeriv i).partialDeriv i) hW.continuous]
    congr 1
    funext p
    simp only [laplacianR4, Finset.sum_mul, Finset.mul_sum]
  have hr : doublePair a b (laplacianR4 W) =
      ∑ i, doublePair a b (partialDerivR4 i (partialDerivR4 i W)) := by
    unfold doublePair
    rw [← integral_finsetSum _ fun i _ => integrable_doublePair ha hb
      (contDiff_partialDerivR4 (contDiff_partialDerivR4 hW i) i).continuous]
    congr 1
    funext p
    simp only [laplacianR4, Finset.mul_sum]
  rw [hl, hr]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [doublePair_partialDerivR4_right ha (hb.partialDeriv i) hW i,
    doublePair_partialDerivR4_right ha hb (contDiff_partialDerivR4 hW i) i, neg_neg]
theorem doublePair_triLap_left {a b W : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hb : IsSmoothCompact b) (hW : ContDiff ℝ ∞ W) :
    doublePair (triLap a) b W = doublePair a b (triLap W) := by
  rw [doublePair_laplacianR4_left ha.laplacian.laplacian hb hW,
    doublePair_laplacianR4_left ha.laplacian hb (contDiff_laplacianR4 hW),
    doublePair_laplacianR4_left ha hb (contDiff_laplacianR4 (contDiff_laplacianR4 hW))]
theorem doublePair_triLap_right {a b W : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hb : IsSmoothCompact b) (hW : ContDiff ℝ ∞ W) :
    doublePair a (triLap b) W = doublePair a b (triLap W) := by
  rw [doublePair_laplacianR4_right ha hb.laplacian.laplacian hW,
    doublePair_laplacianR4_right ha hb.laplacian (contDiff_laplacianR4 hW),
    doublePair_laplacianR4_right ha hb (contDiff_laplacianR4 (contDiff_laplacianR4 hW))]
def iterIntegral (a b W : AmbientSpace → ℂ) : ℂ :=
  lebesgueIntegral fun y : AmbientSpace => lebesgueIntegral fun x : AmbientSpace =>
    a x * b y * W (y - x)
theorem iterIntegral_congr {a b W W' : AmbientSpace → ℂ}
    (h : ∀ x ∈ tsupport a, ∀ y ∈ tsupport b, W (y - x) = W' (y - x)) :
    iterIntegral a b W = iterIntegral a b W' := by
  unfold iterIntegral
  congr 1
  funext y
  congr 1
  funext x
  by_cases hx : a x = 0
  · simp [hx]
  by_cases hy : b y = 0
  · simp [hy]
  rw [h x (subset_tsupport _ hx) y (subset_tsupport _ hy)]
theorem doublePair_eq_iterIntegral {a b W : AmbientSpace → ℂ} (ha : IsSmoothCompact a)
    (hb : IsSmoothCompact b) (hW : Continuous W) : doublePair a b W = iterIntegral a b W := by apply _root_.YangMills.Construction.TwoPoints.LocalFormKernel.doublePair_eq_integral_integral <;> assumption
theorem isDisjointSupportPair_symm {f g : AmbientSpace → ℂ} (p : IsDisjointSupportPair f g) :
    IsDisjointSupportPair g f :=
  ⟨p.2.1, p.1, Disjoint.symm p.2.2⟩
theorem complexifyForm_add_add {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    (hlin : ComplexifyLinear S) {f₁ f₂ g₁ g₂ : AmbientSpace → ℂ}
    (p11 : IsDisjointSupportPair f₁ g₁) (p12 : IsDisjointSupportPair f₁ g₂)
    (p21 : IsDisjointSupportPair f₂ g₁) (p22 : IsDisjointSupportPair f₂ g₂) :
    complexifyForm S (f₁ + f₂) (g₁ + g₂) =
      complexifyForm S f₁ g₁ + complexifyForm S f₁ g₂ + complexifyForm S f₂ g₁ +
        complexifyForm S f₂ g₂ := by
  have a1 := hlin 1 1 g₁ g₂ f₁ (isDisjointSupportPair_symm p11) (isDisjointSupportPair_symm p12)
  have a2 := hlin 1 1 g₁ g₂ f₂ (isDisjointSupportPair_symm p21) (isDisjointSupportPair_symm p22)
  simp only [one_smul, one_mul] at a1 a2
  have a3 := hlin 1 1 f₁ f₂ (g₁ + g₂) (isDisjointSupportPair_symm a1.1)
    (isDisjointSupportPair_symm a2.1)
  simp only [one_smul, one_mul] at a3
  rw [a3.2.1, a1.2.2, a2.2.2]
  ring
def kernelFn (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (ψ χ : AmbientSpace → ℂ) :
    AmbientSpace → ℂ :=
  triLap (triLap (shiftPairing S ψ ψ)) + triLap (shiftPairing S ψ χ) +
    triLap (shiftPairing S χ ψ) + shiftPairing S χ χ
theorem mem_compactC1Complex_of_mem {ε : ℝ} {φ : AmbientSpace → ℂ} (h : φ ∈ cc1NearZero ε) :
    φ ∈ compactC1Complex :=
  ⟨h.1, h.2.1, subset_univ _⟩
theorem complexifyForm_eq_iterIntegral_kernelFn {St : FixedScale}
    {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {ε : ℝ} {c : AmbientSpace}
    {U : Set AmbientSpace} {ψ χ : AmbientSpace → ℂ} (hs : ψ ∈ cc1NearZero ε)
    (hr : χ ∈ cc1NearZero ε)
    (hk : ∀ k ∈ ccInfIn (univ : Set AmbientSpace), k = convolve (triLap k) ψ + convolve k χ)
    (hB : euclidClosedBall c (2 * ε) ⊆ U) (hUε : U ⊆ {z | 2 * ε < euclidNorm z})
    (hV : ∀ φ₁ ∈ cc1NearZero ε, ∀ φ₂ ∈ cc1NearZero ε, AnalyticOnNhd ℝ (shiftPairing S φ₁ φ₂) U)
    (hlin : ComplexifyLinear S) (hconv : RiemannSumConvApprox St)
    (hsup : ∀ φ₁ ∈ cc1NearZero ε, ∀ φ₂ ∈ cc1NearZero ε,
      ∀ k₁ ∈ ccIn (univ : Set AmbientSpace), ∀ k₂ ∈ ccIn (univ : Set AmbientSpace),
          (∀ x ∈ tsupport k₁, ∀ y ∈ tsupport k₂, 2 * ε < euclidNorm (y - x)) →
            DisjointSupports (convolve k₁ φ₁) (convolve k₂ φ₂) ∧
              complexifyForm S (convolve k₁ φ₁) (convolve k₂ φ₂) =
                iterIntegral k₁ k₂ (shiftPairing S φ₁ φ₂))
    {k₁ k₂ : AmbientSpace → ℂ} (hk₁ : k₁ ∈ ccInfIn (euclidOpenBall (0 : AmbientSpace) ε))
    (hk₂ : k₂ ∈ ccInfIn (euclidOpenBall c ε)) :
    complexifyForm S k₁ k₂ = iterIntegral k₁ k₂ (kernelFn S ψ χ) := by
  have t₁ : IsSmoothCompact k₁ := ⟨hk₁.1, hk₁.2.1⟩
  have t₂ : IsSmoothCompact k₂ := ⟨hk₂.1, hk₂.2.1⟩
  let K : Set AmbientSpace :=
    (fun p : AmbientSpace × AmbientSpace => p.1 - p.2) '' (tsupport k₂ ×ˢ tsupport k₁)
  have hKc : IsCompact K :=
    (t₂.compact.isCompact.prod t₁.compact.isCompact).image (continuous_fst.sub continuous_snd)
  have hKb : K ⊆ euclidOpenBall c (2 * ε) := by
    rintro _ ⟨⟨y, x⟩, ⟨hy, hx⟩, rfl⟩
    have a : euclidNorm (y - c) < ε := hk₂.2.2 hy
    have b : euclidNorm (x - 0) < ε := hk₁.2.2 hx
    have e : y - x - c = (y - c) + -(x - 0) := by
      rw [sub_zero]
      abel
    have d := euclidNorm_add_le (y - c) (-(x - 0))
    rw [euclidNorm_neg, ← e] at d
    change euclidNorm (y - x - c) < 2 * ε
    linarith
  have hdiff : ∀ x ∈ tsupport k₁, ∀ y ∈ tsupport k₂, y - x ∈ K :=
    fun x hx y hy => ⟨(y, x), ⟨hy, hx⟩, rfl⟩
  have hfar : ∀ x ∈ tsupport k₁, ∀ y ∈ tsupport k₂, 2 * ε < euclidNorm (y - x) :=
    fun x hx y hy =>
      hUε (hB (mem_euclidClosedBall_of_mem_euclidOpenBall (hKb (hdiff x hx y hy))))
  obtain ⟨ρ, hρ, h1, h0⟩ := exists_smooth_bump hKc hKb
  have hc : ∀ φ₁ ∈ cc1NearZero ε, ∀ φ₂ ∈ cc1NearZero ε,
      ContDiff ℝ ∞ (bumpMul ρ (shiftPairing S φ₁ φ₂)) :=
    fun φ₁ h₁ φ₂ h₂ => contDiff_bumpMul hρ h0 hB (hV φ₁ h₁ φ₂ h₂)
  have term : ∀ φ₁ ∈ cc1NearZero ε, ∀ φ₂ ∈ cc1NearZero ε, ∀ a b : AmbientSpace → ℂ,
      IsSmoothCompact a → tsupport a ⊆ tsupport k₁ → IsSmoothCompact b →
      tsupport b ⊆ tsupport k₂ →
      IsDisjointSupportPair (convolve a φ₁) (convolve b φ₂) ∧
        complexifyForm S (convolve a φ₁) (convolve b φ₂) =
          doublePair a b (bumpMul ρ (shiftPairing S φ₁ φ₂)) := by
    intro φ₁ h₁ φ₂ h₂ a b ha hsa hb hsb
    have ca : a ∈ ccIn (univ : Set AmbientSpace) :=
      (mem_ccIn_iff _ _).2 ⟨ha.continuous, ha.compact, subset_univ _⟩
    have cb : b ∈ ccIn (univ : Set AmbientSpace) :=
      (mem_ccIn_iff _ _).2 ⟨hb.continuous, hb.compact, subset_univ _⟩
    obtain ⟨hd, he⟩ := hsup φ₁ h₁ φ₂ h₂ a ca b cb
      fun x hx y hy => hfar x (hsa hx) y (hsb hy)
    refine ⟨⟨(hconv a ca φ₁ (mem_compactC1Complex_of_mem h₁) 1 one_pos).1,
      (hconv b cb φ₂ (mem_compactC1Complex_of_mem h₂) 1 one_pos).1, hd⟩, ?_⟩
    rw [he, doublePair_eq_iterIntegral ha hb (hc φ₁ h₁ φ₂ h₂).continuous]
    exact iterIntegral_congr fun x hx y hy =>
      (bumpMul_eventuallyEq h1 (hdiff x (hsa hx) y (hsb hy))).self_of_nhds.symm
  have s₁ : tsupport (triLap k₁) ⊆ tsupport k₁ := tsupport_triLap_subset t₁.smooth
  have s₂ : tsupport (triLap k₂) ⊆ tsupport k₂ := tsupport_triLap_subset t₂.smooth
  obtain ⟨p11, e11⟩ := term ψ hs ψ hs (triLap k₁) (triLap k₂) t₁.triLap s₁ t₂.triLap s₂
  obtain ⟨p12, e12⟩ := term ψ hs χ hr (triLap k₁) k₂ t₁.triLap s₁ t₂ subset_rfl
  obtain ⟨p21, e21⟩ := term χ hr ψ hs k₁ (triLap k₂) t₁ subset_rfl t₂.triLap s₂
  obtain ⟨p22, e22⟩ := term χ hr χ hr k₁ k₂ t₁ subset_rfl t₂ subset_rfl
  have hexp : complexifyForm S k₁ k₂ =
      complexifyForm S (convolve (triLap k₁) ψ + convolve k₁ χ)
        (convolve (triLap k₂) ψ + convolve k₂ χ) := by
    rw [← hk k₁ ⟨hk₁.1, hk₁.2.1, subset_univ _⟩, ← hk k₂ ⟨hk₂.1, hk₂.2.1, subset_univ _⟩]
  have css := hc ψ hs ψ hs
  have csr := hc ψ hs χ hr
  have crs := hc χ hr ψ hs
  have crr := hc χ hr χ hr
  have c1 := (contDiff_triLap (contDiff_triLap css)).continuous
  have c2 := (contDiff_triLap csr).continuous
  have c3 := (contDiff_triLap crs).continuous
  have c4 := crr.continuous
  have c12 : Continuous (triLap (triLap (bumpMul ρ (shiftPairing S ψ ψ))) +
      triLap (bumpMul ρ (shiftPairing S ψ χ))) := c1.add c2
  have c123 : Continuous (triLap (triLap (bumpMul ρ (shiftPairing S ψ ψ))) +
      triLap (bumpMul ρ (shiftPairing S ψ χ)) + triLap (bumpMul ρ (shiftPairing S χ ψ))) :=
    c12.add c3
  have c1234 : Continuous (triLap (triLap (bumpMul ρ (shiftPairing S ψ ψ))) +
      triLap (bumpMul ρ (shiftPairing S ψ χ)) + triLap (bumpMul ρ (shiftPairing S χ ψ)) +
      bumpMul ρ (shiftPairing S χ χ)) := c123.add c4
  rw [hexp, complexifyForm_add_add hlin p11 p12 p21 p22, e11, e12, e21, e22,
    doublePair_triLap_left t₁ t₂.triLap css, doublePair_triLap_right t₁ t₂ (contDiff_triLap css),
    doublePair_triLap_left t₁ t₂ csr, doublePair_triLap_right t₁ t₂ crs,
    ← doublePair_add t₁ t₂ c1 c2, ← doublePair_add t₁ t₂ c12 c3, ← doublePair_add t₁ t₂ c123 c4,
    doublePair_eq_iterIntegral t₁ t₂ c1234]
  refine iterIntegral_congr fun x hx y hy => ?_
  have hz := hdiff x hx y hy
  have g1 := (triLap_congr (triLap_congr (bumpMul_eventuallyEq (W := shiftPairing S ψ ψ) h1
    hz))).self_of_nhds
  have g2 := (triLap_congr (bumpMul_eventuallyEq (W := shiftPairing S ψ χ) h1 hz)).self_of_nhds
  have g3 := (triLap_congr (bumpMul_eventuallyEq (W := shiftPairing S χ ψ) h1 hz)).self_of_nhds
  have g4 := (bumpMul_eventuallyEq (W := shiftPairing S χ χ) h1 hz).self_of_nhds
  simp only [kernelFn, Pi.add_apply]
  rw [g1, g2, g3, g4]
theorem holds (hfirst : AdmissibleFormConsequences.Statement)
    (hpar : LaplacianCubeParametrix.Statement)
    (hpair : ShiftPairingLocallyAnalytic.Statement)
    (htr : SharpNormTranslates) :
    LocalFormKernel.Statement := by
  intro St S hS hP c hc
  have hε : 0 < euclidNorm c / 32 := by
    have := euclidNorm_pos hc
    positivity
  obtain ⟨ψ, hψ, χ, hχ, hk⟩ := hpar _ hε
  obtain ⟨U, hUo, hBU, hUε, hV⟩ := hpair St S hS hP c hc
  obtain ⟨C₂, hC₂⟩ := hP.ballDecay
  have hlin : ComplexifyLinear S := (hfirst.2.2.2.2 St S C₂ hS hP hC₂).1.2.1
  obtain ⟨-, hconv, hsup, -⟩ := htr St
  have hs : ψ ∈ cc1NearZero (euclidNorm c / 32) := hψ.1
  have hr : χ ∈ cc1NearZero (euclidNorm c / 32) :=
    ⟨hχ.1.1.of_le (by simp), hχ.1.2.1, hχ.1.2.2⟩
  refine ⟨kernelFn S ψ χ, ?_, ?_⟩
  · have A1 := analyticOnNhd_triLap hUo (analyticOnNhd_triLap hUo (hV ψ hs ψ hs))
    have A2 := analyticOnNhd_triLap hUo (hV ψ hs χ hr)
    have A3 := analyticOnNhd_triLap hUo (hV χ hr ψ hs)
    have A4 := hV χ hr χ hr
    exact (((A1.add A2).add A3).add A4).mono fun z hz =>
      hBU (mem_euclidClosedBall_of_mem_euclidOpenBall hz)
  · intro k₁ hk₁ k₂ hk₂
    exact complexifyForm_eq_iterIntegral_kernelFn hs hr hk hBU hUε hV hlin hconv
      (fun φ₁ h₁ φ₂ h₂ a ha b hb hab => (hsup S hS hP _ hε φ₁ h₁ φ₂ h₂).2.2 a ha b hb hab) hk₁ hk₂
end LocalFormKernel
end YangMills.Construction.TwoPoints
end
