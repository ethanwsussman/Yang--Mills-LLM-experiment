import YangMills.Construction.MinkowskiSpace.MeasureOfTheTimeTranslationsAndTheVectorsTheyFixProof
import YangMills.Construction.PassageToTheLimit.SpacesOfFunctionsOfClassC1AreBanachSpacesProof
import YangMills.Construction.ReflectionPositivity.ContractionOfTheLimitOfALatticeApproximationProof
import Reconstruction.Continuum.KernelsThatGiveBackAFunctionFromItsThirdDerivativesProof
import Reconstruction.MinkowskiSpace.ClassesOfOneInsertedField
import Reconstruction.MinkowskiSpace.ConjugatedInsertionsOfTheKernels
import Reconstruction.MinkowskiSpace.DensityNearTheMiddleOfASlab
import Reconstruction.MinkowskiSpace.InsertionOperatorsOfOneField
import Reconstruction.MinkowskiSpace.SmearingOfTheInsertionOperators
import Reconstruction.MinkowskiSpace.SmoothedFieldOfTheKernels
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import Mathlib
set_option autoImplicit false
open YangMills.Construction.TestFunctions MeasureTheory
open scoped ContDiff Topology
namespace YangMills.Construction.CentralDensity
def basisVec (μ : Fin 4) : Fin 4 → ℝ := Pi.single μ 1
theorem partialDerivR4_eq_fderiv {g : (Fin 4 → ℝ) → ℂ} {y : Fin 4 → ℝ}
    (hg : DifferentiableAt ℝ g y) (μ : Fin 4) :
    partialDerivR4 μ g y = fderiv ℝ g y (basisVec μ) :=
  hg.lineDeriv_eq_fderiv
theorem contDiff_partialDerivR4 {g : (Fin 4 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (μ : Fin 4) :
    ContDiff ℝ ∞ (partialDerivR4 μ g) := by apply _root_.YangMills.Construction.CubeKernels.contDiff_partialDerivR4 <;> assumption
theorem contDiffOn_partialDerivR4 {g : (Fin 4 → ℝ) → ℂ} {O : Set (Fin 4 → ℝ)} (hO : IsOpen O)
    (hg : ContDiffOn ℝ ∞ g O) (μ : Fin 4) : ContDiffOn ℝ ∞ (partialDerivR4 μ g) O := by
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y (basisVec μ)) O :=
    (hg.fderiv_of_isOpen (m := ∞) hO (by simp)).clm_apply contDiffOn_const
  refine h1.congr fun y hy => ?_
  exact partialDerivR4_eq_fderiv
    (((hg.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))) μ
theorem partialDerivR4_eq_zero_of_notMem {g : (Fin 4 → ℝ) → ℂ} {y : Fin 4 → ℝ}
    (hy : y ∉ tsupport g) (μ : Fin 4) : partialDerivR4 μ g y = 0 := by
  have h0 : g =ᶠ[𝓝 y] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hy
  have hd : DifferentiableAt ℝ g y := (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq h0
  rw [partialDerivR4_eq_fderiv hd, h0.fderiv_eq]
  simp
theorem tsupport_partialDerivR4_subset (g : (Fin 4 → ℝ) → ℂ) (μ : Fin 4) :
    tsupport (partialDerivR4 μ g) ⊆ tsupport g := by
  refine closure_minimal ?_ (isClosed_tsupport g)
  intro y hy
  by_contra h
  exact hy (partialDerivR4_eq_zero_of_notMem h μ)
theorem continuous_mul_of_tsupport_subset {G U : (Fin 4 → ℝ) → ℂ} {O : Set (Fin 4 → ℝ)}
    (hO : IsOpen O) (hG : Continuous G) (hU : ContinuousOn U O) (hs : tsupport G ⊆ O) :
    Continuous (fun x => G x * U x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ O
  · exact hG.continuousAt.mul (hU.continuousAt (hO.mem_nhds hx))
  · have hx' : x ∉ tsupport G := fun h => hx (hs h)
    have h0 : G =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hx'
    have : (fun x => G x * U x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [h0] with y hy
      simp [hy]
    exact continuousAt_const.congr this.symm
theorem integrable_mul_of_tsupport_subset {G U : (Fin 4 → ℝ) → ℂ} {O : Set (Fin 4 → ℝ)}
    (hO : IsOpen O) (hG : Continuous G) (hc : HasCompactSupport G) (hU : ContinuousOn U O)
    (hs : tsupport G ⊆ O) : Integrable (fun x => G x * U x) :=
  (continuous_mul_of_tsupport_subset hO hG hU hs).integrable_of_hasCompactSupport hc.mul_right
theorem integral_partialDerivR4_mul {G U : (Fin 4 → ℝ) → ℂ} {O : Set (Fin 4 → ℝ)} (hO : IsOpen O)
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (hU : ContDiffOn ℝ ∞ U O)
    (hs : tsupport G ⊆ O) (μ : Fin 4) :
    ∫ x, partialDerivR4 μ G x * U x = -∫ x, G x * partialDerivR4 μ U x := by
  have hdG : Differentiable ℝ G := hG.differentiable (by simp)
  have hdU : ∀ x ∈ O, DifferentiableAt ℝ U x := fun x hx =>
    (hU.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have e1 : (fun x => fderiv ℝ G x (basisVec μ) * U x) = fun x => partialDerivR4 μ G x * U x :=
    funext fun x => by rw [partialDerivR4_eq_fderiv (hdG x)]
  have e2 : (fun x => G x * fderiv ℝ U x (basisVec μ)) = fun x => G x * partialDerivR4 μ U x := by
    funext x
    by_cases hx : x ∈ O
    · rw [partialDerivR4_eq_fderiv (hdU x hx)]
    · have hz : G x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs h)
      simp [hz]
  have hi1 : Integrable (fun x => partialDerivR4 μ G x * U x) :=
    integrable_mul_of_tsupport_subset hO (contDiff_partialDerivR4 hG μ).continuous
      (hc.mono' ((subset_tsupport _).trans (tsupport_partialDerivR4_subset G μ))) hU.continuousOn
      ((tsupport_partialDerivR4_subset G μ).trans hs)
  have hi2 : Integrable (fun x => G x * partialDerivR4 μ U x) :=
    integrable_mul_of_tsupport_subset hO hG.continuous hc
      (contDiffOn_partialDerivR4 hO hU μ).continuousOn hs
  have hi3 : Integrable (fun x => G x * U x) :=
    integrable_mul_of_tsupport_subset hO hG.continuous hc hU.continuousOn hs
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Fin 4 → ℝ)))
    (f := G) (g := U) (v := basisVec μ) (e1 ▸ hi1) (e2 ▸ hi2) hi3 (fun x _ => hdG x)
    (fun x hx => hdU x (hs hx))
  rw [e1, e2] at h
  rw [h, neg_neg]
structure IsSmoothCompactIn (O : Set (Fin 4 → ℝ)) (G : (Fin 4 → ℝ) → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ G
  hasCompactSupport : HasCompactSupport G
  tsupport_subset : tsupport G ⊆ O
theorem IsSmoothCompactIn.partialDeriv {O : Set (Fin 4 → ℝ)} {G : (Fin 4 → ℝ) → ℂ}
    (h : IsSmoothCompactIn O G) (μ : Fin 4) : IsSmoothCompactIn O (partialDerivR4 μ G) :=
  ⟨contDiff_partialDerivR4 h.contDiff μ,
    h.hasCompactSupport.mono' ((subset_tsupport _).trans (tsupport_partialDerivR4_subset G μ)),
    (tsupport_partialDerivR4_subset G μ).trans h.tsupport_subset⟩
theorem IsSmoothCompactIn.iterate_partialDeriv {O : Set (Fin 4 → ℝ)} {G : (Fin 4 → ℝ) → ℂ}
    (h : IsSmoothCompactIn O G) (μ : Fin 4) (n : ℕ) :
    IsSmoothCompactIn O ((partialDerivR4 μ)^[n] G) := by
  induction n generalizing G with
  | zero => exact h
  | succ n ih => exact ih (h.partialDeriv μ)
theorem contDiffOn_iterate_partialDerivR4 {O : Set (Fin 4 → ℝ)} (hO : IsOpen O)
    {U : (Fin 4 → ℝ) → ℂ} (hU : ContDiffOn ℝ ∞ U O) (μ : Fin 4) (n : ℕ) :
    ContDiffOn ℝ ∞ ((partialDerivR4 μ)^[n] U) O := by
  induction n generalizing U with
  | zero => exact hU
  | succ n ih => exact ih (contDiffOn_partialDerivR4 hO hU μ)
theorem integral_iterate_partialDerivR4_mul {O : Set (Fin 4 → ℝ)} (hO : IsOpen O)
    {G U : (Fin 4 → ℝ) → ℂ} (hG : IsSmoothCompactIn O G) (hU : ContDiffOn ℝ ∞ U O) (μ : Fin 4)
    (n : ℕ) :
    ∫ x, (partialDerivR4 μ)^[n] G x * U x =
      (-1) ^ n * ∫ x, G x * (partialDerivR4 μ)^[n] U x := by
  induction n generalizing G U with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih (hG.partialDeriv μ) hU,
      integral_partialDerivR4_mul hO hG.contDiff hG.hasCompactSupport
        (contDiffOn_iterate_partialDerivR4 hO hU μ n) hG.tsupport_subset μ,
      Function.iterate_succ_apply', pow_succ]
    ring
abbrev SmoothFn : Type := {G : (Fin 4 → ℝ) → ℂ // ContDiff ℝ ∞ G}
noncomputable def smoothPartial (μ : Fin 4) (G : SmoothFn) : SmoothFn :=
  ⟨partialDerivR4 μ G.1, contDiff_partialDerivR4 G.2 μ⟩
theorem partialDerivR4_comm {G : (Fin 4 → ℝ) → ℂ} (hG : ContDiff ℝ ∞ G) (μ ν : Fin 4) :
    partialDerivR4 μ (partialDerivR4 ν G) = partialDerivR4 ν (partialDerivR4 μ G) := by
  have hd : Differentiable ℝ G := hG.differentiable (by simp)
  have hf : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (m := ∞) (by simp)
  have hdf : Differentiable ℝ (fderiv ℝ G) := hf.differentiable (by simp)
  have e : ∀ ρ, partialDerivR4 ρ G = fun y => fderiv ℝ G y (basisVec ρ) :=
    fun ρ => funext fun y => partialDerivR4_eq_fderiv (hd y) ρ
  have e2 : ∀ ρ τ x, partialDerivR4 ρ (partialDerivR4 τ G) x =
      fderiv ℝ (fderiv ℝ G) x (basisVec ρ) (basisVec τ) := by
    intro ρ τ x
    have hh : HasFDerivAt (fun y => fderiv ℝ G y (basisVec τ))
        ((fderiv ℝ (fderiv ℝ G) x).flip (basisVec τ)) x :=
      (hdf x).hasFDerivAt.clm_apply (hasFDerivAt_const _ _) |>.congr_fderiv (by ext; simp)
    rw [e τ, partialDerivR4_eq_fderiv hh.differentiableAt, hh.fderiv]
    rfl
  funext x
  rw [e2, e2]
  exact (hG.contDiffAt.isSymmSndFDerivAt (by
    simp
    exact (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.2 le_top))) _ _
theorem commute_smoothPartial (μ ν : Fin 4) :
    Function.Commute (smoothPartial μ) (smoothPartial ν) := fun G =>
  Subtype.ext (partialDerivR4_comm G.2 μ ν)
theorem val_iterate_smoothPartial (μ : Fin 4) (n : ℕ) (G : SmoothFn) :
    ((smoothPartial μ)^[n] G).1 = (partialDerivR4 μ)^[n] G.1 := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]; rfl
theorem iterate_partialDerivR4_reverse {G : (Fin 4 → ℝ) → ℂ} (hG : ContDiff ℝ ∞ G)
    (a b c d : ℕ) :
    (partialDerivR4 0)^[a] ((partialDerivR4 1)^[b] ((partialDerivR4 2)^[c]
        ((partialDerivR4 3)^[d] G))) =
      (partialDerivR4 3)^[d] ((partialDerivR4 2)^[c] ((partialDerivR4 1)^[b]
        ((partialDerivR4 0)^[a] G))) := by
  have C : ∀ (μ ν : Fin 4) (m n : ℕ) (X : SmoothFn),
      (smoothPartial μ)^[m] ((smoothPartial ν)^[n] X) =
        (smoothPartial ν)^[n] ((smoothPartial μ)^[m] X) := fun μ ν m n X =>
    ((commute_smoothPartial μ ν).iterate_iterate m n) X
  have key : (smoothPartial 0)^[a] ((smoothPartial 1)^[b] ((smoothPartial 2)^[c]
      ((smoothPartial 3)^[d] ⟨G, hG⟩))) =
      (smoothPartial 3)^[d] ((smoothPartial 2)^[c] ((smoothPartial 1)^[b]
        ((smoothPartial 0)^[a] ⟨G, hG⟩))) := by
    rw [C 2 3, C 1 3, C 0 3, C 1 2, C 0 2, C 0 1]
  have := congrArg Subtype.val key
  simpa only [val_iterate_smoothPartial] using this
theorem integral_iterate_four_mul {O : Set (Fin 4 → ℝ)} (hO : IsOpen O) {G U : (Fin 4 → ℝ) → ℂ}
    (hG : IsSmoothCompactIn O G) (hU : ContDiffOn ℝ ∞ U O) (a b c d : ℕ) :
    ∫ x, (partialDerivR4 0)^[a] ((partialDerivR4 1)^[b] ((partialDerivR4 2)^[c]
        ((partialDerivR4 3)^[d] G))) x * U x =
      (-1) ^ (a + b + c + d) * ∫ x, G x * (partialDerivR4 0)^[a] ((partialDerivR4 1)^[b]
        ((partialDerivR4 2)^[c] ((partialDerivR4 3)^[d] U))) x := by
  rw [iterate_partialDerivR4_reverse hG.contDiff,
    integral_iterate_partialDerivR4_mul hO
      (((hG.iterate_partialDeriv 0 a).iterate_partialDeriv 1 b).iterate_partialDeriv 2 c) hU 3 d,
    integral_iterate_partialDerivR4_mul hO
      ((hG.iterate_partialDeriv 0 a).iterate_partialDeriv 1 b)
      (contDiffOn_iterate_partialDerivR4 hO hU 3 d) 2 c,
    integral_iterate_partialDerivR4_mul hO (hG.iterate_partialDeriv 0 a)
      (contDiffOn_iterate_partialDerivR4 hO (contDiffOn_iterate_partialDerivR4 hO hU 3 d) 2 c) 1 b,
    integral_iterate_partialDerivR4_mul hO hG
      (contDiffOn_iterate_partialDerivR4 hO (contDiffOn_iterate_partialDerivR4 hO
        (contDiffOn_iterate_partialDerivR4 hO hU 3 d) 2 c) 1 b) 0 a]
  simp only [pow_add]
  ring
theorem norm_basisVec_le (μ : Fin 4) : ‖basisVec μ‖ ≤ 1 := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.C1Banach.norm_single_one_le <;> assumption
theorem exists_smooth_approx {g : (Fin 4 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    ∃ g' : (Fin 4 → ℝ) → ℂ, ContDiff ℝ ∞ g' ∧ HasCompactSupport g' ∧
      tsupport g' ⊆ Metric.cthickening r (tsupport g) ∧ (∀ x, ‖g' x - g x‖ ≤ δ) ∧
      ∀ μ x, ‖partialDerivR4 μ g' x - partialDerivR4 μ g x‖ ≤ δ := by
  have hdg : Differentiable ℝ g := hg.differentiable (by simp)
  have hD : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  have hDc : HasCompactSupport (fderiv ℝ g) := hc.fderiv (𝕜 := ℝ)
  obtain ⟨ρ₀, hρ₀, h₀⟩ := Metric.uniformContinuous_iff.1
    (hc.uniformContinuous_of_continuous hg.continuous) δ hδ
  obtain ⟨ρ₁, hρ₁, h₁⟩ := Metric.uniformContinuous_iff.1
    (hDc.uniformContinuous_of_continuous hD) δ hδ
  set ρ : ℝ := min r (min ρ₀ ρ₁) with hρdef
  have hρ : 0 < ρ := lt_min hr (lt_min hρ₀ hρ₁)
  let φ : ContDiffBump (0 : Fin 4 → ℝ) := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  have hφr : φ.rOut = ρ := rfl
  let n : (Fin 4 → ℝ) → ℝ := φ.normed volume
  have hn : ContDiff ℝ ∞ n := φ.contDiff_normed
  have hnc : HasCompactSupport n := φ.hasCompactSupport_normed
  have hnl : LocallyIntegrable n := hn.continuous.locallyIntegrable
  have hgl : LocallyIntegrable g := hg.continuous.locallyIntegrable
  let L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  refine ⟨convolution n g L volume, ?_, ?_, ?_, ?_, ?_⟩
  · exact hnc.contDiff_convolution_left L hn hgl
  · exact hnc.convolution L hc
  · refine closure_minimal ?_ Metric.isClosed_cthickening
    refine (support_convolution_subset L).trans ?_
    rintro _ ⟨u, hu, w, hw, rfl⟩
    have hu' : u ∈ Metric.ball (0 : Fin 4 → ℝ) ρ := by
      have : Function.support n = Metric.ball 0 φ.rOut := φ.support_normed_eq
      rw [this, hφr] at hu
      exact hu
    refine Metric.mem_cthickening_of_dist_le _ w _ _ (subset_tsupport _ hw) ?_
    have : dist u 0 < ρ := hu'
    have h2 : ρ ≤ r := min_le_left _ _
    simp only [dist_eq_norm, add_sub_cancel_right] at this ⊢
    simp only [sub_zero] at this
    linarith
  · intro x
    have := φ.dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := δ) (g := g)
      hg.continuous.aestronglyMeasurable (fun y hy => by
        have hy' : dist y x < ρ₀ := lt_of_lt_of_le hy
          ((min_le_right _ _).trans (min_le_left _ _))
        exact (h₀ hy').le)
    simpa [dist_eq_norm] using this
  · intro μ x
    have hfd := hc.hasFDerivAt_convolution_right L hnl hg x
    have e1 : partialDerivR4 μ (convolution n g L volume) x =
        convolution n (fun y => fderiv ℝ g y (basisVec μ)) L volume x := by
      rw [partialDerivR4_eq_fderiv hfd.differentiableAt, hfd.fderiv]
      exact convolution_precompR_apply L hnl hDc hD x _
    have e2 : partialDerivR4 μ g x = fderiv ℝ g x (basisVec μ) :=
      partialDerivR4_eq_fderiv (hdg x) μ
    rw [e1, e2, ← dist_eq_norm]
    refine φ.dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := δ)
      (g := fun y => fderiv ℝ g y (basisVec μ))
      (hD.clm_apply continuous_const).aestronglyMeasurable (fun y hy => ?_)
    have hy' : dist y x < ρ₁ := lt_of_lt_of_le hy
      ((min_le_right _ _).trans (min_le_right _ _))
    have h3 := (h₁ hy').le
    rw [dist_eq_norm] at h3 ⊢
    rw [← sub_apply]
    calc _ ≤ ‖fderiv ℝ g y - fderiv ℝ g x‖ * ‖basisVec μ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ δ * 1 := by gcongr; exact norm_basisVec_le μ
      _ = δ := mul_one δ
theorem supC1Norm_le {f : (Fin 4 → ℝ) → ℂ} {δ : ℝ} (hδ : 0 ≤ δ) (h0 : ∀ x, ‖f x‖ ≤ δ)
    (h1 : ∀ μ x, ‖partialDerivR4 μ f x‖ ≤ δ) : WightmanReconstruction.supC1Norm f ≤ 3 * δ := by
  have a1 : TestFunctions.uniformNorm f ≤ δ := Real.iSup_le h0 hδ
  have a2 : ⨆ x, Real.sqrt (∑ μ, ‖partialDerivR4 μ f x‖ ^ 2) ≤ 2 * δ := by
    refine Real.iSup_le (fun x => ?_) (by positivity)
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have : ∀ μ ∈ (Finset.univ : Finset (Fin 4)), ‖partialDerivR4 μ f x‖ ^ 2 ≤ δ ^ 2 :=
      fun μ _ => pow_le_pow_left₀ (norm_nonneg _) (h1 μ x) 2
    calc _ ≤ ∑ _μ : Fin 4, δ ^ 2 := Finset.sum_le_sum this
      _ = (2 * δ) ^ 2 := by simp; ring
  unfold WightmanReconstruction.supC1Norm
  linarith
section Geometry
open InsertedFieldForm FieldForms FieldFormConditions
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (v + w) ≤
      TorusMetric.euclidNormVec v + TorusMetric.euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (-v) = TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem continuous_euclidNormVec : Continuous TorusMetric.euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem smul_timeUnitVec_timeIdx (c : ℝ) : (c • timeUnitVec) TimeAxis.timeIdx = c := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitContraction.timeComponent_smul_basisVector <;> assumption
theorem isOpen_centralBox (η : ℝ) : IsOpen (centralBox η) := by
  have h1 : IsOpen {a : Fin 4 → ℝ | |a TimeAxis.timeIdx| < η / 4} :=
    isOpen_lt (continuous_abs.comp (continuous_apply _)) continuous_const
  have h2 : IsOpen {a : Fin 4 → ℝ | TorusMetric.euclidNormVec a < 1 / 4} :=
    isOpen_lt continuous_euclidNormVec continuous_const
  exact h1.inter h2
def shiftedBox (η : ℝ) : Set (Fin 4 → ℝ) := {x | x - (2 * η) • timeUnitVec ∈ centralBox η}
theorem isOpen_shiftedBox (η : ℝ) : IsOpen (shiftedBox η) :=
  (isOpen_centralBox η).preimage (continuous_id.sub continuous_const)
def smallCube (η : ℝ) : Set (Fin 4 → ℝ) := {x | ∀ μ, x μ ∈ Set.Icc 0 (η / 8)}
theorem euclidNormVec_sub_le_of_mem_smallCube {η : ℝ} (hη1 : η ≤ 1) {y y' : Fin 4 → ℝ}
    (hy : y ∈ smallCube η) (hy' : y' ∈ smallCube η) :
    TorusMetric.euclidNormVec (y - y') ≤ 1 / 4 := by
  unfold TorusMetric.euclidNormVec
  refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
  have : ∀ μ ∈ (Finset.univ : Finset (Fin 4)), (y - y') μ ^ 2 ≤ (1 / 8) ^ 2 := by
    intro μ _
    have h1 := hy μ
    have h2 := hy' μ
    simp only [Set.mem_Icc] at h1 h2
    have : |(y - y') μ| ≤ 1 / 8 := by
      rw [Pi.sub_apply, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc _ ≤ ∑ _μ : Fin 4, ((1 : ℝ) / 8) ^ 2 := Finset.sum_le_sum this
    _ ≤ _ := by norm_num
theorem timeIdx_add_mem_of_shiftedBox {η : ℝ} (hη : 0 < η) {x y : Fin 4 → ℝ}
    (hx : x ∈ shiftedBox η) (hy : y ∈ smallCube η) :
    η ≤ (x + y) TimeAxis.timeIdx ∧ (x + y) TimeAxis.timeIdx ≤ 3 * η := by
  have h1 := (abs_lt.1 hx.1)
  have h2 := hy TimeAxis.timeIdx
  simp only [Set.mem_Icc] at h2
  have h3 : (x - (2 * η) • timeUnitVec) TimeAxis.timeIdx = x TimeAxis.timeIdx - 2 * η := by
    rw [Pi.sub_apply, smul_timeUnitVec_timeIdx]
  rw [h3] at h1
  rw [Pi.add_apply]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
theorem euclidNormVec_add_sub_le {η : ℝ} (hη1 : η ≤ 1) {x x' y y' : Fin 4 → ℝ}
    (hx : x ∈ shiftedBox η) (hx' : x' ∈ shiftedBox η) (hy : y ∈ smallCube η)
    (hy' : y' ∈ smallCube η) :
    TorusMetric.euclidNormVec ((x + y) - (x' + y')) ≤ 1 := by
  have e : (x + y) - (x' + y') =
      ((x - (2 * η) • timeUnitVec) + -(x' - (2 * η) • timeUnitVec)) + (y - y') := by abel
  rw [e]
  have h1 := hx.2
  have h2 := hx'.2
  have h3 := euclidNormVec_sub_le_of_mem_smallCube hη1 hy hy'
  have h4 := euclidNormVec_add_le
    ((x - (2 * η) • timeUnitVec) + -(x' - (2 * η) • timeUnitVec)) (y - y')
  have h5 := euclidNormVec_add_le (x - (2 * η) • timeUnitVec) (-(x' - (2 * η) • timeUnitVec))
  rw [euclidNormVec_neg] at h5
  linarith
theorem zero_mem_smallCube {η : ℝ} (hη : 0 < η) : (0 : Fin 4 → ℝ) ∈ smallCube η := fun μ => by
  simp only [Pi.zero_apply, Set.mem_Icc, le_refl, true_and]
  positivity
theorem isAdmissible_of_tsupport_subset {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {f : (Fin 4 → ℝ) → ℂ} (h1 : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Set.image2 (· + ·) (shiftedBox η) (smallCube η)) : IsAdmissible η f where
  mem := ⟨h1, hc, Set.subset_univ _⟩
  tsupport_time x hx := by
    obtain ⟨u, hu, v, hv, rfl⟩ := hs hx
    exact timeIdx_add_mem_of_shiftedBox hη hu hv
  diam_le x hx y hy := by
    obtain ⟨u, hu, v, hv, rfl⟩ := hs hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hs hy
    exact euclidNormVec_add_sub_le hη1 hu hu' hv hv'
theorem shiftedBox_subset_add {η : ℝ} (hη : 0 < η) :
    shiftedBox η ⊆ Set.image2 (· + ·) (shiftedBox η) (smallCube η) := fun x hx =>
  ⟨x, hx, 0, zero_mem_smallCube hη, add_zero x⟩
end Geometry
section Main
open InsertedFieldForm FieldForms FieldFormConditions CubeKernels ReflectionPositivity.TupleForm
  ReflectionPositivity.FormProperties
open scoped InnerProductSpace
theorem realWickPoint_smul_timeUnitVec (η : ℝ) :
    realWickPoint (η • timeUnitVec) = imagTimeShift η := by apply _root_.YangMills.Construction.TimeTranslations.wickMap_smul_timeUnitVec <;> assumption
theorem partialDerivR4_comp_add (b : Fin 4 → ℝ) (μ : Fin 4) (f : (Fin 4 → ℝ) → ℂ) :
    partialDerivR4 μ (fun a => f (b + a)) = fun a => partialDerivR4 μ f (b + a) := by
  funext a
  simp only [partialDerivR4, add_assoc]
theorem iterate_partialDerivR4_comp_add (b : Fin 4 → ℝ) (μ : Fin 4) (n : ℕ)
    (f : (Fin 4 → ℝ) → ℂ) :
    (partialDerivR4 μ)^[n] (fun a => f (b + a)) = fun a => (partialDerivR4 μ)^[n] f (b + a) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, partialDerivR4_comp_add, ih (partialDerivR4 μ f)]
    rfl
def cubeExponent (Γ : Finset (Fin 4)) (μ : Fin 4) : ℕ := if μ ∈ Γ then 3 else 0
theorem cubedPartial_eq_iterate (Γ : Finset (Fin 4)) (f : (Fin 4 → ℝ) → ℂ) :
    cubedPartial Γ f = (partialDerivR4 0)^[cubeExponent Γ 0] ((partialDerivR4 1)^[cubeExponent Γ 1]
      ((partialDerivR4 2)^[cubeExponent Γ 2] ((partialDerivR4 3)^[cubeExponent Γ 3] f))) := rfl
theorem cubedPartial_comp_add (b : Fin 4 → ℝ) (Γ : Finset (Fin 4)) (f : (Fin 4 → ℝ) → ℂ) :
    cubedPartial Γ (fun a => f (b + a)) = fun a => cubedPartial Γ f (b + a) := by
  simp only [cubedPartial_eq_iterate, iterate_partialDerivR4_comp_add]
theorem cubeExponent_sum_mod_two : ∀ Γ : Finset (Fin 4),
    (cubeExponent Γ 0 + cubeExponent Γ 1 + cubeExponent Γ 2 + cubeExponent Γ 3) % 2 =
      Γ.card % 2 := by
  unfold cubeExponent
  decide
theorem integral_cubedPartial_mul {O : Set (Fin 4 → ℝ)} (hO : IsOpen O) {G U : (Fin 4 → ℝ) → ℂ}
    (hG : IsSmoothCompactIn O G) (hU : ContDiffOn ℝ ∞ U O) (Γ : Finset (Fin 4)) :
    ∫ x, cubedPartial Γ G x * U x = (-1) ^ Γ.card * ∫ x, G x * cubedPartial Γ U x := by
  have h := integral_iterate_four_mul hO hG hU (cubeExponent Γ 0) (cubeExponent Γ 1)
    (cubeExponent Γ 2) (cubeExponent Γ 3)
  rw [neg_one_pow_eq_pow_mod_two, cubeExponent_sum_mod_two, ← neg_one_pow_eq_pow_mod_two] at h
  exact h
theorem IsSmoothCompactIn.cubedPartial {O : Set (Fin 4 → ℝ)} {G : (Fin 4 → ℝ) → ℂ}
    (h : IsSmoothCompactIn O G) (Γ : Finset (Fin 4)) :
    IsSmoothCompactIn O (CubeKernels.cubedPartial Γ G) :=
  (((h.iterate_partialDeriv 3 _).iterate_partialDeriv 2 _).iterate_partialDeriv 1 _).iterate_partialDeriv 0 _
theorem contDiffOn_cubedPartial {O : Set (Fin 4 → ℝ)} (hO : IsOpen O) {U : (Fin 4 → ℝ) → ℂ}
    (hU : ContDiffOn ℝ ∞ U O) (Γ : Finset (Fin 4)) : ContDiffOn ℝ ∞ (cubedPartial Γ U) O :=
  contDiffOn_iterate_partialDerivR4 hO (contDiffOn_iterate_partialDerivR4 hO
    (contDiffOn_iterate_partialDerivR4 hO (contDiffOn_iterate_partialDerivR4 hO hU 3 _) 2 _) 1 _) 0 _
theorem conv_regularity {k φ : (Fin 4 → ℝ) → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ContDiff ℝ 1 (EuclideanFunctionals.conv k φ) ∧
      HasCompactSupport (EuclideanFunctionals.conv k φ) ∧
      tsupport (EuclideanFunctionals.conv k φ) ⊆
        Set.image2 (· + ·) (tsupport k) (tsupport φ) := by
  have e : EuclideanFunctionals.conv k φ =
      convolution k φ (ContinuousLinearMap.mul ℝ ℂ) volume := rfl
  rw [e]
  refine ⟨?_, hkc.convolution _ hφc, ?_⟩
  · exact (hφc.contDiff_convolution_right _ hk.locallyIntegrable hφ).of_le (by simp)
  · have hcl : IsClosed (Set.image2 (· + ·) (tsupport k) (tsupport φ)) := by
      rw [Set.image2_add]
      exact (hkc.isCompact.add hφc.isCompact).isClosed
    refine closure_minimal ((support_convolution_subset _).trans ?_) hcl
    rintro _ ⟨u, hu, w, hw, rfl⟩
    exact ⟨u, subset_tsupport _ hu, w, subset_tsupport _ hw, rfl⟩
theorem scaledKernel_regularity (hK : KernelFacts) {η : ℝ} (hη : 0 < η) (Γ : Finset (Fin 4)) :
    ContDiff ℝ 1 (scaledKernel η Γ) ∧ HasCompactSupport (scaledKernel η Γ) ∧
      tsupport (scaledKernel η Γ) ⊆ smallCube η := by
  obtain ⟨h1, h2⟩ := hK.2.1.2.2.2.2.2.2 Γ (η / 8) (by positivity)
  have e : scaledKernel η Γ = (fun z : ℝ => (z : ℂ)) ∘ cubeKernel Γ (η / 8) := rfl
  rw [e]
  refine ⟨Complex.ofRealCLM.contDiff.comp h1.1,
    HasCompactSupport.comp_left h1.2 Complex.ofReal_zero, ?_⟩
  exact (tsupport_comp_subset Complex.ofReal_zero _).trans h2
theorem IsSmoothCompactIn.translate {η : ℝ} {g : (Fin 4 → ℝ) → ℂ}
    (hg : IsSmoothCompactIn (shiftedBox η) g) :
    IsSmoothCompactIn (centralBox η) (fun a => g ((2 * η) • timeUnitVec + a)) := by
  refine ⟨hg.contDiff.comp (contDiff_const.add contDiff_id),
    hg.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft _), ?_⟩
  have e := tsupport_comp_eq_preimage g (Homeomorph.addLeft ((2 * η) • timeUnitVec))
  intro a ha
  have h2 : a ∈ (Homeomorph.addLeft ((2 * η) • timeUnitVec)) ⁻¹' tsupport g := by
    rw [← e]
    exact ha
  have h3 := hg.tsupport_subset h2
  simpa [shiftedBox] using h3
variable {σ : TestSpaces.SepTuple → ℝ}
  {E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (StateSpace σ)} {p C : ℝ}
theorem central_density_of_smooth (hK : KernelFacts)
    (hI : InsertionOperators.InsertionOperatorBounds) (hS : InsertionSmearing.Claim)
    (hCj : KernelInsertionConjugation) (hV : SmoothedKernelField.Regularity)
    (hc : Hypotheses σ E p C) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {g : (Fin 4 → ℝ) → ℂ} (hg : IsSmoothCompactIn (shiftedBox η) g) (χ χ' : StateSpace σ) :
    ⟪χ, (spectralTranslation E (imagTimeShift η) * insertionOp σ η g *
        spectralTranslation E (imagTimeShift η)) χ'⟫_ℂ =
      ∫ a, g ((2 * η) • timeUnitVec + a) * ⟪χ, smoothedFieldOp σ E η a χ'⟫_ℂ := by
  set T := spectralTranslation E (imagTimeShift η) with hT
  set b : Fin 4 → ℝ := (2 * η) • timeUnitVec with hb
  have hυ : 0 < η / 8 := by positivity
  let φ : Finset (Fin 4) → (Fin 4 → ℝ) → ℂ := fun Γ => cubedPartial Γ g
  let f : Finset (Fin 4) → (Fin 4 → ℝ) → ℂ := fun Γ =>
    EuclideanFunctionals.conv (scaledKernel η Γ) (φ Γ)
  let D : Set (Fin 4 → ℝ) := Set.image2 (· + ·) (shiftedBox η) (smallCube η)
  have hφ : ∀ Γ, IsSmoothCompactIn (shiftedBox η) (φ Γ) := fun Γ => hg.cubedPartial Γ
  have hkf := fun Γ => scaledKernel_regularity hK hη Γ
  have hfacts := fun Γ => conv_regularity (hkf Γ).1.continuous (hkf Γ).2.1 (hφ Γ).contDiff
    (hφ Γ).hasCompactSupport
  have hfD : ∀ Γ, tsupport (f Γ) ⊆ D := by
    intro Γ
    refine (hfacts Γ).2.2.trans ?_
    rintro _ ⟨u, hu, w, hw, rfl⟩
    exact ⟨w, (hφ Γ).tsupport_subset hw, u, (hkf Γ).2.2 hu, add_comm _ _⟩
  have hadm : ∀ Γ, IsAdmissible η (f Γ) := fun Γ =>
    isAdmissible_of_tsupport_subset hη hη1 (hfacts Γ).1 (hfacts Γ).2.1 (hfD Γ)
  have hsum : g = ∑ Γ, f Γ := hK.2.2.1 g hg.contDiff hg.hasCompactSupport (η / 8) hυ
  have hAg : insertionOp σ η g = ∑ Γ, insertionOp σ η (f Γ) := by
    have h := (hI σ E p C hc η hη hη1).2.1 Finset.univ (fun _ => (1 : ℂ)) f D
      (fun Γ _ => hadm Γ) (fun Γ _ => hfD Γ) (by
        rintro _ ⟨u, hu, v, hv, rfl⟩ _ ⟨u', hu', v', hv', rfl⟩
        exact euclidNormVec_add_sub_le hη1 hu hu' hv hv')
    simpa only [one_smul, ← hsum] using h
  let G : (Fin 4 → ℝ) → ℂ := fun a => g (b + a)
  have hGm : IsSmoothCompactIn (centralBox η) G := hg.translate
  let O : Set (Fin 4 → ℝ) := {a | |a TimeAxis.timeIdx| < η}
  have hO : IsOpen O := isOpen_lt (continuous_abs.comp (continuous_apply _)) continuous_const
  have hQO : centralBox η ⊆ O := fun a ha => lt_trans ha.1 (by linarith)
  have hGO : IsSmoothCompactIn O G :=
    ⟨hGm.contDiff, hGm.hasCompactSupport, hGm.tsupport_subset.trans hQO⟩
  let U : Finset (Fin 4) → (Fin 4 → ℝ) → ℂ := fun Γ a => ⟪χ, conjKernelInsertion σ E η Γ a χ'⟫_ℂ
  have hV' := hV σ E p C hc η hη hη1
  have hU : ∀ Γ, ContDiffOn ℝ ∞ (U Γ) O := fun Γ => hV'.1 Γ χ χ'
  have hΓ : ∀ Γ, ⟪χ, (T * insertionOp σ η (f Γ) * T) χ'⟫_ℂ =
      (-1) ^ Γ.card * ∫ a, G a * cubedPartial Γ (U Γ) a := by
    intro Γ
    rw [← integral_cubedPartial_mul hO hGO (hU Γ) Γ]
    set ψ := ContinuousLinearMap.adjoint T χ with hψ
    have e1 : ∀ B : OneLoopNotation.BddOp (StateSpace σ),
        ⟪χ, (T * B * T) χ'⟫_ℂ = ⟪ψ, B (T χ')⟫_ℂ := by
      intro B
      rw [hψ, ContinuousLinearMap.adjoint_inner_left]
      rfl
    have hk1 : scaledKernel η Γ ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) :=
      ⟨(hkf Γ).1, (hkf Γ).2.1, Set.subset_univ _⟩
    have hsm := (hS σ E p C hc η (scaledKernel η Γ) (φ Γ) hη hη1 hk1 (hφ Γ).contDiff.continuous
      (hφ Γ).hasCompactSupport (fun x hx y hy => by
        have := timeIdx_add_mem_of_shiftedBox hη ((hφ Γ).tsupport_subset hx) ((hkf Γ).2.2 hy)
        exact this)
      (fun x hx y hy x' hx' y' hy' =>
        euclidNormVec_add_sub_le hη1 ((hφ Γ).tsupport_subset hx) ((hφ Γ).tsupport_subset hx')
          ((hkf Γ).2.2 hy) ((hkf Γ).2.2 hy'))).2 ψ (T χ')
    rw [e1, hsm, ← integral_add_left_eq_self _ b]
    refine integral_congr_ae (.of_forall fun a => ?_)
    have hpart : cubedPartial Γ G a = φ Γ (b + a) := congrFun (cubedPartial_comp_add b Γ g) a
    simp only [hpart]
    by_cases ha : |a TimeAxis.timeIdx| ≤ η / 2
    · have hcj := (hCj σ E p C hc η Γ a hη hη1 ha).2
      rw [← e1]
      simp only [U]
      rw [← hcj]
    · have hz : φ Γ (b + a) = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hin => ha ?_
        have h1 : b + a ∈ shiftedBox η := (hφ Γ).tsupport_subset hin
        have h2 : a ∈ centralBox η := by simpa [shiftedBox, hb] using h1
        exact (h2.1.le).trans (by linarith)
      simp [hz]
  have hrhs : ∀ a, G a * ⟪χ, smoothedFieldOp σ E η a χ'⟫_ℂ =
      ∑ Γ, (-1) ^ Γ.card * (G a * cubedPartial Γ (U Γ) a) := by
    intro a
    by_cases ha : |a TimeAxis.timeIdx| ≤ η / 2
    · rw [(hV'.2.1 a ha).1 χ χ']
      simp only [smoothedPairing, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Γ _ => ?_
      ring
    · have hz : G a = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hin => ha ?_
        exact ((hGm.tsupport_subset hin).1.le).trans (by linarith)
      simp [hz]
  have hint : ∀ Γ, Integrable (fun a => (-1 : ℂ) ^ Γ.card * (G a * cubedPartial Γ (U Γ) a)) :=
    fun Γ => (integrable_mul_of_tsupport_subset hO hGO.contDiff.continuous hGO.hasCompactSupport
      (contDiffOn_cubedPartial hO (hU Γ) Γ).continuousOn hGO.tsupport_subset).const_mul _
  rw [show (∫ a, g (b + a) * ⟪χ, smoothedFieldOp σ E η a χ'⟫_ℂ) = _ from
    integral_congr_ae (.of_forall hrhs), integral_finsetSum _ fun Γ _ => hint Γ, hAg]
  have e2 : (T * (∑ Γ, insertionOp σ η (f Γ)) * T) χ' =
      ∑ Γ, (T * insertionOp σ η (f Γ) * T) χ' := by
    rw [Finset.mul_sum, Finset.sum_mul, sum_apply]
  rw [e2, inner_sum]
  refine Finset.sum_congr rfl fun Γ _ => ?_
  rw [hΓ, integral_const_mul]
theorem insertedState_shift_eq (hCl : InsertedStateProperties) (hc : Hypotheses σ E p C)
    {η : ℝ} (hη : 0 < η) {g : (Fin 4 → ℝ) → ℂ}
    (hg : SupportedBelow ((4 * η) • timeUnitVec) g) (F : PositiveSpan) :
    insertedState σ (translateFun (η • timeUnitVec) g) ((6 * η) • timeUnitVec) F =
      spectralTranslation E (imagTimeShift η)
        (insertedState σ g ((4 * η) • timeUnitVec) (shiftedSpan (η • timeUnitVec) F)) := by
  obtain ⟨-, -, h3, h4⟩ := hCl σ E p C hc
  have hnn : 0 ≤ (η • timeUnitVec : Fin 4 → ℝ) TimeAxis.timeIdx := by
    rw [smul_timeUnitVec_timeIdx]; exact hη.le
  have hb : SupportedBelow ((4 * η) • timeUnitVec + η • timeUnitVec) g := by
    refine ⟨hg.1, fun x hx => ⟨(hg.2 x hx).1, ?_⟩⟩
    have := (hg.2 x hx).2
    rw [smul_timeUnitVec_timeIdx] at this
    rw [Pi.add_apply, smul_timeUnitVec_timeIdx, smul_timeUnitVec_timeIdx]
    linarith
  rw [← h4 _ _ g F hnn hg, ← realWickPoint_smul_timeUnitVec, h3 _ _ g F hnn hb]
  congr 1
  module
theorem supportedBelow_of_isAdmissible {η : ℝ} (hη : 0 < η) {f : (Fin 4 → ℝ) → ℂ}
    (hf : IsAdmissible η f) : SupportedBelow ((4 * η) • timeUnitVec) f := by
  refine ⟨hf.mem, fun x hx => ?_⟩
  have := hf.tsupport_time x hx
  rw [smul_timeUnitVec_timeIdx]
  constructor <;> linarith [this.1, this.2]
theorem eq_zero_of_norm_le_mul_forall {X : ℂ} {M : ℝ} (h : ∀ δ : ℝ, 0 < δ → ‖X‖ ≤ M * δ) :
    X = 0 := by
  have h0 : ‖X‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hp : 0 < |M| + 1 := by positivity
    have h1 := h (ε / (|M| + 1)) (by positivity)
    have h2 : M * (ε / (|M| + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ hp]
      nlinarith [le_abs_self M, abs_nonneg M]
    linarith
  exact norm_le_zero_iff.1 h0
theorem centralDensityFormula_holds (hK : KernelFacts)
    (hI : InsertionOperators.InsertionOperatorBounds) (hCl : InsertedStateProperties)
    (hS : InsertionSmearing.Claim) (hCj : KernelInsertionConjugation)
    (hV : SmoothedKernelField.Regularity) : CentralDensityFormula := by
  intro σ E p C hc η h F χ hη hη1 hh hsupp
  set T := spectralTranslation E (imagTimeShift η) with hT
  set b : Fin 4 → ℝ := (2 * η) • timeUnitVec with hb
  set cF := stateOf σ F with hcF
  let F' : PositiveSpan := shiftedSpan (η • timeUnitVec) F
  let g : (Fin 4 → ℝ) → ℂ := fun x => h (x + η • timeUnitVec)
  have hshift : translateFun (η • timeUnitVec) g = h := by
    funext x
    simp [translateFun, g]
  have hg1 : ContDiff ℝ 1 g := hh.1.comp (contDiff_id.add contDiff_const)
  have hgc : HasCompactSupport g := hh.2.1.comp_homeomorph (Homeomorph.addRight _)
  have hgs : tsupport g ⊆ shiftedBox η := by
    intro x hx
    have e := tsupport_comp_eq_preimage h (Homeomorph.addRight (η • timeUnitVec))
    have h2 : x ∈ (Homeomorph.addRight (η • timeUnitVec)) ⁻¹' tsupport h := by
      rw [← e]
      exact hx
    have h3 := hsupp _ h2
    have e2 : (Homeomorph.addRight (η • timeUnitVec)) x - (3 * η) • timeUnitVec =
        x - (2 * η) • timeUnitVec := by
      simp only [Homeomorph.coe_addRight]
      module
    rw [e2] at h3
    exact h3
  obtain ⟨ρ, hρ, hρs⟩ := hgc.isCompact.exists_thickening_subset_open (isOpen_shiftedBox η) hgs
  have hr : 0 < ρ / 2 := by positivity
  set K : Set (Fin 4 → ℝ) := Metric.cthickening (ρ / 2) (tsupport g) with hKdef
  have hKc : IsCompact K := hgc.isCompact.cthickening
  have hKs : K ⊆ shiftedBox η :=
    (Metric.cthickening_subset_thickening' hρ (half_lt_self hρ) _).trans hρs
  have hgK : tsupport g ⊆ K := Metric.self_subset_cthickening _
  let Ka : Set (Fin 4 → ℝ) := (Homeomorph.addLeft b) ⁻¹' K
  have hKac : IsCompact Ka := (Homeomorph.addLeft b).isCompact_preimage.2 hKc
  have hKaQ : Ka ⊆ centralBox η := fun a ha => by
    have h1 : b + a ∈ shiftedBox η := hKs ha
    simpa [shiftedBox, hb] using h1
  let w : (Fin 4 → ℝ) → ℂ := fun a => ⟪χ, smoothedFieldOp σ E η a cF⟫_ℂ
  have hV' := hV σ E p C hc η hη hη1
  let O₂ : Set (Fin 4 → ℝ) := {a | |a TimeAxis.timeIdx| < η / 2}
  have hO₂ : IsOpen O₂ := isOpen_lt (continuous_abs.comp (continuous_apply _)) continuous_const
  have hwc : ContinuousOn w O₂ := (hV'.2.2 χ cF).mono fun a (ha : |a TimeAxis.timeIdx| < η / 2) =>
    show |a TimeAxis.timeIdx| ≤ η / 2 from ha.le
  have hKaO : Ka ⊆ O₂ := fun a ha => lt_trans (hKaQ ha).1 (by linarith)
  obtain ⟨B, hB⟩ := hKac.exists_bound_of_continuousOn (hwc.mono hKaO)
  have hcomp : ∀ {u : (Fin 4 → ℝ) → ℂ}, Continuous u → HasCompactSupport u → tsupport u ⊆ K →
      Integrable (fun a => u (b + a) * w a) := by
    intro u hu huc hus
    have e := tsupport_comp_eq_preimage u (Homeomorph.addLeft b)
    refine integrable_mul_of_tsupport_subset (G := fun a => u (b + a)) hO₂
      (hu.comp (continuous_const.add continuous_id)) (huc.comp_homeomorph (Homeomorph.addLeft b))
      hwc ?_
    intro a ha
    have h2 : a ∈ (Homeomorph.addLeft b) ⁻¹' tsupport u := by
      rw [← e]
      exact ha
    exact hKaO (hus h2)
  have hadmK : ∀ {f : (Fin 4 → ℝ) → ℂ}, ContDiff ℝ 1 f → HasCompactSupport f → tsupport f ⊆ K →
      IsAdmissible η f := fun h1 h2 h3 =>
    isAdmissible_of_tsupport_subset hη hη1 h1 h2 ((h3.trans hKs).trans (shiftedBox_subset_add hη))
  have hgadm : IsAdmissible η g := hadmK hg1 hgc hgK
  have hgb := supportedBelow_of_isAdmissible hη hgadm
  have hL : ⟪χ, insertedState σ h ((6 * η) • timeUnitVec) F⟫_ℂ =
      ⟪χ, T (insertedState σ g ((4 * η) • timeUnitVec) F')⟫_ℂ := by
    rw [← insertedState_shift_eq hCl hc hη hgb F, hshift]
  have hR : ∀ a, h ((3 * η) • timeUnitVec + a) = g (b + a) := by
    intro a
    simp only [g, hb]
    congr 1
    module
  have hTF : T cF = stateOf σ F' := by
    rw [hT, ← realWickPoint_smul_timeUnitVec]
    exact hc.translationMeasure.translate_stateOf F _ (by rw [smul_timeUnitVec_timeIdx]; exact hη.le)
  set M₁ : ℝ := ‖χ‖ * ‖T‖ * (C * η ^ (-p) * 3 * ‖stateOf σ F'‖) with hM₁
  set M₂ : ℝ := B * volume.real Ka with hM₂
  have hCn : 0 ≤ C * η ^ (-p) := mul_nonneg (by linarith [hc.one_le_const])
    (Real.rpow_nonneg hη.le _)
  have key : ∀ δ : ℝ, 0 < δ →
      ‖⟪χ, T (insertedState σ g ((4 * η) • timeUnitVec) F')⟫_ℂ -
        ∫ a, g (b + a) * w a‖ ≤ (M₁ + M₂) * δ := by
    intro δ hδ
    obtain ⟨g', hs', hc', ht', h0', h1'⟩ := exists_smooth_approx hg1 hgc hr hδ
    have hgt : IsSmoothCompactIn (shiftedBox η) g' := ⟨hs', hc', ht'.trans hKs⟩
    have hg'1 : ContDiff ℝ 1 g' := hs'.of_le (by simp)
    have hg'adm : IsAdmissible η g' := hadmK hg'1 hc' ht'
    have hg'b := supportedBelow_of_isAdmissible hη hg'adm
    have hm := central_density_of_smooth hK hI hS hCj hV hc hη hη1 hgt χ cF
    have hins := ((hI σ E p C hc η hη hη1).1 g' hg'adm).1 F'
    have hm' : ⟪χ, T (insertedState σ g' ((4 * η) • timeUnitVec) F')⟫_ℂ =
        ∫ a, g' (b + a) * w a := by
      rw [← hins, ← hTF]
      exact hm
    let d : (Fin 4 → ℝ) → ℂ := g - g'
    have hd1 : ContDiff ℝ 1 d := hg1.sub hg'1
    have hdc : HasCompactSupport d := hgc.sub hc'
    have hdK : tsupport d ⊆ K := by
      refine closure_minimal ?_ hKc.isClosed
      intro x hx
      by_contra hxK
      have e1 : g x = 0 := image_eq_zero_of_notMem_tsupport fun hin => hxK (hgK hin)
      have e2 : g' x = 0 := image_eq_zero_of_notMem_tsupport fun hin => hxK (ht' hin)
      exact hx (by simp [d, e1, e2])
    have hdadm : IsAdmissible η d := hadmK hd1 hdc hdK
    have hdb := supportedBelow_of_isAdmissible hη hdadm
    obtain ⟨hmem, hlin, -, -⟩ := hCl σ E p C hc
    have hdiff : insertedState σ d ((4 * η) • timeUnitVec) F' =
        insertedState σ g ((4 * η) • timeUnitVec) F' -
          insertedState σ g' ((4 * η) • timeUnitVec) F' := by
      have := hlin (Finset.univ : Finset (Fin 2)) ![1, -1] ![g, g'] ((4 * η) • timeUnitVec) F' (by
        intro i _
        fin_cases i
        · exact hgb
        · exact hg'b)
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul,
        ← sub_eq_add_neg] at this
      exact this
    have hdnorm : WightmanReconstruction.supC1Norm d ≤ 3 * δ := by
      refine supC1Norm_le hδ.le (fun x => ?_) (fun μ x => ?_)
      · have e : d x = g x - g' x := rfl
        rw [e, norm_sub_rev]
        exact h0' x
      · have hdg : DifferentiableAt ℝ g x := (hg1.differentiable (by simp)) x
        have hdg' : DifferentiableAt ℝ g' x := (hg'1.differentiable (by simp)) x
        have e : partialDerivR4 μ d x = partialDerivR4 μ g x - partialDerivR4 μ g' x := by
          rw [partialDerivR4_eq_fderiv (hdg.sub hdg'), partialDerivR4_eq_fderiv hdg,
            partialDerivR4_eq_fderiv hdg', fderiv_sub hdg hdg']
          rfl
        rw [e, norm_sub_rev]
        exact h1' μ x
    have hbound : ‖insertedState σ d ((4 * η) • timeUnitVec) F'‖ ≤
        C * η ^ (-p) * 3 * ‖stateOf σ F'‖ * δ := by
      have hmd := hmem _ d F' hdb
      have hb' := hc.insertion_bound η hη hη1 d hdadm.mem hdadm.tsupport_time hdadm.diam_le F' hmd
      have e : insertedState σ d ((4 * η) • timeUnitVec) F' = stateOf σ ⟨_, hmd⟩ := by
        simp only [insertedState]
        rw [dif_pos hmd]
      rw [e]
      calc _ ≤ _ := hb'
        _ ≤ C * η ^ (-p) * (3 * δ) * ‖stateOf σ F'‖ := by gcongr
        _ = _ := by ring
    have hfirst : ‖⟪χ, T (insertedState σ g ((4 * η) • timeUnitVec) F')⟫_ℂ -
        ⟪χ, T (insertedState σ g' ((4 * η) • timeUnitVec) F')⟫_ℂ‖ ≤ M₁ * δ := by
      rw [← inner_sub_right, ← map_sub, ← hdiff]
      calc _ ≤ ‖χ‖ * ‖T (insertedState σ d ((4 * η) • timeUnitVec) F')‖ :=
            norm_inner_le_norm _ _
        _ ≤ ‖χ‖ * (‖T‖ * (C * η ^ (-p) * 3 * ‖stateOf σ F'‖ * δ)) := by
          gcongr
          exact (T.le_opNorm _).trans (by gcongr)
        _ = _ := by rw [hM₁]; ring
    have hsecond : ‖(∫ a, g' (b + a) * w a) - ∫ a, g (b + a) * w a‖ ≤ M₂ * δ := by
      rw [← integral_sub (hcomp hs'.continuous hc' ht') (hcomp hg1.continuous hgc hgK)]
      have e : ∫ a, (g' (b + a) * w a - g (b + a) * w a) =
          ∫ a in Ka, (g' (b + a) * w a - g (b + a) * w a) := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => ?_).symm
        have hn : b + a ∉ K := ha
        have e1 : g (b + a) = 0 := image_eq_zero_of_notMem_tsupport fun hin => hn (hgK hin)
        have e2 : g' (b + a) = 0 := image_eq_zero_of_notMem_tsupport fun hin => hn (ht' hin)
        simp [e1, e2]
      rw [e]
      have hle : ∀ a ∈ Ka, ‖g' (b + a) * w a - g (b + a) * w a‖ ≤ δ * B := by
        intro a ha
        rw [← sub_mul, norm_mul]
        exact mul_le_mul (h0' _) (hB a ha) (norm_nonneg _) hδ.le
      calc _ ≤ δ * B * volume.real Ka :=
            norm_setIntegral_le_of_norm_le_const hKac.measure_lt_top hle
        _ = _ := by rw [hM₂]; ring
    calc _ = ‖(⟪χ, T (insertedState σ g ((4 * η) • timeUnitVec) F')⟫_ℂ -
            ⟪χ, T (insertedState σ g' ((4 * η) • timeUnitVec) F')⟫_ℂ) +
          ((∫ a, g' (b + a) * w a) - ∫ a, g (b + a) * w a)‖ := by rw [hm']; congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ M₁ * δ + M₂ * δ := add_le_add hfirst hsecond
      _ = _ := by ring
  have hX := eq_zero_of_norm_le_mul_forall key
  rw [hL]
  simp_rw [hR]
  exact sub_eq_zero.1 hX
end Main
end YangMills.Construction.CentralDensity
