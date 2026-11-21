import YangMills.Construction.Continuum.ParametrixIdentityAtTheOrigin
import YangMills.Construction.Continuum.PartialIntegrationOfTheCubeOfTheLaplacian
import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.EuclideanAnalysis.ParametrixOfTheCubedLaplacian
import YangMills.Construction.EuclideanAnalysis.RadialCutOffAndContinuousDensities
import YangMills.Construction.EuclideanAnalysis.RadialCutOffHasItsProperties
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis.CubedLaplacian.ParametrixConstruction
open YangMills.Construction.Parametrix YangMills.Construction.TorusMetric
section Affine
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem partialDeriv_comp_affine (f : RealSpace 4 → F) (a : RealSpace 4) (c : ℝ) (μ : Fin 4)
    (y : RealSpace 4) :
    partialDeriv μ (fun z => f (a + c • z)) y = c • partialDeriv μ f (a + c • y) := by
  unfold partialDeriv
  rw [← lineDeriv_smul]
  unfold lineDeriv
  congr 1
  funext t
  show f (a + c • (y + t • stdBasisVector μ)) = _
  rw [smul_add, smul_comm c t, add_assoc]
theorem partialDeriv_const_smul (k : ℝ) (f : RealSpace 4 → F) (μ : Fin 4) (y : RealSpace 4) :
    partialDeriv μ (fun z => k • f z) y = k • partialDeriv μ f y := by
  unfold partialDeriv lineDeriv
  exact deriv_const_smul_field k (fun t : ℝ => f (y + t • stdBasisVector μ))
theorem laplacian_comp_affine (f : RealSpace 4 → F) (a : RealSpace 4) (c : ℝ) (y : RealSpace 4) :
    laplacian (fun z => f (a + c • z)) y = (c ^ 2) • laplacian f (a + c • y) := by
  unfold laplacian
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h : partialDeriv μ (fun z => f (a + c • z)) =
      fun z => c • partialDeriv μ f (a + c • z) := funext (partialDeriv_comp_affine f a c μ)
  rw [h, partialDeriv_const_smul, partialDeriv_comp_affine, smul_smul, sq]
end Affine
def affineComp (a : RealSpace 4) (c : ℝ) (hc : c ≠ 0) (φ : SmoothTestFunction) :
    SmoothTestFunction where
  toFun y := φ (a + c • y)
  contDiff' := φ.contDiff.comp (contDiff_const.add (contDiff_const_smul c))
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph
    ((Homeomorph.smulOfNeZero c hc).trans (Homeomorph.addLeft a))
  tsupport_subset' := fun _ _ => trivial
@[simp] theorem affineComp_apply (a : RealSpace 4) (c : ℝ) (hc : c ≠ 0)
    (φ : SmoothTestFunction) (y : RealSpace 4) : affineComp a c hc φ y = φ (a + c • y) := rfl
theorem testLaplacian_affineComp (a : RealSpace 4) (c : ℝ) (hc : c ≠ 0) (φ : SmoothTestFunction) :
    testLaplacian (affineComp a c hc φ) =
      ((c ^ 2 : ℝ) : ℂ) • affineComp a c hc (testLaplacian φ) := by
  refine TestFunction.ext fun y => ?_
  have h : laplacian (affineComp a c hc φ) y = (c ^ 2) • laplacian φ (a + c • y) :=
    laplacian_comp_affine (fun z => φ z) a c y
  rw [testLaplacian_apply, h, ← testLaplacian_apply]
  simp [Complex.real_smul]
theorem testLaplacianCubed_affineComp (a : RealSpace 4) (c : ℝ) (hc : c ≠ 0)
    (φ : SmoothTestFunction) (y : RealSpace 4) :
    testLaplacianCubed (affineComp a c hc φ) y =
      ((c ^ 6 : ℝ) : ℂ) * testLaplacianCubed φ (a + c • y) := by
  unfold testLaplacianCubed
  rw [testLaplacian_affineComp, map_smul, testLaplacian_affineComp, map_smul, map_smul,
    testLaplacian_affineComp]
  show ((c ^ 2 : ℝ) : ℂ) * (((c ^ 2 : ℝ) : ℂ) * (((c ^ 2 : ℝ) : ℂ) * _)) = _
  simp only [affineComp_apply]
  push_cast
  ring
abbrev ofCoords (y : Fin 4 → ℝ) : RealSpace 4 := WithLp.toLp 2 y
theorem partialDerivR4_comp_ofCoords {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : RealSpace 4 → F) (μ : Fin 4) (y : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 μ (fun z => f (ofCoords z)) y = partialDeriv μ f (ofCoords y) := by
  unfold TestFunctions.partialDerivR4 partialDeriv lineDeriv stdBasisVector
  congr 1
theorem laplacianR4_comp_ofCoords {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : RealSpace 4 → F) :
    TestFunctions.laplacianR4 (fun z => f (ofCoords z)) = fun y => laplacian f (ofCoords y) := by
  funext y
  unfold TestFunctions.laplacianR4 laplacian
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h : TestFunctions.partialDerivR4 μ (fun z => f (ofCoords z)) =
      fun z => partialDeriv μ f (ofCoords z) := funext (partialDerivR4_comp_ofCoords f μ)
  rw [h, partialDerivR4_comp_ofCoords]
theorem coe_testLaplacian (φ : SmoothTestFunction) :
    ((testLaplacian φ : SmoothTestFunction) : RealSpace 4 → ℂ) = laplacian φ :=
  funext (testLaplacian_apply φ)
theorem laplacianR4_iterate_three_comp_ofCoords (φ : SmoothTestFunction) :
    TestFunctions.laplacianR4^[3] (fun z => φ (ofCoords z)) =
      fun y => testLaplacianCubed φ (ofCoords y) := by
  show TestFunctions.laplacianR4 (TestFunctions.laplacianR4
    (TestFunctions.laplacianR4 (fun z => φ (ofCoords z)))) = _
  rw [laplacianR4_comp_ofCoords, laplacianR4_comp_ofCoords, laplacianR4_comp_ofCoords]
  funext y
  unfold testLaplacianCubed
  rw [coe_testLaplacian, ← coe_testLaplacian φ,
    ← coe_testLaplacian (testLaplacian φ)]
theorem euclidNormVec_ofLp (x : RealSpace 4) : euclidNormVec x.ofLp = ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclidNormVec
  simp
theorem integral_comp_ofLp (G : (Fin 4 → ℝ) → ℂ) : ∫ x : RealSpace 4, G x.ofLp = ∫ y, G y :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 4)).integral_comp' G
theorem contDiff_ofCoords : ContDiff ℝ ∞ ofCoords :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff
theorem contDiff_ofLp : ContDiff ℝ ∞ (fun x : RealSpace 4 => x.ofLp) :=
  (EuclideanSpace.equiv (Fin 4) ℝ).contDiff
theorem fundSol_eq_logKernel (x : RealSpace 4) :
    fundSolLaplacianCubed x = logKernel 0 x.ofLp := by
  unfold fundSolLaplacianCubed logKernel
  rw [euclidNormVec_ofLp]
  by_cases hx : x = 0
  · simp [hx]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hp : 0 < ‖x‖ ^ 2 + 0 := by positivity
    rw [if_neg hx, if_pos hp, add_zero, Real.log_pow]
    have hpi := Real.pi_ne_zero
    push_cast
    field_simp
    ring
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem contDiff_laplacianR4 {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (TestFunctions.laplacianR4 f) := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.contDiff_laplacianR4 <;> assumption
theorem laplacianR4_eventuallyEq {f g : (Fin 4 → ℝ) → ℝ} {y : Fin 4 → ℝ} (h : f =ᶠ[𝓝 y] g) :
    TestFunctions.laplacianR4 f =ᶠ[𝓝 y] TestFunctions.laplacianR4 g := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.laplacianR4_eventuallyEq <;> assumption
theorem contDiff_radialBump : ContDiff ℝ ∞ (radialBump : RealSpace 4 → ℝ) := radialBump.contDiff
theorem exists_radius_tsupport_radialBump :
    ∃ ϱ : ℝ, 0 < ϱ ∧ ϱ < 1 ∧ ∀ x : RealSpace 4, ϱ < ‖x‖ → x ∉ tsupport radialBump := by
  have hK : IsCompact (tsupport (radialBump : RealSpace 4 → ℝ)) := radialBump.hasCompactSupport
  have hsub : tsupport (radialBump : RealSpace 4 → ℝ) ⊆ Metric.ball 0 1 :=
    radialBump.tsupport_subset
  by_cases hne : (tsupport (radialBump : RealSpace 4 → ℝ)).Nonempty
  · obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    have h1 : ‖x₀‖ < 1 := by simpa using hsub hx₀
    refine ⟨max ‖x₀‖ (1 / 2), by positivity, max_lt h1 (by norm_num), fun x hx hmem => ?_⟩
    have h2 : ‖x‖ ≤ ‖x₀‖ := hmax hmem
    exact absurd (lt_of_le_of_lt (le_max_left _ _) hx) (not_lt.2 h2)
  · exact ⟨1 / 2, by norm_num, by norm_num, fun x _ hmem => hne ⟨x, hmem⟩⟩
def bumpComplLogKernel (y : Fin 4 → ℝ) : ℝ := (1 - radialBump (ofCoords y)) * logKernel 0 y
theorem euclidNormVec_sq_pos {y : Fin 4 → ℝ} (hy : y ≠ 0) : 0 < euclidNormVec y ^ 2 + 0 := by
  have h : euclidNormVec y = ‖ofCoords y‖ := euclidNormVec_ofLp (ofCoords y)
  have hn : ofCoords y ≠ 0 := fun h0 => hy (by simpa using congrArg WithLp.ofLp h0)
  rw [h]
  have := norm_pos_iff.2 hn
  positivity
theorem contDiffAt_logKernel (hTL : TripleLaplacianLogKernel) {y : Fin 4 → ℝ}
    (hy : y ≠ 0) : ContDiffAt ℝ ∞ (logKernel 0) y := by
  have hopen : IsOpen {x : Fin 4 → ℝ | 0 < euclidNormVec x ^ 2 + 0} :=
    isOpen_lt continuous_const ((continuous_euclidNormVec.pow 2).add continuous_const)
  exact (hTL.1 0 le_rfl).1.contDiffAt (hopen.mem_nhds (euclidNormVec_sq_pos hy))
theorem contDiff_bumpComplLogKernel (hRC : RadialBumpHasProperties)
    (hTL : TripleLaplacianLogKernel) : ContDiff ℝ ∞ bumpComplLogKernel := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    have hc : Tendsto ofCoords (𝓝 0) (𝓝 (0 : RealSpace 4)) := by
      have := contDiff_ofCoords.continuous.tendsto (0 : Fin 4 → ℝ)
      simpa using this
    have h1 : ∀ᶠ z in 𝓝 (0 : Fin 4 → ℝ), radialBump (ofCoords z) = 1 := hc.eventually hRC.2.2
    have h2 : bumpComplLogKernel =ᶠ[𝓝 0] fun _ => 0 :=
      h1.mono fun z hz => by simp [bumpComplLogKernel, hz]
    exact contDiffAt_const.congr_of_eventuallyEq h2
  · have h1 : ContDiffAt ℝ ∞ (fun z : Fin 4 → ℝ => 1 - radialBump (ofCoords z)) y :=
      (contDiff_const.sub (contDiff_radialBump.comp contDiff_ofCoords)).contDiffAt
    exact h1.mul (contDiffAt_logKernel hTL hy)
def remainderFun (x : RealSpace 4) : ℝ := TestFunctions.laplacianR4^[3] bumpComplLogKernel x.ofLp
theorem contDiff_remainderFun (hRC : RadialBumpHasProperties)
    (hTL : TripleLaplacianLogKernel) : ContDiff ℝ ∞ remainderFun := by
  have h := contDiff_bumpComplLogKernel hRC hTL
  exact (contDiff_laplacianR4 (contDiff_laplacianR4 (contDiff_laplacianR4 h))).comp
    contDiff_ofLp
theorem remainderFun_eq_zero (hTL : TripleLaplacianLogKernel) {ϱ : ℝ}
    (hϱ : 0 < ϱ) (hsup : ∀ x : RealSpace 4, ϱ < ‖x‖ → x ∉ tsupport radialBump) {x : RealSpace 4}
    (hx : ϱ < ‖x‖) : remainderFun x = 0 := by
  have hopen : IsOpen {z : Fin 4 → ℝ | ϱ < euclidNormVec z} :=
    isOpen_lt continuous_const continuous_euclidNormVec
  have hmem : x.ofLp ∈ {z : Fin 4 → ℝ | ϱ < euclidNormVec z} := by
    simpa [euclidNormVec_ofLp] using hx
  have heq : bumpComplLogKernel =ᶠ[𝓝 x.ofLp] logKernel 0 := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz' : ϱ < ‖ofCoords z‖ := by
      have : euclidNormVec z = ‖ofCoords z‖ := euclidNormVec_ofLp (ofCoords z)
      rwa [this] at hz
    simp [bumpComplLogKernel, image_eq_zero_of_notMem_tsupport (hsup _ hz')]
  have hne : x.ofLp ≠ 0 := by
    intro h0
    have : x = 0 := by simpa using congrArg (WithLp.toLp 2) h0
    rw [this, norm_zero] at hx
    linarith
  have h3 :=
    (laplacianR4_eventuallyEq (laplacianR4_eventuallyEq (laplacianR4_eventuallyEq heq))).self_of_nhds
  unfold remainderFun
  exact h3.trans (hTL.2 _ hne)
theorem parametrixOne_ofCoords (y : Fin 4 → ℝ) :
    parametrixOne (ofCoords y) = logKernel 0 y - bumpComplLogKernel y := by
  simp only [parametrixOne, fundSol_eq_logKernel, bumpComplLogKernel]
  ring
theorem logKernel_eq_inner_add_outer (y : Fin 4 → ℝ) :
    logKernel 0 y = innerKernelUnit y + outerLogKernel y := by
  simp only [innerKernelUnit, outerLogKernel]
  ring
theorem contDiff_fundSol (hUK : UnitKernelRegularity) :
    ContDiff ℝ 1 fundSolLaplacianCubed := by
  have h : fundSolLaplacianCubed = fun x : RealSpace 4 => logKernel 0 x.ofLp :=
    funext fundSol_eq_logKernel
  rw [h]
  exact hUK.1.comp (contDiff_ofLp.of_le (by simp))
theorem contDiff_parametrixOne (hUK : UnitKernelRegularity) :
    ContDiff ℝ 1 parametrixOne :=
  (contDiff_radialBump.of_le (by simp)).mul (contDiff_fundSol hUK)
section Identities
variable (hO : OriginIdentity)
  (hPI : LaplacianCubeSelfAdjoint)
  (hUK : UnitKernelRegularity)
include hO hPI hUK
def coordHomeomorph : (Fin 4 → ℝ) ≃ₜ RealSpace 4 := (EuclideanSpace.equiv (Fin 4) ℝ).symm.toHomeomorph
theorem integral_logKernel_sub_mul (φ : SmoothTestFunction) (u : (Fin 4 → ℝ) → ℝ)
    (hu : ContDiff ℝ ∞ u) :
    ∫ y : Fin 4 → ℝ, (((logKernel 0 y - u y : ℝ)) : ℂ) * testLaplacianCubed φ (ofCoords y) =
      φ 0 - ∫ y : Fin 4 → ℝ, ((TestFunctions.laplacianR4^[3] u y : ℝ) : ℂ) * φ (ofCoords y) := by
  set φ' : (Fin 4 → ℝ) → ℂ := fun z => φ (ofCoords z) with hφ'
  have hs : ContDiff ℝ ∞ φ' := φ.contDiff.comp contDiff_ofCoords
  have hc : HasCompactSupport φ' := φ.hasCompactSupport.comp_homeomorph coordHomeomorph
  have hcube : TestFunctions.laplacianR4^[3] φ' =
      fun y => testLaplacianCubed φ (ofCoords y) := laplacianR4_iterate_three_comp_ofCoords φ
  set G : (Fin 4 → ℝ) → ℂ := fun y => testLaplacianCubed φ (ofCoords y) with hG
  have hGc : Continuous G :=
    (testLaplacianCubed φ).continuous.comp contDiff_ofCoords.continuous
  have hGs : HasCompactSupport G :=
    (testLaplacianCubed φ).hasCompactSupport.comp_homeomorph coordHomeomorph
  have h1 := hO φ' hs hc
  have h2 := hPI φ' outerLogKernel hs hc hUK.2.1
  have h3 := hPI φ' u hs hc hu
  rw [hcube] at h1 h2 h3
  have hint : ∀ v : (Fin 4 → ℝ) → ℝ, Continuous v → Integrable fun x => (v x : ℂ) * G x :=
    fun v hv => ((Complex.continuous_ofReal.comp hv).mul hGc).integrable_of_hasCompactSupport
      hGs.mul_left
  have hκ : Continuous innerKernelUnit := hUK.2.2.1.continuous
  have hout : Continuous outerLogKernel := hUK.2.1.continuous
  have hφ0 : φ' 0 = φ 0 := by simp [hφ']
  have e2 : (∫ x, (outerLogKernel x : ℂ) * G x) = ∫ x, (outerKernelUnit x : ℂ) * φ' x := by
    rw [show (fun x => (outerLogKernel x : ℂ) * G x) = fun x => G x * (outerLogKernel x : ℂ) from
      funext fun x => mul_comm _ _, h2]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have e3 : (∫ x, (u x : ℂ) * G x) =
      ∫ x, ((TestFunctions.laplacianR4^[3] u x : ℝ) : ℂ) * φ' x := by
    rw [show (fun x => (u x : ℂ) * G x) = fun x => G x * (u x : ℂ) from
      funext fun x => mul_comm _ _, h3]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  calc ∫ y, (((logKernel 0 y - u y : ℝ)) : ℂ) * G y
      = ∫ y, ((innerKernelUnit y : ℂ) * G y + (outerLogKernel y : ℂ) * G y - (u y : ℂ) * G y) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [logKernel_eq_inner_add_outer]
        push_cast
        ring
    _ = (∫ y, (innerKernelUnit y : ℂ) * G y) + (∫ y, (outerLogKernel y : ℂ) * G y) -
          ∫ y, (u y : ℂ) * G y := by
        have hA : Integrable fun y =>
            (innerKernelUnit y : ℂ) * G y + (outerLogKernel y : ℂ) * G y :=
          (hint _ hκ).add (hint _ hout)
        rw [integral_sub hA (hint _ hu.continuous), integral_add (hint _ hκ) (hint _ hout)]
    _ = φ 0 - ∫ y, ((TestFunctions.laplacianR4^[3] u y : ℝ) : ℂ) * φ (ofCoords y) := by
        rw [h1, e2, e3, hφ0]
        ring
theorem integral_fundSol_mul (φ : SmoothTestFunction) :
    ∫ x, (fundSolLaplacianCubed x : ℂ) * testLaplacianCubed φ x = φ 0 := by
  have h := integral_logKernel_sub_mul hO hPI hUK φ (fun _ => 0) contDiff_const
  have hz : TestFunctions.laplacianR4^[3] (fun _ : Fin 4 → ℝ => (0 : ℝ)) = fun _ => 0 := by
    have h1 : TestFunctions.laplacianR4 (fun _ : Fin 4 → ℝ => (0 : ℝ)) = fun _ => 0 := by
      funext y
      simp [TestFunctions.laplacianR4, TestFunctions.partialDerivR4]
    show TestFunctions.laplacianR4 (TestFunctions.laplacianR4
      (TestFunctions.laplacianR4 _)) = _
    rw [h1, h1, h1]
  rw [hz] at h
  simp only [sub_zero, Complex.ofReal_zero, zero_mul, integral_zero] at h
  rw [← h, ← integral_comp_ofLp]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [fundSol_eq_logKernel]
theorem integral_parametrixOne_mul (hRC : RadialBumpHasProperties)
    (hTL : TripleLaplacianLogKernel) (φ : SmoothTestFunction) :
    ∫ x, (parametrixOne x : ℂ) * testLaplacianCubed φ x =
      φ 0 - ∫ x, (remainderFun x : ℂ) * φ x := by
  have h := integral_logKernel_sub_mul hO hPI hUK φ bumpComplLogKernel
    (contDiff_bumpComplLogKernel hRC hTL)
  have l : ∫ x, (parametrixOne x : ℂ) * testLaplacianCubed φ x =
      ∫ y : Fin 4 → ℝ, (((logKernel 0 y - bumpComplLogKernel y : ℝ)) : ℂ) *
        testLaplacianCubed φ (ofCoords y) := by
    rw [← integral_comp_ofLp]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have := parametrixOne_ofCoords x.ofLp
    simp only [ofCoords, WithLp.toLp_ofLp] at this
    simp [this]
  have r : ∫ x, (remainderFun x : ℂ) * φ x =
      ∫ y : Fin 4 → ℝ, ((TestFunctions.laplacianR4^[3] bumpComplLogKernel y : ℝ) : ℂ) *
        φ (ofCoords y) := by
    rw [← integral_comp_ofLp]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [remainderFun]
  rw [l, r, h]
end Identities
theorem parametrixRemainderOne_apply (hUK : UnitKernelRegularity)
    (φ : SmoothTestFunction) :
    parametrixRemainderOne φ =
      φ 0 - ∫ x, (parametrixOne x : ℂ) * testLaplacianCubed φ x := by
  have hl : LocallyIntegrable (fun x => (parametrixOne x : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (contDiff_parametrixOne hUK).continuous).locallyIntegrable
  show EuclideanAnalysis.dirac φ - EuclideanAnalysis.ofFunction (fun x => (parametrixOne x : ℂ))
    (testLaplacian (testLaplacian (testLaplacian φ))) = _
  rw [EuclideanAnalysis.ofFunction_apply hl]
  rfl
theorem isContinuousDensityOf_unique
    (hCV : BumpAndDensities.ContinuousEqZeroOfIntegralMul)
    {u : Distribution} {f₁ f₂ : RealSpace 4 → ℂ} (h₁ : IsContinuousDensityOf u f₁)
    (h₂ : IsContinuousDensityOf u f₂) : f₁ = f₂ := by
  have hint : ∀ (f : RealSpace 4 → ℂ) (φ : SmoothTestFunction), Continuous f →
      Integrable fun x => f x * φ x := fun f φ hf =>
    (hf.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  funext x
  refine sub_eq_zero.1 (hCV (fun y => f₁ y - f₂ y) (h₁.1.sub h₂.1) (fun φ => ?_) x)
  simp only [sub_mul]
  rw [integral_sub (hint _ φ h₁.1) (hint _ φ h₂.1), ← h₁.2 φ, ← h₂.2 φ, sub_self]
theorem integral_comp_smul_pos {r : ℝ} (hr : 0 < r) (F : RealSpace 4 → ℂ) :
    ∫ y, F (r • y) = ((r ^ 4)⁻¹ : ℝ) • ∫ x, F x := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure (RealSpace 4)) F r (hR := hr.le)
  simpa using h
theorem lt_norm_inv_smul {r ϱ : ℝ} (hr : 0 < r) {x : RealSpace 4} (hx : ϱ * r < ‖x‖) :
    ϱ < ‖r⁻¹ • x‖ := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), inv_mul_eq_div]
  exact (lt_div_iff₀ hr).2 hx
theorem support_small_of_eq_zero {E : Type*} [TopologicalSpace E] [Zero E] {f : RealSpace 4 → E}
    {ϱ r : ℝ} (hϱ : ϱ < 1) (hr : 0 < r) (h : ∀ x, ϱ * r < ‖x‖ → f x = 0) :
    HasCompactSupport f ∧ tsupport f ⊆ Metric.ball 0 r := by
  have hsub : Function.support f ⊆ Metric.closedBall 0 (ϱ * r) := fun x hx => by
    by_contra hn
    exact hx (h x (by simpa using hn))
  have hts : tsupport f ⊆ Metric.closedBall 0 (ϱ * r) :=
    closure_minimal hsub Metric.isClosed_closedBall
  refine ⟨HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 _) hsub,
    hts.trans (Metric.closedBall_subset_ball ?_)⟩
  nlinarith
theorem uniformNorm_of_norm_eq {E : Type*} [Norm E] {k r : ℝ} (hk : 0 ≤ k) (hr : 0 < r)
    (f g : RealSpace 4 → E) (h : ∀ x, ‖g x‖ = k * ‖f (r⁻¹ • x)‖) :
    TestFunctions.uniformNorm g = k * TestFunctions.uniformNorm f := by
  unfold TestFunctions.uniformNorm
  simp only [h]
  rw [Real.mul_iSup_of_nonneg hk]
  exact (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')).toEquiv.iSup_comp
    (g := fun y => k * ‖f y‖)
theorem gradNorm_of_eq_smul_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k c : ℝ)
    (f g : RealSpace 4 → E) (hg : g = fun z => k • f (c • z)) (x : RealSpace 4) :
    gradNorm g x = |k * c| * gradNorm f (c • x) := by
  have hp : ∀ μ : Fin 4, partialDeriv μ g x = (k * c) • partialDeriv μ f (c • x) := by
    intro μ
    have h1 := partialDeriv_comp_affine f 0 c μ x
    simp only [zero_add] at h1
    rw [hg, partialDeriv_const_smul k (fun z => f (c • z)), h1, smul_smul]
  unfold gradNorm
  have hs : ∑ μ, ‖partialDeriv μ g x‖ ^ 2 =
      |k * c| ^ 2 * ∑ μ, ‖partialDeriv μ f (c • x)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hp, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
theorem gradUniformNorm_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k r : ℝ}
    (hr : 0 < r) (f g : RealSpace 4 → E) (hg : g = fun z => k • f (r⁻¹ • z)) :
    gradUniformNorm g = |k * r⁻¹| * gradUniformNorm f := by
  unfold gradUniformNorm
  refine uniformNorm_of_norm_eq (abs_nonneg _) hr _ _ fun x => ?_
  rw [gradNorm_of_eq_smul_comp k r⁻¹ f g hg x, norm_mul, Real.norm_eq_abs, abs_abs]
theorem isBoundedFun_of_compact {E : Type*} [NormedAddCommGroup E] {f : RealSpace 4 → E}
    (hf : Continuous f) (hc : HasCompactSupport f) : TestFunctions.IsBoundedFun f :=
  hf.bounded_above_of_compact_support hc
theorem isBoundedFun_gradNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : RealSpace 4 → E} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    TestFunctions.IsBoundedFun (gradNorm f) := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hp : ∀ μ : Fin 4, partialDeriv μ f = fun x => fderiv ℝ f x (stdBasisVector μ) :=
    fun μ => funext fun x => (hd x).lineDeriv_eq_fderiv
  have hcont : Continuous (gradNorm f) := by
    unfold gradNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun μ _ => ?_)
    rw [hp]
    exact (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).norm).pow 2
  refine isBoundedFun_of_compact hcont (HasCompactSupport.of_support_subset_isCompact hc ?_)
  intro x hx
  by_contra hn
  refine hx ?_
  have hz : fderiv ℝ f x = 0 := fderiv_of_notMem_tsupport ℝ hn
  simp [gradNorm, hp, hz]
theorem remainderDensity_eq_smul (r : ℝ) :
    remainderDensity r = fun x => ((r ^ 4)⁻¹ : ℝ) • remainderDensityOne (r⁻¹ • x) := by
  funext x
  unfold remainderDensity
  rw [Complex.real_smul]
  push_cast
  rfl
section Main
variable (hCut : BumpAndDensities.Combined)
  (hRC : RadialBumpHasProperties)
  (hO : OriginIdentity)
  (hPI : LaplacianCubeSelfAdjoint)
  (hTL : TripleLaplacianLogKernel)
  (hUK : UnitKernelRegularity)
include hRC hO hPI hTL hUK
theorem isContinuousDensityOf_remainderFun :
    IsContinuousDensityOf parametrixRemainderOne (fun x => (remainderFun x : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp (contDiff_remainderFun hRC hTL).continuous, fun φ => ?_⟩
  rw [parametrixRemainderOne_apply hUK, integral_parametrixOne_mul hO hPI hUK hRC hTL]
  ring
include hCut
theorem remainderDensityOne_eq :
    remainderDensityOne = fun x => (remainderFun x : ℂ) :=
  have h := isContinuousDensityOf_remainderFun hRC hO hPI hTL hUK
  isContinuousDensityOf_unique hCut.2.1 (Classical.epsilon_spec ⟨_, h⟩) h
theorem remainderDensity_eq_remainderFun (r : ℝ) :
    remainderDensity r = fun x => ((r ^ 4)⁻¹ : ℝ) • (remainderFun (r⁻¹ • x) : ℂ) := by
  rw [remainderDensity_eq_smul, remainderDensityOne_eq hCut hRC hO hPI hTL hUK]
theorem integral_remainderDensity_mul {r : ℝ} (hr : 0 < r) (φ : SmoothTestFunction) :
    ∫ x, remainderDensity r x * φ x = ∫ y, (remainderFun y : ℂ) * φ (r • y) := by
  have h := integral_comp_smul_pos hr (fun x => remainderDensity r x * φ x)
  have hpt : ∀ y : RealSpace 4, remainderDensity r (r • y) * φ (r • y) =
      ((r ^ 4)⁻¹ : ℝ) • ((remainderFun y : ℂ) * φ (r • y)) := fun y => by
    rw [remainderDensity_eq_remainderFun hCut hRC hO hPI hTL hUK]
    simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul, smul_mul_assoc]
  simp only [hpt] at h
  rw [integral_smul] at h
  exact (smul_right_injective ℂ (inv_ne_zero (pow_ne_zero 4 hr.ne'))
    (by simpa using h)).symm
theorem isContinuousDensityOf_remainderDensity {r : ℝ} (hr : 0 < r) :
    IsContinuousDensityOf (laplacianCubedRemainder r hr) (remainderDensity r) := by
  have hs := contDiff_remainderFun hRC hTL
  refine ⟨?_, fun φ => ?_⟩
  · rw [remainderDensity_eq_remainderFun hCut hRC hO hPI hTL hUK]
    exact ((Complex.continuous_ofReal.comp hs.continuous).comp
      (continuous_const_smul r⁻¹)).const_smul ((r ^ 4)⁻¹ : ℝ)
  · have h1 : laplacianCubedRemainder r hr φ =
        parametrixRemainderOne (testFunctionRescale r hr φ) := by
      have hne : ((r : ℂ) ^ 4) ≠ 0 := pow_ne_zero 4 (by exact_mod_cast hr.ne')
      show ((r : ℂ) ^ 4)⁻¹ • ((r : ℂ) ^ 4) •
        parametrixRemainderOne (testFunctionRescale r hr φ) = _
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [h1, (isContinuousDensityOf_remainderFun hRC hO hPI hTL hUK).2,
      integral_remainderDensity_mul hCut hRC hO hPI hTL hUK hr]
    rfl
theorem integral_laplacianCubedParametrix_mul {r : ℝ} (hr : 0 < r) (φ : SmoothTestFunction) :
    ∫ x, (laplacianCubedParametrix r x : ℂ) * testLaplacianCubed φ x =
      φ 0 - ∫ x, remainderDensity r x * φ x := by
  have hu := integral_parametrixOne_mul hO hPI hUK hRC hTL (affineComp 0 r hr.ne' φ)
  have hd := integral_comp_smul_pos hr
    (fun x => (laplacianCubedParametrix r x : ℂ) * testLaplacianCubed φ x)
  have hpt : ∀ y : RealSpace 4,
      (laplacianCubedParametrix r (r • y) : ℂ) * testLaplacianCubed φ (r • y) =
      ((r ^ 4)⁻¹ : ℝ) • ((parametrixOne y : ℂ) *
        testLaplacianCubed (affineComp 0 r hr.ne' φ) y) := fun y => by
    rw [testLaplacianCubed_affineComp, Complex.real_smul]
    simp only [laplacianCubedParametrix, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, zero_add]
    have hne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    field_simp
  simp only [hpt] at hd
  rw [integral_smul] at hd
  have he : ∫ x, (laplacianCubedParametrix r x : ℂ) * testLaplacianCubed φ x =
      ∫ y, (parametrixOne y : ℂ) * testLaplacianCubed (affineComp 0 r hr.ne' φ) y :=
    (smul_right_injective ℂ (inv_ne_zero (pow_ne_zero 4 hr.ne')) (by simpa using hd)).symm
  rw [he, hu, integral_remainderDensity_mul hCut hRC hO hPI hTL hUK hr]
  simp
theorem reproducingIdentity_of_pos {r : ℝ} (hr : 0 < r) : ReproducingIdentity r := by
  intro h x
  have hs := integral_laplacianCubedParametrix_mul hCut hRC hO hPI hTL hUK hr
    (affineComp x (-1) (by norm_num) h)
  have e1 : ∫ y, (laplacianCubedParametrix r y : ℂ) *
      testLaplacianCubed (affineComp x (-1) (by norm_num) h) y =
      EuclideanAnalysis.convolution (testLaplacianCubed h)
        (fun y => (laplacianCubedParametrix r y : ℂ)) x := by
    unfold EuclideanAnalysis.convolution
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have h6 : ((((-1 : ℝ) ^ 6 : ℝ)) : ℂ) = 1 := by norm_num
    beta_reduce
    rw [testLaplacianCubed_affineComp, h6]
    simp [sub_eq_add_neg, mul_comm]
  have e2 : ∫ y, remainderDensity r y * affineComp x (-1) (by norm_num) h y =
      EuclideanAnalysis.convolution h (remainderDensity r) x := by
    unfold EuclideanAnalysis.convolution
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [sub_eq_add_neg, mul_comm]
  rw [e1, e2] at hs
  have h0 : affineComp x (-1) (by norm_num) h 0 = h x := by simp
  rw [h0] at hs
  rw [hs]
  ring
theorem kernelsRegularAndLocal_of_pos {r : ℝ} (hr : 0 < r) : KernelsRegularAndLocal r := by
  obtain ⟨ϱ, hϱ0, hϱ1, hsup⟩ := exists_radius_tsupport_radialBump
  have hs := contDiff_remainderFun hRC hTL
  have hreq := remainderDensity_eq_remainderFun hCut hRC hO hPI hTL hUK r
  have hpar : ∀ x, ϱ * r < ‖x‖ → laplacianCubedParametrix r x = 0 := fun x hx => by
    have := image_eq_zero_of_notMem_tsupport (hsup _ (lt_norm_inv_smul hr hx))
    simp [laplacianCubedParametrix, parametrixOne, this]
  have hrem : ∀ x, ϱ * r < ‖x‖ → remainderDensity r x = 0 := fun x hx => by
    rw [hreq]
    simp [remainderFun_eq_zero hTL hϱ0 hsup (lt_norm_inv_smul hr hx)]
  have hcloc := support_small_of_eq_zero hϱ1 hr hpar
  have hsloc := support_small_of_eq_zero hϱ1 hr hrem
  refine ⟨?_, ?_, ?_, hcloc.1, hcloc.2, hsloc.1, hsloc.2⟩
  · show ContDiff ℝ 1 (fun x => r ^ 2 * parametrixOne (r⁻¹ • x))
    exact contDiff_const.mul ((contDiff_parametrixOne hUK).comp (contDiff_const_smul r⁻¹))
  · rw [hreq]
    exact (Complex.ofRealCLM.contDiff.comp (hs.comp (contDiff_const_smul r⁻¹))).const_smul
      ((r ^ 4)⁻¹ : ℝ)
  · intro x
    rw [hreq]
    beta_reduce
    rw [Complex.real_smul, ← Complex.ofReal_mul]
    exact Complex.ofReal_im _
omit hCut hRC hO hPI hTL hUK in
theorem kernelNormsScaling_of_pos {r : ℝ} (hr : 0 < r) : KernelNormsScaling r := by
  have hp : laplacianCubedParametrix r = fun z => (r ^ 2) • parametrixOne (r⁻¹ • z) := rfl
  have hk1 : |r ^ 2 * r⁻¹| = r := by
    rw [abs_of_nonneg (by positivity)]
    field_simp
  have hk2 : |(r ^ 4)⁻¹ * r⁻¹| = (r ^ 5)⁻¹ := by
    rw [abs_of_nonneg (by positivity)]
    field_simp
  refine ⟨uniformNorm_of_norm_eq (by positivity) hr _ _ fun x => ?_, ?_,
    uniformNorm_of_norm_eq (by positivity) hr _ _ fun x => ?_, ?_⟩
  · rw [hp]
    simp only [smul_eq_mul]
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hr.le]
  · rw [gradUniformNorm_of_eq hr parametrixOne (laplacianCubedParametrix r) hp, hk1]
  · rw [remainderDensity_eq_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
  · rw [gradUniformNorm_of_eq hr remainderDensityOne (remainderDensity r)
      (remainderDensity_eq_smul r), hk2]
theorem oneScaleNormsFinite_holds : OneScaleNormsFinite := by
  obtain ⟨ϱ, hϱ0, hϱ1, hsup⟩ := exists_radius_tsupport_radialBump
  have heq := remainderDensityOne_eq hCut hRC hO hPI hTL hUK
  have hn : HasCompactSupport parametrixOne :=
    (support_small_of_eq_zero (r := 1) hϱ1 one_pos fun x hx => by
      have := image_eq_zero_of_notMem_tsupport (hsup x (by simpa using hx))
      simp [parametrixOne, this]).1
  have hg : HasCompactSupport remainderDensityOne :=
    (support_small_of_eq_zero (r := 1) hϱ1 one_pos fun x hx => by
      rw [heq]
      simp [remainderFun_eq_zero hTL hϱ0 hsup (by simpa using hx)]).1
  have hgs : ContDiff ℝ ∞ remainderDensityOne := by
    rw [heq]
    exact Complex.ofRealCLM.contDiff.comp (contDiff_remainderFun hRC hTL)
  have hn1 := contDiff_parametrixOne hUK
  exact ⟨isBoundedFun_of_compact hn1.continuous hn, isBoundedFun_gradNorm hn1 hn,
    isBoundedFun_of_compact hgs.continuous hg, isBoundedFun_gradNorm (hgs.of_le (by simp)) hg⟩
end Main
theorem parametrixSpec_holds (hCut : BumpAndDensities.Combined)
    (hRC : RadialBumpHasProperties)
    (hO : OriginIdentity)
    (hPI : LaplacianCubeSelfAdjoint)
    (hTL : TripleLaplacianLogKernel)
    (hUK : UnitKernelRegularity) :
    ParametrixSpec := by
  have hU := isContinuousDensityOf_remainderFun hRC hO hPI hTL hUK
  have heq := remainderDensityOne_eq hCut hRC hO hPI hTL hUK
  have hCV := hCut.2.1
  refine ⟨⟨Complex.ofRealCLM.contDiff.comp (contDiff_fundSol hUK),
      integral_fundSol_mul hO hPI hUK⟩, ⟨⟨_, hU, fun f hf => isContinuousDensityOf_unique hCV hf hU⟩,
      ?_, ?_,
      fun r hr f => ⟨fun hf => isContinuousDensityOf_unique hCV hf
        (isContinuousDensityOf_remainderDensity hCut hRC hO hPI hTL hUK hr), fun e => e ▸
        isContinuousDensityOf_remainderDensity hCut hRC hO hPI hTL hUK hr⟩⟩,
    fun r hr => kernelsRegularAndLocal_of_pos hCut hRC hO hPI hTL hUK hr,
    fun r hr => ⟨reproducingIdentity_of_pos hCut hRC hO hPI hTL hUK hr, kernelNormsScaling_of_pos hr⟩,
    oneScaleNormsFinite_holds hCut hRC hO hPI hTL hUK⟩
  · rw [heq]
    exact hU
  · rw [heq]
    exact Complex.ofRealCLM.contDiff.comp (contDiff_remainderFun hRC hTL)
end YangMills.Construction.EuclideanAnalysis.CubedLaplacian.ParametrixConstruction
