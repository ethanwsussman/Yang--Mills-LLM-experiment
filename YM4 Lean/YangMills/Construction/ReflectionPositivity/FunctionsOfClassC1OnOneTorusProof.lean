import YangMills.Construction.ReflectionPositivity.FunctionsOfClassC1OnOneTorus
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.Torus.CellsOfATranslatedLatticeAndBallsOfTheTorusProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.TorusMetric
open YangMills.Construction.ReflectionPositivity.TorusCutoffs
open YangMills.Construction.ReflectionPositivity.TorusTuples
open YangMills.Construction.ReflectionPositivity.TorusC1
open scoped ENNReal Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.TorusC1Facts
section EuclideanNorm
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : Fin 4 → ℝ) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
theorem norm_le_euclidNormVec (v : Fin 4 → ℝ) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem abs_sum_mul_le_euclidNormVec (v u : Fin 4 → ℝ) :
    |∑ i, v i * u i| ≤ euclidNormVec v * euclidNormVec u := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.abs_inner_le_euclidNormVec_mul <;> assumption
theorem clm_apply_eq_sum_basis (A : (Fin 4 → ℝ) →L[ℝ] ℝ) (v : Fin 4 → ℝ) :
    A v = ∑ i, v i * A (Pi.single i 1) := by
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin 4 → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum]
end EuclideanNorm
variable {s : Conventions.StandingParameters}
theorem torusSide_pos (s : Conventions.StandingParameters) :
    0 < PeriodicLattice.torusSide s.L s.m := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.torusSide_pos <;> assumption
theorem continuous_liftGrad {f : s.Torus → ℝ} (hf : IsC1 f) :
    Continuous (liftGrad f) := by
  have hc : ContDiff ℝ 1 (f ∘ proj s) := hf
  have hd : Continuous (fderiv ℝ (f ∘ proj s)) := hc.continuous_fderiv one_ne_zero
  exact continuous_pi fun i => hd.clm_apply continuous_const
theorem grad_proj (f : s.Torus → ℝ) (y : Fin 4 → ℝ) :
    grad f (proj s y) = liftGrad f y :=
  grad_eq_of_proj_eq f rfl
theorem exists_preimage_mem_box (x : s.Torus) :
    ∃ y, proj s y = x ∧ ∀ i, 0 ≤ y i ∧ y i ≤ PeriodicLattice.torusSide s.L s.m := by
  have hℓ := torusSide_pos s
  refine ⟨lift s x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide s.L s.m)
    (fun i => -⌊lift s x i / PeriodicLattice.torusSide s.L s.m⌋), ?_, fun i => ?_⟩
  · have h : proj s (lift s x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide s.L s.m)
        (fun i => -⌊lift s x i / PeriodicLattice.torusSide s.L s.m⌋)) = proj s (lift s x) :=
      TestFunctions.torusProj_add_latticeTranslate _ _ _
    rw [h, proj_lift]
  · have hl := (le_div_iff₀ hℓ).mp (Int.floor_le (lift s x i / PeriodicLattice.torusSide s.L s.m))
    have hu := (div_lt_iff₀ hℓ).mp
      (Int.lt_floor_add_one (lift s x i / PeriodicLattice.torusSide s.L s.m))
    simp only [Pi.add_apply, TestFunctions.latticeTranslate, Int.cast_neg]
    constructor <;> nlinarith
theorem exists_preimage_near (hT : CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (y : Fin 4 → ℝ) (x' : s.Torus) :
    ∃ y', proj s y' = x' ∧ euclidNormVec (y - y') = torusDist (proj s y) x' := by
  obtain ⟨k, hk⟩ := ((hT (unitData s)).1.1 y (lift s x')).1
  refine ⟨lift s x' + TestFunctions.latticeTranslate (PeriodicLattice.torusSide s.L s.m) k, ?_, ?_⟩
  · have h : proj s (lift s x' + TestFunctions.latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) =
        proj s (lift s x') := TestFunctions.torusProj_add_latticeTranslate _ _ _
    rw [h, proj_lift]
  · have h : torusDist (proj s y) (proj s (lift s x')) =
        euclidNormVec (y - lift s x' - TestFunctions.latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) :=
      hk.symm
    rw [proj_lift] at h
    rw [h, sub_sub]
def widenedBox (s : Conventions.StandingParameters) : Set (Fin 4 → ℝ) :=
  Icc (fun _ => -PeriodicLattice.torusSide s.L s.m) (fun _ => 2 * PeriodicLattice.torusSide s.L s.m)
theorem isCompact_widenedBox (s : Conventions.StandingParameters) : IsCompact (widenedBox s) :=
  isCompact_Icc
theorem mem_widenedBox {y : Fin 4 → ℝ}
    (h : ∀ i, -PeriodicLattice.torusSide s.L s.m ≤ y i ∧ y i ≤ 2 * PeriodicLattice.torusSide s.L s.m) :
    y ∈ widenedBox s :=
  ⟨fun i => (h i).1, fun i => (h i).2⟩
theorem gradSupNorm_lt_top {f : s.Torus → ℝ} (hf : IsC1 f) : gradSupNorm f < ∞ := by
  have hℓ := torusSide_pos s
  obtain ⟨C, hC⟩ := (isCompact_widenedBox s).exists_bound_of_continuousOn
    (f := fun y => euclidNormVec (liftGrad f y))
    (continuous_euclidNormVec.comp (continuous_liftGrad hf)).continuousOn
  refine lt_of_le_of_lt (iSup_le fun x => ?_) (ENNReal.ofReal_lt_top (r := C))
  obtain ⟨y, rfl, hy⟩ := exists_preimage_mem_box x
  apply ENNReal.ofReal_le_ofReal
  rw [grad_proj]
  refine (le_abs_self _).trans (hC y (mem_widenedBox fun i => ?_))
  constructor <;> linarith [(hy i).1, (hy i).2]
theorem grad_uniformContinuous (hT : CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    {f : s.Torus → ℝ} (hf : IsC1 f) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x x' : s.Torus, torusDist x x' ≤ δ →
      euclidNormVec (grad f x - grad f x') ≤ ε := by
  have hℓ := torusSide_pos s
  have huc := (isCompact_widenedBox s).uniformContinuousOn_of_continuous
    (continuous_liftGrad hf).continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₁, hδ₁, h⟩ := huc (ε / 2) (half_pos hε)
  refine ⟨min (δ₁ / 2) (PeriodicLattice.torusSide s.L s.m), lt_min (half_pos hδ₁) hℓ,
    fun x x' hxx' => ?_⟩
  obtain ⟨y, rfl, hy⟩ := exists_preimage_mem_box x
  obtain ⟨y', rfl, hy'⟩ := exists_preimage_near hT y x'
  rw [← hy'] at hxx'
  have hco : ∀ i, |y i - y' i| ≤ PeriodicLattice.torusSide s.L s.m := fun i =>
    (abs_apply_le_euclidNormVec (y - y') i).trans (hxx'.trans (min_le_right _ _))
  have hyQ : y ∈ widenedBox s := mem_widenedBox fun i => by
    constructor <;> linarith [(hy i).1, (hy i).2]
  have hy'Q : y' ∈ widenedBox s := mem_widenedBox fun i => by
    have := abs_le.mp (hco i)
    constructor <;> linarith [(hy i).1, (hy i).2, this.1, this.2]
  have hdist : dist y y' < δ₁ := by
    rw [dist_eq_norm]
    have h1 := (norm_le_euclidNormVec (y - y')).trans (hxx'.trans (min_le_left _ _))
    linarith
  have h2 := h y hyQ y' hy'Q hdist
  rw [dist_eq_norm] at h2
  rw [grad_proj, grad_proj]
  have h3 := euclidNormVec_le_two_mul_norm (liftGrad f y - liftGrad f y')
  linarith
theorem euclidNormVec_liftGrad_le {f : s.Torus → ℝ} (hf : IsC1 f) (z : Fin 4 → ℝ) :
    euclidNormVec (liftGrad f z) ≤ (gradSupNorm f).toReal := by
  have h : ENNReal.ofReal (euclidNormVec (grad f (proj s z))) ≤ gradSupNorm f :=
    le_iSup (fun x => ENNReal.ofReal (euclidNormVec (grad f x))) (proj s z)
  rw [grad_proj] at h
  exact (ENNReal.ofReal_le_iff_le_toReal (gradSupNorm_lt_top hf).ne).mp h
theorem abs_sub_le_gradSupNorm_mul (hT : CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    {f : s.Torus → ℝ} (hf : IsC1 f) (x x' : s.Torus) :
    |f x - f x'| ≤ (gradSupNorm f).toReal * torusDist x x' := by
  obtain ⟨y, rfl⟩ := exists_proj_eq s x
  obtain ⟨y', rfl, hy'⟩ := exists_preimage_near hT y x'
  rw [← hy']
  have hc : ContDiff ℝ 1 (f ∘ proj s) := hf
  have hder : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => (f ∘ proj s) (y' + t • (y - y')))
        (fderiv ℝ (f ∘ proj s) (y' + t • (y - y')) (y - y')) (Icc (0 : ℝ) 1) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => y' + t • (y - y')) (y - y') t := by
      simpa using ((hasDerivAt_id t).smul_const (y - y')).const_add y'
    have h2 : HasFDerivAt (f ∘ proj s) (fderiv ℝ (f ∘ proj s) (y' + t • (y - y')))
        (y' + t • (y - y')) := (hc.differentiable one_ne_zero _).hasFDerivAt
    exact (h2.comp_hasDerivAt t h1).hasDerivWithinAt
  have hb : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖fderiv ℝ (f ∘ proj s) (y' + t • (y - y')) (y - y')‖ ≤
        (gradSupNorm f).toReal * euclidNormVec (y - y') := by
    intro t _
    rw [Real.norm_eq_abs, clm_apply_eq_sum_basis, mul_comm]
    exact (abs_sum_mul_le_euclidNormVec _ (liftGrad f (y' + t • (y - y')))).trans
      (mul_le_mul_of_nonneg_left (euclidNormVec_liftGrad_le hf _) (Real.sqrt_nonneg _))
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hder hb
  simpa [Real.norm_eq_abs] using h
theorem liftGrad_of_affine {f g : s.Torus → ℝ} (hf : IsC1 f)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ)
    (hcomp : ∀ y, g (proj s y) = f (proj s (R *ᵥ y + w))) :
    IsC1 g ∧ ∀ y, liftGrad g y = Rᵀ *ᵥ liftGrad f (R *ᵥ y + w) := by
  have hc : ContDiff ℝ 1 (f ∘ proj s) := hf
  let Rl : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin R)
  have e : g ∘ proj s = (f ∘ proj s) ∘ fun y => Rl y + w := funext hcomp
  constructor
  · show ContDiff ℝ 1 (g ∘ proj s)
    rw [e]
    exact hc.comp (Rl.contDiff.add contDiff_const)
  · intro y
    funext i
    have h2 : HasFDerivAt (f ∘ proj s) (fderiv ℝ (f ∘ proj s) (Rl y + w))
        ((fun y => Rl y + w) y) := (hc.differentiable one_ne_zero _).hasFDerivAt
    have h1 : HasFDerivAt (fun y => Rl y + w) Rl y := Rl.hasFDerivAt.add_const w
    have h3 := (h2.comp y h1).fderiv
    have hcol : ∀ j, Rl (Pi.single i 1) j = R j i := fun j => by
      show (R *ᵥ Pi.single i 1) j = R j i
      simp
    show fderiv ℝ (g ∘ proj s) y (Pi.single i 1) = _
    rw [e, h3, ContinuousLinearMap.comp_apply, clm_apply_eq_sum_basis]
    simp only [hcol]
    rfl
theorem proj_neg_lift (v : s.Torus) : proj s (-lift s v) = -v := by
  have h := proj_add s (lift s v) (-lift s v)
  have h0 : proj s 0 = 0 := by
    funext i
    show ((0 : ℝ) : AddCircle (PeriodicLattice.torusSide s.L s.m)) = 0
    simp
  rw [add_neg_cancel, proj_lift, h0] at h
  exact eq_neg_of_add_eq_zero_right h.symm
theorem gradEquivariant_of_isC1 {f : s.Torus → ℝ} (hf : IsC1 f) :
    GradEquivariant f := by
  refine ⟨fun r _ R w _ hrw => ?_, fun v x => ?_⟩
  · obtain ⟨h1, h2⟩ := liftGrad_of_affine (g := transport r f) hf R w
      (fun y => by simp only [transport, Function.comp, hrw])
    refine ⟨h1, fun x => ?_⟩
    obtain ⟨y, rfl⟩ := exists_proj_eq s x
    rw [grad_proj, h2 y, hrw, grad_proj]
  · have hm : ∀ y, proj s y - v = proj s (y + -lift s v) := fun y => by
      rw [proj_add, proj_neg_lift, sub_eq_add_neg]
    obtain ⟨-, h2⟩ := liftGrad_of_affine (g := transport (shiftBy v) f) hf 1
      (-lift s v) (fun y => by rw [transport_shiftBy, Matrix.one_mulVec, hm])
    obtain ⟨y, rfl⟩ := exists_proj_eq s x
    rw [grad_proj, h2 y, Matrix.transpose_one, Matrix.one_mulVec, Matrix.one_mulVec, hm,
      grad_proj]
theorem subC1_of_isC1 {f : s.Torus → ℝ} (hf : IsC1 f) :
    SubC1 f := by
  intro f' hf'
  have hc : ContDiff ℝ 1 (f ∘ proj s) := hf
  have hc' : ContDiff ℝ 1 (f' ∘ proj s) := hf'
  have e : (f - f') ∘ proj s = (f ∘ proj s) - f' ∘ proj s := rfl
  refine ⟨?_, ?_⟩
  · show ContDiff ℝ 1 ((f - f') ∘ proj s)
    rw [e]
    exact hc.sub hc'
  · funext x i
    show fderiv ℝ ((f - f') ∘ proj s) (lift s x) (Pi.single i 1) =
      fderiv ℝ (f ∘ proj s) (lift s x) (Pi.single i 1) -
        fderiv ℝ (f' ∘ proj s) (lift s x) (Pi.single i 1)
    have h := ((hc.differentiable one_ne_zero (lift s x)).hasFDerivAt.sub
      (hc'.differentiable one_ne_zero (lift s x)).hasFDerivAt).fderiv
    rw [e]
    erw [h]
    rfl
theorem c1Properties_holds (hT : CutoffMirrors.TorusMetricSpace.MetricTorusFacts) :
    C1Properties := by
  intro s f hf
  have hb := abs_sub_le_gradSupNorm_mul hT hf
  refine ⟨⟨gradSupNorm_lt_top hf, grad_uniformContinuous hT hf⟩, ⟨hb, ?_, ?_⟩,
    gradEquivariant_of_isC1 hf, subC1_of_isC1 hf⟩
  · exact ⟨_, ENNReal.toReal_nonneg, hb⟩
  · exact csInf_le ⟨0, fun _ h => h.1⟩ ⟨ENNReal.toReal_nonneg, hb⟩
end YangMills.Construction.ReflectionPositivity.TorusC1Facts
end
