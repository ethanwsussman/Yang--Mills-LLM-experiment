import YangMills.Construction.ForwardTube.ArgumentsOfTheGramKernelProof
import YangMills.Construction.ForwardTube.SuccessiveTubeDomainsAndLabelledPoints
import YangMills.Construction.EuclideanFunctionals.ForwardTubeAndTheSemigroupOfItsOperatorsProof
import YangMills.Construction.ForwardTube.ElementaryFactsOfTheTubeFramesStripSectorAndPencils
import YangMills.Construction.RotationInvariance.DensityOfThePlateFunctionsAtDistinctPointsProof
import Mathlib
set_option autoImplicit false
open Complex (I)
open ComplexConjugate
open Filter Topology
noncomputable section
namespace YangMills.Construction.ForwardTube.TubeGeometry
theorem re_lightConePlus (v : ℂ × ℂ) : (lightConePlus v).re = v.1.re - v.2.im := by
  simp [lightConePlus, sub_eq_add_neg]
theorem re_lightConeMinus (v : ℂ × ℂ) : (lightConeMinus v).re = v.1.re + v.2.im := by
  simp [lightConeMinus]
theorem eq_of_lightCone_eq {v w : ℂ × ℂ} (hp : lightConePlus v = lightConePlus w)
    (hm : lightConeMinus v = lightConeMinus w) : v = w := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeSemigroup.pair_ext_lightCone <;> assumption
theorem coords_eq_lightCone (v : ℂ × ℂ) :
    v.1 = 1 / 2 * (lightConePlus v + lightConeMinus v) ∧
      v.2 = 1 / (2 * I) * (lightConePlus v - lightConeMinus v) :=
  ⟨(congrArg Prod.fst (ofLightConeCoords_lightConePlus_lightConeMinus v)).symm,
    (congrArg Prod.snd (ofLightConeCoords_lightConePlus_lightConeMinus v)).symm⟩
theorem isLinearMap_lightConePair :
    IsLinearMap ℂ (fun v : ℂ × ℂ => (lightConePlus v, lightConeMinus v)) := by
  refine ⟨fun v w => ?_, fun c v => ?_⟩
  · refine Prod.ext ?_ ?_
    · simp only [lightConePlus, Prod.fst_add, Prod.snd_add]
      ring
    · simp only [lightConeMinus, Prod.fst_add, Prod.snd_add]
      ring
  · refine Prod.ext ?_ ?_
    · simp only [lightConePlus, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    · simp only [lightConeMinus, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
theorem bijective_lightConePair :
    Function.Bijective (fun v : ℂ × ℂ => (lightConePlus v, lightConeMinus v)) :=
  Function.bijective_iff_has_inverse.2 ⟨fun p => ofLightConeCoords p.1 p.2,
    ofLightConeCoords_lightConePlus_lightConeMinus,
    fun _ => Prod.ext (lightConePlus_ofLightConeCoords _ _) (lightConeMinus_ofLightConeCoords _ _)⟩
theorem existsUnique_linearMap_boost (hlin : ∀ z : ℂ, IsLinearMap ℂ (complexBoost z)) (z : ℂ) :
    ∃! f : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ), ∀ v : ℂ × ℂ,
      lightConePlus (f v) = Complex.exp (I * z) * lightConePlus v ∧
        lightConeMinus (f v) = Complex.exp (-(I * z)) * lightConeMinus v := by
  refine ⟨IsLinearMap.mk' _ (hlin z),
    fun v => ⟨lightConePlus_complexBoost z v, lightConeMinus_complexBoost z v⟩, fun g hg => ?_⟩
  refine LinearMap.ext fun v => eq_of_lightCone_eq ?_ ?_
  · exact (hg v).1.trans (lightConePlus_complexBoost z v).symm
  · exact (hg v).2.trans (lightConeMinus_complexBoost z v).symm
theorem lightConePlus_boost_imag (s : ℝ) (v : ℂ × ℂ) :
    lightConePlus (complexBoost (I * s) v) = (Real.exp (-s) : ℂ) * lightConePlus v := by apply _root_.YangMills.Construction.ForwardTube.GramKernelArgs.lightConePlus_imagBoost <;> assumption
theorem lightConeMinus_boost_imag (s : ℝ) (v : ℂ × ℂ) :
    lightConeMinus (complexBoost (I * s) v) = (Real.exp s : ℂ) * lightConeMinus v := by apply _root_.YangMills.Construction.ForwardTube.GramKernelArgs.lightConeMinus_imagBoost <;> assumption
theorem mem_forwardTube_iff_abs (v : ℂ × ℂ) : v ∈ forwardTube ↔ v.1.re > |v.2.im| := by
  rw [gt_iff_lt, abs_lt]
  constructor
  · rintro ⟨hp, hm⟩
    rw [gt_iff_lt, re_lightConePlus] at hp
    rw [gt_iff_lt, re_lightConeMinus] at hm
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hp, hm⟩
    refine ⟨?_, ?_⟩
    · rw [gt_iff_lt, re_lightConePlus]
      linarith
    · rw [gt_iff_lt, re_lightConeMinus]
      linarith
theorem mem_closedForwardTube_iff_abs (v : ℂ × ℂ) :
    v ∈ closedForwardTube ↔ v.1.re ≥ |v.2.im| := by
  rw [ge_iff_le, abs_le]
  constructor
  · rintro ⟨hp, hm⟩
    rw [ge_iff_le, re_lightConePlus] at hp
    rw [ge_iff_le, re_lightConeMinus] at hm
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hp, hm⟩
    refine ⟨?_, ?_⟩
    · rw [ge_iff_le, re_lightConePlus]
      linarith
    · rw [ge_iff_le, re_lightConeMinus]
      linarith
theorem lightConePair_image_forwardTube :
    (fun v : ℂ × ℂ => (lightConePlus v, lightConeMinus v)) '' forwardTube =
      {a : ℂ | a.re > 0} ×ˢ {b : ℂ | b.re > 0} := by
  ext p
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hv.1, hv.2⟩
  · rintro ⟨hp, hm⟩
    refine ⟨ofLightConeCoords p.1 p.2, ⟨?_, ?_⟩,
      Prod.ext (lightConePlus_ofLightConeCoords _ _) (lightConeMinus_ofLightConeCoords _ _)⟩
    · rw [lightConePlus_ofLightConeCoords]
      exact hp
    · rw [lightConeMinus_ofLightConeCoords]
      exact hm
theorem lightConePair_image_closedForwardTube :
    (fun v : ℂ × ℂ => (lightConePlus v, lightConeMinus v)) '' closedForwardTube =
      closure {a : ℂ | a.re > 0} ×ˢ closure {b : ℂ | b.re > 0} := by
  have hcl : closure {a : ℂ | a.re > 0} = {a : ℂ | 0 ≤ a.re} :=
    Complex.closure_setOfPred_lt_re 0
  rw [hcl]
  ext p
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hv.1, hv.2⟩
  · rintro ⟨hp, hm⟩
    refine ⟨ofLightConeCoords p.1 p.2, ⟨?_, ?_⟩,
      Prod.ext (lightConePlus_ofLightConeCoords _ _) (lightConeMinus_ofLightConeCoords _ _)⟩
    · rw [lightConePlus_ofLightConeCoords]
      exact hp
    · rw [lightConeMinus_ofLightConeCoords]
      exact hm
theorem isLinearMap_re_lightConePlus :
    IsLinearMap ℝ (fun v : ℂ × ℂ => (lightConePlus v).re) := by
  refine ⟨fun v w => ?_, fun c v => ?_⟩ <;> simp only [re_lightConePlus] <;> simp <;> ring
theorem isLinearMap_re_lightConeMinus :
    IsLinearMap ℝ (fun v : ℂ × ℂ => (lightConeMinus v).re) := by
  refine ⟨fun v w => ?_, fun c v => ?_⟩ <;> simp only [re_lightConeMinus] <;> simp <;> ring
theorem convex_forwardTube : Convex ℝ forwardTube := by
  have h := (convex_halfSpace_gt isLinearMap_re_lightConePlus 0).inter
    (convex_halfSpace_gt isLinearMap_re_lightConeMinus 0)
  have he : forwardTube =
      {w : ℂ × ℂ | 0 < (lightConePlus w).re} ∩ {w : ℂ × ℂ | 0 < (lightConeMinus w).re} :=
    Set.ext fun _ => Iff.rfl
  rw [he]
  exact h
theorem isClosed_closedForwardTube : IsClosed closedForwardTube := by
  have hp : Continuous fun v : ℂ × ℂ => (lightConePlus v).re := by
    unfold lightConePlus
    fun_prop
  have hm : Continuous fun v : ℂ × ℂ => (lightConeMinus v).re := by
    unfold lightConeMinus
    fun_prop
  exact (isClosed_le continuous_const hp).inter (isClosed_le continuous_const hm)
theorem re_lightConePlus_add_time (v : ℂ × ℂ) (ε : ℝ) :
    (lightConePlus (v + ((ε : ℂ), (0 : ℂ)))).re = (lightConePlus v).re + ε := by
  simp only [re_lightConePlus]
  simp
  ring
theorem re_lightConeMinus_add_time (v : ℂ × ℂ) (ε : ℝ) :
    (lightConeMinus (v + ((ε : ℂ), (0 : ℂ)))).re = (lightConeMinus v).re + ε := by
  simp only [re_lightConeMinus]
  simp
  ring
theorem tendsto_add_time (v : ℂ × ℂ) (s : Set ℝ) :
    Tendsto (fun ε : ℝ => v + ((ε : ℂ), (0 : ℂ))) (𝓝[s] 0) (𝓝 v) := by
  have hc : Continuous fun ε : ℝ => v + ((ε : ℂ), (0 : ℂ)) := by fun_prop
  exact (hc.tendsto' 0 v (by simp)).mono_left nhdsWithin_le_nhds
theorem closure_forwardTube : closure forwardTube = closedForwardTube := by
  refine Set.Subset.antisymm
    (closure_minimal (fun v hv => ⟨hv.1.le, hv.2.le⟩) isClosed_closedForwardTube)
    fun v hv => ?_
  refine mem_closure_of_tendsto (tendsto_add_time v (Set.Ioi 0))
    (eventually_mem_nhdsWithin.mono fun ε hε => ?_)
  have hε' : 0 < ε := hε
  have hp : 0 ≤ (lightConePlus v).re := hv.1
  have hm : 0 ≤ (lightConeMinus v).re := hv.2
  refine ⟨?_, ?_⟩
  · rw [gt_iff_lt, re_lightConePlus_add_time]
    linarith
  · rw [gt_iff_lt, re_lightConeMinus_add_time]
    linarith
theorem interior_closedForwardTube (hopen : IsOpen forwardTube) :
    interior closedForwardTube = forwardTube := by
  refine Set.Subset.antisymm (fun v hv => ?_)
    (interior_maximal (fun v hv => ⟨hv.1.le, hv.2.le⟩) hopen)
  have hev := (tendsto_add_time v (Set.Iio 0)).eventually (isOpen_interior.mem_nhds hv)
  obtain ⟨ε, hi, hε⟩ := (hev.and self_mem_nhdsWithin).exists
  have hmem : v + ((ε : ℂ), (0 : ℂ)) ∈ closedForwardTube := interior_subset hi
  have hp : 0 ≤ (lightConePlus (v + ((ε : ℂ), (0 : ℂ)))).re := hmem.1
  have hm : 0 ≤ (lightConeMinus (v + ((ε : ℂ), (0 : ℂ)))).re := hmem.2
  rw [re_lightConePlus_add_time] at hp
  rw [re_lightConeMinus_add_time] at hm
  refine ⟨?_, ?_⟩
  · show 0 < (lightConePlus v).re
    linarith
  · show 0 < (lightConeMinus v).re
    linarith
theorem add_mem_closedForwardTube {v w : ℂ × ℂ} (hv : v ∈ closedForwardTube)
    (hw : w ∈ closedForwardTube) : v + w ∈ closedForwardTube := by
  have h₁ : 0 ≤ (lightConePlus v).re := hv.1
  have h₂ : 0 ≤ (lightConeMinus v).re := hv.2
  have h₃ : 0 ≤ (lightConePlus w).re := hw.1
  have h₄ : 0 ≤ (lightConeMinus w).re := hw.2
  have h₅ : (lightConePlus (v + w)).re = (lightConePlus v).re + (lightConePlus w).re :=
    isLinearMap_re_lightConePlus.map_add v w
  have h₆ : (lightConeMinus (v + w)).re = (lightConeMinus v).re + (lightConeMinus w).re :=
    isLinearMap_re_lightConeMinus.map_add v w
  refine ⟨?_, ?_⟩
  · show 0 ≤ (lightConePlus (v + w)).re
    rw [h₅]
    linarith
  · show 0 ≤ (lightConeMinus (v + w)).re
    rw [h₆]
    linarith
theorem closedForwardTube_inter_realVectors :
    closedForwardTube ∩ realVectors = embedPlane '' {y : RealPlane | y 0 ≥ 0} := by
  ext v
  constructor
  · rintro ⟨hv, hre₁, hre₂⟩
    have hp : 0 ≤ (lightConePlus v).re := hv.1
    rw [re_lightConePlus, hre₂, sub_zero] at hp
    refine ⟨!₂[v.1.re, v.2.re], by simpa using hp, ?_⟩
    refine Prod.ext (Complex.ext ?_ ?_) (Complex.ext ?_ ?_) <;> simp [embedPlane, hre₁, hre₂]
  · rintro ⟨y, hy, rfl⟩
    have hy' : 0 ≤ y 0 := hy
    refine ⟨(mem_closedForwardTube_iff_abs _).2 ?_, ?_, ?_⟩
    · simpa [embedPlane] using hy'
    · simp [embedPlane]
    · simp [embedPlane]
theorem image_eq_self_of_involutive {f : ℂ × ℂ → ℂ × ℂ} {A : Set (ℂ × ℂ)}
    (hf : ∀ v, f (f v) = v) (hA : ∀ v ∈ A, f v ∈ A) : f '' A = A := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeSemigroup.image_eq_self_of_involutive <;> assumption
theorem tubeStar_tubeStar (v : ℂ × ℂ) : tubeStar (tubeStar v) = v := by
  simp [tubeStar]
theorem conjPair_conjPair (v : ℂ × ℂ) : conjPair (conjPair v) = v := by
  simp [conjPair]
theorem lightConePlus_conjPair (v : ℂ × ℂ) :
    lightConePlus (conjPair v) = conj (lightConeMinus v) := by
  simp only [lightConePlus, lightConeMinus, conjPair, map_sub, map_mul, Complex.conj_I]
  ring
theorem lightConeMinus_conjPair (v : ℂ × ℂ) :
    lightConeMinus (conjPair v) = conj (lightConePlus v) := by
  simp only [lightConePlus, lightConeMinus, conjPair, map_add, map_mul, Complex.conj_I]
  ring
theorem boost_imag_mem_forwardTube (s : ℝ) {v : ℂ × ℂ} (hv : v ∈ forwardTube) :
    complexBoost (I * s) v ∈ forwardTube := by apply _root_.YangMills.Construction.ForwardTube.imagBoost_mem_forwardTube <;> assumption
theorem boost_imag_image_forwardTube
    (hgroup : ∀ (z z' : ℂ) (v : ℂ × ℂ),
      complexBoost z (complexBoost z' v) = complexBoost (z + z') v)
    (hid : ∀ v : ℂ × ℂ, complexBoost 0 v = v) (s : ℝ) :
    complexBoost (I * s) '' forwardTube = forwardTube := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact boost_imag_mem_forwardTube s hw
  · intro hv
    refine ⟨complexBoost (I * ((-s : ℝ) : ℂ)) v, boost_imag_mem_forwardTube _ hv, ?_⟩
    rw [hgroup, show I * (s : ℂ) + I * ((-s : ℝ) : ℂ) = 0 by push_cast; ring, hid]
theorem tubeStar_boost_imag
    (hstar : ∀ v : ℂ × ℂ, lightConePlus (tubeStar v) = conj (lightConePlus v) ∧
      lightConeMinus (tubeStar v) = conj (lightConeMinus v))
    (s : ℝ) (v : ℂ × ℂ) :
    tubeStar (complexBoost (I * s) v) = complexBoost (I * s) (tubeStar v) := by
  refine eq_of_lightCone_eq ?_ ?_
  · rw [(hstar _).1, lightConePlus_boost_imag, lightConePlus_boost_imag, (hstar _).1, map_mul,
      Complex.conj_ofReal]
  · rw [(hstar _).2, lightConeMinus_boost_imag, lightConeMinus_boost_imag, (hstar _).2, map_mul,
      Complex.conj_ofReal]
theorem cos_sin_int_mul_pi_div_two (k : ℤ) :
    (Real.cos (k * (Real.pi / 2)) = 1 ∧ Real.sin (k * (Real.pi / 2)) = 0) ∨
      (Real.cos (k * (Real.pi / 2)) = -1 ∧ Real.sin (k * (Real.pi / 2)) = 0) ∨
      (Real.cos (k * (Real.pi / 2)) = 0 ∧ Real.sin (k * (Real.pi / 2)) = 1) ∨
      (Real.cos (k * (Real.pi / 2)) = 0 ∧ Real.sin (k * (Real.pi / 2)) = -1) := by
  obtain ⟨m, r, hk, hr⟩ : ∃ m r : ℤ, k = r + m * 4 ∧ (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) :=
    ⟨k / 4, k % 4, by omega, by omega⟩
  have hx : (k : ℝ) * (Real.pi / 2) = (r : ℝ) * (Real.pi / 2) + m * (2 * Real.pi) := by
    rw [hk]
    push_cast
    ring
  rw [hx, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  rcases hr with rfl | rfl | rfl | rfl
  · left
    simp
  · right; right; left
    simp
  · right; left
    have h : ((2 : ℤ) : ℝ) * (Real.pi / 2) = Real.pi := by
      push_cast
      ring
    rw [h]
    simp
  · right; right; right
    have h : ((3 : ℤ) : ℝ) * (Real.pi / 2) = Real.pi / 2 + Real.pi := by
      push_cast
      ring
    rw [h, Real.cos_add_pi, Real.sin_add_pi]
    simp
theorem rotatedDirection_coords (θ : rightAngleMultiples) :
    rotatedDirection θ 0 = Real.cos θ ∧ rotatedDirection θ 1 = Real.sin θ := by
  constructor <;>
    simp [rotatedDirection, rotatedUnitVector_eq_cos_sin, Complex.cos_ofReal_re,
      Complex.sin_ofReal_re]
theorem plane_ext_coords {u w : RealPlane} (h₀ : u 0 = w 0) (h₁ : u 1 = w 1) : u = w := by apply _root_.YangMills.Construction.EuclideanFunctionals.HarmonicDensity.ext_of_coords <;> assumption
theorem rotatedDirection_mem_axes (θ : rightAngleMultiples) :
    rotatedDirection θ ∈ ({RealPlane.unitX, -RealPlane.unitX,
      RealPlane.unitY, -RealPlane.unitY} : Set RealPlane) := by
  obtain ⟨k, hk⟩ := θ.2
  obtain ⟨h₀, h₁⟩ := rotatedDirection_coords θ
  rw [hk] at h₀ h₁
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases cos_sin_int_mul_pi_div_two k with ⟨c, s⟩ | ⟨c, s⟩ | ⟨c, s⟩ | ⟨c, s⟩
  · left
    exact plane_ext_coords (by rw [h₀, c]; simp [RealPlane.unitX])
      (by rw [h₁, s]; simp [RealPlane.unitX])
  · right; left
    exact plane_ext_coords (by rw [h₀, c]; simp [RealPlane.unitX])
      (by rw [h₁, s]; simp [RealPlane.unitX])
  · right; right; left
    exact plane_ext_coords (by rw [h₀, c]; simp [RealPlane.unitY])
      (by rw [h₁, s]; simp [RealPlane.unitY])
  · right; right; right
    exact plane_ext_coords (by rw [h₀, c]; simp [RealPlane.unitY])
      (by rw [h₁, s]; simp [RealPlane.unitY])
theorem embedPlane_mem_rotatedForwardTube_iff
    (hform : ∀ (z : ℂ) (v : ℂ × ℂ), complexBoost z v =
      (v.1 * Complex.cos z - v.2 * Complex.sin z, v.1 * Complex.sin z + v.2 * Complex.cos z))
    (hgroup : ∀ (z z' : ℂ) (v : ℂ × ℂ),
      complexBoost z (complexBoost z' v) = complexBoost (z + z') v)
    (hid : ∀ v : ℂ × ℂ, complexBoost 0 v = v)
    (θ : rightAngleMultiples) (y : RealPlane) :
    embedPlane y ∈ rotatedForwardTube θ ↔ inner ℝ (rotatedDirection θ) y > 0 := by
  obtain ⟨h₀, h₁⟩ := rotatedDirection_coords θ
  rw [inner_eq_coord_sum, h₀, h₁]
  have key : complexBoost (-(((θ : ℝ)) : ℂ)) (embedPlane y) =
      (((y 0 * Real.cos θ + y 1 * Real.sin θ : ℝ) : ℂ),
        ((y 1 * Real.cos θ - y 0 * Real.sin θ : ℝ) : ℂ)) := by
    rw [hform]
    simp only [embedPlane, Complex.cos_neg, Complex.sin_neg]
    push_cast
    refine Prod.ext ?_ ?_
    · simp only
      ring
    · simp only
      ring
  have hiff : complexBoost (-(((θ : ℝ)) : ℂ)) (embedPlane y) ∈ forwardTube ↔
      Real.cos θ * y 0 + Real.sin θ * y 1 > 0 := by
    rw [key, mem_forwardTube_iff_abs]
    simp only [Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    constructor <;> intro h <;> linarith
  rw [← hiff]
  constructor
  · rintro ⟨w, hw, hwy⟩
    rw [← hwy, hgroup, neg_add_cancel, hid]
    exact hw
  · intro h
    exact ⟨_, h, by rw [hgroup, add_neg_cancel, hid]⟩
theorem openDiscAt_subset_planeStrip (c η : ℝ) :
    RealPlane.openDiscAt 0 (c * η) ⊆ EuclideanFunctionals.planeStrip c η := by
  intro y hy
  have h : ‖y - 0‖ < c * η := hy
  rw [sub_zero] at h
  have h₀ : ‖y 0‖ ≤ ‖y‖ := PiLp.norm_apply_le y 0
  rw [Real.norm_eq_abs] at h₀
  exact lt_of_le_of_lt h₀ h
theorem abs_arg_lt_iff_abs_im_lt {a : ℂ} (ha : 0 < a.re) {φ : ℝ} (h₀ : 0 ≤ φ)
    (h₁ : φ < Real.pi / 2) : |Complex.arg a| < φ ↔ |a.im| < a.re * Real.tan φ := by
  have harg : |Complex.arg a| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl ha)
  have ht : Real.tan (Complex.arg a) = a.im / a.re := Complex.tan_arg a
  have htan : Real.tan |Complex.arg a| = |a.im| / a.re := by
    rcases le_or_gt 0 (Complex.arg a) with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Complex.arg_nonneg_iff.1 h), ht]
    · rw [abs_of_neg h, abs_of_neg (Complex.arg_neg_iff.1 h), Real.tan_neg, ht, neg_div]
  have hmono : Real.tan |Complex.arg a| < Real.tan φ ↔ |Complex.arg a| < φ :=
    Real.strictMonoOn_tan.lt_iff_lt
      ⟨by linarith [abs_nonneg (Complex.arg a)], harg⟩ ⟨by linarith, h₁⟩
  rw [← hmono, htan, div_lt_iff₀ ha, mul_comm]
theorem re_lightConePlus_embedPlane (v : RealPlane) : (lightConePlus (embedPlane v)).re = v 0 := by
  simp [lightConePlus, embedPlane]
theorem im_lightConePlus_embedPlane (v : RealPlane) : (lightConePlus (embedPlane v)).im = v 1 := by
  simp [lightConePlus, embedPlane]
theorem tan_openingAngle_pos (φ : RealPlane.openingAngles) : 0 < Real.tan φ :=
  Real.tan_pos_of_pos_of_lt_pi_div_two φ.2.1 (by linarith [φ.2.2, Real.pi_pos])
theorem coneSector_eq (φ : RealPlane.openingAngles) :
    RealPlane.coneSector φ = {v : RealPlane | |v 1| < v 0 * Real.tan φ} := by
  have hφ : 0 ≤ (φ : ℝ) := φ.2.1.le
  have hφ' : (φ : ℝ) < Real.pi / 2 := by linarith [φ.2.2, Real.pi_pos]
  have htan := tan_openingAngle_pos φ
  ext v
  have hre := re_lightConePlus_embedPlane v
  have him := im_lightConePlus_embedPlane v
  constructor
  · rintro ⟨hv, harg⟩
    have hne : lightConePlus (embedPlane v) ≠ 0 := by
      intro h
      apply hv
      refine plane_ext_coords ?_ ?_
      · rw [← hre, h]
        simp
      · rw [← him, h]
        simp
    have hpos : 0 < (lightConePlus (embedPlane v)).re :=
      (Complex.abs_arg_lt_pi_div_two_iff.1 (harg.trans hφ')).resolve_right hne
    have h := (abs_arg_lt_iff_abs_im_lt hpos hφ hφ').1 harg
    rw [hre, him] at h
    exact h
  · intro h
    have h' : |v 1| < v 0 * Real.tan φ := h
    have hv₀ : 0 < v 0 := by
      by_contra hn
      have := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) htan.le
      linarith [abs_nonneg (v 1)]
    refine ⟨fun h₀ => ?_, (abs_arg_lt_iff_abs_im_lt (by rw [hre]; exact hv₀) hφ hφ').2
      (by rw [hre, him]; exact h')⟩
    rw [h₀] at hv₀
    simp at hv₀
theorem continuous_planeCoord (i : Fin 2) : Continuous fun v : RealPlane => v i :=
  (EuclideanSpace.proj i : RealPlane →L[ℝ] ℝ).continuous
theorem isOpen_coneSector (φ : RealPlane.openingAngles) : IsOpen (RealPlane.coneSector φ) := by
  rw [coneSector_eq]
  exact isOpen_lt (continuous_planeCoord 1).abs
    ((continuous_planeCoord 0).mul continuous_const)
theorem convex_coneSector (φ : RealPlane.openingAngles) : Convex ℝ (RealPlane.coneSector φ) := by
  have h₁ : IsLinearMap ℝ (fun v : RealPlane => v 1 - v 0 * Real.tan φ) :=
    ⟨fun v w => by simp only [PiLp.add_apply]; ring,
      fun c v => by simp only [PiLp.smul_apply, smul_eq_mul]; ring⟩
  have h₂ : IsLinearMap ℝ (fun v : RealPlane => -v 1 - v 0 * Real.tan φ) :=
    ⟨fun v w => by simp only [PiLp.add_apply]; ring,
      fun c v => by simp only [PiLp.smul_apply, smul_eq_mul]; ring⟩
  have he : RealPlane.coneSector φ = {v : RealPlane | v 1 - v 0 * Real.tan φ < 0} ∩
      {v : RealPlane | -v 1 - v 0 * Real.tan φ < 0} := by
    rw [coneSector_eq]
    ext v
    show |v 1| < v 0 * Real.tan φ ↔
      v 1 - v 0 * Real.tan φ < 0 ∧ -v 1 - v 0 * Real.tan φ < 0
    rw [abs_lt]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨a, b⟩
      exact ⟨by linarith, by linarith⟩
  rw [he]
  exact (convex_halfSpace_lt h₁ 0).inter (convex_halfSpace_lt h₂ 0)
theorem smul_mem_coneSector (φ : RealPlane.openingAngles) {v : RealPlane}
    (hv : v ∈ RealPlane.coneSector φ) {a : ℝ} (ha : 0 < a) :
    a • v ∈ RealPlane.coneSector φ := by
  rw [coneSector_eq] at hv ⊢
  have hv' : |v 1| < v 0 * Real.tan φ := hv
  show |(a • v) 1| < (a • v) 0 * Real.tan φ
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos ha]
  rw [mul_assoc]
  exact mul_lt_mul_of_pos_left hv' ha
theorem coneSector_subset_openRightHalf (φ : RealPlane.openingAngles) :
    RealPlane.coneSector φ ⊆ RealPlane.openRightHalf := by
  rw [coneSector_eq]
  intro v hv
  have hv' : |v 1| < v 0 * Real.tan φ := hv
  show 0 < v 0
  by_contra hn
  have := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) (tan_openingAngle_pos φ).le
  linarith [abs_nonneg (v 1)]
theorem neg_reflectFirst_coords (v : RealPlane) :
    (-RealPlane.reflectFirst v) 0 = v 0 ∧ (-RealPlane.reflectFirst v) 1 = -v 1 := by
  constructor <;> simp [RealPlane.reflectFirst]
theorem neg_reflectFirst_mem_coneSector (φ : RealPlane.openingAngles) {v : RealPlane}
    (hv : v ∈ RealPlane.coneSector φ) :
    -RealPlane.reflectFirst v ∈ RealPlane.coneSector φ := by
  rw [coneSector_eq] at hv ⊢
  have hv' : |v 1| < v 0 * Real.tan φ := hv
  show |(-RealPlane.reflectFirst v) 1| < (-RealPlane.reflectFirst v) 0 * Real.tan φ
  rw [(neg_reflectFirst_coords v).1, (neg_reflectFirst_coords v).2, abs_neg]
  exact hv'
theorem isOpen_pencilSet (φ : RealPlane.openingAngles) (n : ℕ) :
    IsOpen (RealPlane.pencilSet φ n) := by
  have he : RealPlane.pencilSet φ n =
      ⋂ i, (fun y => RealPlane.successiveDifferences y i) ⁻¹' RealPlane.coneSector φ := by
    ext y
    simp [RealPlane.pencilSet]
  rw [he]
  refine isOpen_iInter_of_finite fun i => (isOpen_coneSector φ).preimage ?_
  exact (continuous_apply _).sub (continuous_apply _)
theorem openingAngleCos_pos (φ : RealPlane.openingAngles) :
    RealPlane.openingAngleCos φ > 0 :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [φ.2.1, Real.pi_pos], by linarith [φ.2.2, Real.pi_pos]⟩
theorem tubeFrameStripSectorPencilFacts_holds (h : TubeStarAndBoostFacts) :
    TubeFrameStripSectorPencilFacts := by
  obtain ⟨-, ⟨hopen, hadd, hsmul, hreal⟩, ⟨hstar, hstarPlane⟩, -, hlin, hmat, hform, hplane, hhol,
    hgroup, hid⟩ := h
  refine ⟨⟨coords_eq_lightCone, isLinearMap_lightConePair, bijective_lightConePair,
      fun v => ⟨re_lightConePlus v, re_lightConeMinus v⟩⟩,
    ⟨fun t s => ⟨existsUnique_linearMap_boost hlin _, hlin _,
        fun v => ⟨lightConePlus_complexBoost _ v, lightConeMinus_complexBoost _ v⟩⟩,
      hmat, hhol, hplane, hgroup,
      fun s v => ⟨lightConePlus_boost_imag s v, lightConeMinus_boost_imag s v⟩⟩,
    ⟨Set.ext mem_forwardTube_iff_abs, Set.ext mem_closedForwardTube_iff_abs,
      lightConePair_image_forwardTube, lightConePair_image_closedForwardTube,
      hopen, convex_forwardTube, hsmul, closure_forwardTube, interior_closedForwardTube hopen,
      hadd, fun _ hv _ hw => add_mem_closedForwardTube hv hw, hreal, rfl,
      closedForwardTube_inter_realVectors⟩,
    ⟨hstar, ?_, ?_, fun v => ⟨lightConePlus_conjPair v, lightConeMinus_conjPair v⟩, ?_⟩,
    ⟨boost_imag_image_forwardTube hgroup hid, tubeStar_boost_imag hstar, hstarPlane⟩,
    fun θ => ⟨rotatedDirection_mem_axes θ, embedPlane_mem_rotatedForwardTube_iff hform hgroup hid θ⟩,
    fun c _ η _ => openDiscAt_subset_planeStrip c η,
    fun φ => ⟨coneSector_eq φ, isOpen_coneSector φ, convex_coneSector φ,
      fun _ hv _ ha => smul_mem_coneSector φ hv ha, coneSector_subset_openRightHalf φ,
      fun _ hv => neg_reflectFirst_mem_coneSector φ hv, neg_reflectFirst_coords,
      fun n _ => isOpen_pencilSet φ n, rfl, openingAngleCos_pos φ⟩⟩
  · refine image_eq_self_of_involutive tubeStar_tubeStar fun v hv => ⟨?_, ?_⟩
    · rw [(hstar v).1, Complex.conj_re]
      exact hv.1
    · rw [(hstar v).2, Complex.conj_re]
      exact hv.2
  · refine image_eq_self_of_involutive tubeStar_tubeStar fun v hv => ⟨?_, ?_⟩
    · rw [(hstar v).1, Complex.conj_re]
      exact hv.1
    · rw [(hstar v).2, Complex.conj_re]
      exact hv.2
  · refine image_eq_self_of_involutive conjPair_conjPair fun v hv => ⟨?_, ?_⟩
    · rw [lightConePlus_conjPair, Complex.conj_re]
      exact hv.2
    · rw [lightConeMinus_conjPair, Complex.conj_re]
      exact hv.1
end YangMills.Construction.ForwardTube.TubeGeometry
end
