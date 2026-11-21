import YangMills.Construction.ForwardTube.ElementaryFactsOfTheTubeFramesStripSectorAndPencils
import YangMills.Construction.RotationInvariance.DeterminationOfHolomorphicFunctionsOfTheDifferencesProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Complex (I)
open RealPlane ForwardTube MeasureTheory Filter
open Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
open scoped Topology ContDiff
namespace EuclideanFunctionals.AngleFunctionOnPencil
variable {m : SharpScale} {S : ConnFamily} {q : ℕ}
theorem norm_lightConePlus_embedPlane (d : RealPlane) :
    ‖lightConePlus (embedPlane d)‖ = ‖d‖ := by
  have h1 : ‖lightConePlus (embedPlane d)‖ ^ 2 = ‖d‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Complex.sq_norm, Complex.normSq_apply]
    simp [lightConePlus, embedPlane, Fin.sum_univ_two]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
theorem lightConeMinus_embedPlane (d : RealPlane) :
    lightConeMinus (embedPlane d) = (starRingEnd ℂ) (lightConePlus (embedPlane d)) := by
  simp [lightConePlus, lightConeMinus, embedPlane, sub_eq_add_neg]
theorem re_lightConePlus_boost (d : RealPlane) (θ s : ℝ) :
    (lightConePlus (complexBoost ((θ : ℂ) + I * (s : ℂ)) (embedPlane d))).re =
      ‖d‖ * Real.exp (-s) * Real.cos (Complex.arg (lightConePlus (embedPlane d)) + θ) := by
  have hpe : lightConePlus (embedPlane d) =
      (‖d‖ : ℂ) * Complex.exp ((Complex.arg (lightConePlus (embedPlane d)) : ℂ) * I) := by
    rw [← norm_lightConePlus_embedPlane d]
    exact (Complex.norm_mul_exp_arg_mul_I _).symm
  rw [lightConePlus_complexBoost]
  have h : Complex.exp (I * ((θ : ℂ) + I * (s : ℂ))) * lightConePlus (embedPlane d) =
      ((‖d‖ * Real.exp (-s) : ℝ) : ℂ) *
        Complex.exp (((Complex.arg (lightConePlus (embedPlane d)) + θ : ℝ) : ℂ) * I) := by
    generalize Complex.arg (lightConePlus (embedPlane d)) = β at hpe
    rw [hpe]
    push_cast
    rw [show I * ((θ : ℂ) + I * (s : ℂ)) = (θ : ℂ) * I + (-(s : ℂ)) by
      linear_combination (s : ℂ) * Complex.I_sq]
    rw [Complex.exp_add, add_mul, Complex.exp_add]
    ring
  rw [h, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
theorem re_lightConeMinus_boost (d : RealPlane) (θ s : ℝ) :
    (lightConeMinus (complexBoost ((θ : ℂ) + I * (s : ℂ)) (embedPlane d))).re =
      ‖d‖ * Real.exp s * Real.cos (Complex.arg (lightConePlus (embedPlane d)) + θ) := by
  have h := re_lightConePlus_boost d θ (-s)
  rw [neg_neg] at h
  rw [← h, lightConeMinus_complexBoost, lightConePlus_complexBoost, lightConeMinus_embedPlane]
  have he : Complex.exp (-(I * ((θ : ℂ) + I * (s : ℂ)))) =
      (starRingEnd ℂ) (Complex.exp (I * ((θ : ℂ) + I * ((-s : ℝ) : ℂ)))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_add, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [he, ← map_mul, Complex.conj_re]
theorem boost_angle_sub (t s υ : ℝ) :
    (t : ℂ) + I * (s : ℂ) - (υ : ℂ) = ((t - υ : ℝ) : ℂ) + I * (s : ℂ) := by
  push_cast
  ring
theorem sub_eq_re_add_im (ζ : ℂ) (υ : ℝ) :
    ζ - (υ : ℂ) = ((ζ.re - υ : ℝ) : ℂ) + I * (ζ.im : ℂ) := by
  conv_lhs => rw [← Complex.re_add_im ζ]
  push_cast
  ring
theorem boost_mem_forwardTube {φ₀ : openingAngles} {d : RealPlane} (hd : d ∈ coneSector φ₀)
    {θ : ℝ} (hθ : |θ| < Real.pi / 2 - (φ₀ : ℝ)) (s : ℝ) :
    complexBoost ((θ : ℂ) + I * (s : ℂ)) (embedPlane d) ∈ forwardTube := by
  have hβ := abs_lt.1 hd.2
  have hθ' := abs_lt.1 hθ
  have hcos : 0 < Real.cos (Complex.arg (lightConePlus (embedPlane d)) + θ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hβ.1, hθ'.1], by linarith [hβ.2, hθ'.2]⟩
  have hn : 0 < ‖d‖ := norm_pos_iff.2 hd.1
  refine ⟨?_, ?_⟩
  · rw [re_lightConePlus_boost]
    positivity
  · rw [re_lightConeMinus_boost]
    positivity
theorem boostTuple_mem_forwardTubePow {φ₀ : openingAngles} {y : Fin (q + 1) → RealPlane}
    (hy : y ∈ pencilSet φ₀ (q + 1)) {θ : ℝ} (hθ : |θ| < Real.pi / 2 - (φ₀ : ℝ)) (s : ℝ) :
    complexBoostTuple ((θ : ℂ) + I * (s : ℂ)) (planeTupleDiffs y) ∈ forwardTubePow q :=
  fun i _ => boost_mem_forwardTube (hy i) hθ s
def stripBranch (S : ConnFamily) (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → realLabels)
    (υ : ℝ) (ζ : ℂ) : ℂ :=
  planeKernel S φ (complexBoostTuple (ζ - (υ : ℂ)) (planeTupleDiffs y))
def verticalStrip (φ₀ : openingAngles) (υ : ℝ) : Set ℂ :=
  {ζ | |ζ.re - υ| < Real.pi / 2 - (φ₀ : ℝ)}
theorem verticalStrip_eq_inter (φ₀ : openingAngles) (υ : ℝ) :
    verticalStrip φ₀ υ = {c : ℂ | c.re < υ + (Real.pi / 2 - (φ₀ : ℝ))} ∩
      {c : ℂ | υ - (Real.pi / 2 - (φ₀ : ℝ)) < c.re} := by
  ext ζ
  simp only [verticalStrip, Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
theorem isOpen_verticalStrip (φ₀ : openingAngles) (υ : ℝ) : IsOpen (verticalStrip φ₀ υ) :=
  isOpen_lt (by fun_prop) continuous_const
theorem convex_verticalStrip (φ₀ : openingAngles) (υ : ℝ) : Convex ℝ (verticalStrip φ₀ υ) := by
  rw [verticalStrip_eq_inter]
  exact (convex_halfSpace_re_lt _).inter (convex_halfSpace_re_gt _)
theorem boostTuple_mem_of_mem_strip {φ₀ : openingAngles} {y : Fin (q + 1) → RealPlane}
    (hy : y ∈ pencilSet φ₀ (q + 1)) {υ : ℝ} {ζ : ℂ} (hζ : ζ ∈ verticalStrip φ₀ υ) :
    complexBoostTuple (ζ - (υ : ℂ)) (planeTupleDiffs y) ∈ forwardTubePow q := by
  rw [sub_eq_re_add_im]
  exact boostTuple_mem_forwardTubePow hy hζ _
theorem differentiableAt_pairTupleEquiv_boost (v : Fin q → ℂ × ℂ) (u ζ : ℂ) :
    DifferentiableAt ℂ
      (fun ζ : ℂ => pairTupleEquiv q (complexBoostTuple (ζ - u) v)) ζ := by
  rw [differentiableAt_pi]
  intro k
  obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective k
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · simp only [pairTupleEquiv_apply_fst]
    simp only [complexBoostTuple, complexBoost, ofLightConeCoords]
    fun_prop
  · simp only [pairTupleEquiv_apply_snd]
    simp only [complexBoostTuple, complexBoost, ofLightConeCoords]
    fun_prop
theorem differentiableAt_comp_boost
    (hholo : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {K : (Fin q → ℂ × ℂ) → ℂ} (hK : HolomorphicOnTuples (forwardTubePow q) K)
    (v : Fin q → ℂ × ℂ) (u ζ : ℂ) (hmem : complexBoostTuple (ζ - u) v ∈ forwardTubePow q) :
    DifferentiableAt ℂ (fun ζ : ℂ => K (complexBoostTuple (ζ - u) v)) ζ := by
  have hK' : Coordinates.ComplexCoordinates.IsHolomorphicIn
      (pairTupleEquiv q '' forwardTubePow q)
      (scalarEquiv ∘ K ∘ (pairTupleEquiv q).symm) := hK
  obtain ⟨L, hL⟩ := ((hholo.1 (q * 2) _ hK'.1).1 1 _ hK').2.2.1
    (pairTupleEquiv q (complexBoostTuple (ζ - u) v)) ⟨_, hmem, rfl⟩
  have hC := (hasFDerivAt_of_restrictScalars ℝ hL rfl).differentiableAt
  have hcomp := hC.comp ζ (differentiableAt_pairTupleEquiv_boost v u ζ)
  have h0 := differentiableAt_pi.1 hcomp 0
  have he : (fun ζ : ℂ => K (complexBoostTuple (ζ - u) v)) = fun ζ : ℂ =>
      ((scalarEquiv ∘ K ∘ (pairTupleEquiv q).symm) ∘
          fun ζ : ℂ => pairTupleEquiv q (complexBoostTuple (ζ - u) v)) ζ 0 := by
    funext ζ'
    simp [scalarEquiv]
  rw [he]
  exact h0
theorem continuousOn_of_holomorphicOnTuples {K : (Fin q → ℂ × ℂ) → ℂ}
    (hK : HolomorphicOnTuples (forwardTubePow q) K) : ContinuousOn K (forwardTubePow q) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.continuousOn_of_holomorphicOnTuples <;> assumption
theorem continuous_embedPlane : Continuous embedPlane := by apply _root_.YangMills.Construction.ForwardTube.ProductIntegralDetermination.continuous_embedPlane <;> assumption
theorem boost_boost (hfacts : ForwardTube.TubeFrameStripSectorPencilFacts)
    (z z' : ℂ) (v : ℂ × ℂ) :
    complexBoost z (complexBoost z' v) = complexBoost (z + z') v :=
  hfacts.2.1.2.2.2.2.1 z z' v
theorem boost_ofReal_embedPlane (hfacts : ForwardTube.TubeFrameStripSectorPencilFacts)
    (t : ℝ) (y : RealPlane) :
    complexBoost (t : ℂ) (embedPlane y) = embedPlane (RealPlane.rotate t y) :=
  hfacts.2.1.2.2.2.1 t y
theorem embedPlane_mem_rotatedForwardTube_iff
    (hfacts : ForwardTube.TubeFrameStripSectorPencilFacts)
    (υ : rightAngleMultiples) (y : RealPlane) :
    embedPlane y ∈ rotatedForwardTube υ ↔ inner ℝ (rotatedDirection υ) y > 0 :=
  (hfacts.2.2.2.2.2.1 υ).2 y
theorem rotate_sub_rotate (t : ℝ) (a b : RealPlane) :
    RealPlane.rotate t a - RealPlane.rotate t b = RealPlane.rotate t (a - b) := by
  ext c
  fin_cases c <;> simp [RealPlane.rotate] <;> ring
theorem successiveDifferences_mapPoints_rotate (t : ℝ) (y : Fin (q + 1) → RealPlane)
    (i : Fin q) :
    successiveDifferences (n := q + 1) (mapPoints (RealPlane.rotate t) y) i =
      RealPlane.rotate t (successiveDifferences (n := q + 1) y i) :=
  rotate_sub_rotate t _ _
def frameArg (υ : rightAngleMultiples) (y : Fin (q + 1) → RealPlane) : Fin q → ℂ × ℂ :=
  unrotate υ (embedPlaneTuple (q := q) (successiveDifferences y))
def frameKernel (S : ConnFamily) (φ : Fin (q + 1) → realLabels) (υ : rightAngleMultiples)
    (y : Fin (q + 1) → RealPlane) : ℂ :=
  planeKernel S φ (frameArg υ y)
def separatedTuples (q : ℕ) (υ : rightAngleMultiples) : Set (Fin (q + 1) → RealPlane) :=
  {y | ∀ i : Fin q, 0 < inner ℝ (rotatedDirection υ) (successiveDifferences (n := q + 1) y i)}
theorem isOpen_separatedTuples (υ : rightAngleMultiples) : IsOpen (separatedTuples q υ) := by
  have h : separatedTuples q υ = ⋂ i : Fin q, {y : Fin (q + 1) → RealPlane |
      0 < inner ℝ (rotatedDirection υ) (successiveDifferences (n := q + 1) y i)} := by
    ext y
    simp [separatedTuples]
  rw [h]
  refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ?_
  have hd : Continuous fun y : Fin (q + 1) → RealPlane =>
      successiveDifferences (n := q + 1) y i :=
    (continuous_apply _).sub (continuous_apply _)
  exact continuous_const.inner hd
theorem continuous_complexBoost (z : ℂ) : Continuous (complexBoost z) := by
  show Continuous fun v : ℂ × ℂ => complexBoost z v
  simp only [complexBoost, ofLightConeCoords, lightConePlus, lightConeMinus]
  fun_prop
theorem continuous_frameArg (υ : rightAngleMultiples) :
    Continuous (frameArg (q := q) υ) := by
  refine continuous_pi fun i => ?_
  have hd : Continuous fun y : Fin (q + 1) → RealPlane =>
      successiveDifferences (n := q + 1) y i :=
    (continuous_apply _).sub (continuous_apply _)
  exact (continuous_complexBoost _).comp (continuous_embedPlane.comp hd)
theorem frameArg_mem (hfacts : ForwardTube.TubeFrameStripSectorPencilFacts)
    {φ : Fin (q + 1) → realLabels} {υ : rightAngleMultiples}
    (hframe : PlaneKernelProps.RotatedFrameRep S φ υ) {y : Fin (q + 1) → RealPlane}
    (hy : y ∈ separatedTuples q υ) : frameArg υ y ∈ forwardTubePow q :=
  hframe.1 _ fun i _ => (embedPlane_mem_rotatedForwardTube_iff hfacts υ _).2 (hy i)
theorem continuousOn_frameKernel (hfacts : ForwardTube.TubeFrameStripSectorPencilFacts)
    {φ : Fin (q + 1) → realLabels} {υ : rightAngleMultiples}
    (hK : HolomorphicOnTuples (forwardTubePow q) (planeKernel S φ))
    (hframe : PlaneKernelProps.RotatedFrameRep S φ υ) :
    ContinuousOn (frameKernel S φ υ) (separatedTuples q υ) :=
  (continuousOn_of_holomorphicOnTuples hK).comp (continuous_frameArg υ).continuousOn
    fun _ hy => frameArg_mem hfacts hframe hy
theorem funsDirectionSeparated_of_subset {υ : rightAngleMultiples}
    {α : Fin (q + 1) → RealPlane → ℂ} (hc : ∀ i, HasCompactSupport (α i))
    (hne : ∀ i, α i ≠ 0)
    (hsub : (Set.univ.pi fun i => tsupport (α i)) ⊆ separatedTuples q υ) :
    FunsDirectionSeparated υ α := by
  have hnon : ∀ i, (tsupport (α i)).Nonempty := by
    intro i
    obtain ⟨x, hx⟩ := Function.ne_iff.1 (hne i)
    exact ⟨x, subset_tsupport _ hx⟩
  refine ⟨hc, hne, fun i => hc i, hnon, fun i hi => ?_⟩
  obtain ⟨⟨a, ha, hae⟩, -⟩ := isGreatest_supInner (rotatedDirection υ)
    (hc ⟨i, Nat.lt_of_succ_lt hi⟩) (hnon _)
  obtain ⟨⟨b, hb, hbe⟩, -⟩ := isLeast_infInner (rotatedDirection υ) (hc ⟨i + 1, hi⟩) (hnon _)
  rw [← hae, ← hbe]
  show inner ℝ (rotatedDirection υ) a < inner ℝ (rotatedDirection υ) b
  choose c hc' using hnon
  have hij : (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin (q + 1)) ≠ ⟨i + 1, hi⟩ := by
    simp [Fin.ext_iff]
  let y' : Fin (q + 1) → RealPlane :=
    Function.update (Function.update c ⟨i, Nat.lt_of_succ_lt hi⟩ a) ⟨i + 1, hi⟩ b
  have e1 : y' ⟨i + 1, hi⟩ = b := Function.update_self _ _ _
  have e2 : y' ⟨i, Nat.lt_of_succ_lt hi⟩ = a := by
    show Function.update (Function.update c _ a) _ b _ = a
    rw [Function.update_of_ne hij, Function.update_self]
  have hy : y' ∈ Set.univ.pi fun j => tsupport (α j) := by
    intro j _
    by_cases h1 : j = ⟨i + 1, hi⟩
    · subst h1
      rw [e1]
      exact hb
    · by_cases h2 : j = ⟨i, Nat.lt_of_succ_lt hi⟩
      · subst h2
        rw [e2]
        exact ha
      · show Function.update (Function.update c _ a) _ b _ ∈ _
        rw [Function.update_of_ne h1, Function.update_of_ne h2]
        exact hc' j
  have hpos := hsub hy ⟨i, by omega⟩
  have hd : successiveDifferences (n := q + 1) y' ⟨i, by omega⟩ = b - a := by
    show y' ⟨i + 1, hi⟩ - y' ⟨i, Nat.lt_of_succ_lt hi⟩ = b - a
    rw [e1, e2]
  rw [hd, inner_sub_right] at hpos
  linarith
theorem integrable_profileIntegrand {n : ℕ} {α : Fin n → RealPlane → ℂ}
    (hα : ∀ i, Continuous (α i)) (hc : ∀ i, HasCompactSupport (α i))
    {f : (Fin n → RealPlane) → ℂ}
    (hf : ContinuousOn f (Set.univ.pi fun i => tsupport (α i))) :
    Integrable (profileIntegrand α f) := by
  have hP : IsCompact (Set.univ.pi fun i => tsupport (α i)) := isCompact_univ_pi fun i => hc i
  unfold profileIntegrand
  rw [integrable_indicator_iff hP.measurableSet]
  refine ContinuousOn.integrableOn_compact hP ?_
  refine ContinuousOn.mul ?_ hf
  exact (continuous_finsetProd _ fun i _ => (hα i).comp (continuous_apply i)).continuousOn
theorem productWeightedIntegral_sub_eq_zero {φ : Fin (q + 1) → realLabels}
    {υ₁ υ₂ : rightAngleMultiples}
    (hf₁ : PlaneKernelProps.RotatedFrameRep S φ υ₁)
    (hf₂ : PlaneKernelProps.RotatedFrameRep S φ υ₂)
    (hc₁ : ContinuousOn (frameKernel S φ υ₁) (separatedTuples q υ₁))
    (hc₂ : ContinuousOn (frameKernel S φ υ₂) (separatedTuples q υ₂))
    (α : Fin (q + 1) → RealPlane → ℝ)
    (hα : IsSmoothTestFamilyIn (separatedTuples q υ₁ ∩ separatedTuples q υ₂) α) :
    productWeightedIntegral (separatedTuples q υ₁ ∩ separatedTuples q υ₂) α
      (fun y => frameKernel S φ υ₁ y - frameKernel S φ υ₂ y) = 0 := by
  obtain ⟨hsm, hcs, hsub⟩ := hα
  by_cases h0 : ∃ i, α i = 0
  · obtain ⟨i, hi⟩ := h0
    have hz : ∀ y : Fin (q + 1) → RealPlane, (∏ a, ((α a (y a) : ℝ) : ℂ)) = 0 :=
      fun y => Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    simp [productWeightedIntegral, Set.indicator, hz]
  · push Not at h0
    let β : Fin (q + 1) → RealPlane → ℂ := fun i y => (α i y : ℂ)
    have hts : ∀ i, tsupport (β i) = tsupport (α i) := by
      intro i
      unfold tsupport
      congr 1
      ext y
      simp [β, Function.mem_support]
    have hβp : ∀ i, β i ∈ complexProfiles := fun i =>
      ⟨Complex.ofRealCLM.contDiff.comp ((hsm i).of_le (by simp)),
        (hcs i).comp_left Complex.ofReal_zero⟩
    have hβc : ∀ i, HasCompactSupport (β i) := fun i => (hβp i).2
    have hβne : ∀ i, β i ≠ 0 := by
      intro i h
      apply h0 i
      funext y
      have h1 := congrFun h y
      simpa [β] using h1
    have hP : (Set.univ.pi fun i => tsupport (β i)) = Set.univ.pi fun i => tsupport (α i) := by
      simp only [hts]
    have hsub' : (Set.univ.pi fun i => tsupport (β i)) ⊆
        separatedTuples q υ₁ ∩ separatedTuples q υ₂ := hP ▸ hsub
    have ho₁ := funsDirectionSeparated_of_subset (υ := υ₁) hβc hβne
      (hsub'.trans Set.inter_subset_left)
    have ho₂ := funsDirectionSeparated_of_subset (υ := υ₂) hβc hβne
      (hsub'.trans Set.inter_subset_right)
    have eI : profileIntegral β (frameKernel S φ υ₁) =
        profileIntegral β (frameKernel S φ υ₂) :=
      (hf₁.2.2 β hβp ho₁).symm.trans (hf₂.2.2 β hβp ho₂)
    have i₁ : Integrable (profileIntegrand β (frameKernel S φ υ₁)) :=
      integrable_profileIntegrand (fun i => (hβp i).1.continuous) hβc
        (hc₁.mono (hsub'.trans Set.inter_subset_left))
    have i₂ : Integrable (profileIntegrand β (frameKernel S φ υ₂)) :=
      integrable_profileIntegrand (fun i => (hβp i).1.continuous) hβc
        (hc₂.mono (hsub'.trans Set.inter_subset_right))
    have hpt : (fun y => (separatedTuples q υ₁ ∩ separatedTuples q υ₂).indicator
        (fun y => (∏ a, ((α a (y a) : ℝ) : ℂ)) * (frameKernel S φ υ₁ y - frameKernel S φ υ₂ y))
          y) =
        fun y => profileIntegrand β (frameKernel S φ υ₁) y -
          profileIntegrand β (frameKernel S φ υ₂) y := by
      funext y
      unfold profileIntegrand
      by_cases hy : y ∈ Set.univ.pi fun i => tsupport (β i)
      · rw [Set.indicator_of_mem (hsub' hy), Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        simp only [β]
        ring
      · obtain ⟨i, hi⟩ : ∃ i, y i ∉ tsupport (β i) := by
          simpa [Set.mem_pi] using hy
        rw [hts] at hi
        have hzi : α i (y i) = 0 := image_eq_zero_of_notMem_tsupport hi
        have hz : (∏ a, ((α a (y a) : ℝ) : ℂ)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hzi])
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
        simp [Set.indicator, hz]
    unfold productWeightedIntegral
    rw [hpt, integral_sub i₁ i₂]
    exact sub_eq_zero.2 eI
theorem stripBranch_eq_ofReal (hfacts : ForwardTube.TubeFrameStripSectorPencilFacts)
    (hdens : RealPlane.DensityUniqueness.Claim)
    {φ₀ : openingAngles} {y : Fin (q + 1) → RealPlane} (hy : y ∈ pencilSet φ₀ (q + 1))
    {φ : Fin (q + 1) → realLabels}
    (hK : HolomorphicOnTuples (forwardTubePow q) (planeKernel S φ))
    (hframe : ∀ υ, PlaneKernelProps.RotatedFrameRep S φ υ) (υ₁ υ₂ : rightAngleMultiples)
    {t : ℝ} (h₁ : |t - (υ₁ : ℝ)| < Real.pi / 2 - (φ₀ : ℝ))
    (h₂ : |t - (υ₂ : ℝ)| < Real.pi / 2 - (φ₀ : ℝ)) :
    stripBranch S y φ (υ₁ : ℝ) (t : ℂ) = stripBranch S y φ (υ₂ : ℝ) (t : ℂ) := by
  have hmem : ∀ υ : rightAngleMultiples, |t - (υ : ℝ)| < Real.pi / 2 - (φ₀ : ℝ) →
      mapPoints (RealPlane.rotate t) y ∈ separatedTuples q υ := by
    intro υ h i
    rw [successiveDifferences_mapPoints_rotate]
    refine (embedPlane_mem_rotatedForwardTube_iff hfacts υ _).1 ?_
    refine ⟨_, boost_mem_forwardTube (hy i) h 0, ?_⟩
    rw [boost_boost hfacts, ← boost_ofReal_embedPlane hfacts]
    congr 1
    push_cast
    ring
  have c₁ := continuousOn_frameKernel hfacts hK (hframe υ₁)
  have c₂ := continuousOn_frameKernel hfacts hK (hframe υ₂)
  have hO : IsOpen (separatedTuples q υ₁ ∩ separatedTuples q υ₂) :=
    (isOpen_separatedTuples υ₁).inter (isOpen_separatedTuples υ₂)
  have hdiff : ContinuousOn (fun y' => frameKernel S φ υ₁ y' - frameKernel S φ υ₂ y')
      (separatedTuples q υ₁ ∩ separatedTuples q υ₂) :=
    (c₁.mono Set.inter_subset_left).sub (c₂.mono Set.inter_subset_right)
  have hz := (hdens (q + 1) (by omega) _ hO _ hdiff).1
    (fun α hα => productWeightedIntegral_sub_eq_zero (hframe υ₁) (hframe υ₂) c₁ c₂ α hα)
    (mapPoints (RealPlane.rotate t) y) ⟨hmem υ₁ h₁, hmem υ₂ h₂⟩
  have hfr : ∀ υ : rightAngleMultiples,
      frameKernel S φ υ (mapPoints (RealPlane.rotate t) y) =
        stripBranch S y φ (υ : ℝ) (t : ℂ) := by
    intro υ
    unfold frameKernel stripBranch
    congr 1
    funext i
    show complexBoost ((-(υ : ℝ) : ℝ) : ℂ) (embedPlane (successiveDifferences (n := q + 1)
        (mapPoints (RealPlane.rotate t) y) i)) =
      complexBoost ((t : ℂ) - ((υ : ℝ) : ℂ)) (embedPlane (successiveDifferences (n := q + 1) y i))
    rw [successiveDifferences_mapPoints_rotate, ← boost_ofReal_embedPlane hfacts,
      boost_boost hfacts]
    congr 1
    push_cast
    ring
  rw [← hfr, ← hfr]
  exact sub_eq_zero.1 hz
theorem differentiableAt_stripBranch
    (hholo : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {φ₀ : openingAngles} {y : Fin (q + 1) → RealPlane} (hy : y ∈ pencilSet φ₀ (q + 1))
    {φ : Fin (q + 1) → realLabels}
    (hK : HolomorphicOnTuples (forwardTubePow q) (planeKernel S φ)) {υ : ℝ} {ζ : ℂ}
    (hζ : ζ ∈ verticalStrip φ₀ υ) : DifferentiableAt ℂ (stripBranch S y φ υ) ζ :=
  differentiableAt_comp_boost hholo hK _ _ ζ (boostTuple_mem_of_mem_strip hy hζ)
theorem stripBranch_eq (hfacts : ForwardTube.TubeFrameStripSectorPencilFacts)
    (hdens : RealPlane.DensityUniqueness.Claim)
    (hholo : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {φ₀ : openingAngles} {y : Fin (q + 1) → RealPlane} (hy : y ∈ pencilSet φ₀ (q + 1))
    {φ : Fin (q + 1) → realLabels}
    (hK : HolomorphicOnTuples (forwardTubePow q) (planeKernel S φ))
    (hframe : ∀ υ, PlaneKernelProps.RotatedFrameRep S φ υ) (υ₁ υ₂ : rightAngleMultiples)
    {ζ : ℂ} (h₁ : ζ ∈ verticalStrip φ₀ (υ₁ : ℝ)) (h₂ : ζ ∈ verticalStrip φ₀ (υ₂ : ℝ)) :
    stripBranch S y φ (υ₁ : ℝ) ζ = stripBranch S y φ (υ₂ : ℝ) ζ := by
  have hU : IsOpen (verticalStrip φ₀ (υ₁ : ℝ) ∩ verticalStrip φ₀ (υ₂ : ℝ)) :=
    (isOpen_verticalStrip _ _).inter (isOpen_verticalStrip _ _)
  have hconn : IsPreconnected (verticalStrip φ₀ (υ₁ : ℝ) ∩ verticalStrip φ₀ (υ₂ : ℝ)) :=
    ((convex_verticalStrip _ _).inter (convex_verticalStrip _ _)).isPreconnected
  have a₁ : AnalyticOnNhd ℂ (stripBranch S y φ (υ₁ : ℝ))
      (verticalStrip φ₀ (υ₁ : ℝ) ∩ verticalStrip φ₀ (υ₂ : ℝ)) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_stripBranch hholo hy hK hz.1).differentiableWithinAt) hU
  have a₂ : AnalyticOnNhd ℂ (stripBranch S y φ (υ₂ : ℝ))
      (verticalStrip φ₀ (υ₁ : ℝ) ∩ verticalStrip φ₀ (υ₂ : ℝ)) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_stripBranch hholo hy hK hz.2).differentiableWithinAt) hU
  have hz₀ : ((ζ.re : ℝ) : ℂ) ∈ verticalStrip φ₀ (υ₁ : ℝ) ∩ verticalStrip φ₀ (υ₂ : ℝ) :=
    ⟨by simpa [verticalStrip] using h₁, by simpa [verticalStrip] using h₂⟩
  have hev : ∀ᶠ t : ℝ in 𝓝 ζ.re,
      stripBranch S y φ (υ₁ : ℝ) (t : ℂ) = stripBranch S y φ (υ₂ : ℝ) (t : ℂ) := by
    have o₁ : {t : ℝ | |t - (υ₁ : ℝ)| < Real.pi / 2 - (φ₀ : ℝ)} ∈ 𝓝 ζ.re :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds h₁
    have o₂ : {t : ℝ | |t - (υ₂ : ℝ)| < Real.pi / 2 - (φ₀ : ℝ)} ∈ 𝓝 ζ.re :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds h₂
    filter_upwards [o₁, o₂] with t ht₁ ht₂
    exact stripBranch_eq_ofReal hfacts hdens hy hK hframe υ₁ υ₂ ht₁ ht₂
  have hten : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] ζ.re) (𝓝[≠] ((ζ.re : ℝ) : ℂ)) :=
    tendsto_nhdsWithin_iff.2
      ⟨(Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds,
        eventually_mem_nhdsWithin.mono fun t ht h => ht (Complex.ofReal_injective h)⟩
  have hfr : ∃ᶠ z in 𝓝[≠] ((ζ.re : ℝ) : ℂ),
      stripBranch S y φ (υ₁ : ℝ) z = stripBranch S y φ (υ₂ : ℝ) z :=
    hten.frequently (hev.filter_mono nhdsWithin_le_nhds).frequently
  exact a₁.eqOn_of_preconnected_of_frequently_eq a₂ hconn hz₀ hfr ⟨h₁, h₂⟩
theorem exists_near_rightAngle (t : ℝ) :
    ∃ υ : rightAngleMultiples, |t - (υ : ℝ)| ≤ Real.pi / 4 := by
  refine ⟨⟨round (t / (Real.pi / 2)) * (Real.pi / 2), round (t / (Real.pi / 2)), rfl⟩, ?_⟩
  have h := abs_sub_round (t / (Real.pi / 2))
  have hpi := Real.pi_pos
  show |t - (round (t / (Real.pi / 2)) : ℝ) * (Real.pi / 2)| ≤ Real.pi / 4
  have e : t - (round (t / (Real.pi / 2)) : ℝ) * (Real.pi / 2) =
      (t / (Real.pi / 2) - round (t / (Real.pi / 2))) * (Real.pi / 2) := by
    field_simp
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / 2)]
  nlinarith
theorem mem_verticalStrip_of_le {φ₀ : openingAngles} {υ : ℝ} {ζ : ℂ}
    (h : |ζ.re - υ| ≤ Real.pi / 4) : ζ ∈ verticalStrip φ₀ υ := by
  have := φ₀.2.2
  show |ζ.re - υ| < Real.pi / 2 - (φ₀ : ℝ)
  linarith
def gluedBranch (S : ConnFamily) (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → realLabels)
    (ζ : ℂ) : ℂ :=
  stripBranch S y φ ((Classical.choose (exists_near_rightAngle ζ.re) : rightAngleMultiples) : ℝ) ζ
theorem entire_of_differentiable {a : ℂ → ℂ} (h : Differentiable ℂ a) : Entire a := by
  have hfun : (scalarEquiv ∘ a ∘ scalarEquiv.symm) =
      fun (w : Coordinates.ComplexCoordinates 1) (_ : Fin 1) => a (w 0) := by
    funext w j
    simp [scalarEquiv]
  show Coordinates.ComplexCoordinates.IsHolomorphicIn (scalarEquiv '' Set.univ)
    (scalarEquiv ∘ a ∘ scalarEquiv.symm)
  rw [hfun]
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.image_univ, Equiv.range_eq_univ]
    exact isOpen_univ
  · exact (continuous_pi fun _ => h.continuous.comp (continuous_apply 0)).continuousOn
  · intro b _ j
    refine Eventually.of_forall fun ζ => ?_
    rw [differentiableAt_pi]
    intro _
    have hin : DifferentiableAt ℂ
        (fun ζ : ℂ => b 0 + ζ * Coordinates.ComplexCoordinates.stdBasisVector j 0) ζ := by
      fun_prop
    exact (h _).comp ζ hin
theorem isAngleFunction_gluedBranch (hfacts : ForwardTube.TubeFrameStripSectorPencilFacts)
    (hdens : RealPlane.DensityUniqueness.Claim)
    (hholo : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {φ₀ : openingAngles} {y : Fin (q + 1) → RealPlane} (hy : y ∈ pencilSet φ₀ (q + 1))
    {φ : Fin (q + 1) → realLabels}
    (hK : HolomorphicOnTuples (forwardTubePow q) (planeKernel S φ))
    (hframe : ∀ υ, PlaneKernelProps.RotatedFrameRep S φ υ) :
    IsAngleFunction S φ₀ y φ (gluedBranch S y φ) := by
  have hval : ∀ (υ : rightAngleMultiples) (ζ : ℂ), ζ ∈ verticalStrip φ₀ (υ : ℝ) →
      gluedBranch S y φ ζ = stripBranch S y φ (υ : ℝ) ζ := fun υ ζ hζ =>
    stripBranch_eq hfacts hdens hholo hy hK hframe _ υ
      (mem_verticalStrip_of_le (Classical.choose_spec (exists_near_rightAngle ζ.re))) hζ
  refine ⟨entire_of_differentiable fun ζ => ?_, fun υ t s h => ?_⟩
  · obtain ⟨υ, hυ⟩ := exists_near_rightAngle ζ.re
    have hζ : ζ ∈ verticalStrip φ₀ (υ : ℝ) := mem_verticalStrip_of_le hυ
    have hev : gluedBranch S y φ =ᶠ[𝓝 ζ] stripBranch S y φ (υ : ℝ) := by
      filter_upwards [(isOpen_verticalStrip φ₀ (υ : ℝ)).mem_nhds hζ] with z hz
      exact hval υ z hz
    exact (differentiableAt_stripBranch hholo hy hK hζ).congr_of_eventuallyEq hev
  · have hζ : (t : ℂ) + I * (s : ℂ) ∈ verticalStrip φ₀ (υ : ℝ) := by
      simpa [verticalStrip] using h
    exact hval υ _ hζ
theorem apply_eq_stripBranch {φ₀ : openingAngles} {y : Fin (q + 1) → RealPlane}
    {φ : Fin (q + 1) → realLabels} {a : ℂ → ℂ} (ha : IsAngleFunction S φ₀ y φ a)
    (υ : rightAngleMultiples) {ζ : ℂ} (hζ : ζ ∈ verticalStrip φ₀ (υ : ℝ)) :
    a ζ = stripBranch S y φ (υ : ℝ) ζ := by
  have h := ha.apply_eq_planeKernel υ ζ.re ζ.im hζ
  have e : (ζ.re : ℂ) + I * (ζ.im : ℂ) = ζ := by
    rw [mul_comm]
    exact Complex.re_add_im ζ
  rw [e] at h
  exact h
theorem re_boost_lower_bound {φ₀ : openingAngles} {d : RealPlane} (hd : d ∈ coneSector φ₀)
    {r : ℝ} (hr : r ≤ ‖d‖) (hr0 : 0 ≤ r) {θ : ℝ} (hθ : |θ| ≤ Real.pi / 4) (s : ℝ) :
    openingAngleCos φ₀ * r * Real.exp (-|s|) ≤
        (lightConePlus (complexBoost ((θ : ℂ) + I * (s : ℂ)) (embedPlane d))).re ∧
      openingAngleCos φ₀ * r * Real.exp (-|s|) ≤
        (lightConeMinus (complexBoost ((θ : ℂ) + I * (s : ℂ)) (embedPlane d))).re := by
  have hφ := φ₀.2
  have hβ := hd.2
  have hpi := Real.pi_pos
  have hc0 : 0 < openingAngleCos φ₀ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have habs : |Complex.arg (lightConePlus (embedPlane d)) + θ| ≤ (φ₀ : ℝ) + Real.pi / 4 :=
    (abs_add_le _ _).trans (by linarith)
  have hcos : openingAngleCos φ₀ ≤ Real.cos (Complex.arg (lightConePlus (embedPlane d)) + θ) := by
    rw [← Real.cos_abs (Complex.arg (lightConePlus (embedPlane d)) + θ)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [hφ.2]) habs
  have hE : ∀ x : ℝ, -|s| ≤ x → openingAngleCos φ₀ * r * Real.exp (-|s|) ≤
      ‖d‖ * Real.exp x * Real.cos (Complex.arg (lightConePlus (embedPlane d)) + θ) := by
    intro x hx
    have e1 : Real.exp (-|s|) ≤ Real.exp x := Real.exp_le_exp.2 hx
    calc openingAngleCos φ₀ * r * Real.exp (-|s|)
        ≤ Real.cos (Complex.arg (lightConePlus (embedPlane d)) + θ) * ‖d‖ * Real.exp x :=
          mul_le_mul (mul_le_mul hcos hr hr0 (hc0.le.trans hcos)) e1 (Real.exp_pos _).le
            (mul_nonneg (hc0.le.trans hcos) (norm_nonneg _))
      _ = ‖d‖ * Real.exp x * Real.cos (Complex.arg (lightConePlus (embedPlane d)) + θ) := by
          ring
  refine ⟨?_, ?_⟩
  · rw [re_lightConePlus_boost]
    exact hE _ (by linarith [le_abs_self s])
  · rw [re_lightConeMinus_boost]
    exact hE _ (by linarith [neg_abs_le s])
theorem minGapLength_le (hq : 1 ≤ q) (y : Fin (q + 1) → RealPlane) (i : Fin q) :
    minGapLength (Nat.succ_le_succ hq) y ≤ ‖successiveDifferences (n := q + 1) y i‖ :=
  Finset.inf'_le _ (Finset.mem_univ _)
theorem minGapLength_pos (hq : 1 ≤ q) {φ₀ : openingAngles} {y : Fin (q + 1) → RealPlane}
    (hy : y ∈ pencilSet φ₀ (q + 1)) : 0 < minGapLength (Nat.succ_le_succ hq) y := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin q)),
      0 < ‖successiveDifferences (n := q + 1) y i‖ :=
    fun i _ => norm_pos_iff.2 (hy i).1
  exact (Finset.lt_inf'_iff _).2 h
theorem rpowPos_neg_antitone {x z p : ℝ} (hx : 0 < x) (hxz : x ≤ z) (hp : 0 ≤ p) :
    RealPower.rpowPos z (-p) ≤ RealPower.rpowPos x (-p) := by
  unfold RealPower.rpowPos
  rw [if_pos hx, if_pos (hx.trans_le hxz)]
  refine Real.exp_le_exp.2 ?_
  have := Real.log_le_log hx hxz
  nlinarith
theorem rpowPos_pos {x : ℝ} (hx : 0 < x) (p : ℝ) : 0 < RealPower.rpowPos x p := by
  unfold RealPower.rpowPos
  rw [if_pos hx]
  exact Real.exp_pos _
theorem rpowPos_min_le {ρ p σ : ℝ} (hρ : 0 < ρ) (hp : 0 ≤ p) (hσ : 0 ≤ σ) :
    RealPower.rpowPos (min 1 (ρ * Real.exp (-σ))) (-p) ≤
      max 1 (RealPower.rpowPos ρ (-p)) * Real.exp (p * σ) := by
  by_cases h : 1 ≤ ρ * Real.exp (-σ)
  · rw [min_eq_left h]
    have h1 : RealPower.rpowPos 1 (-p) = 1 := by
      simp [RealPower.rpowPos]
    rw [h1]
    have a : 1 ≤ max 1 (RealPower.rpowPos ρ (-p)) := le_max_left _ _
    have b : 1 ≤ Real.exp (p * σ) := Real.one_le_exp (by positivity)
    nlinarith
  · have h' : ρ * Real.exp (-σ) ≤ 1 := (not_le.1 h).le
    rw [min_eq_right h']
    have hx : 0 < ρ * Real.exp (-σ) := mul_pos hρ (Real.exp_pos _)
    have e : RealPower.rpowPos (ρ * Real.exp (-σ)) (-p) =
        RealPower.rpowPos ρ (-p) * Real.exp (p * σ) := by
      unfold RealPower.rpowPos
      rw [if_pos hx, if_pos hρ, Real.log_mul hρ.ne' (Real.exp_pos _).ne', Real.log_exp,
        ← Real.exp_add]
      congr 1
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
theorem min_le_tubeMargin (hq : 1 ≤ q) {v : Fin q → ℂ × ℂ} {ρ : ℝ}
    (h : ∀ i, ρ ≤ (lightConePlus (v i)).re ∧ ρ ≤ (lightConeMinus (v i)).re) :
    min 1 ρ ≤ tubeMargin v := by
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  refine le_min (min_le_left _ _) (le_ciInf fun i => ?_)
  exact (min_le_right _ _).trans (le_min (h i).1 (h i).2)
theorem norm_le_of_margin (hq : 1 ≤ q) {C p ρ σ : ℝ} {K : (Fin q → ℂ × ℂ) → ℂ}
    {v : Fin q → ℂ × ℂ} (hρ : 0 < ρ) (hp : 0 ≤ p)
    (hb : ‖K v‖ ≤ C * RealPower.rpowPos (tubeMargin v) (-p))
    (hC : 0 ≤ C)
    (hm : ∀ i, ρ * Real.exp (-σ) ≤ (lightConePlus (v i)).re ∧
      ρ * Real.exp (-σ) ≤ (lightConeMinus (v i)).re) :
    ‖K v‖ ≤ C * RealPower.rpowPos (min 1 (ρ * Real.exp (-σ))) (-p) := by
  have hmin : 0 < min 1 (ρ * Real.exp (-σ)) := lt_min one_pos (mul_pos hρ (Real.exp_pos _))
  exact hb.trans (mul_le_mul_of_nonneg_left
    (rpowPos_neg_antitone hmin (min_le_tubeMargin hq hm) hp) hC)
theorem holds (hkernels : PlaneKernelProps.Holds)
    (hfacts : ForwardTube.TubeFrameStripSectorPencilFacts)
    (hdens : RealPlane.DensityUniqueness.Claim)
    (hholo : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) : Holds := by
  intro m S d q hq y hy φ
  obtain ⟨hker, -, hbound, hreal, -, hframe⟩ := hkernels m S d q hq φ
  have hK := hker.holomorphic
  have hP : IsAngleFunction S d.angle y φ (angleFunction S d.angle y φ) :=
    Classical.epsilon_spec
      ⟨_, isAngleFunction_gluedBranch hfacts hdens hholo hy hK hframe⟩
  have hrealAll : ∀ t : ℝ, (angleFunction S d.angle y φ (t : ℂ)).im = 0 := by
    intro t
    obtain ⟨υ, hυ⟩ := exists_near_rightAngle t
    have hs : (t : ℂ) ∈ verticalStrip d.angle (υ : ℝ) :=
      mem_verticalStrip_of_le (by simpa using hυ)
    rw [apply_eq_stripBranch hP υ hs]
    refine hreal.2 _ ⟨boostTuple_mem_of_mem_strip hy hs, fun i => RealPlane.rotate (t - (υ : ℝ))
      (successiveDifferences (n := q + 1) y i), fun i => ?_⟩
    show complexBoost ((t : ℂ) - ((υ : ℝ) : ℂ))
        (embedPlane (successiveDifferences (n := q + 1) y i)) =
      embedPlane (RealPlane.rotate (t - (υ : ℝ)) (successiveDifferences (n := q + 1) y i))
    rw [← boost_ofReal_embedPlane hfacts]
    congr 1
    push_cast
    rfl
  refine ⟨?_, hP, ?_, ?_, ?_, ?_⟩
  · intro υ t s h
    rw [boost_angle_sub]
    exact boostTuple_mem_forwardTubePow hy h s
  · intro a ha
    funext ζ
    obtain ⟨υ, hυ⟩ := exists_near_rightAngle ζ.re
    have hs : ζ ∈ verticalStrip d.angle (υ : ℝ) := mem_verticalStrip_of_le hυ
    rw [apply_eq_stripBranch ha υ hs, apply_eq_stripBranch hP υ hs]
  · refine ⟨fun t ht => ⟨?_, hrealAll t⟩, fun s => ?_, ?_, hrealAll⟩
    · have hs : (t : ℂ) ∈ verticalStrip d.angle (rightAngleZero : ℝ) := by
        show |((t : ℂ)).re - 0| < _
        simpa using ht
      rw [apply_eq_stripBranch hP rightAngleZero hs]
      show planeKernel S φ (complexBoostTuple ((t : ℂ) - ((0 : ℝ) : ℂ)) _) = _
      congr 1
      funext i
      show complexBoost ((t : ℂ) - ((0 : ℝ) : ℂ))
          (embedPlane (successiveDifferences (n := q + 1) y i)) =
        embedPlane (successiveDifferences (n := q + 1) (mapPoints (RealPlane.rotate t) y) i)
      rw [successiveDifferences_mapPoints_rotate, ← boost_ofReal_embedPlane hfacts,
        Complex.ofReal_zero, sub_zero]
    · have hs : I * (s : ℂ) ∈ verticalStrip d.angle (rightAngleZero : ℝ) := by
        show |(I * (s : ℂ)).re - 0| < Real.pi / 2 - (d.angle : ℝ)
        have := d.angle.2.2
        have hpi := Real.pi_pos
        simp
        linarith
      rw [apply_eq_stripBranch hP rightAngleZero hs]
      show planeKernel S φ (complexBoostTuple (I * (s : ℂ) - ((0 : ℝ) : ℂ)) _) = _
      rw [Complex.ofReal_zero, sub_zero]
    · funext ζ
      obtain ⟨υ, hυ⟩ := exists_near_rightAngle ζ.re
      have hs : ζ ∈ verticalStrip d.angle (υ : ℝ) := mem_verticalStrip_of_le hυ
      obtain ⟨k, hk⟩ := υ.2
      let υ' : rightAngleMultiples :=
        ⟨(υ : ℝ) + Real.pi / 2, k + 1, by rw [hk]; push_cast; ring⟩
      have hs' : ζ + ((Real.pi / 2 : ℝ) : ℂ) ∈ verticalStrip d.angle (υ' : ℝ) := by
        show |(ζ + ((Real.pi / 2 : ℝ) : ℂ)).re - ((υ : ℝ) + Real.pi / 2)| < _
        have e : (ζ + ((Real.pi / 2 : ℝ) : ℂ)).re - ((υ : ℝ) + Real.pi / 2) =
            ζ.re - (υ : ℝ) := by
          simp only [Complex.add_re, Complex.ofReal_re]
          ring
        rw [e]
        exact hs
      rw [apply_eq_stripBranch hP υ' hs', apply_eq_stripBranch hP υ hs]
      unfold stripBranch
      congr 2
      show ζ + ((Real.pi / 2 : ℝ) : ℂ) - (((υ : ℝ) + Real.pi / 2 : ℝ) : ℂ) = ζ - ((υ : ℝ) : ℂ)
      push_cast
      ring
  · intro υ t s ht i
    rw [boost_angle_sub]
    exact re_boost_lower_bound (hy i) (minGapLength_le hq y i) (minGapLength_pos hq hy).le ht s
  · intro t s
    have hφ := d.angle.2
    have hpi := Real.pi_pos
    have hc0 : 0 < openingAngleCos d.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
    have hρ : 0 < openingAngleCos d.angle * minGapLength (Nat.succ_le_succ hq) y :=
      mul_pos hc0 (minGapLength_pos hq hy)
    have hp : 0 ≤ d.base.expo * ((q + 1 : ℕ) : ℝ) :=
      mul_nonneg d.base.expo_pos.le (Nat.cast_nonneg _)
    have hmarg : ∀ (θ s' : ℝ), |θ| ≤ Real.pi / 4 → ∀ i : Fin q,
        openingAngleCos d.angle * minGapLength (Nat.succ_le_succ hq) y * Real.exp (-|s'|) ≤
            (lightConePlus (complexBoostTuple ((θ : ℂ) + I * (s' : ℂ))
              (planeTupleDiffs y) i)).re ∧
          openingAngleCos d.angle * minGapLength (Nat.succ_le_succ hq) y * Real.exp (-|s'|) ≤
            (lightConeMinus (complexBoostTuple ((θ : ℂ) + I * (s' : ℂ))
              (planeTupleDiffs y) i)).re :=
      fun θ s' hθ i => re_boost_lower_bound (hy i) (minGapLength_le hq y i)
        (minGapLength_pos hq hy).le hθ s'
    have hC : 0 ≤ ∏ i, d.base.labelConst (φ i) := by
      have hv := boostTuple_mem_forwardTubePow (θ := 0) hy (by
        have : (0 : ℝ) < Real.pi / 2 - (d.angle : ℝ) := by linarith [hφ.2]
        simpa using this) 0
      have hb := hbound _ hv
      have hmin : 0 < min 1 (openingAngleCos d.angle * minGapLength (Nat.succ_le_succ hq) y *
          Real.exp (-|(0 : ℝ)|)) := lt_min one_pos (mul_pos hρ (Real.exp_pos _))
      have hd0 := hmin.trans_le (min_le_tubeMargin hq (hmarg 0 0 (by simp; positivity)))
      exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hb) (rpowPos_pos hd0 _)
    obtain ⟨υ, hυ⟩ := exists_near_rightAngle t
    have hs : (t : ℂ) + I * (s : ℂ) ∈ verticalStrip d.angle (υ : ℝ) :=
      mem_verticalStrip_of_le (by simpa using hυ)
    refine ⟨?_, ?_⟩
    · rw [apply_eq_stripBranch hP υ hs]
      have hv := boostTuple_mem_of_mem_strip hy hs
      refine norm_le_of_margin hq hρ hp (hbound _ hv) hC fun i => ?_
      have e := boost_angle_sub t s (υ : ℝ)
      rw [e]
      exact hmarg (t - (υ : ℝ)) s hυ i
    · exact (mul_le_mul_of_nonneg_left (rpowPos_min_le hρ hp (abs_nonneg s)) hC).trans_eq
        (mul_assoc _ _ _).symm
end EuclideanFunctionals.AngleFunctionOnPencil
end YangMills.Construction
end
