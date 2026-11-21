import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMomentsProof
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAndTwoFormsOfReflectionPositivityProof
import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirrorProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.ComplexAnalysis.JoukowskiRadiusProperties
import YangMills.Construction.ComplexAnalysis.RealAnalyticInCoordinates
import YangMills.Construction.ComplexAnalysis.SeparateToJointHolomorphy
import YangMills.Construction.TwoPoints.OneFieldSpaceAndSlidesAlongTheNormalProof
import YangMills.Construction.TwoPoints.TranslatePairingIsAnalyticNearAPoint
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints.ShiftPairingLocallyAnalytic
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
open YangMills.Construction.Coordinates.ComplexCoordinates YangMills.Construction.Ellipses YangMills.Construction.JointHolomorphy
theorem euclidNorm_eq_norm_toLp (x : AmbientSpace) :
    euclidNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.TwoPoints.MollifierBump.euclidNorm_eq_norm_toLp <;> assumption
theorem euclidNorm_nonneg (x : AmbientSpace) : 0 ≤ euclidNorm x := Real.sqrt_nonneg _
theorem euclidNorm_add_le (x y : AmbientSpace) :
    euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.euclidNorm_add_le <;> assumption
theorem euclidNorm_smul (c : ℝ) (x : AmbientSpace) : euclidNorm (c • x) = |c| * euclidNorm x := by apply _root_.YangMills.DeltaSharedProofs.p501477 <;> assumption
theorem euclidNorm_neg (x : AmbientSpace) : euclidNorm (-x) = euclidNorm x := by
  simp [euclidNorm]
theorem euclidNorm_zero : euclidNorm (0 : AmbientSpace) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
theorem euclidNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → AmbientSpace) :
    euclidNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, euclidNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [euclidNorm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (euclidNorm_add_le _ _).trans (by linarith)
theorem abs_euclidDot_le (n x : AmbientSpace) :
    |euclidDot n x| ≤ euclidNorm n * euclidNorm x := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.abs_inner_le_euclidNormVec_mul <;> assumption
theorem euclidDot_add (n x y : AmbientSpace) :
    euclidDot n (x + y) = euclidDot n x + euclidDot n y := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.euclidDot_add <;> assumption
theorem euclidDot_smul (n x : AmbientSpace) (c : ℝ) :
    euclidDot n (c • x) = c * euclidDot n x := by apply _root_.YangMills.Construction.TwoPoints.ReflectedSpaceSlides.dot_smul_right <;> assumption
theorem add_euclidDot (n n' x : AmbientSpace) :
    euclidDot (n + n') x = euclidDot n x + euclidDot n' x := by apply _root_.YangMills.Construction.LatticeConventions.LatticeMirrorsAndReflectionPositivity.euclidDot_add_left <;> assumption
theorem smul_euclidDot (n x : AmbientSpace) (c : ℝ) :
    euclidDot (c • n) x = c * euclidDot n x := by
  simp only [euclidDot, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring
theorem coordVec_apply (μ i : Fin 4) :
    coordVec μ i = if i = μ then 1 else 0 := by
  simp [YangMills.Construction.PeriodicLattice.coordVec, Pi.single_apply]
theorem euclidDot_coordVec (μ : Fin 4) (x : AmbientSpace) :
    euclidDot (coordVec μ) x = x μ := by
  simp [euclidDot, coordVec_apply]
theorem euclidNorm_eq_sqrt_euclidDot (x : AmbientSpace) :
    euclidNorm x = Real.sqrt (euclidDot x x) := by
  simp only [euclidNorm, euclidDot, sq]
def signOne (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1
theorem signOne_eq_or (a : ℝ) : signOne a = 1 ∨ signOne a = -1 := by
  unfold signOne
  split_ifs <;> simp
theorem signOne_mul_self (a : ℝ) : signOne a * a = |a| := by
  unfold signOne
  split_ifs with h
  · rw [abs_of_nonneg h, one_mul]
  · rw [abs_of_neg (not_le.1 h)]
    ring
theorem signOne_mul_signOne (a : ℝ) : signOne a * signOne a = 1 := by
  rcases signOne_eq_or a with h | h <;> rw [h] <;> norm_num
theorem signOne_ne_zero (a : ℝ) : signOne a ≠ 0 := by
  rcases signOne_eq_or a with h | h <;> rw [h] <;> norm_num
def frameVec (ξ : AmbientSpace) (μ ν : Fin 4) : AmbientSpace :=
  if ν = μ then signOne (ξ μ) • coordVec μ
  else (Real.sqrt 2)⁻¹ • (signOne (ξ μ) • coordVec μ + signOne (ξ ν) • coordVec ν)
theorem frameVec_mem (ξ : AmbientSpace) (μ ν : Fin 4) : frameVec ξ μ ν ∈ reflectionNormals := by
  unfold frameVec
  split_ifs with h
  · exact Or.inl ⟨μ, _, signOne_eq_or _, rfl⟩
  · rcases lt_or_gt_of_ne h with h' | h'
    · refine Or.inr ⟨ν, μ, _, _, h', signOne_eq_or (ξ ν), signOne_eq_or (ξ μ), ?_⟩
      rw [add_comm]
    · exact Or.inr ⟨μ, ν, _, _, h', signOne_eq_or _, signOne_eq_or _, rfl⟩
theorem inv_sqrt_two_mul_self : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num
theorem euclidNorm_frameVec (ξ : AmbientSpace) (μ ν : Fin 4) : euclidNorm (frameVec ξ μ ν) = 1 := by
  rw [euclidNorm_eq_sqrt_euclidDot]
  have hσ := signOne_mul_signOne (ξ μ)
  have hσ' := signOne_mul_signOne (ξ ν)
  have h1 : euclidDot (frameVec ξ μ ν) (frameVec ξ μ ν) = 1 := by
    unfold frameVec
    split_ifs with h
    · simp only [smul_euclidDot, euclidDot_smul, euclidDot_coordVec, coordVec_apply, if_true]
      linarith
    · have hs := inv_sqrt_two_mul_self
      simp only [smul_euclidDot, add_euclidDot, euclidDot_smul, euclidDot_add, euclidDot_coordVec,
        coordVec_apply, if_true, if_neg h, if_neg (Ne.symm h)]
      linear_combination (signOne (ξ μ) * signOne (ξ μ) + signOne (ξ ν) * signOne (ξ ν)) * hs +
        1 / 2 * hσ + 1 / 2 * hσ'
  rw [h1, Real.sqrt_one]
theorem euclidNorm_le_two_mul_abs (ξ : AmbientSpace) (μ : Fin 4) (h : ∀ ν, |ξ ν| ≤ |ξ μ|) :
    euclidNorm ξ ≤ 2 * |ξ μ| := by
  unfold euclidNorm
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h' : ∀ ν, ξ ν ^ 2 ≤ |ξ μ| ^ 2 := fun ν => by
    rw [← sq_abs (ξ ν)]
    exact pow_le_pow_left₀ (abs_nonneg _) (h ν) 2
  rw [Fin.sum_univ_four, mul_pow]
  linarith [h' 0, h' 1, h' 2, h' 3]
theorem le_inv_sqrt_two : (17 / 32 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by
  have hs : Real.sqrt 2 ≤ 32 / 17 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have h0 : 0 < Real.sqrt 2 := by positivity
  rw [show (17 / 32 : ℝ) = (32 / 17)⁻¹ by norm_num]
  exact inv_anti₀ h0 hs
theorem le_euclidDot_frameVec (ξ : AmbientSpace) (μ ν : Fin 4) (h : ∀ ν, |ξ ν| ≤ |ξ μ|) :
    17 / 64 * euclidNorm ξ ≤ euclidDot (frameVec ξ μ ν) ξ := by
  have h2 := euclidNorm_le_two_mul_abs ξ μ h
  have h0 := euclidNorm_nonneg ξ
  unfold frameVec
  split_ifs with hν
  · rw [smul_euclidDot, euclidDot_coordVec, signOne_mul_self]
    linarith
  · rw [smul_euclidDot, add_euclidDot, smul_euclidDot, smul_euclidDot, euclidDot_coordVec,
      euclidDot_coordVec, signOne_mul_self, signOne_mul_self]
    have hs := le_inv_sqrt_two
    have ha := abs_nonneg (ξ μ)
    have hb := abs_nonneg (ξ ν)
    nlinarith [mul_le_mul_of_nonneg_right hs (add_nonneg ha hb)]
theorem frameVec_apply_of_ne (ξ : AmbientSpace) {μ ν : Fin 4} (h : ν ≠ μ) (l : Fin 4) :
    frameVec ξ μ l ν = if l = ν then (Real.sqrt 2)⁻¹ * signOne (ξ ν) else 0 := by
  unfold frameVec
  by_cases hl : l = μ
  · have hlν : ¬l = ν := fun e => h (e.symm.trans hl)
    subst hl
    simp [coordVec_apply, h, hlν]
  · by_cases hlν : l = ν
    · subst hlν
      simp [hl, coordVec_apply]
    · simp [hl, hlν, coordVec_apply, h, Ne.symm hlν]
def frameMap (ξ : AmbientSpace) (μ : Fin 4) : (Fin 4 → ℝ) →ₗ[ℝ] AmbientSpace :=
  ∑ ν, (LinearMap.proj ν : (Fin 4 → ℝ) →ₗ[ℝ] ℝ).smulRight (frameVec ξ μ ν)
theorem frameMap_apply (ξ : AmbientSpace) (μ : Fin 4) (u : Fin 4 → ℝ) :
    frameMap ξ μ u = ∑ ν, u ν • frameVec ξ μ ν := by
  simp [frameMap, LinearMap.sum_apply]
theorem frameMap_injective (ξ : AmbientSpace) (μ : Fin 4) : Function.Injective (frameMap ξ μ) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  rw [frameMap_apply] at hu
  have hne : ∀ ν, ν ≠ μ → u ν = 0 := by
    intro ν hν
    have h1 := congrFun hu ν
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      frameVec_apply_of_ne ξ hν] at h1
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    have hs : (Real.sqrt 2)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    exact (mul_eq_zero.1 h1).resolve_right (mul_ne_zero hs (signOne_ne_zero _))
  have hμ : u μ = 0 := by
    have h1 := congrFun hu μ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    rw [Finset.sum_eq_single μ (fun ν _ hν => by rw [hne ν hν, zero_mul]) (by simp)] at h1
    have h2 : frameVec ξ μ μ μ = signOne (ξ μ) := by
      simp [frameVec, coordVec_apply]
    rw [h2] at h1
    exact (mul_eq_zero.1 h1).resolve_right (signOne_ne_zero _)
  funext ν
  by_cases h : ν = μ
  · rw [h, hμ]; rfl
  · rw [hne ν h]; rfl
theorem frameMap_single (ξ : AmbientSpace) (μ j : Fin 4) :
    frameMap ξ μ (Pi.single j 1) = frameVec ξ μ j := by
  simp [frameMap_apply, Pi.single_apply]
theorem euclidNorm_frameMap_le (ξ : AmbientSpace) (μ : Fin 4) (u : Fin 4 → ℝ) :
    euclidNorm (frameMap ξ μ u) ≤ ∑ ν, |u ν| := by
  rw [frameMap_apply]
  refine (euclidNorm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun ν _ => by rw [euclidNorm_smul, euclidNorm_frameVec, mul_one]
def cubeChart (ξ : AmbientSpace) (μ : Fin 4) (ε : ℝ) (p : AmbientSpace) (u : Fin 4 → ℝ) :
    AmbientSpace :=
  p + (ε / 2) • frameMap ξ μ u
def frameMapInv (ξ : AmbientSpace) (μ : Fin 4) : AmbientSpace →L[ℝ] (Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap
    (LinearEquiv.ofInjectiveEndo (frameMap ξ μ) (frameMap_injective ξ μ)).symm.toLinearMap
theorem frameMap_frameMapInv (ξ : AmbientSpace) (μ : Fin 4) (y : AmbientSpace) :
    frameMap ξ μ (frameMapInv ξ μ y) = y :=
  (LinearEquiv.ofInjectiveEndo (frameMap ξ μ) (frameMap_injective ξ μ)).apply_symm_apply y
def cubeChartInv (ξ : AmbientSpace) (μ : Fin 4) (ε : ℝ) (p y : AmbientSpace) : Fin 4 → ℝ :=
  (2 / ε) • frameMapInv ξ μ (y - p)
theorem cubeChart_cubeChartInv (ξ : AmbientSpace) (μ : Fin 4) {ε : ℝ} (hε : ε ≠ 0)
    (p y : AmbientSpace) :
    cubeChart ξ μ ε p (cubeChartInv ξ μ ε p y) = y := by
  simp only [cubeChart, cubeChartInv, map_smul, frameMap_frameMapInv, smul_smul]
  rw [show ε / 2 * (2 / ε) = 1 by field_simp, one_smul]
  abel
theorem continuous_cubeChartInv (ξ : AmbientSpace) (μ : Fin 4) (ε : ℝ) (p : AmbientSpace) :
    Continuous (cubeChartInv ξ μ ε p) := by
  unfold cubeChartInv
  exact ((frameMapInv ξ μ).continuous.comp
    (continuous_id.sub continuous_const)).const_smul (2 / ε)
theorem analyticAt_cubeChartInv (ξ : AmbientSpace) (μ : Fin 4) (ε : ℝ) (p y : AmbientSpace) :
    AnalyticAt ℝ (cubeChartInv ξ μ ε p) y := by
  have h : cubeChartInv ξ μ ε p = fun y' => ((2 / ε) • frameMapInv ξ μ) (y' - p) := by
    funext y'
    simp [cubeChartInv]
  rw [h]
  exact AnalyticAt.comp (g := (2 / ε) • frameMapInv ξ μ) (f := fun y' : AmbientSpace => y' - p)
    (ContinuousLinearMap.analyticAt _ _) (analyticAt_id.sub analyticAt_const)
theorem cubeChart_update (ξ : AmbientSpace) (μ : Fin 4) (ε : ℝ) (p : AmbientSpace)
    (u : Fin 4 → ℝ) (j : Fin 4) (t : ℝ) :
    cubeChart ξ μ ε p (Function.update u j t) =
      cubeChart ξ μ ε p (Function.update u j 0) + (ε / 2 * t) • frameVec ξ μ j := by
  have h : Function.update u j t = Function.update u j 0 + t • Pi.single j (1 : ℝ) := by
    funext ν
    by_cases hν : ν = j
    · subst hν
      simp
    · simp [hν]
  rw [h]
  simp only [cubeChart, map_add, map_smul, frameMap_single, smul_add, smul_smul, add_assoc]
def symCube : Set (Fin 4 → ℝ) := {u | ∀ ν, u ν ∈ Ioo (-1 : ℝ) 1}
theorem isOpen_symCube : IsOpen symCube := by
  have h : symCube = ⋂ ν, (fun u : Fin 4 → ℝ => u ν) ⁻¹' Ioo (-1 : ℝ) 1 := by
    ext u
    simp [symCube]
  rw [h]
  exact isOpen_iInter_of_finite fun ν => isOpen_Ioo.preimage (continuous_apply ν)
theorem lt_euclidNorm_cubeChart {ξ p : AmbientSpace} {μ : Fin 4} {ε : ℝ} (hε : 0 < ε)
    (hξ : euclidNorm ξ = 32 * ε) (hp : p ∈ euclidClosedBall ξ (2 * ε)) {u : Fin 4 → ℝ}
    (hu : ∀ ν, |u ν| ≤ 1) : 2 * ε < euclidNorm (cubeChart ξ μ ε p u) := by
  have h1 : euclidNorm (frameMap ξ μ u) ≤ 4 := by
    refine (euclidNorm_frameMap_le ξ μ u).trans ?_
    rw [Fin.sum_univ_four]
    linarith [hu 0, hu 1, hu 2, hu 3]
  have h2 : euclidNorm ((ε / 2) • frameMap ξ μ u) ≤ 2 * ε := by
    rw [euclidNorm_smul, abs_of_pos (by positivity)]
    nlinarith
  have h3 : euclidNorm (p - ξ) ≤ 2 * ε := hp
  have e : ξ = cubeChart ξ μ ε p u + -((ε / 2) • frameMap ξ μ u) + -(p - ξ) := by
    simp only [cubeChart]
    abel
  have h4 := euclidNorm_add_le (cubeChart ξ μ ε p u + -((ε / 2) • frameMap ξ μ u)) (-(p - ξ))
  have h5 := euclidNorm_add_le (cubeChart ξ μ ε p u) (-((ε / 2) • frameMap ξ μ u))
  rw [← e, euclidNorm_neg] at h4
  rw [euclidNorm_neg] at h5
  linarith
abbrev lineEquiv : ℂ ≃ Coordinates.ComplexCoordinates 1 := (Equiv.funUnique (Fin 1) ℂ).symm
theorem lineEquiv_conj_apply (f : ℂ → ℂ) (z : Coordinates.ComplexCoordinates 1) (i : Fin 1) :
    (lineEquiv ∘ f ∘ lineEquiv.symm) z i = f (z 0) := by apply _root_.YangMills.Construction.TwoPoints.ReflectedSpaceSlides.lineEquiv_conj_apply <;> assumption
theorem differentiableAt_of_isHolomorphicVia {O : Set ℂ} {f : ℂ → ℂ}
    (h : IsHolomorphicVia lineEquiv lineEquiv O f) {a : ℂ} (ha : a ∈ O) :
    DifferentiableAt ℂ f a := by
  have h1 := (h.2.2 (lineEquiv a) ⟨a, ha, rfl⟩ 0).self_of_nhds
  have h2 := differentiableAt_pi.1 h1 0
  simp only [lineEquiv_conj_apply] at h2
  have h3 : (fun ζ : ℂ => f ((lineEquiv a + ζ • stdBasisVector (0 : Fin 1)) 0)) =
      fun ζ => f (a + ζ) := by
    funext ζ
    simp [lineEquiv, stdBasisVector]
  rw [h3] at h2
  have h4 : DifferentiableAt ℂ (fun ζ : ℂ => f (a + ζ)) (a - a) := by simpa using h2
  have h5 : DifferentiableAt ℂ (fun w : ℂ => w - a) a := by fun_prop
  have h6 : DifferentiableAt ℂ ((fun ζ : ℂ => f (a + ζ)) ∘ fun w : ℂ => w - a) a :=
    DifferentiableAt.comp (f := fun w : ℂ => w - a) a h4 h5
  have h7 : ((fun ζ : ℂ => f (a + ζ)) ∘ fun w : ℂ => w - a) = f := by
    funext w
    simp
  rwa [h7] at h6
theorem isHolomorphicVia_of_differentiableOn {O : Set ℂ} {f : ℂ → ℂ} (hO : IsOpen O)
    (hf : DifferentiableOn ℂ f O) :
    IsHolomorphicVia lineEquiv lineEquiv O f := by apply _root_.YangMills.Construction.Cumulants.MomentCumulantFormulas.isHolomorphicVia_of_differentiableOn <;> assumption
theorem mem_compactC1Complex {ε : ℝ} {φ : AmbientSpace → ℂ} (h : φ ∈ cc1NearZero ε) :
    φ ∈ compactC1Complex :=
  ⟨h.1, h.2.1, subset_univ _⟩
theorem tsupport_subset_euclidOpenBall {ε : ℝ} {φ : AmbientSpace → ℂ} (h : φ ∈ cc1NearZero ε) :
    tsupport φ ⊆ euclidOpenBall (0 : AmbientSpace) ε :=
  h.2.2
theorem translateFun_translateFun {E : Type*} (a b : AmbientSpace) (f : AmbientSpace → E) :
    translateFun a (translateFun b f) = translateFun (b + a) f := by
  funext y
  simp only [translateFun, sub_sub, add_comm]
theorem sum_abs_le_three_of_eq_zero {v : Fin 4 → ℝ} {j : Fin 4} (hj : v j = 0)
    (hv : ∀ ν, |v ν| ≤ 1) : ∑ ν, |v ν| ≤ 3 := by
  have h1 : ∑ ν ∈ Finset.univ.erase j, |v ν| = ∑ ν, |v ν| :=
    Finset.sum_erase _ (by simp [hj])
  rw [← h1]
  have h2 := Finset.sum_le_card_nsmul (Finset.univ.erase j) (fun ν => |v ν|) 1 fun ν _ => hv ν
  simpa [Finset.card_erase_of_mem] using h2
theorem exists_sliceExtension (hF : AdmissibleFormConsequences.Statement)
    (hO : ReflectedSpaceAndSlides.Statement) (hE : JoukowskiRadius.JoukowskiRadiusProperties)
    {St : FixedScale} {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} (hS : IsDisjointForm S)
    (hP : IsAdmissibleForm St S) {C₂ : ℝ → ℝ → ℝ} (hC : IsBallDecayBound St S C₂)
    {ξ p : AmbientSpace} {μ : Fin 4} (hμ : ∀ ν, |ξ ν| ≤ |ξ μ|) {ε : ℝ} (hε : 0 < ε)
    (hξ : euclidNorm ξ = 32 * ε) (hp : p ∈ euclidClosedBall ξ (2 * ε))
    {φ₁ φ₂ : AmbientSpace → ℂ} (h₁ : φ₁ ∈ cc1NearZero ε) (h₂ : φ₂ ∈ cc1NearZero ε) (j : Fin 4)
    (x : Coordinates.ComplexCoordinates 4) (hx : x ∈ realClosedCube 4) :
    ∃ h : ℂ → ℂ, IsBoundedSliceExtension 2 one_lt_two
      (4 * C₂ (2 * ε) ε * St.sharpNorm φ₁ * St.sharpNorm φ₂)
      (fun z => shiftPairing S φ₁ φ₂ (cubeChart ξ μ ε p fun ν => (z ν).re)) j x h := by
  obtain ⟨-, -, -, hopen, -, -, -, hc, -⟩ := hE
  set u : Fin 4 → ℝ := fun ν => (x ν).re with hu_def
  have hu : ∀ ν, |u ν| ≤ 1 := fun ν => abs_le.2 ⟨(hx ν).2.1, (hx ν).2.2⟩
  set v : Fin 4 → ℝ := Function.update u j 0 with hv_def
  have hv : ∀ ν, |v ν| ≤ 1 := by
    intro ν
    by_cases hν : ν = j
    · subst hν
      simp [hv_def]
    · simpa [hv_def, hν] using hu ν
  have hvj : v j = 0 := by simp [hv_def]
  set q : AmbientSpace := cubeChart ξ μ ε p v with hq_def
  set n : AmbientSpace := frameVec ξ μ j with hn_def
  have hn1 : euclidNorm n = 1 := euclidNorm_frameVec ξ μ j
  set f₂ : AmbientSpace → ℂ := translateFun q φ₂ with hf₂_def
  obtain ⟨hkeep, -, hsupp⟩ := ((hF.2.2.2.1 St).1 φ₂ (mem_compactC1Complex h₂)).1 q
  have hprod : ∀ y : AmbientSpace, |euclidDot n y| ≤ euclidNorm y := fun y => by
    have := abs_euclidDot_le n y
    rwa [hn1, one_mul] at this
  have hleft : tsupport φ₁ ⊆ {y | euclidDot n y ≤ ε} := by
    intro y hy
    have h1 : euclidNorm (y - 0) < ε := tsupport_subset_euclidOpenBall h₁ hy
    rw [sub_zero] at h1
    exact (le_abs_self _).trans ((hprod y).trans h1.le)
  have hq : 5 * ε ≤ euclidDot n q := by
    have h1 := le_euclidDot_frameVec ξ μ j hμ
    have h2 : euclidNorm (p - ξ) ≤ 2 * ε := hp
    have h3 := abs_le.1 ((hprod (p - ξ)).trans h2)
    have h4 : euclidNorm (frameMap ξ μ v) ≤ 3 :=
      (euclidNorm_frameMap_le ξ μ v).trans (sum_abs_le_three_of_eq_zero hvj hv)
    have h5 := abs_le.1 ((hprod _).trans h4)
    have e : q = ξ + (p - ξ) + (ε / 2) • frameMap ξ μ v := by
      simp only [hq_def, cubeChart]
      abel
    rw [e, euclidDot_add, euclidDot_add, euclidDot_smul]
    rw [hξ] at h1
    nlinarith [h3.1, h5.1]
  have hright : tsupport f₂ ⊆ {y | ε + 3 * ε ≤ euclidDot n y} := by
    intro y hy
    rw [hf₂_def, hsupp] at hy
    obtain ⟨y', hy', q', rfl, rfl⟩ := hy
    have h1 : euclidNorm (y' - 0) < ε := tsupport_subset_euclidOpenBall h₂ hy'
    rw [sub_zero] at h1
    have h2 := abs_le.1 ((hprod y').trans h1.le)
    show ε + 3 * ε ≤ euclidDot n (y' + q)
    rw [euclidDot_add]
    linarith [h2.1]
  have hpair : IsSeparatedPair n ε (3 * ε) φ₁ f₂ :=
    ⟨by positivity, mem_compactC1Complex h₁, hkeep.mem, hleft, hright⟩
  have hball : ∀ {φ : AmbientSpace → ℂ}, φ ∈ cc1NearZero ε →
      tsupport φ ⊆ euclidClosedBall (0 : AmbientSpace) ε :=
    fun {φ} hφ y hy => (show euclidNorm (y - 0) < ε from tsupport_subset_euclidOpenBall hφ hy).le
  obtain ⟨hcs, hbd⟩ := (hO St S C₂ n ⟨hS, frameVec_mem ξ μ j, hP⟩ hC).2 ε ε (3 * ε) φ₁ f₂ hε
    ⟨0, hball h₁⟩ (hkeep.ballSupport 0 ε hε (hball h₂)) hpair
  set Φ : ℂ → ℂ := slideContinuation S n (3 * ε) φ₁ f₂ with hΦ_def
  have hre : ∀ w ∈ focalEllipse 2 one_lt_two, -ε ≤ ((((ε / 2 : ℝ) : ℂ)) * w).re := by
    intro w hw
    have h1 := abs_lt.1 (hc 2 one_lt_two w hw).1
    rw [Complex.re_ofReal_mul]
    nlinarith [h1.1]
  refine ⟨fun w => Φ (((ε / 2 : ℝ) : ℂ) * w), ?_⟩
  unfold IsBoundedSliceExtension
  refine ⟨?_, ?_, ?_⟩
  · refine isHolomorphicVia_of_differentiableOn (hopen 2 one_lt_two) fun w hw => ?_
    have hs : ((ε / 2 : ℝ) : ℂ) * w ∈ shiftedHalfPlane (3 * ε) := by
      have := hre w hw
      show -(3 * ε) < _
      linarith
    have hd := differentiableAt_of_isHolomorphicVia hcs.holomorphic hs
    have hg : DifferentiableAt ℂ (fun w : ℂ => ((ε / 2 : ℝ) : ℂ) * w) w := by fun_prop
    exact (DifferentiableAt.comp w hd hg).differentiableWithinAt
  · intro w hw
    have h1 := hbd ε hε (by linarith) (((ε / 2 : ℝ) : ℂ) * w) (by linarith [hre w hw])
    rwa [hkeep.sharpNorm_eq] at h1
  · intro t ht
    have hs : ε / 2 * t ∈ slideRange (3 * ε) := by
      show -(3 * ε) < ε / 2 * t
      nlinarith [ht.1]
    have h1 := hcs.eq_slideFn _ hs
    have e1 : (fun ν => (Function.update x j (t : ℂ) ν).re) = Function.update u j t := by
      funext ν
      by_cases hν : ν = j
      · subst hν
        simp
      · simp [hν, hu_def]
    show Φ (((ε / 2 : ℝ) : ℂ) * (t : ℂ)) = shiftPairing S φ₁ φ₂
      (cubeChart ξ μ ε p fun ν => (Function.update x j (t : ℂ) ν).re)
    rw [e1, cubeChart_update, ← Complex.ofReal_mul, h1]
    simp only [slideFn, shiftPairing, hf₂_def, translateFun_translateFun, hq_def, hn_def, hv_def]
theorem analyticOnNhd_symCube (hJ : JointHolomorphy.SeparateImpliesJoint)
    (hE : JoukowskiRadius.JoukowskiRadiusProperties)
    (hR : RealAnalyticity.CoordRealAnalyticIffAnalytic)
    (hF : AdmissibleFormConsequences.Statement) (hO : ReflectedSpaceAndSlides.Statement)
    (hT : SharpNormTranslates)
    {St : FixedScale} {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} (hS : IsDisjointForm S)
    (hP : IsAdmissibleForm St S) {C₂ : ℝ → ℝ → ℝ} (hC : IsBallDecayBound St S C₂)
    {ξ p : AmbientSpace} {μ : Fin 4} (hμ : ∀ ν, |ξ ν| ≤ |ξ μ|) {ε : ℝ} (hε : 0 < ε)
    (hξ : euclidNorm ξ = 32 * ε) (hp : p ∈ euclidClosedBall ξ (2 * ε))
    {φ₁ φ₂ : AmbientSpace → ℂ} (h₁ : φ₁ ∈ cc1NearZero ε) (h₂ : φ₂ ∈ cc1NearZero ε) :
    AnalyticOnNhd ℝ (fun u : Fin 4 → ℝ => shiftPairing S φ₁ φ₂ (cubeChart ξ μ ε p u)) symCube := by
  set F : Coordinates.ComplexCoordinates 4 → ℂ :=
    fun z => shiftPairing S φ₁ φ₂ (cubeChart ξ μ ε p fun ν => (z ν).re) with hF_def
  have hnonneg : ∀ φ : AmbientSpace → ℂ, 0 ≤ St.sharpNorm φ := fun φ =>
    le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
  have hA : 0 ≤ 4 * C₂ (2 * ε) ε * St.sharpNorm φ₁ * St.sharpNorm φ₂ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hC.1 _ _ (by positivity) hε)) (hnonneg _))
      (hnonneg _)
  have hcont : ContinuousOn F (realClosedCube 4) := by
    have hV := ((hT St).2.2.1 S hS hP ε hε φ₁ h₁ φ₂ h₂).2.1
    have hc : Continuous fun z : Coordinates.ComplexCoordinates 4 =>
        cubeChart ξ μ ε p fun ν => (z ν).re := by
      unfold cubeChart
      exact continuous_const.add (((frameMap ξ μ).continuous_of_finiteDimensional.comp
        (continuous_pi fun ν => Complex.continuous_re.comp (continuous_apply ν))).const_smul
          (ε / 2))
    exact hV.comp hc.continuousOn fun z hz =>
      lt_euclidNorm_cubeChart hε hξ hp fun ν => abs_le.2 ⟨(hz ν).2.1, (hz ν).2.2⟩
  have h1 := (hJ 4 (by norm_num) 2 one_lt_two _ hA F hcont fun j x hx =>
    exists_sliceExtension hF hO hE hS hP hC hμ hε hξ hp h₁ h₂ j x hx).2
  have hsub : realOpenCube 4 ⊆ realLocus 4 := fun z hz j => (hz j).1
  have h2 := ((hR 4 (realOpenCube 4) F hsub).1 h1).2
  have hpre : (fun (u : Fin 4 → ℝ) (j : Fin 4) => (u j : ℂ)) ⁻¹' realOpenCube 4 = symCube := by
    ext u
    simp [realOpenCube, symCube]
  rw [hpre] at h2
  intro u hu
  simpa [hF_def] using h2 u hu
theorem euclidNorm_pos {ξ : AmbientSpace} (hξ : ξ ≠ 0) : 0 < euclidNorm ξ := by apply _root_.YangMills.Construction.TwoPoints.MollifierBump.euclidNorm_pos <;> assumption
theorem holds (hJ : JointHolomorphy.SeparateImpliesJoint)
    (hE : JoukowskiRadius.JoukowskiRadiusProperties)
    (hR : RealAnalyticity.CoordRealAnalyticIffAnalytic)
    (hF : AdmissibleFormConsequences.Statement) (hO : ReflectedSpaceAndSlides.Statement)
    (hT : SharpNormTranslates) :
    ShiftPairingLocallyAnalytic.Statement := by
  intro St S hS hP ξ hξ
  obtain ⟨C₂, hC⟩ := hP.ballDecay
  obtain ⟨μ, hμ⟩ := Finite.exists_max fun ν => |ξ ν|
  have hpos := euclidNorm_pos hξ
  set ε : ℝ := euclidNorm ξ / 32 with hε_def
  have hε : 0 < ε := by positivity
  have hN : euclidNorm ξ = 32 * ε := by
    rw [hε_def]
    ring
  have hne : ε ≠ 0 := hε.ne'
  have hcube : ∀ {p y : AmbientSpace}, cubeChartInv ξ μ ε p y ∈ symCube →
      ∀ ν, |cubeChartInv ξ μ ε p y ν| ≤ 1 := fun h ν => abs_le.2 ⟨(h ν).1.le, (h ν).2.le⟩
  refine ⟨⋃ p ∈ euclidClosedBall ξ (2 * ε), cubeChartInv ξ μ ε p ⁻¹' symCube,
    isOpen_biUnion fun p _ => isOpen_symCube.preimage (continuous_cubeChartInv ξ μ ε p),
    fun p hp => mem_iUnion₂.2 ⟨p, hp, ?_⟩, fun y hy => ?_, fun φ₁ h₁ φ₂ h₂ y hy => ?_⟩
  · intro ν
    simp [cubeChartInv]
  · obtain ⟨p, hp, hy⟩ := mem_iUnion₂.1 hy
    have h1 := lt_euclidNorm_cubeChart (μ := μ) hε hN hp (hcube hy)
    rwa [cubeChart_cubeChartInv ξ μ hne] at h1
  · obtain ⟨p, hp, hy⟩ := mem_iUnion₂.1 hy
    have h1 := analyticOnNhd_symCube hJ hE hR hF hO hT hS hP hC hμ hε hN hp h₁ h₂ _ hy
    have h2 := h1.comp (analyticAt_cubeChartInv ξ μ ε p y)
    convert h2 using 1
    funext y'
    simp [cubeChart_cubeChartInv ξ μ hne]
end YangMills.Construction.TwoPoints.ShiftPairingLocallyAnalytic
end
