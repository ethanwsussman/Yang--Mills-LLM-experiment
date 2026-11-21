import YangMills.Construction.ComplexAnalysis.RealAnalyticInCoordinates
import YangMills.Construction.TwoPoints.ElementaryFactsOfMirrorsAndPlates
import YangMills.Construction.TwoPoints.FromThePlaneKernelsToTheOrthogonalGroup
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
private theorem eq_sum_coordVec (x : AmbientSpace) :
    x = ∑ i, x i • coordVec i := by
  funext μ
  fin_cases μ <;> simp [Fin.sum_univ_four, PeriodicLattice.coordVec]
private theorem rotateInPlane_eq_vec (t : ℝ) (x : AmbientSpace) :
    rotateInPlane t x = ![Real.sin t * x 3 + Real.cos t * x 0, x 1, x 2,
      Real.cos t * x 3 - Real.sin t * x 0] := by
  conv_lhs => rw [eq_sum_coordVec x]
  simp only [Fin.sum_univ_four, map_add, map_smul, rotateInPlane_coordVec_three,
    rotateInPlane_coordVec_zero, rotateInPlane_coordVec_one, rotateInPlane_coordVec_two]
  funext μ
  fin_cases μ <;>
    simp [planeUnit, PeriodicLattice.coordVec, Real.cos_add_pi_div_two,
      Real.sin_add_pi_div_two] <;> ring
private theorem rotationInCoordPlane_fst {μ ν : Fin 4} (h : μ ≠ ν) (t : ℝ) (x : AmbientSpace) :
    rotationInCoordPlane μ ν t x μ = Real.cos t * x μ - Real.sin t * x ν := by
  simp [rotationInCoordPlane, Function.update_of_ne h]
private theorem rotationInCoordPlane_snd (μ ν : Fin 4) (t : ℝ) (x : AmbientSpace) :
    rotationInCoordPlane μ ν t x ν = Real.sin t * x μ + Real.cos t * x ν := by
  simp [rotationInCoordPlane]
private theorem rotationInCoordPlane_of_ne {μ ν k : Fin 4} (h₁ : k ≠ μ) (h₂ : k ≠ ν) (t : ℝ)
    (x : AmbientSpace) :
    rotationInCoordPlane μ ν t x k = x k := by
  simp [rotationInCoordPlane, Function.update_of_ne h₁, Function.update_of_ne h₂]
private theorem eq_zero_of_rotate_eq_zero {a b t : ℝ}
    (h₁ : Real.cos t * a - Real.sin t * b = 0) (h₂ : Real.sin t * a + Real.cos t * b = 0) :
    a = 0 ∧ b = 0 := by
  have h := Real.sin_sq_add_cos_sq t
  constructor
  · linear_combination Real.cos t * h₁ + Real.sin t * h₂ - a * h
  · linear_combination -Real.sin t * h₁ + Real.cos t * h₂ - b * h
private theorem rotateInPlane_ne_zero (t : ℝ) {x : AmbientSpace} (hx : x ≠ 0) :
    rotateInPlane t x ≠ 0 := by
  intro h
  rw [rotateInPlane_eq_vec] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp at h0 h1 h2 h3
  obtain ⟨a, b⟩ := eq_zero_of_rotate_eq_zero h3 h0
  apply hx
  funext μ
  fin_cases μ <;> simp [a, b, h1, h2]
private theorem exists_angle_to_axis (a a' : ℝ) :
    ∃ t : ℝ, Real.cos t * a - Real.sin t * a' = Real.sqrt (a ^ 2 + a' ^ 2) ∧
      Real.sin t * a + Real.cos t * a' = 0 := by
  by_cases h : (⟨a, -a'⟩ : ℂ) = 0
  · have ha : a = 0 := congrArg Complex.re h
    have ha' : a' = 0 := by simpa using congrArg Complex.im h
    exact ⟨0, by simp [ha, ha'], by simp [ha, ha']⟩
  · have hr : ‖(⟨a, -a'⟩ : ℂ)‖ = Real.sqrt (a ^ 2 + a' ^ 2) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
      simp
    have hr0 : ‖(⟨a, -a'⟩ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 h
    have hsq : ‖(⟨a, -a'⟩ : ℂ)‖ ^ 2 = a ^ 2 + a' ^ 2 := by
      rw [hr, Real.sq_sqrt (by positivity)]
    refine ⟨Complex.arg ⟨a, -a'⟩, ?_, ?_⟩
    · rw [Complex.cos_arg h, Complex.sin_arg, ← hr]
      field_simp
      linarith
    · rw [Complex.cos_arg h, Complex.sin_arg]
      simp only []
      field_simp
      ring
private theorem exists_rotationInCoordPlane_to_axis {μ ν : Fin 4} (h : μ ≠ ν) (x : AmbientSpace) :
    ∃ t : ℝ, rotationInCoordPlane μ ν t x μ = Real.sqrt (x μ ^ 2 + x ν ^ 2) ∧
      rotationInCoordPlane μ ν t x ν = 0 ∧
      (∀ k, k ≠ μ → k ≠ ν → rotationInCoordPlane μ ν t x k = x k) ∧
      (x ≠ 0 → rotationInCoordPlane μ ν t x ≠ 0) := by
  obtain ⟨t, h₁, h₂⟩ := exists_angle_to_axis (x μ) (x ν)
  refine ⟨t, by rw [rotationInCoordPlane_fst h, h₁], by rw [rotationInCoordPlane_snd, h₂],
    fun k a b => rotationInCoordPlane_of_ne a b t x, fun hx h0 => hx ?_⟩
  have e₁ : Real.cos t * x μ - Real.sin t * x ν = 0 := by
    rw [← rotationInCoordPlane_fst h t x, h0]; rfl
  have e₂ : Real.sin t * x μ + Real.cos t * x ν = 0 := by
    rw [← rotationInCoordPlane_snd μ ν t x, h0]; rfl
  obtain ⟨a, b⟩ := eq_zero_of_rotate_eq_zero e₁ e₂
  funext k
  by_cases hk : k = μ
  · subst hk; simpa using a
  by_cases hk' : k = ν
  · subst hk'; simpa using b
  rw [← rotationInCoordPlane_of_ne hk hk' t x, h0]
private theorem hyperoctahedral_apply_perm {w : Equiv.Perm AmbientSpace}
    (hw : w ∈ hyperoctahedralPerms)
    {σ : Equiv.Perm (Fin 4)} (hσ : ∀ l, w (coordVec l) = coordVec (σ l))
    (x : AmbientSpace) (k : Fin 4) : w x (σ k) = x k := by
  obtain ⟨l, hl, -⟩ := exists_isSignedPerm hw
  have hl' : ∀ i, l (coordVec i) = coordVec (σ i) := fun i => by
    rw [hl]; exact hσ i
  have e : w x = ∑ i, x i • coordVec (σ i) := by
    rw [← hl]
    conv_lhs => rw [eq_sum_coordVec x]
    simp only [map_sum, map_smul, hl']
  rw [e, Finset.sum_apply, Finset.sum_eq_single k]
  · simp [PeriodicLattice.coordVec]
  · intro b _ hb
    have : σ k ≠ σ b := fun h => hb (σ.injective h).symm
    simp [PeriodicLattice.coordVec, this]
  · simp
private theorem perm_apply_inv (w : Equiv.Perm AmbientSpace) (x : AmbientSpace) :
    w (w⁻¹ x) = x :=
  w.apply_symm_apply x
private theorem hyperoctahedral_inv_apply {w : Equiv.Perm AmbientSpace}
    (hw : w ∈ hyperoctahedralPerms)
    {σ : Equiv.Perm (Fin 4)} (hσ : ∀ l, w (coordVec l) = coordVec (σ l))
    (x : AmbientSpace) (k : Fin 4) : w⁻¹ x k = x (σ k) := by
  rw [← hyperoctahedral_apply_perm hw hσ (w⁻¹ x) k, perm_apply_inv]
private theorem permConjRotation_eq {w : Equiv.Perm AmbientSpace} (hw : w ∈ hyperoctahedralPerms)
    {σ : Equiv.Perm (Fin 4)} (hσ : ∀ l, w (coordVec l) = coordVec (σ l))
    {μ ν : Fin 4} (h : μ ≠ ν) (h₃ : σ 3 = μ) (h₀ : σ 0 = ν) (t : ℝ) :
    permConjRotation w t = rotationInCoordPlane μ ν t := by
  funext ξ k
  obtain ⟨l, rfl⟩ := σ.surjective k
  rw [permConjRotation, hyperoctahedral_apply_perm hw hσ, rotateInPlane_eq_vec]
  have i₃ := hyperoctahedral_inv_apply hw hσ ξ 3
  have i₀ := hyperoctahedral_inv_apply hw hσ ξ 0
  rw [h₃] at i₃
  rw [h₀] at i₀
  obtain rfl | rfl | rfl | rfl : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by revert l; decide
  · rw [h₀, rotationInCoordPlane_snd]; simp [i₃, i₀]
  · have a : σ 1 ≠ μ := fun e => absurd (σ.injective (e.trans h₃.symm)) (by decide)
    have b : σ 1 ≠ ν := fun e => absurd (σ.injective (e.trans h₀.symm)) (by decide)
    rw [rotationInCoordPlane_of_ne a b]
    simp [hyperoctahedral_inv_apply hw hσ]
  · have a : σ 2 ≠ μ := fun e => absurd (σ.injective (e.trans h₃.symm)) (by decide)
    have b : σ 2 ≠ ν := fun e => absurd (σ.injective (e.trans h₀.symm)) (by decide)
    rw [rotationInCoordPlane_of_ne a b]
    simp [hyperoctahedral_inv_apply hw hσ]
  · rw [h₃, rotationInCoordPlane_fst h]; simp [i₃, i₀]
private theorem exists_perm_three_zero {μ ν : Fin 4} (h : μ ≠ ν) :
    ∃ σ : Equiv.Perm (Fin 4), σ 3 = μ ∧ σ 0 = ν := by
  refine ⟨Equiv.swap (Equiv.swap 3 μ 0) ν * Equiv.swap 3 μ, ?_, ?_⟩
  · have h1 : μ ≠ Equiv.swap 3 μ 0 := by
      intro e
      have : Equiv.swap 3 μ 3 = Equiv.swap 3 μ 0 := by rw [Equiv.swap_apply_left]; exact e
      exact absurd ((Equiv.swap 3 μ).injective this) (by decide)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne h1 h
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
private theorem exists_perm_matrix (σ : Equiv.Perm (Fin 4)) :
    ∃ w ∈ hyperoctahedralPerms, ∀ l, w (coordVec l) = coordVec (σ l) := by
  have hw : TorusLifts.signedCoordinateEquiv σ⁻¹ (fun _ => 1) ∈ hyperoctahedralPerms :=
    ⟨_, _, rfl⟩
  have hl : ∀ x, TorusLifts.signedCoordinateEquiv σ⁻¹ (fun _ => 1) x =
      signedPermLinear σ⁻¹ (fun _ => 1) x := fun _ => rfl
  have he : ∀ l : Fin 4, signedPermLinear σ⁻¹ (fun _ => 1) (coordVec l) =
      coordVec (σ l) := by
    intro l
    rw [signedPermLinear_coordVec]
    simp only [Units.val_one, Int.cast_one, one_smul]
    rfl
  exact ⟨_, hw, fun l => by rw [hl, he]⟩
private theorem kernel_permConjRotation {K : AmbientSpace → ℝ}
    (hinv : ∀ w ∈ hyperoctahedralPerms, ∀ ξ : AmbientSpace, ξ ≠ 0 → K (w ξ) = K ξ)
    (hi : ∀ ξ : AmbientSpace, ξ ≠ 0 → ∀ t : ℝ, K (rotateInPlane t ξ) = K ξ)
    {w : Equiv.Perm AmbientSpace} (hw : w ∈ hyperoctahedralPerms) (t : ℝ) {ξ : AmbientSpace}
    (hξ : ξ ≠ 0) :
    K (permConjRotation w t ξ) = K ξ := by
  have hη : w⁻¹ ξ ≠ 0 := by
    intro h
    obtain ⟨l, hl, -⟩ := exists_isSignedPerm hw
    apply hξ
    rw [← perm_apply_inv w ξ, h, ← hl, map_zero]
  rw [permConjRotation, hinv w hw _ (rotateInPlane_ne_zero t hη), hi _ hη,
    hinv _ (inv_mem hw) _ hξ]
private theorem kernel_rotationInCoordPlane {K : AmbientSpace → ℝ}
    (hinv : ∀ w ∈ hyperoctahedralPerms, ∀ ξ : AmbientSpace, ξ ≠ 0 → K (w ξ) = K ξ)
    (hi : ∀ ξ : AmbientSpace, ξ ≠ 0 → ∀ t : ℝ, K (rotateInPlane t ξ) = K ξ)
    {μ ν : Fin 4} (h : μ ≠ ν) (t : ℝ) {ξ : AmbientSpace} (hξ : ξ ≠ 0) :
    K (rotationInCoordPlane μ ν t ξ) = K ξ := by
  obtain ⟨σ, h₃, h₀⟩ := exists_perm_three_zero h
  obtain ⟨w, hw, hσ⟩ := exists_perm_matrix σ
  rw [← permConjRotation_eq hw hσ h h₃ h₀, kernel_permConjRotation hinv hi hw t hξ]
private theorem kernel_eq_on_axis {K : AmbientSpace → ℝ}
    (hrot : ∀ μ ν : Fin 4, μ ≠ ν → ∀ (t : ℝ) (ξ : AmbientSpace), ξ ≠ 0 →
      K (rotationInCoordPlane μ ν t ξ) = K ξ)
    {ξ : AmbientSpace} (hξ : ξ ≠ 0) : K ξ = K (euclidNorm ξ • coordVec 3) := by
  obtain ⟨t₁, a₁, b₁, c₁, d₁⟩ := exists_rotationInCoordPlane_to_axis (μ := 1) (ν := 2) (by decide) ξ
  set ξ₁ := rotationInCoordPlane 1 2 t₁ ξ with e₁
  have n₁ := d₁ hξ
  obtain ⟨t₂, a₂, b₂, c₂, d₂⟩ := exists_rotationInCoordPlane_to_axis (μ := 0) (ν := 1) (by decide) ξ₁
  set ξ₂ := rotationInCoordPlane 0 1 t₂ ξ₁ with e₂
  have n₂ := d₂ n₁
  obtain ⟨t₃, a₃, b₃, c₃, -⟩ := exists_rotationInCoordPlane_to_axis (μ := 3) (ν := 0) (by decide) ξ₂
  set ξ₃ := rotationInCoordPlane 3 0 t₃ ξ₂ with e₃
  have k₁ : K ξ₃ = K ξ := by
    rw [e₃, hrot _ _ (by decide) _ _ n₂, e₂, hrot _ _ (by decide) _ _ n₁, e₁,
      hrot _ _ (by decide) _ _ hξ]
  have p₀ : ξ₁ 0 = ξ 0 := c₁ 0 (by decide) (by decide)
  have p₃ : ξ₁ 3 = ξ 3 := c₁ 3 (by decide) (by decide)
  have q₃ : ξ₂ 3 = ξ₁ 3 := c₂ 3 (by decide) (by decide)
  have q₂ : ξ₂ 2 = ξ₁ 2 := c₂ 2 (by decide) (by decide)
  have r₁ : ξ₃ 1 = ξ₂ 1 := c₃ 1 (by decide) (by decide)
  have r₂ : ξ₃ 2 = ξ₂ 2 := c₃ 2 (by decide) (by decide)
  have hn : ξ₃ 3 = euclidNorm ξ := by
    rw [a₃, a₂, q₃, p₃, p₀, a₁, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      euclidNorm, Fin.sum_univ_four]
    congr 1
    ring
  have hv : ξ₃ = euclidNorm ξ • coordVec 3 := by
    funext k
    obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by revert k; decide
    · simp [b₃, PeriodicLattice.coordVec]
    · simp [r₁, b₂, PeriodicLattice.coordVec]
    · simp [r₂, q₂, b₁, PeriodicLattice.coordVec]
    · simp [hn, PeriodicLattice.coordVec]
  rw [← hv, k₁]
private theorem analyticOnNhd_of_isRealAnalytic (hA : RealAnalyticity.CoordRealAnalyticIffAnalytic)
    {K : AmbientSpace → ℝ} (h : IsRealAnalyticAwayFromZero K) :
    AnalyticOnNhd ℝ (fun u : AmbientSpace => (K u : ℂ)) {0}ᶜ := by
  have h₁ := ((hA 4 (Coordinates.ComplexCoordinates.realLocus 4 \ {0})
    (fun z => ((K fun μ => (z μ).re : ℝ) : ℂ)) sdiff_subset).1 h).2
  have e : (fun (u : Fin 4 → ℝ) (j : Fin 4) => (u j : ℂ)) ⁻¹'
      (Coordinates.ComplexCoordinates.realLocus 4 \ {0}) = {0}ᶜ := by
    ext u
    simp only [mem_preimage, Set.mem_sdiff, mem_singleton_iff, mem_compl_iff]
    constructor
    · rintro ⟨-, h⟩ rfl
      exact h (by funext j; simp)
    · intro hu
      refine ⟨fun j => by simp, fun h => hu ?_⟩
      funext j
      simpa using congrFun h j
  rw [e] at h₁
  simpa using h₁
private theorem continuousOn_of_analyticOnNhd {K : AmbientSpace → ℝ}
    (h : AnalyticOnNhd ℝ (fun u : AmbientSpace => (K u : ℂ)) {0}ᶜ) : ContinuousOn K {0}ᶜ := by
  have := Complex.continuous_re.comp_continuousOn h.continuousOn
  simpa [Function.comp_def] using this
private theorem continuous_assemble (y : Fin 2 → ℝ) :
    Continuous fun z : Fin 2 → ℝ => assemble y z := by
  refine continuous_pi fun μ => ?_
  obtain rfl | rfl | rfl | rfl : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 := by revert μ; decide
  · simpa [assemble] using continuous_const
  · simpa [assemble] using continuous_apply 0
  · simpa [assemble] using continuous_apply 1
  · simpa [assemble] using continuous_const
private theorem assemble_ne_zero {y : Fin 2 → ℝ} (hy : y ≠ 0) (z : Fin 2 → ℝ) :
    assemble y z ≠ 0 := by
  intro h
  apply hy
  funext i
  have h0 := congrFun h 0
  have h3 := congrFun h 3
  simp [assemble] at h0 h3
  obtain rfl | rfl : i = 0 ∨ i = 1 := by revert i; decide
  · simpa using h3
  · simpa using h0
abbrev _root_.YangMills.SharedProofs.p69635 := @assemble_ne_zero
private theorem continuous_ofCoords {K : AmbientSpace → ℝ} (hc : ContinuousOn K {0}ᶜ)
    {y : Fin 2 → ℝ} (hy : y ≠ 0) : Continuous (ofCoords K y) :=
  hc.comp_continuous (continuous_assemble y) fun z => assemble_ne_zero hy z
private theorem transProfile_continuous {φ : (Fin 2 → ℝ) → ℂ} (h : φ ∈ transProfiles) :
    Continuous φ :=
  ContDiff.continuous h.1.1
private theorem transProfile_hasCompactSupport {φ : (Fin 2 → ℝ) → ℂ} (h : φ ∈ transProfiles) :
    HasCompactSupport φ :=
  h.1.2.1
private theorem ofReal_mem_transProfiles {g : (Fin 2 → ℝ) → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) : (fun x => (g x : ℂ)) ∈ transProfiles := by
  refine ⟨⟨Complex.ofRealCLM.contDiff.comp hg, ?_, subset_univ _⟩, fun x => by simp⟩
  exact HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hc Complex.ofReal_zero
private theorem integrable_mul_shift {a b : (Fin 2 → ℝ) → ℂ} (ha : a ∈ transProfiles)
    (hb : b ∈ transProfiles) (ζ : Fin 2 → ℝ) :
    Integrable fun υ => a υ * b (υ + ζ) :=
  ((transProfile_continuous ha).mul
    ((transProfile_continuous hb).comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
    ((transProfile_hasCompactSupport ha).mul_right (f' := fun υ => b (υ + ζ)))
private theorem profileCorr_polarization {φ₁ φ₂ : (Fin 2 → ℝ) → ℂ} (h₁ : φ₁ ∈ transProfiles)
    (h₂ : φ₂ ∈ transProfiles) (ζ : Fin 2 → ℝ) :
    profileCorr (φ₁ + φ₂) (φ₁ + φ₂) ζ - profileCorr (φ₁ - φ₂) (φ₁ - φ₂) ζ =
      2 * (profileCorr φ₁ φ₂ ζ + profileCorr φ₂ φ₁ ζ) := by
  have hp := add_mem h₁ h₂
  have hm := sub_mem h₁ h₂
  simp only [profileCorr, lebesgueIntegral, integralWrt]
  rw [← integral_sub (integrable_mul_shift hp hp ζ) (integrable_mul_shift hm hm ζ),
    ← integral_add (integrable_mul_shift h₁ h₂ ζ) (integrable_mul_shift h₂ h₁ ζ),
    ← integral_const_mul]
  congr 1
  funext υ
  simp only [Pi.add_apply, Pi.sub_apply]
  ring
private theorem ofCoords_eq_of_integral_eq {K : AmbientSpace → ℝ} (hc : ContinuousOn K {0}ᶜ)
    (hcorr : ProfileCorrProperties)
    (heven : ∀ y ζ : Fin 2 → ℝ, y ≠ 0 → ofCoords K y (-ζ) = ofCoords K y ζ)
    {y y' : Fin 2 → ℝ} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (hG : ∀ φ ∈ transProfiles,
      (lebesgueIntegral fun ζ : Fin 2 → ℝ => ((ofCoords K y' ζ : ℝ) : ℂ) * profileCorr φ φ ζ) =
        lebesgueIntegral fun ζ : Fin 2 → ℝ => ((ofCoords K y ζ : ℝ) : ℂ) * profileCorr φ φ ζ)
    (ζ₀ : Fin 2 → ℝ) : ofCoords K y' ζ₀ = ofCoords K y ζ₀ := by
  by_contra hne
  set E : (Fin 2 → ℝ) → ℝ := fun ζ => ofCoords K y ζ - ofCoords K y' ζ with hE
  have hEc : Continuous E := (continuous_ofCoords hc hy).sub (continuous_ofCoords hc hy')
  have hEeven : ∀ ζ, E (-ζ) = E ζ := fun ζ => by simp only [hE, heven _ _ hy, heven _ _ hy']
  have hc0 : E ζ₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  set P : (Fin 2 → ℝ) → ℝ := fun ζ => E ζ₀ * E ζ with hP
  have hPc : Continuous P := continuous_const.mul hEc
  have hP0 : 0 < P ζ₀ := mul_self_pos.2 hc0
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ ζ, dist ζ ζ₀ < 2 * δ → 0 < P ζ := by
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1
      (hPc.continuousAt.eventually (lt_mem_nhds hP0))
    exact ⟨ε / 2, by positivity, fun ζ hζ => h (by linarith)⟩
  let ρ : ContDiffBump (0 : Fin 2 → ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => ρ.nonneg
  have hρc : Continuous (fun x => ρ x) := ρ.continuous
  have hρs : ∀ x, ρ x ≠ 0 → ‖x‖ < δ := fun x h => by
    have : x ∈ Function.support (fun x => ρ x) := h
    rw [ρ.support_eq] at this
    simpa using this
  have hρd : ContDiff ℝ 1 (fun x => ρ x) := ρ.contDiff
  have hρk : HasCompactSupport (fun x => ρ x) := ρ.hasCompactSupport
  set g : (Fin 2 → ℝ) → ℝ := fun x => ρ (x - ζ₀) with hg
  have hgd : ContDiff ℝ 1 g := hρd.comp (contDiff_id.sub contDiff_const)
  have hgk : HasCompactSupport g :=
    hρk.comp_homeomorph (Homeomorph.subRight ζ₀)
  set u : (Fin 2 → ℝ) → ℂ := fun x => (ρ x : ℂ) with hu
  set v : (Fin 2 → ℝ) → ℂ := fun x => (g x : ℂ) with hv
  have hup : u ∈ transProfiles := ofReal_mem_transProfiles hρd hρk
  have hvp : v ∈ transProfiles := ofReal_mem_transProfiles hgd hgk
  set r₁ : (Fin 2 → ℝ) → ℝ := fun ζ => ∫ υ, ρ υ * g (υ + ζ) with hr₁
  set r₂ : (Fin 2 → ℝ) → ℝ := fun ζ => ∫ υ, g υ * ρ (υ + ζ) with hr₂
  have c₁ : ∀ ζ, profileCorr u v ζ = (r₁ ζ : ℂ) := fun ζ => by
    simp only [profileCorr, lebesgueIntegral, integralWrt, hu, hv, hr₁,
      ← Complex.ofReal_mul]
    exact integral_complex_ofReal
  have c₂ : ∀ ζ, profileCorr v u ζ = (r₂ ζ : ℂ) := fun ζ => by
    simp only [profileCorr, lebesgueIntegral, integralWrt, hu, hv, hr₂,
      ← Complex.ofReal_mul]
    exact integral_complex_ofReal
  have hg0 : ∀ x, 0 ≤ g x := fun x => hρ0 _
  have r₁0 : ∀ ζ, 0 ≤ r₁ ζ := fun ζ => integral_nonneg fun υ => mul_nonneg (hρ0 _) (hg0 _)
  have r₂0 : ∀ ζ, 0 ≤ r₂ ζ := fun ζ => integral_nonneg fun υ => mul_nonneg (hg0 _) (hρ0 _)
  set T : (Fin 2 → ℝ) → ℝ := fun ζ => r₁ ζ + r₂ ζ with hT
  obtain ⟨-, k₁, s₁⟩ := hcorr u hup v hvp
  obtain ⟨-, k₂, s₂⟩ := hcorr v hvp u hup
  have hTe : T = fun ζ => (profileCorr u v ζ + profileCorr v u ζ).re := by
    funext ζ
    simp [hT, c₁, c₂]
  have hTc : Continuous T := by
    rw [hTe]
    exact Complex.continuous_re.comp (k₁.add k₂)
  have hTk : HasCompactSupport T := by
    rw [hTe]
    exact HasCompactSupport.comp_left (g := Complex.re)
      (HasCompactSupport.add (f := profileCorr u v) (f' := profileCorr v u) s₁ s₂)
      Complex.zero_re
  have hint : ∀ (z : Fin 2 → ℝ), z ≠ 0 → ∀ φ ∈ transProfiles,
      Integrable fun ζ : Fin 2 → ℝ => ((ofCoords K z ζ : ℝ) : ℂ) * profileCorr φ φ ζ := by
    intro z hz φ hφ
    obtain ⟨-, k, s⟩ := hcorr φ hφ φ hφ
    refine ((Complex.continuous_ofReal.comp (continuous_ofCoords hc hz)).mul
      k).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.mul_left (f := fun ζ => ((ofCoords K z ζ : ℝ) : ℂ)) s
  have hI : ∀ φ ∈ transProfiles,
      Integrable (fun ζ : Fin 2 → ℝ => ((E ζ : ℝ) : ℂ) * profileCorr φ φ ζ) ∧
      ∫ ζ : Fin 2 → ℝ, ((E ζ : ℝ) : ℂ) * profileCorr φ φ ζ = 0 := by
    intro φ hφ
    have e : (fun ζ : Fin 2 → ℝ => ((E ζ : ℝ) : ℂ) * profileCorr φ φ ζ) =
        fun ζ => ((ofCoords K y ζ : ℝ) : ℂ) * profileCorr φ φ ζ -
          ((ofCoords K y' ζ : ℝ) : ℂ) * profileCorr φ φ ζ := by
      funext ζ
      simp only [hE]
      push_cast
      ring
    rw [e]
    refine ⟨(hint y hy φ hφ).sub (hint y' hy' φ hφ), ?_⟩
    rw [integral_sub (hint y hy φ hφ) (hint y' hy' φ hφ)]
    have := hG φ hφ
    simp only [lebesgueIntegral, integralWrt] at this
    rw [this, sub_self]
  have hpm := hI (u + v) (add_mem hup hvp)
  have hmm := hI (u - v) (sub_mem hup hvp)
  have hET : ∫ ζ : Fin 2 → ℝ, P ζ * T ζ = 0 := by
    have h₀ : ∫ ζ : Fin 2 → ℝ, (((E ζ₀ / 2) : ℝ) : ℂ) *
        (((E ζ : ℝ) : ℂ) * profileCorr (u + v) (u + v) ζ -
          ((E ζ : ℝ) : ℂ) * profileCorr (u - v) (u - v) ζ) = 0 := by
      rw [integral_const_mul, integral_sub hpm.1 hmm.1, hpm.2, hmm.2]
      simp
    have e : (fun ζ : Fin 2 → ℝ => (((E ζ₀ / 2) : ℝ) : ℂ) *
        (((E ζ : ℝ) : ℂ) * profileCorr (u + v) (u + v) ζ -
          ((E ζ : ℝ) : ℂ) * profileCorr (u - v) (u - v) ζ)) =
        fun ζ => ((P ζ * T ζ : ℝ) : ℂ) := by
      funext ζ
      have := profileCorr_polarization hup hvp ζ
      rw [← mul_sub, this, c₁, c₂]
      simp only [hP, hT]
      push_cast
      ring
    rw [e, integral_complex_ofReal] at h₀
    exact_mod_cast h₀
  have hsupp₁ : ∀ ζ, r₁ ζ ≠ 0 → dist ζ ζ₀ < 2 * δ := by
    intro ζ h
    by_contra hd
    apply h
    simp only [hr₁]
    rw [← integral_zero (Fin 2 → ℝ) ℝ]
    congr 1
    funext υ
    by_contra hne'
    have a : ρ υ ≠ 0 := left_ne_zero_of_mul hne'
    have b : g (υ + ζ) ≠ 0 := right_ne_zero_of_mul hne'
    have a' := hρs _ a
    have b' := hρs _ b
    apply hd
    rw [dist_eq_norm]
    have e : ζ - ζ₀ = (υ + ζ - ζ₀) - υ := by abel
    rw [e]
    calc ‖υ + ζ - ζ₀ - υ‖ ≤ ‖υ + ζ - ζ₀‖ + ‖υ‖ := norm_sub_le _ _
      _ < 2 * δ := by linarith
  have hsupp₂ : ∀ ζ, r₂ ζ ≠ 0 → dist (-ζ) ζ₀ < 2 * δ := by
    intro ζ h
    by_contra hd
    apply h
    simp only [hr₂]
    rw [← integral_zero (Fin 2 → ℝ) ℝ]
    congr 1
    funext υ
    by_contra hne'
    have a : g υ ≠ 0 := left_ne_zero_of_mul hne'
    have b : ρ (υ + ζ) ≠ 0 := right_ne_zero_of_mul hne'
    have a' := hρs _ a
    have b' := hρs _ b
    apply hd
    rw [dist_eq_norm]
    have e : -ζ - ζ₀ = (υ - ζ₀) - (υ + ζ) := by abel
    rw [e]
    calc ‖υ - ζ₀ - (υ + ζ)‖ ≤ ‖υ - ζ₀‖ + ‖υ + ζ‖ := norm_sub_le _ _
      _ < 2 * δ := by linarith
  have hPeven : ∀ ζ, P (-ζ) = P ζ := fun ζ => by simp only [hP, hEeven]
  have hF0 : (0 : (Fin 2 → ℝ) → ℝ) ≤ fun ζ => P ζ * T ζ := by
    intro ζ
    by_cases h₁ : r₁ ζ = 0
    · by_cases h₂ : r₂ ζ = 0
      · simp [hT, h₁, h₂]
      · have := hball _ (hsupp₂ ζ h₂)
        rw [hPeven] at this
        exact mul_nonneg this.le (add_nonneg (r₁0 ζ) (r₂0 ζ))
    · exact mul_nonneg (hball _ (hsupp₁ ζ h₁)).le (add_nonneg (r₁0 ζ) (r₂0 ζ))
  have hr₁pos : 0 < r₁ ζ₀ := by
    have e : r₁ ζ₀ = ∫ υ, ρ υ * ρ υ := by
      simp only [hr₁, hg, add_sub_cancel_right]
    rw [e]
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (hρc.mul hρc) (hρk.mul_right (f' := fun x => ρ x)) (fun x => mul_self_nonneg _) ?_
    have : ρ 0 = 1 := ρ.one_of_mem_closedBall (by simp [ρ.rIn_pos.le])
    simp [this]
  have hFpos : 0 < ∫ ζ : Fin 2 → ℝ, P ζ * T ζ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := ζ₀)
      (hPc.mul hTc) (hTk.mul_left (f := P)) hF0 ?_
    exact (mul_pos hP0 (add_pos_of_pos_of_nonneg hr₁pos (r₂0 ζ₀))).ne'
  exact hFpos.ne' hET
private theorem rotateInPlane_assemble (t : ℝ) (y z : Fin 2 → ℝ) :
    rotateInPlane t (assemble y z) =
      assemble (planeCoords (rotateInPlane t (embedPlane y))) z := by
  rw [rotateInPlane_eq_vec, rotateInPlane_eq_vec]
  funext μ
  obtain rfl | rfl | rfl | rfl : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 := by revert μ; decide
  all_goals simp [assemble, planeCoords, embedPlane, PeriodicLattice.coordVec]
private theorem planeCoords_rotate_ne_zero (t : ℝ) {y : Fin 2 → ℝ} (hy : y ≠ 0) :
    planeCoords (rotateInPlane t (embedPlane y)) ≠ 0 := by
  intro h
  rw [rotateInPlane_eq_vec] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [planeCoords, embedPlane, PeriodicLattice.coordVec] at h0 h1
  obtain ⟨a, b⟩ := eq_zero_of_rotate_eq_zero h0 h1
  apply hy
  funext i
  obtain rfl | rfl : i = 0 ∨ i = 1 := by revert i; decide
  · simpa using a
  · simpa using b
private theorem assemble_planeCoords_transCoords (x : AmbientSpace) :
    assemble (planeCoords x) (transCoords x) = x := by
  funext μ
  obtain rfl | rfl | rfl | rfl : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 := by revert μ; decide
  all_goals simp [assemble, planeCoords, transCoords]
private theorem formKernel_rotateInPlane {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    (hc : ContinuousOn (formKernel S) {0}ᶜ) (hcorr : ProfileCorrProperties)
    (heven : ∀ y ζ : Fin 2 → ℝ, y ≠ 0 →
      ofCoords (formKernel S) y (-ζ) = ofCoords (formKernel S) y ζ)
    (hplane : ∀ φ ∈ transProfiles, IsRotationInvariantAveragedKernel S φ)
    (ξ : AmbientSpace) (t : ℝ) : formKernel S (rotateInPlane t ξ) = formKernel S ξ := by
  by_cases hy : planeCoords ξ = 0
  · have h3 : ξ 3 = 0 := congrFun hy 0
    have h0 : ξ 0 = 0 := congrFun hy 1
    congr 1
    rw [rotateInPlane_eq_vec]
    funext μ
    obtain rfl | rfl | rfl | rfl : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 := by revert μ; decide
    all_goals simp [h3, h0]
  · have key := ofCoords_eq_of_integral_eq hc hcorr heven hy (planeCoords_rotate_ne_zero t hy)
      (fun φ hφ => hplane φ hφ _ hy t) (transCoords ξ)
    simp only [ofCoords] at key
    rw [← rotateInPlane_assemble, assemble_planeCoords_transCoords] at key
    exact key
private theorem radialProfile_isRealAnalyticOnIoi (hA : RealAnalyticity.CoordRealAnalyticIffAnalytic)
    {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    (h : AnalyticOnNhd ℝ (fun u : AmbientSpace => (formKernel S u : ℂ)) {0}ᶜ) :
    IsRealAnalyticOnIoi (radialProfile S) := by
  refine (hA 1 (Coordinates.ComplexCoordinates.realLocus 1 ∩ {z | 0 < (z 0).re})
    (fun z => ((radialProfile S (z 0).re : ℝ) : ℂ)) inter_subset_left).2 ?_
  have e : (fun (u : Fin 1 → ℝ) (j : Fin 1) => (u j : ℂ)) ⁻¹'
      (Coordinates.ComplexCoordinates.realLocus 1 ∩ {z | 0 < (z 0).re}) = {u | 0 < u 0} := by
    ext u
    simp [Coordinates.ComplexCoordinates.realLocus]
  rw [e]
  refine ⟨isOpen_lt continuous_const (continuous_apply 0), ?_⟩
  let L : (Fin 1 → ℝ) →L[ℝ] AmbientSpace :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight
      (coordVec 3)
  have hL : MapsTo L {u | 0 < u 0} {0}ᶜ := by
    intro u hu h0
    have := congrFun h0 3
    simp [L, PeriodicLattice.coordVec] at this
    exact (ne_of_gt hu) this
  have := h.comp (L.analyticOnNhd _) hL
  refine this.congr (isOpen_lt continuous_const (continuous_apply 0)) ?_
  intro u _
  simp [L, radialProfile, Function.comp]
private theorem euclidNorm_sub_comm (x x' : AmbientSpace) :
    euclidNorm (x' - x) = euclidNorm (x - x') := by
  simp only [euclidNorm, Pi.sub_apply]
  congr 1
  exact Finset.sum_congr rfl fun μ _ => by ring
private theorem hasRadialProfile_of_formKernel {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    (hS : IsDisjointForm S)
    (hK : IsAnalyticKernel S (formKernel S))
    (hrad : ∀ ξ : AmbientSpace, ξ ≠ 0 → formKernel S ξ = radialProfile S (euclidNorm ξ)) :
    HasRadialProfile S (radialProfile S) := by
  intro f₁ h₁ f₂ h₂ hd
  have hr := hK.represents f₁ h₁.1 f₂ h₂.1 hd
  rw [hS.complexifyForm_of_mem_compactC1Real h₁ h₂] at hr
  rw [hr]
  congr 1
  funext x'
  congr 1
  funext x
  by_cases hx : x' - x = 0
  · have e : x' = x := sub_eq_zero.1 hx
    subst e
    have z : f₁ x' * f₂ x' = 0 := by
      by_contra hne
      exact Set.disjoint_left.1 hd
        (subset_tsupport _ (left_ne_zero_of_mul hne))
        (subset_tsupport _ (right_ne_zero_of_mul hne))
    simp [z]
  · rw [hrad _ hx, euclidNorm_sub_comm]
private abbrev O4 : Type := Matrix.orthogonalGroup (Fin 4) ℝ
private theorem o4_inv_mul (Q : O4) :
    ((Q⁻¹ : O4) : Matrix (Fin 4) (Fin 4) ℝ) * (Q : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
  have : ((Q⁻¹ * Q : O4) : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by simp
  exact this
private theorem o4_mul_inv (Q : O4) :
    (Q : Matrix (Fin 4) (Fin 4) ℝ) * ((Q⁻¹ : O4) : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
  have : ((Q * Q⁻¹ : O4) : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by simp
  exact this
private def o4Equiv (Q : O4) : AmbientSpace ≃L[ℝ] AmbientSpace :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (Q : Matrix (Fin 4) (Fin 4) ℝ).mulVec x
      invFun := fun x => ((Q⁻¹ : O4) : Matrix (Fin 4) (Fin 4) ℝ).mulVec x
      map_add' := Matrix.mulVec_add _
      map_smul' := fun c x => Matrix.mulVec_smul _ c x
      left_inv := fun x => by
        simp only [Matrix.mulVec_mulVec, o4_inv_mul, Matrix.one_mulVec]
      right_inv := fun x => by
        simp only [Matrix.mulVec_mulVec, o4_mul_inv, Matrix.one_mulVec] }
private theorem o4Equiv_apply (Q : O4) (x : AmbientSpace) :
    o4Equiv Q x = (Q : Matrix (Fin 4) (Fin 4) ℝ).mulVec x := rfl
private theorem o4Equiv_inv_apply (Q : O4) (x : AmbientSpace) :
    o4Equiv Q⁻¹ (o4Equiv Q x) = x := by
  simp only [o4Equiv_apply, Matrix.mulVec_mulVec, o4_inv_mul, Matrix.one_mulVec]
private theorem o4_transpose_mul_self (Q : O4) :
    (Q : Matrix (Fin 4) (Fin 4) ℝ).transpose * (Q : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
  have h := (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).1 Q.2
  simpa [Matrix.star_eq_conjTranspose] using h
private theorem euclidNorm_o4Equiv (Q : O4) (v : AmbientSpace) :
    euclidNorm (o4Equiv Q v) = euclidNorm v := by
  simp only [euclidNorm, o4Equiv_apply]
  congr 1
  set M := (Q : Matrix (Fin 4) (Fin 4) ℝ)
  have e : ∀ w : AmbientSpace, ∑ μ, w μ ^ 2 = w ⬝ᵥ w := fun w => by simp [dotProduct, sq]
  rw [e, e, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
    o4_transpose_mul_self, Matrix.one_mulVec]
private theorem o4Equiv_measurePreserving (Q : O4) :
    MeasurePreserving (o4Equiv Q) volume volume := by
  have hd : (Q : Matrix (Fin 4) (Fin 4) ℝ).det * (Q : Matrix (Fin 4) (Fin 4) ℝ).det = 1 := by
    have := congrArg Matrix.det (o4_transpose_mul_self Q)
    simpa [Matrix.det_mul, Matrix.det_transpose] using this
  have hne : (Q : Matrix (Fin 4) (Fin 4) ℝ).det ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have habs : |((Q : Matrix (Fin 4) (Fin 4) ℝ).det)⁻¹| = 1 := by
    have h1 : |(Q : Matrix (Fin 4) (Fin 4) ℝ).det| = 1 := by
      have : |(Q : Matrix (Fin 4) (Fin 4) ℝ).det| * |(Q : Matrix (Fin 4) (Fin 4) ℝ).det| = 1 := by
        rw [← abs_mul, hd, abs_one]
      nlinarith [abs_nonneg (Q : Matrix (Fin 4) (Fin 4) ℝ).det]
    rw [abs_inv, h1, inv_one]
  refine ⟨(o4Equiv Q).continuous.measurable, ?_⟩
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hne
  rw [habs, ENNReal.ofReal_one, one_smul] at h
  exact h
private theorem rotateFun_eq_comp {E : Type*} (R : O4) (f : AmbientSpace → E) :
    rotateFun R f = f ∘ (o4Equiv R⁻¹).toHomeomorph := rfl
private theorem rotateFun_mem_compactC1Real (R : O4) {f : AmbientSpace → ℂ}
    (h : f ∈ compactC1Real) :
    rotateFun R f ∈ compactC1Real := by
  rw [rotateFun_eq_comp]
  refine ⟨⟨ContDiff.comp h.1.1 (o4Equiv R⁻¹).contDiff, ?_, subset_univ _⟩,
    fun x => h.2 _⟩
  rw [tsupport_comp_eq_preimage]
  exact (o4Equiv R⁻¹).toHomeomorph.isCompact_preimage.2 h.1.2.1
private theorem rotateFun_disjointSupports (R : O4) {f g : AmbientSpace → ℂ}
    (h : DisjointSupports f g) :
    DisjointSupports (rotateFun R f) (rotateFun R g) := by
  simp only [DisjointSupports, rotateFun_eq_comp, tsupport_comp_eq_preimage]
  exact Disjoint.preimage _ h
private theorem form_rotateFun {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {s : ℝ → ℝ}
    (hs : HasRadialProfile S s) (R : O4) {f₁ f₂ : AmbientSpace → ℂ}
    (h₁ : f₁ ∈ compactC1Real) (h₂ : f₂ ∈ compactC1Real) (hd : DisjointSupports f₁ f₂) :
    S (rotateFun R f₁) (rotateFun R f₂) = S f₁ f₂ := by
  have a := hs _ (rotateFun_mem_compactC1Real R h₁) _ (rotateFun_mem_compactC1Real R h₂)
    (rotateFun_disjointSupports R hd)
  have b := hs _ h₁ _ h₂ hd
  have mp := o4Equiv_measurePreserving R
  have me : MeasurableEmbedding (o4Equiv R) :=
    (o4Equiv R).toHomeomorph.measurableEmbedding
  apply Complex.ofReal_injective
  rw [a, b]
  simp only [lebesgueIntegral, integralWrt]
  rw [← mp.integral_comp me]
  congr 1
  funext u'
  rw [← mp.integral_comp me]
  congr 1
  funext u
  have e : ∀ (f : AmbientSpace → ℂ) (x : AmbientSpace), rotateFun R f (o4Equiv R x) = f x := by
    intro f x
    rw [rotateFun_eq_comp]
    simp only [Function.comp_apply]
    exact congrArg f (o4Equiv_inv_apply R x)
  rw [e, e, ← map_sub, euclidNorm_o4Equiv]
private theorem eq_of_coordVec_eq {a b : Fin 4} (h : coordVec a = coordVec b) :
    a = b := by
  by_contra hne
  have := congrFun h a
  simp [PeriodicLattice.coordVec, hne] at this
theorem PlaneKernelsToOrthogonalInvariance.proof
    (hA : RealAnalyticity.CoordRealAnalyticIffAnalytic) (hKer : AnalyticKernel.Statement)
    (hTr : KernelAxisSymmetries.Statement) (hEl : ReflectionsPlaneFacts.Statement) :
    PlaneKernelsToOrthogonalInvariance.Statement := by
  intro St S hS hP hplane
  have hK : IsAnalyticKernel S (formKernel S) := (hKer St S hS hP).1
  have han := analyticOnNhd_of_isRealAnalytic hA hK.analytic
  have hc := continuousOn_of_analyticOnNhd han
  have hcorr : ProfileCorrProperties := hEl.2.2.2.2.2.2.2
  have heven : ∀ y ζ : Fin 2 → ℝ, y ≠ 0 →
      ofCoords (formKernel S) y (-ζ) = ofCoords (formKernel S) y ζ := by
    intro y ζ hy
    refine (hTr St S hS hP).1.2 y ζ fun h => hy ?_
    exact congrArg Prod.fst h
  have hi : ∀ ξ : AmbientSpace, ξ ≠ 0 → ∀ t : ℝ,
      formKernel S (rotateInPlane t ξ) = formKernel S ξ :=
    fun ξ _ t => formKernel_rotateInPlane hc hcorr heven hplane ξ t
  have hrot := fun (μ ν : Fin 4) (h : μ ≠ ν) (t : ℝ) (ξ : AmbientSpace) (hξ : ξ ≠ 0) =>
    kernel_rotationInCoordPlane hK.invariant hi h t hξ
  have hrad : ∀ ξ : AmbientSpace, ξ ≠ 0 → formKernel S ξ = radialProfile S (euclidNorm ξ) :=
    fun ξ hξ => kernel_eq_on_axis hrot hξ
  have hs := hasRadialProfile_of_formKernel hS hK hrad
  refine ⟨hi, ?_, ⟨radialProfile_isRealAnalyticOnIoi hA han, hrad⟩, hs, ?_⟩
  · rintro μ ν h w hw ⟨σ, hσ⟩ h₃ h₀ t
    have e₃ : σ 3 = μ := eq_of_coordVec_eq ((hσ 3).symm.trans h₃)
    have e₀ : σ 0 = ν := eq_of_coordVec_eq ((hσ 0).symm.trans h₀)
    exact ⟨permConjRotation_eq hw hσ h e₃ e₀ t,
      fun ξ hξ => kernel_permConjRotation hK.invariant hi hw t hξ⟩
  · intro R f₁ h₁ f₂ h₂ hd
    exact form_rotateFun hs R h₁ h₂ hd
end YangMills.Construction.TwoPoints
end
