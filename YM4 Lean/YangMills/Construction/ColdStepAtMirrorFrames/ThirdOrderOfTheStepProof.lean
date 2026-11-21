import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.CouplingFloorOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinatesProof
import YangMills.Construction.ColdStepAtMirrorFrames.TermsInFixedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivativeAlongFieldsProofForm
import YangMills.Construction.ColdStepAtMirrorFrames.ThirdOrderOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesInASpace
import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesOfAComposite
import YangMills.Construction.SummableBoundsOfTheFlow.ScaledExponentIsTheExponentOfTheStepProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Topology Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
open ThirdDerivative
namespace ThirdDerivLocal
section LogOfProduct
open NormedSpace
def imaginaryPart : ℍ[ℝ] →ₗ[ℝ] imaginaryQuaternions where
  toFun q := ⟨q - (q.re : ℍ[ℝ]), by show (q - (q.re : ℍ[ℝ])).re = 0; simp⟩
  map_add' a b := by apply Subtype.ext; ext <;> simp
  map_smul' c a := by apply Subtype.ext; ext <;> simp
theorem imaginaryPart_coe_of_re_eq_zero (q : ℍ[ℝ]) (h : q.re = 0) :
    ((imaginaryPart q : imaginaryQuaternions) : ℍ[ℝ]) = q := by
  show q - (q.re : ℍ[ℝ]) = q
  simp [h]
theorem quaternion_exp_contDiff : ContDiff ℝ 5 (exp : ℍ[ℝ] → ℍ[ℝ]) :=
  contDiff_iff_contDiffAt.mpr fun x => (exp_analytic (𝕂 := ℝ) x).contDiffAt
def expMulExp (z : imaginaryQuaternions × imaginaryQuaternions) : ℍ[ℝ] :=
  exp (z.1 : ℍ[ℝ]) * exp (z.2 : ℍ[ℝ])
theorem expMulExp_contDiff : ContDiff ℝ 5 expMulExp := by
  have c1 : ContDiff ℝ 5 (fun z : imaginaryQuaternions × imaginaryQuaternions => (z.1 : ℍ[ℝ])) :=
    imaginaryQuaternions.subtypeL.contDiff.comp contDiff_fst
  have c2 : ContDiff ℝ 5 (fun z : imaginaryQuaternions × imaginaryQuaternions => (z.2 : ℍ[ℝ])) :=
    imaginaryQuaternions.subtypeL.contDiff.comp contDiff_snd
  exact (quaternion_exp_contDiff.comp c1).mul (quaternion_exp_contDiff.comp c2)
theorem norm_expMulExp (z : imaginaryQuaternions × imaginaryQuaternions) : ‖expMulExp z‖ = 1 := by
  have h : ∀ w : imaginaryQuaternions, ‖exp (w : ℍ[ℝ])‖ = 1 := fun w => by
    have hw : (w : ℍ[ℝ]).re = 0 := w.2
    rw [Quaternion.norm_exp, hw]
    simp
  simp only [expMulExp, norm_mul, h, one_mul]
theorem expMulExp_zero : expMulExp (0 : imaginaryQuaternions × imaginaryQuaternions) = 1 := by
  simp [expMulExp]
theorem exists_bound_iteratedFDeriv_of_hasCompactSupport {E G : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {Λ : E → G} (hΛ : ContDiff ℝ 5 Λ) (hcs : HasCompactSupport Λ) :
    ∃ CL : ℝ, 0 ≤ CL ∧ ∀ (z : E) (j : ℕ), j ≤ 5 → ‖iteratedFDeriv ℝ j Λ z‖ ≤ CL := by
  have hb : ∀ j : ℕ, j ≤ 5 → ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖iteratedFDeriv ℝ j Λ z‖ ≤ C := by
    intro j hj
    have hc : Continuous (iteratedFDeriv ℝ j Λ) :=
      hΛ.continuous_iteratedFDeriv (by exact_mod_cast hj)
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (hcs.iteratedFDeriv j)
    exact ⟨|C|, abs_nonneg _, fun z => (hC z).trans (le_abs_self C)⟩
  choose! C hC0 hC using hb
  refine ⟨∑ j ∈ Finset.range 6, C j, Finset.sum_nonneg fun j hj => hC0 j (by
      have := Finset.mem_range.mp hj
      omega), fun z j hj => ?_⟩
  refine (hC j hj z).trans ?_
  exact Finset.single_le_sum (f := C) (fun i hi => hC0 i (by
    have := Finset.mem_range.mp hi
    omega)) (Finset.mem_range.mpr (by omega))
theorem exists_smooth_log_of_product :
    ∃ (Λ : imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions) (r₀ CL : ℝ),
    0 < r₀ ∧ 0 ≤ CL ∧ ContDiff ℝ 5 Λ ∧
    (∀ p q : imaginaryQuaternions, ‖p‖ < r₀ → ‖q‖ < r₀ → expUnit (Λ (p, q)) = expUnit p * expUnit q) ∧
    (∀ p : imaginaryQuaternions, ‖p‖ < r₀ → Λ (p, 0) = p) ∧
    ∀ (z : imaginaryQuaternions × imaginaryQuaternions) (j : ℕ), j ≤ 5 →
      ‖iteratedFDeriv ℝ j Λ z‖ ≤ CL := by
  have hA : ContDiffAt ℝ 5 (exp : ℍ[ℝ] → ℍ[ℝ]) 0 := quaternion_exp_contDiff.contDiffAt
  let f' : ℍ[ℝ] ≃L[ℝ] ℍ[ℝ] := ContinuousLinearEquiv.refl ℝ _
  have hf' : HasFDerivAt (exp : ℍ[ℝ] → ℍ[ℝ]) (f' : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) 0 :=
    hasFDerivAt_exp_zero (𝕂 := ℝ)
  have hn : (5 : WithTop ℕ∞) ≠ 0 := by norm_num
  let Lq := hA.localInverse hf' hn
  have hLc : ContDiffAt ℝ 5 Lq 1 := by
    have := hA.to_localInverse hf' hn
    rwa [exp_zero] at this
  have hRi : ∀ᶠ y in 𝓝 (1 : ℍ[ℝ]), exp (Lq y) = y := by
    have := (hA.hasStrictFDerivAt' hf' hn).eventually_right_inverse
    rw [exp_zero] at this
    exact this
  have hLi : ∀ᶠ x in 𝓝 (0 : ℍ[ℝ]), Lq (exp x) = x :=
    (hA.hasStrictFDerivAt' hf' hn).eventually_left_inverse
  obtain ⟨V₁, hV, hVo, h1V⟩ := mem_nhds_iff.mp ((hLc.eventually (by simp)).and hRi)
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.eventually_nhds_iff.mp hLi
  let P : ℍ[ℝ] →L[ℝ] imaginaryQuaternions := LinearMap.toContinuousLinearMap imaginaryPart
  let Θ₀ : imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions :=
    fun z => P (Lq (expMulExp z))
  let U : Set (imaginaryQuaternions × imaginaryQuaternions) := expMulExp ⁻¹' V₁
  have hUo : IsOpen U := hVo.preimage expMulExp_contDiff.continuous
  have h0U : (0 : imaginaryQuaternions × imaginaryQuaternions) ∈ U := by
    show expMulExp 0 ∈ V₁
    rw [expMulExp_zero]
    exact h1V
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.isOpen_iff.mp hUo 0 h0U
  set ε := min ε₁ ε₂ with hε
  have hε0 : 0 < ε := lt_min hε₁ hε₂
  have hΘa : ∀ z ∈ U, ContDiffAt ℝ 5 Θ₀ z := fun z hz =>
    P.contDiff.contDiffAt.comp z ((hV hz).1.comp z expMulExp_contDiff.contDiffAt)
  have hre : ∀ z ∈ U, (Lq (expMulExp z)).re = 0 := by
    intro z hz
    have e : exp (Lq (expMulExp z)) = expMulExp z := (hV hz).2
    have h1 : ‖exp (Lq (expMulExp z))‖ = 1 := by rw [e, norm_expMulExp]
    rw [Quaternion.norm_exp, ← Real.exp_eq_exp_ℝ, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    exact Real.exp_eq_one_iff _ |>.mp h1
  have hΘ1 : ∀ z ∈ U, ((Θ₀ z : imaginaryQuaternions) : ℍ[ℝ]) = Lq (expMulExp z) := fun z hz =>
    imaginaryPart_coe_of_re_eq_zero _ (hre z hz)
  have hexp : ∀ z ∈ U, expUnit (Θ₀ z) = expUnit z.1 * expUnit z.2 := by
    intro z hz
    apply Subtype.ext
    show exp ((Θ₀ z : imaginaryQuaternions) : ℍ[ℝ]) = exp (z.1 : ℍ[ℝ]) * exp (z.2 : ℍ[ℝ])
    rw [hΘ1 z hz, (hV hz).2]
    rfl
  let f : ContDiffBump (0 : imaginaryQuaternions × imaginaryQuaternions) :=
    ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hfc : ContDiff ℝ 5 (fun z => f z) := f.contDiff
  let Λ : imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions := fun z => f z • Θ₀ z
  have hεε : ε ≤ ε₂ := min_le_right _ _
  have hΛ : ContDiff ℝ 5 Λ := by
    rw [contDiff_iff_contDiffAt]
    intro z
    rcases lt_or_ge ‖z‖ ε₂ with hz | hz
    · have hzU : z ∈ U := hb₂ (by simpa using hz)
      exact hfc.contDiffAt.smul (hΘa z hzU)
    · have hev : Λ =ᶠ[𝓝 z] fun _ => 0 := by
        have : {w : imaginaryQuaternions × imaginaryQuaternions | ε / 2 < ‖w‖} ∈ 𝓝 z :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds (by
            show ε / 2 < ‖z‖
            linarith)
        filter_upwards [this] with w hw
        have : f w = 0 := f.zero_of_le_dist (by
          show ε / 2 ≤ dist w 0
          rw [dist_zero_right]
          exact (le_of_lt hw))
        simp [Λ, this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hcs : HasCompactSupport Λ := by
    refine HasCompactSupport.intro
      (isCompact_closedBall (0 : imaginaryQuaternions × imaginaryQuaternions) (ε / 2)) fun z hz => ?_
    have : f z = 0 := f.zero_of_le_dist (by
      show ε / 2 ≤ dist z 0
      have : ¬ dist z 0 ≤ ε / 2 := hz
      linarith)
    simp [Λ, this]
  obtain ⟨CL, hCL0, hCL⟩ := exists_bound_iteratedFDeriv_of_hasCompactSupport hΛ hcs
  refine ⟨Λ, ε / 4, CL, by positivity, hCL0, hΛ, ?_, ?_, hCL⟩
  · intro p q hp hq
    have hz : ‖((p, q) : imaginaryQuaternions × imaginaryQuaternions)‖ < ε / 4 := by
      rw [Prod.norm_def]
      exact max_lt hp hq
    have h1 : f (p, q) = 1 := f.one_of_mem_closedBall (by
      show dist ((p, q) : imaginaryQuaternions × imaginaryQuaternions) 0 ≤ ε / 4
      rw [dist_zero_right]
      exact hz.le)
    have hU : ((p, q) : imaginaryQuaternions × imaginaryQuaternions) ∈ U := hb₂ (by
      rw [Metric.mem_ball, dist_zero_right]
      linarith)
    show expUnit (f (p, q) • Θ₀ (p, q)) = _
    rw [h1, one_smul, hexp _ hU]
  · intro p hp
    have hz : ‖((p, 0) : imaginaryQuaternions × imaginaryQuaternions)‖ < ε / 4 := by
      rw [Prod.norm_def]
      simpa using hp
    have h1 : f (p, 0) = 1 := f.one_of_mem_closedBall (by
      show dist ((p, 0) : imaginaryQuaternions × imaginaryQuaternions) 0 ≤ ε / 4
      rw [dist_zero_right]
      exact hz.le)
    show f (p, 0) • Θ₀ (p, 0) = p
    rw [h1, one_smul]
    have hq : dist (p : ℍ[ℝ]) 0 < ε₁ := by
      rw [dist_zero_right]
      have : ε ≤ ε₁ := min_le_left _ _
      have e : ‖(p : ℍ[ℝ])‖ = ‖p‖ := rfl
      rw [e]
      linarith
    have h2 : Lq (exp (p : ℍ[ℝ])) = p := hb₁ hq
    have h3 : expMulExp (p, 0) = exp (p : ℍ[ℝ]) := by
      simp [expMulExp]
    show P (Lq (expMulExp (p, 0))) = p
    rw [h3, h2]
    apply Subtype.ext
    exact imaginaryPart_coe_of_re_eq_zero _ p.2
end LogOfProduct
section Coordinates
def imaginaryCoords (X : imaginaryQuaternions) : BondVector :=
  WithLp.toLp 2 ![(X : ℍ[ℝ]).imI, (X : ℍ[ℝ]).imJ, (X : ℍ[ℝ]).imK]
theorem toImaginary_imaginaryCoords (X : imaginaryQuaternions) : toImaginary (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivLocal.imaginaryCoords X) = X := by
  have h : (X : ℍ[ℝ]).re = 0 := X.2
  apply Subtype.ext
  ext <;> simp [toImaginary, _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivLocal.imaginaryCoords, h]
theorem imaginaryCoords_toImaginary (v : BondVector) : _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivLocal.imaginaryCoords (toImaginary v) = v := by
  ext i
  fin_cases i <;> rfl
theorem toImaginary_add (v w : BondVector) : toImaginary (v + w) = toImaginary v + toImaginary w := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.toImaginary_add <;> assumption
theorem toImaginary_smul (c : ℝ) (v : BondVector) : toImaginary (c • v) = c • toImaginary v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.toImaginary_smul <;> assumption
theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
def coordsIsometry : BondVector ≃ₗᵢ[ℝ] imaginaryQuaternions where
  toFun := toImaginary
  invFun := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivLocal.imaginaryCoords
  left_inv := imaginaryCoords_toImaginary
  right_inv := toImaginary_imaginaryCoords
  map_add' := toImaginary_add
  map_smul' := toImaginary_smul
  norm_map' := norm_toImaginary
def basisVector (i : Fin 3) : BondVector := EuclideanSpace.single i (1 : ℝ)
theorem norm_basisVector (i : Fin 3) : ‖basisVector i‖ = 1 := by simp [basisVector]
theorem fieldC1Bound_of_fieldC2Bound {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ}
    {z : ι → BondVector → BondVector} {u : ι → ℝ} (h : FieldC2Bound ρ z u) : FieldC1Bound ρ z u :=
  ⟨fun b => (h.smooth b).of_le (by norm_num), h.norm_le, h.deriv_le⟩
theorem expWeight_nonneg {X : Type} {δ : X → X → ℝ} (r : ℝ) (x y : X) : 0 ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ r x y :=
  (Real.exp_pos _).le
theorem radialWeightProd_cutoffFactor {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ℝ) (p : ℝ → ℝ) :
    radialWeightProd (ι := ι) (cutoffFactor ρ p) = radialWeightProd (extendedCutoff ρ p) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.radialWeightProd_cutoffFactor <;> assumption
theorem extendedCutoff_isRadialCutoff {ρ : ℝ} {p : ℝ → ℝ} (hR : CutoffFactorIsRadialCutoff)
    (hρ : 0 < ρ) (hp : IsCutoff ρ p) : IsRadialCutoff ρ (extendedCutoff ρ p) := hR ρ p hρ hp
theorem extendedCutoff_eq_zero {ρ : ℝ} {p : ℝ → ℝ} (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) {u : ℝ} (h : ρ ≤ u) : extendedCutoff ρ p u = 0 :=
  (extendedCutoff_isRadialCutoff hR hρ hp).zero u h
section Fields
def liftPoint (w₀ : imaginaryQuaternions) (v : BondVector) : imaginaryQuaternions × imaginaryQuaternions :=
  (w₀ + coordsIsometry v, 0)
def firstInclusion : BondVector →L[ℝ] imaginaryQuaternions × imaginaryQuaternions :=
  (ContinuousLinearMap.inl ℝ imaginaryQuaternions imaginaryQuaternions).comp
    (coordsIsometry.toContinuousLinearEquiv : BondVector →L[ℝ] imaginaryQuaternions)
theorem liftPoint_eq (w₀ : imaginaryQuaternions) (v : BondVector) :
    liftPoint w₀ v = firstInclusion v + (w₀, 0) := by
  simp [liftPoint, firstInclusion, add_comm]
theorem norm_firstInclusion_le : ‖firstInclusion‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp [firstInclusion, Prod.norm_def]
def pullback (g : imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (w₀ : imaginaryQuaternions) (v : BondVector) : BondVector :=
  coordsIsometry.symm (g (liftPoint w₀ v))
theorem pullback_bounds {g : imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    (hg : ContDiff ℝ 2 g) {B : ℝ}
    (hB : ∀ (z : imaginaryQuaternions × imaginaryQuaternions) (j : ℕ), j ≤ 2 →
      ‖iteratedFDeriv ℝ j g z‖ ≤ B) (w₀ : imaginaryQuaternions) (v : BondVector) :
    ‖pullback g w₀ v‖ ≤ B ∧ ‖fderiv ℝ (pullback g w₀) v‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ (pullback g w₀)) v‖ ≤ B := by
  have key : ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j (pullback g w₀) v‖ ≤ B := by
    intro j hj
    have e1 : pullback g w₀ = coordsIsometry.symm ∘ ((fun z => g (z + (w₀, 0))) ∘ firstInclusion) := by
      funext u
      simp [pullback, liftPoint_eq]
    rw [e1, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    have hsh : ContDiff ℝ 2 (fun z : imaginaryQuaternions × imaginaryQuaternions => g (z + (w₀, 0))) :=
      hg.comp (contDiff_id.add contDiff_const)
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right firstInclusion hsh v (by exact_mod_cast hj)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have e2 : iteratedFDeriv ℝ j (fun z : imaginaryQuaternions × imaginaryQuaternions => g (z + (w₀, 0)))
        (firstInclusion v) = iteratedFDeriv ℝ j g (firstInclusion v + (w₀, 0)) := by
      simpa using iteratedFDeriv_comp_add_right j (f := g) (w₀, 0) (firstInclusion v)
    rw [e2]
    have p1 : ∏ _i : Fin j, ‖firstInclusion‖ ≤ 1 := by
      rw [Finset.prod_const]
      exact pow_le_one₀ (ContinuousLinearMap.opNorm_nonneg firstInclusion) norm_firstInclusion_le
    have := hB (firstInclusion v + (w₀, 0)) j hj
    nlinarith [norm_nonneg (iteratedFDeriv ℝ j g (firstInclusion v + (w₀, 0)))]
  refine ⟨?_, ?_, ?_⟩
  · have := key 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero] at this
  · have := key 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at this
  · have := key 2 (by norm_num)
    rw [show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at this
    exact this
end Fields
end Coordinates
section DirectionalDerivatives
section Generic
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {Λ : E → G} {CL : ℝ}
def dirDeriv (a : E) (f : E → G) (z : E) : G := fderiv ℝ f z a
theorem dirDeriv_contDiff {N : ℕ} {f : E → G} (hf : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) f) (a : E) :
    ContDiff ℝ N (dirDeriv a f) := by
  have h1 : ContDiff ℝ N (fderiv ℝ f) := hf.fderiv_right (m := N) (by
    exact_mod_cast le_rfl)
  exact h1.clm_apply contDiff_const
theorem norm_iteratedFDeriv_dirDeriv_le {N : ℕ} {f : E → G}
    (hf : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) f) (a z : E) (j : ℕ)
    (hj : j ≤ N) : ‖iteratedFDeriv ℝ j (dirDeriv a f) z‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (j + 1) f z‖ := by
  have h1 : ContDiff ℝ N (fderiv ℝ f) := hf.fderiv_right (m := N) (by
    exact_mod_cast le_rfl)
  set T : (E →L[ℝ] G) →L[ℝ] G := ContinuousLinearMap.apply ℝ G a with hT
  have e : dirDeriv a f = T ∘ fderiv ℝ f := rfl
  rw [e]
  have hT1 : ‖T‖ ≤ ‖a‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa [hT, mul_comm] using x.le_opNorm a
  have h2 := T.norm_iteratedFDeriv_comp_left (f := fderiv ℝ f) (x := z) (N := N) (n := j)
    h1.contDiffAt (by exact_mod_cast hj)
  refine h2.trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_right hT1 (norm_nonneg _)
def dirDeriv₁ (Λ : E → G) (a : E) : E → G := dirDeriv a Λ
def dirDeriv₂ (Λ : E → G) (a b : E) : E → G := dirDeriv a (dirDeriv b Λ)
def dirDeriv₃ (Λ : E → G) (a b c : E) : E → G := dirDeriv a (dirDeriv b (dirDeriv c Λ))
theorem contDiff_four_add_one (hΛ : ContDiff ℝ 5 Λ) : ContDiff ℝ ((4 + 1 : ℕ) : WithTop ℕ∞) Λ := by
  simpa using hΛ
theorem dirDeriv₁_contDiff (hΛ : ContDiff ℝ 5 Λ) (a : E) : ContDiff ℝ 2 (dirDeriv₁ Λ a) :=
  (dirDeriv_contDiff (N := 4) (contDiff_four_add_one hΛ) a).of_le (by norm_num)
theorem dirDeriv_contDiff_four (hΛ : ContDiff ℝ 5 Λ) (b : E) :
    ContDiff ℝ ((3 + 1 : ℕ) : WithTop ℕ∞) (dirDeriv b Λ) := by
  simpa using dirDeriv_contDiff (N := 4) (contDiff_four_add_one hΛ) b
theorem dirDeriv_dirDeriv_contDiff_three (hΛ : ContDiff ℝ 5 Λ) (b c : E) :
    ContDiff ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) (dirDeriv b (dirDeriv c Λ)) := by
  simpa using dirDeriv_contDiff (N := 3) (dirDeriv_contDiff_four hΛ c) b
theorem dirDeriv₂_contDiff (hΛ : ContDiff ℝ 5 Λ) (a b : E) : ContDiff ℝ 2 (dirDeriv₂ Λ a b) :=
  (dirDeriv_contDiff (N := 3) (dirDeriv_contDiff_four hΛ b) a).of_le (by norm_num)
theorem dirDeriv₃_contDiff (hΛ : ContDiff ℝ 5 Λ) (a b c : E) : ContDiff ℝ 2 (dirDeriv₃ Λ a b c) := by
  have := dirDeriv_contDiff (N := 2) (dirDeriv_dirDeriv_contDiff_three hΛ b c) a
  simpa [dirDeriv₃] using this
theorem dirDeriv₁_bound (hΛ : ContDiff ℝ 5 Λ)
    (hCL : ∀ (z : E) (j : ℕ), j ≤ 5 → ‖iteratedFDeriv ℝ j Λ z‖ ≤ CL)
    (a z : E) (j : ℕ) (hj : j ≤ 2) : ‖iteratedFDeriv ℝ j (dirDeriv₁ Λ a) z‖ ≤ CL * ‖a‖ := by
  have h := norm_iteratedFDeriv_dirDeriv_le (N := 4) (contDiff_four_add_one hΛ) a z j (by omega)
  have := hCL z (j + 1) (by omega)
  have n := norm_nonneg a
  refine h.trans ?_
  nlinarith
theorem dirDeriv₂_bound (hΛ : ContDiff ℝ 5 Λ)
    (hCL : ∀ (z : E) (j : ℕ), j ≤ 5 → ‖iteratedFDeriv ℝ j Λ z‖ ≤ CL)
    (a b z : E) (j : ℕ) (hj : j ≤ 2) : ‖iteratedFDeriv ℝ j (dirDeriv₂ Λ a b) z‖ ≤ CL * (‖a‖ * ‖b‖) := by
  have h1 := norm_iteratedFDeriv_dirDeriv_le (N := 3) (dirDeriv_contDiff_four hΛ b) a z j (by omega)
  have h2 := norm_iteratedFDeriv_dirDeriv_le (N := 4) (contDiff_four_add_one hΛ) b z (j + 1) (by omega)
  have h3 := hCL z (j + 1 + 1) (by omega)
  have n1 := norm_nonneg a
  have n2 := norm_nonneg b
  have t1 := mul_le_mul_of_nonneg_left h3 n2
  have t2 := mul_le_mul_of_nonneg_left (h2.trans t1) n1
  refine h1.trans (t2.trans (le_of_eq ?_))
  ring
theorem dirDeriv₃_bound (hΛ : ContDiff ℝ 5 Λ)
    (hCL : ∀ (z : E) (j : ℕ), j ≤ 5 → ‖iteratedFDeriv ℝ j Λ z‖ ≤ CL)
    (a b c z : E) (j : ℕ) (hj : j ≤ 2) :
    ‖iteratedFDeriv ℝ j (dirDeriv₃ Λ a b c) z‖ ≤ CL * (‖a‖ * ‖b‖ * ‖c‖) := by
  have h1 := norm_iteratedFDeriv_dirDeriv_le (N := 2) (dirDeriv_dirDeriv_contDiff_three hΛ b c) a z j
    (by omega)
  have h2 := norm_iteratedFDeriv_dirDeriv_le (N := 3) (dirDeriv_contDiff_four hΛ c) b z (j + 1) (by omega)
  have h3 := norm_iteratedFDeriv_dirDeriv_le (N := 4) (contDiff_four_add_one hΛ) c z (j + 1 + 1)
    (by omega)
  have h4 := hCL z (j + 1 + 1 + 1) (by omega)
  have n1 := norm_nonneg a
  have n2 := norm_nonneg b
  have n3 := norm_nonneg c
  have t1 := mul_le_mul_of_nonneg_left h4 n3
  have t2 := mul_le_mul_of_nonneg_left (h3.trans t1) n2
  have t3 := mul_le_mul_of_nonneg_left (h2.trans t2) n1
  refine h1.trans (t3.trans (le_of_eq ?_))
  ring
theorem iteratedFDeriv_one_eq_dirDeriv (f : E → G) (a z : E) :
    iteratedFDeriv ℝ 1 f z ![a] = dirDeriv a f z := by
  rw [iteratedFDeriv_one_apply]
  rfl
theorem iteratedFDeriv_two_eq_dirDeriv {f : E → G} (hf : ContDiff ℝ 3 f) (a b z : E) :
    iteratedFDeriv ℝ 2 f z ![a, b] = dirDeriv a (dirDeriv b f) z := by
  rw [iteratedFDeriv_two_apply]
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) z
  have h2 := h1.hasFDerivAt.clm_apply (hasFDerivAt_const b z)
  have h3 : fderiv ℝ (dirDeriv b f) z = _ := h2.fderiv
  show fderiv ℝ (fderiv ℝ f) z a b = fderiv ℝ (dirDeriv b f) z a
  rw [h3]
  simp
theorem iteratedFDeriv_three_eq_dirDeriv {f : E → G} (hf : ContDiff ℝ 4 f) (a b c z : E) :
    iteratedFDeriv ℝ 3 f z ![a, b, c] = dirDeriv a (dirDeriv b (dirDeriv c f)) z := by
  have hs : ContDiff ℝ 3 f := hf.of_le (by norm_num)
  have e1' : dirDeriv b (dirDeriv c f) = fun w => iteratedFDeriv ℝ 2 f w ![b, c] := by
    funext w
    rw [iteratedFDeriv_two_eq_dirDeriv hs]
  have h2 : ContDiff ℝ 1 (iteratedFDeriv ℝ 2 f) :=
    hf.iteratedFDeriv_right (by norm_num)
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) z := h2.differentiable (by norm_num) z
  have h3 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) G ![b, c]).hasFDerivAt.comp z
    hd.hasFDerivAt
  have h4 : fderiv ℝ (fun w => iteratedFDeriv ℝ 2 f w ![b, c]) z = _ := h3.fderiv
  rw [iteratedFDeriv_succ_apply_left]
  show (fderiv ℝ (iteratedFDeriv ℝ 2 f) z a) (Fin.tail ![a, b, c]) =
    fderiv ℝ (dirDeriv b (dirDeriv c f)) z a
  rw [e1', h4]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply]
  congr 1
theorem norm_iteratedFDeriv_add_le_of_contDiff {f g : E → G} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (z : E) (j : ℕ)
    (hj : j ≤ 2) : ‖iteratedFDeriv ℝ j (fun w => f w + g w) z‖ ≤
      ‖iteratedFDeriv ℝ j f z‖ + ‖iteratedFDeriv ℝ j g z‖ := by
  have h1 : ContDiffAt ℝ j f z := (hf.of_le (by exact_mod_cast hj)).contDiffAt
  have h2 : ContDiffAt ℝ j g z := (hg.of_le (by exact_mod_cast hj)).contDiffAt
  have e := iteratedFDeriv_add_apply (x := z) (i := j) h1 h2
  have e' : iteratedFDeriv ℝ j (fun w => f w + g w) z =
      iteratedFDeriv ℝ j f z + iteratedFDeriv ℝ j g z := e
  rw [e']
  exact norm_add_le _ _
def secondOrderTerm (Λ : E → G) (a b c : E) (z : E) : G := dirDeriv₂ Λ a b z + dirDeriv₁ Λ c z
def thirdOrderTerm (Λ : E → G) (a₁ a₂ a₃ a₁₂ a₁₃ a₂₃ a₁₂₃ : E) (z : E) : G :=
  dirDeriv₃ Λ a₁ a₂ a₃ z + dirDeriv₂ Λ a₁₂ a₃ z + dirDeriv₂ Λ a₁₃ a₂ z + dirDeriv₂ Λ a₂₃ a₁ z +
    dirDeriv₁ Λ a₁₂₃ z
theorem secondOrderTerm_contDiff (hΛ : ContDiff ℝ 5 Λ) (a b c : E) :
    ContDiff ℝ 2 (secondOrderTerm Λ a b c) :=
  (dirDeriv₂_contDiff hΛ _ _).add (dirDeriv₁_contDiff hΛ _)
theorem thirdOrderTerm_contDiff (hΛ : ContDiff ℝ 5 Λ) (a₁ a₂ a₃ a₁₂ a₁₃ a₂₃ a₁₂₃ : E) :
    ContDiff ℝ 2 (thirdOrderTerm Λ a₁ a₂ a₃ a₁₂ a₁₃ a₂₃ a₁₂₃) :=
  ((((dirDeriv₃_contDiff hΛ _ _ _).add (dirDeriv₂_contDiff hΛ _ _)).add (dirDeriv₂_contDiff hΛ _ _)).add
    (dirDeriv₂_contDiff hΛ _ _)).add (dirDeriv₁_contDiff hΛ _)
theorem secondOrderTerm_bound (hΛ : ContDiff ℝ 5 Λ)
    (hCL : ∀ (z : E) (j : ℕ), j ≤ 5 → ‖iteratedFDeriv ℝ j Λ z‖ ≤ CL)
    (a b c : E) (z : E) (j : ℕ) (hj : j ≤ 2) :
    ‖iteratedFDeriv ℝ j (secondOrderTerm Λ a b c) z‖ ≤ CL * (‖a‖ * ‖b‖ + ‖c‖) := by
  have h := norm_iteratedFDeriv_add_le_of_contDiff (dirDeriv₂_contDiff hΛ a b) (dirDeriv₁_contDiff hΛ c)
    z j hj
  have b1 := dirDeriv₂_bound hΛ hCL a b z j hj
  have b2 := dirDeriv₁_bound hΛ hCL c z j hj
  have e : secondOrderTerm Λ a b c = fun w => dirDeriv₂ Λ a b w + dirDeriv₁ Λ c w := rfl
  rw [e]
  refine h.trans ?_
  calc _ ≤ CL * (‖a‖ * ‖b‖) + CL * ‖c‖ := add_le_add b1 b2
    _ = _ := by ring
theorem thirdOrderTerm_bound (hΛ : ContDiff ℝ 5 Λ)
    (hCL : ∀ (z : E) (j : ℕ), j ≤ 5 → ‖iteratedFDeriv ℝ j Λ z‖ ≤ CL)
    (a₁ a₂ a₃ a₁₂ a₁₃ a₂₃ a₁₂₃ : E) (z : E) (j : ℕ) (hj : j ≤ 2) :
    ‖iteratedFDeriv ℝ j (thirdOrderTerm Λ a₁ a₂ a₃ a₁₂ a₁₃ a₂₃ a₁₂₃) z‖ ≤
      CL * (‖a₁‖ * ‖a₂‖ * ‖a₃‖ + ‖a₁₂‖ * ‖a₃‖ + ‖a₁₃‖ * ‖a₂‖ + ‖a₂₃‖ * ‖a₁‖ + ‖a₁₂₃‖) := by
  have s3 := dirDeriv₃_contDiff hΛ a₁ a₂ a₃
  have s2a := dirDeriv₂_contDiff hΛ a₁₂ a₃
  have s2b := dirDeriv₂_contDiff hΛ a₁₃ a₂
  have s2c := dirDeriv₂_contDiff hΛ a₂₃ a₁
  have s1 := dirDeriv₁_contDiff hΛ a₁₂₃
  have b3 := dirDeriv₃_bound hΛ hCL a₁ a₂ a₃ z j hj
  have b2a := dirDeriv₂_bound hΛ hCL a₁₂ a₃ z j hj
  have b2b := dirDeriv₂_bound hΛ hCL a₁₃ a₂ z j hj
  have b2c := dirDeriv₂_bound hΛ hCL a₂₃ a₁ z j hj
  have b1 := dirDeriv₁_bound hΛ hCL a₁₂₃ z j hj
  have t1 := norm_iteratedFDeriv_add_le_of_contDiff s3 s2a z j hj
  have t2 := norm_iteratedFDeriv_add_le_of_contDiff (s3.add s2a) s2b z j hj
  have t3 := norm_iteratedFDeriv_add_le_of_contDiff ((s3.add s2a).add s2b) s2c z j hj
  have t4 := norm_iteratedFDeriv_add_le_of_contDiff (((s3.add s2a).add s2b).add s2c) s1 z j hj
  have e : thirdOrderTerm Λ a₁ a₂ a₃ a₁₂ a₁₃ a₂₃ a₁₂₃ = fun w => dirDeriv₃ Λ a₁ a₂ a₃ w +
      dirDeriv₂ Λ a₁₂ a₃ w + dirDeriv₂ Λ a₁₃ a₂ w + dirDeriv₂ Λ a₂₃ a₁ w + dirDeriv₁ Λ a₁₂₃ w := rfl
  rw [e]
  have fin : CL * (‖a₁‖ * ‖a₂‖ * ‖a₃‖ + ‖a₁₂‖ * ‖a₃‖ + ‖a₁₃‖ * ‖a₂‖ + ‖a₂₃‖ * ‖a₁‖ + ‖a₁₂₃‖) =
      CL * (‖a₁‖ * ‖a₂‖ * ‖a₃‖) + CL * (‖a₁₂‖ * ‖a₃‖) + CL * (‖a₁₃‖ * ‖a₂‖) + CL * (‖a₂₃‖ * ‖a₁‖) +
        CL * ‖a₁₂₃‖ := by ring
  rw [fin]
  linarith
end Generic
abbrev LiePair : Type := imaginaryQuaternions × imaginaryQuaternions
theorem pullback_contDiff {g : LiePair → imaginaryQuaternions} (hg : ContDiff ℝ 2 g)
    (w₀ : imaginaryQuaternions) : ContDiff ℝ 2 (pullback g w₀) := by
  have e1 : pullback g w₀ = coordsIsometry.symm ∘ (g ∘ fun v => firstInclusion v + (w₀, 0)) := by
    funext u
    simp [pullback, liftPoint_eq]
  rw [e1]
  exact (coordsIsometry.symm.toContinuousLinearEquiv : imaginaryQuaternions →L[ℝ] BondVector).contDiff.comp
    (hg.comp (firstInclusion.contDiff.add contDiff_const))
end DirectionalDerivatives
section MovedCoordinates
theorem iteratedFDeriv_succ_sub_const {P D : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup D] [NormedSpace ℝ D] (f : P → D) (c : D) (n : ℕ) (x : P) :
    iteratedFDeriv ℝ (n + 1) (fun τ => f τ - c) x = iteratedFDeriv ℝ (n + 1) f x := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  have e : (fun y => fderiv ℝ (fun τ => f τ - c) y) = fun y => fderiv ℝ f y := by
    funext y
    exact fderiv_sub_const c
  simp only [Function.comp_apply, e]
theorem iteratedFDeriv_three_apply_eq {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (f : P → ℝ)
    (a b c z : P) :
    iteratedFDeriv ℝ 3 f z ![a, b, c] = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z a b c := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  rfl
variable {Λ : LiePair → imaginaryQuaternions} {φ : (Fin 3 → ℝ) → LiePair} {w₀ : imaginaryQuaternions}
  {ι' : Type}
def movedCoord (Λ : LiePair → imaginaryQuaternions) (φ : (Fin 3 → ℝ) → LiePair)
    (w₀ : imaginaryQuaternions) (τ : Fin 3 → ℝ) (v : BondVector) : BondVector :=
  coordsIsometry.symm (Λ (φ τ + (coordsIsometry v, 0)) - w₀)
def pairDeriv₁ (φ : (Fin 3 → ℝ) → LiePair) (u : Fin 3 → ℝ) : LiePair := iteratedFDeriv ℝ 1 φ 0 ![u]
def pairDeriv₂ (φ : (Fin 3 → ℝ) → LiePair) (u u' : Fin 3 → ℝ) : LiePair :=
  iteratedFDeriv ℝ 2 φ 0 ![u, u']
def pairDeriv₃ (φ : (Fin 3 → ℝ) → LiePair) (u u' u'' : Fin 3 → ℝ) : LiePair :=
  iteratedFDeriv ℝ 3 φ 0 ![u, u', u'']
theorem movedCoord_derivs (hIn : ThirdOrderChainRuleVectorValued) (hΛ : ContDiff ℝ 5 Λ)
    (hφ : ContDiffAt ℝ 3 φ 0) (h0 : φ 0 = (w₀, 0)) (v : BondVector) :
    ContDiffAt ℝ 3 (fun τ => movedCoord Λ φ w₀ τ v) 0 ∧
    (∀ u, iteratedFDeriv ℝ 1 (fun τ => movedCoord Λ φ w₀ τ v) 0 ![u] =
      pullback (dirDeriv₁ Λ (pairDeriv₁ φ u)) w₀ v) ∧
    (∀ u u', iteratedFDeriv ℝ 2 (fun τ => movedCoord Λ φ w₀ τ v) 0 ![u, u'] =
      pullback (secondOrderTerm Λ (pairDeriv₁ φ u) (pairDeriv₁ φ u') (pairDeriv₂ φ u u')) w₀ v) ∧
    ∀ u u' u'', iteratedFDeriv ℝ 3 (fun τ => movedCoord Λ φ w₀ τ v) 0 ![u, u', u''] =
      pullback (thirdOrderTerm Λ (pairDeriv₁ φ u) (pairDeriv₁ φ u') (pairDeriv₁ φ u'')
        (pairDeriv₂ φ u u') (pairDeriv₂ φ u u'') (pairDeriv₂ φ u' u'')
        (pairDeriv₃ φ u u' u'')) w₀ v := by
  set sh : LiePair := (coordsIsometry v, 0) with hsh
  set h : LiePair → imaginaryQuaternions := fun z => Λ (z + sh) with hh
  have hh3 : ContDiff ℝ 3 h := (hΛ.of_le (by norm_num)).comp (contDiff_id.add contDiff_const)
  have hat : φ 0 + sh = liftPoint w₀ v := by
    simp [hsh, h0, liftPoint]
  have hK := hIn h φ 0 hh3.contDiffAt hφ
  obtain ⟨hK0, hK1, hK2, hK3⟩ := hK
  set S : imaginaryQuaternions →L[ℝ] BondVector :=
    (coordsIsometry.symm.toContinuousLinearEquiv : imaginaryQuaternions →L[ℝ] BondVector) with hS
  set f : (Fin 3 → ℝ) → imaginaryQuaternions := fun τ => (h ∘ φ) τ - w₀ with hf
  have hf3 : ContDiffAt ℝ 3 f 0 := hK0.sub contDiffAt_const
  have eΘ : (fun τ => movedCoord Λ φ w₀ τ v) = S ∘ f := rfl
  have key : ∀ (n : ℕ), n + 1 ≤ 3 → ∀ m : Fin (n + 1) → (Fin 3 → ℝ),
      iteratedFDeriv ℝ (n + 1) (fun τ => movedCoord Λ φ w₀ τ v) 0 m =
        coordsIsometry.symm (iteratedFDeriv ℝ (n + 1) (h ∘ φ) 0 m) := by
    intro n hn m
    rw [eΘ, S.iteratedFDeriv_comp_left hf3 (by exact_mod_cast hn)]
    have e3 := iteratedFDeriv_succ_sub_const (h ∘ φ) w₀ n 0
    show S ((iteratedFDeriv ℝ (n + 1) (fun τ => (h ∘ φ) τ - w₀) 0) m) = _
    rw [e3]
    rfl
  have hi : ∀ (j : ℕ) (m : Fin j → LiePair), iteratedFDeriv ℝ j h (φ 0) m =
      iteratedFDeriv ℝ j Λ (liftPoint w₀ v) m := by
    intro j m
    have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) j (f := Λ) sh (φ 0)
    rw [hat] at this
    rw [show iteratedFDeriv ℝ j h (φ 0) = _ from this]
  have h4 : ContDiff ℝ 4 Λ := hΛ.of_le (by norm_num)
  have h3' : ContDiff ℝ 3 Λ := hΛ.of_le (by norm_num)
  refine ⟨S.contDiff.contDiffAt.comp _ hf3, fun u => ?_, fun u u' => ?_, fun u u' u'' => ?_⟩
  · rw [key 0 (by norm_num), hK1 u, hi, iteratedFDeriv_one_eq_dirDeriv Λ]
    rfl
  · rw [key 1 (by norm_num), hK2 u u', hi, hi, iteratedFDeriv_two_eq_dirDeriv h3',
      iteratedFDeriv_one_eq_dirDeriv Λ]
    rfl
  · rw [key 2 (by norm_num), hK3 u u' u'', hi, hi, hi, hi, hi, iteratedFDeriv_three_eq_dirDeriv h4,
      iteratedFDeriv_two_eq_dirDeriv h3', iteratedFDeriv_two_eq_dirDeriv h3',
      iteratedFDeriv_two_eq_dirDeriv h3', iteratedFDeriv_one_eq_dirDeriv Λ]
    rfl
def firstField (Λ : LiePair → imaginaryQuaternions) (w₀ : ι' → imaginaryQuaternions) (a : ι' → LiePair)
    (b : ι') : BondVector → BondVector :=
  pullback (dirDeriv₁ Λ (a b)) (w₀ b)
def secondField (Λ : LiePair → imaginaryQuaternions) (w₀ : ι' → imaginaryQuaternions)
    (a a' a'' : ι' → LiePair) (b : ι') : BondVector → BondVector :=
  pullback (secondOrderTerm Λ (a b) (a' b) (a'' b)) (w₀ b)
def thirdField (Λ : LiePair → imaginaryQuaternions) (w₀ : ι' → imaginaryQuaternions)
    (a₁ a₂ a₃ a₁₂ a₁₃ a₂₃ a₁₂₃ : ι' → LiePair) (b : ι') : BondVector → BondVector :=
  pullback (thirdOrderTerm Λ (a₁ b) (a₂ b) (a₃ b) (a₁₂ b) (a₁₃ b) (a₂₃ b) (a₁₂₃ b)) (w₀ b)
def paramBasis (l : Fin 3) : Fin 3 → ℝ := Pi.single l 1
section Config
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def moveField₁ (Λ : LiePair → imaginaryQuaternions) (φ : ι → (Fin 3 → ℝ) → LiePair)
    (w₀ : ι → imaginaryQuaternions) (l : Fin 3) : ι → BondVector → BondVector :=
  firstField Λ w₀ (fun b => pairDeriv₁ (φ b) (paramBasis l))
def moveField₂ (Λ : LiePair → imaginaryQuaternions) (φ : ι → (Fin 3 → ℝ) → LiePair)
    (w₀ : ι → imaginaryQuaternions) (l l' : Fin 3) : ι → BondVector → BondVector :=
  secondField Λ w₀ (fun b => pairDeriv₁ (φ b) (paramBasis l)) (fun b => pairDeriv₁ (φ b) (paramBasis l'))
    (fun b => pairDeriv₂ (φ b) (paramBasis l) (paramBasis l'))
def moveField₃ (Λ : LiePair → imaginaryQuaternions) (φ : ι → (Fin 3 → ℝ) → LiePair)
    (w₀ : ι → imaginaryQuaternions) : ι → BondVector → BondVector :=
  thirdField Λ w₀ (fun b => pairDeriv₁ (φ b) (paramBasis 0)) (fun b => pairDeriv₁ (φ b) (paramBasis 1))
    (fun b => pairDeriv₁ (φ b) (paramBasis 2))
    (fun b => pairDeriv₂ (φ b) (paramBasis 0) (paramBasis 1))
    (fun b => pairDeriv₂ (φ b) (paramBasis 0) (paramBasis 2))
    (fun b => pairDeriv₂ (φ b) (paramBasis 1) (paramBasis 2))
    (fun b => pairDeriv₃ (φ b) (paramBasis 0) (paramBasis 1) (paramBasis 2))
theorem thirdDerivAlong_eq_iteratedFDeriv (hComp : ThirdOrderChainRule)
    (hIn : ThirdOrderChainRuleVectorValued) (hΛ : ContDiff ℝ 5 Λ)
    {φ : ι → (Fin 3 → ℝ) → LiePair} {w₀ : ι → imaginaryQuaternions} (hφ : ∀ b, ContDiffAt ℝ 3 (φ b) 0)
    (h0 : ∀ b, φ b 0 = (w₀ b, 0)) {G : BondField ι → ℝ} {η : BondField ι}
    (hG : ContDiffAt ℝ 3 G η) (hθ : ∀ b, movedCoord Λ (φ b) (w₀ b) 0 (η b) = η b) :
    iteratedFDeriv ℝ 3 (fun τ => G (fun b => movedCoord Λ (φ b) (w₀ b) τ (η b))) 0
        ![paramBasis 0, paramBasis 1, paramBasis 2] =
      ThirdDerivative.thirdDerivAlong G (moveField₁ Λ φ w₀ 0) (moveField₁ Λ φ w₀ 1) (moveField₁ Λ φ w₀ 2)
        (moveField₂ Λ φ w₀ 0 1) (moveField₂ Λ φ w₀ 0 2) (moveField₂ Λ φ w₀ 1 2)
        (moveField₃ Λ φ w₀) η := by
  set α : (Fin 3 → ℝ) → BondField ι := fun τ b => movedCoord Λ (φ b) (w₀ b) τ (η b) with hα
  have td := fun b => movedCoord_derivs hIn hΛ (hφ b) (h0 b) (η b)
  have hαc : ContDiffAt ℝ 3 α 0 := contDiffAt_pi.2 fun b => (td b).1
  have hα0 : α 0 = η := by
    funext b
    exact hθ b
  have hG' : ContDiffAt ℝ 3 G (α 0) := by rwa [hα0]
  obtain ⟨-, -, -, h3⟩ := hComp G α 0 hG' hαc
  have hcomp : (fun τ => G (fun b => movedCoord Λ (φ b) (w₀ b) τ (η b))) = G ∘ α := rfl
  rw [hcomp, h3, hα0]
  have comp : ∀ (n : ℕ), n ≤ 3 → ∀ (m : Fin n → (Fin 3 → ℝ)) (b : ι),
      (iteratedFDeriv ℝ n α 0 m) b = iteratedFDeriv ℝ n (fun τ => α τ b) 0 m := by
    intro n hn m b
    have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).iteratedFDeriv_comp_left
      hαc (i := n) (by exact_mod_cast hn)
    have h2 : (fun τ => α τ b) =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b) ∘ α := rfl
    rw [h2, h1]
    rfl
  have a1 : ∀ l, iteratedFDeriv ℝ 1 α 0 ![paramBasis l] = fieldAlong (moveField₁ Λ φ w₀ l) η := by
    intro l
    funext b
    rw [comp 1 (by norm_num)]
    exact (td b).2.1 (paramBasis l)
  have a2 : ∀ l l', iteratedFDeriv ℝ 2 α 0 ![paramBasis l, paramBasis l'] =
      fieldAlong (moveField₂ Λ φ w₀ l l') η := by
    intro l l'
    funext b
    rw [comp 2 (by norm_num)]
    exact (td b).2.2.1 (paramBasis l) (paramBasis l')
  have a3 : iteratedFDeriv ℝ 3 α 0 ![paramBasis 0, paramBasis 1, paramBasis 2] =
      fieldAlong (moveField₃ Λ φ w₀) η := by
    funext b
    rw [comp 3 (by norm_num)]
    exact (td b).2.2.2 (paramBasis 0) (paramBasis 1) (paramBasis 2)
  rw [a1, a1, a1, a2, a2, a2, a3, iteratedFDeriv_three_apply_eq, iteratedFDeriv_two_apply,
    iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, iteratedFDeriv_one_apply]
  rfl
end Config
end MovedCoordinates
section MoveFieldBounds
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : Type}
variable {Λ : LiePair → imaginaryQuaternions} {CL D Dz ρ a : ℝ} {φ : ι → (Fin 3 → ℝ) → LiePair}
  {w₀ : ι → imaginaryQuaternions} {δ : X → X → ℝ} {loc : ι → X}
structure PairDerivBounds (φ : ι → (Fin 3 → ℝ) → LiePair) (D : ℝ) (w : Fin 3 → ι → ℝ) : Prop where
  one_le : 1 ≤ D
  weight_nonneg : ∀ l b, 0 ≤ w l b
  first : ∀ l b, ‖pairDeriv₁ (φ b) (paramBasis l)‖ ≤ D * w l b
  second : ∀ l l' b, ‖pairDeriv₂ (φ b) (paramBasis l) (paramBasis l')‖ ≤ D * (w l b * w l' b)
  third : ∀ b, ‖pairDeriv₃ (φ b) (paramBasis 0) (paramBasis 1) (paramBasis 2)‖ ≤
    D * (w 0 b * w 1 b * w 2 b)
theorem fieldC2Bound_pullback {g : ι → LiePair → imaginaryQuaternions} (hg : ∀ b, ContDiff ℝ 2 (g b))
    {B : ι → ℝ}
    (hB : ∀ b (z : LiePair) (j : ℕ), j ≤ 2 → ‖iteratedFDeriv ℝ j (g b) z‖ ≤ B b) :
    FieldC2Bound ρ (fun b => pullback (g b) (w₀ b)) B :=
  ⟨fun b => pullback_contDiff (hg b) (w₀ b),
    fun b v _ => (pullback_bounds (hg b) (hB b) (w₀ b) v).1,
    fun b v _ => (pullback_bounds (hg b) (hB b) (w₀ b) v).2.1,
    fun b v _ => (pullback_bounds (hg b) (hB b) (w₀ b) v).2.2⟩
theorem thirdFieldBounds_of_pairDerivBounds (hΛ : ContDiff ℝ 5 Λ)
    (hCL : ∀ (z : LiePair) (j : ℕ), j ≤ 5 → ‖iteratedFDeriv ℝ j Λ z‖ ≤ CL) (hC0 : 0 ≤ CL)
    {c : Fin 3 → X} (hm : PairDerivBounds φ D (fun l b => _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l))) :
    ThirdFieldBounds ρ δ loc a (1 + 5 * CL * D ^ 3) (c 0) (c 1) (c 2) (moveField₁ Λ φ w₀ 0)
      (moveField₁ Λ φ w₀ 1) (moveField₁ Λ φ w₀ 2) (moveField₂ Λ φ w₀ 0 1) (moveField₂ Λ φ w₀ 0 2)
      (moveField₂ Λ φ w₀ 1 2) (moveField₃ Λ φ w₀) := by
  have hD := hm.one_le
  have hD0 : 0 ≤ D := by linarith
  set Dz := 1 + 5 * CL * D ^ 3 with hDz
  have hD3 : D ≤ D ^ 3 := by
    have := pow_le_pow_right₀ hD (by norm_num : 1 ≤ 3)
    simpa using this
  have hD23 : D ^ 2 ≤ D ^ 3 := pow_le_pow_right₀ hD (by norm_num)
  have wn : ∀ (l : Fin 3) b, 0 ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l) := fun l b => expWeight_nonneg _ _ _
  have one : ∀ l, FieldC2Bound ρ (moveField₁ Λ φ w₀ l) (fun b => Dz * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l)) := by
    intro l
    refine fieldC2Bound_pullback (g := fun b => dirDeriv₁ Λ (pairDeriv₁ (φ b) (paramBasis l)))
      (fun b => dirDeriv₁_contDiff hΛ _) ?_
    intro b z j hj
    refine (dirDeriv₁_bound hΛ hCL _ z j hj).trans ?_
    have h1 := hm.first l b
    have h2 := mul_le_mul_of_nonneg_left h1 hC0
    refine h2.trans ?_
    have e : CL * (D * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l)) = (CL * D) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (wn l b)
    simp only [hDz]
    nlinarith [mul_le_mul_of_nonneg_left hD3 hC0, mul_nonneg hC0 (pow_nonneg hD0 3)]
  have two : ∀ l l', FieldC1Bound ρ (moveField₂ Λ φ w₀ l l')
      (fun b => Dz * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l'))) := by
    intro l l'
    have L2 : FieldC2Bound ρ (moveField₂ Λ φ w₀ l l')
        (fun b => Dz * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l'))) := by
      refine fieldC2Bound_pullback (g := fun b => secondOrderTerm Λ (pairDeriv₁ (φ b) (paramBasis l))
        (pairDeriv₁ (φ b) (paramBasis l')) (pairDeriv₂ (φ b) (paramBasis l) (paramBasis l')))
        (fun b => secondOrderTerm_contDiff hΛ _ _ _) ?_
      intro b z j hj
      refine (secondOrderTerm_bound hΛ hCL _ _ _ z j hj).trans ?_
      have a1 := hm.first l b
      have a2 := hm.first l' b
      have a3 := hm.second l l' b
      have w1 := wn l b
      have w2 := wn l' b
      have t1 := mul_le_mul a1 a2 (norm_nonneg _) (mul_nonneg hD0 w1)
      have t2 : ‖pairDeriv₁ (φ b) (paramBasis l)‖ * ‖pairDeriv₁ (φ b) (paramBasis l')‖ +
          ‖pairDeriv₂ (φ b) (paramBasis l) (paramBasis l')‖ ≤
          (D ^ 2 + D) * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l')) := by
        have e : (D ^ 2 + D) * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l')) =
            D * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l) * (D * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l')) +
              D * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l')) := by ring
        rw [e]
        linarith
      have t3 := mul_le_mul_of_nonneg_left t2 hC0
      refine t3.trans ?_
      have e : CL * ((D ^ 2 + D) * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l'))) =
          (CL * (D ^ 2 + D)) * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c l')) := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg w1 w2)
      simp only [hDz]
      nlinarith [mul_le_mul_of_nonneg_left hD3 hC0, mul_le_mul_of_nonneg_left hD23 hC0,
        mul_nonneg hC0 (pow_nonneg hD0 3)]
    exact fieldC1Bound_of_fieldC2Bound L2
  have three : FieldC1Bound ρ (moveField₃ Λ φ w₀) (fun b => Dz * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c 0) *
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c 1) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c 2))) := by
    have L3 : FieldC2Bound ρ (moveField₃ Λ φ w₀) (fun b => Dz * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c 0) *
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c 1) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c 2))) := by
      refine fieldC2Bound_pullback (g := fun b => thirdOrderTerm Λ (pairDeriv₁ (φ b) (paramBasis 0))
        (pairDeriv₁ (φ b) (paramBasis 1)) (pairDeriv₁ (φ b) (paramBasis 2))
        (pairDeriv₂ (φ b) (paramBasis 0) (paramBasis 1)) (pairDeriv₂ (φ b) (paramBasis 0) (paramBasis 2))
        (pairDeriv₂ (φ b) (paramBasis 1) (paramBasis 2))
        (pairDeriv₃ (φ b) (paramBasis 0) (paramBasis 1) (paramBasis 2)))
        (fun b => thirdOrderTerm_contDiff hΛ _ _ _ _ _ _ _) ?_
      intro b z j hj
      refine (thirdOrderTerm_bound hΛ hCL _ _ _ _ _ _ _ z j hj).trans ?_
      set p := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c 0) with hp
      set q := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c 1) with hq
      set r := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight δ a (loc b) (c 2) with hr
      have p0 : 0 ≤ p := wn 0 b
      have q0 : 0 ≤ q := wn 1 b
      have r0 : 0 ≤ r := wn 2 b
      have a1 := hm.first 0 b
      have a2 := hm.first 1 b
      have a3 := hm.first 2 b
      have b1 := hm.second 0 1 b
      have b2 := hm.second 0 2 b
      have b3 := hm.second 1 2 b
      have d3 := hm.third b
      have t0 : ‖pairDeriv₁ (φ b) (paramBasis 0)‖ * ‖pairDeriv₁ (φ b) (paramBasis 1)‖ *
          ‖pairDeriv₁ (φ b) (paramBasis 2)‖ ≤ D * p * (D * q) * (D * r) :=
        mul_le_mul (mul_le_mul a1 a2 (norm_nonneg _) (by positivity)) a3 (norm_nonneg _)
          (by positivity)
      have t1 : ‖pairDeriv₂ (φ b) (paramBasis 0) (paramBasis 1)‖ * ‖pairDeriv₁ (φ b) (paramBasis 2)‖ ≤
          D * (p * q) * (D * r) :=
        mul_le_mul b1 a3 (norm_nonneg _) (by positivity)
      have t2 : ‖pairDeriv₂ (φ b) (paramBasis 0) (paramBasis 2)‖ * ‖pairDeriv₁ (φ b) (paramBasis 1)‖ ≤
          D * (p * r) * (D * q) :=
        mul_le_mul b2 a2 (norm_nonneg _) (by positivity)
      have t3 : ‖pairDeriv₂ (φ b) (paramBasis 1) (paramBasis 2)‖ * ‖pairDeriv₁ (φ b) (paramBasis 0)‖ ≤
          D * (q * r) * (D * p) :=
        mul_le_mul b3 a1 (norm_nonneg _) (by positivity)
      have s : ‖pairDeriv₁ (φ b) (paramBasis 0)‖ * ‖pairDeriv₁ (φ b) (paramBasis 1)‖ *
          ‖pairDeriv₁ (φ b) (paramBasis 2)‖ +
          ‖pairDeriv₂ (φ b) (paramBasis 0) (paramBasis 1)‖ * ‖pairDeriv₁ (φ b) (paramBasis 2)‖ +
          ‖pairDeriv₂ (φ b) (paramBasis 0) (paramBasis 2)‖ * ‖pairDeriv₁ (φ b) (paramBasis 1)‖ +
          ‖pairDeriv₂ (φ b) (paramBasis 1) (paramBasis 2)‖ * ‖pairDeriv₁ (φ b) (paramBasis 0)‖ +
          ‖pairDeriv₃ (φ b) (paramBasis 0) (paramBasis 1) (paramBasis 2)‖ ≤
          (D ^ 3 + 3 * D ^ 2 + D) * (p * q * r) := by
        have e : (D ^ 3 + 3 * D ^ 2 + D) * (p * q * r) = D * p * (D * q) * (D * r) +
            D * (p * q) * (D * r) + D * (p * r) * (D * q) + D * (q * r) * (D * p) +
            D * (p * q * r) := by ring
        rw [e]
        linarith
      have t4 := mul_le_mul_of_nonneg_left s hC0
      refine t4.trans ?_
      have e : CL * ((D ^ 3 + 3 * D ^ 2 + D) * (p * q * r)) =
          (CL * (D ^ 3 + 3 * D ^ 2 + D)) * (p * q * r) := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simp only [hDz]
      nlinarith [mul_le_mul_of_nonneg_left hD3 hC0, mul_le_mul_of_nonneg_left hD23 hC0,
        mul_nonneg hC0 (pow_nonneg hD0 3)]
    exact fieldC1Bound_of_fieldC2Bound L3
  have hone : 1 ≤ Dz := by
    simp only [hDz]
    nlinarith [mul_nonneg hC0 (pow_nonneg hD0 3)]
  exact ⟨hone, one 0, one 1, one 2, two 0 1, two 0 2, two 1 2, three⟩
end MoveFieldBounds
section MovedTop
theorem expUnit_of_zero_eq_one : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
variable {F : BlockFrame}
theorem leftTranslate_bondSpread_at_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) :
    leftTranslate (bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p2043 <;> assumption
def subParams {k : ℕ} (s : Fin k → Fin 3) : (Fin k → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight (paramBasis (s i))
theorem subParams_single {k : ℕ} (s : Fin k → Fin 3) (i : Fin k) :
    subParams s (Pi.single i 1) = paramBasis (s i) := by
  simp [subParams, _root_.sum_apply, Pi.single_apply]
theorem bondSpread_comp {k : ℕ} (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions)
    (s : Fin k → Fin 3) (τ : Fin k → ℝ) : bondSpread (c ∘ s) (X ∘ s) τ = bondSpread c X (subParams s τ) := by
  funext y i
  simp only [bondSpread, subParams, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Function.comp_apply, Finset.sum_apply, Pi.smul_apply, paramBasis,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have e : ∀ l : Fin 3, (if c l = (y, i) then (∑ i', if l = s i' then τ i' else 0) • X l else 0) =
      ∑ i', if s i' = l then (if c (s i') = (y, i) then τ i' • X (s i') else 0) else 0 := by
    intro l
    by_cases h : c l = (y, i)
    · simp only [if_pos h, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i' _
      by_cases hl : s i' = l
      · subst hl
        simp [h]
      · have : ¬ l = s i' := fun e => hl e.symm
        simp [hl, this]
    · rw [if_neg h]
      symm
      apply Finset.sum_eq_zero
      intro i' _
      by_cases hl : s i' = l
      · subst hl
        simp [h]
      · simp [hl]
  simp only [e]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i' _
  simp
variable (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions) (V : F.GaugeField F.top)
def alongParams {E : Type} (g : F.GaugeField F.top → E) (τ : Fin 3 → ℝ) : E :=
  g (leftTranslate (bondSpread c X τ) V)
section Sub
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : F.GaugeField F.top → E}
theorem iteratedFDeriv_two_clm {P D : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup D] [NormedSpace ℝ D] (R : P →L[ℝ] D) (x : P) (m : Fin 2 → P) :
    iteratedFDeriv ℝ 2 R x m = 0 := by
  rw [iteratedFDeriv_two_apply]
  have : fderiv ℝ R = fun _ => R := by
    funext y
    exact R.fderiv
  rw [this]
  simp
theorem iteratedFDeriv_three_clm {P D : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup D] [NormedSpace ℝ D] (R : P →L[ℝ] D) (x : P) (m : Fin 3 → P) :
    iteratedFDeriv ℝ 3 R x m = 0 := by
  rw [iteratedFDeriv_succ_apply_right]
  have : (fun y => fderiv ℝ R y) = fun _ => R := by
    funext y
    exact R.fderiv
  rw [this, iteratedFDeriv_const_of_ne (by norm_num)]
  simp
theorem iteratedFDeriv_one_clm {P D : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup D] [NormedSpace ℝ D] (R : P →L[ℝ] D) (x : P) (m : Fin 1 → P) :
    iteratedFDeriv ℝ 1 R x m = R (m 0) := by
  rw [iteratedFDeriv_one_apply, R.fderiv]
theorem bondDeriv_one (hIn : ThirdOrderChainRuleVectorValued)
    (hg : ContDiffAt ℝ 3 (alongParams c X V g) 0) (s : Fin 1 → Fin 3) :
    bondDeriv g V (c ∘ s) (X ∘ s) = iteratedFDeriv ℝ 1 (alongParams c X V g) 0 ![paramBasis (s 0)] := by
  have e : (fun τ : Fin 1 → ℝ => g (leftTranslate (bondSpread (c ∘ s) (X ∘ s) τ) V)) =
      alongParams c X V g ∘ subParams s := by
    funext τ
    simp only [bondSpread_comp, alongParams, Function.comp_apply]
  have hg' : ContDiffAt ℝ 3 (alongParams c X V g) (subParams s 0) := by simpa using hg
  obtain ⟨-, h1, -, -⟩ := hIn (alongParams c X V g) (subParams s) 0 hg' (subParams s).contDiff.contDiffAt
  unfold bondDeriv
  rw [e]
  have m1 : (fun l : Fin 1 => (Pi.single l 1 : Fin 1 → ℝ)) = ![Pi.single 0 1] := by
    funext l
    fin_cases l
    rfl
  rw [m1, h1, iteratedFDeriv_one_clm, map_zero]
  simp [subParams_single]
theorem bondDeriv_two (hIn : ThirdOrderChainRuleVectorValued)
    (hg : ContDiffAt ℝ 3 (alongParams c X V g) 0) (s : Fin 2 → Fin 3) :
    bondDeriv g V (c ∘ s) (X ∘ s) =
      iteratedFDeriv ℝ 2 (alongParams c X V g) 0 ![paramBasis (s 0), paramBasis (s 1)] := by
  have e : (fun τ : Fin 2 → ℝ => g (leftTranslate (bondSpread (c ∘ s) (X ∘ s) τ) V)) =
      alongParams c X V g ∘ subParams s := by
    funext τ
    simp only [bondSpread_comp, alongParams, Function.comp_apply]
  have hg' : ContDiffAt ℝ 3 (alongParams c X V g) (subParams s 0) := by simpa using hg
  obtain ⟨-, -, h2, -⟩ := hIn (alongParams c X V g) (subParams s) 0 hg' (subParams s).contDiff.contDiffAt
  unfold bondDeriv
  rw [e]
  have m1 : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
    funext l
    fin_cases l <;> rfl
  rw [m1, h2, iteratedFDeriv_two_clm, iteratedFDeriv_one_clm, iteratedFDeriv_one_clm, map_zero]
  simp [subParams_single]
theorem bondDeriv_three (g : F.GaugeField F.top → E) :
    bondDeriv g V c X = iteratedFDeriv ℝ 3 (alongParams c X V g) 0 ![paramBasis 0, paramBasis 1, paramBasis 2] := by
  have m1 : (fun l : Fin 3 => (Pi.single l 1 : Fin 3 → ℝ)) = ![paramBasis 0, paramBasis 1, paramBasis 2] := by
    funext l
    fin_cases l <;> rfl
  unfold bondDeriv
  rw [m1]
  rfl
end Sub
end MovedTop
section MovedPairs
variable {F : BlockFrame}
abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
def cellDistReal (x y : F.Cell) : ℝ := (cellSupDist x y : ℝ)
def bondCell (b : ChordBond F) : F.Cell := enclosingCell b.1.1
variable (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions) (V : F.GaugeField F.top)
open Classical in
def moveAt (b : ChordBond F) (l : Fin 3) : imaginaryQuaternions :=
  if IsCrossingBond b.1 ∧ c l = (enclosingCell b.1.1, b.1.2) then X l else 0
def moveMap (b : ChordBond F) : (Fin 3 → ℝ) →L[ℝ] imaginaryQuaternions :=
  ∑ l, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) l).smulRight (moveAt c X b l)
open Classical in
theorem moveMap_apply (b : ChordBond F) (τ : Fin 3 → ℝ) :
    moveMap c X b τ = if IsCrossingBond b.1 then bondSpread c X τ (enclosingCell b.1.1) b.1.2 else 0 := by
  simp only [moveMap, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, moveAt, bondSpread]
  by_cases h : IsCrossingBond b.1
  · simp [h]
  · simp [h]
theorem moveMap_paramBasis (b : ChordBond F) (l : Fin 3) : moveMap c X b (paramBasis l) = moveAt c X b l := by
  simp [moveMap, _root_.sum_apply, paramBasis, Pi.single_apply]
variable (star : Bool) (a ρA : ℝ) (m : ℕ)
def frameAlong (b : ChordBond F) : (Fin 3 → ℝ) → imaginaryQuaternions :=
  alongParams c X V (stepFrame star a ρA m b.1)
def framePair (b : ChordBond F) (τ : Fin 3 → ℝ) : LiePair :=
  (frameAlong c X V star a ρA m b τ, moveMap c X b τ)
def frameCoord (b : ChordBond F) : imaginaryQuaternions := stepFrame star a ρA m b.1 V
theorem framePair_zero (b : ChordBond F) :
    framePair c X V star a ρA m b 0 = (frameCoord V star a ρA m b, 0) := by
  simp only [framePair, frameAlong, alongParams, frameCoord, map_zero]
  rw [leftTranslate_bondSpread_at_zero]
theorem iteratedFDeriv_pair {u : (Fin 3 → ℝ) → imaginaryQuaternions} {A : (Fin 3 → ℝ) → imaginaryQuaternions}
    (hu : ContDiffAt ℝ 3 u 0)
    (hA : ContDiffAt ℝ 3 A 0) (j : ℕ) (hj : j ≤ 3) (v : Fin j → (Fin 3 → ℝ)) :
    iteratedFDeriv ℝ j (fun τ => ((u τ, A τ) : LiePair)) 0 v =
      (iteratedFDeriv ℝ j u 0 v, iteratedFDeriv ℝ j A 0 v) := by
  have hp : ContDiffAt ℝ 3 (fun τ => ((u τ, A τ) : LiePair)) 0 := hu.prodMk hA
  have h1 := (ContinuousLinearMap.fst ℝ imaginaryQuaternions imaginaryQuaternions).iteratedFDeriv_comp_left
    hp (i := j) (by exact_mod_cast hj)
  have h2 := (ContinuousLinearMap.snd ℝ imaginaryQuaternions imaginaryQuaternions).iteratedFDeriv_comp_left
    hp (i := j) (by exact_mod_cast hj)
  have e1 : (ContinuousLinearMap.fst ℝ imaginaryQuaternions imaginaryQuaternions) ∘
      (fun τ => ((u τ, A τ) : LiePair)) = u := rfl
  have e2 : (ContinuousLinearMap.snd ℝ imaginaryQuaternions imaginaryQuaternions) ∘
      (fun τ => ((u τ, A τ) : LiePair)) = A := rfl
  rw [e1] at h1
  rw [e2] at h2
  apply Prod.ext
  · rw [h1]
    rfl
  · rw [h2]
    rfl
theorem cellDistReal_nonneg (x y : F.Cell) : 0 ≤ cellDistReal x y := Nat.cast_nonneg _
theorem cellDistReal_le_listDistance {k : ℕ} (Y : F.Cell) (c' : Fin k → F.Site F.top × Fin 4) (l : Fin k) :
    cellDistReal Y (c' l).1 ≤ (bondListDistance Y c' : ℝ) := by
  have : cellSupDist Y (c' l).1 ≤ bondListDistance Y c' :=
    Finset.le_sup (f := fun l : Fin k => cellSupDist Y (c' l).1) (Finset.mem_univ l)
  show ((cellSupDist Y (c' l).1 : ℕ) : ℝ) ≤ _
  exact_mod_cast this
theorem pairDerivBounds_framePair (hIn : ThirdOrderChainRuleVectorValued) (hX : AreUnitVectors X)
    {δ₂ κ₂ C σ r : ℝ}
    {Kk : ℕ → ℝ} (hS : FrameSmallness star a ρA δ₂ κ₂ C σ Kk m V) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hr2 : 12 * r ≤ δ₂) :
    PairDerivBounds (framePair c X V star a ρA m) (1 + C)
      (fun l b => _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l).1) := by
  have hu : ∀ b : ChordBond F, ContDiffAt ℝ 3 (frameAlong c X V star a ρA m b) 0 := by
    intro b
    exact ((hS.analytic b.1 b.2 3 c X).contDiffAt).of_le le_top
  have hA : ∀ b : ChordBond F, ContDiffAt ℝ 3 (moveMap c X b) 0 := fun b => (moveMap c X b).contDiff.contDiffAt
  have hφ : ∀ (b : ChordBond F) (j : ℕ) (hj : j ≤ 3) (v : Fin j → (Fin 3 → ℝ)),
      iteratedFDeriv ℝ j (framePair c X V star a ρA m b) 0 v =
        (iteratedFDeriv ℝ j (frameAlong c X V star a ρA m b) 0 v, iteratedFDeriv ℝ j (moveMap c X b) 0 v) :=
    fun b j hj v => iteratedFDeriv_pair (hu b) (hA b) j hj v
  refine ⟨by linarith, fun l b => expWeight_nonneg _ _ _, fun l b => ?_, fun l l' b => ?_, fun b => ?_⟩
  · have e1 : pairDeriv₁ (framePair c X V star a ρA m b) (paramBasis l) = _ := hφ b 1 (by norm_num) ![paramBasis l]
    rw [e1, Prod.norm_def, iteratedFDeriv_one_clm]
    have d1 := bondDeriv_one c X V hIn (g := stepFrame star a ρA m b.1) (hu b) ![l]
    have d2 := hS.deriv_decay b.1 b.2 1 (c ∘ ![l]) (X ∘ ![l]) le_rfl (by norm_num) (fun i => hX _)
    rw [d1] at d2
    have d3 := cellDistReal_le_listDistance (enclosingCell b.1.1) (c ∘ ![l]) 0
    have w1 : Real.exp (-(δ₂ / 4 * bondListDistance (enclosingCell b.1.1) (c ∘ ![l]))) ≤
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l).1 := by
      apply Real.exp_le_exp.mpr
      have hd : cellDistReal (enclosingCell b.1.1) (c l).1 ≤
          bondListDistance (enclosingCell b.1.1) (c ∘ ![l]) := d3
      have e : cellDistReal (bondCell b) (c l).1 = cellDistReal (enclosingCell b.1.1) (c l).1 := rfl
      rw [e]
      nlinarith
    have w0' : 0 ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l).1 := expWeight_nonneg _ _ _
    have m1 : ‖iteratedFDeriv ℝ 1 (alongParams c X V (stepFrame star a ρA m b.1)) 0 ![paramBasis l]‖ ≤
        (1 + C) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l).1 := by
      have t : ‖iteratedFDeriv ℝ 1 (alongParams c X V (stepFrame star a ρA m b.1)) 0 ![paramBasis l]‖ ≤
          C * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l).1 := d2.trans (mul_le_mul_of_nonneg_left w1 hC)
      refine t.trans ?_
      nlinarith
    have m2 : ‖moveMap c X b (![paramBasis l] 0)‖ ≤ (1 + C) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l).1 := by
      show ‖moveMap c X b (paramBasis l)‖ ≤ _
      rw [moveMap_paramBasis]
      unfold moveAt
      split_ifs with h
      · have hc : (c l).1 = enclosingCell b.1.1 := by rw [h.2]
        have hw : _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l).1 = 1 := by
          simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight, cellDistReal, bondCell, hc]
          have : cellSupDist (enclosingCell b.1.1) (enclosingCell b.1.1) = 0 := by
            simp [cellSupDist]
          simp [this]
        rw [hw, hX l]
        linarith
      · rw [norm_zero]
        positivity
    exact max_le m1 m2
  · have e1 : pairDeriv₂ (framePair c X V star a ρA m b) (paramBasis l) (paramBasis l') = _ :=
      hφ b 2 (by norm_num) ![paramBasis l, paramBasis l']
    rw [e1, Prod.norm_def, iteratedFDeriv_two_clm, norm_zero]
    have d1 := bondDeriv_two c X V hIn (g := stepFrame star a ρA m b.1) (hu b) ![l, l']
    have d2 := hS.deriv_decay b.1 b.2 2 (c ∘ ![l, l']) (X ∘ ![l, l']) (by norm_num) (by norm_num)
      (fun i => hX _)
    rw [d1] at d2
    have d3 := cellDistReal_le_listDistance (enclosingCell b.1.1) (c ∘ ![l, l']) 0
    have d4 := cellDistReal_le_listDistance (enclosingCell b.1.1) (c ∘ ![l, l']) 1
    set Ld : ℝ := (bondListDistance (enclosingCell b.1.1) (c ∘ ![l, l']) : ℝ) with hLd
    have w1 : Real.exp (-(δ₂ / 4 * Ld)) ≤
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l).1 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l').1 := by
      simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hd : cellDistReal (enclosingCell b.1.1) (c l).1 ≤ Ld := d3
      have hd' : cellDistReal (enclosingCell b.1.1) (c l').1 ≤ Ld := d4
      have e : cellDistReal (bondCell b) (c l).1 = cellDistReal (enclosingCell b.1.1) (c l).1 := rfl
      have e' : cellDistReal (bondCell b) (c l').1 = cellDistReal (enclosingCell b.1.1) (c l').1 := rfl
      rw [e, e']
      have n1 := cellDistReal_nonneg (enclosingCell b.1.1) (c l).1
      have n2 := cellDistReal_nonneg (enclosingCell b.1.1) (c l').1
      nlinarith
    have w0' : 0 ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l).1 *
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l').1 :=
      mul_nonneg (expWeight_nonneg _ _ _) (expWeight_nonneg _ _ _)
    have t : ‖iteratedFDeriv ℝ 2 (frameAlong c X V star a ρA m b) 0 ![paramBasis l, paramBasis l']‖ ≤
        C * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l).1 *
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c l').1) :=
      d2.trans (mul_le_mul_of_nonneg_left w1 hC)
    refine max_le ?_ (by positivity)
    show ‖iteratedFDeriv ℝ 2 (frameAlong c X V star a ρA m b) 0 ![paramBasis l, paramBasis l']‖ ≤ _
    refine t.trans ?_
    nlinarith
  · have e1 : pairDeriv₃ (framePair c X V star a ρA m b) (paramBasis 0) (paramBasis 1) (paramBasis 2) = _ :=
      hφ b 3 le_rfl ![paramBasis 0, paramBasis 1, paramBasis 2]
    rw [e1, Prod.norm_def, iteratedFDeriv_three_clm, norm_zero]
    have d1 := bondDeriv_three c X V (stepFrame star a ρA m b.1)
    have d2 := hS.deriv_decay b.1 b.2 3 c X (by norm_num) le_rfl hX
    rw [d1] at d2
    have d3 := cellDistReal_le_listDistance (enclosingCell b.1.1) c 0
    have d4 := cellDistReal_le_listDistance (enclosingCell b.1.1) c 1
    have d5 := cellDistReal_le_listDistance (enclosingCell b.1.1) c 2
    set Ld : ℝ := (bondListDistance (enclosingCell b.1.1) c : ℝ) with hLd
    have w1 : Real.exp (-(δ₂ / 4 * Ld)) ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c 0).1 *
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c 1).1 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c 2).1 := by
      simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight]
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e : ∀ l, cellDistReal (bondCell b) (c l).1 = cellDistReal (enclosingCell b.1.1) (c l).1 :=
        fun l => rfl
      rw [e, e, e]
      have n1 := cellDistReal_nonneg (enclosingCell b.1.1) (c 0).1
      have n2 := cellDistReal_nonneg (enclosingCell b.1.1) (c 1).1
      nlinarith
    have w0' : 0 ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c 0).1 *
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c 1).1 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c 2).1 :=
      mul_nonneg (mul_nonneg (expWeight_nonneg _ _ _) (expWeight_nonneg _ _ _)) (expWeight_nonneg _ _ _)
    have t : ‖iteratedFDeriv ℝ 3 (frameAlong c X V star a ρA m b) 0
        ![paramBasis 0, paramBasis 1, paramBasis 2]‖ ≤
        C * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c 0).1 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c 1).1 *
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal r (bondCell b) (c 2).1) :=
      d2.trans (mul_le_mul_of_nonneg_left w1 hC)
    refine max_le ?_ (by positivity)
    show ‖iteratedFDeriv ℝ 3 (frameAlong c X V star a ρA m b) 0
      ![paramBasis 0, paramBasis 1, paramBasis 2]‖ ≤ _
    refine t.trans ?_
    nlinarith
end MovedPairs
section MovedVariables
variable {F : BlockFrame}
variable (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions) (V : F.GaugeField F.top)
variable (star : Bool) (a ρA : ℝ) (m : ℕ)
structure ProductLog (Λ : LiePair → imaginaryQuaternions) (r₀ : ℝ) : Prop where
  radius_pos : 0 < r₀
  contDiff : ContDiff ℝ 5 Λ
  exp_eq : ∀ p q : imaginaryQuaternions, ‖p‖ < r₀ → ‖q‖ < r₀ → expUnit (Λ (p, q)) = expUnit p * expUnit q
  eq_self : ∀ p : imaginaryQuaternions, ‖p‖ < r₀ → Λ (p, 0) = p
variable {Λ : LiePair → imaginaryQuaternions} {r₀ ρ : ℝ}
theorem movedCoord_zero (hL : ProductLog Λ r₀) (b : ChordBond F) (v : BondVector)
    (hv : ‖frameCoord V star a ρA m b + coordsIsometry v‖ < r₀) :
    movedCoord Λ (framePair c X V star a ρA m b) (frameCoord V star a ρA m b) 0 v = v := by
  simp only [movedCoord, framePair_zero]
  have e : ((frameCoord V star a ρA m b, 0) : LiePair) + (coordsIsometry v, 0) =
      (frameCoord V star a ρA m b + coordsIsometry v, 0) := by
    simp
  rw [e, hL.eq_self _ hv]
  simp
def movedVariable (Λ : LiePair → imaginaryQuaternions) (η : StepVariable (finiteCells F)) (τ : Fin 3 → ℝ) :
    StepVariable (finiteCells F) :=
  fun b => movedCoord Λ (framePair c X V star a ρA m b) (frameCoord V star a ρA m b) τ (η b)
open Classical in
theorem fieldAboveFrame_leftTranslate (hL : ProductLog Λ r₀)
    (hcover : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth)
    (η : StepVariable (finiteCells F)) (τ : Fin 3 → ℝ)
    (h1 : ∀ b : ChordBond F, ‖frameAlong c X V star a ρA m b τ + coordsIsometry (η b)‖ < r₀)
    (h2 : ∀ b : ChordBond F, ‖moveMap c X b τ‖ < r₀) :
    fieldAboveFrame star a ρA m (leftTranslate (bondSpread c X τ) V) η =
      fieldAboveFrame star a ρA m V (movedVariable c X V star a ρA m Λ η τ) := by
  funext x i
  by_cases hb : (x, i) ∈ chordBonds (finiteCells F)
  · set b : ChordBond F := ⟨(x, i), hb⟩ with hbdef
    have co : ∀ ζ : StepVariable (finiteCells F), stepCoordinates ζ x i = toImaginary (ζ b) := by
      intro ζ
      simp only [stepCoordinates, dif_pos hb]
      rfl
    have eL : coordsAboveFrame star a ρA m (leftTranslate (bondSpread c X τ) V) η x i =
        frameAlong c X V star a ρA m b τ + coordsIsometry (η b) := by
      simp only [coordsAboveFrame, co]
      rfl
    have eR : coordsAboveFrame star a ρA m V (movedVariable c X V star a ρA m Λ η τ) x i =
        Λ (frameAlong c X V star a ρA m b τ + coordsIsometry (η b), moveMap c X b τ) := by
      simp only [coordsAboveFrame, co, movedVariable, movedCoord]
      have e1 : toImaginary (coordsIsometry.symm (Λ (framePair c X V star a ρA m b τ +
          (coordsIsometry (η b), 0)) - frameCoord V star a ρA m b)) =
          Λ (framePair c X V star a ρA m b τ + (coordsIsometry (η b), 0)) -
          frameCoord V star a ρA m b := coordsIsometry.apply_symm_apply _
      rw [e1]
      have e2 : framePair c X V star a ρA m b τ + (coordsIsometry (η b), 0) =
          (frameAlong c X V star a ρA m b τ + coordsIsometry (η b), moveMap c X b τ) := by
        simp [framePair]
      rw [e2]
      show frameCoord V star a ρA m b + _ = _
      abel
    simp only [fieldAboveFrame, chartedField, eL, eR]
    by_cases hc : IsCrossingBond (x, i)
    · simp only [if_pos hc]
      have hq : moveMap c X b τ = bondSpread c X τ (enclosingCell x) i := by
        rw [moveMap_apply]
        exact if_pos hc
      rw [hL.exp_eq _ _ (h1 b) (h2 b), hq]
      simp only [leftTranslate]
      rw [mul_assoc]
    · simp only [if_neg hc]
      by_cases ht : IsAxialTreeBond (x, i)
      · simp only [if_pos ht]
      · simp only [if_neg ht]
        have hq : moveMap c X b τ = 0 := by
          rw [moveMap_apply]
          exact if_neg hc
        have := hL.exp_eq _ _ (h1 b) (h2 b)
        rw [this, hq, expUnit_of_zero_eq_one, mul_one]
  · have hbonds : (x, i) ∈ innerBonds (finiteCells F) F.depth := by
      simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨hcover x, hcover _⟩
    have ht : IsAxialTreeBond (x, i) := by
      by_contra h
      exact hb (by simp only [chordBonds, Finset.mem_filter]; exact ⟨hbonds, h⟩)
    have hc : ¬ IsCrossingBond (x, i) := ht.1
    simp only [fieldAboveFrame, chartedField, if_neg hc, if_pos ht]
theorem eventually_norm_lt (hu : ∀ b : ChordBond F, ContinuousAt (frameAlong c X V star a ρA m b) 0)
    (hr : 0 < r₀) (η : StepVariable (finiteCells F))
    (h0 : ∀ b : ChordBond F, ‖frameCoord V star a ρA m b + coordsIsometry (η b)‖ < r₀) :
    ∀ᶠ τ in 𝓝 (0 : Fin 3 → ℝ),
      (∀ b : ChordBond F, ‖frameAlong c X V star a ρA m b τ + coordsIsometry (η b)‖ < r₀) ∧
      ∀ b : ChordBond F, ‖moveMap c X b τ‖ < r₀ := by
  have e1 : ∀ b : ChordBond F, ∀ᶠ τ in 𝓝 (0 : Fin 3 → ℝ),
      ‖frameAlong c X V star a ρA m b τ + coordsIsometry (η b)‖ < r₀ := by
    intro b
    have hc : ContinuousAt (fun τ => ‖frameAlong c X V star a ρA m b τ + coordsIsometry (η b)‖) 0 :=
      ((hu b).add continuousAt_const).norm
    have hz : ‖frameAlong c X V star a ρA m b 0 + coordsIsometry (η b)‖ < r₀ := by
      have : frameAlong c X V star a ρA m b 0 = frameCoord V star a ρA m b := by
        simp only [frameAlong, alongParams, frameCoord]
        rw [leftTranslate_bondSpread_at_zero]
      rw [this]
      exact h0 b
    exact hc.eventually (gt_mem_nhds hz)
  have e2 : ∀ b : ChordBond F, ∀ᶠ τ in 𝓝 (0 : Fin 3 → ℝ), ‖moveMap c X b τ‖ < r₀ := by
    intro b
    have hc : ContinuousAt (fun τ => ‖moveMap c X b τ‖) 0 := (moveMap c X b).continuous.norm.continuousAt
    have hz : ‖moveMap c X b 0‖ < r₀ := by simpa using hr
    exact hc.eventually (gt_mem_nhds hz)
  exact (Filter.eventually_all.mpr e1).and (Filter.eventually_all.mpr e2)
theorem bondDeriv_centredExpansion_eq (hComp : ThirdOrderChainRule)
    (hIn : ThirdOrderChainRuleVectorValued) (hL : ProductLog Λ r₀) (hX : AreUnitVectors X)
    {δ₂ κ₂ C σ : ℝ} {Kk : ℕ → ℝ} (hS : FrameSmallness star a ρA δ₂ κ₂ C σ Kk m V)
    (hcover : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth) (f : LocalFamily)
    (y : F.Site F.depth)
    {G : StepVariable (finiteCells F) → ℝ}
    (hG : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ < ρ) →
      G ζ = centredExpansion star a ρA m f y ζ V)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < ρ) (hGc : ContDiffAt ℝ 3 G η)
    (h0 : ∀ b : ChordBond F, ‖frameCoord V star a ρA m b + coordsIsometry (η b)‖ < r₀) :
    bondDeriv (centredExpansion star a ρA m f y η) V c X =
      ThirdDerivative.thirdDerivAlong G (moveField₁ Λ (framePair c X V star a ρA m) (frameCoord V star a ρA m) 0)
        (moveField₁ Λ (framePair c X V star a ρA m) (frameCoord V star a ρA m) 1)
        (moveField₁ Λ (framePair c X V star a ρA m) (frameCoord V star a ρA m) 2)
        (moveField₂ Λ (framePair c X V star a ρA m) (frameCoord V star a ρA m) 0 1)
        (moveField₂ Λ (framePair c X V star a ρA m) (frameCoord V star a ρA m) 0 2)
        (moveField₂ Λ (framePair c X V star a ρA m) (frameCoord V star a ρA m) 1 2)
        (moveField₃ Λ (framePair c X V star a ρA m) (frameCoord V star a ρA m)) η := by
  have hu : ∀ b : ChordBond F, ContDiffAt ℝ 3 (frameAlong c X V star a ρA m b) 0 := fun b =>
    ((hS.analytic b.1 b.2 3 c X).contDiffAt).of_le le_top
  have hφ : ∀ b : ChordBond F, ContDiffAt ℝ 3 (framePair c X V star a ρA m b) 0 := fun b =>
    (hu b).prodMk (moveMap c X b).contDiff.contDiffAt
  have hθ0 : ∀ b : ChordBond F,
      movedCoord Λ (framePair c X V star a ρA m b) (frameCoord V star a ρA m b) 0 (η b) = η b :=
    fun b => movedCoord_zero c X V star a ρA m hL b (η b) (h0 b)
  have hid := thirdDerivAlong_eq_iteratedFDeriv hComp hIn hL.contDiff hφ
    (fun b => framePair_zero c X V star a ρA m b) hGc hθ0
  rw [bondDeriv_three, ← hid]
  have ev := eventually_norm_lt c X V star a ρA m (fun b => (hu b).continuousAt) hL.radius_pos η h0
  have ev2 : ∀ b : ChordBond F, ∀ᶠ τ in 𝓝 (0 : Fin 3 → ℝ),
      ‖movedCoord Λ (framePair c X V star a ρA m b) (frameCoord V star a ρA m b) τ (η b)‖ < ρ := by
    intro b
    have hc := (movedCoord_derivs hIn hL.contDiff (hφ b) (framePair_zero c X V star a ρA m b) (η b)).1
    have hc2 : ContinuousAt
        (fun τ => ‖movedCoord Λ (framePair c X V star a ρA m b) (frameCoord V star a ρA m b) τ (η b)‖) 0 :=
      hc.continuousAt.norm
    have hz : ‖movedCoord Λ (framePair c X V star a ρA m b) (frameCoord V star a ρA m b) 0 (η b)‖ < ρ := by
      rw [hθ0]
      exact hη b
    exact hc2.eventually (gt_mem_nhds hz)
  have hev : alongParams c X V (centredExpansion star a ρA m f y η) =ᶠ[𝓝 0]
      fun τ => G (fun b => movedCoord Λ (framePair c X V star a ρA m b) (frameCoord V star a ρA m b) τ (η b)) := by
    filter_upwards [ev, Filter.eventually_all.mpr ev2] with τ hτ hτ2
    show centredExpansion star a ρA m f y η (leftTranslate (bondSpread c X τ) V) = G _
    have e1 : G (movedVariable c X V star a ρA m Λ η τ) =
        centredExpansion star a ρA m f y (movedVariable c X V star a ρA m Λ η τ) V := hG _ hτ2
    have e2 := fieldAboveFrame_leftTranslate c X V star a ρA m hL hcover η τ hτ.1 hτ.2
    show _ = G (movedVariable c X V star a ρA m Λ η τ)
    rw [e1]
    simp only [centredExpansion, e2]
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev 3).eq_of_nhds]
end MovedVariables
section Extension
section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
theorem exists_contDiff_extension {G : E → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hG : ∀ η ∈ Metric.closedBall (0 : E) ρ, ContDiffAt ℝ 3 G η) :
    ∃ (Gt : E → ℝ) (r₁ : ℝ), ρ < r₁ ∧ ContDiff ℝ 3 Gt ∧ ∀ ζ, ‖ζ‖ < r₁ → Gt ζ = G ζ := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  set U : Set E := {η | ∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ 3 G ζ} with hU
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro η hη
    exact eventually_eventually_nhds.mpr hη
  have hKU : Metric.closedBall (0 : E) ρ ⊆ U := fun η hη => (hG η hη).eventually (by simp)
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall (0 : E) ρ).exists_thickening_subset_open hUo hKU
  rw [thickening_closedBall hδ hρ.le] at hsub
  let f : ContDiffBump (0 : E) := ⟨ρ + δ / 3, ρ + 2 * δ / 3, by positivity, by linarith⟩
  have hfc : ContDiff ℝ 3 (fun z => f z) := f.contDiff
  refine ⟨fun z => f z * G z, ρ + δ / 3, by linarith, ?_, fun ζ hζ => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    rcases lt_or_ge ‖z‖ (δ + ρ) with hz | hz
    · have hzU : z ∈ U := hsub (by simpa using hz)
      exact hfc.contDiffAt.mul (hzU.self_of_nhds)
    · have hev : (fun z => f z * G z) =ᶠ[𝓝 z] fun _ => 0 := by
        have : {w : E | ρ + 2 * δ / 3 < ‖w‖} ∈ 𝓝 z :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds (by
            show ρ + 2 * δ / 3 < ‖z‖
            linarith)
        filter_upwards [this] with w hw
        have : f w = 0 := f.zero_of_le_dist (by
          show ρ + 2 * δ / 3 ≤ dist w 0
          rw [dist_zero_right]
          exact le_of_lt hw)
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · have h1 : f ζ = 1 := f.one_of_mem_closedBall (by
      show dist ζ 0 ≤ ρ + δ / 3
      rw [dist_zero_right]
      exact hζ.le)
    simp [h1]
end Generic
theorem abs_le_of_unit {f : BondVector → ℝ} (hf : ∀ (s : ℝ) e, f (s • e) = s * f e) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ e, ‖e‖ = 1 → |f e| ≤ M) (e : BondVector) : |f e| ≤ M * ‖e‖ := by
  by_cases h : e = 0
  · subst h
    have := hf 0 0
    simp only [smul_zero, zero_mul] at this
    simp [this]
  · have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have hu : ‖(‖e‖⁻¹ • e)‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have h1 := hM _ hu
    have h2 := hf ‖e‖ (‖e‖⁻¹ • e)
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul] at h2
    rw [h2, abs_mul, abs_of_nonneg (norm_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
section WilsonWeightSeriesExpansion
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem bondVariation_smul (b : ι) (s : ℝ) (e : BondVector) :
    bondVariation b (s • e) = s • bondVariation b e := by apply _root_.YangMills.SharedProofs.p169 <;> assumption
variable {G Gt : BondField ι → ℝ} {η : BondField ι}
theorem secondDerivAlong_eq_fderiv_fderiv (h : ContDiff ℝ 3 Gt) (ζ u v : BondField ι) :
    secondDerivAlong Gt ζ u v = fderiv ℝ (fderiv ℝ Gt) ζ v u := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.secondDerivAlong_eq_fderiv_fderiv <;> assumption
theorem thirdDerivAlong_eq_fderiv_fderiv_fderiv (h : ContDiff ℝ 3 Gt) (ζ u v z : BondField ι) :
    ColdStepAtMirrorFrames.thirdDerivAlong Gt ζ u v z = fderiv ℝ (fderiv ℝ (fderiv ℝ Gt)) ζ z v u := by
  have e : (fun y => secondDerivAlong Gt y u v) = fun y => fderiv ℝ (fderiv ℝ Gt) y v u := by
    funext y
    exact secondDerivAlong_eq_fderiv_fderiv h y u v
  have hd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ Gt)) ζ := by
    have h1 : ContDiff ℝ 2 (fderiv ℝ Gt) := h.fderiv_right (m := 2) (by norm_num)
    have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ Gt)) := h1.fderiv_right (m := 1) (by norm_num)
    exact h2.differentiable (by norm_num) ζ
  have h2 := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v ζ)).clm_apply (hasFDerivAt_const u ζ)
  have h3 : fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ Gt) y v u) ζ = _ := h2.fderiv
  show fderiv ℝ (fun y => secondDerivAlong Gt y u v) ζ z = _
  rw [e, h3]
  simp
theorem eventuallyEq_secondDerivAlong (hev : Gt =ᶠ[𝓝 η] G) (u : BondField ι) :
    (fun ζ => secondDerivAlong G ζ u) =ᶠ[𝓝 η] fun ζ => secondDerivAlong Gt ζ u := by
  have h1 := Filter.EventuallyEq.eventuallyEq_nhds hev
  filter_upwards [h1] with ζ hζ
  funext v
  have h2 : (fun y => fderiv ℝ G y u) =ᶠ[𝓝 ζ] fun y => fderiv ℝ Gt y u := by
    have := Filter.EventuallyEq.fderiv (𝕜 := ℝ) hζ.symm
    filter_upwards [this] with y hy
    rw [hy]
  show fderiv ℝ (fun y => fderiv ℝ G y u) ζ v = fderiv ℝ (fun y => fderiv ℝ Gt y u) ζ v
  rw [h2.fderiv_eq]
theorem secondDerivAlong_congr (hev : Gt =ᶠ[𝓝 η] G) (u v : BondField ι) :
    secondDerivAlong G η u v = secondDerivAlong Gt η u v :=
  congrFun (eventuallyEq_secondDerivAlong hev u).eq_of_nhds v
theorem thirdDerivAlong_congr (hev : Gt =ᶠ[𝓝 η] G) (u v z : BondField ι) :
    ColdStepAtMirrorFrames.thirdDerivAlong G η u v z = ColdStepAtMirrorFrames.thirdDerivAlong Gt η u v z := by
  have h1 : (fun ζ => secondDerivAlong G ζ u v) =ᶠ[𝓝 η] fun ζ => secondDerivAlong Gt ζ u v := by
    filter_upwards [eventuallyEq_secondDerivAlong hev u] with ζ hζ
    exact congrFun hζ v
  show fderiv ℝ (fun ζ => secondDerivAlong G ζ u v) η z = fderiv ℝ (fun ζ => secondDerivAlong Gt ζ u v) η z
  rw [h1.fderiv_eq]
end WilsonWeightSeriesExpansion
end Extension
section ExpansionJet
variable {F : BlockFrame}
theorem cellDistReal_le_bondSpan {k : ℕ} (Y : F.Cell) (c' : Fin k → F.Site F.top × Fin 4) (l : Fin k) :
    cellDistReal Y (c' l).1 ≤ (bondSpan Y c' : ℝ) := by
  have h1 : siteSupDist Y (c' l).1 ≤ Finset.univ.sup fun l : Fin k => siteSupDist Y (c' l).1 :=
    Finset.le_sup (f := fun l : Fin k => siteSupDist Y (c' l).1) (Finset.mem_univ l)
  have h2 : siteSupDist Y (c' l).1 ≤ bondSpan Y c' := h1.trans (le_max_left _ _)
  show ((cellSupDist Y (c' l).1 : ℕ) : ℝ) ≤ _
  have e : cellSupDist Y (c' l).1 = siteSupDist Y (c' l).1 := rfl
  rw [e]
  exact_mod_cast h2
theorem cellDistReal_le_chordBondSpan {k : ℕ} (Y : F.Cell) (b : Fin k → ChordBond F) (l : Fin k) :
    cellDistReal Y (bondCell (b l)) ≤ (chordBondSpan Y b : ℝ) :=
  cellDistReal_le_bondSpan Y (fun l => (enclosingCell (b l).1.1, (0 : Fin 4))) l
theorem cellDistReal_le_bondSpanWithCell {k : ℕ} (Y z : F.Cell) (c' : Fin k → F.Site F.top × Fin 4) :
    cellDistReal Y z ≤ (bondSpanWithCell Y z c' : ℝ) :=
  cellDistReal_le_bondSpan Y (Fin.cons (z, 0) c' : Fin (k + 1) → F.Site F.top × Fin 4) 0
variable {star : Bool} {a ρA ρ κ δ E E₃ C : ℝ} {L m : ℕ} {f : LocalFamily} {V : F.GaugeField F.top}
def noBonds : Fin 0 → F.Site F.top × Fin 4 := Fin.elim0
def noDirections : Fin 0 → imaginaryQuaternions := Fin.elim0
theorem areUnitVectors_noDirections : AreUnitVectors noDirections := fun l => l.elim0
theorem centredExpansion_contDiffAt (R : CentredExpansionBounds star a ρA ρ κ δ E E₃ C L m f V) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ContDiffAt ℝ 3 (fun ζ => centredExpansion star a ρA m f y ζ V) η := by
  have h := R.smooth y η 0 noBonds noDirections hη
  have h2 : ContDiffAt ℝ 3 (fun ζ : StepVariable (finiteCells F) =>
      (((0 : Fin 0 → ℝ), ζ) : (Fin 0 → ℝ) × StepVariable (finiteCells F))) η :=
    contDiffAt_const.prodMk contDiffAt_id
  have h3 := ContDiffAt.comp η h h2
  have e : ((fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) =>
      centredExpansion star a ρA m f y q.2 (leftTranslate (bondSpread noBonds noDirections q.1) V)) ∘
      fun ζ : StepVariable (finiteCells F) =>
        (((0 : Fin 0 → ℝ), ζ) : (Fin 0 → ℝ) × StepVariable (finiteCells F))) =
      fun ζ => centredExpansion star a ρA m f y ζ V := by
    funext ζ
    simp only [Function.comp_apply]
    rw [leftTranslate_bondSpread_at_zero]
  rwa [e] at h3
theorem abs_bondPartialDeriv_centredExpansion_le (R : CentredExpansionBounds star a ρA ρ κ δ E E₃ C L m f V)
    (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < ρ) (b : ChordBond F) {e : BondVector}
    (he : ‖e‖ = 1) :
    |bondPartialDeriv (fun ζ => centredExpansion star a ρA m f y ζ V) b η e| ≤
      C * E * Real.exp (-(2 ^ 5 * κ * bondSpanWithCell (enclosingCell y) (enclosingCell b.1.1) noBonds)) := by
  have h := R.deriv_top_partial y η b e 0 noBonds noDirections hη (by norm_num) areUnitVectors_noDirections he
  have e1 : bondDeriv (fun V' => bondPartialDeriv (fun ζ => centredExpansion star a ρA m f y ζ V') b η e) V
      noBonds noDirections = bondPartialDeriv (fun ζ => centredExpansion star a ρA m f y ζ V) b η e := by
    unfold bondDeriv
    rw [iteratedFDeriv_zero_apply, leftTranslate_bondSpread_at_zero]
  rw [e1] at h
  simpa using h
theorem exp_span_le_exp_dist {s d r : ℝ} (hr : 0 ≤ r) (h : d ≤ s) (hs : r ≤ 2 ^ 5) {κ : ℝ} (hκ : 0 < κ)
    (hd : 0 ≤ d) : Real.exp (-(2 ^ 5 * κ * s)) ≤ Real.exp (-(r * κ * d)) := by
  apply Real.exp_le_exp.mpr
  have h1 : r * κ * d ≤ 2 ^ 5 * κ * d :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hκ.le) hd
  have h2 : 2 ^ 5 * κ * d ≤ 2 ^ 5 * κ * s := mul_le_mul_of_nonneg_left h (by positivity)
  linarith
theorem centredExpansion_thirdJetBound (R : CentredExpansionBounds star a ρA ρ κ δ E E₃ C L m f V) (hρ : 0 < ρ)
    (hκ : 0 < κ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃) (y : F.Site F.depth) :
    ∃ (Gt : BondField (ChordBond F) → ℝ) (r₁ : ℝ), ρ < r₁ ∧
      (∀ ζ : BondField (ChordBond F), (∀ b, ‖ζ b‖ < r₁) → Gt ζ = centredExpansion star a ρA m f y ζ V) ∧
      ThirdJetBound ρ Gt (C * E) (C * E₃)
        (fun b => _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b)) := by
  set G : BondField (ChordBond F) → ℝ := fun ζ => centredExpansion star a ρA m f y ζ V with hG
  have hcd : ∀ η ∈ Metric.closedBall (0 : BondField (ChordBond F)) ρ, ContDiffAt ℝ 3 G η := by
    intro η hη
    refine centredExpansion_contDiffAt R y η fun b => ?_
    have h1 : ‖η‖ ≤ ρ := by simpa using hη
    exact (norm_le_pi_norm η b).trans h1
  obtain ⟨Gt, r₁, hr₁, hGt, hEq⟩ := exists_contDiff_extension hρ hcd
  have hr0 : 0 < r₁ := hρ.trans hr₁
  have hEq' : ∀ ζ : BondField (ChordBond F), (∀ b, ‖ζ b‖ < r₁) → Gt ζ = G ζ := fun ζ hζ =>
    hEq ζ ((pi_norm_lt_iff hr0).mpr hζ)
  have hev : ∀ η : BondField (ChordBond F), InOpenBalls ρ η → Gt =ᶠ[𝓝 η] G := by
    intro η hη
    have h1 : ‖η‖ < r₁ := (pi_norm_lt_iff hr0).mpr fun b => (hη b).trans hr₁
    have : {ζ : BondField (ChordBond F) | ‖ζ‖ < r₁} ∈ 𝓝 η :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds h1
    filter_upwards [this] with ζ hζ
    exact hEq ζ hζ
  have key : ∀ (η : BondField (ChordBond F)), InOpenBalls ρ η → ∀ (b b' b'' : ChordBond F)
      (e e' e'' : BondVector),
      ‖e‖ = 1 → ‖e'‖ = 1 → ‖e''‖ = 1 →
      |fderiv ℝ Gt η (bondVariation b e)| ≤
        C * E * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b) ∧
      |fderiv ℝ (fderiv ℝ Gt) η (bondVariation b e) (bondVariation b' e')| ≤
        C * E * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b) *
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b') ∧
      |fderiv ℝ (fderiv ℝ (fderiv ℝ Gt)) η (bondVariation b e) (bondVariation b' e') (bondVariation b'' e'')| ≤
        C * E₃ * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b) *
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b') *
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b'') := by
    intro η hη b b' b'' e e' e'' he he' he''
    set Y := enclosingCell y with hY
    have hv := hev η hη
    have n1 := cellDistReal_nonneg Y (bondCell b)
    refine ⟨?_, ?_, ?_⟩
    · have e1 : fderiv ℝ Gt η (bondVariation b e) = bondPartialDeriv G b η e := by
        rw [hv.fderiv_eq]
        rfl
      rw [e1]
      refine (abs_bondPartialDeriv_centredExpansion_le R y η hη b he).trans ?_
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hE)
      have h := cellDistReal_le_bondSpanWithCell Y (enclosingCell b.1.1) (noBonds (F := F))
      have := exp_span_le_exp_dist (r := 4) (by norm_num) h (by norm_num) hκ n1
      refine this.trans (le_of_eq ?_)
      simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight]
      rfl
    · have e1 : fderiv ℝ (fderiv ℝ Gt) η (bondVariation b e) (bondVariation b' e') =
          secondDerivAlong G η (bondVariation b' e') (bondVariation b e) := by
        rw [secondDerivAlong_congr hv, secondDerivAlong_eq_fderiv_fderiv hGt]
      rw [e1]
      have h := R.second_deriv y η b' b e' e hη he' he
      refine h.trans ?_
      have s1 := cellDistReal_le_chordBondSpan Y ![b', b] 0
      have s2 := cellDistReal_le_chordBondSpan Y ![b', b] 1
      set s : ℝ := (chordBondSpan Y ![b', b] : ℝ) with hs
      have s1' : cellDistReal Y (bondCell b') ≤ s := s1
      have s2' : cellDistReal Y (bondCell b) ≤ s := s2
      have w : Real.exp (-(2 ^ 5 * κ * s)) ≤
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) Y (bondCell b) * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) Y (bondCell b') := by
        simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight]
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left s1' hκ.le, mul_le_mul_of_nonneg_left s2' hκ.le]
      have := mul_le_mul_of_nonneg_left w (mul_nonneg hC hE)
      refine this.trans (le_of_eq ?_)
      ring
    · have e1 : fderiv ℝ (fderiv ℝ (fderiv ℝ Gt)) η (bondVariation b e) (bondVariation b' e')
          (bondVariation b'' e'') =
          ColdStepAtMirrorFrames.thirdDerivAlong G η (bondVariation b'' e'') (bondVariation b' e')
            (bondVariation b e) := by
        rw [thirdDerivAlong_congr hv, thirdDerivAlong_eq_fderiv_fderiv_fderiv hGt]
      rw [e1]
      have h := R.third_deriv y η b'' b' b e'' e' e hη he'' he' he
      refine h.trans ?_
      have s1 := cellDistReal_le_chordBondSpan Y ![b'', b', b] 0
      have s2 := cellDistReal_le_chordBondSpan Y ![b'', b', b] 1
      have s3 := cellDistReal_le_chordBondSpan Y ![b'', b', b] 2
      set s : ℝ := (chordBondSpan Y ![b'', b', b] : ℝ) with hs
      have s1' : cellDistReal Y (bondCell b'') ≤ s := s1
      have s2' : cellDistReal Y (bondCell b') ≤ s := s2
      have s3' : cellDistReal Y (bondCell b) ≤ s := s3
      have w : Real.exp (-(2 ^ 5 * κ * s)) ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) Y (bondCell b) *
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) Y (bondCell b') * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) Y (bondCell b'') := by
        simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight]
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left s1' hκ.le, mul_le_mul_of_nonneg_left s2' hκ.le,
          mul_le_mul_of_nonneg_left s3' hκ.le]
      have := mul_le_mul_of_nonneg_left w (mul_nonneg hC hE₃)
      refine this.trans (le_of_eq ?_)
      ring
  have u0 : ‖basisVector 0‖ = 1 := norm_basisVector 0
  have w0' : ∀ b : ChordBond F, 0 ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b) :=
    fun b => expWeight_nonneg _ _ _
  refine ⟨Gt, r₁, hr₁, hEq', hGt, ?_, ?_, ?_⟩
  · intro η hη b e
    refine abs_le_of_unit (f := fun e => fderiv ℝ Gt η (bondVariation b e)) (fun s e => ?_)
      (mul_nonneg (mul_nonneg hC hE) (w0' b)) (fun e he => ?_) e
    · simp [bondVariation_smul]
    · exact (key η hη b b b e (basisVector 0) (basisVector 0) he u0 u0).1
  · intro η hη b b' e e'
    have st1 : ∀ e, ‖e‖ = 1 → ∀ e', |fderiv ℝ (fderiv ℝ Gt) η (bondVariation b e) (bondVariation b' e')| ≤
        C * E * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b) *
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b') * ‖e'‖ := by
      intro e he e'
      refine abs_le_of_unit (f := fun e' => fderiv ℝ (fderiv ℝ Gt) η (bondVariation b e) (bondVariation b' e'))
        (fun s e' => ?_) (mul_nonneg (mul_nonneg (mul_nonneg hC hE) (w0' b)) (w0' b'))
        (fun e' he' => ?_) e'
      · simp [bondVariation_smul]
      · exact (key η hη b b' b e e' (basisVector 0) he he' u0).2.1
    have st2 := abs_le_of_unit
      (f := fun e => fderiv ℝ (fderiv ℝ Gt) η (bondVariation b e) (bondVariation b' e'))
      (fun s e => by simp [bondVariation_smul])
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hE) (w0' b)) (w0' b')) (norm_nonneg e'))
      (fun e he => st1 e he e') e
    refine st2.trans (le_of_eq ?_)
    ring
  · intro η hη b b' b'' e e' e''
    have st1 : ∀ e, ‖e‖ = 1 → ∀ e', ‖e'‖ = 1 → ∀ e'',
        |fderiv ℝ (fderiv ℝ (fderiv ℝ Gt)) η (bondVariation b e) (bondVariation b' e')
          (bondVariation b'' e'')| ≤
        C * E₃ * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b) *
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b') *
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b'') * ‖e''‖ := by
      intro e he e' he' e''
      refine abs_le_of_unit
        (f := fun e'' => fderiv ℝ (fderiv ℝ (fderiv ℝ Gt)) η (bondVariation b e) (bondVariation b' e')
          (bondVariation b'' e''))
        (fun s e'' => ?_)
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hE₃) (w0' b)) (w0' b')) (w0' b''))
        (fun e'' he'' => ?_) e''
      · simp [bondVariation_smul]
      · exact (key η hη b b' b'' e e' e'' he he' he'').2.2
    have st2 : ∀ e, ‖e‖ = 1 → ∀ e' e'',
        |fderiv ℝ (fderiv ℝ (fderiv ℝ Gt)) η (bondVariation b e) (bondVariation b' e')
          (bondVariation b'' e'')| ≤
        C * E₃ * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b) *
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b') *
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (4 * κ) (enclosingCell y) (bondCell b'') * ‖e''‖ * ‖e'‖ := by
      intro e he e' e''
      exact abs_le_of_unit
        (f := fun e' => fderiv ℝ (fderiv ℝ (fderiv ℝ Gt)) η (bondVariation b e) (bondVariation b' e')
          (bondVariation b'' e''))
        (fun s e' => by simp [bondVariation_smul])
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hE₃) (w0' b)) (w0' b')) (w0' b''))
          (norm_nonneg e'')) (fun e' he' => st1 e he e' he' e'') e'
    have st3 := abs_le_of_unit
      (f := fun e => fderiv ℝ (fderiv ℝ (fderiv ℝ Gt)) η (bondVariation b e) (bondVariation b' e')
        (bondVariation b'' e''))
      (fun s e => by simp [bondVariation_smul])
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hE₃) (w0' b)) (w0' b'))
        (w0' b'')) (norm_nonneg e'')) (norm_nonneg e')) (fun e he => st2 e he e' e'') e
    refine st3.trans (le_of_eq ?_)
    ring
end ExpansionJet
section SecondDerivatives
section Sum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {η u v : BondField ι}
  {f g : BondField ι → ℝ}
theorem differentiableAt_fderiv_apply (hf : ContDiffAt ℝ 2 f η) :
    DifferentiableAt ℝ (fun ζ => fderiv ℝ f ζ u) η := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) η := hf.fderiv_right (m := 1) (by norm_num)
  exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
theorem eventually_differentiableAt_of_contDiffAt (hf : ContDiffAt ℝ 2 f η) :
    ∀ᶠ ζ in 𝓝 η, DifferentiableAt ℝ f ζ := by
  filter_upwards [hf.eventually (by simp)] with ζ hζ
  exact hζ.differentiableAt (by norm_num)
theorem secondDerivAlong_add (hf : ContDiffAt ℝ 2 f η) (hg : ContDiffAt ℝ 2 g η) :
    secondDerivAlong (fun ζ => f ζ + g ζ) η u v = secondDerivAlong f η u v + secondDerivAlong g η u v := by
  have hev : (fun ζ => fderiv ℝ (fun ξ => f ξ + g ξ) ζ u) =ᶠ[𝓝 η]
      fun ζ => fderiv ℝ f ζ u + fderiv ℝ g ζ u := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt hf,
      eventually_differentiableAt_of_contDiffAt hg] with ζ h1 h2
    rw [fderiv_fun_add h1 h2]
    rfl
  show fderiv ℝ (fun ζ => fderiv ℝ (fun ξ => f ξ + g ξ) ζ u) η v = _
  rw [hev.fderiv_eq, fderiv_fun_add (differentiableAt_fderiv_apply hf) (differentiableAt_fderiv_apply hg)]
  rfl
theorem secondDerivAlong_const_mul (c : ℝ) (hf : ContDiffAt ℝ 2 f η) :
    secondDerivAlong (fun ζ => c * f ζ) η u v = c * secondDerivAlong f η u v := by
  have hev : (fun ζ => fderiv ℝ (fun ξ => c * f ξ) ζ u) =ᶠ[𝓝 η]
      fun ζ => c * fderiv ℝ f ζ u := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt hf] with ζ h1
    rw [fderiv_const_mul h1]
    rfl
  show fderiv ℝ (fun ζ => fderiv ℝ (fun ξ => c * f ξ) ζ u) η v = _
  rw [hev.fderiv_eq, fderiv_const_mul (differentiableAt_fderiv_apply hf)]
  rfl
theorem secondDerivAlong_sum {α : Type} {s : Finset α} {h : α → BondField ι → ℝ}
    (hh : ∀ i ∈ s, ContDiffAt ℝ 2 (h i) η) :
    secondDerivAlong (fun ζ => ∑ i ∈ s, h i ζ) η u v = ∑ i ∈ s, secondDerivAlong (h i) η u v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [secondDerivAlong]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 : ContDiffAt ℝ 2 (fun ζ => ∑ i ∈ s, h i ζ) η :=
      ContDiffAt.sum fun i hi => hh i (Finset.mem_insert_of_mem hi)
    rw [secondDerivAlong_add (hh a (Finset.mem_insert_self a s)) h1,
      ih fun i hi => hh i (Finset.mem_insert_of_mem hi)]
end Sum
end SecondDerivatives
section Kernel
variable {F : BlockFrame}
def cellKernel (κ : ℝ) (Y : F.Cell) (b b' : ChordBond F) : ℝ :=
  Real.exp (-(8 * κ * (cellDistReal Y (bondCell b) + cellDistReal Y (bondCell b')))) *
    Real.exp (-(8 * κ * cellDistReal (bondCell b) (bondCell b')))
def cellKernelSum (κ : ℝ) (b b' : ChordBond F) : ℝ := ∑ Y ∈ finiteCells F, cellKernel κ Y b b'
def siteKernelSum (κ : ℝ) (b b' : ChordBond F) : ℝ :=
  ∑ y ∈ sitesOfCells (finiteCells F) F.depth, cellKernel κ (enclosingCell y) b b'
theorem cellDistReal_pair_le_bondSpan {k : ℕ} (Y : F.Cell) (c' : Fin k → F.Site F.top × Fin 4)
    (l l' : Fin k) : cellDistReal (c' l).1 (c' l').1 ≤ (bondSpan Y c' : ℝ) := by
  have h1 : siteSupDist (c' l).1 (c' l').1 ≤
      Finset.univ.sup fun l' : Fin k => siteSupDist (c' l).1 (c' l').1 :=
    Finset.le_sup (f := fun l' : Fin k => siteSupDist (c' l).1 (c' l').1) (Finset.mem_univ l')
  have h2 : (Finset.univ.sup fun l' : Fin k => siteSupDist (c' l).1 (c' l').1) ≤
      Finset.univ.sup fun l : Fin k => Finset.univ.sup fun l' : Fin k => siteSupDist (c' l).1 (c' l').1 :=
    Finset.le_sup (f := fun l : Fin k => Finset.univ.sup fun l' : Fin k => siteSupDist (c' l).1 (c' l').1)
      (Finset.mem_univ l)
  have h3 : siteSupDist (c' l).1 (c' l').1 ≤ bondSpan Y c' := (h1.trans h2).trans (le_max_right _ _)
  show ((cellSupDist (c' l).1 (c' l').1 : ℕ) : ℝ) ≤ _
  have e : cellSupDist (c' l).1 (c' l').1 = siteSupDist (c' l).1 (c' l').1 := rfl
  rw [e]
  exact_mod_cast h3
theorem exp_chordBondSpan_le_cellKernel {κ : ℝ} (hκ : 0 < κ) (Y : F.Cell) (b b' : ChordBond F) :
    Real.exp (-(2 ^ 5 * κ * chordBondSpan Y ![b, b'])) ≤ cellKernel κ Y b b' := by
  set s : ℝ := (chordBondSpan Y ![b, b'] : ℝ) with hs
  have s1 : cellDistReal Y (bondCell b) ≤ s := cellDistReal_le_chordBondSpan Y ![b, b'] 0
  have s2 : cellDistReal Y (bondCell b') ≤ s := cellDistReal_le_chordBondSpan Y ![b, b'] 1
  have s3 : cellDistReal (bondCell b) (bondCell b') ≤ s :=
    cellDistReal_pair_le_bondSpan Y
      (fun l => (enclosingCell ((![b, b'] : Fin 2 → ChordBond F) l).1.1, (0 : Fin 4))) 0 1
  simp only [cellKernel]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left s1 hκ.le, mul_le_mul_of_nonneg_left s2 hκ.le,
    mul_le_mul_of_nonneg_left s3 hκ.le]
theorem cellKernel_symm (κ : ℝ) (pl : IsSiteDistance (cellDistReal (F := F))) (Y : F.Cell)
    (b b' : ChordBond F) : cellKernel κ Y b b' = cellKernel κ Y b' b := by
  simp only [cellKernel, pl.symm (bondCell b) (bondCell b'), add_comm]
variable {star : Bool} {a ρA ρ κ δ E E₃ C x : ℝ} {L m : ℕ} {f : LocalFamily} {V : F.GaugeField F.top}
theorem cellExponent_contDiffAt (EB : CellExponentBounds star a ρA ρ x κ C m V) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ContDiffAt ℝ 3 (cellExponent star a ρA x m Y V) η := by
  have h := EB.smooth Y η 0 noBonds noDirections hη
  have h2 : ContDiffAt ℝ 3 (fun ζ : StepVariable (finiteCells F) =>
      (((0 : Fin 0 → ℝ), ζ) : (Fin 0 → ℝ) × StepVariable (finiteCells F))) η :=
    contDiffAt_const.prodMk contDiffAt_id
  have h3 := ContDiffAt.comp η h h2
  have e : ((fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) =>
      cellExponent star a ρA x m Y (leftTranslate (bondSpread noBonds noDirections q.1) V) q.2) ∘
      fun ζ : StepVariable (finiteCells F) =>
        (((0 : Fin 0 → ℝ), ζ) : (Fin 0 → ℝ) × StepVariable (finiteCells F))) =
      cellExponent star a ρA x m Y V := by
    funext ζ
    simp only [Function.comp_apply]
    rw [leftTranslate_bondSpread_at_zero]
  rwa [e] at h3
theorem eventually_forall_norm_lt {η : BondField (ChordBond F)} (hρ : 0 < ρ) (hη : ∀ b, ‖η b‖ < ρ) :
    ∀ᶠ ζ in 𝓝 η, ∀ b, ‖ζ b‖ < ρ := by
  have h1 : ‖η‖ < ρ := (pi_norm_lt_iff hρ).mpr hη
  have : {ζ : BondField (ChordBond F) | ‖ζ‖ < ρ} ∈ 𝓝 η :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds h1
  filter_upwards [this] with ζ hζ
  exact (pi_norm_lt_iff hρ).mp hζ
theorem abs_secondDerivAlong_stepExponent_le (EB : CellExponentBounds star a ρA ρ x κ C m V)
    (R : CentredExpansionBounds star a ρA ρ κ δ E E₃ C L m f V) (hρ : 0 < ρ) (hκ : 0 < κ) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (hx : 0 ≤ x) {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (η : BondField (ChordBond F)) (hη : ∀ b, ‖η b‖ < ρ) (b b' : ChordBond F) {e e' : BondVector}
    (he : ‖e‖ = 1) (he' : ‖e'‖ = 1) :
    |secondDerivAlong (stepExponent star a ρA x m f ν V) η (bondVariation b e) (bondVariation b' e')| ≤
      C * x * cellKernelSum κ b b' + C * E * siteKernelSum κ b b' := by
  set S₀ : BondField (ChordBond F) → ℝ := stepExponent star a ρA x m (fun _ _ _ => 0) 0 V with hS₀
  set Sb : BondField (ChordBond F) → ℝ := fun ζ => ∑ Y ∈ finiteCells F, cellExponent star a ρA x m Y V ζ
    with hSb
  set Sr : BondField (ChordBond F) → ℝ :=
    fun ζ => ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion star a ρA m f y ζ V with hSr
  have hcl : ∀ b, ‖η b‖ ≤ ρ := fun b => (hη b).le
  have cb : ∀ Y ∈ finiteCells F, ContDiffAt ℝ 2 (cellExponent star a ρA x m Y V) η := fun Y _ =>
    (cellExponent_contDiffAt EB Y η hcl).of_le (by norm_num)
  have cr : ∀ y ∈ sitesOfCells (finiteCells F) F.depth,
      ContDiffAt ℝ 2 (fun ζ => centredExpansion star a ρA m f y ζ V) η := fun y _ =>
    (centredExpansion_contDiffAt R y η hcl).of_le (by norm_num)
  have cSb : ContDiffAt ℝ 2 Sb η := ContDiffAt.sum cb
  have cSr : ContDiffAt ℝ 2 Sr η := ContDiffAt.sum cr
  have hnear : Sb =ᶠ[𝓝 η] S₀ := by
    filter_upwards [eventually_forall_norm_lt hρ hη] with ζ hζ
    exact (EB.sum_eq ζ hζ).symm
  have cS₀ : ContDiffAt ℝ 2 S₀ η := cSb.congr_of_eventuallyEq hnear.symm
  have hP : stepExponent star a ρA x m f ν V = fun ζ => S₀ ζ + (-ν) * Sr ζ := by
    funext ζ
    simp only [stepExponent, hS₀, hSr]
    ring
  rw [hP, secondDerivAlong_add cS₀ (contDiffAt_const.mul cSr), secondDerivAlong_const_mul _ cSr,
    secondDerivAlong_congr hnear, secondDerivAlong_sum cb, secondDerivAlong_sum cr]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_neg, abs_of_nonneg hν0]
  have t1 : |∑ Y ∈ finiteCells F, secondDerivAlong (cellExponent star a ρA x m Y V) η (bondVariation b e)
      (bondVariation b' e')| ≤ C * x * cellKernelSum κ b b' := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [cellKernelSum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Y _
    refine (EB.second_deriv Y η b b' e e' hη he he').trans ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hx)
    refine le_trans (Real.exp_le_exp.mpr ?_) (exp_chordBondSpan_le_cellKernel hκ Y b b')
    have s0 : (0 : ℝ) ≤ (chordBondSpan Y ![b, b'] : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hκ.le s0]
  have t2 : |∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      secondDerivAlong (fun ζ => centredExpansion star a ρA m f y ζ V) η
      (bondVariation b e) (bondVariation b' e')| ≤ C * E * siteKernelSum κ b b' := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [siteKernelSum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    refine (R.second_deriv y η b b' e e' hη he he').trans ?_
    exact mul_le_mul_of_nonneg_left (exp_chordBondSpan_le_cellKernel hκ (enclosingCell y) b b')
      (mul_nonneg hC hE)
  have t3 : ν * |∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      secondDerivAlong (fun ζ => centredExpansion star a ρA m f y ζ V) η
      (bondVariation b e) (bondVariation b' e')| ≤ C * E * siteKernelSum κ b b' := by
    have h0 := abs_nonneg (∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      secondDerivAlong (fun ζ => centredExpansion star a ρA m f y ζ V) η (bondVariation b e) (bondVariation b' e'))
    nlinarith
  linarith
end Kernel
section ConvexExponent
variable {F : BlockFrame}
structure DecaySumBounds (F : BlockFrame) (κ W W₁ W₃ Wy : ℝ) : Prop where
  bond_sum : ∀ z : F.Cell, ∑ b : ChordBond F, _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (κ / 16) (bondCell b) z ≤ W
  cell_sum : ∀ b : ChordBond F, ∑ Y ∈ finiteCells F, Real.exp (-(8 * κ * cellDistReal Y (bondCell b))) ≤ W₁
  site_sum : ∀ b : ChordBond F, ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
    Real.exp (-(8 * κ * cellDistReal (enclosingCell y) (bondCell b))) ≤ W₃
  site_weight_sum : ∀ z : F.Cell, ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (κ / 16) (enclosingCell y) z ≤ Wy
variable {κ W W₁ W₃ Wy : ℝ}
theorem cellKernel_mul_exp_le (pl : IsSiteDistance (cellDistReal (F := F))) (hκ : 0 < κ) (Y : F.Cell)
    (b b' : ChordBond F) :
    cellKernel κ Y b b' * Real.exp (κ * cellDistReal (bondCell b) (bondCell b')) ≤
      Real.exp (-(8 * κ * cellDistReal Y (bondCell b))) * Real.exp (-(8 * κ * cellDistReal Y (bondCell b'))) := by
  simp only [cellKernel]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have n := mul_nonneg hκ.le (pl.nonneg (bondCell b) (bondCell b'))
  nlinarith
theorem sum_exp_bondCell_le (S : DecaySumBounds F κ W W₁ W₃ Wy) (pl : IsSiteDistance (cellDistReal (F := F)))
    (hκ : 0 < κ) (Y : F.Cell) : ∑ b' : ChordBond F, Real.exp (-(8 * κ * cellDistReal Y (bondCell b'))) ≤ W := by
  refine le_trans (Finset.sum_le_sum fun b' _ => ?_) (S.bond_sum Y)
  apply Real.exp_le_exp.mpr
  rw [pl.symm Y (bondCell b')]
  have n := pl.nonneg (bondCell b') Y
  nlinarith [mul_nonneg hκ.le n]
theorem decaySumBounds_nonneg (S : DecaySumBounds F κ W W₁ W₃ Wy) (z : F.Cell) : 0 ≤ W :=
  (Finset.sum_nonneg fun b _ => expWeight_nonneg _ _ _).trans (S.bond_sum z)
theorem cellKernelSum_rows_le (S : DecaySumBounds F κ W W₁ W₃ Wy) (pl : IsSiteDistance (cellDistReal (F := F)))
    (hκ : 0 < κ) (b : ChordBond F) :
    ∑ b', cellKernelSum κ b b' * Real.exp (κ * cellDistReal (bondCell b) (bondCell b')) ≤ W₁ * W := by
  have hW : 0 ≤ W := decaySumBounds_nonneg S (bondCell b)
  simp only [cellKernelSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ Y ∈ finiteCells F, ∑ b' : ChordBond F,
      cellKernel κ Y b b' * Real.exp (κ * cellDistReal (bondCell b) (bondCell b')) ≤
      Real.exp (-(8 * κ * cellDistReal Y (bondCell b))) * W := by
    intro Y _
    refine (Finset.sum_le_sum fun b' _ => cellKernel_mul_exp_le pl hκ Y b b').trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_exp_bondCell_le S pl hκ Y) (Real.exp_pos _).le
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (S.cell_sum b) hW
theorem siteKernelSum_rows_le (S : DecaySumBounds F κ W W₁ W₃ Wy) (pl : IsSiteDistance (cellDistReal (F := F)))
    (hκ : 0 < κ) (b : ChordBond F) :
    ∑ b', siteKernelSum κ b b' * Real.exp (κ * cellDistReal (bondCell b) (bondCell b')) ≤ W₃ * W := by
  have hW : 0 ≤ W := decaySumBounds_nonneg S (bondCell b)
  simp only [siteKernelSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ y ∈ sitesOfCells (finiteCells F) F.depth, ∑ b' : ChordBond F,
      cellKernel κ (enclosingCell y) b b' * Real.exp (κ * cellDistReal (bondCell b) (bondCell b')) ≤
      Real.exp (-(8 * κ * cellDistReal (enclosingCell y) (bondCell b))) * W := by
    intro y _
    refine (Finset.sum_le_sum fun b' _ => cellKernel_mul_exp_le pl hκ (enclosingCell y) b b').trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_exp_bondCell_le S pl hκ (enclosingCell y)) (Real.exp_pos _).le
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (S.site_sum b) hW
theorem cellKernelSum_nonneg (κ : ℝ) (b b' : ChordBond F) : 0 ≤ cellKernelSum κ b b' :=
  Finset.sum_nonneg fun Y _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
theorem siteKernelSum_nonneg (κ : ℝ) (b b' : ChordBond F) : 0 ≤ siteKernelSum κ b b' :=
  Finset.sum_nonneg fun Y _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
variable {ρ C E x m : ℝ} {p : ℝ → ℝ} {P : BondField (ChordBond F) → ℝ}
theorem exists_localizedMeasureHyp (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hκ : 0 < κ)
    (pl : IsSiteDistance (cellDistReal (F := F))) (S : DecaySumBounds F κ W W₁ W₃ Wy) (hC : 0 ≤ C)
    (hx : 0 ≤ x) (hE0 : 0 ≤ E) (hEx : E ≤ x) (hm1 : 1 ≤ m) {c₁ : ℝ} (hc₁0 : 0 ≤ c₁)
    (hc₁ : C * x * (W₁ * W) + C * x * (W₃ * W) ≤ c₁ * m)
    (EC : IsConvexClassMember ρ m κ (chordBondDist F) P)
    (hH : ∀ η : BondField (ChordBond F), (∀ b, ‖η b‖ < ρ) → ∀ (b b' : ChordBond F) (e e' : BondVector),
      ‖e‖ = 1 → ‖e'‖ = 1 →
      |secondDerivAlong P η (bondVariation b e) (bondVariation b' e')| ≤
        C * x * cellKernelSum κ b b' + C * E * siteKernelSum κ b b') :
    ∃ (Ψ : BondField (ChordBond F) → ℝ) (K : ChordBond F → ChordBond F → ℝ),
      (∀ η, (∀ b, ‖η b‖ < ρ) → Ψ η = P η) ∧
      LocalizedMeasureHyp ρ p m κ Ψ K c₁ W (4 * κ) cellDistReal bondCell := by
  classical
  obtain ⟨Ψ, K₀, hag, hconv, hslope⟩ := EC
  have hd : chordBondDist F = fun b b' => cellDistReal (bondCell b) (bondCell b') := rfl
  rw [hd] at hconv
  set K₂ : ChordBond F → ChordBond F → ℝ :=
    fun b b' => C * x * cellKernelSum κ b b' + C * E * siteKernelSum κ b b' with hK₂
  have hK₂0 : ∀ b b', 0 ≤ K₂ b b' := fun b b' =>
    add_nonneg (mul_nonneg (mul_nonneg hC hx) (cellKernelSum_nonneg _ _ _))
      (mul_nonneg (mul_nonneg hC hE0) (siteKernelSum_nonneg _ _ _))
  have hK₂s : ∀ b b', K₂ b b' = K₂ b' b := by
    intro b b'
    simp only [hK₂, cellKernelSum, siteKernelSum, cellKernel_symm κ pl _ b b']
  have hker₂ : ∀ η : BondField (ChordBond F), (∀ b, ‖η b‖ < ρ) → ∀ (b b' : ChordBond F) (e e' : BondVector),
      |secondDerivAlong Ψ η (bondVariation b e) (bondVariation b' e')| ≤ K₂ b b' * ‖e‖ * ‖e'‖ := by
    intro η hη b b' e e'
    have hev : Ψ =ᶠ[𝓝 η] P := by
      filter_upwards [eventually_forall_norm_lt hρ hη] with ζ hζ
      exact hag ζ hζ
    have hform : ∀ u v : BondField (ChordBond F),
        secondDerivAlong Ψ η u v = fderiv ℝ (fderiv ℝ Ψ) η v u :=
      fun u v => secondDerivAlong_eq_fderiv_fderiv hconv.smooth η u v
    have st1 : ∀ e, ‖e‖ = 1 → ∀ e',
        |secondDerivAlong Ψ η (bondVariation b e) (bondVariation b' e')| ≤ K₂ b b' * ‖e'‖ := by
      intro e he e'
      refine abs_le_of_unit (f := fun e' => secondDerivAlong Ψ η (bondVariation b e) (bondVariation b' e'))
        (fun s e' => ?_) (hK₂0 b b') (fun e' he' => ?_) e'
      · simp only [hform, bondVariation_smul, map_smul, _root_.smul_apply, smul_eq_mul]
      · have := hH η hη b b' e e' he he'
        rw [secondDerivAlong_congr hev] at this
        exact this
    have st2 := abs_le_of_unit (f := fun e => secondDerivAlong Ψ η (bondVariation b e) (bondVariation b' e'))
      (fun s e => by simp only [hform, bondVariation_smul, map_smul, _root_.smul_apply, smul_eq_mul])
      (mul_nonneg (hK₂0 b b') (norm_nonneg e')) (fun e he => st1 e he e') e
    refine st2.trans (le_of_eq ?_)
    ring
  refine ⟨Ψ, fun b b' => min (K₀ b b') (K₂ b b'), hag, ?_⟩
  have hdist : IsPseudoMetricOnBonds (fun b b' : ChordBond F => cellDistReal (bondCell b) (bondCell b')) := by
    refine ⟨fun b => ?_, fun b b' => pl.symm _ _, fun b b' b'' => pl.triangle _ _ _⟩
    simp [cellDistReal, cellSupDist]
  have hconv' : IsUniformlyConvexDecaying ρ m κ (fun b b' => cellDistReal (bondCell b) (bondCell b')) Ψ
      (fun b b' => min (K₀ b b') (K₂ b b')) := by
    refine ⟨hconv.smooth, hconv.floor, fun η hη b b' e e' => ?_, fun b b' => ?_, fun b => ?_⟩
    · have n := mul_nonneg (norm_nonneg e) (norm_nonneg e')
      have h1 := hconv.kernel η hη b b' e e'
      have h2 := hker₂ η hη b b' e e'
      rcases min_cases (K₀ b b') (K₂ b b') with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> assumption
    · simp only [hconv.symm b b', hK₂s b b']
    · refine le_trans (Finset.sum_le_sum fun b' _ => ?_) (hconv.standingConstraints b)
      have n : 0 ≤ Real.exp (2 * κ * cellDistReal (bondCell b) (bondCell b')) - 1 := by
        have := Real.one_le_exp (mul_nonneg (by positivity : 0 ≤ 2 * κ) (pl.nonneg (bondCell b) (bondCell b')))
        linarith
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) n
  have hrows : ∀ b, ∑ b', min (K₀ b b') (K₂ b b') * Real.exp (κ * cellDistReal (bondCell b) (bondCell b')) ≤
      c₁ * m := by
    intro b
    have s1 : ∑ b', min (K₀ b b') (K₂ b b') * Real.exp (κ * cellDistReal (bondCell b) (bondCell b')) ≤
        ∑ b', K₂ b b' * Real.exp (κ * cellDistReal (bondCell b) (bondCell b')) :=
      Finset.sum_le_sum fun b' _ =>
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le
    have s2 : ∑ b', K₂ b b' * Real.exp (κ * cellDistReal (bondCell b) (bondCell b')) =
        C * x * ∑ b', cellKernelSum κ b b' * Real.exp (κ * cellDistReal (bondCell b) (bondCell b')) +
          C * E * ∑ b', siteKernelSum κ b b' * Real.exp (κ * cellDistReal (bondCell b) (bondCell b')) := by
      simp only [hK₂, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    have hW : 0 ≤ W := decaySumBounds_nonneg S (bondCell b)
    have hW₃ : 0 ≤ W₃ := by
      refine le_trans ?_ (S.site_sum b)
      exact Finset.sum_nonneg fun y _ => (Real.exp_pos _).le
    have t1 := mul_le_mul_of_nonneg_left (cellKernelSum_rows_le S pl hκ b) (mul_nonneg hC hx)
    have t2 := mul_le_mul_of_nonneg_left (siteKernelSum_rows_le S pl hκ b) (mul_nonneg hC hE0)
    have t3 : C * E * (W₃ * W) ≤ C * x * (W₃ * W) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEx hC) (mul_nonneg hW₃ hW)
    rw [s2] at s1
    linarith
  have hsumW : ∀ b₀ : ChordBond F,
      ∑ b : ChordBond F, Real.exp (-(2 * κ * cellDistReal (bondCell b) (bondCell b₀))) ≤ W := by
    intro b₀
    refine le_trans (Finset.sum_le_sum fun b _ => ?_) (S.bond_sum (bondCell b₀))
    apply Real.exp_le_exp.mpr
    have n := pl.nonneg (bondCell b) (bondCell b₀)
    nlinarith [mul_nonneg hκ.le n]
  have hdata : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ :=
    ⟨hρ, extendedCutoff_isRadialCutoff hR hρ hp, hconv.smooth⟩
  exact ⟨⟨hρ, hp, hm1, hκ, hdist, hconv', hdata, hslope, hrows, hsumW, hc₁0⟩, pl, S.bond_sum,
    le_rfl⟩
end ConvexExponent
section CovarianceAtTop
open MeasureTheory
variable {F : BlockFrame} {ρ : ℝ} {p : ℝ → ℝ}
theorem radialWeightProd_eq_zero (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (η : BondField (ChordBond F)) (hη : ¬ ∀ b, ‖η b‖ < ρ) : radialWeightProd (extendedCutoff ρ p) η = 0 := by
  simp only [not_forall, not_lt] at hη
  obtain ⟨b, hb⟩ := hη
  exact Finset.prod_eq_zero (Finset.mem_univ b) (extendedCutoff_eq_zero hR hρ hp hb)
theorem cutoffMean_eq_ballExpectation (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    {Ψ₁ Ψ₂ H f : BondField (ChordBond F) → ℝ} (hΨ : ∀ η, (∀ b, ‖η b‖ < ρ) → Ψ₁ η = Ψ₂ η)
    (hH : ∀ η, (∀ b, ‖η b‖ < ρ) → H η = f η) :
    cutoffMean ρ p Ψ₁ H = ballExpectation (extendedCutoff ρ p) Ψ₂ f := by
  have hw : ∀ η : BondField (ChordBond F), cutoffWeight ρ p η = radialWeightProd (extendedCutoff ρ p) η := by
    intro η
    have := congrFun (radialWeightProd_cutoffFactor (ι := ChordBond F) ρ p) η
    exact this
  have e1 : ∀ η, H η * (cutoffWeight ρ p η * Real.exp (- Ψ₁ η)) =
      f η * ballDensity (extendedCutoff ρ p) Ψ₂ η := by
    intro η
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · rw [hw, hH η hη, hΨ η hη]
      rfl
    · simp [hw, ballDensity, radialWeightProd_eq_zero hR hρ hp η hη]
  have e2 : ∀ η, cutoffWeight ρ p η * Real.exp (- Ψ₁ η) = ballDensity (extendedCutoff ρ p) Ψ₂ η := by
    intro η
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · rw [hw, hΨ η hη]
      rfl
    · simp [hw, ballDensity, radialWeightProd_eq_zero hR hρ hp η hη]
  have i1 : (∫ η, H η * (cutoffWeight ρ p η * Real.exp (- Ψ₁ η))) =
      ∫ η, f η * ballDensity (extendedCutoff ρ p) Ψ₂ η :=
    integral_congr_ae (Filter.Eventually.of_forall e1)
  have i2 : (∫ η, cutoffWeight ρ p η * Real.exp (- Ψ₁ η)) = ∫ η, ballDensity (extendedCutoff ρ p) Ψ₂ η :=
    integral_congr_ae (Filter.Eventually.of_forall e2)
  simp only [cutoffMean, ballExpectation]
  rw [i1, i2]
theorem cutoffCovariance_eq_ballCovariance (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    {Ψ₁ Ψ₂ H H' f h : BondField (ChordBond F) → ℝ} (hΨ : ∀ η, (∀ b, ‖η b‖ < ρ) → Ψ₁ η = Ψ₂ η)
    (hH : ∀ η, (∀ b, ‖η b‖ < ρ) → H η = f η) (hH' : ∀ η, (∀ b, ‖η b‖ < ρ) → H' η = h η) :
    cutoffCovariance ρ p Ψ₁ H H' = ballCovariance (extendedCutoff ρ p) Ψ₂ f h := by
  simp only [cutoffCovariance, ballCovariance]
  rw [cutoffMean_eq_ballExpectation hR hρ hp hΨ hH, cutoffMean_eq_ballExpectation hR hρ hp hΨ hH',
    cutoffMean_eq_ballExpectation hR hρ hp hΨ (f := fun η => f η * h η)
      (fun η hη => by rw [hH η hη, hH' η hη])]
theorem expWeight_mul_le_bondSpan (pl : IsSiteDistance (cellDistReal (F := F))) {κ : ℝ} (hκ : 0 < κ)
    (Y Y' : F.Cell) (c : Fin 3 → F.Site F.top × Fin 4) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (κ / 8) Y Y' * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (κ / 16) Y' (c 0).1 *
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (κ / 16) Y' (c 1).1 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (κ / 16) Y' (c 2).1) ≤
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (κ / 16) Y' Y * Real.exp (-(κ / 2 ^ 5 * bondSpan Y c)) := by
  set d := cellDistReal Y Y' with hd
  set d0 := cellDistReal Y' (c 0).1 with h0
  set d1 := cellDistReal Y' (c 1).1 with h1
  set d2 := cellDistReal Y' (c 2).1 with h2
  have n : 0 ≤ d := pl.nonneg _ _
  have n0 : 0 ≤ d0 := pl.nonneg _ _
  have n1 : 0 ≤ d1 := pl.nonneg _ _
  have n2 : 0 ≤ d2 := pl.nonneg _ _
  have hall : ∀ l, cellDistReal Y' (c l).1 ≤ d0 + d1 + d2 := by
    intro l
    fin_cases l
    · show d0 ≤ _
      linarith
    · show d1 ≤ _
      linarith
    · show d2 ≤ _
      linarith
  have hs1 : ∀ l, cellDistReal Y (c l).1 ≤ 2 * (d + d0 + d1 + d2) := by
    intro l
    have := pl.triangle Y Y' (c l).1
    have := hall l
    linarith
  have hs2 : ∀ l l', cellDistReal (c l).1 (c l').1 ≤ 2 * (d + d0 + d1 + d2) := by
    intro l l'
    have t := pl.triangle (c l).1 Y' (c l').1
    have s := pl.symm (c l).1 Y'
    have a1 := hall l
    have a2 := hall l'
    rw [s] at t
    linarith
  set N : ℕ := 2 * (cellSupDist Y Y' + cellSupDist Y' (c 0).1 + cellSupDist Y' (c 1).1 +
    cellSupDist Y' (c 2).1) with hN
  have hNr : (N : ℝ) = 2 * (d + d0 + d1 + d2) := by
    simp only [hN, hd, h0, h1, h2, cellDistReal]
    push_cast
    ring
  have hspan : bondSpan Y c ≤ N := by
    apply max_le
    · apply Finset.sup_le
      intro l _
      have := hs1 l
      rw [← hNr] at this
      have e : cellDistReal Y (c l).1 = ((siteSupDist Y (c l).1 : ℕ) : ℝ) := rfl
      rw [e] at this
      exact_mod_cast this
    · apply Finset.sup_le
      intro l _
      apply Finset.sup_le
      intro l' _
      have := hs2 l l'
      rw [← hNr] at this
      have e : cellDistReal (c l).1 (c l').1 = ((siteSupDist (c l).1 (c l').1 : ℕ) : ℝ) := rfl
      rw [e] at this
      exact_mod_cast this
  have hsr : (bondSpan Y c : ℝ) ≤ 2 * (d + d0 + d1 + d2) := by
    rw [← hNr]
    exact_mod_cast hspan
  have es : cellDistReal Y' Y = d := pl.symm _ _
  simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight, es]
  rw [← hd, ← h0, ← h1, ← h2, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hsr hκ.le, mul_nonneg hκ.le n, mul_nonneg hκ.le n0,
    mul_nonneg hκ.le n1, mul_nonneg hκ.le n2]
end CovarianceAtTop
section SumAtTop
open MeasureTheory
variable {F : BlockFrame} {ρ : ℝ} {p : ℝ → ℝ}
structure TopLevelData (F : BlockFrame) (star : Bool) (a ρA ρ lam x κ δ E E₃ C CF : ℝ) (L M : ℕ)
    (p : ℝ → ℝ) (f : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top) (Λ : LiePair → imaginaryQuaternions)
    (r₀ δ₂ κ₂ σ : ℝ) (Kk : ℕ → ℝ) (W W₁ W₃ Wy c₁ : ℝ) : Prop where
  radius_pos : 0 < ρ
  cutoff : IsCutoff ρ p
  rate_pos : 0 < κ
  dist : IsSiteDistance (cellDistReal (F := F))
  sums : DecaySumBounds F κ W W₁ W₃ Wy
  const_nonneg : 0 ≤ C
  frameConst_nonneg : 0 ≤ CF
  energy_nonneg : 0 ≤ E
  energy_le : E ≤ E₃
  coupling_nonneg : 0 ≤ x
  energy_le_coupling : E ≤ x
  one_le_mass : 1 ≤ x * lam / 4
  expansionConst_nonneg : 0 ≤ c₁
  expansionConst_bound : C * x * (W₁ * W) + C * x * (W₃ * W) ≤ c₁ * (x * lam / 4)
  convex : IsConvexClassMember ρ (x * lam / 4) κ (chordBondDist F) (stepExponent star a ρA x M f ν V)
  exponentBounds : CellExponentBounds star a ρA ρ x κ C M V
  expansionBounds : CentredExpansionBounds star a ρA ρ κ δ E E₃ C L M f V
  weight_nonneg : 0 ≤ ν
  weight_le_one : ν ≤ 1
  log : ProductLog Λ r₀
  frameSmall : FrameSmallness star a ρA δ₂ κ₂ CF σ Kk M V
  rate_le : 12 * (4 * κ) ≤ δ₂
  room : ∀ b : ChordBond F, ‖frameCoord V star a ρA M b‖ + ρ < r₀
  cover : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth
theorem sum_abs_cutoffCovariance_le (hR : CutoffFactorIsRadialCutoff)
    (hComp : ThirdOrderChainRule) (hIn : ThirdOrderChainRuleVectorValued)
    {star : Bool} {a ρA lam x κ δ E E₃ C CF : ℝ} {L M : ℕ} {f : LocalFamily} {ν : ℝ}
    {V : F.GaugeField F.top} {Λ : LiePair → imaginaryQuaternions} {r₀ δ₂ κ₂ σ : ℝ} {Kk : ℕ → ℝ}
    {W W₁ W₃ Wy c₁ : ℝ}
    (D : TopLevelData F star a ρA ρ lam x κ δ E E₃ C CF L M p f ν V Λ r₀ δ₂ κ₂ σ Kk W W₁ W₃ Wy c₁)
    {CL : ℝ} (hCL0 : 0 ≤ CL)
    (hCL : ∀ (z : LiePair) (j : ℕ), j ≤ 5 → ‖iteratedFDeriv ℝ j Λ z‖ ≤ CL)
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hBd : CovarianceThirdDerivBound ρ p c₁ W (1 + 5 * CL * (1 + CF) ^ 3) Cf)
    (y : F.Site F.depth) (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions)
    (hX : AreUnitVectors X) :
    ∑ y' ∈ sitesOfCells (finiteCells F) F.depth,
      |cutoffCovariance ρ p (stepExponent star a ρA x M f ν V) (fun η => centredExpansion star a ρA M f y η V)
        (fun η => bondDeriv (centredExpansion star a ρA M f y' η) V c X)| ≤
      Cf * ((C * E) * (C * E₃) / Real.sqrt (x * lam / 4)) * Wy *
        Real.exp (-(κ / 2 ^ 5 * bondSpan (enclosingCell y) c)) := by
  have hρ := D.radius_pos
  have hp := D.cutoff
  have hκ := D.rate_pos
  have pl := D.dist
  have S := D.sums
  have hE₃ : 0 ≤ E₃ := D.energy_nonneg.trans D.energy_le
  obtain ⟨Ψ, K, hag, core⟩ := exists_localizedMeasureHyp hR hρ hp hκ pl S D.const_nonneg D.coupling_nonneg
    D.energy_nonneg D.energy_le_coupling D.one_le_mass D.expansionConst_nonneg D.expansionConst_bound
    D.convex (fun η hη b b' e e' he he' => abs_secondDerivAlong_stepExponent_le D.exponentBounds D.expansionBounds
      hρ hκ D.const_nonneg D.energy_nonneg D.coupling_nonneg D.weight_nonneg D.weight_le_one
      η hη b b' he he')
  obtain ⟨g, r₁, hr₁, hgeq, hgJ⟩ := centredExpansion_thirdJetBound D.expansionBounds hρ hκ D.const_nonneg
    D.energy_nonneg hE₃ y
  have hmoves := pairDerivBounds_framePair c X V star a ρA M hIn hX D.frameSmall D.frameConst_nonneg
    (by positivity) D.rate_le
  have hF := thirdFieldBounds_of_pairDerivBounds (ρ := ρ) (w₀ := frameCoord V star a ρA M)
    (δ := cellDistReal) (loc := bondCell) (a := 4 * κ)
    (c := fun l => (c l).1) D.log.contDiff hCL hCL0 hmoves
  have hEE' : C * E ≤ C * E₃ := mul_le_mul_of_nonneg_left D.energy_le D.const_nonneg
  have hCE : 0 ≤ C * E := mul_nonneg D.const_nonneg D.energy_nonneg
  have each : ∀ y' ∈ sitesOfCells (finiteCells F) F.depth,
      |cutoffCovariance ρ p (stepExponent star a ρA x M f ν V) (fun η => centredExpansion star a ρA M f y η V)
        (fun η => bondDeriv (centredExpansion star a ρA M f y' η) V c X)| ≤
      Cf * ((C * E) * (C * E₃) / Real.sqrt (x * lam / 4)) *
        (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (κ / 16) (enclosingCell y') (enclosingCell y) *
          Real.exp (-(κ / 2 ^ 5 * bondSpan (enclosingCell y) c))) := by
    intro y' _
    obtain ⟨G, r₂, hr₂, hGeq, hGJ⟩ := centredExpansion_thirdJetBound D.expansionBounds hρ hκ D.const_nonneg
      D.energy_nonneg hE₃ y'
    have e1 : cutoffCovariance ρ p (stepExponent star a ρA x M f ν V)
        (fun η => centredExpansion star a ρA M f y η V)
        (fun η => bondDeriv (centredExpansion star a ρA M f y' η) V c X) =
        ballCovariance (extendedCutoff ρ p) Ψ g
          (ThirdDerivative.thirdDerivAlong G (moveField₁ Λ (framePair c X V star a ρA M) (frameCoord V star a ρA M) 0)
            (moveField₁ Λ (framePair c X V star a ρA M) (frameCoord V star a ρA M) 1)
            (moveField₁ Λ (framePair c X V star a ρA M) (frameCoord V star a ρA M) 2)
            (moveField₂ Λ (framePair c X V star a ρA M) (frameCoord V star a ρA M) 0 1)
            (moveField₂ Λ (framePair c X V star a ρA M) (frameCoord V star a ρA M) 0 2)
            (moveField₂ Λ (framePair c X V star a ρA M) (frameCoord V star a ρA M) 1 2)
            (moveField₃ Λ (framePair c X V star a ρA M) (frameCoord V star a ρA M))) := by
      refine cutoffCovariance_eq_ballCovariance hR hρ hp (fun η hη => (hag η hη).symm)
        (fun η hη => (hgeq η fun b => (hη b).trans hr₁).symm) (fun η hη => ?_)
      refine bondDeriv_centredExpansion_eq c X V star a ρA M hComp hIn D.log hX D.frameSmall D.cover f y' (ρ := ρ)
        (fun ζ hζ => hGeq ζ fun b => (hζ b).trans hr₂) η hη hGJ.smooth.contDiffAt fun b => ?_
      have h1 : ‖frameCoord V star a ρA M b + coordsIsometry (η b)‖ ≤
          ‖frameCoord V star a ρA M b‖ + ‖η b‖ := by
        refine (_root_.norm_add_le _ _).trans ?_
        rw [coordsIsometry.norm_map]
      have h2 := D.room b
      have h3 := hη b
      linarith
    rw [e1]
    have h := hBd (ChordBond F) F.Cell _ κ (4 * κ) Ψ K cellDistReal bondCell g G (C * E) (C * E₃)
      (enclosingCell y) (enclosingCell y')
      (c 0).1 (c 1).1 (c 2).1 _ _ _ _ _ _ _ core hCE hEE' hgJ hGJ hF
    refine h.trans ?_
    have hw := expWeight_mul_le_bondSpan pl hκ (enclosingCell y) (enclosingCell y') c
    have hC0 : 0 ≤ Cf * ((C * E) * (C * E₃) / Real.sqrt (x * lam / 4)) := by
      have h4 : 0 ≤ C * E₃ := mul_nonneg D.const_nonneg hE₃
      positivity
    have := mul_le_mul_of_nonneg_left hw hC0
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
    · ring
    · ring
  refine (Finset.sum_le_sum each).trans ?_
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hfin := S.site_weight_sum (enclosingCell y)
  have hC0 : 0 ≤ Cf * ((C * E) * (C * E₃) / Real.sqrt (x * lam / 4)) := by
    have h4 : 0 ≤ C * E₃ := mul_nonneg D.const_nonneg hE₃
    positivity
  have t := mul_le_mul_of_nonneg_right hfin
    (Real.exp_pos (-(κ / 2 ^ 5 * bondSpan (enclosingCell y) c))).le
  have t2 := mul_le_mul_of_nonneg_left t hC0
  refine t2.trans (le_of_eq ?_)
  ring
end SumAtTop
section Table
open MeasureTheory
variable {F : BlockFrame}
theorem isSiteDistance_cellDistReal (hG : CubicTorusCellGeometry) (hodd : Odd F.blockSide)
    (hc : IsLargeCubicTorus F) : IsSiteDistance (cellDistReal (F := F)) := by
  obtain ⟨-, -, h3, h4, -⟩ := hG.1 F hodd hc
  refine ⟨fun x y => Nat.cast_nonneg _, fun x y => ?_, fun x y z => ?_⟩
  · simp only [cellDistReal, h3 x y]
  · simp only [cellDistReal]
    exact_mod_cast h4 x y z
theorem chordBonds_subset_fineBonds : chordBonds (finiteCells F) ⊆ fineBonds F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.chordBonds_subset_fineBonds <;> assumption
theorem sum_sites_le_sum_fineBonds (g : F.Site F.depth → ℝ) (hg : ∀ y, 0 ≤ g y) :
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, g y ≤ ∑ b ∈ fineBonds F, g b.1 := by
  unfold fineBonds
  rw [Finset.sum_product]
  apply Finset.sum_le_sum
  intro y _
  have := Finset.single_le_sum (f := fun _ : Fin 4 => g y) (fun _ _ => hg y) (Finset.mem_univ (0 : Fin 4))
  exact this
theorem decaySumBounds_of_geometry {κ C16 C8 S : ℝ} (hκ : 0 < κ) (hodd : Odd F.blockSide)
    (hc : IsLargeCubicTorus F)
    (pl : IsSiteDistance (cellDistReal (F := F)))
    (h16 : ∀ z : F.Cell, ∑ b ∈ fineBonds F, Real.exp (-(κ / 16 * cellSupDist (enclosingCell b.1) z)) ≤
      C16 * (F.blockSide : ℝ) ^ 4)
    (h8 : ∀ z : F.Cell, ∑ b ∈ fineBonds F, Real.exp (-(8 * κ * cellSupDist (enclosingCell b.1) z)) ≤
      C8 * (F.blockSide : ℝ) ^ 4)
    (hS : ∀ (y : F.Cell) (A : Finset F.Cell), ∑ z ∈ A, Real.exp (-(8 * κ * siteSupDist y z)) ≤ S) :
    DecaySumBounds F κ (C16 * (F.blockSide : ℝ) ^ 4) S (C8 * (F.blockSide : ℝ) ^ 4)
      (C16 * (F.blockSide : ℝ) ^ 4) := by
  refine ⟨fun z => ?_, fun b => ?_, fun b => ?_, fun z => ?_⟩
  · refine le_trans ?_ (h16 z)
    have e : ∑ b : ChordBond F, _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (κ / 16) (bondCell b) z =
        ∑ b ∈ chordBonds (finiteCells F), Real.exp (-(κ / 16 * cellSupDist (enclosingCell b.1) z)) :=
      Finset.sum_coe_sort (chordBonds (finiteCells F))
        (fun b => Real.exp (-(κ / 16 * cellSupDist (enclosingCell b.1) z)))
    rw [e]
    exact Finset.sum_le_sum_of_subset_of_nonneg chordBonds_subset_fineBonds
      fun _ _ _ => (Real.exp_pos _).le
  · refine le_trans (le_of_eq ?_) (hS (bondCell b) (finiteCells F))
    apply Finset.sum_congr rfl
    intro Y _
    rw [pl.symm Y (bondCell b)]
    rfl
  · refine le_trans ?_ (h8 (bondCell b))
    exact sum_sites_le_sum_fineBonds (fun y => Real.exp (-(8 * κ * cellDistReal (enclosingCell y) (bondCell b))))
      fun y => (Real.exp_pos _).le
  · refine le_trans ?_ (h16 z)
    exact sum_sites_le_sum_fineBonds (fun y => _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.expWeight cellDistReal (κ / 16) (enclosingCell y) z)
      fun y => (Real.exp_pos _).le
def TermBoundsAt (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ExponentsConvexAt T ∧ CellExponentsBoundedAt T ∧ CentredExpansionsBoundedAt T
theorem thirdDerivLocalForParameters_of_termBounds (hR : CutoffFactorIsRadialCutoff)
    (hComp : ThirdOrderChainRule) (hIn : ThirdOrderChainRuleVectorValued)
    (hG : CubicTorusCellGeometry) (hB : BlocksCoverLowerLevel)
    {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} (hT : TermBoundsAt T) {Λ : LiePair → imaginaryQuaternions} {r₀ CL : ℝ}
    (hL : ProductLog Λ r₀)
    (hCL0 : 0 ≤ CL) (hCL : ∀ (z : LiePair) (j : ℕ), j ≤ 5 → ‖iteratedFDeriv ℝ j Λ z‖ ≤ CL)
    {Cf CF σF C16 C8 S C₀ c₁ : ℝ} (hFr : FrameBounds T.a T.L T.chainParams Cf CF σF) (hodd : Odd T.L)
    (hn₀ : 64 ≤ T.n₀) (hσ0 : 0 < T.σ) (hσ : T.σ ≤ σF) (hroom : CF * T.σ + T.ballRadius < r₀)
    (hκ : 0 < T.κ)
    (hκle : T.κ ≤ T.chainParams.δ₂ / 2 ^ 14) (hCt : 0 ≤ T.Ct) (hE : 1 ≤ T.E) (hη0 : 0 < T.η₃)
    (hη1 : T.η₃ ≤ 1) (hp : IsCutoff T.ballRadius T.p) (hlam : 0 < T.chainParams.lam)
    (h16 : ∀ F : BlockFrame, Odd F.blockSide → IsLargeCubicTorus F → ∀ z : F.Cell,
      ∑ b ∈ fineBonds F, Real.exp (-(T.κ / 16 * cellSupDist (enclosingCell b.1) z)) ≤
        C16 * (F.blockSide : ℝ) ^ 4)
    (h8 : ∀ F : BlockFrame, Odd F.blockSide → IsLargeCubicTorus F → ∀ z : F.Cell,
      ∑ b ∈ fineBonds F, Real.exp (-(8 * T.κ * cellSupDist (enclosingCell b.1) z)) ≤
        C8 * (F.blockSide : ℝ) ^ 4)
    (hS : ∀ (F : BlockFrame) (y : F.Cell) (A : Finset F.Cell),
      ∑ z ∈ A, Real.exp (-(8 * T.κ * siteSupDist y z)) ≤ S)
    (hc₁0 : 0 ≤ c₁)
    (hc₁ : T.Ct * (S * (C16 * (T.L : ℝ) ^ 4)) + T.Ct * ((C8 * (T.L : ℝ) ^ 4) * (C16 * (T.L : ℝ) ^ 4)) ≤
      c₁ * (T.chainParams.lam / 4))
    (hC₀ : 0 ≤ C₀)
    (hBd : CovarianceThirdDerivBound T.ballRadius T.p c₁ (C16 * (T.L : ℝ) ^ 4)
      (1 + 5 * CL * (1 + CF) ^ 3) C₀)
    (hcs : C₀ * T.Ct ^ 2 * (2 / Real.sqrt T.chainParams.lam) * (C16 * (T.L : ℝ) ^ 4) ≤ T.Cs)
    (hy : ∀ x, T.coupling ≤ x → 1 ≤ x ∧ T.E ≤ x ∧ 4 ≤ x * T.chainParams.lam ∧ 16 ≤ frameRadius x ∧
      frameDecayBound Cf T.chainParams.δ₂ (frameRadius x) ≤ 2⁻¹ ^ 10 * T.σ ∧
      CF * x ^ 2 * frameDecayBound Cf T.chainParams.δ₂ (frameRadius x) ≤
        Real.exp (-(2 ^ 10 * T.κ * frameRadius x)) ∧
      CF * x ^ 2 * Real.exp (-(2 * T.chainParams.δ₂ * frameRadius x)) ≤ 1) :
    ThirdDerivLocalForParameters T := by
  intro t x f F V hx hrow htop hcold star ν y c X hν0 hν1 hX
  obtain ⟨hFL, hFt, n, hside, hn⟩ := htop
  have hoddF : Odd F.blockSide := by rw [hFL]; exact hodd
  have hcub : IsLargeCubicTorus F := ⟨n, by omega, hside⟩
  have pl : IsSiteDistance (cellDistReal (F := F)) := isSiteDistance_cellDistReal hG hoddF hcub
  have S' : DecaySumBounds F T.κ (C16 * (F.blockSide : ℝ) ^ 4) S (C8 * (F.blockSide : ℝ) ^ 4)
      (C16 * (F.blockSide : ℝ) ^ 4) :=
    decaySumBounds_of_geometry hκ hoddF hcub pl (h16 F hoddF hcub) (h8 F hoddF hcub) (hS F)
  rw [hFL] at S'
  obtain ⟨hx1, hEx, hx4, hm16, hg1, hg2, hg3⟩ := hy x hx
  have htop' : IsCubicTopTorus T.L t T.n₀ F := ⟨hFL, hFt, n, hside, hn⟩
  obtain ⟨hCf0, hCF1, hσF0, hFall⟩ := hFr
  have hFH := hFall T.κ T.σ x (frameRadius x) t T.n₀ hκ hκle hσ0 hσ hx1 hm16 hn₀ hg1 hg2 hg3 F V
    htop' hcold
  have hsmall := hFH.2.1 star
  have hρ : 0 < T.ballRadius := by
    simp only [StepParameters.ballRadius]
    positivity
  have hE₃ : T.E ≤ T.energyRatio := by
    simp only [StepParameters.energyRatio]
    rw [le_div_iff₀ hη0]
    have : 0 ≤ T.E := by linarith
    nlinarith
  have hx0 : 0 < x := by linarith
  have hlam4 : 0 < T.chainParams.lam / 4 := by positivity
  have hnpos : 0 < n := by omega
  have D : TopLevelData F star T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x T.κ T.decayRate T.E
      T.energyRatio T.Ct CF T.L
      (frameRadius x) T.p f ν V Λ r₀ T.chainParams.δ₂ T.chainParams.κ₂ T.σ T.chainParams.Kk
      (C16 * (T.L : ℝ) ^ 4) S
      (C8 * (T.L : ℝ) ^ 4) (C16 * (T.L : ℝ) ^ 4) c₁ := by
    refine ⟨hρ, hp, hκ, pl, S', hCt, by linarith, by linarith, hE₃, hx0.le, hEx, ?_, hc₁0, ?_,
      hT.1 t x f F V star ν hx hrow htop' hcold hν0 hν1, (hT.2.1 t x F V star hx htop' hcold).1,
      hT.2.2 t x f F V star hx hrow htop' hcold, hν0, hν1, hL, hsmall, ?_, ?_, ?_⟩
    · linarith
    · have := mul_le_mul_of_nonneg_left hc₁ hx0.le
      calc _ = x * (T.Ct * (S * (C16 * (T.L : ℝ) ^ 4)) +
              T.Ct * ((C8 * (T.L : ℝ) ^ 4) * (C16 * (T.L : ℝ) ^ 4))) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    · have h2 : (2 : ℝ) ^ 14 * T.κ ≤ T.chainParams.δ₂ := by
        have := mul_le_mul_of_nonneg_left hκle (by positivity : (0 : ℝ) ≤ 2 ^ 14)
        have e : (2 : ℝ) ^ 14 * (T.chainParams.δ₂ / 2 ^ 14) = T.chainParams.δ₂ := by
          field_simp
        linarith
      nlinarith
    · intro b
      have h1 := hsmall.norm_le b.1 b.2
      have e : ‖frameCoord V star T.a T.chainParams.ρA (frameRadius x) b‖ =
          ‖stepFrame star T.a T.chainParams.ρA (frameRadius x) b.1 V‖ := rfl
      rw [e]
      linarith
    · exact hB F hoddF fun i => by
        rw [hside i]
        exact hnpos
  have hsum := sum_abs_cutoffCovariance_le (ρ := T.ballRadius) (p := T.p) hR hComp hIn D hCL0 hCL hC₀ hBd
    y c X hX
  refine hsum.trans ?_
  set Wy := C16 * (T.L : ℝ) ^ 4 with hWy
  set ex := Real.exp (-(T.κ / 2 ^ 5 * bondSpan (enclosingCell y) c)) with hex
  set xr := x ^ (-(1 / 2 : ℝ)) with hxr
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsl : 0 < Real.sqrt T.chainParams.lam := Real.sqrt_pos.mpr hlam
  have e1 : xr = (Real.sqrt x)⁻¹ := by
    rw [hxr, Real.sqrt_eq_rpow, Real.rpow_neg hx0.le]
  have e2 : Real.sqrt (x * T.chainParams.lam / 4) = Real.sqrt x * Real.sqrt T.chainParams.lam / 2 := by
    rw [Real.sqrt_div' _ (by norm_num), Real.sqrt_mul hx0.le]
    have : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [this]
  have e3 : (T.Ct * T.E) * (T.Ct * T.energyRatio) / Real.sqrt (x * T.chainParams.lam / 4) =
      T.Ct ^ 2 * (2 / Real.sqrt T.chainParams.lam) * (T.E * T.energyRatio * xr) := by
    rw [e2, e1]
    field_simp
  rw [e3]
  have hxr0 : 0 ≤ xr := by
    rw [e1]
    positivity
  have hE₃0 : 0 ≤ T.energyRatio := by linarith
  have hE0 : 0 ≤ T.E := by linarith
  have nn : 0 ≤ T.E * T.energyRatio * xr * ex := by
    have : 0 ≤ ex := (Real.exp_pos _).le
    positivity
  have := mul_le_mul_of_nonneg_right hcs nn
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · ring
  · ring
end Table
end ThirdDerivLocal
open ThirdDerivLocal in
theorem thirdDerivLocalEventually_holds (hCore : CovarianceThirdDerivBounded)
    (hR : CutoffFactorIsRadialCutoff) (hComp : ThirdOrderChainRule) (hIn : ThirdOrderChainRuleVectorValued)
    (hG : CubicTorusCellGeometry) (hB : BlocksCoverLowerLevel)
    (hSum : _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpDecaySumBounded) (hW : frameBoundsStatement)
    (hFl : CouplingThreshold) (hJ : EventuallyInParametersCombines)
    (hConv : exponentConvexityStatement) (hExp : CellExponentsBounded)
    (hRow : CentredExpansionsBounded) : ThirdDerivLocalEventually := by
  have hP : EventuallyInParameters TermBoundsAt := hJ.1 _ _ hConv (hJ.1 _ _ hExp hRow)
  obtain ⟨Λ, r₀, CL, hr₀, hCL0, hΛ, hprod, hfirst, hCL⟩ := exists_smooth_log_of_product
  have hLog : ProductLog Λ r₀ := ⟨hr₀, hΛ, hprod, hfirst⟩
  intro a ha
  obtain ⟨L₀, hL₀⟩ := hP a ha
  refine ⟨max L₀ (2 ^ 40), fun L hodd hL c hc => ?_⟩
  obtain ⟨Ct₀, hCt₀⟩ := hL₀ L hodd (le_of_max_le_left hL) c hc
  obtain ⟨Cf, CF, σF, hFr⟩ := hW a L c ha hodd (le_of_max_le_right hL) hc
  have hCF1 : 1 ≤ CF := hFr.2.1
  have hσF0 : 0 < σF := hFr.2.2.1
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  have hlam : 0 < c.lam := hc.positivity.2.2.1
  refine ⟨max Ct₀ 0, fun Ct hCt => ?_⟩
  obtain ⟨κ₁, hκ₁, hκ₂⟩ := hCt₀ Ct (le_of_max_le_left hCt)
  have hCt0 : 0 ≤ Ct := le_of_max_le_right hCt
  refine ⟨min κ₁ (c.δ₂ / 2 ^ 14), lt_min hκ₁ (by positivity), fun κ hκ hκle => ?_⟩
  obtain ⟨η₀, hη₀, h1⟩ := hκ₂ κ hκ (hκle.trans (min_le_left _ _))
  refine ⟨η₀, hη₀, fun η₃ hη hη1 hηle => ?_⟩
  obtain ⟨N₀, h2⟩ := h1 η₃ hη hη1 hηle
  refine ⟨N₀, fun nss hn => ?_⟩
  obtain ⟨σ₁, hσ₁, h3⟩ := h2 nss hn
  have hσc : 0 < r₀ / (2 * (CF + 1)) := by positivity
  refine ⟨min σ₁ (min σF (r₀ / (2 * (CF + 1)))), lt_min hσ₁ (lt_min hσF0 hσc), fun σ hσ hσle => ?_⟩
  have h4 := h3 σ hσ (hσle.trans (min_le_left _ _))
  have hσ2 : σ ≤ σF := (hσle.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hσ3 : σ ≤ r₀ / (2 * (CF + 1)) := (hσle.trans (min_le_right _ _)).trans (min_le_right _ _)
  intro p hp
  obtain ⟨C₁, h5⟩ := h4 p hp
  have hρ : 0 < σ / 64 := by positivity
  have hκ16 : 0 < κ / 16 := by positivity
  have hκ8 : 0 < 8 * κ := by positivity
  obtain ⟨C16, hC16, h16⟩ := hG.2 (κ / 16) hκ16
  obtain ⟨C8, hC8, h8⟩ := hG.2 (8 * κ) hκ8
  obtain ⟨S, hS0, hS⟩ := hSum (8 * κ) hκ8
  have hlam4 : 0 < c.lam / 4 := by positivity
  set W : ℝ := C16 * (L : ℝ) ^ 4 with hWdef
  have hW0 : 0 ≤ W := by positivity
  set W₃ : ℝ := C8 * (L : ℝ) ^ 4 with hW₃
  have hW₃0 : 0 ≤ W₃ := by positivity
  set c₁ : ℝ := (Ct * (S * W) + Ct * (W₃ * W)) / (c.lam / 4) with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hDz : 1 ≤ 1 + 5 * CL * (1 + CF) ^ 3 := by
    have : 0 ≤ CF := by linarith
    have : 0 ≤ 5 * CL * (1 + CF) ^ 3 := by positivity
    linarith
  obtain ⟨C₀, hC₀, hBd⟩ := hCore (σ / 64) p c₁ W _ hρ hp hc₁0 hW0 hDz
  refine ⟨max C₁ (C₀ * Ct ^ 2 * (2 / Real.sqrt c.lam) * W), fun Cs hCs => ?_⟩
  have h6 := h5 Cs (le_of_max_le_left hCs)
  intro E hE
  obtain ⟨m₀, h7⟩ := h6 E hE
  refine ⟨max m₀ 64, fun n₀ hn₀ => ?_⟩
  obtain ⟨C₂, h8'⟩ := h7 n₀ (le_of_max_le_left hn₀)
  refine ⟨C₂, fun CE hCE => ?_⟩
  obtain ⟨y₀, h9⟩ := h8' CE hCE
  have hκδ : κ ≤ c.δ₂ / 2 ^ 14 := hκle.trans (min_le_right _ _)
  obtain ⟨y₂, hy₂⟩ := hFl Cf CF c.δ₂ κ σ 16 hδ₂ hκ hκδ hσ
  refine ⟨max y₀ (max y₂ (max 1 (max E (4 / c.lam)))), fun y₁ hy => ?_⟩
  have hT := h9 y₁ (le_of_max_le_left hy)
  have hyr := le_of_max_le_right hy
  have hy2 : y₂ ≤ y₁ := le_of_max_le_left hyr
  have hy3 := le_of_max_le_right hyr
  have hy4 : 1 ≤ y₁ := le_of_max_le_left hy3
  have hy5 := le_of_max_le_right hy3
  have hy6 : E ≤ y₁ := le_of_max_le_left hy5
  have hy7 : 4 / c.lam ≤ y₁ := le_of_max_le_right hy5
  have hroom : CF * σ + σ / 64 < r₀ := by
    rw [le_div_iff₀ (by positivity)] at hσ3
    nlinarith
  refine thirdDerivLocalForParameters_of_termBounds hR hComp hIn hG hB hT hLog hCL0 hCL (Cf := Cf)
    (CF := CF) (σF := σF)
    (C16 := C16) (C8 := C8) (S := S) (c₁ := c₁) hFr hodd
    (le_of_max_le_right hn₀) hσ hσ2 hroom hκ hκδ hCt0 hE hη hη1 hp hlam
    (fun F hF hc z => h16 F hF hc z) (fun F hF hc z => h8 F hF hc z)
    (fun F y A => hS F F.top y A) hc₁0 ?_ hC₀ hBd (le_of_max_le_right hCs) ?_
  · show Ct * (S * W) + Ct * (W₃ * W) ≤ c₁ * (c.lam / 4)
    rw [hc₁]
    field_simp
    exact le_rfl
  · intro x hx
    have hx' : y₁ ≤ x := hx
    obtain ⟨-, a2, a3, a4, a5, -⟩ := hy₂ x (hy2.trans hx')
    have hl4 : 4 ≤ x * c.lam := by
      have := hy7.trans hx'
      rw [div_le_iff₀ hlam] at this
      exact this
    exact ⟨hy4.trans hx', hy6.trans hx', hl4, a2, a3, a4, a5⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
