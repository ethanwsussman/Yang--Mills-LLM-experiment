import YangMills.Construction.RunningCouplingSlope.EnergyAtTheLeastFieldHasKernelsProof
import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.MotionAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation
namespace Estimates
section
variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂]
theorem exists_open_nhds_contDiffOn {f : E₁ → E₂} {x : E₁} {n : ℕ} (hf : ContDiffAt ℝ n f x) :
    ∃ U : Set E₁, IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ n f U := by apply _root_.YangMills.Construction.GaugeAlongMotion.exists_isOpen_contDiffOn_of_contDiffAt <;> assumption
theorem iteratedFDeriv_comp_clm_apply {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    (Λ : E₁ →L[ℝ] E₂) {f : E₂ → E₃} {x : E₁} {n : ℕ} (hf : ContDiffAt ℝ n f (Λ x)) (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (f ∘ Λ) x v = iteratedFDeriv ℝ n f (Λ x) fun l => Λ (v l) := by
  obtain ⟨U, hU, hxU, hfU⟩ := exists_open_nhds_contDiffOn hf
  have hΛ : IsOpen (Λ ⁻¹' U) := hU.preimage Λ.continuous
  have h := Λ.iteratedFDerivWithin_comp_right hfU hU.uniqueDiffOn hΛ.uniqueDiffOn
    (x := x) hxU (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hΛ (show x ∈ Λ ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen n hU hxU] at h
  rw [h]
  rfl
theorem norm_iteratedFDeriv_comp_single_le {p n : ℕ} {g : E₁ → E₂} {β : (Fin p → ℝ) → E₁}
    {x : Fin p → ℝ}
    (hg : ContDiffAt ℝ n g (β x)) (hβ : ContDiffAt ℝ n β x) (ω : Fin p → ℝ)
    (h0 : ∀ i, 0 ≤ ω i) (h1 : ∀ i, ω i ≤ 1) (A : ℕ → ℝ) (hA : ∀ r, 0 ≤ A r)
    (hpart : ∀ (r : ℕ) (J : Fin r → Fin p) (l : Fin r), r ≤ n →
      ‖iteratedFDeriv ℝ r β x fun q => Pi.single (J q) 1‖ ≤ A r * ω (J l))
    {r : ℕ} (J : Fin r → Fin p) (l : Fin r) (hr : r ≤ n) :
    ‖iteratedFDeriv ℝ r (g ∘ β) x fun q => Pi.single (J q) 1‖ ≤
      (∑ c : OrderedFinpartition r, ‖iteratedFDeriv ℝ c.length g (β x)‖ * ∏ m, A (c.partSize m)) *
        ω (J l) := by apply _root_.YangMills.Construction.GaugeAlongMotion.norm_iteratedFDeriv_comp_single_le <;> assumption
end
section
def imPartL : ℍ[ℝ] →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => ⟨q - ((q.re : ℝ) : ℍ[ℝ]), by
        show (q - ((q.re : ℝ) : ℍ[ℝ])).re = 0
        simp⟩
      map_add' := fun q q' => by
        apply Subtype.ext
        simp only [Submodule.coe_add, Quaternion.re_add, Quaternion.coe_add]
        abel
      map_smul' := fun u q => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        apply Quaternion.ext <;> simp }
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem contDiff_quaternionExp (n : ℕ) : ContDiff ℝ n (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
theorem exists_local_logarithm (n : ℕ) : ∃ (Lg : ℍ[ℝ] → imaginaryQuaternions) (U : Set ℍ[ℝ]),
    U ∈ 𝓝 (1 : ℍ[ℝ]) ∧ ContDiffAt ℝ n Lg 1 ∧ Lg 1 = 0 ∧
    ∀ g ∈ U, ‖g‖ = 1 → NormedSpace.exp ((Lg g : imaginaryQuaternions) : ℍ[ℝ]) = g := by apply _root_.YangMills.Construction.GaugeAlongMotion.exists_local_logarithm <;> assumption
theorem hasFDerivAt_exp_coe_comp_zero {p : ℕ} {h : (Fin p → ℝ) → imaginaryQuaternions}
    {h' : (Fin p → ℝ) →L[ℝ] imaginaryQuaternions}
    (hd : HasFDerivAt h h' 0) (h0 : h 0 = 0) :
    HasFDerivAt (fun τ => NormedSpace.exp ((h τ : imaginaryQuaternions) : ℍ[ℝ]))
      (imaginaryQuaternions.subtypeL.comp h') 0 := by apply _root_.YangMills.Construction.GaugeAlongMotion.hasFDerivAt_exp_comp_of_eq_zero <;> assumption
theorem exists_lipschitz_bound_closedBall {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G} (hf : ContDiff ℝ 1 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : E, ‖v‖ ≤ 1 → ‖f v - f 0‖ ≤ C * ‖v‖ := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hc : Continuous (fun v : E => ‖fderiv ℝ f v‖) := (hf.continuous_fderiv (by norm_num)).norm
  have hcomp : IsCompact (Metric.closedBall (0 : E) 1) := isCompact_closedBall 0 1
  obtain ⟨C₁, hC₁⟩ := hcomp.bddAbove_image hc.continuousOn
  have hconv : Convex ℝ (Metric.closedBall (0 : E) 1) := convex_closedBall 0 1
  have h0m : (0 : E) ∈ Metric.closedBall (0 : E) 1 := by simp
  refine ⟨max C₁ 0, le_max_right _ _, fun v hv => ?_⟩
  have hvm : v ∈ Metric.closedBall (0 : E) 1 := by simpa using hv
  have e1 := hconv.norm_image_sub_le_of_norm_fderiv_le (f := f) (C := max C₁ 0) (fun x _ => hd x)
    (fun x hx => (hC₁ ⟨x, hx, rfl⟩).trans (le_max_left _ _)) h0m hvm
  simpa using e1
theorem exists_exp_lipschitz_near_zero : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℍ[ℝ], ‖v‖ ≤ 1 →
    ‖NormedSpace.exp v - 1‖ ≤ C * ‖v‖ ∧
      ‖fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) v - 1‖ ≤ C * ‖v‖ := by
  have h2 : ContDiff ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) := contDiff_quaternionExp 2
  have hf : ContDiff ℝ 1 (fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ])) :=
    h2.fderiv_right (m := 1) (by norm_num)
  obtain ⟨C₁, hC₁, h₁⟩ := exists_lipschitz_bound_closedBall (contDiff_quaternionExp 1)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_lipschitz_bound_closedBall hf
  have hz : fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) 0 = 1 :=
    (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ℍ[ℝ])).fderiv
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun v hv => ⟨?_, ?_⟩⟩
  · have := h₁ v hv
    rw [NormedSpace.exp_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · have := h₂ v hv
    rw [hz] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
theorem norm_fderiv_sub_add_le_of_exp_eq_mul {C : ℝ} (hC : 0 ≤ C) (hexpL : ∀ v : ℍ[ℝ], ‖v‖ ≤ 1 →
      ‖NormedSpace.exp v - 1‖ ≤ C * ‖v‖ ∧
        ‖fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) v - 1‖ ≤ C * ‖v‖)
    {p : ℕ} {h b₁ b₂ : (Fin p → ℝ) → imaginaryQuaternions} {v : imaginaryQuaternions} (hv : ‖v‖ ≤ 1)
    (hh : DifferentiableAt ℝ h 0) (h₁ : DifferentiableAt ℝ b₁ 0) (h₂ : DifferentiableAt ℝ b₂ 0)
    (hh0 : h 0 = 0) (hb₁ : b₁ 0 = v) (hb₂ : b₂ 0 = 0)
    (hev : ∀ᶠ τ in 𝓝 (0 : Fin p → ℝ), NormedSpace.exp ((h τ : imaginaryQuaternions) : ℍ[ℝ]) =
      NormedSpace.exp ((b₁ τ : imaginaryQuaternions) : ℍ[ℝ]) *
        NormedSpace.exp ((b₂ τ : imaginaryQuaternions) : ℍ[ℝ]) *
        (((expUnit v)⁻¹ : UnitQuaternion) : ℍ[ℝ])) (u₀ : Fin p → ℝ) :
    ‖fderiv ℝ h 0 u₀ - (fderiv ℝ b₁ 0 u₀ + fderiv ℝ b₂ 0 u₀)‖ ≤
      3 * C * ‖v‖ * (‖fderiv ℝ b₁ 0 u₀‖ + ‖fderiv ℝ b₂ 0 u₀‖) := by
  set E : ℍ[ℝ] := (((expUnit v)⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hE
  set e : ℍ[ℝ] := NormedSpace.exp ((v : imaginaryQuaternions) : ℍ[ℝ]) with he
  have heE : e * E = 1 := by
    show ((expUnit v * (expUnit v)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1
    rw [mul_inv_cancel]
    rfl
  have hEn : ‖E‖ = 1 := norm_coe_unitQuaternion _
  have D0 := hasFDerivAt_exp_coe_comp_zero hh.hasFDerivAt hh0
  have H1 : HasFDerivAt (fun τ => ((b₁ τ : imaginaryQuaternions) : ℍ[ℝ]))
      (imaginaryQuaternions.subtypeL.comp (fderiv ℝ b₁ 0)) 0 :=
    imaginaryQuaternions.subtypeL.hasFDerivAt.comp 0 h₁.hasFDerivAt
  have X1 : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ])
      (fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) ((b₁ 0 : imaginaryQuaternions) : ℍ[ℝ]))
      ((b₁ 0 : imaginaryQuaternions) : ℍ[ℝ]) :=
    ((contDiff_quaternionExp 1).differentiable (by norm_num) _).hasFDerivAt
  have D1 := X1.comp (0 : Fin p → ℝ) H1
  have D2 := hasFDerivAt_exp_coe_comp_zero h₂.hasFDerivAt hb₂
  have P := (D1.mul' D2).mul_const' E
  have Q : HasFDerivAt (fun τ => NormedSpace.exp ((b₁ τ : imaginaryQuaternions) : ℍ[ℝ]) *
      NormedSpace.exp ((b₂ τ : imaginaryQuaternions) : ℍ[ℝ]) * E)
      (imaginaryQuaternions.subtypeL.comp (fderiv ℝ h 0)) 0 :=
    D0.congr_of_eventuallyEq (hev.mono fun τ hτ => hτ.symm)
  have R := Q.unique P
  have R' := congrArg (fun Lm : (Fin p → ℝ) →L[ℝ] ℍ[ℝ] => Lm u₀) R
  simp only [hb₁, hb₂, ZeroMemClass.coe_zero, NormedSpace.exp_zero] at R'
  have hb₁e : (NormedSpace.exp ∘ fun τ => ((b₁ τ : imaginaryQuaternions) : ℍ[ℝ])) 0 = e := by
    simp only [Function.comp, hb₁, he]
  rw [hb₁e] at R'
  set t : ℍ[ℝ] := ((fderiv ℝ b₂ 0 u₀ : imaginaryQuaternions) : ℍ[ℝ]) with ht
  set u : ℍ[ℝ] := ((fderiv ℝ b₁ 0 u₀ : imaginaryQuaternions) : ℍ[ℝ]) with hu
  set Dv : ℍ[ℝ] := fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) ((v : imaginaryQuaternions) : ℍ[ℝ]) u
    with hDv
  have R2 : ((fderiv ℝ h 0 u₀ : imaginaryQuaternions) : ℍ[ℝ]) = (e * t + Dv * 1) * E := R'
  obtain ⟨hL1, hL2⟩ := hexpL ((v : imaginaryQuaternions) : ℍ[ℝ]) hv
  have hDu : ‖Dv - u‖ ≤ C * ‖(v : ℍ[ℝ])‖ * ‖u‖ := by
    have h1 : Dv - u = (fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ])
        ((v : imaginaryQuaternions) : ℍ[ℝ]) - 1) u := by
      simp [hDv]
    rw [h1]
    exact ((fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) ((v : imaginaryQuaternions) : ℍ[ℝ]) -
      1).le_opNorm u).trans (mul_le_mul_of_nonneg_right hL2 (norm_nonneg _))
  have h1 : t * e * E = t := by rw [mul_assoc, heE, mul_one]
  have h2 : u * e * E = u := by rw [mul_assoc, heE, mul_one]
  have heq : (e * t + Dv * 1) * E - (u + t) =
      ((e - 1) * t - t * (e - 1)) * E + (Dv - u) * E - u * (e - 1) * E := by
    have e1 : ((e - 1) * t - t * (e - 1)) * E + (Dv - u) * E - u * (e - 1) * E =
        e * t * E - t * e * E + (Dv * E - u * E) - (u * e * E - u * E) := by noncomm_ring
    rw [e1, h1, h2]
    noncomm_ring
  have hnorm : ‖fderiv ℝ h 0 u₀ - (fderiv ℝ b₁ 0 u₀ + fderiv ℝ b₂ 0 u₀)‖ =
      ‖(e * t + Dv * 1) * E - (u + t)‖ := by
    rw [← R2]
    rfl
  rw [hnorm, heq]
  have hnv : ‖(v : ℍ[ℝ])‖ = ‖v‖ := rfl
  have ht' : ‖fderiv ℝ b₂ 0 u₀‖ = ‖t‖ := rfl
  have hu' : ‖fderiv ℝ b₁ 0 u₀‖ = ‖u‖ := rfl
  rw [ht', hu', ← hnv]
  set ν := ‖(v : ℍ[ℝ])‖ with hν
  have hν0 : 0 ≤ ν := norm_nonneg _
  have b1 : ‖((e - 1) * t - t * (e - 1)) * E‖ ≤ 2 * (C * ν) * ‖t‖ := by
    rw [norm_mul, hEn, mul_one]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    nlinarith [mul_le_mul_of_nonneg_right hL1 (norm_nonneg t)]
  have b2 : ‖(Dv - u) * E‖ ≤ C * ν * ‖u‖ := by
    rw [norm_mul, hEn, mul_one]
    exact hDu
  have b3 : ‖u * (e - 1) * E‖ ≤ C * ν * ‖u‖ := by
    rw [norm_mul, norm_mul, hEn, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left hL1 (norm_nonneg u)]
  have hs := norm_sub_le (((e - 1) * t - t * (e - 1)) * E + (Dv - u) * E) (u * (e - 1) * E)
  have ha := norm_add_le (((e - 1) * t - t * (e - 1)) * E) ((Dv - u) * E)
  have hCν : 0 ≤ C * ν := mul_nonneg hC hν0
  nlinarith [mul_nonneg hCν (norm_nonneg t), mul_nonneg hCν (norm_nonneg u)]
end
section
variable {F : BlockFrame}
theorem expUnit_zero_eq_one : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem leftTranslate_zero_eq {j : ℕ} (W : F.GaugeField j) : leftTranslate (fun _ _ => 0) W = W := by apply _root_.YangMills.SharedProofs.p21302 <;> assumption
theorem bondSpread_at_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondSpread c X 0 = fun _ _ => 0 := by apply _root_.YangMills.SharedProofs.p27189 <;> assumption
def coordEmbedding {j r : ℕ} (q : Fin r → Fin j) : (Fin r → ℝ) →L[ℝ] (Fin j → ℝ) :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin r → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (q l) 1)
theorem coordEmbedding_apply {j r : ℕ} (q : Fin r → Fin j) (τ : Fin r → ℝ) :
    coordEmbedding q τ = ∑ l, τ l • (Pi.single (q l) 1 : Fin j → ℝ) := by
  simp [coordEmbedding]
theorem coordEmbedding_single {j r : ℕ} (q : Fin r → Fin j) (l : Fin r) :
    coordEmbedding q (Pi.single l 1) = Pi.single (q l) 1 := by
  rw [coordEmbedding_apply]
  simp [Pi.single_apply]
theorem bondSpread_comp_coordEmbedding {i j r : ℕ} (c : Fin j → F.Site i × Fin 4)
    (X : Fin j → imaginaryQuaternions) (q : Fin r → Fin j) (τ : Fin r → ℝ) :
    bondSpread (c ∘ q) (X ∘ q) τ = bondSpread c X (coordEmbedding q τ) := by
  funext y d
  simp only [bondSpread, coordEmbedding_apply, Finset.sum_apply, Pi.smul_apply, Function.comp]
  have h : ∀ p : Fin j, (if c p = (y, d) then
      (∑ l, τ l • (Pi.single (q l) (1 : ℝ) : Fin j → ℝ) p) • X p else 0) =
        ∑ l, if q l = p then (if c (q l) = (y, d) then τ l • X (q l) else 0) else 0 := by
    intro p
    split_ifs with hc
    · rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hq : q l = p
      · subst hq
        simp [hc]
      · have hq' : p ≠ q l := fun e => hq e.symm
        simp [hq, hq']
    · refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hq : q l = p
      · subst hq
        simp [hc]
      · simp [hq]
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp
theorem iteratedFDeriv_const_add_clm_of_two_le {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (L : E₁ →L[ℝ] E₂) (v₀ : E₂)
    {r : ℕ} (hr : 2 ≤ r) (x : E₁) : iteratedFDeriv ℝ r (fun τ => v₀ + L τ) x = 0 := by apply _root_.YangMills.Construction.GaugeAlongMotion.iteratedFDeriv_const_add_clm_of_two_le <;> assumption
theorem iteratedFDeriv_const_add_clm_one {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (L : E₁ →L[ℝ] E₂) (v₀ : E₂)
    (x : E₁) (v : Fin 1 → E₁) : iteratedFDeriv ℝ 1 (fun τ => v₀ + L τ) x v = L (v 0) := by
  rw [iteratedFDeriv_one_apply, ((L.hasFDerivAt).const_add v₀).fderiv]
end
section
variable {F : BlockFrame}
theorem toImaginary_add_eq (v v' : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (v + v') = toImaginary v + toImaginary v' := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
theorem toImaginary_zero_eq : toImaginary (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
theorem norm_toImaginary_eq (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem stepCoordinates_add_apply {S : Finset F.Cell} (w w' : StepVariable S) (x : F.Site F.depth)
    (i : Fin 4) : stepCoordinates (w + w') x i = stepCoordinates w x i + stepCoordinates w' x i := by
  simp only [stepCoordinates]
  split_ifs with h
  · simp [toImaginary_add_eq]
  · simp
theorem stepCoordinates_smul_apply {S : Finset F.Cell} (u : ℝ) (w : StepVariable S)
    (x : F.Site F.depth) (i : Fin 4) : stepCoordinates (u • w) x i = u • stepCoordinates w x i := by apply _root_.YangMills.SharedProofs.p61127 <;> assumption
theorem stepCoordinates_zero_apply {S : Finset F.Cell} (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable S) x i = 0 := by apply _root_.YangMills.SharedProofs.p7539 <;> assumption
theorem stepCoordinates_sum_apply {S : Finset F.Cell} {ι : Type*} (T : Finset ι)
    (f : ι → StepVariable S) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (∑ l ∈ T, f l) x i = ∑ l ∈ T, stepCoordinates (f l) x i := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using stepCoordinates_zero_apply x i
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, stepCoordinates_add_apply, ih]
theorem norm_stepCoordinates_variableDirection_le (w : Perturbation F) (hw : w.IsUnit) (r : ℝ)
    (x : F.Site F.depth) (i : Fin 4) :
    ‖stepCoordinates w.variableDirection x i‖ ≤ w.decayWeight r x i ∨ w.variableDirection = 0 := by
  classical
  cases w with
  | top c X => right; rfl
  | bulk b u =>
    left
    have hu : ‖u‖ = 1 := hw
    simp only [Perturbation.variableDirection, Perturbation.decayWeight, stepCoordinates]
    split_ifs with h1 h2 h2
    · have hb : (⟨(x, i), h1⟩ : ↥(chordBonds (finiteCells F))) = b := Subtype.ext h2.symm
      rw [hb]
      simp only [Pi.single_eq_same]
      have h3 := norm_toImaginary_eq u
      rw [hu] at h3
      exact h3.le
    · have hb : (⟨(x, i), h1⟩ : ↥(chordBonds (finiteCells F))) ≠ b := fun e => h2 (by rw [← e])
      rw [Pi.single_eq_of_ne hb, toImaginary_zero_eq]
      simp
    · simp
    · simp
def expProd (z : imaginaryQuaternions × imaginaryQuaternions) : ℍ[ℝ] :=
  NormedSpace.exp (z.1 : ℍ[ℝ]) * NormedSpace.exp (z.2 : ℍ[ℝ])
theorem contDiff_expProd (n : ℕ) : ContDiff ℝ n expProd := by
  have h1 : ContDiff ℝ n (fun z : imaginaryQuaternions × imaginaryQuaternions => (z.1 : ℍ[ℝ])) :=
    (imaginaryQuaternions.subtypeL.contDiff).comp contDiff_fst
  have h2 : ContDiff ℝ n (fun z : imaginaryQuaternions × imaginaryQuaternions => (z.2 : ℍ[ℝ])) :=
    (imaginaryQuaternions.subtypeL.contDiff).comp contDiff_snd
  exact ((contDiff_quaternionExp n).comp h1).mul ((contDiff_quaternionExp n).comp h2)
theorem exists_norm_iteratedFDeriv_le_on_compact {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G} (i : ℕ)
    (hf : ContDiff ℝ i f) {T : Set E} (hT : IsCompact T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ T, ‖iteratedFDeriv ℝ i f x‖ ≤ B := by
  have h0 := hf.continuous_iteratedFDeriv (m := i) le_rfl
  obtain ⟨C, hC⟩ := hT.bddAbove_image h0.norm.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
theorem exists_norm_iteratedFDeriv_expProd_le (i : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ v : imaginaryQuaternions, ‖v‖ ≤ 1 → ‖iteratedFDeriv ℝ i expProd (v, 0)‖ ≤ B := by
  have hT : IsCompact ((fun v : imaginaryQuaternions => (v, (0 : imaginaryQuaternions))) ''
      Metric.closedBall 0 1) :=
    (isCompact_closedBall (0 : imaginaryQuaternions) 1).image
      (continuous_id.prodMk continuous_const)
  obtain ⟨B, hB, h⟩ := exists_norm_iteratedFDeriv_le_on_compact i (contDiff_expProd i) hT
  exact ⟨B, hB, fun v hv => h _ ⟨v, by simpa using hv, rfl⟩⟩
end
section
variable {F : BlockFrame} {p : ℕ}
theorem Perturbation.decayWeight_nonneg (w : Perturbation F) (r : ℝ) (x : F.Site F.depth)
    (i : Fin 4) : 0 ≤ w.decayWeight r x i := by
  cases w with
  | bulk b u =>
    simp only [Perturbation.decayWeight]
    split_ifs <;> norm_num
  | top c X => exact (Real.exp_pos _).le
theorem Perturbation.decayWeight_le_one (w : Perturbation F) {r : ℝ} (hr : 0 ≤ r)
    (x : F.Site F.depth) (i : Fin 4) : w.decayWeight r x i ≤ 1 := by
  cases w with
  | bulk b u =>
    simp only [Perturbation.decayWeight]
    split_ifs <;> norm_num
  | top c X =>
    simp only [Perturbation.decayWeight]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hr (Nat.cast_nonneg _)))
def Perturbation.topIndicator : Perturbation F → ℝ
  | .bulk _ _ => 0
  | .top _ _ => 1
def topCoordProj (w : Fin p → Perturbation F) : (Fin p → ℝ) →L[ℝ] (Fin p → ℝ) :=
  ContinuousLinearMap.pi fun l =>
    (w l).topIndicator • (ContinuousLinearMap.proj l : (Fin p → ℝ) →L[ℝ] ℝ)
theorem topCoordProj_apply (w : Fin p → Perturbation F) (τ : Fin p → ℝ) (l : Fin p) :
    topCoordProj w τ l = (w l).topIndicator * τ l := rfl
theorem perturbedTop_topCoordProj (V : F.GaugeField F.top) (w : Fin p → Perturbation F)
    (τ : Fin p → ℝ) : perturbedTop V w (topCoordProj w τ) = perturbedTop V w τ := by
  simp only [perturbedTop]
  congr 1
  funext y i
  simp only [bondSpread]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [topCoordProj_apply]
  cases h : w l with
  | bulk b u => simp [Perturbation.topDirection]
  | top c X => simp [Perturbation.topIndicator]
theorem perturbedTop_coordEmbedding (V : F.GaugeField F.top) (w : Fin p → Perturbation F)
    {r : ℕ} (J : Fin r → Fin p) (τ : Fin r → ℝ) :
    perturbedTop V w (coordEmbedding J τ) = leftTranslate
      (bondSpread ((fun l => (w l).topBond) ∘ J) ((fun l => (w l).topDirection) ∘ J) τ) V := by
  simp only [perturbedTop]
  rw [bondSpread_comp_coordEmbedding]
theorem iteratedFDeriv_interpolatedFrame_single_eq {s a ρA : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    {w : Fin p → Perturbation F} {d : F.Site F.depth × Fin 4} {q : ℕ} (J : Fin q → Fin p)
    (hc : ContDiffAt ℝ q (fun τ => interpolatedFrame s a ρA m d (perturbedTop V w τ)) 0) :
    iteratedFDeriv ℝ q (fun τ => interpolatedFrame s a ρA m d (perturbedTop V w τ)) 0
        (fun e => Pi.single (J e) 1) =
      bondDeriv (interpolatedFrame s a ρA m d) V ((fun l => (w l).topBond) ∘ J)
        ((fun l => (w l).topDirection) ∘ J) := by
  have h1 : (fun τ : Fin q → ℝ => interpolatedFrame s a ρA m d
      (leftTranslate (bondSpread ((fun l => (w l).topBond) ∘ J)
        ((fun l => (w l).topDirection) ∘ J) τ) V)) =
      (fun τ => interpolatedFrame s a ρA m d (perturbedTop V w τ)) ∘ coordEmbedding J := by
    funext τ
    simp only [Function.comp, perturbedTop_coordEmbedding]
  have hz : coordEmbedding J 0 = 0 := map_zero _
  have h2 := iteratedFDeriv_comp_clm_apply (coordEmbedding J) (x := 0) (n := q)
    (f := fun τ => interpolatedFrame s a ρA m d (perturbedTop V w τ)) (hz ▸ hc)
    (fun l => Pi.single l 1)
  simp only [bondDeriv]
  rw [h1, h2, hz]
  simp only [coordEmbedding_single]
theorem norm_iteratedFDeriv_interpolatedFrame_le {K : ℕ → ℝ} {s a ρA r : ℝ} {m : ℕ}
    {V : F.GaugeField F.top} {w : Fin p → Perturbation F}
    (hK : ∀ k, 0 ≤ K k) (hr : 0 ≤ r) (hunit : ∀ l, (w l).IsUnit)
    {x : F.Site F.depth} {i : Fin 4} (hA : IsBondAnalyticAt (interpolatedFrame s a ρA m (x, i)) V)
    (hdec : ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions),
      1 ≤ k → AreUnitVectors X' →
        ‖bondDeriv (interpolatedFrame s a ρA m (x, i)) V c' X'‖ ≤
          K k * Real.exp (-(r * bondListDistance (enclosingCell x) c')))
    {q : ℕ} (J : Fin q → Fin p) (l : Fin q) :
    ‖iteratedFDeriv ℝ q (fun τ => interpolatedFrame s a ρA m (x, i) (perturbedTop V w τ)) 0
        (fun e => Pi.single (J e) 1)‖ ≤ K q * (w (J l)).decayWeight r x i := by
  set h : (Fin p → ℝ) → imaginaryQuaternions :=
    fun τ => interpolatedFrame s a ρA m (x, i) (perturbedTop V w τ) with hh
  have hc : ContDiffAt ℝ q h 0 :=
    (hA p (fun l => (w l).topBond) (fun l => (w l).topDirection)).contDiffAt
  by_cases hall : ∀ e, (w (J e)).topIndicator = 1
  · have hu : AreUnitVectors ((fun l => (w l).topDirection) ∘ J) := by
      intro e
      have h1 := hunit (J e)
      have h2 := hall e
      simp only [Function.comp]
      cases h3 : w (J e) with
      | bulk b u => rw [h3] at h2; simp [Perturbation.topIndicator] at h2
      | top c X => rw [h3] at h1; exact h1
    have heq : iteratedFDeriv ℝ q h 0 (fun e => Pi.single (J e) 1) =
        bondDeriv (interpolatedFrame s a ρA m (x, i)) V ((fun l => (w l).topBond) ∘ J)
          ((fun l => (w l).topDirection) ∘ J) := by
      have h1 : (fun τ : Fin q → ℝ => interpolatedFrame s a ρA m (x, i)
          (leftTranslate (bondSpread ((fun l => (w l).topBond) ∘ J)
            ((fun l => (w l).topDirection) ∘ J) τ) V)) =
          h ∘ coordEmbedding J := by
        funext τ
        simp only [hh, Function.comp, perturbedTop_coordEmbedding]
      have hz : coordEmbedding J 0 = 0 := map_zero _
      have h2 := iteratedFDeriv_comp_clm_apply (coordEmbedding J) (x := 0) (n := q) (f := h)
        (hz ▸ hc) (fun l => Pi.single l 1)
      simp only [bondDeriv]
      rw [h1, h2, hz]
      simp only [coordEmbedding_single]
    rw [heq]
    have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 fun e => by subst e; exact l.elim0
    refine (hdec q _ _ hq hu).trans (mul_le_mul_of_nonneg_left ?_ (hK q))
    have hl := hall l
    cases h3 : w (J l) with
    | bulk b u => rw [h3] at hl; simp [Perturbation.topIndicator] at hl
    | top c X =>
      simp only [Perturbation.decayWeight]
      apply Real.exp_le_exp.2
      apply neg_le_neg
      apply mul_le_mul_of_nonneg_left _ hr
      have h4 : cellSupDist (enclosingCell x) c.1 ≤
          bondListDistance (enclosingCell x) ((fun l => (w l).topBond) ∘ J) := by
        have h5 : c = ((fun l => (w l).topBond) ∘ J) l := by
          simp [Function.comp, h3, Perturbation.topBond]
        rw [h5]
        exact Finset.le_sup
          (f := fun l' => cellSupDist (enclosingCell x) ((((fun l => (w l).topBond) ∘ J) l').1))
          (Finset.mem_univ l)
      exact_mod_cast h4
  · push Not at hall
    obtain ⟨e₀, he₀⟩ := hall
    have h1 : h = h ∘ topCoordProj w := by
      funext τ
      simp only [hh, Function.comp, perturbedTop_topCoordProj]
    have hz : topCoordProj w 0 = 0 := map_zero _
    have h2 := iteratedFDeriv_comp_clm_apply (topCoordProj w) (x := 0) (n := q) (f := h)
      (by rw [hz]; exact hc) (fun e => Pi.single (J e) 1)
    have h3 : topCoordProj w (Pi.single (J e₀) 1) = 0 := by
      funext l'
      rw [topCoordProj_apply]
      by_cases hl' : l' = J e₀
      · subst hl'
        have : (w (J e₀)).topIndicator = 0 := by
          cases h4 : w (J e₀) with
          | bulk b u => rfl
          | top c X => rw [h4] at he₀; simp [Perturbation.topIndicator] at he₀
        simp [this]
      · simp [hl']
    have h4 : iteratedFDeriv ℝ q h 0 (fun e => Pi.single (J e) 1) = 0 := by
      rw [h1, h2, hz]
      exact ContinuousMultilinearMap.map_coord_zero _ e₀ h3
    rw [h4, norm_zero]
    exact mul_nonneg (hK q) ((w (J l)).decayWeight_nonneg r x i)
def bulkLinearPart (w : Fin p → Perturbation F) (x : F.Site F.depth) (i : Fin 4) :
    (Fin p → ℝ) →L[ℝ] imaginaryQuaternions :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin p → ℝ) →L[ℝ] ℝ).smulRight
    (stepCoordinates (w l).variableDirection x i)
theorem bulkLinearPart_apply (w : Fin p → Perturbation F) (x : F.Site F.depth) (i : Fin 4)
    (τ : Fin p → ℝ) :
    bulkLinearPart w x i τ = ∑ l, τ l • stepCoordinates (w l).variableDirection x i := by
  simp [bulkLinearPart]
theorem bulkLinearPart_single (w : Fin p → Perturbation F) (x : F.Site F.depth) (i : Fin 4)
    (l : Fin p) :
    bulkLinearPart w x i (Pi.single l 1) = stepCoordinates (w l).variableDirection x i := by
  rw [bulkLinearPart_apply]
  simp [Pi.single_apply]
theorem stepCoordinates_perturbedVariable (η : StepVariable (finiteCells F))
    (w : Fin p → Perturbation F) (τ : Fin p → ℝ) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (perturbedVariable η w τ) x i =
      stepCoordinates η x i + bulkLinearPart w x i τ := by
  rw [perturbedVariable, stepCoordinates_add_apply, stepCoordinates_sum_apply,
    bulkLinearPart_apply]
  congr 1
  exact Finset.sum_congr rfl fun l _ => stepCoordinates_smul_apply _ _ _ _
open Classical in
def crossingLinearPart (w : Fin p → Perturbation F) (x : F.Site F.depth) (i : Fin 4) :
    (Fin p → ℝ) →L[ℝ] imaginaryQuaternions :=
  if IsCrossingBond (x, i) then
    ∑ l, (ContinuousLinearMap.proj l : (Fin p → ℝ) →L[ℝ] ℝ).smulRight
      (if (w l).topBond = (enclosingCell x, i) then (w l).topDirection else 0)
  else 0
open Classical in
theorem crossingLinearPart_apply (w : Fin p → Perturbation F) (x : F.Site F.depth) (i : Fin 4)
    (τ : Fin p → ℝ) :
    crossingLinearPart w x i τ = if IsCrossingBond (x, i) then
      bondSpread (fun l => (w l).topBond) (fun l => (w l).topDirection) τ (enclosingCell x) i
    else 0 := by
  simp only [crossingLinearPart]
  split_ifs with h
  · simp only [bondSpread]
    simp only [FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  · simp
open Classical in
theorem crossingLinearPart_single (w : Fin p → Perturbation F) (x : F.Site F.depth) (i : Fin 4)
    (l : Fin p) :
    crossingLinearPart w x i (Pi.single l 1) = if IsCrossingBond (x, i) then
      (if (w l).topBond = (enclosingCell x, i) then (w l).topDirection else 0) else 0 := by
  simp only [crossingLinearPart]
  split_ifs with h h2
  · simp only [FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
    rw [Finset.sum_eq_single l]
    · simp [h2]
    · intro l' _ hl'
      simp [hl']
    · simp
  · simp only [FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
    rw [Finset.sum_eq_single l]
    · simp [h2]
    · intro l' _ hl'
      simp [hl']
    · simp
  · simp
theorem cellSupDist_self_eq_zero (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
def bondExponents (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
    (w : Fin p → Perturbation F) (x : F.Site F.depth) (i : Fin 4) (τ : Fin p → ℝ) :
    imaginaryQuaternions × imaginaryQuaternions :=
  (interpolatedFrame s a ρA m (x, i) (perturbedTop V w τ) +
      (stepCoordinates η x i + bulkLinearPart w x i τ), 0 + crossingLinearPart w x i τ)
theorem norm_iteratedFDeriv_bondExponents_le {K : ℕ → ℝ} {s a ρA r : ℝ} {m n : ℕ}
    {V : F.GaugeField F.top} {η : StepVariable (finiteCells F)} {w : Fin p → Perturbation F}
    (hK : ∀ k, 0 ≤ K k) (hr : 0 ≤ r) (hunit : ∀ l, (w l).IsUnit)
    {x : F.Site F.depth} {i : Fin 4} (hA : IsBondAnalyticAt (interpolatedFrame s a ρA m (x, i)) V)
    (hdec : ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions),
      1 ≤ k → AreUnitVectors X' →
        ‖bondDeriv (interpolatedFrame s a ρA m (x, i)) V c' X'‖ ≤
          K k * Real.exp (-(r * bondListDistance (enclosingCell x) c')))
    {q : ℕ} (J : Fin q → Fin p) (l : Fin q) (hq : q ≤ n) :
    ContDiffAt ℝ n (bondExponents s a ρA m V η w x i) 0 ∧
    ‖iteratedFDeriv ℝ q (bondExponents s a ρA m V η w x i) 0 (fun e => Pi.single (J e) 1)‖ ≤
      (K q + 1) * (w (J l)).decayWeight r x i := by
  have hh : ∀ N : ℕ, ContDiffAt ℝ N
      (fun τ => interpolatedFrame s a ρA m (x, i) (perturbedTop V w τ)) (0 : Fin p → ℝ) :=
    fun N => (hA p (fun l => (w l).topBond) (fun l => (w l).topDirection)).contDiffAt
  have haff : ∀ N : ℕ, ContDiffAt ℝ N (fun τ => stepCoordinates η x i + bulkLinearPart w x i τ)
      (0 : Fin p → ℝ) := fun N =>
    contDiffAt_const.add (bulkLinearPart w x i).contDiff.contDiffAt
  have hcr : ∀ N : ℕ, ContDiffAt ℝ N
      (fun τ => (0 : imaginaryQuaternions) + crossingLinearPart w x i τ) (0 : Fin p → ℝ) :=
    fun N => contDiffAt_const.add (crossingLinearPart w x i).contDiff.contDiffAt
  have hβ : ∀ N : ℕ, ContDiffAt ℝ N (bondExponents s a ρA m V η w x i) 0 := fun N =>
    ((hh N).add (haff N)).prodMk (hcr N)
  refine ⟨hβ n, ?_⟩
  set v : Fin q → Fin p → ℝ := fun e => Pi.single (J e) 1 with hv
  have hw0 := (w (J l)).decayWeight_nonneg r x i
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 fun e => by subst e; exact l.elim0
  have h1 : ‖iteratedFDeriv ℝ q (fun τ => stepCoordinates η x i + bulkLinearPart w x i τ) 0 v‖ ≤
      (w (J l)).decayWeight r x i := by
    by_cases h2 : 2 ≤ q
    · rw [iteratedFDeriv_const_add_clm_of_two_le _ _ h2]
      simpa using hw0
    · obtain rfl : q = 1 := by omega
      rw [iteratedFDeriv_const_add_clm_one]
      have hl : l = 0 := Subsingleton.elim _ _
      subst hl
      simp only [hv, bulkLinearPart_single]
      rcases norm_stepCoordinates_variableDirection_le (w (J 0)) (hunit _) r x i with h3 | h3
      · exact h3
      · rw [h3, stepCoordinates_zero_apply, norm_zero]
        exact hw0
  have h2 : ‖iteratedFDeriv ℝ q (fun τ => (0 : imaginaryQuaternions) + crossingLinearPart w x i τ)
      0 v‖ ≤ (w (J l)).decayWeight r x i := by
    by_cases h2 : 2 ≤ q
    · rw [iteratedFDeriv_const_add_clm_of_two_le _ _ h2]
      simpa using hw0
    · obtain rfl : q = 1 := by omega
      rw [iteratedFDeriv_const_add_clm_one]
      have hl : l = 0 := Subsingleton.elim _ _
      subst hl
      classical
      simp only [hv, crossingLinearPart_single]
      split_ifs with h3 h4
      · have hu := hunit (J 0)
        cases h5 : w (J 0) with
        | bulk b u => simpa [h5, Perturbation.topDirection] using (by simpa [h5] using hw0)
        | top c X =>
          rw [h5] at hu h4
          have hc : c = (enclosingCell x, i) := h4
          have hu' : ‖X‖ = 1 := hu
          subst hc
          simp [Perturbation.topDirection, Perturbation.decayWeight, cellSupDist_self_eq_zero, hu']
      · simpa using hw0
      · simpa using hw0
  have hfr := norm_iteratedFDeriv_interpolatedFrame_le (s := s) (a := a) (ρA := ρA) (m := m)
    hK hr hunit hA hdec J l
  have hfst : (iteratedFDeriv ℝ q (bondExponents s a ρA m V η w x i) 0 v).1 =
      iteratedFDeriv ℝ q (fun τ => interpolatedFrame s a ρA m (x, i) (perturbedTop V w τ)) 0 v +
        iteratedFDeriv ℝ q (fun τ => stepCoordinates η x i + bulkLinearPart w x i τ) 0 v := by
    have h3 := (ContinuousLinearMap.fst ℝ imaginaryQuaternions imaginaryQuaternions).iteratedFDeriv_comp_left
      (hβ q) (i := q) le_rfl
    have h4 := congrArg (fun M => M v) h3
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp,
      ContinuousLinearMap.coe_fst'] at h4
    rw [← h4]
    have h5 : (Prod.fst ∘ bondExponents s a ρA m V η w x i) =
        (fun τ => interpolatedFrame s a ρA m (x, i) (perturbedTop V w τ)) +
          fun τ => stepCoordinates η x i + bulkLinearPart w x i τ := rfl
    rw [h5, iteratedFDeriv_add_apply (hh q) (haff q)]
    rfl
  have hsnd : (iteratedFDeriv ℝ q (bondExponents s a ρA m V η w x i) 0 v).2 =
      iteratedFDeriv ℝ q (fun τ => (0 : imaginaryQuaternions) + crossingLinearPart w x i τ) 0 v := by
    have h3 := (ContinuousLinearMap.snd ℝ imaginaryQuaternions imaginaryQuaternions).iteratedFDeriv_comp_left
      (hβ q) (i := q) le_rfl
    have h4 := congrArg (fun M => M v) h3
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp,
      ContinuousLinearMap.coe_snd'] at h4
    rw [← h4]
    rfl
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [hfst]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ K q * (w (J l)).decayWeight r x i + (w (J l)).decayWeight r x i := add_le_add hfr h1
      _ = _ := by ring
  · rw [hsnd]
    refine h2.trans ?_
    nlinarith [hK q]
theorem bondExponents_zero (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (w : Fin p → Perturbation F) (x : F.Site F.depth)
    (i : Fin 4) :
    bondExponents s a ρA m V η w x i 0 = (interpolatedCoords s a ρA m V η x i, 0) := by
  have h : perturbedTop V w 0 = V := by
    simp only [perturbedTop]
    rw [bondSpread_at_zero, leftTranslate_zero_eq]
  simp only [bondExponents, h, map_zero, add_zero]
  rfl
end
theorem motionAboveFrameStatement_proof : motionAboveFrameStatement := by
  intro n K hK
  obtain ⟨Lg, U, hU, hLg, hL1, hexp⟩ := exists_local_logarithm n
  choose B hB0 hB using exists_norm_iteratedFDeriv_expProd_le
  let A₀ : ℕ → ℝ := fun q => K q + 1
  have hA₀ : ∀ q, 0 ≤ A₀ q := fun q => add_nonneg (hK q) zero_le_one
  let A₁ : ℕ → ℝ := fun r => ∑ c : OrderedFinpartition r, B c.length * ∏ m, A₀ (c.partSize m)
  have hA₁ : ∀ q, 0 ≤ A₁ q := fun q => Finset.sum_nonneg fun c _ =>
    mul_nonneg (hB0 _) (Finset.prod_nonneg fun m _ => hA₀ _)
  let M : ℕ → ℝ := fun q => ∑ c : OrderedFinpartition q,
    ‖iteratedFDeriv ℝ c.length Lg 1‖ * ∏ m, A₁ (c.partSize m)
  have hM : ∀ q, 0 ≤ M q := fun q => Finset.sum_nonneg fun c _ =>
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun m _ => hA₁ _)
  obtain ⟨Ce, hCe, hexpL⟩ := exists_exp_lipschitz_near_zero
  let M' : ℕ → ℝ := fun q => M q + 3 * Ce * (K 1 + 1)
  have hM' : ∀ q, 0 ≤ M' q := fun q => add_nonneg (hM q)
    (mul_nonneg (mul_nonneg (by norm_num) hCe) (add_nonneg (hK 1) zero_le_one))
  refine ⟨M', hM', ?_⟩
  intro F s a ρA r m p V η w hper hr hchart hsmall hA hdec hunit
  classical
  have hne : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨hper i⟩
  let E : F.Site F.depth → Fin 4 → ℍ[ℝ] := fun x i =>
    (((expUnit (interpolatedCoords s a ρA m V η x i))⁻¹ : UnitQuaternion) : ℍ[ℝ])
  let R : F.Site F.depth → Fin 4 → ℍ[ℝ] →L[ℝ] ℍ[ℝ] := fun x i =>
    (ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip (E x i)
  let Θ : F.Site F.depth → Fin 4 → (Fin p → ℝ) → ℍ[ℝ] := fun x i τ =>
    R x i (expProd (bondExponents s a ρA m V η w x i τ))
  have hR : ∀ x i, ‖R x i‖ ≤ 1 := fun x i => by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    show ‖z * E x i‖ ≤ 1 * ‖z‖
    rw [norm_mul, norm_coe_unitQuaternion]
    simp
  have hΘ0 : ∀ x i, Θ x i 0 = 1 := fun x i => by
    show expProd (bondExponents s a ρA m V η w x i 0) * E x i = 1
    rw [bondExponents_zero]
    simp only [expProd, E, ZeroMemClass.coe_zero, NormedSpace.exp_zero, mul_one]
    have h1 : NormedSpace.exp ((interpolatedCoords s a ρA m V η x i : imaginaryQuaternions) : ℍ[ℝ]) =
        ((expUnit (interpolatedCoords s a ρA m V η x i) : UnitQuaternion) : ℍ[ℝ]) := rfl
    rw [h1]
    show ((expUnit (interpolatedCoords s a ρA m V η x i) *
      (expUnit (interpolatedCoords s a ρA m V η x i))⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1
    rw [mul_inv_cancel]
    rfl
  have htwo : ∀ N : ℕ, ∀ z, ContDiffAt ℝ N expProd z := fun N z => (contDiff_expProd N).contDiffAt
  have hΘ : ∀ x i, ¬ IsAxialTreeBond (x, i) → ContDiffAt ℝ n (Θ x i) 0 ∧
      ∀ (q : ℕ) (J : Fin q → Fin p) (l : Fin q), q ≤ n →
        ‖iteratedFDeriv ℝ q (Θ x i) 0 fun e => Pi.single (J e) 1‖ ≤
          A₁ q * (w (J l)).decayWeight r x i := by
    intro x i ht
    have hd := hchart (x, i) ht
    have hpair : ∀ (q : ℕ) (J : Fin q → Fin p) (l : Fin q), q ≤ n →
        ‖iteratedFDeriv ℝ q (bondExponents s a ρA m V η w x i) 0 fun e => Pi.single (J e) 1‖ ≤
          A₀ q * (w (J l)).decayWeight r x i := fun q J l hq =>
      (norm_iteratedFDeriv_bondExponents_le (η := η) hK hr hunit (hA _ hd) (hdec _ hd) J l hq).2
    have hβ : ContDiffAt ℝ n (bondExponents s a ρA m V η w x i) 0 := by
      have hA' := hA _ hd
      have hh : ContDiffAt ℝ n (fun τ => interpolatedFrame s a ρA m (x, i) (perturbedTop V w τ))
          (0 : Fin p → ℝ) :=
        (hA' p (fun l => (w l).topBond) (fun l => (w l).topDirection)).contDiffAt
      exact (hh.add (contDiffAt_const.add (bulkLinearPart w x i).contDiff.contDiffAt)).prodMk
        (contDiffAt_const.add (crossingLinearPart w x i).contDiff.contDiffAt)
    have hg : ∀ N : ℕ, ContDiffAt ℝ N (R x i ∘ expProd) (bondExponents s a ρA m V η w x i 0) :=
      fun N => (R x i).contDiff.contDiffAt.comp _ (htwo N _)
    refine ⟨(hg n).comp (0 : Fin p → ℝ) hβ, fun q J l hq => ?_⟩
    have h1 := norm_iteratedFDeriv_comp_single_le (hg n) hβ (fun l => (w l).decayWeight r x i)
      (fun l => (w l).decayWeight_nonneg r x i) (fun l => (w l).decayWeight_le_one hr x i) A₀ hA₀
      hpair J l hq
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ ((w (J l)).decayWeight_nonneg r x i))
    refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right ?_
      (Finset.prod_nonneg fun m _ => hA₀ _)
    have hv : ‖(interpolatedCoords s a ρA m V η x i : imaginaryQuaternions)‖ ≤ 1 := hsmall x i ht
    have h2 := (R x i).norm_iteratedFDeriv_comp_left (x := bondExponents s a ρA m V η w x i 0)
      (N := c.length) (n := c.length) (htwo c.length _) le_rfl
    rw [bondExponents_zero] at h2 ⊢
    refine h2.trans ?_
    calc _ ≤ 1 * ‖iteratedFDeriv ℝ c.length expProd (interpolatedCoords s a ρA m V η x i, 0)‖ :=
          mul_le_mul_of_nonneg_right (hR x i) (ContinuousMultilinearMap.opNorm_nonneg _)
      _ ≤ B c.length := by rw [one_mul]; exact hB _ _ hv
  let α : (Fin p → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions := fun τ x i =>
    if IsAxialTreeBond (x, i) then 0 else Lg (Θ x i τ)
  have hfun : ∀ x i, ¬ IsAxialTreeBond (x, i) → (fun τ => α τ x i) = Lg ∘ Θ x i :=
    fun x i ht => by
      funext τ
      simp [α, ht]
  have hfun0 : ∀ x i, IsAxialTreeBond (x, i) → (fun τ => α τ x i) = fun _ => 0 := fun x i ht => by
    funext τ
    simp [α, ht]
  have hαs : ∀ x i, ContDiffAt ℝ n (fun τ => α τ x i) 0 := by
    intro x i
    by_cases ht : IsAxialTreeBond (x, i)
    · rw [hfun0 x i ht]
      exact contDiffAt_const
    · rw [hfun x i ht]
      exact ContDiffAt.comp (0 : Fin p → ℝ) (by rw [hΘ0]; exact hLg) (hΘ x i ht).1
  have hα0 : ∀ x i, α 0 x i = 0 := by
    intro x i
    by_cases ht : IsAxialTreeBond (x, i)
    · simp [α, ht]
    · simp [α, ht, hΘ0, hL1]
  have hev : ∀ᶠ τ in 𝓝 (0 : Fin p → ℝ), ∀ x i, ¬ IsAxialTreeBond (x, i) → Θ x i τ ∈ U := by
    rw [Filter.eventually_all]
    intro x
    rw [Filter.eventually_all]
    intro i
    by_cases ht : IsAxialTreeBond (x, i)
    · exact Filter.Eventually.of_forall fun τ h => (h ht).elim
    · have hc : ContinuousAt (Θ x i) 0 := (hΘ x i ht).1.continuousAt
      have h1 : Θ x i ⁻¹' U ∈ 𝓝 (0 : Fin p → ℝ) :=
        hc.preimage_mem_nhds (by rw [hΘ0]; exact hU)
      exact Filter.mem_of_superset h1 fun τ h _ => h
  refine ⟨α, hα0, hαs, fun x i ht τ => by simp [α, ht], ?_, ?_, ?_⟩
  · filter_upwards [hev] with τ hτ
    funext x i
    show chartedField (interpolatedCoords s a ρA m (perturbedTop V w τ) (perturbedVariable η w τ))
        (perturbedTop V w τ) x i =
      expUnit (α τ x i) * chartedField (interpolatedCoords s a ρA m V η) V x i
    by_cases ht : IsAxialTreeBond (x, i)
    · have hnc : ¬ IsCrossingBond (x, i) := ht.1
      simp [chartedField, hnc, ht, α, expUnit_zero_eq_one]
    · have hU' := hτ x i ht
      set a₁ : imaginaryQuaternions := (bondExponents s a ρA m V η w x i τ).1 with ha₁
      set a₂ : imaginaryQuaternions := (bondExponents s a ρA m V η w x i τ).2 with ha₂
      have hth : Θ x i τ = ((expUnit a₁ * expUnit a₂ *
          (expUnit (interpolatedCoords s a ρA m V η x i))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := rfl
      have hunitΘ : ‖Θ x i τ‖ = 1 := by
        rw [hth]
        exact norm_coe_unitQuaternion _
      have hα : expUnit (α τ x i) =
          expUnit a₁ * expUnit a₂ * (expUnit (interpolatedCoords s a ρA m V η x i))⁻¹ := by
        apply Subtype.ext
        have h1 : α τ x i = Lg (Θ x i τ) := by simp [α, ht]
        rw [h1]
        show NormedSpace.exp ((Lg (Θ x i τ) : imaginaryQuaternions) : ℍ[ℝ]) = _
        rw [hexp _ hU' hunitΘ]
        exact hth
      have ha₁' : interpolatedCoords s a ρA m (perturbedTop V w τ) (perturbedVariable η w τ) x i =
          a₁ := by
        simp only [ha₁, bondExponents, interpolatedCoords]
        rw [stepCoordinates_perturbedVariable]
      have ha₂' : a₂ = crossingLinearPart w x i τ := by
        simp only [ha₂, bondExponents, zero_add]
      rw [hα]
      by_cases hcr : IsCrossingBond (x, i)
      · have h2 : a₂ = bondSpread (fun l => (w l).topBond) (fun l => (w l).topDirection) τ
            (enclosingCell x) i := by
          rw [ha₂', crossingLinearPart_apply, if_pos hcr]
        simp only [chartedField, if_pos hcr, ha₁']
        have h3 : perturbedTop V w τ (enclosingCell x) i = expUnit a₂ * V (enclosingCell x) i := by
          rw [h2]
          rfl
        rw [h3]
        group
      · have h2 : a₂ = 0 := by
          rw [ha₂', crossingLinearPart_apply, if_neg hcr]
        simp only [chartedField, if_neg hcr, if_neg ht, ha₁', h2, expUnit_zero_eq_one]
        group
  · intro q e x i l hq
    by_cases ht : IsAxialTreeBond (x, i)
    · have hq1 : q ≠ 0 := fun h => by subst h; exact l.elim0
      simp only [motionComponent]
      rw [hfun0 x i ht, iteratedFDeriv_const_of_ne hq1]
      simpa using mul_nonneg (hM' q) ((w (e l)).decayWeight_nonneg r x i)
    · simp only [motionComponent]
      rw [hfun x i ht]
      have h1 := norm_iteratedFDeriv_comp_single_le (g := Lg) (β := Θ x i) (x := 0) (n := n)
        (by rw [hΘ0]; exact hLg) (hΘ x i ht).1 (fun l => (w l).decayWeight r x i)
        (fun l => (w l).decayWeight_nonneg r x i) (fun l => (w l).decayWeight_le_one hr x i)
        A₁ hA₁ (hΘ x i ht).2 e l hq
      rw [hΘ0] at h1
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ ((w (e l)).decayWeight_nonneg r x i))
      simp only [M']
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hCe)
        (add_nonneg (hK 1) zero_le_one)
      linarith
  · intro l c X x i hn1 hwl ht
    have hd := hchart (x, i) ht
    have hn0 : ((n : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hn1' : ((1 : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast hn1
    have hA' := hA _ hd
    have hh1 : ContDiffAt ℝ (1 : ℕ)
        (fun τ => interpolatedFrame s a ρA m (x, i) (perturbedTop V w τ)) (0 : Fin p → ℝ) :=
      (hA' p (fun l => (w l).topBond) (fun l => (w l).topDirection)).contDiffAt
    have hhd : HasFDerivAt (fun τ => interpolatedFrame s a ρA m (x, i) (perturbedTop V w τ))
        (fderiv ℝ (fun τ => interpolatedFrame s a ρA m (x, i) (perturbedTop V w τ)) 0)
        (0 : Fin p → ℝ) :=
      (hh1.differentiableAt (by norm_num)).hasFDerivAt
    have G1 : HasFDerivAt (fun τ => stepCoordinates η x i + bulkLinearPart w x i τ)
        (bulkLinearPart w x i) (0 : Fin p → ℝ) := ((bulkLinearPart w x i).hasFDerivAt).const_add _
    have B1 := hhd.add G1
    have G2 : HasFDerivAt (fun τ => (0 : imaginaryQuaternions) + crossingLinearPart w x i τ)
        (crossingLinearPart w x i) (0 : Fin p → ℝ) :=
      ((crossingLinearPart w x i).hasFDerivAt).const_add _
    have hv := hsmall x i ht
    have hval : ∀ τ, Θ x i τ ∈ U → NormedSpace.exp ((α τ x i : imaginaryQuaternions) : ℍ[ℝ]) =
        NormedSpace.exp (((bondExponents s a ρA m V η w x i τ).1 : imaginaryQuaternions) : ℍ[ℝ]) *
          NormedSpace.exp (((bondExponents s a ρA m V η w x i τ).2 : imaginaryQuaternions) : ℍ[ℝ]) *
          (((expUnit (interpolatedCoords s a ρA m V η x i))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      intro τ hτ
      have hα : α τ x i = Lg (Θ x i τ) := by simp [α, ht]
      have hu : ‖Θ x i τ‖ = 1 := by
        have : Θ x i τ = ((expUnit (bondExponents s a ρA m V η w x i τ).1 *
            expUnit (bondExponents s a ρA m V η w x i τ).2 *
            (expUnit (interpolatedCoords s a ρA m V η x i))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := rfl
        rw [this]
        exact norm_coe_unitQuaternion _
      rw [hα, hexp _ hτ hu]
      rfl
    have hb0 := bondExponents_zero s a ρA m V η w x i
    have key := norm_fderiv_sub_add_le_of_exp_eq_mul hCe hexpL
      (v := interpolatedCoords s a ρA m V η x i)
      (h := fun τ => α τ x i)
      (b₁ := fun τ => (bondExponents s a ρA m V η w x i τ).1)
      (b₂ := fun τ => (bondExponents s a ρA m V η w x i τ).2) hv
      ((hαs x i).differentiableAt hn0) B1.differentiableAt G2.differentiableAt (hα0 x i)
      (by rw [hb0]) (by rw [hb0]) (hev.mono fun τ hτ => hval τ (hτ x i ht)) (Pi.single l 1)
    have hb1 : fderiv ℝ (fun τ => (bondExponents s a ρA m V η w x i τ).1) 0 (Pi.single l 1) =
        bondDeriv (interpolatedFrame s a ρA m (x, i)) V (fun _ : Fin 1 => c) (fun _ => X) := by
      have h1 : fderiv ℝ (fun τ => (bondExponents s a ρA m V η w x i τ).1) 0 = _ := B1.fderiv
      rw [h1]
      have hfp := iteratedFDeriv_interpolatedFrame_single_eq (s := s) (a := a) (ρA := ρA) (m := m)
        (V := V) (w := w) (d := (x, i)) (fun _ : Fin 1 => l) hh1
      have e1 : ((fun l => (w l).topBond) ∘ fun _ : Fin 1 => l) = fun _ : Fin 1 => c := by
        funext _
        simp [hwl, Perturbation.topBond]
      have e2 : ((fun l => (w l).topDirection) ∘ fun _ : Fin 1 => l) = fun _ : Fin 1 => X := by
        funext _
        simp [hwl, Perturbation.topDirection]
      rw [e1, e2, iteratedFDeriv_one_apply] at hfp
      have hz : bulkLinearPart w x i (Pi.single l 1) = 0 := by
        rw [bulkLinearPart_single, hwl]
        exact stepCoordinates_zero_apply x i
      simp only [add_apply, hz, add_zero]
      exact hfp
    have hb2 : fderiv ℝ (fun τ => (bondExponents s a ρA m V η w x i τ).2) 0 (Pi.single l 1) =
        if IsCrossingBond (x, i) ∧ c = (enclosingCell x, i) then X else 0 := by
      have h1 : fderiv ℝ (fun τ => (bondExponents s a ρA m V η w x i τ).2) 0 = _ := G2.fderiv
      rw [h1, crossingLinearPart_single, hwl]
      simp only [Perturbation.topBond, Perturbation.topDirection]
      by_cases hc1 : IsCrossingBond (x, i) <;> by_cases hc2 : c = (enclosingCell x, i) <;>
        simp [hc1, hc2]
    rw [hb1, hb2] at key
    have hm : motionComponent α (fun _ : Fin 1 => l) x i =
        fderiv ℝ (fun τ => α τ x i) 0 (Pi.single l 1) := by
      simp only [motionComponent]
      rw [iteratedFDeriv_one_apply]
    rw [hm]
    refine key.trans ?_
    have hu1 : ‖bondDeriv (interpolatedFrame s a ρA m (x, i)) V (fun _ : Fin 1 => c) (fun _ => X)‖ ≤
        K 1 := by
      have hX : ‖X‖ = 1 := by
        have := hunit l
        rw [hwl] at this
        exact this
      have h2 := hdec _ hd 1 (fun _ => c) (fun _ => X) le_rfl (fun _ => hX)
      refine h2.trans ?_
      have h3 : Real.exp (-(r * bondListDistance (enclosingCell (x, i).1) fun _ : Fin 1 => c)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hr (Nat.cast_nonneg _)))
      exact mul_le_of_le_one_right (hK 1) h3
    have ht1 : ‖(if IsCrossingBond (x, i) ∧ c = (enclosingCell x, i) then X else 0 :
        imaginaryQuaternions)‖ ≤ 1 := by
      split_ifs
      · have := hunit l
        rw [hwl] at this
        exact le_of_eq this
      · simp
    have hnv := norm_nonneg (interpolatedCoords s a ρA m V η x i)
    simp only [M']
    have hsum := add_le_add hu1 ht1
    have h3C : 0 ≤ 3 * Ce * ‖interpolatedCoords s a ρA m V η x i‖ :=
      mul_nonneg (mul_nonneg (by norm_num) hCe) hnv
    have h4 := mul_le_mul_of_nonneg_left hsum h3C
    have hM0 := mul_nonneg (hM 0) hnv
    nlinarith
end Estimates
end YangMills.Construction
end
