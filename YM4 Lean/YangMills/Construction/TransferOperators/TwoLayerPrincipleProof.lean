import YangMills.Construction.MirrorGridsOfEverySide.DominationByTheChessboardProof
import YangMills.Construction.TransferOperators.FactsOfTheOperatorsOfACubicTorus
import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernel
import YangMills.Construction.TransferOperators.GaugeAveragesOfFunctionsOfLayersProof
import YangMills.Construction.TransferOperators.InsertionObservableIsRealLocalAndGaugeInvariantProof
import YangMills.Construction.TransferOperators.InsertionOfContractionsBetweenLayers
import YangMills.Construction.TransferOperators.TwoLayerPrinciple
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction
open InfiniteLattice Schatten Matrices.ComplexMatrix2 TransferOperators.SqrtLinkFacts
open SpinHarmonics hiding toHaarL2
namespace TransferOperators.TwoLevelArgument
section Operators
variable {J : Type} [Finite J]
theorem integrable_haarL2 (φ : HaarL2 J) :
    Integrable (φ : (J → specialUnitary) → ℂ) (haarPi J) :=
  (Lp.memLp φ).integrable (by norm_num)
theorem integrable_kernel_mul (K : C((J → specialUnitary) × (J → specialUnitary), ℂ)) (φ : HaarL2 J)
    (u : J → specialUnitary) :
    Integrable (fun w => K (u, w) * (φ : (J → specialUnitary) → ℂ) w) (haarPi J) := by
  refine (integrable_haarL2 φ).bdd_mul (c := ‖K‖) ?_ ?_
  · exact (K.continuous.comp (Continuous.prodMk_right u)).aestronglyMeasurable
  · exact ae_of_all _ fun w => K.norm_coe_le_norm _
theorem hasKernel_unique {A : (J → specialUnitary) × (J → specialUnitary) → ℂ}
    {T T' : HaarL2 J →L[ℂ] HaarL2 J}
    (h : HasKernel (haarPi J) A T)
    (h' : HasKernel (haarPi J) A T') : T = T' :=
  ContinuousLinearMap.ext fun ψ => Lp.ext ((h ψ).trans (h' ψ).symm)
theorem hasKernel_zero :
    HasKernel (haarPi J)
      ((0 : C((J → specialUnitary) × (J → specialUnitary), ℂ)) : (J → specialUnitary) × (J → specialUnitary) → ℂ)
      (0 : HaarL2 J →L[ℂ] HaarL2 J) := by
  intro ψ
  filter_upwards [Lp.coeFn_zero ℂ 2 (haarPi J)] with u h
  simp [kernelApply]
theorem hasKernel_add {K K' : C((J → specialUnitary) × (J → specialUnitary), ℂ)}
    {T T' : HaarL2 J →L[ℂ] HaarL2 J}
    (h : HasKernel (haarPi J) K T)
    (h' : HasKernel (haarPi J) K' T') :
    HasKernel (haarPi J) (K + K' : C(_, ℂ)) (T + T') := by
  intro ψ
  filter_upwards [h ψ, h' ψ, Lp.coeFn_add (T ψ) (T' ψ)] with u h₁ h₂ h₃
  have e : (T + T') ψ = T ψ + T' ψ := rfl
  rw [e, h₃, Pi.add_apply, h₁, h₂]
  simp only [kernelApply, ContinuousMap.add_apply, add_mul]
  rw [integral_add (integrable_kernel_mul K ψ u) (integrable_kernel_mul K' ψ u)]
theorem hasKernel_smul (c : ℂ) {K : C((J → specialUnitary) × (J → specialUnitary), ℂ)}
    {T : HaarL2 J →L[ℂ] HaarL2 J}
    (h : HasKernel (haarPi J) K T) :
    HasKernel (haarPi J) (c • K : C(_, ℂ)) (c • T) := by
  intro ψ
  filter_upwards [h ψ, Lp.coeFn_smul c (T ψ)] with u h₁ h₂
  rw [show (c • T) ψ = c • T ψ from rfl, h₂, Pi.smul_apply, h₁]
  simp only [kernelApply, ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]
def outerOp (A A' : C(J → specialUnitary, ℂ)) : HaarL2 J →L[ℂ] HaarL2 J :=
  (innerSL ℂ (SqrtLinkFacts.toHaarL2 (star A'))).smulRight (SqrtLinkFacts.toHaarL2 A)
theorem outerOp_apply (A A' : C(J → specialUnitary, ℂ)) (φ : HaarL2 J) :
    outerOp A A' φ = (inner ℂ (SqrtLinkFacts.toHaarL2 (star A')) φ : ℂ) • SqrtLinkFacts.toHaarL2 A :=
  rfl
theorem coeFn_toHaarL2 (A : C(J → specialUnitary, ℂ)) :
    (SqrtLinkFacts.toHaarL2 A : (J → specialUnitary) → ℂ) =ᵐ[haarPi J] A :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (haarPi J) A
theorem inner_toHaarL2_star (A' : C(J → specialUnitary, ℂ)) (φ : HaarL2 J) :
    (inner ℂ (SqrtLinkFacts.toHaarL2 (star A')) φ : ℂ) =
      ∫ w, A' w * (φ : (J → specialUnitary) → ℂ) w ∂haarPi J := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toHaarL2 (star A')] with w h
  rw [h]
  simp [RCLike.inner_apply, mul_comm]
theorem hasKernel_outerOp (A A' : C(J → specialUnitary, ℂ)) :
    HasKernel (haarPi J) (fun p => A p.1 * A' p.2) (outerOp A A') := by
  intro ψ
  filter_upwards [Lp.coeFn_smul (inner ℂ (SqrtLinkFacts.toHaarL2 (star A')) ψ : ℂ)
    (SqrtLinkFacts.toHaarL2 A), coeFn_toHaarL2 A] with u h₁ h₂
  rw [outerOp_apply, h₁, Pi.smul_apply, h₂, smul_eq_mul, kernelApply,
    inner_toHaarL2_star, ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only
  ring
def finiteModeKernels (J : Type) [Finite J] (ϰ : HalfNatural) :
    Submodule ℂ C((J → specialUnitary) × (J → specialUnitary), ℂ) :=
  Submodule.span ℂ {K | ∃ A ∈ truncatedCoeffSpan J ϰ, ∃ A' ∈ truncatedCoeffSpan J ϰ,
    ∀ p, K p = A p.1 * A' p.2}
def kernelSwap (K : C((J → specialUnitary) × (J → specialUnitary), ℂ)) :
    C((J → specialUnitary) × (J → specialUnitary), ℂ) :=
  ⟨fun p => K p.swap, K.continuous.comp continuous_swap⟩
theorem kernelSwap_mem {ϰ : HalfNatural} {K : C((J → specialUnitary) × (J → specialUnitary), ℂ)}
    (hK : K ∈ finiteModeKernels J ϰ) : kernelSwap K ∈ finiteModeKernels J ϰ := by
  refine Submodule.span_induction (p := fun K _ => kernelSwap K ∈ finiteModeKernels J ϰ)
    ?_ ?_ ?_ ?_ hK
  · rintro K ⟨A, hA, A', hA', h⟩
    refine Submodule.subset_span ⟨A', hA', A, hA, fun p => ?_⟩
    change K p.swap = _
    rw [h, Prod.fst_swap, Prod.snd_swap, mul_comm]
  · have : kernelSwap (0 : C((J → specialUnitary) × (J → specialUnitary), ℂ)) = 0 := rfl
    rw [this]
    exact Submodule.zero_mem _
  · intro K K' _ _ h h'
    have : kernelSwap (K + K') = kernelSwap K + kernelSwap K' := rfl
    rw [this]
    exact Submodule.add_mem _ h h'
  · intro c K _ h
    have : kernelSwap (c • K) = c • kernelSwap K := rfl
    rw [this]
    exact Submodule.smul_mem _ c h
theorem proj_mul_outerOp_mul_proj {P : HaarL2 J →L[ℂ] HaarL2 J}
    (hP : P = star P) {A A' : C(J → specialUnitary, ℂ)} (hA : P (SqrtLinkFacts.toHaarL2 A) = SqrtLinkFacts.toHaarL2 A)
    (hA' : P (SqrtLinkFacts.toHaarL2 (star A')) = SqrtLinkFacts.toHaarL2 (star A')) :
    P * outerOp A A' * P = outerOp A A' := by
  refine ContinuousLinearMap.ext fun φ => ?_
  have e : (inner ℂ (SqrtLinkFacts.toHaarL2 (star A')) (P φ) : ℂ) =
      inner ℂ (SqrtLinkFacts.toHaarL2 (star A')) φ := by
    have h := ContinuousLinearMap.adjoint_inner_left P φ (SqrtLinkFacts.toHaarL2 (star A'))
    rw [← ContinuousLinearMap.star_eq_adjoint, ← hP, hA'] at h
    exact h.symm
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, outerOp_apply, map_smul, hA, e]
theorem exists_op_of_finiteMode {ϰ : HalfNatural}
    (hP : HilbertSpaceBasics.IsOrthProjOp (truncationProj J ϰ))
    (hE : ∀ A ∈ truncatedCoeffSpan J ϰ,
      truncationProj J ϰ (SqrtLinkFacts.toHaarL2 A) = SqrtLinkFacts.toHaarL2 A)
    (hstar : ∀ A ∈ truncatedCoeffSpan J ϰ, star A ∈ truncatedCoeffSpan J ϰ)
    {K : C((J → specialUnitary) × (J → specialUnitary), ℂ)} (hK : K ∈ finiteModeKernels J ϰ) :
    ∃ T : HaarL2 J →L[ℂ] HaarL2 J,
      HasKernel (haarPi J) K T ∧
        truncationProj J ϰ * T * truncationProj J ϰ = T := by
  refine Submodule.span_induction (p := fun (K : C((J → specialUnitary) × (J → specialUnitary), ℂ)) _ =>
    ∃ T : HaarL2 J →L[ℂ] HaarL2 J,
      HasKernel (haarPi J) K T ∧
        truncationProj J ϰ * T * truncationProj J ϰ = T) ?_ ?_ ?_ ?_ hK
  · rintro K ⟨A, hA, A', hA', h⟩
    refine ⟨outerOp A A', ?_, proj_mul_outerOp_mul_proj hP.1 (hE A hA) (hE _ (hstar A' hA'))⟩
    have e : (K : (J → specialUnitary) × (J → specialUnitary) → ℂ) = fun p => A p.1 * A' p.2 := funext h
    rw [e]
    exact hasKernel_outerOp A A'
  · exact ⟨0, hasKernel_zero, by simp⟩
  · rintro K K' _ _ ⟨T, hT, h⟩ ⟨T', hT', h'⟩
    refine ⟨T + T', hasKernel_add hT hT', ?_⟩
    rw [mul_add, add_mul, h, h']
  · rintro c K _ ⟨T, hT, h⟩
    refine ⟨c • T, hasKernel_smul c hT, ?_⟩
    rw [mul_smul_comm, smul_mul_assoc, h]
theorem inner_antisymm_of_kernel {K : C((J → specialUnitary) × (J → specialUnitary), ℂ)}
    {T : HaarL2 J →L[ℂ] HaarL2 J}
    (hT : HasKernel (haarPi J) K T) (hre : ∀ p, (K p).im = 0)
    (hanti : ∀ u u', K (u, u') = -K (u', u)) (φ ψ : HaarL2 J) :
    (inner ℂ (T φ) ψ : ℂ) = -inner ℂ φ (T ψ) := by
  set f : (J → specialUnitary) → (J → specialUnitary) → ℂ := fun u w =>
    K (u, w) * (star ((φ : (J → specialUnitary) → ℂ) w) * (ψ : (J → specialUnitary) → ℂ) u) with hf
  have hint : Integrable (Function.uncurry f)
      ((haarPi J).prod (haarPi J)) := by
    have h₀ : Integrable (fun z : (J → specialUnitary) × (J → specialUnitary) =>
        (ψ : (J → specialUnitary) → ℂ) z.1 * star ((φ : (J → specialUnitary) → ℂ) z.2))
        ((haarPi J).prod (haarPi J)) :=
      (integrable_haarL2 ψ).mul_prod
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (integrable_haarL2 φ))
    have h₁ := h₀.bdd_mul (c := ‖K‖) K.continuous.aestronglyMeasurable
      (ae_of_all _ fun z => K.norm_coe_le_norm z)
    refine h₁.congr (ae_of_all _ fun z => ?_)
    simp only [hf, Function.uncurry]
    rw [mul_comm ((ψ : (J → specialUnitary) → ℂ) z.1)]
  have hconj : ∀ p, star (K p) = K p := fun p => Complex.conj_eq_iff_im.2 (hre p)
  have e₁ : (inner ℂ (T φ) ψ : ℂ) = ∫ u, ∫ w, f u w ∂haarPi J ∂haarPi J := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hT φ] with u h
    rw [h, RCLike.inner_apply, kernelApply]
    have e : (starRingEnd ℂ) (∫ ξ', K (u, ξ') * (φ : (J → specialUnitary) → ℂ) ξ' ∂haarPi J) =
        ∫ ξ', K (u, ξ') * star ((φ : (J → specialUnitary) → ℂ) ξ') ∂haarPi J := by
      rw [← integral_conj]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      simp only [map_mul]
      congr 1
      exact hconj _
    rw [e, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [hf]
    ring
  have e₂ : (inner ℂ φ (T ψ) : ℂ) =
      -∫ u, ∫ w, f w u ∂haarPi J ∂haarPi J := by
    rw [L2.inner_def, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hT ψ] with u h
    rw [h, RCLike.inner_apply, kernelApply, ← integral_neg, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [hf]
    rw [hanti u w]
    change _ = -(K (w, u) * (star ((φ : (J → specialUnitary) → ℂ) u) * (ψ : (J → specialUnitary) → ℂ) w))
    simp only [RCLike.star_def]
    ring
  rw [e₂, neg_neg, e₁]
  exact integral_integral_swap hint
theorem isRealPreserving_mul {A A' : HaarL2 J →L[ℂ] HaarL2 J}
    (h : IsRealPreserving A) (h' : IsRealPreserving A') : IsRealPreserving (A * A') :=
  fun _ hφ => h _ (h' _ hφ)
theorem isRealPreserving_one : IsRealPreserving (1 : HaarL2 J →L[ℂ] HaarL2 J) :=
  fun _ hφ => hφ
theorem isRealPreserving_linComb (a b : ℝ)
    {X D : HaarL2 J →L[ℂ] HaarL2 J} (hX : IsRealPreserving X)
    (hD : IsRealPreserving D) : IsRealPreserving ((a : ℂ) • X + (b : ℂ) • D) := by
  intro φ hφ
  filter_upwards [hX φ hφ, hD φ hφ, Lp.coeFn_add ((a : ℂ) • X φ) ((b : ℂ) • D φ),
    Lp.coeFn_smul (a : ℂ) (X φ), Lp.coeFn_smul (b : ℂ) (D φ)] with u h₁ h₂ h₃ h₄ h₅
  have e : ((a : ℂ) • X + (b : ℂ) • D) φ = (a : ℂ) • X φ + (b : ℂ) • D φ := rfl
  rw [e, h₃, Pi.add_apply, h₄, h₅]
  simp [h₁, h₂]
theorem norm_cayleyApprox_le {D : HaarL2 J →L[ℂ] HaarL2 J}
    (hD : ∀ φ ψ : HaarL2 J, (inner ℂ (D φ) ψ : ℂ) = -inner ℂ φ (D ψ)) (ε : ℝ) :
    ‖(((1 + ε ^ 2 * ‖D‖ ^ 2)⁻¹ : ℝ) : ℂ) • (1 : HaarL2 J →L[ℂ] HaarL2 J) +
      (((1 + ε ^ 2 * ‖D‖ ^ 2)⁻¹ * ε : ℝ) : ℂ) • D‖ ≤ 1 := by
  set w : ℝ := 1 + ε ^ 2 * ‖D‖ ^ 2 with hw
  have hw1 : 1 ≤ w := by
    have : 0 ≤ ε ^ 2 * ‖D‖ ^ 2 := by positivity
    linarith
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ => ?_
  have e : ((((w⁻¹ : ℝ) : ℂ) • (1 : HaarL2 J →L[ℂ] HaarL2 J) +
      ((w⁻¹ * ε : ℝ) : ℂ) • D) φ) = ((w⁻¹ : ℝ) : ℂ) • (φ + (ε : ℂ) • D φ) := by
    change ((w⁻¹ : ℝ) : ℂ) • φ + ((w⁻¹ * ε : ℝ) : ℂ) • D φ = _
    rw [smul_add, smul_smul, Complex.ofReal_mul]
  rw [e, norm_smul, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hre : RCLike.re (inner ℂ φ ((ε : ℂ) • D φ) : ℂ) = 0 := by
    have h₁ : (inner ℂ φ (D φ) : ℂ).re = 0 := by
      have h₂ := hD φ φ
      rw [← inner_conj_symm] at h₂
      have h₃ := congrArg Complex.re h₂
      simp only [Complex.conj_re, Complex.neg_re] at h₃
      linarith
    rw [inner_smul_right]
    simp [h₁]
  have hsq : ‖φ + (ε : ℂ) • D φ‖ ^ 2 ≤ w * ‖φ‖ ^ 2 := by
    rw [@norm_add_sq ℂ, hre, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h₁ : ‖D φ‖ ≤ ‖D‖ * ‖φ‖ := D.le_opNorm φ
    have h₂ : ‖D φ‖ ^ 2 ≤ (‖D‖ * ‖φ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    have h₃ : (|ε| * ‖D φ‖) ^ 2 = ε ^ 2 * ‖D φ‖ ^ 2 := by rw [mul_pow, sq_abs]
    rw [h₃, hw]
    have h₄ : ε ^ 2 * ‖D φ‖ ^ 2 ≤ ε ^ 2 * (‖D‖ * ‖φ‖) ^ 2 :=
      mul_le_mul_of_nonneg_left h₂ (by positivity)
    nlinarith
  have hle : (w⁻¹ * ‖φ + (ε : ℂ) • D φ‖) ^ 2 ≤ ‖φ‖ ^ 2 := by
    rw [mul_pow]
    calc (w⁻¹) ^ 2 * ‖φ + (ε : ℂ) • D φ‖ ^ 2 ≤ (w⁻¹) ^ 2 * (w * ‖φ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = w⁻¹ * ‖φ‖ ^ 2 := by field_simp
      _ ≤ 1 * ‖φ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hw1) (by positivity)
      _ = ‖φ‖ ^ 2 := one_mul _
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hle
end Operators
theorem sub_two_mul_sq_le_log_one_add {x : ℝ} (hx : |x| ≤ 1 / 2) : x - 2 * x ^ 2 ≤ Real.log (1 + x) := by apply _root_.YangMills.Construction.MirrorGridsAllSides.ChessboardDomination.sub_two_mul_sq_le_log_one_add <;> assumption
section Generator
variable {μ : Fin 4} (B : Block μ)
instance linkType_nonempty : Nonempty B.LinkType :=
  let ⟨b, hb⟩ := B.links_nonempty
  ⟨⟨b, hb⟩⟩
theorem exists_skew_generator
    (hS : SandwichOperatorStatement)
    (hR : SqrtLinkFacts.SqrtLinkKernelFacts)
    (hF : SpinHarmonics.SeveralVariables.SeveralVariablesFacts)
    (hH : GibbsHaarKernels.Statement)
    (hT : CubicTorusOperators.Statement)
    {β : ℝ} (hβ : 0 < β) (ϰ : HalfNatural)
    {K : C((B.LinkType → specialUnitary) × (B.LinkType → specialUnitary), ℂ)}
    (hK : K ∈ finiteModeKernels B.LinkType ϰ) (hre : ∀ p, (K p).im = 0)
    (hanti : ∀ u u', K (u, u') = -K (u', u)) (hinv : B.IsInvariantKernel K) :
    ∃ D : HaarL2 B.LinkType →L[ℂ] HaarL2 B.LinkType,
      (∀ φ ψ : HaarL2 B.LinkType, (inner ℂ (D φ) ψ : ℂ) = -inner ℂ φ (D ψ)) ∧
      IsRealPreserving D ∧ (∀ g, Commute D (blockGaugeRep B g)) ∧
      ∀ u u', sqrtKernelSandwich β D u u' = K (u, u') := by
  have facts : B.OperatorProperties β := (hT β hβ).2 μ B
  obtain ⟨-, -, -, -, -, -, -, -, -, hInv⟩ := (hR β hβ).1 B.LinkType
  obtain ⟨hCr, hCs, -, hC1, hC2⟩ := hInv ϰ
  obtain ⟨hBasis, -, -, -, hConj, -⟩ := hF B.LinkType (fun _ => ⟨0⟩) ϰ
  obtain ⟨-, -, -, -, -, -, hP, -⟩ := hBasis
  have hE : ∀ A ∈ truncatedCoeffSpan B.LinkType ϰ,
      truncationProj B.LinkType ϰ (SqrtLinkFacts.toHaarL2 A) = SqrtLinkFacts.toHaarL2 A := by
    intro A hA
    have hmem : SqrtLinkFacts.toHaarL2 A ∈ Set.range (truncationProj B.LinkType ϰ) := by
      rw [hP.2]
      exact Submodule.mem_map_of_mem hA
    obtain ⟨x, hx⟩ := hmem
    rw [← hx]
    exact (DFunLike.congr_fun hP.1.2 x).symm
  obtain ⟨T, hT₁, hT₂⟩ := exists_op_of_finiteMode hP.1 hE hConj.2.2 hK
  obtain ⟨hOp, hUniq⟩ := hH.2.2.2 B.LinkType
  have hTeq : T = kernelOp (haarPi B.LinkType) K :=
    hasKernel_unique hT₁ (hOp K K.continuous).2.1
  have hTr : IsRealPreserving T := by
    rw [hTeq]
    exact (hOp K K.continuous).2.2.2.1 hre
  have hTc : ∀ g, Commute T (blockGaugeRep B g) := fun g => by
    rw [hTeq]
    exact facts.kernelOp_commute K K.continuous hinv g
  set Cinv := truncInvSqrtLinkOperator β B.LinkType ϰ with hCinv
  have hCc : ∀ g, Commute Cinv (blockGaugeRep B g) := fun g => by
    rw [hCinv, truncInvSqrtLinkOperator]
    refine Commute.sum_left _ _ _ fun l _ => Commute.smul_left ?_ _
    exact facts.kernelOp_commute _ (facts.isotypic_continuous l)
      (facts.isotypic_invariant l) g
  have hsk := inner_antisymm_of_kernel hT₁ hre (fun u u' => hanti u u')
  refine ⟨Cinv * T * Cinv, ?_, isRealPreserving_mul (isRealPreserving_mul hCr hTr) hCr,
    fun g => ((hCc g).mul_left (hTc g)).mul_left (hCc g), ?_⟩
  · intro φ ψ
    change (inner ℂ (Cinv (T (Cinv φ))) ψ : ℂ) = -inner ℂ φ (Cinv (T (Cinv ψ)))
    rw [← hCs, hsk, hCs]
  · have hCDC : sqrtLinkOperator β B.LinkType * (Cinv * T * Cinv) * sqrtLinkOperator β B.LinkType =
        T := by
      calc sqrtLinkOperator β B.LinkType * (Cinv * T * Cinv) * sqrtLinkOperator β B.LinkType
          = (sqrtLinkOperator β B.LinkType * Cinv) * T * (Cinv * sqrtLinkOperator β B.LinkType) := by
            simp only [mul_assoc]
        _ = T := by rw [hC1, hC2, hT₂]
    have hSan := (hS β hβ).1 B.LinkType (Cinv * T * Cinv)
    have hcont := hSan.1.2.1
    have hint := hSan.2.2
    rw [hCDC] at hint
    have hA : kernelOp (haarPi B.LinkType)
        (fun p : (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary) =>
          sqrtKernelSandwich β (Cinv * T * Cinv) p.1 p.2) =
        kernelOp (haarPi B.LinkType) K := by
      rw [← hTeq]
      exact hasKernel_unique (hOp _ hcont).2.1 hint
    have hkeq := hUniq.2 _ _ hcont K.continuous hA
    intro u u'
    exact congrFun hkeq (u, u')
end Generator
section FirstOrder
variable {μ : Fin 4} (B : Block μ)
theorem continuous_transportedLinkVariable (S : Stack) (j : ℤ) (b : SliceLink μ) :
    Continuous fun U : GaugeField 1 => S.transportedLinkVariable μ U j b := by apply _root_.YangMills.Construction.TransferOperators.SliceMean.continuous_transportedLinkVariable <;> assumption
def adjacentPair (i : ℤ) (U : GaugeField 1) :
    (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary) :=
  ((Stack.ofConsecutive i).blockValues B U i, (Stack.ofConsecutive i).blockValues B U (i + 1))
theorem continuous_blockValues (S : Stack) (j : ℤ) :
    Continuous fun U : GaugeField 1 => (S.blockValues B U j : B.LinkType → specialUnitary) :=
  continuous_pi fun b => continuous_transportedLinkVariable S j b.1
theorem continuous_adjacentPair (i : ℤ) : Continuous (adjacentPair B i) :=
  Continuous.prodMk (continuous_blockValues B _ _) (continuous_blockValues B _ _)
theorem integrable_comp_adjacentPair {ν : Measure (GaugeField 1)} [IsProbabilityMeasure ν] (i : ℤ)
    (f : C((B.LinkType → specialUnitary) × (B.LinkType → specialUnitary), ℝ)) :
    Integrable (fun U => f (adjacentPair B i U)) ν :=
  Integrable.of_bound (f.continuous.comp (continuous_adjacentPair B i)).measurable.aestronglyMeasurable
    ‖f‖ (ae_of_all _ fun _ => f.norm_coe_le_norm _)
theorem mean_mul_le_sq
    (hI : ContractionInsertionStatement)
    (hS : SandwichOperatorStatement)
    (hB : KernelSymmetryAndGaugeInvariance.Statement)
    {β : ℝ} (hβ : 0 < β) (i : ℤ) {ν : Measure (GaugeField 1)}
    (hν : IsPeriodicGibbs β ν)
    {D : HaarL2 B.LinkType →L[ℂ] HaarL2 B.LinkType}
    (hskew : ∀ φ ψ : HaarL2 B.LinkType, (inner ℂ (D φ) ψ : ℂ) = -inner ℂ φ (D ψ))
    (hreal : IsRealPreserving D) (hcomm : ∀ g, Commute D (blockGaugeRep B g))
    {Z : C((B.LinkType → specialUnitary) × (B.LinkType → specialUnitary), ℝ)}
    (hZ : ∀ u u', sqrtKernelSandwich β D u u' = (Z (u, u') : ℂ) * linkProductKernel β u u')
    {ε : ℝ} (hε : |ε| * ‖Z‖ ≤ 1 / 2) :
    ε * ∫ U, Z (adjacentPair B i U) ∂ν ≤ ε ^ 2 * (‖D‖ ^ 2 + 2 * ‖Z‖ ^ 2) := by
  have : IsProbabilityMeasure ν := hν.1.1
  set w : ℝ := 1 + ε ^ 2 * ‖D‖ ^ 2 with hw
  have hw0 : 0 < w := by positivity
  set Ξ : HaarL2 B.LinkType →L[ℂ] HaarL2 B.LinkType :=
    ((w⁻¹ : ℝ) : ℂ) • (1 : HaarL2 B.LinkType →L[ℂ] HaarL2 B.LinkType) +
      ((w⁻¹ * ε : ℝ) : ℂ) • D with hΞ
  have hnorm : ‖Ξ‖ ≤ 1 := norm_cayleyApprox_le hskew ε
  have hXr : IsRealPreserving Ξ := isRealPreserving_linComb _ _ isRealPreserving_one hreal
  have hXc : ∀ g, Commute Ξ (blockGaugeRep B g) := fun g =>
    (((Commute.one_left _).smul_left _).add_left ((hcomm g).smul_left _))
  obtain ⟨hlin, hone, -⟩ := (hS β hβ).2.1 B.LinkType
  have hbk := fun u u' => ((hB β hβ).1 B.LinkType).1 u u'
  have hbond : ∀ u u' : B.LinkType → specialUnitary,
      linkProductKernel β u u' = (((linkProductKernel β u u').re : ℝ) : ℂ) := fun u u' =>
    Complex.ext (by simp) (by simp [(hbk u u').2.1])
  have hbpos : ∀ u u' : B.LinkType → specialUnitary, 0 < (linkProductKernel β u u').re := fun u u' =>
    lt_of_lt_of_le (Real.exp_pos _) (hbk u u').2.2.1
  have hx : ∀ p, |ε * Z p| ≤ 1 / 2 := fun p => by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm.le.trans (Z.norm_coe_le_norm p))
      (abs_nonneg ε)).trans hε
  have hx0 : ∀ p, 0 < 1 + ε * Z p := fun p => by linarith [(abs_le.1 (hx p)).1]
  have hy0 : ∀ p, 0 < w⁻¹ * (1 + ε * Z p) := fun p => mul_pos (inv_pos.2 hw0) (hx0 p)
  have hval : ∀ u u', sqrtKernelSandwich β Ξ u u' =
      ((w⁻¹ * (1 + ε * Z (u, u')) : ℝ) : ℂ) * linkProductKernel β u u' := fun u u' => by
    rw [hΞ, hlin, hone, hZ]
    push_cast
    ring
  have hpos : ∀ u u', 0 < sqrtKernelSandwich β Ξ u u' := fun u u' => by
    rw [hval, hbond, ← Complex.ofReal_mul]
    exact Complex.zero_lt_real.2 (mul_pos (hy0 _) (hbpos u u'))
  have hins := (hI β hβ μ B Ξ hnorm hXr hXc hpos i).2.2.2.2 ν hν
  have hobs : ∀ U, B.logKernelRatio β Ξ i U =
      ((Real.log (w⁻¹ * (1 + ε * Z (adjacentPair B i U))) : ℝ) : ℂ) := fun U => by
    change Complex.log (sqrtKernelSandwich β Ξ (adjacentPair B i U).1 (adjacentPair B i U).2 /
      linkProductKernel β (adjacentPair B i U).1 (adjacentPair B i U).2) = _
    have hne : linkProductKernel β (adjacentPair B i U).1 (adjacentPair B i U).2 ≠ 0 := by
      intro h
      have := hbpos (adjacentPair B i U).1 (adjacentPair B i U).2
      rw [h] at this
      simp at this
    rw [hval, mul_div_cancel_right₀ _ hne, Complex.ofReal_log (hy0 _).le]
  have hle : ∫ U, Real.log (w⁻¹ * (1 + ε * Z (adjacentPair B i U))) ∂ν ≤ 0 := by
    have e : stateEval ν (B.logKernelRatio β Ξ i) =
        ((∫ U, Real.log (w⁻¹ * (1 + ε * Z (adjacentPair B i U))) ∂ν : ℝ) : ℂ) := (integral_congr_ae (ae_of_all _ hobs)).trans integral_complex_ofReal
    rw [e] at hins
    exact_mod_cast hins
  let ℓ : C((B.LinkType → specialUnitary) × (B.LinkType → specialUnitary), ℝ) :=
    ⟨fun p => Real.log (w⁻¹ * (1 + ε * Z p)),
      Continuous.log (continuous_const.mul (continuous_const.add (continuous_const.mul Z.continuous)))
        fun p => (hy0 p).ne'⟩
  have hlower : ∀ p, ε * Z p - ε ^ 2 * (‖D‖ ^ 2 + 2 * ‖Z‖ ^ 2) ≤ ℓ p := fun p => by
    change _ ≤ Real.log (w⁻¹ * (1 + ε * Z p))
    rw [Real.log_mul (inv_pos.2 hw0).ne' (hx0 p).ne', Real.log_inv]
    have h₁ : Real.log w ≤ ε ^ 2 * ‖D‖ ^ 2 := by
      have := Real.log_le_sub_one_of_pos hw0
      rw [hw] at this ⊢
      linarith
    have h₂ := sub_two_mul_sq_le_log_one_add (hx p)
    have h₃ : (Z p) ^ 2 ≤ ‖Z‖ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        ((Real.norm_eq_abs _).symm.le.trans (Z.norm_coe_le_norm p)) 2
    have h₄ : (ε * Z p) ^ 2 ≤ ε ^ 2 * ‖Z‖ ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left h₃ (by positivity)
    nlinarith
  have hmono : ∫ U, (ε * Z (adjacentPair B i U) - ε ^ 2 * (‖D‖ ^ 2 + 2 * ‖Z‖ ^ 2)) ∂ν ≤
      ∫ U, ℓ (adjacentPair B i U) ∂ν :=
    integral_mono (((integrable_comp_adjacentPair B i Z).const_mul ε).sub (integrable_const _))
      (integrable_comp_adjacentPair B i ℓ) fun U => hlower _
  rw [integral_sub ((integrable_comp_adjacentPair B i Z).const_mul ε) (integrable_const _),
    integral_const_mul, integral_const] at hmono
  simp only [probReal_univ, one_smul] at hmono
  have hle' : ∫ U, ℓ (adjacentPair B i U) ∂ν ≤ 0 := hle
  linarith
theorem mean_eq_zero
    (hI : ContractionInsertionStatement)
    (hS : SandwichOperatorStatement)
    (hB : KernelSymmetryAndGaugeInvariance.Statement)
    {β : ℝ} (hβ : 0 < β) (i : ℤ) {ν : Measure (GaugeField 1)}
    (hν : IsPeriodicGibbs β ν)
    {D : HaarL2 B.LinkType →L[ℂ] HaarL2 B.LinkType}
    (hskew : ∀ φ ψ : HaarL2 B.LinkType, (inner ℂ (D φ) ψ : ℂ) = -inner ℂ φ (D ψ))
    (hreal : IsRealPreserving D) (hcomm : ∀ g, Commute D (blockGaugeRep B g))
    {Z : C((B.LinkType → specialUnitary) × (B.LinkType → specialUnitary), ℝ)}
    (hZ : ∀ u u', sqrtKernelSandwich β D u u' = (Z (u, u') : ℂ) * linkProductKernel β u u') :
    ∫ U, Z (adjacentPair B i U) ∂ν = 0 := by
  set L := ∫ U, Z (adjacentPair B i U) ∂ν with hL
  set R : ℝ := ‖D‖ ^ 2 + 2 * ‖Z‖ ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  have hM0 : 0 ≤ ‖Z‖ := norm_nonneg _
  have key : ∀ t : ℝ, 0 < t → t * ‖Z‖ ≤ 1 / 2 → |L| ≤ t * R := by
    intro t ht htM
    have h₁ := mean_mul_le_sq B hI hS hB hβ i hν hskew hreal hcomm hZ (ε := t)
      (by rw [abs_of_pos ht]; exact htM)
    have h₂ := mean_mul_le_sq B hI hS hB hβ i hν hskew hreal hcomm hZ (ε := -t)
      (by rw [abs_neg, abs_of_pos ht]; exact htM)
    rw [← hL, ← hR] at h₁ h₂
    have h₃ : L ≤ t * R := by
      have : t * L ≤ t * (t * R) := by nlinarith
      exact le_of_mul_le_mul_left this ht
    have h₄ : -L ≤ t * R := by
      have : t * (-L) ≤ t * (t * R) := by nlinarith
      exact le_of_mul_le_mul_left this ht
    exact abs_le.2 ⟨by linarith, h₃⟩
  by_contra hne
  have hpos : 0 < |L| := abs_pos.2 hne
  set t : ℝ := min (1 / (2 * (‖Z‖ + 1))) (|L| / (2 * (R + 1))) with ht
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have ht1 : t * ‖Z‖ ≤ 1 / 2 := by
    calc t * ‖Z‖ ≤ 1 / (2 * (‖Z‖ + 1)) * ‖Z‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hM0
      _ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  have ht2 : t * R ≤ |L| / 2 := by
    calc t * R ≤ |L| / (2 * (R + 1)) * R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR0
      _ ≤ |L| / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have := key t ht0 ht1
  linarith
end FirstOrder
section Approximation
variable {μ : Fin 4} (B : Block μ) (i : ℤ)
def pairIndex : Set (ℤ × SliceLink μ) :=
  {q | (q.1 = i ∨ q.1 = i + 1) ∧ q.2 ∈ (B.links : Set (SliceLink μ))}
theorem pairIndex_subset : ∀ q ∈ pairIndex B i, q.2 ∈ linksWithin B.vertices :=
  fun _ hq => B.links_subset_linksWithin hq.2
def sumEquivPairIndex : B.LinkType ⊕ B.LinkType ≃ pairIndex B i :=
  Equiv.ofBijective
    (Sum.elim (fun b => ⟨(i, b.1), Or.inl rfl, b.2⟩) fun b => ⟨(i + 1, b.1), Or.inr rfl, b.2⟩) <| by
    constructor
    · rintro (a | a) (b | b) h
      · have := congrArg (fun q : pairIndex B i => q.1.2) h
        exact congrArg Sum.inl (Subtype.ext this)
      · have := congrArg (fun q : pairIndex B i => q.1.1) h
        simp at this
      · have := congrArg (fun q : pairIndex B i => q.1.1) h
        simp at this
      · have := congrArg (fun q : pairIndex B i => q.1.2) h
        exact congrArg Sum.inr (Subtype.ext this)
    · rintro ⟨⟨j, b⟩, hj | hj, hb⟩
      · obtain rfl : j = i := hj
        exact ⟨Sum.inl ⟨b, hb⟩, rfl⟩
      · obtain rfl : j = i + 1 := hj
        exact ⟨Sum.inr ⟨b, hb⟩, rfl⟩
instance pairIndex_finite : Finite (pairIndex B i) := Finite.of_equiv _ (sumEquivPairIndex B i)
instance pairIndex_nonempty : Nonempty (pairIndex B i) :=
  ⟨sumEquivPairIndex B i (Sum.inl (Classical.arbitrary _))⟩
theorem vertices_finite : B.vertices.Finite := by apply _root_.YangMills.Construction.TransferOperators.LogKernelRatio.finite_vertices <;> assumption
def joinPair (p : (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary)) :
    pairIndex B i → specialUnitary :=
  fun q => Sum.elim p.1 p.2 ((sumEquivPairIndex B i).symm q)
def splitPair (w : pairIndex B i → specialUnitary) :
    (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary) :=
  (fun b => w (sumEquivPairIndex B i (Sum.inl b)), fun b => w (sumEquivPairIndex B i (Sum.inr b)))
theorem joinPair_inl (p : (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary)) (b : B.LinkType) :
    joinPair B i p (sumEquivPairIndex B i (Sum.inl b)) = p.1 b := by
  simp [joinPair]
theorem joinPair_inr (p : (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary)) (b : B.LinkType) :
    joinPair B i p (sumEquivPairIndex B i (Sum.inr b)) = p.2 b := by
  simp [joinPair]
theorem splitPair_joinPair (p : (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary)) :
    splitPair B i (joinPair B i p) = p :=
  Prod.ext (funext fun b => joinPair_inl B i p b) (funext fun b => joinPair_inr B i p b)
theorem joinPair_splitPair (w : pairIndex B i → specialUnitary) : joinPair B i (splitPair B i w) = w := by
  funext q
  obtain ⟨s, rfl⟩ := (sumEquivPairIndex B i).surjective q
  rcases s with b | b
  · exact joinPair_inl B i _ b
  · exact joinPair_inr B i _ b
theorem continuous_splitPair : Continuous (splitPair B i) :=
  Continuous.prodMk (continuous_pi fun _ => continuous_apply _)
    (continuous_pi fun _ => continuous_apply _)
theorem continuous_joinPair : Continuous (joinPair B i) := by
  refine continuous_pi fun q => ?_
  obtain ⟨s, rfl⟩ := (sumEquivPairIndex B i).surjective q
  rcases s with b | b
  · have : (fun p => joinPair B i p (sumEquivPairIndex B i (Sum.inl b))) = fun p => p.1 b :=
      funext fun p => joinPair_inl B i p b
    rw [this]
    exact (continuous_apply b).comp continuous_fst
  · have : (fun p => joinPair B i p (sumEquivPairIndex B i (Sum.inr b))) = fun p => p.2 b :=
      funext fun p => joinPair_inr B i p b
    rw [this]
    exact (continuous_apply b).comp continuous_snd
theorem splitPair_diagonalGaugeAct (g : B.vertices → specialUnitary) (w : pairIndex B i → specialUnitary) :
    splitPair B i (diagonalGaugeAct (pairIndex_subset B i) g w) =
      (gaugeAct B.links_subset_linksWithin g (splitPair B i w).1,
        gaugeAct B.links_subset_linksWithin g (splitPair B i w).2) :=
  rfl
theorem joinPair_gaugeAct (g : B.vertices → specialUnitary) (u u' : B.LinkType → specialUnitary) :
    joinPair B i (gaugeAct B.links_subset_linksWithin g u,
        gaugeAct B.links_subset_linksWithin g u') =
      diagonalGaugeAct (pairIndex_subset B i) g (joinPair B i (u, u')) := by
  have h := splitPair_diagonalGaugeAct B i g (joinPair B i (u, u'))
  rw [splitPair_joinPair] at h
  rw [← h, joinPair_splitPair]
def joinPairMap : C((B.LinkType → specialUnitary) × (B.LinkType → specialUnitary), pairIndex B i → specialUnitary) :=
  ⟨joinPair B i, continuous_joinPair B i⟩
theorem coordProduct_joinPair (ψ : pairIndex B i → C(specialUnitary, ℂ))
    (p : (B.LinkType → specialUnitary) × (B.LinkType → specialUnitary)) :
    coordProduct ψ (joinPair B i p) =
      coordProduct (fun b => ψ (sumEquivPairIndex B i (Sum.inl b))) p.1 *
        coordProduct (fun b => ψ (sumEquivPairIndex B i (Sum.inr b))) p.2 := by
  classical
  let _ : Fintype B.LinkType := Fintype.ofFinite _
  change (∏ᶠ q, ψ q (joinPair B i p q)) = (∏ᶠ b, ψ (sumEquivPairIndex B i (Sum.inl b)) (p.1 b)) *
    ∏ᶠ b, ψ (sumEquivPairIndex B i (Sum.inr b)) (p.2 b)
  rw [← finprod_comp_equiv (sumEquivPairIndex B i)]
  simp only [finprod_eq_prod_of_fintype, Fintype.prod_sum_type, joinPair_inl, joinPair_inr]
theorem comp_joinPairMap_mem {ϰ : HalfNatural} {H : C(pairIndex B i → specialUnitary, ℂ)}
    (hH : H ∈ truncatedCoeffSpan (pairIndex B i) ϰ) :
    H.comp (joinPairMap B i) ∈ finiteModeKernels B.LinkType ϰ := by
  have hle : truncatedCoeffSpan (pairIndex B i) ϰ ≤
      (finiteModeKernels B.LinkType ϰ).comap
        (ContinuousMap.compRightAlgHom ℂ ℂ (joinPairMap B i)).toLinearMap := by
    refine iSup₂_le fun l hl => Submodule.span_le.2 ?_
    rintro F ⟨ψ, hψ, rfl⟩
    have hl' := mem_boundedWeights.1 hl
    have hpart : ∀ s : B.LinkType → B.LinkType ⊕ B.LinkType,
        coordProduct (fun b => ψ (sumEquivPairIndex B i (s b))) ∈
          truncatedCoeffSpan B.LinkType ϰ := fun s => by
      have h₁ : prodCoeffSpan (fun b => l (sumEquivPairIndex B i (s b))) ≤
          truncatedCoeffSpan B.LinkType ϰ :=
        le_iSup₂ (f := fun (l : B.LinkType → HalfNatural) (_ : l ∈ boundedWeights B.LinkType ϰ) =>
          prodCoeffSpan l) _ (mem_boundedWeights.2 fun b => hl' _)
      exact h₁ (Submodule.subset_span ⟨_, fun b => hψ _, rfl⟩)
    refine Submodule.subset_span ⟨_, hpart Sum.inl, _, hpart Sum.inr, fun p => ?_⟩
    exact coordProduct_joinPair B i ψ p
  exact hle hH
end Approximation
section General
variable {μ : Fin 4} (B : Block μ)
def linkKernelRe (β : ℝ) (facts : B.OperatorProperties β) :
    C((B.LinkType → specialUnitary) × (B.LinkType → specialUnitary), ℝ) :=
  ⟨fun p => (linkProductKernel β p.1 p.2).re, Complex.continuous_re.comp facts.link_continuous⟩
theorem mean_eq_zero_of_invariant_antisymm
    (hI : ContractionInsertionStatement)
    (hS : SandwichOperatorStatement)
    (hB : KernelSymmetryAndGaugeInvariance.Statement)
    (hR : SqrtLinkFacts.SqrtLinkKernelFacts)
    (hF : SpinHarmonics.SeveralVariables.SeveralVariablesFacts)
    (hH : GibbsHaarKernels.Statement)
    (hT : CubicTorusOperators.Statement)
    (hA : SliceGaugeMeanProperties)
    {β : ℝ} (hβ : 0 < β) (i : ℤ) {ν : Measure (GaugeField 1)}
    (hν : IsPeriodicGibbs β ν)
    (Y : C((B.LinkType → specialUnitary) × (B.LinkType → specialUnitary), ℝ))
    (hinv : ∀ (g : B.vertices → specialUnitary) (u u' : B.LinkType → specialUnitary),
      Y (gaugeAct B.links_subset_linksWithin g u,
        gaugeAct B.links_subset_linksWithin g u') = Y (u, u'))
    (hanti : ∀ u u' : B.LinkType → specialUnitary, Y (u, u') = -Y (u', u)) :
    ∫ U, Y (adjacentPair B i U) ∂ν = 0 := by
  have : IsProbabilityMeasure ν := hν.1.1
  have facts : B.OperatorProperties β := (hT β hβ).2 μ B
  set CR := linkKernelRe B β facts with hCR
  have hbk := fun u u' => ((hB β hβ).1 B.LinkType).1 u u'
  set c₀ : ℝ := Real.exp (-2 * β * (Nat.card B.LinkType : ℝ)) with hc₀
  have hc₀pos : 0 < c₀ := Real.exp_pos _
  have hCl : ∀ p, c₀ ≤ CR p := fun p => (hbk p.1 p.2).2.2.1
  have hCpos : ∀ p, 0 < CR p := fun p => lt_of_lt_of_le hc₀pos (hCl p)
  have hCb : ∀ p, linkProductKernel β p.1 p.2 = ((CR p : ℝ) : ℂ) := fun p =>
    Complex.ext (by simp [hCR, linkKernelRe]) (by simp [(hbk p.1 p.2).2.1])
  have hCs : ∀ p, CR p.swap = CR p := fun p => by
    change (linkProductKernel β p.2 p.1).re = (linkProductKernel β p.1 p.2).re
    rw [(hbk p.1 p.2).1]
  have hCi : ∀ (g : B.vertices → specialUnitary) (u u' : B.LinkType → specialUnitary),
      CR (gaugeAct B.links_subset_linksWithin g u,
        gaugeAct B.links_subset_linksWithin g u') = CR (u, u') := fun g u u' =>
    congrArg Complex.re (facts.link_invariant g u u')
  let Ψ : C(pairIndex B i → specialUnitary, ℂ) :=
    ⟨fun w => (((Y * CR) (splitPair B i w) : ℝ) : ℂ),
      Complex.continuous_ofReal.comp ((Y * CR).continuous.comp (continuous_splitPair B i))⟩
  have hΨre : IsRealValuedSliceFunction (Ψ : (pairIndex B i → specialUnitary) → ℂ) := fun w => by
    simp [Ψ]
  have hΨinv : IsDiagonalGaugeInvariant (pairIndex_subset B i)
      (Ψ : (pairIndex B i → specialUnitary) → ℂ) := fun g w => by
    change (((Y * CR) (splitPair B i (diagonalGaugeAct (pairIndex_subset B i) g w)) : ℝ) : ℂ) =
      (((Y * CR) (splitPair B i w) : ℝ) : ℂ)
    rw [splitPair_diagonalGaugeAct]
    simp only [ContinuousMap.mul_apply]
    rw [hinv, hCi]
  have hsites : B.vertices.Nonempty := by
    obtain ⟨b, hb⟩ := B.links_nonempty
    exact ⟨b.source, b, hb, Or.inl rfl⟩
  have : Finite B.vertices := (vertices_finite B).to_subtype
  obtain ⟨P, hP, hlim⟩ := (hA μ β hβ B.vertices (pairIndex B i) hsites
    (Set.nonempty_coe_sort.1 inferInstance) (pairIndex_subset B i)).2.2.1 Ψ hΨre hΨinv
  set L := ∫ U, Y (adjacentPair B i U) ∂ν with hL
  have key : ∀ η : ℝ, 0 < η → |L| ≤ η / c₀ := by
    intro η hη
    obtain ⟨n, hn⟩ := ((Metric.tendstoUniformly_iff.1 hlim) η hη).exists
    obtain ⟨hPr, hPi⟩ := hP n
    obtain ⟨-, -, -, -, -, -, -, hEv, -⟩ :=
      hF (pairIndex B i) (fun _ => ⟨0⟩) ⟨0⟩
    obtain ⟨ϰ, H, hHmem, hHP⟩ := (hEv (P n) hPr.1).1
    have hKp : H.comp (joinPairMap B i) ∈ finiteModeKernels B.LinkType ϰ := comp_joinPairMap_mem B i hHmem
    set Kp := H.comp (joinPairMap B i) with hKpdef
    set K : C((B.LinkType → specialUnitary) × (B.LinkType → specialUnitary), ℂ) :=
      (1 / 2 : ℂ) • (Kp - kernelSwap Kp) with hKdef
    have hKmem : K ∈ finiteModeKernels B.LinkType ϰ :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ hKp (kernelSwap_mem hKp))
    have hKval : ∀ p, K p = (1 / 2 : ℂ) * (P n (joinPair B i p) - P n (joinPair B i p.swap)) :=
      fun p => by
        rw [hHP, hHP]
        rfl
    have hKre : ∀ p, (K p).im = 0 := fun p => by
      rw [hKval]
      simp [hPr.2]
    have hKanti : ∀ u u', K (u, u') = -K (u', u) := fun u u' => by
      rw [hKval, hKval]
      simp only [Prod.swap_prod_mk]
      ring
    have hKinv : B.IsInvariantKernel K := fun g u u' => by
      rw [hKval, hKval]
      simp only [Prod.swap_prod_mk]
      rw [joinPair_gaugeAct, joinPair_gaugeAct, hPi, hPi]
    obtain ⟨D, hDs, hDr, hDc, hDk⟩ :=
      exists_skew_generator B hS hR hF hH hT hβ ϰ hKmem hKre hKanti hKinv
    let Z : C((B.LinkType → specialUnitary) × (B.LinkType → specialUnitary), ℝ) :=
      ⟨fun p => (K p).re / CR p,
        (Complex.continuous_re.comp K.continuous).div CR.continuous fun p => (hCpos p).ne'⟩
    have hZ : ∀ u u', sqrtKernelSandwich β D u u' = (Z (u, u') : ℂ) * linkProductKernel β u u' :=
      fun u u' => by
        have e₁ : K (u, u') = (((K (u, u')).re : ℝ) : ℂ) :=
          Complex.ext (by simp) (by simp [hKre])
        have e₂ : ((CR (u, u') : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hCpos (u, u')).ne'
        rw [hDk, hCb (u, u')]
        change K (u, u') = (((K (u, u')).re / CR (u, u') : ℝ) : ℂ) * ((CR (u, u') : ℝ) : ℂ)
        rw [Complex.ofReal_div, div_mul_cancel₀ _ e₂, ← e₁]
    have hZ0 := mean_eq_zero B hI hS hB hβ i hν hDs hDr hDc hZ
    have hclose : ∀ p, |(P n (joinPair B i p)).re - (Y * CR) p| < η := fun p => by
      have h₁ := hn (joinPair B i p)
      have h₂ : Ψ (joinPair B i p) = (((Y * CR) p : ℝ) : ℂ) := by
        change (((Y * CR) (splitPair B i (joinPair B i p)) : ℝ) : ℂ) = _
        rw [splitPair_joinPair]
      rw [h₂, dist_comm, dist_eq_norm] at h₁
      have h₃ := Complex.abs_re_le_norm (P n (joinPair B i p) - (((Y * CR) p : ℝ) : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at h₃
      exact lt_of_le_of_lt h₃ h₁
    have hYs : ∀ p, (Y * CR) p.swap = -(Y * CR) p := fun p => by
      simp only [ContinuousMap.mul_apply]
      rw [hCs]
      have : Y p.swap = -Y p := by
        rcases p with ⟨u, u'⟩
        exact (hanti u' u)
      rw [this]
      ring
    have hKclose : ∀ p, |(K p).re - (Y * CR) p| ≤ η := fun p => by
      have hre : (K p).re =
          1 / 2 * ((P n (joinPair B i p)).re - (P n (joinPair B i p.swap)).re) := by
        rw [hKval]
        simp
      have h₁ := abs_lt.1 (hclose p)
      have h₂ := abs_lt.1 (hclose p.swap)
      rw [hYs] at h₂
      rw [hre, abs_le]
      constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
    have hdiff : ∀ p, ‖(Y - Z) p‖ ≤ η / c₀ := fun p => by
      have e : (Y - Z) p = ((Y * CR) p - (K p).re) / CR p := by
        change Y p - (K p).re / CR p = (Y p * CR p - (K p).re) / CR p
        field_simp [(hCpos p).ne']
      rw [e, Real.norm_eq_abs, abs_div, abs_of_pos (hCpos p), abs_sub_comm]
      exact div_le_div₀ hη.le (hKclose p) hc₀pos (hCl p)
    have hsub : L = ∫ U, (Y - Z) (adjacentPair B i U) ∂ν := by
      change L = ∫ U, (Y (adjacentPair B i U) - Z (adjacentPair B i U)) ∂ν
      rw [integral_sub (integrable_comp_adjacentPair B i Y) (integrable_comp_adjacentPair B i Z), hZ0,
        sub_zero]
    have hnorm := norm_integral_le_of_norm_le_const (μ := ν)
      (ae_of_all _ fun U => hdiff (adjacentPair B i U))
    rw [← hsub] at hnorm
    simpa using hnorm
  by_contra hne
  have hpos : 0 < |L| := abs_pos.2 hne
  have h₁ := key (|L| * c₀ / 2) (by positivity)
  have h₂ : |L| * c₀ / 2 / c₀ = |L| / 2 := by field_simp
  rw [h₂] at h₁
  linarith
end General
theorem twoLevelPrinciple
    (hI : ContractionInsertionStatement)
    (hS : SandwichOperatorStatement)
    (hB : KernelSymmetryAndGaugeInvariance.Statement)
    (hR : SqrtLinkFacts.SqrtLinkKernelFacts)
    (hF : SpinHarmonics.SeveralVariables.SeveralVariablesFacts)
    (hH : GibbsHaarKernels.Statement)
    (hT : CubicTorusOperators.Statement)
    (hA : SliceGaugeMeanProperties) :
    TwoLevelPrinciple.Statement := by
  intro β hβ μ ν hν B i Y hinv hanti
  exact mean_eq_zero_of_invariant_antisymm B hI hS hB hR hF hH hT hA hβ i hν Y hinv hanti
end TransferOperators.TwoLevelArgument
end YangMills.Construction
end
