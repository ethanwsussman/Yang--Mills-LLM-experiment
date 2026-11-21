import YangMills.Construction.Matrices.FactsOnFunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernel
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsIsBoundedContinuousAndASeries
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsIsLinearAndReal
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics
open YangMills.Construction.TransferOperators.SqrtLinkFacts
open YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.TransferOperators.SandwichKernelBounds
variable {β : ℝ} {B : Type} [Finite B]
omit [Finite B] in
theorem continuous_sqrtLinkKernel_left
    (hc : Continuous fun p : (B → specialUnitary) × (B → specialUnitary) => sqrtLinkKernel β p.1 p.2)
    (u : B → specialUnitary) : Continuous fun w : B → specialUnitary => sqrtLinkKernel β w u := by
  have hm : Continuous fun w : B → specialUnitary => (w, u) :=
    Continuous.prodMk continuous_id continuous_const
  have hcomp := hc.comp hm
  exact hcomp
def sqrtLinkSliceMap
    (hc : Continuous fun p : (B → specialUnitary) × (B → specialUnitary) => sqrtLinkKernel β p.1 p.2)
    (u : B → specialUnitary) : C(B → specialUnitary, ℂ) :=
  ⟨fun w => sqrtLinkKernel β w u, continuous_sqrtLinkKernel_left hc u⟩
theorem sqrtLinkKernelSlice_eq_toHaarL2
    (hc : Continuous fun p : (B → specialUnitary) × (B → specialUnitary) => sqrtLinkKernel β p.1 p.2)
    (u : B → specialUnitary) :
    sqrtLinkKernelSlice β u = SqrtLinkFacts.toHaarL2 (sqrtLinkSliceMap hc u) := by
  have hm : MemLp (fun w => sqrtLinkKernel β w u) 2 (haarPi B) :=
    MemLp.of_bound (sqrtLinkSliceMap hc u).continuous.aestronglyMeasurable ‖sqrtLinkSliceMap hc u‖
      (Filter.Eventually.of_forall fun w => (sqrtLinkSliceMap hc u).norm_coe_le_norm w)
  have hs : sqrtLinkKernelSlice β u = hm.toLp _ := dif_pos hm
  rw [hs]
  apply Lp.ext
  exact hm.coeFn_toLp.trans (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (haarPi B) (sqrtLinkSliceMap hc u)).symm
theorem hasSum_sqrtLinkKernelSlice
    (hc : Continuous fun p : (B → specialUnitary) × (B → specialUnitary) => sqrtLinkKernel β p.1 p.2)
    (hser : HasAbsUniformSum
      (fun (α : PeterWeylIndex B) (p : (B → specialUnitary) × (B → specialUnitary)) =>
        (sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α p.1 * star (peterWeylFn α p.2))
      (fun p => sqrtLinkKernel β p.1 p.2))
    (u : B → specialUnitary) :
    HasSum (fun α : PeterWeylIndex B =>
        ((sqrtPeterWeylCoeff β α : ℂ) * star (peterWeylFn α u)) • peterWeylVec α)
      (sqrtLinkKernelSlice β u) := by
  have hC : HasSum (fun α : PeterWeylIndex B =>
      ((sqrtPeterWeylCoeff β α : ℂ) * star (peterWeylFn α u)) • peterWeylFn α)
      (sqrtLinkSliceMap hc u) := by
    have hu : TendstoUniformly (fun (s : Finset (PeterWeylIndex B)) (w : B → specialUnitary) =>
        ∑ α ∈ s, (sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α w *
          star (peterWeylFn α u)) (sqrtLinkSliceMap hc u) Filter.atTop :=
      hser.2.comp (fun w : B → specialUnitary => (w, u))
    have ht : Filter.Tendsto (fun s : Finset (PeterWeylIndex B) => ∑ α ∈ s,
        ((sqrtPeterWeylCoeff β α : ℂ) * star (peterWeylFn α u)) • peterWeylFn α)
        Filter.atTop (nhds (sqrtLinkSliceMap hc u)) := by
      rw [ContinuousMap.tendsto_iff_tendstoUniformly]
      have hfun : (fun (s : Finset (PeterWeylIndex B)) (w : B → specialUnitary) =>
          (∑ α ∈ s, ((sqrtPeterWeylCoeff β α : ℂ) * star (peterWeylFn α u)) •
            peterWeylFn α) w) = fun s w =>
          ∑ α ∈ s, (sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α w *
            star (peterWeylFn α u) := by
        funext s w
        rw [ContinuousMap.sum_apply]
        refine Finset.sum_congr rfl fun α _ => ?_
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      rw [hfun]
      exact hu
    simpa [HasSum] using ht
  have h := (ContinuousMap.toLp (E := ℂ) 2 (haarPi B) ℂ).hasSum hC
  rw [sqrtLinkKernelSlice_eq_toHaarL2 hc u]
  simpa [peterWeylVec, SqrtLinkFacts.toHaarL2] using h
theorem norm_toLp_le_norm (ψ : C(B → specialUnitary, ℂ)) :
    ‖ContinuousMap.toLp (E := ℂ) 2 (haarPi B) ℂ ψ‖ ≤ ‖ψ‖ := by
  have h₁ := (ContinuousMap.toLp (E := ℂ) 2 (haarPi B) ℂ).le_opNorm ψ
  have h₂ := ContinuousMap.toLp_norm_le (E := ℂ) (p := 2) (μ := haarPi B) (𝕜 := ℂ)
  simp only [measureUnivNNReal, measure_univ] at h₂
  simp at h₂
  calc _ ≤ _ := h₁
    _ ≤ 1 * ‖ψ‖ := mul_le_mul_of_nonneg_right h₂ (norm_nonneg _)
    _ = ‖ψ‖ := one_mul _
theorem summable_sqrtPeterWeylCoeff_mul_norm
    (hunit : ∀ α : PeterWeylIndex B, ‖peterWeylVec α‖ = 1)
    (hb : Summable fun α : PeterWeylIndex B =>
      (peterWeylCoeff β α).re ^ (1 / 2 : ℝ) * ‖peterWeylFn α‖ ^ 2) :
    Summable fun α : PeterWeylIndex B => sqrtPeterWeylCoeff β α * ‖peterWeylFn α‖ := by
  refine Summable.of_nonneg_of_le
    (fun α => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (fun α => ?_) hb
  have h1 : 1 ≤ ‖peterWeylFn α‖ := by
    have h := norm_toLp_le_norm (peterWeylFn α)
    rw [show ContinuousMap.toLp (E := ℂ) 2 (haarPi B) ℂ (peterWeylFn α) =
      peterWeylVec α from rfl, hunit α] at h
    exact h
  have hr : sqrtPeterWeylCoeff β α = (peterWeylCoeff β α).re ^ (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow _
  rw [← hr]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  nlinarith
theorem norm_peterWeylEntry_le
    (hunit : ∀ α : PeterWeylIndex B, ‖peterWeylVec α‖ = 1)
    (X : HaarL2 B →L[ℂ] HaarL2 B) (α α' : PeterWeylIndex B) :
    ‖peterWeylEntry X α α'‖ ≤ ‖X‖ := by
  calc ‖peterWeylEntry X α α'‖
      ≤ ‖peterWeylVec α‖ * ‖X (peterWeylVec α')‖ := norm_inner_le_norm _ _
    _ ≤ ‖peterWeylVec α‖ * (‖X‖ * ‖peterWeylVec α'‖) :=
        mul_le_mul_of_nonneg_left (X.le_opNorm _) (norm_nonneg _)
    _ = ‖X‖ := by rw [hunit, hunit, one_mul, mul_one]
def sandwichTerm (β : ℝ) (X : HaarL2 B →L[ℂ] HaarL2 B) (u u' : B → specialUnitary)
    (p : PeterWeylIndex B × PeterWeylIndex B) : ℂ :=
  (sqrtPeterWeylCoeff β p.1 : ℂ) * (sqrtPeterWeylCoeff β p.2 : ℂ) *
    peterWeylEntry X p.1 p.2 * peterWeylFn p.1 u * star (peterWeylFn p.2 u')
def sandwichTermBound (β : ℝ) (X : HaarL2 B →L[ℂ] HaarL2 B)
    (p : PeterWeylIndex B × PeterWeylIndex B) : ℝ :=
  sqrtPeterWeylCoeff β p.1 * sqrtPeterWeylCoeff β p.2 *
    ‖peterWeylEntry X p.1 p.2‖ * ‖peterWeylFn p.1‖ * ‖peterWeylFn p.2‖
omit [Finite B] in
theorem sqrtPeterWeylCoeff_nonneg (α : PeterWeylIndex B) : 0 ≤ sqrtPeterWeylCoeff β α :=
  Real.sqrt_nonneg _
theorem summable_sandwichTermBound
    (hunit : ∀ α : PeterWeylIndex B, ‖peterWeylVec α‖ = 1)
    (hs : Summable fun α : PeterWeylIndex B => sqrtPeterWeylCoeff β α * ‖peterWeylFn α‖)
    (X : HaarL2 B →L[ℂ] HaarL2 B) : Summable (sandwichTermBound β X) := by
  have hnn : ∀ α : PeterWeylIndex B, 0 ≤ sqrtPeterWeylCoeff β α * ‖peterWeylFn α‖ :=
    fun α => mul_nonneg (sqrtPeterWeylCoeff_nonneg α) (norm_nonneg _)
  have hprod := (Summable.mul_of_nonneg hs hs hnn hnn).mul_left ‖X‖
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hprod
  · unfold sandwichTermBound
    have := sqrtPeterWeylCoeff_nonneg (β := β) p.1
    have := sqrtPeterWeylCoeff_nonneg (β := β) p.2
    positivity
  · have hM := norm_peterWeylEntry_le hunit X p.1 p.2
    have hq : 0 ≤ sqrtPeterWeylCoeff β p.1 * ‖peterWeylFn p.1‖ *
        (sqrtPeterWeylCoeff β p.2 * ‖peterWeylFn p.2‖) := mul_nonneg (hnn _) (hnn _)
    calc sandwichTermBound β X p
        = ‖peterWeylEntry X p.1 p.2‖ * (sqrtPeterWeylCoeff β p.1 * ‖peterWeylFn p.1‖ *
            (sqrtPeterWeylCoeff β p.2 * ‖peterWeylFn p.2‖)) := by
          unfold sandwichTermBound; ring
      _ ≤ ‖X‖ * (sqrtPeterWeylCoeff β p.1 * ‖peterWeylFn p.1‖ *
            (sqrtPeterWeylCoeff β p.2 * ‖peterWeylFn p.2‖)) :=
          mul_le_mul_of_nonneg_right hM hq
theorem norm_sandwichTerm_le (X : HaarL2 B →L[ℂ] HaarL2 B)
    (u u' : B → specialUnitary) (p : PeterWeylIndex B × PeterWeylIndex B) :
    ‖sandwichTerm β X u u' p‖ ≤ sandwichTermBound β X p := by
  have h₁ := (peterWeylFn p.1).norm_coe_le_norm u
  have h₂ := (peterWeylFn p.2).norm_coe_le_norm u'
  have r₁ := sqrtPeterWeylCoeff_nonneg (β := β) p.1
  have r₂ := sqrtPeterWeylCoeff_nonneg (β := β) p.2
  unfold sandwichTerm sandwichTermBound
  simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r₁,
    abs_of_nonneg r₂]
  gcongr
theorem hasSum_sandwichTerm
    (hS : ∀ u : B → specialUnitary, HasSum (fun α : PeterWeylIndex B =>
        ((sqrtPeterWeylCoeff β α : ℂ) * star (peterWeylFn α u)) • peterWeylVec α)
      (sqrtLinkKernelSlice β u))
    (X : HaarL2 B →L[ℂ] HaarL2 B)
    (hsum : Summable (sandwichTermBound β X)) (u u' : B → specialUnitary) :
    HasSum (sandwichTerm β X u u') (sqrtKernelSandwich β X u u') := by
  have hT : Summable (sandwichTerm β X u u') :=
    Summable.of_norm_bounded hsum (norm_sandwichTerm_le X u u')
  set y := X (sqrtLinkKernelSlice β u') with hy
  have fiber : ∀ α : PeterWeylIndex B, HasSum (fun α' => sandwichTerm β X u u' (α, α'))
      ((sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α u * inner ℂ (peterWeylVec α) y) := by
    intro α
    have h := (((innerSL ℂ (peterWeylVec α)).comp X).hasSum (hS u')).mul_left
      ((sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α u)
    have hfun : (fun α' => sandwichTerm β X u u' (α, α')) = fun α' =>
        (sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α u *
          ((innerSL ℂ (peterWeylVec α)).comp X)
            (((sqrtPeterWeylCoeff β α' : ℂ) * star (peterWeylFn α' u')) •
              peterWeylVec α') := by
      funext α'
      change _ = (sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α u *
        inner ℂ (peterWeylVec α) (X (((sqrtPeterWeylCoeff β α' : ℂ) *
          star (peterWeylFn α' u')) • peterWeylVec α'))
      rw [map_smul, inner_smul_right]
      simp only [sandwichTerm, peterWeylEntry]
      ring
    rw [hfun]
    exact h
  have h₁ := hT.hasSum.prod_fiberwise fiber
  have h₂ : HasSum (fun α : PeterWeylIndex B => (sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α u *
      inner ℂ (peterWeylVec α) y) (sqrtKernelSandwich β X u u') := by
    have h := ((innerSL ℂ y).hasSum (hS u)).star
    have hfun : (fun α : PeterWeylIndex B => (sqrtPeterWeylCoeff β α : ℂ) * peterWeylFn α u *
        inner ℂ (peterWeylVec α) y) = fun α => star (innerSL ℂ y
          (((sqrtPeterWeylCoeff β α : ℂ) * star (peterWeylFn α u)) •
            peterWeylVec α)) := by
      funext α
      change _ = star (inner ℂ y (((sqrtPeterWeylCoeff β α : ℂ) *
        star (peterWeylFn α u)) • peterWeylVec α))
      have hc : star (inner ℂ y (peterWeylVec α) : ℂ) = inner ℂ (peterWeylVec α) y :=
        inner_conj_symm _ _
      have hr : star (sqrtPeterWeylCoeff β α : ℂ) = sqrtPeterWeylCoeff β α :=
        Complex.conj_ofReal _
      rw [inner_smul_right, star_mul', star_mul', hc, star_star, hr]
    have hv : sqrtKernelSandwich β X u u' = star (innerSL ℂ y (sqrtLinkKernelSlice β u)) :=
      (inner_conj_symm _ _).symm
    rw [hfun, hv]
    exact h
  rw [← h₁.unique h₂]
  exact hT.hasSum
theorem singleBondWeight_one : InfiniteLattice.singleBondWeight β (1 : specialUnitary) = 1 := by
  simp [InfiniteLattice.singleBondWeight, fullTrace]
theorem norm_sqrtLinkKernelSlice
    (hone : ∀ u u' : B → specialUnitary, sqrtKernelSandwich β 1 u u' = linkProductKernel β u u')
    (u : B → specialUnitary) : ‖sqrtLinkKernelSlice β u‖ = 1 := by
  have h₁ : linkProductKernel β u u = 1 := by
    have hb : ∀ b, InfiniteLattice.singleBondWeight β (u b * (u b)⁻¹) = 1 := fun b => by
      rw [mul_inv_cancel, singleBondWeight_one]
    simp only [linkProductKernel, hb, finprod_one]
  have h₂ : inner ℂ (sqrtLinkKernelSlice β u) (sqrtLinkKernelSlice β u) = (1 : ℂ) := by
    rw [← h₁, ← hone]
    rfl
  have h₃ := norm_sq_eq_re_inner (𝕜 := ℂ) (sqrtLinkKernelSlice β u)
  rw [h₂] at h₃
  have h₄ : ‖sqrtLinkKernelSlice β u‖ ^ 2 = 1 := by simpa using h₃
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h₄
theorem sandwichKernelBounded (hroot : SqrtLinkKernelFacts)
    (hseveral : SeveralVariables.SeveralVariablesFacts)
    (hlinear : SandwichKernelLinearStatement) : SandwichKernelBoundedStatement := by
  intro β hβ B _ _ X
  obtain ⟨⟨-, -, hc⟩, ⟨-, hser, -⟩, ⟨-, hb⟩, -⟩ := (hroot β hβ).1 B
  have hunit : ∀ α : PeterWeylIndex B, ‖peterWeylVec α‖ = 1 :=
    (hseveral B (fun _ => ⟨0⟩) ⟨0⟩).1.1.1
  have hS := hasSum_sqrtLinkKernelSlice hc hser
  have hs := summable_sqrtPeterWeylCoeff_mul_norm hunit (hb (1 / 2) (by norm_num))
  have hsum := summable_sandwichTermBound hunit hs X
  have hu := norm_sqrtLinkKernelSlice (hlinear β hβ B).2.1
  refine ⟨hu, ?_, fun u u' => ?_, hasSum_sandwichTerm hS X hsum, hsum⟩
  · have hfun : (fun p : (B → specialUnitary) × (B → specialUnitary) => sqrtKernelSandwich β X p.1 p.2) =
        fun p => ∑' q, sandwichTerm β X p.1 p.2 q :=
      funext fun p => (hasSum_sandwichTerm hS X hsum p.1 p.2).tsum_eq.symm
    rw [hfun]
    refine continuous_tsum (fun q => ?_) hsum fun q p => norm_sandwichTerm_le X p.1 p.2 q
    exact (continuous_const.mul ((peterWeylFn q.1).continuous.comp continuous_fst)).mul
      (continuous_star.comp ((peterWeylFn q.2).continuous.comp continuous_snd))
  · calc ‖sqrtKernelSandwich β X u u'‖
        ≤ ‖sqrtLinkKernelSlice β u‖ * ‖X (sqrtLinkKernelSlice β u')‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖sqrtLinkKernelSlice β u‖ * (‖X‖ * ‖sqrtLinkKernelSlice β u'‖) :=
          mul_le_mul_of_nonneg_left (X.le_opNorm _) (norm_nonneg _)
      _ = ‖X‖ := by rw [hu, hu, one_mul, mul_one]
end YangMills.Construction.TransferOperators.SandwichKernelBounds
end
