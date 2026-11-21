import YangMills.Construction.TransferOperators.MultiplicationByABoundedFunctionOnAPowerOfG
import YangMills.Construction.TransferOperators.PeriodicStatesHaarMeasureCubicLatticesAndIntegralOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory ComplexConjugate
open YangMills.Construction.SpinHarmonics (HaarL2)
open YangMills.Construction.Matrices.ComplexMatrix2 (specialUnitary haarPi)
open YangMills.Construction.TransferOperators.GibbsHaarKernels (HaarPiInvariance)
noncomputable section
namespace YangMills.Construction.TransferOperators.BoundedMultiplication
section Operators
variable {ι : Type} [Finite ι] {f : (ι → specialUnitary) → ℂ}
  {A : HaarL2 ι →L[ℂ] HaarL2 ι}
theorem eq_ofReal_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext rfl (by simp [hz])
theorem memLp_mul_of_norm_le_one (hf : Continuous f) (hle : ∀ u, ‖f u‖ ≤ 1) (φ : HaarL2 ι) :
    MemLp (fun u => f u * (φ : (ι → specialUnitary) → ℂ) u) 2 (haarPi ι) :=
  (Lp.memLp φ).of_le_mul (c := 1) (hf.aestronglyMeasurable.mul (Lp.aestronglyMeasurable φ))
    (Filter.Eventually.of_forall fun u => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hle u) (norm_nonneg _))
def mulOp (hf : Continuous f) (hle : ∀ u, ‖f u‖ ≤ 1) :
    HaarL2 ι →L[ℂ] HaarL2 ι :=
  LinearMap.mkContinuous
    { toFun := fun φ => (memLp_mul_of_norm_le_one hf hle φ).toLp _
      map_add' := fun φ ψ => by
        refine Lp.ext ?_
        filter_upwards [(memLp_mul_of_norm_le_one hf hle (φ + ψ)).coeFn_toLp, Lp.coeFn_add φ ψ,
          Lp.coeFn_add ((memLp_mul_of_norm_le_one hf hle φ).toLp _)
            ((memLp_mul_of_norm_le_one hf hle ψ).toLp _),
          (memLp_mul_of_norm_le_one hf hle φ).coeFn_toLp,
          (memLp_mul_of_norm_le_one hf hle ψ).coeFn_toLp] with u e₁ e₂ e₃ e₄ e₅
        rw [e₁, e₃, Pi.add_apply, e₄, e₅, e₂, Pi.add_apply, mul_add]
      map_smul' := fun c φ => by
        refine Lp.ext ?_
        filter_upwards [(memLp_mul_of_norm_le_one hf hle (c • φ)).coeFn_toLp, Lp.coeFn_smul c φ,
          Lp.coeFn_smul c ((memLp_mul_of_norm_le_one hf hle φ).toLp _),
          (memLp_mul_of_norm_le_one hf hle φ).coeFn_toLp] with u e₁ e₂ e₃ e₄
        simp only [RingHom.id_apply]
        rw [e₁, e₃, Pi.smul_apply, e₄, e₂, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
    1 fun φ => Lp.norm_le_mul_norm_of_ae_le_mul (by
      filter_upwards [(memLp_mul_of_norm_le_one hf hle φ).coeFn_toLp] with u hu
      show ‖((memLp_mul_of_norm_le_one hf hle φ).toLp _ : (ι → specialUnitary) → ℂ) u‖ ≤ _
      rw [hu, norm_mul]
      exact mul_le_mul_of_nonneg_right (hle u) (norm_nonneg _))
theorem isMultiplicationOp_mulOp (hf : Continuous f) (hle : ∀ u, ‖f u‖ ≤ 1) :
    IsMultiplicationOp f (mulOp hf hle) :=
  fun φ => (memLp_mul_of_norm_le_one hf hle φ).coeFn_toLp
theorem isSymmetricOp_of_real_mul (him : ∀ u, (f u).im = 0)
    (hA : IsMultiplicationOp f A) : IsSymmetricOp A := by
  intro φ ψ
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hA φ, hA ψ] with u e₁ e₂
  have hc : conj (f u) = f u := Complex.conj_eq_iff_im.2 (him u)
  rw [e₁, e₂]
  simp only [RCLike.inner_apply, map_mul, hc]
  ring
theorem isPositiveOp_of_nonneg_mul (him : ∀ u, (f u).im = 0)
    (hpos : ∀ u, 0 ≤ (f u).re) (hA : IsMultiplicationOp f A) : IsPositiveOp A := by
  refine ⟨isSymmetricOp_of_real_mul him hA, fun φ => ?_⟩
  have hinner : (inner ℂ φ (A φ) : ℂ) =
      ((∫ u, (f u).re * ‖(φ : (ι → specialUnitary) → ℂ) u‖ ^ 2 ∂haarPi ι : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hA φ] with u hu
    have hf := eq_ofReal_re_of_im_eq_zero (him u)
    have hsq : (φ : (ι → specialUnitary) → ℂ) u * conj ((φ : (ι → specialUnitary) → ℂ) u) =
        ((‖(φ : (ι → specialUnitary) → ℂ) u‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    rw [hu, RCLike.inner_apply]
    push_cast
    linear_combination (f u) * hsq + ((‖(φ : (ι → specialUnitary) → ℂ) u‖ : ℝ) : ℂ) ^ 2 * hf
  rw [hinner]
  exact ⟨by
    rw [Complex.ofReal_re]
    exact integral_nonneg fun u => mul_nonneg (hpos u) (sq_nonneg _), Complex.ofReal_im _⟩
theorem opNorm_le_one_of_mul (hle : ∀ u, ‖f u‖ ≤ 1) (hA : IsMultiplicationOp f A) :
    ‖A‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ =>
    Lp.norm_le_mul_norm_of_ae_le_mul (by
      filter_upwards [hA φ] with u hu
      rw [hu, norm_mul]
      exact mul_le_mul_of_nonneg_right (hle u) (norm_nonneg _))
theorem isMultiplicationOp_one_sub (hA : IsMultiplicationOp f A) :
    IsMultiplicationOp (fun u => 1 - f u) (1 - A) := by
  intro φ
  have hsub : (1 - A) φ = φ - A φ := rfl
  rw [hsub]
  filter_upwards [Lp.coeFn_sub φ (A φ), hA φ] with u e₁ e₂
  rw [e₁, Pi.sub_apply, e₂]
  ring
theorem mul_comm_of_invariant (hH : HaarPiInvariance ι) (hA : IsMultiplicationOp f A)
    {V : Type} {s r : ι → V} {g : V → specialUnitary}
    {B : HaarL2 ι →L[ℂ] HaarL2 ι} (hB : IsTwistedTranslation s r g B)
    (hinv : ∀ u, f (twistedConjAction s r g⁻¹ u) = f u) : A * B = B * A := by
  have hmp : MeasurePreserving (twistedConjAction s r g⁻¹) (haarPi ι)
      (haarPi ι) := hH.1 (fun b => g⁻¹ (s b)) fun b => (g⁻¹ (r b))⁻¹
  refine ContinuousLinearMap.ext fun φ => Lp.ext ?_
  have hlhs : (A (B φ) : (ι → specialUnitary) → ℂ) =ᵐ[haarPi ι]
      fun u => f u * (φ : (ι → specialUnitary) → ℂ) (twistedConjAction s r g⁻¹ u) := by
    filter_upwards [hA (B φ), hB φ] with u e₁ e₂
    rw [e₁, e₂]
  have hrhs : (B (A φ) : (ι → specialUnitary) → ℂ) =ᵐ[haarPi ι]
      fun u => f u * (φ : (ι → specialUnitary) → ℂ) (twistedConjAction s r g⁻¹ u) := by
    refine (hB (A φ)).trans ((hmp.quasiMeasurePreserving.ae_eq_comp (hA φ)).trans
      (Filter.Eventually.of_forall fun u => ?_))
    simp only [Function.comp_apply]
    rw [hinv]
  exact hlhs.trans hrhs.symm
end Operators
theorem boundedMultiplicationStatement_of_gibbsHaarKernels
    (hS : GibbsHaarKernels.Statement) : BoundedMultiplicationStatement := by
  intro ι _ _ f hf hrange
  have hH : HaarPiInvariance ι := hS.2.1 ι
  have him : ∀ u, (f u).im = 0 := fun u => (hrange u).1
  have hle : ∀ u, ‖f u‖ ≤ 1 := fun u => by
    rw [eq_ofReal_re_of_im_eq_zero (him u), Complex.norm_real, Real.norm_of_nonneg (hrange u).2.1]
    exact (hrange u).2.2
  refine ⟨⟨_, isMultiplicationOp_mulOp hf hle⟩, fun A hA => ?_⟩
  refine ⟨isPositiveOp_of_nonneg_mul him (fun u => (hrange u).2.1) hA, ?_,
    opNorm_le_one_of_mul hle hA, fun V s r g B hB hinv =>
      mul_comm_of_invariant hH hA hB hinv⟩
  refine isPositiveOp_of_nonneg_mul (fun u => ?_) (fun u => ?_)
    (isMultiplicationOp_one_sub hA)
  · simp [him u]
  · simpa using (hrange u).2.2
end YangMills.Construction.TransferOperators.BoundedMultiplication
end
