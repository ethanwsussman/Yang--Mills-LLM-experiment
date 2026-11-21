import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.PeriodicOperators.TransposeOfAProductOfKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TransposeComp
theorem kernelDomain_weight_pos (hQ : Quotients.QuotientTransposeNorm) :
    ∀ (D : KernelDomain) (d : D.Elem), 0 < D.weight d
  | .lattice _ hP, x => hP.weight_pos _
  | .quot P hP t ht, q => by
    obtain ⟨x, rfl⟩ := Quot.exists_rep q
    have hq : P.quotWeight t (P.mkQuot t x) = P.weightOf x :=
      ((hQ P P hP hP t ht).2.1 t (Or.inr rfl)).1.2 x
    have hx : 0 < P.weightOf x := hP.weight_pos _
    show 0 < P.quotWeight t (P.mkQuot t x)
    rw [hq]
    exact hx
theorem wTranspose_mul_wTranspose (hQ : Quotients.QuotientTransposeNorm)
    (D D' D'' : KernelDomain) (U : D'.Elem → D.Elem → ℂ) (V : D.Elem → D''.Elem → ℂ)
    (y' : D'.Elem) (y'' : D''.Elem) (y : D.Elem) :
    wTranspose D''.weight D.weight V y'' y * wTranspose D.weight D'.weight U y y' =
      ((D'.weight y' / D''.weight y'' : ℝ) : ℂ) * (U y' y * V y y'') := by
  have hy : ((D.weight y : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (kernelDomain_weight_pos hQ D y).ne'
  have hy'' : ((D''.weight y'' : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (kernelDomain_weight_pos hQ D'' y'').ne'
  simp only [wTranspose]
  push_cast
  field_simp
theorem claim_holds (hQ : Quotients.QuotientTransposeNorm) : Claim := by
  intro D D' D'' U V hUV
  refine ⟨fun y'' y' => ?_, ?_⟩
  · have hs := (hUV y' y'').mul_left ‖((D'.weight y' / D''.weight y'' : ℝ) : ℂ)‖
    refine hs.congr fun y => ?_
    rw [wTranspose_mul_wTranspose hQ]
    exact (norm_mul _ _).symm
  · funext y'' y'
    show ∑' y, wTranspose D''.weight D.weight V y'' y * wTranspose D.weight D'.weight U y y' =
      wTranspose D''.weight D'.weight (compKernel U V) y'' y'
    simp_rw [wTranspose_mul_wTranspose hQ, tsum_mul_left]
    rfl
end YangMills.Construction.PeriodicOperators.TransposeComp
end
