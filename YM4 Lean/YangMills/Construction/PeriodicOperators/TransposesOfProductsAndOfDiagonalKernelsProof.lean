import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNormProof
import YangMills.Construction.PeriodicOperators.TransposesOfProductsAndOfDiagonalKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TransposeCompDiagProof
theorem quotWeight_mkQuot (P : PeriodicData) (hP : IsPeriodic P) (s : ℕ) (x : P.Carrier) :
    P.quotWeight s (P.mkQuot s x) = P.weightOf x := by apply _root_.YangMills.Construction.PeriodicOperators.Quotients.quotWeight_mkQuot <;> assumption
theorem kernelDomain_weight_pos : ∀ (D : KernelDomain) (a : D.Elem), 0 < D.weight a
  | .lattice _ hP, x => hP.weight_pos _
  | .quot P hP s _, c => by
    obtain ⟨x, rfl⟩ := Quot.exists_rep c
    have hw := quotWeight_mkQuot P hP s x
    have hpos : 0 < P.weightOf x := hP.weight_pos _
    show 0 < P.quotWeight s (P.mkQuot s x)
    rw [hw]
    exact hpos
theorem kernelDomain_weight_ne_zero (D : KernelDomain) (a : D.Elem) :
    ((D.weight a : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (kernelDomain_weight_pos D a).ne'
theorem wTranspose_mul_wTranspose (D D' D'' : KernelDomain) (K : D'.Elem → D.Elem → ℂ)
    (K' : D.Elem → D''.Elem → ℂ) (y' : D'.Elem) (y'' : D''.Elem) (y : D.Elem) :
    wTranspose D''.weight D.weight K' y'' y * wTranspose D.weight D'.weight K y y' =
      ((D'.weight y' / D''.weight y'' : ℝ) : ℂ) * (K y' y * K' y y'') := by
  have h := kernelDomain_weight_ne_zero D y
  have h'' := kernelDomain_weight_ne_zero D'' y''
  simp only [wTranspose]
  push_cast
  field_simp
theorem wTranspose_diag (D : KernelDomain) (K : D.Elem → D.Elem → ℂ) (y : D.Elem) :
    wTranspose D.weight D.weight K y y = K y y := by
  have h := (kernelDomain_weight_pos D y).ne'
  simp [wTranspose, div_self h]
theorem transposeCompDiag_holds : TransposeCompDiag := by
  refine ⟨fun D D' D'' K K' hfin => ⟨fun y'' y' => ?_, ?_⟩, fun D K => ⟨wTranspose_diag D K, ?_, ?_⟩⟩
  · refine (hfin y' y'').subset fun y hy => ?_
    have hterm : wTranspose D''.weight D.weight K' y'' y * wTranspose D.weight D'.weight K y y' ≠ 0 := hy
    rw [wTranspose_mul_wTranspose] at hterm
    exact right_ne_zero_of_mul hterm
  · funext y'' y'
    show wTranspose D''.weight D'.weight (compKernel K K') y'' y' =
      ∑' y, wTranspose D''.weight D.weight K' y'' y * wTranspose D.weight D'.weight K y y'
    simp_rw [wTranspose_mul_wTranspose, tsum_mul_left]
    rfl
  · intro hoff
    funext y y'
    by_cases h : y' = y
    · subst h
      exact wTranspose_diag D K y'
    · simp [wTranspose, hoff y' y h, hoff y y' (Ne.symm h)]
  · intro _
    exact Finset.sum_congr rfl fun y _ => wTranspose_diag D K y
end YangMills.Construction.PeriodicOperators.TransposeCompDiagProof
end
