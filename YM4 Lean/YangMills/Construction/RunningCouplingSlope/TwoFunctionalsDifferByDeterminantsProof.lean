import YangMills.Construction.RunningCouplingSlope.DeterminantSandwichAndNeighborhood
import YangMills.Construction.RunningCouplingSlope.SoftSaddleIsTheMixedSaddle
import YangMills.Construction.RunningCouplingSlope.TopDeterminantsAtOneProof
import YangMills.Construction.RunningCouplingSlope.TwoFunctionalsDifferByDeterminants
import YangMills.Construction.RunningCouplingSlope.GhostOfTheSoftChainIsTheMixedGhost
import YangMills.Construction.RunningCouplingSlope.SaddlesOfTheBackgroundGaugeInTheScaledPicture
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
section Blocks
variable {I T : Type} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
private theorem det_mixedSaddle_schur (A : Matrix I I ℂ) (Bu B : Matrix T I ℂ) (Ct C : Matrix I T ℂ)
    (G : Matrix T T ℂ) (h : det A ≠ 0) :
    det (fromBlocks (A - C * B) Ct Bu (-G)) =
      det A * det (fromBlocks (-G - Bu * A⁻¹ * Ct) (-(Bu * A⁻¹ * C)) (-(B * A⁻¹ * Ct))
        (1 - B * A⁻¹ * C)) := by apply _root_.YangMills.SharedProofs.p321 <;> assumption
private theorem det_symmetricSaddle_schur (A : Matrix I I ℂ) (B : Matrix T I ℂ) (C : Matrix I T ℂ)
    (h : det A ≠ 0) :
    det (fromBlocks (A - C * B) C B (0 : Matrix T T ℂ)) = det A * det (-(B * A⁻¹ * C)) := by apply _root_.YangMills.SharedProofs.p73231 <;> assumption
private theorem det_twoMapSaddle_schur (D : Matrix I I ℂ) (Su S : Matrix T I ℂ) (St : Matrix I T ℂ)
    (h : det (D + St * S) ≠ 0) :
    det (fromBlocks D St Su (0 : Matrix T T ℂ)) =
      det (D + St * S) * det (-(Su * (D + St * S)⁻¹ * St)) := by apply _root_.YangMills.SharedProofs.p13006 <;> assumption
private theorem norm_det_neg_eq (A : Matrix T T ℂ) : ‖det (-A)‖ = ‖det A‖ := by
  rw [det_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
end Blocks
variable {L n k : ℕ}
private theorem matrixOf_X_eq [Fintype (Fin 3 × PositiveEdge L n k k)] (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Matrix.of (rescaledOperators L n k U).X =
      Matrix.of (rescaledOperators L n k U).Xi -
        Matrix.of (rescaledOperators L n k U).Qt * Matrix.of (rescaledOperators L n k U).Q := by
  ext i j
  simp [Tower.RescaledOperators.X, PeriodicOperators.compKernel, Matrix.mul_apply, tsum_fintype]
private theorem matrixOf_Y_eq [Fintype (Fin 3 × Vertex L n k k)] (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Matrix.of (rescaledOperators L n k U).Y =
      Matrix.of (rescaledOperators L n k U).Delta +
        Matrix.of (rescaledOperators L n k U).Rt * Matrix.of (rescaledOperators L n k U).R := by
  ext i j
  simp [Tower.RescaledOperators.Y, PeriodicOperators.compKernel, Matrix.mul_apply, tsum_fintype]
private theorem matrixOf_saddleX_eq (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Matrix.of (rescaledOperators L n k U).saddleX =
      fromBlocks (Matrix.of (rescaledOperators L n k U).X) (Matrix.of (rescaledOperators L n k U).Qt)
        (Matrix.of (rescaledOperators L n k U).Q) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Tower.RescaledOperators.saddleX, PeriodicOperators.saddleMatrix]
private theorem matrixOf_saddleDelta_eq (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Matrix.of (rescaledOperators L n k U).saddleDelta =
      fromBlocks (Matrix.of (rescaledOperators L n k U).Delta) (Matrix.of (rescaledOperators L n k U).Rt)
        (Matrix.of (rescaledOperators L n k U).R) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Tower.RescaledOperators.saddleDelta, PeriodicOperators.saddleMatrix]
theorem functionalDifferenceIsTopDeterminants_of_parts
    (h₁ : QuietSaddleDetEqSaddleMatrixDet)
    (h₂ : GhostDeterminantAtQuietPoint)
    (h₃ : BackgroundGaugeSaddleDeterminants) :
    FunctionalDifferenceIsTopDeterminants := by
  intro a ha L hL k n hk hn _ _ _ _ _ _ _ _
  obtain ⟨c₁, hc₁, e₁⟩ := h₁ a ha L hL k n hk hn
  obtain ⟨c₂, hc₂, e₂⟩ := h₂ L hL k n hk hn
  obtain ⟨c₃, c₄, hc₃, hc₄, e₃⟩ := h₃ L hL k n hk hn
  refine ⟨-(1 / 2) * Real.log c₁ + Real.log c₂ + 1 / 2 * Real.log c₃ - Real.log c₄, ?_⟩
  unfold Tower.EventuallyNearIdentity at e₁ e₂ e₃ ⊢
  filter_upwards [e₁, e₂, e₃] with U f₁ f₂ f₃
  obtain ⟨f₃, f₃'⟩ := f₃
  rintro ⟨dN, dC, dRu, dR⟩
  letI : Nonempty (PositiveEdge L n k k) :=
    ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, 0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩
  letI : Nonempty (Vertex L n k k) := ⟨0⟩
  set p := rescaledOperators L n k U with hp
  have dXi : det (Matrix.of p.Xi) ≠ 0 :=
    DirectDeterminants.det_ne_zero_of_inverse_sandwich
      (Matrix.of p.Xi) (Matrix.of p.Q) (Matrix.of p.Qt) dC
  have dY : det (Matrix.of p.Y) ≠ 0 :=
    DirectDeterminants.det_ne_zero_of_inverse_sandwich
      (Matrix.of p.Y) (Matrix.of p.R) (Matrix.of p.Rt) dR
  have mix : ‖det (RunningCouplingSlope.saddleMatrix a U)‖ =
      ‖det (Matrix.of p.Xi)‖ * ‖det (noiseBlockMatrix a U)‖ := by
    have := det_mixedSaddle_schur (Matrix.of p.Xi) (Matrix.of (meanKernelQ L n k U)) (Matrix.of p.Q)
      (meanQTranspose L n k U) (Matrix.of p.Qt) (Matrix.of (noiseCovariance a L n k U k)) dXi
    rw [← matrixOf_X_eq] at this
    rw [RunningCouplingSlope.saddleMatrix, ← hp, this, norm_mul]
    rfl
  have sX : ‖det (Matrix.of p.saddleX)‖ =
      ‖det (Matrix.of p.Xi)‖ * ‖det (topCovariance U)‖ := by
    have := det_symmetricSaddle_schur (Matrix.of p.Xi) (Matrix.of p.Q) (Matrix.of p.Qt) dXi
    rw [← matrixOf_X_eq] at this
    rw [matrixOf_saddleX_eq, ← hp, this, norm_mul, norm_det_neg_eq]
    rfl
  have gh : ‖det (ghostMatrix U)‖ = ‖det (Matrix.of p.Y)‖ *
      ‖det (Matrix.of (meanKernelR L n k U) * yInv U * Matrix.of p.Rt)‖ := by
    have := det_twoMapSaddle_schur (Matrix.of p.Delta) (Matrix.of (meanKernelR L n k U)) (Matrix.of p.R)
      (Matrix.of p.Rt) (by rw [← matrixOf_Y_eq]; exact dY)
    rw [← matrixOf_Y_eq] at this
    rw [ghostMatrix, ← hp, this, norm_mul, norm_det_neg_eq]
    rfl
  have sD : ‖det (Matrix.of p.saddleDelta)‖ = ‖det (Matrix.of p.Y)‖ *
      ‖det (Matrix.of p.R * yInv U * Matrix.of p.Rt)‖ := by
    have := det_twoMapSaddle_schur (Matrix.of p.Delta) (Matrix.of p.R) (Matrix.of p.R)
      (Matrix.of p.Rt) (by rw [← matrixOf_Y_eq]; exact dY)
    rw [← matrixOf_Y_eq] at this
    rw [matrixOf_saddleDelta_eq, ← hp, this, norm_mul, norm_det_neg_eq]
    rfl
  have pXi : ‖det (Matrix.of p.Xi)‖ ≠ 0 := norm_ne_zero_iff.2 dXi
  have pY : ‖det (Matrix.of p.Y)‖ ≠ 0 := norm_ne_zero_iff.2 dY
  have pN : ‖det (noiseBlockMatrix a U)‖ ≠ 0 := norm_ne_zero_iff.2 dN
  have pC : ‖det (topCovariance U)‖ ≠ 0 := norm_ne_zero_iff.2 dC
  have pRu := norm_ne_zero_iff.2 dRu
  have pR := norm_ne_zero_iff.2 dR
  have l₁ : Real.log |levelSaddleDet (gaugedOperator a (quietPoint U) 0 0)
      (shiftedGaugeMap (quietPoint U))| = Real.log c₁ + 3 * logRadiusSum (quietPoint U) +
        Real.log ‖det (Matrix.of p.Xi)‖ + Real.log ‖det (noiseBlockMatrix a U)‖ := by
    rw [f₁, mix, Real.log_mul (by positivity) (mul_ne_zero pXi pN), Real.log_mul hc₁.ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_mul pXi pN]
    ring
  have l₂ : Real.log |LinearMap.det (ghostBlockOperator (quietPoint U))| = Real.log c₂ +
      Real.log ‖det (Matrix.of p.Y)‖ +
      Real.log ‖det (Matrix.of (meanKernelR L n k U) * yInv U * Matrix.of p.Rt)‖ := by
    rw [f₂, gh, Real.log_mul hc₂.ne' (mul_ne_zero pY pRu), Real.log_mul pY pRu]
    ring
  have l₃ : Real.log |hessianSaddleDet U 0 0| = Real.log c₃ +
      Real.log ‖det (Matrix.of p.Xi)‖ + Real.log ‖det (topCovariance U)‖ := by
    rw [f₃, sX, Real.log_mul hc₃.ne' (mul_ne_zero pXi pC), Real.log_mul pXi pC]
    ring
  have l₄ : Real.log |ghostSaddleDet L n k U| = Real.log c₄ +
      Real.log ‖det (Matrix.of p.Y)‖ +
      Real.log ‖det (Matrix.of p.R * yInv U * Matrix.of p.Rt)‖ := by
    rw [f₃', sD, Real.log_mul hc₄.ne' (mul_ne_zero pY pR), Real.log_mul pY pR]
    ring
  simp only [chainMinusBackground, chainFreeEnergy, backgroundFunctional, topLogDeterminants]
  rw [l₁, l₂, l₃, l₄]
  ring
end YangMills.Construction.RunningCouplingSlope
end
