import YangMills.Construction.TransferOperators.AlgebraOfATransferOperatorOnAPowerOfG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open SpinHarmonics
namespace TransferOperators
theorem transferAlgebraStatement_proof : TransferAlgebraStatement := by
  intro J _ c R P M hR hP hPP hRP hM hM1 hMP hc hc2 hc1
  have hmul : ∀ (A B : HaarL2 J →L[ℂ] HaarL2 J) (x : HaarL2 J),
      (A * B) x = A (B x) := fun _ _ _ => rfl
  have hRsymm : ∀ φ ψ : HaarL2 J, inner ℂ φ (R ψ) = inner ℂ (R φ) ψ := hR
  have hPsymm : ∀ φ ψ : HaarL2 J, inner ℂ φ (P ψ) = inner ℂ (P φ) ψ := hP
  have hMsymm : ∀ φ ψ : HaarL2 J, inner ℂ φ (M ψ) = inner ℂ (M φ) ψ := hM.1
  have hPnorm : ∀ x : HaarL2 J, ‖P x‖ ≤ ‖x‖ := by
    intro x
    have hidem : P (P x) = P x := by rw [← hmul, hPP]
    have hin : inner ℂ (P x) (P x) = inner ℂ x (P x) := by
      rw [← hPsymm x (P x), hidem]
    have hsq : ‖P x‖ * ‖P x‖ ≤ ‖x‖ * ‖P x‖ := by
      calc ‖P x‖ * ‖P x‖ = RCLike.re (inner ℂ (P x) (P x) : ℂ) :=
            (inner_self_eq_norm_mul_norm (P x)).symm
        _ = RCLike.re (inner ℂ x (P x) : ℂ) := by rw [hin]
        _ ≤ ‖(inner ℂ x (P x) : ℂ)‖ := RCLike.re_le_norm _
        _ ≤ ‖x‖ * ‖P x‖ := norm_inner_le_norm x (P x)
    rcases (norm_nonneg (P x)).eq_or_lt with h0 | hpos
    · rw [← h0]; exact norm_nonneg x
    · exact le_of_mul_le_mul_right hsq hpos
  have hS : ∀ φ ψ : HaarL2 J, inner ℂ φ ((R * P) ψ) = inner ℂ ((R * P) φ) ψ := by
    intro φ ψ
    rw [hmul, hRsymm, hPsymm, ← hmul, ← hRP]
  have hSnorm : ∀ α, ‖(R * P) (peterWeylVec α)‖ ≤ c α := by
    intro α
    rw [hRP, hmul]
    exact (hPnorm _).trans (hc α)
  have hc0 : ∀ α, 0 ≤ c α := fun α => (norm_nonneg _).trans (hSnorm α)
  have hMnorm : ∀ x : HaarL2 J, ‖M x‖ ≤ ‖x‖ := by
    intro x
    calc ‖M x‖ ≤ ‖M‖ * ‖x‖ := M.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hM1 (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hMSnorm : ∀ α, ‖(M * (R * P)) (peterWeylVec α)‖ ≤ c α := by
    intro α
    rw [hmul]
    exact (hMnorm _).trans (hSnorm α)
  have hHS : IsHilbertSchmidtPW (R * P) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun α => pow_le_pow_left₀ (norm_nonneg _) (hSnorm α) 2) hc2
  have hMHS : IsHilbertSchmidtPW (M * (R * P)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun α => pow_le_pow_left₀ (norm_nonneg _) (hMSnorm α) 2) hc2
  have hL : R * P * M * (R * P) = (R * P) * (M * (R * P)) := by
    simp only [mul_assoc]
  have hpair : ∀ φ ψ : HaarL2 J,
      inner ℂ φ ((R * P * M * (R * P)) ψ) = inner ℂ ((R * P) φ) (M ((R * P) ψ)) := by
    intro φ ψ
    rw [hL, hmul (R * P) (M * (R * P)) ψ, hS φ, hmul M (R * P) ψ]
  have hLsymm : ∀ φ ψ : HaarL2 J,
      inner ℂ φ ((R * P * M * (R * P)) ψ) = inner ℂ ((R * P * M * (R * P)) φ) ψ := by
    intro φ ψ
    rw [hpair, hMsymm, hL, hmul (R * P) (M * (R * P)) φ, hmul M (R * P) φ, ← hS]
  have hLpos : IsPositiveOp (R * P * M * (R * P)) := by
    refine ⟨hLsymm, fun φ => ?_⟩
    rw [hpair]
    exact hM.2 ((R * P) φ)
  have hbound : ∀ α α', ‖peterWeylEntry (R * P * M * (R * P)) α α'‖ ≤ c α * c α' := by
    intro α α'
    unfold peterWeylEntry
    rw [hpair]
    calc ‖(inner ℂ ((R * P) (peterWeylVec α)) (M ((R * P) (peterWeylVec α'))) : ℂ)‖
        ≤ ‖(R * P) (peterWeylVec α)‖ * ‖M ((R * P) (peterWeylVec α'))‖ :=
          norm_inner_le_norm _ _
      _ ≤ c α * c α' :=
          mul_le_mul (hSnorm α) ((hMnorm _).trans (hSnorm α')) (norm_nonneg _) (hc0 α)
  refine ⟨hS, hHS, ?_, ?_, hLpos, hLsymm, ⟨R * P, M * (R * P), hHS, hMHS, hL⟩, hbound, ?_⟩
  · have e : R * P * M * (R * P) = R * P * M * R * P := by simp only [mul_assoc]
    rw [e, hRP]
  · calc R * P * M * (R * P) = R * P * M * (P * R) := congrArg (fun X => R * P * M * X) hRP
      _ = R * (P * (M * P)) * R := by simp only [mul_assoc]
      _ = R * (P * (P * M)) * R := by rw [hMP]
      _ = R * (P * P * M) * R := by simp only [mul_assoc]
      _ = R * P * M * R := by rw [hPP]; simp only [mul_assoc]
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => hbound p.1 p.2)
      (Summable.mul_of_nonneg hc1 hc1 hc0 hc0)
end TransferOperators
end YangMills.Construction
end
