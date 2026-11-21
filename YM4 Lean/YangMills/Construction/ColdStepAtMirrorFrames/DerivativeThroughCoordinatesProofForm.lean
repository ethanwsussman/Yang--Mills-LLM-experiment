import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeThroughCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeAlongASegmentProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Calculus
theorem weightedNorm_nonneg_of_nonneg {N : ℕ} {w : Fin N → ℝ} (hw : ∀ n, 0 ≤ w n) (x : Fin N → ℝ) :
    0 ≤ weightedNorm w x :=
  Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (hw n)
theorem abs_apply_le_mul_prod_weightedNorm {N j : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin N → ℝ) ℝ) (K : ℝ)
    (w : Fin N → ℝ) (hw : ∀ n, 0 ≤ w n) (hK : 0 ≤ K)
    (hT : ∀ r : Fin j → Fin N, |T (fun i => Pi.single (r i) 1)| ≤ K * ∏ i, w (r i))
    (v : Fin j → Fin N → ℝ) : |T v| ≤ K * ∏ i, weightedNorm w (v i) := by apply _root_.YangMills.Construction.Calculus.abs_multilinear_le_prod_weightedNorm <;> assumption
theorem iteratedDerivCompBound_of_faaDiBruno (hFaa : FaaDiBrunoAt) : IteratedDerivCompBound := by
  classical
  intro N k g Q w K C₁ hw hQa hga hK hNP hk hK0 hC₁
  have hQc : ContDiffAt ℝ k Q 0 := hQa.contDiffAt
  have h := hFaa _ _ _ g Q k 0 hga.contDiffAt hQc (fun l => Pi.single l 1)
  rw [h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ p : OrderedFinpartition k, |iteratedFDeriv ℝ p.length g (Q 0) (fun i =>
      iteratedFDeriv ℝ (p.partSize i) Q 0 (fun l => Pi.single (p.emb i l) 1))| ≤ K * C₁ ^ k := by
    intro p
    have hl := p.length_le
    have hl1 : 1 ≤ p.length := by
      have := (p.index ⟨0, hk⟩).isLt
      omega
    have h1 := abs_apply_le_mul_prod_weightedNorm (iteratedFDeriv ℝ p.length g (Q 0)) K w hw hK0
      (hK _ hl1 hl) (fun i => iteratedFDeriv ℝ (p.partSize i) Q 0 (fun l => Pi.single (p.emb i l) 1))
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    have h2 : ∏ i, weightedNorm w (iteratedFDeriv ℝ (p.partSize i) Q 0 (fun l => Pi.single (p.emb i l) 1)) ≤
        ∏ _i : Fin p.length, C₁ :=
      Finset.prod_le_prod (fun i _ => weightedNorm_nonneg_of_nonneg hw _) fun i _ =>
        hNP _ _ (p.partSize_pos i) (p.emb_strictMono i).injective
    refine h2.trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_right₀ hC₁ hl
  refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  apply le_of_eq
  unfold compositionConstant
  ring
end YangMills.Construction.Calculus
end
