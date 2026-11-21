import YangMills.Construction.ColdStepAtMirrorFrames.CalculusOfLocalTerms
import YangMills.Construction.ColdStepAtMirrorFrames.CovarianceOnOpenBalls
import YangMills.Construction.ColdStepAtMirrorFrames.MomentsOfAConvexMeasure
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace MomentBounds
variable {ι P : Type} [Fintype ι] [DecidableEq ι] [Fintype P]
theorem pseudoMetric_nonneg {D : P → P → ℝ} (hD : IsPseudoMetricOnBonds D) (y z : P) : 0 ≤ D y z := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.pseudoMetric_nonneg <;> assumption
theorem pseudoMetric_comp {pos : ι → P} {D : P → P → ℝ} (hD : IsPseudoMetricOnBonds D) :
    IsPseudoMetricOnBonds (fun b b' => D (pos b) (pos b')) :=
  ⟨fun b => hD.self _, fun b b' => hD.symm _ _, fun b b' b'' => hD.triangle _ _ _⟩
theorem sum_exp_neg_mul_le_of_le {pos : ι → P} {D : P → P → ℝ} (hD : IsPseudoMetricOnBonds D)
    {r r' S : ℝ} (hrr : r ≤ r')
    (hS : ∀ z, ∑ b, Real.exp (-(r * D (pos b) z)) ≤ S) (z : P) :
    ∑ b, Real.exp (-(r' * D (pos b) z)) ≤ S := by
  refine le_trans (Finset.sum_le_sum fun b _ => ?_) (hS z)
  apply Real.exp_le_exp.mpr
  have := pseudoMetric_nonneg hD (pos b) z
  nlinarith
end MomentBounds
open MomentBounds in
theorem admissibleMomentBoundsHold_of_cutoff (hgauss : GaussianMomentBound)
    (hc : BallCovarianceBoundOnOpenPolyball) (hcut : CutoffFactorIsRadialCutoff)
    (hm : CutoffExpectationIsPositiveForm) : AdmissibleMomentBoundsHold := by
  intro ι P _ _ _ ρ m r S p pos D Ψ hρ hm0 hr hp hD hΨ hS
  obtain ⟨K, hK, hsl⟩ := hΨ
  have F := hm ι ρ p Ψ hρ hp hK.smooth.continuous
  have hd := pseudoMetric_comp (pos := pos) hD
  have hrw := hcut ρ p hρ hp
  have hS0 : 0 ≤ S ∨ IsEmpty P := by
    by_cases h : Nonempty P
    · obtain ⟨z⟩ := h
      exact Or.inl ((Finset.sum_nonneg fun b _ => (Real.exp_pos _).le).trans (hS z))
    · exact Or.inr (not_nonempty_iff.mp h)
  have moment : ∀ b, ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ 2) ≤ 8 * S / m := by
    intro b
    have hW : ∀ b₀, ∑ b, Real.exp (-(2 * r * (fun b b' => D (pos b) (pos b')) b b₀)) ≤ S := by
      intro b₀
      exact sum_exp_neg_mul_le_of_le hD (r := r / 4) (r' := 2 * r) (by linarith) hS (pos b₀)
    have h := hgauss ι ρ m r S (fun b b' => D (pos b) (pos b')) Ψ K _ hρ hm0 hr.le hrw hd hK hW
      hsl 1 b
    simp only [Finset.range_one, Finset.prod_singleton, pow_one, mul_one] at h
    have e : ballExpectation (fun u => cutoffFactor ρ p (max u 0)) Ψ (fun η => ‖η b‖ ^ 2) =
        ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ 2) := by
      unfold ballExpectation ballDensity radialWeightProd
      simp only [max_eq_left (norm_nonneg _)]
    rw [e] at h
    simpa using h
  have hwt : ∀ z b, Real.exp (-(2 ^ 5 * r * D (pos b) z)) ≤ Real.exp (-(r / 4 * D (pos b) z)) := by
    intro z b
    apply Real.exp_le_exp.mpr
    have := pseudoMetric_nonneg hD (pos b) z
    nlinarith
  have hwS : ∀ z, ∑ b, Real.exp (-(2 ^ 5 * r * D (pos b) z)) ≤ S := fun z =>
    (Finset.sum_le_sum fun b _ => hwt z b).trans (hS z)
  have hbondn := fun b => IsBoundedContinuousOn.norm_sq_apply (ι := ι) hρ b
  have near : ∀ z, ballExpectation (cutoffFactor ρ p) Ψ (weightedSqNormNear r pos D z) ≤ 8 * S ^ 2 / m := by
    intro z
    unfold weightedSqNormNear
    rw [F.map_sum Finset.univ _ (fun b _ => (IsBoundedContinuousOn.const _).mul (hbondn b))]
    simp only [F.map_smul]
    calc ∑ b, Real.exp (-(2 ^ 5 * r * D (pos b) z)) * ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ 2)
        ≤ ∑ b, Real.exp (-(2 ^ 5 * r * D (pos b) z)) * (8 * S / m) :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (moment b) (Real.exp_pos _).le
      _ = (∑ b, Real.exp (-(2 ^ 5 * r * D (pos b) z))) * (8 * S / m) := by rw [Finset.sum_mul]
      _ ≤ S * (8 * S / m) := by
          have hS0 : 0 ≤ S := (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le).trans (hS z)
          exact mul_le_mul_of_nonneg_right (hwS z) (by positivity)
      _ = 8 * S ^ 2 / m := by ring
  refine ⟨moment, near, ?_, ?_⟩
  · intro a ha
    have hpt : ∀ η : BondField ι, (∑ b, a b * ‖η b‖) ^ 2 ≤
        (∑ b, a b) * ∑ b, a b * ‖η b‖ ^ 2 := by
      intro η
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => Real.sqrt (a b))
        (fun b => Real.sqrt (a b) * ‖η b‖)
      have e1 : ∀ b, Real.sqrt (a b) * (Real.sqrt (a b) * ‖η b‖) = a b * ‖η b‖ := fun b => by
        rw [← mul_assoc, Real.mul_self_sqrt (ha b)]
      have e2 : ∀ b, Real.sqrt (a b) ^ 2 = a b := fun b => Real.sq_sqrt (ha b)
      have e3 : ∀ b, (Real.sqrt (a b) * ‖η b‖) ^ 2 = a b * ‖η b‖ ^ 2 := fun b => by
        rw [mul_pow, e2]
      simp only [e1, e2, e3] at h
      exact h
    have hn1 : IsBoundedContinuousOn ι ρ (fun η => (∑ b, a b * ‖η b‖) ^ 2) := by
      refine ⟨?_, (∑ b, a b * ρ) ^ 2, fun η hη => ?_⟩
      · apply Continuous.continuousOn
        exact (continuous_finsetSum _ fun b _ =>
          continuous_const.mul (continuous_apply b).norm).pow 2
      · rw [abs_of_nonneg (by positivity)]
        apply pow_le_pow_left₀ (Finset.sum_nonneg fun b _ => mul_nonneg (ha b) (norm_nonneg _))
        exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hη b).le (ha b)
    have hn2 : IsBoundedContinuousOn ι ρ (fun η => ∑ b, a b * ‖η b‖ ^ 2) :=
      IsBoundedContinuousOn.sum _ _ fun b _ => (IsBoundedContinuousOn.const _).mul (hbondn b)
    have hA : 0 ≤ ∑ b, a b := Finset.sum_nonneg fun b _ => ha b
    have hle := F.mono _ _ hn1 ((IsBoundedContinuousOn.const (∑ b, a b)).mul hn2) (fun η _ => hpt η)
    rw [F.map_smul, F.map_sum Finset.univ _ (fun b _ => (IsBoundedContinuousOn.const _).mul (hbondn b))] at hle
    simp only [F.map_smul] at hle
    refine hle.trans ?_
    have : ∑ b, a b * ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ 2) ≤
        (∑ b, a b) * (8 * S / m) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (moment b) (ha b)
    calc (∑ b, a b) * ∑ b, a b * ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ 2)
        ≤ (∑ b, a b) * ((∑ b, a b) * (8 * S / m)) := mul_le_mul_of_nonneg_left this hA
      _ = _ := by ring
  · intro f g M A z G hf hg hb hA hG hfn hgn
    have h := hc ι ρ m r (fun b b' => D (pos b) (pos b')) Ψ K p hρ hm0 hr.le hp hd hK f g M hf hg hb
    refine h.trans ?_
    have hcn : ∀ (h : BondField ι → ℝ), 0 ≤ ballL2Norm (cutoffFactor ρ p) Ψ h := fun h =>
      Real.sqrt_nonneg _
    have hin : ∀ b', ∑ b, Real.exp (-(2 * r * D (pos b) z)) * Real.exp (-(r * D (pos b) (pos b'))) ≤
        S * Real.exp (-(r / 2 * D (pos b') z)) := by
      intro b'
      have : ∀ b, Real.exp (-(2 * r * D (pos b) z)) * Real.exp (-(r * D (pos b) (pos b'))) ≤
          Real.exp (-(r / 4 * D (pos b) z)) * Real.exp (-(r / 2 * D (pos b') z)) := by
        intro b
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have t1 := hD.triangle (pos b') (pos b) z
        have t2 := pseudoMetric_nonneg hD (pos b) z
        have t3 := pseudoMetric_nonneg hD (pos b) (pos b')
        rw [hD.symm (pos b') (pos b)] at t1
        nlinarith
      refine (Finset.sum_le_sum fun b _ => this b).trans ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hS z) (Real.exp_pos _).le
    have hmi : 0 ≤ m⁻¹ := by positivity
    rw [mul_assoc m⁻¹ A S, mul_assoc m⁻¹ (A * S)]
    apply mul_le_mul_of_nonneg_left _ hmi
    calc ∑ b, ∑ b', ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm f b) *
            Real.exp (-(r * D (pos b) (pos b'))) * ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm g b')
        ≤ ∑ b, ∑ b', (A * Real.exp (-(2 * r * D (pos b) z))) *
            Real.exp (-(r * D (pos b) (pos b'))) * G b' := by
          refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => ?_
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hfn b) (Real.exp_pos _).le) (hgn b')
            (hcn _) (by positivity)
      _ = ∑ b', G b' * (A * ∑ b, Real.exp (-(2 * r * D (pos b) z)) *
            Real.exp (-(r * D (pos b) (pos b')))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b' _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ ∑ b', G b' * (A * (S * Real.exp (-(r / 2 * D (pos b') z)))) := by
          refine Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left ?_ (hG b')
          exact mul_le_mul_of_nonneg_left (hin b') hA
      _ = A * S * ∑ b, G b * Real.exp (-(r / 2 * D (pos b) z)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
