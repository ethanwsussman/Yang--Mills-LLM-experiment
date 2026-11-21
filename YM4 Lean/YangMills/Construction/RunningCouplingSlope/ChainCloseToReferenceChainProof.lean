import YangMills.Construction.RunningCouplingSlope.ChainCloseToReferenceChain
import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheCoefficients
import YangMills.Construction.RunningCouplingSlope.TheKernelOfTheDifferenceDecays
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.ChainNearNormaliserSumProof
def secondMomentWeight (θ : ℝ) (w : Fin 4 → ℤ) : ℝ :=
  Real.exp (-(θ * ∑ μ, |(w μ : ℝ)|)) * ((w 0 : ℤ) : ℝ) ^ 2
theorem summable_exp_neg_mul_abs_mul_pow {θ : ℝ} (hθ : 0 < θ) (m : ℕ) :
    Summable fun t : ℤ => Real.exp (-(θ * |(t : ℝ)|)) * |(t : ℝ)| ^ m := by
  have hr : ‖Real.exp (-θ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_zero ▸ Real.exp_lt_exp.mpr (by linarith)
  have h := summable_pow_mul_geometric_of_norm_lt_one m hr
  have hnat : Summable fun t : ℕ => Real.exp (-(θ * |((t : ℤ) : ℝ)|)) * |((t : ℤ) : ℝ)| ^ m := by
    refine h.congr fun t => ?_
    have hpow : Real.exp (-θ) ^ t = Real.exp (-(θ * (t : ℝ))) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    simp only [Int.cast_natCast, Nat.abs_cast, hpow]
    ring
  refine Summable.of_nat_of_neg hnat ?_
  refine hnat.congr fun t => ?_
  simp
theorem summable_secondMomentWeight {θ : ℝ} (hθ : 0 < θ) : Summable (secondMomentWeight θ) := by
  let e : (Fin 4 → ℤ) ≃ ℤ × ℤ × ℤ × ℤ :=
    { toFun := fun w => (w 0, w 1, w 2, w 3)
      invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      left_inv := by
        intro w
        funext i
        fin_cases i <;> rfl
      right_inv := fun p => rfl }
  have g0 : ∀ t : ℤ, 0 ≤ Real.exp (-(θ * |(t : ℝ)|)) * |(t : ℝ)| ^ 0 := fun t => by positivity
  have g2 : ∀ t : ℤ, 0 ≤ Real.exp (-(θ * |(t : ℝ)|)) * |(t : ℝ)| ^ 2 := fun t => by positivity
  have s0 := summable_exp_neg_mul_abs_mul_pow hθ 0
  have s2 := summable_exp_neg_mul_abs_mul_pow hθ 2
  have s00 := Summable.mul_of_nonneg s0 s0 g0 g0
  have s000 := Summable.mul_of_nonneg s0 s00 g0 (fun p => mul_nonneg (g0 _) (g0 _))
  have s := Summable.mul_of_nonneg s2 s000 g2
    (fun p => mul_nonneg (g0 _) (mul_nonneg (g0 _) (g0 _)))
  rw [← e.symm.summable_iff]
  refine s.congr fun p => ?_
  have h1 : Real.exp (-(θ * (|(p.1 : ℝ)| + |(p.2.1 : ℝ)| + |(p.2.2.1 : ℝ)| + |(p.2.2.2 : ℝ)|))) =
      Real.exp (-(θ * |(p.1 : ℝ)|)) * Real.exp (-(θ * |(p.2.1 : ℝ)|)) *
        Real.exp (-(θ * |(p.2.2.1 : ℝ)|)) * Real.exp (-(θ * |(p.2.2.2 : ℝ)|)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h2 : (secondMomentWeight θ ∘ e.symm) p =
      Real.exp (-(θ * (|(p.1 : ℝ)| + |(p.2.1 : ℝ)| + |(p.2.2.1 : ℝ)| + |(p.2.2.2 : ℝ)|))) *
        (p.1 : ℝ) ^ 2 := by
    change Real.exp (-(θ * ∑ μ, |((![p.1, p.2.1, p.2.2.1, p.2.2.2] μ : ℤ) : ℝ)|)) *
      ((p.1 : ℤ) : ℝ) ^ 2 = _
    rw [Fin.sum_univ_four]
    rfl
  rw [h2, h1, ← sq_abs (p.1 : ℝ)]
  ring
theorem slopeCoefficient_eq_zero_of_trivial (a ρ : ℝ) (L : ℕ) (v : ℝ)
    (h : SlopeCoefficient.HasSlopeCoefficient Filter.atTop
      (SlopeCoefficient.chainLogarithm a ρ L 0) v) : v = 0 := by
  obtain ⟨K, hK, hs⟩ := h
  have hzero : ∀ (c c' : TorusLumps.LatticeBond), K c c' = 0 := by
    intro c c'
    let X : BlockAverages.imaginaryQuaternions := ⟨(⟨0, 1, 0, 0⟩ : ℍ[ℝ]), rfl⟩
    have hl := hK.tendsto_kernel c c' X X
    have hconst : (fun n => SlopeCoefficient.hessianAtTrivial (SlopeCoefficient.chainLogarithm a ρ L 0) n
        (TorusLumps.bondFrom 0 c) (TorusLumps.bondFrom 0 c') X X) = fun _ => 0 := by
      funext n
      simp [SlopeCoefficient.hessianAtTrivial, TorusFields.mixedDeriv, SlopeCoefficient.chainLogarithm]
    rw [hconst] at hl
    have h0 := tendsto_nhds_unique hl tendsto_const_nhds
    have hX : inner ℝ ((X : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])
        ((X : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) ≠ 0 := by
      refine inner_self_ne_zero.mpr fun h => ?_
      have h1 := congrArg (fun q : ℍ[ℝ] => q.imI) h
      simp [X] at h1
    exact (mul_eq_zero.mp h0).resolve_left hX
  have hmom : SlopeCoefficient.secondMomentTerm K = fun _ => 0 := by
    funext w
    simp [SlopeCoefficient.secondMomentTerm, hzero]
  rw [hmom] at hs
  exact hs.unique hasSum_zero
theorem chainNearNormaliserSum_holds (hdec : DifferenceKernelExpDecay)
    (hmom : CoefficientDifferenceIsSecondMoment) : ChainNearNormaliserSum := by
  intro a ha L hL hLs
  obtain ⟨θ, C, hθ, hC, h⟩ := hdec a ha L hLs
  have hw := summable_secondMomentWeight hθ
  have hw0 : ∀ w, 0 ≤ secondMomentWeight θ w := fun w => by unfold secondMomentWeight; positivity
  have hT : 0 ≤ ∑' w, secondMomentWeight θ w := tsum_nonneg hw0
  refine ⟨1 / 2 * C * ∑' w, secondMomentWeight θ w, by positivity, ?_⟩
  intro k ρ v hρ hρ1 hv
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [slopeCoefficient_eq_zero_of_trivial a ρ L v hv]
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, abs_zero]
    positivity
  · obtain ⟨κ, hκ, hb⟩ := h k hk
    have hs := hmom a ha L hL hLs k hk κ hκ ρ v hρ hρ1 hv
    rw [← hs.tsum_eq]
    have hg : HasSum (fun w => 1 / 2 * C * secondMomentWeight θ w)
        (1 / 2 * C * ∑' w, secondMomentWeight θ w) :=
      hw.hasSum.mul_left _
    have hbd := tsum_of_norm_bounded hg (f := fun w : Fin 4 → ℤ =>
        -(1 / 2) * κ w * ((w 0 : ℤ) : ℝ) ^ 2) (fun w => ?_)
    · simpa [Real.norm_eq_abs] using hbd
    · have hw' := hb w
      have h2 : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_pos (by norm_num)
      have hsq : 0 ≤ ((w 0 : ℤ) : ℝ) ^ 2 := sq_nonneg _
      simp only [Real.norm_eq_abs, secondMomentWeight, abs_mul, abs_neg]
      rw [h2, abs_of_nonneg hsq]
      nlinarith [mul_le_mul_of_nonneg_right hw' hsq]
end YangMills.Construction.RunningCouplingSlope.ChainNearNormaliserSumProof
end
