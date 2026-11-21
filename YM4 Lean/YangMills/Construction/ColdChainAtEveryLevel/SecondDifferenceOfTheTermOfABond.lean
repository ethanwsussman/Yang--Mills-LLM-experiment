import YangMills.Construction.ColdChainAtEveryLevel.ComplexChartElements
import YangMills.Construction.ColdChainAtEveryLevel.FirstVariationAtTheReferenceProof
import YangMills.Construction.ColdChainAtEveryLevel.LinearPartOfTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.BondSecondDifference
open FiniteDifferences ComplexifiedQuaternions BlockAverages ComplexRemainders ComplexDifferences ComplexContours
  ComplexLevels ComplexChainStep RealChartTerms PlaquetteSecondDifference LinearLevels SecondDifferences
variable {F : BlockFrame} {j : ℕ}
section Split
variable {V E : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {N : V → ℝ} {G : V → E} {K σ ε : ℝ}
theorem norm_second_diff_le_of_quadraticBound (h : QuadraticBoundOnBall N G K σ ε) (hK : 0 ≤ K) (hσ : 0 < σ)
    {y₁ y₂ y₃ : V} {t : ℝ}
    (ht : 0 ≤ t) (hsm : 24 * (2 * t + σ) < ε) (h1 : N y₁ ≤ t) (h2 : N y₂ ≤ t) (h3 : N y₃ ≤ 2 * t) :
    ‖G y₃ - G y₁ - G y₂ + G 0‖ ≤ 12 * K * (2 * t + σ) * N (y₃ - (y₁ + y₂)) + 64 * K * N y₁ * N y₂ := by
  have hN0 : N 0 = 0 := by
    have := h.homogeneous 0 (0 : V)
    simpa using this
  have hsd := h.norm_second_diff_le hK hσ (by linarith) (y := 0) (e₁ := y₁) (e₂ := y₂) (t := t) ht (by linarith)
    (by rw [hN0]; exact ht) h1 h2
  simp only [zero_add] at hsd
  have hadd : N (y₁ + y₂) ≤ 2 * t := (h.triangle _ _).trans (by linarith)
  have hl := h.norm_sub_le hK hσ (t := 2 * t) (by positivity) (by linarith) hadd h3
  have e : G y₃ - G y₁ - G y₂ + G 0 = (G y₃ - G (y₁ + y₂)) + (G (y₁ + y₂) - G y₁ - G y₂ + G 0) := by abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add hl hsd)
end Split
theorem gaugedBondAverage_zeroChart (hodd : Odd F.blockSide) (R : F.FieldChain) (j : ℕ)
    (c : F.Site (j + 1) × Fin 4) :
    gaugedBondAverage R (zeroChart F) j c = contourAverage (R j) c := by apply _root_.YangMills.Construction.BlockAverages.FirstVariation.gaugedBondAverage_zeroChart <;> assumption
theorem bondAverageGap_zeroChart (hodd : Odd F.blockSide) (R : F.FieldChain) (j : ℕ)
    (c : F.Site (j + 1) × Fin 4) :
    bondAverageGap R (zeroChart F) j c = 1 := by
  simp [bondAverageGap, gaugedBondAverage_zeroChart hodd]
theorem bondHullNorm_zero_field (c : F.Site (j + 1) × Fin 4) :
    bondHullNorm c (0 : F.Site j → Fin 4 → ComplexQuat) = 0 := by
  have h := bondHullNorm_smul c 0 (0 : F.Site j → Fin 4 → ComplexQuat)
  simpa using h
theorem bound_assemble_of_lt_top {a ρ R₃ i E m p q Z Z' Y₁ Y₁' Y₂ Y₂' C : ℝ}
    (b1 : (a + ρ) * (i + E) + E ≤ (a + R₃) * m + 3 * E)
    (b2 : q * Z ≤ q * Z') (b3 : Y₁ ≤ Y₁') (b4 : Y₂ ≤ Y₂') (b5 : 3 * E = 24768 * p * m + 3 * C) :
    (a + ρ) * (i + E) + E + q * Z + Y₁ + Y₂ ≤ (a + 24768 * p) * m + q * Z' + Y₁' + Y₂' + R₃ * m + 3 * C := by
  nlinarith
theorem norm_ofUnit_sub_one (g : UnitQuaternion) : ‖ofUnit g - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.ComplexChart.norm_ofUnit_sub_one <;> assumption
theorem abs_fit_secondDifference_sub_inner_le {r₀ ρ₁ ρ₂ ρ₃ : ℝ} {A₁ A₂ A₃ P : UnitQuaternion} {v w : ℍ[ℝ]}
    {R₃ Z L₁ L₂ n₁ n₂ Dd E p : ℝ}
    (hp : ‖(P : ℍ[ℝ]) - 1‖ = p) (r3 : |ρ₃| ≤ R₃) (r1 : |ρ₃ - ρ₁| ≤ L₁) (r2 : |ρ₃ - ρ₂| ≤ L₂)
    (r12 : |ρ₃ - ρ₁ - ρ₂| ≤ Z) (he₁ : ‖(A₁ : ℍ[ℝ]) - 1‖ ≤ 2 * n₁) (he₂ : ‖(A₂ : ℍ[ℝ]) - 1‖ ≤ 2 * n₂)
    (hd : ‖(A₃ : ℍ[ℝ]) - A₁ - A₂ + 1‖ ≤ Dd)
    (hEd : Dd * p + (2 * n₁ + 2 * n₂) * Dd + Dd ^ 2 / 2 + ‖(A₁ : ℍ[ℝ]) - 1 - v‖ * (2 * n₂) +
      ‖v‖ * ‖(A₂ : ℍ[ℝ]) - 1 - w‖ ≤ E) :
    |(r₀ + ρ₃) * (1 - ((A₃ * P : UnitQuaternion) : ℍ[ℝ]).re) - (r₀ + ρ₁) * (1 - ((A₁ * P : UnitQuaternion) : ℍ[ℝ]).re) -
        (r₀ + ρ₂) * (1 - ((A₂ * P : UnitQuaternion) : ℍ[ℝ]).re) + r₀ * (1 - (P : ℍ[ℝ]).re) - inner ℝ v w| ≤
      (|r₀ - 1| + R₃) * (‖v‖ * ‖w‖ + E) + E + p ^ 2 / 2 * Z + L₁ * ((2 * n₁) ^ 2 / 2 + 2 * n₁ * p) +
        L₂ * ((2 * n₂) ^ 2 / 2 + 2 * n₂ * p) := by
  have hp0 : 0 ≤ p := by rw [← hp]; exact norm_nonneg _
  have n₁0 : 0 ≤ n₁ := by linarith [norm_nonneg ((A₁ : ℍ[ℝ]) - 1)]
  have n₂0 : 0 ≤ n₂ := by linarith [norm_nonneg ((A₂ : ℍ[ℝ]) - 1)]
  set d := ‖(A₃ : ℍ[ℝ]) - A₁ - A₂ + 1‖ with hdd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hE : d * ‖(P : ℍ[ℝ]) - 1‖ + (‖(A₁ : ℍ[ℝ]) - 1‖ + ‖(A₂ : ℍ[ℝ]) - 1‖) * d + d ^ 2 / 2 +
      ‖(A₁ : ℍ[ℝ]) - 1 - v‖ * ‖(A₂ : ℍ[ℝ]) - 1‖ + ‖v‖ * ‖(A₂ : ℍ[ℝ]) - 1 - w‖ ≤ E := by
    rw [hp]
    refine le_trans ?_ hEd
    have a1 : d * p ≤ Dd * p := mul_le_mul_of_nonneg_right hd hp0
    have a2 : (‖(A₁ : ℍ[ℝ]) - 1‖ + ‖(A₂ : ℍ[ℝ]) - 1‖) * d ≤ (2 * n₁ + 2 * n₂) * Dd :=
      mul_le_mul (add_le_add he₁ he₂) hd hd0 (by positivity)
    have a3 : d ^ 2 / 2 ≤ Dd ^ 2 / 2 := by
      have := pow_le_pow_left₀ hd0 hd 2
      linarith
    have a4 : ‖(A₁ : ℍ[ℝ]) - 1 - v‖ * ‖(A₂ : ℍ[ℝ]) - 1‖ ≤ ‖(A₁ : ℍ[ℝ]) - 1 - v‖ * (2 * n₂) :=
      mul_le_mul_of_nonneg_left he₂ (norm_nonneg _)
    linarith
  have key := abs_weighted_secondDifference_sub_inner_le r₀ ρ₁ ρ₂ ρ₃ A₁ A₂ A₃ P v w hE
  refine key.trans ?_
  rw [hp]
  have hE0 : 0 ≤ E := le_trans (by positivity) hE
  have hi : |inner ℝ v w| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm v w
  have hR0 : 0 ≤ R₃ := (abs_nonneg _).trans r3
  have b1 : (|r₀ - 1| + |ρ₃|) * (|inner ℝ v w| + E) ≤ (|r₀ - 1| + R₃) * (‖v‖ * ‖w‖ + E) :=
    mul_le_mul (add_le_add_right r3 _) (add_le_add_left hi _) (by positivity) (by positivity)
  have b2 : p ^ 2 / 2 * |ρ₃ - ρ₁ - ρ₂| ≤ p ^ 2 / 2 * Z := mul_le_mul_of_nonneg_left r12 (by positivity)
  have b3 : |ρ₃ - ρ₁| * (‖(A₁ : ℍ[ℝ]) - 1‖ ^ 2 / 2 + ‖(A₁ : ℍ[ℝ]) - 1‖ * p) ≤
      L₁ * ((2 * n₁) ^ 2 / 2 + 2 * n₁ * p) := by
    refine mul_le_mul r1 ?_ (by positivity) ((abs_nonneg _).trans r1)
    have := pow_le_pow_left₀ (norm_nonneg _) he₁ 2
    have := mul_le_mul_of_nonneg_right he₁ hp0
    linarith
  have b4 : |ρ₃ - ρ₂| * (‖(A₂ : ℍ[ℝ]) - 1‖ ^ 2 / 2 + ‖(A₂ : ℍ[ℝ]) - 1‖ * p) ≤
      L₂ * ((2 * n₂) ^ 2 / 2 + 2 * n₂ * p) := by
    refine mul_le_mul r2 ?_ (by positivity) ((abs_nonneg _).trans r2)
    have := pow_le_pow_left₀ (norm_nonneg _) he₂ 2
    have := mul_le_mul_of_nonneg_right he₂ hp0
    linarith
  exact add_le_add (add_le_add (add_le_add (add_le_add_left b1 _) b2) b3) b4
section Bond
variable (hodd : Odd F.blockSide) {R : F.FieldChain} {W₁ W₂ W₃ : ChainChart F} {σ t : ℝ}
  {c : F.Site (j + 1) × Fin 4}
include hodd
theorem gaugedBondAverage_ne_zero (hj : j + 1 ≤ F.top) (W : ChainChart F) (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (R j) (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ)
    (hy : 8 * (F.blockSide : ℝ) * bondHullNorm c (levelDeviation R (realChart W) j) ≤ 1 / 1024) :
    gaugedBondAverage R W j c ≠ 0 := by
  intro h0
  have h := (remainder_bounds hodd hj hσ hy href).1
  rw [liftedBondMean_realChart hodd hj, h0, ofQuat_zero] at h
  simp at h
theorem unitRemainder_zero_and_sqrtRemainder_zero (hj : j + 1 ≤ F.top) (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (R j) (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ) :
    unitRemainder (R j) c 0 = 0 ∧ sqrtRemainder (R j) c 0 = 0 := by
  have h := remainder_bounds hodd hj (y := 0) hσ (by rw [bondHullNorm_zero_field]; norm_num) href
  rw [bondHullNorm_zero_field] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    norm_le_zero_iff] at h
  exact ⟨h.2.1, h.2.2⟩
theorem sqrtRemainder_bounds (hj : j + 1 ≤ F.top) (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (R j) (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ)
    (ht : 0 ≤ t) (hsm : 24 * (2 * t + σ) < hullBallRadius F.blockSide)
    (h1 : bondHullNorm c (levelDeviation R (realChart W₁) j) ≤ t)
    (h2 : bondHullNorm c (levelDeviation R (realChart W₂) j) ≤ t)
    (h3 : bondHullNorm c (levelDeviation R (realChart W₃) j) ≤ 2 * t) :
    |‖gaugedBondAverage R W₃ j c‖ - ‖contourAverage (R j) c‖| ≤ 200000 * (F.blockSide : ℝ) ^ 2 *
        (bondHullNorm c (levelDeviation R (realChart W₃) j) ^ 2 +
          σ * bondHullNorm c (levelDeviation R (realChart W₃) j)) ∧
    |(‖gaugedBondAverage R W₃ j c‖ - ‖contourAverage (R j) c‖) -
        (‖gaugedBondAverage R W₁ j c‖ - ‖contourAverage (R j) c‖)| ≤
        12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
          bondHullNorm c (levelDeviation R (realChart W₃) j - levelDeviation R (realChart W₁) j) ∧
    |(‖gaugedBondAverage R W₃ j c‖ - ‖contourAverage (R j) c‖) -
        (‖gaugedBondAverage R W₂ j c‖ - ‖contourAverage (R j) c‖)| ≤
        12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
          bondHullNorm c (levelDeviation R (realChart W₃) j - levelDeviation R (realChart W₂) j) ∧
    |(‖gaugedBondAverage R W₃ j c‖ - ‖contourAverage (R j) c‖) -
        (‖gaugedBondAverage R W₁ j c‖ - ‖contourAverage (R j) c‖) -
        (‖gaugedBondAverage R W₂ j c‖ - ‖contourAverage (R j) c‖)| ≤
      12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
          bondHullNorm c (levelDeviation R (realChart W₃) j -
            (levelDeviation R (realChart W₁) j + levelDeviation R (realChart W₂) j)) +
        64 * (200000 * (F.blockSide : ℝ) ^ 2) * bondHullNorm c (levelDeviation R (realChart W₁) j) *
          bondHullNorm c (levelDeviation R (realChart W₂) j) := by
  have hK : (0 : ℝ) ≤ 200000 * (F.blockSide : ℝ) ^ 2 := by positivity
  have hq := sqrtRemainder_quadraticBound hodd hj hσ href
  have hsmall : ∀ {N : ℝ}, N ≤ 2 * t → N < hullBallRadius F.blockSide := fun h => by linarith
  have hy : ∀ W : ChainChart F, bondHullNorm c (levelDeviation R (realChart W) j) ≤ 2 * t →
      sqrtRemainder (R j) c (levelDeviation R (realChart W) j) =
        ((‖gaugedBondAverage R W j c‖ - ‖contourAverage (R j) c‖ : ℝ) : ℂ) :=
    fun W hW => sqrtRemainder_realChart hodd hj R W c (gaugedBondAverage_ne_zero hodd hj W hσ href
      (eight_mul_le_of_lt_hullBallRadius hodd (hsmall hW)))
  have h1' : bondHullNorm c (levelDeviation R (realChart W₁) j) ≤ 2 * t := by linarith
  have h2' : bondHullNorm c (levelDeviation R (realChart W₂) j) ≤ 2 * t := by linarith
  have r1 := hy W₁ h1'
  have r2 := hy W₂ h2'
  have r3 := hy W₃ h3
  set ρ₁ := ‖gaugedBondAverage R W₁ j c‖ - ‖contourAverage (R j) c‖ with hρ₁
  set ρ₂ := ‖gaugedBondAverage R W₂ j c‖ - ‖contourAverage (R j) c‖ with hρ₂
  set ρ₃ := ‖gaugedBondAverage R W₃ j c‖ - ‖contourAverage (R j) c‖ with hρ₃
  have hsm3 : 3 * (2 * t + σ) < hullBallRadius F.blockSide := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (remainder_bounds hodd hj hσ (eight_mul_le_of_lt_hullBallRadius hodd (hsmall h3)) href).2.2
    rw [r3, Complex.norm_real] at this
    exact this
  · have := hq.norm_sub_le hK hσ0 (t := 2 * t) (by positivity) hsm3 h1' h3
    rw [r1, r3, ← Complex.ofReal_sub, Complex.norm_real] at this
    exact this
  · have := hq.norm_sub_le hK hσ0 (t := 2 * t) (by positivity) hsm3 h2' h3
    rw [r2, r3, ← Complex.ofReal_sub, Complex.norm_real] at this
    exact this
  · have := norm_second_diff_le_of_quadraticBound hq hK hσ0 ht hsm h1 h2 h3
    rw [r1, r2, r3, (unitRemainder_zero_and_sqrtRemainder_zero hodd hj hσ href).2, ← Complex.ofReal_sub,
      ← Complex.ofReal_sub, add_zero, Complex.norm_real] at this
    exact this
theorem norm_bondAverageGap_second_diff_le (hj : j + 1 ≤ F.top) (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (R j) (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ)
    (ht : 0 ≤ t) (hsm : 24 * (2 * t + σ) < hullBallRadius F.blockSide)
    (h1 : bondHullNorm c (levelDeviation R (realChart W₁) j) ≤ t)
    (h2 : bondHullNorm c (levelDeviation R (realChart W₂) j) ≤ t)
    (h3 : bondHullNorm c (levelDeviation R (realChart W₃) j) ≤ 2 * t) :
    ‖((bondAverageGap R W₃ j c : UnitQuaternion) : ℍ[ℝ]) - (bondAverageGap R W₁ j c : UnitQuaternion) -
        (bondAverageGap R W₂ j c : UnitQuaternion) + 1‖ ≤
      lineBlockAverage (fun x d => ‖(levelDeviation R (realChart W₃) j -
        (levelDeviation R (realChart W₁) j + levelDeviation R (realChart W₂) j)) x d‖) c +
      (12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
          bondHullNorm c (levelDeviation R (realChart W₃) j -
            (levelDeviation R (realChart W₁) j + levelDeviation R (realChart W₂) j)) +
        64 * (200000 * (F.blockSide : ℝ) ^ 2) * bondHullNorm c (levelDeviation R (realChart W₁) j) *
          bondHullNorm c (levelDeviation R (realChart W₂) j)) := by
  have hK : (0 : ℝ) ≤ 200000 * (F.blockSide : ℝ) ^ 2 := by positivity
  have hq := norm_second_diff_le_of_quadraticBound (unitRemainder_quadraticBound hodd hj hσ href) hK hσ0 ht hsm
    h1 h2 h3
  rw [(unitRemainder_zero_and_sqrtRemainder_zero hodd hj hσ href).1, add_zero] at hq
  set y₁ := levelDeviation R (realChart W₁) j with hy₁
  set y₂ := levelDeviation R (realChart W₂) j with hy₂
  set y₃ := levelDeviation R (realChart W₃) j with hy₃
  have e : ofQuat (((bondAverageGap R W₃ j c : UnitQuaternion) : ℍ[ℝ]) -
        (bondAverageGap R W₁ j c : UnitQuaternion) - (bondAverageGap R W₂ j c : UnitQuaternion) + 1) =
      purePart (transportedAverage (R j) (fun x d => (y₃ - (y₁ + y₂)) x d) c) +
        (unitRemainder (R j) c y₃ - unitRemainder (R j) c y₁ - unitRemainder (R j) c y₂) := by
    have u1 := linearizedUnit_realChart hodd hj R W₁ c
    have u2 := linearizedUnit_realChart hodd hj R W₂ c
    have u3 := linearizedUnit_realChart hodd hj R W₃ c
    rw [← hy₁] at u1
    rw [← hy₂] at u2
    rw [← hy₃] at u3
    have e1 : ofQuat (((bondAverageGap R W₃ j c : UnitQuaternion) : ℍ[ℝ]) -
          (bondAverageGap R W₁ j c : UnitQuaternion) - (bondAverageGap R W₂ j c : UnitQuaternion) + 1) =
        ofUnit (bondAverageGap R W₃ j c) - ofUnit (bondAverageGap R W₁ j c) -
          ofUnit (bondAverageGap R W₂ j c) + 1 := by
      simp only [ofUnit, ofQuat_add, ofQuat_one, ofQuat_sub_eq]
    have e2 : (fun x d => (y₃ - (y₁ + y₂)) x d) = fun x d => y₃ x d - (y₁ x d + y₂ x d) := rfl
    rw [e1, ← u1, ← u2, ← u3, e2, transportedAverage_sub, transportedAverage_add, purePart_sub, purePart_add]
    simp only [linearizedUnit]
    abel
  rw [← norm_ofQuat, e]
  refine (norm_add_le _ _).trans (add_le_add ?_ hq)
  exact (norm_purePart_le _).trans (norm_transportedAverage_le hodd _ _ c)
def bondEnergy (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) (j : ℕ)
    (c : F.Site (j + 1) × Fin 4) : ℝ :=
  gaugedBlockFit (chartChain R U V j) (chartGauge R U (j + 1)) (chartChain R U V (j + 1)) c
def cubicRemainder (m₁ m₂ : ℝ) : ℝ :=
  (m₁ + m₂) * (8256 * m₁ * m₂) + (8256 * m₁ * m₂) ^ 2 / 2 + m₁ ^ 2 * m₂ + m₁ * m₂ ^ 2
set_option maxHeartbeats 4000000 in
theorem abs_bondEnergy_secondDifference_sub_inner_le_of_lt_top (V : F.GaugeField F.top) (hj : j + 1 < F.top)
    (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (R j) (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ)
    (ht : 0 ≤ t) (hsm : 24 * (2 * t + σ) < hullBallRadius F.blockSide)
    (h1 : bondHullNorm c (levelDeviation R (realChart W₁) j) ≤ t)
    (h2 : bondHullNorm c (levelDeviation R (realChart W₂) j) ≤ t)
    (h3 : bondHullNorm c (levelDeviation R (realChart W₃) j) ≤ 2 * t)
    (hx₁ : ‖(W₁.coarse j c.1 c.2 : ℍ[ℝ])‖ ≤ 1 / 4000) (hx₂ : ‖(W₂.coarse j c.1 c.2 : ℍ[ℝ])‖ ≤ 1 / 4000)
    (hx₃ : W₃.coarse j c.1 c.2 = W₁.coarse j c.1 c.2 + W₂.coarse j c.1 c.2)
    (ha : |‖contourAverage (R j) c‖ - 1| ≤ 1)
    (hρ : 200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c (levelDeviation R (realChart W₃) j) ^ 2 +
      σ * bondHullNorm c (levelDeviation R (realChart W₃) j)) ≤ 1) :
    |bondEnergy R W₃ V j c - bondEnergy R W₁ V j c - bondEnergy R W₂ V j c + bondEnergy R (zeroChart F) V j c -
        inner ℝ (W₁.coarse j c.1 c.2 : ℍ[ℝ]) (W₂.coarse j c.1 c.2 : ℍ[ℝ])| ≤
      (|‖contourAverage (R j) c‖ - 1| + 24768 * ‖((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖) *
          (‖(W₁.coarse j c.1 c.2 : ℍ[ℝ])‖ * ‖(W₂.coarse j c.1 c.2 : ℍ[ℝ])‖) +
        ‖((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 / 2 *
          (12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
              bondHullNorm c (levelDeviation R (realChart W₃) j -
                (levelDeviation R (realChart W₁) j + levelDeviation R (realChart W₂) j)) +
            64 * (200000 * (F.blockSide : ℝ) ^ 2) * bondHullNorm c (levelDeviation R (realChart W₁) j) *
              bondHullNorm c (levelDeviation R (realChart W₂) j)) +
        12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
          bondHullNorm c (levelDeviation R (realChart W₃) j - levelDeviation R (realChart W₁) j) *
          (‖(W₁.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 / 2 +
            ‖(W₁.coarse j c.1 c.2 : ℍ[ℝ])‖ * ‖((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖) +
        12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
          bondHullNorm c (levelDeviation R (realChart W₃) j - levelDeviation R (realChart W₂) j) *
          (‖(W₂.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 / 2 +
            ‖(W₂.coarse j c.1 c.2 : ℍ[ℝ])‖ * ‖((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖) +
        200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c (levelDeviation R (realChart W₃) j) ^ 2 +
            σ * bondHullNorm c (levelDeviation R (realChart W₃) j)) *
          (‖(W₁.coarse j c.1 c.2 : ℍ[ℝ])‖ * ‖(W₂.coarse j c.1 c.2 : ℍ[ℝ])‖) +
        3 * cubicRemainder ‖(W₁.coarse j c.1 c.2 : ℍ[ℝ])‖ ‖(W₂.coarse j c.1 c.2 : ℍ[ℝ])‖ := by
  have hj' : j + 1 ≤ F.top := hj.le
  obtain ⟨r3, r1, r2, r12⟩ :=
    sqrtRemainder_bounds (W₁ := W₁) (W₂ := W₂) (W₃ := W₃) hodd hj' hσ0 hσ href ht hsm h1 h2 h3
  have hne : ∀ W : ChainChart F, bondHullNorm c (levelDeviation R (realChart W) j) ≤ 2 * t →
      gaugedBondAverage R W j c ≠ 0 :=
    fun W hW => gaugedBondAverage_ne_zero hodd hj' W hσ href
      (eight_mul_le_of_lt_hullBallRadius hodd (by linarith))
  have n1 := hne W₁ (by linarith)
  have n2 := hne W₂ (by linarith)
  have n3 := hne W₃ h3
  have n0 : gaugedBondAverage R (zeroChart F) j c ≠ 0 := hne _ (by
    rw [levelDeviation_zeroChart hodd, bondHullNorm_zero_field]
    positivity)
  set x₁ := W₁.coarse j c.1 c.2 with hx₁d
  set x₂ := W₂.coarse j c.1 c.2 with hx₂d
  set m₁ := ‖(x₁ : ℍ[ℝ])‖ with hm₁
  set m₂ := ‖(x₂ : ℍ[ℝ])‖ with hm₂
  set μ := referenceDefect R j c with hμ
  set P : UnitQuaternion := μ⁻¹ with hP
  set r₀ := ‖contourAverage (R j) c‖ with hr₀
  set ρ₁ := ‖gaugedBondAverage R W₁ j c‖ - r₀ with hρ₁
  set ρ₂ := ‖gaugedBondAverage R W₂ j c‖ - r₀ with hρ₂
  set ρ₃ := ‖gaugedBondAverage R W₃ j c‖ - r₀ with hρ₃
  set A₁ := expUnit (-x₁) with hA₁
  set A₂ := expUnit (-x₂) with hA₂
  set A₃ := expUnit (-x₁ + -x₂) with hA₃
  have t1 : bondEnergy R W₁ V j c = (r₀ + ρ₁) * (1 - ((A₁ * P : UnitQuaternion) : ℍ[ℝ]).re) := by
    have e : r₀ + ρ₁ = ‖gaugedBondAverage R W₁ j c‖ := by
      rw [hρ₁]
      ring
    rw [e]
    exact gaugedBlockFit_chartChain_of_lt_top R W₁ V hj c n1
  have t2 : bondEnergy R W₂ V j c = (r₀ + ρ₂) * (1 - ((A₂ * P : UnitQuaternion) : ℍ[ℝ]).re) := by
    have e : r₀ + ρ₂ = ‖gaugedBondAverage R W₂ j c‖ := by
      rw [hρ₂]
      ring
    rw [e]
    exact gaugedBlockFit_chartChain_of_lt_top R W₂ V hj c n2
  have t3 : bondEnergy R W₃ V j c = (r₀ + ρ₃) * (1 - ((A₃ * P : UnitQuaternion) : ℍ[ℝ]).re) := by
    have e' : -W₃.coarse j c.1 c.2 = -x₁ + -x₂ := by rw [hx₃, neg_add]
    have e : r₀ + ρ₃ = ‖gaugedBondAverage R W₃ j c‖ := by
      rw [hρ₃]
      ring
    rw [e]
    have := gaugedBlockFit_chartChain_of_lt_top R W₃ V hj c n3
    rw [e'] at this
    exact this
  have t0 : bondEnergy R (zeroChart F) V j c = r₀ * (1 - (P : ℍ[ℝ]).re) := by
    have e : -(zeroChart F).coarse j c.1 c.2 = 0 := neg_zero
    have := gaugedBlockFit_chartChain_of_lt_top R (zeroChart F) V hj c n0
    rw [e, expUnit_zero_eq_one, one_mul, gaugedBondAverage_zeroChart hodd] at this
    exact this
  have neg1 : ‖((-x₁ : imaginaryQuaternions) : ℍ[ℝ])‖ = m₁ := norm_neg _
  have neg2 : ‖((-x₂ : imaginaryQuaternions) : ℍ[ℝ])‖ = m₂ := norm_neg _
  have m10 : 0 ≤ m₁ := norm_nonneg _
  have m20 : 0 ≤ m₂ := norm_nonneg _
  set v : ℍ[ℝ] := ((-x₁ : imaginaryQuaternions) : ℍ[ℝ]) with hv
  set w : ℍ[ℝ] := ((-x₂ : imaginaryQuaternions) : ℍ[ℝ]) with hw
  have hd : ‖(A₃ : ℍ[ℝ]) - A₁ - A₂ + 1‖ ≤ 8256 * m₁ * m₂ := by
    have := norm_expUnit_second_diff_le (ξ := -x₁) (η := -x₂) (by rw [← hv, neg1]; exact hx₁)
      (by rw [← hw, neg2]; exact hx₂)
    rwa [← hv, ← hw, neg1, neg2] at this
  have he₁ : ‖(A₁ : ℍ[ℝ]) - 1‖ ≤ m₁ := by
    have := norm_coe_expUnit_sub_one_le (-x₁)
    rwa [← hv, neg1] at this
  have he₂ : ‖(A₂ : ℍ[ℝ]) - 1‖ ≤ m₂ := by
    have := norm_coe_expUnit_sub_one_le (-x₂)
    rwa [← hw, neg2] at this
  have hb₁ : ‖(A₁ : ℍ[ℝ]) - 1 - v‖ ≤ m₁ ^ 2 := by
    have := norm_expUnit_sub_one_sub_le (ξ := -x₁) (by rw [← hv, neg1]; linarith)
    rwa [← hv, neg1] at this
  have hb₂ : ‖(A₂ : ℍ[ℝ]) - 1 - w‖ ≤ m₂ ^ 2 := by
    have := norm_expUnit_sub_one_sub_le (ξ := -x₂) (by rw [← hw, neg2]; linarith)
    rwa [← hw, neg2] at this
  set p := ‖((μ : UnitQuaternion) : ℍ[ℝ]) - 1‖ with hp
  have hPp : ‖(P : ℍ[ℝ]) - 1‖ = p := norm_coe_inv_sub_one μ
  have hp0 : 0 ≤ p := norm_nonneg _
  set d := ‖(A₃ : ℍ[ℝ]) - A₁ - A₂ + 1‖ with hdd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hE : d * ‖(P : ℍ[ℝ]) - 1‖ + (‖(A₁ : ℍ[ℝ]) - 1‖ + ‖(A₂ : ℍ[ℝ]) - 1‖) * d + d ^ 2 / 2 +
      ‖(A₁ : ℍ[ℝ]) - 1 - v‖ * ‖(A₂ : ℍ[ℝ]) - 1‖ + ‖v‖ * ‖(A₂ : ℍ[ℝ]) - 1 - w‖ ≤
      8256 * m₁ * m₂ * p + cubicRemainder m₁ m₂ := by
    rw [hPp, neg1]
    have a1 : d * p ≤ 8256 * m₁ * m₂ * p := mul_le_mul_of_nonneg_right hd hp0
    have a2 : (‖(A₁ : ℍ[ℝ]) - 1‖ + ‖(A₂ : ℍ[ℝ]) - 1‖) * d ≤ (m₁ + m₂) * (8256 * m₁ * m₂) :=
      mul_le_mul (add_le_add he₁ he₂) hd hd0 (by positivity)
    have a3 : d ^ 2 / 2 ≤ (8256 * m₁ * m₂) ^ 2 / 2 := by
      have := pow_le_pow_left₀ hd0 hd 2
      linarith
    have a4 : ‖(A₁ : ℍ[ℝ]) - 1 - v‖ * ‖(A₂ : ℍ[ℝ]) - 1‖ ≤ m₁ ^ 2 * m₂ :=
      mul_le_mul hb₁ he₂ (norm_nonneg _) (by positivity)
    have a5 : m₁ * ‖(A₂ : ℍ[ℝ]) - 1 - w‖ ≤ m₁ * m₂ ^ 2 := mul_le_mul_of_nonneg_left hb₂ m10
    simp only [cubicRemainder]
    linarith
  have key := abs_weighted_secondDifference_sub_inner_le r₀ ρ₁ ρ₂ ρ₃ A₁ A₂ A₃ P v w hE
  have einn : inner ℝ v w = inner ℝ (x₁ : ℍ[ℝ]) (x₂ : ℍ[ℝ]) := by
    have e1 : v = -(x₁ : ℍ[ℝ]) := rfl
    have e2 : w = -(x₂ : ℍ[ℝ]) := rfl
    rw [e1, e2, inner_neg_neg]
  rw [t1, t2, t3, t0, ← einn]
  refine key.trans ?_
  rw [hPp]
  set E := 8256 * m₁ * m₂ * p + cubicRemainder m₁ m₂ with hEd
  have hQ0 : 0 ≤ cubicRemainder m₁ m₂ := by
    simp only [cubicRemainder]
    positivity
  have hE0 : 0 ≤ E := by positivity
  have hi : |inner ℝ v w| ≤ m₁ * m₂ := by
    have := abs_real_inner_le_norm v w
    rwa [neg1, neg2] at this
  set a := |r₀ - 1| with hadef
  have ha0 : 0 ≤ a := abs_nonneg _
  set R₃ := 200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c (levelDeviation R (realChart W₃) j) ^ 2 +
      σ * bondHullNorm c (levelDeviation R (realChart W₃) j)) with hR₃
  have hρ3 : |ρ₃| ≤ R₃ := r3
  have hR0 : 0 ≤ R₃ := (abs_nonneg _).trans hρ3
  have hρ30 := abs_nonneg ρ₃
  have b1 : (a + |ρ₃|) * (|inner ℝ v w| + E) + E ≤ (a + R₃) * (m₁ * m₂) + 3 * E := by
    have c1 : (a + |ρ₃|) * (|inner ℝ v w| + E) ≤ (a + R₃) * (m₁ * m₂ + E) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have c2 : (a + R₃) * E ≤ 2 * E := mul_le_mul_of_nonneg_right (by linarith) hE0
    nlinarith
  have b2 : p ^ 2 / 2 * |ρ₃ - ρ₁ - ρ₂| ≤ p ^ 2 / 2 * _ := mul_le_mul_of_nonneg_left r12 (by positivity)
  have b3 : |ρ₃ - ρ₁| * (‖(A₁ : ℍ[ℝ]) - 1‖ ^ 2 / 2 + ‖(A₁ : ℍ[ℝ]) - 1‖ * p) ≤
      12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
        bondHullNorm c (levelDeviation R (realChart W₃) j - levelDeviation R (realChart W₁) j) *
        (m₁ ^ 2 / 2 + m₁ * p) := by
    refine mul_le_mul r1 ?_ (by positivity) ((abs_nonneg _).trans r1)
    have := pow_le_pow_left₀ (norm_nonneg _) he₁ 2
    have := mul_le_mul_of_nonneg_right he₁ hp0
    linarith
  have b4 : |ρ₃ - ρ₂| * (‖(A₂ : ℍ[ℝ]) - 1‖ ^ 2 / 2 + ‖(A₂ : ℍ[ℝ]) - 1‖ * p) ≤
      12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
        bondHullNorm c (levelDeviation R (realChart W₃) j - levelDeviation R (realChart W₂) j) *
        (m₂ ^ 2 / 2 + m₂ * p) := by
    refine mul_le_mul r2 ?_ (by positivity) ((abs_nonneg _).trans r2)
    have := pow_le_pow_left₀ (norm_nonneg _) he₂ 2
    have := mul_le_mul_of_nonneg_right he₂ hp0
    linarith
  have b5 : 3 * E = 24768 * p * (m₁ * m₂) + 3 * cubicRemainder m₁ m₂ := by
    rw [hEd]
    ring
  exact bound_assemble_of_lt_top b1 b2 b3 b4 b5
set_option maxHeartbeats 4000000 in
theorem abs_bondEnergy_secondDifference_sub_inner_le_top (V : F.GaugeField F.top) (hV : R F.top = V)
    (hj : j + 1 = F.top) (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (R j) (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ)
    (ht : 0 ≤ t) (hsm : 24 * (2 * t + σ) < hullBallRadius F.blockSide)
    (h1 : bondHullNorm c (levelDeviation R (realChart W₁) j) ≤ t)
    (h2 : bondHullNorm c (levelDeviation R (realChart W₂) j) ≤ t)
    (h3 : bondHullNorm c (levelDeviation R (realChart W₃) j) ≤ 2 * t)
    (hK₁ : 200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c (levelDeviation R (realChart W₁) j) + σ) ≤ 1)
    (hK₂ : 200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c (levelDeviation R (realChart W₂) j) + σ) ≤ 1)
    {Dd E : ℝ}
    (hDd : lineBlockAverage (fun x d => ‖(levelDeviation R (realChart W₃) j -
        (levelDeviation R (realChart W₁) j + levelDeviation R (realChart W₂) j)) x d‖) c +
      (12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
          bondHullNorm c (levelDeviation R (realChart W₃) j -
            (levelDeviation R (realChart W₁) j + levelDeviation R (realChart W₂) j)) +
        64 * (200000 * (F.blockSide : ℝ) ^ 2) * bondHullNorm c (levelDeviation R (realChart W₁) j) *
          bondHullNorm c (levelDeviation R (realChart W₂) j)) ≤ Dd)
    (hEd : Dd * ‖((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
        (2 * bondHullNorm c (levelDeviation R (realChart W₁) j) +
        2 * bondHullNorm c (levelDeviation R (realChart W₂) j)) * Dd + Dd ^ 2 / 2 +
        ‖((bondAverageGap R W₁ j c : UnitQuaternion) : ℍ[ℝ]) - 1 - linearPart R W₁ (j + 1) c.1 c.2‖ *
          (2 * bondHullNorm c (levelDeviation R (realChart W₂) j)) +
        ‖linearPart R W₁ (j + 1) c.1 c.2‖ *
          ‖((bondAverageGap R W₂ j c : UnitQuaternion) : ℍ[ℝ]) - 1 - linearPart R W₂ (j + 1) c.1 c.2‖ ≤ E) :
    |bondEnergy R W₃ V j c - bondEnergy R W₁ V j c - bondEnergy R W₂ V j c + bondEnergy R (zeroChart F) V j c -
        inner ℝ (linearPart R W₁ (j + 1) c.1 c.2) (linearPart R W₂ (j + 1) c.1 c.2)| ≤
      (|‖contourAverage (R j) c‖ - 1| + 200000 * (F.blockSide : ℝ) ^ 2 *
            (bondHullNorm c (levelDeviation R (realChart W₃) j) ^ 2 +
            σ * bondHullNorm c (levelDeviation R (realChart W₃) j))) *
          (‖linearPart R W₁ (j + 1) c.1 c.2‖ * ‖linearPart R W₂ (j + 1) c.1 c.2‖ + E) + E +
        ‖((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 / 2 *
          (12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
              bondHullNorm c (levelDeviation R (realChart W₃) j -
                (levelDeviation R (realChart W₁) j + levelDeviation R (realChart W₂) j)) +
            64 * (200000 * (F.blockSide : ℝ) ^ 2) * bondHullNorm c (levelDeviation R (realChart W₁) j) *
              bondHullNorm c (levelDeviation R (realChart W₂) j)) +
        12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
          bondHullNorm c (levelDeviation R (realChart W₃) j - levelDeviation R (realChart W₁) j) *
          ((2 * bondHullNorm c (levelDeviation R (realChart W₁) j)) ^ 2 / 2 +
            2 * bondHullNorm c (levelDeviation R (realChart W₁) j) *
              ‖((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖) +
        12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * t + σ) *
          bondHullNorm c (levelDeviation R (realChart W₃) j - levelDeviation R (realChart W₂) j) *
          ((2 * bondHullNorm c (levelDeviation R (realChart W₂) j)) ^ 2 / 2 +
            2 * bondHullNorm c (levelDeviation R (realChart W₂) j) *
              ‖((referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖) := by
  have hj' : j + 1 ≤ F.top := hj.le
  obtain ⟨r3, r1, r2, r12⟩ :=
    sqrtRemainder_bounds (W₁ := W₁) (W₂ := W₂) (W₃ := W₃) hodd hj' hσ0 hσ href ht hsm h1 h2 h3
  have hd := norm_bondAverageGap_second_diff_le (W₁ := W₁) (W₂ := W₂) (W₃ := W₃) hodd hj' hσ0 hσ href ht hsm
    h1 h2 h3
  have hsmall : ∀ W : ChainChart F, bondHullNorm c (levelDeviation R (realChart W) j) ≤ 2 * t →
      8 * (F.blockSide : ℝ) * bondHullNorm c (levelDeviation R (realChart W) j) ≤ 1 / 1024 :=
    fun W hW => eight_mul_le_of_lt_hullBallRadius hodd (by linarith)
  have hne : ∀ W : ChainChart F, bondHullNorm c (levelDeviation R (realChart W) j) ≤ 2 * t →
      gaugedBondAverage R W j c ≠ 0 :=
    fun W hW => gaugedBondAverage_ne_zero hodd hj' W hσ href (hsmall W hW)
  have n1 := hne W₁ (by linarith)
  have n2 := hne W₂ (by linarith)
  have n3 := hne W₃ h3
  have n0 : gaugedBondAverage R (zeroChart F) j c ≠ 0 := hne _ (by
    rw [levelDeviation_zeroChart hodd, bondHullNorm_zero_field]
    positivity)
  have he : ∀ W : ChainChart F, bondHullNorm c (levelDeviation R (realChart W) j) ≤ 2 * t →
      200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c (levelDeviation R (realChart W) j) + σ) ≤ 1 →
      ‖((bondAverageGap R W j c : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        2 * bondHullNorm c (levelDeviation R (realChart W) j) := by
    intro W hW hKW
    have := norm_linearizedUnit_sub_one_le hodd R W hj' hσ href (hsmall W hW) hKW
    rwa [linearizedUnit_realChart hodd hj', norm_ofUnit_sub_one] at this
  have he₁ := he W₁ (by linarith) hK₁
  have he₂ := he W₂ (by linarith) hK₂
  have t1 : bondEnergy R W₁ V j c = (‖contourAverage (R j) c‖ +
      (‖gaugedBondAverage R W₁ j c‖ - ‖contourAverage (R j) c‖)) *
      (1 - ((bondAverageGap R W₁ j c * (referenceDefect R j c)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re) := by
    rw [add_sub_cancel]
    exact gaugedBlockFit_chartChain_top R W₁ V hV hj c n1
  have t2 : bondEnergy R W₂ V j c = (‖contourAverage (R j) c‖ +
      (‖gaugedBondAverage R W₂ j c‖ - ‖contourAverage (R j) c‖)) *
      (1 - ((bondAverageGap R W₂ j c * (referenceDefect R j c)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re) := by
    rw [add_sub_cancel]
    exact gaugedBlockFit_chartChain_top R W₂ V hV hj c n2
  have t3 : bondEnergy R W₃ V j c = (‖contourAverage (R j) c‖ +
      (‖gaugedBondAverage R W₃ j c‖ - ‖contourAverage (R j) c‖)) *
      (1 - ((bondAverageGap R W₃ j c * (referenceDefect R j c)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re) := by
    rw [add_sub_cancel]
    exact gaugedBlockFit_chartChain_top R W₃ V hV hj c n3
  have t0 : bondEnergy R (zeroChart F) V j c = ‖contourAverage (R j) c‖ *
      (1 - (((referenceDefect R j c)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re) := by
    have := gaugedBlockFit_chartChain_top R (zeroChart F) V hV hj c n0
    rw [bondAverageGap_zeroChart hodd, one_mul, gaugedBondAverage_zeroChart hodd] at this
    exact this
  rw [t1, t2, t3, t0]
  exact abs_fit_secondDifference_sub_inner_le (norm_coe_inv_sub_one _) r3 r1 r2 r12 he₁ he₂ (hd.trans hDd) hEd
end Bond
end YangMills.Construction.BondSecondDifference
end
