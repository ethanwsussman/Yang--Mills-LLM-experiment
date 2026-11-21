import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesOfEveryLevelProof
import YangMills.Construction.ColdChainAtEveryLevel.WeightSumsOverTheLevels
import YangMills.Construction.ColdChainAtEveryLevel.WeightedRecursion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LevelRecursion
open YangMills.Construction.BlockAverages YangMills.Construction.BlockLines YangMills.Construction.WeightedAverages.Sums YangMills.Construction.WeightedAverages.Chains
variable {F : BlockFrame}
theorem finsetLpNorm_const_mul {ι : Type} {P : ℕ} (hP : 1 ≤ P) (s : Finset ι) (f : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    finsetLpNorm P s (fun i => c * f i) = c * finsetLpNorm P s f := by
  unfold finsetLpNorm
  have hP0 : (P : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  have e : ∑ i ∈ s, |c * f i| ^ P = c ^ P * ∑ i ∈ s, |f i| ^ P := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_mul, abs_of_nonneg hc, mul_pow]
  rw [e, Real.mul_rpow (by positivity) (Finset.sum_nonneg fun _ _ => by positivity), ← Real.rpow_natCast c P,
    ← Real.rpow_mul hc, mul_one_div_cancel hP0, Real.rpow_one]
theorem weightedScaleNorm_const_mul {P : ℕ} (hP : 1 ≤ P) (D : Finset F.Cell) (p : F.Site 0) (ϑ : ℝ) (m : ℕ)
    (f : F.Site m → Fin 4 → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    weightedScaleNorm D p ϑ P m (fun x i => c * f x i) = c * weightedScaleNorm D p ϑ P m f := by
  unfold weightedScaleNorm
  rw [← finsetLpNorm_const_mul hP _ _ hc]
  congr 1
  funext b
  ring
theorem weightedScaleNorm_mono_of_abs_le {P : ℕ} (hP : 1 ≤ P) (D : Finset F.Cell) (p : F.Site 0) (ϑ : ℝ) (m : ℕ)
    {f g : F.Site m → Fin 4 → ℝ} (h : ∀ b ∈ innerBonds D m, |f b.1 b.2| ≤ |g b.1 b.2|) :
    weightedScaleNorm D p ϑ P m f ≤ weightedScaleNorm D p ϑ P m g := by
  unfold weightedScaleNorm
  refine finsetLpNorm_mono hP _ fun b hb => ?_
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (h b hb) (abs_nonneg _)
theorem card_innerBonds_le_of_card_le (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81) (l : ℕ) :
    ((innerBonds D l).card : ℝ) ≤ 324 * (((F.blockSide ^ (F.top - l) : ℕ) : ℝ)) ^ 4 := by
  have h1 := card_innerBonds_le hodd D l
  have h2 : ((innerBonds D l).card : ℝ) ≤
      4 * ((D.card : ℝ) * (((F.blockSide ^ (F.top - l) : ℕ) : ℝ)) ^ 4) := by
    exact_mod_cast h1
  have h3 : (D.card : ℝ) ≤ 81 := by exact_mod_cast hD
  have h4 : (D.card : ℝ) * (((F.blockSide ^ (F.top - l) : ℕ) : ℝ)) ^ 4 ≤
      81 * (((F.blockSide ^ (F.top - l) : ℕ) : ℝ)) ^ 4 :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  linarith
theorem sqrt_sqrt_le_of_le_pow_four {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 4) : Real.sqrt (Real.sqrt x) ≤ y := by apply _root_.YangMills.Construction.BlockAverages.LevelCoordinates.sqrt_sqrt_le_of_le_pow_four <;> assumption
theorem finsetLpNorm_four_le_of_abs_le {ι : Type} (s : Finset ι) (f : ι → ℝ) {x Q : ℝ} (hx : 0 ≤ x) (hQ : 0 ≤ Q)
    (hf : ∀ i ∈ s, |f i| ≤ x) (hs : (s.card : ℝ) ≤ 324 * Q ^ 4) : finsetLpNorm 4 s f ≤ 5 * Q * x := by
  rw [finsetLpNorm_four_eq_sqrt_sqrt]
  refine sqrt_sqrt_le_of_le_pow_four (by positivity) ?_
  calc ∑ i ∈ s, f i ^ 4 ≤ ∑ _i ∈ s, x ^ 4 := Finset.sum_le_sum fun i hi => by
        have h1 : f i ^ 4 = |f i| ^ 4 := by
          rw [← abs_pow, abs_of_nonneg (by positivity)]
        rw [h1]
        exact pow_le_pow_left₀ (abs_nonneg _) (hf i hi) 4
    _ = (s.card : ℝ) * x ^ 4 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (324 * Q ^ 4) * x ^ 4 := mul_le_mul_of_nonneg_right hs (by positivity)
    _ ≤ _ := by
        have : 0 ≤ Q ^ 4 * x ^ 4 := by positivity
        nlinarith
theorem finsetLpNorm_two_le_four {ι : Type} (s : Finset ι) (f : ι → ℝ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hs : (s.card : ℝ) ≤ 324 * Q ^ 4) : finsetLpNorm 2 s f ≤ 5 * Q * finsetLpNorm 4 s f := by
  rw [finsetLpNorm_two_eq_sqrt, finsetLpNorm_four_eq_sqrt_sqrt]
  set T := ∑ i ∈ s, f i ^ 4 with hT
  have h1 : ∑ i ∈ s, f i ^ 2 ≤ Real.sqrt (s.card : ℝ) * Real.sqrt T := by
    have := Real.sum_mul_le_sqrt_mul_sqrt s (fun _ => (1 : ℝ)) (fun i => f i ^ 2)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at this
    refine this.trans (le_of_eq ?_)
    congr 2
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : Real.sqrt (s.card : ℝ) ≤ 18 * Q ^ 2 := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg (Q ^ 2)]
  have h3 : ∑ i ∈ s, f i ^ 2 ≤ 18 * Q ^ 2 * Real.sqrt T :=
    h1.trans (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _))
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have h4 : (Real.sqrt (Real.sqrt T)) ^ 2 = Real.sqrt T := Real.sq_sqrt (Real.sqrt_nonneg _)
  calc _ ≤ 18 * Q ^ 2 * Real.sqrt T := h3
    _ ≤ 25 * Q ^ 2 * Real.sqrt T := by
        have : 0 ≤ Q ^ 2 * Real.sqrt T := by positivity
        nlinarith
    _ = _ := by
        rw [mul_pow, mul_pow, h4]
        ring
theorem weightedScaleNorm_two_le_four (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81) (p : F.Site 0)
    (ϑ : ℝ) (l : ℕ) (f : F.Site l → Fin 4 → ℝ) :
    weightedScaleNorm D p ϑ 2 l f ≤
      5 * ((F.blockSide ^ (F.top - l) : ℕ) : ℝ) * weightedScaleNorm D p ϑ 4 l f :=
  finsetLpNorm_two_le_four _ _ (by positivity) (card_innerBonds_le_of_card_le hodd hD l)
theorem sum_innerBonds_le_weightedScaleNorm (hodd : Odd F.blockSide) {l : ℕ} (hl : l ≤ F.top) {D : Finset F.Cell}
    (hD : D.card ≤ 81) (p : F.Site 0) {θ : ℝ} (h0 : 0 ≤ θ) (h8 : θ ≤ 1 / 8) {f : F.Site l → Fin 4 → ℝ}
    (hf : ∀ x i, 0 ≤ f x i) :
    ∑ b ∈ innerBonds D l, f b.1 b.2 ≤
      48 * ((F.blockSide ^ (F.top - l) : ℕ) : ℝ) ^ 2 * ((F.blockSide : ℝ) ^ F.top) ^ (-θ) *
        weightedScaleNorm D p (-θ) 2 l f := by
  have hL := hodd.pos
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hN0 : 0 < N := by positivity
  set Q : ℝ := ((F.blockSide ^ (F.top - l) : ℕ) : ℝ) with hQ
  have hr : ∀ x : F.Site l, 0 < scaleRadius F l p x := fun x => scaleRadius_pos hL l p x
  have h1 : ∑ b ∈ innerBonds D l, f b.1 b.2 ≤
      Real.sqrt (∑ b ∈ innerBonds D l, (scaleRadius F l p b.1 ^ (-θ)) ^ 2) *
        Real.sqrt (∑ b ∈ innerBonds D l, (scaleWeight p (-θ) l b.1 * f b.1 b.2) ^ 2) := by
    refine le_trans (le_of_eq ?_) (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)
    refine Finset.sum_congr rfl fun b _ => ?_
    have : scaleRadius F l p b.1 ^ (-θ) * scaleWeight p (-θ) l b.1 = 1 := by
      unfold scaleWeight
      rw [neg_neg, ← Real.rpow_add (hr _)]
      simp
    rw [← mul_assoc, this, one_mul]
  have h2 : ∑ b ∈ innerBonds D l, (scaleRadius F l p b.1 ^ (-θ)) ^ 2 ≤ (N ^ (-θ)) ^ 2 * (2248 * Q ^ 4) := by
    have h3 := sum_innerBonds_scaleRadius_rpow_neg_le hodd hl hD p (e := 2 * θ) (by positivity) (by linarith)
    have e : ∀ b ∈ innerBonds D l, (scaleRadius F l p b.1 ^ (-θ)) ^ 2 =
        (N ^ (-θ)) ^ 2 * (scaleRadius F l p b.1 / N) ^ (-(2 * θ)) := by
      intro b _
      rw [Real.div_rpow (hr _).le hN0.le, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (hr _).le,
        ← Real.rpow_mul hN0.le, mul_div_assoc']
      have e2 : -θ * ((2 : ℕ) : ℝ) = -(2 * θ) := by
        push_cast
        ring
      rw [e2]
      field_simp
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have h4 : Real.sqrt (∑ b ∈ innerBonds D l, (scaleRadius F l p b.1 ^ (-θ)) ^ 2) ≤ 48 * Q ^ 2 * N ^ (-θ) := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, h2.trans ?_⟩
    have : 0 ≤ (N ^ (-θ)) ^ 2 * Q ^ 4 := by positivity
    nlinarith
  refine h1.trans ?_
  have e : Real.sqrt (∑ b ∈ innerBonds D l, (scaleWeight p (-θ) l b.1 * f b.1 b.2) ^ 2) =
      weightedScaleNorm D p (-θ) 2 l f := by
    unfold weightedScaleNorm
    rw [finsetLpNorm_two_eq_sqrt]
  rw [e]
  exact mul_le_mul_of_nonneg_right h4 (finsetLpNorm_nonneg _ _ _)
end YangMills.Construction.LevelRecursion
end
