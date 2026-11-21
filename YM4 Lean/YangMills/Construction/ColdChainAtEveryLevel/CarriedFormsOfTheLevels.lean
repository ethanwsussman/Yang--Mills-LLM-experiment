import YangMills.Construction.ColdChainAtEveryLevel.LevelRecursionNearACell
import YangMills.Construction.ColdChainAtEveryLevel.WeightsUpTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
open YangMills.Construction.BlockLines YangMills.Construction.BlockWeights YangMills.Construction.LatticePaths
variable {F : BlockFrame}
def transportedForm (R : F.FieldChain) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) : (j : ℕ) → F.Site j → Fin 4 → ℍ[ℝ]
  | 0 => f
  | j + 1 => fun y i => parallelAverage (R j) (transportedForm R f j) (y, i)
theorem lineBlockAverage_eq {j : ℕ} (g : F.Site j → Fin 4 → ℝ) (c : F.Site (j + 1) × Fin 4) :
    lineBlockAverage g c = (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
      g (lineBond c h r).1 (lineBond c h r).2 := rfl
theorem lineBlockAverage_nonneg {j : ℕ} {g : F.Site j → Fin 4 → ℝ} (hg : ∀ x i, 0 ≤ g x i)
    (c : F.Site (j + 1) × Fin 4) : 0 ≤ lineBlockAverage g c := by
  rw [lineBlockAverage_eq]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hg _ _)
theorem lineBlockAverage_mono {j : ℕ} {g g' : F.Site j → Fin 4 → ℝ} (hle : ∀ x i, g x i ≤ g' x i)
    (c : F.Site (j + 1) × Fin 4) : lineBlockAverage g c ≤ lineBlockAverage g' c := by
  rw [lineBlockAverage_eq, lineBlockAverage_eq]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => hle _ _) (by positivity)
theorem sum_lineBlockAverage_rpow_le {B : Finset F.Cell} {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide)
    (Y : Finset (F.Site (j + 1) × Fin 4)) (hY : Y ⊆ innerBonds B (j + 1)) (g : F.Site j → Fin 4 → ℝ)
    (hg : ∀ x i, 0 ≤ g x i) {p : ℝ} (hp : 1 ≤ p) :
    ∑ c ∈ Y, lineBlockAverage g c ^ p ≤ (F.blockSide : ℝ) ^ (p - 4) * ∑ b ∈ innerBonds B j, g b.1 b.2 ^ p := by
  classical
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  set s : Finset ((Fin 4 → ℤ) × ℕ) := centredCube F.blockSide ×ˢ Finset.range F.blockSide with hs
  have hcard : (s.card : ℝ) = (F.blockSide : ℝ) ^ 5 := by
    rw [hs, Finset.card_product, card_centredCube hodd, Finset.card_range]
    push_cast
    ring
  set φ : (F.Site (j + 1) × Fin 4) → (Fin 4 → ℤ) × ℕ → ℝ := fun c q =>
    g (lineBond c q.1 q.2).1 (lineBond c q.1 q.2).2 with hφ
  have hφ0 : ∀ c q, 0 ≤ φ c q := fun c q => hg _ _
  have hone : ∀ c, lineBlockAverage g c ^ p ≤
      (F.blockSide : ℝ) ^ (p - 4) * ((F.blockSide : ℝ)⁻¹ * ∑ q ∈ s, φ c q ^ p) := by
    intro c
    have h2 : lineBlockAverage g c = (1 / (F.blockSide : ℝ) ^ 4) * ∑ q ∈ s, φ c q := by
      rw [lineBlockAverage_eq, hs, Finset.sum_product]
    have h3 := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s (f := fun q => φ c q) hp (fun q _ => hφ0 c q)
    rw [h2, Real.mul_rpow (by positivity) (Finset.sum_nonneg fun q _ => hφ0 c q)]
    have e : (1 / (F.blockSide : ℝ) ^ 4) ^ p * (s.card : ℝ) ^ (p - 1) =
        (F.blockSide : ℝ) ^ (p - 4) * (F.blockSide : ℝ)⁻¹ := by
      rw [hcard, one_div, ← Real.rpow_natCast (F.blockSide : ℝ) 4, ← Real.rpow_natCast (F.blockSide : ℝ) 5,
        Real.inv_rpow (by positivity), ← Real.rpow_mul hLR.le, ← Real.rpow_mul hLR.le, ← Real.rpow_neg hLR.le,
        ← Real.rpow_add hLR, ← Real.rpow_neg_one (F.blockSide : ℝ), ← Real.rpow_add hLR]
      congr 1
      push_cast
      ring
    calc _ ≤ (1 / (F.blockSide : ℝ) ^ 4) ^ p * ((s.card : ℝ) ^ (p - 1) * ∑ q ∈ s, φ c q ^ p) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ((1 / (F.blockSide : ℝ) ^ 4) ^ p * (s.card : ℝ) ^ (p - 1)) * ∑ q ∈ s, φ c q ^ p := by ring
      _ = _ := by rw [e]; ring
  have hsum : ∑ c ∈ Y, ∑ q ∈ s, φ c q ^ p ≤ F.blockSide * ∑ b ∈ innerBonds B j, g b.1 b.2 ^ p := by
    have e : ∑ c ∈ Y, ∑ q ∈ s, φ c q ^ p = ∑ r ∈ Finset.range F.blockSide, ∑ c ∈ Y, ∑ h ∈ centredCube F.blockSide,
        g (lineBond c h r).1 (lineBond c h r).2 ^ p := by
      calc ∑ c ∈ Y, ∑ q ∈ s, φ c q ^ p
          = ∑ c ∈ Y, ∑ r ∈ Finset.range F.blockSide, ∑ h ∈ centredCube F.blockSide,
              g (lineBond c h r).1 (lineBond c h r).2 ^ p :=
            Finset.sum_congr rfl fun c _ => by
              rw [hs, Finset.sum_product, Finset.sum_comm]
        _ = _ := Finset.sum_comm
    rw [e]
    have hb : ∀ r ∈ Finset.range F.blockSide, ∑ c ∈ Y, ∑ h ∈ centredCube F.blockSide,
        g (lineBond c h r).1 (lineBond c h r).2 ^ p ≤ ∑ b ∈ innerBonds B j, g b.1 b.2 ^ p :=
      fun r hr => sum_lineBond_le hj hodd Y hY (fun b => g b.1 b.2 ^ p) (fun b => Real.rpow_nonneg (hg _ _) _) r
        (Finset.mem_range.1 hr)
    refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ∑ c ∈ Y, lineBlockAverage g c ^ p
      ≤ ∑ c ∈ Y, (F.blockSide : ℝ) ^ (p - 4) * ((F.blockSide : ℝ)⁻¹ * ∑ q ∈ s, φ c q ^ p) :=
        Finset.sum_le_sum fun c _ => hone c
    _ = (F.blockSide : ℝ) ^ (p - 4) * ((F.blockSide : ℝ)⁻¹ * ∑ c ∈ Y, ∑ q ∈ s, φ c q ^ p) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (F.blockSide : ℝ) ^ (p - 4) * ((F.blockSide : ℝ)⁻¹ * (F.blockSide * ∑ b ∈ innerBonds B j, g b.1 b.2 ^ p)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity)
    _ = _ := by
        rw [← mul_assoc ((F.blockSide : ℝ)⁻¹), inv_mul_cancel₀ hLR.ne', one_mul]
theorem sum_lineBlockAverage_pow_four_le {B : Finset F.Cell} {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide)
    (Y : Finset (F.Site (j + 1) × Fin 4)) (hY : Y ⊆ innerBonds B (j + 1)) (g : F.Site j → Fin 4 → ℝ)
    (hg : ∀ x i, 0 ≤ g x i) :
    ∑ c ∈ Y, lineBlockAverage g c ^ 4 ≤ ∑ b ∈ innerBonds B j, g b.1 b.2 ^ 4 := by
  have h := sum_lineBlockAverage_rpow_le hj hodd Y hY g hg (p := 4) (by norm_num)
  have e : ∀ x : ℝ, x ^ (4 : ℝ) = x ^ 4 := fun x => by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [sub_self, Real.rpow_zero, one_mul, e] at h
  exact h
theorem sum_lineBlockAverage_sq_le {B : Finset F.Cell} {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide)
    (Y : Finset (F.Site (j + 1) × Fin 4)) (hY : Y ⊆ innerBonds B (j + 1)) (g : F.Site j → Fin 4 → ℝ)
    (hg : ∀ x i, 0 ≤ g x i) :
    ∑ c ∈ Y, lineBlockAverage g c ^ 2 ≤ (1 / (F.blockSide : ℝ) ^ 2) * ∑ b ∈ innerBonds B j, g b.1 b.2 ^ 2 := by
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have h := sum_lineBlockAverage_rpow_le hj hodd Y hY g hg (p := 2) (by norm_num)
  have e : (F.blockSide : ℝ) ^ ((2 : ℝ) - 4) = 1 / (F.blockSide : ℝ) ^ 2 := by
    rw [show ((2 : ℝ) - 4) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hLR.le, Real.rpow_natCast, one_div]
  have e2 : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e] at h
  simp only [e2] at h
  exact h
theorem adjointAction_mul (a b : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction (a * b) w = adjointAction a (adjointAction b w) := by
  simp only [adjointAction, Submonoid.coe_mul, mul_inv_rev, mul_assoc]
theorem adjointAction_one (w : ℍ[ℝ]) : adjointAction 1 w = w := by simp [adjointAction]
theorem adjointAction_add (g : UnitQuaternion) (x y : ℍ[ℝ]) :
    adjointAction g (x + y) = adjointAction g x + adjointAction g y := by
  simp only [adjointAction, mul_add, add_mul]
theorem adjointAction_smul (g : UnitQuaternion) (t : ℝ) (x : ℍ[ℝ]) :
    adjointAction g (t • x) = t • adjointAction g x := by
  simp only [adjointAction, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
theorem adjointAction_sum {ι : Type*} (g : UnitQuaternion) (s : Finset ι) (f : ι → ℍ[ℝ]) :
    adjointAction g (∑ i ∈ s, f i) = ∑ i ∈ s, adjointAction g (f i) := by
  simp only [adjointAction, Finset.mul_sum, Finset.sum_mul]
theorem shiftedWeight_le_two_mul_of_near (hL : 0 < F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (p : F.Site 0) {j : ℕ} (hj : j ≤ F.top) (x x' : F.Site j)
    (hnear : baseDistance x' p ≤ baseDistance x p + F.blockSide ^ j) :
    shiftedWeight F θ p j x ≤ 2 * shiftedWeight F θ p j x' := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have hp : (0 : ℝ) < (F.blockSide : ℝ) ^ j := by positivity
  have h1 : shiftedRadius F p j x' ≤ 2 * shiftedRadius F p j x := by
    have hd : (baseDistance x' p : ℝ) ≤ (baseDistance x p : ℝ) + (F.blockSide : ℝ) ^ j := by exact_mod_cast hnear
    unfold shiftedRadius
    rcases le_total ((F.blockSide : ℝ) ^ F.top) ((baseDistance x p : ℝ) + 4 * (F.blockSide : ℝ) ^ j) with hc | hc
    · rw [min_eq_left hc]
      refine (min_le_left _ _).trans ?_
      linarith
    · rw [min_eq_right hc]
      refine (min_le_right _ _).trans ?_
      have : (0 : ℝ) ≤ (baseDistance x p : ℝ) := by positivity
      linarith
  have h0 := shiftedRadius_pos hL p j x
  have h0' := shiftedRadius_pos hL p j x'
  have e1 : shiftedWeight F θ p j x' ≥ (2 * (shiftedRadius F p j x / (F.blockSide : ℝ) ^ F.top)) ^ (-θ) := by
    refine rpow_neg_le_rpow_neg (div_pos h0' hN) ?_ hθ
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right h1 hN.le
  rw [Real.mul_rpow (by norm_num) (by positivity)] at e1
  have e2 : (2 : ℝ) ^ (-θ) ≥ 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ge_iff_le, one_div]
    refine inv_anti₀ (by positivity) ?_
    calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
      _ = 2 := Real.rpow_one 2
  have e3 : 0 ≤ shiftedWeight F θ p j x := zero_le_one.trans (one_le_shiftedWeight hL hθ p j x)
  have e4 : (1 / 2) * shiftedWeight F θ p j x ≤ (2 : ℝ) ^ (-θ) * shiftedWeight F θ p j x :=
    mul_le_mul_of_nonneg_right e2 e3
  have e5 : shiftedWeight F θ p j x = (shiftedRadius F p j x / (F.blockSide : ℝ) ^ F.top) ^ (-θ) := rfl
  rw [← e5] at e1
  linarith
end BlockAverages
end YangMills.Construction
end
