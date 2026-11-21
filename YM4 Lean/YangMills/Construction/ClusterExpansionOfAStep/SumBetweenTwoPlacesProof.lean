import YangMills.Construction.ClusterExpansionOfAStep.SumBetweenTwoPlaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.DecayingPairSums
theorem doubleSum_le_of_one_side {ι Y : Type} [Fintype ι] (β : ι → Y) (dist : Y → Y → ℝ) (P P' : Finset Y)
    (f g : ι → ℝ) (κ A W D : ℝ) (hnn : ∀ y y', 0 ≤ dist y y') (hs : ∀ y y', dist y y' = dist y' y)
    (ht : ∀ y y' y'', dist y y'' ≤ dist y y' + dist y' y'') (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hsum : ∀ y, ∑ b, Real.exp (-(κ / 2 * dist (β b) y)) ≤ W) (hD : ∀ y ∈ P, ∀ y' ∈ P', D ≤ dist y y')
    (hf0 : ∀ b, 0 ≤ f b) (hg0 : ∀ b, 0 ≤ g b)
    (hf : ∀ b, f b = 0 ∨ ∃ y ∈ P, f b ≤ A * Real.exp (-(2 * κ * dist (β b) y)))
    (hg : ∀ b, g b = 0 ∨ ∃ y ∈ P', g b ≤ A * Real.exp (-(2 * κ * dist (β b) y))) :
    ∑ b, ∑ b', f b * Real.exp (-(κ * dist (β b) (β b'))) * g b' ≤
      A ^ 2 * W ^ 2 * P.card * Real.exp (-(κ * D / 2)) := by
  set E : ℝ := Real.exp (-(κ * D / 2)) with hE
  set S : ι → ℝ := fun b => ∑ y ∈ P, Real.exp (-(κ / 2 * dist (β b) y)) with hS
  have hSn : ∀ b, 0 ≤ S b := fun b => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have key : ∀ b b', f b * Real.exp (-(κ * dist (β b) (β b'))) * g b' ≤
      A ^ 2 * E * S b * Real.exp (-(κ / 2 * dist (β b) (β b'))) := by
    intro b b'
    have hR : 0 ≤ A ^ 2 * E * S b * Real.exp (-(κ / 2 * dist (β b) (β b'))) := by
      have := hSn b
      positivity
    rcases hf b with h0 | ⟨y, hy, hfb⟩
    · rw [h0]
      simpa using hR
    rcases hg b' with h0 | ⟨y', hy', hgb⟩
    · rw [h0]
      simpa using hR
    set d1 := dist (β b) y
    set d2 := dist (β b) (β b')
    set d3 := dist (β b') y'
    have hd1 : 0 ≤ d1 := hnn _ _
    have hd2 : 0 ≤ d2 := hnn _ _
    have hd3 : 0 ≤ d3 := hnn _ _
    have htri : D ≤ d1 + d2 + d3 := by
      have h1 := hD y hy y' hy'
      have h2 := ht y (β b) y'
      have h3 := ht (β b) (β b') y'
      have h4 : dist y (β b) = d1 := hs _ _
      linarith
    have hSy : Real.exp (-(κ / 2 * d1)) ≤ S b :=
      Finset.single_le_sum (f := fun y => Real.exp (-(κ / 2 * dist (β b) y)))
        (fun _ _ => (Real.exp_pos _).le) hy
    calc f b * Real.exp (-(κ * d2)) * g b'
        ≤ (A * Real.exp (-(2 * κ * d1))) * Real.exp (-(κ * d2)) * (A * Real.exp (-(2 * κ * d3))) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hfb (Real.exp_pos _).le) hgb (hg0 b')
            (mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (Real.exp_pos _).le)
      _ = A ^ 2 * Real.exp (-(2 * κ * d1) + -(κ * d2) + -(2 * κ * d3)) := by
          rw [Real.exp_add, Real.exp_add]
          ring
      _ ≤ A ^ 2 * Real.exp (-(κ * D / 2) + -(κ / 2 * d1) + -(κ / 2 * d2)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          have h5 := mul_le_mul_of_nonneg_left htri hκ
          nlinarith [mul_nonneg hκ hd1, mul_nonneg hκ hd2, mul_nonneg hκ hd3]
      _ = A ^ 2 * E * Real.exp (-(κ / 2 * d1)) * Real.exp (-(κ / 2 * d2)) := by
          rw [Real.exp_add, Real.exp_add]
          ring
      _ ≤ A ^ 2 * E * S b * Real.exp (-(κ / 2 * d2)) := by
          gcongr
  have hsym : ∀ b, ∑ b', Real.exp (-(κ / 2 * dist (β b) (β b'))) ≤ W := by
    intro b
    have := hsum (β b)
    refine le_of_eq_of_le (Finset.sum_congr rfl fun b' _ => ?_) this
    rw [hs (β b) (β b')]
  have step1 : ∀ b, ∑ b', f b * Real.exp (-(κ * dist (β b) (β b'))) * g b' ≤ A ^ 2 * E * S b * W := by
    intro b
    refine (Finset.sum_le_sum fun b' _ => key b b').trans ?_
    rw [← Finset.mul_sum]
    have h1 := hsym b
    have := hSn b
    gcongr
  refine (Finset.sum_le_sum fun b _ => step1 b).trans ?_
  have h2 : ∑ b, S b ≤ P.card * W := by
    simp only [hS]
    rw [Finset.sum_comm]
    calc ∑ y ∈ P, ∑ b, Real.exp (-(κ / 2 * dist (β b) y)) ≤ ∑ y ∈ P, W :=
          Finset.sum_le_sum fun y _ => hsum y
      _ = P.card * W := by simp
  calc ∑ b, A ^ 2 * E * S b * W = A ^ 2 * E * W * ∑ b, S b := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ A ^ 2 * E * W * (P.card * W) := by gcongr
    _ = A ^ 2 * W ^ 2 * P.card * E := by ring
theorem doubleSumBoundBySeparation_holds : DoubleSumBoundBySeparation := by
  intro ι Y _ β dist P P' f g κ A W D hnn hs ht hκ hA hW hsum hD hf0 hg0 hf hg
  have h1 := doubleSum_le_of_one_side β dist P P' f g κ A W D hnn hs ht hκ hA hW hsum hD hf0 hg0 hf hg
  have h2 := doubleSum_le_of_one_side β dist P' P g f κ A W D hnn hs ht hκ hA hW hsum
    (fun y hy y' hy' => by rw [hs]; exact hD y' hy' y hy) hg0 hf0 hg hf
  have h3 : ∑ b, ∑ b', g b * Real.exp (-(κ * dist (β b) (β b'))) * f b' =
      ∑ b, ∑ b', f b * Real.exp (-(κ * dist (β b) (β b'))) * g b' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [hs (β b') (β b)]
    ring
  rw [h3] at h2
  rcases le_total (P.card : ℝ) P'.card with h | h
  · rw [min_eq_left h]
    exact h1
  · rw [min_eq_right h]
    exact h2
end YangMills.Construction.DecayingPairSums
end
