import YangMills.Construction.LawByMomentsOfTheFlow.CumulantByTheGaussianChain
import YangMills.Construction.LawByMomentsOfTheFlow.LawInTheComponentsProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsByTheGaussianChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusLumps
private theorem abs_prod_sub_prod_le_card_mul {α : Type} [DecidableEq α] (s : Finset α) (a b u : α → ℝ) (w : ℝ)
    (hw : 0 ≤ w) (ha : ∀ i ∈ s, |a i| ≤ u i) (hb : ∀ i ∈ s, |b i| ≤ u i)
    (hd : ∀ i ∈ s, |a i - b i| ≤ w * u i) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ (s.card : ℝ) * w * ∏ i ∈ s, u i := by apply _root_.YangMills.SharedProofs.p34157 <;> assumption
private def partitionSumBound (k : ℕ) (M : ℝ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin k)),
    ((π.parts.card - 1).factorial : ℝ) * (π.parts.card : ℝ) * M ^ π.parts.card
private theorem partitionSumBound_nonneg (k : ℕ) {M : ℝ} (hM : 0 ≤ M) : 0 ≤ partitionSumBound k M :=
  Finset.sum_nonneg fun _ _ => by positivity
private theorem abs_scaled_cumulant_sub_le {k : ℕ} (m₁ m₂ : Finset (Fin k) → ℝ) (x r M : ℝ)
    (hx : 1 ≤ x) (hr : 0 ≤ r) (hM : 1 ≤ M)
    (hd : ∀ B : Finset (Fin k), |x ^ B.card * m₁ B - m₂ B| ≤
      M * r ^ (4 * B.card + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ))
    (h₁ : ∀ B : Finset (Fin k), |x ^ B.card * m₁ B| ≤ M * r ^ (4 * B.card) * x ^ ((1 : ℝ) / 1000))
    (h₂ : ∀ B : Finset (Fin k), |m₂ B| ≤ M * r ^ (4 * B.card) * x ^ ((1 : ℝ) / 1000)) :
    |x ^ k * (∑ π : Finpartition (Finset.univ : Finset (Fin k)), (-1 : ℝ) ^ (π.parts.card - 1) *
        ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, m₁ J) -
      ∑ π : Finpartition (Finset.univ : Finset (Fin k)), (-1 : ℝ) ^ (π.parts.card - 1) *
        ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, m₂ J| ≤
      partitionSumBound k M * r ^ (4 * k + 3) * x ^ (-(1 / 2) + ((k : ℝ) + 1) / 1000) := by apply _root_.YangMills.DeltaSharedProofs.p501138 <;> assumption
private theorem clusterRange_le_two_mul_rpow {x : ℝ} (hx : 1 ≤ x) :
    (clusterRange x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100) := by apply _root_.YangMills.SharedProofs.p52588 <;> assumption
private theorem range_pow_mul_rpow_le {x r : ℝ} {n : ℕ} (hx : 1 ≤ x) (hr0 : 0 ≤ r)
    (hr : r ≤ 2 * x ^ ((1 : ℝ) / 100)) (hn : n ≤ 8) :
    r ^ (4 * n + 3) * x ^ (-(1 / 2) + ((n : ℝ) + 1) / 1000) ≤ 2 ^ (4 * n + 3) * x ^ (-(1 / 10) : ℝ) := by apply _root_.YangMills.SharedProofs.p93516 <;> assumption
private theorem ForAllHullParameters.mono_of_le_eight {Q₁ Q₂ : MomentParameters → Prop}
    (H : ForAllHullParameters Q₁) (f : ∀ Λ : MomentParameters, Λ.k ≤ 8 → Q₁ Λ → Q₂ Λ) :
    ForAllHullParameters Q₂ := by apply _root_.YangMills.SharedProofs.p30752 <;> assumption
theorem cumulantByGaussianChain_of_moments (h : gaussianChainMomentsStatement) :
    cumulantByGaussianChainStatement := by
  unfold gaussianChainMomentsStatement ForAllHullPoints at h
  unfold cumulantByGaussianChainStatement ForAllHullPoints
  refine ForAllHullParameters.mono_of_le_eight h fun Λ hk H => ?_
  obtain ⟨C, c, X₀, hc, hyX, H⟩ := H
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max |C 0| |C 1| + 1 := ⟨_, rfl⟩
  have hC0 : C 0 ≤ M := by
    have := le_abs_self (C 0)
    have := le_max_left |C 0| |C 1|
    linarith
  have hC1 : C 1 ≤ M := by
    have := le_abs_self (C 1)
    have := le_max_right |C 0| |C 1|
    linarith
  have hM : 1 ≤ M := by
    have := abs_nonneg (C 0)
    have := le_max_left |C 0| |C 1|
    linarith
  have hK := partitionSumBound_nonneg Λ.k (by linarith : (0 : ℝ) ≤ M)
  refine ⟨fun i => if i = 0 then partitionSumBound Λ.k M else partitionSumBound Λ.k M * 2 ^ (4 * Λ.k + 3),
    c, max X₀ 1, hc, hyX.trans (le_max_left _ _), ?_⟩
  intro S hS d hd μ hμ
  have hx1 : 1 ≤ S.scaleCoupling := (le_max_right _ _).trans hS
  have hx0 : 0 < S.scaleCoupling := by linarith
  have hB := H S ((le_max_left _ _).trans hS) d hd μ hμ
  have hr0 : (0 : ℝ) ≤ (S.range : ℝ) := Nat.cast_nonneg _
  have hmain : |S.scaleCoupling ^ Λ.k * S.responseCumulant -
      jointCumulant μ (fun i => S.halfForm d (S.data.period Λ.stepParams.side) i)| ≤
      partitionSumBound Λ.k M * (S.range : ℝ) ^ (4 * Λ.k + 3) *
        S.scaleCoupling ^ (-(1 / 2) + ((Λ.k : ℝ) + 1) / 1000) :=
    abs_scaled_cumulant_sub_le
      (fun B => ∫ w, ∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)
        ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)))
      (fun B => ∫ X, ∏ i ∈ B, S.halfForm d (S.data.period Λ.stepParams.side) i X ∂μ) S.scaleCoupling (S.range : ℝ) M hx1 hr0 hM
      (fun B => (hB B).1.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC0 (by positivity)) (Real.rpow_nonneg hx0.le _)))
      (fun B => (hB B).2.1.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC1 (by positivity)) (Real.rpow_nonneg hx0.le _)))
      (fun B => (hB B).2.2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC1 (by positivity)) (Real.rpow_nonneg hx0.le _)))
  have hpow := range_pow_mul_rpow_le hx1 hr0 (clusterRange_le_two_mul_rpow hx1) hk
  refine ⟨hmain, hmain.trans ?_⟩
  calc partitionSumBound Λ.k M * (S.range : ℝ) ^ (4 * Λ.k + 3) *
        S.scaleCoupling ^ (-(1 / 2) + ((Λ.k : ℝ) + 1) / 1000)
      = partitionSumBound Λ.k M * ((S.range : ℝ) ^ (4 * Λ.k + 3) *
          S.scaleCoupling ^ (-(1 / 2) + ((Λ.k : ℝ) + 1) / 1000)) := by
        ring
    _ ≤ partitionSumBound Λ.k M * (2 ^ (4 * Λ.k + 3) * S.scaleCoupling ^ (-(1 / 10) : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow hK
    _ = partitionSumBound Λ.k M * 2 ^ (4 * Λ.k + 3) * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by ring
end YangMills.Construction.MomentLaw
end
