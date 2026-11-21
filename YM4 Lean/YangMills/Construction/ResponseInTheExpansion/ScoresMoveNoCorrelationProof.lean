import YangMills.Construction.ResponseInTheExpansion.MeanOfScoresOverAStep
import YangMills.Construction.ResponseInTheExpansion.MeanOverAStepOfTheChain
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheMarksBelowALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts
namespace CorrelationPreservation
theorem measurable_initialField (ℓ : StepParameters) : (s n : ℕ) → Measurable (initialField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => (measurable_initialField ℓ s (n * ℓ.side)).comp measurable_fst
theorem measurable_bondScore_sample (hScore : BondScoreProperties) (ℓ : StepParameters)
    (hadm : ℓ.Admissible) (y : ℝ) (s n : ℕ) [NeZero n] (c : TorusBond n) :
    Measurable fun u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n =>
      bondScore ℓ y (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c := by apply _root_.YangMills.SharedProofs.p2216 <;> assumption
theorem measurable_weightedScoreSum (hScore : BondScoreProperties) (ℓ : StepParameters)
    (hadm : ℓ.Admissible) (x : ℕ → ℝ) {m : ℕ} :
    (s n : ℕ) → [NeZero n] → (w : ScoreWeights ℓ m s n) → (i : Fin m) →
      Measurable (weightedScoreSum ℓ x s n w i)
  | 0, _, _, _, _ => measurable_const
  | s + 1, n, _, w, i =>
    ((measurable_weightedScoreSum hScore ℓ hadm x s (n * ℓ.side) w.1 i).comp measurable_fst).add
      (Finset.measurable_sum _ fun c _ =>
        (measurable_bondScore_sample hScore ℓ hadm (x s) s n c).const_mul (w.2 i c))
theorem weightedScoreSum_bounded (hScore : BondScoreProperties) (ℓ : StepParameters)
    (hadm : ℓ.Admissible) (x : ℕ → ℝ) {m : ℕ} :
    (s n : ℕ) → [NeZero n] → (w : ScoreWeights ℓ m s n) → (i : Fin m) →
      ∃ C : ℝ, ∀ u, |weightedScoreSum ℓ x s n w i u| ≤ C
  | 0, _, _, _, _ => ⟨0, fun _ => by simp [weightedScoreSum]⟩
  | s + 1, n, _, w, i => by
    obtain ⟨C, hC⟩ := weightedScoreSum_bounded hScore ℓ hadm x s (n * ℓ.side) w.1 i
    refine ⟨C + ∑ c : TorusBond n, |w.2 i c| * 2, fun u => ?_⟩
    show |weightedScoreSum ℓ x s (n * ℓ.side) w.1 i u.1 +
      ∑ c : TorusBond n, w.2 i c *
        bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c| ≤ _
    refine (abs_add_le _ _).trans (add_le_add (hC u.1) ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hScore ℓ hadm (x s) n u.2.1 c).2.2.1 _ _) (abs_nonneg _)
theorem measurable_and_bounded_prod {α : Type} [MeasurableSpace α] {m : ℕ} (f : Fin m → α → ℝ)
    (hf : ∀ i, Measurable (f i)) (hb : ∀ i, ∃ C : ℝ, ∀ u, |f i u| ≤ C) :
    Measurable (fun u => ∏ i, f i u) ∧ ∃ C : ℝ, ∀ u, |∏ i, f i u| ≤ C := by
  refine ⟨Finset.measurable_prod _ fun i _ => hf i, ?_⟩
  choose C hC using hb
  refine ⟨∏ i, |C i|, fun u => ?_⟩
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => (hC i u).trans (le_abs_self _)
theorem integral_prod_shifted_eq (hChain : ChainStepMean) (hStep : ScoreProductStepMean)
    (hScore : BondScoreProperties) (ℓ : StepParameters) (hadm : ℓ.Admissible) (β : ℝ)
    (x : ℕ → ℝ) {m : ℕ} (k : Fin m → ℝ) :
    (s n : ℕ) → [NeZero n] → (X : Fin m → TorusField (fineSide ℓ.side s n) → ℝ) →
    (w : ScoreWeights ℓ m s n) → (∀ i, Measurable (X i)) → (∀ i, ∃ C : ℝ, ∀ W, |X i W| ≤ C) →
    ScoreWeights.Disjoint s n w →
    ∫ u, ∏ i, (X i (initialField ℓ s n u) + weightedScoreSum ℓ x s n w i u - k i)
        ∂(chainJointLaw ℓ β x s n) =
      ∫ u, ∏ i, (X i (initialField ℓ s n u) - k i) ∂(chainJointLaw ℓ β x s n)
  | 0, n, _, X, w, _, _, _ => by
    simp [weightedScoreSum]
  | s + 1, n, _, X, w, hX, hXb, hw => by
    have hinit := measurable_initialField ℓ s (n * ℓ.side)
    have hinit' : ∀ i, Measurable fun u : ChainSample ℓ (s + 1) n =>
        X i (initialField ℓ (s + 1) n u) := fun i =>
      (hX i).comp (measurable_initialField ℓ (s + 1) n)
    have hsum : ∀ i, Measurable (weightedScoreSum ℓ x (s + 1) n w i) :=
      measurable_weightedScoreSum hScore ℓ hadm x (s + 1) n w
    have hsumb := weightedScoreSum_bounded hScore ℓ hadm x (s + 1) n w
    have hL : ∫ u, ∏ i, (X i (initialField ℓ (s + 1) n u) + weightedScoreSum ℓ x (s + 1) n w i u - k i)
          ∂(chainJointLaw ℓ β x (s + 1) n) =
        ∫ u, ∏ i, (X i (initialField ℓ s (n * ℓ.side) u) +
            weightedScoreSum ℓ x s (n * ℓ.side) w.1 i u - k i)
          ∂(chainJointLaw ℓ β x s (n * ℓ.side)) := by
      obtain ⟨hF, hFb⟩ := measurable_and_bounded_prod
        (fun i (u : ChainSample ℓ (s + 1) n) =>
          X i (initialField ℓ (s + 1) n u) + weightedScoreSum ℓ x (s + 1) n w i u - k i)
        (fun i => ((hinit' i).add (hsum i)).sub_const _) (fun i => by
          obtain ⟨C, hC⟩ := hXb i
          obtain ⟨C', hC'⟩ := hsumb i
          refine ⟨C + C' + |k i|, fun u => ?_⟩
          refine (abs_sub _ _).trans
            (add_le_add ((abs_add_le _ _).trans (add_le_add (hC _) (hC' u))) le_rfl))
      refine (hChain ℓ β x).2.2 s n _ _ hF hFb fun u => ?_
      have h := hStep ℓ hadm hadm.depth_lt (x s) n (finalField ℓ s (n * ℓ.side) u) m
        (fun i => X i (initialField ℓ s (n * ℓ.side) u) +
          weightedScoreSum ℓ x s (n * ℓ.side) w.1 i u - k i) w.2 hw.2
      rw [← h]
      refine Finset.sum_congr rfl fun b _ => ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
      show (∏ i, (X i (initialField ℓ s (n * ℓ.side) u) +
        (weightedScoreSum ℓ x s (n * ℓ.side) w.1 i u +
          ∑ c : TorusBond n, w.2 i c * bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) u) V b c) -
            k i)) * _ = _
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      ring
    have hR : ∫ u, ∏ i, (X i (initialField ℓ (s + 1) n u) - k i) ∂(chainJointLaw ℓ β x (s + 1) n) =
        ∫ u, ∏ i, (X i (initialField ℓ s (n * ℓ.side) u) - k i)
          ∂(chainJointLaw ℓ β x s (n * ℓ.side)) := by
      obtain ⟨hF, hFb⟩ := measurable_and_bounded_prod
        (fun i (u : ChainSample ℓ (s + 1) n) => X i (initialField ℓ (s + 1) n u) - k i)
        (fun i => (hinit' i).sub_const _) (fun i => by
          obtain ⟨C, hC⟩ := hXb i
          exact ⟨C + |k i|, fun u => (abs_sub _ _).trans (add_le_add (hC _) le_rfl)⟩)
      refine (hChain ℓ β x).2.2 s n _ _ hF hFb fun u => ?_
      have h := hStep ℓ hadm hadm.depth_lt (x s) n (finalField ℓ s (n * ℓ.side) u) m
        (fun i => X i (initialField ℓ s (n * ℓ.side) u) - k i) (fun _ _ => 0)
        (fun _ _ _ _ => Or.inl rfl)
      simp only [zero_mul, Finset.sum_const_zero, add_zero] at h
      exact h
    rw [hL, hR]
    exact integral_prod_shifted_eq hChain hStep hScore ℓ hadm β x k s (n * ℓ.side) X w.1 hX hXb hw.1
theorem scoresPreserveCorrelations_holds (hChain : ChainStepMean) (hStep : ScoreProductStepMean)
    (hScore : BondScoreProperties) : ScoresPreserveCorrelations := by
  intro ℓ hadm _ β x s n _ m X w k hX hXb hw
  exact integral_prod_shifted_eq hChain hStep hScore ℓ hadm β x k s n X w hX hXb hw
end CorrelationPreservation
end YangMills.Construction.WeightedResponses
end
