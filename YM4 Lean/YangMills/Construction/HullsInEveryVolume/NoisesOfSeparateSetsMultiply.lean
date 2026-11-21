import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ChainNoise
open TorusLumps TorusFields WeightedResponses
def disjointNoisesMultiplyStatement : Prop :=
  ∀ (ℓ : StepParameters) (u n : ℕ) [NeZero n] {ι : Type} (I : Finset ι) (Q : ι → Finset (TorusSite n))
    (Φ : ι → TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ),
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Q i) (Q j)) →
    (∀ i ∈ I, Measurable (Φ i) ∧ (∃ C : ℝ, ∀ p, |Φ i p| ≤ C) ∧ DependsAbove ℓ u n (Q i) (Φ i)) →
    ∀ W : TorusField (fineSide ℓ.side u n),
      noiseExpectation ℓ u n (fun p => ∏ i ∈ I, Φ i p) W = ∏ i ∈ I, noiseExpectation ℓ u n (Φ i) W
end YangMills.Construction.ChainNoise
end
