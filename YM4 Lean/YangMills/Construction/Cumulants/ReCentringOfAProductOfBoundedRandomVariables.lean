import YangMills.Construction.Cumulants.LogMomentGeneratingFunction
import YangMills.Construction.Cumulants.PartitionsMomentsAndTheCentredFunctionalOfAFamily
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.ProductRecentering
variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
def realExpect (ρ : Measure Ω) (u : Ω → ℝ) : ℝ := ∫ ω, u ω ∂ρ
def centeredMean (ρ : Measure Ω) (Y : Fin k → Ω → ℝ) (c : Fin k → ℝ) (i : Fin k) : ℝ :=
  realExpect ρ (Y i) - c i
def recenteredCumulant (ρ : Measure Ω) (Y : Fin k → Ω → ℝ) (c : Fin k → ℝ)
    (J : Finset (Fin k)) : ℂ :=
  if J.card = 1 then ∑ i ∈ J, (centeredMean ρ Y c i : ℂ) else finsetCumulant ρ Y J
theorem recenteredCumulant_singleton (ρ : Measure Ω) (Y : Fin k → Ω → ℝ) (c : Fin k → ℝ)
    (i : Fin k) : recenteredCumulant ρ Y c {i} = centeredMean ρ Y c i := by
  simp [recenteredCumulant]
theorem recenteredCumulant_of_two_le_card (ρ : Measure Ω) (Y : Fin k → Ω → ℝ) (c : Fin k → ℝ)
    {J : Finset (Fin k)} (hJ : 2 ≤ J.card) : recenteredCumulant ρ Y c J = finsetCumulant ρ Y J := by
  rw [recenteredCumulant, if_neg (by omega)]
def ProductRecenteringExpansion : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] (k : ℕ), 1 ≤ k →
    ∀ (Y : Fin k → Ω → ℝ) (c : Fin k → ℝ),
    (∀ i, YangMills.Construction.Probability.IsBoundedRealRV (Y i)) →
    ((realExpect ρ (fun ω => ∏ i, (Y i ω - c i)) : ℂ) =
        ∑ I : Finset (Fin k), (∏ i ∈ I, (centeredMean ρ Y c i : ℂ)) *
          ∑ π ∈ YangMills.Construction.SetPartition.atLeastTwoPartitions (Finset.univ \ I),
            ∏ J ∈ π.parts, recenteredCumulant ρ Y c J ∧
      (∑ I : Finset (Fin k), (∏ i ∈ I, (centeredMean ρ Y c i : ℂ)) *
          ∑ π ∈ YangMills.Construction.SetPartition.atLeastTwoPartitions (Finset.univ \ I),
            ∏ J ∈ π.parts, recenteredCumulant ρ Y c J) =
        ∑ π' : YangMills.Construction.SetPartition.PartitionsFin k,
          ∏ J ∈ π'.parts, recenteredCumulant ρ Y c J) ∧
    ∀ (D : ℕ → ℝ) (b : Fin k → ℝ), (∀ m, 1 ≤ m → m ≤ k → 0 ≤ D m) → (∀ i, 0 ≤ b i) →
      (∀ i, |centeredMean ρ Y c i| ≤ D 1 * b i) →
      (∀ J : Finset (Fin k), 2 ≤ J.card → ‖recenteredCumulant ρ Y c J‖ ≤ D J.card * ∏ i ∈ J, b i) →
      |realExpect ρ fun ω => ∏ i, (Y i ω - c i)| ≤
        (∑ I : Finset (Fin k), D 1 ^ I.card *
          ∑ π ∈ YangMills.Construction.SetPartition.singletonFree (k - I.card),
            ∏ J ∈ π.parts, D J.card) * ∏ i, b i
end YangMills.Construction.Cumulants.ProductRecentering
