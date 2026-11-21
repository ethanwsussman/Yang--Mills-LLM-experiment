import YangMills.Construction.InfiniteLattice.LimitsAlongTheCutoffs
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.CutoffLimits.TwoMeasures
open YangMills.Construction.Cumulants (mixedCumulant finsetCumulant)
open YangMills.Construction.InfiniteLattice (centeredMoment ursellFunction)
open YangMills.Construction.Probability (IsBoundedRealRV complexExpectation)
open YangMills.Construction.SetPartition (PartitionsFin blockCount singletonFree)
def blockProduct {Ω : Type*} {n : ℕ} (f : Fin n → Ω → ℝ) (s : Finset (Fin n)) : Ω → ℝ :=
  fun ω => ∏ i ∈ s, f i ω
def blockMean {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) {n : ℕ} (f : Fin n → Ω → ℝ)
    (s : Finset (Fin n)) : ℂ :=
  complexExpectation ν fun ω => (blockProduct f s ω : ℂ)
def partitionFactorialSum (n : ℕ) : ℕ :=
  ∑ π : PartitionsFin n, (blockCount π).factorial
def ursellFamily (D : Setting) {a : ℝ} (ν : Measure (InfiniteLattice.GaugeField a)) :
    RealFamily D :=
  fun n _ X => (ursellFunction ν n X.1).re
def CumulantComparison : Prop :=
  (∀ (Ω : Type) [MeasurableSpace Ω] (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (n : ℕ) (f : Fin n → Ω → ℝ), 1 ≤ n →
    (∀ i, IsBoundedRealRV (f i)) →
    (blockMean ν f Finset.univ =
        ∑ π : PartitionsFin n, ∏ s ∈ π.parts, finsetCumulant ν f s) ∧
    (mixedCumulant ν f =
      ∑ π : PartitionsFin n, (-1 : ℂ) ^ (blockCount π - 1) *
        ((blockCount π - 1).factorial : ℂ) * ∏ s ∈ π.parts, blockMean ν f s) ∧
    (∀ (k : Fin n) (g : Ω → ℝ) (c c' : ℝ), IsBoundedRealRV g →
      mixedCumulant ν (Function.update f k fun ω => c * f k ω + c' * g ω) =
        (c : ℂ) * mixedCumulant ν f + (c' : ℂ) * mixedCumulant ν (Function.update f k g)) ∧
    ((complexExpectation ν fun ω => ∏ i, ((f i ω : ℂ) - complexExpectation ν fun ω' => (f i ω' : ℂ))) =
      ∑ π ∈ singletonFree n, ∏ s ∈ π.parts, finsetCumulant ν f s) ∧
    ∀ (y : Fin n → ℝ) (ε : ℝ), (∀ i, 0 ≤ y i) → 0 ≤ ε → (∀ i ω, |f i ω| ≤ y i) →
      (∀ s : Finset (Fin n), s.Nonempty →
        ‖blockMean μ f s - blockMean ν f s‖ ≤ ε * ∏ i ∈ s, y i) →
      ‖mixedCumulant μ f - mixedCumulant ν f‖ ≤
        (partitionFactorialSum n : ℝ) * ε * ∏ i, y i) ∧
  ∀ (D : Setting) (Λ : FixedSpacing.Setup) (ν : Measure Λ.Fields)
    [IsProbabilityMeasure ν],
    (∀ (n : ℕ), 2 ≤ n → ∀ X : D.SepTuples n, (ursellFunction ν n X.1).im = 0) ∧
    ∀ X : D.AllSepTuples, centeredMoment ν X.1.2 = ((centred (ursellFamily D ν) X : ℝ) : ℂ)
end YangMills.Construction.CutoffLimits.TwoMeasures
end
