import YangMills.Construction.Towers.ConfigurationsWhoseAveragesStayInThePolydiscs
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.IteratedMeans
section Torus
open MeanStableFields
variable {L m k : ℕ}
def meanStep {i : ℕ} (V : Edge L m k i → Matrices.ComplexMatrix2) :
    Edge L m k (i + 1) → Matrices.ComplexMatrix2 :=
  fun c => PeriodicLattice.complexBlockAverage V c
def iteratedMean (W : Edge L m k 0 → Matrices.ComplexMatrix2) :
    (i : ℕ) → Option (Edge L m k i → Matrices.ComplexMatrix2)
  | 0 => some W
  | i + 1 => (iteratedMean W i).bind fun V =>
    open Classical in
    if V ∈ fieldsNearOne L m k i then some (meanStep V) else none
structure TorusConditions (L m k : ℕ) : Prop where
  meanStep_mem : ∀ i < k, ∀ V ∈ fieldsNearOne L m k i,
    meanStep V ∈ fieldsIn L m k (i + 1) PeriodicLattice.complexGaugeGroup
  meanStep_unique : ∀ i < k, ∀ V ∈ fieldsNearOne L m k i,
    ∀ V' ∈ fieldsIn L m k (i + 1) PeriodicLattice.complexGaugeGroup,
      (∀ c : Edge L m k (i + 1), c.IsPositivelyOriented →
          V' c = PeriodicLattice.complexBlockAverage V c) ↔
        V' = meanStep V
  isSome_iff : ∀ l ≤ k, ∀ W ∈ fieldsIn L m k 0 PeriodicLattice.complexGaugeGroup,
    (iteratedMean W l).isSome ↔ W ∈ meanStableFields L m k l
  iteratedMean_eq : ∀ l ≤ k, ∀ W ∈ fieldsIn L m k 0 PeriodicLattice.complexGaugeGroup,
    ∀ V : ∀ i : ℕ, Edge L m k i → Matrices.ComplexMatrix2, IsMeanSequenceFrom l W V →
      ∀ i ≤ l, iteratedMean W i = some (V i)
  eventually_near : ∀ i < k, EventuallyNearIdentity (fieldSpace L m k i) fun V =>
    ∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L
  mem_complex : ∀ i < k, ∀ V ∈ fieldSpace L m k i,
    V ∈ fieldsIn L m k i PeriodicLattice.complexGaugeGroup
end Torus
namespace Unbounded
variable {L k : ℕ}
def meanStep {i : ℕ} (V : FullSpace.Edge L k i → Matrices.ComplexMatrix2) :
    FullSpace.Edge L k (i + 1) → Matrices.ComplexMatrix2 :=
  fun c => FullSpace.complexSmoothing L V c
def iteratedMean (W : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :
    (i : ℕ) → Option (FullSpace.Edge L k i → Matrices.ComplexMatrix2)
  | 0 => some W
  | i + 1 => (iteratedMean W i).bind fun V =>
    open Classical in
    if V ∈ MeanStableFields.Infinite.fieldsNearOne L k i then some (meanStep V) else none
structure SpaceConditions (L k : ℕ) : Prop where
  meanStep_mem : ∀ i < k, ∀ V ∈ MeanStableFields.Infinite.fieldsNearOne L k i,
    meanStep V ∈ FullSpace.fieldsValuedIn L k (i + 1) PeriodicLattice.complexGaugeGroup
  meanStep_unique : ∀ i < k, ∀ V ∈ MeanStableFields.Infinite.fieldsNearOne L k i,
    ∀ V' ∈ FullSpace.fieldsValuedIn L k (i + 1) PeriodicLattice.complexGaugeGroup,
      (∀ c : FullSpace.Edge L k (i + 1), c.IsPositivelyOriented →
          V' c = FullSpace.complexSmoothing L V c) ↔
        V' = meanStep V
  isSome_iff : ∀ l ≤ k,
    ∀ W ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
      (iteratedMean W l).isSome ↔ W ∈ MeanStableFields.Infinite.meanStableFields L k l
  iteratedMean_eq : ∀ l ≤ k,
    ∀ W ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
      ∀ V : ∀ i : ℕ, FullSpace.Edge L k i → Matrices.ComplexMatrix2,
        MeanStableFields.Infinite.IsMeanSequenceFrom l W V →
          ∀ i ≤ l, iteratedMean W i = some (V i)
  eventually_near : ∀ i < k,
    FullSpace.EventuallyNearIdentity (FullSpace.fieldSpace L k i) fun V =>
      ∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L
  mem_complex : ∀ i < k, ∀ V ∈ FullSpace.fieldSpace L k i,
    V ∈ FullSpace.fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup
end Unbounded
def IteratedMeansHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ m : ℕ, 0 < m → TorusConditions L m k) ∧ Unbounded.SpaceConditions L k
end YangMills.Construction.Tower.IteratedMeans
end
