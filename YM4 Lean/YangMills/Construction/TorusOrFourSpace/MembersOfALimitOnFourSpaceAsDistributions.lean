import YangMills.Construction.TorusOrFourSpace.ConvergenceOfPartialHierarchiesOnFourSpace
import YangMills.Construction.TorusOrFourSpace.DistributionsOfAHierarchyOnProductsAndDistinctPoints
import YangMills.Construction.TorusOrFourSpace.FourKindsOfMapsOfSeveralPoints
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.EuclideanLimitDistributions
def HasMemberValues {D : Params} (Φ : Hierarchy D Kind.euclidean) {n : ℕ+} (hn : 2 ≤ (n : ℕ))
    (T : Tuple.testFns D Kind.euclidean (pairwiseDistinct D Kind.euclidean n) → ℂ) :
    Prop :=
  Tuple.IsDistrib T ∧
    ∀ φ ∈ sepC1Tuples D Kind.euclidean (n : ℕ),
      (∀ i, IsSmoothFn D Kind.euclidean (φ i)) → Φ.ValueAtTensor hn T φ
def LimitMembersAreDistributions : Prop :=
  ∀ (D : Params) (C : BoundFamily) (J : Sequences.PNatIndexSet) (ρ : J.carrier → ℝ≥0∞)
    (S : BoundedPartialHierarchySeq D Kind.euclidean J ρ C)
    (Φ : Hierarchy D Kind.euclidean),
    S.ConvergesOnSepTuples Φ →
    ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ)),
      (∃! T, HasMemberValues Φ hn T) ∧
      ∀ T, HasMemberValues Φ hn T →
        Tuple.IsDistribOfOrderLE (5 * (n : ℕ) + 1) T ∧
        (∀ (U : Set (Kind.euclidean.Tuple D n))
            (hU : U ⊆ pairwiseDistinct D Kind.euclidean n),
          Tuple.IsOpenT D Kind.euclidean U →
            Tuple.HasOrderLEOn hU (5 * (n : ℕ) + 1) T) ∧
        (∀ σ : Equiv.Perm (Fin (n : ℕ)), InvariantUnder (fun x i => x (σ i)) T) ∧
        ∀ g : Kind.euclidean.Pt D → Kind.euclidean.Pt D,
          IsIsometry D Kind.euclidean g →
          (∀ (φ : sepC1Tuples D Kind.euclidean (n : ℕ))
              (h : compEach φ.1 g ∈ sepC1Tuples D Kind.euclidean (n : ℕ)),
            Φ.func (n : ℕ) hn ⟨_, h⟩ = Φ.func (n : ℕ) hn φ) →
          InvariantUnder (fun x i => g (x i)) T
end YangMills.Construction.PeriodicSpace.Kind.EuclideanLimitDistributions
