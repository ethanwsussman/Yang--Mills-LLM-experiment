import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.ComplexIteratesByTheBondwiseMaps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def ComplexPartialItersFormedByPartialMaps : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ j : ℕ, j < K →
    (∀ V : PartialGaugeField L m (levelDepth K j), IsReversalClosed V.support →
      IsGaugeField complexGaugeGroup V.support V.field → ∀ i : ℕ, j + i ≤ K →
      ∀ c : Bond L m (levelDepth K (j + i)),
        (c ∈ (complexPartialBlockAverageIter j V i).support ↔ ComplexPartialDefinedAt j V i c) ∧
        (ComplexPartialDefinedAt j V i c →
          (complexPartialBlockAverageIter j V i).field c = complexPartialValues j V i c)) ∧
    (∀ U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2, IsGaugeField complexGaugeGroup univ U →
      ∀ i : ℕ, i ≤ K → U ∈ complexBlockFieldDomain (K := K) i →
        bareComplexPartialIter (⟨univ, U⟩ : PartialGaugeField L m (levelDepth K 0)) i =
          (⟨univ, complexBlockFieldAtLevel i U⟩ : PartialGaugeField L m (levelDepth K i)))
end YangMills.Construction.PeriodicLattice
