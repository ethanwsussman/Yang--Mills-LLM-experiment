import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BondwiseAverage
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def RealAverageDefinedAtInnerBonds : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ k : ℕ, k < K →
    ∀ X : Set (FourTorus L m), IsPartitionRegion (levelDepth K (k + 1)) X →
    ∀ U : BondAtLevel L m K k → Matrices.ComplexMatrix2, IsGaugeField compactGaugeGroup (bondsInside X) U →
    ∀ c ∈ (bondsInside X : Set (BondAtLevel L m K (k + 1))),
      let mean : PartialGaugeField L m (levelDepth K (k + 1)) :=
        realPartialBlockAverage (Averaging.smoothingRadius L) ⟨bondsInside X, U⟩
      c ∈ mean.support ∧
        (∃ V ∈ gaugeFieldsAtLevel L m K k,
          ∀ v ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), V v = U v) ∧
        ∀ V ∈ gaugeFieldsAtLevel L m K k,
          (∀ v ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), V v = U v) →
            mean.field c = blockAverage (Averaging.smoothingRadius L) V c
end YangMills.Construction.PeriodicLattice
