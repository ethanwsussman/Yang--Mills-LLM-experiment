import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.LiftOfBlockFields
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def BlockFieldLifts.Statement : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
    (∀ n : ℕ, n + 1 ≤ K → ∀ V : BondAtLevel L m K (n + 1) → Matrices.ComplexMatrix2,
      V ∈ gaugeFieldsAtLevel L m K (n + 1) →
      bareLift V ∈ gaugeFieldsAtLevel L m K 0 ∧
      (∀ j : ℕ, j ≤ n + 1 →
        averagedLift (Averaging.smoothingRadius L) j V =
            blockFieldAtLevel (Averaging.smoothingRadius L) j (bareLift V) ∧
        averagedLift (Averaging.smoothingRadius L) j V ∈ gaugeFieldsAtLevel L m K j ∧
        (∀ b : BondAtLevel L m K j, EndsInOneBlock (n + 1) b →
          averagedLift (Averaging.smoothingRadius L) j V b = 1) ∧
        ∀ (c : BondAtLevel L m K (n + 1)) (b : BondAtLevel L m K j), CoversBond c b →
          averagedLift (Averaging.smoothingRadius L) j V b = V c) ∧
      blockAverageStep (Averaging.smoothingRadius L) n
          (averagedLift (Averaging.smoothingRadius L) n V) =
        blockFieldAtLevel (Averaging.smoothingRadius L) (n + 1) (bareLift V) ∧
      blockFieldAtLevel (Averaging.smoothingRadius L) (n + 1) (bareLift V) = V) ∧
    ∀ q : ℕ, q ≤ K →
      blockFieldAtLevel (Averaging.smoothingRadius L) q
          (trivialGaugeField : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) =
        (trivialGaugeField : BondAtLevel L m K q → Matrices.ComplexMatrix2)
end YangMills.Construction.PeriodicLattice
