import YangMills.Construction.Lattice.HolomorphicIdentitiesUnderIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def ComplexHolonomiesAndAveragesCovariance.Statement : Prop :=
  ∃ ε : SignedFrame → Fin 4 → Fin 4 → ℤˣ,
    ∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
      Conventions.IsAdmissibleBlockingFactor L → 0 < m →
      -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i →
        PreservesComplexHolonomies σ i ∧ PreservesComplexPlaquetteHolonomies ε σ i ∧
        PreservesComplexEnergies σ i ∧ PreservesComplexContourMeans σ i ∧
        PreservesComplexBlockAverages σ i ∧ PreservesComplexLevelLifts σ i ∧
        PreservesComplexDeterminingIterates σ i ∧
        PreservesLinearBlockIterates σ i
end YangMills.Construction.PeriodicLattice
