import YangMills.Construction.Lattice.CovarianceOfTheAveragingMaps
import YangMills.Construction.Lattice.LocalisedBackgroundsOfSetsInForce
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def GluedDataEquivariant : Prop :=
  ∀ (L m K k n j : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m)
    (Ω : ℕ → Set (FourTorus L m)) (W : Set (FourTorus L m))
    (V : ∀ q : ℕ, BondAtLevel L m K q → Matrices.ComplexMatrix2),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m → -(m : ℤ) ≤ i →
    σ ∈ latticeIsometries L m i → IsDeterminingChainFrom K k i Ω →
    i ≤ scaledCubeIndex K j n → IsGluedHyp K k n j Ω W V →
    gluedChain K n j Ω W 0 = W ∧
    ∀ q ∈ gluedActiveSet K k n j Ω W,
      gluedBoundaryData K k j (imageChain σ Ω) (datumImage σ V) q.1 (bondImage σ q.2) =
        gluedBoundaryData K k j Ω V q.1 q.2
end YangMills.Construction.PeriodicLattice
