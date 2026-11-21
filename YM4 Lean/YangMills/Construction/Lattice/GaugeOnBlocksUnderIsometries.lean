import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.SetsOfBondsOfASequenceOfRegions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def BlockwiseGaugeEquivariance : Prop :=
  ∀ (L m : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ i : ℤ, -(m : ℤ) ≤ i →
    ∀ σ ∈ latticeIsometries L m i,
      ∀ (K k e r : ℕ) (Ω : ℕ → Set (FourTorus L m)), IsChainFromIndex K k i Ω →
        IsSeparatedChain K e r 0 k Ω → ∀ v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
          blockwiseGauge K k (imageChain σ Ω) (transportSiteFunction σ v) =
            transportSiteFunction σ (blockwiseGauge K k Ω v)
end YangMills.Construction.PeriodicLattice
