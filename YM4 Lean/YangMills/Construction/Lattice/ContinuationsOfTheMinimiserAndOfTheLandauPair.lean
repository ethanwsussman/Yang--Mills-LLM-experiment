import YangMills.Construction.Lattice.LandauGaugeRelativeToABackground
import YangMills.Construction.Lattice.MinimalConfigurationsAtComplexData
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def activeLandauPotential (ξ α ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) (B : ActiveFamily L m K k Ω) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  landauGaugeForm (Averaging.smoothingRadius L) ξ α k Ω (activeGaugeRepresentative ε K k Ω V₀)
    (activeGaugeRepresentative ε K k Ω (expTwistedDatum B V₀))
end YangMills.Construction.PeriodicLattice
end
