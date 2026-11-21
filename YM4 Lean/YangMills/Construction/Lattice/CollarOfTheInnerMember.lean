import YangMills.Construction.Lattice.DirichletDifferenceOperators
import YangMills.Construction.Lattice.SeparatedSequenceData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedSequences
namespace BaseParameters
variable (D : BaseParameters)
def collarOfFirstMember (Ω : ℕ → Set D.Torus) (r : ℕ) : Set (BareSite D.L D.m D.K) :=
  {x | ∃ x₀ ∈ sitesOfRegion D.K (D.memberAt Ω 1), ∃ Γ : List (BareOrientedBond D.L D.m D.K),
    IsBondPathFromTo Γ x₀ x ∧ Γ.length ≤ r}
end BaseParameters
end SeparatedSequences
end YangMills.Construction
end
