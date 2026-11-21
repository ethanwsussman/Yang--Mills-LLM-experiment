import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import YangMills.Construction.InfiniteLattice.RefinedLattices
import YangMills.Construction.Lattice.ToriLatticesNormsAndFunctionsOfFinitelyManyVariables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.VolumeTransfer
open MeasureTheory InfiniteLattice
def refinedLinkValue (L K : ℕ) (U : RefinedGaugeField L K) (b : Link (refinedSpacing L K)) :
    Matrices.ComplexMatrix2.specialUnitary :=
  U b
abbrev periodicLinkValue (L m K : ℕ) (U : PeriodicLattice.CompactGaugeField L m (K : ℤ))
    (b : PeriodicLattice.Bond L m (K : ℤ)) : Matrices.ComplexMatrix2.specialUnitary :=
  PeriodicLattice.CompactGaugeField.linkValue U b
section LinkVariablesOfFunctions
variable {𝒱 B : Type} (val : 𝒱 → B → Matrices.ComplexMatrix2.specialUnitary)
def IsBoundedBorelInLinks (S : Set B) (F : 𝒱 → ℂ) : Prop :=
  ∃ Φ : LinkVariables S → ℂ, Measurable[borel (LinkVariables S)] Φ ∧ (∃ C : ℝ, ∀ g, ‖Φ g‖ ≤ C) ∧
    ∀ U, F U = Φ fun b => val U b
def IsBoundedBorelInFinitelyManyLinks (F : 𝒱 → ℂ) : Prop :=
  ∃ S : Set B, S.Finite ∧ IsBoundedBorelInLinks val S F
end LinkVariablesOfFunctions
end YangMills.Construction.VolumeTransfer
end
