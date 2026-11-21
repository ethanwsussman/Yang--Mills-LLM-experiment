import YangMills.Construction.Lattice.FaddeevPopovKernel
import YangMills.Construction.Measurability.BorelKernelsAndParameterSetting
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ConfigSpaces
open FaddeevPopov
universe u
variable {L m K : ℕ}
abbrev GradedBond (L m K : ℕ) : Type := Σ k : ℕ, BondAtLevel L m K k
structure IsConfigBondSet (𝔅 : Finset (GradedBond L m K)) : Prop where
  level_le : ∀ b ∈ 𝔅, b.1 ≤ K
  opposite_notMem : ∀ b ∈ 𝔅, OrientedEdgeEnds.flip b ∉ 𝔅
structure IsConfigSpaceData (𝔅 : Finset (GradedBond L m K)) (𝒴 : Type u)
    [MeasurableSpace 𝒴] : Prop where
  bonds : IsConfigBondSet 𝔅
  standardBorel : BorelKernels.IsStandardBorelSpace 𝒴
abbrev ConfigSpace (𝔅 : Finset (GradedBond L m K)) (𝒴 : Type u) : Type u :=
  (𝔅 → Matrices.ComplexMatrix2.specialUnitary) × 𝒴
def linkValue {𝔅 : Finset (GradedBond L m K)} (v : 𝔅 → Matrices.ComplexMatrix2.specialUnitary)
    (b : GradedBond L m K) : Matrices.ComplexMatrix2.specialUnitary :=
  open Classical in
  if h : b ∈ 𝔅 then v ⟨b, h⟩
  else if h' : OrientedEdgeEnds.flip b ∈ 𝔅 then (v ⟨OrientedEdgeEnds.flip b, h'⟩)⁻¹ else 1
def gaugeHaar (S : Finset (FourTorus L m)) : Measure (SiteGaugeGroup S) :=
  Matrices.ComplexMatrix2.haarPi S
def gaugeTransformedValues {𝔅 : Finset (GradedBond L m K)} {S : Finset (FourTorus L m)}
    (v : 𝔅 → Matrices.ComplexMatrix2.specialUnitary) (u : SiteGaugeGroup S) :
    𝔅 → Matrices.ComplexMatrix2.specialUnitary :=
  fun b => movedField (linkValue v) u b.1
def gaugeTransformedPoint {𝔅 : Finset (GradedBond L m K)} {𝒴 : Type u} {S : Finset (FourTorus L m)}
    (ξ : ConfigSpace 𝔅 𝒴) (g : SiteGaugeGroup S) : ConfigSpace 𝔅 𝒴 :=
  (gaugeTransformedValues ξ.1 g, ξ.2)
end YangMills.Construction.PeriodicLattice.ConfigSpaces
