import YangMills.Construction.Lattice.BlockAxialLaw
import YangMills.Construction.Lattice.GaugeConfigSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ConfigSpaces
open BorelKernels FaddeevPopov Matrices
universe u
variable {L m : ℕ}
def axialWeight (a ε : ℝ) (w : ComplexMatrix2) : ℝ :=
  (axialNormalizer a ε)⁻¹ * nearIdentityIndicator ε w * Real.exp (-a * traceDeficit w)
variable (K j : ℕ) [Finite (SiteAtLevel L m K j)] (P'' : Set (SiteAtLevel L m K (j + 1)))
def shellPoints : Finset (FourTorus L m) :=
  (Set.toFinite (Subtype.val '' axialShellSites K j P'')).toFinset
variable {K j P''}
theorem shellPoints_mem_sublattice (x : shellPoints (L := L) (m := m) K j P'') :
    (x : FourTorus L m) ∈ sublattice L m (levelDepth K j) := by
  obtain ⟨z, -, hz⟩ := (Set.Finite.mem_toFinset _).1 x.2
  exact hz ▸ z.2
def shellSite (x : shellPoints (L := L) (m := m) K j P'') : SiteAtLevel L m K j :=
  ⟨x, shellPoints_mem_sublattice x⟩
variable {𝔅 : Finset (GradedBond L m K)} {𝒴 : Type u} [MeasurableSpace 𝒴]
variable (j) in
def fieldAtLevel (v : 𝔅 → ComplexMatrix2.specialUnitary) (b : BondAtLevel L m K j) :
    ComplexMatrix2 :=
  (linkValue v ⟨j, b⟩ : ComplexMatrix2.specialUnitary)
variable (P'') in
def contourDomain (ξ : ConfigSpace 𝔅 𝒴) : Set (shellPoints (L := L) (m := m) K j P'') :=
  {x | HasContourMean (fieldAtLevel j ξ.1) (axialShellCentre K j P'' (shellSite x))
    (shellSite x)}
variable (P'') in
def axialFactorMeasure (a ε : ℝ) (ξ : ConfigSpace 𝔅 𝒴)
    (x : shellPoints (L := L) (m := m) K j P'') : Measure ComplexMatrix2.specialUnitary :=
  open Classical in
  if x ∈ contourDomain P'' ξ then
    ComplexMatrix2.haarProb.withDensity fun w => ENNReal.ofReal (axialWeight a ε
      (meanContourHolonomy (fieldAtLevel j ξ.1) (axialShellCentre K j P'' (shellSite x))
        (shellSite x) * ((w⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)))
  else pointMass 1
variable (K j P'') in
def axialLaw (a ε : ℝ) (ξ : ConfigSpace 𝔅 𝒴) :
    Measure (SiteGaugeGroup (shellPoints (L := L) (m := m) K j P'')) :=
  Measure.pi (axialFactorMeasure P'' a ε ξ)
end YangMills.Construction.PeriodicLattice.ConfigSpaces
