import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.PlaquetteFunctionsAndTwoNotionsOfSupport
import YangMills.Construction.Torus.DistanceBallsIntegralAndVolumeInPhysicalUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.BareLattice
open PlaquetteSupports
variable (s : Conventions.StandingParameters)
def latticePointsPerSide : ℕ := 2 * s.L ^ ((s.m : ℕ) + (s.K : ℕ))
abbrev baseLattice : AddSubgroup s.Torus := PeriodicLattice.sublattice s.L s.m ((s.K : ℕ) : ℤ)
abbrev LatticeSite : Type := PeriodicLattice.Site s.L s.m ((s.K : ℕ) : ℤ)
def coordinateMultiples : AddSubgroup s.Torus :=
  AddSubgroup.pi univ fun _ =>
    AddSubgroup.zmultiples ((latticeSpacing s : ℝ) : AddCircle (PeriodicLattice.torusSide s.L s.m))
def projectedLattice : Set s.Torus :=
  TorusMeasure.proj s '' (InfiniteLattice.latticeSubgroup (latticeSpacing s) : Set (Fin 4 → ℝ))
abbrev AxisPair : Type := {q : Fin 4 × Fin 4 // q.1 < q.2}
variable {s}
def plaquetteOf (y : LatticeSite s) (q : AxisPair) : LatticePlaquette s := ⟨y, q.1.1, q.1.2, q.2⟩
variable (s)
def SideDivSpacing : Prop :=
  s.side / latticeSpacing s = (latticePointsPerSide s : ℝ) ∧ 0 < latticePointsPerSide s
def LatticeDescriptions : Prop :=
  baseLattice s = coordinateMultiples s ∧ (baseLattice s : Set s.Torus) = projectedLattice s
def BarycenterFormula : Prop :=
  ∀ (y : LatticeSite s) (q : AxisPair),
    PeriodicLattice.Plaquette.barycenter (plaquetteOf y q) =
      (y : s.Torus) + planeDiagonal s q.1.1 q.1.2
def SixPlaquettesPerSite : Prop :=
  ∀ y : LatticeSite s, {p : LatticePlaquette s | p.origin = y}.ncard = 6 ∧
    ∀ q : AxisPair, ∃! p : LatticePlaquette s, p.origin = y ∧ planeOf p = q.1
def PlaquetteSumDecomposition : Prop :=
  ∀ φ : PlaquetteFunction s,
    ∑ᶠ p : LatticePlaquette s, φ p = ∑ q : AxisPair, ∑ᶠ y : LatticeSite s, φ (plaquetteOf y q)
def BareLatticeProperties : Prop :=
  ∀ s : Conventions.StandingParameters, 0 < latticeSpacing s ∧ SideDivSpacing s ∧
    LatticeDescriptions s ∧ BarycenterFormula s ∧ SixPlaquettesPerSite s ∧
    PlaquetteSumDecomposition s
end YangMills.Construction.BareLattice
