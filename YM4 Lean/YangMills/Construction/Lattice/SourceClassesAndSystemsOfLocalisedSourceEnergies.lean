import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.Lattice.LatticesOfAnIndexAndTheCutoffZero
import YangMills.Construction.Lattice.LocalizationDomainsAndEdgeTrees
import YangMills.Construction.Lattice.RealSystemsAndClassesOfSources
import YangMills.Construction.PolymerActivities.DomainCountingRate
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace LocalizedEnergies
structure EnergyData extends Conventions.StandingParameters where
  cubeExp : ℕ
  β : ℝ
  β_pos : 0 < β
  radius : ℝ
  radius_pos : 0 < radius
  index : toStandingParameters.LatticeIndex
namespace EnergyData
variable (D : EnergyData)
abbrev blockSide : ℕ := D.L ^ D.cubeExp
abbrev indexValue : ℕ := D.index.1
abbrev FinePlaquette : Type := PeriodicLattice.Plaquette D.L D.m (D.indexValue : ℤ)
def sourceClass : Set (D.Torus → ℂ) :=
  PeriodicLattice.flatSourceClass D.L D.m (D.blockSide : ℝ) D.radius
abbrev sourceDisc {n : ℕ} (h : Fin n → D.Torus → ℝ) : Set (Fin n → ℂ) :=
  PeriodicLattice.sourceDisc (D.blockSide : ℝ) D.radius h
theorem complexSource_mem_sourceClass {n : ℕ} {h : Fin n → D.Torus → ℝ}
    (hh : PeriodicLattice.IsRealLipschitzTuple h) {ζ : Fin n → ℂ} (hζ : ζ ∈ D.sourceDisc h) :
    PeriodicLattice.complexSource h ζ ∈ D.sourceClass :=
  ⟨n, h, ζ, hh, hζ, rfl⟩
theorem zero_mem_sourceClass : (0 : D.Torus → ℂ) ∈ D.sourceClass := by
  refine ⟨1, fun _ _ => 0, 0, ⟨le_rfl, fun _ => ⟨0, le_rfl, fun _ _ => by simp⟩⟩, ?_, ?_⟩
  · simpa [PeriodicLattice.sourceDisc] using D.radius_pos
  · funext x
    simp [PeriodicLattice.complexSource]
def zeroSource : D.sourceClass := ⟨0, D.zero_mem_sourceClass⟩
abbrev levelSet : Finset ℕ := PeriodicLattice.levelRange D.K D.indexValue
abbrev partitionIndex (j : ℕ) : ℤ := PeriodicLattice.coarseCubeIndex D.K D.cubeExp j
def PartitionExists (j : ℕ) : Prop := D.cubeExp + j ≤ (D.m : ℕ) + (D.K : ℕ)
def domainsAt (j : ℕ) : Set (Set D.Torus) :=
  {X | D.PartitionExists j ∧ X ∈ PeriodicLattice.connectedRegions D.L D.m (D.partitionIndex j)}
structure EnergyFamily where
  vacuumEnergy : ℝ
  localEnergy : (j : D.levelSet) → D.domainsAt j → D.sourceClass → ℂ
namespace EnergyFamily
variable {D} (e : D.EnergyFamily)
def counterterm (v : D.sourceClass) : ℂ :=
  ∑ j : D.levelSet, ∑ᶠ X : D.domainsAt j, e.localEnergy j X v
def IsLocal : Prop :=
  ∀ (j : D.levelSet) (X : D.domainsAt j),
    (∀ v v' : D.sourceClass,
      (∀ p ∈ (PeriodicLattice.plaquettesMeeting
          (PeriodicLattice.addCubeLayer (D.partitionIndex j) X.1) : Set D.FinePlaquette),
          v.1 p.barycenter = v'.1 p.barycenter) →
        e.localEnergy j X v = e.localEnergy j X v') ∧
      e.localEnergy j X D.zeroSource = 0
open Classical in
def localEnergyAlong (j : D.levelSet) (X : D.domainsAt j) {n : ℕ} (h : Fin n → D.Torus → ℝ)
    (hh : PeriodicLattice.IsRealLipschitzTuple h) (ζ : Fin n → ℂ) : ℂ :=
  if hζ : ζ ∈ D.sourceDisc h then
    e.localEnergy j X ⟨PeriodicLattice.complexSource h ζ, D.complexSource_mem_sourceClass hh hζ⟩
  else 0
def IsAnalytic : Prop :=
  ∀ (j : D.levelSet) (X : D.domainsAt j) (n : ℕ) (h : Fin n → D.Torus → ℝ)
    (hh : PeriodicLattice.IsRealLipschitzTuple h),
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) (D.sourceDisc h)
      fun ζ _ => e.localEnergyAlong j X h hh ζ
def DecaysExponentially (C κ : ℝ) : Prop :=
  0 ≤ C ∧ PolymerActivities.DomainCounting.countingRate < κ ∧
    ∀ (j : D.levelSet) (X : D.domainsAt j) (v : D.sourceClass),
      ‖e.localEnergy j X v‖ ≤
        C * Real.exp (-κ * PeriodicLattice.linearExtent D.K D.cubeExp j X.1)
end EnergyFamily
end EnergyData
end LocalizedEnergies
end YangMills.Construction
end
