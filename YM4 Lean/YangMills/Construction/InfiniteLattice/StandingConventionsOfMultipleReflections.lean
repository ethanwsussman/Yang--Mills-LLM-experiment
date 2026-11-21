import YangMills.Construction.InfiniteLattice.CoveringPeriodicExtensionsAndTheTwoSetsOfStates
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.ReflectionPositivity.AxisMirrorData
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace MultipleReflections
abbrev Setup : Type := ReflectionPositivity.AxisMirror.MirrorData
namespace Setup
variable (D : Setup)
abbrev GaugeField : Type := InfiniteLattice.GaugeField D.mesh
abbrev LatticeSymmetry : Type := InfiniteLattice.LatticeSymmetry D.mesh
def gibbsStates : Set (Measure D.GaugeField) :=
  InfiniteLattice.periodicGibbsSet D.L D.K D.β
def atCoupling (K' : ℕ+) (β' : ℝ) (hβ' : 0 < β') : Setup :=
  { D with K := K', β := β', β_pos := hβ' }
def atSide (ℓ' : ℝ) (hℓ' : ℓ' ∈ PeriodicLattice.torusSides D.L) : Setup :=
  { D with m := ⟨hℓ'.choose, hℓ'.choose_spec.1⟩ }
theorem side_atSide (ℓ' : ℝ) (hℓ' : ℓ' ∈ PeriodicLattice.torusSides D.L) :
    (D.atSide ℓ' hℓ').side = ℓ' :=
  hℓ'.choose_spec.2.symm
abbrev TorusField : Type := PeriodicLattice.CompactGaugeField D.L D.m ((D.K : ℕ) : ℤ)
abbrev TorusSymmetry : Type := PeriodicLattice.TorusLatticeSymmetry D.L D.m D.K
def lift (U : D.TorusField) : D.GaugeField :=
  InfiniteLattice.liftCompactField U
def pullbackObs (A : D.GaugeField → ℂ) : D.TorusField → ℂ :=
  fun U => A (D.lift U)
def torusExpectation (A : D.GaugeField → ℂ) : ℂ :=
  PeriodicLattice.gibbsExpectation D.L D.m D.K D.β
    fun U => A (InfiniteLattice.liftField D.L D.m ((D.K : ℕ) : ℤ) U)
def projectPlaquette (p : InfiniteLattice.ElementaryPlaquette D.mesh) :
    PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ) :=
  CutoffLattice.projectFace D.L D.m D.K p
end Setup
end MultipleReflections
end YangMills.Construction
end
