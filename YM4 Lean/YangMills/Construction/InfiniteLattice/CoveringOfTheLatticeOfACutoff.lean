import YangMills.Construction.InfiniteLattice.CoveringPeriodicExtensionsAndTheTwoSetsOfStates
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import YangMills.Construction.InfiniteLattice.WindowsOfTheLatticeOfACutoff
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set InfiniteLattice
namespace CutoffLinks.CutoffData
variable (d : CutoffData)
abbrev PeriodicSite : Type := PeriodicLattice.Site d.L d.m ((d.K : ℕ) : ℤ)
abbrev PeriodicBond : Type := PeriodicLattice.Bond d.L d.m ((d.K : ℕ) : ℤ)
abbrev PeriodicPlaquette : Type := PeriodicLattice.Plaquette d.L d.m ((d.K : ℕ) : ℤ)
abbrev PeriodicFields : Type := PeriodicLattice.CompactGaugeField d.L d.m ((d.K : ℕ) : ℤ)
def positiveLinkAt (y : d.PeriodicSite) (μ : Fin 4) : d.PeriodicBond :=
  PeriodicLattice.Bond.forwardFrom y μ
abbrev positiveLinkSet : Set d.PeriodicBond :=
  PeriodicLattice.forwardBonds d.L d.m ((d.K : ℕ) : ℤ)
variable {d}
abbrev GroupFamily (R : Set d.PeriodicBond) : Type := R → Matrices.ComplexMatrix2.specialUnitary
def FaceContains (p : d.PeriodicPlaquette) (l : d.PeriodicBond) : Prop :=
  l ∈ InfiniteLattice.WilsonOperator.periodicEdgeList p
variable (d)
abbrev projLink (b : Link d.spacing) : d.PeriodicBond := projectLink d.L d.m ((d.K : ℕ) : ℤ) b
theorem projLink_forwardFrom (x : LatticePoint d.spacing) (μ : Fin 4) :
    d.projLink (Link.forwardFrom x μ) =
      d.positiveLinkAt (projectPoint d.L d.m ((d.K : ℕ) : ℤ) x) μ := by
  refine PeriodicLattice.Bond.ext rfl ?_
  have hsub := projectPoint_sub d.L d.m ((d.K : ℕ) : ℤ) (x + axisStep d.spacing μ) x
  rw [add_sub_cancel_left, projectPoint_axisStep] at hsub
  exact eq_add_of_sub_eq' hsub.symm
abbrev projFace (p : ElementaryPlaquette d.spacing) : d.PeriodicPlaquette :=
  CutoffLattice.projectFace d.L d.m d.K p
def projLinks (S : Set (Link d.spacing)) : Set d.PeriodicBond := d.projLink '' S
abbrev liftField (U : d.PeriodicFields) : GaugeField d.spacing := liftCompactField U
variable {d}
def CutoffWindow.EmbedsInPeriodicLattice (W : d.CutoffWindow) : Prop :=
  InjOn d.projLink (W.links ∪ W.rim)
end CutoffLinks.CutoffData
end YangMills.Construction
