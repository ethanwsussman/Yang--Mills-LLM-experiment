import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.FactsOfTheBondsConfigurationsAndMotionsAtOneSpacing
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import YangMills.Construction.Torus.LiftsAndInducedMaps
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace PeriodicLift
variable {a : ℝ}
def linkEndpoints (S : Finset (Link a)) : Set (LatticePoint a) :=
  {x | ∃ e ∈ S, x = e.initial ∨ x = e.terminal}
def endpointDiameter (S : Finset (Link a)) : ℝ :=
  sSup {t | ∃ x ∈ linkEndpoints S, ∃ y ∈ linkEndpoints S,
    t = GibbsAtFixedSpacing.linfNorm ((x : AmbientSpace) - (y : AmbientSpace))}
theorem meshSize_pos (s : Conventions.StandingParameters) :
    0 < PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ) := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.meshSize_pos <;> assumption
def ProjectsPlaquettes (s : Conventions.StandingParameters) : Prop :=
  ∀ p : ElementaryPlaquette (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)),
    WilsonOperator.periodicEdgeList (TorusLifts.projectPlaquette s.L s.m ((s.K : ℕ) : ℤ) p) =
        (WilsonOperator.edgeList p).map (projectLink s.L s.m ((s.K : ℕ) : ℤ)) ∧
      ∀ U ∈ PeriodicLattice.compactGaugeFields s.L s.m ((s.K : ℕ) : ℤ),
        ((faceHolonomy (liftField s.L s.m ((s.K : ℕ) : ℤ) U) p :
            Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
            PeriodicLattice.plaquetteHolonomy U
              (TorusLifts.projectPlaquette s.L s.m ((s.K : ℕ) : ℤ) p) ∧
          faceEnergy (liftField s.L s.m ((s.K : ℕ) : ℤ) U) p =
            PeriodicLattice.plaquetteCost U
              (TorusLifts.projectPlaquette s.L s.m ((s.K : ℕ) : ℤ) p)
def ShiftInvariant (s : Conventions.StandingParameters) (β : ℝ) : Prop :=
  ∀ v : LatticePoint (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)),
    IsSymmetricUnder (liftedWilsonMeasure s.L s.m s.K β) (shift v)
def KernelInvariantInWindow (s : Conventions.StandingParameters) (β : ℝ) : Prop :=
  ∀ (L S : Finset (Link (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ))))
    (hL : (L : Set (Link (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)))) ⊆ S)
    (hS : (S : Set (Link (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)))) ⊆
      positiveLinkSet (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ))),
    WilsonOperator.thickenedLinks L ⊆ S →
      endpointDiameter S < s.side →
        ∀ F : GaugeField (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)) → ℂ,
          IsBoundedObservable F → DependsOnlyOnLinks (S : Set _) F →
            ∫ U, WilsonOperator.kernelOperator (meshSize_pos s) β (hL.trans hS) F U
                ∂liftedWilsonMeasure s.L s.m s.K β =
              ∫ U, F U ∂liftedWilsonMeasure s.L s.m s.K β
end PeriodicLift
def PeriodicLift.Statement : Prop :=
  ∀ s : Conventions.StandingParameters, ∀ β : ℝ, 0 < β →
    PeriodicLift.ProjectsPlaquettes s ∧
      PeriodicLift.ShiftInvariant s β ∧
        PeriodicLift.KernelInvariantInWindow s β
end YangMills.Construction.InfiniteLattice
