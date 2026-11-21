import YangMills.Construction.InfiniteLattice.PeriodicExtensionIsFormed
import YangMills.Construction.InfiniteLattice.PeriodicExtensionPeriodisationAndWeakLimitPointsAtACutoff
import YangMills.Construction.InfiniteLattice.PeriodicExtensionsAndTheirWeakLimitPoints
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace CutoffCoverLift
open CutoffLattice PeriodicExtensions
variable (L m K : ℕ)
def PointsAndLinks : Prop :=
  latticeSubgroup (PeriodicLattice.torusSide L m) ≤ latticeAt L K ∧
    torusCover L m '' (latticeAt L K : Set AmbientSpace) =
      (PeriodicLattice.sublattice L m (K : ℤ) : Set (PeriodicLattice.FourTorus L m)) ∧
    (∀ x : AmbientSpace, x ∈ latticeAt L K ↔ torusCover L m x ∈ PeriodicLattice.sublattice L m (K : ℤ)) ∧
    ∀ e : Link (CutoffLattice.spacingAt L K),
      (((projectLink L m (K : ℤ) e).source : PeriodicLattice.FourTorus L m),
          ((projectLink L m (K : ℤ) e).target : PeriodicLattice.FourTorus L m)) =
        PeriodicLiftAtCutoff.projectPair L m ((e.initial : AmbientSpace), (e.terminal : AmbientSpace)) ∧
      (e.IsPositivelyOriented → (projectLink L m (K : ℤ) e).IsPositivelyOriented) ∧
      projectLink L m (K : ℤ) e.opposite = (projectLink L m (K : ℤ) e).opposite
def FacesCovered : Prop :=
  (∀ q : ElementaryPlaquette (CutoffLattice.spacingAt L K),
    [torusFirstEdge (projectFace L m K q), torusSecondEdge (projectFace L m K q),
        torusThirdEdge (projectFace L m K q), torusFourthEdge (projectFace L m K q)] =
      [firstEdge q, secondEdge q, thirdEdge q, fourthEdge q].map (projectLink L m (K : ℤ)) ∧
    (projectFace L m K q).barycenter = torusCover L m q.center) ∧
    Function.Surjective (projectFace L m K) ∧
    ∀ q q' : ElementaryPlaquette (CutoffLattice.spacingAt L K),
      projectFace L m K q = projectFace L m K q' ↔
        (q.lowAxis, q.highAxis) = (q'.lowAxis, q'.highAxis) ∧
          (q'.corner : AmbientSpace) - (q.corner : AmbientSpace) ∈
            latticeSubgroup (PeriodicLattice.torusSide L m)
def LiftOfField (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) : Prop :=
  (∀ e : Link (CutoffLattice.spacingAt L K),
    liftCompactField U e = U.linkValue (projectLink L m (K : ℤ) e)) ∧
    (∀ q : ElementaryPlaquette (CutoffLattice.spacingAt L K),
      ((faceHolonomy (liftCompactField U) q : Matrices.ComplexMatrix2.specialUnitary) :
          Matrices.ComplexMatrix2) =
          PeriodicLattice.plaquetteHolonomy U.1 (projectFace L m K q) ∧
        faceEnergy (liftCompactField U) q =
          PeriodicLattice.plaquetteCost U.1 (projectFace L m K q)) ∧
    ∀ t : LatticePoint (CutoffLattice.spacingAt L K),
      (t : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) →
      (shift t).pullbackField (liftCompactField U) = liftCompactField U
def PushforwardWilson (β : ℝ) : Prop :=
  IsProbabilityMeasure (PeriodicTorusMeasures.pushforwardWilsonMeasure L m K β) ∧
    ∀ F : GaugeField (CutoffLattice.spacingAt L K) → ℂ, IsBoundedObservable F →
      ∫ U, F U ∂PeriodicTorusMeasures.pushforwardWilsonMeasure L m K β =
        ∫ U, F (liftCompactField U) ∂LiftFormation.torusWilson L m K β
def Statement : Prop :=
  ∀ s : Conventions.StandingParameters, ∀ β : ℝ, 0 < β →
    PointsAndLinks s.L s.m s.K ∧ FacesCovered s.L s.m s.K ∧
      (∀ U : PeriodicLattice.CompactGaugeField s.L s.m ((s.K : ℕ) : ℤ),
        LiftOfField s.L s.m s.K U) ∧
      Continuous (liftCompactField :
        PeriodicLattice.CompactGaugeField s.L s.m ((s.K : ℕ) : ℤ) →
          GaugeField (CutoffLattice.spacingAt s.L s.K)) ∧
      PushforwardWilson s.L s.m s.K β
end CutoffCoverLift
end InfiniteLattice
end YangMills.Construction
