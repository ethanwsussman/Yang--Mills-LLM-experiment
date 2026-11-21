import YangMills.Construction.InfiniteLattice.PeriodicExtensionsAndTheirWeakLimitPoints
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.WeakLimitPointsAlongSides
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.TorusFieldsAsPeriodic
open YangMills.Construction.CutoffLattice YangMills.Construction.InfiniteLattice.PeriodicExtensions
def ProjectionOnOrientedLinks (L m K : ℕ) : Prop :=
  (∀ b : Link (CutoffLattice.spacingAt L K),
    projectLink L m (K : ℤ) b.opposite = (projectLink L m (K : ℤ) b).opposite) ∧
    (∀ c : PeriodicLattice.Bond L m (K : ℤ),
      ∃ b : Link (CutoffLattice.spacingAt L K), projectLink L m (K : ℤ) b = c) ∧
    ∀ b b' : Link (CutoffLattice.spacingAt L K),
      projectLink L m (K : ℤ) b = projectLink L m (K : ℤ) b' ↔
        ∃ v : LatticePoint (CutoffLattice.spacingAt L K),
          (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) ∧
            b' = CutoffLattice.translateLink b v
def linkPeriodicFields (L m K : ℕ) : Set (CutoffLattice.FieldsAt L K) :=
  {U | ∀ (b : Link (CutoffLattice.spacingAt L K)) (v : LatticePoint (CutoffLattice.spacingAt L K)),
    (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) →
      U (CutoffLattice.translateLink b v) = U b}
def LiftOntoPeriodicFields (L m K : ℕ) : Prop :=
  (∀ (W : PeriodicLattice.CompactGaugeField L m (K : ℤ)) (b : Link (CutoffLattice.spacingAt L K)),
    liftCompactField W b = W.linkValue (projectLink L m (K : ℤ) b)) ∧
    Continuous (liftCompactField : PeriodicLattice.CompactGaugeField L m (K : ℤ) → _) ∧
    Function.Injective
      (liftCompactField : PeriodicLattice.CompactGaugeField L m (K : ℤ) → _) ∧
    range (liftCompactField : PeriodicLattice.CompactGaugeField L m (K : ℤ) → _) =
      linkPeriodicFields L m K ∧
    linkPeriodicFields L m K = periodicFields L m (K : ℤ)
def LiftedMeasureAsImage (L m K : ℕ) (β : ℝ) : Prop :=
  IsProbabilityMeasure (liftedWilsonMeasure L m K β) ∧
    ∀ E : Set (CutoffLattice.FieldsAt L K), MeasurableSet E →
      liftedWilsonMeasure L m K β E =
        PeriodicLattice.wilsonGibbsMeasure L m K β
          {U | ∃ h : U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ),
            liftCompactField (⟨U, h⟩ : PeriodicLattice.CompactGaugeField L m (K : ℤ)) ∈ E}
def SubsequentialLimitsAreTorusLimits (L K : ℕ) (β : ℝ) : Prop :=
  ∀ ν : RealWeakState (CutoffLattice.spacingAt L K),
    (IsInfiniteVolumeLimit L K β ν.measure ↔ ν ∈ limitsOfLiftedMeasures L K β) ∧
      (IsWeakLimitAlongSides L K β ν.measure ↔ ν ∈ limitsOfLiftedMeasures L K β)
def TorusLimitsArePeriodicGibbs (L K : ℕ) (β : ℝ) : Prop :=
  (limitsOfLiftedMeasures L K β).Nonempty ∧
    ∀ ν ∈ limitsOfLiftedMeasures L K β, ν.measure ∈ periodicGibbsSet L K β
def Statement : Prop :=
  ∀ (s : Conventions.StandingParameters) (β : ℝ), 0 < β →
    ProjectionOnOrientedLinks s.L s.m s.K ∧ LiftOntoPeriodicFields s.L s.m s.K ∧
      LiftedMeasureAsImage s.L s.m s.K β ∧
      SubsequentialLimitsAreTorusLimits s.L s.K β ∧
      TorusLimitsArePeriodicGibbs s.L s.K β
end YangMills.Construction.InfiniteLattice.TorusFieldsAsPeriodic
