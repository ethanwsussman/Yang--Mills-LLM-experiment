import YangMills.Construction.InfiniteLattice.CutoffLattice
import YangMills.Construction.InfiniteLattice.PeriodicExtensionPeriodisationAndWeakLimitPointsAtACutoff
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.ReflectionPositivity.AxisMirrorData
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CutoffCovering
open YangMills.Construction.CutoffLattice
def PeriodsAndLinks (L m K : ℕ) : Prop :=
  latticeSubgroup (PeriodicLattice.torusSide L m) ≤ latticeSubgroup (CutoffLattice.spacingAt L K) ∧
    (∀ e e' : Link (CutoffLattice.spacingAt L K),
      projectLink L m (K : ℤ) e = projectLink L m (K : ℤ) e' ↔
        ∃ v : LatticePoint (CutoffLattice.spacingAt L K),
          (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) ∧
            e' = (shift v).linkMap e) ∧
    ∀ c : PeriodicLattice.Bond L m (K : ℤ),
      ∃ e : Link (CutoffLattice.spacingAt L K), projectLink L m (K : ℤ) e = c
def LiftIsBijective (L m K : ℕ) : Prop :=
  BijOn (liftCompactField : PeriodicLattice.CompactGaugeField L m (K : ℤ) → _) univ
    (periodicFields L m (K : ℤ))
def LiftAndMeasure (L m K : ℕ) (β : ℝ) : Prop :=
  (∀ U : PeriodicLattice.CompactGaugeField L m (K : ℤ),
    liftField L m (K : ℤ) U.1 = liftCompactField U) ∧
    (∀ (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) (e : Link (CutoffLattice.spacingAt L K)),
      liftCompactField U e = U.linkValue (projectLink L m (K : ℤ) e)) ∧
    IsProbabilityMeasure (liftedWilsonMeasure L m K β) ∧
    (∀ E : Set (FieldsAt L K), MeasurableSet E →
      liftedWilsonMeasure L m K β E =
        PeriodicLattice.wilsonGibbsMeasure L m K β
          {U | ∃ hU : U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ),
            liftCompactField (⟨U, hU⟩ : PeriodicLattice.CompactGaugeField L m (K : ℤ)) ∈ E}) ∧
    liftedWilsonMeasure L m K β = PeriodicTorusMeasures.pushforwardWilsonMeasure L m K β
def LimitsAreTorusStates (L K : ℕ) (β : ℝ) : Prop :=
  {ν | IsInfiniteVolumeLimit L K β ν} =
    (fun ν : ProbabilityMeasure (FieldsAt L K) => (ν : Measure (FieldsAt L K))) ''
      PeriodicLiftAtCutoff.weakClusterPoints L K β
def CoveringIdentification : Prop :=
  ∀ S : ReflectionPositivity.AxisMirror.MirrorData,
    PeriodsAndLinks S.L S.m S.K ∧ LiftIsBijective S.L S.m S.K ∧
      LiftAndMeasure S.L S.m S.K S.β ∧
      LimitsAreTorusStates S.L S.K S.β
end YangMills.Construction.InfiniteLattice.CutoffCovering
end
