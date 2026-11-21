import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.InfiniteLattice.CopiesBoxesAndTheChessboardNorm
import YangMills.Construction.InfiniteLattice.PeriodicExtensionPeriodisationAndWeakLimitPointsAtACutoff
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace PeriodizationIdentities
open YangMills.Construction.InfiniteLattice (IsBoundedBorelCompactlySupported AmbientSpace liftCompactField
  smearedEnergyCumulant smearedEnergy weightedPartitionFn)
open YangMills.Construction.InfiniteLattice.PeriodicLiftAtCutoff (cutoffConnectedFunction periodizeTuple)
open YangMills.Construction.InfiniteLattice.PeriodicTorusMeasures (measureConnectedFunction
  pushforwardWilsonMeasure)
def DiameterLT (A : Set AmbientSpace) (r : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ D < r ∧ TestFunctions.HasDiameterLE A D
def PeriodicSumDescends (L m : ℕ) : Prop :=
  ∀ v : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported v →
    (∀ x : AmbientSpace, {k : Fin 4 → ℤ |
      v (x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide L m) k) ≠ 0}.Finite) ∧
    (∃ C : ℝ, ∀ x, ‖TestFunctions.periodicSum (PeriodicLattice.torusSide L m) v x‖ ≤ C) ∧
    (∀ (x : AmbientSpace) (k : Fin 4 → ℤ),
      TestFunctions.periodicSum (PeriodicLattice.torusSide L m) v
          (x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide L m) k) =
        TestFunctions.periodicSum (PeriodicLattice.torusSide L m) v x) ∧
    (∃! g : PeriodicLattice.FourTorus L m → ℂ, g ∘ TorusMetric.torusProj (PeriodicLattice.torusSide L m) =
      TestFunctions.periodicSum (PeriodicLattice.torusSide L m) v) ∧
    TestFunctions.periodize (PeriodicLattice.torusSide L m) v ∘
        TorusMetric.torusProj (PeriodicLattice.torusSide L m) =
      TestFunctions.periodicSum (PeriodicLattice.torusSide L m) v ∧
    (DiameterLT (tsupport v) (PeriodicLattice.torusSide L m / 2) →
      TestFunctions.IsPeriodizable (PeriodicLattice.torusSide L m) (tsupport v) v)
def SmearedEnergyOfLift (L m K : ℕ) : Prop :=
  ∀ v : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported v →
    ∀ U : PeriodicLattice.CompactGaugeField L m (K : ℤ),
      smearedEnergy v (liftCompactField U) =
        PeriodicLattice.smearedObservable (TestFunctions.periodize (PeriodicLattice.torusSide L m) v) U.1
def ExpMomentRatio (L m K : ℕ) (β : ℝ) : Prop :=
  weightedPartitionFn L m K β 0 = (PeriodicLattice.partitionFunction L m K β : ℂ) ∧
    0 < PeriodicLattice.partitionFunction L m K β ∧
    ∀ v : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported v →
      ∫ U, Complex.exp (smearedEnergy v U) ∂pushforwardWilsonMeasure L m K β =
        weightedPartitionFn L m K β (TestFunctions.periodize (PeriodicLattice.torusSide L m) v) /
          weightedPartitionFn L m K β 0
def LiftCumulants (L m K : ℕ) (β : ℝ) : Prop :=
  ∀ (n : ℕ) (f : Fin n → AmbientSpace → ℝ), 1 ≤ n → (∀ i, IsBoundedBorelCompactlySupported (f i)) →
    IsProbabilityMeasure (pushforwardWilsonMeasure L m K β) ∧
    (∀ i, Measurable (smearedEnergy (a := PeriodicLattice.meshSize L (K : ℤ)) (f i)) ∧
      ∃ C : ℝ, ∀ U, |smearedEnergy (a := PeriodicLattice.meshSize L (K : ℤ)) (f i) U| ≤ C) ∧
    smearedEnergyCumulant (pushforwardWilsonMeasure L m K β) f =
      PeriodicLattice.gibbsCumulant L m K β
        (fun i U => PeriodicLattice.smearedObservable (periodizeTuple L m f i) U) ∧
    PeriodicLattice.gibbsCumulant L m K β
        (fun i U => PeriodicLattice.smearedObservable (periodizeTuple L m f i) U) =
      cutoffConnectedFunction L m K β (periodizeTuple L m f) ∧
    (2 ≤ n → measureConnectedFunction (pushforwardWilsonMeasure L m K β) f =
      smearedEnergyCumulant (pushforwardWilsonMeasure L m K β) f)
def LiftCumulantsAreSchwinger (L m K : ℕ) (β : ℝ) : Prop :=
  ∀ (n : ℕ) (f : Fin n → AmbientSpace → ℝ), 2 ≤ n → (∀ i, IsBoundedBorelCompactlySupported (f i)) →
    (∀ i k, i ≠ k → 0 < TestFunctions.setDistR4 (tsupport (f i)) (tsupport (f k))) →
    (∃ A : Set AmbientSpace, DiameterLT A (PeriodicLattice.torusSide L m / 2) ∧
      ∀ i, tsupport (f i) ⊆ A) →
    SchwingerFunctions.IsR4TestFamily (PeriodicLattice.torusSide L m) f ∧
    periodizeTuple L m f = SchwingerFunctions.periodizeAll L m f ∧
    SchwingerFunctions.IsTorusTestFamily (SchwingerFunctions.periodizeAll L m f) ∧
    measureConnectedFunction (pushforwardWilsonMeasure L m K β) f =
      SchwingerFunctions.connectedSchwingerR4 L m K β f
def Statement : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K → ∀ β : ℝ, 0 < β →
    PeriodicSumDescends L m ∧ SmearedEnergyOfLift L m K ∧
      ExpMomentRatio L m K β ∧ LiftCumulants L m K β ∧
      LiftCumulantsAreSchwinger L m K β
end PeriodizationIdentities
end YangMills.Construction
end
