import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGrids
import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import YangMills.Construction.Torus.LiftsAndInducedMaps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ChessboardSetup
variable (D : ChessboardSetup)
abbrev torusPeriod : ℝ := PeriodicLattice.torusSide D.L D.m
abbrev periodicSites : AddSubgroup D.Torus := PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ)
abbrev compactFields : Set (D.PeriodicLink → Matrices.ComplexMatrix2) :=
  PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)
def projPlaquette (p : D.Plaquette) : D.PeriodicPlaquette :=
  TorusLifts.projectPlaquette D.L D.m ((D.K : ℕ) : ℤ) p
def ProjectionRespectsPlaquettes : Prop :=
  D.proj '' (D.gridPoints : Set AmbientSpace) = (D.periodicSites : Set D.Torus) ∧
    Function.Surjective D.projLink ∧
    Function.Surjective D.projPlaquette ∧
    (∀ p : D.Plaquette, (D.projPlaquette p).barycenter = D.proj p.center) ∧
    ∀ (p : D.Plaquette), ∀ U ∈ D.compactFields,
      InfiniteLattice.faceEnergy (D.liftField U) p =
        PeriodicLattice.plaquetteCost U (D.projPlaquette p)
def PeriodizationRespectsObservables (f : AmbientSpace → ℂ) : Prop :=
  (∃ C : ℝ, ∀ x, ‖D.periodize f x‖ ≤ C) ∧
    (∀ (x : AmbientSpace) (k : Fin 4 → ℤ),
      D.periodize f (x + TestFunctions.latticeTranslate D.torusPeriod k) = D.periodize f x) ∧
    (∀ U ∈ D.compactFields,
      D.smeared f (D.liftField U) =
        PeriodicLattice.smearedObservable (D.descend (D.periodize f)) U) ∧
    D.liftedExpectation (fun U => Complex.exp (D.smeared f U)) =
      D.partitionFunctionOfPeriodic (D.periodize f) / D.partitionFunction 0 ∧
    ∀ A : Set AmbientSpace, TestFunctions.IsPeriodizable D.torusPeriod A f →
      D.descend (D.periodize f) = TestFunctions.periodize D.torusPeriod f
def InducedMapRespectsFields (r : D.LatticeSym) (s : D.Torus → D.Torus) : Prop :=
  s '' (D.periodicSites : Set D.Torus) = D.periodicSites ∧
    ∀ U ∈ D.compactFields,
      r.pullbackField (D.liftField U) = D.liftField (D.pullbackField s U) ∧
      ∀ e : D.PeriodicLink, ∃ e' : D.PeriodicLink,
        (e'.source : D.Torus) = s e.source ∧ (e'.target : D.Torus) = s e.target ∧
          D.pullbackField s U e = U e'
end ChessboardSetup
def ReflectionGrid.TransportsArePeriodic {D : ChessboardSetup} (g : ReflectionGrid D) : Prop :=
  ∀ U ∈ D.compactFields, ∀ v : InfiniteLattice.LatticePoint D.mesh,
    (∃ k : Fin 4 → ℤ, (v : AmbientSpace) = TestFunctions.latticeTranslate D.torusPeriod k) →
    (InfiniteLattice.shift v).pullbackField (D.liftField U) =
        D.liftField U ∧
      ∀ S ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S, ∀ S' ∈ g.cellSet,
        g.transportTo S (translate v '' S') F (D.liftField U) =
            (InfiniteLattice.shift v).actOn (g.transportTo S S' F)
              (D.liftField U) ∧
          (InfiniteLattice.shift v).actOn (g.transportTo S S' F)
              (D.liftField U) =
            g.transportTo S S' F (D.liftField U)
def LiftingRules.Statement : Prop :=
  ∀ D : ChessboardSetup,
    D.ProjectionRespectsPlaquettes ∧
      (∀ f : AmbientSpace → ℂ, (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) → ChessboardSetup.HasBoundedSupport f →
        D.PeriodizationRespectsObservables f) ∧
      (∀ g : ReflectionGrid D, 2 * g.cellSide ≤ D.torusPeriod → g.TransportsArePeriodic) ∧
      ∀ (r : D.LatticeSym) (s : D.Torus → D.Torus),
        D.proj ∘ r.toFun = s ∘ D.proj → D.InducedMapRespectsFields r s
end YangMills.Construction.ChessboardTori
end
