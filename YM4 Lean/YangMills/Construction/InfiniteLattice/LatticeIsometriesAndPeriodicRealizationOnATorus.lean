import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservables
import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.StandingConventionsOfMultipleReflections
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.MultipleReflections
namespace Setup
variable (D : Setup)
def IsDescentOf (s : D.TorusSymmetry) (g : D.LatticeSymmetry) : Prop :=
  ∀ x : InfiniteLattice.AmbientSpace, D.projection (g.toFun x) = s.toFun (D.projection x)
def PullbackRespectsAlgebra : Prop :=
  Continuous D.lift ∧
    ∀ A B : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable A →
      InfiniteLattice.IsBoundedObservable B → ∀ c : ℂ,
      Measurable (D.pullbackObs A) ∧ (∃ C : ℝ, ∀ U, ‖D.pullbackObs A U‖ ≤ C) ∧
      (⨆ U, ‖D.pullbackObs A U‖) ≤ InfiniteLattice.observableSupNorm A ∧
      D.pullbackObs (A + B) = D.pullbackObs A + D.pullbackObs B ∧
      D.pullbackObs (A * B) = D.pullbackObs A * D.pullbackObs B ∧
      D.pullbackObs (c • A) = c • D.pullbackObs A ∧
      D.pullbackObs (fun U => conj (A U)) = (fun U => conj (D.pullbackObs A U)) ∧
      D.pullbackObs (1 : D.GaugeField → ℂ) = 1
def SymmetriesAreHyperoctahedralMotions : Prop :=
  ∀ g : D.LatticeSymmetry,
    (∃ R ∈ InfiniteLattice.hyperoctahedralLinearGroup,
      ∃ v ∈ InfiniteLattice.latticeSubgroup D.mesh,
        ∀ x : InfiniteLattice.AmbientSpace, g.toFun x = R x + v) ∧
    Function.Surjective g.linkMap ∧
    (∀ p : InfiniteLattice.ElementaryPlaquette D.mesh, ∃ q : InfiniteLattice.ElementaryPlaquette D.mesh,
      q.cornerSet = g.pointMap '' p.cornerSet) ∧
    ∀ q : InfiniteLattice.ElementaryPlaquette D.mesh, ∃ p : InfiniteLattice.ElementaryPlaquette D.mesh,
      q.cornerSet = g.pointMap '' p.cornerSet
def SymmetriesClosedUnderInvMul : Prop :=
  (∀ g : D.LatticeSymmetry, ∃ h : D.LatticeSymmetry, h.IsInverse g) ∧
    ∀ g h : D.LatticeSymmetry, ∃ c : D.LatticeSymmetry, c.toFun = g.toFun ∘ h.toFun
def ActOnRespectsAlgebra : Prop :=
  ∀ g : D.LatticeSymmetry,
    Function.Bijective g.pullbackField ∧
    ∀ A B : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable A →
      InfiniteLattice.IsBoundedObservable B → ∀ c : ℂ,
      g.actOn (A + B) = g.actOn A + g.actOn B ∧
      g.actOn (A * B) = g.actOn A * g.actOn B ∧
      g.actOn (c • A) = c • g.actOn A ∧
      g.actOn (fun U => conj (A U)) = (fun U => conj (g.actOn A U)) ∧
      g.actOn (1 : D.GaugeField → ℂ) = 1 ∧
      InfiniteLattice.observableSupNorm (g.actOn A) = InfiniteLattice.observableSupNorm A
def SymmetriesDescendToTorus : Prop :=
  ∀ g : D.LatticeSymmetry,
    (∃ s : D.TorusSymmetry, D.IsDescentOf s g) ∧
    ∀ s : D.TorusSymmetry, D.IsDescentOf s g →
      (∀ U : D.TorusField, g.pullbackField (D.lift U) = D.lift (s.pullback U)) ∧
      ∀ A : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable A →
        D.pullbackObs (g.actOn A) = D.pullbackObs A ∘ s.pullback
def PeriodShiftsInvisible : Prop :=
  (∀ k : Fin 4 → ℤ, TestFunctions.latticeTranslate D.side k ∈ InfiniteLattice.latticeSubgroup D.mesh) ∧
    ∀ (v : InfiniteLattice.LatticePoint D.mesh) (k : Fin 4 → ℤ),
      (v : InfiniteLattice.AmbientSpace) = TestFunctions.latticeTranslate D.side k →
      ∀ A : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable A →
        D.pullbackObs ((InfiniteLattice.shift v).actOn A) = D.pullbackObs A
def ProjectionMatchesFaces : Prop :=
  ∀ (p : InfiniteLattice.ElementaryPlaquette D.mesh) (U : D.TorusField),
    (D.projectPlaquette p).barycenter = D.projection p.center ∧
      InfiniteLattice.faceEnergy (D.lift U).1 p =
        PeriodicLattice.plaquetteCost U.1 (D.projectPlaquette p)
def PullbackSmearedEqPeriodized : Prop :=
  ∀ S : Set InfiniteLattice.AmbientSpace,
    (∀ f : InfiniteLattice.AmbientSpace → ℂ, Measurable f → TestFunctions.IsBoundedFun f →
      TestFunctions.IsPeriodizable D.side S f →
      ∀ U : D.TorusField,
        D.pullbackObs (InfiniteLattice.smearedEnergy f) U =
          PeriodicLattice.smearedObservable (TestFunctions.periodize D.side f) U.1) ∧
    ∀ f : InfiniteLattice.AmbientSpace → ℝ, Measurable f → TestFunctions.IsBoundedFun f →
      TestFunctions.IsPeriodizable D.side S f →
      ∀ U : D.TorusField,
        D.pullbackObs (fun V => ((InfiniteLattice.smearedEnergy f V : ℝ) : ℂ)) U =
          ((PeriodicLattice.smearedObservable (TestFunctions.periodize D.side f) U.1 : ℝ) : ℂ)
end Setup
def SymmetriesAndTorusPullback : Prop :=
  ∀ D : Setup,
    D.PullbackRespectsAlgebra ∧
    D.SymmetriesAreHyperoctahedralMotions ∧ D.SymmetriesClosedUnderInvMul ∧
    D.ActOnRespectsAlgebra ∧
    D.SymmetriesDescendToTorus ∧ D.PeriodShiftsInvisible ∧
    D.ProjectionMatchesFaces ∧ D.PullbackSmearedEqPeriodized
end YangMills.Construction.MultipleReflections
end
