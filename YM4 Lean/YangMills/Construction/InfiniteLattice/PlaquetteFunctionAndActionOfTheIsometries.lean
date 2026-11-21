import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import YangMills.Construction.InfiniteLattice.SidesOfAPlaquetteAndTheDensityOfBoundedSupport
import YangMills.Construction.InfiniteLattice.UnitSpacingLatticeData
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.Lattice.ParallelBondsAndSidesOfAPlaquette
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def IsLoopAroundPlaquette (p : Plaquette L m j) (γ : List (Bond L m j)) : Prop :=
  γ.length = 4 ∧ (∃ x, IsBondPathFromTo γ x x) ∧ {x | ∃ b ∈ γ, b.source = x} = p.vertices
end PeriodicLattice
namespace InfiniteLattice
open FixedSpacing
def FaceEnergyProperties (a : ℝ) : Prop :=
  ∀ p : ElementaryPlaquette a,
    (∀ (U : GaugeField a) (c c' : GibbsAtFixedSpacing.BoundaryCycle p),
      (Matrices.ComplexMatrix2.fullTrace (c.holonomy U : Matrices.ComplexMatrix2)).re =
        (Matrices.ComplexMatrix2.fullTrace (c'.holonomy U : Matrices.ComplexMatrix2)).re) ∧
    (∀ U : GaugeField a, 0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2) ∧
    Continuous (fun U : GaugeField a => faceEnergy U p) ∧
    DependsOnlyOnLinks {b | b ∈ p.sideLinks} (fun U : GaugeField a => faceEnergy U p)
def PeriodicFaceEnergyProperties (L m : ℕ) (j : ℤ) : Prop :=
  ∀ p : PeriodicLattice.Plaquette L m j,
    (∀ (U : PeriodicLattice.CompactGaugeField L m j) (γ γ' : List (PeriodicLattice.Bond L m j)),
      PeriodicLattice.IsLoopAroundPlaquette p γ → PeriodicLattice.IsLoopAroundPlaquette p γ' →
        (Matrices.ComplexMatrix2.fullTrace (PeriodicLattice.pathHolonomy U.1 γ)).re =
          (Matrices.ComplexMatrix2.fullTrace (PeriodicLattice.pathHolonomy U.1 γ')).re) ∧
    (∀ U : PeriodicLattice.CompactGaugeField L m j,
      0 ≤ PeriodicLattice.plaquetteCost U.1 p ∧ PeriodicLattice.plaquetteCost U.1 p ≤ 2) ∧
    Continuous (fun U : PeriodicLattice.CompactGaugeField L m j =>
      PeriodicLattice.plaquetteCost U.1 p) ∧
    PeriodicLattice.DependsOnlyOn p.edges (fun U : PeriodicLattice.CompactGaugeField L m j =>
      PeriodicLattice.plaquetteCost U.1 p)
def ComposesOnTheRight {a : ℝ} (r t : latticeMotions a) : Prop :=
  ∃ h : latticeMotionMul r.1 t.1 ∈ latticeMotions a,
    latticeMotionField t ∘ latticeMotionField r = latticeMotionField ⟨_, h⟩ ∧
    ∀ F : GaugeField a → ℂ,
      latticeMotionAct r (latticeMotionAct t F) = latticeMotionAct ⟨_, h⟩ F
def ActsByHomeomorph {a : ℝ} (r : latticeMotions a) : Prop :=
  ∃ r' : latticeMotions a, r.1 ∘ r'.1 = id ∧ r'.1 ∘ r.1 = id ∧
    ∃ e : GaugeField a ≃ₜ GaugeField a,
      ⇑e = latticeMotionField r ∧ ⇑e.symm = latticeMotionField r'
def ActsOnObservables {a : ℝ} (r : latticeMotions a) : Prop :=
  (∀ (c₁ c₂ : ℂ) (F₁ F₂ : GaugeField a → ℂ),
    latticeMotionAct r (c₁ • F₁ + c₂ • F₂) =
      c₁ • latticeMotionAct r F₁ + c₂ • latticeMotionAct r F₂) ∧
  (∀ F₁ F₂ : GaugeField a → ℂ,
    latticeMotionAct r (F₁ * F₂) = latticeMotionAct r F₁ * latticeMotionAct r F₂) ∧
  (∀ F : GaugeField a → ℂ,
    latticeMotionAct r (fun U => conj (F U)) = fun U => conj (latticeMotionAct r F U)) ∧
  (∀ S : Set AmbientSpace,
    latticeMotionAct r '' localizedBoundedObservables a S =
      localizedBoundedObservables a (r.1 '' S)) ∧
  latticeMotionAct r '' continuousCylinderFunctions a = continuousCylinderFunctions a
def FaceEnergyAndMotionStatement : Prop :=
  ∀ D : Params,
    FaceEnergyProperties D.mesh ∧
    PeriodicFaceEnergyProperties D.L D.m ((D.K : ℕ) : ℤ) ∧
    ∀ r : latticeMotions D.mesh,
      (∀ (U : GaugeField D.mesh) (b : Link D.mesh),
        latticeMotionField r U b.opposite = (latticeMotionField r U b)⁻¹) ∧
      (∀ t : latticeMotions D.mesh, ComposesOnTheRight r t) ∧
      ActsByHomeomorph r ∧
      ActsOnObservables r
end InfiniteLattice
end YangMills.Construction
