import YangMills.Construction.Lattice.SignedPermutationMatricesAndAffineHypercubicMaps
import YangMills.Construction.ReflectionPositiveLimits.ClassesOfTuplesAndRepresentativesCentredAtAState
import YangMills.Construction.ReflectionPositiveLimits.LAdicNumbersAndLAdicMirrors
import YangMills.Construction.ReflectionPositiveLimits.RepresentativesOfSeparatedTuples
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open InfiniteLattice (GaugeField IsLocalObservable IsBoundedObservable LatticeSymmetry
  ElementaryPlaquette scaledCube regionObservables periodicGibbsSet faceEnergy latticeSubgroup
  smearedEnergy)
open GibbsAtFixedSpacing (BorelProb)
open TestFunctions (euclidDistR4 setDistR4 sharpNormR4)
open TorusMetric (euclidNormVec)
namespace LatticeRepresentatives
def toComplexObs {a : ℝ} (F : GaugeField a → ℝ) : GaugeField a → ℂ := fun U => (F U : ℂ)
def IsBoundedBoundedSupp (f : ScalarField) : Prop :=
  TestFunctions.IsBoundedFun f ∧ Bornology.IsBounded (tsupport f)
def SmearedEnergyStructure (a : ℝ) : Prop :=
  (∀ p : ElementaryPlaquette a, ∀ y ∈ p.cornerSet,
    maxNorm ((y : Space) - p.center) = a / 2 ∧
      euclidNormVec ((y : Space) - p.center) = a / √2) ∧
  ∀ f : ScalarField, IsBoundedBoundedSupp f →
    (∃ (P : Finset (ElementaryPlaquette a)) (c : ElementaryPlaquette a → ℝ),
      (∀ p ∈ P, p.center ∈ tsupport f) ∧
        ∀ U : GaugeField a, smearedEnergy f U = ∑ p ∈ P, c p * faceEnergy U p) ∧
    Continuous (smearedEnergy f : GaugeField a → ℝ) ∧
    (∀ (g : ScalarField) (α α' : ℝ), IsBoundedBoundedSupp g →
      IsBoundedBoundedSupp (α • f + α' • g) ∧
        (smearedEnergy (α • f + α' • g) : GaugeField a → ℝ) =
          α • smearedEnergy f + α' • smearedEnergy g) ∧
    ∀ S : Set Space,
      (∀ p : ElementaryPlaquette a, p.center ∈ tsupport f → ∀ y ∈ p.cornerSet, (y : Space) ∈ S) →
        toComplexObs (smearedEnergy f : GaugeField a → ℝ) ∈ regionObservables a S
def SymmetryCovariance (a : ℝ) : Prop :=
  (∀ g : Space → Space, (∃ r : LatticeSymmetry a, r.toFun = g) ↔
    ∃ w ∈ PeriodicLattice.signedPermMatrices, ∃ v ∈ latticeSubgroup a, ∀ x, g x = w *ᵥ x + v) ∧
  (∀ r : LatticeSymmetry a,
    (∀ p : ElementaryPlaquette a,
      (∃! q : ElementaryPlaquette a, q.cornerSet = r.pointMap '' p.cornerSet) ∧
        (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet) ∧
    Function.Bijective r.plaquetteMap ∧
    (∀ p : ElementaryPlaquette a, (r.plaquetteMap p).center = r.toFun p.center) ∧
    (∀ p : ElementaryPlaquette a,
      r.actOn (fun U : GaugeField a => faceEnergy U p) =
        fun U : GaugeField a => faceEnergy U (r.plaquetteMap p)) ∧
    ∀ f : ScalarField, IsBoundedBoundedSupp f →
      r.actOn (smearedEnergy f : GaugeField a → ℝ) =
        smearedEnergy (pushFn (latticeSymmetryToEuclid r) f)) ∧
  ∀ p q : ElementaryPlaquette a, ∃ r : LatticeSymmetry a, r.plaquetteMap p = q
def IsMultilinearOnSupports {V : Type*} [AddCommMonoid V] [Module ℝ V] {k : ℕ}
    (A : Fin k → Set Space) (T : Tuple → V) : Prop :=
  ∀ (i : Fin k) (h : Fin k → ScalarField) (f g : ScalarField) (α α' : ℝ),
    (∀ j, j ≠ i → h j ∈ c1Compact (A j)) →
    f ∈ c1Compact (A i) → g ∈ c1Compact (A i) →
    ∀ (h₁ : List.ofFn (Function.update h i f) ∈ separatedSet)
      (h₂ : List.ofFn (Function.update h i g) ∈ separatedSet)
      (h₃ : List.ofFn (Function.update h i (α • f + α' • g)) ∈ separatedSet),
      T ⟨_, h₃⟩ = α • T ⟨_, h₁⟩ + α' • T ⟨_, h₂⟩
def CenteredProductCalculus (L : ℕ) (K : ℕ+) (μ : BorelProb (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))) :
    Prop :=
  (∀ X : Tuple,
    Continuous (centeredProduct L K μ X) ∧
      IsBoundedObservable (toComplexObs (centeredProduct L K μ X)) ∧
        IsLocalObservable (toComplexObs (centeredProduct L K μ X))) ∧
  (∀ X Y : Tuple, X.1.Perm Y.1 → centeredProduct L K μ X = centeredProduct L K μ Y) ∧
  (∀ (k : ℕ), 1 ≤ k → ∀ A : Fin k → Set Space,
    (Pairwise fun i j => setDistR4 (A i) (A j) ≠ 0) →
      (∀ h : Fin k → ScalarField, (∀ i, h i ∈ c1Compact (A i)) →
        List.ofFn h ∈ separatedSet) ∧
      (∀ (i : Fin k) (f g : ScalarField) (α α' : ℝ), f ∈ c1Compact (A i) →
        g ∈ c1Compact (A i) → α • f + α' • g ∈ c1Compact (A i)) ∧
      IsMultilinearOnSupports A (centeredProduct L K μ)) ∧
  (∀ (X Y : Tuple) (h : Concatenable X Y),
    centeredProduct L K μ (concat X Y h) =
      centeredProduct L K μ X * centeredProduct L K μ Y) ∧
  (∀ (r : LatticeSymmetry (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))) (Z : TupleComb),
    centeredProductLinear L K μ (pushComb (latticeSymmetryToEuclid r) Z) =
      r.actOn (centeredProductLinear L K μ Z)) ∧
  ∀ (Z : TupleComb) (U : GaugeFieldsAtLevel L K),
    conj (centeredProductLinear L K μ Z U) =
      centeredProductLinear L K μ (conjComb Z) U
def CenteredProductLocality (s : Conventions.StandingParameters) (K : ℕ+)
    (μ : BorelProb (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ))) : Prop :=
  (∀ ϖ ∈ posAdicGridPoints s.L, ∀ d R : ℝ, 0 < d → 0 < R → ∀ X ∈ admissibleClass s ϖ d R,
    PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ) ≤ d / 2 →
    ∀ r : ℕ+, (r : ℝ) = ϖ / PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ) →
      toComplexObs (centeredProduct s.L K μ X) ∈
        regionObservables (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ))
          (scaledCube (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) r) ∧
      scaledCube (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) r = {x | maxNorm x ≤ ϖ}) ∧
  ∀ (n : Space) (δ : ℝ), euclidNormVec n = 1 →
    PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ) / √2 < δ →
    ∀ X : Tuple, (∀ f ∈ X.1, tsupport f ⊆ {x | δ ≤ euclidInner n x}) →
      ∃ S' : Set Space, Bornology.IsBounded S' ∧ S' ⊆ {x | 0 < euclidInner n x} ∧
        toComplexObs (centeredProduct s.L K μ X) ∈
          regionObservables (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) S'
def AdmissibleClassProperties (s : Conventions.StandingParameters) : Prop :=
  (∀ (n : ℕ) (X : Fin n → Tuple), ∃ ϖ : ℕ+, (ϖ : ℝ) ∈ posAdicGridPoints s.L ∧
    ∃ d R : ℝ, 0 < d ∧ 0 < R ∧ ∀ b, X b ∈ admissibleClass s ϖ d R) ∧
  (∀ ϖ ∈ posAdicGridPoints s.L, ∀ d R : ℝ, 0 < d → 0 < R →
    admissibleClass s ϖ d R ⊆ tuplesSupportedIn (centredCube ϖ)) ∧
  (∀ (r : EuclidIsometry) (f : ScalarField), TestFunctions.IsLipschitzFor euclidDistR4 f →
    HasCompactSupport f → ∀ M : ℝ, sharpNormR4 M (pushFn r f) = sharpNormR4 M f) ∧
  ∀ (r : EuclidIsometry) (d R : ℝ), 0 < d → 0 < R → ∀ X : Tuple,
    IsAdmissibleAt s d R X → IsAdmissibleAt s d R (push r X)
def Statement : Prop :=
  ∀ (s : Conventions.StandingParameters) (K : ℕ+) (β : ℝ)
    (μ : BorelProb (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ))),
    0 < β → μ.1 ∈ periodicGibbsSet s.L K β →
      SmearedEnergyStructure (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) ∧
      SymmetryCovariance (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) ∧
      CenteredProductCalculus s.L K μ ∧
      CenteredProductLocality s K μ ∧
      AdmissibleClassProperties s
end LatticeRepresentatives
end YangMills.Construction.ReflectionPositivity
