import YangMills.Construction.Lattice.LatticeSymmetriesRectangularToriAndInducedSymmetries
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.CoordinateMirrorsThroughLinks
import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import YangMills.Construction.InfiniteLattice.SidesOfAPlaquetteAndTheDensityOfBoundedSupport
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.Lattice.SiteCoordinates
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice.OneSpacing
open InfiniteLattice
def LinkVariablesBorelEqPi (ι : Type) : Prop :=
  borel (LinkVariables ι) =
      @MeasurableSpace.pi ι (fun _ => Matrices.ComplexMatrix2.specialUnitary)
        (fun _ => borel Matrices.ComplexMatrix2.specialUnitary) ∧
    borel (LinkVariables ι) =
      ⨆ e : ι, MeasurableSpace.comap (fun V : LinkVariables ι => V e)
        (borel Matrices.ComplexMatrix2.specialUnitary)
section Space
variable {a : ℝ}
def FieldsAsProduct (a : ℝ) : Prop :=
  (positiveLinkSet a).Countable ∧
    (∀ e : Link a, Xor (e ∈ positiveLinkSet a)
      (∃ e' ∈ positiveLinkSet a, e = e'.opposite)) ∧
    IsHomeomorph fun U : GaugeField a => restrictField U (positiveLinkSet a)
def FieldBorelGenerated (a : ℝ) : Prop :=
  (∀ S : Set (Link a), S ⊆ positiveLinkSet a → LinkVariablesBorelEqPi S) ∧
    borel (GaugeField a) = linkSigma (positiveLinkSet a)
def FieldSplitting (ha : 0 < a) : Prop :=
  ∀ (S : Set (Link a)) (hS : S ⊆ positiveLinkSet a),
    (IsHomeomorph fun U : GaugeField a =>
      (restrictField U S, restrictField U (positiveLinkSet a \ S))) ∧
    (∀ (V : LinkVariables S) (ω : GaugeField a),
      (restrictField (gluedField ha hS V ω) S,
        restrictField (gluedField ha hS V ω) (positiveLinkSet a \ S)) =
      (V, restrictField ω (positiveLinkSet a \ S))) ∧
    (Continuous fun q : LinkVariables S × GaugeField a => gluedField ha hS q.1 q.2) ∧
    (∀ V : LinkVariables S,
      DependsOnlyOnLinks (positiveLinkSet a \ S) (gluedField ha hS V)) ∧
    ∀ (V : LinkVariables S) (ω : GaugeField a),
      restrictField (gluedField ha hS V ω) S = V
def MotionsClosed (a : ℝ) : Prop :=
  id ∈ latticeMotions a ∧
    (∀ g ∈ latticeMotions a, ∀ h ∈ latticeMotions a,
      latticeMotionMul g h ∈ latticeMotions a) ∧
    ∀ g ∈ latticeMotions a, ∃ h ∈ latticeMotions a,
      latticeMotionMul g h = id ∧ latticeMotionMul h g = id
def MotionGroupFacts (a : ℝ) : Prop :=
  MotionsClosed a ∧
    (∀ g ∈ latticeMotions a,
      (∀ x y, TorusMetric.euclidNormVec (g x - g y) = TorusMetric.euclidNormVec (x - y)) ∧
        g '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a) ∧
    (∀ v ∈ latticeSubgroup a, (fun x : AmbientSpace => x + v) ∈ latticeMotions a) ∧
    (∀ w ∈ hypercubicGroup, (⇑w : AmbientSpace → AmbientSpace) ∈ latticeMotions a) ∧
    ∀ (μ : Fin 4) (c : ℝ), (∃ n : ℤ, 2 * c = (n : ℝ) * a) →
      coordinateReflection μ c ∈ latticeMotions a
def PlaquetteFiniteness (a : ℝ) : Prop :=
  (∀ B : Set AmbientSpace, Bornology.IsBounded B →
      {P : ElementaryPlaquette a | P.center ∈ B}.Finite) ∧
    (∀ f : AmbientSpace → ℂ, IsBoundedOfBoundedSupport f →
      {P : ElementaryPlaquette a | f P.center ≠ 0}.Finite) ∧
    (∀ (x : LatticePoint a) (κ : Fin 4),
      {P : ElementaryPlaquette a | Link.forwardFrom x κ ∈ P.sideLinks}.encard = 6) ∧
    ∀ W : Set (Link a), W ⊆ positiveLinkSet a → W.Finite →
      {P : ElementaryPlaquette a | P.HasEdgeIn W}.encard ≤ 6 * W.encard ∧
        {e : Link a | ∃ P : ElementaryPlaquette a, P.HasEdgeIn W ∧ e ∈ P.sideLinks}.Finite
def MirrorsAtHalfLevels (a : ℝ) : Prop :=
  ∀ (μ : Fin 4) (c : ℝ), c ∈ halfIntegerLevels a →
    ({x : AmbientSpace | x μ = c} ∩ (latticeSubgroup a : Set AmbientSpace) = ∅) ∧
      coordinateReflection μ c ∈ latticeMotions a
end Space
section Torus
open PeriodicLattice (CompactGaugeField forwardBonds pointsPerAxis)
variable {L m : ℕ} {j : ℤ}
def TorusCounts (L m K : ℕ) : Prop :=
  pointsPerAxis L m K = PeriodicLattice.torusSide L m / PeriodicLattice.meshSize L (K : ℤ) ∧
    pointsPerAxis L m K = 2 * (L : ℝ) ^ (m + K) ∧
    (∀ (y : PeriodicLattice.Site L m (K : ℤ)) (μ : Fin 4),
      ((PeriodicLattice.axisLine y μ).ncard : ℝ) = pointsPerAxis L m K) ∧
    (∃ n : ℤ, Even n ∧ pointsPerAxis L m K = (n : ℝ)) ∧
    3 ≤ pointsPerAxis L m K ∧
    PeriodicLattice.meshSize L (K : ℤ) < PeriodicLattice.torusSide L m / 2 ∧
    ∀ C : ℝ, ∃ ℓ ∈ PeriodicLattice.torusSides L, C < ℓ
def TorusFieldsAsProduct (L m : ℕ) (j : ℤ) : Prop :=
  (forwardBonds L m j).Finite ∧
    IsHomeomorph fun U : CompactGaugeField L m j =>
      U.restrictTo (forwardBonds L m j)
def TorusFieldBorelGenerated (L m : ℕ) (j : ℤ) : Prop :=
  (∀ S : Set (PeriodicLattice.Bond L m j), S ⊆ forwardBonds L m j →
      LinkVariablesBorelEqPi S) ∧
    borel (CompactGaugeField L m j) =
      ⨆ e ∈ forwardBonds L m j,
        MeasurableSpace.comap (fun U : CompactGaugeField L m j => U.linkValue e)
          (borel Matrices.ComplexMatrix2.specialUnitary)
def TorusFieldSplitting (hL : 2 ≤ L) (hj : -(m : ℤ) < j) : Prop :=
  ∀ (S : Set (PeriodicLattice.Bond L m j)) (hS : S ⊆ forwardBonds L m j),
    (IsHomeomorph fun U : CompactGaugeField L m j =>
      (U.restrictTo S, U.restrictTo (forwardBonds L m j \ S))) ∧
    (∀ (V : LinkVariables S) (ω : CompactGaugeField L m j),
      ((CompactGaugeField.glue hL hj hS V ω).restrictTo S,
        (CompactGaugeField.glue hL hj hS V ω).restrictTo
          (forwardBonds L m j \ S)) =
      (V, ω.restrictTo (forwardBonds L m j \ S))) ∧
    (Continuous fun q : LinkVariables S × CompactGaugeField L m j =>
      CompactGaugeField.glue hL hj hS q.1 q.2) ∧
    (∀ V : LinkVariables S,
      PeriodicLattice.DependsOnlyOn (forwardBonds L m j \ S)
        (CompactGaugeField.glue hL hj hS V)) ∧
    ∀ (V : LinkVariables S) (ω : CompactGaugeField L m j),
      (CompactGaugeField.glue hL hj hS V ω).restrictTo S = V
end Torus
theorem meshSize_pos (p : Conventions.StandingParameters) :
    0 < PeriodicLattice.meshSize p.L ((p.K : ℕ) : ℤ) := by apply _root_.YangMills.Construction.Conventions.StandingParameters.latticeSpacing_pos <;> assumption
theorem two_le_L (p : Conventions.StandingParameters) : 2 ≤ p.L := by
  have := p.isAdmissible.2
  omega
theorem neg_m_lt_K (p : Conventions.StandingParameters) :
    -((p.m : ℕ) : ℤ) < ((p.K : ℕ) : ℤ) := by
  have h₁ := p.m.pos
  have h₂ := p.K.pos
  omega
def AllFacts : Prop :=
  ∀ p : Conventions.StandingParameters,
    FieldsAsProduct (PeriodicLattice.meshSize p.L ((p.K : ℕ) : ℤ)) ∧
    FieldBorelGenerated (PeriodicLattice.meshSize p.L ((p.K : ℕ) : ℤ)) ∧
    FieldSplitting (meshSize_pos p) ∧
    MotionGroupFacts (PeriodicLattice.meshSize p.L ((p.K : ℕ) : ℤ)) ∧
    PlaquetteFiniteness (PeriodicLattice.meshSize p.L ((p.K : ℕ) : ℤ)) ∧
    TorusCounts p.L p.m p.K ∧
    TorusFieldsAsProduct p.L p.m ((p.K : ℕ) : ℤ) ∧
    TorusFieldBorelGenerated p.L p.m ((p.K : ℕ) : ℤ) ∧
    TorusFieldSplitting (two_le_L p) (neg_m_lt_K p) ∧
    MirrorsAtHalfLevels (PeriodicLattice.meshSize p.L ((p.K : ℕ) : ℤ))
end InfiniteLattice.OneSpacing
end YangMills.Construction
end
