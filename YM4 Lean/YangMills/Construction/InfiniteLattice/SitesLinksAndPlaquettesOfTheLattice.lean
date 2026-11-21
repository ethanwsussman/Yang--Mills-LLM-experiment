import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.CutoffMotionsAndPlaquetteSquares
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open GibbsAtFixedSpacing
namespace InfiniteLattice.LatticeGeometry
def LinksAreNeighborPairs (a : ℝ) : Prop :=
  (∀ x y : LatticePoint a,
    (TorusMetric.euclidNormVec ((y : AmbientSpace) - x) = a ↔
      ∃ ε ∈ ({1, -1} : Set ℝ), ∃ μ : Fin 4, (y : AmbientSpace) - x = ε • (Pi.single μ a : AmbientSpace))) ∧
  (∀ x y : LatticePoint a, ∀ ε ∈ ({1, -1} : Set ℝ), ∀ ε' ∈ ({1, -1} : Set ℝ), ∀ μ ν : Fin 4,
    (y : AmbientSpace) - x = ε • (Pi.single μ a : AmbientSpace) →
    (y : AmbientSpace) - x = ε' • (Pi.single ν a : AmbientSpace) → ε = ε' ∧ μ = ν) ∧
  (∀ x y : LatticePoint a,
    (∃ l : Link a, l.initial = x ∧ l.terminal = y) ↔
      TorusMetric.euclidNormVec ((y : AmbientSpace) - x) = a) ∧
  (∀ l : Link a, l.opposite.initial = l.terminal ∧ l.opposite.terminal = l.initial ∧
    l.opposite.opposite = l) ∧
  (∀ l : Link a, Xor (l ∈ positiveLinkSet a) (l.opposite ∈ positiveLinkSet a)) ∧
  (∀ L : Set (Link a), L.Finite → L ⊆ positiveLinkSet a → HasNoOppositePairs L)
def BoundedSetsAreFinite (a : ℝ) : Prop :=
  (∀ S : Set AmbientSpace, Bornology.IsBounded S →
    {x : LatticePoint a | (x : AmbientSpace) ∈ S}.Finite ∧ (positiveLinksWithin a S).Finite) ∧
  (positiveLinkSet a).Countable
def PlaquetteCornersAndEdges (a : ℝ) : Prop :=
  (∀ p : ElementaryPlaquette a,
    [p.corner, p.corner + axisStep a p.lowAxis, p.corner + axisStep a p.lowAxis + axisStep a p.highAxis,
      p.corner + axisStep a p.highAxis].Nodup) ∧
  (∀ p q : ElementaryPlaquette a, p.cornerSet = q.cornerSet → p = q) ∧
  (∀ p q : ElementaryPlaquette a, p.closedSquare = q.closedSquare → p = q) ∧
  (∀ p : ElementaryPlaquette a, p.edges.Nodup) ∧
  (∀ p : ElementaryPlaquette a, ∀ l ∈ p.edges, l.initial ∈ p.cornerSet ∧ l.terminal ∈ p.cornerSet) ∧
  (∀ (p : ElementaryPlaquette a) (y : LatticePoint a) (κ : Fin 4),
    Link.forwardFrom y κ ∈ p.edges ↔
      (κ = p.lowAxis ∧ (p.corner = y ∨ p.corner = y - axisStep a p.highAxis)) ∨
        (κ = p.highAxis ∧ (p.corner = y ∨ p.corner = y - axisStep a p.lowAxis))) ∧
  (∀ l ∈ positiveLinkSet a, {p : ElementaryPlaquette a | l ∈ p.edges}.ncard = 6)
def SymmetriesMapLinks (a : ℝ) : Prop :=
  ∀ (s : LatticeSymmetry a) (l : Link a),
    ((s.linkMap l).initial : AmbientSpace) = s.toFun l.initial ∧
      ((s.linkMap l).terminal : AmbientSpace) = s.toFun l.terminal ∧
      (s.linkMap l).opposite = s.linkMap l.opposite
def LatticeGeometryStatement : Prop :=
  ∀ a : ℝ, 0 < a →
    LinksAreNeighborPairs a ∧ BoundedSetsAreFinite a ∧
      PlaquetteCornersAndEdges a ∧ SymmetriesMapLinks a
end InfiniteLattice.LatticeGeometry
end YangMills.Construction
