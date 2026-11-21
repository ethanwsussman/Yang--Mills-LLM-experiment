import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TheFourBondsOfAPlaquette
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FaceEdgeFinsets
section Periodic
variable {L n k j : ℕ}
def baseFace (L n k j : ℕ) : Face L n k j := ⟨0, 0, 1, by decide⟩
def facesMeeting (S : Set (Edge L n k j)) : Set (Face L n k j) :=
  {p | ∃ e ∈ S, e ∈ faceEdges p}
def facesMeetingWithBase (S : Set (Edge L n k j)) : Set (Face L n k j) :=
  facesMeeting S ∪ {baseFace L n k j}
def edgesOfFacesMeetingWithBase (S : Set (Edge L n k j)) : Set (Edge L n k j) :=
  {e | e ∈ faceEdges (baseFace L n k j) ∨ ∃ p ∈ facesMeeting S, e ∈ faceEdges p}
def HoldsOnTorus (L n k j : ℕ) : Prop :=
  ((0 : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) ∧
    ∀ p : Face L n k j, ∀ e ∈ faceEdges p, e.IsPositivelyOriented) ∧
  (∀ S : Set (Edge L n k j), S.Finite → (∀ e ∈ S, e.IsPositivelyOriented) →
    (facesMeeting S).Finite ∧ (S = ∅ → facesMeeting S = ∅) ∧
    (facesMeetingWithBase S).Finite ∧ (facesMeetingWithBase S).Nonempty) ∧
  (∀ S : Set (Edge L n k j), S.Finite → (∀ e ∈ S, e.IsPositivelyOriented) →
    (edgesOfFacesMeetingWithBase S).Finite ∧ (edgesOfFacesMeetingWithBase S).Nonempty ∧
    ∀ e ∈ edgesOfFacesMeetingWithBase S, e.IsPositivelyOriented) ∧
  ((univ : Set (Face L n k j)).Finite ∧ baseFace L n k j ∈ (univ : Set (Face L n k j)))
end Periodic
namespace Unbounded
section Infinite
variable {L k j : ℕ}
def baseFace (L k j : ℕ) : Tower.FullSpace.Face L k j := ⟨0, 0, 1, by decide⟩
def facesMeeting (S : Set (Tower.FullSpace.Edge L k j)) :
    Set (Tower.FullSpace.Face L k j) :=
  {p | ∃ e ∈ S, e ∈ Tower.FullSpace.faceEdges p}
def facesMeetingWithBase (S : Set (Tower.FullSpace.Edge L k j)) :
    Set (Tower.FullSpace.Face L k j) :=
  facesMeeting S ∪ {baseFace L k j}
def edgesOfFacesMeetingWithBase (S : Set (Tower.FullSpace.Edge L k j)) :
    Set (Tower.FullSpace.Edge L k j) :=
  {e | e ∈ Tower.FullSpace.faceEdges (baseFace L k j) ∨
    ∃ p ∈ facesMeeting S, e ∈ Tower.FullSpace.faceEdges p}
def HoldsOnFullSpace (L k j : ℕ) : Prop :=
  ((0 : InfiniteLattice.AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k j) ∧
    ∀ p : Tower.FullSpace.Face L k j,
      ∀ e ∈ Tower.FullSpace.faceEdges p, e.IsPositivelyOriented) ∧
  (∀ S : Set (Tower.FullSpace.Edge L k j), S.Finite → (∀ e ∈ S, e.IsPositivelyOriented) →
    (facesMeeting S).Finite ∧ (S = ∅ → facesMeeting S = ∅) ∧
    (facesMeetingWithBase S).Finite ∧ (facesMeetingWithBase S).Nonempty) ∧
  (∀ S : Set (Tower.FullSpace.Edge L k j), S.Finite → (∀ e ∈ S, e.IsPositivelyOriented) →
    (edgesOfFacesMeetingWithBase S).Finite ∧ (edgesOfFacesMeetingWithBase S).Nonempty ∧
    ∀ e ∈ edgesOfFacesMeetingWithBase S, e.IsPositivelyOriented)
end Infinite
end Unbounded
def FacesAndEdgesFinite : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    (∀ n : ℕ, 0 < n → HoldsOnTorus L n k j) ∧ Unbounded.HoldsOnFullSpace L k j
end FaceEdgeFinsets
end Tower
end YangMills.Construction
end
