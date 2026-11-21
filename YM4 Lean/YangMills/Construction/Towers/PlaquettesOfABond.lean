import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FormsOnTowers
import YangMills.Construction.Towers.TheFourBondsOfAPlaquette
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FacesContainingEdge
def Periodic (L n k j : ℕ) : Prop :=
  (∀ (z : Tower.Vertex L n k j) (ρ : Fin 4) (p : Tower.Face L n k j),
    PeriodicLattice.Bond.forwardFrom z ρ ∈ Tower.faceEdges p →
    ∃ l : Fin 4, l ≠ ρ ∧ ({p.firstAxis, p.secondAxis} : Set (Fin 4)) = {ρ, l} ∧
      (p.origin = z ∨
        p.origin = z - PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) l)) ∧
  (∀ e : Tower.PositiveEdge L n k j,
    {p : Tower.Face L n k j | (e : Tower.Edge L n k j) ∈ Tower.faceEdges p}.encard ≤ 6) ∧
  (∀ F : Set (Tower.PositiveEdge L n k j), F.Finite →
    {p : Tower.Face L n k j | ∃ e ∈ F, (e : Tower.Edge L n k j) ∈ Tower.faceEdges p}.Finite)
def OnFullSpace (L k j : ℕ) : Prop :=
  (∀ (z : Tower.FullSpace.Vertex L k j) (ρ : Fin 4) (p : Tower.FullSpace.Face L k j),
    InfiniteLattice.Link.forwardFrom z ρ ∈ Tower.FullSpace.faceEdges p →
    ∃ l : Fin 4, l ≠ ρ ∧ ({p.lowAxis, p.highAxis} : Set (Fin 4)) = {ρ, l} ∧
      (p.corner = z ∨ p.corner = z - InfiniteLattice.axisStep (Tower.meshAt L k j) l)) ∧
  (∀ e : Tower.FullSpace.PositiveEdge (Tower.meshAt L k j),
    {p : Tower.FullSpace.Face L k j |
      (e : InfiniteLattice.Link (Tower.meshAt L k j)) ∈ Tower.FullSpace.faceEdges p}.encard ≤ 6) ∧
  (∀ F : Set (Tower.FullSpace.PositiveEdge (Tower.meshAt L k j)), F.Finite →
    {p : Tower.FullSpace.Face L k j | ∃ e ∈ F,
      (e : InfiniteLattice.Link (Tower.meshAt L k j)) ∈ Tower.FullSpace.faceEdges p}.Finite)
def Holds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    (∀ n : ℕ, 0 < n → Periodic L n k j) ∧ OnFullSpace L k j
end FacesContainingEdge
end Tower
end YangMills.Construction
end
