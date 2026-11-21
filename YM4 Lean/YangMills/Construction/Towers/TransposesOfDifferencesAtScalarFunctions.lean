import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicOperators (HasFiniteSupport)
namespace Tower
namespace FullSpace
section Differences
variable {a : ℝ} {R : Type} [CommRing R]
def forwardEdge (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) : PositiveEdge a :=
  ⟨InfiniteLattice.Link.forwardFrom x μ, μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
def vertexDifference (v : InfiniteLattice.LatticePoint a → R) : PositiveEdge a → R :=
  fun e => v e.1.terminal - v e.1.initial
def edgeDifference (f : PositiveEdge a → R) : InfiniteLattice.ElementaryPlaquette a → R :=
  fun p => f (forwardEdge p.corner p.lowAxis) +
      f (forwardEdge (p.corner + InfiniteLattice.axisStep a p.lowAxis) p.highAxis) -
    f (forwardEdge (p.corner + InfiniteLattice.axisStep a p.highAxis) p.lowAxis) -
      f (forwardEdge p.corner p.highAxis)
def IsVertexAdjoint (T : (PositiveEdge a → R) → InfiniteLattice.LatticePoint a → R) : Prop :=
  ∀ (f : PositiveEdge a → R) (v : InfiniteLattice.LatticePoint a → R), HasFiniteSupport v →
    ∑ᶠ x, T f x * v x = ∑ᶠ e, f e * vertexDifference v e
def IsFaceAdjoint (T : (InfiniteLattice.ElementaryPlaquette a → R) → PositiveEdge a → R) : Prop :=
  ∀ (g : InfiniteLattice.ElementaryPlaquette a → R) (f : PositiveEdge a → R), HasFiniteSupport f →
    ∑ᶠ e, T g e * f e = ∑ᶠ p, g p * edgeDifference f p
def vertexAdjoint : (PositiveEdge a → R) → InfiniteLattice.LatticePoint a → R :=
  Classical.epsilon IsVertexAdjoint
def faceAdjoint : (InfiniteLattice.ElementaryPlaquette a → R) → PositiveEdge a → R :=
  Classical.epsilon IsFaceAdjoint
def VertexAdjointProperties (R : Type) [CommRing R] (a : ℝ) : Prop :=
  (∀ v : InfiniteLattice.LatticePoint a → R, HasFiniteSupport v →
    HasFiniteSupport (vertexDifference v)) ∧
  (∃! T : (PositiveEdge a → R) → InfiniteLattice.LatticePoint a → R, IsVertexAdjoint T) ∧
  IsVertexAdjoint (vertexAdjoint (a := a) (R := R)) ∧
  IsLinearMap R (vertexAdjoint (a := a) (R := R)) ∧
  ∀ (f : PositiveEdge a → R) (x : InfiniteLattice.LatticePoint a),
    vertexAdjoint f x =
      ∑ μ : Fin 4, (f (forwardEdge (x - InfiniteLattice.axisStep a μ) μ) - f (forwardEdge x μ))
def FaceAdjointProperties (R : Type) [CommRing R] (a : ℝ) : Prop :=
  (∀ f : PositiveEdge a → R, HasFiniteSupport f →
    HasFiniteSupport (edgeDifference f)) ∧
  (∃! T : (InfiniteLattice.ElementaryPlaquette a → R) → PositiveEdge a → R, IsFaceAdjoint T) ∧
  IsFaceAdjoint (faceAdjoint (a := a) (R := R)) ∧
  IsLinearMap R (faceAdjoint (a := a) (R := R)) ∧
  ∀ (g : InfiniteLattice.ElementaryPlaquette a → R) (x : InfiniteLattice.LatticePoint a) (μ : Fin 4),
    faceAdjoint g (forwardEdge x μ) =
      (∑ ν : {ν : Fin 4 // μ < ν},
        (g ⟨x, μ, ν.1, ν.2⟩ - g ⟨x - InfiniteLattice.axisStep a ν.1, μ, ν.1, ν.2⟩)) -
      ∑ ν : {ν : Fin 4 // ν < μ},
        (g ⟨x, ν.1, μ, ν.2⟩ - g ⟨x - InfiniteLattice.axisStep a ν.1, ν.1, μ, ν.2⟩)
end Differences
def IsRealValued {σ : Type} (f : σ → ℂ) : Prop := ∀ s, (f s).im = 0
def RealValuedProperties (a : ℝ) : Prop :=
  (∀ v : InfiniteLattice.LatticePoint a → ℂ, IsRealValued v →
    IsRealValued (vertexDifference v)) ∧
  (∀ f : PositiveEdge a → ℂ, IsRealValued f → IsRealValued (edgeDifference f)) ∧
  (∀ f : PositiveEdge a → ℂ, IsRealValued f → IsRealValued (vertexAdjoint f)) ∧
  (∀ g : InfiniteLattice.ElementaryPlaquette a → ℂ, IsRealValued g →
    IsRealValued (faceAdjoint g)) ∧
  VertexAdjointProperties ℝ a ∧ FaceAdjointProperties ℝ a
end FullSpace
def ScalarDifferenceAdjoints : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    FullSpace.VertexAdjointProperties ℂ (meshAt L 0 0) ∧
    FullSpace.FaceAdjointProperties ℂ (meshAt L 0 0) ∧
    FullSpace.RealValuedProperties (meshAt L 0 0)
end Tower
end YangMills.Construction
end
