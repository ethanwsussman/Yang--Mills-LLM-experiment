import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
open YangMills.Construction.PeriodicOperators
namespace FullSpace
def scaledVertexCoboundaryKernel (L k j : ℕ) :
    KernelMatrix (Fin 3 × Vertex L k j) (Fin 3 × PositiveEdge (meshAt L k j)) :=
  (vertexCoordinate (Vertex L k j)).kernel (edgePauliCoordinates L k j) scaledVertexCoboundary
def scaledEdgeCoboundaryKernel (L k j : ℕ) :
    KernelMatrix (Fin 3 × PositiveEdge (meshAt L k j)) (Fin 3 × Face L k j) :=
  (edgePauliCoordinates L k j).kernel (vertexCoordinate (Face L k j)) scaledEdgeCoboundary
end FullSpace
namespace FreeOperators
def HasFiniteRangeEveryRate (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) : Prop :=
  IsPeriodicKernel I I' T ∧ IsFiniteRange I I' T ∧ ∀ δ : ℝ, 0 < δ → IsDecayRate I I' T δ
structure IsRangeThreeKernelOf (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ)
    (M : (I.Carrier → ℂ) → I'.Carrier → ℂ) : Prop where
  shift_invariant : IsShiftInvariant I I' T
  vanishes_outside : VanishesOutsideRadius I I' 3 T
  finite_range : HasFiniteRangeEveryRate I I' T
  finite_support : ∀ (f : I.Carrier → ℂ) (x' : I'.Carrier),
    (Function.support fun x => T x' x * f x).Finite
  applyKernel_eq : ∀ f : I.Carrier → ℂ, applyKernel T f = M f
structure CompositionsSummable {S₀ B₀ S B : Type} (p : RescaledOperators S₀ B₀ S B) : Prop where
  D_Dt : ∀ x' x, CompSummableAt p.D p.Dt x' x
  Dt_D : ∀ x' x, CompSummableAt p.Dt p.D x' x
  D_Rt : ∀ x' x, CompSummableAt p.D p.Rt x' x
  R_Dt : ∀ x' x, CompSummableAt p.R p.Dt x' x
  D_Rt_R_Dt : ∀ x' x, CompSummableAt (compKernel p.D p.Rt) (compKernel p.R p.Dt) x' x
  Qt_Q : ∀ x' x, CompSummableAt p.Qt p.Q x' x
  Rt_R : ∀ x' x, CompSummableAt p.Rt p.R x' x
structure FreeMapsRangeThree (L k : ℕ) : Prop where
  vertexCoboundary : ∀ j : ℕ, j ≤ k →
    IsRangeThreeKernelOf (colourVertices L k j) (colourEdges L k j)
      (FullSpace.scaledVertexCoboundaryKernel L k j)
      ((vertexCoordinate (FullSpace.Vertex L k j)).mapOnCoeffs (FullSpace.edgePauliCoordinates L k j)
        FullSpace.scaledVertexCoboundary)
  edgeCoboundary : ∀ j : ℕ, j ≤ k →
    IsRangeThreeKernelOf (colourEdges L k j) (colourFaces L k j)
      (FullSpace.scaledEdgeCoboundaryKernel L k j)
      ((FullSpace.edgePauliCoordinates L k j).mapOnCoeffs (vertexCoordinate (FullSpace.Face L k j))
        FullSpace.scaledEdgeCoboundary)
  edgeAverage : IsRangeThreeKernelOf (colourEdges L k 0) (colourEdges L k k)
    (FullSpace.rescaledOperators L k fun _ => 1).Q
    ((FullSpace.edgePauliCoordinates L k 0).mapOnCoeffs (FullSpace.edgePauliCoordinates L k k)
      fun A => finestMesh L k • FullSpace.iterCovariantDeriv L k (fun _ => 1) k A)
  vertexAverage : IsRangeThreeKernelOf (colourVertices L k 0) (colourVertices L k k)
    (FullSpace.rescaledOperators L k fun _ => 1).R
    ((vertexCoordinate (FullSpace.Vertex L k 0)).mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L k k))
      (FullSpace.iterAdjointCubeAverage L k (fun _ => 1) k))
structure FreeOperatorsFiniteRange (L k : ℕ) : Prop where
  compositions : CompositionsSummable (FullSpace.rescaledOperators L k fun _ => 1)
  vertexCoboundary_transpose : ∀ j : ℕ, j ≤ k →
    HasFiniteRangeEveryRate (colourEdges L k j) (colourVertices L k j)
      (kernelTranspose (colourVertices L k j) (colourEdges L k j)
        (FullSpace.scaledVertexCoboundaryKernel L k j))
  edgeCoboundary_transpose : ∀ j : ℕ, j ≤ k →
    HasFiniteRangeEveryRate (colourFaces L k j) (colourEdges L k j)
      (kernelTranspose (colourEdges L k j) (colourFaces L k j)
        (FullSpace.scaledEdgeCoboundaryKernel L k j))
  edgeAverage_transpose : HasFiniteRangeEveryRate (colourEdges L k k) (colourEdges L k 0)
    (FullSpace.rescaledOperators L k fun _ => 1).Qt
  vertexAverage_transpose : HasFiniteRangeEveryRate (colourVertices L k k) (colourVertices L k 0)
    (FullSpace.rescaledOperators L k fun _ => 1).Rt
  K : HasFiniteRangeEveryRate (colourEdges L k 0) (colourEdges L k 0)
    (FullSpace.rescaledOperators L k fun _ => 1).K
  Delta : HasFiniteRangeEveryRate (colourVertices L k 0) (colourVertices L k 0)
    (FullSpace.rescaledOperators L k fun _ => 1).Delta
  Xi : HasFiniteRangeEveryRate (colourEdges L k 0) (colourEdges L k 0)
    (FullSpace.rescaledOperators L k fun _ => 1).Xi
  Y : HasFiniteRangeEveryRate (colourVertices L k 0) (colourVertices L k 0)
    (FullSpace.rescaledOperators L k fun _ => 1).Y
  X : HasFiniteRangeEveryRate (colourEdges L k 0) (colourEdges L k 0)
    (FullSpace.rescaledOperators L k fun _ => 1).X
def FreeOperatorsArePeriodic : Prop :=
  (∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    (∀ (r : ℝ) (T : I'.Carrier → I.Carrier → ℂ), 0 ≤ r → IsShiftInvariant I I' T →
      VanishesOutsideRadius I I' r T → HasFiniteRangeEveryRate I I' T) ∧
    ∀ T : I'.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I' T → IsFiniteRange I I' T →
      ∀ δ : ℝ, 0 < δ → IsDecayRate I I' T δ) ∧
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    FreeMapsRangeThree L k ∧ FreeOperatorsFiniteRange L k
end FreeOperators
end Tower
end YangMills.Construction
end
