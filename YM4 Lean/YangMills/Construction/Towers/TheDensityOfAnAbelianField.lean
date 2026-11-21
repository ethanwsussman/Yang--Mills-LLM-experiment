import YangMills.Construction.HilbertSpaces.LimitsSeriesIntegralsAndTheLogarithmOfBoundedOperators
import YangMills.Construction.Towers.AbelianFields
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace AbelianFieldDensity
def traceAt {J : Type} (pos : J → InfiniteLattice.AmbientSpace)
    (T : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2) (y : InfiniteLattice.AmbientSpace) : ℂ :=
  ∑ᶠ k ∈ {k | pos k = y}, matrixEntry T k k
section VectorValued
variable {L p : ℕ}
open Classical in
def vecDelta (k : Fin p × FullSpace.Vertex L 0 0) : VectorL2 L p :=
  lp.single 2 k.2 (EuclideanSpace.single k.1 (1 : ℂ))
def vecCoord (f : VectorL2 L p) (k : Fin p × FullSpace.Vertex L 0 0) : ℂ := f k.2 k.1
def vecTraceAt (T : VectorL2 L p →L[ℂ] VectorL2 L p)
    (y : FullSpace.Vertex L 0 0) : ℂ :=
  ∑ᶠ k ∈ {k : Fin p × FullSpace.Vertex L 0 0 | k.2 = y}, vecCoord (T (vecDelta k)) k
end VectorValued
section AbelianField
variable {L : ℕ}
open Classical in
def formOfPositiveValues (g : PeriodicOperators.PosEdge L 0 0 → Matrices.ComplexMatrix2) :
    FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2 :=
  FullSpace.extendOddly fun e => if he : e.IsPositivelyOriented then g ⟨e, he⟩ else 0
def laplacianOp (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) :
    L2Field (FullSpace.Vertex L 0 0) →L[ℂ]
      L2Field (FullSpace.Vertex L 0 0) :=
  opOfMap (FullSpace.abelianGaugeLaplacian θ)
def massiveOp (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) :
    L2Field (PeriodicOperators.PosEdge L 0 0) →L[ℂ]
      L2Field (PeriodicOperators.PosEdge L 0 0) :=
  opOfMap fun g e => FullSpace.abelianMassiveHessian θ (formOfPositiveValues g) e.1
def DensityDefined (s : ℝ) (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) : Prop :=
  IsBoundedBelowBy (addScalar (massiveOp θ) s) (s / 2)
def densityAt (s : ℝ) (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (y : FullSpace.Vertex L 0 0) : ℂ :=
  traceAt (vertexPos L) (opLog (addScalar (laplacianOp θ) s)) y -
    (1 / 2 : ℂ) *
      traceAt (edgePos L) (opLog (addScalar (massiveOp θ) s)) y
end AbelianField
end AbelianFieldDensity
end Tower
end YangMills.Construction
end
