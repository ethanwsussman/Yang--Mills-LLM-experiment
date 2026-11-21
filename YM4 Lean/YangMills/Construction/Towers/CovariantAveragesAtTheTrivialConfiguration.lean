import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace TrivialFieldAverages
section FiniteSide
def StepIdentities (L n k i : ℕ) : Prop :=
  (∀ B ∈ edgeFormSpace L n k i,
    complexSmoothingDeriv (trivialField L n k i) B = linearSmoothing L n k i B ∧
    contourLogDrift (trivialField L n k i) B = cubeContourAverage L n k i B ∧
    covariantSmoothingDeriv (trivialField L n k i) B = crossingSmoothing L n k i B) ∧
  ∀ f ∈ vertexFunctionSpace L n k i,
    adjointCubeAverage (trivialField L n k i) f = vertexSmoothing L n k i f
def IterateIdentities (L n k j : ℕ) : Prop :=
  (∀ B ∈ edgeFormSpace L n k 0,
    complexIterDeriv L n k j (trivialField L n k 0) B =
      linearSmoothingIter L n k j B ∧
    iterCovariantDeriv L n k (trivialField L n k 0) j B =
      crossingSmoothingIter L n k j B ∧
    iterContourLogDrift L n k (trivialField L n k 0) j B =
      cubeContourAverageIter L n k j B) ∧
  ∀ f ∈ vertexFunctionSpace L n k 0,
    iterAdjointCubeAverage L n k (trivialField L n k 0) j f = vertexSmoothingIter L n k j f
def kernelOrthogonal (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Set (Vertex L n k 0 → Matrices.ComplexMatrix2) :=
  {f | f ∈ vertexFunctionSpace L n k 0 ∧ ∀ g ∈ vertexFunctionSpace L n k 0,
    iterAdjointCubeAverage L n k U k g = 0 → traceFinsumPairing f g = 0}
def IsIterCubeAverage (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2)
    (T : (pairedFunctions (Vertex L n k 0)).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (Vertex L n k k)).complexSubmodule) :
    Prop :=
  ∀ f : (pairedFunctions (Vertex L n k 0)).complexSubmodule,
    (T f).1 = iterAdjointCubeAverage L n k U k f.1
def projectionMap (L n k : ℕ)
    (T : (pairedFunctions (Vertex L n k 0)).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (Vertex L n k k)).complexSubmodule)
    (f : (pairedFunctions (Vertex L n k 0)).complexSubmodule) :
    Vertex L n k 0 → Matrices.ComplexMatrix2 :=
  (L : ℂ) ^ (4 * k) • (PairedFunctionSpace.transposeMap (S := pairedFunctions (Vertex L n k 0))
    (S' := pairedFunctions (Vertex L n k k)) T (T f)).1
def IsOrthogonalProjection (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) : Prop :=
  ∃ T : (pairedFunctions (Vertex L n k 0)).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (Vertex L n k k)).complexSubmodule,
    IsIterCubeAverage L n k U T ∧
    ∀ f : (pairedFunctions (Vertex L n k 0)).complexSubmodule, f.1 ∈ vertexFunctionSpace L n k 0 →
      projectionMap L n k T f ∈ kernelOrthogonal L n k U ∧
      ∀ w ∈ kernelOrthogonal L n k U,
        traceFinsumPairing (fun x => f.1 x - projectionMap L n k T f x) w = 0
def GaugeDirectionIdentity (L n k j : ℕ) : Prop :=
  ∀ U ∈ smallIterateFields L n k,
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k 0),
      complexIterDeriv L n k j U (covDiff U f) =
        covDiff (PeriodicLattice.complexBlockFieldAtLevel j U) (restrictVertexFunction j f)
end FiniteSide
end TrivialFieldAverages
namespace FullSpace
namespace TrivialFieldAverages
def StepIdentities (L k i : ℕ) : Prop :=
  (∀ B ∈ edgeFormSpace (Tower.meshAt L k i),
    complexSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) B =
      linearSmoothing (a := Tower.meshAt L k (i + 1)) L B ∧
    contourLogDrift (L := L) (k := k) (j := i) (fun _ => 1) B =
      cubeContourAverage (a := Tower.meshAt L k (i + 1)) L B ∧
    covariantSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) B =
      crossingSmoothing (a := Tower.meshAt L k (i + 1)) L B) ∧
  ∀ f ∈ vertexFunctionSpace (Tower.meshAt L k i),
    adjointCubeAverage (L := L) (k := k) (j := i) (fun _ => 1) f =
      vertexSmoothing (a := Tower.meshAt L k (i + 1)) L f
def IterateIdentities (L k j : ℕ) : Prop :=
  (∀ B ∈ edgeFormSpace (Tower.meshAt L k 0),
    complexIterDeriv L k j (fun _ => 1) B = linearSmoothingIter L k j B ∧
    iterCovariantDeriv L k (fun _ => 1) j B = crossingSmoothingIter L k j B ∧
    iterContourLogDrift L k (fun _ => 1) j B = cubeContourAverageIter L k j B) ∧
  ∀ f ∈ vertexFunctionSpace (Tower.meshAt L k 0),
    iterAdjointCubeAverage L k (fun _ => 1) j f = vertexSmoothingIter L k j f
def GaugeDirectionIdentity (L k j : ℕ) : Prop :=
  ∀ U ∈ smallIterateFields L k,
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k 0),
      complexIterDeriv L k j U (covDiff U f) =
        covDiff (complexIter L k j U) (restrictVertexFunction (Tower.meshAt L k j) f)
end TrivialFieldAverages
end FullSpace
namespace TrivialFieldAverages
def AtTrivialField : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ n k : ℕ, 0 < n → 0 < k →
      (∀ i < k, StepIdentities L n k i) ∧
      (∀ j ≤ k, IterateIdentities L n k j) ∧
      EventuallyNearIdentity (fieldSpace L n k 0) (IsOrthogonalProjection L n k) ∧
      ∀ j ≤ k, GaugeDirectionIdentity L n k j) ∧
    ∀ k : ℕ, 0 < k →
      (∀ i < k, FullSpace.TrivialFieldAverages.StepIdentities L k i) ∧
      (∀ j ≤ k, FullSpace.TrivialFieldAverages.IterateIdentities L k j) ∧
      ∀ j ≤ k, FullSpace.TrivialFieldAverages.GaugeDirectionIdentity L k j
end TrivialFieldAverages
end Tower
end YangMills.Construction
end
