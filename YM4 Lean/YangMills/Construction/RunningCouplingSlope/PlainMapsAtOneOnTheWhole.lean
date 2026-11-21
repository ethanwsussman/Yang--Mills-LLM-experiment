import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.Tower.FullSpace
def MeanMapsAtTrivialField : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ m : ℕ, m ≤ k → FullLattice.meanIterate (L := L) (k := k) (fun _ => 1) m = fun _ => 1) ∧
    (∀ m : ℕ, m < k → ∀ c : FullSpace.Edge L k (m + 1), c.IsPositivelyOriented →
      FullLattice.meanRadius (L := L) (k := k) (j := m) (fun _ => 1) c = 1) ∧
    (∀ m : ℕ, m < k → ∀ B ∈ complexEdgeForms (meshAt L k m),
      FullLattice.meanCovariantStep (L := L) (k := k) (j := m) (fun _ => 1) B =
        crossingSmoothing (a := meshAt L k (m + 1)) L B) ∧
    (∀ m : ℕ, m ≤ k → ∀ B ∈ complexEdgeForms (meshAt L k 0),
      FullLattice.meanCovariant (L := L) (k := k) (fun _ => 1) m B =
        crossingSmoothingIter L k m B) ∧
    (∀ m : ℕ, m ≤ k → ∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Vertex L k 0),
      FullLattice.meanCubeAverage (L := L) (k := k) (fun _ => 1) m l =
        vertexSmoothingIter L k m l)
end YangMills.Construction.RunningCouplingSlope
end
