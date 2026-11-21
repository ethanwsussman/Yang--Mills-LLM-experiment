import YangMills.Construction.Lattice.AxisBivectorBasis
import YangMills.Construction.LinearAlgebra.FreeCurvaturePropagator
import YangMills.Construction.LinearAlgebra.SignsOfCoordinatePlanesAndEntriesOfTwoVectors
import Mathlib
set_option autoImplicit false
open YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.Exterior
namespace PropagatorProperties
def AlgebraAndBoundsAt (y : Fin 4 → ℝ) : Prop :=
  freeCurvaturePropagator (-y) = freeCurvaturePropagator y ∧
  IsSelfAdjointMap (freeCurvaturePropagator y) ∧
  freeCurvaturePropagator y ∘ₗ freeCurvaturePropagator y =
    ((Real.pi ^ 4 * euclidNormVec y ^ 8)⁻¹) • LinearMap.id ∧
  bivectorTrace (freeCurvaturePropagator y) = 0 ∧
  hodge ∘ₗ freeCurvaturePropagator y ∘ₗ hodge = -freeCurvaturePropagator y ∧
  (∀ P Q : AxisPlane, |bivectorMatrixEntry (freeCurvaturePropagator y) P Q| ≤
    (Real.pi ^ 2 * euclidNormVec y ^ 4)⁻¹) ∧
  (∀ P Q : AxisPlane,
    euclidNormVec (gradientVec (fun z => bivectorMatrixEntry (freeCurvaturePropagator z) P Q) y) ≤
      curvatureKernelGradientSup.toReal / euclidNormVec y ^ 5) ∧
  (∀ α β : Bivector,
    inner ℝ ((Real.pi ^ 2 * euclidNormVec y ^ 4) • freeCurvaturePropagator y α)
        ((Real.pi ^ 2 * euclidNormVec y ^ 4) • freeCurvaturePropagator y β) = inner ℝ α β) ∧
  ((Real.pi ^ 2 * euclidNormVec y ^ 4) • freeCurvaturePropagator y) ∘ₗ
      ((Real.pi ^ 2 * euclidNormVec y ^ 4) • freeCurvaturePropagator y) = LinearMap.id ∧
  bivectorTrace (freeCurvaturePropagator y ∘ₗ freeCurvaturePropagator y) =
    6 * (Real.pi ^ 4 * euclidNormVec y ^ 8)⁻¹ ∧
  ∀ P Q : AxisPlane, P.IsDisjoint Q → bivectorMatrixEntry (freeCurvaturePropagator y) P Q = 0
end PropagatorProperties
open PropagatorProperties in
def FreeCurvaturePropagatorProperties : Prop :=
  (∀ y : Fin 4 → ℝ, y ≠ 0 → AlgebraAndBoundsAt y) ∧
  (∀ P Q : AxisPlane,
    ContDiffOn ℝ ∞ (fun y => bivectorMatrixEntry (freeCurvaturePropagator y) P Q) {y | y ≠ 0}) ∧
  (∀ (y : Fin 4 → ℝ) (s : ℝ), y ≠ 0 → 0 < s →
    freeCurvaturePropagator (s • y) = (s ^ 4)⁻¹ • freeCurvaturePropagator y) ∧
  (∀ v : Fin 4 → ℝ, v ≠ 0 →
    householderMatrix v = householder (unitDirection v) ∧
      ∀ P P' : AxisPlane,
        continuumCurvatureKernel P P' v = bivectorMatrixEntry (freeCurvaturePropagator v) P P') ∧
  curvatureKernelGradientSup =
    (⨆ (P : AxisPlane) (Q : AxisPlane) (v : Fin 4 → ℝ) (_ : euclidNormVec v = 1),
      ENNReal.ofReal
        (euclidNormVec (gradientVec (fun z => bivectorMatrixEntry (freeCurvaturePropagator z) P Q) v))) ∧
  curvatureKernelGradientSup ≠ ⊤
end YangMills.Construction.Exterior
end
