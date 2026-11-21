import YangMills.Construction.Towers.SecondDifferentialOfTheActionAsAKernel
import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.HessianDeterminants
open YangMills.Construction.Tower.HessianKernel (IsSymmBilinearOn finiteSupportComplexForms)
open YangMills.Construction.Tower.Massive (shiftedDetOn)
def IsSymmOperatorOn {ι : Type} (V : Submodule ℝ (ι → Matrices.ComplexMatrix2))
    (Q : (ι → Matrices.ComplexMatrix2) → (ι → Matrices.ComplexMatrix2) → ℂ)
    (T : (ι → Matrices.ComplexMatrix2) → ι → Matrices.ComplexMatrix2) : Prop :=
  (∃ T' : V →ₗ[ℝ] V, ∀ f : V, (T' f : ι → Matrices.ComplexMatrix2) = T f) ∧
    ∀ f g : V, Q (T f) g = Q f (T g)
def HessianSymmRealOnTorus (L n k j : ℕ) : Prop :=
  (∀ U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    IsSymmBilinearOn (complexEdgeForms L n k j : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (complexActionHessian U)) ∧
  ∀ U ∈ fieldsIn L n k j PeriodicLattice.compactGaugeGroup,
    ∀ B ∈ edgeFormSpace L n k j, ∀ B' ∈ edgeFormSpace L n k j,
      (complexActionHessian U B B').im = 0
def HessianSymmRealOnFullSpace (L k j : ℕ) : Prop :=
  (∀ U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
    IsSymmBilinearOn (finiteSupportComplexForms L k j)
      (FullSpace.complexActionHessian U)) ∧
  ∀ U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.compactGaugeGroup,
    ∀ B ∈ FullSpace.edgeFormSpace (meshAt L k j), FullSpace.HasFiniteEdgeSupport B →
      ∀ B' ∈ FullSpace.edgeFormSpace (meshAt L k j), FullSpace.HasFiniteEdgeSupport B' →
        (FullSpace.complexActionHessian U B B').im = 0
def PositiveDeterminantsOnTorus (L n : ℕ) (z : ℝ) : Prop :=
  (∀ U ∈ fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup,
    IsSymmOperatorOn (vertexFunctionSpace L n 0 0) traceFinsumPairing (gaugeLaplacian U) ∧
    IsSymmOperatorOn (edgeFormSpace L n 0 0) edgeFormPairing (massiveHessian U) ∧
    0 < shiftedDetOn (vertexFunctionSpace L n 0 0) (gaugeLaplacian U) z) ∧
  EventuallyNearIdentity (fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup) fun U' =>
    0 < shiftedDetOn (edgeFormSpace L n 0 0) (massiveHessian U') z
def HessianSymmAndDetsPositive : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ k j : ℕ, j ≤ k →
      (∀ n : ℕ, 0 < n → HessianSymmRealOnTorus L n k j) ∧ HessianSymmRealOnFullSpace L k j) ∧
    ∀ z : ℝ, 0 < z → ∀ n : ℕ, 0 < n → PositiveDeterminantsOnTorus L n z
end YangMills.Construction.Tower.HessianDeterminants
end
