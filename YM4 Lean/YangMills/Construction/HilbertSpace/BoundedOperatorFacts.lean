import YangMills.Construction.HilbertSpace.FormsAndOperators
import YangMills.Construction.SpectralTheory.EuclideanBorelProjectionValuedMeasures
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate ComplexOrder InnerProductSpace
open YangMills.Construction.HilbertSpaceBasics (IsSesquilinear IsPosSemidef completionClass formNullSet)
open YangMills.Construction.EuclideanSpectral
noncomputable section
namespace YangMills.Construction.BoundedOperators
def FormPolarization : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (s : V → V → ℂ), IsSesquilinear s →
    (∀ u v : V, 4 * s u v = s (u + v) (u + v) - s (u - v) (u - v) -
      Complex.I * s (u + Complex.I • v) (u + Complex.I • v) +
      Complex.I * s (u - Complex.I • v) (u - Complex.I • v)) ∧
    ((∀ u, (s u u).im = 0) → ∀ u v, s v u = conj (s u v))
def PositiveFormCompletion : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (s : V → V → ℂ) (hs : IsPosSemidef s),
    (∀ u v : V, ((‖s u v‖ ^ 2 : ℝ) : ℂ) ≤ s u u * s v v) ∧
    (∃ N : Submodule ℂ V, (N : Set V) = formNullSet s) ∧
    Dense (range (completionClass s hs)) ∧
    (∀ u v : V, ⟪completionClass s hs u, completionClass s hs v⟫_ℂ = s u v) ∧
    ∀ u v : V, completionClass s hs u = completionClass s hs v ↔ u - v ∈ formNullSet s
def DiagonalDeterminesOp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (∀ T : H →L[ℂ] H, (∀ x, ⟪x, T x⟫_ℂ = 0) → T = 0) ∧
    (∀ T : H →L[ℂ] H, (∀ x, (⟪x, T x⟫_ℂ).im = 0) → IsSelfAdjointOp T) ∧
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (s : V → V → ℂ), IsSesquilinear s →
      ∀ L : V →ₗ[ℂ] H, (∀ u, ((‖L u‖ ^ 2 : ℝ) : ℂ) = s u u) →
        ∀ u v, ⟪L u, L v⟫_ℂ = s u v) ∧
    ∀ U : H →L[ℂ] H, IsUnitaryOp U → ∃ U' : H →L[ℂ] H, U' * U = 1 ∧ U * U' = 1 ∧ IsAdjointPair U U'
def DenseSubspaceExtension : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : Submodule ℂ H), Dense (D : Set H) →
    (∀ (c : ℝ) (T₀ : D →ₗ[ℂ] H), 0 ≤ c → (∀ x : D, ‖T₀ x‖ ≤ c * ‖(x : H)‖) →
      ∃ T : H →L[ℂ] H, (∀ x : D, T x = T₀ x) ∧ ‖T‖ ≤ c ∧
        ∀ T' : H →L[ℂ] H, (∀ x : D, T' x = T₀ x) → T' = T) ∧
    (∀ T T' : H →L[ℂ] H, (∀ x : D, T x = T' x) → T = T') ∧
    (∀ T T' : H →L[ℂ] H, (∀ y x : D, ⟪(y : H), T x⟫_ℂ = ⟪T' y, (x : H)⟫_ℂ) → IsAdjointPair T T') ∧
    ∀ T : H →L[ℂ] H, IsSelfAdjointOp T → (∀ x : D, 0 ≤ (⟪(x : H), T x⟫_ℂ).re) →
      OpGe T (scalarOp 0)
def AdjointNorms : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T T' : H →L[ℂ] H), IsAdjointPair T T' →
    IsAdjointPair T' T ∧ ‖T'‖ = ‖T‖ ∧ ‖T' * T‖ = ‖T‖ ^ 2 ∧
    (∀ S S' : H →L[ℂ] H, IsAdjointPair S S' →
      IsAdjointPair (T * S) (S' * T') ∧
      ∀ a b : ℂ, IsAdjointPair (a • T + b • S) (conj a • T' + conj b • S')) ∧
    (T * T' = T' * T → ∀ k : ℕ, ‖T ^ 2 ^ k‖ = ‖T‖ ^ 2 ^ k)
def UnitIntervalOpContracts : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), IsSelfAdjointOp T → OpGe T (scalarOp 0) →
    OpGe (scalarOp 1) T → IsContractionOp T
def OrthProjEqOfFixedSet : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P Q : H →L[ℂ] H), IsOrthProjection P → IsOrthProjection Q →
    fixedSet P = fixedSet Q → P = Q
def BoundedOperatorFacts : Prop :=
  FormPolarization ∧ PositiveFormCompletion ∧ DiagonalDeterminesOp ∧
    DenseSubspaceExtension ∧ AdjointNorms ∧ UnitIntervalOpContracts ∧
    OrthProjEqOfFixedSet
end YangMills.Construction.BoundedOperators
