import YangMills.Construction.HilbertSpaces.FormsOperatorsAndFamiliesInAHilbertSpace
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder InnerProductSpace
namespace YangMills.Construction.BoundedRepresentation
open FormsOperators
open EuclideanBorel (IsOrthoProjection)
variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def RieszAntilinear (c : ℝ) : Prop :=
  ∀ f : H →ₛₗ[starRingEnd ℂ] ℂ, (∀ v, ‖f v‖ ≤ c * ‖v‖) →
    ∃ w : H, (∀ v, f v = ⟪v, w⟫_ℂ) ∧ ‖w‖ ≤ c ∧
      ∀ w' : H, (∀ v, f v = ⟪v, w'⟫_ℂ) → w' = w
def BoundedSesquilinearRepr (c : ℝ) : Prop :=
  ∀ s : H → H → ℂ, IsSesquilinear s → (∀ u v, ‖s u v‖ ≤ c * ‖u‖ * ‖v‖) →
    ∃ T : H →L[ℂ] H, (∀ u v, s u v = ⟪u, T v⟫_ℂ) ∧ ‖T‖ ≤ c ∧
      ∀ T' : H →L[ℂ] H, (∀ u v, s u v = ⟪u, T' v⟫_ℂ) → T' = T
def ExtOfDiagonal : Prop :=
  ∀ T T' : H →L[ℂ] H, (∀ v, ⟪v, T v⟫_ℂ = ⟪v, T' v⟫_ℂ) → T = T'
def AdjBoundedOfBounded : Prop :=
  ∀ T : H →L[ℂ] H,
    (∃ hT : IsDenselyDefined (ofCLM T), (adj (ofCLM T) hT).domain = ⊤ ∧
      ∃ T' : H →L[ℂ] H, adj (ofCLM T) hT = ofCLM T') ∧
    (IsSelfAdj (ofCLM T) ↔ ∀ u v, ⟪u, T v⟫_ℂ = ⟪T u, v⟫_ℂ)
def EqTopOfOrthogonalTrivial : Prop :=
  ∀ K : Submodule ℂ H, IsSeqClosedSubmodule K →
    (∀ u : H, (∀ k ∈ K, ⟪u, k⟫_ℂ = 0) → u = 0) → K = ⊤
def OrthoProjectionRangeNorm : Prop :=
  (∀ P : H →L[ℂ] H, IsOrthoProjection P →
    Set.range P = {v | P v = v} ∧
      ∀ v, ((‖P v‖ ^ 2 : ℝ) : ℂ) = ⟪v, P v⟫_ℂ ∧ ⟪v, P v⟫_ℂ ≤ ((‖v‖ ^ 2 : ℝ) : ℂ)) ∧
  ∀ P P' : H →L[ℂ] H, IsOrthoProjection P → IsOrthoProjection P' →
    Set.range P = Set.range P' → P = P'
def Claim : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (c : ℝ), 0 ≤ c →
    RieszAntilinear H c ∧
    BoundedSesquilinearRepr H c ∧
    ExtOfDiagonal H ∧
    AdjBoundedOfBounded H ∧
    EqTopOfOrthogonalTrivial H ∧
    OrthoProjectionRangeNorm H
end YangMills.Construction.BoundedRepresentation
