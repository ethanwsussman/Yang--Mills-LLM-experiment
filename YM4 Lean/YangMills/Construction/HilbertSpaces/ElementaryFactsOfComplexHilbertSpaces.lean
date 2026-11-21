import YangMills.Construction.HilbertSpaces.ComplexHilbertSpaceDefs
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.HilbertFacts
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert
def IsClosedSubmoduleSet {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (S : Set E) : Prop :=
  (∃ N : Submodule ℂ E, (N : Set E) = S) ∧ IsClosedSet S
def EqOfInnerSelfEq : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T T' : BddOp E), (∀ x : E, ⟪x, T x⟫_ℂ = ⟪x, T' x⟫_ℂ) → T = T'
def IsometryInnerAndClosedRange : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (V : E →ₗ[ℂ] F),
    IsIsometry V →
      (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧ IsClosedSet (linearRange V)
def UnitaryInverseExists : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (V : E →ₗ[ℂ] F),
    IsUnitaryMap V →
      ∃ W : F →ₗ[ℂ] E, W ∘ₗ V = LinearMap.id ∧ V ∘ₗ W = LinearMap.id ∧
        IsUnitaryMap W ∧ ∀ (z : F) (x : E), ⟪z, V x⟫_ℂ = ⟪W z, x⟫_ℂ
def PosOpCauchySchwarz : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : BddOp E), IsSymmetricOp T → OpGE T 0 →
      (∀ x y : E, ((‖⟪x, T y⟫_ℂ‖ ^ 2 : ℝ) : ℂ) ≤ ⟪x, T x⟫_ℂ * ⟪y, T y⟫_ℂ) ∧
        ∀ y : E, ⟪y, T y⟫_ℂ = 0 → T y = 0
def ClosedSubmoduleHilbert : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (N : Submodule ℂ E), IsClosedSet (N : Set E) →
      IsHilbert N ∧ ∀ x y : N, ⟪x, y⟫_ℂ = ⟪(x : E), (y : E)⟫_ℂ
def OrthSetClosed : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (S : Set E),
    IsClosedSubmoduleSet (orthSet S)
def KerClosed : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : BddOpBetween E F), IsClosedSubmoduleSet (linearKer (T : E →ₗ[ℂ] F))
def EqOfEqOnDense : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (S : Set E),
    IsDenseSet S → ∀ T T' : BddOpBetween E F, (∀ x ∈ S, T x = T' x) → T = T'
def ClosureImageDenseEqClosureRange : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (S : Set E),
    IsDenseSet S → ∀ T : BddOpBetween E F,
      seqClosureOf ((T : E → F) '' S) = seqClosureOf (linearRange (T : E →ₗ[ℂ] F))
def CommutingSymmetricProd : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (n : ℕ) (T : Fin n → BddOp E), 1 ≤ n →
    (∀ i, IsSymmetricOp (T i)) → (∀ i j, i ≠ j → Commute (T i) (T j)) →
      IsSymmetricOp (List.ofFn T).prod
def ElementaryFacts : Prop :=
  EqOfInnerSelfEq ∧
  (IsometryInnerAndClosedRange ∧ UnitaryInverseExists) ∧
  PosOpCauchySchwarz ∧
  (ClosedSubmoduleHilbert ∧ OrthSetClosed ∧ KerClosed) ∧
  (EqOfEqOnDense ∧ ClosureImageDenseEqClosureRange) ∧
  CommutingSymmetricProd
end YangMills.Construction.HilbertFacts
