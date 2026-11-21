import YangMills.Construction.HilbertSpaces.FormsOperatorsAndFamiliesInAHilbertSpace
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.FormsOperators
section Forms
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def qNorm (q : V → V → ℂ) (v : V) : ℝ := Real.sqrt (q v v).re
def formRadical (q : V → V → ℂ) (hq : IsSesquilinear q) : Submodule ℂ V where
  carrier := {v | ∀ w, q w v = 0}
  add_mem' := fun {v₁ v₂} h₁ h₂ w => by
    rw [Set.mem_ofPred_eq] at h₁ h₂
    rw [hq.add_right, h₁, h₂, add_zero]
  zero_mem' := fun w => by
    have h := hq.smul_right 0 w 0
    rwa [zero_smul, zero_mul] at h
  smul_mem' := fun c v h w => by
    rw [Set.mem_ofPred_eq] at h
    rw [hq.smul_right, h, mul_zero]
def formOnQuotient (q : V → V → ℂ) (hq : IsSesquilinear q) (x y : V ⧸ formRadical q hq) : ℂ :=
  q (Quotient.out x) (Quotient.out y)
end Forms
def FormPolarization : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (q : V → V → ℂ), IsSesquilinear q → ∀ v w : V,
    q v w = (1 / 4 : ℂ) * ∑ α ∈ ({1, Complex.I, -1, -Complex.I} : Finset ℂ),
      conj α * q (v + α • w) (v + α • w) ∧
    ∑ α ∈ ({1, Complex.I, -1, -Complex.I} : Finset ℂ), q (v + α • w) (v + α • w) =
      4 * q v v + 4 * q w w
def PosFormQuotient : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (q : V → V → ℂ) (hh : IsHermitianForm q),
    IsPosSemidefForm q →
    (∀ v w : V, ‖q v w‖ ≤ qNorm q v * qNorm q w) ∧
    (∃ p : Seminorm ℂ V, ∀ v, p v = qNorm q v) ∧
    {v : V | q v v = 0} = {v : V | ∀ w, q w v = 0} ∧
    ((formRadical q hh.1 : Submodule ℂ V) : Set V) = {v : V | q v v = 0} ∧
    (∀ v w : V, formOnQuotient q hh.1 (Submodule.Quotient.mk v) (Submodule.Quotient.mk w) =
      q v w) ∧
    IsInnerProductForm (formOnQuotient q hh.1)
def DenseExtension : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (D : Submodule ℂ E) (c : ℝ) (T₀ : D →ₗ[ℂ] F),
    IsDenseSet (D : Set E) → 0 ≤ c → (∀ x : D, ‖T₀ x‖ ≤ c * ‖(x : E)‖) →
    ∃ T : E →L[ℂ] F,
      (∀ x : D, T x = T₀ x) ∧
      (∀ x, ‖T x‖ ≤ c * ‖x‖) ∧
      (∀ T' : E →L[ℂ] F, (∀ x : D, T' x = T₀ x) → T' = T) ∧
      ((∀ x : D, ‖T₀ x‖ = ‖(x : E)‖) → IsDenseSet (range T₀) →
        ∃ U : UnitaryMap E F, ∀ x, U x = T x)
def CLMEqOfEqOnDense : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (S : Set E) (T T' : E →L[ℂ] F),
    IsDenseSet S → (∀ x ∈ S, T x = T' x) → T = T'
def UnitaryMapInner : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (U : UnitaryMap E F),
    (∀ x y : E, ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    ∃ W : UnitaryMap F E, (∀ x, W (U x) = x) ∧ ∀ z, U (W z) = z
def UnitaryAdjEqInv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : UnitaryMap E E),
    ∃ hU : IsDenselyDefined (ofCLM (U.toContinuousLinearEquiv : E →L[ℂ] E)),
      (adj (ofCLM (U.toContinuousLinearEquiv : E →L[ℂ] E)) hU).domain = ⊤ ∧
      adj (ofCLM (U.toContinuousLinearEquiv : E →L[ℂ] E)) hU =
        ofCLM (U.symm.toContinuousLinearEquiv : E →L[ℂ] E)
def HilbertCompletionExistsUnique : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (q : V → V → ℂ), IsInnerProductForm q →
    (∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E)
      (j : V →ₗ[ℂ] E), IsHilbertCompletion q j) ∧
    ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      (j : V →ₗ[ℂ] E) (j' : V →ₗ[ℂ] F), IsHilbertCompletion q j → IsHilbertCompletion q j' →
      ∃! U : UnitaryMap E F, ∀ w, U (j w) = j' w
def FormsAndCompletions : Prop :=
  FormPolarization ∧ PosFormQuotient ∧ DenseExtension ∧
    CLMEqOfEqOnDense ∧ UnitaryMapInner ∧
    UnitaryAdjEqInv ∧ HilbertCompletionExistsUnique
end YangMills.Construction.FormsOperators
