import YangMills.Construction.HilbertSpace.FormsAndOperators
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace NNReal ComplexOrder
noncomputable section
namespace YangMills.Construction.OperatorTransport
open YangMills.Construction.HilbertSpaceBasics (UnboundedOp IsContraction)
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
def IsBoundedAdjoint (B' B : E →L[ℂ] E) : Prop := ∀ x y, ⟪x, B y⟫_ℂ = ⟪B' x, y⟫_ℂ
def IsSelfAdjointCLM (B : E →L[ℂ] E) : Prop := IsBoundedAdjoint B B
def IsProjectionCLM (B : E →L[ℂ] E) : Prop := IsSelfAdjointCLM B ∧ B * B = B
structure IsUnitaryMap (V : E →ₗ[ℂ] F) : Prop where
  bijective : Function.Bijective V
  inner_map_map : ∀ x y, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ
def IsUnitaryMap.toLinearEquiv {V : E →ₗ[ℂ] F} (hV : IsUnitaryMap V) : E ≃ₗ[ℂ] F :=
  LinearEquiv.ofBijective V hV.bijective
def IsUnitaryMap.inv {V : E →ₗ[ℂ] F} (hV : IsUnitaryMap V) : F →ₗ[ℂ] E :=
  hV.toLinearEquiv.symm.toLinearMap
def IsSelfAdjointUnbounded (A : UnboundedOp E) : Prop :=
  Dense (A.domain : Set E) ∧
    ∀ x z : E, (∃ h : x ∈ A.domain, A ⟨x, h⟩ = z) ↔
      ∀ y : A.domain, ⟪x, A y⟫_ℂ = ⟪z, (y : E)⟫_ℂ
def IsNonnegUnbounded (A : UnboundedOp E) : Prop := ∀ y : A.domain, 0 ≤ ⟪(y : E), A y⟫_ℂ
def conjOp {V : E →ₗ[ℂ] F} (hV : IsUnitaryMap V) (A : UnboundedOp E) : UnboundedOp F :=
  ⟨A.domain.map (hV.toLinearEquiv : E →ₗ[ℂ] F),
    V ∘ₗ A.toFun ∘ₗ (hV.toLinearEquiv.submoduleMap A.domain).symm.toLinearMap⟩
theorem conjOp_apply {V : E →ₗ[ℂ] F} (hV : IsUnitaryMap V) (A : UnboundedOp E) (y : A.domain) :
    conjOp hV A ⟨V y, Submodule.mem_map_of_mem y.2⟩ = V (A y) := by
  have h : (hV.toLinearEquiv.submoduleMap A.domain).symm ⟨V y, Submodule.mem_map_of_mem y.2⟩ = y :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  exact congrArg (fun p : A.domain => V (A.toFun p)) h
structure IsContractionSemigroup (T : ℝ≥0 → E →L[ℂ] E) : Prop where
  selfAdjoint : ∀ t, IsSelfAdjointCLM (T t)
  contraction : ∀ t, IsContraction (T t)
  map_zero : T 0 = 1
  map_add : ∀ t t', T t * T t' = T (t + t')
  continuous_apply : ∀ y, Continuous fun t => T t y
structure IsUnitaryGroup (U : ℝ → E →ₗ[ℂ] E) : Prop where
  unitary : ∀ s, IsUnitaryMap (U s)
  map_zero : U 0 = LinearMap.id
  map_add : ∀ s s', U s ∘ₗ U s' = U (s + s')
  continuous_apply : ∀ y, Continuous fun s => U s y
end YangMills.Construction.OperatorTransport
