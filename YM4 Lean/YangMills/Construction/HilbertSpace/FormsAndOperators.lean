import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction
namespace HilbertSpaceBasics
section Forms
variable {𝒱 : Type*}
def IsHermitianForm (b : 𝒱 → 𝒱 → ℂ) : Prop := ∀ x y, b y x = conj (b x y)
def formSeminorm (b : 𝒱 → 𝒱 → ℂ) (x : 𝒱) : ℝ := Real.sqrt (b x x).re
variable [AddCommGroup 𝒱] [Module ℂ 𝒱]
structure IsSesquilinear (b : 𝒱 → 𝒱 → ℂ) : Prop where
  add_left : ∀ x₁ x₂ y, b (x₁ + x₂) y = b x₁ y + b x₂ y
  smul_left : ∀ (z : ℂ) x y, b (z • x) y = conj z * b x y
  add_right : ∀ x y₁ y₂, b x (y₁ + y₂) = b x y₁ + b x y₂
  smul_right : ∀ (z : ℂ) x y, b x (z • y) = z * b x y
structure IsPosSemidef (b : 𝒱 → 𝒱 → ℂ) : Prop extends IsSesquilinear b where
  nonneg : ∀ x, 0 ≤ b x x
structure IsInnerProductForm (b : 𝒱 → 𝒱 → ℂ) : Prop extends IsPosSemidef b where
  definite : ∀ x, b x x = 0 → x = 0
theorem IsPosSemidef.isHermitianForm {b : 𝒱 → 𝒱 → ℂ} (h : IsPosSemidef b) :
    IsHermitianForm b := by
  intro x y
  have d₁ := Complex.le_def.mp (h.nonneg x)
  have d₂ := Complex.le_def.mp (h.nonneg y)
  have s₁ := Complex.le_def.mp (h.nonneg (x + y))
  have s₂ := Complex.le_def.mp (h.nonneg (x + Complex.I • y))
  rw [h.add_left, h.add_right, h.add_right] at s₁
  rw [h.add_left, h.add_right, h.add_right, h.smul_left, h.smul_left, h.smul_right,
    h.smul_right] at s₂
  simp only [Complex.zero_re, Complex.zero_im, Complex.add_im, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im, Complex.mul_re] at d₁ d₂ s₁ s₂
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith [s₂.2]
  · simp only [Complex.conj_im]
    linarith [s₁.2]
def formNullSet (b : 𝒱 → 𝒱 → ℂ) : Set 𝒱 := {x | b x x = 0}
def IsFormCauchy (b : 𝒱 → 𝒱 → ℂ) (x : ℕ → 𝒱) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r, ∀ s s', r ≤ s → r ≤ s' → formSeminorm b (x s - x s') ≤ ε
def FormEquivalent (b : 𝒱 → 𝒱 → ℂ) (x y : ℕ → 𝒱) : Prop :=
  Tendsto (fun r => formSeminorm b (x r - y r)) atTop (𝓝 0)
@[reducible] def toPreInnerCore {b : 𝒱 → 𝒱 → ℂ} (h : IsPosSemidef b) :
    PreInnerProductSpace.Core ℂ 𝒱 where
  inner := b
  conj_inner_symm x y := (h.isHermitianForm y x).symm
  re_inner_nonneg x := (Complex.le_def.mp (h.nonneg x)).1
  add_left := h.add_left
  smul_left x y r := h.smul_left r x y
def FormSpace (b : 𝒱 → 𝒱 → ℂ) (_h : IsPosSemidef b) : Type _ := 𝒱
instance (b : 𝒱 → 𝒱 → ℂ) (h : IsPosSemidef b) :
    SeminormedAddCommGroup (FormSpace b h) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ 𝒱 _ _ _ (toPreInnerCore h)
instance (b : 𝒱 → 𝒱 → ℂ) (h : IsPosSemidef b) :
    InnerProductSpace ℂ (FormSpace b h) :=
  InnerProductSpace.ofCore (toPreInnerCore h)
abbrev FormCompletion (b : 𝒱 → 𝒱 → ℂ) (h : IsPosSemidef b) : Type _ :=
  UniformSpace.Completion (FormSpace b h)
def completionClass (b : 𝒱 → 𝒱 → ℂ) (h : IsPosSemidef b) : 𝒱 →ₗ[ℂ] FormCompletion b h :=
  (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := FormSpace b h)).toLinearMap
def IsLimitClass (b : 𝒱 → 𝒱 → ℂ) (h : IsPosSemidef b) (ξ : FormCompletion b h)
    (x : ℕ → 𝒱) : Prop :=
  IsFormCauchy b x ∧ Tendsto (fun r => completionClass b h (x r)) atTop (𝓝 ξ)
end Forms
section Bounded
variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
def orthComplement (M : Set ℋ) : Set ℋ := {φ | ∀ ψ ∈ M, ⟪φ, ψ⟫_ℂ = 0}
variable [CompleteSpace ℋ]
def IsPositiveOp (A : ℋ →L[ℂ] ℋ) : Prop := IsSelfAdjoint A ∧ ∀ ψ, 0 ≤ ⟪ψ, A ψ⟫_ℂ
def IsGE (A B : ℋ →L[ℂ] ℋ) : Prop :=
  IsSelfAdjoint A ∧ IsSelfAdjoint B ∧ IsPositiveOp (A - B)
def IsContraction (A : ℋ →L[ℂ] ℋ) : Prop := ‖A‖ ≤ 1
def IsUnitaryOp (A : ℋ →L[ℂ] ℋ) : Prop := star A * A = 1 ∧ A * star A = 1
def IsOrthProjOp (A : ℋ →L[ℂ] ℋ) : Prop := A = star A ∧ A = A * A
def IsOrthProjOnto (Q : ℋ →L[ℂ] ℋ) (M : Set ℋ) : Prop :=
  IsOrthProjOp Q ∧ Set.range Q = M
def orthProjOnto (M : Set ℋ) : ℋ →L[ℂ] ℋ :=
  Classical.epsilon fun Q => IsOrthProjOnto Q M
def realPartOp (A : ℋ →L[ℂ] ℋ) : ℋ →L[ℂ] ℋ := (1 / 2 : ℂ) • (A + star A)
def imagPartOp (A : ℋ →L[ℂ] ℋ) : ℋ →L[ℂ] ℋ := (1 / (2 * Complex.I)) • (A - star A)
def TendstoStrongly {ι : Type*} (A : ι → ℋ →L[ℂ] ℋ) (l : Filter ι) (B : ℋ →L[ℂ] ℋ) : Prop :=
  ∀ ψ, Tendsto (fun t => A t ψ) l (𝓝 (B ψ))
def IsStronglyCont {X : Type*} [TopologicalSpace X] (A : X → ℋ →L[ℂ] ℋ) : Prop :=
  ∀ ψ, Continuous fun t => A t ψ
def IsOpSemigroup (T : ℝ≥0 → ℋ →L[ℂ] ℋ) : Prop :=
  T 0 = 1 ∧ ∀ t t', T t * T t' = T (t + t')
def IsUnitaryRep {G : Type*} [AddMonoid G] (U : G → ℋ →L[ℂ] ℋ) : Prop :=
  (∀ a, IsUnitaryOp (U a)) ∧ U 0 = 1 ∧ ∀ a a', U a * U a' = U (a + a')
abbrev UnboundedOp (ℋ : Type*) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type _ :=
  ℋ →ₗ.[ℂ] ℋ
def ofBounded (A : ℋ →L[ℂ] ℋ) : UnboundedOp ℋ :=
  ⟨⊤, (A : ℋ →ₗ[ℂ] ℋ).comp (Submodule.subtype ⊤)⟩
def opKernel (A : UnboundedOp ℋ) : Submodule ℂ ℋ :=
  (LinearMap.ker A.toFun).map A.domain.subtype
def opRange (A : UnboundedOp ℋ) : Set ℋ := Set.range A
def addConst (A : UnboundedOp ℋ) (z : ℂ) : UnboundedOp ℋ :=
  ⟨A.domain, A.toFun + z • A.domain.subtype⟩
def IsAdjointOf (B A : UnboundedOp ℋ) : Prop :=
  (∀ φ, φ ∈ B.domain ↔ ∃ η, ∀ ψ : A.domain, ⟪φ, A ψ⟫_ℂ = ⟪η, (ψ : ℋ)⟫_ℂ) ∧
    ∀ (φ : B.domain) (ψ : A.domain), ⟪(φ : ℋ), A ψ⟫_ℂ = ⟪B φ, (ψ : ℋ)⟫_ℂ
def IsSelfAdjointOp (A : UnboundedOp ℋ) : Prop :=
  Dense (A.domain : Set ℋ) ∧ IsAdjointOf A A
def IsNonnegOp (A : UnboundedOp ℋ) : Prop :=
  IsSelfAdjointOp A ∧ ∀ ψ : A.domain, 0 ≤ ⟪(ψ : ℋ), A ψ⟫_ℂ
def conjByUnitary (U : ℋ →L[ℂ] ℋ) (A : UnboundedOp ℋ) : UnboundedOp ℋ :=
  ⟨A.domain.comap (star U : ℋ →L[ℂ] ℋ).toLinearMap,
    (U : ℋ →ₗ[ℂ] ℋ).comp (A.toFun.comp
      (((star U : ℋ →L[ℂ] ℋ).toLinearMap.comp (Submodule.subtype _)).codRestrict A.domain
        fun ψ => ψ.2))⟩
end Bounded
end HilbertSpaceBasics
end YangMills.Construction
