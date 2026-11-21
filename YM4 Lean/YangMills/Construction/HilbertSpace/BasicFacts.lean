import YangMills.Construction.HilbertSpace.FormsAndOperators
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.HilbertSpaceFacts
open HilbertSpaceBasics
def Polarization : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ), IsSesquilinear β → ∀ x y : V,
    4 * β x y = ∑ k ∈ Finset.range 4,
      (-Complex.I) ^ k * β (x + Complex.I ^ k • y) (x + Complex.I ^ k • y)
def FormEqOfDiagEq : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (β β' : V → V → ℂ), IsSesquilinear β →
    IsSesquilinear β' → (∀ x, β x x = β' x x) → β = β'
def FormHermitianOfRealDiag : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ), IsSesquilinear β →
    (∀ x, (β x x).im = 0) → IsHermitianForm β
def PosSemidefFormHermitian : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ), IsPosSemidef β →
    IsHermitianForm β
def SeminormAndQuotient : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (b : V → V → ℂ), IsPosSemidef b →
    (∀ x y, ‖b x y‖ ≤ formSeminorm b x * formSeminorm b y) ∧
    (∀ x y, formSeminorm b (x + y) ≤ formSeminorm b x + formSeminorm b y) ∧
    (∀ (z : ℂ) x, formSeminorm b (z • x) = ‖z‖ * formSeminorm b x) ∧
    (∀ x y, formSeminorm b (x + y) ^ 2 + formSeminorm b (x - y) ^ 2 =
      2 * formSeminorm b x ^ 2 + 2 * formSeminorm b y ^ 2) ∧
    formNullSet b = {x | ∀ y, b y x = 0} ∧
    (∀ x y, ∀ x₀ ∈ formNullSet b, ∀ y₀ ∈ formNullSet b, b (x + x₀) (y + y₀) = b x y) ∧
    ∃ N : Submodule ℂ V, (N : Set V) = formNullSet b ∧
      ∃ q : V ⧸ N → V ⧸ N → ℂ, IsInnerProductForm q ∧ ∀ x y, q (N.mkQ x) (N.mkQ y) = b x y
def CompletionProperties : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (b : V → V → ℂ) (h : IsPosSemidef b),
    CompleteSpace (FormCompletion b h) ∧
    (∀ x y, ⟪completionClass b h x, completionClass b h y⟫_ℂ = b x y) ∧
    (∀ x y, completionClass b h x = completionClass b h y ↔ x - y ∈ formNullSet b) ∧
    Dense ((LinearMap.range (completionClass b h) : Submodule ℂ (FormCompletion b h)) :
      Set (FormCompletion b h)) ∧
    (∀ x, IsLimitClass b h (completionClass b h x) fun _ => x) ∧
    (∀ u, IsFormCauchy b u → ∃ ξ, IsLimitClass b h ξ u) ∧
    (∀ ξ, ∃ u, IsLimitClass b h ξ u) ∧
    ∀ (ξ ξ' : FormCompletion b h) (u u' : ℕ → V),
      IsLimitClass b h ξ u → IsLimitClass b h ξ' u' →
      (ξ = ξ' ↔ FormEquivalent b u u') ∧
      Tendsto (fun n => b (u n) (u' n)) atTop (𝓝 ⟪ξ, ξ'⟫_ℂ) ∧
      IsLimitClass b h (ξ + ξ') (fun n => u n + u' n) ∧
      ∀ z : ℂ, IsLimitClass b h (z • ξ) fun n => z • u n
def DenseExtension : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : Submodule ℂ H) (c : ℝ) (A₀ : D →ₗ[ℂ] H),
    Dense (D : Set H) → 0 ≤ c → (∀ ψ : D, ‖A₀ ψ‖ ≤ c * ‖(ψ : H)‖) →
    ∃ A : H →L[ℂ] H, (∀ ψ : D, A ψ = A₀ ψ) ∧ ‖A‖ ≤ c ∧
      ∀ A' : H →L[ℂ] H, (∀ ψ : D, A' ψ = A₀ ψ) → A' = A
def CompletionOperatorExtension : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (b : V → V → ℂ) (h : IsPosSemidef b)
    (c : ℝ) (T : V →ₗ[ℂ] V), 0 ≤ c → (∀ x, formSeminorm b (T x) ≤ c * formSeminorm b x) →
    (∀ x ∈ formNullSet b, T x ∈ formNullSet b) ∧
    ∃ A : FormCompletion b h →L[ℂ] FormCompletion b h,
      (∀ x, A (completionClass b h x) = completionClass b h (T x)) ∧ ‖A‖ ≤ c ∧
      ∀ A' : FormCompletion b h →L[ℂ] FormCompletion b h,
        (∀ x, A' (completionClass b h x) = completionClass b h (T x)) → A' = A
def OrthProjOntoClosed : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : Submodule ℂ H), IsClosed (M : Set H) →
    (∀ ψ : H, ∃! ψ₁ : H, ψ₁ ∈ M ∧ ψ - ψ₁ ∈ orthComplement (M : Set H)) ∧
    ∃ Q : H →L[ℂ] H, (∀ ψ, Q ψ ∈ M ∧ ψ - Q ψ ∈ orthComplement (M : Set H)) ∧
      IsOrthProjOnto Q (M : Set H) ∧
      (∀ Q' : H →L[ℂ] H, IsOrthProjOnto Q' (M : Set H) → Q' = Q) ∧
      Q = orthProjOnto (M : Set H)
def DenseOfOrthComplementTrivial : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (∀ M : Submodule ℂ H, IsClosed (M : Set H) → orthComplement (M : Set H) = {0} → M = ⊤) ∧
    ∀ D : Submodule ℂ H, orthComplement (D : Set H) = {0} → Dense (D : Set H)
def OrthProjRange : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Q : H →L[ℂ] H), IsOrthProjOp Q →
    IsClosed (Set.range Q) ∧ Set.range Q = {ψ | Q ψ = ψ} ∧
    ∀ ψ, ⟪ψ, Q ψ⟫_ℂ = ((‖Q ψ‖ ^ 2 : ℝ) : ℂ) ∧ ‖Q ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2
def BoundedFormRepresentation : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (β : H → H → ℂ) (c : ℝ), 0 ≤ c → IsSesquilinear β → (∀ φ ψ, ‖β φ ψ‖ ≤ c * ‖φ‖ * ‖ψ‖) →
    ∃ B : H →L[ℂ] H, (∀ φ ψ, β φ ψ = ⟪φ, B ψ⟫_ℂ) ∧ ‖B‖ ≤ c ∧
      ∀ B' : H →L[ℂ] H, (∀ φ ψ, β φ ψ = ⟪φ, B' ψ⟫_ℂ) → B' = B
def BoundedAdjointProperties : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H),
    (∀ φ ψ, ⟪φ, A ψ⟫_ℂ = ⟪star A φ, ψ⟫_ℂ) ∧
    ((∀ φ ψ, ⟪φ, A ψ⟫_ℂ = ⟪B φ, ψ⟫_ℂ) → B = star A) ∧
    ‖star A‖ = ‖A‖ ∧ star (star A) = A ∧ star (A * B) = star B * star A ∧
    star (A + B) = star A + star B ∧ ∀ z : ℂ, star (z • A) = conj z • star A
def BoundedOpDiagonal : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H),
    (∀ B : H →L[ℂ] H, (∀ ψ, ⟪ψ, A ψ⟫_ℂ = ⟪ψ, B ψ⟫_ℂ) → A = B) ∧
    ((∀ ψ, (⟪ψ, A ψ⟫_ℂ).im = 0) → IsSelfAdjoint A)
def PositiveOpCauchySchwarz : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H), IsPositiveOp A →
    (∀ φ ψ, ((‖⟪φ, A ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) ≤ ⟪φ, A φ⟫_ℂ * ⟪ψ, A ψ⟫_ℂ) ∧
    ∀ ψ, ⟪ψ, A ψ⟫_ℂ = 0 → A ψ = 0
def SelfAdjointNormBounds : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (c : ℝ), IsSelfAdjoint A → ‖A‖ ≤ c →
    IsGE A (((-c : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ∧ IsGE (((c : ℝ) : ℂ) • (1 : H →L[ℂ] H)) A
def StarMulMulPositive : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H),
    (∀ A : H →L[ℂ] H, IsPositiveOp A → IsPositiveOp (star B * A * B)) ∧
    IsPositiveOp (star B * B) ∧
    ∀ ψ, ((‖B ψ‖ ^ 2 : ℝ) : ℂ) = ⟪ψ, (star B * B) ψ⟫_ℂ
def PositiveEqOfSqEq : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H), IsPositiveOp A → IsPositiveOp B → A * B = B * A → A ^ 2 = B ^ 2 → A = B
def NormalOpKernelRange : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H), star B * B = B * star B →
    opKernel (ofBounded (star B)) = opKernel (ofBounded B) ∧
    (opKernel (ofBounded B) = ⊥ → Dense (HilbertSpaceBasics.opRange (ofBounded B)))
def DenseSubsetIdentities : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : Set H), Dense D →
    (∀ A B A' B' : H →L[ℂ] H, (∀ φ ∈ D, ∀ ψ ∈ D, ⟪A φ, B ψ⟫_ℂ = ⟪A' φ, B' ψ⟫_ℂ) →
      ∀ φ ψ, ⟪A φ, B ψ⟫_ℂ = ⟪A' φ, B' ψ⟫_ℂ) ∧
    (∀ A B : H →L[ℂ] H, (∀ ψ ∈ D, A ψ = B ψ) → A = B) ∧
    (∀ A B : H →L[ℂ] H, (∀ φ ∈ D, ∀ ψ ∈ D, ⟪φ, A ψ⟫_ℂ = ⟪φ, B ψ⟫_ℂ) → A = B) ∧
    (∀ A : H →L[ℂ] H, (∀ φ ∈ D, ∀ ψ ∈ D, ⟪φ, A ψ⟫_ℂ = ⟪A φ, ψ⟫_ℂ) → IsSelfAdjoint A) ∧
    ∀ A : H →L[ℂ] H, IsSelfAdjoint A → (∀ ψ ∈ D, 0 ≤ ⟪ψ, A ψ⟫_ℂ) → IsPositiveOp A
def DenseSubsetStrongConvergence : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : Set H) (ι : Type) (T : ι → H →L[ℂ] H) (l : Filter ι) (A : H →L[ℂ] H), Dense D →
    BddAbove (Set.range fun t => ‖T t‖) →
    (∀ ψ ∈ D, Tendsto (fun t => T t ψ) l (𝓝 (A ψ))) → TendstoStrongly T l A
def Facts : Prop :=
  Polarization ∧ FormEqOfDiagEq ∧ FormHermitianOfRealDiag ∧
    PosSemidefFormHermitian ∧ SeminormAndQuotient ∧
    CompletionProperties ∧ DenseExtension ∧
    CompletionOperatorExtension ∧ OrthProjOntoClosed ∧
    DenseOfOrthComplementTrivial ∧ OrthProjRange ∧
    BoundedFormRepresentation ∧ BoundedAdjointProperties ∧ BoundedOpDiagonal ∧
    PositiveOpCauchySchwarz ∧ SelfAdjointNormBounds ∧
    StarMulMulPositive ∧ PositiveEqOfSqEq ∧
    NormalOpKernelRange ∧ DenseSubsetIdentities ∧
    DenseSubsetStrongConvergence
end YangMills.Construction.HilbertSpaceFacts
