import YangMills.Construction.HilbertSpace.FormsAndOperators
import YangMills.Construction.JointSpectrum.OperatorPolynomials
import Mathlib
set_option autoImplicit false
open Filter Topology MvPolynomial YangMills.Construction.HilbertSpaceBasics YangMills.Construction.OperatorPolynomials
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.BernsteinPositivity
def IsDownwardClosed {n : ℕ} (𝒜 : Finset (Fin n →₀ ℕ)) : Prop :=
  ∀ α ∈ 𝒜, ∀ α' : Fin n →₀ ℕ, (∀ i, α' i ≤ α i) → α' ∈ 𝒜
def finsetMvSum {n : ℕ} [NeZero n] (𝒜 : Finset (Fin n →₀ ℕ)) (c : (Fin n →₀ ℕ) → ℝ) :
    RealMvPolynomial n :=
  ∑ α ∈ 𝒜, monomial α (c α)
def coordBox {n : ℕ} (γ γ' : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun i => Set.Icc (γ i) (γ' i)
def SpectrallyBetween {n : ℕ} {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] (A : Fin n → ℋ →L[ℂ] ℋ) (γ γ' : Fin n → ℝ) : Prop :=
  ∀ i, IsSelfAdjoint (A i) ∧ γ i < γ' i ∧ IsGE (A i) ((γ i : ℂ) • 1) ∧
    IsGE ((γ' i : ℂ) • 1) (A i)
def BernsteinPositivityStatement : Prop :=
  ∀ (n : ℕ) [NeZero n],
    (∀ (p : RealMvPolynomial n) (𝒜 : Finset (Fin n →₀ ℕ)) (c : (Fin n →₀ ℕ) → ℝ),
      p = finsetMvSum 𝒜 c → IsDownwardClosed 𝒜 →
        (∃ cr : ℕ+ → (Fin n →₀ ℕ) → ℝ,
          (∀ r, bernsteinApprox r p = finsetMvSum 𝒜 (cr r)) ∧
            ∀ α ∈ 𝒜, Tendsto (fun r => cr r α) atTop (𝓝 (c α))) ∧
        (∀ (ℋ : Type) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
          (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A) (γ γ' : Fin n → ℝ),
          SpectrallyBetween A γ γ' → (∀ y ∈ coordBox γ γ', 0 ≤ eval y p) →
            IsPositiveOp (evalOperators p A hA))) ∧
    (∀ (ℋ : Type) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
      (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A) (γ γ' : Fin n → ℝ),
      SpectrallyBetween A γ γ' → ∀ (p : RealMvPolynomial n) (ψ : ℋ),
        ‖⟪ψ, evalOperators p A hA ψ⟫_ℂ‖ ≤
          (⨆ y : coordBox γ γ', |eval (y : Fin n → ℝ) p|) * ‖ψ‖ ^ 2) ∧
    (∀ (ℋ : Type) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
      (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A),
      IsLinearMap ℝ (fun p : RealMvPolynomial n => evalOperators p A hA) ∧
        (∀ p q : RealMvPolynomial n,
          evalOperators (p * q) A hA = evalOperators p A hA * evalOperators q A hA) ∧
        ((∀ i, IsSelfAdjoint (A i)) →
          ∀ p : RealMvPolynomial n, IsSelfAdjoint (evalOperators p A hA)))
end YangMills.Construction.BernsteinPositivity
