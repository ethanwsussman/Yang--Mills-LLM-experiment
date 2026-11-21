import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OperatorPolynomials
open MvPolynomial
abbrev RealMvPolynomial (n : ℕ) [NeZero n] : Type := MvPolynomial (Fin n) ℝ
def PairwiseCommute {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : Fin n → H →L[ℂ] H) : Prop :=
  ∀ i j, Commute (A i) (A j)
def orderedMonomial {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : Fin n → H →L[ℂ] H) (α : Fin n → ℕ) : H →L[ℂ] H :=
  (List.ofFn fun i => A i ^ α i).prod
def evalOperators {n : ℕ} [NeZero n] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (p : RealMvPolynomial n) (A : Fin n → H →L[ℂ] H)
    (_hA : PairwiseCommute A) : H →L[ℂ] H :=
  ∑ α ∈ p.support, p.coeff α • orderedMonomial A α
def bernsteinApprox {n : ℕ} [NeZero n] (r : ℕ+) (p : RealMvPolynomial n) : RealMvPolynomial n :=
  ∑ k ∈ Fintype.piFinset (fun _ : Fin n => Finset.range ((r : ℕ) + 1)),
    C (eval (fun i => (k i : ℝ) / (r : ℕ)) p) *
      ∏ i, (C (((r : ℕ).choose (k i) : ℕ) : ℝ) * X i ^ k i * (1 - X i) ^ ((r : ℕ) - k i))
end YangMills.Construction.OperatorPolynomials
