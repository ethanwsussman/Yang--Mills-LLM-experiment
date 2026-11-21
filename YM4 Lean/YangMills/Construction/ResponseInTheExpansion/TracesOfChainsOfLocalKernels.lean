import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MatrixTraces
def TraceOfLocalKernelCycle : Prop :=
  ∀ (S X Q : Type) [Fintype S] [DecidableEq S] [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    (q : ℕ) (A : Fin (q + 1) → Finset S) (K : Fin (q + 1) → S → Matrix X X ℝ) (T : Matrix X X ℝ)
    (plane : X → Q) (Cc : S → S → Matrix Q Q ℝ) (w : S → X → ℝ) (near : S → X → Prop) (g : Fin (q + 1) → S → ℝ)
    (B δ c η G Am : ℝ) (σ : Equiv.Perm (Fin (q + 1))),
    1 ≤ q → 0 ≤ B → 0 ≤ δ → 0 ≤ c → 0 ≤ η → 0 ≤ G → 0 ≤ Am → (∀ z a, 1 ≤ w z a) →
    (∀ i, ((A i).card : ℝ) ≤ Am) →
    (∀ i, ∀ z ∈ A i, ∀ a b, K i z a b ≠ 0 → near z a ∧ near z b) →
    (∀ i, ∀ z ∈ A i, ∑ a, ∑ b, |K i z a b| * w z a * w z b ≤ B) →
    (∀ i j, i ≠ j → ∀ z ∈ A i, ∀ z' ∈ A j, ∀ a b, near z a → near z' b →
      |T a b - Cc z z' (plane a) (plane b)| ≤ δ * w z a * w z' b) →
    (∀ i j, i ≠ j → ∀ z ∈ A i, ∀ z' ∈ A j, ∀ Q₁ Q₂, |Cc z z' Q₁ Q₂| ≤ c) →
    (∀ i, ∀ z ∈ A i, ∀ Q₁ Q₂, |(∑ a, ∑ b, if plane a = Q₁ ∧ plane b = Q₂ then K i z a b else 0) -
      (if Q₁ = Q₂ then g i z else 0)| ≤ η) →
    (∀ i, ∀ z ∈ A i, |g i z| ≤ G) →
    |Matrix.trace (List.ofFn fun j : Fin (q + 1) => (∑ z ∈ A (σ j), K (σ j) z) * T).prod -
        ∑ z ∈ Fintype.piFinset A, (∏ i, g i (z i)) *
          Matrix.trace (List.ofFn fun j : Fin (q + 1) => Cc (z (σ j)) (z (σ (finRotate (q + 1) j)))).prod| ≤
      ((q : ℝ) + 1) * (δ * (c + δ) ^ q * (Am * B) ^ (q + 1)) +
        ((q : ℝ) + 1) * (c ^ (q + 1) * (Am * (Fintype.card Q : ℝ) ^ 2 * η) *
          (Am * (B + (Fintype.card Q : ℝ) * G)) ^ q)
end YangMills.Construction.MatrixTraces
end
