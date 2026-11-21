import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Calculus
def compositeCoordBound (k n : ℕ) (D N : ℝ) : ℝ :=
  (Fintype.card (OrderedFinpartition k) : ℝ) * ((n : ℝ) + 1) ^ k * (D + 1) ^ k * N
def CompositeDerivativesAtPoint : Prop :=
  (∀ (j : ℕ) (A B E : Type) [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
      [CompleteSpace B] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (L : A →L[ℝ] B) (f : B → E) (x : A),
      AnalyticAt ℝ f (L x) → ∀ v : Fin j → A,
        iteratedFDeriv ℝ j (f ∘ L) x v = iteratedFDeriv ℝ j f (L x) fun m => L (v m)) ∧
  (∀ (k j : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : (Fin k → ℝ) → E) (i : Fin k)
      (v : Fin j → Fin k → ℝ) (m : Fin j), AnalyticAt ℝ f 0 →
      (∀ (σ : Fin k → ℝ) (t : ℝ), f (Function.update σ i t) = f σ) → v m = Pi.single i 1 →
      iteratedFDeriv ℝ j f 0 v = 0) ∧
  (∀ (j : ℕ) (A B W : Type) [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A] [NormedAddCommGroup B]
      [NormedSpace ℝ B] [CompleteSpace B] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (G : B → W) (T : A → B) (x : A) (C D : ℝ), 0 ≤ C → 0 ≤ D → AnalyticAt ℝ T x → AnalyticAt ℝ G (T x) →
      (∀ p, p ≤ j → ‖iteratedFDeriv ℝ p G (T x)‖ ≤ C) →
      (∀ q, 1 ≤ q → q ≤ j → ‖iteratedFDeriv ℝ q T x‖ ≤ D) → ∀ v : Fin j → A, (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ j (G ∘ T) x v‖ ≤ (Fintype.card (OrderedFinpartition j) : ℝ) * C * (D + 1) ^ j) ∧
  ∀ (k n : ℕ) (G : (Fin n → ℝ) → ℝ) (T : (Fin k → ℝ) → Fin n → ℝ) (R : Fin k → Fin n → Prop) (D N : ℝ),
    1 ≤ k → 0 ≤ D → 0 ≤ N → AnalyticAt ℝ T 0 → T 0 = 0 → AnalyticAt ℝ G 0 →
    (∀ (j : ℕ) (v : Fin j → Fin k) (r : Fin n), 1 ≤ j → j ≤ k →
      |iteratedFDeriv ℝ j T 0 (fun m => Pi.single (v m) 1) r| ≤ D) →
    (∀ (j : ℕ) (v : Fin j → Fin k) (r : Fin n) (m : Fin j), ¬ R (v m) r →
      iteratedFDeriv ℝ j T 0 (fun m => Pi.single (v m) 1) r = 0) →
    (∀ (p : ℕ) (r : Fin p → Fin n), 1 ≤ p → p ≤ k → (∀ i, ∃ m, R i (r m)) →
      |iteratedFDeriv ℝ p G 0 (fun m => Pi.single (r m) 1)| ≤ N) →
    |iteratedFDeriv ℝ k (G ∘ T) 0 (fun i => Pi.single i 1)| ≤ compositeCoordBound k n D N
end Calculus
end YangMills.Construction
end
