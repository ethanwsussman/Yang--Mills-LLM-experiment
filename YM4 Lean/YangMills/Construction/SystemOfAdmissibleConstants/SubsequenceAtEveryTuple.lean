import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
structure NormedFunctionClass (P : Type) [MetricSpace P] where
  supportedIn : Set P → Set (P → ℝ)
  SizeLE : (P → ℝ) → ℝ → Prop
  supportedIn_mono : ∀ {A B : Set P}, A ⊆ B → supportedIn A ⊆ supportedIn B
  sub_mem : ∀ {A : Set P} {f h : P → ℝ}, IsClosed A → f ∈ supportedIn A → h ∈ supportedIn A →
    f - h ∈ supportedIn A
  sizeLE_mono : ∀ {f : P → ℝ} {b b' : ℝ}, SizeLE f b → b ≤ b' → SizeLE f b'
  sizeLE_of_sub : ∀ {A : Set P} {f h : P → ℝ} {b ε : ℝ}, f ∈ supportedIn A → h ∈ supportedIn A →
    SizeLE f b → SizeLE (f - h) ε → SizeLE h (b + ε)
  exists_sizeLE : ∀ {A : Set P} {f : P → ℝ}, IsCompact A → f ∈ supportedIn A → ∃ b, SizeLE f b
  exists_countable_dense : ∀ {A : Set P}, IsCompact A → ∃ D : Set (P → ℝ), D.Countable ∧
    D ⊆ supportedIn A ∧ ∀ f ∈ supportedIn A, ∀ ε : ℝ, 0 < ε → ∃ h ∈ D, SizeLE (f - h) ε
structure NormedFunctionClass.IsMultiadditiveBounded {P : Type} [MetricSpace P]
    (C : NormedFunctionClass P) {n : ℕ} (A : Fin n → Set P) (Ψ : (Fin n → P → ℝ) → ℂ)
    (c : ℝ) : Prop where
  update_sub : ∀ u : Fin n → P → ℝ, (∀ i, u i ∈ C.supportedIn (A i)) → ∀ (i : Fin n) (v : P → ℝ),
    v ∈ C.supportedIn (A i) →
      Ψ u - Ψ (Function.update u i v) = Ψ (Function.update u i (u i - v))
  norm_le : ∀ u : Fin n → P → ℝ, (∀ i, u i ∈ C.supportedIn (A i)) → ∀ b : Fin n → ℝ,
    (∀ i, C.SizeLE (u i) (b i)) → ‖Ψ u‖ ≤ c * ∏ i, b i
def DiagonalSubsequenceExists : Prop :=
  ∀ (P : Type) [MetricSpace P] [ProperSpace P] [Nonempty P] (C : NormedFunctionClass P)
    (Tup : ∀ n : ℕ, Set (Fin n → P → ℝ)) (Φ : ℕ → ∀ n : ℕ, (Fin n → P → ℝ) → ℂ),
    (∀ (n : ℕ), ∀ X ∈ Tup n, (∀ i, IsCompact (tsupport (X i))) ∧
      (∀ i, X i ∈ C.supportedIn (tsupport (X i))) ∧
      Pairwise fun i k => Disjoint (tsupport (X i)) (tsupport (X k))) →
    (∀ n : ℕ, 2 ≤ n → ∀ A : Fin n → Set P, (∀ i, IsCompact (A i)) → ∀ d : ℝ, 0 < d →
      (∀ i k, i ≠ k → ∀ x ∈ A i, ∀ y ∈ A k, d ≤ dist x y) →
      ∃ (c : ℝ) (N : ℕ), 0 ≤ c ∧ ∀ j, N ≤ j → C.IsMultiadditiveBounded A (Φ j n) c) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n : ℕ, 2 ≤ n → ∀ X ∈ Tup n,
      ∃ z : ℂ, Tendsto (fun i => Φ (φ i) n X) atTop (𝓝 z)
end YangMills.Construction.AdmissibleConstants
end
