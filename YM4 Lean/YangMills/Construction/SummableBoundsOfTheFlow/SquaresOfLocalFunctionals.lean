import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps
namespace LocalFunctionals
structure IsLocalFunctional (ρ : ℕ) (Λ : (LatticeBond → ℝ) → ℝ) : Prop where
  zero : Λ 0 = 0
  congr : ∀ f f' : LatticeBond → ℝ, (∀ u, BondOffsetInBox ρ u → f u = f' u) → Λ f = Λ f'
open Classical in
def bondIndicator {m : ℕ} (b : TorusBond m) : TorusBond m → ℝ := fun b' => if b' = b then 1 else 0
def gramEntry {N m : ℕ} [NeZero N] {κ : Type} [Fintype κ] (sc : TorusSite N → TorusSite m)
    (Λ : κ → (LatticeBond → ℝ) → ℝ) (b b' : TorusBond m) : ℝ :=
  ∑ y : TorusSite N, ∑ k, Λ k (fun u => bondIndicator b (bondFrom (sc y) u)) *
    Λ k (fun u => bondIndicator b' (bondFrom (sc y) u))
def GramEntriesTranslationInvariant : Prop :=
  ∀ (κ : Type) [Fintype κ] (ρ S : ℕ) (Λ : κ → (LatticeBond → ℝ) → ℝ), 1 ≤ S →
    (∀ k, IsLocalFunctional ρ (Λ k)) →
    ∃ (Γ : LatticeBond → LatticeBond → ℝ) (C : ℝ), 0 ≤ C ∧
      ∀ (N m : ℕ) [NeZero N] [NeZero m] (sc : TorusSite N → TorusSite m), (m : ℤ) = S * N →
        (∀ (y : TorusSite N) (v : Fin 4 → ℤ), sc (y + siteOfInt v) = sc y + siteOfInt fun i => (S : ℤ) * v i) →
        (∀ (y : TorusSite N) (r : ℕ) (e e' : LatticeBond), 2 * (r + ρ + 2 * S + 2) ≤ m →
          BondOffsetInBox r e → BondOffsetInBox r e' →
          gramEntry sc Λ (bondFrom (sc y) e) (bondFrom (sc y) e') = Γ e e') ∧
        (∀ b b' : TorusBond m, 2 * ρ < supDist b.1 b'.1 → gramEntry sc Λ b b' = 0) ∧
        ((∀ x : TorusSite m, ∃ (y : TorusSite N) (v : Fin 4 → ℤ), x = sc y + siteOfInt v ∧ ∀ i, |v i| ≤ (S : ℤ)) →
          2 * (4 * S + 3 * ρ + 4) ≤ m → ∀ b b' : TorusBond m, |gramEntry sc Λ b b'| ≤ C)
end LocalFunctionals
end YangMills.Construction
end
