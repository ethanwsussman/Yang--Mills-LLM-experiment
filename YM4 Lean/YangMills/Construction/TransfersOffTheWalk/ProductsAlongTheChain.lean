import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace TransfersOffTheWalk
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion
variable {ℓ : StepParameters}
def SitesSeparated {n p : ℕ} (S : Fin p → Finset (TorusSite n)) (D : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∀ y ∈ S i, ∀ y' ∈ S j, D + 4 ≤ (supDist y y' : ℝ)
def SeparatedAlongTower (ℓ : StepParameters) (x D : ℕ → ℝ) {p : ℕ} :
    (s n : ℕ) → [NeZero n] → (Fin p → PlaquetteWeight (fineSide ℓ.side s n)) → Prop
  | 0, _, _, _ => True
  | s + 1, n, _, h =>
    (2 ^ 10 * (clusterRange (x s) : ℝ) ≤ D s ∧ 8 < D s ∧
      SitesSeparated (fun i => weightSupportSites ℓ.side (s + 1) n (h i)) (D s)) ∧
    SeparatedAlongTower ℓ x D s (n * ℓ.side) h
def separationError (ℓ : StepParameters) (Cp C₀ : ℝ) (D : ℕ → ℝ) {p : ℕ} :
    (s n : ℕ) → [NeZero n] → (Fin p → PlaquetteWeight (fineSide ℓ.side s n)) → ℝ
  | 0, _, _, _ => 0
  | s + 1, n, _, h =>
    separationError ℓ Cp C₀ D s (n * ℓ.side) h +
      Cp * (∑ i, ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ)) ^ 2 * Real.exp (-(ℓ.rt * D s / 2 ^ 8)) *
        ∏ i, (4 * C₀ * ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ))
def sideBelow (L : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => sideBelow L k (n * L)
instance instNeZeroSideBelow (L k n : ℕ) [NeZero L] [NeZero n] : NeZero (sideBelow L k n) := by
  induction k generalizing n with
  | zero => exact ‹NeZero n›
  | succ k ih => exact ih (n * L)
open Classical in
def ancestors (L : ℕ) : (k n : ℕ) → Finset (TorusSite (sideBelow L k n)) → Finset (TorusSite n)
  | 0, _, S => S
  | k + 1, n, S => (ancestors L k (n * L) S).image (parentBlock L)
end TransfersOffTheWalk
end YangMills.Construction
end
