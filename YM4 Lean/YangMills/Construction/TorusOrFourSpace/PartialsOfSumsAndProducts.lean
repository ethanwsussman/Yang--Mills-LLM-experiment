import YangMills.Construction.TorusOrFourSpace.FunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
namespace Coords
variable {p : ℕ+}
def HasSmoothPartials (G : Coords p → ℂ) : Prop :=
  ∀ ν, ContPartialsUpTo ν G
end Coords
namespace SumsProductsPartials
open Coords
def LeibnizRules : Prop :=
  ∀ (p : ℕ+) (F K : Coords p → ℂ), HasSmoothPartials F → HasSmoothPartials K →
    (∀ s t : ℂ, HasSmoothPartials (s • F + t • K)) ∧
    HasSmoothPartials (F * K) ∧
    (∀ j, HasSmoothPartials (partialAlong j F)) ∧
    (∀ α : CoordIndex p, HasSmoothPartials (iterPartial α F)) ∧
    (∀ (s t : ℂ) (α : CoordIndex p),
      iterPartial α (s • F + t • K) = s • iterPartial α F + t • iterPartial α K) ∧
    (∀ j : Fin (4 * (p : ℕ)),
      iterPartial (Pi.single j 1 : CoordIndex p) F = partialAlong j F) ∧
    (∀ j : Fin (4 * (p : ℕ)),
      partialAlong j (F * K) = partialAlong j F * K + F * partialAlong j K) ∧
    ∀ (ν : ℕ) (A B : ℝ) (x : Coords p),
      (∀ γ : CoordIndex p, γ.degree ≤ ν → ‖iterPartial γ F x‖ ≤ A) →
      (∀ γ : CoordIndex p, γ.degree ≤ ν → ‖iterPartial γ K x‖ ≤ B) →
      ∀ α : CoordIndex p, α.degree ≤ ν → ‖iterPartial α (F * K) x‖ ≤ 2 ^ ν * A * B
end SumsProductsPartials
end YangMills.Construction.PeriodicSpace
