import YangMills.Construction.GrowingTori.DefinitionsForSequencesOfGrowingTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GrowingTori.Ambient
variable {𝕜 : Type*} [RCLike 𝕜]
def periodizeTuple {L : ℕ} {ℓ : ℝ} (hℓ : ℓ ∈ PeriodicLattice.torusSides L) {n : ℕ}
    (X : Fin n → (Fin 4 → ℝ) → 𝕜) : Fin n → (torus ℓ hℓ : Ambient L).Point → 𝕜 :=
  fun i => TestFunctions.periodize ℓ (X i)
end YangMills.Construction.GrowingTori.Ambient
end
