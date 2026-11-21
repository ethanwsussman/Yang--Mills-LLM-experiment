import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HullsInEveryVolume
def functionalBoundByLumpPrice : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (t : ℕ) (x : ℝ) (D : TorusLumps.TorusFunctional) (f : TorusLumps.LocalDensity)
    (Λ : TorusLumps.LabelSpace)
    (Dq : (n : ℕ) → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Φ : (n : ℕ) → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) → (Y → Λ.Ω) →
      Finset (TorusFields.TorusSite n) → ℝ)
    (φ : (n : ℕ) → TorusFields.TorusSite n → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) →
      (Y → Λ.Ω) → ℝ),
    ℓ.Admissible → 1 ≤ ℓ.E → 0 < x → 4 * ℓ.n₀ + 2 ^ 16 ≤ TorusLumps.clusterRange x →
    TorusLumps.ColdExpansion ℓ t x D f →
    TorusLumps.HullExpansion ℓ t x D f Λ Dq Φ φ → ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide ℓ n →
    ∀ W : TorusFields.TorusField n,
      D n W ≤ (2 : ℝ) ^ Fintype.card (TorusFields.TorusSite n) * (D n (TorusFields.trivialField n) *
        Real.exp (2 * ℓ.E * Fintype.card (TorusFields.TorusSite n) -
        x * TorusFields.actionAtLevel ℓ.coupling ℓ.side t
          (Finset.univ \ TorusLumps.thickening LumpContours.lumpRange (TorusLumps.torusHotSites ℓ W)) W -
        x * ℓ.κ * ℓ.threshold ^ 2 * ((TorusLumps.torusHotLumps ℓ W).card : ℝ)))
end YangMills.Construction.HullsInEveryVolume
end
