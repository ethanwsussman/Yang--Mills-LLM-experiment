import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAHolonomy
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
open Classical in
def HolonomySumDerivBounds : Prop :=
  ∃ B : ℕ → ℕ → ℝ, (∀ k n, 0 ≤ B k n) ∧
    ∀ (F : BlockFrame) (lev : ℕ) (ι : Type) (Q : Finset ι) (x : ι → F.Site lev) (l : ι → List PathStep)
      (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (A : ι → ℍ[ℝ] →L[ℝ] E) (e₀ : E)
      (G : F.GaugeField lev → E),
      (∀ W, G W = e₀ + ∑ q ∈ Q, A q ((pathHolonomy W (x q) (l q) : UnitQuaternion) : ℍ[ℝ])) →
      ∀ W : F.GaugeField lev, ContDiffThreeAlongBonds G W ∧
        ∀ (k : ℕ) (c : Fin k → F.Site lev × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X →
          ‖bondDeriv G W c X‖ ≤
            ∑ q ∈ Q.filter (fun q => ∀ i, c i ∈ pathPositiveBonds (x q) (l q)), ‖A q‖ * B k (l q).length
end YangMills.Construction.ColdStepAtMirrorFrames
end
