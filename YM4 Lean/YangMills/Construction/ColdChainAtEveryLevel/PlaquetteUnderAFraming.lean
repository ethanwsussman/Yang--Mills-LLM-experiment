import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def pinnedGaugePlaquetteBoundStatement : Prop :=
  ∀ a θ δ A : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < A →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ K₁ K : ℝ, 0 < K₁ → 0 < K → ∃ σ K₂ : ℝ, 0 < σ ∧ 0 < K₂ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F →
        1024 ≤ m → IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ σ → IsCold S F.top s V →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ A K₁ s S V V U →
            ∀ (X : F.FieldChain) (g Γ : F.SiteGauge) (z : F.Cell), X F.top = V → z ∈ S →
              IsPinnedGauge a K S z (chartChain (referenceFieldChain S V) U V)
                (chartGauge (referenceFieldChain S V) U) X g Γ →
              ∀ q ∈ innerPlaquettes S F.depth, enclosingCell q.1 = z →
                ‖((plaquetteHolonomy (gaugedChainFields X Γ F.depth) q : UnitQuaternion) : ℍ[ℝ]) -
                    ((plaquetteHolonomy (chartField (referenceFieldChain S V) U F.depth) q :
                      UnitQuaternion) : ℍ[ℝ])‖ ≤
                  K₂ * Real.sqrt (relativeEnergy a S z (chartChain (referenceFieldChain S V) U V)
                    (chartGauge (referenceFieldChain S V) U) X g Γ)
end YangMills.Construction.BlockAverages
end
