import YangMills.Construction.ColdChainAtEveryLevel.TermsAndVariationsOfAFramedChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def distFromOne (g : UnitQuaternion) : ℝ := ‖(g : ℍ[ℝ]) - 1‖
structure GaugeChangeBounds (C₂ s : ℝ) (S : Finset F.Cell) (z z' y : F.Cell) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (k Γ Γ' : F.SiteGauge) (d : ℝ) : Prop where
  covariantDiff_le : ∀ j, j < F.top → ∑ b ∈ (patchInnerBonds S z j ∩ patchInnerBonds S z' j).filter
      (fun b => enclosingCell b.1 = y),
    distFromOne (gaugeChange Γ Γ' j b.1 * W j b.1 b.2 * (gaugeChange Γ Γ' j (b.1 + unitStep j b.2))⁻¹ *
      (W j b.1 b.2)⁻¹) ^ 4 ≤ (C₂ * d) ^ 4
  scaled_le : ∀ j, j < F.top → ((1 / (F.blockSide : ℝ)) ^ (F.top - j)) ^ 4 *
    ∑ x ∈ sitesOfCells {y} j, distFromOne (gaugeChange Γ Γ' j x) ^ 4 ≤ (C₂ * d) ^ 4
  curvature_le : ∑ p ∈ (patchPlaquettes S z ∩ patchPlaquettes S z').filter (fun p => enclosingCell p.1 = y),
    (distFromOne (gaugeChange Γ Γ' 0 p.1) * ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).im‖) ^ 2 ≤
      (C₂ * s * d) ^ 2
  misfit_le : ∑ j ∈ Finset.range F.top, Real.sqrt (∑ c ∈ (patchFitBonds S z j ∩ patchFitBonds S z' j).filter
      (fun c => enclosingCell c.1 = y),
    (distFromOne (gaugeChangeAbove W kW X k Γ Γ' j c.1) * distFromOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)) ^ 2)
      ≤ C₂ * s * d
def gaugeChangeBoundStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ C Cd : ℝ, 0 < C₁ → 0 < C → 0 < Cd →
      ∃ C₂ c : ℝ, 0 < C₂ ∧ 0 < c ∧ ∀ e₀ : ℝ, 0 < e₀ → e₀ ≤ c → ∃ σ : ℝ, 0 < σ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ σ →
          IsCold S F.top s V →
          (∀ y i, ‖v y i‖ ≤ s) →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V (rotatedField v V) U →
            ∀ (X : F.FieldChain) (k Γ Γ' : F.SiteGauge) (z z' y : F.Cell), X F.top = rotatedField v V → z ∈ S →
              z' ∈ S → y ∈ S →
              cellSupDist z z' ≤ 40 → baseSite y ∈ patchBaseSites S z → baseSite y ∈ patchBaseSites S z' →
              HasPinnedGaugeAt a C Cd e₀ S z (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ →
              HasPinnedGaugeAt a C Cd e₀ S z' (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ' →
              GaugeChangeBounds C₂ s S z z' y (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ Γ'
                (Real.sqrt (relativeEnergy a S z (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ +
                  relativeEnergy a S z' (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ'))
end YangMills.Construction.BlockAverages
end
