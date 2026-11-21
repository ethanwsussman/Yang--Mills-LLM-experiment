import YangMills.Construction.ColdChainAtEveryLevel.GaugeFixedCellsOfAPatchForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open YangMills.Construction.PinnedGauge YangMills.Construction.LatticeFractionalIntegration YangMills.Construction.GaugeMap YangMills.Construction.PatchLatticeChart
def pinnedBondDifferenceStatement : Prop :=
  ∀ (C₃ n₀ : ℝ) (F : BlockFrame) (m : ℕ) (S : Finset F.Cell) (V : F.GaugeField F.top) (W : F.FieldChain)
    (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge) (γ : Lattice4 → UnitQuaternion) (z y y' : F.Cell) (B v : ℝ),
    0 ≤ C₃ → Odd F.blockSide → IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m → z ∈ S →
    y ∈ patchCells S z → y' ∈ patchCells S z →
    (∃ i, y' = y + unitStep F.top i) → X F.top = W F.top →
    HasPatchCellConditions (pinnedGaugeDataOfPatch S V z W kW X k) 9 (47 ^ 4) C₃ n₀ →
    (∀ f g : F.Site 0 → Fin 4 → ℍ[ℝ], (∀ b ∈ patchInnerBonds S z 0, f b.1 b.2 = g b.1 b.2) →
      ∀ c ∈ patchInnerBonds S z F.top, iteratedBlockAverage f F.top c.1 c.2 = iteratedBlockAverage g F.top c.1 c.2) →
    (∀ b ∈ patchInnerBonds S z F.top, ‖adjointAction (frameChange S V z (baseSite b.1))⁻¹
        (pureComponent ((topDefect W kW X k
        (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) -
        iteratedBlockAverage (framedPureDefect S V z W X
          (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0) F.top b.1 b.2‖ ≤ B) →
    (∀ c ∈ innerBonds (patchCells S z) F.top, distFromOne ((patchFrame S V z c.1)⁻¹ * W F.top c.1 c.2 *
      patchFrame S V z (c.1 + unitStep F.top c.2)) ≤ v) →
    ∃ T : ℝ, 0 ≤ T ∧ T ^ 4 ≤ C₃ * (16 * (∑ b ∈ bondsOf (patchDomain S z),
        ‖((framedLatticeField S V z (W 0) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4) *
        (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ) ∧
      ‖pureComponent ((pinnedTopCorrection S V z W kW X k γ y : UnitQuaternion) : ℍ[ℝ]) -
          pureComponent ((pinnedTopCorrection S V z W kW X k γ y' : UnitQuaternion) : ℍ[ℝ]) -
          (pinnedGaugeDataOfPatch S V z W kW X k).bondAverage y y'
            ((pinnedGaugeDataOfPatch S V z W kW X k).defectForm γ)‖ ≤
        B + (distFromOne (pinnedTopCorrection S V z W kW X k γ y) + 2 * v) *
          distFromOne (pinnedTopCorrection S V z W kW X k γ y') + T
end YangMills.Construction.BlockAverages
end
