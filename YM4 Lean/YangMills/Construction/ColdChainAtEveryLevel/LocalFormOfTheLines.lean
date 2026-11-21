import YangMills.Construction.ColdChainAtEveryLevel.NearlyFlatPairing
import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def patchLocalSites (S : Finset F.Cell) (z : F.Cell) : Set LatticeFractionalIntegration.Lattice4 :=
  {x | (∀ i, -(10 * GaugeMap.cellSideLength F) ≤ x i ∧ x i < 21 * GaugeMap.cellSideLength F) ∧
    GaugeMap.patchSite S z x ∈ sitesOfCells S 0}
def patchPairingLocalFormStatement : Prop :=
  ∃ B C c : ℝ, 1 ≤ B ∧ 0 < C ∧ 0 < c ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide →
    IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m →
    ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V → ∀ z ∈ S,
      ∃ (P0 : LatticeFractionalIntegration.Lattice4 × LatticeFractionalIntegration.Lattice4 → ℝ)
        (P1 : LatticeFractionalIntegration.Lattice4 × LatticeFractionalIntegration.Lattice4 → ℍ[ℝ]),
        FiniteDifferences.FiniteDiffBound
          (FlatPairing.scaledPairNorm (1 / (GaugeMap.cellSideLength F : ℝ))) 3
          (patchLocalSites S z ×ˢ patchLocalSites S z) B P0 ∧
        FiniteDifferences.FiniteDiffBound
          (FlatPairing.scaledPairNorm (1 / (GaugeMap.cellSideLength F : ℝ))) 3
          (patchLocalSites S z ×ˢ patchLocalSites S z) (C * s) P1 ∧
        (∀ a b, FlatPairing.pairingValue P0 P1 b a = star (FlatPairing.pairingValue P0 P1 a b)) ∧
        (∀ a ∈ patchLocalSites S z, 1 ≤ (FlatPairing.pairingValue P0 P1 a a).re) ∧
        (∀ a ∈ patchLocalSites S z, ∀ b ∈ patchLocalSites S z, FlatPairing.pairingValue P0 P1 a b ≠ 0 →
          polarUnit (quaternionPairing S (leadingFrame S V (GaugeMap.patchSite S z a))
              (leadingFrame S V (GaugeMap.patchSite S z b))) =
            GaugeMap.frameChange S V z (GaugeMap.patchSite S z a) *
              polarUnit (FlatPairing.pairingValue P0 P1 a b) *
              (GaugeMap.frameChange S V z (GaugeMap.patchSite S z b))⁻¹) ∧
        ∀ y ∈ S, ∀ a ∈ patchLocalSites S z, GaugeMap.patchSite S z a = cellCentre 0 y →
          GaugeMap.frameChange S V z (GaugeMap.patchSite S z a) = GaugeMap.cellTransport S V z y
end BlockAverages
end YangMills.Construction
end
