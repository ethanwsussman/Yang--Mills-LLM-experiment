import YangMills.Construction.ColdChainAtEveryLevel.PinOfAFramingOnAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open LatticeFractionalIntegration PinnedGauge PatchLatticeChart GaugeMap
namespace BlockAverages
def pinnedCorrectionLocalityStatement : Prop :=
  ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (W : F.FieldChain)
    (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge), Odd F.blockSide → IsAdmissibleAmbient F → 1024 ≤ m →
    IsOrthantRegular S m →
    (∀ γ γ' : Lattice4 → UnitQuaternion, (∀ x ∈ patchDomain S z, γ x = γ' x) → ∀ y ∈ patchCells S z,
      pinnedTopCorrection S V z W kW X k γ y = pinnedTopCorrection S V z W kW X k γ' y) ∧
    ∀ R : Set ((pinnedGaugeDataOfPatch S V z W kW X k).region → UnitQuaternion),
      (∀ μ ∈ R, ∀ j, j < F.top → ∀ y ∈ sitesOfCells (patchCells S z) (j + 1),
        relativePathAverage
          (gaugeTransform (pinnedGaugeLevel W kW X k
            (siteGaugeOfLatticeGauge S V z ((pinnedGaugeDataOfPatch S V z W kW X k).extendByOne μ)) j) (X j))
          (W j) y ≠ 0) →
      ∀ y ∈ patchCells S z,
        ContinuousOn (fun μ : (pinnedGaugeDataOfPatch S V z W kW X k).region → UnitQuaternion =>
          ((pinnedTopCorrection S V z W kW X k ((pinnedGaugeDataOfPatch S V z W kW X k).extendByOne μ) y :
            UnitQuaternion) : ℍ[ℝ])) R
end BlockAverages
end YangMills.Construction
end
