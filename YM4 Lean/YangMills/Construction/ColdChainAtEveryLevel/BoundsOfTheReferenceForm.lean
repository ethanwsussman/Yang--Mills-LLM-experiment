import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def levelScale (F : BlockFrame) (j : ℕ) : ℝ := (1 / (F.blockSide : ℝ)) ^ (F.top - j)
def unitDeviation (g : UnitQuaternion) : ℝ := ‖(g : ℍ[ℝ]) - 1‖
def referenceInPatchFrame (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (j : ℕ) :
    F.GaugeField j :=
  gaugeTransform (fun x => (GaugeMap.frameChange S V z (baseSite x))⁻¹) (referenceFieldChain S V j)
def referenceBoundsStatement : Prop :=
  ∃ (C c : ℝ) (L1 : ℕ), 0 < C ∧ 0 < c ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide →
    L1 ≤ F.blockSide → IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m →
    ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
      (∀ j, j < F.top → ∀ z ∈ S, ∀ b ∈ innerBonds S j,
        baseSite b.1 ∈ (GaugeMap.patchDomain S z).image (GaugeMap.patchSite S z) →
        baseSite (b.1 + unitStep j b.2) ∈ (GaugeMap.patchDomain S z).image (GaugeMap.patchSite S z) →
        unitDeviation (referenceInPatchFrame S V z j b.1 b.2) ≤ C * s * levelScale F j) ∧
      (∀ j, j < F.top → ∀ p ∈ innerPlaquettes S j,
        plaquetteDefect (referenceFieldChain S V j) p ≤ C * s * levelScale F j ^ 2) ∧
      (∀ j, j + 1 < F.top → ∀ e ∈ innerBonds S (j + 1),
        unitDeviation (referenceDefect (referenceFieldChain S V) j e) ≤
          C * s * levelScale F (j + 1) ^ 3) ∧
      (∀ e ∈ innerBonds S F.top,
        unitDeviation (referenceDefect (referenceFieldChain S V) F.depth e) ≤ C * s) ∧
      (∀ j, j < F.top → ∀ e ∈ innerBonds S (j + 1), ∀ h ∈ centredCube F.blockSide,
        ∀ π : Equiv.Perm (Fin 4),
        unitDeviation (pathHolonomy (referenceFieldChain S V j) (refineSite e.1)
            (bondContour F.blockSide h π e.2) *
            (polarUnit (contourAverage (referenceFieldChain S V j) e))⁻¹) ≤
          C * s * levelScale F (j + 1) ^ 2) ∧
      ∀ j, j < F.top → ∀ e ∈ innerBonds S (j + 1),
        0 ≤ 1 - ‖contourAverage (referenceFieldChain S V j) e‖ ∧
          1 - ‖contourAverage (referenceFieldChain S V j) e‖ ≤
            C * s ^ 2 * levelScale F (j + 1) ^ 4
end BlockAverages
end YangMills.Construction
end
