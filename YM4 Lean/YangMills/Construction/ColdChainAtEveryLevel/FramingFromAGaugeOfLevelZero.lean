import YangMills.Construction.ColdChainAtEveryLevel.TermsAndVariationsOfAFramedChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def pinnedGaugeLevel (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge)
    (γ : F.Site 0 → UnitQuaternion) : (j : ℕ) → F.Site j → UnitQuaternion
  | 0 => γ
  | j + 1 => fun y =>
    if j + 1 < F.top then
      kW (j + 1) y * balancingGauge (gaugeTransform (pinnedGaugeLevel W kW X k γ j) (X j)) (W j) y *
        pinnedGaugeLevel W kW X k γ j (refineSite y) * (k (j + 1) y)⁻¹
    else 1
def pinnedGaugeOfBase (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge)
    (γ : F.Site 0 → UnitQuaternion) : F.SiteGauge :=
  pinnedGaugeLevel W kW X k γ
def quarticDefectNorm (S : Finset F.Cell) (z : F.Cell) (W X : F.FieldChain) (Γ : F.SiteGauge) (j : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (∑ b ∈ patchInnerBonds S z j, normSubOne (relativeDefect W X Γ j b.1 b.2) ^ 4))
def topDefect (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ : F.SiteGauge)
    (y : F.Site F.top) (i : Fin 4) : UnitQuaternion :=
  framedUpperField W kW X k Γ F.depth y i * (W F.top y i)⁻¹
def framedPureDefect (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (W X : F.FieldChain)
    (Γ : F.SiteGauge) (j : ℕ) (x : F.Site j) (i : Fin 4) : ℍ[ℝ] :=
  adjointAction (GaugeMap.frameChange S V z (baseSite x))⁻¹
    (pureComponent ((relativeDefect W X Γ j x i : UnitQuaternion) : ℍ[ℝ]))
def iteratedBlockAverage (f : F.Site 0 → Fin 4 → ℍ[ℝ]) : (j : ℕ) → F.Site j → Fin 4 → ℍ[ℝ]
  | 0 => f
  | j + 1 => fun y i => (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
      iteratedBlockAverage f j (refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j i) i
end YangMills.Construction.BlockAverages
end
