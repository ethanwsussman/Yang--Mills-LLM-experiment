import YangMills.Construction.ColdChainAtEveryLevel.ChartOfAFramingOnAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PatchCurls
open BlockAverages LatticeFractionalIntegration PatchLatticeChart GaugeMap
variable {F : BlockFrame}
def gaugedGap (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (X W : F.GaugeField 0)
    (g : Lattice4 → UnitQuaternion) (a : Lattice4) (i : Fin 4) : UnitQuaternion :=
  latticeGaugeTransform g (latticeField S z X) a i * (framedLatticeField S V z W a i)⁻¹
def curlGapBoundStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell)
    (X W : F.GaugeField 0) (g : Lattice4 → UnitQuaternion), Odd F.blockSide → IsAdmissibleAmbient F → 1024 ≤ m →
    IsOrthantRegular S m →
    (∑ p ∈ orientedPlaquettesOf (patchDomain S z),
      ‖plaquetteCurl (fun a i => pureComponent ((gaugedGap S V z X W g a i : UnitQuaternion) : ℍ[ℝ]))
        p.1 p.2.1 p.2.2‖ ^ 2) ^ 2 ≤
      32 * (∑ q ∈ patchPlaquettes S z,
        ‖((plaquetteHolonomy (gaugeTransform (siteGaugeOfLatticeGauge S V z g) X) q : UnitQuaternion) : ℍ[ℝ]) -
          ((plaquetteHolonomy W q : UnitQuaternion) : ℍ[ℝ])‖ ^ 2) ^ 2 +
      C * (∑ b ∈ bondsOf (patchDomain S z), ‖((gaugedGap S V z X W g b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4) *
        (∑ b ∈ bondsOf (patchDomain S z), (‖((gaugedGap S V z X W g b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 +
          ‖((framedLatticeField S V z W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4))
end PatchCurls
end YangMills.Construction
end
