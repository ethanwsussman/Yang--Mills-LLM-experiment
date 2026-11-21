import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
abbrev BlockFrame.SiteGauge (F : BlockFrame) : Type := (j : ℕ) → F.Site j → UnitQuaternion
def gaugedContourAverage {j : ℕ} (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  (k c.1 : ℍ[ℝ]) * contourAverage X c *
    (((k (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ])
def gaugedBlockFit {j : ℕ} (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  ‖gaugedContourAverage X k c‖ - (gaugedContourAverage X k c * ((X' c.1 c.2)⁻¹ : UnitQuaternion)).re
def gaugedChainAction (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (k : F.SiteGauge) : ℝ :=
  wilsonAction S (X 0) + a * ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1),
    gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c
def gaugedChainLowerBoundStatement : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell), 0 ≤ a → 0 < F.blockSide →
    (∀ (X : F.FieldChain) (k : F.SiteGauge),
      minimalAction a S F.top (X F.top) ≤ gaugedChainAction a S X k) ∧
    ∀ X : F.FieldChain, gaugedChainAction a S X (fun _ _ => 1) = chainAction a S X
end YangMills.Construction.BlockAverages
end
