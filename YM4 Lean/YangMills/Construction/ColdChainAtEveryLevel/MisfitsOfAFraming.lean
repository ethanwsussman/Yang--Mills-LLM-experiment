import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFraming
import YangMills.Construction.ColdChainAtEveryLevel.FramingFromAGaugeOfLevelZero
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
theorem pinnedGaugeOfBase_zero (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge)
    (g : F.Site 0 → UnitQuaternion) :
    pinnedGaugeOfBase W kW X k g 0 = g := rfl
theorem pinnedGaugeOfBase_top (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge)
    (g : F.Site 0 → UnitQuaternion) (y : F.Site F.top) : pinnedGaugeOfBase W kW X k g F.top y = 1 := by
  show pinnedGaugeLevel W kW X k g (F.depth + 1) y = 1
  simp [pinnedGaugeLevel]
theorem pinnedGaugeOfBase_succ (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge)
    (g : F.Site 0 → UnitQuaternion) {j : ℕ} (hj : j + 1 < F.top) (y : F.Site (j + 1)) :
    pinnedGaugeOfBase W kW X k g (j + 1) y =
      kW (j + 1) y * balancingGauge (gaugedChainFields X (pinnedGaugeOfBase W kW X k g) j) (W j) y *
        pinnedGaugeOfBase W kW X k g j (refineSite y) * (k (j + 1) y)⁻¹ := by
  show pinnedGaugeLevel W kW X k g (j + 1) y = _
  simp only [pinnedGaugeLevel, if_pos hj]
  rfl
theorem gaugedLink_pinnedGaugeOfBase (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge)
    (g : F.Site 0 → UnitQuaternion) {j : ℕ} (hj : j + 1 < F.top) (y : F.Site (j + 1)) :
    gaugedLink k (pinnedGaugeOfBase W kW X k g) j y =
      balancedLinkAgainst W kW (gaugedChainFields X (pinnedGaugeOfBase W kW X k g)) j y := by
  unfold gaugedLink balancedLinkAgainst
  rw [pinnedGaugeOfBase_succ W kW X k g hj y]
  group
def rotationAboveLevel (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k G : F.SiteGauge) (j : ℕ)
    (y : F.Site (j + 1)) : UnitQuaternion :=
  balancedRotation W kW X k G j y * G (j + 1) y
theorem balancedLinkAgainst_eq_rotationAboveLevel (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain)
    (k G : F.SiteGauge) (j : ℕ) (y : F.Site (j + 1)) :
    balancedLinkAgainst W kW (gaugedChainFields X G) j y =
      rotationAboveLevel W kW X k G j y * k (j + 1) y * (G j (refineSite y))⁻¹ := by
  unfold rotationAboveLevel balancedRotation gaugedLink
  group
theorem framedUpperField_eq_gaugeTransform (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain)
    (k G : F.SiteGauge) {j : ℕ} (hj : j < F.top)
    (htop : ∀ y, G F.top y = 1)
    (hbal : ∀ i, i + 1 < F.top → ∀ y,
      gaugedLink k G i y = balancedLinkAgainst W kW (gaugedChainFields X G) i y) :
    framedUpperField W kW X k G j = gaugeTransform (rotationAboveLevel W kW X k G j) (X (j + 1)) := by
  by_cases h : j = F.depth
  · subst h
    funext y i
    have e : ∀ y' : F.Site F.top, rotationAboveLevel W kW X k G F.depth y' = topCorrection W kW X k G y' := by
      intro y'
      have : G (F.depth + 1) y' = 1 := htop y'
      unfold rotationAboveLevel balancedRotation topCorrection
      rw [this, mul_one]
    simp only [framedUpperField, dite_true, gaugeTransform, e]
  · have hj' : j + 1 < F.top := by
      have : F.top = F.depth + 1 := rfl
      omega
    funext y i
    have e : ∀ y' : F.Site (j + 1), rotationAboveLevel W kW X k G j y' = G (j + 1) y' := by
      intro y'
      unfold rotationAboveLevel balancedRotation
      rw [← hbal j hj' y', mul_inv_cancel, one_mul]
    simp only [framedUpperField, dif_neg h, gaugedChainFields, gaugeTransform, e]
def gaugedMisfitNormStatement : Prop :=
  ∀ (F : BlockFrame) (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k G : F.SiteGauge) (j : ℕ)
    (c : F.Site (j + 1) × Fin 4),
    0 < F.blockSide → j < F.top → (∀ y, G F.top y = 1) →
    (∀ i, i + 1 < F.top → ∀ y, gaugedLink k G i y = balancedLinkAgainst W kW (gaugedChainFields X G) i y) →
    gaugedContourAverage (X j) (k (j + 1)) c ≠ 0 →
    distFromOne (bondMisfit (gaugedChainFields X G j) (balancedLinkAgainst W kW (gaugedChainFields X G) j)
        (framedUpperField W kW X k G j) c) =
      distFromOne (bondMisfit (X j) (k (j + 1)) (X (j + 1)) c)
end YangMills.Construction.BlockAverages
end
