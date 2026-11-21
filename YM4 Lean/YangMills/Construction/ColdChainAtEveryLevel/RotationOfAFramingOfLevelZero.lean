import YangMills.Construction.ColdChainAtEveryLevel.FramingFromAGaugeOfLevelZero
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMotionsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
open YangMills.Construction.GaugeMotions
def rotatedBaseGauge (ξ : F.Site 0 → imaginaryQuaternions) (τ : ℝ) (γ : F.Site 0 → UnitQuaternion) :
    F.Site 0 → UnitQuaternion := fun x => expUnit (τ • ξ x) * γ x
def pathAveragedGenerator {j : ℕ} (g : F.Site j → UnitQuaternion) (A B : F.GaugeField j)
    (v : F.Site j → ℍ[ℝ]) (y : F.Site (j + 1)) : ℍ[ℝ] :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ σ : Equiv.Perm (Fin 4),
    ((pathHolonomy A (refineSite y) (axisPath h σ) * (g (refineSite y + siteOfCoords j h))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
      v (refineSite y + siteOfCoords j h) *
      (((pathHolonomy B (refineSite y) (axisPath h σ))⁻¹ : UnitQuaternion) : ℍ[ℝ])
def coarseGenerator {j : ℕ} (g : F.Site j → UnitQuaternion) (A B : F.GaugeField j) (u : UnitQuaternion)
    (v : F.Site j → ℍ[ℝ]) (y : F.Site (j + 1)) : ℍ[ℝ] :=
  (1 / ‖gaugedPathAverage g A B y‖) • adjointAction u (pureComponent
    ((((polarUnit (gaugedPathAverage g A B y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * pathAveragedGenerator g A B v y))
def pinnedGaugeGenerator (W : F.FieldChain) (kW : F.SiteGauge) (A : F.FieldChain) (k : F.SiteGauge)
    (γ : F.Site 0 → UnitQuaternion) (ξ : F.Site 0 → ℍ[ℝ]) : (j : ℕ) → F.Site j → ℍ[ℝ]
  | 0 => ξ
  | j + 1 => fun y => coarseGenerator (pinnedGaugeLevel W kW A k γ j) (A j) (W j) (kW (j + 1) y)
      (pinnedGaugeGenerator W kW A k γ ξ j) y
namespace PinnedGaugeVariation
variable {j : ℕ}
theorem polarUnit_coe_mul (g : UnitQuaternion) {q : ℍ[ℝ]} (hq : q ≠ 0) :
    polarUnit ((g : ℍ[ℝ]) * q) = g * polarUnit q := by
  have hgq : (g : ℍ[ℝ]) * q ≠ 0 := mul_ne_zero (fun h0 => by
    have := norm_coe_unitQuaternion g
    rw [h0, norm_zero] at this
    norm_num at this) hq
  apply Subtype.ext
  rw [coe_polarUnit hgq, Submonoid.coe_mul, coe_polarUnit hq, norm_mul, norm_coe_unitQuaternion, one_mul,
    mul_smul_comm]
theorem gaugedPathAverage_ne_zero {g : F.Site j → UnitQuaternion} {A B : F.GaugeField j} {y : F.Site (j + 1)}
    (h : relativePathAverage (gaugeTransform g A) B y ≠ 0) : gaugedPathAverage g A B y ≠ 0 := by
  intro h0
  apply h
  rw [relativePathAverage_gaugeTransform, h0, mul_zero]
theorem balancingGauge_mul_eq (g : F.Site j → UnitQuaternion) (A B : F.GaugeField j) (u u' : UnitQuaternion)
    (y : F.Site (j + 1)) (h : gaugedPathAverage g A B y ≠ 0) :
    u * balancingGauge (gaugeTransform g A) B y * g (refineSite y) * u' =
      u * (polarUnit (gaugedPathAverage g A B y))⁻¹ * u' := by
  unfold balancingGauge
  rw [relativePathAverage_gaugeTransform, polarUnit_coe_mul _ h]
  group
theorem topCorrection_eq {W : F.FieldChain} {kW : F.SiteGauge} {A : F.FieldChain} {k : F.SiteGauge}
    (γ : F.Site 0 → UnitQuaternion) (y : F.Site F.top) :
    topCorrection W kW A k (pinnedGaugeOfBase W kW A k γ) y = kW F.top y *
      balancingGauge (gaugeTransform (pinnedGaugeLevel W kW A k γ F.depth) (A F.depth)) (W F.depth) y *
        pinnedGaugeLevel W kW A k γ F.depth (refineSite y) * (k F.top y)⁻¹ := by
  have e : pinnedGaugeLevel W kW A k γ (F.depth + 1) y = 1 := by
    show (if F.depth + 1 < F.top then _ else (1 : UnitQuaternion)) = 1
    exact if_neg (lt_irrefl _)
  unfold topCorrection balancedLinkAgainst gaugedLink gaugedChainFields pinnedGaugeOfBase
  rw [e]
  group
end PinnedGaugeVariation
def pinnedGaugeVariationStatement : Prop :=
  ∀ (F : BlockFrame) (W : F.FieldChain) (kW : F.SiteGauge) (A : F.FieldChain) (k : F.SiteGauge)
    (γ : F.Site 0 → UnitQuaternion) (ξ : F.Site 0 → imaginaryQuaternions) (D : Finset F.Cell), Odd F.blockSide →
    (∀ j, j < F.top → ∀ y ∈ sitesOfCells D (j + 1),
      relativePathAverage (gaugeTransform (pinnedGaugeLevel W kW A k γ j) (A j)) (W j) y ≠ 0) →
    (∀ j, j < F.top → ∀ y ∈ sitesOfCells D j,
      (pinnedGaugeGenerator W kW A k γ (fun x => (ξ x : ℍ[ℝ])) j y).re = 0 ∧
      HasDerivAt (fun τ : ℝ => ((pinnedGaugeLevel W kW A k (rotatedBaseGauge ξ τ γ) j y : UnitQuaternion) : ℍ[ℝ]))
        (pinnedGaugeGenerator W kW A k γ (fun x => (ξ x : ℍ[ℝ])) j y *
          ((pinnedGaugeLevel W kW A k γ j y : UnitQuaternion) : ℍ[ℝ])) 0) ∧
    ∀ y ∈ sitesOfCells D F.top,
      (pinnedGaugeGenerator W kW A k γ (fun x => (ξ x : ℍ[ℝ])) F.top y).re = 0 ∧
      HasDerivAt (fun τ : ℝ => ((topCorrection W kW A k
          (pinnedGaugeOfBase W kW A k (rotatedBaseGauge ξ τ γ)) y : UnitQuaternion) : ℍ[ℝ]))
        (pinnedGaugeGenerator W kW A k γ (fun x => (ξ x : ℍ[ℝ])) F.top y *
          ((topCorrection W kW A k (pinnedGaugeOfBase W kW A k γ) y : UnitQuaternion) : ℍ[ℝ])) 0
end YangMills.Construction.BlockAverages
end
