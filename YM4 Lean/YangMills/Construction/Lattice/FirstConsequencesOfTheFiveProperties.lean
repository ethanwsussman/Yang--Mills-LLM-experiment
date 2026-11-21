import YangMills.Construction.Lattice.SystemsOfRadiusInTheSettingOfTheTorusBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusBound
namespace Setup.RadiusFamily
variable {D : Setup} {ϱ : ℝ} {hϱ : 0 < ϱ}
def restrict (e : D.RadiusFamily ϱ hϱ) {ϱ' : ℝ} (hϱ' : 0 < ϱ')
    (hsub : D.sources ϱ' ⊆ D.sources ϱ) : D.RadiusFamily ϱ' hϱ' where
  vacuumEnergy := e.vacuumTerm
  localEnergy j X w :=
    LocalizedEnergies.EnergyData.EnergyFamily.localEnergy e j X ⟨w.1, hsub w.2⟩
end Setup.RadiusFamily
namespace Consequences
def UnitSiteCount (D : Setup) : Prop :=
  (Nat.card (PeriodicLattice.Site D.L D.m 0) : ℝ) = D.side ^ 4
def ZeroSourceValue {D : Setup} {ϱ : ℝ} {hϱ : 0 < ϱ} (e : D.RadiusFamily ϱ hϱ) : Prop :=
  e.Local →
    e.totalEnergy (D.zeroSourceAt ϱ hϱ) = 0 ∧
      e.normalizedZ (D.zeroSourceAt ϱ hϱ) =
        Complex.exp (-(e.vacuumTerm : ℂ)) * D.partitionFun (D.zeroSourceAt ϱ hϱ).1 ∧
      (e.normalizedZ (D.zeroSourceAt ϱ hϱ)).im = 0 ∧
      0 < (e.normalizedZ (D.zeroSourceAt ϱ hϱ)).re
def ConstantsSumNonneg {D : Setup} {ϱ : ℝ} {hϱ : 0 < ϱ} (e : D.RadiusFamily ϱ hϱ)
    (Eplus Clow : ℝ) : Prop :=
  e.UpperStable Eplus → e.FloorBounded Clow → 0 ≤ Eplus + Clow
def RestrictionInherits {D : Setup} {ϱ : ℝ} {hϱ : 0 < ϱ} (e : D.RadiusFamily ϱ hϱ) : Prop :=
  ∀ (ϱ' : ℝ) (hϱ' : 0 < ϱ'), ϱ' ≤ ϱ →
    ∃ hsub : D.sources ϱ' ⊆ D.sources ϱ,
      (e.Local → (e.restrict hϱ' hsub).Local) ∧
        (e.Analytic → (e.restrict hϱ' hsub).Analytic) ∧
        (∀ Ce κe : ℝ, e.ExpBounded Ce κe →
          (e.restrict hϱ' hsub).ExpBounded Ce κe) ∧
        (∀ Eplus : ℝ, e.UpperStable Eplus →
          (e.restrict hϱ' hsub).UpperStable Eplus) ∧
        (∀ Clow : ℝ, e.FloorBounded Clow → (e.restrict hϱ' hsub).FloorBounded Clow)
def ConstantsMonotone {D : Setup} {ϱ : ℝ} {hϱ : 0 < ϱ} (e : D.RadiusFamily ϱ hϱ)
    (Eplus Clow : ℝ) : Prop :=
  (e.UpperStable Eplus → ∀ Eplus' : ℝ, Eplus ≤ Eplus' → e.UpperStable Eplus') ∧
    (e.FloorBounded Clow → ∀ Clow' : ℝ, Clow ≤ Clow' → e.FloorBounded Clow')
def VolumeBounds {D : Setup} {ϱ : ℝ} {hϱ : 0 < ϱ} (e : D.RadiusFamily ϱ hϱ)
    (Eplus Clow : ℝ) : Prop :=
  ∀ V : ℝ, 0 ≤ V → V ≤ D.side ^ 4 →
    ((∀ w : D.sources ϱ, ‖e.normalizedZ w‖ ≤ Real.exp (Eplus * V)) →
        e.UpperStable (plusPart Eplus)) ∧
      ((e.normalizedZ (D.zeroSourceAt ϱ hϱ)).im = 0 →
        Real.exp (-Clow * V) ≤ (e.normalizedZ (D.zeroSourceAt ϱ hϱ)).re →
        e.FloorBounded (plusPart Clow))
def AllHold : Prop :=
  ∀ (D : Setup) (ϱ : ℝ) (hϱ : 0 < ϱ) (e : D.RadiusFamily ϱ hϱ) (Eplus Clow : ℝ),
    UnitSiteCount D ∧ ZeroSourceValue e ∧ ConstantsSumNonneg e Eplus Clow ∧
      RestrictionInherits e ∧ ConstantsMonotone e Eplus Clow ∧ VolumeBounds e Eplus Clow
end Consequences
end YangMills.Construction.TorusBound
end
