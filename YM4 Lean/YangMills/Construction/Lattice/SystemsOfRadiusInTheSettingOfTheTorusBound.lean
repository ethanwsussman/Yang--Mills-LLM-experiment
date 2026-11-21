import YangMills.Construction.Lattice.SettingOfTheTorusBound
import YangMills.Construction.Lattice.SourceClassesAndSystemsOfLocalisedSourceEnergies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusBound.Setup
variable (D : Setup)
abbrev energyDataAt (ϱ : ℝ) (hϱ : 0 < ϱ) : LocalizedEnergies.EnergyData where
  toStandingParameters := D.toStandingParameters
  cubeExp := D.cubeExp
  β := D.β
  β_pos := D.β_pos
  radius := ϱ
  radius_pos := hϱ
  index := ⟨(D.K : ℕ), le_rfl⟩
abbrev RadiusFamily (ϱ : ℝ) (hϱ : 0 < ϱ) : Type := (D.energyDataAt ϱ hϱ).EnergyFamily
theorem mem_levelSet_energyDataAt_iff (ϱ : ℝ) (hϱ : 0 < ϱ) (j : ℕ) :
    j ∈ (D.energyDataAt ϱ hϱ).levelSet ↔ j ≤ (D.K : ℕ) := by
  simp [LocalizedEnergies.EnergyData.levelSet, LocalizedEnergies.EnergyData.indexValue,
    PeriodicLattice.levelRange]
abbrev zeroSourceAt (ϱ : ℝ) (hϱ : 0 < ϱ) : D.sources ϱ := (D.energyDataAt ϱ hϱ).zeroSource
namespace RadiusFamily
variable {D} {ϱ : ℝ} {hϱ : 0 < ϱ} (e : D.RadiusFamily ϱ hϱ)
abbrev vacuumTerm : ℝ := LocalizedEnergies.EnergyData.EnergyFamily.vacuumEnergy e
abbrev totalEnergy (w : D.sources ϱ) : ℂ :=
  LocalizedEnergies.EnergyData.EnergyFamily.counterterm e w
def normalizedZ (w : D.sources ϱ) : ℂ :=
  Complex.exp (-(e.vacuumTerm : ℂ) - e.totalEnergy w) * D.partitionFun w.1
abbrev Local : Prop := LocalizedEnergies.EnergyData.EnergyFamily.IsLocal e
abbrev Analytic : Prop := LocalizedEnergies.EnergyData.EnergyFamily.IsAnalytic e
abbrev ExpBounded (Ce κe : ℝ) : Prop :=
  LocalizedEnergies.EnergyData.EnergyFamily.DecaysExponentially e Ce κe
def UpperStable (Eplus : ℝ) : Prop :=
  ∀ w : D.sources ϱ, ‖e.normalizedZ w‖ ≤ Real.exp (Eplus * D.side ^ 4)
def FloorBounded (Clow : ℝ) : Prop :=
  (e.normalizedZ (D.zeroSourceAt ϱ hϱ)).im = 0 ∧
    Real.exp (-Clow * D.side ^ 4) ≤ (e.normalizedZ (D.zeroSourceAt ϱ hϱ)).re
end RadiusFamily
end YangMills.Construction.TorusBound.Setup
end
