import YangMills.Construction.Lattice.PartitionInLevelUnits
import YangMills.Construction.Lattice.SettingOfTheTorusBound
import YangMills.Construction.Lattice.SourceClassesAndSystemsOfLocalisedSourceEnergies
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace TorusBound
inductive DomainKind
  | wallConnected
  | faceConnected
namespace Setup
variable (D : Setup)
abbrev depthOf (j : ℕ) : ℤ := PeriodicLattice.levelDepth D.K j
abbrev cubeScaleIndex (j : ℕ) : ℤ := PeriodicLattice.coarseCubeIndex D.K D.cubeExp j
def LevelFits (j : ℕ) : Prop :=
  (D.cubeSide : ℝ) * PeriodicLattice.meshSize D.L (D.depthOf j) ≤ D.side / 2
variable {D}
theorem cubeSide_mul_meshSize (j : ℕ) :
    (D.cubeSide : ℝ) * PeriodicLattice.meshSize D.L (D.depthOf j) =
      PeriodicLattice.meshSize D.L (D.cubeScaleIndex j) := by
  have hL : D.L ≠ 0 := by
    have := D.isAdmissible.2
    omega
  rw [cubeScaleIndex, PeriodicLattice.coarseCubeIndex, PeriodicLattice.meshSize_scaledCubeIndex hL]
  simp [cubeSide]
theorem levelFits_iff {j : ℕ} :
    D.LevelFits j ↔ (D.cubeExp : ℤ) ≤ (D.m : ℤ) + (D.K : ℤ) - (j : ℤ) := by
  have hL : (1 : ℝ) < (D.L : ℝ) := by
    have := D.isAdmissible.2
    exact_mod_cast (by omega : 1 < D.L)
  have hside : D.side / 2 = (D.L : ℝ) ^ ((D.m : ℕ) : ℤ) := by
    simp [Conventions.StandingParameters.side, PeriodicLattice.torusSide]
  rw [LevelFits, cubeSide_mul_meshSize, hside, PeriodicLattice.meshSize,
    zpow_le_zpow_iff_right₀ hL]
  simp only [cubeScaleIndex, PeriodicLattice.coarseCubeIndex, PeriodicLattice.scaledCubeIndex,
    PeriodicLattice.levelDepth]
  omega
theorem meshSize_le_cubeSide_mul_meshSize (j : ℕ) :
    PeriodicLattice.meshSize D.L (D.K : ℤ) ≤
      (D.cubeSide : ℝ) * PeriodicLattice.meshSize D.L (D.depthOf j) := by
  have hL : (1 : ℝ) ≤ (D.L : ℝ) := by
    have := D.isAdmissible.2
    exact_mod_cast (by omega : 1 ≤ D.L)
  rw [cubeSide_mul_meshSize, PeriodicLattice.meshSize, PeriodicLattice.meshSize]
  apply zpow_le_zpow_right₀ hL
  simp only [cubeScaleIndex, PeriodicLattice.coarseCubeIndex, PeriodicLattice.scaledCubeIndex,
    PeriodicLattice.levelDepth]
  omega
variable (D)
abbrev cubesAt (j : ℕ) : Set (Set D.Torus) :=
  PeriodicLattice.standardCubePartition D.L D.m (D.cubeScaleIndex j)
def regionsBy : DomainKind → ℕ → Set (Set D.Torus)
  | .wallConnected, j =>
      {X | D.LevelFits j ∧ X ∈ PeriodicLattice.connectedRegions D.L D.m (D.cubeScaleIndex j)}
  | .faceConnected, j =>
      {X | D.LevelFits j ∧ X ∈ PeriodicLattice.faceChainConnectedRegions D.L D.m (D.cubeScaleIndex j)}
abbrev regionsAt (j : ℕ) : Set (Set D.Torus) := D.regionsBy .wallConnected j
variable {D}
theorem levelFits_of_mem_regionsBy {d : DomainKind} {j : ℕ} {X : Set D.Torus}
    (h : X ∈ D.regionsBy d j) : D.LevelFits j := by
  cases d <;> exact h.1
theorem regionsBy_eq_empty {j : ℕ} (d : DomainKind) (h : ¬D.LevelFits j) :
    D.regionsBy d j = ∅ :=
  eq_empty_of_forall_notMem fun _ hX => h (levelFits_of_mem_regionsBy hX)
def ofEnergyData (E : LocalizedEnergies.EnergyData) : Setup where
  toStandingParameters := E.toStandingParameters
  cubeExp := E.cubeExp
  β := E.β
  β_pos := E.β_pos
theorem regionsAt_ofEnergyData (E : LocalizedEnergies.EnergyData) (j : ℕ) :
    (ofEnergyData E).regionsAt j = E.domainsAt j := by
  have h : (ofEnergyData E).LevelFits j ↔ E.PartitionExists j := by
    rw [levelFits_iff, LocalizedEnergies.EnergyData.PartitionExists]
    simp only [ofEnergyData]
    omega
  ext X
  simp only [regionsAt, regionsBy, mem_ofPred_eq, LocalizedEnergies.EnergyData.domainsAt, h]
  rfl
variable (D)
abbrev thickened (j : ℕ) (X : Set D.Torus) : Set D.Torus :=
  PeriodicLattice.addCubeLayer (D.cubeScaleIndex j) X
abbrev plaquettesOfThickened (j : ℕ) (X : Set D.Torus) :
    Set (PeriodicLattice.Plaquette D.L D.m (D.K : ℤ)) :=
  PeriodicLattice.plaquettesMeeting (D.thickened j X)
def levelUnitPartition {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j) :
    PeriodicLattice.LevelUnitPartition :=
  ⟨D.toStandingParameters, D.cubeExp, j, hj, levelFits_iff.1 h⟩
abbrev extent (j : ℕ) (X : Set D.Torus) : ℝ := PeriodicLattice.linearExtent D.K D.cubeExp j X
end Setup
def IsEdgeTreeWithCount (P : PeriodicLattice.LevelUnitPartition) (X Γ : Set P.Points) (E : ℕ) :
    Prop :=
  P.IsEdgeTreeInRegion X Γ ∧ (P.graphEdges Γ).ncard = E
end TorusBound
end YangMills.Construction
end
