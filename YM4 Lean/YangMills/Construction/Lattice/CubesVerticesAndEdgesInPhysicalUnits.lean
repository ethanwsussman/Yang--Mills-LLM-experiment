import YangMills.Construction.Lattice.LevelsPresentOnTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice
namespace TorusBound
namespace Setup
variable (D : Setup)
abbrev torusCover (v : Fin 4 → ℝ) : D.Torus := TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) v
def IsLiftOfPoint (y : D.Torus) (w : Fin 4 → ℝ) : Prop := D.torusCover w = y
abbrev maxNorm (v : Fin 4 → ℝ) : ℝ := supNormVec v
abbrev l2Norm (v : Fin 4 → ℝ) : ℝ := TorusMetric.euclidNormVec v
def axisSegment (w : Fin 4 → ℝ) (t : ℝ) (ν : Fin 4) : Set (Fin 4 → ℝ) :=
  {x | ∃ t' : ℝ, 0 ≤ t' ∧ t' ≤ t ∧ x = w + t' • coordVec ν}
def addVec (y : D.Torus) (v : Fin 4 → ℝ) : D.Torus :=
  D.torusCover (TestFunctions.liftPoint y + v)
variable {D}
theorem addVec_eq_torusCover_add {y : D.Torus} {w : Fin 4 → ℝ} (hw : D.IsLiftOfPoint y w)
    (v : Fin 4 → ℝ) : D.addVec y v = D.torusCover (w + v) := by
  have hproj : TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) (TestFunctions.liftPoint y) =
      TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) w :=
    (TestFunctions.torusProj_liftPoint y).trans hw.symm
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hproj
  rw [addVec, hk, add_right_comm]
  exact TestFunctions.torusProj_add_latticeTranslate _ _ _
variable (D)
abbrev physicalCubeSide (j : ℕ) : ℝ := (D.cubeSide : ℝ) * meshSize D.L (D.depthOf j)
def IsLevelCube (j : ℕ) (Q : Set D.Torus) : Prop := Q ∈ D.cubesAt j
abbrev cubeCentredAt {j : ℕ} (c : Site D.L D.m (D.cubeScaleIndex j)) : Set D.Torus := cubeAround c
def IsLevelVertex {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j) (v : D.Torus) : Prop :=
  (D.levelUnitPartition hj h).IsVertex v
def IsLevelEdge {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j) (A : Set D.Torus) : Prop :=
  (D.levelUnitPartition hj h).IsEdge A
def IsHalfIntegralCoord (j : ℕ) (μ : Fin 4) (y : D.Torus) : Prop :=
  ∀ w, D.IsLiftOfPoint y w → IsGridPoint (D.physicalCubeSide j) (w μ)
def IsEdgeAxis {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j) (ν : Fin 4) (A : Set D.Torus) : Prop :=
  ∃ v w, D.IsLevelVertex hj h v ∧ D.IsLiftOfPoint v w ∧
    A = D.torusCover '' axisSegment w (D.physicalCubeSide j) ν
def treeGraphVertices {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j) (Γ : Set D.Torus) :
    Set D.Torus :=
  (D.levelUnitPartition hj h).graphVertices Γ
def treeGraphEdges {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j) (Γ : Set D.Torus) :
    Set (Set D.Torus) :=
  (D.levelUnitPartition hj h).graphEdges Γ
def TreeGraphJoins {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j) (Γ A : Set D.Torus)
    (u u' : D.Torus) : Prop :=
  A ∈ D.treeGraphEdges hj h Γ ∧ {x | (D.levelUnitPartition hj h).IsEdgeEndpoint A x} = {u, u'}
variable {D}
theorem proj_levelUnitPartition {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j) (w : Fin 4 → ℝ) :
    (D.levelUnitPartition hj h).proj w = D.torusCover (meshSize D.L (D.depthOf j) • w) :=
  rfl
theorem edgeAt_levelUnitPartition {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j) (w : Fin 4 → ℝ)
    (ν : Fin 4) :
    (D.levelUnitPartition hj h).edgeAt w ν =
      D.torusCover '' axisSegment (meshSize D.L (D.depthOf j) • w) (D.physicalCubeSide j) ν := by
  have ha : 0 < meshSize D.L (D.depthOf j) := by
    have : 0 < D.L := by
      have := D.isAdmissible.2
      omega
    exact zpow_pos (by exact_mod_cast this) _
  have hM : ((D.levelUnitPartition hj h).side : ℝ) = (D.cubeSide : ℝ) := rfl
  ext y
  constructor
  · rintro ⟨x, ⟨t, ht0, ht, rfl⟩, rfl⟩
    refine ⟨_, ⟨meshSize D.L (D.depthOf j) * t, by positivity, ?_, rfl⟩, ?_⟩
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hM ▸ ht) ha.le
    · rw [proj_levelUnitPartition, smul_add, smul_smul]
  · rintro ⟨x, ⟨t, ht0, ht, rfl⟩, rfl⟩
    refine ⟨w + ((meshSize D.L (D.depthOf j))⁻¹ * t) • coordVec ν,
      ⟨_, by positivity, ?_, rfl⟩, ?_⟩
    · rw [hM, inv_mul_le_iff₀ ha, mul_comm]
      exact ht
    · rw [proj_levelUnitPartition, smul_add, smul_smul, mul_inv_cancel_left₀ ha.ne']
end Setup
end TorusBound
end YangMills.Construction
end
