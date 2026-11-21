import YangMills.Construction.Lattice.CubeGeometryAndTranslationProof
import YangMills.Construction.SeparatedSequences.PartitionsCubesExpansionsAndTheTriangleInequalityProof
import YangMills.Construction.WeightedLength.ChainBoundsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set MeasureTheory TorusMetric PeriodicLattice SeparatedSequences
namespace CubeCovering.FinePath
variable {L m : ℕ}
theorem segmentsSupport_append (S : ℝ) (Γ Δ : List LiftedSegment) :
    segmentsSupport S (Γ ++ Δ) = segmentsSupport S Γ ∪ segmentsSupport S Δ := by apply _root_.YangMills.Construction.SeparatedClasses.BlockStructureProof.segmentsSupport_append <;> assumption
theorem pathLengthIn_append (S : ℝ) (Γ Δ : List LiftedSegment) (A : Set (Torus4 S)) :
    pathLengthIn S (Γ ++ Δ) A = pathLengthIn S Γ A + pathLengthIn S Δ A := by
  simp only [pathLengthIn, List.map_append, List.sum_append]
theorem isTreeGraph_singleton (S : ℝ) (s : LiftedSegment) : IsTreeGraph S [s] := by
  have hproj : Continuous (torusProj S) :=
    continuous_pi fun μ => (AddCircle.continuous_mk' S).comp (continuous_apply μ)
  have hpt : Continuous (s.pointAt S) := by
    unfold LiftedSegment.pointAt
    exact hproj.comp (continuous_const.add (continuous_id.smul continuous_const))
  have h : segmentsSupport S [s] = s.pointAt S '' Icc 0 1 := by
    simp [segmentsSupport, LiftedSegment.support]
  rw [IsTreeGraph, h]
  exact (isConnected_Icc zero_le_one).image _ hpt.continuousOn
def openBox (b : ℝ) (z : FourTorus L m) : Set (FourTorus L m) := {x | ∀ μ, ‖(x - z) μ‖ < b / 2}
theorem mem_openBox {b : ℝ} {z x : FourTorus L m} :
    x ∈ openBox b z ↔ ∀ μ, ‖(x - z) μ‖ < b / 2 := Iff.rfl
theorem volume_toReal_le_halves {A : Set ℝ} (hA : A ⊆ Icc 0 1) (a b : Prop) [Decidable a]
    [Decidable b] (h₁ : ∀ τ ∈ Ioo (0 : ℝ) (1 / 2), τ ∈ A → a)
    (h₂ : ∀ τ ∈ Ioo (1 / 2 : ℝ) 1, τ ∈ A → b) :
    (volume A).toReal ≤ (if a then (1 / 2 : ℝ) else 0) + (if b then (1 / 2 : ℝ) else 0) := by apply _root_.YangMills.Construction.WeightedLength.volume_toReal_le_halves <;> assumption
variable (C : CubeData L m)
theorem base_pos (C : CubeData L m) : 0 < L := by apply _root_.YangMills.Construction.CubeCovering.CubeData.base_pos <;> assumption
def fineMesh (C : CubeData L m) : ℝ := meshSize L (levelDepth C.scales.levels 0)
def topMesh (C : CubeData L m) : ℝ := meshSize L (levelDepth C.scales.levels C.scales.top)
theorem levelScale_pos (n : ℕ) : 0 < C.levelScale n := zpow_pos (by exact_mod_cast base_pos C) _
def liftPoint (x : Space) : Fin 4 → ℝ := fun μ => topMesh C * x μ
def linkSegment (p p' : Space) : LiftedSegment := ⟨liftPoint C p, liftPoint C p'⟩
end CubeCovering.FinePath
end YangMills.Construction
