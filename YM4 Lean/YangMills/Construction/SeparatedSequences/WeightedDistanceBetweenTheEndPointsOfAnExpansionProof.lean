import YangMills.Construction.SeparatedSequences.BoundOfTheDifferencesOfTheExtensionKernelAtATopAndAnExpansionProof
import YangMills.Construction.SeparatedSequences.TopsOfTheBareSitesNearATopProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.SeparatedSequences.PartitionsCubesExpansionsAndTheTriangleInequalityProof
import YangMills.Construction.SeparatedSequences.WeightedDistanceBetweenTheEndPointsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses.ExpansionEndpointBound
open Set MeasureTheory YangMills.Construction.PeriodicLattice YangMills.Construction.TorusMetric
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem continuous_torusProj (S : ℝ) : Continuous (torusProj S) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
theorem torusProj_add {S : ℝ} (v w : Fin 4 → ℝ) :
    torusProj S (v + w) = torusProj S v + torusProj S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem torusProj_zero {S : ℝ} : torusProj S 0 = 0 := funext fun μ => by simp [torusProj]
theorem l1NormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ l1NormVec v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
section BondSegment
variable {L m : ℕ} {j : ℤ}
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem mem_interior_cubeAround {i : ℤ} {w : Site L m i} {p : FourTorus L m}
    (hp : ‖p - (w : FourTorus L m)‖ < meshSize L i / 2) : p ∈ interior (cubeAround w) := by
  have hopen : IsOpen {x : FourTorus L m | ‖x - (w : FourTorus L m)‖ < meshSize L i / 2} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  refine interior_maximal (fun x hx => ?_) hopen hp
  simp only [cubeAround, mem_setOf_eq, torusSupNorm_eq_norm]
  exact le_of_lt hx
end BondSegment
section Classes
variable {C : ClassData} {Ω : ℕ → Set C.Point}
theorem levelMesh_pos (C : ClassData) (n : ℕ) : 0 < C.scales.levelMesh C.L n := by apply _root_.YangMills.Construction.SeparatedClasses.ExtKernelDiff.coarseMesh_pos <;> assumption
theorem memberAt_eq (hΩ : Ω ∈ C.separatedClass) (n : ℕ) : C.memberAt Ω n = Ω n := by apply _root_.YangMills.Construction.SeparatedClasses.BlockStructureProof.memberAt_eq <;> assumption
theorem neg_m_le_levelDepth (C : ClassData) {n : ℕ} (hn : n ≤ C.t) :
    -(C.m : ℤ) ≤ levelDepth C.cutoff n := by apply _root_.YangMills.Construction.SeparatedClasses.BlockStructureProof.neg_m_le_levelDepth <;> assumption
theorem L_pos (C : ClassData) : 0 < C.L := by
  have := C.isAdmissible.2
  omega
end Classes
end YangMills.Construction.SeparatedClasses.ExpansionEndpointBound
end
