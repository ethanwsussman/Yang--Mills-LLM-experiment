import YangMills.Construction.Lattice.BlocksInTheCoordinatesOfAFinerLatticeProof
import YangMills.Construction.Lattice.CubesLayersAndTopsOfADecreasingSequence
import YangMills.Construction.Lattice.GeometryOfASeparatedSequenceProof
import YangMills.Construction.Lattice.WeightedDistanceAlongABarePathProof
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import YangMills.Construction.SeparatedSequences.NumbersOfThePropagatorServeOnTheToriProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice
noncomputable section
namespace SeparatedSequences
namespace AntitoneBlocks
variable {L m : ℕ}
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < PeriodicLattice.meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem abs_le_supNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ _root_.YangMills.Construction.TorusMetric.supNormVec v := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.abs_le_supNormVec <;> assumption
theorem supNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ _root_.YangMills.Construction.TorusMetric.supNormVec v :=
  (abs_nonneg _).trans (abs_le_supNormVec v 0)
theorem supNorm_eq_torusSupNorm {a : ℝ} (p : Torus4 a) : Torus.supNorm p = torusSupNorm p := by apply _root_.YangMills.Construction.GeneralTorus.GreenBounds.FromPropagator.supNorm_eq_torusSupNorm <;> assumption
theorem torusSupNorm_le_of_torusProj_eq {a : ℝ} {x : Torus4 a} {v : Fin 4 → ℝ}
    (hv : torusProj a v = x) : torusSupNorm x ≤ _root_.YangMills.Construction.TorusMetric.supNormVec v :=
  csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact _root_.YangMills.Construction.SeparatedSequences.AntitoneBlocks.supNormVec_nonneg w⟩ ⟨v, hv, rfl⟩
theorem torusSupNorm_zero {a : ℝ} : torusSupNorm (0 : Torus4 a) = 0 := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_zero <;> assumption
theorem mem_spacingLattice_iff (j : ℤ) (y : FourTorus L m) :
    y ∈ Torus.spacingLattice 4 (torusSide L m) (PeriodicLattice.meshSize L j) ↔
      y ∈ PeriodicLattice.sublattice L m j := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, fun μ => rfl⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, funext hn⟩
theorem scaleSpacing_eq_meshSize (hL : 0 < L) (K : ℕ) (i : ℤ) :
    Torus.scaleSpacing L ((L : ℝ) ^ (-(K : ℤ))) i = PeriodicLattice.meshSize L ((K : ℤ) - i) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold Torus.scaleSpacing PeriodicLattice.meshSize
  rw [← zpow_add₀ hL']
  congr 1
  ring
theorem torusSide_eq_mul (hL : 0 < L) {K t : ℕ} (ht : t ≤ K) :
    torusSide L m = (((L ^ (m + K - t) : ℕ) : ℤ) : ℝ) *
      (2 * Torus.scaleSpacing L ((L : ℝ) ^ (-(K : ℤ))) (t : ℤ)) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [scaleSpacing_eq_meshSize hL]
  have h : ((L : ℝ) ^ (m + K - t)) = (L : ℝ) ^ ((m : ℤ) + ((K : ℤ) - (t : ℤ))) := by
    rw [← zpow_natCast]
    congr 1
    omega
  unfold torusSide PeriodicLattice.meshSize
  push_cast
  rw [h, zpow_add₀ hL', zpow_natCast, zpow_neg]
  have h2 : (L : ℝ) ^ ((K : ℤ) - (t : ℤ)) ≠ 0 := zpow_ne_zero _ hL'
  field_simp
variable (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
theorem truncatedMember_of_le {n : ℕ} (h : n ≤ S.top) : truncatedMember S Ω n = Ω n := by
  simp [truncatedMember, h]
variable {S Ω}
theorem centre_mem_cubeAround (hL : 0 < L) {j : ℤ} (y : PeriodicLattice.Site L m j) :
    (y : FourTorus L m) ∈ cubeAround y := by
  have h := meshSize_pos hL j
  change torusSupNorm ((y : FourTorus L m) - (y : FourTorus L m)) ≤ PeriodicLattice.meshSize L j / 2
  rw [sub_self, torusSupNorm_zero]
  positivity
section Cells
variable (hodd : Odd L) (h13 : 13 ≤ L) (hdec : ∀ n < S.top, Ω (n + 1) ⊆ Ω n)
  (hreg : ∀ n ≤ S.top, PeriodicLattice.IsPartitionRegion (levelDepth S.levels n) (Ω n))
end Cells
theorem torusSide_div_meshSize (hL : 0 < L) {j : ℤ} (hj : -(m : ℤ) ≤ j) :
    torusSide L m / PeriodicLattice.meshSize L j = (((2 * L ^ ((m : ℤ) + j).toNat : ℕ) : ℤ) : ℝ) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h : (L : ℝ) ^ ((m : ℤ) + j).toNat = (L : ℝ) ^ ((m : ℤ) + j) := by
    rw [← zpow_natCast]
    congr 1
    omega
  unfold torusSide PeriodicLattice.meshSize
  push_cast
  rw [h, zpow_add₀ hL', zpow_neg, zpow_natCast]
  have h2 : (L : ℝ) ^ j ≠ 0 := zpow_ne_zero _ hL'
  field_simp
theorem segmentsSupport_append {a : ℝ} (Γ₁ Γ₂ : List LiftedSegment) :
    segmentsSupport a (Γ₁ ++ Γ₂) = segmentsSupport a Γ₁ ∪ segmentsSupport a Γ₂ := by apply _root_.YangMills.Construction.SeparatedClasses.BlockStructureProof.segmentsSupport_append <;> assumption
end AntitoneBlocks
end SeparatedSequences
end
end YangMills.Construction
