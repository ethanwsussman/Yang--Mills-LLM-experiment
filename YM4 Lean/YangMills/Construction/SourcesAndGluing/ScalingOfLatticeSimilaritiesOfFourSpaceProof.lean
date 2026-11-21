import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrabilityProof
import YangMills.Construction.SourcesAndGluing.CompositeOfLatticeSimilaritiesProof
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.Torus.LiftsAndInducedMapsProof
import Mathlib
set_option autoImplicit false
open YangMills.Construction.TorusLifts YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace ScaledMotionDilationOfSpace
variable {S : Equiv.Perm AmbientSpace}
theorem hyperoctahedral_map_smul (hS : S ∈ hyperoctahedralGroupEuclidean) (c : ℝ) (x : AmbientSpace) :
    S (c • x) = c • S x := by apply _root_.YangMills.Construction.SourcesAndGluing.CompositionOfScaledMotions.map_smul_of_mem_hyperoctahedral <;> assumption
theorem hyperoctahedral_map_sub (hS : S ∈ hyperoctahedralGroupEuclidean) (x y : AmbientSpace) :
    S (x - y) = S x - S y := by apply _root_.YangMills.Construction.TorusLifts.LiftsAndDescendedMaps.hyperoctahedral_map_sub <;> assumption
theorem euclidNorm_hyperoctahedral_map (hS : S ∈ hyperoctahedralGroupEuclidean) (x : AmbientSpace) :
    euclidNorm (S x) = euclidNorm x := by apply _root_.YangMills.Construction.TorusLifts.LiftsAndDescendedMaps.euclidNormVec_hyperoctahedral <;> assumption
theorem euclidNorm_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x : AmbientSpace) :
    euclidNorm (c • x) = c * euclidNorm x := by apply _root_.YangMills.Construction.WightmanReconstruction.SmoothToolkit.euclidNormVec_smul_of_nonneg <;> assumption
theorem isSignedPermOn_axis_of_mem (hS : S ∈ hyperoctahedralGroupEuclidean) :
    IsSignedPermOn S (axisPerm S) (axisSigns S) := by apply _root_.YangMills.Construction.TorusLifts.LiftsAndDescendedMaps.isSignedPermOn_axisPerm_axisSigns <;> assumption
theorem scaledMotionDilationOfSpace_holds : ScaledMotionDilationOfSpaceClaim := by
  intro D e Φ
  have hLn : 0 < D.L := ScaleExponent.L_pos
  have hL : (0 : ℝ) < (D.L : ℝ) := by exact_mod_cast hLn
  have hc : (0 : ℝ) < (D.L : ℝ) ^ e.shift := zpow_pos hL _
  have hS := Φ.rotation_mem
  have hmap : ∀ x, Φ.onSpace x = (D.L : ℝ) ^ e.shift • Φ.rotation x + Φ.offset := fun _ => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro x y h
    rw [hmap, hmap] at h
    exact Φ.rotation.injective (smul_right_injective AmbientSpace hc.ne' (add_right_cancel h))
  · intro y
    refine ⟨Φ.rotation.symm (((D.L : ℝ) ^ e.shift)⁻¹ • (y - Φ.offset)), ?_⟩
    rw [hmap, Equiv.apply_symm_apply, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, sub_add_cancel]
  · intro x y
    have h : Φ.onSpace x - Φ.onSpace y = (D.L : ℝ) ^ e.shift • Φ.rotation (x - y) := by
      rw [hmap, hmap, hyperoctahedral_map_sub hS, smul_sub]
      abel
    rw [h, euclidNorm_smul_of_nonneg hc.le, euclidNorm_hyperoctahedral_map hS]
  · intro x z
    rw [hmap, hmap, map_add_of_mem_hyperoctahedral hS, smul_add]
    abel
  · intro x μ
    have hb : Φ.rotation (stdBasis μ) =
        (((Φ.signs μ : ℤˣ) : ℤ) : ℝ) • stdBasis (Φ.perm μ) :=
      isSignedPermOn_axis_of_mem hS μ
    have ha : e.target.mesh = (D.L : ℝ) ^ e.shift * D.mesh :=
      (ScaledLatticeMotion.target_mesh (e := e)).trans (meshSize_shift_eq_zpow_mul hLn rfl)
    rw [hmap, hmap, map_add_of_mem_hyperoctahedral hS, hyperoctahedral_map_smul hS, hb, ha, smul_add,
      smul_smul, smul_smul]
    have hcoef : (D.L : ℝ) ^ e.shift * D.mesh * (((Φ.signs μ : ℤˣ) : ℤ) : ℝ) =
        (((Φ.signs μ : ℤˣ) : ℤ) : ℝ) * ((D.L : ℝ) ^ e.shift * D.mesh) := by ring
    rw [hcoef]
    abel
  · refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (Φ.onPoint ⟨x, hx⟩).2
    · intro y hy
      have hyw : y - Φ.offset ∈
          InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize D.L (((D.K : ℕ) : ℤ) - e.shift)) := by
        have h := sub_mem (show y ∈ e.target.gridPoints from hy) Φ.offset_mem
        have ha := ScaledLatticeMotion.target_mesh (e := e)
        simpa only [GluingSetup.gridPoints, ha] using h
      have hx : scaledMotion D.L (-e.shift) (Φ.rotation⁻¹ : Equiv.Perm AmbientSpace) 0
          (y - Φ.offset) ∈ D.gridPoints :=
        scaledMotion_mem_latticeSubgroup (j := ((D.K : ℕ) : ℤ) - e.shift) (j' := ((D.K : ℕ) : ℤ)) hLn
          (by ring) (inv_mem hS) (zero_mem _) hyw
      refine ⟨_, hx, ?_⟩
      rw [hmap]
      simp only [scaledMotion, add_zero]
      have hinv : ∀ z, Φ.rotation (Φ.rotation⁻¹ z) = z :=
        fun z => Φ.rotation.apply_symm_apply z
      rw [hyperoctahedral_map_smul hS, hinv, smul_smul, ← zpow_add₀ hL.ne',
        add_neg_cancel, zpow_zero, one_smul, sub_add_cancel]
end ScaledMotionDilationOfSpace
end YangMills.Construction.SourcesAndGluing
end
