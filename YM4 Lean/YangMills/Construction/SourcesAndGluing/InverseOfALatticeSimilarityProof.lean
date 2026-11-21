import YangMills.Construction.SourcesAndGluing.CompositeOfLatticeSimilaritiesProof
import YangMills.Construction.SourcesAndGluing.InverseOfALatticeSimilarityForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusLifts TorusMetric
namespace SourcesAndGluing
open InfiniteLattice (AmbientSpace)
namespace ScaledMotionInverse
theorem map_smul_of_mem_hyperoctahedral {S : Equiv.Perm AmbientSpace}
    (hS : S ∈ hyperoctahedralGroupEuclidean) (c : ℝ) (x : AmbientSpace) : S (c • x) = c • S x := by apply _root_.YangMills.Construction.SourcesAndGluing.CompositionOfScaledMotions.map_smul_of_mem_hyperoctahedral <;> assumption
theorem transport_torusProj {D D' : GluingSetup} (h : D = D') (x : AmbientSpace) :
    transport (F := fun X : GluingSetup => X.Torus) h
        (torusProj (PeriodicLattice.torusSide D.L (D.m : ℕ)) x) =
      torusProj (PeriodicLattice.torusSide D'.L (D'.m : ℕ)) x := by apply _root_.YangMills.Construction.SourcesAndGluing.CompositionOfScaledMotions.transport_torusProj <;> assumption
variable {D : GluingSetup} {e : ScaleExponent D} (Φ : ScaledLatticeMotion e)
theorem L_ne_zero : (D.L : ℝ) ≠ 0 := by
  exact_mod_cast (ScaleExponent.L_pos (D := D)).ne'
def inverseOffset : AmbientSpace :=
  -((D.L : ℝ) ^ (-e.shift) • Φ.rotation⁻¹ Φ.offset)
theorem inverseOffset_mem : inverseOffset Φ ∈ e.neg.target.gridPoints := by
  rw [e.target_neg]
  refine neg_mem ?_
  have h := scaledMotion_mem_latticeSubgroup (L := D.L) (b := -e.shift) (j := ((e.target.K : ℕ) : ℤ))
    (j' := ((D.K : ℕ) : ℤ)) ScaleExponent.L_pos
    (by have := e.target_K; omega) (inv_mem Φ.rotation_mem) (w := 0)
    (zero_mem _) Φ.offset_mem
  exact show (D.L : ℝ) ^ (-e.shift) • Φ.rotation⁻¹ Φ.offset ∈
      InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)) from by
    simpa [scaledMotion] using h
def inverseMotion : ScaledLatticeMotion e.neg where
  rotation := Φ.rotation⁻¹
  rotation_mem := inv_mem Φ.rotation_mem
  offset := inverseOffset Φ
  offset_mem := inverseOffset_mem Φ
theorem inverseMotion_onSpace_onSpace (x : AmbientSpace) :
    (inverseMotion Φ).onSpace (Φ.onSpace x) = x := by
  have hS := inv_mem Φ.rotation_mem
  change (D.L : ℝ) ^ (-e.shift) • Φ.rotation⁻¹ ((D.L : ℝ) ^ e.shift • Φ.rotation x + Φ.offset) +
    -((D.L : ℝ) ^ (-e.shift) • Φ.rotation⁻¹ Φ.offset) = x
  have hx : Φ.rotation⁻¹ (Φ.rotation x) = x := Φ.rotation.symm_apply_apply x
  rw [map_add_of_mem_hyperoctahedral hS, map_smul_of_mem_hyperoctahedral hS,
    hx, smul_add, smul_smul, ← zpow_add₀ L_ne_zero,
    neg_add_cancel, zpow_zero, one_smul, add_neg_cancel_right]
theorem onSpace_inverseMotion_onSpace (y : AmbientSpace) :
    Φ.onSpace ((inverseMotion Φ).onSpace y) = y := by
  have hS := Φ.rotation_mem
  have hneg : ∀ v : AmbientSpace, Φ.rotation (-v) = -Φ.rotation v := fun v => by
    simpa using map_smul_of_mem_hyperoctahedral hS (-1) v
  change (D.L : ℝ) ^ e.shift • Φ.rotation ((D.L : ℝ) ^ (-e.shift) • Φ.rotation⁻¹ y +
    -((D.L : ℝ) ^ (-e.shift) • Φ.rotation⁻¹ Φ.offset)) + Φ.offset = y
  have hinv : ∀ v : AmbientSpace, Φ.rotation (Φ.rotation⁻¹ v) = v :=
    fun v => Φ.rotation.apply_symm_apply v
  have hc : ∀ v : AmbientSpace, (D.L : ℝ) ^ e.shift • (D.L : ℝ) ^ (-e.shift) • v = v := fun v => by
    rw [smul_smul, ← zpow_add₀ L_ne_zero, add_neg_cancel, zpow_zero, one_smul]
  rw [map_add_of_mem_hyperoctahedral hS, hneg, map_smul_of_mem_hyperoctahedral hS,
    map_smul_of_mem_hyperoctahedral hS, hinv, hinv, smul_add, smul_neg, hc, hc,
    neg_add_cancel_right]
theorem invFun_eq_of_leftInverse_of_rightInverse {α β : Type*} [Nonempty α] {f : α → β}
    {g : β → α} (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f) :
    Function.invFun f = g := by
  funext y
  have h := Function.leftInverse_invFun hl.injective (g y)
  rwa [hr y] at h
def torusReturn (v : e.target.Torus) : D.Torus :=
  transport (F := fun X : GluingSetup => X.Torus) e.target_neg ((inverseMotion Φ).onTorus v)
theorem torusReturn_torusProj (y : AmbientSpace) :
    torusReturn Φ (torusProj (PeriodicLattice.torusSide D.L (e.target.m : ℕ)) y) =
      torusProj (PeriodicLattice.torusSide D.L (D.m : ℕ)) ((inverseMotion Φ).onSpace y) := by
  have h := (inverseMotion Φ).onTorus_torusProj y
  have h' := transport_torusProj e.target_neg ((inverseMotion Φ).onSpace y)
  rw [← h'] at *
  exact congrArg (transport (F := fun X : GluingSetup => X.Torus) e.target_neg) h
theorem torusReturn_leftInverse : Function.LeftInverse (torusReturn Φ) Φ.onTorus := by
  intro u
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  rw [Φ.onTorus_torusProj, torusReturn_torusProj, inverseMotion_onSpace_onSpace]
theorem torusReturn_rightInverse : Function.RightInverse (torusReturn Φ) Φ.onTorus := by
  intro v
  obtain ⟨y, rfl⟩ := TestFunctions.torusProj_surjective _ v
  exact (congrArg Φ.onTorus (torusReturn_torusProj Φ y)).trans ((Φ.onTorus_torusProj _).trans
    (congrArg _ (onSpace_inverseMotion_onSpace Φ y)))
theorem scaledMotionInverse_holds : ScaledMotionInverseClaim := by
  intro D e Φ
  refine ⟨⟨inverseMotion Φ, rfl, ?_⟩, ⟨inverseMotion Φ, rfl, ?_⟩⟩
  · exact (invFun_eq_of_leftInverse_of_rightInverse (inverseMotion_onSpace_onSpace Φ)
      (onSpace_inverseMotion_onSpace Φ)).symm
  · funext v
    change _ = transport (F := fun X : GluingSetup => X.Torus) e.target_neg.symm
      (Function.invFun Φ.onTorus v)
    rw [invFun_eq_of_leftInverse_of_rightInverse (torusReturn_leftInverse Φ)
      (torusReturn_rightInverse Φ)]
    exact (transport_symm_transport (F := fun X : GluingSetup => X.Torus) e.target_neg _).symm
end ScaledMotionInverse
end SourcesAndGluing
end YangMills.Construction
end
