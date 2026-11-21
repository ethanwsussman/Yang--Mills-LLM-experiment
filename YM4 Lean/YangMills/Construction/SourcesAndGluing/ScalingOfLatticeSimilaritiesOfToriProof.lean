import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfTori
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusLifts YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace ScaledMotionDilationOfTori
theorem descendedMap_properties_of_side {L m : ℕ} {b : ℤ} {S : AmbientSpace → AmbientSpace}
    {w : AmbientSpace} {ℓ' : ℝ}
    (hℓ : ℓ' = (L : ℝ) ^ b * PeriodicLattice.torusSide L m) (h : ScaledMotionDescends L m b S w) :
    Function.Bijective (descendedMap (PeriodicLattice.torusSide L m) ℓ' (scaledMotion L b S w)) ∧
      (∀ u v : Torus4 (PeriodicLattice.torusSide L m),
        torusEuclidNorm (descendedMap (PeriodicLattice.torusSide L m) ℓ' (scaledMotion L b S w) u -
            descendedMap (PeriodicLattice.torusSide L m) ℓ' (scaledMotion L b S w) v) =
          (L : ℝ) ^ b * torusEuclidNorm (u - v)) ∧
      ∀ (u : Torus4 (PeriodicLattice.torusSide L m)) (z : AmbientSpace),
        descendedMap (PeriodicLattice.torusSide L m) ℓ' (scaledMotion L b S w)
            (u + torusProj (PeriodicLattice.torusSide L m) z) =
          descendedMap (PeriodicLattice.torusSide L m) ℓ' (scaledMotion L b S w) u +
            torusProj ℓ' ((L : ℝ) ^ b • S z) := by
  subst hℓ
  obtain ⟨-, -, -, hbij, -, -, hdist, hadd⟩ := h
  exact ⟨hbij, hdist, hadd⟩
theorem torusDilationOfScaledMotions_holds (hLifts : LiftsAndDescendedMaps.Statement)
    (hSpace : ScaledMotionDilationOfSpaceClaim) : TorusDilationOfScaledMotions.Statement := by
  intro D e Φ
  obtain ⟨-, -, hadd, hstep, himage⟩ := hSpace D e Φ
  obtain ⟨hbij, hdist, hvec⟩ := descendedMap_properties_of_side e.torusSide_target
    ((hLifts D.toStandingParameters).2.2.2.2.1 e.shift Φ.rotation Φ.offset e.one_le_side_add
      Φ.rotation_mem)
  have hvec' : ∀ u z, Φ.onTorus (D.translateBy u z) =
      e.target.translateBy (Φ.onTorus u) ((D.L : ℝ) ^ e.shift • Φ.rotation z) := hvec
  refine ⟨hbij, hdist, hvec', fun u μ => ?_, ?_⟩
  · have hz : (D.L : ℝ) ^ e.shift • Φ.rotation (D.mesh • stdBasis μ) =
        ((((Φ.signs μ : ℤˣ) : ℤ) : ℝ) * e.target.mesh) • stdBasis (Φ.perm μ) :=
      add_left_cancel ((hadd 0 _).symm.trans (hstep 0 μ))
    rw [hvec', hz]
  · have hD := (hLifts D.toStandingParameters).2.2.2.2.2
    have hI := (hLifts e.target.toStandingParameters).2.2.2.2.2
    have hlift : Φ.onTorus '' (torusProj (PeriodicLattice.torusSide D.L (D.m : ℕ)) ''
          (D.gridPoints : Set AmbientSpace)) =
        torusProj (PeriodicLattice.torusSide D.L (e.target.m : ℕ)) ''
          (Φ.onSpace '' (D.gridPoints : Set AmbientSpace)) := by
      rw [image_image, image_image]
      exact image_congr fun x _ => Φ.onTorus_torusProj x
    have hD' : (D.periodicLattice : Set D.Torus) =
        torusProj (PeriodicLattice.torusSide D.L (D.m : ℕ)) '' (D.gridPoints : Set AmbientSpace) :=
      hD.1.symm
    rw [hD']
    exact hlift.trans
      ((congrArg (torusProj (PeriodicLattice.torusSide D.L (e.target.m : ℕ)) '' ·) himage).trans hI.1)
end ScaledMotionDilationOfTori
end YangMills.Construction.SourcesAndGluing
end
