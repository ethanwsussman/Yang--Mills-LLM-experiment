import YangMills.Construction.InfiniteLattice.ObservablesAndIsometriesAtOneSpacing
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
theorem linearMap_mem_hypercubicGroup_iff (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) :
    (w : AmbientSpace →ₗ[ℝ] AmbientSpace) ∈ hypercubicGroup ↔ w ∈ hyperoctahedralLinearGroup := by
  rw [mem_hyperoctahedralLinearGroup_iff]
  constructor
  · intro hw
    obtain ⟨f, hf⟩ := exists_frameLinearMap_eq_of_mem_hypercubicGroup hw
    refine ⟨f.1, f.2, fun x μ => ?_⟩
    have hx := congrFun (LinearMap.congr_fun hf x) μ
    simpa [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector] using hx
  · rintro ⟨σ, s, hw⟩
    have heq : (w : AmbientSpace →ₗ[ℝ] AmbientSpace) = frameLinearMap (σ, s) :=
      LinearMap.ext fun x => funext fun μ => by
        simpa [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector] using hw x μ
    rw [heq]
    exact frameLinearMap_mem_hypercubicGroup _
theorem mem_hyperoctahedralLinearGroup_iff_signedPerm (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) :
    w ∈ hyperoctahedralLinearGroup ↔ ∃ (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℝ),
      (∀ μ, ε μ = 1 ∨ ε μ = -1) ∧ ∀ μ, w (basisVector μ) = ε μ • basisVector (σ μ) := by
  rw [← linearMap_mem_hypercubicGroup_iff, mem_hypercubicGroup_iff_signedPerm]
  rfl
theorem exists_linearEquiv_of_mem_hypercubicGroup {f : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hf : f ∈ hypercubicGroup) :
    ∃ w ∈ hyperoctahedralLinearGroup, (w : AmbientSpace →ₗ[ℝ] AmbientSpace) = f := by
  obtain ⟨g, rfl⟩ := exists_frameLinearMap_eq_of_mem_hypercubicGroup hf
  have hinj : Function.Injective (frameLinearMap g) := by
    intro x y hxy
    funext κ
    have hκ := congrFun hxy (g.1.symm κ)
    rcases Int.units_eq_one_or (g.2 (g.1.symm κ)) with hs | hs <;>
      simpa [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, hs] using hκ
  let w := LinearEquiv.ofInjectiveEndo (frameLinearMap g) hinj
  have hw : (w : AmbientSpace →ₗ[ℝ] AmbientSpace) = frameLinearMap g := LinearMap.ext fun _ => rfl
  refine ⟨w, (linearMap_mem_hypercubicGroup_iff w).mp ?_, hw⟩
  rw [hw]
  exact frameLinearMap_mem_hypercubicGroup g
theorem latticeMotions_eq_latticeMotions (a : ℝ) :
    latticeMotions a = affineHyperoctahedralMaps a := by
  ext f
  constructor
  · rintro ⟨w, hw, v, hv, hf⟩
    obtain ⟨w', hw', rfl⟩ := exists_linearEquiv_of_mem_hypercubicGroup hw
    exact ⟨w', hw', ⟨v, hv⟩, funext hf⟩
  · rintro ⟨w, hw, v, rfl⟩
    exact ⟨w, (linearMap_mem_hypercubicGroup_iff w).mpr hw, v, v.2, fun _ => rfl⟩
namespace LatticeSymmetry
variable (r : LatticeSymmetry a)
def pointPairMap (b : AmbientSpace × AmbientSpace) : AmbientSpace × AmbientSpace :=
  (r.toFun b.1, r.toFun b.2)
end LatticeSymmetry
end InfiniteLattice
end YangMills.Construction
