import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
namespace InfiniteLattice
def InducesTorusMap (L m : ℕ) (f : AmbientSpace → AmbientSpace)
    (g : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m) : Prop :=
  ∀ x, g (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x) =
    TorusMetric.torusProj (PeriodicLattice.torusSide L m) (f x)
def torusAffineMap (L m : ℕ) (w : AmbientSpace →ₗ[ℝ] AmbientSpace) (v : AmbientSpace) :
    PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m :=
  Classical.epsilon (InducesTorusMap L m fun x => w x + v)
theorem torusAffineMap_torusProj (L m : ℕ) {w : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hypercubicGroup) (v x : AmbientSpace) :
    torusAffineMap L m w v (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) (w x + v) := by
  obtain ⟨r, rfl⟩ := exists_frameLinearMap_eq_of_mem_hypercubicGroup hw
  refine Classical.epsilon_spec (p := InducesTorusMap L m fun x => frameLinearMap r x + v)
    ⟨fun y => r.torusEquiv L m y + TorusMetric.torusProj (PeriodicLattice.torusSide L m) v,
      fun x => ?_⟩ x
  funext μ
  rcases Int.units_eq_one_or (r.2 μ) with hs | hs <;>
    simp [TorusMetric.torusProj, PeriodicLattice.SignedFrame.torusEquiv,
      PeriodicLattice.signedCoordinatePerm, frameLinearMap,
      PeriodicLattice.SignedFrame.actOnVector, hs]
end InfiniteLattice
end
end YangMills.Construction
