import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L : ℕ}
namespace CutoffTorus
def signedPermEuclidean (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) (z : Fin 4 → ℝ) :
    Fin 4 → ℝ :=
  fun μ => ((s μ : ℤ) : ℝ) * z (π μ)
theorem torusProj_signedPermEuclidean (m : ℕ) (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ)
    (z : Fin 4 → ℝ) :
    TorusMetric.torusProj (torusSide L m) (signedPermEuclidean π s z) =
      signedCoordinatePerm L m π s (TorusMetric.torusProj (torusSide L m) z) := by
  funext μ
  rcases Int.units_eq_one_or (s μ) with h | h <;>
    simp [TorusMetric.torusProj, signedCoordinatePerm, signedPermEuclidean, h]
end CutoffTorus
end YangMills.Construction.PeriodicLattice
end
