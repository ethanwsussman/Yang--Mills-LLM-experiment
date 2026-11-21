import YangMills.Construction.Lattice.PositionDependentCouplings
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def smoothedIndicator (n : ℕ) (s : ℝ) (Z : Set (FourTorus L m)) (x : FourTorus L m) : ℝ :=
  ∫ u : Fin 4 → ℝ, symmetricMollifier u *
    Set.indicator
      {w : Fin 4 → ℝ | ENNReal.ofReal (((n : ℝ) - 1 / 2) * s) ≤
        TorusMetric.setSupDist {x - TorusMetric.torusProj (torusSide L m) (s • w)} Z}
      (fun _ => (1 : ℝ)) u
def regionCutoffFn (i : ℤ) (n : ℕ) (Y : Set (FourTorus L m)) (x : FourTorus L m) : ℝ :=
  smoothedIndicator n (meshSize L i) (complementRegion i Y) x
end YangMills.Construction.PeriodicLattice
