import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def IsTorusPeriod (L m : ℕ) (w : Fin 4 → ℝ) : Prop :=
  ∃ n : Fin 4 → ℤ, ∀ μ, w μ = (n μ : ℝ) * torusSide L m
def shiftByVector (w : Fin 4 → ℝ) (A : Set (Fin 4 → ℝ)) : Set (Fin 4 → ℝ) :=
  (fun v => v + w) '' A
def ComponentBoxIndependentOfCube : Prop :=
  ∀ L m : ℕ, Odd L → 13 ≤ L → 0 < m →
    ∀ i : ℤ, -(m : ℤ) ≤ i → 100 * meshSize L i < torusSide L m →
      ∀ X C : Set (FourTorus L m), IsPartitionRegion i X → C ∈ regionComponents i X →
        ∀ y y' : Fin 4 → ℝ, LiesInCornerCube L m i C y → LiesInCornerCube L m i C y' →
          InjOn (torusProj (torusSide L m)) (cornerCube y (100 * meshSize L i)) ∧
          InjOn (torusProj (torusSide L m)) (cornerCube y' (100 * meshSize L i)) ∧
          (∃ w : Fin 4 → ℝ, IsTorusPeriod L m w ∧
            liftToCornerCube i C y' = shiftByVector w (liftToCornerCube i C y) ∧
            boundingBox (liftToCornerCube i C y') =
              shiftByVector w (boundingBox (liftToCornerCube i C y))) ∧
          torusProj (torusSide L m) '' boundingBox (liftToCornerCube i C y') =
            torusProj (torusSide L m) '' boundingBox (liftToCornerCube i C y) ∧
          componentBox i C = torusProj (torusSide L m) '' boundingBox (liftToCornerCube i C y)
end YangMills.Construction.PeriodicLattice
