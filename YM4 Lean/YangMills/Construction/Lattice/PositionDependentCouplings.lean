import YangMills.Construction.Lattice.CubePartitionsAndRegions
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.PeriodicLattice
structure IsSymmetricMollifier (ψ : (Fin 4 → ℝ) → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ ψ
  hasCompactSupport : HasCompactSupport ψ
  nonneg : ∀ u, 0 ≤ ψ u
  integral_eq_one : ∫ u, ψ u = 1
  comp_perm : ∀ (σ : Equiv.Perm (Fin 4)) (u : Fin 4 → ℝ), ψ (u ∘ σ) = ψ u
  update_neg : ∀ (μ : Fin 4) (u : Fin 4 → ℝ), ψ (Function.update u μ (-u μ)) = ψ u
  tsupport_subset : tsupport ψ ⊆ {u | supNormVec u ≤ 1 / 4}
def symmetricMollifier : (Fin 4 → ℝ) → ℝ := Classical.epsilon IsSymmetricMollifier
variable {L m : ℕ}
def regionSizeExponent (K m' v j : ℕ) (Λ : Set (FourTorus L m)) : ℕ :=
  open Classical in
  if m' + v + j ≤ m + K ∧ IsPartitionRegion (scaledCubeIndex K j (m' + v)) Λ then m' + v else m'
def regionSize (K m' v j : ℕ) (Λ : Set (FourTorus L m)) : ℝ :=
  (L : ℝ) ^ regionSizeExponent K m' v j Λ
def supDistToComplement (K m' j : ℕ) (Λ : Set (FourTorus L m)) (x : FourTorus L m) : ℝ≥0∞ :=
  ENNReal.ofReal ((L : ℝ) ^ levelDepth K j) *
    TorusMetric.setSupDist {x} (complementRegion (coarseCubeIndex K m' j) Λ)
def smoothedRegionProfile (K m' v j : ℕ) (Λ : Set (FourTorus L m)) (x : FourTorus L m) : ℝ :=
  ∫ u : Fin 4 → ℝ, symmetricMollifier u *
    Set.indicator
      {w : Fin 4 → ℝ | ENNReal.ofReal (regionSize K m' v j Λ / 2) ≤
        supDistToComplement K m' j Λ (shiftBy L m K j x (-(regionSize K m' v j Λ • w)))}
      (fun _ => (1 : ℝ)) u
def smoothedRegionInterior (K m' v j : ℕ) (Λ : Set (FourTorus L m)) : Set (FourTorus L m) :=
  peelCubeLayer (scaledCubeIndex K j (regionSizeExponent K m' v j Λ)) Λ
def localInverseCoupling (K m' : ℕ) (β : ℝ) (b : ℕ → ℝ) (v : ℕ → ℕ)
    (Λ : ℕ → Set (FourTorus L m)) : ℕ → FourTorus L m → ℝ
  | 0, _ => β
  | j + 1, x => localInverseCoupling K m' β b v Λ j x -
      b (j + 1) * smoothedRegionProfile K m' (v (j + 1)) (j + 1) (Λ (j + 1)) x
def localCoupling (K m' : ℕ) (β : ℝ) (b : ℕ → ℝ) (v : ℕ → ℕ) (Λ : ℕ → Set (FourTorus L m))
    (j : ℕ) (x : FourTorus L m) : ℝ :=
  localInverseCoupling K m' β b v Λ j x ^ (-(1 / 2) : ℝ)
end YangMills.Construction.PeriodicLattice
