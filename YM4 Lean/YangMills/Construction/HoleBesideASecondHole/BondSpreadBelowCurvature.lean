import YangMills.Construction.HoleBesideASecondHole.SquareGoesDown
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BondContours
open YangMills.Construction.BlockAverages
open YangMills.Construction.LumpContours
open YangMills.Construction.SquareDescent
variable {F : BlockFrame}
def blockPairPlaquettes {j : ℕ} (c : F.Site (j + 1) × Fin 4) : Finset (F.Site j × Fin 4 × Fin 4) :=
  cutPlaquettes (sitesBelow j c.1 ∪ sitesBelow j (c.1 + unitStep (j + 1) c.2))
def ContourVarianceCurvatureBound : Prop :=
  (∀ (F : BlockFrame) (j : ℕ), j < F.top → Odd F.blockSide → IsAdmissibleAmbient F →
    ∀ (U : F.GaugeField j) (b : F.Site (j + 1) × Fin 4),
      contourVariance U b ≤ 16 * (F.blockSide : ℝ) ^ 2 * ∑ p ∈ blockPairPlaquettes b, plaquetteDefect U p ^ 2) ∧
  ∀ (F : BlockFrame) (j : ℕ) (U : F.GaugeField j) (x : F.Site j) (N : ℕ) (μ ν : Fin 4), μ < ν →
    squareHolonomyDefect U x N μ ν ≤ ∑ r ∈ Finset.range N, ∑ r' ∈ Finset.range N,
      plaquetteDefect U (x + r • unitStep j μ + r' • unitStep j ν, μ, ν)
end BondContours
end YangMills.Construction
end
