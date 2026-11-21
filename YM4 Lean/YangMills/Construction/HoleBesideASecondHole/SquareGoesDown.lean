import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import YangMills.Construction.HoleBesideASecondHole.MeanOfAProductOfGroupVariables
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace SquareDescent
open BlockAverages GroupMeans LumpContours
variable {F : BlockFrame}
def squarePath (n : ℕ) (μ ν : Fin 4) : List PathStep :=
  List.replicate n (μ, true) ++ List.replicate n (ν, true) ++ List.replicate n (μ, false) ++
    List.replicate n (ν, false)
def squareHolonomyDefect {j : ℕ} (A : F.GaugeField j) (x : F.Site j) (n : ℕ) (μ ν : Fin 4) : ℝ :=
  ‖((pathHolonomy A x (squarePath n μ ν) : UnitQuaternion) : ℍ[ℝ]) - 1‖
def contourHolonomy {j : ℕ} (U : F.GaugeField j) (b : F.Site (j + 1) × Fin 4) :
    (Fin 4 → ℤ) × Equiv.Perm (Fin 4) → UnitQuaternion :=
  fun e => pathHolonomy U (refineSite b.1) (bondContour F.blockSide e.1 e.2 b.2)
def contourVariance {j : ℕ} (U : F.GaugeField j) (b : F.Site (j + 1) × Fin 4) : ℝ :=
  variance (allContours F) (contourHolonomy U b)
def sumAroundSquare {j : ℕ} (g : F.Site j × Fin 4 → ℝ) (x : F.Site j) (n : ℕ) (μ ν : Fin 4) : ℝ :=
  ∑ r ∈ Finset.range n,
    (g (x + r • unitStep j μ, μ) + g (x + n • unitStep j μ + r • unitStep j ν, ν) +
      g (x + n • unitStep j μ + n • unitStep j ν - (r + 1) • unitStep j μ, μ) +
      g (x + n • unitStep j ν - (r + 1) • unitStep j ν, ν))
def SquareDescentEstimate : Prop :=
  ∀ (F : BlockFrame) (j : ℕ), j < F.top → Odd F.blockSide → ∀ (U : F.GaugeField j) (A : F.GaugeField (j + 1))
    (x : F.Site (j + 1)) (n : ℕ) (μ ν : Fin 4),
    squareHolonomyDefect A x n μ ν ≤
      average (centredCube F.blockSide)
          (fun h => squareHolonomyDefect U (refineSite x + siteOfCoords j h) (n * F.blockSide) μ ν) +
        sumAroundSquare (fun b => 2 * Real.sqrt (blockFit U A b) + 2 * contourVariance U b) x n μ ν +
        (2 * n : ℝ) * sumAroundSquare (contourVariance U) x n μ ν
end SquareDescent
end YangMills.Construction
end
