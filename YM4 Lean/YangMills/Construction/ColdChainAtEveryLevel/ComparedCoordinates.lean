import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ColdChainAtEveryLevel.LocalRestrictionsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F F' : BlockFrame}
def offsetChartGapNorm (S : Finset F.Cell) (R : F.FieldChain) (z Y : F.Cell) (Y' : F'.Cell) (A : ChainChart F)
    (A' : ChainChart F') : ℝ :=
  localNorm S R (chartMove A (chartAtSameOffsets Y Y' A') (-1)) (oneSiteWeights F) z
def cellAtSameOffset (Y : F.Cell) (Y' : F'.Cell) (x : F.Cell) : F'.Cell :=
  Y' + siteOfCoords F'.top fun i => ((x - Y) i).valMinAbs
def depthSiteAtSameOffset (Y : F.Cell) (Y' : F'.Cell) (x : F.Site F.depth) : F'.Site F'.depth :=
  cellCentre F'.depth Y' + siteOfCoords F'.depth fun i => ((x - cellCentre F.depth Y) i).valMinAbs
structure AreComparedRepresentations {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Finset F.Cell)
    (R : F.FieldChain) (Y : F.Cell) (Y' : F'.Cell) (B : Finset (F.Site F.top × Fin 4)) (Cm : ℕ → ℝ)
    (U : ChainChart F) (U' : ChainChart F')
    (Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E)
    (Φ' : ChainChart F' → (F'.Site F'.top → Fin 4 → imaginaryQuaternions) → E) : Prop where
  value : ‖Φ U (fun _ _ => 0) - Φ' U' (fun _ _ => 0)‖ ≤ Cm 0 * offsetChartGapNorm S R Y Y Y' U U'
  deriv : ∀ (m : ℕ) (A : Fin m → ChainChart F) (A' : Fin m → ChainChart F')
    (e : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions)
    (e' : Fin m → F'.Site F'.top → Fin 4 → imaginaryQuaternions), 1 ≤ m →
    (∀ l, ∀ b ∈ B, e l b.1 b.2 = e' l (cellAtSameOffset Y Y' b.1) b.2) →
    ‖localIteratedDeriv Φ U A e - localIteratedDeriv Φ' U' A' e'‖ ≤
      Cm m * (offsetChartGapNorm S R Y Y Y' U U' * ∏ l, localDirectionSize S R B Y (A l) (e l) +
        ∑ l, offsetChartGapNorm S R Y Y Y' (A l) (A' l) * ∏ l' ∈ Finset.univ.erase l,
          (localDirectionSize S R B Y (A l') (e l') + offsetChartGapNorm S R Y Y Y' (A l') (A' l')))
end YangMills.Construction.BlockAverages
end
