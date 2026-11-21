import YangMills.Construction.ClusterExpansionOfAStep.SharesOnARegionOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps TorusShares StepCosts ColdChain
variable {n : ℕ}
def minimizingField (a ρ : ℝ) (L t : ℕ) (S : Finset (TorusSite n)) (V : TorusField n) : TorusField (n * L) :=
  fun x i =>
    chartedField (minimizingCoordinates a (cellsOfSites (torusFrame L t n) S)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x) i
def blockFitAt (L : ℕ) (W : TorusField (n * L)) (V : TorusField n) (c : TorusBond n) : ℝ :=
  blockFit (F := stepBlockFrame L n) (readAtLevel (stepBlockFrame L n) 0 W) (readAtLevel (stepBlockFrame L n) 1 V)
    (torusSiteInFrame (stepBlockFrame L n) 1 c.1, c.2)
open Classical in
def halfBlockFits (L : ℕ) (S : Finset (TorusSite n)) (W : TorusField (n * L)) (V : TorusField n)
    (Y : TorusSite n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin 4,
    ((if Y + TorusFields.unitStep n i ∈ S then blockFitAt L W V (Y, i) else 0) +
      (if Y - TorusFields.unitStep n i ∈ S then
        blockFitAt L W V (Y - TorusFields.unitStep n i, i) else 0))
def LevelShareSplits : Prop :=
  ∀ (a δ : ℝ) (L : ℕ) [NeZero L] (lam ρ σA cg : ℝ) (N : ℕ → ℝ), 0 < a → Odd L →
    ColdChainConstants a δ L lam ρ σA cg N →
    ∀ (t n : ℕ) [NeZero n] (S : Finset (TorusSite n)) (V : TorusField n) (s : ℝ) (Y : TorusSite n),
      64 ≤ n → 0 < s → s ≤ σA → IsLocallyOrthantClosed S 1024 → IsColdOn S s V → Y ∈ S →
      levelShare a L (t + 1) S Y V =
        ∑ y ∈ sitesInBlocks L {Y}, levelShare a L t (sitesInBlocks L S) y (minimizingField a ρ L t S V) +
          a * halfBlockFits L S (minimizingField a ρ L t S V) V Y
end YangMills.Construction.ClusterExpansionOfAStep
end
