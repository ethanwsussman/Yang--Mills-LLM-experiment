import YangMills.Construction.Torus.MatrixOfThePairScaledSquare
import YangMills.Construction.Weighted.GivenChain
import YangMills.Construction.Weighted.GreenSquareConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted.ScaledMatrixBound
def Statement : Prop :=
  ∀ G : GivenChain,
    8 * (4 * Real.log (G.data.L : ℝ) + 1) / greenDecayRate 4 G.data.L ≤
        (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) →
      ∀ (W : Set G.data.Space) (𝔟 : Set G.data.Bond), G.chain.IsAdmissiblePair W 𝔟 →
        ∀ y y' : ↥G.chain.allSites,
          (y : G.data.Space) ∈ G.chain.sitesIn W →
            (y' : G.data.Space) ∈ G.chain.sitesIn W →
              |G.chain.admissibleScaledMatrix W 𝔟 y y'| ≤
                upperBoundConst 4 G.data.L *
                  Real.exp (-(1 / 2 * greenDecayRate 4 G.data.L *
                    G.chain.weightedDistance (y : G.data.Space) (y' : G.data.Space)))
end YangMills.Construction.Weighted.ScaledMatrixBound
