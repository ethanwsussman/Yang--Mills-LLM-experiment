import YangMills.Construction.Torus.MatrixOfThePairScaledSquare
import YangMills.Construction.Weighted.GivenChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def PairOperatorFacts (W : Set D.Space) (𝔟 : Set D.Bond) : Prop :=
  IsUnit (B.admissibleOp W 𝔟) ∧
    (∀ f g : ↥(B.bareSpaceOn W),
      B.bareInner (B.admissibleGreen W 𝔟 f) g = B.bareInner f (B.admissibleGreen W 𝔟 g)) ∧
    (∀ f : ↥(B.bareSpaceOn W), f ≠ 0 → 0 < B.bareInner f (B.admissibleGreen W 𝔟 f)) ∧
    (∀ w w' : ↥(B.layerSpaceOn W),
      B.layerInner w (B.admissibleAvgGreenSq W 𝔟 w') =
        B.bareInner
          (B.admissibleGreen W 𝔟 (B.restrictBare W (B.avgOpAdjoint w)))
          (B.admissibleGreen W 𝔟 (B.restrictBare W (B.avgOpAdjoint w')))) ∧
    (∀ w w' : ↥(B.layerSpaceOn W),
      B.layerInner (B.admissibleAvgGreenSq W 𝔟 w) w' =
        B.layerInner w (B.admissibleAvgGreenSq W 𝔟 w')) ∧
    B.AdmissibleScaledMatrixEq W 𝔟
def initialBonds : Set D.Bond := TorusData.bondsMeeting (D.bareSites (B.stage 0))
def InitialPairFacts : Prop :=
  B.IsAdmissiblePair (B.stage 0) B.initialBonds ∧
    B.bareSpaceOn (B.stage 0) = B.bareSpace ∧
    (∀ f : ↥(B.bareSpaceOn (B.stage 0)),
      B.bareSpaceOnIncl (B.stage 0) (B.admissibleOp (B.stage 0) B.initialBonds f) =
        B.weightedLap (B.bareSpaceOnIncl (B.stage 0) f)) ∧
    (∀ f g : ↥B.bareSpace,
      B.bareInner (B.weightedLap f) g = B.bareInner f (B.weightedLap g)) ∧
    (∀ f : ↥B.bareSpace, f ≠ 0 → 0 < B.bareInner f (B.weightedLap f)) ∧
    IsUnit B.weightedLap ∧
    (∀ f : ↥(B.bareSpaceOn (B.stage 0)),
      B.bareSpaceOnIncl (B.stage 0)
          (B.admissibleGreen (B.stage 0) B.initialBonds f) =
        B.greenOp (B.bareSpaceOnIncl (B.stage 0) f)) ∧
    B.layerSpaceOn (B.stage 0) = ⊤ ∧
    ∀ w : ↥(B.layerSpaceOn (B.stage 0)),
      (B.admissibleAvgGreenSq (B.stage 0) B.initialBonds w : B.LayerFn) =
        B.avgGreenSq w
end SeparatedChain
def AdmissiblePairOperators : Prop :=
  ∀ G : GivenChain,
    (∀ (W : Set G.data.Space) (𝔟 : Set G.data.Bond),
      G.chain.IsAdmissiblePair W 𝔟 → G.chain.PairOperatorFacts W 𝔟) ∧
      G.chain.InitialPairFacts
end YangMills.Construction.Weighted
