import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ThirdOrderOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.WeightsOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace CovarianceBounds
def FreezingThresholdsHold (T : StepParameters) : Prop :=
  ∃ S : ℝ, BoundsExpWeights T S ∧ exponentConstantThreshold T S ≤ T.Cs ∧ expansionConstantThreshold T S ≤ T.CE ∧
    1 ≤ T.blockIndex ∧ 2 ≤ T.n₀ ∧ 0 ≤ T.Ct ∧ 1 ≤ T.coupling
theorem eventually_freezingThresholdsHold (hW : ExpWeightSumsBounded) :
    EventuallyInParameters FreezingThresholdsHold := by
  intro a _
  refine ⟨0, fun L hL _ c _ => ⟨0, fun Ct hCt => ⟨1, one_pos, fun κ hκ _ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨1, fun m hm => ⟨1, one_pos, fun σ _ _ p _ => ?_⟩⟩⟩⟩⟩⟩
  obtain ⟨S, hS⟩ := hW L (κ / 4) hL (by positivity)
  refine ⟨exponentConstantThreshold ⟨a, L, c, Ct, κ, η₃, m, σ, p, 0, 0, 0, 0, 0⟩ S, fun Cs hCs E _ =>
    ⟨2, fun n₀ hn₀ => ⟨expansionConstantThreshold ⟨a, L, c, Ct, κ, η₃, m, σ, p, Cs, E, n₀, 0, 0⟩ S, fun CE hCE =>
      ⟨1, fun y hy => ⟨S, ?_, hCs, hCE, hm, hn₀, hCt, hy⟩⟩⟩⟩⟩
  intro F n hL' h2 hn z
  exact hS F n hL' h2 hn z
end CovarianceBounds
open CovarianceBounds in
theorem covarianceBounds_holds (hbe : CellExponentsBounded)
    (hbr : CentredExpansionsBounded) (hcv : exponentConvexityStatement)
    (hcmp : CellExponentsCloseEventually) (htr : expansionTransportStatement)
    (hw : ExpWeightSumsBounded) (hfz : stepFreezingStatement)
    (hthird : ThirdDerivLocalEventually) (hj : EventuallyInParametersCombines) :
    covarianceBoundsStatement := by
  obtain ⟨hand, hweak⟩ := hj
  have h1 := hand _ _ (hand _ _ (hand _ _ (hand _ _ (hand _ _ hbe hbr) hcv) hcmp) htr)
    (hand _ _ (eventually_freezingThresholdsHold hw) hthird)
  refine hweak _ _ ?_ h1
  rintro T hT ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, ⟨S, hS, hc1, hc2, hn1, hn2, hCt, hy⟩, e6⟩
  intro t x f F V hxy hrow htop hcold star
  refine ⟨e6 t x f F V hxy hrow htop hcold star, fun F' V' Y Y' r htop' hcold' hag => ?_⟩
  exact hfz T S hT hn1 hn2 hCt hy hT.chain_admissible.positivity.2.2.1 hS hc1 hc2 e1 e2 e3 e4 e5 t x f F F' V V' Y Y'
    r star hxy hrow htop htop' hcold hcold' hag
end YangMills.Construction.ColdStepAtMirrorFrames
end
