import YangMills.Construction.ClusterExpansionOfAStep.IsometriesCarryTheKernel
import YangMills.Construction.ResponseInTheExpansion.ResponsesOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def iteratedLift (L : ℕ) : ℕ → TorusFields.TorusIsometry → TorusFields.TorusIsometry
  | 0, g => g
  | t + 1, g => iteratedLift L t (g.scaledLift L)
def doubledSiteImage {m : ℕ} (g : TorusFields.TorusIsometry) (d : TorusFields.TorusSite (2 * m)) :
    TorusFields.TorusSite (2 * m) :=
  fun i => (g.axisSign i : ZMod (2 * m)) * d (g.axisPerm i) + 2 * (g.offset i : ZMod (2 * m))
def WeightTransported {m : ℕ} (g : TorusFields.TorusIsometry) (w w' : WeightedResponses.PlaquetteWeight m) : Prop :=
  ∀ p p' : WeightedResponses.OrientedPlaquette m,
    WeightedResponses.doubledBarycentre p'.1 = doubledSiteImage g (WeightedResponses.doubledBarycentre p.1) → w' p'.1 = w p.1
def responseIsometryInvariantStatement : Prop :=
  ∀ P : TorusLumps.StepParameters, P.Admissible → ∀ (β : ℝ) (x c : ℕ → ℝ) (t n : ℕ) [NeZero n], P.n₀ ≤ n →
    ∀ (g : TorusFields.TorusIsometry) (V V' : TorusFields.TorusField n)
    (w w' : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide P.side t n)) (y : TorusFields.TorusSite n),
    g.Transports V V' → WeightTransported (iteratedLift P.side t g) w w' →
    ResponseInTheExpansion.coldResponseChain P β x c t n (g.mapSite y) V' w' = ResponseInTheExpansion.coldResponseChain P β x c t n y V w
end YangMills.Construction.SmallTorusCopies
end
