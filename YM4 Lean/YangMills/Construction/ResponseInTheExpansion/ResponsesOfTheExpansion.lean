import YangMills.Construction.ResponseInTheExpansion.CurvatureOnTheBareTorus
import YangMills.Construction.ResponseInTheExpansion.JointLawOfTheChain
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightHasTheExpansionOfTheResponse
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields
open YangMills.Construction.StepCosts YangMills.Construction.WeightedResponses
variable {n : ℕ}
def conditionalMean (ℓ : StepParameters) (y : ℝ) (D : TorusFunctional) [NeZero n] (V : TorusField n)
    (F : TorusField (n * ℓ.side) → BaseChoice ℓ.side n → ℝ) : ℝ :=
  (∫ W, D (n * ℓ.side) W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V * F W b
      ∂(fieldHaar (n * ℓ.side))) /
    kernelImage ℓ y D n V
def bondScoresAtSite (ℓ : StepParameters) (y : ℝ) (W : TorusField (n * ℓ.side)) (V : TorusField n)
    (b : BaseChoice ℓ.side n) (Y : TorusSite n) : ℝ :=
  ∑ i : Fin 4, (bondScore ℓ y W V b (Y, i) + bondScore ℓ y W V b (Y - unitStep n i, i))
def stepColdResponse (ℓ : StepParameters) (y α : ℝ) (t : ℕ) (D : TorusFunctional)
    (P : ColdResponse ℓ.side t) : ColdResponse ℓ.side (t + 1) := fun n _ Y V h =>
  conditionalMean ℓ y D V fun W b =>
    ∑ z ∈ sitesInBlocks ℓ.side {Y}, P (n * ℓ.side) z W h +
      ℓ.coupling / 2 * α * blockMean ℓ.side (t + 1) n Y h * bondScoresAtSite ℓ y W V b Y
def coldResponseChain (ℓ : StepParameters) (β : ℝ) (x α : ℕ → ℝ) : (t : ℕ) → ColdResponse ℓ.side t
  | 0 => wilsonColdResponse ℓ.side
  | t + 1 => stepColdResponse ℓ (x t) (α t) t (chainFunctional ℓ β x t) (coldResponseChain ℓ β x α t)
def bondBlockMean (L : ℕ) [NeZero L] (t n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide L t n))
    (c : TorusBond n) : ℝ :=
  (blockMean L t n c.1 h + blockMean L t n (c.1 + unitStep n c.2) h) / 2
def chainMark (ℓ : StepParameters) (x α : ℕ → ℝ) :
    (s n : ℕ) → [NeZero n] → PlaquetteWeight (fineSide ℓ.side s n) → ChainSample ℓ s n → ℝ
  | 0, _, _, h, W => curvatureObservable h W
  | s + 1, n, _, h, u => chainMark ℓ x α s (n * ℓ.side) h u.1 +
      ∑ c : TorusBond n, ℓ.coupling * α s * bondBlockMean ℓ.side (s + 1) n h c *
        bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c
end YangMills.Construction.ResponseInTheExpansion
end
