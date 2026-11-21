import YangMills.Construction.ResponseInTheExpansion.JointLawOfTheChain
import YangMills.Construction.RunningCouplingSlope.CoefficientOfATotal
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.TotalDensityFlow
def sideFilter (L : ℕ) : Filter ℕ := Filter.map (fun q : ℕ => 2 * L ^ q) Filter.atTop
def logRatio (D : TorusLumps.TorusFunctional) : SlopeCoefficient.GaugeTotal :=
  fun n V => Real.log (D n V) - Real.log (D n (TorusFields.trivialField n))
def IsPosNearTrivial (L : ℕ) (D : TorusLumps.TorusFunctional) : Prop :=
  ∀ᶠ n in sideFilter L, ∀ᶠ V in 𝓝 (TorusFields.trivialField n), 0 < D n V
def HasNextCoupling (L : ℕ) (D : TorusLumps.TorusFunctional) (x' : ℝ) : Prop :=
  IsPosNearTrivial L D ∧ SlopeCoefficient.HasSlopeCoefficient (sideFilter L) (logRatio D) (-x')
structure IsFlowUpTo (ℓ : TorusLumps.StepParameters) (β : ℝ) (t : ℕ) (x : ℕ → ℝ) : Prop where
  init : x 0 = β
  pos : ∀ k < t, 0 < x k
  succ : ∀ k < t, HasNextCoupling ℓ.side (WeightedResponses.chainFunctional ℓ β x (k + 1)) (x (k + 1))
open Classical in
def nextCoupling (L : ℕ) (x : ℝ) (D : TorusLumps.TorusFunctional) : ℝ :=
  if h : ∃ x' : ℝ, HasNextCoupling L D x' then h.choose else x
def flowData (ℓ : TorusLumps.StepParameters) (β : ℝ) : ℕ → ℝ × TorusLumps.TorusFunctional
  | 0 => (β, TorusLumps.wilsonWeight β)
  | t + 1 => (nextCoupling ℓ.side (flowData ℓ β t).1
        (TorusLumps.kernelImage ℓ (flowData ℓ β t).1 (flowData ℓ β t).2),
      TorusLumps.kernelImage ℓ (flowData ℓ β t).1 (flowData ℓ β t).2)
def coupling (ℓ : TorusLumps.StepParameters) (β : ℝ) (k : ℕ) : ℝ := (flowData ℓ β k).1
def IsDefinedUpTo (ℓ : TorusLumps.StepParameters) (β : ℝ) (t : ℕ) : Prop :=
  IsFlowUpTo ℓ β t (coupling ℓ β)
end YangMills.Construction.TotalDensityFlow
end
