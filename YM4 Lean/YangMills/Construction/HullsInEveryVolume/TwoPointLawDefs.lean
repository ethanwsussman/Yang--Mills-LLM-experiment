import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.TwoPointLaw
def twoPointDecayRate (P : RenormalizationStepParameters.ParameterAssignment) : ℝ :=
  (1 / 16) * min (P.κ * P.threshold ^ 2)
    (min (P.κ₁ * P.threshold ^ 2) (min P.cE (min P.gasRate (Real.log P.side / (2 * P.B)))))
def displacementToPlaquette {N : ℕ} (x : TorusFields.TorusSite N) (p : TorusFields.TorusPlaquette N) (i : Fin 4) : ℝ :=
  let d : ℝ := ((p.1 i).val : ℝ) + (if i = p.2.1 then 1 / 2 else 0) + (if i = p.2.2 then 1 / 2 else 0) - ((x i).val : ℝ)
  d - N * round (d / N)
def scaledTestWeight (L K s : ℕ) (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℤ) (N : ℕ) :
    WeightedResponses.PlaquetteWeight N :=
  fun p => φ fun i => displacementToPlaquette (TorusFields.siteOfInt fun j => (L : ℤ) ^ K * c j) p i / (L : ℝ) ^ s
abbrev OrientedPlaquette : Type := {p : (Fin 4 → ℤ) × Fin 4 × Fin 4 // p.2.1 < p.2.2}
def plaquetteBarycenter (p : OrientedPlaquette) (i : Fin 4) : ℝ :=
  (p.1.1 i : ℝ) + (if i = p.1.2.1 then 1 / 2 else 0) + (if i = p.1.2.2 then 1 / 2 else 0)
end YangMills.Construction.TwoPointLaw
end
