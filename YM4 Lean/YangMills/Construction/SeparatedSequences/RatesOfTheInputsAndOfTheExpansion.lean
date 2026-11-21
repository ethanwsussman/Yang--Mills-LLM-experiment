import YangMills.Construction.Dirichlet.GreenOperatorEstimates
import YangMills.Construction.DirichletOperator.PropagatorOfASequenceOfRegions
import YangMills.Construction.SeparatedSequences.InverseGreenConstants
import YangMills.Construction.Weighted.InverseExpansionConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SeparatedSequences
def sequencePropagatorRate (L : ℕ) : ℝ :=
  (YangMills.Construction.Propagator.SequenceOfRegions.chosenConstants L).δ
def propagatorInverseRate (L : ℕ) : ℝ :=
  YangMills.Construction.SeparatedSequences.inverseDecayRate 4 L (sequencePropagatorRate L)
    (YangMills.Construction.Propagator.SequenceOfRegions.chosenConstants L).B
def minimalInputRate (L : ℕ) : ℝ :=
  min 1 (min (1 / 4 * YangMills.Construction.DirichletGreen.FourDimensional.decayRate L)
    (min (1 / 2 * YangMills.Construction.Weighted.expansionDecayRate 4 L)
      (min (sequencePropagatorRate L)
        (min (1 / 2 * propagatorInverseRate L)
          ((1 - ((L : ℝ) ^ 2)⁻¹) / (32 * 4 * ((L : ℝ) ^ 2 + 1)))))))
def decayingInputRate (L : ℕ) : ℝ := 1 / 2 * minimalInputRate L
def baseShellRate : ℝ := 1 / 4 * Real.log (53 / 52)
def blockOperatorRate (L : ℕ) : ℝ := 1 / 2 * min (decayingInputRate L) baseShellRate
def operatorExpansionRate (L : ℕ) : ℝ := 1 / 4 * blockOperatorRate L
end SeparatedSequences
end YangMills.Construction
