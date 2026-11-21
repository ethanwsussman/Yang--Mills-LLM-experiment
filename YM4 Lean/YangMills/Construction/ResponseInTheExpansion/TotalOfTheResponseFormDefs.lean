import YangMills.Construction.ResponseInTheExpansion.ColdImageAboveTheFrames
import YangMills.Construction.ResponseInTheExpansion.MeansOfTheSmoothMoves
import YangMills.Construction.SummableBoundsOfTheFlow.MeanInTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open ColdStepAtMirrorFrames Estimates StepSettings TorusLumps StepGas WeightedResponses
def blockFrameExcess (S : StepSetup) : TopLevelFamily := fun _ Y V =>
  frameDensity false S.params.coupling S.anchorRadius S.coupling S.frameReach Y V
def blockMeanLinearPart (S : StepSetup) : TopLevelFamily := fun _ Y V =>
  (coldHalfLawOf S).expectationOf ((coldHalfLawOf S).linearBlockPart Y) V
def blockMeanIncrement (S : StepSetup) : TopLevelFamily := fun _ Y V =>
  (coldHalfLawOf S).expectationOf ((coldHalfLawOf S).blockIncrement Y) V
def blockConditionalMean (S : StepSetup) (h : LocalDensity) : TopLevelFamily :=
  conditionalExpansionMean false S.params.coupling S.anchorRadius S.ballRadius S.coupling S.frameReach S.barrierFn
    (localFamilyOfDensity S.density) (localFamilyOfDensity h)
def blockMeanScoreTails (S : StepSetup) : TopLevelFamily := fun _ Y V =>
  ∑ i : Fin 4, ∑ back : Bool, ((coldHalfLawOf S).scoreRemainderAt (cellBond Y i back) 0 V +
    (coldHalfLawOf S).expectationOf ((coldHalfLawOf S).scoreRemainderIncrement (cellBond Y i back)) V)
variable {S : StepSetup}
def frameTerm (A : ResponseSetup S) : LocalDensity :=
  densityOfTopFamily S.params.side S.depth fun F Y V => -(A.coeff / S.coupling) * blockFrameExcess S F Y V
def linearTerm (A : ResponseSetup S) : LocalDensity :=
  densityOfTopFamily S.params.side S.depth fun F Y V => A.coeff / S.coupling * blockMeanLinearPart S F Y V
def incrementTerm (A : ResponseSetup S) : LocalDensity :=
  densityOfTopFamily S.params.side S.depth fun F Y V => A.coeff * blockMeanIncrement S F Y V
def remainderTerm (A : ResponseSetup S) : LocalDensity :=
  densityOfTopFamily S.params.side S.depth (blockConditionalMean S A.totalRemainder)
def scoreTailTerm (A : ResponseSetup S) : LocalDensity :=
  densityOfTopFamily S.params.side S.depth fun F Y V =>
    -(S.params.coupling / 2 * A.coeff * (S.coupling ^ 2)⁻¹) * blockMeanScoreTails S F Y V
def gasTerm (A : ResponseSetup S) : LocalDensity := fun n Y V =>
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    gasTermAtBlock A (coldCaseGround S V) Y (constOneWeight _)
def totalRemainderOfTerms (A : ResponseSetup S) : LocalDensity := fun n Y V =>
  frameTerm A n Y V + linearTerm A n Y V + remainderTerm A n Y V + scoreTailTerm A n Y V +
    gasTerm A n Y V
structure TermBounds (ℓ : TorusLumps.StepParameters) (e e₃ c : ℝ) (g : LocalDensity) : Prop where
  admissible : IsAdmissibleDensity ℓ g
  derivDecay : DerivDecay ℓ g fun k m => (if k = 3 then e₃ else e) / ℓ.weight m
  centered_compare : LocalComparison ℓ (centeredFamily g) fun m => c / ℓ.weight m
end YangMills.Construction.ResponseInTheExpansion
end
