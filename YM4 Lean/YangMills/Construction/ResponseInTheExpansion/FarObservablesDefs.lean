import YangMills.Construction.ClusterExpansionOfAStep.GasIsAWeight
import YangMills.Construction.ResponseInTheExpansion.FarSpinsMoveAVariable
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open Dobrushin WeightedResponses StepGas StepSettings RenormalizationStepParameters TorusFields TorusLumps CoreColumns BlockAverages FreeEnergies
def HoldsAtEveryStepWithConstant (P : ℝ → ParameterAssignment → ∀ R : StepSetup, ResponseSetup R → Prop) : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∀ K : ResponseParameters, ∃ y₀ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y →
      ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = K → OnStepParameters T y A → P C T R A
variable {R : StepSetup} {n : ℕ} [NeZero n]
structure SeparatedWeights {ι : Type} (I : Finset ι) (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (D : ℕ) : Prop where
  weightNorm_le : ∀ i ∈ I, weightNorm R.params.side R.depth (f i) ≤ 1
  nonempty : ∀ i ∈ I, (upperSites (f i)).Nonempty
  range_le : 2 ^ 10 * R.range ≤ D
  eight_lt : 8 < D
  separated : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ Y ∈ thickening 2 (upperSites (f i)),
    ∀ Y' ∈ thickening 2 (upperSites (f j)), D ≤ supDist Y Y'
def totalLowerSites {ι : Type} (I : Finset ι) (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : ℝ :=
  ∑ i ∈ I, ((lowerSites (f i)).card : ℝ)
def lowerMajorant (A : ResponseSetup R) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω) : ℝ :=
  4 * lowerSizeConst A f * meanSiteScore A.score (lowerSites f) Yt ωt
def upperMajorant (A : ResponseSetup R) (G : GasGround R n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : ℝ :=
  4 * lowerSizeConst A f * meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2
open Classical in
def unionUpperSites {ι : Type} (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (J : Finset ι) :
    Finset (TorusSite n) :=
  J.biUnion fun j => upperSites (f j)
open Classical in
def unionLowerSites {ι : Type} (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (J : Finset ι) :
    Finset (TorusSite (n * R.params.side)) :=
  J.biUnion fun j => lowerSites (f j)
def gasMajorantProduct (A : ResponseSetup R) (G : GasGround R n) {ι : Type}
    (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (J : Finset ι) (σ : G.Config) : ℝ :=
  ∏ j ∈ J, (4 * lowerSizeConst A (f j) * spinScore A G (lowerSites (f j)) σ)
open Classical in
def gasMeanProduct (A : ResponseSetup R) (G : GasGround R n) {ι : Type}
    (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (J : Finset ι) (σ : G.Config) : ℝ :=
  ∏ j ∈ J, if G.pairConstraint.IsAdmissible σ then gasSupportMean A G (f j) σ else 0
def tiltActivity (G : GasGround R n) (c e : ℝ) (Q : Finset (TorusSite n)) (i : G.GasSpin) : ℝ :=
  open Classical in
  4 * G.spinActivity c i * if (R.range : ℝ) / (2 * R.params.side) ≤ setGap Q i.1.core then
    min 2 (e * Real.exp (-(R.params.rt * ((setGap Q i.1.core : ℝ) - 2) / 2 ^ 5))) else 2
def decayFromSet (G : GasGround R n) (Q : Finset (TorusSite n)) (i : G.GasSpin) : ℝ :=
  (i.1.core.card : ℝ) * Real.exp (-(R.params.rt / 2 ^ 6 * (setGap Q i.1.core : ℝ)))
end YangMills.Construction.ResponseInTheExpansion
end
