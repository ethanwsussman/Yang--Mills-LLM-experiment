import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.DistancesOfBlocks
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.LocalTermsOfAMeasureForm
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F F' : BlockFrame}
def bondsNearCell (F : BlockFrame) (Y : F.Cell) (r : ℕ) : Finset ↥(chordBonds (finiteCells F)) :=
  open Classical in Finset.univ.filter fun b => 2 * cellSupDist (enclosingCell b.1.1) Y ≤ r
def cellsNearCell (F : BlockFrame) (Y : F.Cell) (r : ℕ) : Finset F.Cell :=
  open Classical in (finiteCells F).filter fun z => 8 * cellSupDist z Y < r
def BondsMatchByOffset (Y : F.Cell) (Y' : F'.Cell) (r : ℕ)
    (e : ↥(bondsNearCell F Y r) ≃ ↥(bondsNearCell F' Y' r)) : Prop :=
  ∀ b, ∃ (h o : Fin 4 → ℤ) (i : Fin 4), o ∈ centredCube F.blockSide ∧ WithinRadius r h ∧
    b.1.1 = fineBondAt Y h o i ∧ (e b).1.1 = fineBondAt Y' h o i
def CellsMatchByOffset (Y : F.Cell) (Y' : F'.Cell) (r : ℕ)
    (φ : {z // z ∈ cellsNearCell F Y r} ≃ {z // z ∈ cellsNearCell F' Y' r}) : Prop :=
  ∀ z, ∃ h : Fin 4 → ℤ, (∀ i, 8 * |h i| ≤ (r : ℤ)) ∧ z.1 = Y + siteOfCoords F.top h ∧
    (φ z).1 = Y' + siteOfCoords F'.top h
def TermsCloseOnNearBonds (ρ c ε x κ : ℝ) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ)
    (e : ↥(bondsNearCell F Y r) ≃ ↥(bondsNearCell F' Y' r))
    (φ : {z // z ∈ cellsNearCell F Y r} ≃ {z // z ∈ cellsNearCell F' Y' r})
    (G : F.Cell → StepVariable (finiteCells F) → ℝ) (G' : F'.Cell → StepVariable (finiteCells F') → ℝ) :
    Prop :=
  ∀ (z : {z // z ∈ cellsNearCell F Y r}), ∀ ξ ∈ openPolyball ↥(bondsNearCell F Y r) ρ,
    |G' (φ z).1 (pushforwardField (fun k => (e k).1) ξ) - G z.1 (pushforwardField (fun k => k.1) ξ)| ≤
      c * ε * (x * weightedSqNormNear κ (fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
        (blockDist F) z.1 ξ + 1) ∧
    ∀ k, bondGradNorm (fun ζ => G' (φ z).1 (pushforwardField (fun k => (e k).1) ζ) -
        G z.1 (pushforwardField (fun k => k.1) ζ)) k ξ ≤
      c * ε * (x * Real.sqrt (weightedSqNormNear κ (fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
        (blockDist F) z.1 ξ) + 1) *
        Real.exp (-(2 * κ * blockDist F (bondBlock F k.1) z.1))
def CellExponentsCloseForParameters (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F F' : BlockFrame) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ)
    (e : ↥(bondsNearCell F Y r) ≃ ↥(bondsNearCell F' Y' r))
    (φ : {z // z ∈ cellsNearCell F Y r} ≃ {z // z ∈ cellsNearCell F' Y' r}), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r → T.blockIndex ≤ r →
    BondsMatchByOffset Y Y' r e → CellsMatchByOffset Y Y' r φ → ∀ star,
      TermsCloseOnNearBonds T.ballRadius T.Ct (Real.exp (-(4 * T.κ * r))) x T.κ Y Y' r e φ
        (fun z => cellExponent star T.a T.chainParams.ρA x (frameRadius x) z V)
        (fun z => cellExponent star T.a T.chainParams.ρA x (frameRadius x) z V') ∧
      TermsCloseOnNearBonds T.ballRadius (T.Ct * T.energyRatio) (Real.exp (-(4 * T.κ * r))) x T.κ Y Y' r e φ
        (fun z η => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f z η V)
        (fun z η => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f z η V')
def CellExponentsCloseEventually : Prop := EventuallyInParameters CellExponentsCloseForParameters
end YangMills.Construction.ColdStepAtMirrorFrames
end
