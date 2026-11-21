import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open StepSettings StepGas TorusFields TorusLumps StepCosts MarkedIntegrals BlockAverages
def kernelProduct (ℓ : TorusLumps.StepParameters) (x : ℝ) {n : ℕ} [NeZero n] (W : TorusField (n * ℓ.side))
    (V : TorusField n) (b : BaseChoice ℓ.side n) : ℝ :=
  ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
    bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c
def centreBases (L n : ℕ) : BaseChoice L n := fun y => cellCentre (F := stepBlockFrame L n) 0 y
def emptyLabeling (R : StepSetup) {m : ℕ} : (↥(∅ : Finset (TorusSite m))) → R.labels.Ω :=
  fun z => absurd z.2 (Finset.notMem_empty _)
variable (R : StepSetup) {n : ℕ} [NeZero n]
abbrev fieldLabelMeasure (n : ℕ) [NeZero n] (Yt : Finset (TorusSite (n * R.params.side))) :
    Measure (TorusField (n * R.params.side) × (Yt → R.labels.Ω)) :=
  (fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)
open Classical in
def hullBaseDensity (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  if IsHullState R.params R.range p.1 Yt then R.labelWeight (n * R.params.side) p.1 Yt p.2 * baseLaw p.1 b else 0
def coldIntegrand (V : TorusField n)
    (f : (Yt : Finset (TorusSite (n * R.params.side))) → BaseChoice R.params.side n →
      TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  f Yt b p * (hullBaseDensity R Yt b p * kernelProduct R.params R.coupling p.1 V b)
def coldWeightedIntegral (V : TorusField n)
    (f : (Yt : Finset (TorusSite (n * R.params.side))) → BaseChoice R.params.side n →
      TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ) : ℝ :=
  ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
    ∫ p, coldIntegrand R V f Yt b p ∂fieldLabelMeasure R n Yt
def coldExpectation (V : TorusField n)
    (f : (Yt : Finset (TorusSite (n * R.params.side))) → BaseChoice R.params.side n →
      TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ) : ℝ :=
  coldWeightedIntegral R V f / coldWeightedIntegral R V fun _ _ _ => 1
def fullyMarkedExpectation (V : TorusField n) (g : TorusField (n * R.params.side) → ℝ) : ℝ :=
  (∫ W, R.avoidingPart Finset.univ W *
      averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) * g W *
      ∏ b ∈ chartBondsInBlocks R.params.side (Finset.univ : Finset (TorusSite n)), R.bondMark V W b
      ∂(fieldHaar (n * R.params.side))) /
    R.markedIntegral Finset.univ V
variable {R}
open Classical in
def liveCenteredResponse (A : ResponseSetup R) (y : TorusSite (n * R.params.side))
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
    centeredHullResponse A.cold A.hull (n * R.params.side) y p.1 Yt p.2 h
  else 0
end YangMills.Construction.WeightedResponses
end
