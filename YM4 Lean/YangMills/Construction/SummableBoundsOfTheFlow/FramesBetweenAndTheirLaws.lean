import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
variable {F : BlockFrame}
def interpolatedFrame (s a ρA : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    imaginaryQuaternions :=
  (1 - s) • stepFrame true a ρA m b V + s • stepFrame false a ρA m b V
def frameGap (a ρA : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    imaginaryQuaternions :=
  stepFrame false a ρA m b V - stepFrame true a ρA m b V
def interpolatedSlope (s a ρA : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions)
    (V : F.GaugeField F.top) : ℝ :=
  chartedSlope a (fun z i => interpolatedFrame s a ρA m (z, i) V) V b e
def interpolatedCoords (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun z i => interpolatedFrame s a ρA m (z, i) V + stepCoordinates η z i
def interpolatedField (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : F.GaugeField F.depth :=
  chartedField (interpolatedCoords s a ρA m V η) V
def interpolatedExpansion (s a ρA : ℝ) (m : ℕ) (f : LocalFamily) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  subtractTrivial f F y (interpolatedField s a ρA m V η)
open Classical in
def interpolatedBlockExpansion (s a ρA : ℝ) (m : ℕ) (f : LocalFamily) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
    interpolatedExpansion s a ρA m f y η V
def interpolatedExponent (s a ρA x : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  x * (chartedEnergy a (interpolatedCoords s a ρA m V η) V -
      chartedEnergy a (interpolatedCoords s a ρA m V 0) V) -
    (∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a x (interpolatedField s a ρA m V η) c) -
    (∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2))
open Classical in
def interpolatedBlockExponent (s a ρA x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  x * (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      ∫ v in (0 : ℝ)..1, chartedSlope a (interpolatedCoords s a ρA m V (v • η)) V b.1
        (toImaginary (η b)) else 0) -
    (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
      haarGapExcess a x (interpolatedField s a ρA m V η) c) -
    (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) else 0)
def familyLawExponent (s a ρA x : ℝ) (m : ℕ) (φ : LocalFamily) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  interpolatedExponent s a ρA x m V η -
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, interpolatedExpansion s a ρA m φ y η V
def weightLawExponent (s a ρA lam x : ℝ) (m : ℕ) (τ : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  τ * interpolatedExponent s a ρA x m V η + (1 - τ) * totalQuadratic lam x η
def extendByZero {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F)))
    (Λ : Finset ι) (ζ : BondField ι) : StepVariable (finiteCells F) :=
  fun b => ∑ i ∈ Λ, if j i = b then ζ i else 0
def frozenExponent {ι : Type} [Fintype ι] [DecidableEq ι] (lam x : ℝ)
    (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) (Ψ : StepVariable (finiteCells F) → ℝ)
    (ζ : BondField ι) : ℝ :=
  Ψ (extendByZero j Λ ζ) + ∑ i ∈ Finset.univ \ Λ, x * lam / 2 * ‖ζ i‖ ^ 2
def MomentBound {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ → ℝ)
    (Ψ H : BondField ι → ℝ) (q : ℕ) (B : ℝ) : Prop :=
  Integrable (fun η => |H η| ^ q * ballDensity r Ψ η) ∧
    ballExpectation r Ψ (fun η => |H η| ^ q) ≤ B ^ q
def HasLocalSize {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ℝ) (r : ℝ → ℝ) (Ψ : BondField ι → ℝ)
    (Cq : ℕ → ℝ) (x κ h : ℝ) (dZ : ι → ℝ) (H : BondField ι → ℝ) : Prop :=
  (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → DifferentiableAt ℝ H η) ∧
    ∃ H₀ : ℝ, ∀ q : ℕ, 1 ≤ q →
      MomentBound r Ψ (fun η => H η - H₀) q (Cq q * h) ∧
      ∀ b : ι, MomentBound r Ψ (bondGradNorm H b) q
        (Cq q * Real.sqrt x * h * Real.exp (-(2 * κ * dZ b)))
end Interpolation
end YangMills.Construction
end
