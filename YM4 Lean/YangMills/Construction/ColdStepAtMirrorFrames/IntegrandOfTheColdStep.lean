import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages MeasureTheory
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def haarRealPartDensity (v : ℝ) : ℝ := (2 / Real.pi) * Real.sqrt (2 * v - v ^ 2)
def haarLaplace (s : ℝ) : ℝ := ∫ v in (0 : ℝ)..2, Real.exp (-(s * v)) * haarRealPartDensity v
def haarCharacterMean (s : ℝ) : ℝ := Real.exp s * haarLaplace s
def haarGap (s : ℝ) : ℝ := s - Real.log (haarCharacterMean s)
def stepKernel (a x : ℝ) (W : F.GaugeField F.depth) (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4) : ℝ :=
  Real.exp (a * x * (contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).re) /
    haarCharacterMean (a * x * ‖contourAverage W c‖)
structure IsCutoff (ρ : ℝ) (p : ℝ → ℝ) : Prop where
  vanish_small : ∀ u, 0 ≤ u → u ≤ 5 * ρ / 8 → p u = 0
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p (Set.Ico 0 ρ)
  convex : ConvexOn ℝ (Set.Ico 0 ρ) p
  rim_second_deriv : ∃ u₀, u₀ < ρ ∧ ∀ u, u₀ < u → u < ρ → deriv (deriv p) u = ((ρ - u) ^ 4)⁻¹
def cutoffFactor (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : ℝ := if u < ρ then Real.exp (- p u) else 0
def toImaginary (v : EuclideanSpace ℝ (Fin 3)) : imaginaryQuaternions :=
  ⟨(⟨0, v 0, v 1, v 2⟩ : ℍ[ℝ]), rfl⟩
def haarLogDensity (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  if ‖v‖ < Real.pi then (Real.sinc ‖v‖) ^ 2 / (2 * Real.pi ^ 2) else 0
abbrev StepVariable (S : Finset F.Cell) : Type :=
  ↥(chordBonds S) → EuclideanSpace ℝ (Fin 3)
open Classical in
def stepCoordinates {S : Finset F.Cell} (w : StepVariable S) : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => if h : (x, i) ∈ chordBonds S then toImaginary (w ⟨(x, i), h⟩) else 0
def lowerBoltzmann (a x : ℝ) (f : LocalFamily) (S : Finset F.Cell) (W : F.GaugeField F.depth) : ℝ :=
  Real.exp (- x * minimalAction a S F.depth W + ∑ y ∈ sitesOfCells S F.depth, subtractTrivial f F y W)
def stepIntegrand (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (f : LocalFamily) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (w : StepVariable S) : ℝ :=
  lowerBoltzmann a x f S (chartedField (stepCoordinates w) V) *
    (∏ b : ↥(chordBonds S), cutoffFactor ρ p
      ‖((toImaginary (w b) : imaginaryQuaternions) : ℍ[ℝ]) - (bondFrameCoord a ρA m b.1 V : imaginaryQuaternions)‖) *
    (∏ c ∈ innerBonds S F.top, stepKernel a x (chartedField (stepCoordinates w) V) V c) *
    ∏ b : ↥(chordBonds S), haarLogDensity (w b)
def stepIntegral (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (f : LocalFamily) (S : Finset F.Cell)
    (V : F.GaugeField F.top) : ℝ :=
  ∫ w, stepIntegrand a ρA ρ x m p f S V w
end ColdStepAtMirrorFrames
end YangMills.Construction
end
