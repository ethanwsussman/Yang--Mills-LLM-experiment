import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMembers
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def chordBondDist (F : BlockFrame) (b b' : ↥(chordBonds (finiteCells F))) : ℝ :=
  cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1)
def bondSpanWithCell {k : ℕ} (Y z : F.Cell) (c : Fin k → F.Site F.top × Fin 4) : ℕ :=
  bondSpan Y (Fin.cons (z, 0) c : Fin (k + 1) → F.Site F.top × Fin 4)
def chordBondSpan {k : ℕ} (Y : F.Cell) (b : Fin k → ↥(chordBonds (finiteCells F))) : ℕ :=
  bondSpan Y fun l => (enclosingCell (b l).1.1, (0 : Fin 4))
def localSqNorm (κ : ℝ) (Y : F.Cell) (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ b : ↥(chordBonds (finiteCells F)),
    Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) * ‖η b‖ ^ 2
def thirdDerivAlong {ι : Type} [Fintype ι] (Ψ : BondField ι → ℝ) (η u v z : BondField ι) : ℝ :=
  fderiv ℝ (fun ζ => secondDerivAlong Ψ ζ u v) η z
structure CellExponentBounds (star : Bool) (a ρA ρ x κ C : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    Prop where
  sum_eq : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
    stepExponent star a ρA x m (fun _ _ _ => 0) 0 V η =
      ∑ Y ∈ finiteCells F, cellExponent star a ρA x m Y V η
  smooth : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ ≤ ρ) →
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      cellExponent star a ρA x m Y (leftTranslate (bondSpread c X q.1) V) q.2) (0, η)
  deriv_top : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ < ρ) →
    k ≤ 3 → AreUnitVectors X →
    |bondDeriv (fun V' => cellExponent star a ρA x m Y V' η) V c X| ≤
      C * (x * localSqNorm κ Y η + 1) * Real.exp (-(2 ^ 6 * κ * bondSpan Y c))
  deriv_top_partial : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F))
    (b : ↥(chordBonds (finiteCells F))) (e : BondVector) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ < ρ) →
    k ≤ 3 → AreUnitVectors X → ‖e‖ = 1 →
    |bondDeriv (fun V' => bondPartialDeriv (cellExponent star a ρA x m Y V') b η e) V c X| ≤
      C * (x * Real.sqrt (localSqNorm κ Y η) + 1) *
        Real.exp (-(2 ^ 6 * κ * bondSpanWithCell Y (enclosingCell b.1.1) c))
  second_deriv : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F))
    (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector), (∀ b, ‖η b‖ < ρ) → ‖e‖ = 1 →
    ‖e'‖ = 1 →
    |secondDerivAlong (cellExponent star a ρA x m Y V) η (bondVariation b e) (bondVariation b' e')| ≤
      C * x * Real.exp (-(2 ^ 6 * κ * chordBondSpan Y ![b, b']))
structure CentredExpansionBounds (star : Bool) (a ρA ρ κ δ E E₃ C : ℝ) (L m : ℕ) (f : LocalFamily)
    (V : F.GaugeField F.top) : Prop where
  smooth : ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ ≤ ρ) →
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      centredExpansion star a ρA m f y q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η)
  deriv_top : ∀ (Y : F.Cell) (y : F.Site F.depth) (η : StepVariable (finiteCells F)) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), enclosingCell y = Y →
    (∀ b, ‖η b‖ < ρ) → 1 ≤ k → k ≤ 3 → AreUnitVectors X →
    |bondDeriv (centredExpansion star a ρA m f y η) V c X| ≤ C * (if k = 3 then E₃ else E) *
      (1 / torusDecayFactor L δ ((L : ℝ) * bondSpan Y c / 16) +
        Real.exp (-(2 ^ 6 * κ * bondSpan Y c)))
  deriv_top_partial : ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F))
    (b : ↥(chordBonds (finiteCells F))) (e : BondVector) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ < ρ) →
    k ≤ 2 → AreUnitVectors X → ‖e‖ = 1 →
    |bondDeriv (fun V' => bondPartialDeriv (fun ζ => centredExpansion star a ρA m f y ζ V') b η e) V c X| ≤
      C * (if k = 2 then E₃ else E) *
        Real.exp (-(2 ^ 5 * κ * bondSpanWithCell (enclosingCell y) (enclosingCell b.1.1) c))
  second_deriv : ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F))
    (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector), (∀ b, ‖η b‖ < ρ) → ‖e‖ = 1 →
    ‖e'‖ = 1 →
    |secondDerivAlong (fun ζ => centredExpansion star a ρA m f y ζ V) η (bondVariation b e)
        (bondVariation b' e')| ≤
      C * E * Real.exp (-(2 ^ 5 * κ * chordBondSpan (enclosingCell y) ![b, b']))
  third_deriv : ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F))
    (b b' b'' : ↥(chordBonds (finiteCells F))) (e e' e'' : BondVector), (∀ b, ‖η b‖ < ρ) →
    ‖e‖ = 1 → ‖e'‖ = 1 → ‖e''‖ = 1 →
    |thirdDerivAlong (fun ζ => centredExpansion star a ρA m f y ζ V) η (bondVariation b e)
        (bondVariation b' e') (bondVariation b'' e'')| ≤
      C * E₃ * Real.exp (-(2 ^ 5 * κ * chordBondSpan (enclosingCell y) ![b, b', b'']))
def StepExponentIsConvex (star : Bool) (a ρA ρ lam x κ : ℝ) (m : ℕ) (f : LocalFamily) (ν : ℝ)
    (V : F.GaugeField F.top) : Prop :=
  IsConvexClassMember ρ (x * lam / 4) κ (chordBondDist F) (stepExponent star a ρA x m f ν V)
def chartedEnergyAt (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) : ℝ :=
  chartedEnergy a (fun x i => w x i + stepCoordinates η x i) V
end ColdStepAtMirrorFrames
end YangMills.Construction
end
