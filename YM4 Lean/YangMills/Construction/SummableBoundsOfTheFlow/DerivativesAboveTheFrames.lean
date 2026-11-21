import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
variable {F : BlockFrame}
def runningMax (e : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => max (runningMax e j) (e (j + 1))
structure HasBoundedDerivatives (L t n₀ : ℕ) (σ δ : ℝ) (k : ℕ) (e : ℕ → ℝ) (f : LocalFamily) : Prop where
  smooth : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth), IsSmallCurvature σ W →
    ∀ (j : ℕ) (c : Fin j → F.Site F.depth × Fin 4) (X : Fin j → imaginaryQuaternions),
      ContDiffAt ℝ k (fun τ : Fin j → ℝ => f F y (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W)) 0
  gauge_invariant : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (γ : F.Site F.depth → UnitQuaternion), IsSmallCurvature σ W → f F y (gaugeTransform γ W) = f F y W
  decay : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth) (j : ℕ)
    (c : Fin j → F.Site F.depth × Fin 4) (X : Fin j → imaginaryQuaternions), IsSmallCurvature σ W → 1 ≤ j → j ≤ k →
    AreUnitVectors X → |bondDeriv (f F y) W c X| ≤ e j / torusDecayFactor L δ (bondSpan y c)
open Classical in
def displacedPoint {l : ℕ} (η : StepVariable (finiteCells F)) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (v : Fin l → EuclideanSpace ℝ (Fin 3)) (u : Fin l → ℝ) : StepVariable (finiteCells F) :=
  η + ∑ i, Pi.single (b i) (u i • v i)
def jointDisplacement {E : Type} {l j : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → E)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (v : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) :
    (Fin (l + j) → ℝ) → E :=
  fun τ => G (displacedPoint η b v fun i => τ (Fin.castAdd j i))
    (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X fun i => τ (Fin.natAdd l i)) V)
def jointMixedDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {l j : ℕ}
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → E) (η : StepVariable (finiteCells F))
    (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (v : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) : E :=
  iteratedFDeriv ℝ (l + j) (jointDisplacement G η V b v c X) 0 fun i => Pi.single i 1
def chordBondCells {l : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) : Finset F.Cell :=
  Finset.univ.image fun i => enclosingCell (b i).1.1
def topBondCells {j : ℕ} (c : Fin j → F.Site F.top × Fin 4) : Finset F.Cell :=
  Finset.univ.image fun i => (c i).1
def cellSetDiameter (P : Finset F.Cell) : ℕ := P.sup fun u => P.sup fun w => cellSupDist u w
end Interpolation
end
end YangMills.Construction
