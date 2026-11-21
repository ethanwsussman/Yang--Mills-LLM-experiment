import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def MinimalActionTranslationInvariant : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (h : F.Cell) (j : ℕ), 0 < F.blockSide → (∀ i, 2 ≤ F.extent i) →
    j ≤ F.top → ∀ X : F.GaugeField j,
    minimalAction a (finiteCells F) j (translateField (cellCentre j h) X) =
      minimalAction a (finiteCells F) j X
def SiteTranslationByCell : Prop :=
  ∀ (F : BlockFrame) (h : F.Cell) (x : F.Site F.depth), Odd F.blockSide → (∀ i, 2 ≤ F.extent i) →
    enclosingCell (x + cellCentre F.depth h) = enclosingCell x + h ∧
      cellOffset (x + cellCentre F.depth h) = cellOffset x
def MinimizingChartTranslation : Prop :=
  ∀ (F : BlockFrame) (a ρ : ℝ) (V : F.GaugeField F.top)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (h : F.Cell), Odd F.blockSide →
    (∀ i, 2 ≤ F.extent i) → IsMinimizingChart a (finiteCells F) V ρ w →
    IsMinimizingChart a (finiteCells F) (translateField h V) ρ fun x i => w (x - cellCentre F.depth h) i
def TranslationOfMinimizingChart : Prop :=
  MinimalActionTranslationInvariant ∧ SiteTranslationByCell ∧ MinimizingChartTranslation
end ColdStepAtMirrorFrames
end YangMills.Construction
end
