import YangMills.Construction.InequalityOnMirroredCopies.ArrayOnRectangularTori
import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellAverages
open ChessboardTori ReflectedCopies StateLaws
open InfiniteLattice (AmbientSpace)
variable {D : ChessboardSetup}
def reflectionNorm (g : ReflectionGrid D) (G : D.GaugeField → ℝ) : ℝ :=
  ‖tiledMean g (minimalCounts D) (g.cell 0) fun U => (G U : ℂ)‖ ^ (1 / 16 : ℝ)
def IsDeepInCell (g : ReflectionGrid D) (f : AmbientSpace → ℝ) : Prop :=
  ∀ x ∈ tsupport f, ∀ μ, 2 * D.mesh ≤ x μ - g.origin μ ∧ x μ - g.origin μ ≤ 1 - 2 * D.mesh
def centeredObservable (L K k : ℕ) (β : ℝ) (v : Fin 4 → ℤ) (f : AmbientSpace → ℝ) (U : LatticeConfig L K) : ℝ :=
  smearedObservable L K (translateBy L K k v f) U - unitTorusMean L K β f
def shiftAverage (m : ℕ) (F : (Fin 4 → ℤ) → ℝ) : ℝ :=
  ((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m, F v
def averagedCovarianceDefect (L K k m : ℕ) (β : ℝ) (f h : AmbientSpace → ℝ) (U : LatticeConfig L K) : ℝ :=
  shiftAverage m fun v =>
    centeredObservable L K k β v f U * centeredObservable L K k β v h U - unitTorusCovariance L K β f h
def averagedCenteredObservable (L K k m : ℕ) (β : ℝ) (f : AmbientSpace → ℝ) (U : LatticeConfig L K) : ℝ :=
  shiftAverage m fun v => centeredObservable L K k β v f U
end YangMills.Construction.CellAverages
end
