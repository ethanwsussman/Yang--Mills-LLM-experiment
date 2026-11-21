import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Interpolation
open BlockAverages ColdStepAtMirrorFrames FamilyNorms
variable {F : BlockFrame}
inductive IsIntermediateLaw (a ρA lam x : ℝ) (m : ℕ) (isFamily : LocalFamily → Prop)
    (V : F.GaugeField F.top) : (StepVariable (finiteCells F) → ℝ) → Prop
  | ofFamily (s : ℝ) (φ : LocalFamily) : 0 ≤ s → s ≤ 1 → isFamily φ →
      IsIntermediateLaw a ρA lam x m isFamily V (familyLawExponent s a ρA x m φ V)
  | ofWeight (s τ : ℝ) : 0 ≤ s → s ≤ 1 → 0 ≤ τ → τ ≤ 1 →
      IsIntermediateLaw a ρA lam x m isFamily V (weightLawExponent s a ρA lam x m τ V)
structure LawOnBondVariables (ι : Type) [Fintype ι] [DecidableEq ι] where
  frame : BlockFrame
  topField : frame.GaugeField frame.top
  embed : ι → ↥(chordBonds (finiteCells frame))
  active : Finset ι
  potential : StepVariable (finiteCells frame) → ℝ
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def LawOnBondVariables.exponent (lam x : ℝ) (M : LawOnBondVariables ι) : BondField ι → ℝ :=
  frozenExponent lam x M.embed M.active M.potential
def embeddedCellDist (j : ι → ↥(chordBonds (finiteCells F))) (Y : F.Cell) : ι → ℝ :=
  fun i => cellSupDist (enclosingCell (j i).1.1) Y
def PreservesCellDist (j : ι → ↥(chordBonds (finiteCells F))) (d : ι → ι → ℝ) : Prop :=
  ∀ i i', d i i' = cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1)
structure LawOnBondVariables.IsAdmissible (a ρA lam x σ δ E E₃ : ℝ) (L t n₀ m : ℕ)
    (d : ι → ι → ℝ) (M : LawOnBondVariables ι) : Prop where
  isCubicTopTorus : IsCubicTopTorus L t n₀ M.frame
  isSmallCurvature : IsSmallCurvature (5 / 4 * σ) M.topField
  isIntermediateLaw :
    IsIntermediateLaw a ρA lam x m (IsNormBoundedLocalFamily L t n₀ σ δ E E₃) M.topField M.potential
  embed_injective : Function.Injective M.embed
  preservesCellDist : PreservesCellDist M.embed d
def convexCombinationExponent {n : ℕ} (lam x : ℝ) (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι) :
    BondField ι → ℝ :=
  fun ζ => ∑ l, w l * (M l).exponent lam x ζ
def IsConvexWeights {n : ℕ} (w : Fin n → ℝ) : Prop := (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1
end Interpolation
end YangMills.Construction
end
