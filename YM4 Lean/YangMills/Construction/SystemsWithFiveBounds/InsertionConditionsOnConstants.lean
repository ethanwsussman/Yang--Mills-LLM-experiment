import YangMills.Construction.BoundsOnEverySide.InsertionBoundAtNumbers
import YangMills.Construction.Continuum.ComplexComponentsOfSeparatedTuples
import YangMills.Construction.Continuum.FreeSlabInsertionFormAndPulledDownNorm
import Mathlib
import YangMills.Construction.SystemsWithFiveBounds.SystemWithFiveBounds
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.Insertion
def ballRadiusRatio : ℝ := 1 / 16
end YangMills.Construction.Insertion
end

noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open SeparatedTuples
open InfiniteLattice (AmbientSpace)
open ReflectionPositivity.TupleForm (PositiveSpan reflectConj)
open R4TupleForms (singleTuple)
open SlabInsertion (timeVec timeAbove insertionForm shiftDownNorm)
open ReflectionsAndOneInsertion (spanClassNorm gradNorm)
open BoundsOnEverySide (timeZeroPoint)
def fieldExponent (N : BoundConstants) : ℝ := 3 + N.insertionExponent
def pieceCount (c : ℝ) : ℝ := (2 / c + 3) ^ 3 * (4 / c + 3) * (40 * (1 + 7 / c))
def fieldOperatorConst (L M : ℝ) (N : BoundConstants) (R : ℝ) : ℝ :=
  2 * pieceCount N.insertionRadiusRatio * L ^ (5 + N.insertionExponent) * M * max 1 R ^ 3 *
    N.insertionConst
def freeSlabConst (L M : ℝ) (N : BoundConstants) : ℝ :=
  (16 : ℝ) ^ fieldExponent N * (1 + 1 / (40 * M)) * fieldOperatorConst L M N 1
def SingleCellBound (L : ℕ) (M : ℝ) (N : BoundConstants) (ς : TupleFunctional) : Prop :=
  ∀ (e : ℤ) (l : ℝ), l = (L : ℝ) ^ e → l ≤ 1 → ∀ (y : Fin 3 → ℝ) (h : RealValued)
    (hh : IsC1c h),
    tsupport h ⊆ TestFunctions.closedBallR4 (timeZeroPoint y) (N.insertionRadiusRatio * l) →
    ∀ P Q : PositiveSpan,
      ‖ς.spanExtension (formalMul (formalMul (reflectConj Q)
          (basisVec (push (translate (timeVec (l / 2))) (singleTuple h hh))))
          (pushSpan (translate (timeVec l)) P.1))‖ ≤
        N.insertionConst * l ^ (-N.insertionExponent) * TestFunctions.sharpNormR4 M h *
          spanClassNorm ς Q * spanClassNorm ς P
def FieldOperatorBound (L : ℕ) (M : ℝ) (N : BoundConstants) (ς : TupleFunctional) : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ R : ℝ, 0 < R →
    ∀ (f : ComplexTestFunctions.ComplexValued) (hf : ComplexTestFunctions.IsC1cComplex f),
    tsupport f ⊆ {x | η ≤ TimeAxis.timeComponent x ∧ TimeAxis.timeComponent x ≤ 3 * η} →
    TestFunctions.HasDiameterLE (tsupport f) R →
    ∀ P : PositiveSpan, ∃ G : PositiveSpan,
      G.1 = formalMul (ComplexTupleComponents.singleSpan f hf)
        (pushSpan (translate (timeVec (4 * η))) P.1) ∧
      spanClassNorm ς G ≤ fieldOperatorConst L M N R * η ^ (-fieldExponent N) *
        (TestFunctions.uniformNorm f + ⨆ x, gradNorm f x) * spanClassNorm ς P
def FreeSlabBound (L : ℕ) (M : ℝ) (N : BoundConstants) (ς : TupleFunctional) : Prop :=
  ∀ (η : ℝ) (hη : 0 < η), η ≤ 1 → ∀ y : AmbientSpace, |TimeAxis.timeComponent y| ≤ η / 8 →
    ∀ (k : RealValued) (hk : IsC1c k),
    tsupport k ⊆ TestFunctions.closedBallR4 y (Insertion.ballRadiusRatio * η) →
    ∀ P Q : spanIn (timeAbove (η / 4)),
      ‖insertionForm ς P k hk Q‖ ≤
        freeSlabConst L M N * η ^ (-fieldExponent N) * TestFunctions.sharpNormR4 M k *
          shiftDownNorm ς hη P * shiftDownNorm ς hη Q
structure InsertionBounds (L : ℕ) (M : ℝ) (N : BoundConstants) (ς : TupleFunctional) :
    Prop where
  singleCell : SingleCellBound L M N ς
  fieldOperator : FieldOperatorBound L M N ς
  freeSlab : FreeSlabBound L M N ς
end YangMills.Construction.SystemsWithFiveBounds
end
