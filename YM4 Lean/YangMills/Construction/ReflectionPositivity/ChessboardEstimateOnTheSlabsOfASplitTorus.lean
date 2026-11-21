import YangMills.Construction.ReflectionPositivity.CopiesOnTheSlabsAndTheFold
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace SlabDecomposition
variable (S : SlabDecomposition)
def IsRealWithPosInf (F : S.period.QuotientField → ℂ) : Prop :=
  (∀ U, (F U).im = 0) ∧ 0 < ⨅ U, (F U).re
def familyIntegral (β : ℝ) (f : ZMod (2 * S.count) → S.period.QuotientField → ℂ) : ℂ :=
  ∫ U, (∏ k : ZMod (2 * S.count), f k U) * (S.period.boltzmannWeight β U : ℂ) ∂S.period.quotientHaar
def FoldPosReal (β : ℝ) (k : ZMod (2 * S.count)) (F : S.period.QuotientField → ℂ) :
    Prop :=
  (S.fold β k F).im = 0 ∧ 0 < (S.fold β k F).re
def ChessboardBound (β : ℝ) (f : ZMod (2 * S.count) → S.period.QuotientField → ℂ) :
    Prop :=
  (S.familyIntegral β f).im = 0 ∧
    (S.familyIntegral β f).re ≤
      ∏ k : ZMod (2 * S.count), (S.fold β k (f k)).re ^ (1 / (2 * (S.count : ℝ)))
end SlabDecomposition
def SlabChessboardEstimate : Prop :=
  ∀ (S : SlabDecomposition) (β : ℝ), 0 < β →
    ∀ f : ZMod (2 * S.count) → S.period.QuotientField → ℂ,
      (∀ k, f k ∈ S.slabAlgebraOfClass k) →
      (∀ k, S.IsRealWithPosInf (f k)) →
      (∀ k, S.FoldPosReal β k (f k)) ∧ S.ChessboardBound β f
end YangMills.Construction.InfiniteLattice
end
