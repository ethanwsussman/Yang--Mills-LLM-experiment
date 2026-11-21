import YangMills.Construction.ReflectionPositivity.ChessboardEstimateTurnsTheUnfoldedArrayIntoTheFoldedOne
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.NormalFamilies
open YangMills.Construction.InfiniteLattice
namespace MirrorLadder
variable {L : MirrorLadder} (A : L.SlabZeroGenerator) (Γ : PeriodSublattice 1) (J : ℕ)
def SlabZeroGenerator.TermInUpperHalf (k : ℤ)
    (c : A.foldedArray.Cosets Γ × Fin A.foldedArray.size) : Prop :=
  ∃ i : ℕ, i < J ∧
    TermInSlabClass A.foldedArray (FoldedLabelInSlab A) Γ J c
      ((k + (i : ℤ) : ℤ) : ZMod (2 * J))
def SlabZeroGenerator.upperHalfFoldedSum (t : ℝ) (k : ℤ) (U : Γ.QuotientField) : ℂ :=
  (t : ℂ) * ∑ᶠ (c : A.foldedArray.Cosets Γ × Fin A.foldedArray.size)
    (_ : A.TermInUpperHalf Γ J k c),
    Γ.periodize (A.foldedArray.translate (A.foldedArray.cosetRep Γ c.1, c.2)) U
end MirrorLadder
def TiltedTorusMeasureReflectsAtEveryRung : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (L : MirrorLadder) (A : L.SlabZeroGenerator) (w : ℤ)
    (S : SlabDecomposition), L.IsAdaptedSlabDecomposition w S → ∀ (t : ℝ) (k : ℤ),
      let E : S.period.QuotientField → ℂ := A.upperHalfFoldedSum S.period S.count t k
      let μ : Measure S.period.QuotientField := A.foldedArray.tiltedMeasure S.period β t
      S.period.plusHalf S.normal S.halfPeriod (S.level k) =
        ⋃ i : Fin S.count, S.slabAt (k + ((i : ℕ) : ℤ)) ∧
      (∀ U, (E U).im = 0) ∧
      E ∈ S.period.plusAlgebra S.normal S.halfPeriod (S.level k) ∧
      (fun U => ((t * A.foldedArray.periodicSum S.period U : ℝ) : ℂ)) =
        (fun U => E U + S.reflectAct k E U) ∧
      PeriodSublattice.PreservesFiniteMeasure (S.reflectPullback k) μ ∧
      ∀ F : S.period.QuotientField → ℂ,
        F ∈ S.period.plusAlgebra S.normal S.halfPeriod (S.level k) ∨
          F ∈ S.period.minusAlgebra S.normal S.halfPeriod (S.level k) →
        0 ≤ ∫ U, S.conjReflectAt k F U * F U ∂μ
end YangMills.Construction.NormalFamilies
