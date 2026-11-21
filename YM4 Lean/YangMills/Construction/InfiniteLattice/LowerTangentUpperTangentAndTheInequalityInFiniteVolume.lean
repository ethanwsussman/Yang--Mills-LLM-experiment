import YangMills.Construction.InfiniteLattice.AdaptedTori
import YangMills.Construction.InfiniteLattice.MeasuresOfTheInvariantClassAsLowerTangents
import YangMills.Construction.ReflectionPositivity.ChessboardEstimateTurnsTheUnfoldedArrayIntoTheFoldedOne
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.NormalFamilies
open InfiniteLattice
def tangentLowerConst : ℕ := Constants.BoxTorus.tangentSideNumber
namespace MirrorLadder
variable {L : MirrorLadder}
def SlabZeroGenerator.tangentDefect (A : L.SlabZeroGenerator) (ϱ : ℕ+) (β t : ℝ) (J : ℕ) (w : ℤ) :
    ℝ :=
  (tangentLowerConst : ℝ) * (β + t * observableSupNorm A.toFun) * ((ϱ : ℕ) : ℝ) ^ 5 *
    (1 / (2 * (J : ℝ) * (L.spacing : ℝ)) +
      ∑ i : Fin 3, 1 / ((w : ℝ) *
        (normalFrame L.normal L.normal_mem).lengthSq i.succ))
end MirrorLadder
def FiniteVolumeTangentBounds.Statement : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (L : MirrorLadder) (A : L.SlabZeroGenerator) (ϱ : ℕ+) (x : LatticePoint 1),
    LinksLieIn (observableSupport A.toFun)
      ((fun y : LatticePoint 1 => (y : AmbientSpace)) '' siteCube x ϱ) →
    ∀ (w : ℤ) (S : SlabDecomposition), L.IsAdaptedSlabDecomposition w S →
    ((ϱ : ℕ) : ℤ) + 1 < min ((S.count : ℤ) * L.spacing) w →
      let F : OrthogonalNormalFrame := normalFrame L.normal L.normal_mem
      let s : Fin 4 → ℕ+ := adaptedSideLengths L.normal L.normal_mem L.spacing (S.count : ℤ) w
      let D : Set (LatticePoint 1) := F.fundamentalBox s
      let ϰ : ℝ := axialPeriodDensity L.normal L.spacing
      let e : ℝ → ℝ := fun t => A.tangentDefect ϱ β t S.count w
      let φ : ℝ → ℝ := fun t => A.foldedArray.logTiltRatioPerSite S.period F s β t
      let μ : ℝ → Measure S.period.QuotientField :=
        fun t => A.foldedArray.tiltedMeasure S.period β t
      let μ' : ℝ → Measure (GaugeField 1) :=
        fun t => A.foldedArray.tiltedLiftMeasure S.period β t
      (∀ t : ℝ, 0 ≤ t →
        e t ≤ 3 * (tangentLowerConst : ℝ) * (β + t * observableSupNorm A.toFun) *
          ((ϱ : ℕ) : ℝ) ^ 5 *
            (1 / ((S.count : ℝ) * (L.spacing : ℝ)) + 1 / (w : ℝ))) ∧
      (∀ c : S.period.QuotientTorus, ∃! y : LatticePoint 1, y ∈ D ∧ S.period.quotientMap y = c) ∧
      D.ncard = S.period.periods.index ∧
      (Nat.card (A.unfoldedArray.Cosets S.period) : ℝ) = ϰ * (D.ncard : ℝ) ∧
      (Nat.card (A.foldedArray.Cosets S.period) : ℝ) = 1 / 2 * ϰ * (D.ncard : ℝ) ∧
      (∀ ν ∈ subgroupInvariantGibbsClass one_pos β L.axialSublattice, ∀ t : ℝ, 0 ≤ t →
        t * ϰ * (stateEval ν A.toFun).re - e t ≤
          A.unfoldedArray.logTiltRatioPerSite S.period F s β t) ∧
      ConvexOn ℝ Set.univ φ ∧
      Differentiable ℝ φ ∧
      φ 0 = 0 ∧
      (∀ t : ℝ, φ t ≤ t * deriv φ t) ∧
      (∀ t : ℝ, deriv φ t =
        1 / (D.ncard : ℝ) * ∫ U, A.foldedArray.periodicSum S.period U ∂(μ t)) ∧
      (∀ t : ℝ,
        (∀ v ∈ L.normalSublattice, PeriodSublattice.PreservesFiniteMeasure
          (S.period.pullbackField (shift v)) (μ t)) ∧
        PeriodSublattice.PreservesFiniteMeasure (S.reflectPullback 1) (μ t) ∧
        ∫ U, S.period.periodize A.reflected U ∂(μ t) =
          ∫ U, S.period.periodize A.toFun U ∂(μ t) ∧
        ((deriv φ t : ℝ) : ℂ) = (ϰ : ℂ) * ∫ U, S.period.periodize A.toFun U ∂(μ t) ∧
        (ϰ : ℂ) * ∫ U, S.period.periodize A.toFun U ∂(μ t) =
          (ϰ : ℂ) * stateEval (μ' t) A.toFun) ∧
      (∀ ν ∈ subgroupInvariantGibbsClass one_pos β L.axialSublattice, ∀ t : ℝ, 0 < t →
        (stateEval ν A.toFun).re ≤ (stateEval (μ' t) A.toFun).re + e t / (t * ϰ))
end YangMills.Construction.NormalFamilies
