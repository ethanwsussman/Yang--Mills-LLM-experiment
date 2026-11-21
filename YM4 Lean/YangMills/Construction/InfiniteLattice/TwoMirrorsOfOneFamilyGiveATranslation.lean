import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace NormalFamilies
open InfiniteLattice
open PeriodicLattice (coordVec)
def planeGap (n : AmbientSpace) (c c' : ℝ) : ℝ :=
  sInf {d | ∃ x y : AmbientSpace, n ⬝ᵥ x = c ∧ n ⬝ᵥ y = c' ∧
    d = TorusMetric.euclidNormVec (x - y)}
namespace ReflectionPairShift
def ReflectionPairsGiveShift : Prop :=
  (∀ (n : AmbientSpace) (hn : n ∈ normalSet) (c c' : ℝ)
      (hc : IsAllowedLevel 1 n c) (hc' : IsAllowedLevel 1 n c'),
    ∃ v : LatticePoint 1, (v : AmbientSpace) = (2 * (c' - c)) • dualVector n ∧
      (∃ s : ℝ, (v : AmbientSpace) = s • n) ∧
      TorusMetric.euclidNormVec (v : AmbientSpace) = 2 * planeGap n c c' ∧
      planeGap n c c' = |c' - c| / Real.sqrt (normSq n) ∧
      ∀ μ : Measure (GaugeField 1), IsProbabilityMeasure μ →
        IsSymmetricUnder μ (NormalLevelPair.reflectSymmetry ⟨n, hn, c, hc⟩) →
        IsSymmetricUnder μ (NormalLevelPair.reflectSymmetry ⟨n, hn, c', hc'⟩) →
        IsSymmetricUnder μ (shift v)) ∧
  ∀ i : Fin 4,
    (∀ c : ℝ, (∃ k : ℤ, c = (k : ℝ) + 1 / 2) →
      ∃ P P' : NormalLevelPair 1,
        P.normal = coordVec i ∧ P.level = c ∧ P.IsLinkPair ∧
        P'.normal = coordVec i ∧ P'.level = c + 1 ∧ P'.IsLinkPair ∧
        P'.reflectSymmetry.toFun ∘ P.reflectSymmetry.toFun =
          (shift (axisStep 1 i + axisStep 1 i)).toFun) ∧
    ∃ P P' : NormalLevelPair 1,
      P.normal = coordVec i ∧ P.level = 0 ∧ P.IsSitePair ∧
      P'.normal = coordVec i ∧ P'.level = 1 / 2 ∧ P'.IsLinkPair ∧
      P'.reflectSymmetry.toFun ∘ P.reflectSymmetry.toFun = (shift (axisStep 1 i)).toFun
end ReflectionPairShift
end NormalFamilies
end YangMills.Construction
end
