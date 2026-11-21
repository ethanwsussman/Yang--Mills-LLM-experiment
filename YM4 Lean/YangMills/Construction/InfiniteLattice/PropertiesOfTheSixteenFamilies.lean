import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.OneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies.Properties
open YangMills.Construction.InfiniteLattice YangMills.Construction.NormalFamilies
open YangMills.Construction.PeriodicLattice (coordVec)
def levelHyperplane (n : AmbientSpace) (c : ℝ) : Set AmbientSpace := {x | n ⬝ᵥ x = c}
def IsOrthogonalReflection (f : AmbientSpace → AmbientSpace) (H : Set AmbientSpace) : Prop :=
  ∀ x, (1 / 2 : ℝ) • (x + f x) ∈ H ∧ ∀ y ∈ H, ∀ z ∈ H, (f x - x) ⬝ᵥ (y - z) = 0
def normalSet_counts : Prop :=
  normalSet.ncard = 16 ∧
    {n ∈ normalSet | normSq n = 1}.ncard = 4 ∧
    {n ∈ normalSet | normSq n = 2}.ncard = 12 ∧
    ∀ n ∈ normalSet,
      n ⬝ᵥ dualVector n = 1 ∧
        n ⬝ᵥ firstNonzeroBasisVec n = 1 ∧
        (∀ ρ, n ρ = 0 ∨ n ρ = 1 ∨ n ρ = -1) ∧
        ∀ x ∈ latticeSubgroup 1, ∃ k : ℤ, linearHeight n x = (k : ℝ)
def reflectAcross_props : Prop :=
  ∀ n ∈ normalSet, ∀ c : ℝ,
    IsOrthogonalReflection (reflectAcross n c) (levelHyperplane n c) ∧
      (∀ x y, TorusMetric.euclidNormVec (reflectAcross n c x - reflectAcross n c y) =
        TorusMetric.euclidNormVec (x - y)) ∧
      (∀ x, n ⬝ᵥ reflectAcross n c x = 2 * c - n ⬝ᵥ x) ∧
      reflectAcross n c ∘ reflectAcross n c = id ∧
      (reflectAcross n c '' (latticeSubgroup 1 : Set AmbientSpace) =
          (latticeSubgroup 1 : Set AmbientSpace) ↔ IsAllowedLevel 1 n c)
def levelPairs_eq_latticeMirrors : Prop :=
  {H | ∃ P : NormalLevelPair 1, H = levelHyperplane P.normal P.level} =
      {H | IsLatticeMirror 1 H} ∧
    (∀ P : NormalLevelPair 1,
      IsOrthogonalReflection (reflectAcross P.normal P.level) (levelHyperplane P.normal P.level)) ∧
    ∀ P : NormalLevelPair 1, normSq P.normal = 2 →
      ∃ x ∈ latticeSubgroup 1, P.normal ⬝ᵥ x = P.level
def reflectAcross_linearPart : Prop :=
  ∀ n ∈ normalSet, ∃ l : AmbientSpace →ₗ[ℝ] AmbientSpace,
    (∀ x, l x = x - (2 * (n ⬝ᵥ x)) • dualVector n) ∧
      (∀ c : ℝ, ∃ v : AmbientSpace, ∀ x, reflectAcross n c x = l x + v) ∧
      (∀ x, n ⬝ᵥ x = 0 → l x = x) ∧
      l n = -n
def halfSpace_partition : Prop :=
  ∀ P : NormalLevelPair 1,
    (∀ (ε : ℤˣ) (F : GaugeField 1 → ℂ), IsBoundedObservable F → IsLocalObservable F →
      IsRegionMeasurable (closedHalfSpace P.normal P.level ε) F →
        F ∈ halfSpaceObservables 1 P.normal P.level ε) ∧
      planeLinks 1 P.normal P.level ⊆ halfSpaceLinks 1 P.normal P.level 1 ∧
      planeLinks 1 P.normal P.level ⊆ halfSpaceLinks 1 P.normal P.level (-1) ∧
      crossingLinks 1 P.normal P.level ∩
          (halfSpaceLinks 1 P.normal P.level 1 ∪ halfSpaceLinks 1 P.normal P.level (-1)) = ∅ ∧
      positiveLinks 1 =
        halfSpaceLinks 1 P.normal P.level 1 ∪ halfSpaceLinks 1 P.normal P.level (-1) ∪
          crossingLinks 1 P.normal P.level
def reflectAcross_zero_props : Prop :=
  (∀ n ∈ normalSet, IsLinearMap ℝ (reflectAcross n 0)) ∧
    (∀ (μ : Fin 4) (x : AmbientSpace),
      reflectAcross (coordVec μ) 0 x = Function.update x μ (-x μ)) ∧
    (∀ μ ν : Fin 4, μ < ν → ∀ x : AmbientSpace,
      reflectAcross (coordVec μ - coordVec ν) 0 x = x ∘ Equiv.swap μ ν) ∧
    (∀ μ ν : Fin 4, μ < ν → ∀ x : AmbientSpace,
      reflectAcross (coordVec μ + coordVec ν) 0 x =
        Function.update (Function.update x μ (-x ν)) ν (-x μ)) ∧
    (∀ μ ν : Fin 4, μ < ν →
      reflectAcross (coordVec μ + coordVec ν) 0 =
        reflectAcross (coordVec μ) 0 ∘ reflectAcross (coordVec ν) 0 ∘
          reflectAcross (coordVec μ - coordVec ν) 0) ∧
    Subgroup.closure {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace | ∃ n ∈ normalSet, ⇑w = reflectAcross n 0} =
      hyperoctahedralLinearGroup
def Statement : Prop :=
  normalSet_counts ∧ reflectAcross_props ∧ levelPairs_eq_latticeMirrors ∧ reflectAcross_linearPart ∧
    halfSpace_partition ∧ reflectAcross_zero_props
end YangMills.Construction.NormalFamilies.Properties
