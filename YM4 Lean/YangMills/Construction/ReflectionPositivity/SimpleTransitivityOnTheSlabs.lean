import YangMills.Construction.ReflectionPositivity.MirrorsSlabsAndTheGroupOfASplitTorus
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
open NormalFamilies
open PeriodicLattice (coordVec)
namespace PeriodSublattice
variable {Γ : PeriodSublattice 1}
namespace TorusMap
protected def identity (Γ : PeriodSublattice 1) : Γ.TorusMap := ⟨_root_.id, _root_.id, _root_.id⟩
def compose (g g' : Γ.TorusMap) : Γ.TorusMap :=
  ⟨g.pointMap ∘ g'.pointMap, g.linkMap ∘ g'.linkMap, g.faceMap ∘ g'.faceMap⟩
instance : Nonempty Γ.TorusMap := ⟨TorusMap.identity Γ⟩
end TorusMap
end PeriodSublattice
namespace SlabDecomposition
variable (S : SlabDecomposition)
def MapsSlabTo (j k : ZMod (2 * S.count)) (g : S.period.TorusMap) : Prop :=
  g ∈ S.generatedMaps ∧ g.pointMap '' S.slabOfClass j = S.slabOfClass k
def slabTransporter (j k : ZMod (2 * S.count)) : S.period.TorusMap :=
  Classical.epsilon (S.MapsSlabTo j k)
end SlabDecomposition
def SlabActionSimplyTransitive : Prop :=
  ∀ S : SlabDecomposition,
    (2 * (S.width : ℝ)) • dualVector S.normal ∈ latticeSubgroup 1 ∧
    S.normal ⬝ᵥ ((2 * (S.width : ℝ)) • dualVector S.normal) = 2 * (S.width : ℝ) ∧
    (∀ μ : Fin 4, S.normal = coordVec μ →
      (2 * (S.width : ℝ)) • dualVector S.normal =
        (2 * (S.width : ℝ)) • coordVec μ) ∧
    (normSq S.normal = 2 →
      (2 * (S.width : ℝ)) • dualVector S.normal = (S.width : ℝ) • S.normal) ∧
    (∀ c : ℝ, IsAllowedLevel 1 S.normal c → ∀ x : AmbientSpace,
      reflectAcross S.normal (c + (S.width : ℝ)) (reflectAcross S.normal c x) =
        x + (2 * (S.width : ℝ)) • dualVector S.normal) ∧
    (2 * (S.halfPeriod : ℝ)) • dualVector S.normal =
      (S.count : ℝ) • ((2 * (S.width : ℝ)) • dualVector S.normal) ∧
    S.halfPeriod = (S.count : ℤ) * S.width ∧ 2 ≤ S.halfPeriod ∧
    (∀ k : ℤ, IsAllowedLevel 1 S.normal (S.level k)) ∧
    (∀ k : ℤ, S.torusReflection (k + (S.count : ℤ)) = S.torusReflection k) ∧
    (∀ (k : ℤ) (b : S.period.QuotientLink), S.period.linkEndpoints b ⊆ S.mirrorLocus k →
      S.period.linkEndpoints b ⊆ S.slabAt (k - 1) ∧ S.period.linkEndpoints b ⊆ S.slabAt k) ∧
    Function.Injective S.slabOfClass ∧
    (∀ s i : ZMod (2 * S.count),
      (S.torusReflectionOfClass s).pointMap '' S.slabOfClass (s + i) = S.slabOfClass (s - 1 - i)) ∧
    (∀ (j : ℤ) (k : ZMod (2 * S.count)),
      (S.period.descendedTorusMap (shift (S.stepVec j))).pointMap '' S.slabOfClass k =
        S.slabOfClass (k + 2 * (j : ZMod (2 * S.count)))) ∧
    S.period.descendedTorusMap (shift (S.stepVec (S.count : ℤ))) =
      PeriodSublattice.TorusMap.identity S.period ∧
    PeriodSublattice.TorusMap.identity S.period ∈ S.generatedMaps ∧
    (∀ g ∈ S.generatedMaps, ∀ g' ∈ S.generatedMaps, g.compose g' ∈ S.generatedMaps) ∧
    (∀ g ∈ S.generatedMaps, ∃ g' ∈ S.generatedMaps,
      g.compose g' = PeriodSublattice.TorusMap.identity S.period ∧
      g'.compose g = PeriodSublattice.TorusMap.identity S.period) ∧
    S.generatedMaps.Finite ∧ S.generatedMaps.ncard = 2 * S.count ∧
    (∀ k : ℤ, S.torusReflection k ∈ S.generatedMaps) ∧
    (∀ j k : ZMod (2 * S.count), ∃! g, S.MapsSlabTo j k g) ∧
    (∀ j k : ZMod (2 * S.count), S.MapsSlabTo j k (S.slabTransporter j k)) ∧
    (∀ (j k : ZMod (2 * S.count)) (g : S.period.TorusMap), S.MapsSlabTo j k g →
      (S.ValModEqTwo k j → S.IsGroupTranslation g) ∧
      (¬ S.ValModEqTwo k j → S.IsGroupReflection g)) ∧
    (∀ g : S.period.TorusMap, ¬ (S.IsGroupTranslation g ∧ S.IsGroupReflection g))
end InfiniteLattice
end YangMills.Construction
