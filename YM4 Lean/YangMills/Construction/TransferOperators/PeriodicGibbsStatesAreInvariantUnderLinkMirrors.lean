import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TransferOperators
open MeasureTheory InfiniteLattice
open PeriodicLattice (coordVec)
theorem normSq_coordVec (μ : Fin 4) :
    NormalFamilies.normSq (coordVec μ) = 1 := by
  rw [NormalFamilies.normSq_eq_dotProduct]
  simp [coordVec]
def linkReflectionPair (μ : Fin 4) (c : ℝ) (hc : ∃ k : ℤ, c = (k : ℝ) + 1 / 2) :
    NormalFamilies.NormalLevelPair 1 where
  normal := coordVec μ
  normal_mem := Or.inl ⟨μ, rfl⟩
  level := c
  allowed := by
    obtain ⟨k, rfl⟩ := hc
    refine ⟨fun _ => ⟨2 * k + 1, by push_cast; ring⟩, fun h => ?_⟩
    rw [normSq_coordVec] at h
    norm_num at h
namespace PeriodicGibbsLinkSymmetry
def Statement : Prop :=
  ∀ β : ℝ, 0 < β →
    (∀ ν : Measure (GaugeField 1), IsPeriodicGibbs β ν →
      (∀ (μ : Fin 4) (c : ℝ) (hc : ∃ k : ℤ, c = (k : ℝ) + 1 / 2) (F : GaugeField 1 → ℂ),
        IsBoundedObservable F →
          ∫ U, (linkReflectionPair μ c hc).reflectObservable F U ∂ν = ∫ U, F U ∂ν) ∧
      ∀ v ∈ cubicSublattice 1 2, IsSymmetricUnder ν (shift v)) ∧
    {ν : Measure (GaugeField 1) | IsPeriodicGibbs β ν} =
      subgroupInvariantGibbsClass one_pos β (cubicSublattice 1 2)
end PeriodicGibbsLinkSymmetry
end TransferOperators
end YangMills.Construction
end
