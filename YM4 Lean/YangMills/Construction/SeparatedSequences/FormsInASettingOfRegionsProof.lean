import YangMills.Construction.SeparatedSequences.ClassBasePointsInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassExpansionsInASettingOfRegionsProof
import YangMills.Construction.SeparatedSequences.PropertiesOfTheOperatorsOfASequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses.FormsMatch
open Set TorusMetric PeriodicLattice PeriodicLattice.DirichletOperators
open SingleSequence SingleSequence.SequenceData
theorem mem_range_indicatorMul {ι : Type} {X : Set ι} {f : ι → ℝ} :
    f ∈ LinearMap.range (indicatorMul X) ↔ ∀ i, i ∉ X → f i = 0 := by apply _root_.YangMills.Construction.SeparatedClasses.NestedOneForms.mem_range_indicatorMul <;> assumption
theorem indicatorMul_of_mem {ι : Type} {X : Set ι} {f : ι → ℝ}
    (hf : f ∈ LinearMap.range (indicatorMul X)) : indicatorMul X f = f := by apply _root_.YangMills.Construction.SeparatedClasses.NestedOneForms.indicatorMul_of_mem <;> assumption
section EvaluationMaps
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions}
theorem toTorus_apply (x : s.data.Point) (μ : Fin 4) :
    s.toTorus 𝒮.side x μ =
      AddCircle.equivAddCircle _ 𝒮.side s.torusSide_ne_zero 𝒮.side_pos.ne' (x μ) := by
  simp only [SequenceData.toTorus, dif_pos 𝒮.side_pos.ne']
theorem toTorus_add (x x' : s.data.Point) :
    s.toTorus 𝒮.side (x + x') = s.toTorus 𝒮.side x + s.toTorus 𝒮.side x' := by
  funext μ
  simp only [toTorus_apply, Pi.add_apply, map_add]
theorem toTorus_neg (x : s.data.Point) : s.toTorus 𝒮.side (-x) = -s.toTorus 𝒮.side x := by
  funext μ
  simp only [toTorus_apply, Pi.neg_apply, map_neg]
theorem toTorus_injective : Function.Injective (s.toTorus 𝒮.side) := by
  intro x x' h
  funext μ
  have h1 := congrFun h μ
  rw [toTorus_apply, toTorus_apply] at h1
  exact (AddCircle.equivAddCircle _ _ _ _).injective h1
theorem toTorus_unitStep (hS : s.IsNestedRegions 𝒮) (μ : Fin 4) :
    s.toTorus 𝒮.side ((unitStep s.data.L s.data.m (levelDepth s.data.cutoff 0) μ :
        Site s.data.L s.data.m (levelDepth s.data.cutoff 0)) : s.data.Point) =
      ((Dirichlet.unitStep 4 𝒮.side 𝒮.ξ μ : Dirichlet.LatticeSite 4 𝒮.side 𝒮.ξ) :
        𝒮.Point) := by apply _root_.YangMills.Construction.SeparatedClasses.NestedOneForms.toTorus_unitStep <;> assumption
variable {σ : s.data.BareSite ≃ 𝒮.FineSite} {β : s.data.BareBond ≃ 𝒮.FineBond}
end EvaluationMaps
end YangMills.Construction.SeparatedClasses.FormsMatch
end
