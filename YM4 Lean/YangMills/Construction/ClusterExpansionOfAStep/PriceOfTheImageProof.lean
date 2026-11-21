import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.ParametersAgreeWithTheSum
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfAClassBeforeItsLength
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheImage
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open YangMills.Construction.StepSettings YangMills.Construction.RenormalizationStepParameters YangMills.Construction.TorusLumps YangMills.Construction.StepFloors
theorem imageHasHullExpansionPrice_holds (hComp : ComponentPriceBound)
    (hExp : ClassExponentLePrice) (hOnParameters : ParameterChoiceMeetsClassSum)
    (hFloor : EventuallyFloorConditions) : ImageHasHullExpansionPrice := by
  obtain ⟨rt₀, hrt₀, hComp'⟩ := hComp
  refine ⟨rt₀, hrt₀, fun T hT hrt => ?_⟩
  obtain ⟨CE, y₀, hCE, hBound⟩ := hComp' T hT hrt
  obtain ⟨y₂, hy₂⟩ := hFloor T hT (2 ^ 18 * CE + 2 ^ 17) 1 (by positivity) one_pos
  refine ⟨max y₀ (max y₂ T.floorMin), fun y hy R hst hfs hx' hmove h => ?_⟩
  have hpar := hst.params_eq
  have hxy := hst.le_coupling
  have hy0 : y₀ ≤ y := (le_max_left _ _).trans hy
  have hy2 : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hyT : T.floorMin ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hyp : ClassSumHypotheses R.params T.cE CE := by
    rw [hpar]
    exact hOnParameters T hT CE 1 y hCE hyT fun x hx => hy₂ x (hy2.trans hx)
  have adm : R.params.Admissible := by
    rw [hpar]
    exact hT.fits y hyT
  have hy1 : R.params.y₁ ≤ R.coupling := by
    rw [hpar]
    exact hxy
  refine ⟨fun n _ hn V Y ω P hull hP hoff => ?_⟩
  refine hBound y hy0 R hst hfs hx' hmove n hn V Y ω P hull hP hoff _ ?_
  intro ν W Yt ωt bad b _ hst
  have hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V) :=
    (congrArg Sigma.fst hst).symm
  have hP' : P ⊆ chainComponents R.nextRange (coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V)) :=
    hY ▸ hP
  exact hExp R.params T.cE CE adm hyp R.coupling R.nextCoupling hy1 hmove n hn.1 V W bad Yt P hP'
end YangMills.Construction.ClusterExpansionOfAStep
end
