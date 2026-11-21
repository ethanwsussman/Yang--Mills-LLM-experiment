import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.EquilibriumClassIsTheSetOfGibbsStates
import YangMills.Construction.InfiniteLattice.FunctionsStatesSupportsClassesMirrorsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.IntegerHeightsAndCubicPeriodsOfTheLadderGroups
import YangMills.Construction.InfiniteLattice.PropertiesOfThePeriodGroups
import YangMills.Construction.InfiniteLattice.SigmaAlgebrasOfSetsOfBondsAndDependenceOnVariables
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndDenseLocalObservables
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import YangMills.Construction.InfiniteLattice.TwoWaysOfNamingALatticeMirror
import YangMills.Construction.InfiniteLattice.WeakTopologyCompactnessAndInvarianceOfTheStates
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.GibbsAtFixedSpacing YangMills.Construction.NormalFamilies YangMills.Construction.LatticeConventions
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice.BasicStructure
theorem symmetryActionFacts_of {a : ℝ} (ha : 0 < a)
    (hSym : YangMills.Construction.InfiniteLattice.FieldSpace.SymmetryProperties)
    (hElem : YangMills.Construction.InfiniteLattice.ElementaryLatticeFacts) :
    YangMills.Construction.InfiniteLattice.BasicStructure.SymmetryActionFacts a := by
  obtain ⟨-, -, -, -, -, -, -, hIso, -⟩ := hElem a 1 ha one_pos
  intro g g'
  have hAct := (hSym a ha).2.1 g g'
  refine ⟨hAct.1, fun F F' hF hF' => ?_, fun S F hF => ?_, fun F hF => ?_, fun F hF => ?_⟩
  · obtain ⟨-, -, -, k₁, k₂, k₃⟩ := hAct.2.2.1 F F' hF hF'
    exact ⟨k₁, k₂, rfl, k₃⟩
  · exact (hAct.2.2.2 S).subset ⟨F, hF, rfl⟩
  · exact (show Continuous F from hF).comp hAct.1.continuous
  · obtain ⟨-, -, -, -, hCl, -⟩ := hIso g g'
    exact hCl.subset ⟨F, hF, rfl⟩
theorem supportFacts_of {a : ℝ} (ha : 0 < a)
    (hElem : YangMills.Construction.InfiniteLattice.ElementaryLatticeFacts) :
    YangMills.Construction.InfiniteLattice.BasicStructure.SupportFacts a := by
  obtain ⟨-, -, -, hLoc, -, -, -, hIso, -⟩ := hElem a 1 ha one_pos
  obtain ⟨-, -, -, -, -, -, hInter, hSupp⟩ := hLoc
  refine ⟨fun F hF hl => ?_, fun F hF v => ?_⟩
  · obtain ⟨hDep, hSet, hFin, hLeast⟩ := hSupp F hF hl
    refine ⟨hFin, hDep, fun 𝓜 h𝓜 hM => ?_⟩
    have hI := hInter F _ _ hF hl h𝓜 hSet hM hDep
    have hSub := hLeast (𝓜 ∩ YangMills.Construction.InfiniteLattice.observableSupport F)
      (fun b hb => h𝓜 hb.1) (hFin.subset Set.inter_subset_right) hI
    exact fun b hb => (hSub hb).1
  · obtain ⟨-, -, -, -, hCl, hSu, -⟩ :=
      hIso (YangMills.Construction.InfiniteLattice.shift v)
        (YangMills.Construction.InfiniteLattice.shift v)
    exact ⟨hCl.subset ⟨F, hF, rfl⟩, hSu F hF.1 hF.2.1⟩
theorem gibbsClass_antitone_period_holds {a : ℝ} (ha : 0 < a) (β : ℝ) :
    YangMills.Construction.InfiniteLattice.BasicStructure.gibbsClass_antitone_period ha β :=
  fun _ _ hle _ hν => ⟨hν.1, fun v hv => hν.2 v (hle hv)⟩
theorem kernelAndClassFacts_of {a : ℝ} (ha : 0 < a) {β : ℝ} (hβ : 0 < β)
    (hElem : YangMills.Construction.InfiniteLattice.ElementaryLatticeFacts)
    (hGibbs : YangMills.Construction.InfiniteLattice.GibbsClassEqGibbsStates) :
    YangMills.Construction.InfiniteLattice.BasicStructure.KernelAndClassFacts ha β := by
  obtain ⟨-, -, hSpec, -⟩ := hElem a β ha hβ
  obtain ⟨hEq, hPer⟩ := hGibbs.2.1 a ha β hβ
  refine ⟨fun W F hF => ?_, hEq, hPer, ?_⟩
  · obtain ⟨-, -, -, -, -, -, k₇, k₈, -, k₁₀, -⟩ := hSpec W
    obtain ⟨hO, -, hN⟩ := k₇ F hF
    refine ⟨hO, hN, fun H hH hm => ?_, fun hc => k₁₀ F hc⟩
    rw [mul_comm H F]
    exact k₈ F H hF hH hm
  · ext ν
    constructor
    · rintro ⟨k₁, k₂⟩
      exact ⟨hEq.subset k₁, fun v => k₂ v (AddSubgroup.mem_top v)⟩
    · rintro ⟨k₁, k₂⟩
      exact ⟨hEq.symm.subset k₁, fun v _ => k₂ v⟩
theorem periodLatticeFacts_of
    (hLev : YangMills.Construction.NormalFamilies.IntegerLevelsAndCubicPeriods.Statement)
    (hProp : YangMills.Construction.NormalFamilies.PeriodLatticeProperties) :
    YangMills.Construction.InfiniteLattice.BasicStructure.PeriodLatticeFacts := by
  intro n hn h hev h₂
  obtain ⟨k₁, k₃, k₄⟩ := hLev n hn h hev h₂
  obtain ⟨-, hFi, hIt⟩ := hProp.1 n hn h hev h₂
  obtain ⟨-, -, hq, -, -, -, -, -, hqi, hdi, -, -⟩ := hFi
  obtain ⟨-, -, -, hle, hi₂, -⟩ := hIt
  exact ⟨k₁, k₃, hle, hq, hi₂, k₄, hdi, hqi⟩
theorem statement_holds
    (h₁ : YangMills.Construction.InfiniteLattice.GaugeFieldSpaceAndDenseLocal)
    (h₂ : YangMills.Construction.InfiniteLattice.WeakCompactnessAndSymmetryOfStates)
    (h₃ : YangMills.Construction.InfiniteLattice.LinkSigmaAndDependence)
    (h₄ : YangMills.Construction.InfiniteLattice.LatticeMirrorNaming.Statement)
    (h₅ : YangMills.Construction.NormalFamilies.IntegerLevelsAndCubicPeriods.Statement)
    (hSym : YangMills.Construction.InfiniteLattice.FieldSpace.SymmetryProperties)
    (hElem : YangMills.Construction.InfiniteLattice.ElementaryLatticeFacts)
    (hGibbs : YangMills.Construction.InfiniteLattice.GibbsClassEqGibbsStates)
    (hProp : YangMills.Construction.NormalFamilies.PeriodLatticeProperties) :
    YangMills.Construction.InfiniteLattice.BasicStructure.Statement :=
  ⟨fun a ha _ hβ => ⟨h₁ a ha, symmetryActionFacts_of ha hSym hElem, h₂ a ha, h₃ a ha,
    supportFacts_of ha hElem, gibbsClass_antitone_period_holds ha _,
    kernelAndClassFacts_of ha hβ hElem hGibbs, h₄ a ha⟩,
    periodLatticeFacts_of h₅ hProp⟩
end YangMills.Construction.InfiniteLattice.BasicStructure
end
