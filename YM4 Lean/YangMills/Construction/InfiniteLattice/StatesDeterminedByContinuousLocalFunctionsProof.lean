import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.StatesDeterminedByContinuousLocalFunctions
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter YangMills.Construction.InfiniteLattice.WilsonOperator
open scoped BoundedContinuousFunction
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CylinderFunctionsDetermineStates
variable {a : ℝ}
instance t2Space_gaugeField : T2Space (GaugeField a) :=
  inferInstanceAs
    (T2Space {U : Link a → Matrices.ComplexMatrix2.specialUnitary // ∀ e, U e.opposite = (U e)⁻¹})
theorem determined_of_pos (ha : 0 < a) : StatesDeterminedOnCylinderFunctions a := by
  intro μ μ' hμ
  have := secondCountable_specialUnitary
  have : Countable (Link a) := countable_link
  have := μ.2
  have := μ'.2
  have hmeas : Measurable (gaugeFieldHomeomorph ha) :=
    (gaugeFieldHomeomorph ha).continuous.measurable
  have hfin : ∀ J : Finset (positiveLinkSet a),
      ((μ.1.map (gaugeFieldHomeomorph ha)).map J.restrict :
          Measure (J → Matrices.ComplexMatrix2.specialUnitary)) =
        (μ'.1.map (gaugeFieldHomeomorph ha)).map J.restrict := by
    intro J
    have hres : Continuous (J.restrict :
        LinkVariables (positiveLinkSet a) → J → Matrices.ComplexMatrix2.specialUnitary) :=
      continuous_pi fun i => continuous_apply _
    have hresm := hres.measurable
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    have pushdown : ∀ ρ : GaugeFieldProbability a,
        ∫ x, f x ∂((ρ.1.map (gaugeFieldHomeomorph ha)).map J.restrict) =
          ∫ U, f (J.restrict (gaugeFieldHomeomorph ha U)) ∂ρ.1 := by
      intro ρ
      have e₁ := integral_map (μ := ρ.1.map (gaugeFieldHomeomorph ha)) hresm.aemeasurable
        (f := fun x => f x) f.continuous.aestronglyMeasurable
      have e₂ := integral_map (μ := ρ.1) hmeas.aemeasurable (f := fun x => f (J.restrict x))
        (f.continuous.comp hres).aestronglyMeasurable
      exact e₁.trans e₂
    let Φ : GaugeField a → ℂ := fun U =>
      ((f (J.restrict (gaugeFieldHomeomorph ha U)) : ℝ) : ℂ)
    have hΦ : Φ ∈ continuousCylinderFunctions a := by
      refine ⟨Complex.continuous_ofReal.comp
        (f.continuous.comp (hres.comp (gaugeFieldHomeomorph ha).continuous)),
        (fun e : positiveLinkSet a => (e : Link a)) '' (J : Set _), J.finite_toSet.image _,
        ?_, ?_⟩
      · rintro _ ⟨e, -, rfl⟩
        exact e.2
      · intro U U' hUU'
        have : J.restrict (gaugeFieldHomeomorph ha U) =
            J.restrict (gaugeFieldHomeomorph ha U') := by
          funext i
          exact congrFun hUU' ⟨i.1.1, mem_image_of_mem _ i.2⟩
        simp only [Φ, this]
    have heq := hμ Φ hΦ
    simp only [GaugeFieldProbability.expect, Φ, integral_complex_ofReal] at heq
    rw [pushdown μ, pushdown μ']
    exact_mod_cast heq
  have hproj : (μ.1.map (gaugeFieldHomeomorph ha)) =
      (μ'.1.map (gaugeFieldHomeomorph ha)) :=
    IsProjectiveLimit.unique (P := fun J =>
        (μ.1.map (gaugeFieldHomeomorph ha)).map J.restrict)
      (fun _ => rfl) (fun J => (hfin J).symm)
  exact Subtype.ext
    ((gaugeFieldHomeomorph ha).toMeasurableEquiv.map_measurableEquiv_injective hproj)
theorem continuous_pullbackField (g : LatticeSymmetry a) : Continuous g.pullbackField := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetry.continuous_pullbackField <;> assumption
theorem symmetriesAct_of_pos (ha : 0 < a) : SymmetriesActOnCylinderFunctions a := by
  intro g
  have hg := continuous_pullbackField g
  have hgm : Measurable g.pullbackField := hg.measurable
  refine ⟨fun F hF => hF.comp hg, ?_, ?_⟩
  · intro F hF
    obtain ⟨hcont, S, hSfin, hFS⟩ := mem_continuousCylinderFunctions_iff.mp hF
    refine mem_continuousCylinderFunctions_iff.mpr
      ⟨hcont.comp hg, g.linkMap '' S, hSfin.image _, fun U U' hUU' => hFS _ _ ?_⟩
    funext e
    exact congrFun hUU' ⟨g.linkMap e, mem_image_of_mem _ e.2⟩
  · intro μ hμ A hA
    have := μ.2
    let μg : GaugeFieldProbability a :=
      ⟨μ.1.map g.pullbackField, Measure.isProbabilityMeasure_map hgm.aemeasurable⟩
    have hsame : μg = μ := determined_of_pos ha μg μ fun F hF => by
      refine Eq.trans ?_ (hμ F hF)
      exact integral_map hgm.aemeasurable hF.1.aestronglyMeasurable
    have hpush : μ.1.map g.pullbackField = μ.1 := congrArg Subtype.val hsame
    have hA' := integral_map (μ := μ.1) hgm.aemeasurable hA.1.aestronglyMeasurable
    rw [hpush] at hA'
    exact hA'.symm
theorem compactSpace_of_pos (ha : 0 < a) : CompactSpace (GaugeFieldProbability a) := by
  have : CompactSpace (GaugeField a) := (gaugeFieldHomeomorph ha).symm.compactSpace
  let ψ : ProbabilityMeasure (GaugeField a) → GaugeFieldProbability a :=
    fun m => ⟨m, inferInstance⟩
  have hψ : Function.Surjective ψ := fun μ => ⟨⟨μ.1, μ.2⟩, rfl⟩
  have hψc : Continuous ψ := by
    refine continuous_iInf_rng.mpr fun F => continuous_induced_rng.mpr ?_
    exact continuous_iff_continuousAt.mpr fun m =>
      (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp tendsto_id F
  have hrange : IsCompact (range ψ) := isCompact_range hψc
  rw [hψ.range_eq] at hrange
  exact isCompact_univ_iff.mp hrange
theorem holds : Statement := by
  intro L K _ hL _
  have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    exact zpow_pos this _
  exact ⟨determined_of_pos ha, symmetriesAct_of_pos ha, compactSpace_of_pos ha⟩
end YangMills.Construction.InfiniteLattice.CylinderFunctionsDetermineStates
