import YangMills.Construction.InfiniteLattice.ConfigurationsAreFamiliesOnTheBondsAtEverySpacing
import YangMills.Construction.InfiniteLattice.FactsOfTheLocalFunctionsAtEverySpacing
import YangMills.Construction.InfiniteLattice.MeasurabilityIsDependenceOnVariablesAtEverySpacing
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace LocalFunctions
variable {a : ℝ}
theorem dependsOnlyOn_mono {S T : Set (Link a)} {F : GaugeField a → ℂ} (hST : S ⊆ T)
    (hF : DependsOnlyOn S F) : DependsOnlyOn T F :=
  fun U V hUV => hF U V fun ℓ hℓ => hUV ℓ (hST hℓ)
theorem mem_of_continuous [CompactSpace (GaugeField a)]
    (hM : MeasurableIffDependsOnly a) {F : GaugeField a → ℂ} (hcont : Continuous F)
    {S : Set (Link a)} (hS : IsLinkSet S) (hfin : S.Finite)
    (hdep : DependsOnlyOn S F) : F ∈ continuousLocalFunctions a := by
  have hobs : IsBoundedObservable F := by
    obtain ⟨C, hC⟩ := (isCompact_range hcont).isBounded.exists_norm_le
    exact ⟨hcont.measurable, C, fun U => hC _ (mem_range_self U)⟩
  exact ⟨hobs, (hM.2.2.2 F hobs).2 ⟨S, hS, hfin, hdep⟩, hcont⟩
theorem exists_finite_linkSet (hM : MeasurableIffDependsOnly a) {F : GaugeField a → ℂ}
    (hF : F ∈ continuousLocalFunctions a) :
    ∃ S : Set (Link a), IsLinkSet S ∧ S.Finite ∧ DependsOnlyOn S F :=
  (hM.2.2.2 F hF.1).1 hF.2.1
theorem add_mem_and_mul_mem [CompactSpace (GaugeField a)]
    (hM : MeasurableIffDependsOnly a) {F G : GaugeField a → ℂ}
    (hF : F ∈ continuousLocalFunctions a) (hG : G ∈ continuousLocalFunctions a) :
    F + G ∈ continuousLocalFunctions a ∧ F * G ∈ continuousLocalFunctions a := by
  obtain ⟨S, hS, hSf, hSd⟩ := exists_finite_linkSet hM hF
  obtain ⟨T, hT, hTf, hTd⟩ := exists_finite_linkSet hM hG
  have dS := dependsOnlyOn_mono (subset_union_left (t := T)) hSd
  have dT := dependsOnlyOn_mono (subset_union_right (s := S)) hTd
  have hunion : IsLinkSet (S ∪ T) := union_subset hS hT
  refine ⟨mem_of_continuous hM (hF.2.2.add hG.2.2) hunion (hSf.union hTf) fun U V hUV => ?_,
    mem_of_continuous hM (hF.2.2.mul hG.2.2) hunion (hSf.union hTf) fun U V hUV => ?_⟩
  · simp only [Pi.add_apply, dS U V hUV, dT U V hUV]
  · simp only [Pi.mul_apply, dS U V hUV, dT U V hUV]
theorem smul_mem [CompactSpace (GaugeField a)]
    (hM : MeasurableIffDependsOnly a) (c : ℂ) {F : GaugeField a → ℂ}
    (hF : F ∈ continuousLocalFunctions a) : c • F ∈ continuousLocalFunctions a := by
  obtain ⟨S, hS, hSf, hSd⟩ := exists_finite_linkSet hM hF
  refine mem_of_continuous hM (continuous_const.smul hF.2.2) hS hSf fun U V hUV => ?_
  simp only [Pi.smul_apply, hSd U V hUV]
theorem const_mem [CompactSpace (GaugeField a)]
    (hM : MeasurableIffDependsOnly a) (c : ℂ) :
    (fun _ => c) ∈ continuousLocalFunctions a :=
  mem_of_continuous hM continuous_const (S := ∅) (empty_subset _) finite_empty fun _ _ _ => rfl
theorem conj_mem [CompactSpace (GaugeField a)]
    (hM : MeasurableIffDependsOnly a) {F : GaugeField a → ℂ}
    (hF : F ∈ continuousLocalFunctions a) :
    (fun U => conj (F U)) ∈ continuousLocalFunctions a := by
  obtain ⟨S, hS, hSf, hSd⟩ := exists_finite_linkSet hM hF
  refine mem_of_continuous hM (Complex.continuous_conj.comp hF.2.2) hS hSf fun U V hUV => ?_
  simp only [hSd U V hUV]
def localStarSubalgebra [CompactSpace (GaugeField a)] (hM : MeasurableIffDependsOnly a) :
    StarSubalgebra ℂ C(GaugeField a, ℂ) where
  carrier := {f | (f : GaugeField a → ℂ) ∈ continuousLocalFunctions a}
  mul_mem' := fun hf hg => (add_mem_and_mul_mem hM hf hg).2
  add_mem' := fun hf hg => (add_mem_and_mul_mem hM hf hg).1
  algebraMap_mem' := fun c => const_mem hM c
  star_mem' := fun hf => conj_mem hM hf
theorem exists_positiveLink_ne (hres : IsHomeomorph (restrictToPositive (a := a)))
    {U V : GaugeField a} (hUV : U ≠ V) : ∃ ℓ ∈ positiveLinks a, U ℓ ≠ V ℓ := by
  by_contra hcon
  push Not at hcon
  exact hUV (hres.bijective.1 (funext fun ℓ => hcon ℓ.1 ℓ.2))
theorem continuous_matrixEntry (ℓ : Link a) (i j : Fin 2) :
    Continuous fun U : GaugeField a =>
      ((U ℓ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) i j := by
  have hlink : Continuous fun U : GaugeField a => U ℓ :=
    (continuous_apply ℓ).comp continuous_subtype_val
  have hentry : Continuous fun u : Matrices.ComplexMatrix2.specialUnitary =>
      (u : Matrices.ComplexMatrix2) i j :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact hentry.comp hlink
theorem separatesPoints [CompactSpace (GaugeField a)] (hM : MeasurableIffDependsOnly a)
    (hres : IsHomeomorph (restrictToPositive (a := a))) :
    (localStarSubalgebra hM).SeparatesPoints := by
  intro U V hUV
  obtain ⟨ℓ, hℓ, hne⟩ := exists_positiveLink_ne hres hUV
  obtain ⟨i, j, hij⟩ : ∃ i j,
      ((U ℓ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) i j ≠
        ((V ℓ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) i j := by
    by_contra hcon
    push Not at hcon
    exact hne (Subtype.ext (Matrix.ext hcon))
  have hmem : (fun W : GaugeField a =>
      ((W ℓ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) i j) ∈
      continuousLocalFunctions a :=
    mem_of_continuous hM (continuous_matrixEntry ℓ i j) (S := {ℓ}) (singleton_subset_iff.2 hℓ)
      (finite_singleton ℓ) fun W W' hW => by rw [hW ℓ (mem_singleton ℓ)]
  exact ⟨_, ⟨⟨_, continuous_matrixEntry ℓ i j⟩, hmem, rfl⟩, hij⟩
theorem exists_uniformly_close [CompactSpace (GaugeField a)] (hM : MeasurableIffDependsOnly a)
    (hres : IsHomeomorph (restrictToPositive (a := a))) (f : C(GaugeField a, ℂ)) (ε : ℝ)
    (hε : 0 < ε) : ∃ F ∈ continuousLocalFunctions a, ∀ U, ‖f U - F U‖ < ε := by
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (localStarSubalgebra hM) (separatesPoints hM hres)
  have hcl : f ∈ closure ((localStarSubalgebra hM : Set C(GaugeField a, ℂ))) := by
    have : f ∈ (localStarSubalgebra hM).topologicalClosure := by
      rw [htop]
      trivial
    exact this
  obtain ⟨G, hG, hdist⟩ := Metric.mem_closure_iff.mp hcl ε hε
  refine ⟨G, hG, fun U => ?_⟩
  have := ContinuousMap.dist_apply_le_dist (f := f) (g := G) U
  rw [dist_eq_norm] at this
  exact this.trans_lt hdist
theorem integrable_of_continuous [CompactSpace (GaugeField a)] (μ : Measure (GaugeField a))
    [IsProbabilityMeasure μ] {F : GaugeField a → ℂ} (hcont : Continuous F) : Integrable F μ :=
  hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
theorem measure_eq_of_integral_eq [CompactSpace (GaugeField a)]
    [TopologicalSpace.MetrizableSpace (GaugeField a)]
    (hM : MeasurableIffDependsOnly a)
    (hres : IsHomeomorph (restrictToPositive (a := a))) (μ ν : Measure (GaugeField a))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hint : ∀ F ∈ continuousLocalFunctions a, stateEval μ F = stateEval ν F) : μ = ν := by
  have happrox : HasOuterApproxClosed (GaugeField a) := by
    let _ := TopologicalSpace.metrizableSpaceMetric (GaugeField a)
    infer_instance
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  let g : C(GaugeField a, ℂ) :=
    ⟨fun U => (f U : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hcomplex : ∫ U, g U ∂μ = ∫ U, g U ∂ν := by
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨F, hF, hclose⟩ := exists_uniformly_close hM hres g (ε / 2) (half_pos hε)
    have hbound : ∀ (ρ : Measure (GaugeField a)) [IsProbabilityMeasure ρ],
        ‖∫ U, g U ∂ρ - ∫ U, F U ∂ρ‖ ≤ ε / 2 := by
      intro ρ _
      rw [← integral_sub (integrable_of_continuous ρ g.continuous)
        (integrable_of_continuous ρ hF.2.2)]
      have := norm_integral_le_of_norm_le_const (μ := ρ) (f := fun U => g U - F U) (C := ε / 2)
        (Eventually.of_forall fun U => (hclose U).le)
      simpa using this
    have hFF : ∫ U, F U ∂μ = ∫ U, F U ∂ν := hint F hF
    have hμ := hbound μ
    have hν := hbound ν
    rw [dist_eq_norm]
    calc ‖∫ U, g U ∂μ - ∫ U, g U ∂ν‖
        = ‖(∫ U, g U ∂μ - ∫ U, F U ∂μ) - (∫ U, g U ∂ν - ∫ U, F U ∂ν)‖ := by
          rw [hFF]
          congr 1
          ring
      _ ≤ ‖∫ U, g U ∂μ - ∫ U, F U ∂μ‖ + ‖∫ U, g U ∂ν - ∫ U, F U ∂ν‖ := norm_sub_le _ _
      _ ≤ ε := by linarith
  have hreal : ((∫ U, f U ∂μ : ℝ) : ℂ) = ((∫ U, f U ∂ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    exact hcomplex
  exact Complex.ofReal_injective hreal
theorem dependsOnlyOn_inter (hres : IsHomeomorph (restrictToPositive (a := a)))
    {F : GaugeField a → ℂ} {S T : Set (Link a)} (hS : IsLinkSet S) (hT : IsLinkSet T)
    (dS : DependsOnlyOn S F) (dT : DependsOnlyOn T F) :
    DependsOnlyOn (S ∩ T) F := by
  classical
  intro U V hUV
  obtain ⟨W, hW⟩ := hres.bijective.2 fun ℓ : positiveLinks a =>
    if ℓ.1 ∈ S then U ℓ.1 else V ℓ.1
  have hWval : ∀ ℓ (hℓ : ℓ ∈ positiveLinks a), W ℓ = if ℓ ∈ S then U ℓ else V ℓ :=
    fun ℓ hℓ => congrFun hW ⟨ℓ, hℓ⟩
  have eUW : F U = F W := dS U W fun ℓ hℓ => by rw [hWval ℓ (hS hℓ), if_pos hℓ]
  have eWV : F W = F V := dT W V fun ℓ hℓ => by
    rw [hWval ℓ (hT hℓ)]
    by_cases hℓS : ℓ ∈ S
    · rw [if_pos hℓS]
      exact hUV ℓ ⟨hℓS, hℓ⟩
    · rw [if_neg hℓS]
  exact eUW.trans eWV
theorem observableSupport_properties (hres : IsHomeomorph (restrictToPositive (a := a)))
    {F : GaugeField a → ℂ}
    (hloc : ∃ S : Set (Link a), IsLinkSet S ∧ S.Finite ∧ DependsOnlyOn S F) :
    DependsOnlyOn (observableSupport F) F ∧
      IsLinkSet (observableSupport F) ∧ (observableSupport F).Finite ∧
      ∀ S : Set (Link a), IsLinkSet S → S.Finite → DependsOnlyOn S F →
        observableSupport F ⊆ S := by
  classical
  have hex : ∃ n : ℕ, ∃ S : Set (Link a), (IsLinkSet S ∧ S.Finite ∧
      DependsOnlyOn S F) ∧ S.ncard = n := by
    obtain ⟨S, hS⟩ := hloc
    exact ⟨_, S, hS, rfl⟩
  obtain ⟨M, hM, hcard⟩ := Nat.find_spec hex
  have hleast : ∀ S : Set (Link a), IsLinkSet S → S.Finite → DependsOnlyOn S F →
      M ⊆ S := by
    intro S hS hSf hSd
    have hinter : IsLinkSet (M ∩ S) ∧ (M ∩ S).Finite ∧ DependsOnlyOn (M ∩ S) F :=
      ⟨inter_subset_left.trans hM.1, hM.2.1.inter_of_left _,
        dependsOnlyOn_inter hres hM.1 hS hM.2.2 hSd⟩
    have hle : M.ncard ≤ (M ∩ S).ncard := by
      rw [hcard]
      exact Nat.find_min' hex ⟨_, hinter, rfl⟩
    exact inter_eq_left.mp (eq_of_subset_of_ncard_le inter_subset_left hle hM.2.1)
  have hsupp : observableSupport F = M :=
    Subset.antisymm (sInter_subset_of_mem hM)
      (subset_sInter fun S hS => hleast S hS.1 hS.2.1 hS.2.2)
  rw [hsupp]
  exact ⟨hM.2.2, hM.1, hM.2.1, hleast⟩
end LocalFunctions
open LocalFunctions in
theorem localFunctionPropertiesForAllSpacings_holds
    (hfields : GaugeFieldsAreLinkFamiliesForAllSpacings)
    (hmeas : MeasurableIffDependsOnlyAllSpacings)
    (hspace : FieldSpace.SymmetryProperties) :
    LocalFunctionPropertiesForAllSpacings := by
  intro a ha
  obtain ⟨⟨hcomp, hmet, -⟩, -⟩ := hspace a ha
  have hres := (hfields a ha).1
  have hM := hmeas a ha
  unfold LocalFunctionProperties
  exact ⟨fun F hF G hG => add_mem_and_mul_mem hM hF hG, fun c F hF => smul_mem hM c hF,
    fun c => const_mem hM c, fun F hF => conj_mem hM hF,
    fun f ε hε => exists_uniformly_close hM hres f ε hε,
    fun μ ν _ _ h => measure_eq_of_integral_eq hM hres μ ν h,
    fun F S T _ _ hS hT dS dT => dependsOnlyOn_inter hres hS hT dS dT,
    fun F hO hL => observableSupport_properties hres ((hM.2.2.2 F hO).1 hL)⟩
end YangMills.Construction.InfiniteLattice
