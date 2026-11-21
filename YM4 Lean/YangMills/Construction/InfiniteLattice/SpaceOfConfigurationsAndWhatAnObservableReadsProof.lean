import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservablesProof
import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorusProof
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometriesProof
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndWhatAnObservableReads
import YangMills.Construction.Measures.ContinuousFunctionsAndProbabilityMeasuresOnACompactMetricSpace
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace LatticePhases.ObservableRegions
section LinkValues
variable {a : ℝ}
theorem mem_positiveLinks_or_opposite (b : Link a) :
    b ∈ positiveLinks a ∨ b.opposite ∈ positiveLinks a := by
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · exact Or.inl ⟨μ, h⟩
  · refine Or.inr ⟨μ, ?_⟩
    show b.initial - b.terminal = axisStep a μ
    rw [← neg_sub, h, neg_neg]
theorem apply_eq_inv_opposite (U : GaugeField a) (b : Link a) : U b = (U b.opposite)⁻¹ :=
  U.2 b.opposite
theorem continuous_eval_link (b : Link a) : Continuous (fun U : GaugeField a => U b) := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem continuous_of_forall_link {X : Type*} [TopologicalSpace X] {f : X → GaugeField a}
    (h : ∀ b, Continuous fun x => f x b) : Continuous f := by apply _root_.YangMills.Construction.InfiniteLattice.FieldSpace.continuous_of_forall_link <;> assumption
theorem compactSpace_gaugeField : CompactSpace (GaugeField a) := by apply _root_.YangMills.SharedProofs.p823 <;> assumption
theorem borel_eq_linkSigma_univ :
    (inferInstance : MeasurableSpace (GaugeField a)) = linkSigma (univ : Set (Link a)) := by apply _root_.YangMills.Construction.InfiniteLattice.FieldSymmetries.borel_eq_linkSigma <;> assumption
theorem measurable_eval_of_mem {L : Set (Link a)} {b : Link a} (hb : b ∈ L) :
    Measurable[linkSigma L] (fun U : GaugeField a => U b) := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.measurable_link_eval_of_mem <;> assumption
theorem borel_eq_linkSigma_positive :
    borel (GaugeField a) = linkSigma (positiveLinks a) := by
  have h : borel (GaugeField a) = linkSigma (univ : Set (Link a)) := borel_eq_linkSigma_univ
  rw [h]
  apply le_antisymm
  · refine iSup₂_le fun b _ => measurable_iff_comap_le.1 ?_
    rcases mem_positiveLinks_or_opposite b with hb | hb
    · exact measurable_eval_of_mem hb
    · have hm : Measurable[linkSigma (positiveLinks a)]
          (fun U : GaugeField a => (U b.opposite)⁻¹) :=
        (continuous_inv.measurable :
            Measurable fun g : Matrices.ComplexMatrix2.specialUnitary => g⁻¹).comp
          (measurable_eval_of_mem hb)
      have he : (fun U : GaugeField a => U b) = fun U => (U b.opposite)⁻¹ :=
        funext fun U => apply_eq_inv_opposite U b
      rw [he]
      exact hm
  · exact iSup₂_le fun b _ => le_iSup₂_of_le b (mem_univ b) le_rfl
theorem regionSigma_le_borel (S : Set AmbientSpace) :
    regionSigma S ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  iSup₂_le fun b _ => (continuous_eval_link b).measurable.comap_le
theorem apply_eq_of_eqOn_links {L : Set (Link a)} {F : GaugeField a → ℂ}
    (hF : Measurable[linkSigma L] F)
    {U U' : GaugeField a} (h : ∀ b ∈ L, U b = U' b) : F U = F U' := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.eq_of_eqOn_links <;> assumption
open Classical in
theorem truncate_apply (S : Set AmbientSpace) (U : GaugeField a) (b : Link a) :
    truncate S U b = if b ∈ linksWithin S then U b else 1 :=
  rfl
theorem continuous_truncate (S : Set AmbientSpace) :
    Continuous (truncate S : GaugeField a → GaugeField a) := by
  refine continuous_of_forall_link fun b => ?_
  by_cases h : b ∈ linksWithin S
  · simpa only [truncate_apply, if_pos h] using continuous_eval_link b
  · simpa only [truncate_apply, if_neg h] using continuous_const
theorem measurable_truncate (S : Set AmbientSpace) :
    Measurable[regionSigma S] (truncate S : GaugeField a → GaugeField a) := by
  have hv : ∀ b : Link a, Measurable[regionSigma S] (fun U : GaugeField a => truncate S U b) := by
    intro b
    by_cases h : b ∈ linksWithin S
    · simpa only [truncate_apply, if_pos h] using measurable_eval_of_mem h
    · simpa only [truncate_apply, if_neg h] using @measurable_const _ _ _ (regionSigma S) _
  have hb : (inferInstance : MeasurableSpace (GaugeField a)) =
      linkSigma (univ : Set (Link a)) := borel_eq_linkSigma_univ
  refine measurable_iff_comap_le.2
    ((congrArg (MeasurableSpace.comap (truncate S)) hb).le.trans ?_)
  simp only [linkSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  exact iSup₂_le fun b _ => measurable_iff_comap_le.1 (hv b)
theorem mem_regionObservables_of_measurable {S : Set AmbientSpace} {F : GaugeField a → ℂ}
    (hF : Measurable[regionSigma S] F)
    (hb : ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C) : F ∈ regionObservables a S :=
  ⟨⟨hF.mono (regionSigma_le_borel S) le_rfl, hb⟩, hF⟩
theorem tfae_region (S : Set AmbientSpace) (F : GaugeField a → ℂ) (hF : IsBoundedObservable F) :
    List.TFAE
      [F ∈ regionObservables a S,
        ∀ U U' : GaugeField a, (∀ b : Link a, b ∈ linksWithin S → U b = U' b) → F U = F U',
        F = F ∘ truncate S] := by
  tfae_have 1 → 2 := fun h U U' hU => apply_eq_of_eqOn_links h.2 hU
  tfae_have 2 → 3 := fun h => funext fun U => h U (truncate S U) fun b hb => by
    rw [truncate_apply, if_pos hb]
  tfae_have 3 → 1 := fun h => by
    refine ⟨hF, ?_⟩
    show Measurable[regionSigma S] F
    rw [h]
    exact hF.1.comp (measurable_truncate S)
  tfae_finish
theorem regionObservables_mono {S S' : Set AmbientSpace} (h : S ⊆ S') :
    regionObservables a S ⊆ regionObservables a S' := by apply _root_.YangMills.Construction.InfiniteLattice.SymmetryAction.boundedRegionObservables_mono <;> assumption
theorem truncate_truncate (S S' : Set AmbientSpace) (U : GaugeField a) :
    truncate S (truncate S' U) = truncate (S ∩ S') U := by
  refine Subtype.ext (funext fun b => ?_)
  show truncate S (truncate S' U) b = truncate (S ∩ S') U b
  by_cases h : b ∈ linksWithin S <;> by_cases h' : b ∈ linksWithin S'
  · have : b ∈ linksWithin (S ∩ S') := ⟨⟨h.1, h'.1⟩, h.2, h'.2⟩
    simp only [truncate_apply, if_pos h, if_pos h', if_pos this]
  · have : b ∉ linksWithin (S ∩ S') := fun k => h' ⟨k.1.2, k.2.2⟩
    simp only [truncate_apply, if_pos h, if_neg h', if_neg this]
  · have : b ∉ linksWithin (S ∩ S') := fun k => h ⟨k.1.1, k.2.1⟩
    simp only [truncate_apply, if_neg h, if_neg this]
  · have : b ∉ linksWithin (S ∩ S') := fun k => h ⟨k.1.1, k.2.1⟩
    simp only [truncate_apply, if_neg h, if_neg this]
theorem regionObservables_inter (S S' : Set AmbientSpace) :
    regionObservables a S ∩ regionObservables a S' = regionObservables a (S ∩ S') := by
  apply Subset.antisymm
  · rintro F ⟨hF, hF'⟩
    have h3 : F = F ∘ truncate S := ((tfae_region S F hF.1).out 0 2).1 hF
    have h3' : F = F ∘ truncate S' := ((tfae_region S' F hF.1).out 0 2).1 hF'
    refine ((tfae_region (S ∩ S') F hF.1).out 0 2).2 (funext fun U => ?_)
    show F U = F (truncate (S ∩ S') U)
    rw [← truncate_truncate]
    calc F U = F (truncate S' U) := congrFun h3' U
      _ = F (truncate S (truncate S' U)) := congrFun h3 _
  · exact subset_inter (regionObservables_mono inter_subset_left)
      (regionObservables_mono inter_subset_right)
theorem regionObservables_algebra (S : Set AmbientSpace) :
    (∀ c : ℂ, (fun _ => c) ∈ regionObservables a S) ∧
    (∀ F ∈ regionObservables a S, ∀ F' ∈ regionObservables a S,
      F + F' ∈ regionObservables a S ∧ F * F' ∈ regionObservables a S) ∧
    (∀ c : ℂ, ∀ F ∈ regionObservables a S, c • F ∈ regionObservables a S) ∧
    ∀ F ∈ regionObservables a S, (fun U => conj (F U)) ∈ regionObservables a S := by
  refine ⟨fun c => mem_regionObservables_of_measurable (@measurable_const _ _ _ (regionSigma S) c)
      ⟨‖c‖, fun _ => le_rfl⟩,
    fun F hF F' hF' => ?_, fun c F hF => ?_, fun F hF => ?_⟩
  · obtain ⟨C, hC⟩ := hF.1.2
    obtain ⟨C', hC'⟩ := hF'.1.2
    have m : Measurable[regionSigma S] F := hF.2
    have m' : Measurable[regionSigma S] F' := hF'.2
    refine ⟨mem_regionObservables_of_measurable (m.add m') ⟨C + C', fun U => ?_⟩,
      mem_regionObservables_of_measurable (m.mul m') ⟨C * C', fun U => ?_⟩⟩
    · exact (norm_add_le _ _).trans (add_le_add (hC U) (hC' U))
    · show ‖F U * F' U‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (hC U) (hC' U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
  · obtain ⟨C, hC⟩ := hF.1.2
    have m : Measurable[regionSigma S] F := hF.2
    refine mem_regionObservables_of_measurable (m.const_smul c) ⟨‖c‖ * C, fun U => ?_⟩
    show ‖c • F U‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC U) (norm_nonneg _)
  · obtain ⟨C, hC⟩ := hF.1.2
    have m : Measurable[regionSigma S] F := hF.2
    refine mem_regionObservables_of_measurable (Complex.continuous_conj.measurable.comp m)
      ⟨C, fun U => ?_⟩
    simpa using hC U
end LinkValues
section FieldDistance
variable (D : Setup)
def linkAt (k : ℕ+) : Link D.mesh := (D.linkEnum k).1
def fieldDistTerm (U U' : GaugeField D.mesh) (k : ℕ+) : ℝ :=
  (2 : ℝ)⁻¹ ^ (k : ℕ) * Matrices.ComplexMatrix2.operatorNorm
    ((U (linkAt D k) : Matrices.ComplexMatrix2) - (U' (linkAt D k) : Matrices.ComplexMatrix2))
theorem fieldDist_eq_tsum (U U' : GaugeField D.mesh) :
    D.fieldDist U U' = ∑' k, fieldDistTerm D U U' k :=
  rfl
theorem norm_specialUnitary (g : Matrices.ComplexMatrix2.specialUnitary) :
    ‖(g : Matrices.ComplexMatrix2)‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
theorem summable_geometric_bound : Summable fun k : ℕ+ => (2 : ℝ)⁻¹ ^ (k : ℕ) * 2 :=
  ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
    PNat.coe_injective).mul_right 2
theorem fieldDistTerm_nonneg (U U' : GaugeField D.mesh) (k : ℕ+) : 0 ≤ fieldDistTerm D U U' k :=
  mul_nonneg (by positivity) (norm_nonneg _)
theorem fieldDistTerm_le (U U' : GaugeField D.mesh) (k : ℕ+) :
    fieldDistTerm D U U' k ≤ (2 : ℝ)⁻¹ ^ (k : ℕ) * 2 := by
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sub_le _ _).trans ?_
  rw [norm_specialUnitary, norm_specialUnitary]
  norm_num
theorem summable_fieldDistTerm (U U' : GaugeField D.mesh) : Summable (fieldDistTerm D U U') :=
  Summable.of_nonneg_of_le (fieldDistTerm_nonneg D U U') (fieldDistTerm_le D U U')
    (summable_geometric_bound)
theorem fieldDistTerm_le_fieldDist (U U' : GaugeField D.mesh) (k : ℕ+) :
    fieldDistTerm D U U' k ≤ D.fieldDist U U' :=
  (summable_fieldDistTerm D U U').le_tsum k fun j _ => fieldDistTerm_nonneg D U U' j
theorem gaugeField_ext_of_linkAt {U U' : GaugeField D.mesh}
    (h : ∀ k, U (linkAt D k) = U' (linkAt D k)) : U = U' := by
  have hp : ∀ b ∈ positiveLinks D.mesh, U b = U' b := fun b hb => by
    have := h (D.linkEnum.symm ⟨b, hb⟩)
    simpa [linkAt] using this
  refine Subtype.ext (funext fun b => ?_)
  rcases mem_positiveLinks_or_opposite b with hb | hb
  · exact hp b hb
  · show U b = U' b
    rw [apply_eq_inv_opposite U b, apply_eq_inv_opposite U' b, hp _ hb]
@[reducible] def fieldMetric : MetricSpace (GaugeField D.mesh) where
  dist := D.fieldDist
  dist_self U := by
    show D.fieldDist U U = 0
    simp [Setup.fieldDist]
  dist_comm U U' := by
    show D.fieldDist U U' = D.fieldDist U' U
    rw [fieldDist_eq_tsum, fieldDist_eq_tsum]
    exact tsum_congr fun k => by
      simp only [fieldDistTerm, Matrices.ComplexMatrix2.operatorNorm]; rw [norm_sub_rev]
  dist_triangle U U' U'' := by
    show D.fieldDist U U'' ≤ D.fieldDist U U' + D.fieldDist U' U''
    rw [fieldDist_eq_tsum, fieldDist_eq_tsum, fieldDist_eq_tsum,
      ← (summable_fieldDistTerm D U U').tsum_add (summable_fieldDistTerm D U' U'')]
    refine Summable.tsum_le_tsum (fun k => ?_) (summable_fieldDistTerm D U U'')
      ((summable_fieldDistTerm D U U').add (summable_fieldDistTerm D U' U''))
    simp only [fieldDistTerm, Matrices.ComplexMatrix2.operatorNorm, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  eq_of_dist_eq_zero {U U'} h := by
    have h0 : D.fieldDist U U' = 0 := h
    refine gaugeField_ext_of_linkAt D fun k => ?_
    have hk : fieldDistTerm D U U' k ≤ 0 := h0 ▸ fieldDistTerm_le_fieldDist D U U' k
    have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (k : ℕ) := by positivity
    have hn : ‖(U (linkAt D k) : Matrices.ComplexMatrix2) -
        (U' (linkAt D k) : Matrices.ComplexMatrix2)‖ ≤ 0 :=
      nonpos_of_mul_nonpos_right hk hpos
    exact Subtype.ext (sub_eq_zero.1 (norm_le_zero_iff.1 hn))
def FieldMetricCopy : Type := GaugeField D.mesh
instance : MetricSpace (FieldMetricCopy D) := fieldMetric D
def toFieldMetricCopy : GaugeField D.mesh → FieldMetricCopy D := id
theorem continuous_fieldDist_left (U' : GaugeField D.mesh) :
    Continuous fun U : GaugeField D.mesh => D.fieldDist U U' := by
  refine continuous_tsum (u := fun k : ℕ+ => (2 : ℝ)⁻¹ ^ (k : ℕ) * 2) (fun k => ?_)
    (summable_geometric_bound) fun k U => ?_
  · refine continuous_const.mul ?_
    exact ((continuous_subtype_val.comp (continuous_eval_link _)).sub continuous_const).norm
  · show ‖fieldDistTerm D U U' k‖ ≤ _
    rw [Real.norm_of_nonneg (fieldDistTerm_nonneg D U U' k)]
    exact fieldDistTerm_le D U U' k
theorem continuous_toFieldMetricCopy : Continuous (toFieldMetricCopy D) := by
  refine continuous_iff_continuousAt.2 fun U => Metric.continuousAt_iff'.2 fun ε hε => ?_
  have h := (continuous_fieldDist_left D U).tendsto U
  have h0 : D.fieldDist U U = 0 := dist_self (toFieldMetricCopy D U)
  rw [h0] at h
  exact h.eventually (gt_mem_nhds hε)
theorem fieldMetric_topology_eq :
    (fieldMetric D).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (GaugeField D.mesh)) := by
  have := compactSpace_gaugeField (a := D.mesh)
  have hh : IsHomeomorph (toFieldMetricCopy D) :=
    isHomeomorph_iff_continuous_bijective.2
      ⟨continuous_toFieldMetricCopy D, Function.bijective_id⟩
  exact (hh.isInducing.eq_induced.trans
    (@induced_id (GaugeField D.mesh) (fieldMetric D).toUniformSpace.toTopologicalSpace)).symm
@[reducible] def fieldMetricCompatible : MetricSpace (GaugeField D.mesh) :=
  (fieldMetric D).replaceTopology (fieldMetric_topology_eq D).symm
theorem compactnessAndTruncation_holds (S : Set AmbientSpace) : CompactnessAndTruncation D S :=
  ⟨⟨fieldMetric D, fun _ _ => rfl, fieldMetric_topology_eq D⟩, compactSpace_gaugeField,
    borel_eq_linkSigma_positive, continuous_truncate S, measurable_truncate S⟩
theorem exists_scaledCube (F : GaugeField D.mesh → ℂ) (hF : IsBoundedObservable F)
    (hl : IsLocalObservable F) :
    ∃ j : ℕ, 1 ≤ j ∧ F ∈ regionObservables D.mesh (scaledCube D j) := by
  obtain ⟨Q, hQ, hm⟩ := hl
  obtain ⟨r, hr⟩ := hQ.subset_closedBall (0 : AmbientSpace)
  obtain ⟨j, hj⟩ := exists_nat_ge (max 1 (r / D.mesh))
  have ha := D.mesh_pos
  have hj1 : (1 : ℝ) ≤ j := (le_max_left _ _).trans hj
  have hrj : r ≤ D.mesh * j := by
    have : r / D.mesh ≤ j := (le_max_right _ _).trans hj
    rw [div_le_iff₀ ha] at this
    linarith
  refine ⟨j, by exact_mod_cast hj1, regionObservables_mono (fun x hx => ?_) ⟨hF, hm⟩⟩
  have hx' : ‖x‖ ≤ r := by simpa using hr hx
  intro μ
  have hμ : |x μ| ≤ r := (norm_le_pi_norm x μ).trans hx'
  have := abs_le.1 (hμ.trans hrj)
  exact ⟨by linarith [this.1], this.2⟩
theorem truncatedContinuous_holds (S : Set AmbientSpace) : TruncatedContinuous D S := by
  intro F
  have := compactSpace_gaugeField (a := D.mesh)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn F.continuous.continuousOn
  have hC' : ∀ U, ‖F U‖ ≤ C := fun U => hC U (mem_univ U)
  refine ⟨F.continuous.comp (continuous_truncate S),
    mem_regionObservables_of_measurable (F.continuous.measurable.comp (measurable_truncate S))
      ⟨C, fun U => hC' _⟩, ?_⟩
  refine Real.iSup_le (fun U => ?_) (Real.iSup_nonneg fun _ => norm_nonneg _)
  exact le_ciSup (f := fun x => ‖F x‖) ⟨C, by rintro _ ⟨x, rfl⟩; exact hC' x⟩ (truncate S U)
end FieldDistance
theorem exists_continuous_L2_near {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (hc : Measures.CompactMetricProbability.CompactMetricProbabilityFacts)
    (ρ : ProbMeasure X) {F : X → ℂ} (hF : Measurable F) (hb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) {ε : ℝ}
    (hε : 0 < ε) : ∃ H : X → ℂ, Continuous H ∧ ∫ x, ‖F x - H x‖ ^ 2 ∂ρ.toMeasure < ε := by
  obtain ⟨C, hC⟩ := hb
  have hmem : MemLp F 2 ρ.toMeasure :=
    MemLp.of_bound hF.aestronglyMeasurable C (ae_of_all _ hC)
  have hd := ((hc X).2.1 ρ).2
  obtain ⟨z, hz, ⟨H, rfl⟩⟩ :=
    Metric.dense_iff.1 hd (hmem.toLp F) (Real.sqrt ε) (Real.sqrt_pos.2 hε)
  refine ⟨H, H.continuous, ?_⟩
  have hz' := mem_ball_iff_norm.1 hz
  set Y : ρ.Lp2 := ContinuousMap.toLp 2 ρ.toMeasure ℂ H - hmem.toLp F with hYdef
  have hsq : ‖Y‖ ^ 2 = ∫ x, ‖Y x‖ ^ 2 ∂ρ.toMeasure := by
    rw [ProbMeasure.norm_Lp2_eq_l2Norm, ProbMeasure.l2Norm, ← Real.sqrt_eq_rpow,
      Real.sq_sqrt (integral_nonneg fun _ => by positivity)]
  have hae : (Y : X → ℂ) =ᵐ[ρ.toMeasure] fun x => H x - F x := by
    filter_upwards [Lp.coeFn_sub (ContinuousMap.toLp 2 ρ.toMeasure ℂ H) (hmem.toLp F),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) ρ.toMeasure H, hmem.coeFn_toLp] with x h1 h2 h3
    rw [hYdef, h1, Pi.sub_apply, h2, h3]
  have hint : ∫ x, ‖F x - H x‖ ^ 2 ∂ρ.toMeasure = ‖Y‖ ^ 2 := by
    rw [hsq]
    refine integral_congr_ae (hae.mono fun x hx => ?_)
    simp only [hx, norm_sub_rev]
  rw [hint]
  calc ‖Y‖ ^ 2 < Real.sqrt ε ^ 2 := pow_lt_pow_left₀ hz' (norm_nonneg _) two_ne_zero
    _ = ε := Real.sq_sqrt hε.le
theorem l2Approximable_holds
    (hc : Measures.CompactMetricProbability.CompactMetricProbabilityFacts)
    (D : Setup) (S : Set AmbientSpace) : L2Approximable D S := by
  intro hS σ F hF
  have := compactSpace_gaugeField (a := D.mesh)
  have hk : Measurable (truncate S : GaugeField D.mesh → GaugeField D.mesh) :=
    (continuous_truncate S).measurable
  let σ' : ProbMeasure (GaugeField D.mesh) :=
    ⟨Measure.map (truncate S) σ.toMeasure, Measure.isProbabilityMeasure_map hk.aemeasurable⟩
  have near : ∀ n : ℕ+, ∃ H : GaugeField D.mesh → ℂ, Continuous H ∧
      ∫ x, ‖F x - H x‖ ^ 2 ∂σ'.toMeasure < 1 / (n : ℝ) := fun n =>
    @exists_continuous_L2_near (GaugeField D.mesh) (fieldMetricCompatible D)
      compactSpace_gaugeField _ (inferInstance : BorelSpace (GaugeField D.mesh)) hc σ' F
      hF.1.1 hF.1.2 (1 / (n : ℝ)) (by positivity)
  choose H hHc hH using near
  have h3 : F = F ∘ truncate S := ((tfae_region S F hF.1).out 0 2).1 hF
  have hmem : ∀ n, H n ∘ truncate S ∈
      continuousLocalFunctions D.mesh ∩ regionObservables D.mesh S := by
    intro n
    have hd := (truncatedContinuous_holds D S ⟨H n, hHc n⟩).2.1
    exact ⟨⟨hd.1, ⟨S, hS, hd.2⟩, (hHc n).comp (continuous_truncate S)⟩, hd⟩
  refine ⟨fun n => H n ∘ truncate S, hmem, ?_⟩
  have hval : ∀ n : ℕ+, σ.eval (fun U => ((‖F U - (H n ∘ truncate S) U‖ ^ 2 : ℝ) : ℂ)) =
      ((∫ x, ‖F x - H n x‖ ^ 2 ∂σ'.toMeasure : ℝ) : ℂ) := by
    intro n
    have hm : Measurable fun x => ‖F x - H n x‖ ^ 2 :=
      ((hF.1.1.sub (hHc n).measurable).norm).pow_const 2
    show ∫ U, ((‖F U - (H n ∘ truncate S) U‖ ^ 2 : ℝ) : ℂ) ∂σ.toMeasure = _
    rw [integral_complex_ofReal]
    congr 1
    have hσ' : σ'.toMeasure = Measure.map (truncate S) σ.toMeasure := rfl
    rw [hσ', integral_map hk.aemeasurable hm.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    show ‖F U - H n (truncate S U)‖ ^ 2 = ‖F (truncate S U) - H n (truncate S U)‖ ^ 2
    rw [show F (truncate S U) = F U from (congrFun h3 U).symm]
  have hcoe : Tendsto (fun n : ℕ+ => (n : ℕ)) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨⟨b + 1, Nat.succ_pos b⟩, fun n hn => by
      have : b + 1 ≤ (n : ℕ) := hn
      omega⟩
  have hlim : Tendsto (fun n : ℕ+ => 1 / ((n : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hcoe
  refine squeeze_zero_norm (fun n => ?_) hlim
  rw [hval n, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => by positivity)]
  exact (hH n).le
theorem statement_holds (hc : Measures.CompactMetricProbability.CompactMetricProbabilityFacts) :
    Statement := fun D S S' =>
  ⟨compactnessAndTruncation_holds D S, fun F hF => tfae_region S F hF,
    ⟨regionObservables_algebra S, regionObservables_mono, regionObservables_inter S S',
      exists_scaledCube D⟩,
    truncatedContinuous_holds D S, l2Approximable_holds hc D S⟩
end LatticePhases.ObservableRegions
end YangMills.Construction
