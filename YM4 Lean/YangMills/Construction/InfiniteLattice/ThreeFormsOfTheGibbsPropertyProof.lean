import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorusProof
import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnConfigurationsAndFunctionsProof
import YangMills.Construction.InfiniteLattice.FormsOfTheWilsonSpecificationOfAWindow
import YangMills.Construction.InfiniteLattice.FunctionsOfSomeOfTheBondsAndClassesStableUnderBoundedLimits
import YangMills.Construction.InfiniteLattice.OperatorsOfTheWilsonSpecification
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsProperty
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set Filter GibbsAtFixedSpacing FieldsAtSpacing
open scoped Topology
namespace InfiniteLattice
namespace GibbsForms
variable {a : ℝ}
theorem measurable_eval_link (b : Link a) : Measurable fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.measurable_link_eval <;> assumption
theorem linkSigma_le_borel (S : Set (Link a)) :
    linkSigma S ≤ (inferInstance : MeasurableSpace (GaugeField a)) := by apply _root_.YangMills.Construction.GibbsAtFixedSpacing.SymmetryActionProof.linkSigma_le_borel <;> assumption
theorem measurable_eval_link_of_mem {S : Set (Link a)} {b : Link a} (hb : b ∈ S) :
    Measurable[linkSigma S] fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.measurable_link_eval_of_mem <;> assumption
theorem isPositivelyOriented_or_opposite (b : Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · exact Or.inl ⟨μ, h⟩
  · refine Or.inr ⟨μ, ?_⟩
    change b.initial - b.terminal = axisStep a μ
    rw [← neg_sub, h, neg_neg]
theorem exteriorSigma_eq_linkSigma (ha : 0 < a) (W : LinkWindow a) :
    exteriorSigma W.links =
      linkSigma (positiveLinkSet a \ (W.links : Set (Link a))) := by
  apply le_antisymm
  · refine iSup₂_le fun b hb => ?_
    rcases isPositivelyOriented_or_opposite b with hp | hp
    · exact (measurable_eval_link_of_mem
        (S := positiveLinkSet a \ (W.links : Set (Link a)))
        ⟨mem_positiveLinks_iff.2 hp, hb.1⟩).comap_le
    · have hm := measurable_eval_link_of_mem
        (S := positiveLinkSet a \ (W.links : Set (Link a)))
        (b := b.opposite) ⟨mem_positiveLinks_iff.2 hp, hb.2⟩
      have hinv : Measurable[linkSigma (positiveLinkSet a \ (W.links : Set (Link a)))]
          fun U : GaugeField a => U b := by
        have heq : (fun U : GaugeField a => U b) =
            fun U : GaugeField a => (U b.opposite)⁻¹ := by
          funext U
          rw [U.2 b, inv_inv]
        rw [heq]
        exact continuous_inv.measurable.comp hm
      exact hinv.comap_le
  · refine iSup₂_le fun b hb => ?_
    have hpos : b.IsPositivelyOriented := mem_positiveLinks_iff.1 hb.1
    refine (measurable_eval_link_of_mem (S := {b | b ∉ W.links ∧ b.opposite ∉ W.links})
      ⟨hb.2, fun h => ?_⟩).comap_le
    exact Link.opposite_not_isPositivelyOriented ha hpos (W.isPositive _ h)
theorem integral_def (ν : BorelProb a) (F : GaugeField a → ℂ) :
    ν.integral F = ∫ U, F U ∂ν.1 :=
  rfl
instance isProbabilityMeasure_measure (ν : BorelProb a) : IsProbabilityMeasure ν.1 := ν.2
theorem integrable_of_isBoundedObservable (ν : BorelProb a) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) : Integrable F ν.1 := by
  obtain ⟨hm, C, hC⟩ := hF
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
theorem norm_le_supNorm {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (U : GaugeField a) : ‖F U‖ ≤ observableSupNorm F := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.norm_le_supNorm <;> assumption
theorem isBoundedObservable_add {F H : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hH : IsBoundedObservable H) : IsBoundedObservable (F + H) := by apply _root_.YangMills.Construction.InfiniteLattice.IsBoundedObservable.add <;> assumption
theorem isBoundedObservable_smul (z : ℂ) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (z • F) := by
  obtain ⟨hm, C, hC⟩ := hF
  refine ⟨hm.const_smul z, ‖z‖ * C, fun U => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hC U) (norm_nonneg z)
theorem isBoundedObservable_one : IsBoundedObservable (1 : GaugeField a → ℂ) :=
  ⟨measurable_const, 1, fun _ => by simp⟩
def unitIndicator (E : Set (GaugeField a)) : GaugeField a → ℂ :=
  E.indicator fun _ => (1 : ℂ)
theorem isBoundedObservable_unitIndicator {E : Set (GaugeField a)} (hE : MeasurableSet E) :
    IsBoundedObservable (unitIndicator E) := by
  refine ⟨measurable_const.indicator hE, 1, fun U => ?_⟩
  by_cases h : U ∈ E <;> simp [unitIndicator, h]
theorem supNorm_unitIndicator_le (E : Set (GaugeField a)) :
    observableSupNorm (unitIndicator E) ≤ 1 := by
  have : Nonempty (GaugeField a) := ⟨trivialField a⟩
  refine ciSup_le fun U => ?_
  by_cases h : U ∈ E <;> simp [unitIndicator, h]
theorem unitIndicator_inter (T X : Set (GaugeField a)) :
    unitIndicator (T ∩ X) = unitIndicator T * unitIndicator X := by
  funext U
  by_cases h : U ∈ T <;> by_cases h' : U ∈ X <;> simp [unitIndicator, h, h']
section Operators
variable (hop : ConditionalAverageProperties.claim) (ha : 0 < a) {β : ℝ} (hβ : 0 < β)
  (W : LinkWindow a)
include hop hβ
theorem isBoundedObservable_conditionalAverage {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) : IsBoundedObservable (W.conditionalAverage ha β F) :=
  (hop a ha β hβ W F F hF hF).2.1.1
theorem isBlindTo_conditionalAverage {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBlindTo (W.links : Set (Link a)) (W.conditionalAverage ha β F) :=
  (hop a ha β hβ W F F hF hF).2.1.2
theorem supNorm_conditionalAverage_le {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    observableSupNorm (W.conditionalAverage ha β F) ≤ observableSupNorm F :=
  (hop a ha β hβ W F F hF hF).2.2.1
theorem conditionalAverage_mul_blind {F H : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hH : IsBoundedObservable H) (hblind : IsBlindTo (W.links : Set (Link a)) H) :
    W.conditionalAverage ha β (H * F) = H * W.conditionalAverage ha β F :=
  (hop a ha β hβ W F H hF hH).2.2.2.1 hblind
theorem conditionalAverage_add {F H : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hH : IsBoundedObservable H) :
    W.conditionalAverage ha β (F + H) =
      W.conditionalAverage ha β F + W.conditionalAverage ha β H :=
  (hop a ha β hβ W F H hF hH).2.2.2.2.2.1
theorem conditionalAverage_smul {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) (z : ℂ) :
    W.conditionalAverage ha β (z • F) = z • W.conditionalAverage ha β F :=
  (hop a ha β hβ W F F hF hF).2.2.2.2.2.2.1 z
theorem conditionalAverage_one : W.conditionalAverage ha β (1 : GaugeField a → ℂ) = 1 :=
  (hop a ha β hβ W 1 1 isBoundedObservable_one isBoundedObservable_one).2.2.2.2.2.2.2.1
def invariantClass (ν : BorelProb a) : Submodule ℂ (GaugeField a → ℂ) where
  carrier := {F | IsBoundedObservable F ∧
    ν.integral (W.conditionalAverage ha β F) = ν.integral F}
  add_mem' := by
    rintro F H ⟨hF, eF⟩ ⟨hH, eH⟩
    refine ⟨isBoundedObservable_add hF hH, ?_⟩
    rw [conditionalAverage_add hop ha hβ W hF hH]
    simp only [integral_def] at eF eH ⊢
    simp only [Pi.add_apply]
    rw [integral_add
        (integrable_of_isBoundedObservable ν (isBoundedObservable_conditionalAverage hop ha hβ W hF))
        (integrable_of_isBoundedObservable ν (isBoundedObservable_conditionalAverage hop ha hβ W hH)),
      integral_add (integrable_of_isBoundedObservable ν hF)
        (integrable_of_isBoundedObservable ν hH), eF, eH]
  zero_mem' := by
    have h0 : (0 : GaugeField a → ℂ) = (0 : ℂ) • (1 : GaugeField a → ℂ) := by simp
    refine ⟨⟨measurable_const, 0, fun _ => by simp⟩, ?_⟩
    rw [h0, conditionalAverage_smul hop ha hβ W isBoundedObservable_one]
    simp [integral_def]
  smul_mem' := by
    rintro z F ⟨hF, eF⟩
    refine ⟨isBoundedObservable_smul z hF, ?_⟩
    rw [conditionalAverage_smul hop ha hβ W hF]
    simp only [integral_def] at eF ⊢
    simp only [Pi.smul_apply]
    rw [integral_smul, integral_smul, eF]
theorem mem_invariantClass_of_tendsto {ν : BorelProb a} (Fn : ℕ → GaugeField a → ℂ)
    (F : GaugeField a → ℂ) (hn : ∀ n, Fn n ∈ invariantClass hop ha hβ W ν)
    (hb : ∃ C : ℝ, ∀ n, observableSupNorm (Fn n) ≤ C)
    (hl : ∀ U, Tendsto (fun n => Fn n U) atTop (𝓝 (F U))) :
    F ∈ invariantClass hop ha hβ W ν := by
  obtain ⟨C, hC⟩ := hb
  have hobs : ∀ n, IsBoundedObservable (Fn n) := fun n => (hn n).1
  have hbound : ∀ n U, ‖Fn n U‖ ≤ C := fun n U =>
    (norm_le_supNorm (hobs n) U).trans (hC n)
  have hF : IsBoundedObservable F := by
    refine ⟨measurable_of_tendsto_metrizable (fun n => (hobs n).1) (tendsto_pi_nhds.2 hl), C,
      fun U => ?_⟩
    exact le_of_tendsto (hl U).norm (Eventually.of_forall fun n => hbound n U)
  have hgbound : ∀ n U, ‖W.conditionalAverage ha β (Fn n) U‖ ≤ C := fun n U =>
    (norm_le_supNorm (isBoundedObservable_conditionalAverage hop ha hβ W (hobs n)) U).trans
      ((supNorm_conditionalAverage_le hop ha hβ W (hobs n)).trans (hC n))
  have hlim : ∀ ξ, Tendsto (fun n => W.conditionalAverage ha β (Fn n) ξ) atTop
      (𝓝 (W.conditionalAverage ha β F ξ)) :=
    (hop a ha β hβ W F F hF hF).2.2.2.2.2.2.2.2 Fn hobs
      ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩ hl
  have t1 : Tendsto (fun n => ν.integral (Fn n)) atTop (𝓝 (ν.integral F)) :=
    tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (hobs n).1.aestronglyMeasurable) (integrable_const C)
      (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hl)
  have t2 : Tendsto (fun n => ν.integral (W.conditionalAverage ha β (Fn n))) atTop
      (𝓝 (ν.integral (W.conditionalAverage ha β F))) :=
    tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (isBoundedObservable_conditionalAverage hop ha hβ W (hobs n)).1.aestronglyMeasurable)
      (integrable_const C) (fun n => ae_of_all _ (hgbound n)) (ae_of_all _ hlim)
  refine ⟨hF, tendsto_nhds_unique t2 ?_⟩
  exact t1.congr fun n => ((hn n).2).symm
end Operators
theorem restrictTo_glue (ha : 0 < a) (W : LinkWindow a) (V : W.Assignments) (ξ : GaugeField a) :
    restrictTo W.links (W.glue ha V ξ) = V := by
  funext b
  simp [restrictTo, LinkWindow.glue, b.2]
theorem measurable_restrictTo (L : Finset (Link a)) : Measurable (restrictTo L) :=
  measurable_pi_lambda _ fun b => measurable_eval_link b.1
theorem integral_unitIndicator_mul_ofReal (ν : BorelProb a) {T : Set (GaugeField a)}
    (hT : MeasurableSet T) (h : GaugeField a → ℝ) :
    ν.integral (unitIndicator T * fun U => (h U : ℂ)) = ((∫ U in T, h U ∂ν.1 : ℝ) : ℂ) := by
  have e : (unitIndicator T * fun U => (h U : ℂ)) = T.indicator fun U => (h U : ℂ) := by
    funext U
    by_cases hU : U ∈ T <;> simp [unitIndicator, hU]
  rw [e, integral_def, integral_indicator hT, integral_complex_ofReal]
section Main
variable (hop : ConditionalAverageProperties.claim)
  (hforms : WindowSpecificationForms.Statement) (ha : 0 < a) {β : ℝ} (hβ : 0 < β)
  (W : LinkWindow a)
def windowEvent (W : LinkWindow a) (A : Set W.Assignments) : Set (GaugeField a) :=
  restrictTo W.links ⁻¹' A
theorem measurableSet_windowEvent {A : Set W.Assignments} (hA : MeasurableSet A) :
    MeasurableSet (windowEvent W A) :=
  measurable_restrictTo W.links hA
def windowEventIndicator (W : LinkWindow a) (A : Set W.Assignments) : GaugeField a → ℝ :=
  (windowEvent W A).indicator fun _ => (1 : ℝ)
theorem unitIndicator_windowEvent (A : Set W.Assignments) :
    unitIndicator (windowEvent W A) = fun U => (windowEventIndicator W A U : ℂ) := by
  funext U
  by_cases h : U ∈ windowEvent W A <;> simp [unitIndicator, windowEventIndicator, h]
include hforms hβ in
theorem conditionalAverage_unitIndicator_windowEvent {A : Set W.Assignments}
    (hA : MeasurableSet A) (ξ : GaugeField a) :
    W.conditionalAverage ha β (unitIndicator (windowEvent W A)) ξ =
      ((wilsonSpecification β W.links ξ A).toReal : ℂ) := by
  obtain ⟨_, hprob, hF⟩ := hforms a ha β hβ W ξ
  rw [(hF _ (isBoundedObservable_unitIndicator (measurableSet_windowEvent W hA))).2]
  have e : (fun V : W.Assignments => unitIndicator (windowEvent W A) (W.glue ha V ξ)) =
      A.indicator fun _ => (1 : ℂ) := by
    funext V
    have hiff : (W.glue ha V ξ ∈ windowEvent W A) ↔ V ∈ A := by
      change restrictTo W.links (W.glue ha V ξ) ∈ A ↔ V ∈ A
      rw [restrictTo_glue]
    by_cases h : V ∈ A
    · simp [unitIndicator, h, hiff]
    · simp [unitIndicator, h, hiff]
  rw [e, integral_indicator_const _ hA]
  simp [Measure.real]
include hop hforms hβ in
theorem invariance_iff_setIntegral_eq (ν : BorelProb a) {T : Set (GaugeField a)}
    (hT : MeasurableSet[exteriorSigma W.links] T) {A : Set W.Assignments} (hA : MeasurableSet A) :
    ν.integral (W.conditionalAverage ha β (unitIndicator (T ∩ windowEvent W A))) =
        ν.integral (unitIndicator (T ∩ windowEvent W A)) ↔
      ∫ U in T, (wilsonSpecification β W.links U A).toReal ∂ν.1 =
        ∫ U in T, windowEventIndicator W A U ∂ν.1 := by
  have hTm : MeasurableSet T := linkSigma_le_borel _ T hT
  have hblind : IsBlindTo (W.links : Set (Link a)) (unitIndicator T) := by
    have hT' : MeasurableSet[linkSigma (positiveLinkSet a \ (W.links : Set (Link a)))] T := by
      rw [← exteriorSigma_eq_linkSigma ha W]
      exact hT
    exact Measurable.indicator measurable_const hT'
  have hX := measurableSet_windowEvent W hA
  rw [unitIndicator_inter, conditionalAverage_mul_blind hop ha hβ W
      (isBoundedObservable_unitIndicator hX) (isBoundedObservable_unitIndicator hTm) hblind]
  have e1 : W.conditionalAverage ha β (unitIndicator (windowEvent W A)) =
      fun U => (((wilsonSpecification β W.links U A).toReal : ℝ) : ℂ) :=
    funext fun U => conditionalAverage_unitIndicator_windowEvent hforms ha hβ W hA U
  rw [e1, unitIndicator_windowEvent, integral_unitIndicator_mul_ofReal ν hTm,
    integral_unitIndicator_mul_ofReal ν hTm, Complex.ofReal_inj]
include hop in
theorem unitIndicator_mem_invariantClass (hlinks : LinkFunctionsStatement) (ν : BorelProb a)
    (hbasic : ∀ (T : Set (GaugeField a)) (A : Set W.Assignments),
      MeasurableSet[exteriorSigma W.links] T → MeasurableSet A →
        unitIndicator (T ∩ windowEvent W A) ∈ invariantClass hop ha hβ W ν)
    {E : Set (GaugeField a)} (hE : MeasurableSet E) :
    unitIndicator E ∈ invariantClass hop ha hβ W ν := by
  let S : Set (Set (GaugeField a)) := {E | ∃ (T : Set (GaugeField a)) (A : Set W.Assignments),
    MeasurableSet[exteriorSigma W.links] T ∧ MeasurableSet A ∧ E = T ∩ windowEvent W A}
  have hsub : (W.links : Set (Link a)) ⊆ positiveLinkSet a := fun b hb =>
    mem_positiveLinks_iff.2 (W.isPositive b hb)
  have hborel : borel (GaugeField a) = linkSigma (positiveLinkSet a) :=
    (hlinks a ha _ hsub).1.2.2.2.2.2.2.1
  have h_eq : (inferInstance : MeasurableSpace (GaugeField a)) =
      MeasurableSpace.generateFrom S := by
    apply le_antisymm
    · change borel (GaugeField a) ≤ _
      rw [hborel]
      refine iSup₂_le fun b hb => ?_
      rintro _ ⟨D, hD, rfl⟩
      apply MeasurableSpace.measurableSet_generateFrom
      by_cases hbW : b ∈ W.links
      · refine ⟨univ, (fun V : W.Assignments => V ⟨b, hbW⟩) ⁻¹' D, MeasurableSet.univ,
          measurable_pi_apply _ hD, ?_⟩
        ext U
        simp [windowEvent, restrictTo]
      · refine ⟨(fun U : GaugeField a => U b) ⁻¹' D, univ, ?_, MeasurableSet.univ, ?_⟩
        · rw [exteriorSigma_eq_linkSigma ha W]
          exact measurable_eval_link_of_mem
            (S := positiveLinkSet a \ (W.links : Set (Link a))) ⟨hb, hbW⟩ hD
        · simp [windowEvent]
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨T, A, hT, hA, rfl⟩
      exact (linkSigma_le_borel _ T hT).inter (measurableSet_windowEvent W hA)
  have hpi : IsPiSystem S := by
    rintro _ ⟨T, A, hT, hA, rfl⟩ _ ⟨T', A', hT', hA', rfl⟩ _
    refine ⟨T ∩ T', A ∩ A', hT.inter hT', hA.inter hA', ?_⟩
    ext U
    simp only [windowEvent, mem_inter_iff, mem_preimage]
    tauto
  have hone : (1 : GaugeField a → ℂ) ∈ invariantClass hop ha hβ W ν := by
    refine ⟨isBoundedObservable_one, ?_⟩
    rw [conditionalAverage_one hop ha hβ W]
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => unitIndicator E ∈ invariantClass hop ha hβ W ν) h_eq hpi ?_ ?_ ?_ ?_ E hE
  · have e : unitIndicator (∅ : Set (GaugeField a)) = 0 := by
      funext U
      simp [unitIndicator]
    rw [e]
    exact Submodule.zero_mem _
  · rintro _ ⟨T, A, hT, hA, rfl⟩
    exact hbasic T A hT hA
  · intro t _ ht
    have e : unitIndicator tᶜ = 1 - unitIndicator t := by
      funext U
      by_cases h : U ∈ t <;> simp [unitIndicator, h]
    rw [e]
    exact Submodule.sub_mem _ hone ht
  · intro f hd hf hin
    let B : ℕ → Set (GaugeField a) := fun n => ⋃ i ∈ Finset.range n, f i
    have hB : ∀ n, unitIndicator (B n) ∈ invariantClass hop ha hβ W ν := by
      intro n
      have e : unitIndicator (B n) = ∑ i ∈ Finset.range n, unitIndicator (f i) := by
        funext U
        have hsum := Finset.indicator_biUnion (Finset.range n) (t := f)
          (f := fun _ : GaugeField a => (1 : ℂ))
          (fun i _ j _ hij => hd hij)
        simp only [unitIndicator, B, Finset.sum_apply]
        rw [hsum]
      rw [e]
      exact Submodule.sum_mem _ fun i _ => hin i
    have hmono : Monotone B := fun m n hmn =>
      biUnion_subset_biUnion_left fun i hi => Finset.mem_coe.2
        (Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 (Finset.mem_coe.1 hi)) hmn))
    have hun : (⋃ n, B n) = ⋃ i, f i := by
      ext U
      simp only [mem_iUnion, B, Finset.mem_range]
      constructor
      · rintro ⟨_, i, _, h⟩
        exact ⟨i, h⟩
      · rintro ⟨i, h⟩
        exact ⟨i + 1, i, Nat.lt_succ_self i, h⟩
    refine mem_invariantClass_of_tendsto hop ha hβ W (fun n => unitIndicator (B n)) _ hB
      ⟨1, fun n => supNorm_unitIndicator_le _⟩ fun U => ?_
    have hlim := hmono.tendsto_indicator B (fun _ : GaugeField a => (1 : ℂ)) U
    rw [hun] at hlim
    exact hlim.mono_right (pure_le_nhds _)
include hop in
theorem mem_invariantClass_of_isBoundedObservable (hlinks : LinkFunctionsStatement)
    (ν : BorelProb a)
    (hbasic : ∀ (T : Set (GaugeField a)) (A : Set W.Assignments),
      MeasurableSet[exteriorSigma W.links] T → MeasurableSet A →
        unitIndicator (T ∩ windowEvent W A) ∈ invariantClass hop ha hβ W ν)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) : F ∈ invariantClass hop ha hβ W ν := by
  obtain ⟨hm, C, hC⟩ := hF
  have hs : StronglyMeasurable F := hm.stronglyMeasurable
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (trivialField a))
  have hsimple : ∀ s : SimpleFunc (GaugeField a) ℂ,
      (s : GaugeField a → ℂ) ∈ invariantClass hop ha hβ W ν := by
    intro s
    refine SimpleFunc.induction
      (motive := fun s : SimpleFunc (GaugeField a) ℂ =>
        (s : GaugeField a → ℂ) ∈ invariantClass hop ha hβ W ν) ?_ ?_ s
    · intro c E hE
      have e : ((SimpleFunc.piecewise E hE (SimpleFunc.const _ c) (SimpleFunc.const _ 0) :
          SimpleFunc (GaugeField a) ℂ) : GaugeField a → ℂ) = c • unitIndicator E := by
        funext U
        by_cases h : U ∈ E <;> simp [unitIndicator, h]
      rw [e]
      exact Submodule.smul_mem _ c
        (unitIndicator_mem_invariantClass hop ha hβ W hlinks ν hbasic hE)
    · intro f g _ hf hg
      rw [SimpleFunc.coe_add]
      exact Submodule.add_mem _ hf hg
  have : Nonempty (GaugeField a) := ⟨trivialField a⟩
  exact mem_invariantClass_of_tendsto hop ha hβ W (fun n => hs.approxBounded C n) F
    (fun n => hsimple _)
    ⟨C, fun n => ciSup_le fun U => StronglyMeasurable.norm_approxBounded_le hs hC0 n U⟩
    fun U => StronglyMeasurable.tendsto_approxBounded_of_norm_le hs (hC U)
end Main
end GibbsForms
open GibbsForms in
theorem gibbsCharacterizations_holds (hop : ConditionalAverageProperties.claim)
    (hlinks : LinkFunctionsStatement)
    (hforms : WindowSpecificationForms.Statement) :
    GibbsCharacterizations := by
  intro a ha β hβ ν
  tfae_have 1 → 2 := by
    intro hG W F hF
    have hbasic : ∀ (T : Set (GaugeField a)) (A : Set W.Assignments),
        MeasurableSet[exteriorSigma W.links] T → MeasurableSet A →
          unitIndicator (T ∩ windowEvent W A) ∈ invariantClass hop ha hβ W ν := by
      intro T A hT hA
      have hX := measurableSet_windowEvent W hA
      refine ⟨isBoundedObservable_unitIndicator ((linkSigma_le_borel _ T hT).inter hX), ?_⟩
      rw [invariance_iff_setIntegral_eq hop hforms ha hβ W ν hT hA]
      have h := hG.2 W.links W.isPositive A hA
      have hint : Integrable ((restrictTo W.links ⁻¹' A).indicator fun _ => (1 : ℝ)) ν.1 :=
        (integrable_const (1 : ℝ)).indicator hX
      exact (integral_congr_ae (ae_restrict_of_ae h)).trans
        (setIntegral_condExp (linkSigma_le_borel _) hint hT)
    exact (mem_invariantClass_of_isBoundedObservable hop ha hβ W hlinks ν hbasic hF).2
  tfae_have 2 → 3 := by
    intro h W F hF
    have hc := (hlinks a ha ∅ (empty_subset _)).2.2.2.1.2.2.2
    have hF' : F ∈ {F | IsBoundedLocal F ∧ Continuous F} := hc ▸ hF
    exact h W F ((isBoundedLocal_iff F).1 hF'.1).1
  tfae_have 3 → 2 := by
    intro h W F hF
    have hcl := (hlinks a ha ∅ (empty_subset _)).2.2.2.2.1 (invariantClass hop ha hβ W ν)
      (fun F hF => hF.1)
      (fun F hF => ⟨((isBoundedLocal_iff F).1
        (((hlinks a ha ∅ (empty_subset _)).2.2.2.1.2.2.2 ▸ hF :
          F ∈ {F | IsBoundedLocal F ∧ Continuous F}).1)).1, h W F hF⟩)
      (fun Fn F hn hb hl => mem_invariantClass_of_tendsto hop ha hβ W Fn F hn hb hl)
    have hF' : F ∈ (invariantClass hop ha hβ W ν : Set (GaugeField a → ℂ)) := by
      rw [hcl]
      exact hF
    exact hF'.2
  tfae_have 2 → 1 := by
    intro h
    refine ⟨ν.2, fun L hL A hA => ?_⟩
    let W : LinkWindow a := ⟨L, hL⟩
    have hX : MeasurableSet (windowEvent W A) := measurableSet_windowEvent W hA
    have hobs := isBoundedObservable_unitIndicator hX
    have hg : (fun U => (wilsonSpecification β L U A).toReal) =
        fun U => (W.conditionalAverage ha β (unitIndicator (windowEvent W A)) U).re := by
      funext U
      rw [conditionalAverage_unitIndicator_windowEvent hforms ha hβ W hA U]
      simp [W]
    have hmeas : Measurable[exteriorSigma L] fun U => (wilsonSpecification β L U A).toReal := by
      rw [hg]
      have hr := isBlindTo_conditionalAverage hop ha hβ W hobs
      have hr' : Measurable[exteriorSigma W.links]
          (W.conditionalAverage ha β (unitIndicator (windowEvent W A))) := by
        rw [exteriorSigma_eq_linkSigma ha W]
        exact hr
      exact Complex.measurable_re.comp hr'
    have hgint : Integrable (fun U => (wilsonSpecification β L U A).toReal) ν.1 := by
      rw [hg]
      exact (integrable_of_isBoundedObservable ν
        (isBoundedObservable_conditionalAverage hop ha hβ W hobs)).re
    have hint : Integrable ((restrictTo L ⁻¹' A).indicator fun _ => (1 : ℝ)) ν.1 :=
      (integrable_const (1 : ℝ)).indicator hX
    exact ae_eq_condExp_of_forall_setIntegral_eq (linkSigma_le_borel _) hint
      (fun s _ _ => hgint.integrableOn)
      (fun s hs _ => (invariance_iff_setIntegral_eq hop hforms ha hβ W ν hs hA).1
        (h W _ (isBoundedObservable_unitIndicator ((linkSigma_le_borel _ s hs).inter hX))))
      ⟨_, hmeas.stronglyMeasurable, Filter.EventuallyEq.rfl⟩
  tfae_finish
end InfiniteLattice
end YangMills.Construction
