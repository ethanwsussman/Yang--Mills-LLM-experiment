import YangMills.Construction.ChessboardTori.JensenAgainstTheChessboardProof
import YangMills.Construction.InfiniteLattice.FunctionsOfTheBondsOfASet
import YangMills.Construction.InfiniteLattice.ReflectionsOfOneFamilyProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Classical
noncomputable section
namespace YangMills.Construction.InfiniteLattice.LinkLocalFunctions
variable {a : ℝ}
theorem countable_link : Countable (Link a) := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.countable_link <;> assumption
theorem measurable_of_forall_link {α : Type*} {m : MeasurableSpace α} {f : α → GaugeField a}
    (h : ∀ l, Measurable fun x => f x l) : Measurable f := by
  have := countable_link (a := a)
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : BorelSpace (Link a → Matrices.ComplexMatrix2.specialUnitary) := Pi.borelSpace
  have e : (inferInstance : MeasurableSpace (GaugeField a)) =
      MeasurableSpace.comap
        (Subtype.val : GaugeField a → Link a → Matrices.ComplexMatrix2.specialUnitary)
        MeasurableSpace.pi :=
    (Subtype.borelSpace
      {g : Link a → Matrices.ComplexMatrix2.specialUnitary | ∀ l, g l.opposite = (g l)⁻¹}).measurable_eq.symm
  have hf : Measurable fun x => (f x).1 := measurable_pi_iff.2 h
  refine measurable_iff_comap_le.2 ((congrArg (MeasurableSpace.comap f) e).trans_le ?_)
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  exact hf ht
theorem measurable_eval_of_mem {S : Set AmbientSpace} {l : Link a} (hl : l ∈ linksWithin S) :
    Measurable[regionSigma S] fun g : GaugeField a => g l :=
  measurable_iff_comap_le.2 (le_iSup₂_of_le l hl le_rfl)
theorem opposite_mem_linksWithin {S : Set AmbientSpace} {l : Link a} :
    l.opposite ∈ (linksWithin S : Set (Link a)) ↔ l ∈ (linksWithin S : Set (Link a)) :=
  and_comm
def splice (S : Set AmbientSpace) (g h : GaugeField a) : GaugeField a :=
  ⟨fun l => if l ∈ (linksWithin S : Set (Link a)) then g l else h l, fun l => by
    by_cases hl : l ∈ (linksWithin S : Set (Link a))
    · simp only [if_pos hl, if_pos (opposite_mem_linksWithin.2 hl)]
      exact g.2 l
    · simp only [if_neg hl, if_neg (fun hl' => hl (opposite_mem_linksWithin.1 hl'))]
      exact h.2 l⟩
theorem splice_of_mem {S : Set AmbientSpace} (g h : GaugeField a) {l : Link a}
    (hl : l ∈ (linksWithin S : Set (Link a))) : splice S g h l = g l :=
  if_pos hl
theorem splice_of_not_mem {S : Set AmbientSpace} (g h : GaugeField a) {l : Link a}
    (hl : l ∉ (linksWithin S : Set (Link a))) : splice S g h l = h l :=
  if_neg hl
def oneField : GaugeField a := ⟨fun _ => 1, fun _ => by simp⟩
theorem eq_of_regionMeasurable {S : Set AmbientSpace} {F : GaugeField a → ℂ}
    (hF : IsRegionMeasurable S F) {g g' : GaugeField a}
    (h : ∀ l : Link a, l.IsWithin S → g l = g' l) : F g = F g' := by
  let π : GaugeField a → (↥(linksWithin S : Set (Link a)) → Matrices.ComplexMatrix2.specialUnitary) :=
    fun k l => k l.1
  have hle : (regionSigma S : MeasurableSpace (GaugeField a)) ≤
      MeasurableSpace.comap π MeasurableSpace.pi :=
    iSup₂_le fun l hl => by
      have : Measurable[MeasurableSpace.comap π MeasurableSpace.pi]
          fun k : GaugeField a => k l :=
        (measurable_pi_apply (⟨l, hl⟩ : ↥(linksWithin S : Set (Link a)))).comp (comap_measurable π)
      exact this.comap_le
  obtain ⟨T, -, hT⟩ := hle _ (hF (measurableSet_singleton (F g)))
  have hπ : π g' = π g := funext fun l => (h l.1 l.2).symm
  have hg : g ∈ π ⁻¹' T := by rw [hT]; rfl
  have hg' : g' ∈ π ⁻¹' T := by
    change π g' ∈ T
    rw [hπ]
    exact hg
  rw [hT] at hg'
  exact hg'.symm
theorem regionMeasurable_of_eq {S : Set AmbientSpace} {F : GaugeField a → ℂ} (hF : Measurable F)
    (h : ∀ g g' : GaugeField a, (∀ l : Link a, l.IsWithin S → g l = g' l) → F g = F g') :
    IsRegionMeasurable S F := by
  have hι : Measurable[regionSigma S] fun g : GaugeField a => splice S g oneField :=
    @measurable_of_forall_link a _ (regionSigma S) _ fun l => by
      by_cases hl : l ∈ (linksWithin S : Set (Link a))
      · simp only [splice_of_mem _ _ hl]
        exact measurable_eval_of_mem hl
      · simp only [splice_of_not_mem _ _ hl]
        exact @measurable_const _ _ _ (regionSigma S) _
  have e : F = fun g => F (splice S g oneField) :=
    funext fun g => h _ _ fun l hl => (splice_of_mem _ _ hl).symm
  rw [e]
  exact hF.comp hι
theorem isBoundedObservable_const (c : ℂ) : IsBoundedObservable fun _ : GaugeField a => c :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩
theorem isBoundedObservable_mul {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable (F * G) := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.isBoundedObservable_mul <;> assumption
theorem isBoundedObservable_conj {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable fun g => starRingEnd ℂ (F g) := by apply _root_.YangMills.Construction.NormalFamilies.ReflectionIdentities.isBoundedObservable_conj <;> assumption
theorem regionMeasurable_mul {S : Set AmbientSpace} {F G : GaugeField a → ℂ}
    (hF : IsRegionMeasurable S F) (hG : IsRegionMeasurable S G) : IsRegionMeasurable S (F * G) :=
  Measurable.mul hF hG
theorem regionMeasurable_conj {S : Set AmbientSpace} {F : GaugeField a → ℂ}
    (hF : IsRegionMeasurable S F) : IsRegionMeasurable S fun g => starRingEnd ℂ (F g) :=
  Complex.continuous_conj.measurable.comp hF
theorem regionMeasurable_const (S : Set AmbientSpace) (c : ℂ) :
    IsRegionMeasurable S fun _ : GaugeField a => c :=
  @measurable_const _ _ _ (regionSigma S) _
theorem regionMeasurable_mono {S S' : Set AmbientSpace} (h : S ⊆ S') {F : GaugeField a → ℂ}
    (hF : IsRegionMeasurable S F) : IsRegionMeasurable S' F := by apply _root_.YangMills.Construction.ChessboardTori.JensenChessboardBound.isRegionMeasurable_mono <;> assumption
theorem isLocalObservable_mul {F G : GaugeField a → ℂ} (hF : IsLocalObservable F)
    (hG : IsLocalObservable G) : IsLocalObservable (F * G) := by
  obtain ⟨S, bS, mS⟩ := hF
  obtain ⟨S', bS', mS'⟩ := hG
  exact ⟨S ∪ S', bS.union bS', regionMeasurable_mul
    (regionMeasurable_mono Set.subset_union_left mS)
    (regionMeasurable_mono Set.subset_union_right mS')⟩
theorem isLocalObservable_conj {F : GaugeField a → ℂ} (hF : IsLocalObservable F) :
    IsLocalObservable fun g => starRingEnd ℂ (F g) := by
  obtain ⟨S, bS, mS⟩ := hF
  exact ⟨S, bS, regionMeasurable_conj mS⟩
theorem isLocalObservable_const (c : ℂ) : IsLocalObservable fun _ : GaugeField a => c :=
  ⟨∅, Bornology.isBounded_empty, regionMeasurable_const _ c⟩
theorem isLocalObservable_smul {F : GaugeField a → ℂ} (hF : IsLocalObservable F) (c : ℂ) :
    IsLocalObservable (c • F) := by
  obtain ⟨S, bS, mS⟩ := hF
  exact ⟨S, bS, Measurable.const_smul mS c⟩
theorem isStarClosedFunctionAlgebra_of {M : Set (GaugeField (1 : ℝ) → ℂ)}
    (hadd : ∀ F ∈ M, ∀ G ∈ M, F + G ∈ M) (hsmul : ∀ (c : ℂ), ∀ F ∈ M, c • F ∈ M)
    (hmul : ∀ F ∈ M, ∀ G ∈ M, F * G ∈ M)
    (hconj : ∀ F ∈ M, (fun g => starRingEnd ℂ (F g)) ∈ M) (hconst : ∀ c : ℂ, (fun _ => c) ∈ M) :
    IsStarClosedFunctionAlgebra M :=
  ⟨⟨{ carrier := M
      add_mem' := fun {F G} hF hG => hadd F hF G hG
      zero_mem' := hconst 0
      smul_mem' := fun c F hF => hsmul c F hF }, rfl⟩, hmul, hconj, hconst⟩
theorem unitRegionObservables_isStarClosed (S : Set AmbientSpace) :
    IsStarClosedFunctionAlgebra (unitRegionObservables S) :=
  isStarClosedFunctionAlgebra_of
    (fun _ hF _ hG => ⟨hF.1.add hG.1, Measurable.add hF.2 hG.2⟩)
    (fun c _ hF => ⟨hF.1.const_smul c, Measurable.const_smul hF.2 c⟩)
    (fun _ hF _ hG => ⟨isBoundedObservable_mul hF.1 hG.1, regionMeasurable_mul hF.2 hG.2⟩)
    (fun _ hF => ⟨isBoundedObservable_conj hF.1, regionMeasurable_conj hF.2⟩)
    (fun c => ⟨isBoundedObservable_const c, regionMeasurable_const S c⟩)
theorem unitRegionObservables_mono {S S' : Set AmbientSpace} (h : S ⊆ S') :
    unitRegionObservables S ⊆ unitRegionObservables S' :=
  fun _ hF => ⟨hF.1, regionMeasurable_mono h hF.2⟩
theorem unitRegionObservables_inter (S S' : Set AmbientSpace) :
    unitRegionObservables S ∩ unitRegionObservables S' = unitRegionObservables (S ∩ S') := by
  refine Set.Subset.antisymm (fun F hF => ⟨hF.1.1, ?_⟩) fun F hF =>
    ⟨unitRegionObservables_mono Set.inter_subset_left hF,
      unitRegionObservables_mono Set.inter_subset_right hF⟩
  refine regionMeasurable_of_eq hF.1.1.1 fun g g' h => ?_
  have h₁ : F (splice S g g') = F g :=
    eq_of_regionMeasurable hF.1.2 fun l hl => splice_of_mem _ _ hl
  have h₂ : F (splice S g g') = F g' := by
    refine eq_of_regionMeasurable hF.2.2 fun l hl => ?_
    by_cases hS : l ∈ (linksWithin S : Set (Link (1 : ℝ)))
    · rw [splice_of_mem _ _ hS]
      exact h l ⟨⟨hS.1, hl.1⟩, ⟨hS.2, hl.2⟩⟩
    · exact splice_of_not_mem _ _ hS
  exact h₁.symm.trans h₂
theorem boundedLocalObservables_isStarClosed :
    IsStarClosedFunctionAlgebra
      {F : GaugeField (1 : ℝ) → ℂ | IsBoundedObservable F ∧ IsLocalObservable F} :=
  isStarClosedFunctionAlgebra_of
    (fun _ hF _ hG => ⟨hF.1.add hG.1, hF.2.add hG.2⟩)
    (fun c _ hF => ⟨hF.1.const_smul c, isLocalObservable_smul hF.2 c⟩)
    (fun _ hF _ hG => ⟨isBoundedObservable_mul hF.1 hG.1, isLocalObservable_mul hF.2 hG.2⟩)
    (fun _ hF => ⟨isBoundedObservable_conj hF.1, isLocalObservable_conj hF.2⟩)
    (fun c => ⟨isBoundedObservable_const c, isLocalObservable_const c⟩)
theorem halfSpaceLocalObservables_isStarClosed (μ : Fin 4) :
    IsStarClosedFunctionAlgebra
      (halfSpaceLocalObservables μ : Set (GaugeField (1 : ℝ) → ℂ)) := by
  obtain ⟨-, hmul, hconj, hconst⟩ := unitRegionObservables_isStarClosed (closedHalfSpace μ)
  exact ⟨⟨halfSpaceLocalObservables μ, rfl⟩,
    fun F hF G hG => ⟨hmul F hF.1 G hG.1, isLocalObservable_mul hF.2 hG.2⟩,
    fun F hF => ⟨hconj F hF.1, isLocalObservable_conj hF.2⟩,
    fun c => ⟨hconst c, isLocalObservable_const c⟩⟩
theorem statement_holds : LinkLocalFunctions.Statement := by
  refine ⟨fun S F hF => ⟨fun h g g' e => eq_of_regionMeasurable h.2 e,
      fun h => ⟨hF, regionMeasurable_of_eq hF.1 h⟩⟩, unitRegionObservables_isStarClosed,
    fun _ _ h => unitRegionObservables_mono h, unitRegionObservables_inter,
    boundedLocalObservables_isStarClosed, halfSpaceLocalObservables_isStarClosed, fun μ F hF => ?_⟩
  obtain ⟨hH, Q, bQ, mQ⟩ := hF
  refine ⟨Q, bQ, ?_⟩
  rw [← unitRegionObservables_inter]
  exact ⟨hH, hH.1, mQ⟩
end YangMills.Construction.InfiniteLattice.LinkLocalFunctions
