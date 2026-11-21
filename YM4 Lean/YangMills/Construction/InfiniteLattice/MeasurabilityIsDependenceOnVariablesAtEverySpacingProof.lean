import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorusProof
import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservablesProof
import YangMills.Construction.InfiniteLattice.MeasurabilityIsDependenceOnVariablesAtEverySpacing
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.MeasurableIffDependsOnlyProof
variable {a : ℝ}
theorem countable_link (a : ℝ) : Countable (Link a) := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.countable_link <;> assumption
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem gaugeField_measurableSpace_eq_comap :
    (inferInstance : MeasurableSpace (GaugeField a)) =
      MeasurableSpace.comap
        (fun U : GaugeField a => (U.1 : Link a → Matrices.ComplexMatrix2.specialUnitary))
        MeasurableSpace.pi := by
  have := countable_link a
  have := secondCountableTopology_specialUnitary
  have hpi : borel (Link a → Matrices.ComplexMatrix2.specialUnitary) = MeasurableSpace.pi :=
    (BorelSpace.measurable_eq (α := Link a → Matrices.ComplexMatrix2.specialUnitary)).symm
  rw [← hpi]
  exact borel_comap
theorem measurable_of_forall_link {m : MeasurableSpace (GaugeField a)}
    {κ : GaugeField a → GaugeField a} (h : ∀ b, Measurable[m] fun U => κ U b) :
    @Measurable _ _ m instMeasurableSpaceGaugeField κ := by
  have hpi : @Measurable _ _ m
      (MeasurableSpace.comap
        (fun U : GaugeField a => (U.1 : Link a → Matrices.ComplexMatrix2.specialUnitary))
        MeasurableSpace.pi) κ :=
    measurable_comap_iff.2 (measurable_pi_iff.2 h)
  rwa [← gaugeField_measurableSpace_eq_comap] at hpi
theorem linkSigma_mono {A B : Set (Link a)} (h : A ⊆ B) : linkSigma A ≤ linkSigma B := by apply _root_.YangMills.Construction.InfiniteLattice.SymmetryAction.linkSigma_mono <;> assumption
@[reducible] def agreementSigma (𝓜 : Set (Link a)) : MeasurableSpace (GaugeField a) where
  MeasurableSet' E := ∀ U U' : GaugeField a, (∀ b ∈ 𝓜, U b = U' b) → (U ∈ E ↔ U' ∈ E)
  measurableSet_empty := fun _ _ _ => Iff.rfl
  measurableSet_compl E h U U' hU := not_congr (h U U' hU)
  measurableSet_iUnion f h U U' hU := by
    simp only [mem_iUnion]
    exact exists_congr fun i => h i U U' hU
theorem dependsOnlyOn_of_measurable {𝓜 : Set (Link a)} {F : GaugeField a → ℂ}
    (hF : Measurable[linkSigma 𝓜] F) : DependsOnlyOn 𝓜 F := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.eq_of_eqOn_links <;> assumption
theorem measurable_eval_link {𝓜 : Set (Link a)} {b : Link a} (hb : b ∈ 𝓜) :
    Measurable[linkSigma 𝓜] fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.measurable_link_eval_of_mem <;> assumption
def truncatedFamily (𝓜 : Set (Link a)) (U : GaugeField a) :
    positiveLinks a → Matrices.ComplexMatrix2.specialUnitary :=
  open Classical in fun c => if c.1 ∈ 𝓜 then U c.1 else 1
def truncate (ha : 0 < a) (𝓜 : Set (Link a)) (U : GaugeField a) : GaugeField a :=
  gaugeFieldOfPositive ha (truncatedFamily 𝓜 U)
theorem truncate_apply (ha : 0 < a) (𝓜 : Set (Link a)) (U : GaugeField a) (b : Link a) :
    truncate ha 𝓜 U b = extendFromPositive (truncatedFamily 𝓜 U) b := rfl
theorem truncate_of_mem (ha : 0 < a) {𝓜 : Set (Link a)} (h𝓜 : IsLinkSet 𝓜)
    (U : GaugeField a) {b : Link a} (hb : b ∈ 𝓜) : truncate ha 𝓜 U b = U b := by
  rw [truncate_apply, extendFromPositive, dif_pos (h𝓜 hb), truncatedFamily]
  exact if_pos hb
theorem measurable_truncatedFamily (𝓜 : Set (Link a)) (c : positiveLinks a) :
    Measurable[linkSigma 𝓜] fun U : GaugeField a => truncatedFamily 𝓜 U c := by
  by_cases hc : c.1 ∈ 𝓜
  · have e : (fun U : GaugeField a => truncatedFamily 𝓜 U c) = fun U => U c.1 :=
      funext fun U => by rw [truncatedFamily]; exact if_pos hc
    rw [e]
    exact measurable_eval_link hc
  · have e : (fun U : GaugeField a => truncatedFamily 𝓜 U c) = fun _ => 1 :=
      funext fun U => by rw [truncatedFamily]; exact if_neg hc
    rw [e]
    exact @measurable_const _ _ _ (linkSigma 𝓜) _
theorem measurable_truncate_eval (ha : 0 < a) (𝓜 : Set (Link a)) (b : Link a) :
    Measurable[linkSigma 𝓜] fun U : GaugeField a => truncate ha 𝓜 U b := by
  by_cases h : b ∈ positiveLinks a
  · have e : (fun U : GaugeField a => truncate ha 𝓜 U b) =
        fun U => truncatedFamily 𝓜 U ⟨b, h⟩ :=
      funext fun U => by rw [truncate_apply, extendFromPositive, dif_pos h]
    rw [e]
    exact measurable_truncatedFamily 𝓜 _
  · by_cases h' : b.opposite ∈ positiveLinks a
    · have e : (fun U : GaugeField a => truncate ha 𝓜 U b) =
          fun U => (truncatedFamily 𝓜 U ⟨b.opposite, h'⟩)⁻¹ :=
        funext fun U => by rw [truncate_apply, extendFromPositive, dif_neg h, dif_pos h']
      rw [e]
      exact (continuous_inv.measurable :
          Measurable fun g : Matrices.ComplexMatrix2.specialUnitary => g⁻¹).comp
        (measurable_truncatedFamily 𝓜 _)
    · have e : (fun U : GaugeField a => truncate ha 𝓜 U b) = fun _ => 1 :=
        funext fun U => by rw [truncate_apply, extendFromPositive, dif_neg h, dif_neg h']
      rw [e]
      exact @measurable_const _ _ _ (linkSigma 𝓜) _
theorem measurable_of_dependsOnlyOn (ha : 0 < a) {𝓜 : Set (Link a)} (h𝓜 : IsLinkSet 𝓜)
    {F : GaugeField a → ℂ} (hF : Measurable F) (hd : DependsOnlyOn 𝓜 F) :
    Measurable[linkSigma 𝓜] F := by
  have hκ : @Measurable _ _ (linkSigma 𝓜) (inferInstance : MeasurableSpace (GaugeField a))
      (truncate ha 𝓜) :=
    measurable_of_forall_link (measurable_truncate_eval ha 𝓜)
  have hcomp := hF.comp hκ
  have e : F ∘ truncate ha 𝓜 = F :=
    funext fun U => hd _ _ fun b hb => truncate_of_mem ha h𝓜 U hb
  rwa [e] at hcomp
theorem isPositivelyOriented_or_opposite (b : Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem mem_linksInside {S : Set AmbientSpace} {b : Link a} (hp : b.IsPositivelyOriented)
    (ht : (b.initial : AmbientSpace) ∈ S) (hh : (b.terminal : AmbientSpace) ∈ S) :
    b ∈ linksInside a S :=
  ⟨hp, fun c hc => by
    rw [mem_singleton_iff] at hc
    subst hc
    exact ⟨ht, hh⟩⟩
theorem endpoints_mem_of_mem_linksInside {S : Set AmbientSpace} {b : Link a}
    (hb : b ∈ linksInside a S) :
    (b.initial : AmbientSpace) ∈ S ∧ (b.terminal : AmbientSpace) ∈ S :=
  hb.2 b (mem_singleton b)
theorem linksInside_isLinkSet (S : Set AmbientSpace) : IsLinkSet (linksInside a S) :=
  fun _ hb => hb.1
theorem regionSigma_eq_linkSigma (S : Set AmbientSpace) :
    (regionSigma S : MeasurableSpace (GaugeField a)) = linkSigma (linksInside a S) := by
  refine le_antisymm (iSup₂_le fun b hb => ?_)
    (linkSigma_mono fun b hb => endpoints_mem_of_mem_linksInside hb)
  have hm : Measurable[linkSigma (linksInside a S)] fun U : GaugeField a => U b := by
    rcases isPositivelyOriented_or_opposite b with hp | hp
    · exact measurable_eval_link (mem_linksInside hp hb.1 hb.2)
    · have e : (fun U : GaugeField a => U b) = fun U => (U b.opposite)⁻¹ :=
        funext fun U => by rw [U.2 b, inv_inv]
      rw [e]
      exact (continuous_inv.measurable :
          Measurable fun g : Matrices.ComplexMatrix2.specialUnitary => g⁻¹).comp
        (measurable_eval_link (mem_linksInside hp hb.2 hb.1))
  exact hm.comap_le
theorem finite_latticePoints_of_isBounded (ha : 0 < a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) : {x : LatticePoint a | (x : AmbientSpace) ∈ S}.Finite := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hS
  have hfin : (Icc (fun _ : Fin 4 => -⌈R / a⌉) (fun _ => ⌈R / a⌉)).Finite := finite_Icc _ _
  refine (hfin.image
    (fun n : Fin 4 → ℤ => (⟨fun μ => (n μ : ℝ) * a, n, fun _ => rfl⟩ : LatticePoint a))).subset ?_
  intro x hx
  obtain ⟨n, hn⟩ := x.2
  have hb : ∀ μ, |n μ| ≤ ⌈R / a⌉ := fun μ => by
    have h1 : |(x : AmbientSpace) μ| ≤ R := (norm_le_pi_norm (x : AmbientSpace) μ).trans (hR _ hx)
    rw [hn μ, abs_mul, abs_of_pos ha] at h1
    have h2 : |(n μ : ℝ)| ≤ (⌈R / a⌉ : ℝ) := ((le_div_iff₀ ha).2 h1).trans (Int.le_ceil _)
    exact_mod_cast h2
  exact ⟨n, ⟨fun μ => (abs_le.1 (hb μ)).1, fun μ => (abs_le.1 (hb μ)).2⟩,
    Subtype.ext (funext fun μ => (hn μ).symm)⟩
theorem finite_linksInside (ha : 0 < a) {S : Set AmbientSpace} (hS : Bornology.IsBounded S) :
    (linksInside a S).Finite := by
  have hs := finite_latticePoints_of_isBounded ha hS
  have hinj : Function.Injective (fun b : Link a => (b.initial, b.terminal)) :=
    fun b b' h => Link.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact ((hs.prod hs).preimage hinj.injOn).subset fun b hb =>
    ⟨(endpoints_mem_of_mem_linksInside hb).1, (endpoints_mem_of_mem_linksInside hb).2⟩
theorem isLocalObservable_iff (ha : 0 < a) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsLocalObservable F ↔ ∃ 𝓜 : Set (Link a), IsLinkSet 𝓜 ∧ 𝓜.Finite ∧ DependsOnlyOn 𝓜 F := by
  constructor
  · rintro ⟨S, hS, hm⟩
    have hm' : Measurable[linkSigma (linksInside a S)] F := by
      rw [← regionSigma_eq_linkSigma S]
      exact hm
    exact ⟨linksInside a S, linksInside_isLinkSet S, finite_linksInside ha hS,
      dependsOnlyOn_of_measurable hm'⟩
  · rintro ⟨𝓜, h𝓜, hfin, hd⟩
    refine ⟨(fun b : Link a => (b.initial : AmbientSpace)) '' 𝓜 ∪
        (fun b : Link a => (b.terminal : AmbientSpace)) '' 𝓜,
      ((hfin.image _).union (hfin.image _)).isBounded, ?_⟩
    have hsub : 𝓜 ⊆ linksInside a
        ((fun b : Link a => (b.initial : AmbientSpace)) '' 𝓜 ∪
          (fun b : Link a => (b.terminal : AmbientSpace)) '' 𝓜) :=
      fun b hb => mem_linksInside (h𝓜 hb) (Or.inl ⟨b, hb, rfl⟩) (Or.inr ⟨b, hb, rfl⟩)
    have hm := measurable_of_dependsOnlyOn ha (linksInside_isLinkSet _) hF.1
      (fun U U' h => hd U U' fun b hb => h b (hsub hb))
    change Measurable[regionSigma _] F
    rw [regionSigma_eq_linkSigma]
    exact hm
theorem measurableIffDependsOnly_of_pos (ha : 0 < a) : MeasurableIffDependsOnly a := by
  unfold MeasurableIffDependsOnly
  refine ⟨fun 𝓜 F h𝓜 hF => ⟨dependsOnlyOn_of_measurable, measurable_of_dependsOnlyOn ha h𝓜 hF.1⟩,
    regionSigma_eq_linkSigma,
    fun S => Set.ext fun F => ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩,
    fun F hF => isLocalObservable_iff ha hF⟩
  · have hm : Measurable[linkSigma (linksInside a S)] F := by
      rw [← regionSigma_eq_linkSigma S]
      exact h.2
    exact dependsOnlyOn_of_measurable hm
  · change Measurable[regionSigma S] F
    rw [regionSigma_eq_linkSigma]
    exact measurable_of_dependsOnlyOn ha (linksInside_isLinkSet S) h.1.1 h.2
theorem measurableIffDependsOnlyAllSpacings_holds : MeasurableIffDependsOnlyAllSpacings := by apply _root_.YangMills.Construction.InfiniteLattice.MeasurableIffDependsOnlyProof.measurableIffDependsOnly_of_pos <;> assumption
end YangMills.Construction.InfiniteLattice.MeasurableIffDependsOnlyProof
