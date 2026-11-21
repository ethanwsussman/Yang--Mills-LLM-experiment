import YangMills.Construction.InfiniteLattice.WhatAnObservableDependsOnAndItsSupport
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.ObservableDependence
theorem gaugeFieldOfPositive_apply_of_mem (g : positiveLinks 1 → Matrices.ComplexMatrix2.specialUnitary)
    {e : Link 1} (he : e ∈ positiveLinks 1) : gaugeFieldOfPositive one_pos g e = g ⟨e, he⟩ :=
  dif_pos he
theorem mem_positiveLinks_or_opposite (e : Link 1) :
    e ∈ positiveLinks 1 ∨ e.opposite ∈ positiveLinks 1 := by
  obtain ⟨μ, hμ | hμ⟩ := e.isAdjacent
  · exact Or.inl ⟨μ, hμ⟩
  · exact Or.inr ⟨μ, show e.initial - e.terminal = axisStep 1 μ by rw [← neg_sub, hμ, neg_neg]⟩
theorem eq_of_measurable_linkSigma {L : Set (Link 1)} {F : GaugeField 1 → ℂ}
    (hF : Measurable[linkSigma L] F) {A B : GaugeField 1} (hAB : ∀ e ∈ L, A e = B e) :
    F A = F B := by
  let m' : MeasurableSpace (GaugeField 1) :=
    { MeasurableSet' := fun s => (A ∈ s ↔ B ∈ s)
      measurableSet_empty := by simp
      measurableSet_compl := fun s hs => not_congr hs
      measurableSet_iUnion := fun f hf => by
        simp only [mem_iUnion]
        exact exists_congr hf }
  have hle : linkSigma L ≤ m' := by
    refine iSup₂_le fun e he => ?_
    rintro s ⟨t, -, rfl⟩
    show A ∈ _ ↔ B ∈ _
    simp only [mem_preimage, hAB e he]
  have hpre : MeasurableSet[linkSigma L] (F ⁻¹' {F A}) := hF (measurableSet_singleton _)
  have hiff : A ∈ F ⁻¹' {F A} ↔ B ∈ F ⁻¹' {F A} := hle _ hpre
  exact (hiff.mp rfl).symm
theorem eq_on_linksWithin_of_eq_on_positive {R : Set AmbientSpace} {A B : GaugeField 1}
    (hAB : ∀ e ∈ {e | e ∈ positiveLinks 1 ∧ LinksLieIn {e} R}, A e = B e) :
    ∀ e ∈ linksWithin (a := 1) R, A e = B e := by
  intro e he
  rcases mem_positiveLinks_or_opposite e with hp | hp
  · exact hAB e ⟨hp, fun c hc => by rw [mem_singleton_iff.mp hc]; exact he⟩
  · have hop := hAB e.opposite ⟨hp, fun c hc => by
      rw [mem_singleton_iff.mp hc]; exact ⟨he.2, he.1⟩⟩
    rw [A.2 e, B.2 e] at hop
    exact inv_injective hop
theorem dependsOnlyOn_of_isRegionMeasurable {R : Set AmbientSpace} {F : GaugeField 1 → ℂ}
    (hF : IsRegionMeasurable R F) :
    DependsOnlyOn {e | e ∈ positiveLinks 1 ∧ LinksLieIn {e} R} F :=
  fun _ _ h => eq_of_measurable_linkSigma hF (eq_on_linksWithin_of_eq_on_positive h)
def extendByIdentity (L : Set (Link 1)) (g : L → Matrices.ComplexMatrix2.specialUnitary) :
    GaugeField 1 :=
  open Classical in
  gaugeFieldOfPositive one_pos fun e => if h : e.1 ∈ L then g ⟨e.1, h⟩ else 1
theorem continuous_extendByIdentity (L : Set (Link 1)) : Continuous (extendByIdentity L) := by
  classical
  refine Continuous.subtype_mk (continuous_pi fun e => ?_) _
  have hval : ∀ c : positiveLinks 1, Continuous fun g : L → Matrices.ComplexMatrix2.specialUnitary =>
      if h : c.1 ∈ L then g ⟨c.1, h⟩ else 1 := fun c => by
    by_cases h : c.1 ∈ L
    · simp only [dif_pos h]
      exact continuous_apply _
    · simp only [dif_neg h]
      exact continuous_const
  simp only [extendFromPositive]
  by_cases h : e ∈ positiveLinks 1
  · simp only [dif_pos h]
    exact hval ⟨e, h⟩
  · by_cases h' : e.opposite ∈ positiveLinks 1
    · simp only [dif_neg h, dif_pos h']
      exact (hval ⟨e.opposite, h'⟩).inv
    · simp only [dif_neg h, dif_neg h']
      exact continuous_const
theorem measurable_linkSigma_of_dependsOnlyOn {L : Set (Link 1)} (hL : IsLinkSet L)
    {F : GaugeField 1 → ℂ} (hF : Measurable F) (hd : DependsOnlyOn L F) :
    Measurable[linkSigma L] F := by
  classical
  have : Countable L := (Set.Countable.mono hL (Set.to_countable _)).to_subtype
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  let π : GaugeField 1 → L → Matrices.ComplexMatrix2.specialUnitary := fun A e => A e.1
  have hπ : Measurable[linkSigma L] π := by
    refine @measurable_pi_lambda _ _ _ (linkSigma L) _ _ fun e => ?_
    exact measurable_iff_comap_le.2 (le_iSup₂_of_le e.1 e.2 le_rfl)
  have hcomp : Measurable (F ∘ extendByIdentity L) :=
    hF.comp (continuous_extendByIdentity L).measurable
  have hfac : F = (F ∘ extendByIdentity L) ∘ π := by
    funext A
    refine hd _ _ fun e he => ?_
    show A e = extendByIdentity L (fun c => A c.1) e
    rw [extendByIdentity, gaugeFieldOfPositive_apply_of_mem _ (hL he)]
    simp only [dif_pos he]
  rw [hfac]
  exact hcomp.comp hπ
theorem isRegionMeasurable_of_dependsOnlyOn {L : Set (Link 1)} (hL : IsLinkSet L)
    {R : Set AmbientSpace} (hR : LinksLieIn L R) {F : GaugeField 1 → ℂ} (hF : Measurable F)
    (hd : DependsOnlyOn L F) : IsRegionMeasurable R F := by
  have hle : linkSigma L ≤ regionSigma (a := 1) R :=
    iSup₂_le fun e he => le_iSup₂_of_le e (hR e he) le_rfl
  exact (measurable_linkSigma_of_dependsOnlyOn hL hF hd).mono hle le_rfl
theorem dependsOnlyOn_inter {L L' : Set (Link 1)} (hL : IsLinkSet L) (hL' : IsLinkSet L')
    {F : GaugeField 1 → ℂ} (hd : DependsOnlyOn L F) (hd' : DependsOnlyOn L' F) :
    DependsOnlyOn (L ∩ L') F := by
  classical
  intro A B hAB
  let C : GaugeField 1 :=
    gaugeFieldOfPositive one_pos fun e => if e.1 ∈ L then A e.1 else B e.1
  have hC : ∀ e (he : e ∈ positiveLinks 1), C e = if e ∈ L then A e else B e :=
    fun e he => gaugeFieldOfPositive_apply_of_mem _ he
  have h₁ : F A = F C := hd _ _ fun e he => by rw [hC e (hL he), if_pos he]
  have h₂ : F C = F B := hd' _ _ fun e he => by
    rw [hC e (hL' he)]
    by_cases hm : e ∈ L
    · rw [if_pos hm]
      exact hAB e ⟨hm, he⟩
    · rw [if_neg hm]
  exact h₁.trans h₂
theorem finite_latticePoints_of_isBounded {S : Set AmbientSpace} (hS : Bornology.IsBounded S) :
    {x : LatticePoint 1 | (x : AmbientSpace) ∈ S}.Finite := by
  obtain ⟨r, hr⟩ := hS.subset_closedBall (0 : AmbientSpace)
  obtain ⟨N, hN⟩ := exists_nat_ge r
  refine Set.Finite.of_injOn (f := fun (x : LatticePoint 1) (μ : Fin 4) => ⌊(x : AmbientSpace) μ⌋)
    (t := Set.Icc (fun _ => -(N : ℤ)) (fun _ => (N : ℤ))) ?_ ?_ (Set.finite_Icc _ _)
  · intro x hx
    obtain ⟨k, hk⟩ := x.2
    have hbd : ∀ μ, |(x : AmbientSpace) μ| ≤ N := fun μ => by
      have h1 := hr hx
      rw [mem_closedBall_zero_iff] at h1
      exact ((norm_le_pi_norm (x : AmbientSpace) μ).trans h1).trans hN
    have hfl : ∀ μ, ⌊(x : AmbientSpace) μ⌋ = k μ := fun μ => by
      rw [hk μ, mul_one, Int.floor_intCast]
    constructor
    · intro μ
      have h2 := (abs_le.mp (hbd μ)).1
      rw [hk μ, mul_one] at h2
      show -(N : ℤ) ≤ ⌊(x : AmbientSpace) μ⌋
      rw [hfl μ]
      exact_mod_cast h2
    · intro μ
      have h2 := (abs_le.mp (hbd μ)).2
      rw [hk μ, mul_one] at h2
      show ⌊(x : AmbientSpace) μ⌋ ≤ (N : ℤ)
      rw [hfl μ]
      exact_mod_cast h2
  · intro x _ y _ hxy
    obtain ⟨k, hk⟩ := x.2
    obtain ⟨k', hk'⟩ := y.2
    refine Subtype.ext (funext fun μ => ?_)
    have h1 := congrFun hxy μ
    simp only [hk μ, hk' μ, mul_one, Int.floor_intCast] at h1
    rw [hk μ, hk' μ, h1]
theorem finite_positiveLinks_of_isBounded {S : Set AmbientSpace} (hS : Bornology.IsBounded S) :
    {e : Link 1 | e ∈ positiveLinks 1 ∧ LinksLieIn {e} S}.Finite := by
  have hT := finite_latticePoints_of_isBounded hS
  refine Set.Finite.of_injOn (f := fun e : Link 1 => (e.initial, e.terminal))
    (t := {x : LatticePoint 1 | (x : AmbientSpace) ∈ S} ×ˢ
      {x : LatticePoint 1 | (x : AmbientSpace) ∈ S}) ?_ ?_ (hT.prod hT)
  · intro e he
    exact ⟨(he.2 e rfl).1, (he.2 e rfl).2⟩
  · intro e _ e' _ h
    exact Link.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
theorem isLocalObservable_iff {F : GaugeField 1 → ℂ} (hF : IsBoundedObservable F) :
    IsLocalObservable F ↔ ∃ L₀ : Set (Link 1), IsLinkSet L₀ ∧ L₀.Finite ∧ DependsOnlyOn L₀ F := by
  constructor
  · rintro ⟨S, hS, hm⟩
    exact ⟨_, fun e he => he.1, finite_positiveLinks_of_isBounded hS,
      dependsOnlyOn_of_isRegionMeasurable hm⟩
  · rintro ⟨L₀, h₀, hfin, hd⟩
    let S : Set AmbientSpace := (fun e : Link 1 => (e.initial : AmbientSpace)) '' L₀ ∪
      (fun e : Link 1 => (e.terminal : AmbientSpace)) '' L₀
    have hSfin : S.Finite := (hfin.image _).union (hfin.image _)
    refine ⟨S, hSfin.isBounded, isRegionMeasurable_of_dependsOnlyOn h₀ (fun e he => ?_) hF.1 hd⟩
    exact ⟨Or.inl ⟨e, he, rfl⟩, Or.inr ⟨e, he, rfl⟩⟩
theorem isLeast_observableSupport {F : GaugeField 1 → ℂ} {L₀ : Set (Link 1)} (h₀ : IsLinkSet L₀)
    (hfin : L₀.Finite) (hd : DependsOnlyOn L₀ F) :
    IsLeast {K : Set (Link 1) | IsLinkSet K ∧ DependsOnlyOn K F} (observableSupport F) ∧
      (observableSupport F).Finite := by
  let 𝒞 : Set (Set (Link 1)) := {L | IsLinkSet L ∧ L.Finite ∧ DependsOnlyOn L F}
  obtain ⟨L₁, h₁, hmin⟩ := (InvImage.wf Set.ncard Nat.lt_wfRel.wf).has_min 𝒞 ⟨L₀, h₀, hfin, hd⟩
  have hsub : ∀ L ∈ 𝒞, L₁ ⊆ L := fun L hL => by
    have hc : L₁ ∩ L ∈ 𝒞 := ⟨inter_subset_left.trans h₁.1, h₁.2.1.inter_of_left _,
      dependsOnlyOn_inter h₁.1 hL.1 h₁.2.2 hL.2.2⟩
    have hle : L₁.ncard ≤ (L₁ ∩ L).ncard := not_lt.mp (hmin _ hc)
    have heq := Set.eq_of_subset_of_ncard_le inter_subset_left hle h₁.2.1
    exact heq ▸ inter_subset_right
  have hsupp : observableSupport F = L₁ :=
    Subset.antisymm (sInter_subset_of_mem h₁) (subset_sInter hsub)
  rw [hsupp]
  refine ⟨⟨⟨h₁.1, h₁.2.2⟩, fun K hK => ?_⟩, h₁.2.1⟩
  have hc : L₁ ∩ K ∈ 𝒞 := ⟨inter_subset_left.trans h₁.1, h₁.2.1.inter_of_left _,
    dependsOnlyOn_inter h₁.1 hK.1 h₁.2.2 hK.2⟩
  exact (hsub _ hc).trans inter_subset_right
theorem mem_regionObservables_iff {F : GaugeField 1 → ℂ} (hF : IsBoundedObservable F)
    (hl : IsLeast {K : Set (Link 1) | IsLinkSet K ∧ DependsOnlyOn K F} (observableSupport F))
    (R : Set AmbientSpace) :
    F ∈ regionObservables 1 R ↔ LinksLieIn (observableSupport F) R := by
  constructor
  · intro hR e he
    have hs := hl.2 (show {e | e ∈ positiveLinks 1 ∧ LinksLieIn {e} R} ∈ _ from
      ⟨fun c hc => hc.1, dependsOnlyOn_of_isRegionMeasurable hR.2⟩)
    exact (hs he).2 e rfl
  · intro hR
    exact ⟨hF, isRegionMeasurable_of_dependsOnlyOn hl.1.1 hR hF.1 hl.1.2⟩
theorem observableSupport_eq_empty_iff {F : GaugeField 1 → ℂ}
    (hl : IsLeast {K : Set (Link 1) | IsLinkSet K ∧ DependsOnlyOn K F} (observableSupport F)) :
    observableSupport F = ∅ ↔ ∃ c : ℂ, ∀ A, F A = c := by
  constructor
  · intro he
    have hd := hl.1.2
    rw [he] at hd
    exact ⟨F (gaugeFieldOfPositive one_pos 1), fun A => hd _ _ fun e he' => he'.elim⟩
  · rintro ⟨c, hc⟩
    refine eq_empty_of_subset_empty (sInter_subset_of_mem ?_)
    exact ⟨empty_subset _, finite_empty, fun A B _ => by rw [hc, hc]⟩
theorem statement_holds : ObservableDependence.Statement := by
  intro F hF L L' hL hL' R
  refine ⟨fun hR => dependsOnlyOn_of_isRegionMeasurable hR.2,
    fun hR hd => ⟨hF, isRegionMeasurable_of_dependsOnlyOn hL hR hF.1 hd⟩,
    dependsOnlyOn_inter hL hL', isLocalObservable_iff hF, fun hloc => ?_, fun hloc => ?_⟩
  · obtain ⟨L₀, h₀, hfin, hd⟩ := (isLocalObservable_iff hF).mp hloc
    exact isLeast_observableSupport h₀ hfin hd
  · obtain ⟨L₀, h₀, hfin, hd⟩ := (isLocalObservable_iff hF).mp hloc
    have hl := (isLeast_observableSupport h₀ hfin hd).1
    exact ⟨mem_regionObservables_iff hF hl R, observableSupport_eq_empty_iff hl⟩
end YangMills.Construction.InfiniteLattice.ObservableDependence
