import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusOfAnyShape
import YangMills.Construction.InfiniteLattice.ReflectionsOfOneFamily
import YangMills.Construction.ReflectionPositivity.ActionOfASplitTorusSplits
import YangMills.Construction.ReflectionPositivity.OneReflectionTwoMirrorsAndWhatTheyCut
import YangMills.Construction.ReflectionPositivity.PullBacksOnASplitTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.SplitTorusActionProof
open NormalFamilies
variable (Γ : PeriodSublattice 1)
theorem linkClass_mem_linksInside_iff {T : Set Γ.QuotientTorus} (b : PositiveLink 1) :
    Γ.linkClass b ∈ Γ.linksInside T ↔
      Γ.quotientMap b.1.initial ∈ T ∧ Γ.quotientMap b.1.terminal ∈ T := by
  change Γ.linkEndpoints (Γ.linkClass b) ⊆ T ↔ _
  rw [Γ.linkEndpoints_eq, Γ.orientedOfLink_linkClass, Γ.sourcePoint_orientedClass,
    Γ.targetPoint_orientedClass, Set.insert_subset_iff, Set.singleton_subset_iff]
theorem isPositivelyOriented_forwardFrom (x : LatticePoint 1) (ρ : Fin 4) :
    (Link.forwardFrom x ρ).IsPositivelyOriented :=
  ⟨ρ, by simp [Link.forwardFrom]⟩
theorem plaquetteLinks_subset_linksInside_iff (q : Γ.QuotientPlaquette) (T : Set Γ.QuotientTorus) :
    Γ.plaquetteLinks q ⊆ Γ.linksInside T ↔ Γ.plaquetteVertices q ⊆ T := by
  unfold PeriodSublattice.plaquetteLinks PeriodSublattice.plaquetteVertices
  generalize Γ.plaquetteRep q = p
  constructor
  · intro h
    have e : ∀ (x : LatticePoint 1) (ρ : Fin 4), Link.forwardFrom x ρ ∈ p.linkSet →
        Γ.quotientMap x ∈ T ∧ Γ.quotientMap (x + axisStep 1 ρ) ∈ T := fun x ρ hb =>
      (linkClass_mem_linksInside_iff Γ ⟨_, isPositivelyOriented_forwardFrom x ρ⟩).1
        (h ⟨⟨_, isPositivelyOriented_forwardFrom x ρ⟩, hb, rfl⟩)
    have b₁ := e p.corner p.lowAxis
      (by simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges])
    have b₂ := e (p.corner + axisStep 1 p.lowAxis) p.highAxis
      (by simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges])
    have b₄ := e p.corner p.highAxis
      (by simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges])
    rintro _ ⟨s, hs, rfl⟩
    rcases hs with rfl | rfl | rfl | rfl
    · exact b₁.1
    · exact b₁.2
    · exact b₂.2
    · exact b₄.2
  · intro h
    have c : ∀ s ∈ p.cornerSet, Γ.quotientMap s ∈ T := fun s hs => h ⟨s, hs, rfl⟩
    have m₁ : p.corner ∈ p.cornerSet := by simp [ElementaryPlaquette.cornerSet]
    have m₂ : p.corner + axisStep 1 p.lowAxis ∈ p.cornerSet := by
      simp [ElementaryPlaquette.cornerSet]
    have m₃ : p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis ∈ p.cornerSet := by
      simp [ElementaryPlaquette.cornerSet]
    have m₄ : p.corner + axisStep 1 p.highAxis ∈ p.cornerSet := by
      simp [ElementaryPlaquette.cornerSet]
    rintro d ⟨⟨b, hpos⟩, hb, rfl⟩
    rw [linkClass_mem_linksInside_iff]
    simp only [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges, Set.mem_ofPred_eq,
      List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨c _ m₁, c _ m₂⟩
    · exact ⟨c _ m₂, c _ m₃⟩
    · refine ⟨c _ m₄, ?_⟩
      change Γ.quotientMap (p.corner + axisStep 1 p.highAxis + axisStep 1 p.lowAxis) ∈ T
      rw [add_right_comm]
      exact c _ m₃
    · exact ⟨c _ m₁, c _ m₄⟩
theorem splitTorusActionSplits_holds (hExt : PeriodicQuotient.FinitenessClaim)
    (hDesc : SplitTorusDescent)
    (hTwo : TwoLevelsOfOneReflection)
    (hPull : SplitTorusPullbacks)
    (hRefl : ReflectionIdentities.Statement) : SplitTorusActionSplits := by
  intro Γ n hn z hs c hc P
  classical
  have E := hExt.1 Γ
  have : Finite Γ.QuotientPlaquette := E.finite_quotientPlaquette
  let : Fintype Γ.QuotientPlaquette := Fintype.ofFinite _
  have hM : Γ.DescendsToQuotient P.reflectSymmetry :=
    (hDesc Γ n hn z c hc 0 hs).2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, hT⟩ := hTwo Γ n hn z c hc hs
  have hUp : Γ.descendPoint P.reflectSymmetry '' Γ.plusHalf n z c = Γ.minusHalf n z c :=
    hT.2.2.2.1
  have hAct : ∀ p : Γ.QuotientPlaquette,
      Γ.compPullback P.reflectSymmetry (fun U => Γ.quotientFaceEnergy U p) =
        fun U => Γ.quotientFaceEnergy U (Γ.descendFace P.reflectSymmetry p) :=
    ((hPull 1 one_pos Γ n hn z hs).2.1 P.reflectSymmetry
      (isClassIsometry_reflectAcross hc)).2.2.2.2.2.2.2.2.2.1
  have hinv : Function.Involutive (Γ.descendPoint P.reflectSymmetry) := by
    intro s
    obtain ⟨x, rfl⟩ : ∃ x, Γ.quotientMap x = s := ⟨s.out, QuotientAddGroup.out_eq' s⟩
    rw [hM.descendPoint_quotientMap, hM.descendPoint_quotientMap]
    exact congrArg Γ.quotientMap (Subtype.ext ((hRefl n hn c c hc hc 0).1 x))
  have hLo : Γ.descendPoint P.reflectSymmetry '' Γ.minusHalf n z c = Γ.plusHalf n z c := by
    rw [← hUp, Set.image_image]
    simp only [hinv _, Set.image_id']
  have hinj := hM.descendPoint_bijective.1
  obtain ⟨up, hup⟩ : ∃ up : Γ.QuotientPlaquette → Prop,
      ∀ q, up q ↔ Γ.plaquetteLinks q ⊆ Γ.plusLinks n z c := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨lo, hlo⟩ : ∃ lo : Γ.QuotientPlaquette → Prop,
      ∀ q, lo q ↔ Γ.plaquetteLinks q ⊆ Γ.minusLinks n z c := ⟨_, fun _ => Iff.rfl⟩
  have hupc : ∀ q, up q ↔ Γ.plaquetteVertices q ⊆ Γ.plusHalf n z c := fun q =>
    (hup q).trans (plaquetteLinks_subset_linksInside_iff Γ q _)
  have hloc : ∀ q, lo q ↔ Γ.plaquetteVertices q ⊆ Γ.minusHalf n z c := fun q =>
    (hlo q).trans (plaquetteLinks_subset_linksInside_iff Γ q _)
  have hupρ : ∀ q, up (Γ.descendFace P.reflectSymmetry q) ↔ lo q := fun q => by
    rw [hupc, hloc, hM.plaquetteVertices_descend, ← hLo, Set.image_subset_image_iff hinj]
  have hloρ : ∀ q, lo (Γ.descendFace P.reflectSymmetry q) ↔ up q := fun q => by
    rw [hupc, hloc, hM.plaquetteVertices_descend, ← hUp, Set.image_subset_image_iff hinj]
  have hcut : ∀ q, Γ.IsSplitPlaquette n z c q ↔ ¬ up q ∧ ¬ lo q := fun q => by
    rw [hup, hlo]
    exact Iff.rfl
  let A₀ : Γ.QuotientField → ℝ := fun U =>
    ∑ q ∈ Finset.univ.filter (fun q => up q ∧ lo q), Γ.quotientFaceEnergy U q
  let Aplus : Γ.QuotientField → ℝ := fun U =>
    ∑ q ∈ Finset.univ.filter (fun q => up q ∧ ¬ lo q), Γ.quotientFaceEnergy U q
  have hθ : ∀ U, Γ.compPullback P.reflectSymmetry Aplus U =
      ∑ q ∈ Finset.univ.filter (fun q => lo q ∧ ¬ up q), Γ.quotientFaceEnergy U q := fun U => by
    refine Finset.sum_equiv (Equiv.ofBijective _ hM.descendFace_bijective) ?_ ?_
    · intro q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.ofBijective_apply, hupρ, hloρ]
    · intro q _
      exact congrFun (hAct q) U
  have hcutsum : ∀ U, (∑ᶠ (p : Γ.QuotientPlaquette) (_ : Γ.IsSplitPlaquette n z c p),
      Γ.quotientFaceEnergy U p) =
      ∑ q ∈ Finset.univ.filter (fun q => ¬ up q ∧ ¬ lo q), Γ.quotientFaceEnergy U q := fun U => by
    rw [finsum_eq_sum_of_fintype, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [finsum_eq_if]
    by_cases h : Γ.IsSplitPlaquette n z c q
    · rw [if_pos h, if_pos ((hcut q).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hcut q).2 h'))]
  have hsum : ∀ U, (∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p) =
      A₀ U + Aplus U + Γ.compPullback P.reflectSymmetry Aplus U +
        ∑ᶠ (p : Γ.QuotientPlaquette) (_ : Γ.IsSplitPlaquette n z c p), Γ.quotientFaceEnergy U p :=
      fun U => by
    rw [hθ, hcutsum, finsum_eq_sum_of_fintype]
    simp only [A₀, Aplus, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h₁ : up q <;> by_cases h₂ : lo q <;> simp [h₁, h₂]
  refine ⟨A₀, Aplus, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_finsetSum _ fun q _ => E.continuous_quotientFaceEnergy q
  · exact continuous_finsetSum _ fun q _ => E.continuous_quotientFaceEnergy q
  · exact fun U => Finset.sum_nonneg fun q _ => (E.quotientFaceEnergy_mem_Icc q U).1
  · exact fun U => Finset.sum_nonneg fun q _ => (E.quotientFaceEnergy_mem_Icc q U).1
  · intro U U' h
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := (Finset.mem_filter.1 hq).2
    exact E.quotientFaceEnergy_dependsOn q U U' fun b hb =>
      h b (show b ∈ Γ.plusLinks n z c ∩ Γ.minusLinks n z c from
        ⟨(hup q).1 hq'.1 hb, (hlo q).1 hq'.2 hb⟩)
  · intro U U' h
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := (Finset.mem_filter.1 hq).2
    exact E.quotientFaceEnergy_dependsOn q U U' fun b hb => h b ((hup q).1 hq'.1 hb)
  · intro β U
    rw [PeriodSublattice.boltzmannWeight, PeriodSublattice.splitFaceWeight, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add, hsum U]
    congr 1
    ring
end YangMills.Construction.InfiniteLattice.SplitTorusActionProof
