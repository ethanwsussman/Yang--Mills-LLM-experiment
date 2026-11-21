import YangMills.Construction.Continuum.ExistenceOfAStableChoiceProof
import YangMills.Construction.ToriAtArbitraryCouplings.ChoicesClosedUnderCountablyManyMaps
import YangMills.Construction.ToriAtArbitraryCouplings.ClassC1OnASupportIsSeparable
import YangMills.Construction.ToriAtArbitraryCouplings.TheNormOfClassC1OnASupport
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace ChoicesStableUnderCountableMaps
theorem countable_setOf_isRationalBox :
    {P : Set (Fin 4 → ℝ) | IsRationalBox P}.Countable := by apply _root_.YangMills.Construction.DisjointTuples.StableChoice.countable_setOf_isRatBox <;> assumption
theorem countable_supportFamily (s : TorusSide) (E : Ambient) :
    (s.supportFamily E).Countable := by
  have hfin := Set.countable_ofPred_finite_subset countable_setOf_isRationalBox
  cases E
  · refine (hfin.image fun B => ⋃ P ∈ B, s.proj '' P).mono ?_
    rintro Q ⟨B, hB, hP, rfl⟩
    exact ⟨B, ⟨hB, fun P hPB => (hP P hPB).1⟩, rfl⟩
  · refine (hfin.image fun B => ⋃₀ B).mono ?_
    rintro Q ⟨B, hB, hP, rfl⟩
    exact ⟨B, ⟨hB, hP⟩, rfl⟩
theorem union_mem_supportFamily (s : TorusSide) (E : Ambient) {U V : Set (s.Point E)}
    (hU : U ∈ s.supportFamily E) (hV : V ∈ s.supportFamily E) : U ∪ V ∈ s.supportFamily E := by
  cases E
  · obtain ⟨B, hB, hP, rfl⟩ := hU
    obtain ⟨B', hB', hP', rfl⟩ := hV
    refine ⟨B ∪ B', hB.union hB', ?_, (Set.biUnion_union B B' _).symm⟩
    rintro P (h | h)
    · exact hP P h
    · exact hP' P h
  · obtain ⟨B, hB, hP, rfl⟩ := hU
    obtain ⟨B', hB', hP', rfl⟩ := hV
    refine ⟨B ∪ B', hB.union hB', ?_, (Set.sUnion_union B B').symm⟩
    rintro P (h | h)
    · exact hP P h
    · exact hP' P h
theorem c1VanishingOutside_mono (s : TorusSide) (E : Ambient) {U V : Set (s.Point E)}
    (h : U ⊆ V) : s.c1VanishingOutside E U ⊆ s.c1VanishingOutside E V :=
  fun _ hf => ⟨hf.1, fun x hx => hf.2 x fun hu => hx (h hu)⟩
theorem countable_span_rat {M : Type*} [AddCommGroup M] [Module ℚ M] {S : Set M}
    (hS : S.Countable) : (Submodule.span ℚ S : Set M).Countable := by
  have : Countable S := hS.to_subtype
  have h : (Submodule.span ℚ S : Set M) =
      Set.range (Finsupp.linearCombination ℚ (Subtype.val : S → M)) := by
    rw [← LinearMap.coe_range, Finsupp.range_linearCombination, Subtype.range_coe]
  rw [h]
  exact Set.countable_range _
theorem rat_smul_eq_cast_smul {X : Type*} (q : ℚ) (f : X → ℝ) : q • f = (q : ℝ) • f := by
  funext x
  simp [Rat.smul_def]
def permWord {X : Type*} (G : Set (Equiv.Perm X)) (w : List G) : Equiv.Perm X :=
  (w.map Subtype.val).prod
theorem permWord_maps_c1 (s : TorusSide) (E : Ambient) (G : Set (Equiv.Perm (s.Point E)))
    (hG : ∀ g ∈ G, ∀ U ∈ s.supportFamily E, ∃ V ∈ s.supportFamily E,
      ∀ f ∈ s.c1VanishingOutside E U, f ∘ g.symm ∈ s.c1VanishingOutside E V) (w : List G) :
    ∀ U ∈ s.supportFamily E, ∃ V ∈ s.supportFamily E, ∀ f ∈ s.c1VanishingOutside E U,
      f ∘ (permWord G w).symm ∈ s.c1VanishingOutside E V := by
  induction w with
  | nil => exact fun U hU => ⟨U, hU, fun f hf => hf⟩
  | cons g w ih =>
    intro U hU
    obtain ⟨V₁, hV₁, h₁⟩ := ih U hU
    obtain ⟨V₂, hV₂, h₂⟩ := hG g.1 g.2 V₁ hV₁
    exact ⟨V₂, hV₂, fun f hf => h₂ _ (h₁ f hf)⟩
def orbitSpan {X : Type*} (G : Set (Equiv.Perm X)) (S : Set (X → ℝ)) :
    Submodule ℚ (X → ℝ) :=
  Submodule.span ℚ (⋃ w : List G, (fun f : X → ℝ => f ∘ (permWord G w).symm) '' S)
theorem countable_orbitSpan {X : Type*} {G : Set (Equiv.Perm X)} (hG : G.Countable)
    {S : Set (X → ℝ)} (hS : S.Countable) :
    (orbitSpan G S : Set (X → ℝ)).Countable := by
  have : Countable G := hG.to_subtype
  exact countable_span_rat (Set.countable_iUnion fun _ => hS.image _)
theorem subset_orbitSpan {X : Type*} (G : Set (Equiv.Perm X)) (S : Set (X → ℝ)) :
    S ⊆ orbitSpan G S := fun f hf =>
  Submodule.subset_span (Set.mem_iUnion.2 ⟨[], f, hf, rfl⟩)
theorem orbitSpan_comp_symm_mem {X : Type*} {G : Set (Equiv.Perm X)} {S : Set (X → ℝ)}
    {g : Equiv.Perm X} (hg : g ∈ G) {v : X → ℝ} (hv : v ∈ orbitSpan G S) :
    v ∘ g.symm ∈ orbitSpan G S := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, f, hf, rfl⟩ := Set.mem_iUnion.1 hv
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨⟨g, hg⟩ :: w, f, hf, rfl⟩)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul q x _ hx => exact Submodule.smul_mem _ q hx
theorem exists_support_of_mem_orbitSpan (hnorm : C1NormOnSupport.Statement) (s : TorusSide)
    (E : Ambient) (G : Set (Equiv.Perm (s.Point E)))
    (hG : ∀ g ∈ G, ∀ U ∈ s.supportFamily E, ∃ V ∈ s.supportFamily E,
      ∀ f ∈ s.c1VanishingOutside E U, f ∘ g.symm ∈ s.c1VanishingOutside E V)
    {S : Set (s.Point E → ℝ)}
    (hS : ∀ f ∈ S, ∃ U ∈ s.supportFamily E, f ∈ s.c1VanishingOutside E U)
    {v : s.Point E → ℝ} (hv : v ∈ orbitSpan G S) :
    ∃ U ∈ s.supportFamily E, v ∈ s.c1VanishingOutside E U := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, f, hf, rfl⟩ := Set.mem_iUnion.1 hv
    obtain ⟨U, hU, hfU⟩ := hS f hf
    obtain ⟨V, hV, h⟩ := permWord_maps_c1 s E G hG w U hU
    exact ⟨V, hV, h f hfU⟩
  | zero => exact ⟨∅, s.empty_mem_supportFamily E,
      (hnorm s E ∅ (s.empty_mem_supportFamily E)).1⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, hU₁, h₁⟩ := hx
    obtain ⟨U₂, hU₂, h₂⟩ := hy
    have hU := union_mem_supportFamily s E hU₁ hU₂
    exact ⟨U₁ ∪ U₂, hU, (hnorm s E _ hU).2.1 x
      (c1VanishingOutside_mono s E Set.subset_union_left h₁) y
      (c1VanishingOutside_mono s E Set.subset_union_right h₂)⟩
  | smul q x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    rw [rat_smul_eq_cast_smul]
    exact ⟨U, hU, (hnorm s E U hU).2.2.1 _ x h⟩
theorem statement_holds (hsep : C1SupportSeparable.Statement)
    (hnorm : C1NormOnSupport.Statement) : Statement := by
  intro s E G hG hmaps
  have hdense : ∀ U : s.supportFamily E, ∃ D : Set (s.Point E → ℝ),
      D ⊆ s.c1VanishingOutside E U.1 ∧ D.Countable ∧
        s.IsC1DenseIn E U.1 D := fun U => hsep s E U.1 U.2
  choose D hDsub hDcount hDdense using hdense
  have : Countable (s.supportFamily E) := (countable_supportFamily s E).to_subtype
  have hS : (⋃ U, D U).Countable := Set.countable_iUnion hDcount
  have hin : ∀ f ∈ ⋃ U, D U, ∃ U ∈ s.supportFamily E, f ∈ s.c1VanishingOutside E U := by
    intro f hf
    obtain ⟨U, hfU⟩ := Set.mem_iUnion.1 hf
    exact ⟨U.1, U.2, hDsub U hfU⟩
  have hlies : ∀ v ∈ orbitSpan G (⋃ U, D U), ∃ U ∈ s.supportFamily E,
      v ∈ s.c1VanishingOutside E U :=
    fun v hv => exists_support_of_mem_orbitSpan hnorm s E G hmaps hin hv
  have hcover : (⋃ U : s.supportFamily E, (orbitSpan G (⋃ U, D U) : Set (s.Point E → ℝ)) ∩
      s.c1VanishingOutside E U.1) = orbitSpan G (⋃ U, D U) := by
    ext v
    constructor
    · intro hv
      obtain ⟨U, hvU⟩ := Set.mem_iUnion.1 hv
      exact hvU.1
    · intro hv
      obtain ⟨U, hU, hvU⟩ := hlies v hv
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hv, hvU⟩
  refine ⟨fun U => (orbitSpan G (⋃ U, D U) : Set (s.Point E → ℝ)) ∩
    s.c1VanishingOutside E U.1, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact fun U => (countable_orbitSpan hG hS).mono Set.inter_subset_left
  · exact fun U => Set.inter_subset_right
  · intro U f hf ε hε
    obtain ⟨φ, hφ, h⟩ := hDdense U f hf ε hε
    exact ⟨φ, ⟨subset_orbitSpan G _ (Set.mem_iUnion.2 ⟨U, hφ⟩), hDsub U hφ⟩, h⟩
  · intro g hg f hf
    rw [hcover] at hf ⊢
    exact orbitSpan_comp_symm_mem hg hf
  · intro n c f hf
    rw [hcover] at hf ⊢
    have hsum : (∑ i, (c i : ℝ) • f i) = ∑ i, c i • f i :=
      Finset.sum_congr rfl fun i _ => (rat_smul_eq_cast_smul (c i) (f i)).symm
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (c i) (hf i)
  · intro U
    rw [hcover]
end ChoicesStableUnderCountableMaps
end YangMills.Construction.ToriAtArbitraryCouplings
end
