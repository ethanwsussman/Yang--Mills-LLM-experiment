import YangMills.Construction.TorusOrFourSpace.ClassC1FunctionsProductsAndNeighbourhoods
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesInBallsAndTheirSeparation
import YangMills.Construction.TorusOrFourSpace.TheTwoKindsOfSequencesOfC1Forms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.C1FormSeqKinds
open Kind
private theorem multilinearOn_mono (D : Params) (E : Kind) {n : ℕ} {S T : Set (FnTuple D E n)}
    (hST : S ⊆ T) {F : T → ℝ} (hF : IsMultilinearOn D E T F) :
    IsMultilinearOn D E S fun g => F ⟨g.1, hST g.2⟩ := by
  intro k u v hEq
  have hRel := hF k ⟨u.1, hST u.2⟩ ⟨v.1, hST v.2⟩ hEq
  exact ⟨fun hAdd => hRel.1 (hST hAdd), fun c hSmul => hRel.2 c (hST hSmul)⟩
private theorem permSymmetricOn_mono (D : Params) (E : Kind) {n : ℕ} {S T : Set (FnTuple D E n)}
    (hST : S ⊆ T) {F : T → ℝ} (hF : IsPermSymmetricOn D E T F) :
    IsPermSymmetricOn D E S fun g => F ⟨g.1, hST g.2⟩ :=
  fun g σ hPerm => hF ⟨g.1, hST g.2⟩ σ (hST hPerm)
private theorem centredBall_mono (D : Params) (E : Kind) {a b : ℝ≥0∞} (ha : a < ∞)
    (hab : a < b) : centredBall D E a ⊆ centredBall D E b := by
  intro x hx
  unfold centredBall at hx ⊢
  rw [if_neg ha.ne] at hx
  by_cases hb : b = ∞
  · rw [if_pos hb]
    exact Set.mem_univ x
  · rw [if_neg hb]
    have hx' : quotDist D E x (origin D E) < a.toReal := hx
    show quotDist D E x (origin D E) < b.toReal
    exact hx'.trans ((ENNReal.toReal_lt_toReal ha.ne hb).2 hab)
private theorem eventuallyInDomains_of
    (hSep : SeparatedTupleFacts.SeparatedTupleBasics) (D : Params) (E : Kind) :
    EventuallyInDomains D E := by
  intro I ρ Ψ n hn g hg
  obtain ⟨a, ha, haTop, hga⟩ := (hSep D E n hn g hg).1
  obtain ⟨k, hk⟩ := Ψ.radii.eventually_gt a.toReal (ENNReal.toReal_pos ha.ne' haTop.ne)
  refine ⟨k, fun j hj => ?_⟩
  have hlt : a < ρ j := by
    have hPast := hk j.1 j.2 hj j.2
    rwa [ENNReal.ofReal_toReal haTop.ne] at hPast
  exact ⟨hg, fun i => (hga.2 i).trans (centredBall_mono D E haTop hlt)⟩
private theorem restrictionsAreC1FormSeq_of
    (hC1 : C1ProductsAndThickenings.Statement)
    (hVec : VectorClasses.Claim) (D : Params) (E : Kind)
    (C : BoundFamily) : RestrictionsAreC1FormSeq D E C := by
  intro I ρ Φ
  have hSub : ∀ (j : I.carrier) (n : ℕ), 1 ≤ n →
      sepC1TuplesInBall D E n (ρ j) ⊆
        sepLipTuplesWithin D E n (centredBall D E (ρ j)) :=
    fun _ n hn _ hg => ⟨(hC1 D E).1.2.2 n hn hg.1, hg.2⟩
  have hSub₂ : ∀ (j : I.carrier) (n : ℕ), 2 ≤ n →
      sepC1TuplesInBall D E n (ρ j) ⊆
        sepLipTuplesWithin D E n (centredBall D E (ρ j)) :=
    fun j n hn => hSub j n (by omega)
  refine ⟨hSub, fun A => ?_, ?_⟩
  · obtain ⟨⟨V', hV'⟩, ⟨V, hV⟩, -, -⟩ := (hVec D E).1 A
    refine ⟨V, V', hV, hV', SetLike.coe_subset_coe.1 ?_⟩
    rw [hV, hV']
    exact (hC1 D E).1.2.1 A
  · let Ψ : BoundedC1FormSeq D E I ρ C :=
      { radii := Φ.radii
        func := fun j n hn g => Φ.func j n hn ⟨g.1, hSub₂ j n hn g.2⟩
        multilinear := fun j n hn =>
          multilinearOn_mono D E (hSub₂ j n hn) (Φ.multilinear j n hn)
        symmetric := fun j n hn =>
          permSymmetricOn_mono D E (hSub₂ j n hn) (Φ.symmetric j n hn)
        threshold := Φ.threshold
        boundedFrom := fun n hn R hR j hj d hd g hg =>
          Φ.boundedFrom n hn R hR j hj d hd ⟨g.1, hSub₂ j n hn g.2⟩ hg }
    exact ⟨Ψ, fun _ _ _ _ => rfl, fun j n hn g => ⟨hSub₂ j n hn g.2, rfl⟩⟩
private def constFamilySeq (D : Params) (E : Kind) (C : BoundFamily) (I : Sequences.PNatIndexSet)
    (Φ : I.carrier → Hierarchy D E) (hΦ : ∀ j, Φ j ∈ boundedHierarchies D E C) :
    BoundedC1FormSeq D E I (fun _ => ∞) C where
  radii :=
    { pos := fun _ => ENNReal.zero_lt_top
      eventually_gt := fun _ _ => ⟨0, fun _ _ _ _ => ENNReal.ofReal_lt_top⟩
      eq_top_of_torus := fun _ _ => rfl }
  func j n hn g := (Φ j).func n hn ⟨g.1, g.2.1⟩
  multilinear j n hn :=
    multilinearOn_mono D E (fun _ hg => hg.1) ((Φ j).multilinear n hn)
  symmetric j n hn :=
    permSymmetricOn_mono D E (fun _ hg => hg.1) ((Φ j).symmetric n hn)
  threshold _ _ _ _ := 1
  boundedFrom n hn R hR j _ d hd g hg := hΦ j n hn d R hd hR ⟨g.1, g.2.1⟩ hg
private theorem familyIsC1FormSeq_of (D : Params) (E : Kind) (θ : RadiusRatio) (C : BoundFamily)
    (I : Sequences.PNatIndexSet) (Φ : I.carrier → Hierarchy D E)
    (hΦ : ∀ j, Φ j ∈ boundedHierarchies D E C) : FamilyIsC1FormSeq D E θ C I Φ := by
  refine ⟨constFamilySeq D E C I Φ hΦ, ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩,
    fun n hn R hR => ?_⟩
  unfold BoundedC1FormSeq.thresholdAtRadius
  split <;> rfl
theorem statement_holds (hSep : SeparatedTupleFacts.SeparatedTupleBasics)
    (hC1 : C1ProductsAndThickenings.Statement)
    (hVec : VectorClasses.Claim) : Statement :=
  fun D θ E C =>
    ⟨eventuallyInDomains_of hSep D E,
      restrictionsAreC1FormSeq_of hC1 hVec D E C,
      fun I Φ hΦ => familyIsC1FormSeq_of D E θ C I Φ hΦ,
      fun Φ hΦ => familyIsC1FormSeq_of D E θ C allPNat (fun _ => Φ) fun _ => hΦ⟩
end YangMills.Construction.PeriodicSpace.C1FormSeqKinds
end
