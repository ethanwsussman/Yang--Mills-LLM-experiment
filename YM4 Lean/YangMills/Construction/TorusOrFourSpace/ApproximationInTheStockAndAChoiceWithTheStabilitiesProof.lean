import YangMills.Construction.TorusOrFourSpace.ApproximationInTheStockAndAChoiceWithTheStabilities
import YangMills.Construction.TorusOrFourSpace.CountableChoicesAndFamiliesOfDenseSets
import YangMills.Construction.TorusOrFourSpace.CountableClosedSaturatedChoicesAndTheirFamily
import YangMills.Construction.TorusOrFourSpace.CountableFamilyOfACountableChoice
import YangMills.Construction.TorusOrFourSpace.GroupOfAdicIsometriesAndItsActions
import YangMills.Construction.TorusOrFourSpace.SpacesC1OfTheStock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SupportAdapted
open Kind
open PeriodicLattice (SignedFrame)
variable (D : Params) (E : Kind)
theorem empty_mem_supportStock : (∅ : Set (E.Pt D)) ∈ supportStock D E :=
  ⟨0, Fin.elim0, fun i => i.elim0, by simp⟩
theorem union_mem_supportStock {Q Q' : Set (E.Pt D)} (h : Q ∈ supportStock D E)
    (h' : Q' ∈ supportStock D E) : Q ∪ Q' ∈ supportStock D E := by
  obtain ⟨r, b, hb, rfl⟩ := h
  obtain ⟨r', b', hb', rfl⟩ := h'
  refine ⟨r + r', Fin.append b b', ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hb j
    · simpa using hb' j
  · ext y
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · exact ⟨Fin.castAdd r' i, by simpa using hi⟩
      · exact ⟨Fin.natAdd r i, by simpa using hi⟩
    · rintro ⟨i, hi⟩
      revert hi
      refine Fin.addCases (fun j hj => ?_) (fun j hj => ?_) i
      · exact Or.inl ⟨j, by simpa using hj⟩
      · exact Or.inr ⟨j, by simpa using hj⟩
theorem exists_mem_supportStock_superset (p : ℕ) (S : Fin p → Set (E.Pt D))
    (hS : ∀ i, S i ∈ supportStock D E) :
    ∃ Q ∈ supportStock D E, ∀ i, S i ⊆ Q := by
  induction p with
  | zero => exact ⟨∅, empty_mem_supportStock D E, fun i => i.elim0⟩
  | succ p ih =>
    obtain ⟨Q, hQ, h⟩ := ih (fun i => S i.succ) (fun i => hS _)
    refine ⟨S 0 ∪ Q, union_mem_supportStock D E (hS 0) hQ, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Set.subset_union_left
    · exact (h j).trans Set.subset_union_right
theorem isSymmetricChoice_of_closed_of_saturated
    (hChoice : SaturatedChoices.Claim)
    (hGroup : AdicIsometryGroup.Claim)
    (hSame : Kind.CountableDenseFamilies.Statement)
    (C : supportStock D E → Set (E.Pt D → ℝ)) (hC : IsCountableDenseChoice D E C)
    (hcl : HasClosedValues D E C) (hsat : IsSaturated D E C) :
    IsSymmetricChoice D E C := by
  obtain ⟨-, -, -, ⟨-, hGrp, -⟩, ⟨hFrame, hTrans⟩, -, -, -, -, -, hActF, hActT, -⟩ := hGroup D E
  obtain ⟨-, -, hStab, -, -⟩ := hChoice D E
  obtain ⟨-, -, hIso, hCat⟩ := hStab C hC.1 hcl hsat
  rw [(hSame D E).2.1 C hC] at hIso hCat
  have frameEquiv : ∀ w : SignedFrame, ∃ r : E.Pt D ≃ E.Pt D, ⇑r = signedFrameMap D E w :=
    fun w => ⟨Equiv.ofBijective _ (hGrp.1 _ (hFrame w)).1, rfl⟩
  have transEquiv : ∀ a ∈ adicPointsQ D E, ∃ r : E.Pt D ≃ E.Pt D,
      ⇑r = AdicIsometryGroup.translateBy D E a :=
    fun a ha => ⟨Equiv.ofBijective _ (hGrp.1 _ (hTrans a ha)).1, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w _
    rw [isStableUnder_ofMap_iff]
    intro f hf
    obtain ⟨r, hr⟩ := frameEquiv w
    rw [← hActF w r hr f]
    exact hcl.1 r (hr ▸ hFrame w) f hf
  · intro a ha
    rw [isStableUnder_ofMap_iff]
    intro f hf
    obtain ⟨r, hr⟩ := transEquiv a ha
    rw [← hActT a ha r hr f]
    exact hcl.1 r (hr ▸ hTrans a ha) f hf
  · rintro l - hl g hg
    exact hcl.2 _ _ g (fun i => hl _ (List.get_mem l i)) hg
  · intro w _
    rw [isStableUnder_ofMap_iff]
    intro p hp
    obtain ⟨r, hr⟩ := frameEquiv w
    have e : frameActSized D E w p = ⟨p.1, pushTuple D E r p.2⟩ :=
      congrArg (Sigma.mk p.1) (funext fun i => (hActF w r hr (p.2 i)).symm)
    rw [e]
    exact hIso r (hr ▸ hFrame w) p hp
  · intro a ha
    rw [isStableUnder_ofMap_iff]
    intro p hp
    obtain ⟨r, hr⟩ := transEquiv a ha
    have e : shiftSized D E a p = ⟨p.1, pushTuple D E r p.2⟩ :=
      congrArg (Sigma.mk p.1) (funext fun i => (hActT a ha r hr (p.2 i)).symm)
    rw [e]
    exact hIso r (hr ▸ hTrans a ha) p hp
  · rintro l - hl z ⟨p, p', rfl, hd, rfl⟩
    exact hCat p (hl p (by simp)) p' (hl p' (by simp)) hd
theorem approxAndSymmetricChoice_holds
    (hChoice : SaturatedChoices.Claim)
    (hGroup : AdicIsometryGroup.Claim)
    (hSame : Kind.CountableDenseFamilies.Statement)
    (hSpaces : C1OfStock.Holds)
    (hFamily : CountableChoiceFamilyFacts) :
    ApproxAndSymmetricChoice := by
  intro D E
  have closedCase : ∀ C : supportStock D E → Set (E.Pt D → ℝ), IsCountableDenseChoice D E C →
      HasClosedValues D E C → IsSaturated D E C →
        IsSymmetricChoice D E C ∧
        (∀ Q : supportStock D E, C Q = choiceComponents D E C ∩ c1VanishingOutside D E Q) ∧
        tupleFamily D E C = disjointComponentTuples D E C := by
    intro C hC hcl hsat
    refine ⟨isSymmetricChoice_of_closed_of_saturated D E hChoice hGroup hSame C hC hcl hsat,
      hsat, ?_⟩
    rw [← (hSame D E).2.1 C hC, (hChoice D E).2.1 C hC.1 hsat]
    ext p
    simp only [SaturatedChoices.disjointComponentTuples,
      disjointComponentTuples, Set.mem_ofPred_eq]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    constructor
    · intro h i k hik
      exact Set.disjoint_iff_inter_eq_empty.2 (h i k hik)
    · intro h i k hik
      exact Set.disjoint_iff_inter_eq_empty.1 (h hik)
  refine ⟨?_, ?_, closedCase, ?_⟩
  · intro C hC f hf hfc W hW hfW
    refine ⟨?_, ?_⟩
    · obtain ⟨Q, hQ, h1, h2⟩ := (hFamily D E).2.2.1 _ W hfc hW hfW
      exact ⟨⟨Q, hQ⟩, h1, h2⟩
    · intro Q hfQ hQW
      have hmem : f ∈ c1VanishingOutside D E Q := (((hSpaces D E Q Q.2).1).1 f hf).2 hfQ
      refine ⟨hmem, ?_⟩
      have hex : ∀ k : ℕ+, ∃ g ∈ C Q,
          c1EuclidNorm D E (f - g) < ENNReal.ofReal (1 / ((k : ℕ) : ℝ)) := fun k =>
        (hC.1 Q).2 f hmem _ (by positivity)
      choose φ hφ hn using hex
      refine ⟨φ, hφ, hn, fun k => ⟨?_, hQW⟩⟩
      have hk := (hC.1 Q).1 (hφ k)
      exact (((hSpaces D E Q Q.2).1).1 (φ k) hk.1).1 hk
  · obtain ⟨C, hC, hcl, hsat⟩ := (hChoice D E).1
    exact ⟨C, hC, (closedCase C hC hcl hsat).1⟩
  · intro C hC
    have hcommon : ∀ (p : ℕ) (f : Fin p → E.Pt D → ℝ), (∀ i, f i ∈ choiceComponents D E C) →
        ∃ Q : supportStock D E, ∀ i, SupportedIn D E (f i) (Q : Set (E.Pt D)) := by
      intro p f hf
      have hf' : ∀ i, ∃ Q : supportStock D E, f i ∈ C Q := fun i => Set.mem_iUnion.1 (hf i)
      choose S hS using hf'
      obtain ⟨Q, hQ, h⟩ := exists_mem_supportStock_superset D E p
        (fun i => (S i : Set (E.Pt D))) (fun i => (S i).2)
      refine ⟨⟨Q, hQ⟩, fun i => ?_⟩
      have hk := (hC (S i)).1 (hS i)
      exact ((((hSpaces D E _ (S i).2).1).1 (f i) hk.1).1 hk).trans (h i)
    refine ⟨hcommon, ?_, ?_⟩
    · rintro h l hne hl g ⟨-, hg⟩
      exact h l hne hl hg
    · intro h l hne hl g hg
      obtain ⟨Q, hQ⟩ := hcommon l.length (fun i => l.get i) (fun i => hl _ (List.get_mem l i))
      refine h l hne hl ⟨⟨Q, fun f hf => ?_⟩, hg⟩
      obtain ⟨i, rfl⟩ := List.get_of_mem hf
      exact hQ i
end YangMills.Construction.PeriodicSpace.SupportAdapted
