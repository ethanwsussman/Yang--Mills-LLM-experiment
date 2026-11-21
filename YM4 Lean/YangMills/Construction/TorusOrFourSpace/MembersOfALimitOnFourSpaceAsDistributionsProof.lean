import YangMills.Construction.TorusOrFourSpace.FunctionalBoundedInTheSharpNormIsADistribution
import YangMills.Construction.TorusOrFourSpace.MapsOfFourKindsOnTuplesTestFunctionsAndDistributions
import YangMills.Construction.TorusOrFourSpace.MembersOfAHierarchyAsDistributions
import YangMills.Construction.TorusOrFourSpace.MembersOfALimitOnFourSpaceAsDistributions
import YangMills.Construction.TorusOrFourSpace.SmallFactsOnLiftsProductsAndDistributions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.EuclideanLimitDistributions
theorem exists_index_ge_of_int (I : Sequences.PNatIndexSet) (a b : ℤ) :
    ∃ k : I.carrier, a ≤ (((k.1 : ℕ+) : ℕ) : ℤ) ∧ b ≤ (((k.1 : ℕ+) : ℕ) : ℤ) := by
  obtain ⟨k, hk, hgt⟩ := I.infinite.exists_gt (⟨(max a b).toNat + 1, Nat.succ_pos _⟩ : ℕ+)
  have hgt' : (max a b).toNat + 1 < ((k : ℕ+) : ℕ) := hgt
  refine ⟨⟨k, hk⟩, ?_, ?_⟩
  · have h₁ := le_max_left a b
    have h₂ := Int.self_le_toNat (max a b)
    show a ≤ (((k : ℕ+) : ℕ) : ℤ)
    omega
  · have h₁ := le_max_right a b
    have h₂ := Int.self_le_toNat (max a b)
    show b ≤ (((k : ℕ+) : ℕ) : ℤ)
    omega
theorem limit_mem_boundedHierarchies {P : Params} {B : BoundFamily} {I : Sequences.PNatIndexSet}
    {ρ : I.carrier → ℝ≥0∞} (S : BoundedPartialHierarchySeq P Kind.euclidean I ρ B)
    {Φ : Hierarchy P Kind.euclidean}
    (hlim : S.toPartialHierarchySeq.ConvergesOnSepTuples Φ) :
    Φ ∈ boundedHierarchies P Kind.euclidean B := by
  intro m hm d R hd hR f hf
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨k₁, hk₁⟩ := hlim m hm f (ε : ℝ) hε'
  obtain ⟨k, ha, hb⟩ := exists_index_ge_of_int I k₁ (S.threshold m hm R hR)
  obtain ⟨hfk, hle⟩ := hk₁ k ha
  have hbound := S.boundedFrom m hm R hR k hb d hd ⟨f.1, hfk⟩ hf
  have habs : |Φ.func m hm f| ≤
      |S.func k m hm ⟨f.1, hfk⟩| + (ε : ℝ) := by
    have h₁ := abs_sub_abs_le_abs_sub (Φ.func m hm f) (S.func k m hm ⟨f.1, hfk⟩)
    rw [abs_sub_comm] at h₁
    linarith
  calc ENNReal.ofReal |Φ.func m hm f|
      ≤ ENNReal.ofReal (|S.func k m hm ⟨f.1, hfk⟩| + (ε : ℝ)) :=
        ENNReal.ofReal_le_ofReal habs
    _ = ENNReal.ofReal |S.func k m hm ⟨f.1, hfk⟩| + (ε : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (abs_nonneg _) (NNReal.coe_nonneg ε), ENNReal.ofReal_coe_nnreal]
    _ ≤ _ := by gcongr
theorem limitMembersAreDistributions_holds (hMembers : HierarchyMembersAsDistributions.Statement)
    (hSharp : Tuple.SharpBoundedIsDistrib.Statement)
    (hMaps : ExtendedTupleMapFacts.MainProperties)
    (hFacts : LiftsProductsDistributions.Statement) : LimitMembersAreDistributions := by
  intro P B I ρ S Φ hlim m hm
  have hbdd := limit_mem_boundedHierarchies S hlim
  obtain ⟨-, ⟨T₀, hT₀, -⟩, hD, -⟩ := hMembers P Kind.euclidean B Φ hbdd m hm
  obtain ⟨⟨-, hord, hval, huniq, -⟩, -⟩ := hD T₀ hT₀
  have heq : ∀ T, HasMemberValues Φ hm T → T = T₀ := fun T hT => huniq T hT.1 hT.2
  refine ⟨⟨T₀, ⟨hT₀.1, hval⟩, heq⟩, fun T hT => ?_⟩
  obtain rfl := heq T hT
  obtain ⟨-, hopen, -, ⟨T₁, hT₁, -⟩, hall⟩ :=
    hSharp P Kind.euclidean m hm (Φ.func (m : ℕ) hm) (B.val (m : ℕ))
      (Φ.multilinear (m : ℕ) hm) (fun d R hd hR => B.nonneg (m : ℕ) hm d R hd hR)
      (fun d R hd hR f hf => hbdd (m : ℕ) hm d R hd hR f hf)
  obtain ⟨-, hv₁, -, hinv⟩ := hall T₁ hT₁
  have h₁₀ : T₁ = T := huniq T₁ hT₁.1 fun f hf hs => by
    obtain ⟨hF, hv⟩ := hv₁ f hf hs
    exact ⟨hf, hF, hv⟩
  subst h₁₀
  refine ⟨hord, fun U h hU => ?_, fun σ => ?_, fun s hs hkeep => ?_⟩
  · exact ((hFacts P Kind.euclidean).2.2.2.2.2.1 m U _ hU hopen h T₁ hT.1).2.2 _ hord
  · have hψ : (fun (x : Kind.euclidean.Tuple P m) i => x (σ i)) =
        (ExtendedTupleMap.ofTupleMap (.permute σ⁻¹) :
          ExtendedTupleMap P Kind.euclidean m).actPts := by
      rfl
    rw [hψ]
    refine hinv _ fun f h => ?_
    exact Φ.symmetric (m : ℕ) hm f σ h
  · have hbij := ((hMaps P Kind.euclidean m hm).2 (.ofIsometry s hs)).1.1
    have hinj : Function.Injective s := fun y y' e =>
      congrFun (hbij.1 (a₁ := fun _ => y) (a₂ := fun _ => y') (funext fun _ => e)) ⟨0, m.pos⟩
    refine hinv (.ofIsometry s hs) fun f h => ?_
    have hback : compEach (compEach f.1 (isometryInverse P Kind.euclidean s)) s = f.1 := by
      funext i y
      exact congrArg (f.1 i) (Function.leftInverse_invFun hinj y)
    have h' : compEach (compEach f.1 (isometryInverse P Kind.euclidean s)) s ∈
        sepC1Tuples P Kind.euclidean (m : ℕ) := by
      rw [hback]
      exact f.2
    refine (hkeep ⟨_, h⟩ h').symm.trans ?_
    exact congrArg _ (Subtype.ext hback)
end YangMills.Construction.PeriodicSpace.Kind.EuclideanLimitDistributions
