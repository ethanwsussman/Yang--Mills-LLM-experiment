import YangMills.Construction.BoundsOnEverySide.MapsAndTheirLimitsFreeOfAWindowProof
import YangMills.Construction.Torus.CentredFunctionalOfAFamilyOfConnectedFunctions
import YangMills.Construction.Torus.IsometriesPermutationsAndSubTuplesKeepTuplesSeparated
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.SetPartition
noncomputable section
namespace YangMills.Construction.AmbientPoints.CentredOfConnectedFamily
variable {s : Conventions.StandingParameters} {E : Ambient}
private def tupleAlong {n k : ℕ} (f : separatedTuples s E n) (a : Fin k → Fin n)
    (ha : Function.Injective a) : allSeparatedTuples s E :=
  ⟨⟨k, f.1 ∘ a⟩, comp_mem_separatedTuples f.2 ha⟩
private theorem card_eq_of_range_eq {n k k' : ℕ} {a : Fin k → Fin n} {b : Fin k' → Fin n}
    (ha : Function.Injective a) (hb : Function.Injective b) (h : Set.range a = Set.range b) :
    k = k' := by apply _root_.YangMills.SharedProofs.p12723 <;> assumption
private theorem tupleAlong_eq_of_strictMono {n k k' : ℕ} (f : separatedTuples s E n)
    {a : Fin k → Fin n} {b : Fin k' → Fin n} (ha : StrictMono a) (hb : StrictMono b)
    (h : Set.range a = Set.range b) :
    tupleAlong f a ha.injective = tupleAlong f b hb.injective := by
  have hk : k = k' := card_eq_of_range_eq ha.injective hb.injective h
  subst hk
  have hab : a = b := (ha.range_inj hb).1 h
  subst hab
  rfl
private theorem tupleAlong_symm {Ψ : allSeparatedTuples s E → ℝ}
    (hΨ : IsSymmetricTupleFunctional Ψ) {n k k' : ℕ} (hk : 1 ≤ k) (f : separatedTuples s E n)
    {a : Fin k → Fin n} {b : Fin k' → Fin n} (ha : Function.Injective a)
    (hb : Function.Injective b) (h : Set.range a = Set.range b) :
    Ψ (tupleAlong f a ha) = Ψ (tupleAlong f b hb) := by
  have hkk : k = k' := card_eq_of_range_eq ha hb h
  subst hkk
  have hex : ∀ i, ∃ t, b t = a i := fun i => by
    have : a i ∈ Set.range b := h ▸ Set.mem_range_self i
    exact this
  choose τ hτ using hex
  have hinj : Function.Injective τ := fun i j hij => ha (by rw [← hτ i, ← hτ j, hij])
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective τ (Finite.injective_iff_bijective.1 hinj)
  let g : separatedTuples s E k := ⟨f.1 ∘ b, comp_mem_separatedTuples f.2 hb⟩
  have hg := hΨ k hk g σ
  have hfg : (⟨permuteTuple σ g.1, permuteTuple_mem g.2 σ⟩ : separatedTuples s E k) =
      ⟨f.1 ∘ a, comp_mem_separatedTuples f.2 ha⟩ := by
    apply Subtype.ext
    funext i
    show f.1 (b (τ i)) = f.1 (a i)
    rw [hτ]
  rw [hfg] at hg
  exact hg
section Transport
variable (hT : SetPartition.Elementary.TransportUnderEquiv)
  {α β : Type} [DecidableEq α] [DecidableEq β] {A : Finset α} {A' : Finset β}
include hT in
private theorem exists_partitionTransport (σ : A ≃ A') (π : Partitions A) :
    ∃ π' : Partitions A', π'.parts = partitionImage σ π :=
  (hT α β A A' σ).1.mapsTo (Set.mem_univ π)
private def partitionTransport (σ : A ≃ A') (π : Partitions A) : Partitions A' :=
  Classical.choose (exists_partitionTransport hT σ π)
private theorem parts_partitionTransport (σ : A ≃ A') (π : Partitions A) :
    (partitionTransport hT σ π).parts = partitionImage σ π :=
  Classical.choose_spec (exists_partitionTransport hT σ π)
private theorem partitionTransport_bijective (σ : A ≃ A') :
    Function.Bijective (partitionTransport hT σ) := by
  constructor
  · intro π₁ π₂ h
    have h' : partitionImage σ π₁ = partitionImage σ π₂ := by
      rw [← parts_partitionTransport hT, ← parts_partitionTransport hT, h]
    exact (hT α β A A' σ).1.injOn (Set.mem_univ _) (Set.mem_univ _) h'
  · intro π'
    obtain ⟨π, -, hπ⟩ := (hT α β A A' σ).1.surjOn
      (show π'.parts ∈ partitionSets A' from ⟨π', rfl⟩)
    exact ⟨π, Finpartition.ext (by rw [parts_partitionTransport hT, hπ])⟩
private theorem prod_partitionTransport {M : Type*} [CommMonoid M] (σ : A ≃ A')
    (π : Partitions A) (g : Finset β → M) :
    ∏ I ∈ (partitionTransport hT σ π).parts, g I = ∏ J ∈ π.parts, g (blockImage σ J) := by
  rw [parts_partitionTransport hT]
  unfold partitionImage
  exact Finset.prod_image ((hT α β A A' σ).2 π).1.injOn
private theorem blockCount_partitionTransport (σ : A ≃ A') (π : Partitions A) :
    blockCount (partitionTransport hT σ π) = blockCount π := by
  unfold blockCount
  rw [parts_partitionTransport hT]
  exact ((hT α β A A' σ).2 π).2.2
end Transport
private theorem mem_singletonFree_iff_partitionTransport
    (hT : SetPartition.Elementary.TransportUnderEquiv) {q : ℕ}
    (σ : (Finset.univ : Finset (Fin q)) ≃ (Finset.univ : Finset (Fin q)))
    (π : PartitionsFin q) :
    π ∈ singletonFree q ↔ partitionTransport hT σ π ∈ singletonFree q := by
  simp only [singletonFree, Finset.mem_filter, Finset.mem_univ, true_and]
  have hc := ((hT (Fin q) (Fin q) Finset.univ Finset.univ σ).2 π).2.1
  constructor
  · intro h I hI
    rw [parts_partitionTransport hT] at hI
    obtain ⟨J, hJ, rfl⟩ := (mem_partitionImage σ π I).1 hI
    rw [hc J hJ]
    exact h J hJ
  · intro h J hJ
    have h' := h (blockImage σ J) (by
      rw [parts_partitionTransport hT]
      exact (mem_partitionImage σ π _).2 ⟨J, hJ, rfl⟩)
    rwa [hc J hJ] at h'
section Family
variable (S : ConnectedFamily s E)
private def evalTuple (X : allSeparatedTuples s E) : ℝ :=
  if h : 2 ≤ X.1.1 then S.fn X.1.1 h ⟨X.1.2, X.2⟩ else 0
private theorem blockFactor_eq_evalTuple {n : ℕ} (f : separatedTuples s E n)
    (J : Finset (Fin n)) :
    S.blockFactor f J = evalTuple S (toAllSeparated (restrictSeparated f J)) := rfl
private theorem evalTuple_of_two_le {n : ℕ} (hn : 2 ≤ n) (f : separatedTuples s E n) :
    evalTuple S (toAllSeparated f) = S.fn n hn f := dif_pos hn
private theorem evalTuple_of_not_two_le {n : ℕ} (hn : ¬ 2 ≤ n) (f : separatedTuples s E n) :
    evalTuple S (toAllSeparated f) = 0 := dif_neg hn
private theorem blockFactor_restrictSeparated {q : ℕ} (f : separatedTuples s E q)
    (J : Finset (Fin q)) (I : Finset (Fin J.card)) :
    S.blockFactor (restrictSeparated f J) I =
      S.blockFactor f (I.map (J.orderEmbOfFin rfl).toEmbedding) := by
  rw [blockFactor_eq_evalTuple, blockFactor_eq_evalTuple]
  congr 1
  have ha : StrictMono (J.orderEmbOfFin rfl ∘ I.orderEmbOfFin rfl) :=
    (J.orderEmbOfFin rfl).strictMono.comp (I.orderEmbOfFin rfl).strictMono
  refine tupleAlong_eq_of_strictMono f ha
    ((I.map (J.orderEmbOfFin rfl).toEmbedding).orderEmbOfFin rfl).strictMono ?_
  rw [Set.range_comp, Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin, Finset.coe_map]
  rfl
private theorem blockFactor_univ {n : ℕ} (hn : 2 ≤ n) (f : separatedTuples s E n) :
    S.blockFactor f Finset.univ = S.fn n hn f := by
  rw [blockFactor_eq_evalTuple, ← evalTuple_of_two_le S hn f]
  congr 1
  have h := tupleAlong_eq_of_strictMono f
    ((Finset.univ : Finset (Fin n)).orderEmbOfFin rfl).strictMono
    (strictMono_id : StrictMono (id : Fin n → Fin n))
    (by rw [Finset.range_orderEmbOfFin]; simp)
  exact h
section Multilinear
variable {q : ℕ} {A : Fin q → Set (Pt s E)}
  (hA : Pairwise fun i j => PositivelySeparated s E (A i) (A j))
private def tupleOfComponents (g : (i : Fin q) → c1Submodule (A i)) : separatedTuples s E q :=
  ⟨fun i => (g i : Pt s E → ℝ),
    mem_separatedTuples_of_forall_mem_c1 hA fun i => (g i).2⟩
private theorem blockFactor_update_of_notMem (g : (i : Fin q) → c1Submodule (A i)) {j : Fin q}
    (x : c1Submodule (A j)) {J : Finset (Fin q)} (hj : j ∉ J) :
    S.blockFactor (tupleOfComponents hA (Function.update g j x)) J =
      S.blockFactor (tupleOfComponents hA g) J := by
  have h : restrictSeparated (tupleOfComponents hA (Function.update g j x)) J =
      restrictSeparated (tupleOfComponents hA g) J := by
    apply Subtype.ext
    funext k
    have hk : J.orderEmbOfFin rfl k ≠ j := fun hkj => hj (hkj ▸ Finset.orderEmbOfFin_mem J rfl k)
    show ((Function.update g j x (J.orderEmbOfFin rfl k) : c1Submodule _) : Pt s E → ℝ) =
      (g (J.orderEmbOfFin rfl k) : Pt s E → ℝ)
    rw [Function.update_of_ne hk]
  rw [blockFactor_eq_evalTuple, blockFactor_eq_evalTuple, h]
private theorem blockFactor_isLinearMap (g : (i : Fin q) → c1Submodule (A i)) {j : Fin q}
    {J : Finset (Fin q)} (hJ : 2 ≤ J.card) (hj : j ∈ J) :
    IsLinearMap ℝ fun x : c1Submodule (A j) =>
      S.blockFactor (tupleOfComponents hA (Function.update g j x)) J := by
  have hr : j ∈ Set.range (J.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hj
  obtain ⟨k, rfl⟩ := hr
  have hinj := (J.orderEmbOfFin rfl).injective
  have hA' : Pairwise fun i l => PositivelySeparated s E (A (J.orderEmbOfFin rfl i))
      (A (J.orderEmbOfFin rfl l)) := fun i l hil => hA (hinj.ne hil)
  obtain ⟨L, hL⟩ := S.fn_multilinear J.card hJ (fun i => A (J.orderEmbOfFin rfl i)) hA'
  have key : ∀ x : c1Submodule (A (J.orderEmbOfFin rfl k)),
      S.blockFactor (tupleOfComponents hA (Function.update g (J.orderEmbOfFin rfl k) x)) J =
        L (Function.update (fun i => g (J.orderEmbOfFin rfl i)) k x) := by
    intro x
    rw [hL]
    unfold ConnectedFamily.blockFactor
    rw [dif_pos hJ]
    congr 1
    apply Subtype.ext
    funext i
    show ((Function.update g (J.orderEmbOfFin rfl k) x (J.orderEmbOfFin rfl i) :
        c1Submodule _) : Pt s E → ℝ) = _
    rw [Function.update_apply_of_injective g hinj k x i]
  constructor
  · intro x y
    simp only [key]
    exact L.map_update_add _ k x y
  · intro c x
    simp only [key]
    exact L.map_update_smul _ k c x
private theorem termProduct_isLinearMap {π : PartitionsFin q} (hπ : π ∈ singletonFree q)
    (g : (i : Fin q) → c1Submodule (A i)) (j : Fin q) :
    IsLinearMap ℝ fun x : c1Submodule (A j) =>
      ∏ J ∈ π.parts, S.blockFactor (tupleOfComponents hA (Function.update g j x)) J := by
  classical
  obtain ⟨J₀, hJ₀, hj⟩ := π.exists_mem (Finset.mem_univ j)
  have hlin := blockFactor_isLinearMap S hA g (two_le_card_of_mem_singletonFree hπ hJ₀) hj
  have hrest : ∀ x : c1Submodule (A j),
      ∏ J ∈ π.parts, S.blockFactor (tupleOfComponents hA (Function.update g j x)) J =
        S.blockFactor (tupleOfComponents hA (Function.update g j x)) J₀ *
          ∏ J ∈ π.parts.erase J₀, S.blockFactor (tupleOfComponents hA g) J := by
    intro x
    rw [← Finset.mul_prod_erase π.parts _ hJ₀]
    congr 1
    refine Finset.prod_congr rfl fun J hJ => ?_
    refine blockFactor_update_of_notMem S hA g x fun hjJ => ?_
    exact (Finset.mem_erase.1 hJ).1 (π.eq_of_mem_parts (Finset.mem_erase.1 hJ).2 hJ₀ hjJ hj)
  constructor
  · intro x y
    simp only [hrest]
    rw [hlin.map_add, add_mul]
  · intro c x
    simp only [hrest]
    rw [hlin.map_smul, smul_eq_mul, smul_eq_mul, mul_assoc]
end Multilinear
private theorem centred_ofLength_multilinear (q : ℕ) : IsTupleMultilinear (ofLength S.centred q) := by
  intro A hA
  refine ⟨MultilinearMap.mk'
    (fun g => ∑ π ∈ singletonFree q, ∏ J ∈ π.parts, S.blockFactor (tupleOfComponents hA g) J)
    ?_ ?_, fun g => rfl⟩
  · intro g j x y
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun π hπ => (termProduct_isLinearMap S hA hπ g j).map_add x y
  · intro g j c x
    rw [smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun π hπ => (termProduct_isLinearMap S hA hπ g j).map_smul c x
private theorem centred_nil : S.centred ⟨nilTuple s E, nilTuple_mem_allSeparatedTuples⟩ = 1 := by
  show ∑ π ∈ singletonFree 0, ∏ J ∈ π.parts, _ = (1 : ℝ)
  have hb : (⊥ : PartitionsFin 0).parts = ∅ := parts_eq_empty_of_empty _
  have hW : singletonFree 0 = {(⊥ : PartitionsFin 0)} := by
    ext π
    simp only [Finset.mem_singleton]
    refine ⟨fun _ => Finpartition.ext ?_, fun h => h ▸ mem_singletonFree_zero _⟩
    rw [hb]
    exact parts_eq_empty_of_empty π
  rw [hW, Finset.sum_singleton, hb]
  exact Finset.prod_empty
private theorem centred_of_length_one (f : separatedTuples s E 1) :
    S.centred (toAllSeparated f) = 0 := by
  show ∑ π ∈ singletonFree 1, ∏ J ∈ π.parts, _ = (0 : ℝ)
  rw [singletonFree_one, Finset.sum_empty]
private def orderEquivOfCard {q : ℕ} (J : Finset (Fin q)) :
    (Finset.univ : Finset (Fin J.card)) ≃ J :=
  (Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _).trans (J.orderIsoOfFin rfl).toEquiv
private theorem blockImage_orderEquivOfCard {q : ℕ} (J : Finset (Fin q))
    (I : Finset (Fin J.card)) :
    blockImage (orderEquivOfCard J) I = I.map (J.orderEmbOfFin rfl).toEmbedding := by
  ext y
  rw [mem_blockImage, Finset.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.1, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, Finset.mem_univ l⟩, hl, rfl⟩
private theorem blockProduct_cumulantNumbers {q : ℕ} (f : separatedTuples s E q)
    {J : Finset (Fin q)} (π : Partitions J) :
    Cumulants.blockProduct (S.cumulantNumbers f) π =
      ((∏ I ∈ π.parts, S.blockFactor f I : ℝ) : ℂ) := by
  rw [Complex.ofReal_prod, ← Finset.prod_coe_sort π.parts]
  rfl
private theorem partitionSum_cumulantNumbers (hT : SetPartition.Elementary.TransportUnderEquiv)
    {q : ℕ} (f : separatedTuples s E q) (J : Cumulants.NonemptyFinSubset q) :
    Cumulants.partitionSum (S.cumulantNumbers f) J =
      ((S.centred (toAllSeparated (restrictSeparated f J.1)) : ℝ) : ℂ) := by
  have hterm : ∀ π : PartitionsFin J.1.card,
      ∏ I ∈ (partitionTransport hT (orderEquivOfCard J.1) π).parts, S.blockFactor f I =
        ∏ I ∈ π.parts, S.blockFactor (restrictSeparated f J.1) I := by
    intro π
    rw [prod_partitionTransport hT]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [blockImage_orderEquivOfCard, blockFactor_restrictSeparated]
  have hsum := (partitionTransport_bijective hT (orderEquivOfCard J.1)).sum_comp
    (fun π' : Partitions J.1 => ((∏ I ∈ π'.parts, S.blockFactor f I : ℝ) : ℂ))
  unfold Cumulants.partitionSum
  simp only [blockProduct_cumulantNumbers]
  rw [← hsum]
  simp only [hterm]
  show _ = ((∑ π ∈ singletonFree J.1.card,
    ∏ I ∈ π.parts, S.blockFactor (restrictSeparated f J.1) I : ℝ) : ℂ)
  rw [Complex.ofReal_sum]
  refine (Finset.sum_subset (Finset.subset_univ _) fun π _ hπ => ?_).symm
  have hex : ∃ I ∈ π.parts, I.card = 1 := by
    by_contra hne
    exact hπ (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun I hI h1 => hne ⟨I, hI, h1⟩⟩)
  obtain ⟨I, hI, h1⟩ := hex
  have hz : S.blockFactor (restrictSeparated f J.1) I = 0 := by
    unfold ConnectedFamily.blockFactor
    rw [dif_neg (by omega)]
  rw [Finset.prod_eq_zero hI hz, Complex.ofReal_zero]
end Family
private def weightedPartitionSum (Ψ : allSeparatedTuples s E → ℝ) {q : ℕ}
    (P : Finset (PartitionsFin q)) (c : ℕ → ℝ) (f : separatedTuples s E q) : ℝ :=
  ∑ π ∈ P, c (blockCount π) *
    ∏ J ∈ π.parts, Ψ (toAllSeparated (restrictSeparated f J))
private def permAsFinsetEquiv {q : ℕ} (σ : Equiv.Perm (Fin q)) :
    (Finset.univ : Finset (Fin q)) ≃ (Finset.univ : Finset (Fin q)) :=
  σ.subtypeEquiv fun a => by simp
private theorem blockImage_permAsFinsetEquiv {q : ℕ} (σ : Equiv.Perm (Fin q))
    (J : Finset (Fin q)) :
    blockImage (permAsFinsetEquiv σ) J = J.map σ.toEmbedding := by
  ext y
  rw [mem_blockImage, Finset.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.1, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, Finset.mem_univ l⟩, hl, rfl⟩
private theorem one_le_card_of_mem_parts {q : ℕ} {π : PartitionsFin q} {J : Finset (Fin q)}
    (hJ : J ∈ π.parts) : 1 ≤ J.card :=
  Finset.card_pos.2 (π.nonempty_of_mem_parts hJ)
private theorem weightedPartitionSum_symmetric
    (hT : SetPartition.Elementary.TransportUnderEquiv)
    {Ψ : allSeparatedTuples s E → ℝ} (hΨ : IsSymmetricTupleFunctional Ψ) {q : ℕ}
    (P : Finset (PartitionsFin q))
    (hP : ∀ (σ : (Finset.univ : Finset (Fin q)) ≃ (Finset.univ : Finset (Fin q)))
      (π : PartitionsFin q), π ∈ P ↔ partitionTransport hT σ π ∈ P) (c : ℕ → ℝ) :
    IsTupleSymmetric (weightedPartitionSum Ψ P c) := by
  intro f σ
  unfold weightedPartitionSum
  refine Finset.sum_equiv
    (Equiv.ofBijective _ (partitionTransport_bijective hT (permAsFinsetEquiv σ))) (hP _)
    fun π _ => ?_
  simp only [Equiv.ofBijective_apply]
  rw [blockCount_partitionTransport hT, prod_partitionTransport hT]
  congr 1
  refine Finset.prod_congr rfl fun J hJ => ?_
  rw [blockImage_permAsFinsetEquiv]
  have hinj : Function.Injective (σ ∘ J.orderEmbOfFin rfl) :=
    σ.injective.comp (J.orderEmbOfFin rfl).injective
  refine (tupleAlong_symm hΨ (one_le_card_of_mem_parts hJ) f hinj
    ((J.map σ.toEmbedding).orderEmbOfFin rfl).injective ?_)
  rw [Set.range_comp, Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin, Finset.coe_map]
  rfl
private theorem weightedPartitionSum_invariant {r : Pt s E ≃ Pt s E}
    {Ψ : allSeparatedTuples s E → ℝ} (hΨ : IsInvariantTupleFunctional r Ψ) {q : ℕ}
    (hm : ∀ f : separatedTuples s E q, transportTuple r f.1 ∈ separatedTuples s E q)
    (P : Finset (PartitionsFin q)) (c : ℕ → ℝ) :
    IsTupleInvariant r (weightedPartitionSum Ψ P c) := by
  intro f
  refine ⟨hm f, ?_⟩
  unfold weightedPartitionSum
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun J hJ => ?_
  obtain ⟨_, h⟩ := hΨ J.card (one_le_card_of_mem_parts hJ) (restrictSeparated f J)
  exact h
theorem centredOfConnectedFamilyProperties_holds (hIso : SeparatedTupleStability.holds)
    (hPart : SetPartition.Elementary.BasicFacts)
    (hPoly : Cumulants.PartitionSubstitutionsInverse) : CentredOfConnectedFamilyProperties := by
  intro s E S
  have hT : SetPartition.Elementary.TransportUnderEquiv := hPart.2.2.1
  have hiso := (hIso s E).2.2.1
  have hmom : ∀ (q : ℕ) (_ : 1 ≤ q) (f : separatedTuples s E q)
      (J : Cumulants.NonemptyFinSubset q),
      Cumulants.expDerivFamily (S.cumulantNumbers f) J =
        ((S.centred (toAllSeparated (restrictSeparated f J.1)) : ℝ) : ℂ) :=
    fun q hq f J => (((hPoly q hq).1 _).2.2.1 J).2.trans (partitionSum_cumulantNumbers S hT f J)
  have hconn : ∀ (q : ℕ) (hq : 1 ≤ q) (f : separatedTuples s E q),
      ((connectedOf S.centred q f : ℝ) : ℂ) =
        S.cumulantNumbers f (Cumulants.univSubset hq) := by
    intro q hq f
    have hk := ((hPoly q hq).1 (S.cumulantNumbers f)).2.2.2 (Cumulants.univSubset hq)
    have hc := (hPoly q hq).2.2.2.2.2.2.2
      (Cumulants.expDerivFamily (S.cumulantNumbers f))
    refine Eq.trans ?_ hk.symm
    rw [hc]
    unfold connectedOf
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    have hprod : Cumulants.blockProduct
        (Cumulants.expDerivFamily (S.cumulantNumbers f)) π =
        ((∏ J ∈ π.parts,
          S.centred (toAllSeparated (restrictSeparated f J)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod, ← Finset.prod_coe_sort π.parts]
      unfold Cumulants.blockProduct
      exact Finset.prod_congr rfl fun B _ => hmom q hq f (Cumulants.blockSubset π B)
    rw [hprod]
    push_cast
    rfl
  have hfirst : ∀ f : separatedTuples s E 1, connectedOf S.centred 1 f = 0 := by
    intro f
    have h := hconn 1 le_rfl f
    have h0 : S.cumulantNumbers f (Cumulants.univSubset le_rfl) = 0 := by
      show ((S.blockFactor f Finset.univ : ℝ) : ℂ) = 0
      unfold ConnectedFamily.blockFactor
      rw [dif_neg (by simp), Complex.ofReal_zero]
    rw [h0] at h
    exact_mod_cast h
  have hrest : ∀ (n : ℕ) (hn : 2 ≤ n) (f : separatedTuples s E n),
      connectedOf S.centred n f = S.fn n hn f := by
    intro n hn f
    have h := hconn n (by omega) f
    have h2 : S.cumulantNumbers f (Cumulants.univSubset (by omega)) =
        ((S.fn n hn f : ℝ) : ℂ) := by
      show ((S.blockFactor f Finset.univ : ℝ) : ℂ) = _
      rw [blockFactor_univ S hn f]
    rw [h2] at h
    exact_mod_cast h
  have hσ : ∀ n, ofLength S.centred n =
      weightedPartitionSum (evalTuple S) (singletonFree n) fun _ => 1 := fun n =>
    funext fun f => by
      simp only [weightedPartitionSum, one_mul]
      rfl
  have hS : ∀ (n : ℕ) (hn : 2 ≤ n), S.fn n hn =
      weightedPartitionSum S.centred Finset.univ
        fun k => (-1 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) := fun n hn =>
    funext fun f => (hrest n hn f).symm
  refine ⟨centred_nil S, centred_of_length_one S, fun q _ => centred_ofLength_multilinear S q,
    ⟨centred_nil S, fun n _ => centred_ofLength_multilinear S n⟩,
    fun q hq f => ⟨hmom q hq f, hconn q hq f⟩, hfirst, hrest, ⟨?_, ?_⟩, ?_⟩
  · intro h n hn
    rw [hS n hn]
    exact weightedPartitionSum_symmetric hT h _ (fun _ _ => by simp) _
  · intro h n _
    rw [hσ n]
    refine weightedPartitionSum_symmetric hT ?_ _ (mem_singletonFree_iff_partitionTransport hT) _
    intro k _ g σ
    by_cases h2 : 2 ≤ k
    · show evalTuple S (toAllSeparated _) = evalTuple S (toAllSeparated g)
      rw [evalTuple_of_two_le S h2, evalTuple_of_two_le S h2]
      exact h k h2 g σ
    · show evalTuple S (toAllSeparated _) = evalTuple S (toAllSeparated g)
      rw [evalTuple_of_not_two_le S h2, evalTuple_of_not_two_le S h2]
  · intro r hr
    have hm : ∀ (n : ℕ), 1 ≤ n → ∀ f : separatedTuples s E n,
        transportTuple r f.1 ∈ separatedTuples s E n :=
      fun n hn f => ((hiso n hn f.1 f.2).2.2 r hr).1
    constructor
    · intro h n hn
      rw [hS n hn]
      exact weightedPartitionSum_invariant h (hm n (by omega)) _ _
    · intro h n hn
      rw [hσ n]
      refine weightedPartitionSum_invariant ?_ (hm n hn) _ _
      intro k hk g
      refine ⟨hm k hk g, ?_⟩
      by_cases h2 : 2 ≤ k
      · obtain ⟨_, e⟩ := h k h2 g
        show evalTuple S (toAllSeparated _) = evalTuple S (toAllSeparated g)
        rw [evalTuple_of_two_le S h2, evalTuple_of_two_le S h2]
        exact e
      · show evalTuple S (toAllSeparated _) = evalTuple S (toAllSeparated g)
        rw [evalTuple_of_not_two_le S h2, evalTuple_of_not_two_le S h2]
end YangMills.Construction.AmbientPoints.CentredOfConnectedFamily
