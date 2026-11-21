import YangMills.Construction.BoundsOnEverySide.MapsAndTheirLimitsFreeOfAWindowProof
import YangMills.Construction.Torus.CentredFunctionalOfAFamilyOfConnectedFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusOrFourSpace
open ReflectionPositivity.AxisMirror (Ambient)
open AmbientPoints SetPartition
variable {s : Conventions.StandingParameters} {E : Ambient}
section MapPartitions
variable (hT : SetPartition.Elementary.TransportUnderEquiv)
  {α β : Type} [DecidableEq α] [DecidableEq β] {A : Finset α} {A' : Finset β}
include hT in
private theorem exists_partitionImage_eq (e : A ≃ A') (P : Partitions A) :
    ∃ P' : Partitions A', P'.parts = partitionImage e P :=
  (hT α β A A' e).1.mapsTo (Set.mem_univ P)
private def mapPartition (e : A ≃ A') (P : Partitions A) : Partitions A' :=
  Classical.choose (exists_partitionImage_eq hT e P)
end MapPartitions
private def finCardEquiv {q : ℕ} (J : Finset (Fin q)) : (Finset.univ : Finset (Fin J.card)) ≃ J :=
  (Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _).trans (J.orderIsoOfFin rfl).toEquiv
private theorem blockImage_finCardEquiv {q : ℕ} (J : Finset (Fin q)) (I : Finset (Fin J.card)) :
    blockImage (finCardEquiv J) I = I.map (J.orderEmbOfFin rfl).toEmbedding := by
  ext y
  rw [mem_blockImage, Finset.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.1, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, Finset.mem_univ l⟩, hl, rfl⟩
private def subTupleAlong {n k : ℕ} (f : separatedTuples s E n) (a : Fin k → Fin n)
    (ha : Function.Injective a) : allSeparatedTuples s E :=
  ⟨⟨k, f.1 ∘ a⟩, comp_mem_separatedTuples f.2 ha⟩
private theorem card_eq_of_range_eq {n k k' : ℕ} {a : Fin k → Fin n} {b : Fin k' → Fin n}
    (ha : Function.Injective a) (hb : Function.Injective b) (h : Set.range a = Set.range b) :
    k = k' := by apply _root_.YangMills.SharedProofs.p12723 <;> assumption
private theorem subTupleAlong_eq_of_strictMono {n k k' : ℕ} (f : separatedTuples s E n)
    {a : Fin k → Fin n} {b : Fin k' → Fin n} (ha : StrictMono a) (hb : StrictMono b)
    (h : Set.range a = Set.range b) :
    subTupleAlong f a ha.injective = subTupleAlong f b hb.injective := by
  have hk : k = k' := card_eq_of_range_eq ha.injective hb.injective h
  subst hk
  have hab : a = b := (ha.range_inj hb).1 h
  subst hab
  rfl
section BlockValues
variable (σ : allSeparatedTuples s E → ℝ)
private def blockValue {n : ℕ} (f : separatedTuples s E n) (J : Finset (Fin n)) : ℝ :=
  σ (toAllSeparated (restrictSeparated f J))
private theorem toAllSeparated_restrict_univ {n : ℕ} (f : separatedTuples s E n) :
    toAllSeparated (restrictSeparated f Finset.univ) = toAllSeparated f :=
  subTupleAlong_eq_of_strictMono f ((Finset.univ : Finset (Fin n)).orderEmbOfFin rfl).strictMono
    (strictMono_id : StrictMono (id : Fin n → Fin n))
    (by rw [Finset.range_orderEmbOfFin]; simp)
private def momentFamily {q : ℕ} (f : separatedTuples s E q) : Cumulants.SubsetFamily q :=
  fun J => (blockValue σ f J.1 : ℂ)
private theorem blockProduct_momentFamily {q : ℕ} (f : separatedTuples s E q)
    {J : Finset (Fin q)} (P : Partitions J) :
    Cumulants.blockProduct (momentFamily σ f) P =
      ((∏ I ∈ P.parts, blockValue σ f I : ℝ) : ℂ) := by
  rw [Complex.ofReal_prod, ← Finset.prod_coe_sort P.parts]
  rfl
private theorem moebiusPartitionSum_momentFamily
    (hT : SetPartition.Elementary.TransportUnderEquiv) {q : ℕ}
    (f : separatedTuples s E q) (J : Cumulants.NonemptyFinSubset q) :
    Cumulants.moebiusPartitionSum (momentFamily σ f) J =
      ((connectedOf σ J.1.card (restrictSeparated f J.1) : ℝ) : ℂ) := by apply _root_.YangMills.DeltaSharedProofs.p501175 <;> assumption
private theorem connectedOf_eq_zero_of_eq_one
    (h0 : ∀ f : separatedTuples s E 1, σ (toAllSeparated f) = 0) {n : ℕ} (hn : n = 1)
    (f : separatedTuples s E n) : connectedOf σ n f = 0 := by
  have hz : ∀ {k : ℕ}, k = 1 → ∀ x : separatedTuples s E k,
      σ (toAllSeparated x) = 0 := by
    rintro k rfl x
    exact h0 x
  subst hn
  unfold connectedOf
  refine Finset.sum_eq_zero fun P _ => ?_
  obtain ⟨J, hJ, -⟩ := P.exists_mem (Finset.mem_univ (0 : Fin 1))
  have hc : J.card = 1 := by
    have h1 : 0 < J.card := Finset.card_pos.2 (P.nonempty_of_mem_parts hJ)
    have h2 : J.card ≤ 1 := by simpa using Finset.card_le_univ J
    omega
  rw [Finset.prod_eq_zero hJ (hz hc _), mul_zero]
end BlockValues
section Multilinear
variable {σ : allSeparatedTuples s E → ℝ} {q : ℕ} {A : Fin q → Set (Pt s E)}
  (hA : Pairwise fun i j => PositivelySeparated s E (A i) (A j))
private def c1Tuple (g : (i : Fin q) → c1Submodule (A i)) : separatedTuples s E q :=
  ⟨fun i => (g i : Pt s E → ℝ),
    mem_separatedTuples_of_forall_mem_c1 hA fun i => (g i).2⟩
private theorem blockValue_update_of_notMem (g : (i : Fin q) → c1Submodule (A i)) {j : Fin q}
    (x : c1Submodule (A j)) {J : Finset (Fin q)} (hj : j ∉ J) :
    blockValue σ (c1Tuple hA (Function.update g j x)) J = blockValue σ (c1Tuple hA g) J := by
  have h : restrictSeparated (c1Tuple hA (Function.update g j x)) J =
      restrictSeparated (c1Tuple hA g) J := by
    apply Subtype.ext
    funext k
    have hk : J.orderEmbOfFin rfl k ≠ j := fun hkj => hj (hkj ▸ Finset.orderEmbOfFin_mem J rfl k)
    show ((Function.update g j x (J.orderEmbOfFin rfl k) : c1Submodule _) : Pt s E → ℝ) =
      (g (J.orderEmbOfFin rfl k) : Pt s E → ℝ)
    rw [Function.update_of_ne hk]
  unfold blockValue
  rw [h]
include hA in
private theorem blockValue_isLinearMap (hσ : IsTupleFunctional σ)
    (g : (i : Fin q) → c1Submodule (A i)) {j : Fin q} {J : Finset (Fin q)} (hj : j ∈ J) :
    IsLinearMap ℝ fun x : c1Submodule (A j) =>
      blockValue σ (c1Tuple hA (Function.update g j x)) J := by
  have hJ : 1 ≤ J.card := Finset.card_pos.2 ⟨j, hj⟩
  have hr : j ∈ Set.range (J.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hj
  obtain ⟨k, rfl⟩ := hr
  have hinj := (J.orderEmbOfFin rfl).injective
  have hA' : Pairwise fun i l => PositivelySeparated s E (A (J.orderEmbOfFin rfl i))
      (A (J.orderEmbOfFin rfl l)) := fun i l hil => hA (hinj.ne hil)
  obtain ⟨L, hL⟩ := hσ.2 J.card hJ (fun i => A (J.orderEmbOfFin rfl i)) hA'
  have key : ∀ x : c1Submodule (A (J.orderEmbOfFin rfl k)),
      blockValue σ (c1Tuple hA (Function.update g (J.orderEmbOfFin rfl k) x)) J =
        L (Function.update (fun i => g (J.orderEmbOfFin rfl i)) k x) := by
    intro x
    rw [hL]
    refine congrArg (fun h => σ (toAllSeparated h)) (Subtype.ext ?_)
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
private theorem term_isLinearMap (hσ : IsTupleFunctional σ) (c : ℝ)
    (P : PartitionsFin q) (g : (i : Fin q) → c1Submodule (A i)) (j : Fin q) :
    IsLinearMap ℝ fun x : c1Submodule (A j) =>
      c * ∏ J ∈ P.parts, blockValue σ (c1Tuple hA (Function.update g j x)) J := by
  classical
  obtain ⟨J₀, hJ₀, hj⟩ := P.exists_mem (Finset.mem_univ j)
  have hlin := blockValue_isLinearMap hA hσ g hj
  have hrest : ∀ x : c1Submodule (A j),
      ∏ J ∈ P.parts, blockValue σ (c1Tuple hA (Function.update g j x)) J =
        blockValue σ (c1Tuple hA (Function.update g j x)) J₀ *
          ∏ J ∈ P.parts.erase J₀, blockValue σ (c1Tuple hA g) J := by
    intro x
    rw [← Finset.mul_prod_erase P.parts _ hJ₀]
    congr 1
    refine Finset.prod_congr rfl fun J hJ => ?_
    refine blockValue_update_of_notMem hA g x fun hjJ => ?_
    exact (Finset.mem_erase.1 hJ).1 (P.eq_of_mem_parts (Finset.mem_erase.1 hJ).2 hJ₀ hjJ hj)
  constructor
  · intro x y
    simp only [hrest]
    rw [hlin.map_add]
    ring
  · intro c' x
    simp only [hrest]
    rw [hlin.map_smul, smul_eq_mul, smul_eq_mul]
    ring
end Multilinear
private theorem connectedOf_isTupleMultilinear {σ : allSeparatedTuples s E → ℝ}
    (hσ : IsTupleFunctional σ) (n : ℕ) :
    IsTupleMultilinear (connectedOf σ n) := by
  intro A hA
  refine ⟨MultilinearMap.mk'
    (fun g => ∑ P : PartitionsFin n,
      (-1 : ℝ) ^ (blockCount P - 1) * ((blockCount P - 1).factorial : ℝ) *
        ∏ J ∈ P.parts, blockValue σ (c1Tuple hA g) J)
    ?_ ?_, fun g => rfl⟩
  · intro g j x y
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun P _ => (term_isLinearMap hA hσ _ P g j).map_add x y
  · intro g j c x
    rw [smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun P _ => (term_isLinearMap hA hσ _ P g j).map_smul c x
private theorem moebiusPartitionSum_eq_cumulantNumbers
    (hT : SetPartition.Elementary.TransportUnderEquiv)
    {σ : allSeparatedTuples s E → ℝ}
    (hml : ∀ n : ℕ, 1 ≤ n → IsTupleMultilinear (connectedOf σ n))
    (h0 : ∀ f : separatedTuples s E 1, σ (toAllSeparated f) = 0) {q : ℕ}
    (f : separatedTuples s E q) :
    Cumulants.moebiusPartitionSum (momentFamily σ f) =
      (connectedFamilyOf σ hml).cumulantNumbers f := by
  funext J
  rw [moebiusPartitionSum_momentFamily σ hT]
  show _ = (((connectedFamilyOf σ hml).blockFactor f J.1 : ℝ) : ℂ)
  unfold AmbientPoints.ConnectedFamily.blockFactor
  by_cases h : 2 ≤ J.1.card
  · rw [dif_pos h]
    rfl
  · have h1 : J.1.card = 1 := by
      have := Finset.card_pos.2 J.2
      omega
    rw [dif_neg h, connectedOf_eq_zero_of_eq_one σ h0 h1]
theorem connectedFamilyCentredInverse_holds (hFam : CentredOfConnectedFamilyProperties)
    (hPart : SetPartition.Elementary.BasicFacts)
    (hPoly : Cumulants.PartitionSubstitutionsInverse) : ConnectedFamilyCentredInverse := by
  intro s E σ hσ
  have hT : SetPartition.Elementary.TransportUnderEquiv := hPart.2.2.1
  have hml : ∀ n : ℕ, 1 ≤ n → IsTupleMultilinear (connectedOf σ n) :=
    fun n _ => connectedOf_isTupleMultilinear hσ n
  refine ⟨hml, fun h0 => ?_⟩
  have hS := hFam s E (connectedFamilyOf σ hml)
  funext X
  obtain ⟨⟨n, f⟩, hf⟩ := X
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hX : (⟨⟨0, f⟩, hf⟩ : allSeparatedTuples s E) =
        ⟨nilTuple s E, nilTuple_mem_allSeparatedTuples⟩ := by
      apply Subtype.ext
      show (⟨0, f⟩ : FunctionTuple s E) = ⟨0, fun i => i.elim0⟩
      congr 1
      funext i
      exact i.elim0
    rw [hX, hS.1, hσ.1]
  · let g : separatedTuples s E n := ⟨f, hf⟩
    have hk := moebiusPartitionSum_eq_cumulantNumbers hT hml h0 g
    have hback : Cumulants.partitionSum
        ((connectedFamilyOf σ hml).cumulantNumbers g) = momentFamily σ g := by
      rw [← hk]
      exact (hPoly n hn).2.2.2.2.2.1 _
    have hm := (hS.2.2.2.2.1 n hn g).1 (Cumulants.univSubset hn)
    rw [(((hPoly n hn).1 _).2.2.1 (Cumulants.univSubset hn)).2, hback] at hm
    have hm' : blockValue σ g Finset.univ =
        (connectedFamilyOf σ hml).centred
          (toAllSeparated (restrictSeparated g Finset.univ)) :=
      Complex.ofReal_injective hm
    unfold blockValue at hm'
    rw [toAllSeparated_restrict_univ] at hm'
    exact hm'.symm
end YangMills.Construction.TorusOrFourSpace
