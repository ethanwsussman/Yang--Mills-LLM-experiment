import YangMills.Construction.BoundsOnEverySide.MapsAndTheirLimitsFreeOfAWindowProof
import YangMills.Construction.ReflectionPositivity.TwoFunctionalsOnSeparatedTuples
import YangMills.Construction.ToriAtArbitraryCouplings.CentredMomentsOfALimitOfABoundedSequence
import YangMills.Construction.ToriAtArbitraryCouplings.ConnectedFunctionsAsCumulantsAndCentredMomentsAtOneCutoff
import YangMills.Construction.ToriAtArbitraryCouplings.NormsCuttingAndNeighbourhoods
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
open Filter SetPartition
open scoped Topology
namespace ToriAtArbitraryCouplings.CenteredMomentsOfLimit
open AmbientPoints (restrictTuple)
section PartitionMaps
variable (hT : SetPartition.Elementary.TransportUnderEquiv)
  {α β : Type} [DecidableEq α] [DecidableEq β] {A : Finset α} {A' : Finset β}
include hT in
private theorem exists_partition_map (e : A ≃ A') (π : Partitions A) :
    ∃ π' : Partitions A', π'.parts = partitionImage e π :=
  (hT α β A A' e).1.mapsTo (Set.mem_univ π)
private def partitionMap (e : A ≃ A') (π : Partitions A) : Partitions A' :=
  Classical.choose (exists_partition_map hT e π)
private theorem partitionMap_parts (e : A ≃ A') (π : Partitions A) :
    (partitionMap hT e π).parts = partitionImage e π :=
  Classical.choose_spec (exists_partition_map hT e π)
private theorem partitionMap_bijective (e : A ≃ A') : Function.Bijective (partitionMap hT e) := by
  constructor
  · intro π₁ π₂ h
    have h' : partitionImage e π₁ = partitionImage e π₂ := by
      rw [← partitionMap_parts hT, ← partitionMap_parts hT, h]
    exact (hT α β A A' e).1.injOn (Set.mem_univ _) (Set.mem_univ _) h'
  · intro π'
    obtain ⟨π, -, hπ⟩ := (hT α β A A' e).1.surjOn
      (show π'.parts ∈ partitionSets A' from ⟨π', rfl⟩)
    exact ⟨π, Finpartition.ext (by rw [partitionMap_parts hT, hπ])⟩
private theorem prod_partitionMap {M : Type*} [CommMonoid M] (e : A ≃ A') (π : Partitions A)
    (g : Finset β → M) :
    ∏ I ∈ (partitionMap hT e π).parts, g I = ∏ B ∈ π.parts, g (blockImage e B) := by
  rw [partitionMap_parts hT]
  unfold partitionImage
  exact Finset.prod_image ((hT α β A A' e).2 π).1.injOn
end PartitionMaps
section TupleEvaluation
variable {α : Type*} (v : (k : ℕ) → (Fin k → α) → ℝ)
private theorem card_eq_of_range_eq {n k k' : ℕ} {a : Fin k → Fin n} {b : Fin k' → Fin n}
    (ha : Function.Injective a) (hb : Function.Injective b) (h : Set.range a = Set.range b) :
    k = k' := by apply _root_.YangMills.SharedProofs.p12723 <;> assumption
private theorem eval_eq_of_strictMono {n k k' : ℕ} (f : Fin n → α) {a : Fin k → Fin n}
    {b : Fin k' → Fin n} (ha : StrictMono a) (hb : StrictMono b)
    (h : Set.range a = Set.range b) : v k (f ∘ a) = v k' (f ∘ b) := by
  have hk : k = k' := card_eq_of_range_eq ha.injective hb.injective h
  subst hk
  have hab : a = b := (ha.range_inj hb).1 h
  subst hab
  rfl
private theorem eval_eq_of_injective
    (hv : ∀ (k : ℕ) (g : Fin k → α) (σ : Equiv.Perm (Fin k)), v k (g ∘ σ) = v k g)
    {n k k' : ℕ} (f : Fin n → α) {a : Fin k → Fin n} {b : Fin k' → Fin n}
    (ha : Function.Injective a) (hb : Function.Injective b) (h : Set.range a = Set.range b) :
    v k (f ∘ a) = v k' (f ∘ b) := by
  have hkk : k = k' := card_eq_of_range_eq ha hb h
  subst hkk
  have hex : ∀ i, ∃ t, b t = a i := fun i => by
    have : a i ∈ Set.range b := h ▸ Set.mem_range_self i
    exact this
  choose τ hτ using hex
  have hinj : Function.Injective τ := fun i j hij => ha (by rw [← hτ i, ← hτ j, hij])
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective τ (Finite.injective_iff_bijective.1 hinj)
  have hfg : (f ∘ b) ∘ σ = f ∘ a := by
    funext i
    show f (b (τ i)) = f (a i)
    rw [hτ]
  rw [← hfg]
  exact hv k _ σ
private def blockSum (q : ℕ) (f : Fin q → α) : ℝ :=
  ∑ π ∈ nonSingletonPartitions q, ∏ B ∈ π.parts, v B.card (restrictTuple f B)
private def blockValues {q : ℕ} (f : Fin q → α) : Cumulants.SubsetFamily q :=
  fun B => (v B.1.card (restrictTuple f B.1) : ℂ)
private theorem eval_restrictTuple_restrictTuple {q : ℕ} (f : Fin q → α) (B : Finset (Fin q))
    (I : Finset (Fin B.card)) :
    v I.card (restrictTuple (restrictTuple f B) I) =
      v (I.map (B.orderEmbOfFin rfl).toEmbedding).card
        (restrictTuple f (I.map (B.orderEmbOfFin rfl).toEmbedding)) := by
  have ha : StrictMono (B.orderEmbOfFin rfl ∘ I.orderEmbOfFin rfl) :=
    (B.orderEmbOfFin rfl).strictMono.comp (I.orderEmbOfFin rfl).strictMono
  refine eval_eq_of_strictMono v f ha
    ((I.map (B.orderEmbOfFin rfl).toEmbedding).orderEmbOfFin rfl).strictMono ?_
  change Set.range (B.orderEmbOfFin rfl ∘ I.orderEmbOfFin rfl) = _
  rw [Set.range_comp, Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin, Finset.coe_map]
  rfl
private def orderEquivOfCard {q : ℕ} (B : Finset (Fin q)) :
    (Finset.univ : Finset (Fin B.card)) ≃ B :=
  (Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _).trans (B.orderIsoOfFin rfl).toEquiv
private theorem blockImage_orderEquivOfCard {q : ℕ} (B : Finset (Fin q))
    (I : Finset (Fin B.card)) :
    blockImage (orderEquivOfCard B) I = I.map (B.orderEmbOfFin rfl).toEmbedding := by
  ext y
  rw [mem_blockImage, Finset.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.1, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, Finset.mem_univ l⟩, hl, rfl⟩
private theorem blockProduct_blockValues {q : ℕ} (f : Fin q → α)
    {B : Finset (Fin q)} (π : Partitions B) :
    Cumulants.blockProduct (blockValues v f) π =
      ((∏ I ∈ π.parts, v I.card (restrictTuple f I) : ℝ) : ℂ) := by
  rw [Complex.ofReal_prod, ← Finset.prod_coe_sort π.parts]
  rfl
private theorem partitionSum_blockValues
    (hT : SetPartition.Elementary.TransportUnderEquiv)
    (hv : ∀ (k : ℕ) (g : Fin k → α), k < 2 → v k g = 0) {q : ℕ} (f : Fin q → α)
    (B : Cumulants.NonemptyFinSubset q) :
    Cumulants.partitionSum (blockValues v f) B =
      ((blockSum v B.1.card (restrictTuple f B.1) : ℝ) : ℂ) := by
  have hterm : ∀ π : PartitionsFin B.1.card,
      ∏ I ∈ (partitionMap hT (orderEquivOfCard B.1) π).parts, v I.card (restrictTuple f I) =
        ∏ I ∈ π.parts, v I.card (restrictTuple (restrictTuple f B.1) I) := by
    intro π
    rw [prod_partitionMap hT]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [blockImage_orderEquivOfCard, eval_restrictTuple_restrictTuple v]
  have hsum := (partitionMap_bijective hT (orderEquivOfCard B.1)).sum_comp
    (fun π' : Partitions B.1 => ((∏ I ∈ π'.parts, v I.card (restrictTuple f I) : ℝ) : ℂ))
  unfold Cumulants.partitionSum
  simp only [blockProduct_blockValues]
  rw [← hsum]
  simp only [hterm]
  unfold blockSum
  rw [Complex.ofReal_sum]
  refine (Finset.sum_subset (Finset.subset_univ _) fun π _ hπ => ?_).symm
  have hex : ∃ I ∈ π.parts, I.card < 2 := by
    by_contra hne
    exact hπ (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun I hI =>
      not_lt.1 fun h => hne ⟨I, hI, h⟩⟩)
  obtain ⟨I, hI, h1⟩ := hex
  rw [Finset.prod_eq_zero hI (hv _ _ h1), Complex.ofReal_zero]
private theorem moebius_blockSum
    (hT : SetPartition.Elementary.TransportUnderEquiv)
    (hPoly : Cumulants.PartitionSubstitutionsInverse)
    (hv : ∀ (k : ℕ) (g : Fin k → α), k < 2 → v k g = 0) {q : ℕ} (hq : 1 ≤ q) (f : Fin q → α) :
    ∑ π : PartitionsFin q,
      (-1 : ℝ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℝ) *
        ∏ B ∈ π.parts, blockSum v B.card (restrictTuple f B) = v q f := by
  have hinv : Cumulants.moebiusPartitionSum
      (Cumulants.partitionSum (blockValues v f)) (Cumulants.univSubset hq) =
      blockValues v f (Cumulants.univSubset hq) :=
    congrFun ((hPoly q hq).2.2.2.2.1 (blockValues v f)) _
  rw [(hPoly q hq).2.2.2.2.2.2.2] at hinv
  have hwhole : blockValues v f (Cumulants.univSubset hq) = ((v q f : ℝ) : ℂ) := by
    have h := eval_eq_of_strictMono v f
      ((Finset.univ : Finset (Fin q)).orderEmbOfFin rfl).strictMono
      (strictMono_id : StrictMono (id : Fin q → Fin q))
      (by rw [Finset.range_orderEmbOfFin]; simp)
    show ((v (Finset.univ : Finset (Fin q)).card (restrictTuple f Finset.univ) : ℝ) : ℂ) = _
    exact congrArg _ h
  rw [hwhole] at hinv
  have hprod : ∀ π : PartitionsFin q,
      Cumulants.blockProduct (Cumulants.partitionSum (blockValues v f)) π =
      ((∏ B ∈ π.parts, blockSum v B.card (restrictTuple f B) : ℝ) : ℂ) := by
    intro π
    rw [Complex.ofReal_prod, ← Finset.prod_coe_sort π.parts]
    unfold Cumulants.blockProduct
    exact Finset.prod_congr rfl fun B _ =>
      partitionSum_blockValues v hT hv f (Cumulants.blockSubset π B)
  simp only [hprod] at hinv
  exact_mod_cast hinv
private def univPerm {q : ℕ} (σ : Equiv.Perm (Fin q)) :
    (Finset.univ : Finset (Fin q)) ≃ (Finset.univ : Finset (Fin q)) :=
  σ.subtypeEquiv fun a => by simp
private theorem blockImage_univPerm {q : ℕ} (σ : Equiv.Perm (Fin q)) (B : Finset (Fin q)) :
    blockImage (univPerm σ) B = B.map σ.toEmbedding := by
  ext y
  rw [mem_blockImage, Finset.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.1, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, Finset.mem_univ l⟩, hl, rfl⟩
private theorem mem_nonSingleton_partitionMap
    (hT : SetPartition.Elementary.TransportUnderEquiv) {q : ℕ}
    (e : (Finset.univ : Finset (Fin q)) ≃ (Finset.univ : Finset (Fin q)))
    (π : PartitionsFin q) :
    π ∈ nonSingletonPartitions q ↔ partitionMap hT e π ∈ nonSingletonPartitions q := by
  simp only [nonSingletonPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
  have hc := ((hT (Fin q) (Fin q) Finset.univ Finset.univ e).2 π).2.1
  constructor
  · intro h I hI
    rw [partitionMap_parts hT] at hI
    obtain ⟨B, hB, rfl⟩ := (mem_partitionImage e π I).1 hI
    rw [hc B hB]
    exact h B hB
  · intro h B hB
    have h' := h (blockImage e B) (by
      rw [partitionMap_parts hT]
      exact (mem_partitionImage e π _).2 ⟨B, hB, rfl⟩)
    rwa [hc B hB] at h'
private theorem blockSum_comp_perm
    (hT : SetPartition.Elementary.TransportUnderEquiv)
    (hv : ∀ (k : ℕ) (g : Fin k → α) (σ : Equiv.Perm (Fin k)), v k (g ∘ σ) = v k g)
    {q : ℕ} (f : Fin q → α) (σ : Equiv.Perm (Fin q)) :
    blockSum v q (f ∘ σ) = blockSum v q f := by
  unfold blockSum
  refine Finset.sum_equiv (Equiv.ofBijective _ (partitionMap_bijective hT (univPerm σ)))
    (mem_nonSingleton_partitionMap hT _) fun π _ => ?_
  simp only [Equiv.ofBijective_apply]
  rw [prod_partitionMap hT]
  refine Finset.prod_congr rfl fun B _ => ?_
  rw [blockImage_univPerm]
  have hinj : Function.Injective (σ ∘ B.orderEmbOfFin rfl) :=
    σ.injective.comp (B.orderEmbOfFin rfl).injective
  refine eval_eq_of_injective v hv f hinj
    ((B.map σ.toEmbedding).orderEmbOfFin rfl).injective ?_
  change Set.range (σ ∘ B.orderEmbOfFin rfl) = _
  rw [Set.range_comp, Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin, Finset.coe_map]
  rfl
end TupleEvaluation
section OnTheTorus
variable (s : TorusSide) (F : Ambient.ConnectedFamily s.asMirrorData .torus)
private def tupleEval (k : ℕ) (g : Fin k → s.Point .torus → ℝ) : ℝ :=
  F.evalAt k (List.ofFn g)
private theorem tupleEval_of_lt (k : ℕ) (g : Fin k → s.Point .torus → ℝ) (hk : k < 2) :
    tupleEval s F k g = 0 := by
  unfold tupleEval Ambient.ConnectedFamily.evalAt
  rw [dif_neg (not_le.2 hk)]
private theorem tupleEval_comp_perm (hsym : s.IsPermInvariantFamily .torus F) (k : ℕ)
    (g : Fin k → s.Point .torus → ℝ) (σ : Equiv.Perm (Fin k)) :
    tupleEval s F k (g ∘ σ) = tupleEval s F k g := by
  unfold tupleEval Ambient.ConnectedFamily.evalAt
  by_cases hk : 2 ≤ k
  · rw [dif_pos hk, dif_pos hk]
    unfold Ambient.evalOrZero
    by_cases hg : List.ofFn g ∈ s.sepOfLength .torus k
    · have hg' := s.comp_perm_mem_sepOfLength hg σ
      rw [dif_pos hg, dif_pos hg']
      exact hsym k hk g σ hg hg'
    · have hg' : List.ofFn (g ∘ σ) ∉ s.sepOfLength .torus k := fun h => hg (by
        have h' := s.comp_perm_mem_sepOfLength h (σ⁻¹ : Equiv.Perm (Fin k))
        have e : (g ∘ σ) ∘ ⇑(σ⁻¹ : Equiv.Perm (Fin k)) = g := by
          funext i
          simp
        rwa [e] at h')
      rw [dif_neg hg, dif_neg hg']
  · rw [dif_neg hk, dif_neg hk]
private theorem get_ofFn_cast {α : Type*} {k : ℕ} (g : Fin k → α) (h : (List.ofFn g).length = k)
    (i : Fin k) : (List.ofFn g).get (Fin.cast h.symm i) = g i := by
  simp
private theorem centered_eq_blockSum (Y : s.FnTuple .torus) (hY : Y ∈ s.sepTuples .torus) {k : ℕ}
    (h : Y.length = k) (g : Fin k → s.Point .torus → ℝ)
    (hg : ∀ i, Y.get (Fin.cast h.symm i) = g i) :
    F.centeredFunctional ⟨Y, hY⟩ = blockSum (tupleEval s F) k g := by
  subst h
  have e : g = Y.get := funext fun i => (hg i).symm
  subst e
  rfl
private theorem centered_subSeparated {n : ℕ} (X : s.sepOfLength .torus n)
    (B : Finset (Fin X.1.length)) :
    F.centeredFunctional (Ambient.subSeparated X B) =
      blockSum (tupleEval s F) B.card (restrictTuple X.1.get B) :=
  centered_eq_blockSum s F _ _ List.length_ofFn _ fun i =>
    get_ofFn_cast (restrictTuple X.1.get B) List.length_ofFn i
private theorem connected_eq_evalAt
    (hT : SetPartition.Elementary.TransportUnderEquiv)
    (hPoly : Cumulants.PartitionSubstitutionsInverse) {n : ℕ}
    (X : s.sepOfLength .torus n) (hn : 1 ≤ X.1.length) :
    Ambient.connectedOfSeparated F.centeredFunctional n X = F.evalAt X.1.length X.1 := by
  have h := moebius_blockSum (tupleEval s F) hT hPoly (tupleEval_of_lt s F) hn X.1.get
  have e : tupleEval s F X.1.length X.1.get = F.evalAt X.1.length X.1 := by
    unfold tupleEval
    rw [List.ofFn_get]
  rw [e] at h
  rw [← h]
  unfold Ambient.connectedOfSeparated
  refine Finset.sum_congr rfl fun π _ => ?_
  refine congrArg₂ (· * ·) rfl ?_
  exact Finset.prod_congr rfl fun B _ => centered_subSeparated s F X B
private theorem isBoundedOnTorus_of_mem (hNorms : LipschitzEstimates.Combined)
    (hL : 8 * 105 ^ 4 ≤ s.L) {f : s.Point .torus → ℝ}
    (hf : f ∈ Ambient.compactC1 s.asMirrorData ℝ .torus) :
    ConnectedFunctionExpansion.IsBoundedOnTorus (L := s.L) (m := s.m) f := by
  obtain ⟨C, hC⟩ := ((hNorms s hL 0 .torus).1.1 f hf).1
  unfold ConnectedFunctionExpansion.IsBoundedOnTorus PeriodicLattice.torusSupNorm
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (iSup_le fun y => ENNReal.ofReal_le_ofReal (hC y))
private theorem connectedFunction_congr (L m c : ℕ) (b : ℂ)
    (Y : List (PeriodicLattice.FourTorus L m → ℝ)) {k : ℕ}
    (h : Y.length = k) (g : Fin k → PeriodicLattice.FourTorus L m → ℝ)
    (hg : ∀ i, Y.get (Fin.cast h.symm i) = g i) :
    PeriodicLattice.connectedFunction L m c b Y.get =
      PeriodicLattice.connectedFunction L m c b g := by
  subst h
  have e : g = Y.get := funext fun i => (hg i).symm
  rw [e]
private theorem tendsto_centeredMomentAt
    (hCentred : OneCutoffCumulants.Statement)
    (hNorms : LipschitzEstimates.Combined) (hL : 8 * 105 ^ 4 ≤ s.L)
    (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (hβ : ∀ j, 0 < β j) (J : Set ℕ+)
    (hlim : s.TendstoAlong K β J (s.toComplexTupleFns F)) (X : s.sepTuples .torus) :
    Tendsto (fun j => s.centeredMomentAt (K j) (β j) (hβ j) X.1) (atTop ⊓ 𝓟 J)
      (𝓝 (F.centeredFunctional X)) := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 X.2
  have hsep : Ambient.IsSeparatedList s.asMirrorData .torus X.1 := hn.2
  have hfac : ∀ I : Finset (Fin X.1.length), 2 ≤ I.card →
      Tendsto (fun j => PeriodicLattice.connectedFunction s.L s.m (K j) ((β j : ℝ) : ℂ)
        (restrictTuple X.1.get I)) (atTop ⊓ 𝓟 J)
        (𝓝 ((F.evalAt I.card (Ambient.subList X.1 I) : ℝ) : ℂ)) := by
    intro I hI
    have hY := Ambient.subList_mem_separatedN hsep I
    have h := hlim I.card hI ⟨_, hY⟩
    rw [F.evalAt_of_mem hI hY]
    refine h.congr fun j => ?_
    exact connectedFunction_congr _ _ _ _ _ List.length_ofFn _ fun i =>
      get_ofFn_cast (restrictTuple X.1.get I) List.length_ofFn i
  have hsum : Tendsto (fun j => ∑ π ∈ nonSingletonPartitions X.1.length, ∏ I ∈ π.parts,
      PeriodicLattice.connectedFunction s.L s.m (K j) ((β j : ℝ) : ℂ) (restrictTuple X.1.get I))
      (atTop ⊓ 𝓟 J)
      (𝓝 (∑ π ∈ nonSingletonPartitions X.1.length, ∏ I ∈ π.parts,
        ((F.evalAt I.card (Ambient.subList X.1 I) : ℝ) : ℂ))) :=
    tendsto_finsetSum _ fun π hπ => tendsto_finsetProd _ fun I hI =>
      hfac I ((Finset.mem_filter.1 hπ).2 I hI)
  have hj : ∀ j, ((s.centeredMomentAt (K j) (β j) (hβ j) X.1 : ℝ) : ℂ) =
      ∑ π ∈ nonSingletonPartitions X.1.length, ∏ I ∈ π.parts,
        PeriodicLattice.connectedFunction s.L s.m (K j) ((β j : ℝ) : ℂ)
          (restrictTuple X.1.get I) := by
    intro j
    have h := (hCentred (s.mirrorDataOf (K j) (β j) (hβ j)) hL).2.1 X.1.length X.1.get
      fun l => isBoundedOnTorus_of_mem s hNorms hL (hsep.1 _ (List.get_mem _ _))
    rw [singletonFree_eq_nonSingletonPartitions] at h
    have e : (List.ofFn X.1.get : List (s.Point .torus → ℝ)) = X.1 := List.ofFn_get _
    have e' : ((s.centeredMomentAt (K j) (β j) (hβ j) X.1 : ℝ) : ℂ) =
        (((s.mirrorDataOf (K j) (β j) (hβ j)).latticeMoment (List.ofFn X.1.get) : ℝ) : ℂ) :=
      congrArg (fun Y => (((s.mirrorDataOf (K j) (β j) (hβ j)).latticeMoment Y : ℝ) : ℂ)) e.symm
    exact e'.trans h
  have hre := (Complex.continuous_re.tendsto _).comp (hsum.congr fun j => (hj j).symm)
  have e : (∑ π ∈ nonSingletonPartitions X.1.length, ∏ I ∈ π.parts,
      ((F.evalAt I.card (Ambient.subList X.1 I) : ℝ) : ℂ)).re = F.centeredFunctional X := by
    have e' : (∑ π ∈ nonSingletonPartitions X.1.length, ∏ I ∈ π.parts,
        ((F.evalAt I.card (Ambient.subList X.1 I) : ℝ) : ℂ)) =
        ((F.centeredFunctional X : ℝ) : ℂ) := by
      unfold Ambient.ConnectedFamily.centeredFunctional
      push_cast
      rfl
    rw [e', Complex.ofReal_re]
  rw [e] at hre
  refine hre.congr fun j => ?_
  simp
end OnTheTorus
theorem statement_holds (hCentred : OneCutoffCumulants.Statement)
    (hFacts : ReflectionPositivity.AxisMirror.BothFunctionalsSeparated)
    (hNorms : LipschitzEstimates.Combined)
    (hPart : SetPartition.Elementary.BasicFacts)
    (hPoly : Cumulants.PartitionSubstitutionsInverse) : Statement := by
  intro s hL m' K β C h J _ F hlim hsym
  have hT : SetPartition.Elementary.TransportUnderEquiv := hPart.2.2.1
  refine ⟨tendsto_centeredMomentAt s F hCentred hNorms hL K β h.β_pos J hlim,
    ((hFacts s.asMirrorData).2.2 .torus F).1, ?_, ?_, ?_⟩
  · intro n f σ hf hf'
    have hs : ∀ (g : Fin n → s.Point .torus → ℝ)
        (hg : List.ofFn g ∈ s.sepOfLength .torus n),
        Ambient.restrictN s.asMirrorData .torus F.centeredFunctional n ⟨_, hg⟩ =
          blockSum (tupleEval s F) n g := fun g hg =>
      centered_eq_blockSum s F (List.ofFn g) (Ambient.separatedN_subset_separatedAll _ _ n hg)
        List.length_ofFn g (get_ofFn_cast g List.length_ofFn)
    rw [hs, hs]
    exact blockSum_comp_perm _ hT (tupleEval_comp_perm s F hsym) f σ
  · intro X
    have h1 : X.1.length = 1 := X.2.1
    rw [connected_eq_evalAt s F hT hPoly X (by omega)]
    unfold Ambient.ConnectedFamily.evalAt
    rw [dif_neg (by omega)]
  · intro n hn X
    have h1 : X.1.length = n := X.2.1
    rw [connected_eq_evalAt s F hT hPoly X (by omega), h1]
    exact F.evalAt_of_mem hn X.2
end ToriAtArbitraryCouplings.CenteredMomentsOfLimit
end YangMills.Construction
end
