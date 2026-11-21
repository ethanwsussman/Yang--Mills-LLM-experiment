import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.Continuum.MultilinearityAndInversionOfTheConnectedFunctions
import YangMills.Construction.Continuum.TheRecursionOfTheConnectedFunctionsIsTriangular
import YangMills.Construction.Cumulants.SmallestPartitionsBlocksAndTransportByABijection
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
noncomputable section
namespace TestSpaces
open SetPartition
namespace RecursionTriangular
variable {k n : ℕ}
abbrev orderEmbFin (I : Finset (Fin k)) : Fin I.card ↪ Fin k :=
  (I.orderEmbOfFin rfl).toEmbedding
theorem sepRestrict_sepRestrict (X : SepTupleOfCard k) (I : Finset (Fin k))
    (J : Finset (Fin I.card)) :
    (⟨J.card, sepRestrict (sepRestrict X I) J⟩ : SepTuple) =
      ⟨(J.map (orderEmbFin I)).card, sepRestrict X (J.map (orderEmbFin I))⟩ := by
  have hc : J.card = (J.map (orderEmbFin I)).card := (Finset.card_map _).symm
  refine sepTuple_ext _ _ hc fun l => ?_
  have hu := Finset.orderEmbOfFin_unique (s := J.map (orderEmbFin I))
    (k := (J.map (orderEmbFin I)).card) rfl
    (f := fun m => orderEmbFin I (J.orderEmbOfFin rfl (Fin.cast hc.symm m)))
    (fun m => Finset.mem_map_of_mem _ (Finset.orderEmbOfFin_mem _ _ _))
    (fun a b hab => (I.orderEmbOfFin rfl).strictMono
      ((J.orderEmbOfFin rfl).strictMono (by simpa using hab)))
  exact congrArg X.1 (congrFun hu (Fin.cast hc l))
def finCardEquiv (I : Finset (Fin k)) : (Finset.univ : Finset (Fin I.card)) ≃ I :=
  (Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _).trans (I.orderIsoOfFin rfl).toEquiv
theorem blockImage_finCardEquiv (I : Finset (Fin k)) (J : Finset (Fin I.card)) :
    blockImage (finCardEquiv I) J = J.map (orderEmbFin I) := by
  ext y
  rw [mem_blockImage, Finset.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.1, hl, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, Finset.mem_univ a⟩, ha, rfl⟩
theorem sum_prod_map_orderEmbFin
    (hT : Elementary.TransportUnderEquiv)
    (I : Finset (Fin k)) (G : Finset (Fin k) → ℝ) :
    ∑ η : Partitions (Finset.univ : Finset (Fin I.card)), ∏ J ∈ η.parts, G (J.map (orderEmbFin I)) =
      ∑ π : Partitions I, ∏ J ∈ π.parts, G J := by
  obtain ⟨hbij, hblocks⟩ := hT (Fin I.card) (Fin k) Finset.univ I (finCardEquiv I)
  have hmaps : ∀ η : Partitions (Finset.univ : Finset (Fin I.card)),
      ∃ π : Partitions I, π.parts = partitionImage (finCardEquiv I) η :=
    fun η => hbij.mapsTo (Set.mem_univ η)
  choose tr htr using hmaps
  have hb : Function.Bijective tr := by
    refine ⟨fun η η' h => hbij.injOn (Set.mem_univ _) (Set.mem_univ _) ?_, fun π => ?_⟩
    · rw [← htr, ← htr, h]
    · obtain ⟨η, -, hη⟩ := hbij.surjOn (show π.parts ∈ partitionSets I from ⟨π, rfl⟩)
      exact ⟨η, Finpartition.ext ((htr η).trans hη)⟩
  refine Fintype.sum_bijective tr hb _ _ fun η => ?_
  rw [htr, partitionImage, Finset.prod_image (hblocks η).1.injOn]
  exact Finset.prod_congr rfl fun J _ => by rw [blockImage_finCardEquiv]
theorem sum_partitions_eq_add_proper {α : Type*} [DecidableEq α] {A : Finset α} (hA : A.Nonempty)
    (F : Finset α → ℝ) :
    ∑ π : Partitions A, ∏ J ∈ π.parts, F J =
      F A + ∑ π ∈ Finset.univ.filter (fun π : Partitions A => π.parts ≠ {A}),
        ∏ J ∈ π.parts, F J := by
  have hA' : A ≠ ⊥ := hA.ne_empty
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun π : Partitions A => π.parts = {A})]
  congr 1
  have h : Finset.univ.filter (fun π : Partitions A => π.parts = {A}) =
      {Finpartition.indiscrete hA'} := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => Finpartition.ext h, fun h => by rw [h]; rfl⟩
  rw [h, Finset.sum_singleton]
  exact Finset.prod_singleton _ _
def cumulantRecSigma (σ : SepTuple → ℝ) (Y : SepTuple) : ℝ :=
  cumulantRec σ Y.1 Y.2
theorem eq_sum_prod_cumulantRec (σ : SepTuple → ℝ) (hn : 1 ≤ n)
    (Y : SepTupleOfCard n) :
    σ ⟨n, Y⟩ = ∑ π : PartitionsFin n, ∏ J ∈ π.parts,
      cumulantRec σ J.card (sepRestrict Y J) := by
  have hu : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  rw [sum_partitions_eq_add_proper hu fun J => cumulantRec σ J.card (sepRestrict Y J)]
  have h₁ : cumulantRec σ (Finset.univ : Finset (Fin n)).card
      (sepRestrict Y Finset.univ) = cumulantRec σ n Y :=
    congrArg (cumulantRecSigma σ) (sepRestrict_univ Y)
  rw [h₁, cumulantRec_eq σ Y, properPartitions, sub_add_cancel]
theorem satisfiesRecursionAt
    (hT : Elementary.TransportUnderEquiv)
    (σ : SepTuple → ℝ) (X : SepTupleOfCard k) : SatisfiesCumulantRecursionAt σ X := by
  intro I hI
  rw [eq_sum_prod_cumulantRec σ hI.card_pos (sepRestrict X I),
    ← sum_prod_map_orderEmbFin hT I fun J => cumulantRec σ J.card (sepRestrict X J)]
  refine Finset.sum_congr rfl fun η _ => Finset.prod_congr rfl fun J _ => ?_
  exact congrArg (cumulantRecSigma σ) (sepRestrict_sepRestrict X I J)
theorem eq_of_sum_prod_eq (hB : Elementary.BlockFacts)
    (e c d : Finset (Fin k) → ℝ)
    (hc : ∀ I : Finset (Fin k), I.Nonempty → e I = ∑ π : Partitions I, ∏ J ∈ π.parts, c J)
    (hd : ∀ I : Finset (Fin k), I.Nonempty → e I = ∑ π : Partitions I, ∏ J ∈ π.parts, d J) :
    ∀ I : Finset (Fin k), I.Nonempty → c I = d I := by
  intro I
  induction I using Finset.strongInduction with
  | H I ih =>
    intro hI
    have h₁ := (hc I hI).symm.trans (hd I hI)
    rw [sum_partitions_eq_add_proper hI c, sum_partitions_eq_add_proper hI d] at h₁
    have h₂ : ∑ π ∈ Finset.univ.filter (fun π : Partitions I => π.parts ≠ {I}),
          ∏ J ∈ π.parts, c J =
        ∑ π ∈ Finset.univ.filter (fun π : Partitions I => π.parts ≠ {I}),
          ∏ J ∈ π.parts, d J :=
      Finset.sum_congr rfl fun π hπ => Finset.prod_congr rfl fun J hJ =>
        ih J (((hB (Fin k) I).2 hI.ne_empty).2 π (Finset.mem_filter.1 hπ).2 J hJ)
          (π.nonempty_of_mem_parts hJ)
    rw [h₂] at h₁
    exact add_right_cancel h₁
theorem cumulantFamily_congr (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ) {m m' : ℕ} (h : 2 ≤ m)
    (h' : 2 ≤ m') {Y : SepTupleOfCard m} {Y' : SepTupleOfCard m'}
    (hY : (⟨m, Y⟩ : SepTuple) = ⟨m', Y'⟩) : S m h Y = S m' h' Y' := by
  obtain ⟨rfl, hY⟩ := Sigma.mk.inj_iff.1 hY
  cases eq_of_heq hY
  rfl
theorem partitionsNoSingletons_fin_two :
    partitionsNoSingletons (Fin 2) = {{Finset.univ}} := by
  ext η
  simp only [partitionsNoSingletons, ClusterExpansion.SymGraph.partitions,
    ClusterExpansion.SymGraph.IsPartition,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨-, -, hU⟩, h2⟩
    have huniv : ∀ J ∈ η, J = Finset.univ := fun J hJ =>
      (Finset.card_eq_iff_eq_univ J).1
        (le_antisymm (Finset.card_le_univ J) (by simpa using h2 J hJ))
    have h0 := Finset.mem_univ (0 : Fin 2)
    rw [← hU] at h0
    obtain ⟨J, hJ, -⟩ : ∃ J ∈ η, (0 : Fin 2) ∈ J := by simpa using h0
    exact Finset.eq_singleton_iff_unique_mem.2 ⟨huniv J hJ ▸ hJ, huniv⟩
  · rintro rfl
    simp
theorem centredOfCumulants_pair (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ)
    (X : SepTupleOfCard 2) :
    centredOfCumulants S ⟨2, X⟩ = S 2 le_rfl X := by
  have hmem : ({Finset.univ} : Finset (Finset (Fin 2))) ∈ partitionsNoSingletons (Fin 2) := by
    simp [partitionsNoSingletons_fin_two]
  unfold centredOfCumulants
  refine (Finset.sum_eq_single_of_mem
    (⟨_, hmem⟩ : {η // η ∈ partitionsNoSingletons (Fin 2)}) (Finset.mem_attach _ _)
    fun η _ hη => ?_).trans ?_
  · exact absurd (Subtype.ext (Finset.mem_singleton.1
      ((Finset.ext_iff.1 partitionsNoSingletons_fin_two η.1).1 η.2))) hη
  · refine (Finset.prod_eq_single_of_mem
      (⟨Finset.univ, Finset.mem_singleton_self _⟩ :
        {J // J ∈ ({Finset.univ} : Finset (Finset (Fin 2)))}) (Finset.mem_attach _ _)
      fun J _ hJ => absurd (Subtype.ext (Finset.mem_singleton.1 J.2)) hJ).trans ?_
    exact cumulantFamily_congr S _ _ (sepRestrict_univ X)
theorem hasLowOrderValues (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ) :
    HasLowOrderValues (centredOfCumulants S) (S 2 le_rfl) :=
  ⟨centredOfCumulants_nil S, centredOfCumulants_single S, centredOfCumulants_pair S⟩
theorem centredOfConnFamily_eq (S : EuclideanFunctionals.ConnFamily) (Y : SepTuple) :
    centredOfConnFamily S Y = centredOfCumulants (connFamilyOnTuples S) Y := by
  have key : ∀ (k : ℕ) (Y : Ambient.separatedN EuclideanFunctionals.defaultMirrorData
      .euclidean k),
      centredOfConnFamily S ⟨k, (sepTupleListEquiv _ k).symm Y⟩ =
        centredOfCumulants (connFamilyOnTuples S) ⟨k, (sepTupleListEquiv _ k).symm Y⟩ := by
    rintro k ⟨L, rfl, hL⟩
    rw [centredOfCumulants_eq_blockProductSum]
    simp only [centredOfConnFamily, Equiv.apply_symm_apply]
    change ∑ π ∈ nonSingletonPartitions L.length, ∏ J ∈ π.parts,
      Ambient.ConnectedFamily.evalAt S J.card (Ambient.subList L J) = _
    rw [nonSingletonPartitions_eq_atLeastTwoPartitions, blockProductSum]
    symm
    refine Eq.trans (Finset.sum_congr rfl fun π _ => ?_) (Finset.sum_attach _
      fun π : Partitions (Finset.univ : Finset (Fin L.length)) =>
        ∏ J ∈ π.parts, Ambient.ConnectedFamily.evalAt S J.card (Ambient.subList L J))
    refine Eq.trans (Finset.prod_congr rfl fun J _ => ?_) (Finset.prod_attach π.1.parts fun J =>
      Ambient.ConnectedFamily.evalAt S J.card (Ambient.subList L J))
    rw [Ambient.ConnectedFamily.evalAt_of_mem S
      (two_le_card_of_mem_atLeastTwoPartitions π.2 J.2)
      (Ambient.subList_mem_separatedN hL J.1)]
    exact congrArg _ (Subtype.ext rfl)
  obtain ⟨k, X⟩ := Y
  have h := key k (sepTupleListEquiv _ k X)
  rwa [Equiv.symm_apply_apply] at h
theorem mem_disjointSupportTuples_of_ofFn_mem (D : ReflectionPositivity.AxisMirror.MirrorData)
    {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : (List.ofFn f : Ambient.FnList D .euclidean) ∈
      Ambient.separatedN D .euclidean n) :
    f ∈ disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) n := by
  have h := get_mem_disjointSupportTuples D ⟨_, hf⟩
  have he : (fun i : Fin n => ((List.ofFn f : Ambient.FnList D .euclidean).get
      (Fin.cast hf.1.symm i) : (Fin 4 → ℝ) → ℝ)) = f :=
    funext fun i => (List.get_ofFn f _).trans (congrArg f (Fin.ext rfl))
  exact he ▸ h
theorem evalOrZero_onAmbientLists (D : ReflectionPositivity.AxisMirror.MirrorData)
    (Φ : SepTupleOfCard n → ℝ) (X : SepTupleOfCard n) :
    Ambient.evalOrZero (onAmbientLists D Φ) (List.ofFn X.1 : Ambient.FnList D .euclidean) =
      Φ X := by
  rw [Ambient.evalOrZero, dif_pos (ofFn_mem_ambientSeparatedN D X)]
  exact congrArg Φ ((sepTupleListEquiv D n).left_inv X)
def slotSet (X X' : SepTupleOfCard n) (i l : Fin n) : Set (Fin 4 → ℝ) :=
  open Classical in
  if l = i then tsupport (X.1 i) ∪ tsupport (X'.1 i) else tsupport (X.1 l)
theorem isCompact_slotSet (X X' : SepTupleOfCard n) (i l : Fin n) :
    IsCompact (slotSet X X' i l) := by
  unfold slotSet
  split_ifs
  · exact (X.2.1 i).2.1.union (X'.2.1 i).2.1
  · exact (X.2.1 l).2.1
theorem disjoint_slotSet {X X' : SepTupleOfCard n} {i : Fin n}
    (h : ∀ j, j ≠ i → X.1 j = X'.1 j) {l l' : Fin n} (hl : l ≠ l') :
    Disjoint (slotSet X X' i l) (slotSet X X' i l') := by
  have hside : ∀ j, j ≠ i → Disjoint (tsupport (X.1 i) ∪ tsupport (X'.1 i)) (tsupport (X.1 j)) :=
    fun j hj => Set.disjoint_union_left.2 ⟨X.2.2 hj.symm, by rw [h j hj]; exact X'.2.2 hj.symm⟩
  unfold slotSet
  split_ifs with h₁ h₂ h₂
  · exact absurd (h₁.trans h₂.symm) hl
  · exact hside l' h₂
  · exact (hside l h₁).symm
  · exact X.2.2 hl
theorem setDistR4_slotSet_pos {X X' : SepTupleOfCard n} {i : Fin n}
    (h : ∀ j, j ≠ i → X.1 j = X'.1 j) {l l' : Fin n} (hl : l ≠ l') :
    0 < TestFunctions.setDistR4 (slotSet X X' i l) (slotSet X X' i l') :=
  SeparatedTuplesR4.setDistR4_pos_of_disjoint (isCompact_slotSet X X' i l)
    (isCompact_slotSet X X' i l').isClosed (disjoint_slotSet h hl)
theorem tsupport_subset_slotSet (X X' : SepTupleOfCard n) (i l : Fin n) :
    tsupport (X.1 l) ⊆ slotSet X X' i l := by
  unfold slotSet
  split_ifs with h
  · exact h ▸ Set.subset_union_left
  · exact subset_rfl
theorem tsupport_subset_slotSet_right (X X' : SepTupleOfCard n) (i : Fin n) :
    tsupport (X'.1 i) ⊆ slotSet X X' i i := by
  unfold slotSet
  rw [if_pos rfl]
  exact Set.subset_union_right
theorem mem_compactC1SuppIn (D : ReflectionPositivity.AxisMirror.MirrorData)
    (X : SepTupleOfCard n) (l : Fin n)
    {A : Set (Fin 4 → ℝ)} (hA : tsupport (X.1 l) ⊆ A) :
    X.1 l ∈ Ambient.compactC1SuppIn D .euclidean A := by
  have hs : (Ambient.closedSupport D Ambient.euclidean (X.1 l) : Set (Fin 4 → ℝ)) =
      tsupport (X.1 l) :=
    SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
  refine ⟨(ofFn_mem_ambientSeparatedN D X).2.1 _ ((List.mem_ofFn' _ _).2 ⟨l, rfl⟩), ?_⟩
  rw [hs]
  exact hA
theorem lin_comb_congr {a a' c c' s t : ℝ} (h : a = a') (h' : c = c') :
    s * a + t * c = s * a' + t * c' := by
  rw [h, h']
theorem isSeparatedMultilinear_onAmbientLists (D : ReflectionPositivity.AxisMirror.MirrorData)
    {Φ : SepTupleOfCard n → ℝ}
    (hΦ : IsMultilinearOnSep Φ) :
    Ambient.IsSeparatedMultilinear D .euclidean (onAmbientLists D Φ) := by
  intro A hA f hf i g hg s t
  have hsep : ∀ f' : Fin n → (Fin 4 → ℝ) → ℝ,
      (∀ l, f' l ∈ Ambient.compactC1SuppIn D .euclidean (A l)) →
        f' ∈ disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) n :=
    fun f' h => mem_disjointSupportTuples_of_ofFn_mem D
      (Ambient.ofFn_mem_separatedN D .euclidean hA h)
  have hupd : ∀ l, Function.update f i g l ∈ Ambient.compactC1SuppIn D .euclidean (A l) := by
    intro l
    by_cases hl : l = i
    · subst hl
      rw [Function.update_self]
      exact hg
    · rw [Function.update_of_ne hl]
      exact hf l
  let X : SepTupleOfCard n := ⟨f, hsep f hf⟩
  let X' : SepTupleOfCard n := ⟨Function.update f i g, hsep _ hupd⟩
  have hXX' : ∀ j, j ≠ i → X.1 j = X'.1 j := fun j hj => (Function.update_of_ne hj _ _).symm
  have hi : X'.1 i = g := Function.update_self _ _ _
  let X'' : SepTupleOfCard n := ⟨Function.update X.1 i (s • X.1 i + t • X'.1 i),
    update_linComb_mem_disjointSupportTuples i s t X X' hXX'⟩
  have h := hΦ i s t X X' X'' hXX' (Function.update_self _ _ _)
    fun j hj => Function.update_of_ne hj _ _
  have e₁ := evalOrZero_onAmbientLists D Φ X
  have e₂ := evalOrZero_onAmbientLists D Φ X'
  have e₃ := evalOrZero_onAmbientLists D Φ X''
  let g₀ : (Fin 4 → ℝ) → ℝ := g
  have hX'' : X''.1 = Function.update X.1 i (s • X.1 i + t • g₀) :=
    congrArg (fun u => Function.update X.1 i (s • X.1 i + t • u)) hi
  rw [hX''] at e₃
  exact e₃.trans (h.trans (lin_comb_congr e₁.symm e₂.symm))
theorem isMultilinearOnSep_of_onAmbientLists (D : ReflectionPositivity.AxisMirror.MirrorData)
    {Φ : SepTupleOfCard n → ℝ}
    (hM : Ambient.IsSeparatedMultilinear D .euclidean (onAmbientLists D Φ)) :
    IsMultilinearOnSep Φ := by
  intro i b b' X X' X'' h₁ h₂ h₃
  have hA : Pairwise fun l l' => 0 < Ambient.setDist D .euclidean (slotSet X X' i l)
      (slotSet X X' i l') := fun l l' hl => setDistR4_slotSet_pos h₁ hl
  have h := hM (slotSet X X' i) hA X.1
    (fun l => mem_compactC1SuppIn D X l (tsupport_subset_slotSet X X' i l)) i (X'.1 i)
    (mem_compactC1SuppIn D X' i (tsupport_subset_slotSet_right X X' i)) b b'
  have e₁ : Function.update X.1 i (b • X.1 i + b' • X'.1 i) = X''.1 := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, h₂]
    · rw [Function.update_of_ne hj, h₃ j hj]
  have e₂ : Function.update X.1 i (X'.1 i) = X'.1 := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
    · rw [Function.update_of_ne hj, h₁ j hj]
  have e₃ := evalOrZero_onAmbientLists D Φ X
  have e₄ := evalOrZero_onAmbientLists D Φ X'
  have e₅ := evalOrZero_onAmbientLists D Φ X''
  rw [← e₁] at e₅
  rw [← e₂] at e₄
  exact e₅.symm.trans (h.trans (lin_comb_congr e₃ e₄))
def toPtFn (s : Conventions.StandingParameters) (f : (Fin 4 → ℝ) → ℝ) :
    AmbientPoints.Pt s .euclidean → ℝ := f
def slotSetPt (s : Conventions.StandingParameters) (X X' : SepTupleOfCard n) (i l : Fin n) :
    Set (AmbientPoints.Pt s .euclidean) := slotSet X X' i l
theorem tsupport_toPtFn (s : Conventions.StandingParameters) (f : (Fin 4 → ℝ) → ℝ) :
    tsupport (toPtFn s f) = tsupport f := by apply _root_.YangMills.Construction.R4TupleForms.tsupport_pt_euclidean <;> assumption
def tupleOfC1Family (s : Conventions.StandingParameters)
    {A : Fin n → Set (AmbientPoints.Pt s .euclidean)}
    (hA : Pairwise fun i j => AmbientPoints.PositivelySeparated s .euclidean (A i) (A j))
    (g : (i : Fin n) → AmbientPoints.c1Submodule (A i)) : SepTupleOfCard n :=
  Continuum.SeparatedFourTuples.sepLenEquiv s n
    ⟨fun i => (g i : AmbientPoints.Pt s .euclidean → ℝ),
      AmbientPoints.mem_separatedTuples_of_forall_mem_c1 hA fun i => (g i).2⟩
theorem isTupleMultilinear_onPointTuples (s : Conventions.StandingParameters)
    {Φ : SepTupleOfCard n → ℝ}
    (hΦ : IsMultilinearOnSep Φ) : AmbientPoints.IsTupleMultilinear (onPointTuples s Φ) := by
  intro A hA
  refine ⟨{ toFun := fun g => Φ (tupleOfC1Family s hA g),
            map_update_add' := ?_, map_update_smul' := ?_ }, fun g => rfl⟩
  · intro _ m i x y
    have h := hΦ i 1 1 (tupleOfC1Family s hA (Function.update m i x))
      (tupleOfC1Family s hA (Function.update m i y))
      (tupleOfC1Family s hA (Function.update m i (x + y)))
      (fun j hj => by
        change ((Function.update m i x j : AmbientPoints.c1Submodule (A j)) :
          AmbientPoints.Pt s .euclidean → ℝ) = (Function.update m i y j : _)
        rw [Function.update_of_ne hj, Function.update_of_ne hj])
      (by
        change ((Function.update m i (x + y) i : AmbientPoints.c1Submodule (A i)) :
          AmbientPoints.Pt s .euclidean → ℝ) = (1 : ℝ) • (Function.update m i x i : _) +
            (1 : ℝ) • (Function.update m i y i : _)
        simp only [Function.update_self, one_smul]
        rfl)
      (fun j hj => by
        change ((Function.update m i (x + y) j : AmbientPoints.c1Submodule (A j)) :
          AmbientPoints.Pt s .euclidean → ℝ) = (Function.update m i x j : _)
        rw [Function.update_of_ne hj, Function.update_of_ne hj])
    simpa using h
  · intro _ m i c x
    have h := hΦ i c 0 (tupleOfC1Family s hA (Function.update m i x))
      (tupleOfC1Family s hA (Function.update m i x))
      (tupleOfC1Family s hA (Function.update m i (c • x)))
      (fun j hj => rfl)
      (by
        change ((Function.update m i (c • x) i : AmbientPoints.c1Submodule (A i)) :
          AmbientPoints.Pt s .euclidean → ℝ) = c • (Function.update m i x i : _) +
            (0 : ℝ) • (Function.update m i x i : _)
        simp only [Function.update_self, zero_smul, add_zero]
        rfl)
      (fun j hj => by
        change ((Function.update m i (c • x) j : AmbientPoints.c1Submodule (A j)) :
          AmbientPoints.Pt s .euclidean → ℝ) = (Function.update m i x j : _)
        rw [Function.update_of_ne hj, Function.update_of_ne hj])
    simpa using h
theorem isMultilinearOnSep_of_onPointTuples (s : Conventions.StandingParameters)
    {Φ : SepTupleOfCard n → ℝ}
    (hP : AmbientPoints.IsTupleMultilinear (onPointTuples s Φ)) : IsMultilinearOnSep Φ := by
  intro i b b' X X' X'' h₁ h₂ h₃
  have hA : Pairwise fun l l' => AmbientPoints.PositivelySeparated s .euclidean
      (slotSetPt s X X' i l) (slotSetPt s X X' i l') :=
    fun l l' hl => (setDistR4_slotSet_pos h₁ hl).ne'
  obtain ⟨L, hL⟩ := hP _ hA
  have hmem : ∀ (Y : SepTupleOfCard n) (l : Fin n) (B : Set (Fin 4 → ℝ)),
      tsupport (Y.1 l) ⊆ B → toPtFn s (Y.1 l) ∈ AmbientPoints.c1CompactlySupportedIn
        (E := .euclidean) (s := s) B := by
    intro Y l B hB
    have h := ((Continuum.SeparatedFourTuples.sepLenEquiv s n).symm Y).2.1 l
    exact ⟨h.1, h.2, (tsupport_toPtFn s (Y.1 l)).le.trans hB⟩
  let g : (l : Fin n) → AmbientPoints.c1Submodule (slotSetPt s X X' i l) :=
    fun l => ⟨toPtFn s (X.1 l), hmem X l _ (tsupport_subset_slotSet X X' i l)⟩
  let y : AmbientPoints.c1Submodule (slotSetPt s X X' i i) :=
    ⟨toPtFn s (X'.1 i), hmem X' i _ (tsupport_subset_slotSet_right X X' i)⟩
  have hval : ∀ (g' : (l : Fin n) → AmbientPoints.c1Submodule (slotSetPt s X X' i l))
      (Y : SepTupleOfCard n), (∀ l, (g' l).1 = toPtFn s (Y.1 l)) → L g' = Φ Y := by
    intro g' Y hY
    rw [hL]
    exact congrArg Φ (Subtype.ext (funext hY))
  have e₁ : L (Function.update g i (b • g i + b' • y)) = Φ X'' := by
    refine hval _ _ fun l => ?_
    by_cases hl : l = i
    · subst hl
      rw [Function.update_self, h₂]
      rfl
    · rw [Function.update_of_ne hl, h₃ l hl]
  have e₂ : L (Function.update g i y) = Φ X' := by
    refine hval _ _ fun l => ?_
    by_cases hl : l = i
    · subst hl
      rw [Function.update_self]
    · rw [Function.update_of_ne hl]
      exact congrArg (toPtFn s) (h₁ l hl)
  have e₃ : L g = Φ X := hval _ _ fun _ => rfl
  rw [← e₁, ← e₂, ← e₃, L.map_update_add, L.map_update_smul, L.map_update_smul,
    Function.update_eq_self]
  simp
theorem multilinearFormsAgree : MultilinearFormsAgree := by
  have h₂ : ∀ (n : ℕ) (s : Conventions.StandingParameters) (Φ : SepTupleOfCard n → ℝ),
      IsMultilinearOnSep Φ ↔ AmbientPoints.IsTupleMultilinear (onPointTuples s Φ) :=
    fun _ s _ => ⟨isTupleMultilinear_onPointTuples s, isMultilinearOnSep_of_onPointTuples s⟩
  have h₁ : ∀ (n : ℕ) (D : ReflectionPositivity.AxisMirror.MirrorData)
      (Φ : SepTupleOfCard n → ℝ),
      IsMultilinearOnSep Φ ↔ Ambient.IsSeparatedMultilinear D .euclidean (onAmbientLists D Φ) :=
    fun _ D _ => ⟨isSeparatedMultilinear_onAmbientLists D, isMultilinearOnSep_of_onAmbientLists D⟩
  refine ⟨fun n _ D s Φ => ⟨h₁ n D Φ, (h₁ n D Φ).symm.trans (h₂ n s Φ)⟩, fun s σ => ?_⟩
  refine and_congr ?_ (forall₂_congr fun n _ => h₂ n s fun X => σ ⟨n, X⟩)
  have he : onAllPointTuples s σ
      ⟨AmbientPoints.nilTuple s .euclidean, AmbientPoints.nilTuple_mem_allSeparatedTuples⟩ =
        σ sepTupleNil :=
    congrArg σ (sepTuple_ext _ _ rfl fun k => k.elim0)
  rw [← he]
theorem cumulantRec_eq_cumulant
    (hB : Elementary.BlockFacts)
    (hT : Elementary.TransportUnderEquiv)
    {σ : SepTuple → ℝ}
    (hinv : ∀ n, 1 ≤ n → ∀ X : SepTupleOfCard n, MomentCumulantInversion σ X) (hn : 1 ≤ n)
    (X : SepTupleOfCard n) : cumulantRec σ n X = cumulant σ X := by
  have hu : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have h := eq_of_sum_prod_eq hB (fun I => σ ⟨I.card, sepRestrict X I⟩)
    (fun I => cumulant σ (sepRestrict X I))
    (fun I => cumulantRec σ I.card (sepRestrict X I))
    (fun I hI => by
      refine (hinv _ hI.card_pos (sepRestrict X I)).trans ?_
      rw [← sum_prod_map_orderEmbFin hT I fun J => cumulant σ (sepRestrict X J)]
      refine Finset.sum_congr rfl fun η _ => Finset.prod_congr rfl fun J _ => ?_
      exact congrArg (fun Y : SepTuple => cumulant σ Y.2)
        (sepRestrict_sepRestrict X I J))
    (satisfiesRecursionAt hT σ X) Finset.univ hu
  have h₁ : cumulant σ (sepRestrict X Finset.univ) = cumulant σ X :=
    congrArg (fun Y : SepTuple => cumulant σ Y.2) (sepRestrict_univ X)
  have h₂ : cumulantRec σ (Finset.univ : Finset (Fin n)).card
      (sepRestrict X Finset.univ) = cumulantRec σ n X :=
    congrArg (cumulantRecSigma σ) (sepRestrict_univ X)
  exact h₂.symm.trans (h.symm.trans h₁)
theorem cumulantRecursionTriangular_holds (hP : Elementary.BasicFacts)
    (hI : CumulantMultilinearInversion) :
    CumulantRecursionTriangular := by
  obtain ⟨-, hB, hT, -⟩ := hP
  refine ⟨fun σ k _ X => ⟨satisfiesRecursionAt hT σ X, fun c hc I hne => ?_⟩,
    ⟨fun S => ?_, hasLowOrderValues⟩, multilinearFormsAgree, fun σ hσ => ?_⟩
  · exact eq_of_sum_prod_eq hB (fun I => σ ⟨I.card, sepRestrict X I⟩) c
      (fun I => cumulantRec σ I.card (sepRestrict X I)) hc (satisfiesRecursionAt hT σ X) I hne
  · have he : centredOfConnFamily S = centredOfCumulants (connFamilyOnTuples S) :=
      funext (centredOfConnFamily_eq S)
    refine ⟨fun k X => centredOfConnFamily_eq S ⟨k, X⟩, ?_⟩
    rw [he]
    exact hasLowOrderValues _
  · obtain ⟨hform, hmult, -, -, hinv⟩ := hI.1 σ hσ fun _ _ _ => 0
    have hconn : ∀ n, 1 ≤ n → ∀ X : SepTupleOfCard n,
        cumulantRec σ n X = cumulant σ X :=
      fun n hn X => cumulantRec_eq_cumulant hB hT hinv hn X
    refine ⟨fun n hn => ⟨fun X => ?_, hconn n hn, fun s X => ?_, ?_⟩, ?_⟩
    · have hu : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      have h₁ : cumulant σ (sepRestrict X Finset.univ) = cumulant σ X :=
        congrArg (fun Y : SepTuple => cumulant σ Y.2) (sepRestrict_univ X)
      rw [hconn n hn X, ← h₁]
      exact (hform n hn X Finset.univ).1 hu
    · have hu : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      have h₁ : cumulant σ (sepRestrict X Finset.univ) = cumulant σ X :=
        congrArg (fun Y : SepTuple => cumulant σ Y.2) (sepRestrict_univ X)
      rw [hconn n hn X, ← h₁]
      exact (hform n hn X Finset.univ).1 hu
    · have hf : cumulantRec σ n = fun X : SepTupleOfCard n =>
          cumulant σ X := funext (hconn n hn)
      rw [hf]
      exact hmult n hn
    · unfold centredOfRec centredPart
      congr 1
      funext m hm X
      exact hconn m (by omega) X
end RecursionTriangular
end TestSpaces
end
end YangMills.Construction
