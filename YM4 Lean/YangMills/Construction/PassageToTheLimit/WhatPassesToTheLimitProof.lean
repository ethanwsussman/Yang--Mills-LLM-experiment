import YangMills.Construction.LinearAlgebra.BoundedMultilinearForms
import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPieces
import YangMills.Construction.PassageToTheLimit.RelationsAmongTensorsInOneProductOfVectorSpaces
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflections
import YangMills.Construction.PassageToTheLimit.SpacesOfTestFunctionsProductsAndSeparatedTuples
import YangMills.Construction.PassageToTheLimit.WhatPassesToTheLimit
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.LimitSpaces.Ambient.LimitPassage
variable {s : Conventions.StandingParameters} {E : Ambient} {k : TestKind} {D : Set (E.Carrier s)}
  {n q : ℕ}
theorem testWithin_subset_lipWithin (hp : testSpacesAndSepTuples)
    (M : SharpParameter) (k : TestKind) (A : Set (E.Carrier s)) :
    E.testWithin s k A ⊆ E.lipWithin s A := by
  cases k
  · exact subset_rfl
  · exact (hp s E M A univ 1 le_rfl).1.2.2.2.1
theorem exists_submodule_testWithin (hp : testSpacesAndSepTuples) (M : SharpParameter)
    (k : TestKind) (A : Set (E.Carrier s)) :
    ∃ W : Submodule ℝ (E.Carrier s → ℝ), (W : Set (E.Carrier s → ℝ)) = E.testWithin s k A := by
  cases k
  · exact (hp s E M A univ 1 le_rfl).1.1
  · exact (hp s E M A univ 1 le_rfl).1.2.2.1
theorem isSepTuple_of_mem (hp : testSpacesAndSepTuples)
    (M : SharpParameter) (hn : 1 ≤ n) (k : TestKind) {A : Fin n → Set (E.Carrier s)}
    (hA : ∀ i, A i ⊆ D) (hpos : Pairwise fun i j => E.PositivelySeparated s (A i) (A j))
    (f : Fin n → E.Carrier s → ℝ) (hf : ∀ i, f i ∈ E.testWithin s k (A i)) :
    E.IsSepTuple s k D f := by
  have h := (hp s E M univ D n hn).2.1.1 A hA hpos
  cases k
  · exact h.1 f hf
  · exact h.2 f hf
variable (s E k D n) in
structure FactorProduct where
  region : Fin n → Set (E.Carrier s)
  space : Fin n → Submodule ℝ (E.Carrier s → ℝ)
  coe_space : ∀ i, (space i : Set (E.Carrier s → ℝ)) = E.testWithin s k (region i)
  region_subset : ∀ i, region i ⊆ D
  region_pos : Pairwise fun i j => E.PositivelySeparated s (region i) (region j)
  sep : ∀ f : Fin n → E.Carrier s → ℝ, (∀ i, f i ∈ E.testWithin s k (region i)) →
    E.IsSepTuple s k D f
def mkFactorProduct (hp : testSpacesAndSepTuples) (M : SharpParameter) (hn : 1 ≤ n)
    (k : TestKind) (A : Fin n → Set (E.Carrier s))
    (W : Fin n → Submodule ℝ (E.Carrier s → ℝ))
    (hW : ∀ i, (W i : Set (E.Carrier s → ℝ)) = E.testWithin s k (A i)) (hA : ∀ i, A i ⊆ D)
    (hpos : Pairwise fun i j => E.PositivelySeparated s (A i) (A j)) : FactorProduct s E k D n :=
  ⟨A, W, hW, hA, hpos, isSepTuple_of_mem hp M hn k hA hpos⟩
namespace FactorProduct
theorem mem_testWithin (P : FactorProduct s E k D n) (h : ∀ i, P.space i) (i : Fin n) :
    (h i).1 ∈ E.testWithin s k (P.region i) := by
  rw [← P.coe_space]
  exact (h i).2
def toSepTuple (P : FactorProduct s E k D n) (h : ∀ i, P.space i) : E.SepTuple s k D n :=
  ⟨fun i => (h i).1, P.sep _ (P.mem_testWithin h)⟩
theorem form_update_linear (P : FactorProduct s E k D n) {Ψ : E.SepTuple s k D n → ℝ}
    (hΨ : E.IsMultilinearOn s Ψ) [DecidableEq (Fin n)] (m : ∀ i, P.space i) (i : Fin n)
    (x y : P.space i) (a b : ℝ) :
    Ψ (P.toSepTuple (Function.update m i (a • x + b • y))) =
      a * Ψ (P.toSepTuple (Function.update m i x)) +
        b * Ψ (P.toSepTuple (Function.update m i y)) := by
  refine hΨ P.region P.region_subset P.region_pos i a b _ _ _ (P.mem_testWithin _)
    (P.mem_testWithin _) (P.mem_testWithin _) ?_ ?_ ?_
  · intro j hj
    simp [toSepTuple, Function.update_of_ne hj]
  · intro j hj
    simp [toSepTuple, Function.update_of_ne hj]
  · simp [toSepTuple]
def toMultilinear (P : FactorProduct s E k D n) (Ψ : E.SepTuple s k D n → ℝ)
    (hΨ : E.IsMultilinearOn s Ψ) : MultilinearMap ℝ (fun i => P.space i) ℝ where
  toFun h := Ψ (P.toSepTuple h)
  map_update_add' := by
    intro _ m i x y
    simpa using P.form_update_linear hΨ m i x y 1 1
  map_update_smul' := by
    intro _ m i c x
    simpa using P.form_update_linear hΨ m i x x c 0
def restrictBlock (P : FactorProduct s E k D q) (hp : testSpacesAndSepTuples)
    (M : SharpParameter) (J : Finset (Fin q)) (hJ : 2 ≤ J.card) : FactorProduct s E k D J.card :=
  mkFactorProduct hp M (by omega) k (fun i => P.region (J.orderEmbOfFin rfl i))
    (fun i => P.space (J.orderEmbOfFin rfl i)) (fun _ => P.coe_space _)
    (fun _ => P.region_subset _)
    (fun _ _ hij => P.region_pos ((J.orderEmbOfFin rfl).injective.ne hij))
def blockMultilinear (P : FactorProduct s E k D q) (hp : testSpacesAndSepTuples)
    (M : SharpParameter) (Ψ : E.TupleFunctionals s k D)
    (hΨ : ∀ n hn, E.IsMultilinearOn s (Ψ n hn)) :
    Multilinear.BlockForms (fun l => P.space l) :=
  fun J hJ => (P.restrictBlock hp M J hJ).toMultilinear (Ψ J.card hJ) (hΨ _ _)
theorem partitionSum_eq_centredSum (P : FactorProduct s E k D q)
    (hp : testSpacesAndSepTuples) (M : SharpParameter)
    (Ψ : E.TupleFunctionals s k D) (hΨ : ∀ n hn, E.IsMultilinearOn s (Ψ n hn))
    (h : ∀ l, P.space l) :
    Multilinear.partitionSum (P.blockMultilinear hp M Ψ hΨ) h =
      E.centredSum s Ψ (P.toSepTuple h) :=
  rfl
end FactorProduct
theorem isMultilinearOn_of_multilinearMap (hp : testSpacesAndSepTuples)
    (M : SharpParameter) (hn : 1 ≤ n) (Ψ : E.SepTuple s k D n → ℝ)
    (h : ∀ P : FactorProduct s E k D n, ∃ F : MultilinearMap ℝ (fun i => P.space i) ℝ,
      ∀ x, F x = Ψ (P.toSepTuple x)) : E.IsMultilinearOn s Ψ := by
  classical
  intro A hA hpos i a b X Y Z hX hY hZ hYX hZX hZi
  choose W hW using fun l => exists_submodule_testWithin (E := E) (s := s) hp M k (A l)
  let P : FactorProduct s E k D n := mkFactorProduct hp M hn k A W hW hA hpos
  obtain ⟨F, hF⟩ := h P
  have mem : ∀ (T : E.SepTuple s k D n), (∀ l, T.1 l ∈ E.testWithin s k (A l)) →
      ∀ l, T.1 l ∈ P.space l := fun T hT l => by
    change T.1 l ∈ (W l : Set (E.Carrier s → ℝ))
    rw [hW]
    exact hT l
  let x : ∀ l, P.space l := fun l => ⟨X.1 l, mem X hX l⟩
  let y : ∀ l, P.space l := fun l => ⟨Y.1 l, mem Y hY l⟩
  have eX : P.toSepTuple x = X := Subtype.ext rfl
  have eY : P.toSepTuple (Function.update x i (y i)) = Y := by
    refine Subtype.ext (funext fun l => ?_)
    by_cases hl : l = i
    · subst hl
      simp [FactorProduct.toSepTuple, y]
    · simp [FactorProduct.toSepTuple, Function.update_of_ne hl, x, hYX l hl]
  have eZ : P.toSepTuple (Function.update x i (a • x i + b • y i)) = Z := by
    refine Subtype.ext (funext fun l => ?_)
    by_cases hl : l = i
    · subst hl
      simp [FactorProduct.toSepTuple, x, y, hZi]
    · simp [FactorProduct.toSepTuple, Function.update_of_ne hl, x, hZX l hl]
  rw [← eZ, ← hF, F.map_update_add, F.map_update_smul, F.map_update_smul, Function.update_eq_self,
    hF, hF, eX, eY]
  rfl
theorem isMultilinearOn_centredSum (hp : testSpacesAndSepTuples)
    (hf : Multilinear.BoundedMultilinearEstimates) (M : SharpParameter) (hq : 1 ≤ q)
    (Ψ : E.TupleFunctionals s k D) (hΨ : ∀ n hn, E.IsMultilinearOn s (Ψ n hn)) :
    E.IsMultilinearOn s (E.centredSum s Ψ (q := q)) := by
  refine isMultilinearOn_of_multilinearMap hp M hq _ fun P => ?_
  obtain ⟨F, hF⟩ := ((hf q hq (fun l => P.space l) fun _ => 0).2 (P.blockMultilinear hp M Ψ hΨ)).1
  exact ⟨F, fun x => (hF x).trans (P.partitionSum_eq_centredSum hp M Ψ hΨ x)⟩
namespace FactorProduct
def ofSepTuple (P : FactorProduct s E k D n) (T : E.SepTuple s k D n)
    (hT : ∀ l, T.1 l ∈ E.testWithin s k (P.region l)) : ∀ l, P.space l := fun l =>
  ⟨T.1 l, by
    change T.1 l ∈ (P.space l : Set (E.Carrier s → ℝ))
    rw [P.coe_space]
    exact hT l⟩
theorem toSepTuple_ofSepTuple (P : FactorProduct s E k D n) (T : E.SepTuple s k D n)
    (hT : ∀ l, T.1 l ∈ E.testWithin s k (P.region l)) : P.toSepTuple (P.ofSepTuple T hT) = T :=
  Subtype.ext rfl
end FactorProduct
def normSharpSeminorm (hp : testSpacesAndSepTuples) (M : SharpParameter)
    {A : Set (E.Carrier s)} {W : Submodule ℝ (E.Carrier s → ℝ)}
    (hW : (W : Set (E.Carrier s → ℝ)) ⊆ E.lipWithin s A) : Seminorm ℝ W where
  toFun f := E.normSharp s M f.1
  map_zero' := by
    have h := (hp s E M A univ 1 le_rfl).1.2.2.2.2.1.2.2.1 0 0 (hW W.zero_mem)
    simpa using h
  add_le' f g := (hp s E M A univ 1 le_rfl).1.2.2.2.2.1.2.2.2 _ (hW f.2) _ (hW g.2)
  neg' f := by
    have h := (hp s E M A univ 1 le_rfl).1.2.2.2.2.1.2.2.1 (-1) f.1 (hW f.2)
    simpa using h
  smul' a f := (hp s E M A univ 1 le_rfl).1.2.2.2.2.1.2.2.1 a f.1 (hW f.2)
theorem prod_comp_orderEmbOfFin (J : Finset (Fin q)) (g : Fin q → ℝ) :
    ∏ i, g (J.orderEmbOfFin rfl i) = ∏ l ∈ J, g l := by
  rw [← Finset.prod_coe_sort J g]
  exact Fintype.prod_equiv (J.orderIsoOfFin rfl).toEquiv _ _ fun _ => rfl
theorem finset_card_le (J : Finset (Fin q)) : J.card ≤ q := by
  simpa using J.card_le_univ
theorem partitionBound_nonneg {C : ℕ → ℝ} (hC : ∀ n, 2 ≤ n → n ≤ q → 0 ≤ C n) :
    0 ≤ Multilinear.partitionBound q C :=
  Finset.sum_nonneg fun _ hπ => Finset.prod_nonneg fun J hJ =>
    hC _ ((Finset.mem_filter.mp hπ).2 J hJ) (finset_card_le J)
theorem centredContinuousOnSets_of_boundedOnSets (hp : testSpacesAndSepTuples)
    (hf : Multilinear.BoundedMultilinearEstimates) (M : SharpParameter) (hq : 1 ≤ q)
    (Ψ : E.TupleFunctionals s k D) (hΨ : ∀ n hn, E.IsMultilinearOn s (Ψ n hn))
    {A : Fin q → Set (E.Carrier s)} (hA : ∀ l, A l ⊆ D)
    (hpos : Pairwise fun i j => E.PositivelySeparated s (A i) (A j)) {C : ℕ → ℝ}
    (hC : ∀ n, 2 ≤ n → n ≤ q → 0 ≤ C n) (hb : E.BoundedOnSets s M Ψ A C) :
    E.CentredContinuousOnSets s M Ψ A C := by
  intro f g hfA hgA
  choose W hW using fun l => exists_submodule_testWithin (E := E) (s := s) hp M k (A l)
  let P : FactorProduct s E k D q := mkFactorProduct hp M hq k A W hW hA hpos
  have hsub : ∀ l, (P.space l : Set (E.Carrier s → ℝ)) ⊆ E.lipWithin s (P.region l) :=
    fun l => by
      rw [P.coe_space]
      exact testWithin_subset_lipWithin hp M k _
  let nn : ∀ l, Seminorm ℝ (P.space l) := fun l => normSharpSeminorm hp M (hsub l)
  have H := hf q hq (fun l => P.space l) nn
  obtain ⟨F, hF⟩ := (H.2 (P.blockMultilinear hp M Ψ hΨ)).1
  have hbd := (H.2 (P.blockMultilinear hp M Ψ hΨ)).2 C hC (by
    intro J hJ h
    have h1 := hb J.card hJ (finset_card_le J) (J.orderEmbOfFin rfl)
      (J.orderEmbOfFin rfl).strictMono
      ((P.restrictBlock hp M J hJ).toSepTuple (Multilinear.restrictOrdered h J))
      (fun i => (P.restrictBlock hp M J hJ).mem_testWithin _ i)
    refine h1.trans_eq ?_
    congr 1
    exact prod_comp_orderEmbOfFin J fun l => E.normSharp s M (h l).1)
  have hfA' : ∀ l, f.1 l ∈ E.testWithin s k (P.region l) := hfA
  have hgA' : ∀ l, g.1 l ∈ E.testWithin s k (P.region l) := hgA
  have H1 := H.1 F _ (partitionBound_nonneg hC) (fun h => by rw [hF]; exact hbd h)
    (P.ofSepTuple f hfA') (P.ofSepTuple g hgA')
  rw [hF, hF, P.partitionSum_eq_centredSum hp M Ψ hΨ, P.partitionSum_eq_centredSum hp M Ψ hΨ,
    P.toSepTuple_ofSepTuple, P.toSepTuple_ofSepTuple] at H1
  exact H1.1.trans H1.2
section LimitSide
variable {𝒥 : Set ℕ+} {Dom : 𝒥 → Set (E.Carrier s)}
  {Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)}
theorem indexAtTop_neBot (h : 𝒥.Infinite) : (indexAtTop 𝒥).NeBot := by
  unfold indexAtTop
  rw [comap_neBot_iff]
  intro t ht
  obtain ⟨N, hN⟩ := mem_atTop_sets.mp ht
  obtain ⟨j, hj, hNj⟩ := h.exists_gt N
  exact ⟨⟨j, hj⟩, hN j hNj.le⟩
theorem infSetDist_anti {S S' T T' : Set (E.Carrier s)} (h : S ⊆ T) (h' : S' ⊆ T') :
    E.infSetDist s T T' ≤ E.infSetDist s S S' :=
  (biInf_mono h).trans (iInf₂_mono fun _ _ => biInf_mono h')
theorem isSepLipTuple_mono {D' : Set (E.Carrier s)} {f : Fin n → E.Carrier s → ℝ}
    (hf : E.IsSepLipTuple s D f) (h : ∀ i, E.closedSupport s (f i) ⊆ D') :
    E.IsSepLipTuple s D' f :=
  ⟨fun i => ⟨(hf.1 i).1, (hf.1 i).2.1, h i⟩, hf.2⟩
theorem eventually_isSepTuple (hp : testSpacesAndSepTuples) (M : SharpParameter)
    (hex : E.ExhaustsCompacts s Dom) (X : E.SepTupleUniv s .cOne n) :
    ∀ᶠ j in indexAtTop 𝒥, E.IsSepTuple s .lip (Dom j) X.1 := by
  have hc := (hp s E M univ univ 1 le_rfl).2.2.1.2.2.2 1 (fun _ => n) (fun _ => X.1)
    (fun _ => X.2.1)
  filter_upwards [hex _ hc] with j hj
  exact isSepLipTuple_mono X.2.1 fun i x hx =>
    hj (mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨i, hx⟩⟩)
theorem tendsto_evalOrZero (hH : E.LimitHypotheses s Φ) (n : ℕ) (hn : 2 ≤ n)
    (X : E.SepTupleUniv s .cOne n) :
    Tendsto (fun j => E.evalOrZero s (Φ j n hn) X.1) (indexAtTop 𝒥)
      (𝓝 (E.limitFunctionals s Φ n hn X)) :=
  have := indexAtTop_neBot hH.infinite_index
  tendsto_nhds_limUnder (hH.tendsto_exists n hn X)
theorem isMultilinearOn_limitFunctionals (hp : testSpacesAndSepTuples) (M : SharpParameter)
    (hH : E.LimitHypotheses s Φ) (n : ℕ) (hn : 2 ≤ n) :
    E.IsMultilinearOn s (E.limitFunctionals s Φ n hn) := by
  have := indexAtTop_neBot hH.infinite_index
  intro A hA hpos i a b X Y Z hX hY hZ hYX hZX hZi
  have mem : ∀ (j : 𝒥) (T : E.SepTupleUniv s .cOne n), E.IsSepTuple s .lip (Dom j) T.1 →
      (∀ l, T.1 l ∈ E.testWithin s .cOne (A l)) → ∀ l,
        T.1 l ∈ E.testWithin s .lip (A l ∩ Dom j) := fun j T hj hT l =>
    ⟨(hj.1 l).1, (hj.1 l).2.1, subset_inter (hT l).2.2 (hj.1 l).2.2⟩
  have key : ∀ᶠ j in indexAtTop 𝒥, E.evalOrZero s (Φ j n hn) Z.1 =
      a * E.evalOrZero s (Φ j n hn) X.1 + b * E.evalOrZero s (Φ j n hn) Y.1 := by
    filter_upwards [eventually_isSepTuple hp M hH.exhausts X,
      eventually_isSepTuple hp M hH.exhausts Y,
      eventually_isSepTuple hp M hH.exhausts Z] with j hXj hYj hZj
    rw [evalOrZero, evalOrZero, evalOrZero, dif_pos hXj, dif_pos hYj, dif_pos hZj]
    exact hH.multilinear j n hn (fun l => A l ∩ Dom j) (fun _ => inter_subset_right)
      (fun u v huv => lt_of_lt_of_le (hpos huv)
        (infSetDist_anti inter_subset_left inter_subset_left))
      i a b ⟨X.1, hXj⟩ ⟨Y.1, hYj⟩ ⟨Z.1, hZj⟩ (mem j X hXj hX) (mem j Y hYj hY) (mem j Z hZj hZ)
      hYX hZX hZi
  exact tendsto_nhds_unique (tendsto_evalOrZero hH n hn Z)
    ((((tendsto_evalOrZero hH n hn X).const_mul a).add
      ((tendsto_evalOrZero hH n hn Y).const_mul b)).congr' (EventuallyEq.symm key))
theorem isPermInvariant_limitFunctionals (hp : testSpacesAndSepTuples) (M : SharpParameter)
    (hH : E.LimitHypotheses s Φ) (n : ℕ) (hn : 2 ≤ n) :
    E.IsPermInvariant s (E.limitFunctionals s Φ n hn) := by
  have := indexAtTop_neBot hH.infinite_index
  intro X ς
  refine tendsto_nhds_unique (tendsto_evalOrZero hH n hn _)
    ((tendsto_evalOrZero hH n hn X).congr' ?_)
  filter_upwards [eventually_isSepTuple hp M hH.exhausts X] with j hj
  have hj' : E.IsSepTuple s .lip (Dom j) (E.permuteTuple s X ς).1 :=
    (E.permuteTuple s ⟨X.1, hj⟩ ς).2
  rw [evalOrZero, evalOrZero, dif_pos hj, dif_pos hj']
  exact (hH.perm_invariant j n hn ⟨X.1, hj⟩ ς).symm
theorem tendsto_evalOrZero_centredSum (hp : testSpacesAndSepTuples) (M : SharpParameter)
    (hH : E.LimitHypotheses s Φ) (q : ℕ) (Y : E.SepTupleUniv s .cOne q) :
    Tendsto (fun j => E.evalOrZero s (E.centredSum s (Φ j) (q := q)) Y.1)
      (indexAtTop 𝒥) (𝓝 (E.centredSum s (E.limitFunctionals s Φ) Y)) := by
  have e : ∀ᶠ j in indexAtTop 𝒥,
      (∑ π ∈ (SetPartition.nonSingletonPartitions q).attach, ∏ J ∈ π.1.parts.attach,
        E.evalOrZero s (Φ j J.1.card (two_le_card_of_mem_nonSingleton π J))
          (E.restrictTuple s Y J.1).1) =
      E.evalOrZero s (E.centredSum s (Φ j) (q := q)) Y.1 := by
    filter_upwards [eventually_isSepTuple hp M hH.exhausts Y] with j hj
    rw [evalOrZero, dif_pos hj]
    refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => ?_
    have hh : E.IsSepTuple s .lip (Dom j) (E.restrictTuple s Y J.1).1 :=
      (E.restrictTuple s ⟨Y.1, hj⟩ J.1).2
    rw [evalOrZero, dif_pos hh]
    rfl
  refine Tendsto.congr' e ?_
  exact tendsto_finsetSum _ fun π _ => tendsto_finsetProd _ fun J _ => tendsto_evalOrZero hH _ _ _
theorem closedRelationsPersist (hH : E.LimitHypotheses s Φ) : E.ClosedRelationsPersist s Φ := by
  have := indexAtTop_neBot hH.infinite_index
  intro r _ length hlength X
  have ht : Tendsto (E.valuesVec s Φ length hlength X) (indexAtTop 𝒥)
      (𝓝 (E.limitsVec s Φ length hlength X)) :=
    tendsto_pi_nhds.mpr fun i => tendsto_evalOrZero hH _ _ _
  refine ⟨fun F hF h => hF.mem_of_tendsto ht h, fun g hg h => ?_⟩
  exact (isClosed_singleton.preimage hg).mem_of_tendsto ht h
theorem boundsPersist (hH : E.LimitHypotheses s Φ) : E.BoundsPersist s Φ := by
  have := indexAtTop_neBot hH.infinite_index
  intro n hn X b h
  exact le_of_tendsto (tendsto_evalOrZero hH n hn X).abs h
theorem positivityPersists (hp : testSpacesAndSepTuples) (M : SharpParameter)
    (hH : E.LimitHypotheses s Φ) : E.PositivityPersists s Φ := by
  have := indexAtTop_neBot hH.infinite_index
  intro t _ ζ length Y h
  have hc : IsClosed (Complex.ofReal '' Ici (0 : ℝ)) :=
    Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ isClosed_Ici
  refine hc.mem_of_tendsto ?_ h
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun i' _ => ?_
  exact ((Complex.continuous_ofReal.tendsto _).comp
    (tendsto_evalOrZero_centredSum hp M hH _ (Y i i'))).const_mul _
theorem boundedOnSets_limitFunctionals (hp : testSpacesAndSepTuples) (M : SharpParameter)
    (hH : E.LimitHypotheses s Φ) {A : Fin q → Set (E.Carrier s)} {C : ℕ → ℝ}
    (hb : ∀ᶠ j in indexAtTop 𝒥, (∀ l, A l ⊆ Dom j) ∧ E.BoundedOnSets s M (Φ j) A C) :
    E.BoundedOnSets s M (E.limitFunctionals s Φ) A C := by
  intro n hn hnq l hl h hhA
  refine boundsPersist hH n hn h _ ?_
  filter_upwards [hb] with j hj
  have hjt : E.IsSepTuple s .lip (Dom j) h.1 :=
    isSepLipTuple_mono h.2.1 fun i => (hhA i).2.2.trans (hj.1 _)
  rw [evalOrZero, dif_pos hjt]
  exact hj.2 n hn hnq l hl ⟨h.1, hjt⟩ fun i => testWithin_subset_lipWithin hp M .cOne _ (hhA i)
theorem positivelySeparated_of_pairwiseSeparatedBy {A : Fin q → Set (E.Carrier s)} {d : ℝ}
    (hd : 0 < d) (h : E.PairwiseSeparatedBy s d A) :
    Pairwise fun i j => E.PositivelySeparated s (A i) (A j) :=
  fun i j hij => lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hd) (h i j hij)
theorem equicontinuityPersists (hp : testSpacesAndSepTuples)
    (hf : Multilinear.BoundedMultilinearEstimates) (M : SharpParameter)
    (hH : E.LimitHypotheses s Φ) : E.EquicontinuityPersists s M Φ := by
  intro q hq d hd C hC
  refine ⟨fun j A hA hdist hb => centredContinuousOnSets_of_boundedOnSets hp hf M (by omega) (Φ j)
      (fun n hn => hH.multilinear j n hn) hA (positivelySeparated_of_pairwiseSeparatedBy hd hdist)
      hC hb, ?_,
    fun A hdist => ⟨fun hb => centredContinuousOnSets_of_boundedOnSets hp hf M (by omega) _
      (fun n hn => isMultilinearOn_limitFunctionals hp M hH n hn) (fun _ => subset_univ _)
      (positivelySeparated_of_pairwiseSeparatedBy hd hdist) hC hb,
      boundedOnSets_limitFunctionals hp M hH⟩⟩
  intro C' hC'
  exact Finset.sum_congr rfl fun π hπ => Finset.prod_congr rfl fun J hJ =>
    hC' _ ((Finset.mem_filter.mp hπ).2 J hJ) (finset_card_le J)
theorem approximatingTuplesConverge (hp : testSpacesAndSepTuples)
    (hf : Multilinear.BoundedMultilinearEstimates) (M : SharpParameter)
    (hH : E.LimitHypotheses s Φ) : E.ApproximatingTuplesConverge s M Φ := by
  have := indexAtTop_neBot hH.infinite_index
  intro q hq d hd C hC A hdist hb h moving hh hm ht
  have hpos := positivelySeparated_of_pairwiseSeparatedBy hd hdist
  have hlip : ∀ l, h.1 l ∈ E.lipWithin s (A l) :=
    fun l => testWithin_subset_lipWithin hp M .cOne _ (hh l)
  have hU : Tendsto (fun j => partitionConstant q C * ∑ l,
      E.normSharp s M (moving j l - h.1 l) * ∏ l' ∈ Finset.univ.erase l,
        (E.normSharp s M (moving j l' - h.1 l') + 2 * E.normSharp s M (h.1 l')))
      (indexAtTop 𝒥) (𝓝 0) := by
    have h0 := (tendsto_finsetSum (Finset.univ : Finset (Fin q)) fun l _ =>
      (ht l).mul (tendsto_finsetProd (Finset.univ.erase l) fun l' _ =>
        (ht l').add (tendsto_const_nhds (x := 2 * E.normSharp s M (h.1 l'))))).const_mul
      (partitionConstant q C)
    simpa using h0
  have hdiff : ∀ᶠ j in indexAtTop 𝒥,
      ‖E.evalOrZero s (E.centredSum s (Φ j) (q := q)) (moving j) -
        E.evalOrZero s (E.centredSum s (Φ j) (q := q)) h.1‖ ≤
      partitionConstant q C * ∑ l,
      E.normSharp s M (moving j l - h.1 l) * ∏ l' ∈ Finset.univ.erase l,
        (E.normSharp s M (moving j l' - h.1 l') + 2 * E.normSharp s M (h.1 l')) := by
    filter_upwards [hb] with j hj
    have hmj : E.IsSepTuple s .lip (Dom j) (moving j) :=
      isSepTuple_of_mem hp M (by omega) .lip hj.1 hpos _ (hm j)
    have hhj : E.IsSepTuple s .lip (Dom j) h.1 :=
      isSepTuple_of_mem hp M (by omega) .lip hj.1 hpos _ hlip
    rw [evalOrZero, evalOrZero, dif_pos hmj, dif_pos hhj, Real.norm_eq_abs]
    have e := centredContinuousOnSets_of_boundedOnSets hp hf M (by omega) (Φ j)
      (fun n hn => hH.multilinear j n hn) hj.1 hpos hC hj.2 ⟨moving j, hmj⟩ ⟨h.1, hhj⟩ (hm j) hlip
    refine e.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_)
      (partitionBound_nonneg hC))
    have hN := fun l => (hp s E M (A l) univ 1 le_rfl).1.2.2.2.2.1
    have hsubm : ∀ l, moving j l - h.1 l ∈ E.lipWithin s (A l) := fun l => by
      obtain ⟨W, hW⟩ := (hp s E M (A l) univ 1 le_rfl).1.1
      have h1 : moving j l ∈ (W : Set (E.Carrier s → ℝ)) := by
        rw [hW]
        exact hm j l
      have h2 : h.1 l ∈ (W : Set (E.Carrier s → ℝ)) := by
        rw [hW]
        exact hlip l
      have h3 : moving j l - h.1 l ∈ (W : Set (E.Carrier s → ℝ)) := W.sub_mem h1 h2
      rwa [hW] at h3
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun l' _ => ?_) (fun l' _ => ?_))
      ((hN l).1 _ (hsubm l))
    · exact add_nonneg ((hN l').1 _ (hm j l')) ((hN l').1 _ (hlip l'))
    · have h1 := (hN l').2.2.2 _ (hsubm l') _ (hlip l')
      rw [sub_add_cancel] at h1
      linarith
  have h0 : Tendsto (fun j => E.evalOrZero s (E.centredSum s (Φ j) (q := q)) (moving j) -
      E.evalOrZero s (E.centredSum s (Φ j) (q := q)) h.1) (indexAtTop 𝒥) (𝓝 0) :=
    squeeze_zero_norm' hdiff hU
  simpa using h0.add (tendsto_evalOrZero_centredSum hp M hH q h)
end LimitSide
theorem exhaustsCompacts_of_eq_univ {𝒥 : Set ℕ+} {Dom : 𝒥 → Set (E.Carrier s)}
    (h : ∀ j, Dom j = univ) : E.ExhaustsCompacts s Dom :=
  fun _ _ => Eventually.of_forall fun j => by
    rw [h]
    exact subset_univ _
theorem exhaustsCompacts_of_lengthBall (hs : AmbientMetric.Claim) {𝒥 : Set ℕ+} {ρ : 𝒥 → ℝ≥0∞}
    {Dom : 𝒥 → Set (E.Carrier s)} (hρ : Tendsto ρ (indexAtTop 𝒥) (𝓝 ⊤))
    (h : ∀ j, Dom j = E.lengthBallLT s (ρ j)) : E.ExhaustsCompacts s Dom := by
  intro C hC
  have hd := (hs s E).1.2.1
  let ball : ℕ → Set (E.Carrier s) := fun m => {y | E.pointDist s y 0 < m}
  obtain ⟨𝒰, hsub, hfin, hcov⟩ := hC (range ball) (by
      rintro _ ⟨m, rfl⟩ x hx
      refine ⟨m - E.pointDist s x 0, sub_pos.mpr hx, fun y hy => ?_⟩
      have h1 := hd.triangle y x 0
      rw [hd.symm y x] at h1
      change E.pointDist s y 0 < m
      linarith) (fun y _ => by
      obtain ⟨m, hm⟩ := exists_nat_gt (E.pointDist s y 0)
      exact ⟨ball m, ⟨m, rfl⟩, hm⟩)
  have hm : ∀ U ∈ 𝒰, ∃ m : ℕ, ball m = U := hsub
  choose! m hm using hm
  obtain ⟨R, hR⟩ := (hfin.image m).bddAbove
  filter_upwards [hρ.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top (r := R)))] with j hj y hy
  obtain ⟨U, hU, hyU⟩ := hcov hy
  rw [← hm U hU] at hyU
  have h1 : E.pointDist s y 0 < m U := hyU
  have h2 : m U ≤ R := hR (mem_image_of_mem m hU)
  have h3 : E.euclidLength s y < R :=
    lt_of_lt_of_le (by simpa [Ambient.pointDist] using h1) (by exact_mod_cast h2)
  rw [h]
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal h3.le) hj
theorem tensor_relation_of_factorProduct (hrel : TensorRelationsTransfer) (hq : 1 ≤ q)
    {Ψ : E.SepTuple s .cOne D q → ℝ} (hΨ : E.IsMultilinearOn s Ψ)
    (P : FactorProduct s E .cOne D q) {Idx : Type} [Fintype Idx] (c : Idx → ℝ)
    (f : Idx → E.SepTuple s .cOne D q)
    (hf : ∀ p l, (f p).1 l ∈ E.testWithin s .cOne (P.region l))
    (hr : ∀ x, ∑ p, c p * E.tensorProd s (fun l => (f p).1 l) x = 0) :
    ∑ p, c p * Ψ (f p) = 0 := by
  have h := hrel s E q hq (fun l => P.space l) (P.toMultilinear Ψ hΨ) Idx c
    (fun p => P.ofSepTuple (f p) (hf p)) hr
  have e : ∀ p, (P.toMultilinear Ψ hΨ) (P.ofSepTuple (f p) (hf p)) = Ψ (f p) := fun p => by
    change Ψ (P.toSepTuple _) = _
    rw [P.toSepTuple_ofSepTuple]
  simpa only [e] using h
theorem mem_closedSupport_of_ne_zero (hs : AmbientMetric.Claim) {f : E.Carrier s → ℝ}
    {x : E.Carrier s} (h : f x ≠ 0) : x ∈ E.closedSupport s f := fun r hr =>
  ⟨x, h, by
    rw [((hs s E).1.2.1.eq_zero_iff x x).mpr rfl]
    exact hr⟩
theorem exists_pos_le_pointDist (hs : AmbientMetric.Claim) {S S' : Set (E.Carrier s)}
    (h : E.PositivelySeparated s S S') :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ y ∈ S', δ ≤ E.pointDist s x y := by
  have hd := (hs s E).1.2.1
  refine ⟨(min (E.infSetDist s S S') 1).toReal,
    ENNReal.toReal_pos (lt_min h one_pos).ne'
      ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne, fun x hx y hy => ?_⟩
  refine ENNReal.toReal_le_of_le_ofReal (hd.nonneg x y) ((min_le_left _ _).trans ?_)
  unfold infSetDist
  exact iInf₂_le_of_le x hx (iInf₂_le y hy)
theorem exists_pos_uniform {T : Type*} [Finite T] (Q : T → ℝ → Prop)
    (hanti : ∀ t a b, a ≤ b → Q t b → Q t a) (h : ∀ t, ∃ δ : ℝ, 0 < δ ∧ Q t δ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, Q t δ := by
  choose d hd hQ using h
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨1, one_pos, fun t => (hT.false t).elim⟩
  · obtain ⟨t0, ht0⟩ := Finite.exists_min d
    exact ⟨d t0, hd t0, fun t => hanti t _ _ (ht0 t) (hQ t)⟩
theorem real_tensor_relation (hp : testSpacesAndSepTuples)
    (hrel : TensorRelationsTransfer)
    (hunity : FinePartitionOfUnity.Claim)
    (hs : AmbientMetric.Claim) (M : SharpParameter) (hq : 1 ≤ q)
    {Ψ : E.SepTuple s .cOne D q → ℝ} (hΨ : E.IsMultilinearOn s Ψ)
    {Idx : Type} [Fintype Idx] (c : Idx → ℝ) (f : Idx → E.SepTuple s .cOne D q)
    (hr : ∀ x, ∑ p, c p * E.tensorProd s (fun l => (f p).1 l) x = 0) :
    ∑ p, c p * Ψ (f p) = 0 := by
  classical
  have hd := (hs s E).1.2.1
  let S : Idx → Fin q → Set (E.Carrier s) := fun p l => E.closedSupport s ((f p).1 l)
  have hSc : ∀ p l, E.IsCompactSubset s (S p l) := fun p l => ((f p).2.1.1 l).2.1
  have hSD : ∀ p l, S p l ⊆ D := fun p l => ((f p).2.1.1 l).2.2
  have hSpos : ∀ p, Pairwise fun l l' => E.PositivelySeparated s (S p l) (S p l') :=
    fun p => ((hp s E M univ D q hq).2.1.2.1 _ (f p).2.1).2.1
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_uniform (T := Idx × Fin q × Fin q)
    (fun t a => t.2.1 ≠ t.2.2 → ∀ x ∈ S t.1 t.2.1, ∀ y ∈ S t.1 t.2.2, a ≤ E.pointDist s x y)
    (fun t a b hab h hne x hx y hy => hab.trans (h hne x hx y hy))
    (fun t => by
      by_cases hne : t.2.1 = t.2.2
      · exact ⟨1, one_pos, fun h => (h hne).elim⟩
      · obtain ⟨a, ha, h⟩ := exists_pos_le_pointDist hs (hSpos t.1 hne)
        exact ⟨a, ha, fun _ => h⟩)
  obtain ⟨I, ψ, hψ⟩ := hunity s E (δ / 3) (by positivity)
  have hfin : (⋃ p, ⋃ l, {ν | (S p l ∩ E.closedSupport s (ψ ν)).Nonempty}).Finite :=
    Set.finite_iUnion fun p => Set.finite_iUnion fun l => hψ.locallyFinite_compact _ (hSc p l)
  let I₀ : Finset I := hfin.toFinset
  have hI₀ : ∀ {p l ν}, (S p l ∩ E.closedSupport s (ψ ν)).Nonempty → ν ∈ I₀ := fun {p l ν} h =>
    hfin.mem_toFinset.mpr (mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨l, h⟩⟩)
  have hpiece : ∀ ν p l, (fun x => ψ ν x * (f p).1 l x) ∈ E.c1Compact s ∧
      E.closedSupport s (fun x => ψ ν x * (f p).1 l x) ⊆ E.closedSupport s (ψ ν) ∩ S p l :=
    fun ν p l => by
    have h := (hs s E).2.2.2.1 _ ((f p).2.2 l) _ ((f p).2.2 l) 0 0 (ψ ν)
      (hψ.mem_c1Compact ν).1
    exact ⟨h.2.2.2.1, h.2.2.2.2⟩
  have hpt : ∀ p l x, (f p).1 l x = ∑ ν ∈ I₀, ψ ν x * (f p).1 l x := fun p l x => by
    by_cases h0 : (f p).1 l x = 0
    · simp [h0]
    · have hx : x ∈ S p l := mem_closedSupport_of_ne_zero hs h0
      have h1 : ∑ ν ∈ I₀, ψ ν x = 1 := by
        rw [← hψ.finsum_eq_one x]
        refine (finsum_eq_sum_of_support_subset _ ?_).symm
        intro ν hν
        exact Finset.mem_coe.mpr (hI₀ ⟨x, hx, mem_closedSupport_of_ne_zero hs hν⟩)
      rw [← Finset.sum_mul, h1, one_mul]
  choose W hW using fun (p : Idx) (l : Fin q) =>
    exists_submodule_testWithin (E := E) (s := s) hp M .cOne (S p l)
  let P : ∀ p, FactorProduct s E .cOne D q := fun p =>
    mkFactorProduct hp M hq .cOne (S p) (W p) (hW p) (hSD p) (hSpos p)
  have hmem : ∀ ν p l, (fun x => ψ ν x * (f p).1 l x) ∈ E.testWithin s .cOne ((P p).region l) :=
    fun ν p l => ⟨(hpiece ν p l).1, (hpiece ν p l).1.2, fun y hy => ((hpiece ν p l).2 hy).2⟩
  let cut : ∀ (p : Idx) (ν : Fin q → I₀), E.SepTuple s .cOne D q := fun p ν =>
    ⟨fun l x => ψ (ν l).1 x * (f p).1 l x, (P p).sep _ fun l => hmem (ν l).1 p l⟩
  have hexp : ∀ p, Ψ (f p) = ∑ ν : Fin q → I₀, Ψ (cut p ν) := fun p => by
    have hfp : ∀ l, (f p).1 l ∈ E.testWithin s .cOne ((P p).region l) :=
      fun l => ⟨(f p).2.2 l, ((f p).2.1.1 l).2.1, subset_rfl⟩
    let g : ∀ l, I₀ → (P p).space l := fun l a =>
      (P p).ofSepTuple ⟨fun l' x => ψ a.1 x * (f p).1 l' x,
        (P p).sep _ fun l' => hmem a.1 p l'⟩ (fun l' => hmem a.1 p l') l
    have hsum : (P p).ofSepTuple (f p) hfp = fun l => ∑ a, g l a := by
      refine funext fun l => Subtype.ext (funext fun x => ?_)
      refine (hpt p l x).trans ?_
      rw [Submodule.coe_sum, Finset.sum_apply]
      exact (Finset.sum_coe_sort I₀ fun ν => ψ ν x * (f p).1 l x).symm
    have h := ((P p).toMultilinear Ψ hΨ).map_sum g
    rw [← hsum] at h
    have e1 : ((P p).toMultilinear Ψ hΨ) ((P p).ofSepTuple (f p) hfp) = Ψ (f p) := by
      change Ψ ((P p).toSepTuple _) = _
      rw [(P p).toSepTuple_ofSepTuple]
    rw [e1] at h
    exact h
  have hdiam : ∀ ν x y, x ∈ E.closedSupport s (ψ ν) → y ∈ E.closedSupport s (ψ ν) →
      E.pointDist s x y ≤ δ / 3 := fun ν x y hx hy => by
    have h1 : ENNReal.ofReal (E.pointDist s x y) ≤ E.setDiam s (E.closedSupport s (ψ ν)) := by
      unfold setDiam
      exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      (h1.trans (hψ.setDiam_closedSupport_le ν))
  have hzero : ∀ (p : Idx) (ν : Fin q → I₀) (l : Fin q),
      ¬ (S p l ∩ E.closedSupport s (ψ (ν l).1)).Nonempty → Ψ (cut p ν) = 0 := fun p ν l h => by
    refine (hp s E M univ D q hq).2.2.2.2 .cOne Ψ hΨ (cut p ν) l (funext fun x => ?_)
    by_contra hne
    have hne' : ψ (ν l).1 x * (f p).1 l x ≠ 0 := hne
    exact h ⟨x, mem_closedSupport_of_ne_zero hs (right_ne_zero_of_mul hne'),
      mem_closedSupport_of_ne_zero hs (left_ne_zero_of_mul hne')⟩
  have hz : ∀ ν : Fin q → I₀, ∑ p, c p * Ψ (cut p ν) = 0 := by
    intro ν
    let Qs : Fin q → Set (E.Carrier s) := fun l => E.closedSupport s (ψ (ν l).1)
    have hQc : ∀ l, E.IsCompactSubset s (Qs l) := fun l => (hψ.mem_c1Compact _).2
    by_cases hdis : Pairwise fun l l' => Disjoint (Qs l) (Qs l')
    · choose W' hW' using fun l =>
        exists_submodule_testWithin (E := E) (s := s) hp M .cOne (D ∩ Qs l)
      let R : FactorProduct s E .cOne D q := mkFactorProduct hp M hq .cOne (fun l => D ∩ Qs l) W' hW'
        (fun _ => inter_subset_left)
        (fun l l' h => lt_of_lt_of_le ((hs s E).2.1.1 _ _ (hQc l) (hQc l') (hdis h))
          (infSetDist_anti inter_subset_right inter_subset_right))
      refine tensor_relation_of_factorProduct hrel hq hΨ R c (fun p => cut p ν) (fun p l => ?_)
        (fun x => ?_)
      · have h := hpiece (ν l).1 p l
        exact ⟨h.1, h.1.2, fun y hy => ⟨hSD p l (h.2 hy).2, (h.2 hy).1⟩⟩
      · have e : ∀ p, E.tensorProd s (fun l => (cut p ν).1 l) x =
            (∏ l, ψ (ν l).1 (x l)) * E.tensorProd s (fun l => (f p).1 l) x := fun p => by
          simp only [tensorProd, cut, Finset.prod_mul_distrib]
        simp only [e]
        calc ∑ p, c p * ((∏ l, ψ (ν l).1 (x l)) * E.tensorProd s (fun l => (f p).1 l) x)
            = (∏ l, ψ (ν l).1 (x l)) * ∑ p, c p * E.tensorProd s (fun l => (f p).1 l) x := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun p _ => by ring
          _ = 0 := by rw [hr x, mul_zero]
    · simp only [Pairwise, not_forall] at hdis
      obtain ⟨l, l', hne, hnd⟩ := hdis
      obtain ⟨z, hz1, hz2⟩ := Set.not_disjoint_iff.mp hnd
      refine Finset.sum_eq_zero fun p _ => ?_
      have key : Ψ (cut p ν) = 0 := by
        by_cases h1 : (S p l ∩ Qs l).Nonempty
        · by_cases h2 : (S p l' ∩ Qs l').Nonempty
          · obtain ⟨x, hxS, hxQ⟩ := h1
            obtain ⟨y, hyS, hyQ⟩ := h2
            have a1 := hsep (p, l, l') hne x hxS y hyS
            have a2 := hdiam _ x z hxQ hz1
            have a3 := hdiam _ z y hz2 hyQ
            have a4 := hd.triangle x z y
            linarith
          · exact hzero p ν l' h2
        · exact hzero p ν l h1
      rw [key, mul_zero]
  calc ∑ p, c p * Ψ (f p) = ∑ p, ∑ ν : Fin q → I₀, c p * Ψ (cut p ν) :=
        Finset.sum_congr rfl fun p _ => by rw [hexp p, Finset.mul_sum]
    _ = ∑ ν : Fin q → I₀, ∑ p, c p * Ψ (cut p ν) := Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun ν _ => hz ν
theorem complexTensorProd_apply (f : Fin q → E.Carrier s → ℝ) (x : Fin q → E.Carrier s) :
    E.complexTensorProd s f x = ((E.tensorProd s f x : ℝ) : ℂ) := by
  simp [complexTensorProd, tensorProd]
theorem complex_tensor_relation (hp : testSpacesAndSepTuples)
    (hrel : TensorRelationsTransfer)
    (hunity : FinePartitionOfUnity.Claim)
    (hs : AmbientMetric.Claim) (M : SharpParameter) (hq : 1 ≤ q)
    {Ψ : E.SepTuple s .cOne D q → ℝ} (hΨ : E.IsMultilinearOn s Ψ)
    (Idx : Type) [Fintype Idx] (ζ : Idx → ℂ) (f : Idx → E.SepTuple s .cOne D q)
    (h : ∑ p, ζ p • E.complexTensorProd s (f p).1 = 0) :
    ∑ p, ζ p * ((Ψ (f p) : ℝ) : ℂ) = 0 := by
  have hx : ∀ x, ∑ p, ζ p * ((E.tensorProd s (f p).1 x : ℝ) : ℂ) = 0 := fun x => by
    have h1 := congrFun h x
    simpa [Finset.sum_apply, complexTensorProd_apply] using h1
  have hre : ∑ p, (ζ p).re * Ψ (f p) = 0 :=
    real_tensor_relation hp hrel hunity hs M hq hΨ _ f fun x => by
      have h1 := congrArg Complex.re (hx x)
      simpa [Complex.re_sum] using h1
  have him : ∑ p, (ζ p).im * Ψ (f p) = 0 :=
    real_tensor_relation hp hrel hunity hs M hq hΨ _ f fun x => by
      have h1 := congrArg Complex.im (hx x)
      simpa [Complex.im_sum] using h1
  apply Complex.ext
  · simpa [Complex.re_sum] using hre
  · simpa [Complex.im_sum] using him
theorem linearMap_span_ext {ι X : Type*} [AddCommGroup X] [Module ℂ X] (v : ι → X)
    (g h : Submodule.span ℂ (range v) →ₗ[ℂ] ℂ)
    (H : ∀ i, g ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ = h ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩) :
    g = h := by
  apply LinearMap.ext
  rintro ⟨y, hy⟩
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact H i
  | zero =>
    change g 0 = h 0
    rw [map_zero, map_zero]
  | add x y hx hy ihx ihy =>
    change g (⟨x, hx⟩ + ⟨y, hy⟩) = h (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, ihx, ihy]
  | smul a x hx ih =>
    change g (a • ⟨x, hx⟩) = h (a • ⟨x, hx⟩)
    rw [map_smul, map_smul, ih]
theorem existsUnique_linearMap_span {ι X : Type*} [AddCommGroup X] [Module ℂ X] (v : ι → X)
    (u : ι → ℂ)
    (hker : ∀ a : ι →₀ ℂ, Finsupp.linearCombination ℂ v a = 0 →
      Finsupp.linearCombination ℂ u a = 0) :
    ∃! form : Submodule.span ℂ (range v) →ₗ[ℂ] ℂ,
      ∀ i, form ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ = u i := by
  classical
  let T := Finsupp.linearCombination ℂ v
  let U := Finsupp.linearCombination ℂ u
  have hk : LinearMap.ker T ≤ LinearMap.ker U := fun a ha =>
    LinearMap.mem_ker.mpr (hker a (LinearMap.mem_ker.mp ha))
  have hle : Submodule.span ℂ (range v) ≤ LinearMap.range T := by
    rw [Finsupp.range_linearCombination]
  let form : Submodule.span ℂ (range v) →ₗ[ℂ] ℂ :=
    ((LinearMap.ker T).liftQ U hk) ∘ₗ T.quotKerEquivRange.symm.toLinearMap ∘ₗ
      Submodule.inclusion hle
  have hform : ∀ i, form ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ = u i := fun i => by
    have e : Submodule.inclusion hle ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ =
        T.quotKerEquivRange (Submodule.Quotient.mk (Finsupp.single i 1)) :=
      Subtype.ext (by simp [T])
    simp only [form, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
    simp [U]
  exact ⟨form, hform, fun form' h' =>
    linearMap_span_ext v form' form fun i => (h' i).trans (hform i).symm⟩
theorem factorsThroughTensorSpan (hp : testSpacesAndSepTuples)
    (hrel : TensorRelationsTransfer)
    (hunity : FinePartitionOfUnity.Claim)
    (hs : AmbientMetric.Claim) (M : SharpParameter) (hq : 1 ≤ q)
    {Ψ : E.SepTuple s .cOne D q → ℝ} (hΨ : E.IsMultilinearOn s Ψ) :
    E.FactorsThroughTensorSpan s Ψ := by
  classical
  have hR := complex_tensor_relation hp hrel hunity hs M hq hΨ
  refine ⟨hR, ?_⟩
  refine existsUnique_linearMap_span (fun f : E.SepTuple s .cOne D q => E.complexTensorProd s f.1)
    (fun f => ((Ψ f : ℝ) : ℂ)) fun a ha => ?_
  have h1 : ∑ p : a.support, a p.1 • E.complexTensorProd s p.1.1 = 0 := by
    rw [Finset.sum_coe_sort a.support fun i => a i • E.complexTensorProd s i.1]
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at ha
    exact ha
  have h2 := hR a.support (fun p => a p.1) (fun p => p.1) h1
  rw [Finset.sum_coe_sort a.support fun i => a i * ((Ψ i : ℝ) : ℂ)] at h2
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact h2
theorem limitPassage_holds (hp : testSpacesAndSepTuples)
    (hf : Multilinear.BoundedMultilinearEstimates)
    (hrel : TensorRelationsTransfer)
    (hunity : FinePartitionOfUnity.Claim)
    (hs : AmbientMetric.Claim) : limitPassageStatement := by
  intro s E M
  refine ⟨fun q hq D Ψ hΨ => factorsThroughTensorSpan hp hrel hunity hs M hq hΨ,
    fun 𝒥 _ => ⟨fun Dom h => exhaustsCompacts_of_eq_univ h,
      fun ρ Dom _ hρ h => exhaustsCompacts_of_lengthBall hs hρ h⟩,
    fun 𝒥 Dom Φ hH => ?_⟩
  have hL : ∀ n hn, E.IsMultilinearOn s (E.limitFunctionals s Φ n hn) :=
    fun n hn => isMultilinearOn_limitFunctionals hp M hH n hn
  exact ⟨fun n X => eventually_isSepTuple hp M hH.exhausts X,
    ⟨fun n hn => ⟨hL n hn, isPermInvariant_limitFunctionals hp M hH n hn⟩,
      fun j q hq => isMultilinearOn_centredSum hp hf M hq _ fun n hn => hH.multilinear j n hn,
      fun q hq => isMultilinearOn_centredSum hp hf M hq _ hL,
      fun q Y => ⟨eventually_isSepTuple hp M hH.exhausts Y,
        tendsto_evalOrZero_centredSum hp M hH q Y⟩⟩,
    closedRelationsPersist hH, boundsPersist hH, positivityPersists hp M hH,
    equicontinuityPersists hp hf M hH, approximatingTuplesConverge hp hf M hH,
    fun q hq => factorsThroughTensorSpan hp hrel hunity hs M hq
      (isMultilinearOn_centredSum hp hf M hq _ hL)⟩
end YangMills.Construction.LimitSpaces.Ambient.LimitPassage
end
