import YangMills.Construction.EuclideanFunctionals.CentredFunctionalSeesTensorComponentsOnly
import YangMills.Construction.EuclideanFunctionals.InvarianceOfTheMomentsAndReductionToTheTimePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror RealPlane
namespace EuclideanFunctionals.MomentSymmetry
def partitionSum (S : ConnFamily) {n : ℕ} (f : Fin n → R4 → ℝ) : ℝ :=
  ∑ π ∈ SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts,
    Ambient.ConnectedFamily.evalAt S J.card
      (List.ofFn fun k => f (J.orderEmbOfFin rfl k))
theorem partitionSum_congr (S : ConnFamily) {m n : ℕ} (e : m = n) (g : Fin m → R4 → ℝ)
    (f : Fin n → R4 → ℝ) (h : ∀ i, g i = f (Fin.cast e i)) :
    partitionSum S g = partitionSum S f := by
  subst e
  have : g = f := funext fun i => h i
  rw [this]
theorem centeredFn_eq_partitionSum (S : ConnFamily) (X : sepAll) :
    centeredFn S X = partitionSum S X.1.get := rfl
theorem centeredFnFree_toFree (S : ConnFamily) {Y : FnList} (hY : Y ∈ sepAll) :
    centeredFnFree S (toFree Y) = (centeredFn S ⟨Y, hY⟩ : ℂ) :=
  liftLin_toFree _ ⟨Y, hY⟩
theorem centeredFn_ofFn (S : ConnFamily) {n : ℕ} (f : Fin n → R4 → ℝ)
    (hf : List.ofFn f ∈ sepAll) :
    centeredFn S ⟨List.ofFn f, hf⟩ = partitionSum S f := by
  rw [centeredFn_eq_partitionSum]
  exact partitionSum_congr S List.length_ofFn _ _ fun i => by
    simp
    rfl
theorem ofFn_mem_sepN_iff {n : ℕ} {f : Fin n → R4 → ℝ} :
    List.ofFn f ∈ sepN n ↔
      (∀ i, f i ∈ C1c ℝ) ∧
        Pairwise fun i j => Disjoint (supp (f i)) (supp (f j)) := by
  constructor
  · rintro ⟨-, hc, hd⟩
    refine ⟨fun i => hc _ ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩), fun i j hij => ?_⟩
    have hp : List.Pairwise (fun g g' : R4 → ℝ => Disjoint (supp g) (supp g'))
      (List.ofFn f) := hd
    rw [List.pairwise_ofFn] at hp
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hp hlt
    · exact (hp hlt).symm
  · rintro ⟨hc, hd⟩
    refine ⟨List.length_ofFn, fun g hg => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
      exact hc i
    · change List.Pairwise (fun g g' : R4 → ℝ => Disjoint (supp g) (supp g'))
        (List.ofFn f)
      rw [List.pairwise_ofFn]
      exact fun i j hij => hd hij.ne
theorem ofFn_mem_sepAll_iff {n : ℕ} {f : Fin n → R4 → ℝ} :
    List.ofFn f ∈ sepAll ↔ List.ofFn f ∈ sepN n := by
  constructor
  · intro hf
    exact ⟨List.length_ofFn, isSeparatedList_of_mem_sepAll hf⟩
  · exact fun hf => Ambient.separatedN_subset_separatedAll _ _ n hf
theorem ofFn_comp_mem_sepN {m n : ℕ} {f : Fin n → R4 → ℝ} (hf : List.ofFn f ∈ sepN n)
    {a : Fin m → Fin n} (ha : Function.Injective a) : List.ofFn (f ∘ a) ∈ sepN m := by
  obtain ⟨hc, hd⟩ := ofFn_mem_sepN_iff.1 hf
  exact ofFn_mem_sepN_iff.2 ⟨fun i => hc _, fun i j hij => hd (ha.ne hij)⟩
def imageOrderIso {n : ℕ} (ς : Equiv.Perm (Fin n)) : Finset (Fin n) ≃o Finset (Fin n) where
  toEquiv := ς.finsetCongr
  map_rel_iff' := by
    intro A B
    change A.map _ ⊆ B.map _ ↔ A ⊆ B
    exact Finset.map_subset_map
theorem imageOrderIso_apply {n : ℕ} (ς : Equiv.Perm (Fin n)) (J : Finset (Fin n)) :
    imageOrderIso ς J = J.map ς.toEmbedding := rfl
def permPartition {n : ℕ} (ς : Equiv.Perm (Fin n))
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    Finpartition (Finset.univ : Finset (Fin n)) :=
  (π.map (imageOrderIso ς)).copy (by rw [imageOrderIso_apply]; exact Finset.map_univ_equiv ς)
theorem parts_permPartition {n : ℕ} (ς : Equiv.Perm (Fin n))
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    (permPartition ς π).parts = π.parts.map (imageOrderIso ς).toEquiv.toEmbedding :=
  Finpartition.parts_map
theorem permPartition_inv {n : ℕ} (ς : Equiv.Perm (Fin n))
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    permPartition ς⁻¹ (permPartition ς π) = π := by
  apply Finpartition.ext
  rw [parts_permPartition, parts_permPartition, Finset.map_map]
  convert Finset.map_refl using 2
  ext J x
  simp [imageOrderIso_apply, Equiv.Perm.inv_def]
theorem permPartition_mem {n : ℕ} (ς : Equiv.Perm (Fin n))
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    (hπ : π ∈ SetPartition.nonSingletonPartitions n) :
    permPartition ς π ∈ SetPartition.nonSingletonPartitions n := by
  simp only [SetPartition.nonSingletonPartitions, Finset.mem_filter, Finset.mem_univ,
    true_and] at hπ ⊢
  intro J hJ
  rw [parts_permPartition, Finset.mem_map] at hJ
  obtain ⟨J', hJ', rfl⟩ := hJ
  change 2 ≤ (imageOrderIso ς J').card
  rw [imageOrderIso_apply, Finset.card_map]
  exact hπ J' hJ'
theorem evalAt_reindex {S : ConnFamily} (hS : ConnectedSymmetric S) {n p q : ℕ}
    {f : Fin n → R4 → ℝ} (hf : List.ofFn f ∈ sepN n)
    {a : Fin p → Fin n} {b : Fin q → Fin n} (ha : Function.Injective a)
    (hb : Function.Injective b) (hab : Set.range a = Set.range b) :
    Ambient.ConnectedFamily.evalAt S p (List.ofFn (f ∘ a)) =
      Ambient.ConnectedFamily.evalAt S q (List.ofFn (f ∘ b)) := by
  have hpq : p = q := by
    have ca := Nat.card_congr (Equiv.ofInjective a ha)
    have cb := Nat.card_congr (Equiv.ofInjective b hb)
    rw [hab] at ca
    simpa using ca.trans cb.symm
  subst hpq
  let τ : Equiv.Perm (Fin p) :=
    ((Equiv.ofInjective a ha).trans (Equiv.setCongr hab)).trans (Equiv.ofInjective b hb).symm
  have hτ : ∀ i, b (τ i) = a i := fun i => by
    have := Equiv.apply_symm_apply (Equiv.ofInjective b hb)
      (Equiv.setCongr hab (Equiv.ofInjective a ha i))
    exact congrArg Subtype.val this
  have hfa : f ∘ a = (f ∘ b) ∘ τ := by
    funext i
    simp [hτ]
  refine (congrArg (Ambient.ConnectedFamily.evalAt S p) (congrArg List.ofFn hfa)).trans ?_
  unfold Ambient.ConnectedFamily.evalAt
  split_ifs with hp
  · exact hS p hp (f ∘ b) (ofFn_comp_mem_sepN hf hb) τ
  · rfl
theorem partitionSum_perm {S : ConnFamily} (hS : ConnectedSymmetric S) {n : ℕ}
    {f : Fin n → R4 → ℝ} (hf : List.ofFn f ∈ sepN n) (ς : Equiv.Perm (Fin n)) :
    partitionSum S (f ∘ ς) = partitionSum S f := by
  unfold partitionSum
  refine Finset.sum_nbij' (permPartition ς) (permPartition ς⁻¹)
    (fun π hπ => permPartition_mem ς hπ) (fun π hπ => permPartition_mem ς⁻¹ hπ)
    (fun π _ => permPartition_inv ς π) (fun π _ => ?_) (fun π _ => ?_)
  · simpa using permPartition_inv ς⁻¹ π
  · rw [parts_permPartition, Finset.prod_map]
    refine Finset.prod_congr rfl fun J _ => ?_
    have key := evalAt_reindex hS hf
      (a := ς ∘ J.orderEmbOfFin rfl)
      (b := (imageOrderIso ς J).orderEmbOfFin rfl)
      (ς.injective.comp (J.orderEmbOfFin rfl).injective)
      ((imageOrderIso ς J).orderEmbOfFin rfl).injective
      (by
        rw [Set.range_comp, Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin,
          imageOrderIso_apply, Finset.coe_map]
        rfl)
    exact key
theorem centeredFnFree_perm {S : ConnFamily} (hS : ConnectedSymmetric S) {n : ℕ}
    (f : Fin n → R4 → ℝ) (ς : Equiv.Perm (Fin n)) :
    centeredFnFree S (toFree (List.ofFn (f ∘ ς))) =
      centeredFnFree S (toFree (List.ofFn f)) := by
  by_cases hf : List.ofFn f ∈ sepAll
  · have hf' := ofFn_mem_sepAll_iff.1 hf
    have hς : List.ofFn (f ∘ ς) ∈ sepAll :=
      ofFn_mem_sepAll_iff.2 (ofFn_comp_mem_sepN hf' ς.injective)
    rw [centeredFnFree_toFree S hς, centeredFnFree_toFree S hf, centeredFn_ofFn,
      centeredFn_ofFn, partitionSum_perm hS hf']
  · have hς : List.ofFn (f ∘ ς) ∉ sepAll := fun hm => hf <| by
      have hm' := ofFn_comp_mem_sepN (ofFn_mem_sepAll_iff.1 hm) (ς⁻¹).injective
      have he : (f ∘ ς) ∘ (ς⁻¹ : Equiv.Perm (Fin n)) = f := by
        funext i
        simp
      rw [he] at hm'
      exact ofFn_mem_sepAll_iff.2 hm'
    simp [toFree, hf, hς]
theorem list_get_map {α β : Type*} (g : α → β) (L : List α) (i : Fin (L.map g).length) :
    (L.map g).get i = g (L.get (Fin.cast (List.length_map g) i)) := by
  simp
theorem centeredFnFree_motion {S : ConnFamily} (r : EuclidMotion)
    (hsep : ∀ n, ∀ Y ∈ sepN n, r.actList Y ∈ sepN n)
    (hr : ∀ (n : ℕ) (hn : 2 ≤ n), ∀ Y ∈ sepN n,
      Ambient.evalOrZero (S.fn n hn) (r.actList Y) = Ambient.evalOrZero (S.fn n hn) Y)
    (A : FreeSep) : centeredFnFree S (r.actFree A) = centeredFnFree S A := by
  have hlist : ∀ X : sepAll,
      centeredFnFree S (r.actFree (toFree X.1)) =
        centeredFnFree S (toFree X.1) := by
    intro X
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 X.2
    have hrX : r.actList X.1 ∈ sepAll := Ambient.separatedN_subset_separatedAll _ _ k (hsep k _ hk)
    rw [EuclidMotion.actFree, liftLin_toFree, centeredFnFree_toFree S hrX,
      centeredFnFree_toFree S X.2]
    congr 1
    rw [centeredFn_eq_partitionSum, centeredFn_eq_partitionSum]
    have hg := partitionSum_congr S (m := (r.actList X.1).length) (n := X.1.length)
      (by simp [EuclidMotion.actList]) (List.get (r.actList X.1)) (fun i => r.actFn (X.1.get i))
      (fun i => list_get_map r.actFn X.1 i)
    refine hg.trans ?_
    unfold partitionSum
    refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => ?_
    have hsub : List.ofFn (fun k => X.1.get (J.orderEmbOfFin rfl k)) ∈ sepN J.card :=
      Ambient.subList_mem_separatedN (isSeparatedList_of_mem_sepAll X.2) J
    have hmap : (List.ofFn fun k => r.actFn (X.1.get (J.orderEmbOfFin rfl k))) =
        r.actList (List.ofFn fun k => X.1.get (J.orderEmbOfFin rfl k)) := by
      simp [EuclidMotion.actList, List.map_ofFn, Function.comp_def]
    refine (congrArg (Ambient.ConnectedFamily.evalAt S J.card) hmap).trans ?_
    unfold Ambient.ConnectedFamily.evalAt
    split_ifs with hJ
    · exact hr _ hJ _ hsub
    · rfl
  induction A using Finsupp.induction_linear with
  | zero => simp
  | add F G hF hG => rw [map_add, map_add, hF, hG, map_add]
  | single X z =>
    have hs : Finsupp.single X z = z • toFree X.1 := by
      rw [toFree_of_mem X.2]
      simp
    rw [hs, map_smul, map_smul, map_smul, hlist]
theorem actList_mem_sepN (hI : TupleRules.MotionOfListsAndCombs) (r : EuclidMotion)
    (n : ℕ) (Y : FnList) (hY : Y ∈ sepN n) : r.actList Y ∈ sepN n := by
  have hin : Y ∈ sepNIn n Set.univ :=
    ⟨hY, Ambient.separatedN_subset_separatedAll _ _ n hY, fun _ _ => Set.subset_univ _⟩
  exact ((hI r Set.univ isOpen_univ).2.1 n).1.mapsTo hin |>.1
theorem permInvariant_of_symm {S : ConnFamily} (hS : ConnectedSymmetric S)
    (hE : TensorComponents.ExpandsOverReImParts S) :
    PermInvariant S := by
  intro n _ ς h hh
  have hh' : ComplexComponents (h ∘ ς) :=
    ⟨hh.one_le, fun l => hh.mem _, fun k l hkl => hh.disjoint (ς.injective.ne hkl)⟩
  rw [hE n _ hh', hE n h hh]
  refine Fintype.sum_equiv (Equiv.arrowCongr ς (Equiv.refl _)) _ _ fun ε' => ?_
  have hsum : ∑ l, (Equiv.arrowCongr ς (Equiv.refl (Fin 2)) ε' l : ℕ) = ∑ l, (ε' l : ℕ) := by
    simpa [Equiv.arrowCongr] using Equiv.sum_comp ς.symm fun l => (ε' l : ℕ)
  have hparts : (fun l => reOrImPart (ε' l) ((h ∘ ς) l)) =
      (fun k => reOrImPart (Equiv.arrowCongr ς (Equiv.refl (Fin 2)) ε' k) (h k)) ∘ ς := by
    funext l
    simp [Equiv.arrowCongr]
  rw [hsum, hparts, centeredFnFree_perm hS]
theorem motionInvariant_of_invariant {S : ConnFamily} (hI : TupleRules.MotionOfListsAndCombs)
    (hS : ConnectedInvariant S) : MotionInvariant S := by
  intro A
  refine ⟨fun v => centeredFnFree_motion _ (actList_mem_sepN hI _)
    (fun n hn Y hY => (hS n hn Y hY).1 v) A, fun w hw => centeredFnFree_motion _
    (actList_mem_sepN hI _) (fun n hn Y hY => ((hS n hn Y hY).2 w hw).symm) A⟩
theorem mappedInsertionForm_eq {S : ConnFamily} (hA : TupleRules.MotionOnFree)
    (hM : MotionInvariant S) (w : hyperoctahedral) (F : FreeSep) (h : R4 → ℂ)
    (A : FreeSep) :
    mappedInsertionForm S w ((w : EuclidMotion).actFree F) ((w : EuclidMotion).actFn h)
        ((w : EuclidMotion).actFree A) =
      insertion S F h A := by
  rw [mappedInsertionForm_image hA]
  exact (hM _).2 w w.2
theorem imagePlaneBoundEquiv_holds {m : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon m S)
    (hA : TupleRules.MotionOnFree) (hM : MotionInvariant S)
    (w : hyperoctahedral) {p c : ℝ} (hp : 0 < p) (hc : c ∈ productBoundFractions) :
    ImagePlaneBoundEquiv σ w hp hc := by
  have hiff : ∀ (φ : RealPlane → ℝ) (C : ℝ),
      ImagePlaneProductBoundWith σ w hp hc φ C ↔ ProductBoundWith σ hp hc φ C := by
    intro φ C
    simp only [ImagePlaneProductBoundWith, ProductBoundWith,
      mappedInsertionForm_eq hA hM]
  refine ⟨fun η _ α _ _ φ _ F _ A _ => mappedInsertionForm_eq hA hM w F _ A,
    fun φ _ C => hiff φ C, ?_⟩
  simp only [ImagePlaneProductBound, ProductBoundWithExponent, hiff]
theorem actFn_mul (r r' : EuclidMotion) (f : R4 → ℝ) :
    (r * r').actFn f = r.actFn (r'.actFn f) := by
  funext x
  simp [EuclidMotion.actFn, mul_inv_rev, EuclidMotion.mul_apply]
theorem actFn_actFn_inv (u : EuclidMotion) (f : R4 → ℝ) :
    u.actFn (u⁻¹.actFn f) = f := by
  rw [← actFn_mul, mul_inv_cancel]
  funext x
  simp [EuclidMotion.actFn, EuclidMotion.one_apply]
theorem twoPointInvariant_conj {S : ConnFamily}
    (hI : TupleRules.MotionOfListsAndCombs)
    (hS : ConnectedInvariant S) {u : EuclidMotion} (hu : u ∈ hyperoctahedral)
    {r : EuclidMotion} (hr : TwoPointInvariant S r) :
    TwoPointInvariant S (u * r * u⁻¹) := by
  intro f₁ f₂ hf
  have hg : [u⁻¹.actFn f₁, u⁻¹.actFn f₂] ∈ sepN 2 :=
    actList_mem_sepN hI u⁻¹ 2 _ hf
  have hrg : [r.actFn (u⁻¹.actFn f₁), r.actFn (u⁻¹.actFn f₂)] ∈ sepN 2 :=
    actList_mem_sepN hI r 2 _ hg
  have e₁ := (hS 2 le_rfl _ hrg).2 u hu
  have e₂ := (hS 2 le_rfl _ hg).2 u hu
  have e₃ := hr _ _ hg
  simp only [EuclidMotion.actList, List.map_cons, List.map_nil, actFn_actFn_inv] at e₁ e₂
  simp only [actFn_mul]
  exact e₁.symm.trans (e₃.trans e₂)
theorem twoPointInvariant_imagePlane_iff {S : ConnFamily}
    (hI : TupleRules.MotionOfListsAndCombs)
    (hS : ConnectedInvariant S) (w : hyperoctahedral) (t : ℝ) :
    TwoPointInvariant S (imagePlaneRotation w t) ↔ TwoPointInvariant S (rotateMotion t) := by
  constructor
  · intro hw
    have hw' := twoPointInvariant_conj hI hS (hyperoctahedral.inv_mem w.2) hw
    have he : (w : EuclidMotion)⁻¹ * imagePlaneRotation w t * ((w : EuclidMotion)⁻¹)⁻¹ =
        rotateMotion t := by
      simp [imagePlaneRotation, mul_assoc]
    rwa [he] at hw'
  · exact twoPointInvariant_conj hI hS w.2
theorem reductionHolds (hT : TupleRules.TupleSpanActionRules)
    (hC : TensorComponents.CenteredSeesTensorComps) : ReductionHolds := by
  intro m S σ
  have hI : TupleRules.MotionOfListsAndCombs := hT.2.1
  have hA : TupleRules.MotionOnFree := hT.2.2.1
  have hM := motionInvariant_of_invariant hI σ.invariant
  exact ⟨permInvariant_of_symm σ.symm (hC S).2.2.2.2, hM,
    fun w p c hp hc => imagePlaneBoundEquiv_holds σ hA hM w hp hc,
    fun w t => twoPointInvariant_imagePlane_iff hI σ.invariant w t⟩
end EuclideanFunctionals.MomentSymmetry
end YangMills.Construction
