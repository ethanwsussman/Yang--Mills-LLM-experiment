import YangMills.Construction.EuclideanFunctionals.InvarianceOfConnectedFunctionsAndOfTheCentredFunctionalProof
import YangMills.Construction.EuclideanFunctionals.InvarianceOfTheMomentsAndReductionToTheTimePlaneProof
import YangMills.Construction.EuclideanFunctionals.SymmetryOfConnectedFunctionsAndOfTheCentredFunctional
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ConnectedSymmetry
theorem ofFn_mem_sepAll_iff_sepN {n : ℕ} {f : Fin n → R4 → ℝ} :
    List.ofFn f ∈ sepAll ↔ List.ofFn f ∈ sepN n := by apply _root_.YangMills.Construction.EuclideanFunctionals.MomentSymmetry.ofFn_mem_sepAll_iff <;> assumption
theorem ofFn_comp_mem_sepN {m n : ℕ} {f : Fin n → R4 → ℝ} (hf : List.ofFn f ∈ sepN n)
    {a : Fin m → Fin n} (ha : Function.Injective a) : List.ofFn (f ∘ a) ∈ sepN m := by apply _root_.YangMills.Construction.EuclideanFunctionals.MomentSymmetry.ofFn_comp_mem_sepN <;> assumption
def blockProduct (S : ConnFamily) {n : ℕ} (f : Fin n → R4 → ℝ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  ∏ J ∈ π.parts, Ambient.ConnectedFamily.evalAt S J.card
    (List.ofFn fun k => f (J.orderEmbOfFin rfl k))
def partitionSum (S : ConnFamily) {n : ℕ} (f : Fin n → R4 → ℝ) : ℝ :=
  ∑ π ∈ SetPartition.nonSingletonPartitions n, blockProduct S f π
theorem partitionSum_congr (S : ConnFamily) {m n : ℕ} (e : m = n) (g : Fin m → R4 → ℝ)
    (f : Fin n → R4 → ℝ) (h : ∀ i, g i = f (Fin.cast e i)) :
    partitionSum S g = partitionSum S f := by
  subst e
  have hgf : g = f := funext fun i => h i
  rw [hgf]
theorem centeredAt_ofFn (S : ConnFamily) {n : ℕ} (f : Fin n → R4 → ℝ)
    (h : List.ofFn f ∈ sepAll) : centeredAt S (List.ofFn f) = partitionSum S f := by
  have hdef : centeredFn S ⟨List.ofFn f, h⟩ = partitionSum S (List.ofFn f).get := rfl
  have hget : partitionSum S (List.ofFn f).get = partitionSum S f :=
    partitionSum_congr S List.length_ofFn _ _ fun i => by
      simp
      rfl
  rw [← hget, ← hdef]
  unfold centeredAt Ambient.evalOrZero
  exact dif_pos h
def wholeBlock {n : ℕ} (hn : 2 ≤ n) : Finpartition (Finset.univ : Finset (Fin n)) :=
  Finpartition.indiscrete (by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact Finset.univ_nonempty.ne_empty)
theorem wholeBlock_parts {n : ℕ} (hn : 2 ≤ n) : (wholeBlock hn).parts = {Finset.univ} := rfl
theorem wholeBlock_mem {n : ℕ} (hn : 2 ≤ n) :
    wholeBlock hn ∈ SetPartition.nonSingletonPartitions n := by
  simp only [SetPartition.nonSingletonPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
  intro J hJ
  rw [wholeBlock_parts, Finset.mem_singleton] at hJ
  subst hJ
  simpa using hn
theorem blockProduct_wholeBlock (S : ConnFamily) {n : ℕ} (hn : 2 ≤ n) (f : Fin n → R4 → ℝ) :
    blockProduct S f (wholeBlock hn) =
      Ambient.ConnectedFamily.evalAt S n (List.ofFn f) := by
  have hc : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
  have he : ∀ i : Fin n,
      (Finset.univ : Finset (Fin n)).orderEmbOfFin rfl (Fin.cast hc.symm i) = i := by
    intro i
    have hu := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin n))) rfl
      (f := Fin.cast hc) (fun _ => Finset.mem_univ _) (fun a b hab => hab)
    rw [← hu]
    rfl
  have hl : (List.ofFn fun k => f ((Finset.univ : Finset (Fin n)).orderEmbOfFin rfl k)) =
      List.ofFn f := by
    rw [List.ofFn_congr hc]
    exact congrArg List.ofFn (funext fun i => congrArg f (he i))
  rw [blockProduct, wholeBlock_parts, Finset.prod_singleton]
  refine (congrArg (Ambient.ConnectedFamily.evalAt S _) hl).trans ?_
  rw [hc]
  rfl
theorem card_lt_of_ne_wholeBlock {n : ℕ} (hn : 2 ≤ n)
    {π : Finpartition (Finset.univ : Finset (Fin n))} (hπ : π ≠ wholeBlock hn)
    {J : Finset (Fin n)} (hJ : J ∈ π.parts) : J.card < n := by
  by_contra hlt
  have hJu : J = Finset.univ := by
    apply Finset.eq_univ_of_card
    have := Finset.card_le_univ J
    simp only [Fintype.card_fin] at this ⊢
    omega
  apply hπ
  apply Finpartition.ext
  rw [wholeBlock_parts]
  ext K
  rw [Finset.mem_singleton]
  constructor
  · intro hK
    obtain ⟨a, ha⟩ := π.nonempty_of_mem_parts hK
    have := π.eq_of_mem_parts hK hJ ha (by simp [hJu])
    rw [this, hJu]
  · rintro rfl
    subst hJu
    exact hJ
def imageIso {n : ℕ} (ς : Equiv.Perm (Fin n)) : Finset (Fin n) ≃o Finset (Fin n) where
  toEquiv := ς.finsetCongr
  map_rel_iff' := by
    intro A B
    change A.map _ ⊆ B.map _ ↔ A ⊆ B
    exact Finset.map_subset_map
theorem imageIso_apply {n : ℕ} (ς : Equiv.Perm (Fin n)) (J : Finset (Fin n)) :
    imageIso ς J = J.map ς.toEmbedding := rfl
def permPartition {n : ℕ} (ς : Equiv.Perm (Fin n))
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    Finpartition (Finset.univ : Finset (Fin n)) :=
  (π.map (imageIso ς)).copy (by rw [imageIso_apply]; exact Finset.map_univ_equiv ς)
theorem permPartition_parts {n : ℕ} (ς : Equiv.Perm (Fin n))
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    (permPartition ς π).parts = π.parts.map (imageIso ς).toEquiv.toEmbedding :=
  Finpartition.parts_map
theorem permPartition_inv_self {n : ℕ} (ς : Equiv.Perm (Fin n))
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    permPartition ς⁻¹ (permPartition ς π) = π := by
  apply Finpartition.ext
  rw [permPartition_parts, permPartition_parts, Finset.map_map]
  convert Finset.map_refl using 2
  ext J x
  simp [imageIso_apply, Equiv.Perm.inv_def]
theorem permPartition_self_inv {n : ℕ} (ς : Equiv.Perm (Fin n))
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    permPartition ς (permPartition ς⁻¹ π) = π := by
  simpa using permPartition_inv_self ς⁻¹ π
theorem permPartition_mem {n : ℕ} (ς : Equiv.Perm (Fin n))
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    (hπ : π ∈ SetPartition.nonSingletonPartitions n) :
    permPartition ς π ∈ SetPartition.nonSingletonPartitions n := by
  simp only [SetPartition.nonSingletonPartitions, Finset.mem_filter, Finset.mem_univ,
    true_and] at hπ ⊢
  intro J hJ
  rw [permPartition_parts, Finset.mem_map] at hJ
  obtain ⟨J', hJ', rfl⟩ := hJ
  change 2 ≤ (imageIso ς J').card
  rw [imageIso_apply, Finset.card_map]
  exact hπ J' hJ'
theorem permPartition_wholeBlock {n : ℕ} (hn : 2 ≤ n) (ς : Equiv.Perm (Fin n)) :
    permPartition ς (wholeBlock hn) = wholeBlock hn := by
  apply Finpartition.ext
  rw [permPartition_parts, wholeBlock_parts, Finset.map_singleton]
  congr 1
  change imageIso ς Finset.univ = Finset.univ
  rw [imageIso_apply]
  exact Finset.map_univ_equiv ς
def SymmetricAtOrder (S : ConnFamily) (p : ℕ) : Prop :=
  ∀ (hp : 2 ≤ p) (f : Fin p → R4 → ℝ), List.ofFn f ∈ sepN p →
    ∀ ς : Equiv.Perm (Fin p),
      Ambient.evalOrZero (S.fn p hp) (List.ofFn (f ∘ ς)) =
        Ambient.evalOrZero (S.fn p hp) (List.ofFn f)
theorem evalAt_reindex {S : ConnFamily} {n p q : ℕ} (hS : SymmetricAtOrder S p)
    {f : Fin n → R4 → ℝ} (hf : List.ofFn f ∈ sepN n)
    {a : Fin p → Fin n} {b : Fin q → Fin n} (ha : Function.Injective a)
    (hb : Function.Injective b) (hr : Set.range a = Set.range b) :
    Ambient.ConnectedFamily.evalAt S p (List.ofFn (f ∘ a)) =
      Ambient.ConnectedFamily.evalAt S q (List.ofFn (f ∘ b)) := by
  have hpq : p = q := by
    have hca := Nat.card_congr (Equiv.ofInjective a ha)
    have hcb := Nat.card_congr (Equiv.ofInjective b hb)
    rw [hr] at hca
    simpa using hca.trans hcb.symm
  subst hpq
  let τ : Equiv.Perm (Fin p) :=
    ((Equiv.ofInjective a ha).trans (Equiv.setCongr hr)).trans (Equiv.ofInjective b hb).symm
  have hτ : ∀ i, b (τ i) = a i := fun i => by
    have := Equiv.apply_symm_apply (Equiv.ofInjective b hb)
      (Equiv.setCongr hr (Equiv.ofInjective a ha i))
    exact congrArg Subtype.val this
  have hfa : f ∘ a = (f ∘ b) ∘ τ := by
    funext i
    simp [hτ]
  refine (congrArg (Ambient.ConnectedFamily.evalAt S p) (congrArg List.ofFn hfa)).trans ?_
  unfold Ambient.ConnectedFamily.evalAt
  split_ifs with hp
  · exact hS hp (f ∘ b) (ofFn_comp_mem_sepN hf hb) τ
  · rfl
theorem blockProduct_comp_perm {S : ConnFamily} {n : ℕ} {f : Fin n → R4 → ℝ}
    (hf : List.ofFn f ∈ sepN n) (ς : Equiv.Perm (Fin n))
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    (hS : ∀ J ∈ π.parts, SymmetricAtOrder S J.card) :
    blockProduct S (f ∘ ς) π = blockProduct S f (permPartition ς π) := by
  unfold blockProduct
  rw [permPartition_parts, Finset.prod_map]
  refine Finset.prod_congr rfl fun J hJ => ?_
  have h := evalAt_reindex (hS J hJ) hf
    (a := ς ∘ J.orderEmbOfFin rfl)
    (b := (imageIso ς J).orderEmbOfFin rfl)
    (ς.injective.comp (J.orderEmbOfFin rfl).injective)
    ((imageIso ς J).orderEmbOfFin rfl).injective
    (by
      rw [Set.range_comp, Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin,
        imageIso_apply, Finset.coe_map]
      rfl)
  exact h
theorem partitionSum_comp_perm_sub {S : ConnFamily} {n : ℕ} (hn : 2 ≤ n)
    (hS : ∀ k < n, SymmetricAtOrder S k)
    {f : Fin n → R4 → ℝ} (hf : List.ofFn f ∈ sepN n) (ς : Equiv.Perm (Fin n)) :
    partitionSum S (f ∘ ς) - partitionSum S f =
      Ambient.ConnectedFamily.evalAt S n (List.ofFn (f ∘ ς)) -
        Ambient.ConnectedFamily.evalAt S n (List.ofFn f) := by
  have hrest : ∑ π ∈ (SetPartition.nonSingletonPartitions n).erase (wholeBlock hn),
        blockProduct S (f ∘ ς) π =
      ∑ π ∈ (SetPartition.nonSingletonPartitions n).erase (wholeBlock hn),
        blockProduct S f π := by
    have hmaps : ∀ (τ : Equiv.Perm (Fin n)) (π : Finpartition (Finset.univ : Finset (Fin n))),
        π ∈ (SetPartition.nonSingletonPartitions n).erase (wholeBlock hn) →
        permPartition τ π ∈ (SetPartition.nonSingletonPartitions n).erase (wholeBlock hn) := by
      intro τ π hπ
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hπ
      refine Finset.mem_erase.2 ⟨fun h => hne ?_, permPartition_mem τ hmem⟩
      rw [← permPartition_inv_self τ π, h, permPartition_wholeBlock]
    refine Finset.sum_nbij' (permPartition ς) (permPartition ς⁻¹)
      (fun π hπ => hmaps ς π hπ) (fun π hπ => hmaps ς⁻¹ π hπ)
      (fun π _ => permPartition_inv_self ς π) (fun π _ => permPartition_self_inv ς π)
      (fun π hπ => ?_)
    exact blockProduct_comp_perm hf ς fun J hJ =>
      hS _ (card_lt_of_ne_wholeBlock hn (Finset.mem_erase.1 hπ).1 hJ)
  have hsplit : ∀ g : Fin n → R4 → ℝ, partitionSum S g =
      Ambient.ConnectedFamily.evalAt S n (List.ofFn g) +
        ∑ π ∈ (SetPartition.nonSingletonPartitions n).erase (wholeBlock hn),
          blockProduct S g π := by
    intro g
    rw [← blockProduct_wholeBlock S hn g]
    exact (Finset.add_sum_erase _ _ (wholeBlock_mem hn)).symm
  rw [hsplit (f ∘ ς), hsplit f, hrest]
  exact add_sub_add_right_eq_sub _ _ _
theorem evalAt_eq_evalOrZero (S : ConnFamily) {n : ℕ} (hn : 2 ≤ n) (X : FnList) :
    Ambient.ConnectedFamily.evalAt S n X = Ambient.evalOrZero (S.fn n hn) X := by apply _root_.YangMills.Construction.EuclideanFunctionals.InvarianceComparison.evalAt_eq_evalOrZero <;> assumption
theorem centeredAt_perm {S : ConnFamily} (hS : ConnectedSymmetric S) (n : ℕ)
    (f : Fin n → R4 → ℝ) (hf : List.ofFn f ∈ sepAll) (ς : Equiv.Perm (Fin n)) :
    centeredAt S (List.ofFn (f ∘ ς)) = centeredAt S (List.ofFn f) := by
  by_cases hn : 2 ≤ n
  · have hfn := ofFn_mem_sepAll_iff_sepN.1 hf
    have hς : List.ofFn (f ∘ ς) ∈ sepAll :=
      ofFn_mem_sepAll_iff_sepN.2 (ofFn_comp_mem_sepN hfn ς.injective)
    have h := partitionSum_comp_perm_sub hn (fun k _ hk g hg τ => hS k hk g hg τ) hfn ς
    have hr : Ambient.ConnectedFamily.evalAt S n (List.ofFn (f ∘ ς)) =
        Ambient.ConnectedFamily.evalAt S n (List.ofFn f) :=
      (evalAt_eq_evalOrZero S hn _).trans
        ((hS n hn f hfn ς).trans (evalAt_eq_evalOrZero S hn _).symm)
    rw [centeredAt_ofFn S _ hς, centeredAt_ofFn S _ hf]
    exact sub_eq_zero.1 (h.trans (sub_eq_zero.2 hr))
  · have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 (by omega)
    have hfix : f ∘ ς = f := funext fun i => congrArg f (Subsingleton.elim _ _)
    rw [hfix]
theorem symmetricAtOrder_of_centered {S : ConnFamily}
    (hσ : ∀ (n : ℕ) (f : Fin n → R4 → ℝ), List.ofFn f ∈ sepAll →
      ∀ ς : Equiv.Perm (Fin n),
        centeredAt S (List.ofFn (f ∘ ς)) = centeredAt S (List.ofFn f)) (n : ℕ) :
    SymmetricAtOrder S n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn f hf ς
    have hsep := ofFn_mem_sepAll_iff_sepN.2 hf
    have hς : List.ofFn (f ∘ ς) ∈ sepAll :=
      ofFn_mem_sepAll_iff_sepN.2 (ofFn_comp_mem_sepN hf ς.injective)
    have h := partitionSum_comp_perm_sub hn ih hf ς
    have hc := hσ n f hsep ς
    rw [centeredAt_ofFn S _ hς, centeredAt_ofFn S _ hsep] at hc
    have hr : Ambient.ConnectedFamily.evalAt S n (List.ofFn (f ∘ ς)) =
        Ambient.ConnectedFamily.evalAt S n (List.ofFn f) :=
      sub_eq_zero.1 (h.symm.trans (sub_eq_zero.2 hc))
    exact (evalAt_eq_evalOrZero S hn _).symm.trans (hr.trans (evalAt_eq_evalOrZero S hn _))
theorem tensorComp_eq_zero_of_ne {n q : ℕ} (hq : q ≠ n) {F : FreeSep}
    (hF : F ∈ combSpan n) : tensorComp q F = 0 := by
  have h : combSpan n ≤ LinearMap.ker (tensorComp q) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨X, hX, rfl⟩
    have hsep : X ∈ sepAll := Ambient.separatedN_subset_separatedAll _ _ n hX
    have hlen : X.length = n := hX.1
    change tensorComp q (toFree X) = 0
    rw [tensorComp, liftLin_toFree _ ⟨X, hsep⟩]
    exact tensorAt_of_length_ne _ (by simpa [hlen] using hq.symm)
  exact h hF
theorem tensorCompZero_eq_zero {n : ℕ} (hn : 1 ≤ n) {F : FreeSep}
    (hF : F ∈ combSpan n) : tensorCompZero F = 0 := by
  have h : combSpan n ≤ LinearMap.ker tensorCompZero := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨X, hX, rfl⟩
    have hsep : X ∈ sepAll := Ambient.separatedN_subset_separatedAll _ _ n hX
    have hlen : X.length = n := hX.1
    change tensorCompZero (toFree X) = 0
    rw [tensorCompZero, liftLin_toFree _ ⟨X, hsep⟩]
    have hne : X.length ≠ 0 := by omega
    simp [tensorAtZero, hne]
  exact h hF
theorem sameTensors_of_tensorComp_eq {n : ℕ} (hn : 1 ≤ n) {F F' : FreeSep}
    (hF : F ∈ combSpan n) (hF' : F' ∈ combSpan n)
    (h : tensorComp n F = tensorComp n F') : SameTensors F F' := by
  refine ⟨by rw [tensorCompZero_eq_zero hn hF, tensorCompZero_eq_zero hn hF'], ?_⟩
  intro q _
  by_cases hq : q = n
  · subst hq
    exact h
  · rw [tensorComp_eq_zero_of_ne hq hF, tensorComp_eq_zero_of_ne hq hF']
theorem centeredFnFree_im_eq_zero (S : ConnFamily) (X : sepAll) :
    (centeredFnFree S (toFree X.1)).im = 0 := by
  have h : centeredFnFree S (toFree X.1) = (centeredFn S X : ℂ) :=
    liftLin_toFree _ X
  rw [h, Complex.ofReal_im]
theorem main_holds (hT : TensorComponents.CenteredSeesTensorComps) : Main := by
  intro S
  obtain ⟨hlin, hsame, -⟩ := hT S
  constructor
  · intro hS
    refine ⟨centeredFnFree_im_eq_zero S, centeredAt_perm hS, ?_, ?_⟩
    · intro n f i g _ hf hg a a'
      have hn : 1 ≤ n := by
        have := i.pos
        omega
      exact (hlin n hn i f g (ofFn_mem_sepAll_iff_sepN.1 hf)
        (ofFn_mem_sepAll_iff_sepN.1 hg) a a').2.1
    · intro n hn F hF F' hF' h
      exact hsame F F' (sameTensors_of_tensorComp_eq hn hF hF' h)
  · intro h n hn f hf ς
    exact symmetricAtOrder_of_centered h.symmetric n hn f hf ς
end YangMills.Construction.EuclideanFunctionals.ConnectedSymmetry
