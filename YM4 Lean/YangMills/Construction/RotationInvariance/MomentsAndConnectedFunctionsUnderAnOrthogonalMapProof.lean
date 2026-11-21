import YangMills.Construction.RotationInvariance.MomentsAndConnectedFunctionsUnderAnOrthogonalMap
import YangMills.Construction.RotationInvariance.WhatAnOrthogonalMapPreserves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.OrthogonalInvariance
theorem exists_ofFn_eq_of_mem_sepN {n : ℕ} {X : FnList} (hX : X ∈ sepN n) :
    ∃ f : Fin n → R4 → ℝ, List.ofFn f = X := by
  obtain ⟨rfl, -⟩ := hX
  exact ⟨X.get, List.ofFn_get X⟩
theorem exists_mem_sepN_of_mem_sepAll {X : FnList} (hX : X ∈ sepAll) : ∃ n, X ∈ sepN n :=
  Set.mem_iUnion.1 hX
theorem ofFn_comp_orderEmb_mem_sepN {n m : ℕ} {f : Fin n → R4 → ℝ} (hf : List.ofFn f ∈ sepN n)
    (e : Fin m ↪o Fin n) : (List.ofFn fun k => f (e k)) ∈ sepN m := by
  refine ⟨List.length_ofFn, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
    exact hf.2.1 _ (List.mem_ofFn.2 ⟨e i, rfl⟩)
  · exact List.pairwise_ofFn.2 fun i j hij => List.pairwise_ofFn.1 hf.2.2 (e.strictMono hij)
theorem centeredAt_ofFn (S : ConnFamily) {n : ℕ} {f : Fin n → R4 → ℝ}
    (hf : List.ofFn f ∈ sepN n) :
    centeredAt S (List.ofFn f) =
      ∑ π ∈ SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts,
        S.evalAt J.card (List.ofFn fun k => f (J.orderEmbOfFin rfl k)) := by
  have hX : List.ofFn f ∈ sepAll :=
    ReflectionPositivity.AxisMirror.Ambient.separatedN_subset_separatedAll _ _ n hf
  have key : ∀ (X : FnList) (m : ℕ) (e : X.length = m) (g : Fin m → R4 → ℝ)
      (_ : ∀ l, g l = X.get (Fin.cast e.symm l)) (hX : X ∈ sepAll),
      centeredFn S ⟨X, hX⟩ = ∑ π ∈ SetPartition.nonSingletonPartitions m, ∏ J ∈ π.parts,
        S.evalAt J.card (List.ofFn fun k => g (J.orderEmbOfFin rfl k)) := by
    intro X m e g hg hX
    subst e
    obtain rfl : g = X.get := funext hg
    rfl
  exact (dif_pos hX).trans
    (key _ n List.length_ofFn f (fun l => by simp) hX)
theorem centeredFnFree_toFree (S : ConnFamily) {X : FnList} (hX : X ∈ sepAll) :
    centeredFnFree S (toFree X) = (centeredAt S X : ℂ) := by
  have h := liftLin_toFree (fun Y : sepAll => (centeredFn S Y : ℂ)) ⟨X, hX⟩
  have h' : centeredAt S X = centeredFn S ⟨X, hX⟩ := dif_pos hX
  rw [h']
  exact h
theorem ofFn_orderEmbOfFin_univ {n : ℕ} (f : Fin n → R4 → ℝ) :
    (List.ofFn fun k : Fin (Finset.univ : Finset (Fin n)).card =>
      f ((Finset.univ : Finset (Fin n)).orderEmbOfFin rfl k)) = List.ofFn f := by
  have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
  have he : ((Finset.univ : Finset (Fin n)).orderEmbOfFin rfl : _ → Fin n) = Fin.cast hc :=
    (Finset.orderEmbOfFin_unique rfl (fun _ => Finset.mem_univ _)
      (fun _ _ h => h)).symm
  rw [he, List.ofFn_congr hc.symm f]
theorem two_le_card_and_card_add_two_le {n : ℕ} {π : Finpartition (Finset.univ : Finset (Fin n))}
    (hπ : π ∈ multiBlockPartitions n) {J : Finset (Fin n)} (hJ : J ∈ π.parts) :
    2 ≤ J.card ∧ J.card + 2 ≤ n := by
  obtain ⟨hB, h2⟩ := Finset.mem_filter.1 hπ
  have hblock := (Finset.mem_filter.1 hB).2
  obtain ⟨J', hJ', hne⟩ := Finset.exists_mem_ne (show 1 < π.parts.card by omega) J
  have hd : Disjoint J' J := π.disjoint hJ' hJ hne
  have hc : (J' ∪ J).card ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hd] at hc
  have h3 := hblock J hJ
  have h4 := hblock J' hJ'
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega
theorem multiBlockPartitionSizes_holds : MultiBlockPartitionSizes := by
  have hnone : ∀ n : ℕ, n < 4 → multiBlockPartitions n = ∅ := by
    intro n hn
    refine Finset.eq_empty_of_forall_notMem fun π hπ => ?_
    have h2 := (Finset.mem_filter.1 hπ).2
    obtain ⟨J, hJ⟩ : π.parts.Nonempty := Finset.card_pos.1 (by omega)
    have := two_le_card_and_card_add_two_le hπ hJ
    omega
  exact ⟨fun n _ π hπ J hJ => two_le_card_and_card_add_two_le hπ hJ, hnone 2 (by omega),
    hnone 3 (by omega)⟩
theorem sum_nonSingletonPartitions_eq {n : ℕ} (hn : 2 ≤ n) (φ : Finset (Fin n) → ℝ) :
    ∑ π ∈ SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts, φ J =
      φ Finset.univ + ∑ π ∈ multiBlockPartitions n, ∏ J ∈ π.parts, φ J := by
  have hne : (Finset.univ : Finset (Fin n)) ≠ ⊥ := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact Finset.univ_nonempty.ne_empty
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hrest : (SetPartition.nonSingletonPartitions n).filter (fun π => ¬2 ≤ π.parts.card) =
      {Finpartition.indiscrete hne} := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h2⟩
      have hpos : 0 < π.parts.card := Finset.card_pos.2 (π.parts_nonempty hne)
      obtain ⟨J, hJ⟩ := Finset.card_eq_one.1 (show π.parts.card = 1 by omega)
      have hsup := π.sup_parts
      rw [hJ] at hsup
      simp only [Finset.sup_singleton, id] at hsup
      refine Finpartition.ext ?_
      rw [hJ, hsup]
      rfl
    · rintro rfl
      refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, fun J hJ => ?_⟩, ?_⟩
      · obtain rfl : J = Finset.univ := Finset.mem_singleton.1 hJ
        omega
      · simp [Finpartition.indiscrete]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun π => 2 ≤ π.parts.card), hrest,
    Finset.sum_singleton, add_comm]
  congr 1
  simp [Finpartition.indiscrete]
theorem momentCumulantExpansion_holds (S : ConnFamily) : MomentCumulantExpansion S := by
  intro n hn f hf
  rw [centeredAt_ofFn S hf,
    sum_nonSingletonPartitions_eq hn fun J =>
      S.evalAt J.card (List.ofFn fun k => f (J.orderEmbOfFin rfl k))]
  refine congrArg₂ (· + ·) ?_ rfl
  have hc : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
  exact (congrArg (S.evalAt (Finset.univ : Finset (Fin n)).card) (ofFn_orderEmbOfFin_univ f)).trans
    (by rw [hc]; rfl)
theorem centeredAt_actFn_eq {S : ConnFamily} {Q : EuclidMotion} (hα : CumulantsInvariant S Q)
    {n : ℕ} {f : Fin n → R4 → ℝ} (hf : List.ofFn f ∈ sepN n)
    (hQ : (List.ofFn fun l => Q.actFn (f l)) ∈ sepN n) :
    centeredAt S (List.ofFn fun l => Q.actFn (f l)) = centeredAt S (List.ofFn f) := by
  rw [centeredAt_ofFn S hQ, centeredAt_ofFn S hf]
  refine Finset.sum_congr rfl fun π hπ => Finset.prod_congr rfl fun J hJ => ?_
  exact hα J.card ((Finset.mem_filter.1 hπ).2 J hJ) (fun k => f (J.orderEmbOfFin rfl k))
    (ofFn_comp_orderEmb_mem_sepN hf _)
theorem actList_ofFn (Q : EuclidMotion) {n : ℕ} (f : Fin n → R4 → ℝ) :
    Q.actList (List.ofFn f) = List.ofFn fun l => Q.actFn (f l) := by
  rw [EuclidMotion.actList, List.map_ofFn]
  rfl
theorem momentsInvariant_of_cumulantsInvariant {S : ConnFamily} {Q : EuclidMotion}
    (hs : ∀ n, ∀ X ∈ sepN n, Q.actList X ∈ sepN n)
    (hα : CumulantsInvariant S Q) : MomentsInvariant S Q := by
  intro n _ X hX
  obtain ⟨f, rfl⟩ := exists_ofFn_eq_of_mem_sepN hX
  have hQ := hs n _ hX
  rw [actList_ofFn] at hQ ⊢
  exact centeredAt_actFn_eq hα hX hQ
theorem cumulantsInvariant_of_momentsInvariant {S : ConnFamily} {Q : EuclidMotion}
    (hs : ∀ n, ∀ X ∈ sepN n, Q.actList X ∈ sepN n)
    (hβ : MomentsInvariant S Q) : CumulantsInvariant S Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn f hf
    have hQ := hs n _ hf
    have hb := hβ n hn _ hf
    rw [actList_ofFn] at hQ hb
    have h₁ := momentCumulantExpansion_holds S n hn f hf
    have h₂ := momentCumulantExpansion_holds S n hn (fun l => Q.actFn (f l)) hQ
    have hsum : (∑ π ∈ multiBlockPartitions n, ∏ J ∈ π.parts,
          S.evalAt J.card (List.ofFn fun k => Q.actFn (f (J.orderEmbOfFin rfl k)))) =
        ∑ π ∈ multiBlockPartitions n, ∏ J ∈ π.parts,
          S.evalAt J.card (List.ofFn fun k => f (J.orderEmbOfFin rfl k)) := by
      refine Finset.sum_congr rfl fun π hπ => Finset.prod_congr rfl fun J hJ => ?_
      have hc := two_le_card_and_card_add_two_le hπ hJ
      exact ih J.card (by omega) hc.1 (fun k => f (J.orderEmbOfFin rfl k))
        (ofFn_comp_orderEmb_mem_sepN hf _)
    linarith
theorem invariantOnFree_of_cumulantsInvariant {S : ConnFamily} {Q : EuclidMotion}
    (hs : ∀ n, ∀ X ∈ sepN n, Q.actList X ∈ sepN n)
    (hα : CumulantsInvariant S Q) : InvariantOnFree S Q := by
  have key : (centeredFnFree S) ∘ₗ Q.actFree = centeredFnFree S := by
    refine freeBasis.ext fun X => ?_
    obtain ⟨n, hn⟩ := exists_mem_sepN_of_mem_sepAll X.2
    have hon : Q.actFree (toFree X.1) = toFree (Q.actList X.1) :=
      liftLin_toFree (fun Y : sepAll => toFree (Q.actList Y.1)) X
    have hQ := hs n _ hn
    rw [freeBasis_apply, LinearMap.comp_apply, hon,
      centeredFnFree_toFree S
        (ReflectionPositivity.AxisMirror.Ambient.separatedN_subset_separatedAll _ _ n hQ),
      centeredFnFree_toFree S X.2]
    obtain ⟨f, hf⟩ := exists_ofFn_eq_of_mem_sepN hn
    rw [← hf] at hQ hn ⊢
    rw [actList_ofFn] at hQ ⊢
    rw [centeredAt_actFn_eq hα hn hQ]
  exact fun X => LinearMap.congr_fun key X
theorem add_smul_mem_C1c {f g : R4 → ℂ} (z : ℂ) (hf : f ∈ C1c ℂ)
    (hg : g ∈ C1c ℂ) : f + z • g ∈ C1c ℂ := by
  have hf' := (mem_C1c_iff_mem_compactC1 f).1 hf
  have hg' := (mem_C1c_iff_mem_compactC1 g).1 hg
  refine (mem_C1c_iff_mem_compactC1 _).2 ⟨hf'.1.add (hg'.1.const_smul z), ?_⟩
  have h₂ : HasCompactSupport (z • g) :=
    HasCompactSupport.comp_left (g := fun y : ℂ => z • y) hg'.2 (smul_zero z)
  exact hf'.2.add h₂
theorem entrywiseLinear_holds (hC : TensorComponents.CenteredSeesTensorComps)
    (S : ConnFamily) : EntrywiseLinear S := by
  intro n i z h g hh hu
  have hn : 1 ≤ n := by have := i.2; omega
  have hE := (mem_disjointComplexTuples_iff hn h).1 hh
  have hE' := (mem_disjointComplexTuples_iff hn _).1 hu
  obtain ⟨-, -, -, hL, -⟩ := hC S
  obtain ⟨hd, hv⟩ := hL n i 1 z h g hE hE'
  rw [one_smul] at hd hv
  refine ⟨⟨fun l => ?_, hd⟩, ?_⟩
  · by_cases hl : l = i
    · subst hl
      have hg : g ∈ C1c ℂ := by simpa using hu.1 l
      rw [Function.update_self]
      exact add_smul_mem_C1c z (hh.1 l) hg
    · rw [Function.update_of_ne hl]
      exact hh.1 l
  · rw [hv, one_mul]
theorem zeroAtZeroArgument_holds (hC : TensorComponents.CenteredSeesTensorComps) (S : ConnFamily) :
    ZeroAtZeroEntry S := by
  intro n hn X hX hz
  obtain ⟨f, rfl⟩ := exists_ofFn_eq_of_mem_sepN hX
  obtain ⟨g, hg, h0⟩ := hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
  obtain ⟨hR, -⟩ := hC S
  have hu : Function.update f i (f i) = f := Function.update_eq_self i f
  have h := (hR n hn i f (f i) hX (by rw [hu]; exact hX) 1 1).2.1
  have hz' : (1 : ℝ) • f i + (1 : ℝ) • f i = f i := by
    funext x
    simp [h0 x]
  rw [hz', hu] at h
  linarith
theorem eqAtComplexification_holds (S : ConnFamily) : EqAtComplexification S := by
  intro n _ X hX
  rw [complexTuple_complexify,
    centeredFnFree_toFree S
      (ReflectionPositivity.AxisMirror.Ambient.separatedN_subset_separatedAll _ _ n hX)]
theorem centeredFnFree_eq_zero_of_mem_tuplesWithZeroEntry
    (hC : TensorComponents.CenteredSeesTensorComps)
    (S : ConnFamily) (n : ℕ) {F : FreeSep}
    (hF : F ∈ tuplesWithZeroComponent n) :
    centeredFnFree S F = 0 := by
  have hle : tuplesWithZeroComponent n ≤ LinearMap.ker (centeredFnFree S) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Z, ⟨hZ, g, hg, hg0⟩, rfl⟩
    have hn : 1 ≤ n := by
      have h₁ := List.length_pos_of_mem hg
      have h₂ : Z.length = n := hZ.1
      omega
    have hv := zeroAtZeroArgument_holds hC S n hn Z hZ ⟨g, hg, fun x => by rw [hg0]; rfl⟩
    show centeredFnFree S (toFree Z) = 0
    rw [centeredFnFree_toFree S
      (ReflectionPositivity.AxisMirror.Ambient.separatedN_subset_separatedAll _ _ n hZ), hv]
    simp
  exact hle hF
theorem holds_of_tensorComps (hC : TensorComponents.CenteredSeesTensorComps)
    (hI : Holds) : OrthogonalMapStatement := by
  intro c S _ Q
  obtain ⟨-, hSup, -, -, -, -, -, hConc, -⟩ := hI
  have hs : ∀ n, ∀ X ∈ sepN n,
      (EuclidMotion.ofOrthogonalMatrix Q).actList X ∈ sepN n := by
    intro n X hX
    rw [← ((hSup Q).2.2.2 n).2]
    exact Set.mem_image_of_mem _ hX
  refine ⟨⟨momentCumulantExpansion_holds S, multiBlockPartitionSizes_holds⟩,
    ⟨momentsInvariant_of_cumulantsInvariant hs, cumulantsInvariant_of_momentsInvariant hs⟩,
    fun hα _ => ⟨invariantOnFree_of_cumulantsInvariant hs hα,
      fun n h _ => invariantOnFree_of_cumulantsInvariant hs hα _⟩,
    entrywiseLinear_holds hC S, zeroAtZeroArgument_holds hC S, eqAtComplexification_holds S, ?_⟩
  intro p p' a ha b hb hd
  have h := (hConc p p' a b ha hb hd).2.2.2
  have h0 := centeredFnFree_eq_zero_of_mem_tuplesWithZeroEntry hC S (p + p') h
  rw [map_sub] at h0
  exact sub_eq_zero.1 h0
end YangMills.Construction.EuclideanFunctionals.OrthogonalInvariance
