import YangMills.Construction.EuclideanFunctionals.InvarianceOfConnectedFunctionsAndOfTheCentredFunctional
import YangMills.Construction.EuclideanFunctionals.TuplesSpansAndActions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.InvarianceComparison
open ReflectionPositivity.AxisMirror
def blockTerm (S : ConnFamily) {n : ℕ} (f : Fin n → R4 → ℝ) (J : Finset (Fin n)) : ℝ :=
  Ambient.ConnectedFamily.evalAt S J.card
    (List.ofFn fun k : Fin J.card => f (J.orderEmbOfFin rfl k))
def nonSingletonSum (S : ConnFamily) (n : ℕ) (f : Fin n → R4 → ℝ) : ℝ :=
  ∑ π ∈ SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts, blockTerm S f J
def FixesConnAt (S : ConnFamily) (r : EuclidMotion) (k : ℕ) : Prop :=
  ∀ Y ∈ sepN k, Ambient.ConnectedFamily.evalAt S k (r.actList Y) =
    Ambient.ConnectedFamily.evalAt S k Y
theorem evalAt_eq_evalOrZero (S : ConnFamily) {n : ℕ} (hn : 2 ≤ n) (Y : FnList) :
    Ambient.ConnectedFamily.evalAt S n Y = Ambient.evalOrZero (S.fn n hn) Y := by
  simp only [Ambient.ConnectedFamily.evalAt, dif_pos hn]
theorem fixesConnAt_of_not_two_le (S : ConnFamily) (r : EuclidMotion) {k : ℕ} (h : ¬ 2 ≤ k) :
    FixesConnAt S r k := fun Y _ => by
  simp only [Ambient.ConnectedFamily.evalAt, dif_neg h]
theorem centeredAt_eq_nonSingletonSum (S : ConnFamily) {X : FnList} (hX : X ∈ sepAll) :
    centeredAt S X = nonSingletonSum S X.length X.get := by
  exact show centeredAt S X = centeredFn S ⟨X, hX⟩ from by
    unfold centeredAt Ambient.evalOrZero
    exact dif_pos hX
theorem nonSingletonSum_congr (S : ConnFamily) {n m : ℕ} (h : n = m) (f : Fin n → R4 → ℝ)
    (g : Fin m → R4 → ℝ) (hfg : ∀ i, f i = g (Fin.cast h i)) :
    nonSingletonSum S n f = nonSingletonSum S m g := by
  subst h
  have : f = g := funext hfg
  rw [this]
theorem get_map_eq_cast {α β : Type*} (g : α → β) (X : List α) (h : (X.map g).length = X.length)
    (i : Fin (X.map g).length) : (X.map g).get i = g (X.get (Fin.cast h i)) := by
  simp
theorem centeredAt_actList (S : ConnFamily) (r : EuclidMotion) {X : FnList}
    (hY : r.actList X ∈ sepAll) :
    centeredAt S (r.actList X) =
      nonSingletonSum S X.length fun i => r.actFn (X.get i) := by
  rw [centeredAt_eq_nonSingletonSum S hY]
  exact nonSingletonSum_congr S (by simp [EuclidMotion.actList]) _ _ fun i => get_map_eq_cast _ _ _ i
theorem blockTerm_actFn (S : ConnFamily) (r : EuclidMotion) {X : FnList}
    (hX : Ambient.IsSeparatedList defaultMirrorData Ambient.euclidean X) (J : Finset (Fin X.length))
    (h : FixesConnAt S r J.card) :
    blockTerm S (fun i => r.actFn (X.get i)) J = blockTerm S X.get J := by
  have hJ := Ambient.subList_mem_separatedN hX J
  have e : r.actList (Ambient.subList X J) =
      List.ofFn fun k : Fin J.card => r.actFn (X.get (J.orderEmbOfFin rfl k)) := by
    rw [EuclidMotion.actList, Ambient.subList, List.map_ofFn]
    rfl
  exact (congrArg (Ambient.ConnectedFamily.evalAt S J.card) e).symm.trans (h _ hJ)
theorem blockTerm_univ (S : ConnFamily) {n : ℕ} (f : Fin n → R4 → ℝ) :
    blockTerm S f Finset.univ =
      Ambient.ConnectedFamily.evalAt S n (List.ofFn f) := by
  have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hu : (fun k : Fin (Finset.univ : Finset (Fin n)).card => Fin.cast hc k) =
      (Finset.univ : Finset (Fin n)).orderEmbOfFin rfl :=
    Finset.orderEmbOfFin_unique rfl (fun _ => Finset.mem_univ _) (Fin.cast_strictMono hc)
  have hf : (fun k : Fin (Finset.univ : Finset (Fin n)).card =>
      f ((Finset.univ : Finset (Fin n)).orderEmbOfFin rfl k)) = fun k => f (Fin.cast hc k) :=
    funext fun k => by rw [← congrFun hu k]
  have hl : List.ofFn (fun k : Fin (Finset.univ : Finset (Fin n)).card =>
      f ((Finset.univ : Finset (Fin n)).orderEmbOfFin rfl k)) = List.ofFn f := by
    rw [hf, List.ofFn_congr hc]
    exact congrArg List.ofFn (funext fun i => congrArg f (Fin.ext rfl))
  have hb : blockTerm S f Finset.univ = Ambient.ConnectedFamily.evalAt S
      (Finset.univ : Finset (Fin n)).card (List.ofFn f) :=
    congrArg (Ambient.ConnectedFamily.evalAt S (Finset.univ : Finset (Fin n)).card) hl
  rw [hb, hc]
theorem card_lt_of_ne_indiscrete {n : ℕ} (hne : (Finset.univ : Finset (Fin n)) ≠ ⊥)
    {π : Finpartition (Finset.univ : Finset (Fin n))} (hπ : π ≠ Finpartition.indiscrete hne)
    {J : Finset (Fin n)} (hJ : J ∈ π.parts) : J.card < n := by
  by_contra hlt
  have hcard : J.card = Fintype.card (Fin n) := by
    have := Finset.card_le_univ J
    simp only [Fintype.card_fin] at this ⊢
    omega
  have huniv : J = Finset.univ := (Finset.card_eq_iff_eq_univ J).1 hcard
  refine hπ (Finpartition.ext ?_)
  ext K
  change K ∈ π.parts ↔ K ∈ ({Finset.univ} : Finset (Finset (Fin n)))
  rw [Finset.mem_singleton]
  constructor
  · intro hK
    obtain ⟨a, ha⟩ := π.nonempty_of_mem_parts hK
    rw [π.eq_of_mem_parts hK hJ ha (huniv ▸ Finset.mem_univ a), huniv]
  · rintro rfl
    exact huniv ▸ hJ
theorem nonSingletonSum_sub (S : ConnFamily) {n : ℕ} (hne : (Finset.univ : Finset (Fin n)) ≠ ⊥)
    (hn : 2 ≤ n) (f g : Fin n → R4 → ℝ)
    (h : ∀ π ∈ SetPartition.nonSingletonPartitions n, π ≠ Finpartition.indiscrete hne →
      ∏ J ∈ π.parts, blockTerm S g J = ∏ J ∈ π.parts, blockTerm S f J) :
    nonSingletonSum S n g - nonSingletonSum S n f =
      Ambient.ConnectedFamily.evalAt S n (List.ofFn g) -
        Ambient.ConnectedFamily.evalAt S n (List.ofFn f) := by
  classical
  have hP : Finpartition.indiscrete hne ∈ SetPartition.nonSingletonPartitions n := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun J hJ => ?_⟩
    have hJ' : J = Finset.univ := Finset.mem_singleton.1 hJ
    rw [hJ']
    simpa using hn
  have hprod : ∀ u : Fin n → R4 → ℝ,
      ∏ J ∈ (Finpartition.indiscrete hne).parts, blockTerm S u J =
        Ambient.ConnectedFamily.evalAt S n (List.ofFn u) := fun u => by
    change ∏ J ∈ ({Finset.univ} : Finset (Finset (Fin n))), blockTerm S u J = _
    rw [Finset.prod_singleton, blockTerm_univ]
  have hrest : ∑ π ∈ (SetPartition.nonSingletonPartitions n).erase (Finpartition.indiscrete hne),
        ∏ J ∈ π.parts, blockTerm S g J =
      ∑ π ∈ (SetPartition.nonSingletonPartitions n).erase (Finpartition.indiscrete hne),
        ∏ J ∈ π.parts, blockTerm S f J :=
    Finset.sum_congr rfl fun π hπ =>
      h π (Finset.mem_of_mem_erase hπ) (Finset.ne_of_mem_erase hπ)
  rw [nonSingletonSum, nonSingletonSum, ← Finset.add_sum_erase _ _ hP, ← Finset.add_sum_erase _ _ hP,
    hrest, hprod, hprod]
  ring
theorem actList_eq_ofFn (r : EuclidMotion) (X : FnList) :
    r.actList X = List.ofFn fun i => r.actFn (X.get i) := by
  conv_lhs => rw [← List.ofFn_get X]
  rw [EuclidMotion.actList, List.map_ofFn]
  rfl
theorem centeredAt_actList_sub (S : ConnFamily) (r : EuclidMotion) {X : FnList} (hX : X ∈ sepAll)
    (hY : r.actList X ∈ sepAll) (hlen : 2 ≤ X.length)
    (hlow : ∀ k, k < X.length → FixesConnAt S r k) :
    centeredAt S (r.actList X) - centeredAt S X =
      Ambient.ConnectedFamily.evalAt S X.length (r.actList X) -
        Ambient.ConnectedFamily.evalAt S X.length X := by
  have hne : (Finset.univ : Finset (Fin X.length)) ≠ ⊥ :=
    (Finset.univ_nonempty_iff.2 ⟨⟨0, by omega⟩⟩).ne_empty
  rw [centeredAt_actList S r hY, centeredAt_eq_nonSingletonSum S hX]
  refine (nonSingletonSum_sub S hne hlen X.get (fun i => r.actFn (X.get i))
    fun π _ hπ => Finset.prod_congr rfl fun J hJ =>
      blockTerm_actFn S r (isSeparatedList_of_mem_sepAll hX) J
        (hlow _ (card_lt_of_ne_indiscrete hne hπ hJ))).trans ?_
  have e : (List.ofFn X.get : FnList) = X := List.ofFn_get X
  exact congrArg₂ (· - ·)
    (congrArg (Ambient.ConnectedFamily.evalAt S X.length) (actList_eq_ofFn r X).symm)
    (congrArg (Ambient.ConnectedFamily.evalAt S X.length) e)
theorem fixesConn_iff_fixesCentered (S : ConnFamily) (r : EuclidMotion)
    (hr : ∀ n, ∀ X ∈ sepN n, r.actList X ∈ sepN n) :
    (∀ k, FixesConnAt S r k) ↔
      ∀ X ∈ sepAll, centeredAt S (r.actList X) = centeredAt S X := by
  have hr' : ∀ X ∈ sepAll, r.actList X ∈ sepAll := fun X hX => by
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hX
    exact Ambient.separatedN_subset_separatedAll _ _ n (hr n X hn)
  constructor
  · intro h X hX
    rw [centeredAt_actList S r (hr' X hX), centeredAt_eq_nonSingletonSum S hX]
    exact Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ =>
      blockTerm_actFn S r (isSeparatedList_of_mem_sepAll hX) J (h _)
  · intro h k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : 2 ≤ k
      · intro Y hY
        have hYs := Ambient.separatedN_subset_separatedAll _ _ k hY
        obtain rfl : Y.length = k := hY.1
        have hd := centeredAt_actList_sub S r hYs (hr' _ hYs) hk ih
        rw [h Y hYs, sub_self] at hd
        exact sub_eq_zero.1 hd.symm
      · exact fixesConnAt_of_not_two_le S r hk
theorem holds (hT : TupleRules.TupleSpanActionRules) : Holds := by
  obtain ⟨-, hI, -⟩ := hT
  have hr : ∀ (r : EuclidMotion) (n : ℕ), ∀ X ∈ sepN n,
      r.actList X ∈ sepN n := by
    intro r n X hX
    have hin : X ∈ sepNIn n Set.univ :=
      ⟨hX, Ambient.separatedN_subset_separatedAll _ _ n hX, fun _ _ => Set.subset_univ _⟩
    exact (((hI r Set.univ isOpen_univ).2.1 n).1.mapsTo hin).1
  intro S
  have hread : ∀ r : EuclidMotion, (∀ (n : ℕ) (hn : 2 ≤ n), ∀ X ∈ sepN n,
      Ambient.evalOrZero (S.fn n hn) (r.actList X) = Ambient.evalOrZero (S.fn n hn) X) →
      ∀ k, FixesConnAt S r k := by
    intro r h k
    by_cases hk : 2 ≤ k
    · intro Y hY
      rw [evalAt_eq_evalOrZero S hk, evalAt_eq_evalOrZero S hk]
      exact h k hk Y hY
    · exact fixesConnAt_of_not_two_le S r hk
  constructor
  · intro hb X hX
    exact ⟨fun v => (fixesConn_iff_fixesCentered S _ (hr _)).1
        (hread _ fun n hn Y hY => (hb n hn Y hY).1 v) X hX,
      fun w hw => ((fixesConn_iff_fixesCentered S _ (hr _)).1
        (hread _ fun n hn Y hY => ((hb n hn Y hY).2 w hw).symm) X hX).symm⟩
  · intro h n hn X hX
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · have hv := (fixesConn_iff_fixesCentered S (EuclidMotion.transl v) (hr _)).2
        (fun Y hY => (h Y hY).1 v) n X hX
      rwa [evalAt_eq_evalOrZero S hn, evalAt_eq_evalOrZero S hn] at hv
    · have hw' := (fixesConn_iff_fixesCentered S w (hr _)).2 (fun Y hY => ((h Y hY).2 w hw).symm) n X hX
      rw [evalAt_eq_evalOrZero S hn, evalAt_eq_evalOrZero S hn] at hw'
      exact hw'.symm
end YangMills.Construction.EuclideanFunctionals.InvarianceComparison
