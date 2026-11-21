import YangMills.Construction.ReflectionPositivity.CentredFunctionalsAlongAConvergentSequence
import YangMills.Construction.ReflectionPositivity.ConnectedFunctionsAtOneCutoff
import YangMills.Construction.ReflectionPositivity.MirrorsAndSides
import YangMills.Construction.ReflectionPositivity.TransportOfFunctionsAndTuplesToTheTorus
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.CenteredConvergence
open YangMills.Construction.LimitSpaces (periodizeFun periodizeList FitsInTorus)
variable {D : MirrorData}
theorem connectedSchwinger_congr {L p K : ℕ} {β : ℝ} {n m : ℕ} (h : n = m)
    {f : Fin n → PeriodicLattice.FourTorus L p → ℝ} {g : Fin m → PeriodicLattice.FourTorus L p → ℝ}
    (hfg : ∀ i, f i = g (Fin.cast h i)) :
    SchwingerFunctions.connectedSchwinger L p K β f =
      SchwingerFunctions.connectedSchwinger L p K β g := by
  subst h
  have : f = g := funext hfg
  rw [this]
theorem connectedSchwinger_get_ofFn {L p K : ℕ} {β : ℝ} {n : ℕ}
    (g : Fin n → PeriodicLattice.FourTorus L p → ℝ) :
    SchwingerFunctions.connectedSchwinger L p K β (List.ofFn g).get =
      SchwingerFunctions.connectedSchwinger L p K β g :=
  connectedSchwinger_congr List.length_ofFn fun i => by simp; rfl
theorem gibbsFunctional_get_ofFn (d : CutoffMirrors.MirrorData) {n : ℕ} (g : Fin n → d.Torus → ℝ) :
    d.gibbsFunctional (List.ofFn g).get = d.gibbsFunctional g := by
  have key : ∀ {a b : ℕ} (h : a = b) (u : Fin a → d.Torus → ℝ) (v : Fin b → d.Torus → ℝ),
      (∀ i, u i = v (Fin.cast h i)) → d.gibbsFunctional u = d.gibbsFunctional v := by
    intro a b h u v huv
    subst h
    have : u = v := funext huv
    rw [this]
  exact key List.length_ofFn _ _ fun i => by simp; rfl
theorem connectedAt_ofFn_periodic (S : LatticeDataSeq D torus) (j : ℕ+) {n : ℕ}
    (f : Fin n → torus.Point D → ℝ) :
    S.connectedAt j (List.ofFn f) =
      SchwingerFunctions.connectedSchwinger D.L D.m (S.K j) (S.β j) f :=
  (S.connectedAt_torus j _).trans (connectedSchwinger_get_ofFn f)
theorem connectedAt_ofFn_euclidean (S : LatticeDataSeq D euclidean) (j : ℕ+) {n : ℕ}
    (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    S.connectedAt j (List.ofFn f) =
      SchwingerFunctions.connectedSchwingerR4 D.L (S.exp j) (S.K j) (S.β j) f := by
  show SchwingerFunctions.connectedSchwinger D.L (S.exp j) (S.K j) (S.β j)
    (periodizeList (S.standingAt j) (List.ofFn f)).get = _
  rw [YangMills.Construction.LimitSpaces.periodizeList_ofFn]
  exact connectedSchwinger_get_ofFn _
theorem periodize_isSepLipTuple
    (hTr : YangMills.Construction.LimitSpaces.Periodization.Properties)
    (S : LatticeDataSeq D euclidean) (j : ℕ+) {n : ℕ} {g : Fin n → (Fin 4 → ℝ) → ℝ}
    (hg : YangMills.Construction.LimitSpaces.Ambient.euclidean.IsSepLipTuple D.toStandingParameters univ g)
    (hfit : FitsInTorus (S.standingAt j) (List.ofFn g)) :
    YangMills.Construction.LimitSpaces.Ambient.periodic.IsSepLipTuple (S.standingAt j) univ
      fun i => periodizeFun (S.standingAt j) (g i) :=
  ((hTr ⟨S.standingAt j, S.β j, S.β_pos j⟩).2.1 n g hg hfit).1
theorem centredAt_eq_sum_euclidean
    (hOne : CutoffMirrors.ConnectedAtCutoff.Statement)
    (hTr : YangMills.Construction.LimitSpaces.Periodization.Properties)
    (S : LatticeDataSeq D euclidean) (j : ℕ+) (X : List ((Fin 4 → ℝ) → ℝ))
    (hX : S.ReadsAt j X) :
    ((S.centredAt j X : ℝ) : ℂ) =
      ∑ π ∈ SetPartition.singletonFree X.length, ∏ J ∈ π.parts,
        S.connectedAt j (subList X J) := by
  have hfit : FitsInTorus (S.standingAt j) (List.ofFn X.get) := by
    rw [List.ofFn_get]
    exact hX.2
  have hm : S.centredAt j X = (S.mirrorDataAt j).gibbsFunctional
      fun i => periodizeFun (S.standingAt j) (X.get i) := by
    show (S.mirrorDataAt j).gibbsFunctional (periodizeList (S.standingAt j) X).get = _
    conv_lhs => rw [← List.ofFn_get X, YangMills.Construction.LimitSpaces.periodizeList_ofFn]
    exact gibbsFunctional_get_ofFn _ _
  rw [hm]
  refine (hOne.2.2.1 (S.mirrorDataAt j) X.length
    ⟨_, periodize_isSepLipTuple hTr S j hX.1 hfit⟩).trans ?_
  refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => ?_
  exact (connectedAt_ofFn_euclidean S j _).symm
theorem centredAt_eq_sum (hOne : CutoffMirrors.ConnectedAtCutoff.Statement)
    (hTr : YangMills.Construction.LimitSpaces.Periodization.Properties)
    {E : Ambient} (S : LatticeDataSeq D E) (j : ℕ+) (X : FnList D E)
    (hX : S.ReadsAt j X) :
    ((S.centredAt j X : ℝ) : ℂ) =
      ∑ π ∈ SetPartition.singletonFree X.length, ∏ J ∈ π.parts,
        S.connectedAt j (subList X J) := by
  cases E with
  | torus =>
    rw [S.centredAt_torus]
    refine (hOne.2.2.1 (S.mirrorDataAtExp j D.m) X.length ⟨X.get, hX⟩).trans ?_
    refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => ?_
    exact (connectedAt_ofFn_periodic S j _).symm
  | euclidean => exact centredAt_eq_sum_euclidean hOne hTr S j X hX
theorem isSepLipList_of_mem (hSides : Sides.HyperplaneSidesClaim) {E : Ambient}
    {X : FnList D E} (hX : X ∈ separatedAll D E) : IsSepLipList D E X := by
  have hsep := isSeparatedList_of_mem_separatedAll hX
  have hdisj : ∀ i k : Fin X.length, i ≠ k →
      Disjoint (closedSupport D E (X.get i)) (closedSupport D E (X.get k)) := by
    intro i k hik
    rcases lt_or_gt_of_ne hik with h | h
    · exact List.pairwise_iff_get.1 hsep.2 _ _ h
    · exact (List.pairwise_iff_get.1 hsep.2 _ _ h).symm
  cases E with
  | torus =>
    have hm := ((hSides D 0 0).1 .periodic).1
    exact ⟨fun i => ⟨(hm.2.2.2.2.2.2.2 _ (hsep.1 _ (List.get_mem X i))).2.2,
      (hsep.1 _ (List.get_mem X i)).2, subset_univ _⟩, fun i k hik => hdisj i k hik⟩
  | euclidean =>
    have hm := ((hSides D 0 0).1 .euclidean).1
    exact ⟨fun i => ⟨(hm.2.2.2.2.2.2.2 _ (hsep.1 _ (List.get_mem X i))).2.2,
      (hsep.1 _ (List.get_mem X i)).2, subset_univ _⟩, fun i k hik => hdisj i k hik⟩
theorem eventually_readsAt (hSides : Sides.HyperplaneSidesClaim) {E : Ambient}
    (S : LatticeDataSeq D E) {X : FnList D E} (hX : X ∈ separatedAll D E) :
    ∀ᶠ j in atTop, S.ReadsAt j X := by
  have hl := isSepLipList_of_mem hSides hX
  cases E with
  | torus => exact Eventually.of_forall fun _ => hl
  | euclidean => exact (S.eventually_fitsInTorus hX).mono fun _ h => ⟨hl, h⟩
theorem tendsto_sum_prod_blocks {q : ℕ} {a : ℕ+ → ℝ} {c : Finset (Fin q) → ℕ+ → ℂ}
    {l : Finset (Fin q) → ℝ}
    (ha : ∀ᶠ j in atTop, ((a j : ℝ) : ℂ) =
      ∑ π ∈ SetPartition.singletonFree q, ∏ J ∈ π.parts, c J j)
    (hc : ∀ J : Finset (Fin q), 2 ≤ J.card → Tendsto (c J) atTop (𝓝 ((l J : ℝ) : ℂ))) :
    Tendsto a atTop (𝓝 (∑ π ∈ SetPartition.nonSingletonPartitions q, ∏ J ∈ π.parts, l J)) := by
  have h : Tendsto (fun j => ∑ π ∈ SetPartition.nonSingletonPartitions q, ∏ J ∈ π.parts, c J j)
      atTop (𝓝 (∑ π ∈ SetPartition.nonSingletonPartitions q, ∏ J ∈ π.parts, ((l J : ℝ) : ℂ))) :=
    tendsto_finsetSum _ fun π hπ =>
      tendsto_finsetProd _ fun J hJ => hc J ((Finset.mem_filter.mp hπ).2 J hJ)
  have h' : Tendsto (fun j => ((a j : ℝ) : ℂ)) atTop
      (𝓝 (((∑ π ∈ SetPartition.nonSingletonPartitions q, ∏ J ∈ π.parts, l J : ℝ)) : ℂ)) := by
    push_cast
    refine h.congr' ?_
    filter_upwards [ha] with j hj
    rw [hj, SetPartition.singletonFree_eq_nonSingletonPartitions]
  have h₂ := (Complex.continuous_re.tendsto _).comp h'
  rw [Complex.ofReal_re] at h₂
  exact h₂.congr fun j => Complex.ofReal_re _
theorem centeredConverges (hOne : CutoffMirrors.ConnectedAtCutoff.Statement)
    (hTr : YangMills.Construction.LimitSpaces.Periodization.Properties)
    (hSides : Sides.HyperplaneSidesClaim) {E : Ambient} (S : LatticeDataSeq D E)
    (T : FunctionalFamily D E) (h : S.TendsToFamily T) : S.CenteredConverges T := by
  rintro ⟨X, hX⟩
  refine tendsto_sum_prod_blocks (c := fun J j => S.connectedAt j (subList X J))
    (l := fun J => T.eval J.card (subList X J)) ?_ ?_
  · exact (eventually_readsAt hSides S hX).mono fun j hj => centredAt_eq_sum hOne hTr S j X hj
  · intro J hJ
    have hmem := subList_mem_separatedN (isSeparatedList_of_mem_separatedAll hX) J
    rw [FunctionalFamily.eval_of_mem T hJ hmem]
    exact h J.card hJ ⟨_, hmem⟩
theorem centeredExpansion {E : Ambient} (T : FunctionalFamily D E) :
    T.CenteredExpansion := by
  refine ⟨fun X => ?_, ?_, ?_⟩
  · rw [FunctionalFamily.centeredFunctional,
      ← Finset.sum_attach (SetPartition.nonSingletonPartitions X.1.length)]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [← Finset.prod_attach π.1.parts]
    refine Finset.prod_congr rfl fun J _ => ?_
    exact FunctionalFamily.eval_of_mem T _ _
  · have hb : ∀ π : SetPartition.PartitionsFin 0, π.parts = ∅ :=
      SetPartition.parts_eq_empty_of_empty
    have hm : (⊥ : SetPartition.PartitionsFin 0) ∈ SetPartition.nonSingletonPartitions 0 := by
      rw [← SetPartition.singletonFree_eq_nonSingletonPartitions]
      exact SetPartition.mem_singletonFree_zero _
    show ∑ π ∈ SetPartition.nonSingletonPartitions 0, ∏ J ∈ π.parts, _ = (1 : ℝ)
    refine (Finset.sum_eq_single_of_mem ⊥ hm fun π _ hπ => ?_).trans ?_
    · exact absurd (Finpartition.ext (by rw [hb π, hb ⊥])) hπ
    · rw [hb ⊥]
      rfl
  · intro X hX
    have hnil : ∀ {q : ℕ}, q = 1 → SetPartition.nonSingletonPartitions q = ∅ := by
      rintro _ rfl
      rw [← SetPartition.singletonFree_eq_nonSingletonPartitions, SetPartition.singletonFree_one]
    rw [FunctionalFamily.centeredFunctional, hnil hX, Finset.sum_empty]
theorem centeredConvergesOnLip
    (hOne : CutoffMirrors.ConnectedAtCutoff.Statement)
    (hTr : YangMills.Construction.LimitSpaces.Periodization.Properties)
    (S : LatticeDataSeq D torus) (h : S.LipLimitsExist) :
    S.CenteredConvergesOnLip := by
  intro X hX
  let Z : YangMills.Construction.LimitSpaces.Ambient.periodic.SepTupleUniv D.toStandingParameters .lip
      X.length := ⟨X.get, hX⟩
  have hlim := tendsto_sum_prod_blocks (q := X.length) (a := fun j => S.centredAt j X)
    (c := fun J j => S.connectedAt j (subList X J))
    (l := fun J => open Classical in if hJ : 2 ≤ J.card then
      S.lipLimitFamily J.card hJ
        (YangMills.Construction.LimitSpaces.Ambient.periodic.restrictTuple D.toStandingParameters Z J)
      else 0)
    (Eventually.of_forall fun j => centredAt_eq_sum hOne hTr S j X hX) ?_
  · convert hlim using 2
    rw [YangMills.Construction.LimitSpaces.Ambient.centredSum,
      ← Finset.sum_attach (SetPartition.nonSingletonPartitions X.length)]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [← Finset.prod_attach π.1.parts]
    refine Finset.prod_congr rfl fun J _ => ?_
    rw [dif_pos (YangMills.Construction.LimitSpaces.Ambient.two_le_card_of_mem_nonSingleton π J)]
  · intro J hJ
    obtain ⟨r, hr⟩ := h J.card hJ
      (YangMills.Construction.LimitSpaces.Ambient.periodic.restrictTuple D.toStandingParameters Z J)
    have hval : S.lipLimitFamily J.card hJ
        (YangMills.Construction.LimitSpaces.Ambient.periodic.restrictTuple D.toStandingParameters Z J)
        = r := by
      show (limUnder atTop (S.connectedAtLip _)).re = r
      rw [hr.limUnder_eq, Complex.ofReal_re]
    simp only [dif_pos hJ, hval]
    refine hr.congr fun j => ?_
    exact (connectedAt_ofFn_periodic S j _).symm
theorem eq_of_tendsto_linear {u v w : ℕ+ → ℂ} {x y z a b : ℝ}
    (hu : Tendsto u atTop (𝓝 ((z : ℝ) : ℂ))) (hv : Tendsto v atTop (𝓝 ((x : ℝ) : ℂ)))
    (hw : Tendsto w atTop (𝓝 ((y : ℝ) : ℂ)))
    (h : ∀ᶠ j in atTop, u j = (a : ℂ) * v j + (b : ℂ) * w j) : z = a * x + b * y := by
  have h₁ : Tendsto (fun j => (a : ℂ) * v j + (b : ℂ) * w j) atTop
      (𝓝 ((a : ℂ) * (x : ℂ) + (b : ℂ) * (y : ℂ))) :=
    (hv.const_mul _).add (hw.const_mul _)
  have h₂ := tendsto_nhds_unique (hu.congr' h) h₁
  exact_mod_cast h₂
theorem eq_ofReal_re_of_im_eq_zero {c : ℂ} (h : c.im = 0) : c = ((c.re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [h])
theorem connectedAt_update_periodic (hOne : CutoffMirrors.ConnectedAtCutoff.Statement)
    (S : LatticeDataSeq D torus) (j : ℕ+) {n : ℕ} (hn : 2 ≤ n)
    (A : Fin n → Set (YangMills.Construction.LimitSpaces.Ambient.periodic.Carrier D.toStandingParameters))
    (hA : Pairwise fun i k =>
      YangMills.Construction.LimitSpaces.Ambient.periodic.PositivelySeparated D.toStandingParameters
        (A i) (A k))
    (i : Fin n) (a b : ℝ)
    (X Y Z : YangMills.Construction.LimitSpaces.Ambient.periodic.SepTupleUniv D.toStandingParameters
      .lip n)
    (hX : ∀ k, X.1 k ∈
      YangMills.Construction.LimitSpaces.Ambient.periodic.testWithin D.toStandingParameters .lip (A k))
    (hY : ∀ k, Y.1 k ∈
      YangMills.Construction.LimitSpaces.Ambient.periodic.testWithin D.toStandingParameters .lip (A k))
    (hZ : ∀ k, Z.1 k ∈
      YangMills.Construction.LimitSpaces.Ambient.periodic.testWithin D.toStandingParameters .lip (A k))
    (hYX : ∀ k, k ≠ i → Y.1 k = X.1 k) (hZX : ∀ k, k ≠ i → Z.1 k = X.1 k)
    (hi : Z.1 i = a • X.1 i + b • Y.1 i) :
    S.connectedAt j (List.ofFn Z.1) =
      (a : ℂ) * S.connectedAt j (List.ofFn X.1) + (b : ℂ) * S.connectedAt j (List.ofFn Y.1) := by
  have hc := (hOne.2.1 (S.mirrorDataAtExp j D.m) n hn).2.1
  have e := hc.2.2 A (fun _ => subset_univ _) hA i a b X Y Z hX hY hZ hYX hZX hi
  have hv : ∀ W : YangMills.Construction.LimitSpaces.Ambient.periodic.SepTupleUniv
      D.toStandingParameters .lip n,
      S.connectedAt j (List.ofFn W.1) =
        ((CutoffMirrors.ConnectedAtCutoff.connectedRe (S.mirrorDataAtExp j D.m) n W : ℝ) : ℂ) :=
    fun W => (connectedAt_ofFn_periodic S j _).trans (eq_ofReal_re_of_im_eq_zero (hc.1 W))
  rw [hv Z, hv X, hv Y]
  exact_mod_cast e
theorem connectedAt_perm_periodic (hOne : CutoffMirrors.ConnectedAtCutoff.Statement)
    (S : LatticeDataSeq D torus) (j : ℕ+) {n : ℕ} (hn : 2 ≤ n)
    (X : YangMills.Construction.LimitSpaces.Ambient.periodic.SepTupleUniv D.toStandingParameters .lip n)
    (ς : Equiv.Perm (Fin n)) :
    S.connectedAt j (List.ofFn (X.1 ∘ ς)) = S.connectedAt j (List.ofFn X.1) := by
  have hc := (hOne.2.1 (S.mirrorDataAtExp j D.m) n hn).2.1
  have e := hc.2.1 X ς
  have hv : ∀ W : YangMills.Construction.LimitSpaces.Ambient.periodic.SepTupleUniv
      D.toStandingParameters .lip n,
      S.connectedAt j (List.ofFn W.1) =
        ((CutoffMirrors.ConnectedAtCutoff.connectedRe (S.mirrorDataAtExp j D.m) n W : ℝ) : ℂ) :=
    fun W => (connectedAt_ofFn_periodic S j _).trans (eq_ofReal_re_of_im_eq_zero (hc.1 W))
  refine (hv (YangMills.Construction.LimitSpaces.Ambient.periodic.permuteTuple
    D.toStandingParameters X ς)).trans (Eq.trans ?_ (hv X).symm)
  exact_mod_cast e
theorem connectedAt_perm_euclidean (hOne : CutoffMirrors.ConnectedAtCutoff.Statement)
    (hTr : YangMills.Construction.LimitSpaces.Periodization.Properties)
    (S : LatticeDataSeq D euclidean) (j : ℕ+) {n : ℕ} (hn : 2 ≤ n)
    {g : Fin n → (Fin 4 → ℝ) → ℝ}
    (hg : YangMills.Construction.LimitSpaces.Ambient.euclidean.IsSepLipTuple D.toStandingParameters univ g)
    (hfit : FitsInTorus (S.standingAt j) (List.ofFn g)) (ς : Equiv.Perm (Fin n)) :
    S.connectedAt j (List.ofFn (g ∘ ς)) = S.connectedAt j (List.ofFn g) := by
  have hc := (hOne.2.1 (S.mirrorDataAt j) n hn).2.1
  let Y : YangMills.Construction.LimitSpaces.Ambient.periodic.SepTupleUniv
      (S.mirrorDataAt j).toStandingParameters .lip n :=
    ⟨_, periodize_isSepLipTuple hTr S j hg hfit⟩
  have e := hc.2.1 Y ς
  have h₁ := eq_ofReal_re_of_im_eq_zero
    (hc.1 (YangMills.Construction.LimitSpaces.Ambient.periodic.permuteTuple
      (S.mirrorDataAt j).toStandingParameters Y ς))
  have h₂ := eq_ofReal_re_of_im_eq_zero (hc.1 Y)
  refine (connectedAt_ofFn_euclidean S j (g ∘ ς)).trans (h₁.trans (Eq.trans ?_
    (h₂.symm.trans (connectedAt_ofFn_euclidean S j g).symm)))
  exact_mod_cast e
theorem eventually_hasDiameterLE (S : LatticeDataSeq D euclidean) {W : Set (Fin 4 → ℝ)}
    {R : ℝ} (hR : ∀ x ∈ W, TorusMetric.euclidNormVec x ≤ R) :
    ∀ᶠ j in atTop, TestFunctions.HasDiameterLE W ((S.standingAt j).side / 2) := by
  have hℓ : Tendsto S.ℓ atTop atTop := S.isSideSequence
  filter_upwards [hℓ.eventually_ge_atTop (4 * R)] with j hj
  intro x hx y hy
  have h₁ := hR x hx
  have h₂ := hR y hy
  have h₃ : TorusMetric.euclidNormVec (x - y) ≤
      TorusMetric.euclidNormVec x + TorusMetric.euclidNormVec y := by
    simp only [euclidNormVec_eq_norm, WithLp.toLp_sub]
    exact norm_sub_le _ _
  rw [side_standingAt]
  linarith
theorem exists_common_bound {n : ℕ} {C : Fin n → Set (Fin 4 → ℝ)}
    (hC : ∀ i, MetricNotions.IsCompactWrt InfiniteLattice.euclidDist (C i)) :
    ∃ R : ℝ, ∀ x ∈ ⋃ i, C i, TorusMetric.euclidNormVec x ≤ R := by
  choose R hR using fun i => exists_bound_of_isCompactWrt (hC i)
  refine ⟨∑ i, |R i|, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  exact (hR i x hi).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |R i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
theorem infSetDist_anti (s : Conventions.StandingParameters)
    {P : YangMills.Construction.LimitSpaces.Ambient}
    {A A' B B' : Set (P.Carrier s)} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    P.infSetDist s A B ≤ P.infSetDist s A' B' :=
  le_iInf₂ fun x hx => le_iInf₂ fun y hy => iInf₂_le_of_le x (hA hx) (iInf₂_le y (hB hy))
theorem connectedAt_update_euclidean
    (hOne : CutoffMirrors.ConnectedAtCutoff.Statement)
    (S : LatticeDataSeq D euclidean) (j : ℕ+) {n : ℕ} (hn : 2 ≤ n)
    (A : Fin n → Set (Fin 4 → ℝ)) (W : Set (Fin 4 → ℝ))
    (hA : Pairwise fun i k =>
      YangMills.Construction.LimitSpaces.Ambient.euclidean.PositivelySeparated D.toStandingParameters
        (A i) (A k))
    (hW : TestFunctions.HasDiameterLE W ((S.standingAt j).side / 2))
    (i : Fin n) (a b : ℝ) (f g h : Fin n → (Fin 4 → ℝ) → ℝ)
    (hf : ∀ k, f k ∈ YangMills.Construction.LimitSpaces.Ambient.euclidean.lipWithin
      (S.standingAt j) (A k ∩ W))
    (hg : ∀ k, g k ∈ YangMills.Construction.LimitSpaces.Ambient.euclidean.lipWithin
      (S.standingAt j) (A k ∩ W))
    (hgf : ∀ k, k ≠ i → g k = f k) (hhf : ∀ k, k ≠ i → h k = f k)
    (hi : h i = a • f i + b • g i) :
    S.connectedAt j (List.ofFn h) =
      (a : ℂ) * S.connectedAt j (List.ofFn f) + (b : ℂ) * S.connectedAt j (List.ofFn g) := by
  have hpos : Pairwise fun i k =>
      YangMills.Construction.LimitSpaces.Ambient.euclidean.PositivelySeparated
        (S.mirrorDataAt j).toStandingParameters (A i ∩ W) (A k ∩ W) := fun i k hik =>
    lt_of_lt_of_le (hA hik) (infSetDist_anti _ inter_subset_left inter_subset_left)
  have hdiam : TestFunctions.HasDiameterLE (⋃ k, A k ∩ W)
      (PeriodicLattice.torusSide (S.mirrorDataAt j).L (S.mirrorDataAt j).m / 2) := by
    intro x hx y hy
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    obtain ⟨k', hk'⟩ := mem_iUnion.1 hy
    exact hW x hk.2 y hk'.2
  obtain ⟨V, Φ, hV, hΦ⟩ := (hOne.2.2.2 (S.mirrorDataAt j) n hn (fun k => A k ∩ W) hpos hdiam)
  have memV : ∀ (k : Fin n) (u : (Fin 4 → ℝ) → ℝ),
      u ∈ YangMills.Construction.LimitSpaces.Ambient.euclidean.lipWithin (S.standingAt j)
        (A k ∩ W) →
      u ∈ V k := fun k u hu => by
    have : u ∈ (V k : Set ((Fin 4 → ℝ) → ℝ)) := by
      rw [hV k]
      exact hu
    exact this
  let x : (k : Fin n) → V k := fun k => ⟨f k, memV k _ (hf k)⟩
  let y : V i := ⟨g i, memV i _ (hg i)⟩
  have hval : ∀ w : (k : Fin n) → V k,
      S.connectedAt j (List.ofFn fun k => (w k : (Fin 4 → ℝ) → ℝ)) = ((Φ w : ℝ) : ℂ) :=
    fun w => (connectedAt_ofFn_euclidean S j _).trans (hΦ w).symm
  have hh : h = fun k => ((Function.update x i (a • x i + b • y) k : V k) : (Fin 4 → ℝ) → ℝ) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simpa [x, y] using hi
    · simpa [hk, x] using hhf k hk
  have hg' : g = fun k => ((Function.update x i y k : V k) : (Fin 4 → ℝ) → ℝ) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [y]
    · simpa [hk, x] using hgf k hk
  have hf' : f = fun k => ((x k : V k) : (Fin 4 → ℝ) → ℝ) := rfl
  have e : Φ (Function.update x i (a • x i + b • y)) =
      a * Φ x + b * Φ (Function.update x i y) := by
    rw [Φ.map_update_add, Φ.map_update_smul, Φ.map_update_smul, Function.update_eq_self]
    simp
  rw [hh, hg', hf', hval, hval, hval]
  exact_mod_cast e
theorem multilinearSymmetric
    (hOne : CutoffMirrors.ConnectedAtCutoff.Statement)
    (hTr : YangMills.Construction.LimitSpaces.Periodization.Properties) {E : Ambient}
    (S : LatticeDataSeq D E) (T : FunctionalFamily D E) (h : S.TendsToFamily T) :
    T.MultilinearSymmetric := by
  intro n hn
  cases E with
  | torus =>
    have hlim : ∀ X : (toLimitAmbient torus).SepTupleUniv D.toStandingParameters .cOne n,
        Tendsto (fun j => S.connectedAt j (List.ofFn X.1)) atTop
          (𝓝 ((restrictToSepTuples D torus (T n hn) X : ℝ) : ℂ)) :=
      fun X => h n hn ⟨_, listOfSepTuple_mem_separatedN D torus X⟩
    refine ⟨?_, ?_⟩
    · intro A _ hA i a b X Y Z hX hY hZ hYX hZX hi
      refine eq_of_tendsto_linear (hlim Z) (hlim X) (hlim Y) (Eventually.of_forall fun j => ?_)
      exact connectedAt_update_periodic hOne S j hn A hA i a b ⟨X.1, X.2.1⟩ ⟨Y.1, Y.2.1⟩
        ⟨Z.1, Z.2.1⟩
        (fun k => ⟨(X.2.1.1 k).1, (hX k).2⟩) (fun k => ⟨(Y.2.1.1 k).1, (hY k).2⟩)
        (fun k => ⟨(Z.2.1.1 k).1, (hZ k).2⟩) hYX hZX hi
    · intro X ς
      have e := tendsto_nhds_unique
        ((hlim ((toLimitAmbient torus).permuteTuple D.toStandingParameters X ς)).congr fun j =>
          connectedAt_perm_periodic hOne S j hn ⟨X.1, X.2.1⟩ ς) (hlim X)
      exact_mod_cast e
  | euclidean =>
    have hlim : ∀ X : (toLimitAmbient euclidean).SepTupleUniv D.toStandingParameters .cOne n,
        Tendsto (fun j => S.connectedAt j (List.ofFn X.1)) atTop
          (𝓝 ((restrictToSepTuples D euclidean (T n hn) X : ℝ) : ℂ)) :=
      fun X => h n hn ⟨_, listOfSepTuple_mem_separatedN D euclidean X⟩
    refine ⟨?_, ?_⟩
    · intro A _ hA i a b X Y Z hX hY hZ hYX hZX hi
      obtain ⟨R₁, h₁⟩ := exists_common_bound (C := fun k =>
        YangMills.Construction.LimitSpaces.Ambient.euclidean.closedSupport D.toStandingParameters
          (X.1 k)) fun k => (hX k).2.1
      obtain ⟨R₂, h₂⟩ := exists_common_bound (C := fun k =>
        YangMills.Construction.LimitSpaces.Ambient.euclidean.closedSupport D.toStandingParameters
          (Y.1 k)) fun k => (hY k).2.1
      let W : Set (Fin 4 → ℝ) :=
        (⋃ k, YangMills.Construction.LimitSpaces.Ambient.euclidean.closedSupport
            D.toStandingParameters (X.1 k)) ∪
          ⋃ k, YangMills.Construction.LimitSpaces.Ambient.euclidean.closedSupport
            D.toStandingParameters (Y.1 k)
      have hR : ∀ x ∈ W, TorusMetric.euclidNormVec x ≤ max R₁ R₂ := by
        rintro x (hx | hx)
        · exact (h₁ x hx).trans (le_max_left _ _)
        · exact (h₂ x hx).trans (le_max_right _ _)
      refine eq_of_tendsto_linear (hlim Z) (hlim X) (hlim Y) ?_
      filter_upwards [eventually_hasDiameterLE S hR] with j hW
      exact connectedAt_update_euclidean hOne S j hn A W hA hW i a b X.1 Y.1 Z.1
        (fun k => ⟨(X.2.1.1 k).1, (hX k).2.1, subset_inter (hX k).2.2
          ((subset_iUnion (fun k =>
            YangMills.Construction.LimitSpaces.Ambient.euclidean.closedSupport D.toStandingParameters
              (X.1 k)) k).trans subset_union_left)⟩)
        (fun k => ⟨(Y.2.1.1 k).1, (hY k).2.1, subset_inter (hY k).2.2
          ((subset_iUnion (fun k =>
            YangMills.Construction.LimitSpaces.Ambient.euclidean.closedSupport D.toStandingParameters
              (Y.1 k)) k).trans subset_union_right)⟩)
        hYX hZX hi
    · intro X ς
      have hfit := S.eventually_fitsInTorus
        (separatedN_subset_separatedAll D euclidean n
          (listOfSepTuple_mem_separatedN D euclidean X))
      have e := tendsto_nhds_unique
        ((hlim ((toLimitAmbient euclidean).permuteTuple D.toStandingParameters X ς)).congr'
          (hfit.mono fun j hj => connectedAt_perm_euclidean hOne hTr S j hn X.2.1 hj ς)) (hlim X)
      exact_mod_cast e
theorem centeredFunctionalsConverge_holds (hOne : CutoffMirrors.ConnectedAtCutoff.Statement)
    (hTr : YangMills.Construction.LimitSpaces.Periodization.Properties)
    (hSides : Sides.HyperplaneSidesClaim) : CenteredFunctionalsConverge :=
  ⟨fun _ _ S T h => ⟨⟨centeredConverges hOne hTr hSides S T h, centeredExpansion T⟩,
      multilinearSymmetric hOne hTr S T h⟩,
    fun _ S _ _ hL => centeredConvergesOnLip hOne hTr S hL⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.CenteredConvergence
end
