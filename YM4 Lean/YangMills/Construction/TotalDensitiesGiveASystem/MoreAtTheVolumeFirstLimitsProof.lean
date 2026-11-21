import YangMills.Construction.FamiliesOfLimits.VolumeLimitPointsAreLimitsAlongGrowingTori
import YangMills.Construction.LawByMomentsOfTheFlow.FourPointsNearALine
import YangMills.Construction.LimitTheorem.RepresentativeAndTheIdentifications
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.MoreAtTheVolumeFirstLimits
import YangMills.Construction.TotalDensitiesGiveASystem.RotationsOfSpaceActOnACompletion
import YangMills.Construction.TotalDensitiesGiveASystem.TheLawAtEightPointsInAVolumeFirstLimit
import YangMills.Construction.TotalDensitiesGiveASystem.TheTopAtTheExpansion
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
section GrowingSides
open TestSpaces (SepTupleOfCard)
open SystemsWithFiveBounds LimitTheorem
private theorem exists_growing_sides (hT : FamiliesOfLimits.InfiniteVolumeLimitsAlongGrowingTori) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {IsPair : ℕ+ → ℝ → Prop} (Q : PairSequence L IsPair)
    (hβ : ∀ j, 0 < Q.coupling j) {S : CumulantFamily} (hQ : Q.Defines S) (b : ℕ+ → ℝ) :
    ∃ m : ℕ+ → ℕ+, (∀ j, b j ≤ PeriodicLattice.torusSide L (m j)) ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) (X : SepTupleOfCard n),
        (∀ᶠ j in atTop, SchwingerFunctions.IsR4TestFamily (PeriodicLattice.torusSide L (m j)) X.1) ∧
        Tendsto (fun j => SchwingerFunctions.connectedSchwingerR4 L (m j) (Q.cutoff j) (Q.coupling j) X.1) atTop
          (𝓝 ((S n hn X : ℝ) : ℂ)) := by
  let c : ℕ+ → ℕ+ := fun i => Nat.succPNat (Nat.unpair (i : ℕ)).1
  obtain ⟨m', -, hside, hlim⟩ := hT L hL Set.univ 0 (fun _ _ _ => Set.mem_univ _) (fun i => Q.cutoff (c i))
    (fun i => Q.coupling (c i)) (fun i => Q.state (c i)) (fun i => hβ _) (fun i => Q.isLimit _)
  have key : ∀ j : ℕ+, ∃ i : ℕ+, c i = j ∧ (j : ℕ) ≤ (i : ℕ) ∧
      max (b j) 3 ≤ PeriodicLattice.torusSide L (m' i) := by
    intro j
    obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 (hside.eventually_ge_atTop (max (b j) 3))
    have hle : (max (t₀ : ℕ) (j : ℕ)) ≤ Nat.pair (PNat.natPred j) (max (t₀ : ℕ) (j : ℕ)) :=
      Nat.right_le_pair _ _
    have hpos : 0 < Nat.pair (PNat.natPred j) (max (t₀ : ℕ) (j : ℕ)) :=
      lt_of_lt_of_le (lt_of_lt_of_le j.pos (le_max_right _ _)) hle
    refine ⟨⟨_, hpos⟩, ?_, (le_max_right _ _).trans hle, ht₀ _ ?_⟩
    · apply PNat.eq
      simp [c, Nat.unpair_pair]
    · show (t₀ : ℕ) ≤ _
      exact (le_max_left _ _).trans hle
  choose i hi₁ hi₂ hi₃ using key
  have hm : ∀ j, 0 < m' (i j) := fun j => by
    rcases Nat.eq_zero_or_pos (m' (i j)) with h | h
    · have := (le_max_right _ _).trans (hi₃ j)
      rw [h] at this
      norm_num [PeriodicLattice.torusSide] at this
    · exact h
  have hti : Tendsto i atTop atTop := tendsto_atTop_mono (fun j => by
    show j ≤ i j
    exact hi₂ j) tendsto_id
  refine ⟨fun j => ⟨m' (i j), hm j⟩, fun j => (le_max_left _ _).trans (hi₃ j), fun n hn X => ?_⟩
  obtain ⟨h₁, h₂⟩ := hlim n hn X
  refine ⟨hti.eventually h₁, ?_⟩
  have h₃ := (h₂.comp hti).add (hQ n hn X)
  rw [zero_add] at h₃
  refine h₃.congr fun j => ?_
  have e₁ : SchwingerFunctions.connectedSchwingerR4 L (m' (i j)) (Q.cutoff (c (i j))) (Q.coupling (c (i j))) X.1 =
      SchwingerFunctions.connectedSchwingerR4 L (m' (i j)) (Q.cutoff j) (Q.coupling j) X.1 := by rw [hi₁ j]
  have e₂ : InfiniteLattice.smearedEnergyCumulant (Q.state (c (i j))) X.1 =
      InfiniteLattice.smearedEnergyCumulant (Q.state j) X.1 :=
    congrArg (fun u => InfiniteLattice.smearedEnergyCumulant (Q.state u) X.1) (hi₁ j)
  simp only [Function.comp_apply, e₁, e₂, sub_add_cancel, PNat.mk_coe]
end GrowingSides
section SpatialRotations
open TestSpaces (SepTupleOfCard)
open SystemsWithFiveBounds LimitTheorem SeparatedTuples
open TupleLists (ofList toList toList_ofList)
open TestFunctions (closedBallR4 setDistR4 sharpNormR4)
open Continuum.RotationModulus (RotationHypotheses)
open OrthogonalAction Orthogonal
private def sepTupleOfList (X : SepTuple) {n : ℕ} (h : X.1.length = n) : SepTupleOfCard n := h ▸ (ofList X).2
private theorem toList_sepTupleOfList (X : SepTuple) {n : ℕ} (h : X.1.length = n) :
    toList ⟨n, sepTupleOfList X h⟩ = X := by
  subst h
  exact toList_ofList X
private theorem sepTupleOfList_apply (X : SepTuple) {n : ℕ} (h : X.1.length = n) (k : Fin n) :
    (sepTupleOfList X h).1 k = X.1[k.1]'(by omega) := by
  subst h
  rfl
private theorem getElem_append_cons_ne {α : Type*} (A B : List α) (f f' : α) (j : ℕ) (hj : j ≠ A.length)
    (h : j < (A ++ f :: B).length) (h' : j < (A ++ f' :: B).length) :
    (A ++ f :: B)[j]'h = (A ++ f' :: B)[j]'h' := by
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · rw [List.getElem_append_left hlt, List.getElem_append_left hlt]
  · rw [List.getElem_append_right hgt.le, List.getElem_append_right hgt.le]
    simp [List.getElem_cons, show j - A.length ≠ 0 by omega]
private theorem isEntrywiseLinear_of_isSepFunctional {σ : TupleFunctional}
    (hf : TestSpaces.IsSepFunctional (evalOnMap σ)) : σ.IsEntrywiseLinear := by
  intro A B f f' α α' X X' Z hX hX' hZ
  have hl : X.1.length = A.length + 1 + B.length := by rw [hX]; simp; omega
  have hl' : X'.1.length = A.length + 1 + B.length := by rw [hX']; simp; omega
  have hl'' : Z.1.length = A.length + 1 + B.length := by rw [hZ]; simp; omega
  have key := hf.2 (A.length + 1 + B.length) (by omega) ⟨A.length, by omega⟩ α α' (sepTupleOfList X hl)
    (sepTupleOfList X' hl') (sepTupleOfList Z hl'') ?_ ?_ ?_
  · simpa only [evalOnMap, toList_sepTupleOfList] using key
  · intro j hj
    have hj' : j.1 ≠ A.length := fun e => hj (Fin.ext e)
    rw [sepTupleOfList_apply, sepTupleOfList_apply, List.getElem_of_eq hX, List.getElem_of_eq hX']
    exact getElem_append_cons_ne A B f f' j.1 hj' _ _
  · rw [sepTupleOfList_apply, sepTupleOfList_apply, sepTupleOfList_apply, List.getElem_of_eq hX,
      List.getElem_of_eq hX', List.getElem_of_eq hZ]
    simp
  · intro j hj
    have hj' : j.1 ≠ A.length := fun e => hj (Fin.ext e)
    rw [sepTupleOfList_apply, sepTupleOfList_apply, List.getElem_of_eq hX, List.getElem_of_eq hZ]
    exact getElem_append_cons_ne A B _ f j.1 hj' _ _
private def partitionBound (C : LimitConstants) (k : ℕ) (d R : ℝ) : ℝ :=
  ∑ η ∈ TestSpaces.partitionsNoSingletons (Fin k), ∏ J ∈ η, C.localBound J.card d R
private theorem prod_orderEmbOfFin {n : ℕ} (J : Finset (Fin n)) (g : Fin n → ℝ) :
    ∏ k, g (J.orderEmbOfFin rfl k) = ∏ i ∈ J, g i := by
  rw [← Finset.prod_coe_sort J g]
  exact Fintype.prod_equiv (J.orderIsoOfFin rfl).toEquiv _ _ fun k => by simp
private theorem abs_centredOf_le {S : CumulantFamily} {C : LimitConstants}
    (hb : LocalCumulantBounds 1 C (centredOf S)) (hc : HasCumulants (centredOf S) S)
    {n : ℕ} (Y : SepTupleOfCard n) {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (hball : ∀ i, ∃ x, tsupport (Y.1 i) ⊆ closedBallR4 x R)
    (hsep : ∀ i l, i ≠ l → ENNReal.ofReal d ≤ setDistR4 (tsupport (Y.1 i)) (tsupport (Y.1 l))) :
    |TestSpaces.centredOfCumulants S ⟨n, Y⟩| ≤ partitionBound C n d R * ∏ i, sharpNormR4 1 (Y.1 i) := by
  set P := ∏ i, sharpNormR4 1 (Y.1 i) with hP
  have hterm : ∀ (η : Finset (Finset (Fin n))) (hη : η ∈ TestSpaces.partitionsNoSingletons (Fin n)),
      |∏ J ∈ η.attach, S J.1.card (TestSpaces.two_le_card_of_mem_partitionsNoSingletons hη J.2)
        (TestSpaces.sepRestrict Y J.1)| ≤ (∏ J ∈ η, C.localBound J.card d R) * P := by
    intro η hη
    have hpart : (η : Set (Finset (Fin n))).PairwiseDisjoint id ∧ η.biUnion id = Finset.univ := by
      have h := hη
      simp only [TestSpaces.partitionsNoSingletons, ClusterExpansion.SymGraph.partitions,
        ClusterExpansion.SymGraph.IsPartition, Finset.mem_filter, Finset.mem_univ, true_and] at h
      obtain ⟨hd, hu⟩ := h.1.2
      refine ⟨hd, ?_⟩
      convert hu
    have hone : ∀ J : {J // J ∈ η}, |S J.1.card (TestSpaces.two_le_card_of_mem_partitionsNoSingletons hη J.2)
        (TestSpaces.sepRestrict Y J.1)| ≤ C.localBound J.1.card d R * ∏ i ∈ J.1, sharpNormR4 1 (Y.1 i) := by
      intro J
      have h2 := TestSpaces.two_le_card_of_mem_partitionsNoSingletons hη J.2
      have hB := (hb J.1.card h2 R hR d hd (TestSpaces.sepRestrict Y J.1) (fun i => hball _)
        (fun i l hil => hsep _ _ fun e => hil ((J.1.orderEmbOfFin rfl).injective e))).1
      rw [hc J.1.card h2] at hB
      have e := prod_orderEmbOfFin J.1 fun i => sharpNormR4 1 (Y.1 i)
      refine hB.trans (le_of_eq ?_)
      rw [← e]
      rfl
    rw [Finset.abs_prod]
    refine (Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun J _ => hone J).trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_attach η fun J => C.localBound J.card d R,
      Finset.prod_attach η fun J => ∏ i ∈ J, sharpNormR4 1 (Y.1 i), hP]
    congr 1
    have e := Finset.prod_biUnion (s := η) (t := id) (f := fun i => sharpNormR4 1 (Y.1 i)) hpart.1
    rw [hpart.2] at e
    exact e.symm
  unfold TestSpaces.centredOfCumulants partitionBound
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul, ← Finset.sum_attach (TestSpaces.partitionsNoSingletons (Fin n))]
  exact Finset.sum_le_sum fun η _ => hterm η.1 η.2
private theorem setDistR4_comm (S T : Set (Fin 4 → ℝ)) : setDistR4 S T = setDistR4 T S := by
  unfold setDistR4
  rw [iInf₂_comm]
  refine iInf_congr fun y => iInf_congr fun _ => iInf_congr fun x => iInf_congr fun _ => ?_
  congr 1
  unfold TorusMetric.euclidNormVec
  congr 1
  exact Finset.sum_congr rfl fun μ _ => by simp only [Pi.sub_apply]; ring
private theorem rotationHypotheses_of {ϑ d₀ : ℝ} {ηBar : ℝ → ℝ} {C : LimitConstants} {L : ℕ}
    {IsPair : ℕ+ → ℝ → Prop} {Q : PairSequence L IsPair} {S : CumulantFamily}
    (A : ErgodicDecompositionConclusion 1 ϑ d₀ ηBar C Q S) (hC : C.Valid)
    (hS : CutoffRepresentatives.CentredSymmetriesAndCumulants S) :
    RotationHypotheses 1 (centredOf S) (partitionBound C) := by
  refine ⟨isEntrywiseLinear_of_isSepFunctional A.limit.distributions.1, A.limit.symmetries.centred_symm,
    A.limit.axialPositive _ ⟨_, rfl⟩, fun k _ d R hd hR => ?_, fun k _ d R hd hR X hk hball hsep => ?_,
    fun Rm => ?_⟩
  · refine Finset.sum_nonneg fun η hη => Finset.prod_nonneg fun J hJ => ?_
    exact (hC.localBound_pos _ (TestSpaces.two_le_card_of_mem_partitionsNoSingletons hη hJ) d R hd hR).le
  · subst hk
    have hv := abs_centredOf_le A.limit.conditions.localBounds A.limit.conditions.cumulants_eq (ofList X).2 hd hR
      (fun i => hball _ (List.get_mem _ _)) (fun i l hil => ?_)
    · have e₁ : ∏ i, sharpNormR4 1 ((ofList X).2.1 i) = (X.1.map (sharpNormR4 1)).prod :=
        Fin.prod_univ_fun_getElem _ _
      rw [e₁] at hv
      exact hv
    · rcases lt_or_gt_of_ne hil with hlt | hlt
      · exact List.pairwise_iff_get.1 hsep i l hlt
      · rw [setDistR4_comm]
        exact List.pairwise_iff_get.1 hsep l i hlt
  · have h := (hS.2.1 (ofOrthogonal (embedOrthogonal Rm))).2 (A.limit.rotationInv (embedOrthogonal Rm))
    have hm : (ofOrthogonal (embedOrthogonal Rm)).toFun = matMap (embedOrthogonal Rm) := funext fun x => by
      simp [ofOrthogonal, Motions.RigidMotion.toFun, matMap]
    unfold IsMotionInvariant at h
    rwa [hm] at h
private theorem spatialRotationRep_of (hRot : RotationsActOnCompletion.Statement)
    (hI : CutoffRepresentatives.IdentificationsHold) {ϑ d₀ : ℝ} {ηBar : ℝ → ℝ} {C : LimitConstants} {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {IsPair : ℕ+ → ℝ → Prop}
    {Q : PairSequence L IsPair} {S : CumulantFamily} (A : ErgodicDecompositionConclusion 1 ϑ d₀ ηBar C Q S)
    (hC : C.Valid) : SpatialRotationRep (centredOf S) := by
  have hS := (hI L hL Q.cutoff Q.state (fun j => (Q.isLimit j).1) S).2.2
  obtain ⟨-, -, h, hrec, -⟩ := A.limit.conditions.reconstruction
  exact hRot 1 _ _ h le_rfl (rotationHypotheses_of A hC hS) hrec
end SpatialRotations
section LimitsOfNumbers
open TestSpaces (SepTupleOfCard)
open SystemsWithFiveBounds LimitTheorem SeparatedTuples
private theorem tendsto_log_two_pow : Tendsto (fun i : ℕ => Real.log ((2 : ℝ) ^ i)) atTop atTop := by
  have h : (fun i : ℕ => Real.log ((2 : ℝ) ^ i)) = fun i : ℕ => (i : ℝ) * Real.log 2 := by
    funext i
    rw [Real.log_pow]
  rw [h]
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos (by norm_num))
private theorem log_two_pow_div {δ : ℝ} (hδ : 0 < δ) (i : ℕ) :
    Real.log ((2 : ℝ) ^ i / δ) = Real.log ((2 : ℝ) ^ i) - Real.log δ := by
  rw [Real.log_div (by positivity) hδ.ne']
private theorem tendsto_scaled_of_coupling_ratio {n : ℕ} {a δ L C : ℝ} (ha : 0 < a) (hδ : 0 < δ) {x v : ℕ → ℝ}
    (hx : Tendsto (fun i : ℕ => x i / (a⁻¹ * Real.log ((2 : ℝ) ^ i / δ))) atTop (𝓝 1))
    (hv : ∀ᶠ i in atTop, |x i ^ n * v i - L| ≤ C * x i ^ (-(1 / 100) : ℝ)) :
    Tendsto (fun i : ℕ => (Real.log ((2 : ℝ) ^ i) / a) ^ n * v i) atTop (𝓝 L) := by
  have hl := tendsto_log_two_pow
  have hl' : Tendsto (fun i : ℕ => Real.log ((2 : ℝ) ^ i / δ)) atTop atTop := by
    simp only [log_two_pow_div hδ]
    exact tendsto_atTop_add_const_right _ _ hl
  have hb : Tendsto (fun i : ℕ => a⁻¹ * Real.log ((2 : ℝ) ^ i / δ)) atTop atTop :=
    hl'.const_mul_atTop (inv_pos.2 ha)
  have hxt : Tendsto x atTop atTop := by
    have h := hx.pos_mul_atTop one_pos hb
    refine h.congr' ?_
    filter_upwards [hb.eventually_gt_atTop 0] with i hi
    exact div_mul_cancel₀ _ hi.ne'
  have hr : Tendsto (fun i : ℕ => Real.log ((2 : ℝ) ^ i) / Real.log ((2 : ℝ) ^ i / δ)) atTop (𝓝 1) := by
    have h₁ : Tendsto (fun i : ℕ => Real.log δ / Real.log ((2 : ℝ) ^ i / δ)) atTop (𝓝 0) :=
      hl'.const_div_atTop _
    have h₂ := h₁.const_add 1
    rw [add_zero] at h₂
    refine h₂.congr' ?_
    filter_upwards [hl'.eventually_gt_atTop 0] with i hi
    have e := log_two_pow_div hδ i
    field_simp
    linarith
  have ht : Tendsto (fun i : ℕ => Real.log ((2 : ℝ) ^ i) / a / x i) atTop (𝓝 1) := by
    have h := hr.div hx one_ne_zero
    rw [div_one] at h
    refine h.congr' ?_
    filter_upwards [hb.eventually_gt_atTop 0, hxt.eventually_gt_atTop 0, hl'.eventually_gt_atTop 0]
      with i h₁ h₂ h₃
    simp only [Pi.div_apply]
    field_simp
  have hw : Tendsto (fun i : ℕ => x i ^ n * v i) atTop (𝓝 L) := by
    have h₀ : Tendsto (fun i : ℕ => C * x i ^ (-(1 / 100) : ℝ)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 100 by norm_num)).comp hxt
      simpa using this.const_mul C
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ h₀
    filter_upwards [hv] with i hi
    simpa using hi
  have hp := (ht.pow n).mul hw
  rw [one_pow, one_mul] at hp
  refine hp.congr' ?_
  filter_upwards [hxt.eventually_gt_atTop 0] with i hi
  rw [div_pow, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero n hi.ne')]
private theorem continuous_connectedFn {A : DecompositionData} {σ : TupleFunctional} (hA : A.IsCanonical σ)
    {n : ℕ} (X : SepTupleOfCard n) : Continuous fun ξ => connectedFn (A.comp ξ) X := by
  unfold connectedFn TestSpaces.cumulant
  exact continuous_finsetSum _ fun η _ => continuous_const.mul
    (continuous_finsetProd _ fun J _ => hA.continuous_comp _)
private theorem gaussianComponents_small {A : DecompositionData} {σ : TupleFunctional} (hA : A.IsCanonical σ)
    {X : SepTupleOfCard 4} {Y : ℕ → SepTupleOfCard 4} {u : ℕ → ℝ} (hpos : 0 < shortDistanceLimit X.1)
    (hae : ∀ᵐ ξ ∂A.law, Tendsto (fun i : ℕ => u i ^ 4 * connectedFn (A.comp ξ) (Y i)) atTop
      (𝓝 (shortDistanceLimit X.1))) :
    IsClosed {ξ : A.space | ∀ (n : ℕ), 3 ≤ n → ∀ X : SepTupleOfCard n, connectedFn (A.comp ξ) X = 0} ∧
      A.law {ξ : A.space | ∀ (n : ℕ), 3 ≤ n → ∀ X : SepTupleOfCard n, connectedFn (A.comp ξ) X = 0} = 0 ∧
      interior {ξ : A.space | ∀ (n : ℕ), 3 ≤ n → ∀ X : SepTupleOfCard n, connectedFn (A.comp ξ) X = 0} = ∅ := by
  set G := {ξ : A.space | ∀ (n : ℕ), 3 ≤ n → ∀ X : SepTupleOfCard n, connectedFn (A.comp ξ) X = 0} with hG
  have hnull : A.law G = 0 := by
    have h : ∀ᵐ ξ ∂A.law, ξ ∉ G := hae.mono fun ξ hξ hin => by
      have h0 : (fun i : ℕ => u i ^ 4 * connectedFn (A.comp ξ) (Y i)) = fun _ => 0 := by
        funext i
        rw [hin 4 (by norm_num) (Y i), mul_zero]
      rw [h0] at hξ
      exact hpos.ne (tendsto_nhds_unique tendsto_const_nhds hξ)
    have := ae_iff.1 h
    simpa using this
  refine ⟨?_, hnull, ?_⟩
  · simp only [hG, Set.ofPred_forall]
    exact isClosed_iInter fun n => isClosed_iInter fun _ => isClosed_iInter fun X =>
      isClosed_eq (continuous_connectedFn hA X) continuous_const
  · refine Set.eq_empty_of_forall_notMem fun ξ hξ => ?_
    have hs : ξ ∈ measureSupport A.law := by
      rw [hA.measureSupport_eq]
      exact Set.mem_univ _
    exact hs ⟨interior G, ⟨isOpen_interior, measure_mono_null interior_subset hnull⟩, hξ⟩
private theorem dyadicRescale_mem {n : ℕ} (X : SepTupleOfCard n) (i : ℕ) :
    dyadicRescale i X.1 ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) n := by
  have h2 : ((2 : ℝ) ^ i) ≠ 0 := by positivity
  let φ : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) := Homeomorph.smulOfNeZero ((2 : ℝ) ^ i) h2
  have hφ : ∀ f : (Fin 4 → ℝ) → ℝ, (fun x => f ((2 : ℝ) ^ i • x)) = f ∘ φ := fun f => rfl
  refine ⟨fun k => ⟨?_, ?_, Set.subset_univ _⟩, fun k l hkl => ?_⟩
  · exact (X.2.1 k).1.comp (contDiff_const_smul _)
  · show HasCompactSupport (fun x => X.1 k ((2 : ℝ) ^ i • x))
    rw [hφ]
    exact (X.2.1 k).2.1.comp_homeomorph φ
  · show Disjoint (tsupport (fun x => X.1 k ((2 : ℝ) ^ i • x))) (tsupport (fun x => X.1 l ((2 : ℝ) ^ i • x)))
    rw [hφ, hφ, tsupport_comp_eq_preimage, tsupport_comp_eq_preimage]
    exact (X.2.2 hkl).preimage φ
section CollinearBumps
open MomentLaw (supDist IsSupTestFamily)
private abbrev EuclideanFour : Type := EuclideanSpace ℝ (Fin 4)
private def firstAxisUnit : EuclideanFour := EuclideanSpace.single 0 1
private theorem norm_firstAxisUnit : ‖firstAxisUnit‖ = 1 := by simp [firstAxisUnit]
private def bumpCentre (i : Fin 4) : EuclideanFour := ((i : ℕ) : ℝ) • firstAxisUnit
private theorem norm_sub_le_two_mul_supDist (x y : EuclideanFour) : ‖x - y‖ ≤ 2 * _root_.YangMills.Construction.MomentLaw.supDist x y := by
  have hb : BddAbove (Set.range fun a : Fin 4 => |x a - y a|) := (Set.finite_range _).bddAbove
  have h₁ : ∀ a, |x a - y a| ≤ _root_.YangMills.Construction.MomentLaw.supDist x y := fun a => le_ciSup hb a
  have h₀ : 0 ≤ _root_.YangMills.Construction.MomentLaw.supDist x y := (abs_nonneg _).trans (h₁ 0)
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h₂ : ∀ a, ‖(x - y) a‖ ^ 2 ≤ _root_.YangMills.Construction.MomentLaw.supDist x y ^ 2 := fun a => by
    have : ‖(x - y) a‖ = |x a - y a| := by simp [Real.norm_eq_abs]
    rw [this]
    exact pow_le_pow_left₀ (abs_nonneg _) (h₁ a) 2
  have h₃ : ∑ a, ‖(x - y) a‖ ^ 2 ≤ ∑ _a : Fin 4, _root_.YangMills.Construction.MomentLaw.supDist x y ^ 2 := Finset.sum_le_sum fun a _ => h₂ a
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h₃
  have e : (2 * _root_.YangMills.Construction.MomentLaw.supDist x y) ^ 2 = ((4 : ℕ) : ℝ) * _root_.YangMills.Construction.MomentLaw.supDist x y ^ 2 := by
    push_cast
    ring
  rw [e]
  exact h₃
private theorem near_axis_of_near_centres {i j : Fin 4} (hij : i ≠ j) {x y : EuclideanFour}
    (hx : ‖x - bumpCentre i‖ ≤ 1 / 64) (hy : ‖y - bumpCentre j‖ ≤ 1 / 64) :
    63 / 64 * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) firstAxisUnit ^ 2 ∧ 1 / 2 ≤ ‖x - y‖ := by
  set t : ℝ := ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) with ht
  set w : EuclideanFour := (x - bumpCentre i) - (y - bumpCentre j) with hw
  have hsplit : x - y = t • firstAxisUnit + w := by
    simp only [hw, bumpCentre, ht, sub_smul]
    abel
  have hwn : ‖w‖ ≤ 1 / 32 := by
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hwn0 : 0 ≤ ‖w‖ := norm_nonneg _
  set p : ℝ := inner ℝ w firstAxisUnit with hp
  have hpabs : |p| ≤ ‖w‖ := by
    have := abs_real_inner_le_norm w firstAxisUnit
    rwa [norm_firstAxisUnit, mul_one] at this
  have hp2 : p ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [← sq_abs p]
    exact pow_le_pow_left₀ (abs_nonneg _) hpabs 2
  have ht1 : 1 ≤ t ^ 2 := by
    have hne : ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) ≠ 0 := by
      intro e
      exact hij (Fin.ext (by omega))
    have h₁ : (1 : ℤ) ≤ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ 2 := by
      have := Int.one_le_abs hne
      nlinarith [sq_abs (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)), abs_nonneg (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))]
    have h₂ : ((1 : ℤ) : ℝ) ≤ (((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h₁
    simpa [ht] using h₂
  have hinner : inner ℝ (x - y) firstAxisUnit = t + p := by
    rw [hsplit, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_firstAxisUnit]
    simp [hp]
  have hnorm : ‖x - y‖ ^ 2 = t ^ 2 + 2 * t * p + ‖w‖ ^ 2 := by
    rw [hsplit, norm_add_sq_real, norm_smul, real_inner_smul_left, norm_firstAxisUnit, real_inner_comm, ← hp]
    simp only [Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hW : ‖w‖ ^ 2 ≤ 1 / 1024 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [hinner, hnorm]
    nlinarith [sq_nonneg (t + 2 * p), sq_nonneg p]
  · have h₃ : (1 / 2 : ℝ) ^ 2 ≤ ‖x - y‖ ^ 2 := by
      rw [hnorm]
      nlinarith [sq_nonneg (t + 2 * p), sq_nonneg p]
    exact (sq_le_sq₀ (by norm_num) (norm_nonneg _)).1 h₃
private theorem exists_positive_quadruple (hF : MomentLaw.nearlyCollinearPositivityStatement) :
    ∃ (X : SepTupleOfCard 4) (Y : ℕ → SepTupleOfCard 4), (∀ i, (Y i).1 = dyadicRescale i X.1) ∧
      0 < shortDistanceLimit X.1 := by
  let b : ContDiffBump (0 : EuclideanFour) := ⟨1 / 128, 1 / 64, by norm_num, by norm_num⟩
  have hbc : ContDiff ℝ 1 (b : EuclideanFour → ℝ) := b.contDiff
  obtain ⟨Kl, hK⟩ := hbc.lipschitzWith_of_hasCompactSupport b.hasCompactSupport one_ne_zero
  set s : ℝ := 1 / (1 + 2 * (Kl : ℝ)) with hs
  have hK0 : (0 : ℝ) ≤ Kl := Kl.2
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one (by positivity)]
    linarith
  have hsK : s * (2 * (Kl : ℝ)) ≤ 1 := by
    rw [hs, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  let φ : Fin 4 → EuclideanFour → ℝ := fun i x => s * b (x - bumpCentre i)
  have hsup : ∀ i, Function.support (φ i) ⊆ Metric.closedBall (bumpCentre i) (1 / 64) := fun i x hx => by
    have h₁ : x - bumpCentre i ∈ Function.support (b : EuclideanFour → ℝ) := fun h => hx (by simp [φ, h])
    have h₂ := subset_tsupport _ h₁
    rw [b.tsupport_eq] at h₂
    simpa [dist_eq_norm, b] using h₂
  have htsup : ∀ i, tsupport (φ i) ⊆ Metric.closedBall (bumpCentre i) (1 / 64) := fun i =>
    closure_minimal (hsup i) Metric.isClosed_closedBall
  have hnear : ∀ i x, x ∈ tsupport (φ i) → ‖x - bumpCentre i‖ ≤ 1 / 64 := fun i x hx => by
    simpa [dist_eq_norm] using htsup i hx
  have hcomp : ∀ i, HasCompactSupport (φ i) := fun i =>
    HasCompactSupport.intro (isCompact_closedBall (bumpCentre i) (1 / 64)) fun x hx => by
      by_contra h
      exact hx (hsup i h)
  have hcentre : ∀ i : Fin 4, ‖bumpCentre i‖ ≤ 3 := fun i => by
    have hi : ((i : ℕ) : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ i.2
    simpa [bumpCentre, norm_smul, norm_firstAxisUnit] using hi
  have htest : IsSupTestFamily 5 (1 / 4) φ := by
    refine ⟨fun i x => ?_, fun i x y => ?_, hcomp, fun i x hx a => ?_, fun i j hij x hx y hy => ?_⟩
    · have h₀ : 0 ≤ b (x - bumpCentre i) := b.nonneg
      have h₁ : b (x - bumpCentre i) ≤ 1 := b.le_one
      rw [abs_of_nonneg (mul_nonneg hs0.le h₀)]
      exact mul_le_one₀ hs1 h₀ h₁
    · have h₁ := hK.dist_le_mul (x - bumpCentre i) (y - bumpCentre i)
      have h₂ : dist (x - bumpCentre i) (y - bumpCentre i) = ‖x - y‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      rw [h₂, Real.dist_eq] at h₁
      have h₃ := norm_sub_le_two_mul_supDist x y
      have h₄ : 0 ≤ _root_.YangMills.Construction.MomentLaw.supDist x y := by nlinarith [norm_nonneg (x - y)]
      show |s * b (x - bumpCentre i) - s * b (y - bumpCentre i)| ≤ _root_.YangMills.Construction.MomentLaw.supDist x y
      rw [← mul_sub, abs_mul, abs_of_pos hs0]
      calc s * |b (x - bumpCentre i) - b (y - bumpCentre i)| ≤ s * ((Kl : ℝ) * (2 * _root_.YangMills.Construction.MomentLaw.supDist x y)) :=
            mul_le_mul_of_nonneg_left (h₁.trans (mul_le_mul_of_nonneg_left h₃ hK0)) hs0.le
        _ = s * (2 * (Kl : ℝ)) * _root_.YangMills.Construction.MomentLaw.supDist x y := by ring
        _ ≤ 1 * _root_.YangMills.Construction.MomentLaw.supDist x y := mul_le_mul_of_nonneg_right hsK h₄
        _ = _root_.YangMills.Construction.MomentLaw.supDist x y := one_mul _
    · have h₁ : ‖x.ofLp a‖ ≤ ‖x‖ := PiLp.norm_apply_le x a
      have h₂ : ‖x‖ ≤ ‖x - bumpCentre i‖ + ‖bumpCentre i‖ := by
        simpa using norm_add_le (x - bumpCentre i) (bumpCentre i)
      have h₃ := hnear i x hx
      have h₄ := hcentre i
      rw [Real.norm_eq_abs] at h₁
      linarith
    · have h₁ := (near_axis_of_near_centres hij (hnear i x hx) (hnear j y hy)).2
      have h₂ := norm_sub_le_two_mul_supDist x y
      linarith
  have hpos := (hF φ 5 (1 / 4) (by norm_num) htest (fun i x => mul_nonneg hs0.le b.nonneg)
    (fun i => ⟨bumpCentre i, ?_⟩) firstAxisUnit norm_firstAxisUnit fun i j hij x hx y hy =>
      (near_axis_of_near_centres hij (hnear i x hx) (hnear j y hy)).1).2
  · let T : (Fin 4 → ℝ) ≃L[ℝ] EuclideanFour := (EuclideanSpace.equiv (Fin 4) ℝ).symm
    have hmem : (fun i => φ i ∘ T) ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) 4 := by
      refine ⟨fun i => ⟨?_, ?_, Set.subset_univ _⟩, fun i j hij => ?_⟩
      · have h₁ : ContDiff ℝ 1 (φ i) := contDiff_const.mul (hbc.comp (contDiff_id.sub contDiff_const))
        exact h₁.comp T.contDiff
      · exact (hcomp i).comp_homeomorph T.toHomeomorph
      · show Disjoint (tsupport (φ i ∘ T.toHomeomorph)) (tsupport (φ j ∘ T.toHomeomorph))
        rw [tsupport_comp_eq_preimage, tsupport_comp_eq_preimage]
        refine Disjoint.preimage _ (Set.disjoint_left.2 fun x hx hy => ?_)
        have h₁ := (near_axis_of_near_centres hij (hnear i x hx) (hnear j x hy)).2
        simp at h₁
        linarith
    let X : SepTupleOfCard 4 := ⟨_, hmem⟩
    refine ⟨X, fun i => ⟨_, dyadicRescale_mem X i⟩, fun i => rfl, ?_⟩
    have e : (fun k (x : EuclideanFour) => X.1 k (WithLp.ofLp x)) = φ := by
      funext k x
      show φ k (T (WithLp.ofLp x)) = φ k x
      congr 1
    show 0 < CyclicFormula.cyclicMomentFormula 4 fun k x => X.1 k (WithLp.ofLp x)
    rw [e]
    exact hpos
  · have h₁ : b (bumpCentre i - bumpCentre i) = 1 := by
      rw [sub_self]
      exact b.one_of_mem_closedBall (by simp [b])
    show s * b (bumpCentre i - bumpCentre i) ≠ 0
    rw [h₁, mul_one]
    exact hs0.ne'
end CollinearBumps
end LimitsOfNumbers
section CouplingAtScale
open TestSpaces (SepTupleOfCard)
open SystemsWithFiveBounds LimitTheorem
private def CouplingAtScaleAtParameters (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : Prop :=
  ∀ Bs : ℝ, 2 * T.B ≤ Bs → ForSmallCoupling fun g => ∃ e : ℝ → ℝ, Tendsto e (𝓝[>] 0) (𝓝 0) ∧
    ∀ (K : ℕ) (β : ℝ), 2 ≤ K → IsFirstPassagePoint (T.stepParameters y) Bs g K β → ∀ k ≤ K, ∀ d : ℝ, d < 1 →
      1 ≤ d / ((T.stepParameters y).side : ℝ) ^ ((k : ℤ) - (K : ℤ)) →
      d / ((T.stepParameters y).side : ℝ) ^ ((k : ℤ) - (K : ℤ)) ≤ ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β k →
      |ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β k / (TrajectoryData.logSlope * Real.log (1 / d)) - 1| ≤ e d
private theorem couplingAtScale_of_trajectoryData (hD : TrajectoryData.trajectoryDataStatement) :
    HoldsAtAdmissibleParameters CouplingAtScaleAtParameters := by
  obtain ⟨Qc, hQ, floorL, ceilRt, ceilσ, floorN, floorCs, C₀, h1, h2, hT⟩ := hD
  refine ⟨⟨Qc, floorL, fun _ => C₀, ceilRt, ceilσ, floorN, floorCs, fun _ => 0⟩, ⟨hQ, h1, h2⟩,
    fun T hDr hM => ?_⟩
  obtain ⟨y₀, f⟩ := hT T hDr hM.side_ge hM.rt_le hM.threshold_le hM.n₀_ge hM.Cs_ge hM.derivBound_ge hM.holds
  refine ⟨y₀, fun y hy Bs hBs => ?_⟩
  obtain ⟨D, hData⟩ := f y hy
  have hlam : 0 < D.rateBound := by
    have hL : (1 : ℝ) < T.side := by
      have h : 2 ^ 40 ≤ T.side := hDr.L_ge
      have h' : 1 < T.side := lt_of_lt_of_le (by norm_num) h
      exact_mod_cast h'
    have hlog := Real.log_pos hL
    have hpi := Real.pi_pos
    show 0 < 3 / 4 * (11 / (3 * Real.pi ^ 2) * Real.log T.side)
    positivity
  obtain ⟨-, hHas⟩ := hData Bs D.rateBound hBs hlam le_rfl
  refine ⟨(D.withShift Bs D.rateBound).floorStar, fun g hg hy₂ => ?_⟩
  obtain ⟨e, he, h⟩ := hHas.distance g hg hy₂ 1 zero_le_one
  refine ⟨e, he, fun K β hK hp k hk d hd h₁ h₂ => h K β hK hp k hk d hd h₁ ?_⟩
  rw [Real.rpow_one]
  exact h₂
private theorem logSlope_eq_inv : TrajectoryData.logSlope = (FourPointCondition.oneLoopCoeff)⁻¹ := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold TrajectoryData.logSlope FourPointCondition.oneLoopCoeff
  norm_num [ParameterChoice.colorNumber]
  field_simp
  norm_num
private theorem oneLoopCoeff_pos : 0 < FourPointCondition.oneLoopCoeff := by
  unfold FourPointCondition.oneLoopCoeff
  norm_num [ParameterChoice.colorNumber]
  positivity
private theorem coupling_ratio_tendsto {ℓ : TorusLumps.StepParameters} {IsPair : ℕ+ → ℝ → Prop}
    {Q : PairSequence ℓ.side IsPair} {Bs g δ : ℝ}
    {e : ℝ → ℝ} {i₁ : ℕ} {x : ℕ → ℝ} (hδ : 0 < δ) (he : Tendsto e (𝓝[>] 0) (𝓝 0))
    (hdat : ∀ j, IsFirstPassagePoint ℓ Bs g (Q.cutoff j) (Q.coupling j))
    (heq : ∀ j, ∀ k ≤ (Q.cutoff j : ℕ),
      TotalDensityFlow.coupling ℓ (Q.coupling j) k = ClusterExpansionOfAStep.flowCoupling ℓ (Q.coupling j) k)
    (hdist : ∀ (K : ℕ) (β : ℝ), 2 ≤ K → IsFirstPassagePoint ℓ Bs g K β → ∀ k ≤ K, ∀ d : ℝ, d < 1 →
      1 ≤ d / (ℓ.side : ℝ) ^ ((k : ℤ) - (K : ℤ)) →
      d / (ℓ.side : ℝ) ^ ((k : ℤ) - (K : ℤ)) ≤ ClusterExpansionOfAStep.flowCoupling ℓ β k →
      |ClusterExpansionOfAStep.flowCoupling ℓ β k / (TrajectoryData.logSlope * Real.log (1 / d)) - 1| ≤ e d)
    (hx : ∀ i, i₁ ≤ i → TotalDensitySystem.IsCouplingAtScale ℓ Q (δ / 2 ^ i) (x i)) :
    Tendsto (fun i : ℕ => x i / (TrajectoryData.logSlope * Real.log ((2 : ℝ) ^ i / δ))) atTop (𝓝 1) := by
  have hb : 0 < TrajectoryData.logSlope := by
    unfold TrajectoryData.logSlope
    positivity
  have hd0 : Tendsto (fun i : ℕ => δ / 2 ^ i) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun i => ?_⟩
    · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul δ
      rw [mul_zero] at h
      refine h.congr fun i => ?_
      rw [one_div, inv_pow]
      rfl
    · show 0 < δ / 2 ^ i
      positivity
  have hed := he.comp hd0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ hed
  have hlt : ∀ᶠ i : ℕ in atTop, δ / 2 ^ i < 1 := (tendsto_nhdsWithin_iff.1 hd0).1.eventually_lt_const one_pos
  filter_upwards [hlt, eventually_ge_atTop i₁] with i hd1 hi
  have hdpos : 0 < δ / 2 ^ i := by positivity
  set d := δ / 2 ^ i with hd
  have e₁ : (2 : ℝ) ^ i / δ = 1 / d := by
    rw [hd, one_div_div]
  rw [e₁, Real.norm_eq_abs]
  have hlog : 0 < Real.log (1 / d) := Real.log_pos (by rw [one_div]; exact one_lt_inv₀ hdpos |>.2 hd1)
  set Lg := TrajectoryData.logSlope * Real.log (1 / d) with hLg
  have hLg0 : 0 < Lg := mul_pos hb hlog
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hf := hx i hi (ε * Lg) (by positivity)
  obtain ⟨j, ⟨k, hk, h₁, h₂, h₃⟩, hK⟩ := (hf.and_eventually (Q.tendsto_cutoff.eventually_ge_atTop 2)).exists
  rw [heq j k hk] at h₂ h₃
  have h₄ := hdist (Q.cutoff j) (Q.coupling j) hK (hdat j) k hk d hd1 h₁ h₂
  have h₅ : |x i / Lg - ClusterExpansionOfAStep.flowCoupling ℓ (Q.coupling j) k / Lg| ≤ ε := by
    rw [← sub_div, abs_div, abs_of_pos hLg0, div_le_iff₀ hLg0, abs_sub_comm]
    exact h₃
  calc |x i / Lg - 1| ≤ |x i / Lg - ClusterExpansionOfAStep.flowCoupling ℓ (Q.coupling j) k / Lg| +
        |ClusterExpansionOfAStep.flowCoupling ℓ (Q.coupling j) k / Lg - 1| :=
        abs_sub_le _ _ _
    _ ≤ e d + ε := by
        have : e d = (e ∘ fun i : ℕ => δ / 2 ^ i) i := rfl
        linarith
end CouplingAtScale
section ShortDistance
open TestSpaces (SepTupleOfCard)
open SystemsWithFiveBounds LimitTheorem SeparatedTuples
private theorem shortDistanceAsymptotics_of (hF : MomentLaw.nearlyCollinearPositivityStatement)
    {S : CumulantFamily}
    (H : ∀ (n : ℕ) [NeZero n] (hn : 2 ≤ n), n ≤ 8 → ∀ X : SepTupleOfCard n, ∃ (δ C : ℝ) (i₁ : ℕ) (x : ℕ → ℝ),
      0 < δ ∧
      Tendsto (fun i : ℕ => x i / ((FourPointCondition.oneLoopCoeff)⁻¹ * Real.log ((2 : ℝ) ^ i / δ))) atTop (𝓝 1) ∧
      (∀ i, i₁ ≤ i → ∀ Y : SepTupleOfCard n, Y.1 = dyadicRescale i X.1 →
        |x i ^ n * S n hn Y - shortDistanceLimit X.1| ≤ C * x i ^ (-(1 / 100) : ℝ)) ∧
      ∀ A : DecompositionData, A.IsCanonical (centredOf S) → ∀ᵐ ξ ∂A.law,
        ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → ∀ Y : SepTupleOfCard n, Y.1 = dyadicRescale i X.1 →
          |x i ^ n * connectedFn (A.comp ξ) Y - shortDistanceLimit X.1| ≤ C * x i ^ (-(1 / 100) : ℝ)) :
    ShortDistanceAsymptotics S := by
  have hcomp : ∀ A : DecompositionData, A.IsCanonical (centredOf S) →
      ∀ (n : ℕ) [NeZero n], 2 ≤ n → n ≤ 8 → ∀ (X : SepTupleOfCard n) (Y : ℕ → SepTupleOfCard n),
        (∀ i, (Y i).1 = dyadicRescale i X.1) → ∀ᵐ ξ ∂A.law,
          Tendsto (fun i : ℕ => (Real.log ((2 : ℝ) ^ i) / FourPointCondition.oneLoopCoeff) ^ n *
            connectedFn (A.comp ξ) (Y i)) atTop (𝓝 (shortDistanceLimit X.1)) := by
    intro A hA n _ hn h8 X Y hY
    obtain ⟨δ, C, i₁, x, hδ, hx, -, hc⟩ := H n hn h8 X
    filter_upwards [hc A hA] with ξ hξ
    obtain ⟨i₀, h⟩ := hξ
    exact tendsto_scaled_of_coupling_ratio oneLoopCoeff_pos hδ hx
      (eventually_atTop.2 ⟨i₀, fun i hi => h i hi (Y i) (hY i)⟩)
  refine ⟨fun n _ hn h8 X Y hY => ?_, hcomp, fun A hA => ?_⟩
  · obtain ⟨δ, C, i₁, x, hδ, hx, hl, -⟩ := H n hn h8 X
    exact tendsto_scaled_of_coupling_ratio oneLoopCoeff_pos hδ hx
      (eventually_atTop.2 ⟨i₁, fun i hi => hl i hi (Y i) (hY i)⟩)
  · obtain ⟨X, Y, hY, hpos⟩ := exists_positive_quadruple hF
    exact gaussianComponents_small hA hpos (hcomp A hA 4 (by norm_num) (by norm_num) X Y hY)
end ShortDistance
section Assembly
open SystemsWithFiveBounds LimitTheorem
private def PairSequence.relabel {L L' : ℕ} {P P' : ℕ+ → ℝ → Prop} (h : L = L') (hP : ∀ K β, P K β → P' K β)
    (Q : PairSequence L P) : PairSequence L' P' := by
  subst h
  exact ⟨Q.cutoff, Q.tendsto_cutoff, Q.coupling, fun j => hP _ _ (Q.pair j), Q.state, Q.isLimit⟩
private theorem PairSequence.relabel_defines {L L' : ℕ} {P P' : ℕ+ → ℝ → Prop} (h : L = L')
    (hP : ∀ K β, P K β → P' K β) (Q : PairSequence L P) (S : CumulantFamily) :
    (PairSequence.relabel h hP Q).Defines S ↔ Q.Defines S := by
  subst h
  exact Iff.rfl
private theorem PairSequence.conclusion_of_relabel {L L' : ℕ} {P P' : ℕ+ → ℝ → Prop} (h : L = L')
    (hP : ∀ K β, P K β → P' K β) (Q : PairSequence L P) (S : CumulantFamily) {M ϑ d₀ : ℝ} {ηBar : ℝ → ℝ}
    {K : LimitConstants}
    (hA : ErgodicDecompositionConclusion M ϑ d₀ ηBar K (PairSequence.relabel h hP Q) S) :
    ErgodicDecompositionConclusion M ϑ d₀ ηBar K Q S := by
  subst h
  exact { limit := { hA.limit with states := hA.limit.states, tori := hA.limit.tori }
          decomposition := hA.decomposition
          onePoint := hA.onePoint
          components := hA.components }
private theorem le_of_zpow_neg_two_le {g t₀ : ℝ} (hg : 0 < g) (ht : 0 < t₀)
    (h : t₀ ^ (-2 : ℤ) ≤ g ^ (-2 : ℤ)) : g ≤ t₀ := by
  by_contra hlt
  have h2 : t₀ ^ 2 < g ^ 2 := by nlinarith
  have h3 : (g ^ 2)⁻¹ < (t₀ ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) h2
  have e : ∀ u : ℝ, u ^ (-2 : ℤ) = (u ^ 2)⁻¹ := fun u => by
    rw [zpow_neg]; norm_cast
  rw [e, e] at h
  linarith
theorem VolumeFirstLimitExtras.proof (hTop : topAtAdmissibleParamsStatement)
    (hD : TrajectoryData.trajectoryDataStatement)
    (hLaw : TotalDensitySystem.ShortDistanceLawAtFewPoints.Statement)
    (hRot : RotationsActOnCompletion.Statement)
    (hT : FamiliesOfLimits.InfiniteVolumeLimitsAlongGrowingTori)
    (hI : CutoffRepresentatives.IdentificationsHold)
    (hF : MomentLaw.nearlyCollinearPositivityStatement) :
    VolumeFirstLimitExtras := by
  refine HoldsAtAdmissibleParameters.mono
    (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and hTop hLaw) (couplingAtScale_of_trajectoryData hD))
    fun T y hDr hA => ?_
  obtain ⟨⟨⟨-, -, -, hw⟩, yL, fL⟩, hDist⟩ := hA
  obtain ⟨c₅', lam', top, -, -, ht, hg₀, hY⟩ := hw (2 * T.B) le_rfl
  obtain ⟨yE, fE⟩ := hDist (2 * T.B) le_rfl
  refine ⟨max (top ^ (-2 : ℤ)) (max yL yE), fun g hg hy Q S hQ => ?_⟩
  obtain ⟨a₀, a₁, a₂⟩ : top ^ (-2 : ℤ) ≤ g ^ (-2 : ℤ) ∧ yL ≤ g ^ (-2 : ℤ) ∧ yE ≤ g ^ (-2 : ℤ) := by
    simpa only [max_le_iff] using hy
  have hgt : g ∈ Ioc 0 top := ⟨hg, le_of_zpow_neg_two_le hg ht a₀⟩
  obtain ⟨-, -, hJ, -⟩ := hg₀ g hgt
  have toPassage : ∀ (K : ℕ+) (β : ℝ), TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β →
      IsFirstPassagePoint (T.stepParameters y) (2 * T.B) g K β := fun K β h => by
    have h' : β ∈ SequencePassage.definedPassageWindow
      (TotalDensityFlow.IsDefinedUpTo (T.stepParameters y)) (2 * T.B) g
      (TotalDensityFlow.coupling (T.stepParameters y)) K := h
    rw [(hJ K).1] at h'
    exact h'
  have hone : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
  obtain ⟨Y₀, hY₀, -, K₀, hK₀⟩ := hY 0 1 hone
  have hg₀' : g ∈ Ioc 0 Y₀.top := by rw [hY₀.top_eq]; exact hgt
  obtain ⟨s₀, -, -, k₀⟩ := hK₀ g hg₀'
  have hM₀ : Y₀.M = 1 := by rw [hY₀.scale_eq]; simp
  have toY₀ : ∀ K β, TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β →
      Y₀.IsPair g K β := fun K β h =>
    (hY₀.isPair_iff g hgt K β).2 (toPassage K β h)
  have A₀ := k₀ (PairSequence.relabel hY₀.side_eq.symm toY₀ Q) S
    ((PairSequence.relabel_defines _ _ _ _).2 hQ)
  rw [hM₀] at A₀
  have A := PairSequence.conclusion_of_relabel _ _ _ _ A₀
  have hL : Conventions.IsAdmissibleBlockingFactor (T.stepParameters y).side := hY₀.side_eq ▸ Y₀.admissibleL
  have hβ : ∀ j, 0 < Q.coupling j := fun j => Y₀.β_pos g hg₀' _ _ (toY₀ _ _ (Q.pair j))
  refine ⟨⟨fun b => exists_growing_sides hT hL Q hβ hQ b, spatialRotationRep_of hRot hI hL A s₀⟩,
    shortDistanceAsymptotics_of hF fun n _ hn h8 X => ?_⟩
  obtain ⟨δ, C, i₁, x, hδ, hx, hl, hc⟩ := fL g hg a₁ Q S hQ n hn h8 X
  obtain ⟨e, he, hE⟩ := fE g hg a₂
  refine ⟨δ, C, i₁, x, hδ, ?_, hl, hc⟩
  rw [← logSlope_eq_inv]
  exact coupling_ratio_tendsto hδ he (fun j => toPassage _ _ (Q.pair j))
    (fun j k hk => (hJ (Q.cutoff j)).2 _ (toPassage _ _ (Q.pair j)) k hk) hE hx
end Assembly
end YangMills.Construction.TotalDensities
end
