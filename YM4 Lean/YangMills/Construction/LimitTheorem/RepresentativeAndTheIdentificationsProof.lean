import YangMills.Construction.BoundsOnEverySide.SeparatedLimitsUnderABoundProof
import YangMills.Construction.Continuum.ActionsOfMotionsAndTheSequencesOfTensorsOverTheUpperHalfSpace
import YangMills.Construction.Continuum.ConnectedFunctionsAndCentredFunctionalOfAFunctional
import YangMills.Construction.Continuum.MultilinearityAndInversionOfTheConnectedFunctions
import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.Cumulants.TwoMutuallyInversePolynomialSubstitutions
import YangMills.Construction.LimitTheorem.RepresentativeAndTheIdentifications
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.LimitTheorem.CutoffRepresentatives
open InfiniteLattice (GaugeField smearedEnergy centeredMoment ursellFunction ursellPartitionSum
  compactTestFunctions)
open InfiniteLattice.CutoffRepresentative (centredProduct centredSmearedField)
open CutoffLattice (FieldsAt)
open SetPartition (Partitions atLeastTwoPartitions nonSingletonPartitions blockCount)
open TestSpaces (SepTuple SepTupleOfCard sepRestrict sepTuple_ext cumulant centredOfCumulants
  partitionsNoSingletons)
open TupleLists (toList ofList ofList_toList toList_ofList)
private theorem mem_compactTestFunctions {m : ℕ} (X : SepTupleOfCard m) (i : Fin m) :
    X.1 i ∈ compactTestFunctions := by apply _root_.YangMills.Construction.BoundsOnEverySide.SubsequentialLimits.tuple_mem_compactTestFunctions <;> assumption
private theorem evalOnMap_centredOf (S : CumulantFamily) (Z : SepTuple) :
    evalOnMap (centredOf S) Z = centredOfCumulants S Z := by
  change centredOfCumulants S (ofList (toList Z)) = _
  rw [ofList_toList]
abbrev _root_.YangMills.SharedProofs.p13412 := @evalOnMap_centredOf
private theorem prod_orderEmbOfFin_eq {m : ℕ} (J : Finset (Fin m)) (g : Fin m → ℂ) :
    ∏ a : Fin J.card, g (J.orderEmbOfFin rfl a) = ∏ l ∈ J, g l := by
  rw [← Finset.prod_coe_sort J g]
  refine Eq.trans ?_ (Equiv.prod_comp (J.orderIsoOfFin rfl).toEquiv fun l : J => g l)
  exact Finset.prod_congr rfl fun a _ => by simp
private theorem integral_centredProduct (L K : ℕ) (μ : Measure (FieldsAt L K)) {k : ℕ}
    (X : SepTupleOfCard k) :
    ((∫ U, centredProduct L K μ ⟨k, X⟩ U ∂μ : ℝ) : ℂ) = centeredMoment μ X.1 := by
  have e : ∀ l, Probability.complexExpectation μ
      (fun V => ((smearedEnergy (X.1 l) V : ℝ) : ℂ)) =
      ((∫ V, smearedEnergy (X.1 l) V ∂μ : ℝ) : ℂ) := fun l => integral_complex_ofReal
  unfold centeredMoment
  simp only [e]
  rw [Probability.complexExpectation, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp [centredProduct, centredSmearedField]
private theorem finsetMoment_shift_eq {a : ℝ} (μ : Measure (GaugeField a)) {m : ℕ}
    (X : SepTupleOfCard m) {J : Finset (Fin m)} (hJ : J.Nonempty) :
    Cumulants.finsetMoment μ (Cumulants.shiftTuple (fun l U => smearedEnergy (X.1 l) U)
      fun l => -∫ V, smearedEnergy (X.1 l) V ∂μ) J =
      centeredMoment μ (sepRestrict X J).1 := by
  have e : ∀ l, Probability.complexExpectation μ
      (fun V => ((smearedEnergy (X.1 l) V : ℝ) : ℂ)) =
      ((∫ V, smearedEnergy (X.1 l) V ∂μ : ℝ) : ℂ) := fun l => integral_complex_ofReal
  rw [Cumulants.finsetMoment, if_neg hJ.ne_empty]
  unfold centeredMoment
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  have h := prod_orderEmbOfFin_eq J fun l =>
    (((smearedEnergy (X.1 l) U : ℝ) : ℂ) -
      Probability.complexExpectation μ fun V => ((smearedEnergy (X.1 l) V : ℝ) : ℂ))
  change _ = ∏ a : Fin J.card, (((smearedEnergy (X.1 (J.orderEmbOfFin rfl a)) U : ℝ) : ℂ) -
      Probability.complexExpectation μ fun V =>
        ((smearedEnergy (X.1 (J.orderEmbOfFin rfl a)) V : ℝ) : ℂ))
  rw [h]
  simp only [e, Cumulants.shiftTuple]
  push_cast
  exact Finset.prod_congr rfl fun l _ => by ring
private theorem ursellFunction_eq_moebius (hCum : Cumulants.CumulantMomentRelations)
    {a : ℝ} (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ]
    (hB : ∀ f ∈ compactTestFunctions, Probability.IsBoundedRealRV
      (smearedEnergy f : GaugeField a → ℝ))
    {m : ℕ} (hm : 2 ≤ m) (X : SepTupleOfCard m) :
    ursellFunction μ m X.1 =
      ∑ η ∈ ClusterExpansion.SymGraph.partitions (Fin m),
        (-1 : ℂ) ^ (η.card - 1) * ((η.card - 1).factorial : ℂ) *
          ∏ J ∈ η, centeredMoment μ (sepRestrict X J).1 := by
  have hx : ∀ l, Probability.IsBoundedRealRV
      (fun U : GaugeField a => smearedEnergy (X.1 l) U) := fun l =>
    hB _ (mem_compactTestFunctions X l)
  set c : Fin m → ℝ := fun l => -∫ V, smearedEnergy (X.1 l) V ∂μ with hc
  have hx' : ∀ l, Probability.IsBoundedRealRV
      (Cumulants.shiftTuple (fun l (U : GaugeField a) => smearedEnergy (X.1 l) U) c l) := by
    intro l
    obtain ⟨C, hC⟩ := (hx l).bounded
    refine ⟨(hx l).measurable.add_const _, C + |c l|, fun U => ?_⟩
    exact (abs_add_le _ _).trans (add_le_add_left (hC U) _)
  obtain ⟨-, -, -, hshift, -, -, hform⟩ := hCum _ μ m _ hx'
  have e₁ : ursellFunction μ m X.1 = Cumulants.mixedCumulant μ
      (Cumulants.shiftTuple (fun l (U : GaugeField a) => smearedEnergy (X.1 l) U) c) :=
    (hshift m _ c hm hx).symm
  rw [e₁, hform (by omega)]
  refine Finset.sum_bij (fun π _ => π.parts) (fun π _ => ?_) (fun π _ π' _ h => Finpartition.ext h)
    (fun η hη => ?_) (fun π _ => ?_)
  · simp only [ClusterExpansion.SymGraph.partitions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact TestSpaces.isPartition_parts π
  · have h : ClusterExpansion.SymGraph.IsPartition η := by
      simpa only [ClusterExpansion.SymGraph.partitions, Finset.mem_filter, Finset.mem_univ,
        true_and] using hη
    exact ⟨TestSpaces.finpartitionOfIsPartition h, Finset.mem_univ _, rfl⟩
  · refine congrArg _ (Finset.prod_congr rfl fun J hJ => ?_)
    exact finsetMoment_shift_eq μ X (π.nonempty_of_mem_parts hJ)
private theorem nonSingletonPartitions_one : nonSingletonPartitions 1 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun π hπ => ?_
  obtain ⟨b, hb, -⟩ := π.exists_mem (Finset.mem_univ (0 : Fin 1))
  have h2 := (Finset.mem_filter.1 hπ).2 b hb
  have h1 : b.card ≤ 1 := by simpa using Finset.card_le_univ b
  omega
abbrev _root_.YangMills.SharedProofs.p2697 := @nonSingletonPartitions_one
private theorem momentsAndCumulantsAt_of (hCI : InfiniteLattice.CenteredIdentity.Statement)
    (hCum : Cumulants.CumulantMomentRelations) (L : ℕ)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ+) (μ : Measure (FieldsAt L K))
    [IsProbabilityMeasure μ] : MomentsAndCumulantsAt L K μ := by
  obtain ⟨⟨hfin, -⟩, -, hid⟩ := hCI ⟨L, hL, K, 1⟩ μ inferInstance
  have hmom : ∀ (k : ℕ) (X : SepTupleOfCard k),
      centeredMoment μ X.1 = ursellPartitionSum μ X.1 :=
    fun k X => hid k X.1 (mem_compactTestFunctions X)
  refine ⟨fun k X => ⟨integral_centredProduct L K μ X, hmom k X⟩, fun X => ?_, fun X => ?_,
    fun m hm X => ursellFunction_eq_moebius hCum μ (fun f hf => (hfin f hf).2) hm X⟩
  · rw [← hmom]
    simp [centeredMoment, Probability.complexExpectation]
  · simp [ursellPartitionSum, nonSingletonPartitions_one]
private theorem partitionSum_eq_centredOf (hML : TestSpaces.CumulantMultilinearInversion)
    (S : CumulantFamily) {n : ℕ} (hn : 1 ≤ n) (X : SepTupleOfCard n)
    (k : Cumulants.SubsetFamily n)
    (hk : ∀ J : Cumulants.NonemptyFinSubset n, k J =
      ((if h : 2 ≤ J.1.card then S _ h (sepRestrict X J.1) else 0 : ℝ) : ℂ))
    (J : Cumulants.NonemptyFinSubset n) :
    Cumulants.partitionSum k J =
      (centredOfCumulants S ⟨J.1.card, sepRestrict X J.1⟩ : ℝ) := by
  classical
  have hφ : TestSpaces.IsSepFunctional fun Z => if Z.1 = 0 then 1 else 0 := by
    refine ⟨by simp [TestSpaces.sepTupleNil], fun m hm i b b' _ _ _ _ _ _ => ?_⟩
    have : m ≠ 0 := by omega
    simp [this]
  have hF := ((hML.1 _ hφ S).1 n hn X J.1).2
  rw [TestSpaces.CentredRestrictFormula] at hF
  rw [hF, Cumulants.partitionSum]
  have hzero : ∀ π ∈ (Finset.univ : Finset (Partitions J.1)),
      π ∉ atLeastTwoPartitions J.1 →
      Cumulants.blockProduct k π = 0 := by
    intro π _ hπ
    rw [SetPartition.mem_atLeastTwoPartitions] at hπ
    push Not at hπ
    obtain ⟨B, hB, hc⟩ := hπ
    refine Finset.prod_eq_zero (Finset.mem_univ (⟨B, hB⟩ : π.parts)) ?_
    rw [hk]
    simp [Cumulants.blockSubset, not_le.2 hc]
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero, ← Finset.sum_attach, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Complex.ofReal_prod, Cumulants.blockProduct, Finset.univ_eq_attach]
  refine Finset.prod_congr rfl fun B _ => ?_
  rw [hk]
  exact congrArg _ (dif_pos (SetPartition.two_le_card_of_mem_atLeastTwoPartitions π.2 B.2))
private theorem connectedFn_centredOf (hInv : Cumulants.PartitionSubstitutionsInverse)
    (hML : TestSpaces.CumulantMultilinearInversion)
    (S : CumulantFamily) {n : ℕ} (hn : 2 ≤ n) (X : SepTupleOfCard n) :
    connectedFn (centredOf S) X = S n hn X := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, -, -, -, hLeft, -, -, -⟩ := hInv n hn1
  let k : Cumulants.SubsetFamily n := fun J =>
    ((if h : 2 ≤ J.1.card then S _ h (sepRestrict X J.1) else 0 : ℝ) : ℂ)
  have hm := partitionSum_eq_centredOf hML S hn1 X k fun _ => rfl
  have hwhole := congrFun (hLeft k) (Cumulants.univSubset hn1)
  let G : SepTuple → ℝ := fun Z => if h : 2 ≤ Z.1 then S Z.1 h Z.2 else 0
  have hkG : k (Cumulants.univSubset hn1) = (S n hn X : ℝ) := by
    have h₃ := congrArg G (TestSpaces.sepRestrict_univ X)
    have h₂ : G ⟨n, X⟩ = S n hn X := dif_pos hn
    rw [← h₂, ← h₃]
    rfl
  have hprod : ∀ π : Partitions (Finset.univ : Finset (Fin n)),
      ∏ B ∈ π.parts, ((evalOnMap (centredOf S) ⟨B.card, sepRestrict X B⟩ : ℝ) : ℂ) =
        Cumulants.blockProduct (Cumulants.partitionSum k) π := by
    intro π
    unfold Cumulants.blockProduct
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun B _ => ?_
    rw [hm, evalOnMap_centredOf]
    rfl
  apply Complex.ofReal_injective
  rw [← hkG, ← hwhole, connectedFn, TestSpaces.cumulant_eq_sum_partitions,
    Cumulants.moebiusPartitionSum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  change _ = (-1 : ℂ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℂ) *
    Cumulants.blockProduct (Cumulants.partitionSum k) π
  rw [← hprod π]
  push_cast
  rfl
private theorem connectedFn_centredOf_one (S : CumulantFamily) (X : SepTupleOfCard 1) :
    connectedFn (centredOf S) X = 0 := by
  rw [connectedFn, TestSpaces.cumulant_single, evalOnMap_centredOf,
    TestSpaces.centredOfCumulants_single]
private theorem ursellTendsto_iff (hCI : InfiniteLattice.CenteredIdentity.Statement)
    (hCum : Cumulants.CumulantMomentRelations)
    (hInv : Cumulants.PartitionSubstitutionsInverse)
    (hML : TestSpaces.CumulantMultilinearInversion)
    (L : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ+ → ℕ+)
    (μ : ∀ j, Measure (FieldsAt L (K j))) (hμ : ∀ j, IsProbabilityMeasure (μ j))
    (S : CumulantFamily) : UrsellTendsto L K μ S ↔ RepresentativesTendsto L K μ S := by
  have hM := fun j => momentsAndCumulantsAt_of hCI hCum L hL (K j) (μ j)
  constructor
  · rintro h ⟨k, X⟩
    have h1 : Tendsto (fun j => ((∫ U, centredProduct L (K j) (μ j) ⟨k, X⟩ U ∂μ j : ℝ) : ℂ)) atTop
        (𝓝 ((evalOnMap (centredOf S) ⟨k, X⟩ : ℝ) : ℂ)) := by
      have e : ∀ j, ((∫ U, centredProduct L (K j) (μ j) ⟨k, X⟩ U ∂μ j : ℝ) : ℂ) =
          ∑ π ∈ (atLeastTwoPartitions (Finset.univ : Finset (Fin k))).attach,
            ∏ J ∈ π.1.parts.attach, ursellFunction (μ j) J.1.card
              (sepRestrict X J.1).1 := by
        intro j
        rw [((hM j).1 k X).1, ((hM j).1 k X).2, ursellPartitionSum,
          SetPartition.nonSingletonPartitions_eq_atLeastTwoPartitions, ← Finset.sum_attach]
        exact Finset.sum_congr rfl fun π _ => (Finset.prod_attach π.1.parts fun J =>
          ursellFunction (μ j) J.card (sepRestrict X J).1).symm
      simp only [e]
      rw [evalOnMap_centredOf, TestSpaces.centredOfCumulants_eq_blockProductSum,
        TestSpaces.blockProductSum, Complex.ofReal_sum]
      refine tendsto_finsetSum _ fun π _ => ?_
      rw [Complex.ofReal_prod]
      exact tendsto_finsetProd _ fun J _ =>
        h _ (SetPartition.two_le_card_of_mem_atLeastTwoPartitions π.2 J.2) _
    have h2 := (Complex.continuous_re.tendsto _).comp h1
    simpa [Function.comp_def] using h2
  · intro h n hn X
    have e : ∀ j, ursellFunction (μ j) n X.1 =
        ∑ η ∈ ClusterExpansion.SymGraph.partitions (Fin n),
          (-1 : ℂ) ^ (η.card - 1) * ((η.card - 1).factorial : ℂ) *
            ∏ J ∈ η, ((∫ U, centredProduct L (K j) (μ j) ⟨J.card, sepRestrict X J⟩ U ∂μ j : ℝ) : ℂ) := by
      intro j
      rw [(hM j).2.2.2 n hn X]
      exact Finset.sum_congr rfl fun η _ => congrArg _ (Finset.prod_congr rfl fun J _ =>
        ((hM j).1 _ (sepRestrict X J)).1.symm)
    have hlim : ((S n hn X : ℝ) : ℂ) = ∑ η ∈ ClusterExpansion.SymGraph.partitions (Fin n),
        (-1 : ℂ) ^ (η.card - 1) * ((η.card - 1).factorial : ℂ) *
          ∏ J ∈ η, ((evalOnMap (centredOf S) ⟨J.card, sepRestrict X J⟩ : ℝ) : ℂ) := by
      rw [← connectedFn_centredOf hInv hML S hn X, connectedFn, cumulant]
      push_cast
      rfl
    simp only [e]
    rw [hlim]
    refine tendsto_finsetSum _ fun η _ =>
      tendsto_const_nhds.mul (tendsto_finsetProd _ fun J _ => ?_)
    exact (Complex.continuous_ofReal.tendsto _).comp (h ⟨J.card, sepRestrict X J⟩)
private def IsReorderInvariant (F : SepTuple → ℝ) : Prop :=
  ∀ (n : ℕ) (X Y : SepTupleOfCard n) (τ : Equiv.Perm (Fin n)), Y.1 = X.1 ∘ τ → F ⟨n, Y⟩ = F ⟨n, X⟩
private theorem exists_restrict_eq {n : ℕ} (X : SepTupleOfCard n) (A : Finset (Fin n)) {m : ℕ}
    (h : A.card = m) : ∃ Z : SepTupleOfCard m, Z.1 = X.1 ∘ A.orderEmbOfFin h ∧
      (⟨m, Z⟩ : SepTuple) = ⟨A.card, sepRestrict X A⟩ := by
  subst h
  exact ⟨sepRestrict X A, rfl, rfl⟩
private theorem exists_perm_comp_of_range_eq {m n : ℕ} {e₁ e₂ : Fin m → Fin n}
    (h₁ : Function.Injective e₁) (h₂ : Function.Injective e₂)
    (hr : Set.range e₁ = Set.range e₂) : ∃ τ : Equiv.Perm (Fin m), e₁ = e₂ ∘ τ := by
  refine ⟨(Equiv.ofInjective e₁ h₁).trans ((Equiv.setCongr hr).trans (Equiv.ofInjective e₂ h₂).symm),
    funext fun a => ?_⟩
  simp [Equiv.apply_ofInjective_symm]
private theorem reorderInvariant_restrict {F : SepTuple → ℝ} (hF : IsReorderInvariant F) {n : ℕ}
    {X Y : SepTupleOfCard n} {ς : Equiv.Perm (Fin n)} (hY : Y.1 = X.1 ∘ ς) (J : Finset (Fin n)) :
    F ⟨J.card, sepRestrict Y J⟩ =
      F ⟨(ς.finsetCongr J).card, sepRestrict X (ς.finsetCongr J)⟩ := by
  have hc : (ς.finsetCongr J).card = J.card := by simp
  obtain ⟨Z, hZ, hZe⟩ := exists_restrict_eq X (ς.finsetCongr J) hc
  rw [← hZe]
  have hr : Set.range (ς ∘ J.orderEmbOfFin rfl) =
      Set.range ((ς.finsetCongr J).orderEmbOfFin hc) := by
    rw [Finset.range_orderEmbOfFin, Set.range_comp, Finset.range_orderEmbOfFin]
    ext x
    simp
  obtain ⟨τ, hτ⟩ := exists_perm_comp_of_range_eq
    (ς.injective.comp (J.orderEmbOfFin rfl).injective) ((ς.finsetCongr J).orderEmbOfFin hc).injective hr
  refine hF _ Z _ τ ?_
  rw [hZ, Function.comp_assoc, ← hτ]
  change SchwingerFunctions.restrictTuple Y.1 J = _
  rw [hY]
  rfl
private theorem mem_finsetCongr_finsetCongr {n : ℕ} (ς : Equiv.Perm (Fin n))
    {η : Finset (Finset (Fin n))} {b : Finset (Fin n)} :
    b ∈ ς.finsetCongr.finsetCongr η ↔ ∃ c ∈ η, ς.finsetCongr c = b := by
  rw [Equiv.finsetCongr_apply]
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
private theorem mem_biUnion_of_inst {α β : Type*} (inst : DecidableEq β) (s : Finset α)
    (t : α → Finset β) (b : β) : b ∈ @Finset.biUnion α β inst s t ↔ ∃ a ∈ s, b ∈ t a :=
  Finset.mem_biUnion
private theorem isPartition_finsetCongr {n : ℕ} (ς : Equiv.Perm (Fin n))
    {η : Finset (Finset (Fin n))} (h : ClusterExpansion.SymGraph.IsPartition η) :
    ClusterExpansion.SymGraph.IsPartition (ς.finsetCongr.finsetCongr η) := by
  obtain ⟨hne, hdis, hU⟩ := h
  refine ⟨fun b hb => ?_, fun b hb b' hb' hbb => ?_, ?_⟩
  · obtain ⟨c, hc, rfl⟩ := (mem_finsetCongr_finsetCongr ς).1 hb
    rw [Equiv.finsetCongr_apply]
    exact (hne c hc).map
  · obtain ⟨c, hc, rfl⟩ := (mem_finsetCongr_finsetCongr ς).1 (Finset.mem_coe.1 hb)
    obtain ⟨c', hc', rfl⟩ := (mem_finsetCongr_finsetCongr ς).1 (Finset.mem_coe.1 hb')
    have hcc : c ≠ c' := fun e => hbb (by rw [e])
    have hd : Disjoint c c' := hdis hc hc' hcc
    change Disjoint (ς.finsetCongr c) (ς.finsetCongr c')
    rw [Equiv.finsetCongr_apply, Equiv.finsetCongr_apply, Finset.disjoint_map]
    exact hd
  · refine Finset.eq_univ_of_forall fun x => ?_
    have hx := Finset.mem_univ (ς.symm x)
    rw [← hU] at hx
    obtain ⟨c, hc, hxc⟩ := (mem_biUnion_of_inst _ _ _ _).1 hx
    refine (mem_biUnion_of_inst _ _ _ _).2
      ⟨ς.finsetCongr c, (mem_finsetCongr_finsetCongr ς).2 ⟨c, hc, rfl⟩, ?_⟩
    change x ∈ ς.finsetCongr c
    rw [Equiv.finsetCongr_apply, Finset.mem_map_equiv]
    exact hxc
private theorem isPartition_finsetCongr_iff {n : ℕ} (ς : Equiv.Perm (Fin n))
    (η : Finset (Finset (Fin n))) :
    ClusterExpansion.SymGraph.IsPartition (ς.finsetCongr.finsetCongr η) ↔
      ClusterExpansion.SymGraph.IsPartition η := by
  refine ⟨fun h => ?_, isPartition_finsetCongr ς⟩
  have hinv : ∀ c, ς.symm.finsetCongr (ς.finsetCongr c) = c := fun c => by
    rw [← Equiv.finsetCongr_symm, Equiv.symm_apply_apply]
  have e : ς.symm.finsetCongr.finsetCongr (ς.finsetCongr.finsetCongr η) = η := by
    ext b
    simp only [mem_finsetCongr_finsetCongr]
    constructor
    · rintro ⟨c, ⟨d, hd, rfl⟩, rfl⟩
      rwa [hinv]
    · exact fun hb => ⟨ς.finsetCongr b, ⟨b, hb, rfl⟩, hinv b⟩
  have h' := isPartition_finsetCongr ς.symm h
  rwa [e] at h'
private theorem sum_reorderInvariant {F : SepTuple → ℝ} (hF : IsReorderInvariant F) {n : ℕ}
    {X Y : SepTupleOfCard n} {ς : Equiv.Perm (Fin n)} (hY : Y.1 = X.1 ∘ ς)
    (P : Finset (Finset (Finset (Fin n))))
    (hP : ∀ η, ς.finsetCongr.finsetCongr η ∈ P ↔ η ∈ P) (w : ℕ → ℝ) :
    ∑ η ∈ P, w η.card * ∏ J ∈ η, F ⟨J.card, sepRestrict Y J⟩ =
      ∑ η ∈ P, w η.card * ∏ J ∈ η, F ⟨J.card, sepRestrict X J⟩ := by
  refine Finset.sum_equiv ς.finsetCongr.finsetCongr (fun η => (hP η).symm) fun η _ => ?_
  have hc : (ς.finsetCongr.finsetCongr η).card = η.card := by simp
  rw [hc]
  refine congrArg _ ?_
  rw [Equiv.finsetCongr_apply, Finset.prod_map]
  exact Finset.prod_congr rfl fun J _ => reorderInvariant_restrict hF hY J
private def cumulantValue (S : CumulantFamily) (Z : SepTuple) : ℝ :=
  if h : 2 ≤ Z.1 then S Z.1 h Z.2 else 0
private theorem centredOfCumulants_eq_sum (S : CumulantFamily) {n : ℕ} (X : SepTupleOfCard n) :
    centredOfCumulants S ⟨n, X⟩ = ∑ η ∈ partitionsNoSingletons (Fin n), (1 : ℝ) *
      ∏ J ∈ η, cumulantValue S ⟨J.card, sepRestrict X J⟩ := by
  rw [centredOfCumulants, ← Finset.sum_attach (partitionsNoSingletons (Fin n))]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [one_mul, ← Finset.prod_attach η.1]
  refine Finset.prod_congr rfl fun J _ => ?_
  rw [cumulantValue, dif_pos (TestSpaces.two_le_card_of_mem_partitionsNoSingletons η.2 J.2)]
private theorem ofList_reorder (T : SeparatedTuples.SepTuple) (τ : Equiv.Perm (Fin T.1.length))
    (Y : SepTupleOfCard T.1.length) (hY : Y.1 = T.1.get ∘ τ) :
    ofList (T.reorder τ) = ⟨_, Y⟩ := by
  refine sepTuple_ext _ _ (by simp [SeparatedTuples.SepTuple.reorder]) fun k => ?_
  rw [hY]
  exact List.get_ofFn _ _
private theorem isPermInvariant_iff (Φ : SeparatedTuples.TupleFunctional) :
    Φ.IsPermInvariant ↔ IsReorderInvariant (evalOnMap Φ) := by
  have hv : ∀ T, evalOnMap Φ (ofList T) = Φ T := fun T => by
    rw [evalOnMap, toList_ofList]
  constructor
  · intro h
    have key : ∀ (Z : SepTuple) (Y : SepTupleOfCard Z.1) (τ : Equiv.Perm (Fin Z.1)),
        Y.1 = Z.2.1 ∘ τ → evalOnMap Φ ⟨Z.1, Y⟩ = evalOnMap Φ Z := by
      intro Z
      obtain ⟨T, rfl⟩ : ∃ T, Z = ofList T := ⟨toList Z, (ofList_toList Z).symm⟩
      intro Y τ hY
      change evalOnMap Φ ⟨T.1.length, Y⟩ = _
      rw [← ofList_reorder T τ Y hY, hv, hv]
      exact h T τ
    exact fun n X Y τ hY => key ⟨n, X⟩ Y τ hY
  · intro h T τ
    have hmem : T.1.get ∘ τ ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ))
        T.1.length :=
      ⟨fun i => (ofList T).2.2.1 (τ i), fun i j hij => (ofList T).2.2.2 (τ.injective.ne hij)⟩
    have e : evalOnMap Φ ⟨T.1.length, ⟨_, hmem⟩⟩ = evalOnMap Φ (ofList T) :=
      h _ (ofList T).2 ⟨_, hmem⟩ τ rfl
    rw [← ofList_reorder T τ ⟨_, hmem⟩ rfl, hv, hv] at e
    exact e
private theorem centredOf_isPermInvariant_iff (hInv : Cumulants.PartitionSubstitutionsInverse)
    (hML : TestSpaces.CumulantMultilinearInversion) (S : CumulantFamily) :
    (centredOf S).IsPermInvariant ↔ IsFamilySymmetric S := by
  rw [isPermInvariant_iff]
  constructor
  · intro h n hn X Y ς hY
    rw [← connectedFn_centredOf hInv hML S hn X, ← connectedFn_centredOf hInv hML S hn Y]
    have hP : ∀ η, ς.finsetCongr.finsetCongr η ∈ ClusterExpansion.SymGraph.partitions (Fin n) ↔
        η ∈ ClusterExpansion.SymGraph.partitions (Fin n) := fun η => by
      simp only [ClusterExpansion.SymGraph.partitions, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact isPartition_finsetCongr_iff ς η
    exact sum_reorderInvariant h (ς := ς) hY _ hP fun c =>
      (-1 : ℝ) ^ (c - 1) * ((c - 1).factorial : ℝ)
  · intro h n X Y τ hY
    have hS : IsReorderInvariant (cumulantValue S) := by
      intro m A B ρ hB
      by_cases hm : 2 ≤ m
      · simpa [cumulantValue, hm] using h m hm A B ρ hB
      · simp [cumulantValue, hm]
    rw [evalOnMap_centredOf, evalOnMap_centredOf, centredOfCumulants_eq_sum,
      centredOfCumulants_eq_sum]
    refine sum_reorderInvariant hS (ς := τ) hY _ (fun η => ?_) fun _ => 1
    simp only [partitionsNoSingletons, ClusterExpansion.SymGraph.partitions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine and_congr (isPartition_finsetCongr_iff τ η) ⟨fun h2 J hJ => ?_, fun h2 J hJ => ?_⟩
    · have h3 := h2 (τ.finsetCongr J) ((mem_finsetCongr_finsetCongr τ).2 ⟨J, hJ, rfl⟩)
      simpa [Equiv.finsetCongr_apply] using h3
    · obtain ⟨c, hc, rfl⟩ := (mem_finsetCongr_finsetCongr τ).1 hJ
      simpa [Equiv.finsetCongr_apply] using h2 c hc
open Motions (RigidMotion actOnTuple actOnPointFun)
open UpperHalfTensors (actOnTuple_mem_disjointSupportTuples)
private def movedTuple (r : RigidMotion) {n : ℕ} (X : SepTupleOfCard n) : SepTupleOfCard n :=
  ⟨actOnTuple r X.1, actOnTuple_mem_disjointSupportTuples r X.2⟩
private theorem invMap_toFun (r : RigidMotion) : SeparatedTuples.invMap r.toFun = r.invFun := by
  funext x
  have hinj : Function.Injective r.toFun := Function.LeftInverse.injective r.invFun_toFun
  calc SeparatedTuples.invMap r.toFun x
      = SeparatedTuples.invMap r.toFun (r.toFun (r.invFun x)) := by rw [r.toFun_invFun]
    _ = r.invFun x := Function.leftInverse_invFun hinj _
abbrev _root_.YangMills.SharedProofs.p78111 := @invMap_toFun
private theorem ofList_push (r : RigidMotion) (X : SeparatedTuples.SepTuple) :
    ofList (SeparatedTuples.push r.toFun X) = ⟨_, movedTuple r (ofList X).2⟩ := by
  have hlist : SeparatedTuples.pushList r.toFun X.1 = List.ofFn (movedTuple r (ofList X).2).1 := by
    apply List.ext_get
    · simp [SeparatedTuples.pushList, ofList]
    · intro i h₁ h₂
      simp [SeparatedTuples.pushList, ofList, movedTuple, actOnTuple, actOnPointFun,
        invMap_toFun]
  have hsep : SeparatedTuples.IsDisjointlySupported (SeparatedTuples.pushList r.toFun X.1) :=
    hlist ▸ TupleLists.isDisjointlySupported_ofFn _
  have e : SeparatedTuples.push r.toFun X = toList ⟨_, movedTuple r (ofList X).2⟩ := by
    unfold SeparatedTuples.push
    rw [dif_pos hsep]
    exact Subtype.ext hlist
  rw [e, ofList_toList]
private theorem sepRestrict_movedTuple (r : RigidMotion) {n : ℕ} (X : SepTupleOfCard n)
    (J : Finset (Fin n)) : sepRestrict (movedTuple r X) J = movedTuple r (sepRestrict X J) :=
  Subtype.ext rfl
private theorem centredOf_motionInvariant_iff (hInv : Cumulants.PartitionSubstitutionsInverse)
    (hML : TestSpaces.CumulantMultilinearInversion) (S : CumulantFamily)
    (r : RigidMotion) :
    IsMotionInvariant (centredOf S) r ↔ IsFamilyInvariant S r := by
  constructor
  · intro h n hn X
    refine ⟨(movedTuple r X).2, ?_⟩
    have hv : ∀ (m : ℕ) (Y : SepTupleOfCard m),
        evalOnMap (centredOf S) ⟨m, movedTuple r Y⟩ =
          evalOnMap (centredOf S) ⟨m, Y⟩ := by
      intro m Y
      have h₁ := h (toList ⟨m, Y⟩)
      change centredOfCumulants S (ofList (SeparatedTuples.push r.toFun (toList ⟨m, Y⟩))) =
        centredOfCumulants S (ofList (toList ⟨m, Y⟩)) at h₁
      rw [ofList_push, ofList_toList] at h₁
      rw [evalOnMap_centredOf, evalOnMap_centredOf]
      exact h₁
    change S n hn (movedTuple r X) = S n hn X
    rw [← connectedFn_centredOf hInv hML S hn X,
      ← connectedFn_centredOf hInv hML S hn (movedTuple r X)]
    have hJ : ∀ J : Finset (Fin n), evalOnMap (centredOf S)
        ⟨J.card, sepRestrict (movedTuple r X) J⟩ =
        evalOnMap (centredOf S) ⟨J.card, sepRestrict X J⟩ := fun J => by
      rw [sepRestrict_movedTuple]
      exact hv _ _
    simp only [connectedFn, cumulant, hJ]
  · intro h X
    have hS : ∀ n hn (Y : SepTupleOfCard n), S n hn (movedTuple r Y) = S n hn Y := fun n hn Y => by
      obtain ⟨_, e⟩ := h n hn Y
      exact e
    change centredOfCumulants S (ofList (SeparatedTuples.push r.toFun X)) =
      centredOfCumulants S (ofList X)
    rw [ofList_push]
    refine Finset.sum_congr rfl fun η _ => Finset.prod_congr rfl fun J _ => ?_
    change S _ _ (sepRestrict (movedTuple r (ofList X).2) J.1) = S _ _ (sepRestrict (ofList X).2 J.1)
    rw [sepRestrict_movedTuple]
    exact hS _ _ _
theorem identificationsHold_of
    (hCI : InfiniteLattice.CenteredIdentity.Statement)
    (hCum : Cumulants.CumulantMomentRelations)
    (hInv : Cumulants.PartitionSubstitutionsInverse)
    (hML : TestSpaces.CumulantMultilinearInversion) :
    IdentificationsHold := by
  intro L hL K μ hμ S
  refine ⟨fun j => ?_, ursellTendsto_iff hCI hCum hInv hML L hL K μ hμ S,
    centredOf_isPermInvariant_iff hInv hML S, centredOf_motionInvariant_iff hInv hML S,
    connectedFn_centredOf_one S, fun n hn X => connectedFn_centredOf hInv hML S hn X⟩
  have := hμ j
  exact momentsAndCumulantsAt_of hCI hCum L hL (K j) (μ j)
end YangMills.Construction.LimitTheorem.CutoffRepresentatives
end
