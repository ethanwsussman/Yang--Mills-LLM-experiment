import YangMills.Construction.InfiniteLattice.CentredMomentsAtOneIndexAndTheTwoFormsOfVolumeFirstProof
import YangMills.Construction.BoundsOnEverySide.MapsAndTheirLimitsFreeOfAWindow
import YangMills.Construction.BoundsOnEverySide.MovingTuplesOfALimitAlongStates
import YangMills.Construction.GrowingTori.TranslationsIsometriesAndMirrorsOfFourSpace
import YangMills.Construction.InfiniteLattice.CalculusOfTheLatticeRepresentatives
import YangMills.Construction.InfiniteLattice.CentredIdentityInAState
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtEverySpacingAndEveryCoupling
import YangMills.Construction.InfiniteLattice.ReflectionFormIsPositiveAndBoundedByTheSupremum
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctional
import YangMills.Construction.ReflectionPositivity.TranslatesOfPositiveCombinationsAndTheirReflectedProducts
import YangMills.Construction.TorusOrFourSpace.BallsTuplesInABallAndAdmissibleTuplesOfFourSpace
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction
open SeparatedTuples AmbientPoints
open ReflectionPositivity.TupleForm (PositiveSpan)
open R4TupleForms (FinTuple realSpanLift toTupleFunctional listOf finTupleEquiv)
open StateLimits (pairedValue)
open StateLimits.SeparatedFunctionals (HasConnectedParts IsPartitionExpansion)
open TorusMetric (euclidNormVec)
open TestFunctions (sharpNormR4 IsLipschitzFor euclidDistR4 closedBallR4 uniformNorm lipConstR4
  bestLipschitzConstant)
open Continuum.SeparatedFourTuples (tupleLength tupleComponents translateSep translateFn)
open PeriodicSpace.Kind (quotDist supportQ closedBallAbout setInfDist IsLipschitzQ lipTuplesSpacedInBalls)
open PeriodicSpace.EuclideanCase (quotDist_euclidean_eq closedBallAbout_euclidean)
open InfiniteLattice.CutoffRepresentative (centredProduct centredProductLinear centredProductLinear_basisVec
  CentredProductCalculus)
open PeriodicLattice (meshSize)
namespace BoundsOnEverySide
open ReflectionsAndOneInsertion (spanClassNorm timeUnitVec)
namespace TranslatedTuples
variable {s : Conventions.StandingParameters} {N : FreeMomentConstants} {K : ℕ → ℕ}
  {ρ ν : ∀ j, Measure (InfiniteLattice.GaugeField (meshSize s.L (K j : ℤ)))}
  {σ : FinTuple s → ℝ}
open SetPartition (Partitions PartitionsFin) in
def singletonPoints {n : ℕ} (π : PartitionsFin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => ({i} : Finset (Fin n)) ∈ π.parts
open SetPartition (Partitions PartitionsFin) in
def largeBlocks {n : ℕ} (π : PartitionsFin n) : Finset (Finset (Fin n)) :=
  π.parts.filter fun J => 2 ≤ J.card
open SetPartition (Partitions PartitionsFin) in
theorem card_eq_one_or_two_le {n : ℕ} (π : PartitionsFin n) {J : Finset (Fin n)} (hJ : J ∈ π.parts) :
    J.card = 1 ∨ 2 ≤ J.card := by
  have h : 0 < J.card := Finset.card_pos.2 (π.nonempty_of_mem_parts hJ)
  omega
open SetPartition (Partitions PartitionsFin) in
theorem filter_small_eq_image_singleton {n : ℕ} (π : PartitionsFin n) :
    π.parts.filter (fun J => ¬ 2 ≤ J.card) =
      (singletonPoints π).image fun i => ({i} : Finset (Fin n)) := by
  ext J
  simp only [Finset.mem_filter, Finset.mem_image, singletonPoints, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hJ, h2⟩
    have h1 : J.card = 1 := (card_eq_one_or_two_le π hJ).resolve_right h2
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h1
    exact ⟨i, hJ, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, by simp⟩
open SetPartition (Partitions PartitionsFin) in
theorem sup_largeBlocks {n : ℕ} (π : PartitionsFin n) :
    (largeBlocks π).sup id = (singletonPoints π)ᶜ := by
  ext i
  simp only [Finset.mem_sup, id, Finset.mem_compl, singletonPoints, largeBlocks, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨J, ⟨hJ, h2⟩, hi⟩ hs
    have : J = {i} := π.eq_of_mem_parts hJ hs hi (Finset.mem_singleton_self i)
    rw [this] at h2
    simp at h2
  · intro hs
    obtain ⟨J, hJ, hi⟩ := π.exists_mem (Finset.mem_univ i)
    refine ⟨J, ⟨hJ, ?_⟩, hi⟩
    rcases card_eq_one_or_two_le π hJ with h1 | h2
    · obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 h1
      have : k = i := (Finset.mem_singleton.1 hi).symm
      subst this
      exact absurd hJ hs
    · exact h2
open SetPartition (Partitions PartitionsFin) in
def largeBlocksPartition {n : ℕ} (π : PartitionsFin n) : Partitions (singletonPoints π)ᶜ :=
  Finpartition.ofSubset π (Finset.filter_subset _ _) (sup_largeBlocks π)
open SetPartition (Partitions PartitionsFin) in
theorem sum_partitions_le {n : ℕ} (A : ENNReal) (C : ℕ → ENNReal) :
    ∑ π : PartitionsFin n, ∏ J ∈ π.parts, (if J.card = 1 then A else C J.card) ≤
      ∑ I : Finset (Fin n), A ^ I.card *
        ∑ π ∈ partitionsBlocksGeTwo Iᶜ, ∏ J ∈ π.parts, C J.card := by
  classical
  have hw : ∀ π : PartitionsFin n, ∏ J ∈ π.parts, (if J.card = 1 then A else C J.card) =
      A ^ (singletonPoints π).card * ∏ J ∈ largeBlocks π, C J.card := by
    intro π
    rw [← Finset.prod_filter_mul_prod_filter_not π.parts (fun J => 2 ≤ J.card), mul_comm]
    congr 1
    · rw [filter_small_eq_image_singleton, Finset.prod_image
        (fun i _ j _ h => Finset.singleton_injective h)]
      simp
    · refine Finset.prod_congr rfl fun J hJ => ?_
      have h2 := (Finset.mem_filter.1 hJ).2
      rw [if_neg (by omega)]
  simp only [hw]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (PartitionsFin n)) singletonPoints]
  refine Finset.sum_le_sum fun I _ => ?_
  have h1 : ∑ π ∈ Finset.univ.filter (fun π : PartitionsFin n => singletonPoints π = I),
      A ^ (singletonPoints π).card * ∏ J ∈ largeBlocks π, C J.card =
      A ^ I.card * ∑ π ∈ Finset.univ.filter (fun π : PartitionsFin n => singletonPoints π = I),
        ∏ J ∈ largeBlocks π, C J.card := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun π hπ => ?_
    rw [(Finset.mem_filter.1 hπ).2]
  rw [h1]
  gcongr
  have hinj : Set.InjOn largeBlocks
      (Finset.univ.filter (fun π : PartitionsFin n => singletonPoints π = I) :
        Set (PartitionsFin n)) := by
    intro π hπ π' hπ' h
    have e1 : singletonPoints π = I := (Finset.mem_filter.1 hπ).2
    have e2 : singletonPoints π' = I := (Finset.mem_filter.1 hπ').2
    refine Finpartition.ext ?_
    rw [← Finset.filter_union_filter_not_eq (fun J => 2 ≤ J.card) π.parts,
      ← Finset.filter_union_filter_not_eq (fun J => 2 ≤ J.card) π'.parts,
      filter_small_eq_image_singleton, filter_small_eq_image_singleton, e1, e2]
    exact congrArg (· ∪ _) h
  have hinj2 : Set.InjOn (fun π : Partitions Iᶜ => π.parts)
      (partitionsBlocksGeTwo Iᶜ : Set (Partitions Iᶜ)) :=
    fun π _ π' _ h => Finpartition.ext h
  rw [← Finset.sum_image (f := fun T => ∏ J ∈ T, C J.card) hinj,
    show ∑ π ∈ partitionsBlocksGeTwo Iᶜ, ∏ J ∈ π.parts, C J.card =
      ∑ T ∈ (partitionsBlocksGeTwo Iᶜ).image (fun π : Partitions Iᶜ => π.parts),
        ∏ J ∈ T, C J.card from (Finset.sum_image (f := fun T => ∏ J ∈ T, C J.card) hinj2).symm]
  refine Finset.sum_le_sum_of_subset ?_
  intro T hT
  obtain ⟨π, hπ, rfl⟩ := Finset.mem_image.1 hT
  have e1 : singletonPoints π = I := (Finset.mem_filter.1 hπ).2
  subst e1
  refine Finset.mem_image.2 ⟨largeBlocksPartition π, ?_, rfl⟩
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun J hJ => ?_⟩
  exact (Finset.mem_filter.1 hJ).2
theorem momentBound_ne_top_of_hyp (B : MomentHypotheses N ρ ν) :
    ∀ n, 1 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → N.momentBound n d R ≠ ⊤ := by
  intro n _ d R hd hR
  refine ENNReal.sum_ne_top.2 fun I _ => ENNReal.mul_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ?_
  refine ENNReal.sum_ne_top.2 fun π hπ => ENNReal.prod_ne_top fun J hJ => ?_
  exact B.cStar_ne_top _ ((Finset.mem_filter.1 hπ).2 J hJ) d R hd hR
theorem sharpNormR4_nonneg (M : ℝ) (f : (Fin 4 → ℝ) → ℝ) : 0 ≤ sharpNormR4 M f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem prod_orderEmb_eq_prod {n : ℕ} (g : Fin n → ℝ) (J : Finset (Fin n)) :
    ∏ k : Fin J.card, g (J.orderEmbOfFin rfl k) = ∏ i ∈ J, g i := by
  rw [← Finset.prod_coe_sort J g]
  exact Fintype.prod_equiv (J.orderIsoOfFin rfl).toEquiv _ _ fun k => rfl
theorem isLipAt_comp {m n : ℕ} {f : Fin n → Pt s .euclidean → ℝ} {d R : ℝ}
    {e : Fin m → Fin n} (he : Function.Injective e) (h : IsLipAt s N.M N.one_le_M d R f) :
    IsLipAt s N.M N.one_le_M d R (f ∘ e) :=
  ⟨fun _ => h.1 _, fun _ => h.2.1 _, fun _ _ hik => h.2.2 _ _ (he.ne hik)⟩
theorem isLipschitzFor_of_isLipschitzQ {D : PeriodicSpace.Params} {f : (Fin 4 → ℝ) → ℝ}
    (h : IsLipschitzQ D .euclidean f) :
    IsLipschitzFor euclidDistR4 f := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C, hC, fun x y => ?_⟩
  have h' := hf x y
  rwa [quotDist_euclidean_eq] at h'
theorem euclidSupp_subset_of_supportQ {D : PeriodicSpace.Params} {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ}
    {R : ℝ} (h : supportQ D .euclidean f ⊆ closedBallAbout D .euclidean x R) :
    ReflectionPositivity.CutoffMirrors.euclidSupp f ⊆ closedBallR4 x R := by
  intro y hy
  have h' : y ∈ closedBallAbout D .euclidean x R := h fun r hr => by
    obtain ⟨z, hz, hd⟩ := hy r hr
    refine ⟨z, hz, ?_⟩
    rw [quotDist_euclidean_eq]
    exact hd
  rwa [closedBallAbout_euclidean] at h'
theorem abs_connected_le (B : MomentHypotheses N ρ ν)
    (hMap : ∀ j, HasConnectedParts K ρ ν j) (j : ℕ) {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (m : ℕ) (hm : 1 ≤ m) (g : separatedTuples s .euclidean m)
    (hg : IsLipAt s N.M N.one_le_M d R g.1) :
    ENNReal.ofReal |connectedOf (pairedValue K ρ ν j) m g| ≤
      (if m = 1 then ENNReal.ofReal (N.cTr * (1 + R) ^ 4) else N.cStar m d R) *
        ENNReal.ofReal (∏ i, sharpNormR4 N.M (g.1 i)) := by
  by_cases h1 : m = 1
  · subst h1
    rw [if_pos rfl, (hMap j).2.1 g]
    obtain ⟨B', ⟨-, x, rfl⟩, hsub⟩ := hg.2.1 0
    have ht := B.transfer_le j R hR (g.1 0) x (isLipschitzFor_of_isLipschitzQ (hg.1 0))
      (euclidSupp_subset_of_supportQ hsub)
    have hn := sharpNormR4_nonneg N.M (g.1 0)
    have hp : ∏ i, sharpNormR4 N.M (g.1 i) = sharpNormR4 N.M (g.1 0) := by simp
    rw [hp]
    by_cases hC : 0 ≤ N.cTr * (1 + R) ^ 4
    · rw [← ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal ht
    · have hC := not_le.1 hC
      have h0 : |(∫ U, InfiniteLattice.smearedEnergy (g.1 0) U ∂ρ j) -
          ∫ U, InfiniteLattice.smearedEnergy (g.1 0) U ∂ν j| ≤ 0 :=
        ht.trans (mul_nonpos_of_nonpos_of_nonneg hC.le hn)
      rw [ENNReal.ofReal_of_nonpos h0]
      exact bot_le
  · have h2 : 2 ≤ m := by omega
    rw [if_neg h1]
    have hc := B.cumulant_le j m h2 d R hd hR g.1 hg
    have he := (hMap j).2.2 m h2 g
    have hnorm : ‖Cumulants.mixedCumulant (ρ j) fun i U => InfiniteLattice.smearedEnergy (g.1 i) U‖ =
        |connectedOf (pairedValue K ρ ν j) m g| := by
      change ‖InfiniteLattice.smearedEnergyCumulant (ρ j) g.1‖ = _
      rw [← he, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm] at hc
    exact hc
theorem abs_pairedValue_le (B : MomentHypotheses N ρ ν)
    (hMap : ∀ j, HasConnectedParts K ρ ν j)
    (hSum : ∀ τ : FinTuple s → ℝ, IsTupleFunctional τ → IsPartitionExpansion τ) :
    ∀ (X : FinTuple s), 1 ≤ tupleLength X → ∀ d R : ℝ, 0 < d → 0 < R →
      TupleLipAt N X d R → ∀ j,
        |pairedValue K ρ ν j X| ≤
          (N.momentBound (tupleLength X) d R).toReal * sharpNormProd N X := by
  intro X hX d R hd hR hread j
  have hs := hSum _ (hMap j).1.1 (tupleLength X) hX ⟨X.1.2, X.2⟩
  have hs' : pairedValue K ρ ν j X = ∑ π : SetPartition.PartitionsFin (tupleLength X),
      ∏ J ∈ π.parts, connectedOf (pairedValue K ρ ν j) J.card
        (restrictSeparated ⟨X.1.2, X.2⟩ J) := hs
  set g : Fin (tupleLength X) → ℝ :=
    fun i => sharpNormR4 N.M (tupleComponents X i) with hgdef
  have hg0 : ∀ i, 0 ≤ g i := fun i => sharpNormR4_nonneg _ _
  have hP : 0 ≤ sharpNormProd N X := Finset.prod_nonneg fun i _ => hg0 i
  have hterm : ∀ π : SetPartition.PartitionsFin (tupleLength X),
      ENNReal.ofReal |∏ J ∈ π.parts, connectedOf (pairedValue K ρ ν j) J.card
        (restrictSeparated ⟨X.1.2, X.2⟩ J)| ≤
      (∏ J ∈ π.parts, (if J.card = 1 then ENNReal.ofReal (N.cTr * (1 + R) ^ 4)
        else N.cStar J.card d R)) * ENNReal.ofReal (sharpNormProd N X) := by
    intro π
    rw [Finset.abs_prod, ENNReal.ofReal_prod_of_nonneg fun _ _ => abs_nonneg _]
    have hb : ∀ J ∈ π.parts, ENNReal.ofReal |connectedOf (pairedValue K ρ ν j) J.card
        (restrictSeparated ⟨X.1.2, X.2⟩ J)| ≤
        (if J.card = 1 then ENNReal.ofReal (N.cTr * (1 + R) ^ 4) else N.cStar J.card d R) *
          ENNReal.ofReal (∏ i ∈ J, g i) := by
      intro J hJ
      have h := abs_connected_le B hMap j hd hR J.card
        (Finset.card_pos.2 (π.nonempty_of_mem_parts hJ)) (restrictSeparated ⟨X.1.2, X.2⟩ J)
        (isLipAt_comp (e := fun k => J.orderEmbOfFin rfl k) (J.orderEmbOfFin rfl).injective hread)
      have hp := prod_orderEmb_eq_prod g J
      rw [← hp]
      exact h
    refine (Finset.prod_le_prod' hb).trans ?_
    rw [Finset.prod_mul_distrib]
    refine le_of_eq ?_
    congr 1
    rw [← ENNReal.ofReal_prod_of_nonneg fun J _ => Finset.prod_nonneg fun i _ => hg0 i]
    have hb' : ∏ J ∈ π.parts, ∏ i ∈ J, g i = ∏ i, g i := by
      calc ∏ J ∈ π.parts, ∏ i ∈ J, g i = ∏ i ∈ π.parts.biUnion id, g i :=
            (Finset.prod_biUnion π.disjoint).symm
        _ = ∏ i, g i := by rw [π.biUnion_parts]
    rw [hb']
    rfl
  have hkey : ENNReal.ofReal |pairedValue K ρ ν j X| ≤
      N.momentBound (tupleLength X) d R * ENNReal.ofReal (sharpNormProd N X) := by
    rw [hs']
    calc ENNReal.ofReal |∑ π : SetPartition.PartitionsFin (tupleLength X),
          ∏ J ∈ π.parts, connectedOf (pairedValue K ρ ν j) J.card
            (restrictSeparated ⟨X.1.2, X.2⟩ J)|
        ≤ ENNReal.ofReal (∑ π : SetPartition.PartitionsFin (tupleLength X),
          |∏ J ∈ π.parts, connectedOf (pairedValue K ρ ν j) J.card
            (restrictSeparated ⟨X.1.2, X.2⟩ J)|) :=
          ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ π : SetPartition.PartitionsFin (tupleLength X),
          ENNReal.ofReal |∏ J ∈ π.parts, connectedOf (pairedValue K ρ ν j) J.card
            (restrictSeparated ⟨X.1.2, X.2⟩ J)| :=
          ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _
      _ ≤ ∑ π : SetPartition.PartitionsFin (tupleLength X),
          (∏ J ∈ π.parts, (if J.card = 1 then ENNReal.ofReal (N.cTr * (1 + R) ^ 4)
            else N.cStar J.card d R)) * ENNReal.ofReal (sharpNormProd N X) :=
          Finset.sum_le_sum fun π _ => hterm π
      _ = (∑ π : SetPartition.PartitionsFin (tupleLength X),
          ∏ J ∈ π.parts, (if J.card = 1 then ENNReal.ofReal (N.cTr * (1 + R) ^ 4)
            else N.cStar J.card d R)) * ENNReal.ofReal (sharpNormProd N X) := by
          rw [Finset.sum_mul]
      _ ≤ N.momentBound (tupleLength X) d R *
          ENNReal.ofReal (sharpNormProd N X) := by
          gcongr
          exact sum_partitions_le _ fun m => N.cStar m d R
  have hne := momentBound_ne_top_of_hyp B _ hX d R hd hR
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hne ENNReal.ofReal_ne_top) hkey
  rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_ofReal hP] at h3
section ShiftBounds
open InfiniteLattice (smearedEnergy compactTestFunctions)
theorem euclidNormVec_add_le (a b : Fin 4 → ℝ) :
    euclidNormVec (a + b) ≤ euclidNormVec a + euclidNormVec b := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem supportQ_eq_tsupport (D : PeriodicSpace.Params) (f : (Fin 4 → ℝ) → ℝ) :
    (supportQ D .euclidean f : Set (Fin 4 → ℝ)) = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (quotDist_euclidean_eq D) _
theorem euclidean_of_isLipAt {M : ℝ} {hM : 1 ≤ M} {n : ℕ} {d R : ℝ} (hd : 0 < d)
    {f : Fin n → (Fin 4 → ℝ) → ℝ} (h : IsLipAt s M hM d R f) :
    (∀ i, IsLipschitzFor euclidDistR4 (f i)) ∧
      (∀ i, ∃ x, tsupport (f i) ⊆ closedBallR4 x R) ∧
      ∀ i k, i ≠ k → ∀ x ∈ tsupport (f i), ∀ y ∈ tsupport (f k),
        d ≤ euclidNormVec (x - y) := by
  set Y := LipschitzClasses.params s M hM with hY
  have h' : f ∈ lipTuplesSpacedInBalls Y .euclidean n d R := h
  obtain ⟨hlip, hball, hsep⟩ := h'
  refine ⟨fun i => ?_, fun i => ?_, fun i k hik x hx y hy => ?_⟩
  · obtain ⟨C, hC, hh⟩ := hlip i
    refine ⟨C, hC, fun x y => ?_⟩
    have e' : quotDist Y .euclidean x y = euclidDistR4 x y :=
      quotDist_euclidean_eq Y x y
    have := hh x y
    rwa [e'] at this
  · obtain ⟨S, ⟨-, x, rfl⟩, hS⟩ := hball i
    refine ⟨x, ?_⟩
    rw [← supportQ_eq_tsupport Y]
    intro (y : Fin 4 → ℝ) hy
    have h₁ : quotDist Y .euclidean y x ≤ R := hS hy
    exact (quotDist_euclidean_eq Y y x).ge.trans h₁
  · have h₁ := hsep i k hik
    have hx' : x ∈ supportQ Y .euclidean (f i) := by
      rw [supportQ_eq_tsupport Y]
      exact hx
    have hy' : y ∈ supportQ Y .euclidean (f k) := by
      rw [supportQ_eq_tsupport Y]
      exact hy
    have h₂ : setInfDist Y .euclidean
        (supportQ Y .euclidean (f i))
        (supportQ Y .euclidean (f k)) ≤
        ENNReal.ofReal (quotDist Y .euclidean x y) :=
      iInf₂_le_of_le x hx' (iInf₂_le y hy')
    have h₃ := h₁.trans h₂
    rw [quotDist_euclidean_eq Y x y] at h₃
    exact (ENNReal.ofReal_le_ofReal_iff'.1 h₃).resolve_right (not_le.2 hd)
theorem isLipAt_of_euclidean {M : ℝ} {hM : 1 ≤ M} {n : ℕ} {d R : ℝ} (hR : 0 < R)
    {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hL : ∀ i, IsLipschitzFor euclidDistR4 (f i))
    (hB : ∀ i, ∃ x, tsupport (f i) ⊆ closedBallR4 x R)
    (hD : ∀ i k, i ≠ k → ∀ x ∈ tsupport (f i), ∀ y ∈ tsupport (f k),
      d ≤ euclidNormVec (x - y)) :
    IsLipAt s M hM d R f := by
  set Y := LipschitzClasses.params s M hM with hY
  suffices h' : f ∈ lipTuplesSpacedInBalls Y .euclidean n d R from h'
  · refine ⟨fun i => ?_, fun i => ?_, fun i k hik => ?_⟩
    · obtain ⟨C, hC, hh⟩ := hL i
      refine ⟨C, hC, fun x y => ?_⟩
      have e' : quotDist Y .euclidean x y = euclidDistR4 x y :=
        quotDist_euclidean_eq Y x y
      rw [e']
      exact hh x y
    · obtain ⟨x, hx⟩ := hB i
      refine ⟨closedBallAbout Y .euclidean x R, ⟨hR, x, rfl⟩, ?_⟩
      rw [supportQ_eq_tsupport Y]
      intro (y : Fin 4 → ℝ) hy
      have h₁ : euclidNormVec (y - x) ≤ R := hx hy
      exact (quotDist_euclidean_eq Y y x).le.trans h₁
    · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
      rw [supportQ_eq_tsupport Y] at hx hy
      rw [quotDist_euclidean_eq Y x y]
      exact ENNReal.ofReal_le_ofReal (hD i k hik x hx y hy)
theorem mem_separatedTuples_of {n : ℕ} {g : Fin n → (Fin 4 → ℝ) → ℝ}
    (h₁ : ∀ i, IsC1c (g i))
    (h₂ : ∀ i k, i ≠ k → Disjoint (tsupport (g i)) (tsupport (g k))) :
    g ∈ separatedTuples s .euclidean n := by
  refine (R4TupleForms.mem_separatedTuples_iff_ofFn g).2 ⟨fun f hf => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact h₁ i
  · exact List.pairwise_ofFn.2 fun i k hik => h₂ i k hik.ne
theorem isC1c_of_mem {n : ℕ} {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ separatedTuples s .euclidean n) (i : Fin n) : IsC1c (f i) :=
  ⟨(hf.1 i).1, (R4TupleForms.isCompact_tsupport_pt_iff_hasCompactSupport (s := s) (f i)).1 (hf.1 i).2⟩
theorem mem_compactTestFunctions {f : (Fin 4 → ℝ) → ℝ} (h : IsC1c f) :
    f ∈ compactTestFunctions := by apply _root_.YangMills.Construction.CutoffLimits.CenteredMomentsAndVolumeFirst.mem_compactTestFunctions_of_isC1c <;> assumption
theorem tsupport_shift (v : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℝ) :
    tsupport (fun x => f (x - v)) = (fun x => x - v) ⁻¹' tsupport f :=
  Continuum.SeparatedFourTuples.tsupport_comp_homeo (Homeomorph.subRight v) f
theorem isC1c_shift {f : (Fin 4 → ℝ) → ℝ} (h : IsC1c f) (v : Fin 4 → ℝ) :
    IsC1c (fun x => f (x - v)) :=
  ⟨ContDiff.comp h.1 (contDiff_id.sub contDiff_const),
    h.2.comp_homeomorph (Homeomorph.subRight v)⟩
theorem isC1c_sub {f g : (Fin 4 → ℝ) → ℝ} (hf : IsC1c f) (hg : IsC1c g) : IsC1c (f - g) :=
  ⟨ContDiff.sub hf.1 hg.1, hf.2.sub hg.2⟩
theorem tsupport_sub_subset (f g : (Fin 4 → ℝ) → ℝ) :
    tsupport (f - g) ⊆ tsupport f ∪ tsupport g := by
  refine closure_minimal ?_ ((isClosed_tsupport f).union (isClosed_tsupport g))
  exact (Function.support_sub f g).trans
    (Set.union_subset_union (subset_tsupport f) (subset_tsupport g))
theorem sharpNormR4_shift (M : ℝ) (f : (Fin 4 → ℝ) → ℝ) (v : Fin 4 → ℝ) :
    sharpNormR4 M (fun x => f (x - v)) = sharpNormR4 M f := by
  unfold sharpNormR4
  have h₁ : uniformNorm (fun x => f (x - v)) = uniformNorm f := by
    unfold uniformNorm
    exact (Equiv.subRight v).iSup_congr fun x => rfl
  have h₂ : lipConstR4 (fun x => f (x - v)) = lipConstR4 f := by
    unfold lipConstR4 bestLipschitzConstant
    congr 1
    ext C
    refine and_congr_right fun _ => ?_
    constructor
    · intro h x y
      have := h (x + v) (y + v)
      simpa [euclidDistR4] using this
    · intro h x y
      have := h (x - v) (y - v)
      simpa [euclidDistR4] using this
  rw [h₁, h₂]
theorem isBoundedRealRV_smearedEnergy (hCI : InfiniteLattice.CenteredIdentity.Statement) {k : ℕ}
    (hk : 0 < k) (μ : Measure (InfiniteLattice.GaugeField (meshSize s.L (k : ℤ))))
    [hμ : IsProbabilityMeasure μ] {f : (Fin 4 → ℝ) → ℝ} (hf : f ∈ compactTestFunctions) :
    Probability.IsBoundedRealRV
      (smearedEnergy f : InfiniteLattice.GaugeField (meshSize s.L (k : ℤ)) → ℝ) :=
  ((hCI { s with K := ⟨k, hk⟩ } μ hμ).1.1 f hf).2
theorem smearedEnergy_sub (hCI : InfiniteLattice.CenteredIdentity.Statement) {k : ℕ} (hk : 0 < k)
    (μ : Measure (InfiniteLattice.GaugeField (meshSize s.L (k : ℤ))))
    [hμ : IsProbabilityMeasure μ] {p q : (Fin 4 → ℝ) → ℝ} (hp : p ∈ compactTestFunctions)
    (hq : q ∈ compactTestFunctions)
    (U : InfiniteLattice.GaugeField (meshSize s.L (k : ℤ))) :
    smearedEnergy (p - q) U = smearedEnergy p U - smearedEnergy q U := by
  obtain ⟨F, hF, O, hO⟩ := (hCI { s with K := ⟨k, hk⟩ } μ hμ).1.2
  have hp' : p ∈ F := by
    rw [← SetLike.mem_coe, hF]
    exact hp
  have hq' : q ∈ F := by
    rw [← SetLike.mem_coe, hF]
    exact hq
  have h := map_sub O ⟨p, hp'⟩ ⟨q, hq'⟩
  have h₁ := hO (⟨p, hp'⟩ - ⟨q, hq'⟩)
  have h₂ := hO ⟨p, hp'⟩
  have h₃ := hO ⟨q, hq'⟩
  rw [h₁, h₂, h₃] at h
  exact congrFun h U
theorem integrable_smearedEnergy (hCI : InfiniteLattice.CenteredIdentity.Statement) {k : ℕ}
    (hk : 0 < k)
    (μ : Measure (InfiniteLattice.GaugeField (meshSize s.L (k : ℤ))))
    [hμ : IsProbabilityMeasure μ] {f : (Fin 4 → ℝ) → ℝ} (hf : f ∈ compactTestFunctions) :
    Integrable (smearedEnergy f :
      InfiniteLattice.GaugeField (meshSize s.L (k : ℤ)) → ℝ) μ := by
  have hb := isBoundedRealRV_smearedEnergy hCI hk μ hf
  obtain ⟨C, hC⟩ := hb.bounded
  exact Integrable.of_bound hb.measurable.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun U => by simpa using hC U)
theorem integrable_prod_centered (hCI : InfiniteLattice.CenteredIdentity.Statement) {k : ℕ}
    (hk : 0 < k)
    (μ : Measure (InfiniteLattice.GaugeField (meshSize s.L (k : ℤ))))
    [hμ : IsProbabilityMeasure μ] {n : ℕ} {g : Fin n → (Fin 4 → ℝ) → ℝ}
    (hg : ∀ i, g i ∈ compactTestFunctions) (c : Fin n → ℝ) :
    Integrable (fun U : InfiniteLattice.GaugeField (meshSize s.L (k : ℤ)) =>
      ∏ i, (smearedEnergy (g i) U - c i)) μ := by
  have hb := fun i => isBoundedRealRV_smearedEnergy hCI hk μ (hg i)
  choose C hC using fun i => (hb i).bounded
  have hm : Measurable (fun U : InfiniteLattice.GaugeField (meshSize s.L (k : ℤ)) =>
      ∏ i, (smearedEnergy (g i) U - c i)) :=
    Finset.measurable_prod _ fun i _ => (hb i).measurable.sub_const (c i)
  refine Integrable.of_bound hm.aestronglyMeasurable (∏ i, (C i + |c i|))
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
  exact (abs_sub _ _).trans (add_le_add (hC i U) le_rfl)
theorem prod_sub_prod_telescope {R : Type*} [CommRing R] : ∀ (n : ℕ) (a b : Fin n → R),
    ∏ i, a i - ∏ i, b i =
      ∑ i, ∏ l, (if l < i then a l else if l = i then a l - b l else b l)
  | 0, a, b => by simp
  | n + 1, a, b => by
    have ih := prod_sub_prod_telescope n (fun l => a l.succ) (fun l => b l.succ)
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
    have h₀ : ∏ l : Fin (n + 1), (if l < 0 then a l else if l = 0 then a l - b l else b l) =
        (a 0 - b 0) * ∏ l : Fin n, b l.succ := by
      rw [Fin.prod_univ_succ]
      simp [Fin.succ_ne_zero]
    have h₁ : ∀ i : Fin n, ∏ l : Fin (n + 1),
        (if l < i.succ then a l else if l = i.succ then a l - b l else b l) =
        a 0 * ∏ l : Fin n, (if l < i then a l.succ else
          if l = i then a l.succ - b l.succ else b l.succ) := by
      intro i
      rw [Fin.prod_univ_succ]
      simp [Fin.succ_pos, Fin.succ_lt_succ_iff, Fin.succ_inj]
    rw [h₀]
    simp only [h₁]
    rw [← Finset.mul_sum, ← ih]
    ring
def shiftHybrid {n : ℕ} (f : Fin n → (Fin 4 → ℝ) → ℝ) (v : Fin 4 → ℝ) (i l : Fin n) :
    (Fin 4 → ℝ) → ℝ :=
  if l < i then (fun x => f l (x - v)) else
    if l = i then (fun x => f l (x - v)) - f l else f l
theorem tsupport_shiftHybrid_subset {n : ℕ} (f : Fin n → (Fin 4 → ℝ) → ℝ) (v : Fin 4 → ℝ)
    (i l : Fin n) :
    tsupport (shiftHybrid f v i l) ⊆ tsupport (f l) ∪ (fun x => x - v) ⁻¹' tsupport (f l) := by
  unfold shiftHybrid
  split_ifs
  · rw [tsupport_shift]
    exact Set.subset_union_right
  · refine (tsupport_sub_subset _ _).trans ?_
    rw [tsupport_shift]
    exact Set.union_subset Set.subset_union_right Set.subset_union_left
  · exact Set.subset_union_left
theorem euclidNormVec_neg (a : Fin 4 → ℝ) : euclidNormVec (-a) = euclidNormVec a := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem half_le_of_enlarged {A B : Set (Fin 4 → ℝ)} {d : ℝ} {v : Fin 4 → ℝ}
    (hD : ∀ x ∈ A, ∀ y ∈ B, d ≤ euclidNormVec (x - y))
    (hv : euclidNormVec v ≤ d / 2) (hd : 0 < d) {x y : Fin 4 → ℝ}
    (hx : x ∈ A ∪ (fun x => x - v) ⁻¹' A) (hy : y ∈ B ∪ (fun x => x - v) ⁻¹' B) :
    d / 2 ≤ euclidNormVec (x - y) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · linarith [hD x hx y hy]
  · have h := hD x hx _ hy
    have e : x - (y - v) = (x - y) + v := by abel
    rw [e] at h
    linarith [euclidNormVec_add_le (x - y) v]
  · have h := hD _ hx y hy
    have e : x - v - y = (x - y) + -v := by abel
    rw [e] at h
    linarith [euclidNormVec_add_le (x - y) (-v), euclidNormVec_neg v]
  · have h := hD _ hx _ hy
    have e : x - v - (y - v) = x - y := by abel
    rw [e] at h
    linarith
theorem enlarged_subset_ball {A : Set (Fin 4 → ℝ)} {c : Fin 4 → ℝ} {R : ℝ} {v : Fin 4 → ℝ}
    (hA : A ⊆ closedBallR4 c R) (hv : euclidNormVec v ≤ 1) :
    A ∪ (fun x => x - v) ⁻¹' A ⊆ closedBallR4 c (R + 1) := by
  rintro x (hx | hx)
  · have h : euclidNormVec (x - c) ≤ R := hA hx
    change euclidNormVec (x - c) ≤ R + 1
    linarith
  · have h : euclidNormVec (x - v - c) ≤ R := hA hx
    change euclidNormVec (x - c) ≤ R + 1
    have e : x - c = (x - v - c) + v := by abel
    rw [e]
    linarith [euclidNormVec_add_le (x - v - c) v]
theorem isLipschitzFor_shift {f : (Fin 4 → ℝ) → ℝ} (v : Fin 4 → ℝ)
    (h : IsLipschitzFor euclidDistR4 f) :
    IsLipschitzFor euclidDistR4 (fun x => f (x - v)) := by
  obtain ⟨C, hC, hh⟩ := h
  refine ⟨C, hC, fun x y => ?_⟩
  have := hh (x - v) (y - v)
  simpa [euclidDistR4] using this
theorem isLipschitzFor_sub {f g : (Fin 4 → ℝ) → ℝ}
    (hf : IsLipschitzFor euclidDistR4 f) (hg : IsLipschitzFor euclidDistR4 g) :
    IsLipschitzFor euclidDistR4 (f - g) := by
  obtain ⟨C, hC, hh⟩ := hf
  obtain ⟨C', hC', hh'⟩ := hg
  refine ⟨C + C', add_nonneg hC hC', fun x y => ?_⟩
  have e : (f - g) x - (f - g) y = (f x - f y) - (g x - g y) := by
    simp only [Pi.sub_apply]
    ring
  rw [e, add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (hh x y) (hh' x y))
theorem shiftHybrid_mem {n : ℕ} {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ separatedTuples s .euclidean n) {d : ℝ} (hd : 0 < d) {v : Fin 4 → ℝ}
    (hD : ∀ i k, i ≠ k → ∀ x ∈ tsupport (f i), ∀ y ∈ tsupport (f k),
      d ≤ euclidNormVec (x - y))
    (hv : euclidNormVec v ≤ d / 2) (i : Fin n) :
    shiftHybrid f v i ∈ separatedTuples s .euclidean n := by
  refine mem_separatedTuples_of (fun l => ?_) fun l k hlk => ?_
  · have h₁ := isC1c_of_mem hf l
    unfold shiftHybrid
    split_ifs
    · exact isC1c_shift h₁ v
    · exact isC1c_sub (isC1c_shift h₁ v) h₁
    · exact h₁
  · refine Set.disjoint_left.2 fun x hx hy => ?_
    have h := half_le_of_enlarged (hD l k hlk) hv hd (tsupport_shiftHybrid_subset f v i l hx)
      (tsupport_shiftHybrid_subset f v i k hy)
    have h₀ : euclidNormVec (x - x) = 0 := by simp [euclidNormVec]
    rw [h₀] at h
    linarith
theorem shiftHybrid_isLipAt {M : ℝ} {hM : 1 ≤ M} {n : ℕ} {f : Fin n → (Fin 4 → ℝ) → ℝ} {d R : ℝ}
    (hd : 0 < d) (hR : 0 < R) (hr : IsLipAt s M hM d R f) {v : Fin 4 → ℝ}
    (hv : euclidNormVec v ≤ min (d / 2) 1) (i : Fin n) :
    IsLipAt s M hM (d / 2) (R + 1) (shiftHybrid f v i) := by
  obtain ⟨hL, hB, hD⟩ := euclidean_of_isLipAt hd hr
  have hv₁ := hv.trans (min_le_left _ _)
  have hv₂ := hv.trans (min_le_right _ _)
  refine isLipAt_of_euclidean (by linarith) (fun l => ?_) (fun l => ?_) fun l k hlk x hx y hy => ?_
  · unfold shiftHybrid
    split_ifs
    · exact isLipschitzFor_shift v (hL l)
    · exact isLipschitzFor_sub (isLipschitzFor_shift v (hL l)) (hL l)
    · exact hL l
  · obtain ⟨c, hc⟩ := hB l
    exact ⟨c, (tsupport_shiftHybrid_subset f v i l).trans (enlarged_subset_ball hc hv₂)⟩
  · exact half_le_of_enlarged (hD l k hlk) hv₁ hd (tsupport_shiftHybrid_subset f v i l hx)
      (tsupport_shiftHybrid_subset f v i k hy)
theorem prod_sharpNorm_shiftHybrid (M : ℝ) {n : ℕ} (f : Fin n → (Fin 4 → ℝ) → ℝ) (v : Fin 4 → ℝ)
    (i : Fin n) :
    ∏ l, sharpNormR4 M (shiftHybrid f v i l) =
      sharpNormR4 M ((fun x => f i (x - v)) - f i) *
        ∏ l ∈ Finset.univ.erase i, sharpNormR4 M (f l) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp [shiftHybrid]
  · refine Finset.prod_congr rfl fun l hl => ?_
    have hli : l ≠ i := Finset.ne_of_mem_erase hl
    unfold shiftHybrid
    split_ifs
    · exact sharpNormR4_shift M (f l) v
    · rfl
theorem abs_shift_sub_le_aux (hKpos : ∀ j, 0 < K j)
    (hCI : InfiniteLattice.CenteredIdentity.Statement)
    (hρ : ∀ j, IsProbabilityMeasure (ρ j)) (hν : ∀ j, IsProbabilityMeasure (ν j))
    (hle : ∀ (X : FinTuple s), 1 ≤ tupleLength X → ∀ d R : ℝ, 0 < d → 0 < R →
      TupleLipAt N X d R → ∀ j,
        |pairedValue K ρ ν j X| ≤
          (N.momentBound (tupleLength X) d R).toReal * sharpNormProd N X)
    {n : ℕ} (hn : 1 ≤ n) {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ separatedTuples s .euclidean n) {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (hr : IsLipAt s N.M N.one_le_M d R f) (j : ℕ) {v : Fin 4 → ℝ}
    (hv : euclidNormVec v ≤ min (d / 2) 1) :
    |(∫ U, ∏ i, (smearedEnergy (fun x => f i (x - v)) U -
          ∫ V, smearedEnergy (fun x => f i (x - v)) V ∂ν j) ∂ρ j) -
        ∫ U, ∏ i, (smearedEnergy (f i) U - ∫ V, smearedEnergy (f i) V ∂ν j) ∂ρ j| ≤
      (N.momentBound n (d / 2) (R + 1)).toReal *
        ∑ i, sharpNormR4 N.M ((fun x => f i (x - v)) - f i) *
          ∏ l ∈ Finset.univ.erase i, sharpNormR4 N.M (f l) := by
  have := hρ j
  have := hν j
  obtain ⟨-, -, hD⟩ := euclidean_of_isLipAt hd hr
  have hv₁ := hv.trans (min_le_left _ _)
  have hk := hKpos j
  have ht : ∀ l, f l ∈ compactTestFunctions := fun l => mem_compactTestFunctions (isC1c_of_mem hf l)
  have hts : ∀ l, (fun x => f l (x - v)) ∈ compactTestFunctions :=
    fun l => mem_compactTestFunctions (isC1c_shift (isC1c_of_mem hf l) v)
  have hmem := fun i => shiftHybrid_mem (s := s) hf hd hD hv₁ i
  have hmt : ∀ i l, shiftHybrid f v i l ∈ compactTestFunctions :=
    fun i l => mem_compactTestFunctions (isC1c_of_mem (hmem i) l)
  have hfac : ∀ (i l : Fin n) (U : InfiniteLattice.GaugeField (meshSize s.L (K j : ℤ))),
      smearedEnergy (shiftHybrid f v i l) U -
      ∫ V, smearedEnergy (shiftHybrid f v i l) V ∂ν j =
      if l < i then smearedEnergy (fun x => f l (x - v)) U -
          ∫ V, smearedEnergy (fun x => f l (x - v)) V ∂ν j
        else if l = i then (smearedEnergy (fun x => f l (x - v)) U -
            ∫ V, smearedEnergy (fun x => f l (x - v)) V ∂ν j) -
          (smearedEnergy (f l) U - ∫ V, smearedEnergy (f l) V ∂ν j)
        else smearedEnergy (f l) U - ∫ V, smearedEnergy (f l) V ∂ν j := by
    intro i l U
    unfold shiftHybrid
    split_ifs with h₁ h₂
    · rfl
    · have e₁ : ∀ W : InfiniteLattice.GaugeField (meshSize s.L (K j : ℤ)),
          smearedEnergy ((fun x => f l (x - v)) - f l) W =
          smearedEnergy (fun x => f l (x - v)) W - smearedEnergy (f l) W :=
        fun W => smearedEnergy_sub hCI hk (ρ j) (hts l) (ht l) W
      simp only [e₁]
      rw [integral_sub (integrable_smearedEnergy hCI hk (ν j) (hts l))
        (integrable_smearedEnergy hCI hk (ν j) (ht l))]
      ring
    · rfl
  have hint₁ := integrable_prod_centered hCI hk (ρ j) hts
    (fun i => ∫ V, smearedEnergy (fun x => f i (x - v)) V ∂ν j)
  have hint₂ := integrable_prod_centered hCI hk (ρ j) ht
    (fun i => ∫ V, smearedEnergy (f i) V ∂ν j)
  have hint₃ := fun i => integrable_prod_centered hCI hk (ρ j) (hmt i)
    (fun l => ∫ V, smearedEnergy (shiftHybrid f v i l) V ∂ν j)
  have hsum : (∫ U, ∏ i, (smearedEnergy (fun x => f i (x - v)) U -
        ∫ V, smearedEnergy (fun x => f i (x - v)) V ∂ν j) ∂ρ j) -
      ∫ U, ∏ i, (smearedEnergy (f i) U - ∫ V, smearedEnergy (f i) V ∂ν j) ∂ρ j =
      ∑ i, ∫ U, ∏ l, (smearedEnergy (shiftHybrid f v i l) U -
        ∫ V, smearedEnergy (shiftHybrid f v i l) V ∂ν j) ∂ρ j := by
    rw [← integral_sub hint₁ hint₂, ← integral_finsetSum _ fun i _ => hint₃ i]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp only [hfac]
    exact prod_sub_prod_telescope n _ _
  rw [hsum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hb := hle ⟨⟨n, shiftHybrid f v i⟩, hmem i⟩ hn (d / 2) (R + 1) (by linarith) (by linarith)
    (shiftHybrid_isLipAt hd hR hr hv i) j
  have hnorms := prod_sharpNorm_shiftHybrid N.M f v i
  refine le_trans hb (le_of_eq ?_)
  change _ * ∏ l, sharpNormR4 N.M (shiftHybrid f v i l) = _
  rw [hnorms]
  rfl
theorem abs_shift_sub_le_of (hKpos : ∀ j, 0 < K j)
    (hCI : InfiniteLattice.CenteredIdentity.Statement)
    (hρ : ∀ j, IsProbabilityMeasure (ρ j)) (hν : ∀ j, IsProbabilityMeasure (ν j))
    (hle : ∀ (X : FinTuple s), 1 ≤ tupleLength X → ∀ d R : ℝ, 0 < d → 0 < R →
      TupleLipAt N X d R → ∀ j,
        |pairedValue K ρ ν j X| ≤
          (N.momentBound (tupleLength X) d R).toReal * sharpNormProd N X) :
    ∀ (X : FinTuple s), 1 ≤ tupleLength X →
    ∀ d R : ℝ, 0 < d → 0 < R → TupleLipAt N X d R →
    ∀ (j : ℕ) (v : Fin 4 → ℝ), euclidNormVec v ≤ min (d / 2) 1 →
      |pairedValue K ρ ν j (translateSep v X) - pairedValue K ρ ν j X| ≤
        (N.momentBound (tupleLength X) (d / 2) (R + 1)).toReal *
          shiftedSharpNormSum N X v := by
  intro X hn d R hd hR hr j v hv
  exact abs_shift_sub_le_aux hKpos hCI hρ hν hle hn (f := X.1.2) X.2 hd hR hr j hv
theorem sharpNorm_nonneg (M : ℝ) (f : (Fin 4 → ℝ) → ℝ) : 0 ≤ sharpNormR4 M f := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.sharpNormR4_nonneg <;> assumption
theorem tendsto_sharpNorm_shift_sub (hT : ToriLimits.EuclideanSymmetryFacts.Statement)
    (s : Conventions.StandingParameters) {M : ℝ} (hM : 1 ≤ M) {f : (Fin 4 → ℝ) → ℝ}
    (hf : IsC1c f) :
    Tendsto (fun v : Fin 4 → ℝ =>
      sharpNormR4 M ((fun x => f (x - v)) - f)) (𝓝 0) (𝓝 0) := by
  let D : ReflectionPositivity.AxisMirror.MirrorData := ⟨s, 1, one_pos⟩
  let Mc : ReflectionPositivity.AxisMirror.Ambient.ScaleParam := ⟨M, hM⟩
  have hd : ∀ x y : Fin 4 → ℝ, ReflectionPositivity.AxisMirror.Ambient.metric D .euclidean x y =
      euclidNormVec (x - y) := fun _ _ => rfl
  have hs : (ReflectionPositivity.AxisMirror.Ambient.closedSupport D .euclidean f :
      Set (Fin 4 → ℝ)) = tsupport f :=
    SeparatedTuplesR4.closureWrt_euclid_eq_closure hd _
  have hmem : f ∈ ReflectionPositivity.AxisMirror.Ambient.compactC1 D ℝ .euclidean := by
    refine ⟨hf.1, ?_⟩
    rw [hs]
    exact (SeparatedTuplesR4.isCompactWrt_euclid_iff hd _).2 hf.2
  obtain ⟨⟨hmono, hlim⟩, ⟨hclose, -⟩, -⟩ := (hT D Mc).1 ⟨f, hmem⟩
  set μ := ReflectionPositivity.AxisMirror.Ambient.smoothModulus Mc (⟨f, hmem⟩ :
    ReflectionPositivity.AxisMirror.Ambient.compactC1 D ℝ .euclidean) with hμ
  have hμ₀ : ∀ δ, 0 ≤ μ δ := fun δ =>
    le_max_of_le_left (mul_nonneg ENNReal.toReal_nonneg δ.2)
  have hbound : ∀ v : Fin 4 → ℝ, sharpNormR4 M ((fun x => f (x - v)) - f) ≤
      μ (euclidNormVec v).toNNReal := by
    intro v
    have h := hclose v 0
    have e₁ : ReflectionPositivity.AxisMirror.Ambient.metric D .euclidean v (0 : Fin 4 → ℝ) =
        euclidNormVec v := by
      rw [hd, sub_zero]
    rw [e₁] at h
    change sharpNormR4 M ((fun x => f (x - v)) - (fun x => f (x - 0))) ≤ _ at h
    simpa only [sub_zero] using h
  have hve : Tendsto euclidNormVec (𝓝 0) (𝓝 0) := by
    have hc : Continuous euclidNormVec := by
      unfold euclidNormVec
      fun_prop
    have h0 : euclidNormVec 0 = 0 := by simp [euclidNormVec]
    simpa [h0] using hc.tendsto (0 : Fin 4 → ℝ)
  refine squeeze_zero (fun v => sharpNorm_nonneg M _) hbound ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ₀, hδ₁, hδ₂⟩ := ((hlim.eventually (Metric.ball_mem_nhds _ hε)).and
    self_mem_nhdsWithin).exists
  have hδ₀ : (0 : ℝ) < δ₀ := NNReal.coe_pos.2 hδ₂
  filter_upwards [hve.eventually (gt_mem_nhds hδ₀)] with v hv
  have h₁ : (euclidNormVec v).toNNReal ≤ δ₀ := Real.toNNReal_le_iff_le_coe.2 hv.le
  have h₂ := hmono h₁
  have h₃ : dist (μ δ₀) 0 < ε := hδ₁
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hμ₀ _)] at h₃ ⊢
  exact h₂.trans_lt h₃
theorem shift_bound_tendsto_of (hT : ToriLimits.EuclideanSymmetryFacts.Statement) :
    ∀ (X : FinTuple s), 1 ≤ tupleLength X →
    ∀ d R : ℝ, 0 < d → 0 < R → TupleLipAt N X d R →
      Tendsto (fun v : Fin 4 → ℝ =>
        (N.momentBound (tupleLength X) (d / 2) (R + 1)).toReal *
          shiftedSharpNormSum N X v) (𝓝 0) (𝓝 0) := by
  intro X _ d R _ _ _
  have hsum : Tendsto (fun v : Fin 4 → ℝ => shiftedSharpNormSum N X v) (𝓝 0) (𝓝 0) := by
    unfold shiftedSharpNormSum
    have h : Tendsto (fun v : Fin 4 → ℝ => ∑ i,
        sharpNormR4 N.M (_root_.YangMills.Construction.Continuum.SeparatedFourTuples.translateFn v (tupleComponents X i) - tupleComponents X i) *
          ∏ l ∈ Finset.univ.erase i, sharpNormR4 N.M (tupleComponents X l))
        (𝓝 0) (𝓝 (∑ _i : Fin (tupleLength X), (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      have h₁ := tendsto_sharpNorm_shift_sub hT s N.one_le_M
        (isC1c_of_mem (f := tupleComponents X) X.2 i)
      have h₂ := h₁.mul_const (∏ l ∈ Finset.univ.erase i, sharpNormR4 N.M (tupleComponents X l))
      rw [zero_mul] at h₂
      exact h₂
    simpa using h
  simpa using hsum.const_mul (N.momentBound (tupleLength X) (d / 2) (R + 1)).toReal
end ShiftBounds
theorem quotDist_euclidean (D : PeriodicSpace.Params) (x y : Fin 4 → ℝ) :
    quotDist D .euclidean x y = euclidNormVec (x - y) := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_euclidean <;> assumption
theorem supportQ_euclidean (D : PeriodicSpace.Params) (f : (Fin 4 → ℝ) → ℝ) :
    (supportQ D .euclidean f : Set (Fin 4 → ℝ)) = tsupport f := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.supportQ_eq_tsupport <;> assumption
def entryFn (X : FinTuple s) (i : Fin (tupleLength X)) : (Fin 4 → ℝ) → ℝ :=
  tupleComponents X i
theorem isC1c_componentFn (X : FinTuple s) (i : Fin (tupleLength X)) :
    SeparatedTuples.IsC1c (entryFn X i) :=
  ((R4TupleForms.mem_separatedTuples_iff_ofFn X.1.2).1 X.2).1 _
    ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩)
theorem disjoint_componentFn (X : FinTuple s) {i k : Fin (tupleLength X)} (hik : i ≠ k) :
    Disjoint (tsupport (entryFn X i)) (tsupport (entryFn X k)) :=
  Disjoint.mono (R4TupleForms.tsupport_pt_euclidean (s := s) (entryFn X i)).ge
    (R4TupleForms.tsupport_pt_euclidean (s := s) (entryFn X k)).ge (X.2.2 hik)
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem isLipschitzQ_of_isC1c (D : PeriodicSpace.Params) {f : (Fin 4 → ℝ) → ℝ}
    (hf : SeparatedTuples.IsC1c f) :
    IsLipschitzQ D .euclidean f := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hf.2 hf.1 (by norm_num)
  refine ⟨C, C.2, fun (x y : Fin 4 → ℝ) => ?_⟩
  have h := hC.dist_le_mul x y
  rw [Real.dist_eq, dist_eq_norm] at h
  have h₂ : ‖x - y‖ ≤ euclidNormVec (x - y) :=
    SeparatedTuplesR4.norm_le_euclidNormVec _
  rw [Real.norm_eq_abs]
  refine h.trans ?_
  rw [show quotDist D .euclidean x y = _ from quotDist_euclidean D x y]
  exact mul_le_mul_of_nonneg_left h₂ C.2
theorem exists_tupleLipAt (X : FinTuple s) (_hX : 1 ≤ tupleLength X) :
    ∃ d R : ℝ, 0 < d ∧ 0 < R ∧ TupleLipAt N X d R := by
  have hC : ∀ i, IsCompact (tsupport (entryFn X i)) := fun i => (isC1c_componentFn X i).2
  have hU : IsCompact (⋃ i, tsupport (entryFn X i)) := isCompact_iUnion hC
  obtain ⟨R₀, hR₀⟩ := hU.exists_bound_of_continuousOn continuous_euclidNormVec.continuousOn
  let P : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ)) :=
    ⋃ p : {p : Fin (tupleLength X) × Fin (tupleLength X) // p.1 ≠ p.2},
      tsupport (entryFn X p.1.1) ×ˢ tsupport (entryFn X p.1.2)
  have hP : IsCompact P := isCompact_iUnion fun p => (hC _).prod (hC _)
  have hcont : ContinuousOn (fun q : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      euclidNormVec (q.1 - q.2)) P :=
    (continuous_euclidNormVec.comp (continuous_fst.sub continuous_snd)).continuousOn
  have hpos : ∀ q ∈ P, (0 : ℝ) < euclidNormVec (q.1 - q.2) := by
    intro q hq
    obtain ⟨p, hq⟩ := Set.mem_iUnion.1 hq
    have hne : q.1 - q.2 ≠ 0 := fun h => by
      have h' : q.1 = q.2 := sub_eq_zero.1 h
      exact Set.disjoint_left.1 (disjoint_componentFn X p.2) hq.1 (h' ▸ hq.2)
    have hn : 0 < ‖(WithLp.toLp 2 (q.1 - q.2) : EuclideanSpace ℝ (Fin 4))‖ :=
      norm_pos_iff.2 fun h => hne (congrArg WithLp.ofLp h)
    rwa [euclidNormVec_eq_norm]
  obtain ⟨d, hd, hdP⟩ := hP.exists_forall_le' hcont hpos
  refine ⟨d, max R₀ 1, hd, lt_max_of_lt_right one_pos, ?_⟩
  refine ⟨fun i => isLipschitzQ_of_isC1c _ (isC1c_componentFn X i), fun i => ?_, fun i k hik => ?_⟩
  · refine ⟨_, ⟨lt_max_of_lt_right one_pos, (0 : Fin 4 → ℝ), rfl⟩, ?_⟩
    intro y hy
    have hy' : y ∈ tsupport (entryFn X i) := by
      rw [← supportQ_euclidean (PeriodicSpace.Params.ofStanding s N.M N.one_le_M)]
      exact hy
    have h₁ := hR₀ y (Set.mem_iUnion.2 ⟨i, hy'⟩)
    have h₂ : ∀ y' : Fin 4 → ℝ, ‖euclidNormVec y'‖ ≤ R₀ →
        euclidNormVec (y' - 0) ≤ max R₀ 1 := fun y' h => by
      rw [sub_zero]
      exact (le_abs_self _).trans (h.trans (le_max_left _ _))
    exact (quotDist_euclidean _ y 0).le.trans (h₂ y h₁)
  · refine le_iInf fun z => le_iInf fun hz => le_iInf fun z' => le_iInf fun hz' => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hz₁ : z ∈ tsupport (entryFn X i) := by
      rw [← supportQ_euclidean (PeriodicSpace.Params.ofStanding s N.M N.one_le_M)]
      exact hz
    have hz₂ : z' ∈ tsupport (entryFn X k) := by
      rw [← supportQ_euclidean (PeriodicSpace.Params.ofStanding s N.M N.one_le_M)]
      exact hz'
    exact (hdP (z, z') (Set.mem_iUnion.2 ⟨⟨(i, k), hik⟩, hz₁, hz₂⟩)).trans
      (quotDist_euclidean _ z z').ge
theorem listOf_translateSep (v : Fin 4 → ℝ) (X : FinTuple s) :
    listOf (translateSep v X) = push (translate v) (listOf X) := by
  obtain ⟨⟨n, f⟩, hf⟩ := X
  exact R4TupleForms.listOf_transportTuple (Continuum.SeparatedFourTuples.translateEquiv v) hf
    (Continuum.SeparatedFourTuples.transportTuple_mem
      (Continuum.SeparatedFourTuples.translateIsometry v) hf)
theorem realSpanLift_basisVec (ψ : FinTuple s → ℝ) (X : FinTuple s) :
    realSpanLift ψ (basisVec (listOf X)) = (ψ X : ℂ) := by
  have h : (finTupleEquiv s).symm (listOf X) = X :=
    (finTupleEquiv s).symm_apply_apply X
  simp [realSpanLift, R4TupleForms.spanLift, linearExtend_basisVec, h]
theorem realSpanLift_pushSpan_translate (ψ : FinTuple s → ℝ) (v : Fin 4 → ℝ) (X : FinTuple s) :
    realSpanLift ψ (pushSpan (translate v) (basisVec (listOf X))) =
      (ψ (translateSep v X) : ℂ) := by
  rw [pushSpan, linearExtend_basisVec, ← listOf_translateSep, realSpanLift_basisVec]
theorem exists_listOf_eq (Y : SepTuple) : ∃ X : FinTuple s, listOf X = Y :=
  (finTupleEquiv s).surjective Y
theorem translateSep_of_length_zero (v : Fin 4 → ℝ) {X : FinTuple s}
    (hX : tupleLength X = 0) : translateSep v X = X := by
  refine Continuum.SeparatedFourTuples.sepTuple_ext rfl fun i => ?_
  have : IsEmpty (Fin (tupleLength (translateSep v X))) := by
    change IsEmpty (Fin (tupleLength X))
    rw [hX]
    exact inferInstance
  exact this.elim i
theorem tendsto_euclidNormVec {v : ℕ → Fin 4 → ℝ} (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun j => euclidNormVec (v j)) atTop (𝓝 0) := by
  have h := (continuous_euclidNormVec.tendsto (0 : Fin 4 → ℝ)).comp hv
  have h0 : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by
    simp [euclidNormVec]
  rwa [h0] at h
theorem tendsto_pairedValue_translateSep
    (hlim : StateLimits.IsPointwiseLimit K ρ ν σ)
    (hEq : ∀ (X : FinTuple s), 1 ≤ tupleLength X →
      ∀ d R : ℝ, 0 < d → 0 < R → TupleLipAt N X d R →
      ∀ (j : ℕ) (v : Fin 4 → ℝ), euclidNormVec v ≤ min (d / 2) 1 →
        |pairedValue K ρ ν j (translateSep v X) - pairedValue K ρ ν j X| ≤
          (N.momentBound (tupleLength X) (d / 2) (R + 1)).toReal *
            shiftedSharpNormSum N X v)
    (hTend : ∀ (X : FinTuple s), 1 ≤ tupleLength X →
      ∀ d R : ℝ, 0 < d → 0 < R → TupleLipAt N X d R →
        Tendsto (fun v : Fin 4 → ℝ =>
          (N.momentBound (tupleLength X) (d / 2) (R + 1)).toReal *
            shiftedSharpNormSum N X v) (𝓝 0) (𝓝 0))
    (X : FinTuple s) {v : ℕ → Fin 4 → ℝ} (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun j => pairedValue K ρ ν j (translateSep (v j) X)) atTop (𝓝 (σ X)) := by
  rcases Nat.eq_zero_or_pos (tupleLength X) with h0 | hpos
  · simpa only [translateSep_of_length_zero _ h0] using hlim X
  obtain ⟨d, R, hd, hR, hread⟩ := exists_tupleLipAt (N := N) X hpos
  have hsmall : ∀ᶠ j in atTop, euclidNormVec (v j) ≤ min (d / 2) 1 :=
    (tendsto_euclidNormVec hv).eventually (Iic_mem_nhds (lt_min (half_pos hd) one_pos))
  have hdiff : Tendsto (fun j => pairedValue K ρ ν j (translateSep (v j) X) -
      pairedValue K ρ ν j X) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((hTend X hpos d R hd hR hread).comp hv)
    filter_upwards [hsmall] with j hj
    exact hEq X hpos d R hd hR hread j (v j) hj
  simpa using hdiff.add (hlim X)
theorem tendsto_shifted_of
    (_hρ : ∀ j, IsProbabilityMeasure (ρ j))
    (hlim : StateLimits.IsPointwiseLimit K ρ ν σ)
    (hEq : ∀ (X : FinTuple s), 1 ≤ tupleLength X →
      ∀ d R : ℝ, 0 < d → 0 < R → TupleLipAt N X d R →
      ∀ (j : ℕ) (v : Fin 4 → ℝ), euclidNormVec v ≤ min (d / 2) 1 →
        |pairedValue K ρ ν j (translateSep v X) - pairedValue K ρ ν j X| ≤
          (N.momentBound (tupleLength X) (d / 2) (R + 1)).toReal *
            shiftedSharpNormSum N X v)
    (hTend : ∀ (X : FinTuple s), 1 ≤ tupleLength X →
      ∀ d R : ℝ, 0 < d → 0 < R → TupleLipAt N X d R →
        Tendsto (fun v : Fin 4 → ℝ =>
          (N.momentBound (tupleLength X) (d / 2) (R + 1)).toReal *
            shiftedSharpNormSum N X v) (𝓝 0) (𝓝 0)) :
    ∀ (Ξ : FormalSpan) (v : ℕ → Fin 4 → ℝ), Tendsto v atTop (𝓝 0) →
      Tendsto (fun j => realSpanLift (pairedValue K ρ ν j) (pushSpan (translate (v j)) Ξ))
        atTop (𝓝 (realSpanLift σ Ξ)) := by
  intro Ξ v hv
  induction Ξ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simpa only [map_add] using ha.add hb
  | single Y c =>
    have hY : Finsupp.single Y c = c • basisVec Y := by simp [basisVec]
    rw [hY]
    simp only [map_smul, smul_eq_mul]
    refine Tendsto.const_mul c ?_
    obtain ⟨X, rfl⟩ := exists_listOf_eq (s := s) Y
    simp only [realSpanLift_pushSpan_translate, realSpanLift_basisVec]
    exact (Complex.continuous_ofReal.tendsto _).comp
      (tendsto_pairedValue_translateSep hlim hEq hTend X hv)
theorem centredProductLinear_basisVec_listOf (j : ℕ) (X : FinTuple s)
    (U : InfiniteLattice.GaugeField (meshSize s.L (K j : ℤ))) :
    centredProductLinear s.L (K j) (ν j) (basisVec (listOf X)) U =
      ((StateLimits.centeredProduct (K j) (ν j) X U : ℝ) : ℂ) := by
  have h := centredProductLinear_basisVec s.L (K j) (ν j)
    (Continuum.SeparatedFourTuples.sepTupleEquiv s X) U
  have hl : TupleLists.toList (Continuum.SeparatedFourTuples.sepTupleEquiv s X) = listOf X :=
    Subtype.ext rfl
  rw [hl] at h
  exact h
theorem ofReal_pairedValue_eq_integral (j : ℕ) (X : FinTuple s) :
    ((pairedValue K ρ ν j X : ℝ) : ℂ) =
      ∫ U, centredProductLinear s.L (K j) (ν j) (basisVec (listOf X)) U ∂ρ j := by
  simp only [centredProductLinear_basisVec_listOf]
  exact integral_complex_ofReal.symm
def withCutoff (s : Conventions.StandingParameters) (k : ℕ) (hk : 0 < k) :
    Conventions.StandingParameters :=
  { s with K := ⟨k, hk⟩ }
theorem meshSize_pos (hL : 2 ≤ s.L) (k : ℕ) : 0 < meshSize s.L (k : ℤ) := by
  have h : (0 : ℝ) < (s.L : ℝ) := by exact_mod_cast (by omega : 0 < s.L)
  exact zpow_pos h _
theorem isBoundedObservable_centredProductLinear (hL : 2 ≤ s.L) (hKpos : ∀ j, 0 < K j)
    (hν : ∀ j, IsProbabilityMeasure (ν j))
    (hCalc : CentredProductCalculus)
    (j : ℕ) (X : FinTuple s) :
    InfiniteLattice.IsBoundedObservable (centredProductLinear s.L (K j) (ν j)
      (basisVec (listOf X))) := by
  have ha := meshSize_pos hL (K j)
  set a := meshSize s.L (K j : ℤ) with ha'
  have hU : IsCompact (⋃ i, tsupport (entryFn X i)) :=
    isCompact_iUnion fun i => (isC1c_componentFn X i).2
  obtain ⟨B, hB⟩ := hU.exists_bound_of_continuousOn
    (f := fun x : Fin 4 → ℝ => x InfiniteLattice.timeAxis) (continuous_apply _).continuousOn
  let q : ℤ := ⌊(-B - a) / (a / 2)⌋
  have hq : (q : ℝ) * (a / 2) + a ≤ -B := by
    have h₁ : (q : ℝ) ≤ (-B - a) / (a / 2) := Int.floor_le _
    have h₂ := (le_div_iff₀ (half_pos ha)).1 h₁
    linarith
  have hc := (hCalc (withCutoff s (K j) (hKpos j)) (ν j) (hν j)).2.2.2.2
    ⟨(q : ℝ) * (a / 2), q, rfl⟩ a (half_lt_self ha) (basisVec (listOf X))
    (Submodule.subset_span ⟨⟨listOf X, fun f hf => ?_⟩, rfl⟩)
  · exact hc.1
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    intro x hx
    have h₁ := hB x (Set.mem_iUnion.2 ⟨i, hx⟩)
    have h₂ := (abs_le.1 h₁).1
    change (q : ℝ) * (a / 2) + a ≤ x InfiniteLattice.timeAxis
    linarith
theorem pairedValue_translateSep_site (hL : 2 ≤ s.L) (hKpos : ∀ j, 0 < K j)
    (hν : ∀ j, IsProbabilityMeasure (ν j))
    (hρi : ∀ j (v : InfiniteLattice.LatticePoint (meshSize s.L (K j : ℤ))),
      InfiniteLattice.IsSymmetricUnder (ρ j) (InfiniteLattice.shift v))
    (hνi : ∀ j (v : InfiniteLattice.LatticePoint (meshSize s.L (K j : ℤ))),
      InfiniteLattice.IsSymmetricUnder (ν j) (InfiniteLattice.shift v))
    (hCalc : CentredProductCalculus)
    (j : ℕ) (w : InfiniteLattice.LatticePoint (meshSize s.L (K j : ℤ))) (X : FinTuple s) :
    pairedValue K ρ ν j (translateSep w.1 X) = pairedValue K ρ ν j X := by
  apply Complex.ofReal_injective
  have hc₀ := (hCalc (withCutoff s (K j) (hKpos j)) (ν j) (hν j)).2.2.2.1
    (InfiniteLattice.shift w) (hνi j w) (basisVec (listOf X))
  have hact : pushSpan (InfiniteLattice.shift w).toFun (basisVec (listOf X)) =
      basisVec (listOf (translateSep w.1 X)) := by
    rw [listOf_translateSep, pushSpan, linearExtend_basisVec]
    rfl
  have hc : (InfiniteLattice.shift w).actOn
      (centredProductLinear s.L (K j) (ν j) (basisVec (listOf X))) =
      centredProductLinear s.L (K j) (ν j) (basisVec (listOf (translateSep w.1 X))) :=
    hc₀.trans (congrArg (centredProductLinear s.L (K j) (ν j)) hact)
  rw [ofReal_pairedValue_eq_integral, ofReal_pairedValue_eq_integral, ← hc]
  exact hρi j w _ (isBoundedObservable_centredProductLinear hL hKpos hν hCalc j X)
theorem exists_latticePoints_tendsto (hL : 2 ≤ s.L) (hK : Tendsto K atTop atTop) (y : Fin 4 → ℝ) :
    ∃ w : ∀ j, InfiniteLattice.LatticePoint (meshSize s.L (K j : ℤ)),
      Tendsto (fun j => (w j).1 - y) atTop (𝓝 0) := by
  have hL' : (1 : ℝ) < (s.L : ℝ) := by exact_mod_cast (by omega : 1 < s.L)
  have hspacing : Tendsto (fun j => meshSize s.L (K j : ℤ)) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun k : ℕ => ((s.L : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hL')
    refine (h₁.comp hK).congr fun j => ?_
    simp [meshSize, zpow_neg]
  refine ⟨fun j => ⟨fun μ => (round (y μ / meshSize s.L (K j : ℤ)) : ℝ) *
      meshSize s.L (K j : ℤ),
    fun μ => round (y μ / meshSize s.L (K j : ℤ)), fun μ => rfl⟩, ?_⟩
  refine tendsto_pi_nhds.2 fun μ => ?_
  have hlim : Tendsto (fun j => meshSize s.L (K j : ℤ) / 2) atTop (𝓝 0) := by
    simpa using hspacing.div_const 2
  refine squeeze_zero_norm (fun j => ?_) hlim
  have ha := meshSize_pos hL (K j)
  set a := meshSize s.L (K j : ℤ)
  have h₁ := abs_sub_round (y μ / a)
  have h₂ : ((round (y μ / a) : ℝ) * a - y μ) = -((y μ / a - round (y μ / a)) * a) := by
    field_simp
    ring
  change ‖(round (y μ / a) : ℝ) * a - y μ‖ ≤ a / 2
  rw [Real.norm_eq_abs, h₂, abs_neg, abs_mul, abs_of_pos ha]
  nlinarith
theorem translateSep_translateSep (w y : Fin 4 → ℝ) (X : FinTuple s) :
    translateSep (w - y) (translateSep y X) = translateSep w X := by
  refine Continuum.SeparatedFourTuples.sepTuple_ext rfl fun i => ?_
  refine funext fun (x : Fin 4 → ℝ) => ?_
  have h : (x - (w - y)) - y = x - w := by abel
  change tupleComponents X i ((x - (w - y)) - y) = tupleComponents X i (x - w)
  rw [h]
theorem translate_invariant_of
    (hL : 2 ≤ s.L) (hK : Tendsto K atTop atTop) (hKpos : ∀ j, 0 < K j)
    (_hρ : ∀ j, IsProbabilityMeasure (ρ j)) (hν : ∀ j, IsProbabilityMeasure (ν j))
    (hρi : ∀ j (v : InfiniteLattice.LatticePoint (meshSize s.L (K j : ℤ))),
      InfiniteLattice.IsSymmetricUnder (ρ j) (InfiniteLattice.shift v))
    (hνi : ∀ j (v : InfiniteLattice.LatticePoint (meshSize s.L (K j : ℤ))),
      InfiniteLattice.IsSymmetricUnder (ν j) (InfiniteLattice.shift v))
    (hCalc : CentredProductCalculus)
    (hlim : StateLimits.IsPointwiseLimit K ρ ν σ)
    (hMov : ∀ (Ξ : FormalSpan) (v : ℕ → Fin 4 → ℝ), Tendsto v atTop (𝓝 0) →
      Tendsto (fun j => realSpanLift (pairedValue K ρ ν j) (pushSpan (translate (v j)) Ξ))
        atTop (𝓝 (realSpanLift σ Ξ))) :
    ∀ (y : Fin 4 → ℝ) (Ξ : FormalSpan),
      realSpanLift σ (pushSpan (translate y) Ξ) = realSpanLift σ Ξ := by
  intro y Ξ
  induction Ξ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single Y c =>
    have hY : Finsupp.single Y c = c • basisVec Y := by simp [basisVec]
    rw [hY]
    simp only [map_smul, smul_eq_mul]
    congr 1
    obtain ⟨X, rfl⟩ := exists_listOf_eq (s := s) Y
    rw [realSpanLift_pushSpan_translate, realSpanLift_basisVec]
    congr 1
    obtain ⟨w, hw⟩ := exists_latticePoints_tendsto hL hK y
    have h₁ := hMov (basisVec (listOf (translateSep y X)))
      (fun j => (w j).1 - y) hw
    simp only [realSpanLift_pushSpan_translate, realSpanLift_basisVec,
      translateSep_translateSep,
      pairedValue_translateSep_site hL hKpos hν hρi hνi hCalc] at h₁
    have h₂ := (Complex.continuous_re.tendsto _).comp h₁
    simp only [Function.comp_def, Complex.ofReal_re] at h₂
    exact tendsto_nhds_unique h₂ (hlim X)
theorem reflectionForm_cauchySchwarz_triangle {σ' : TupleFunctional}
    (h : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm σ')) :
    (∀ F F' : PositiveSpan, ‖ReflectionPositivity.TupleForm.reflectionForm σ' F F'‖ ≤
      spanClassNorm σ' F * spanClassNorm σ' F') ∧
    (∀ F F' : PositiveSpan, spanClassNorm σ' (F + F') ≤
      spanClassNorm σ' F + spanClassNorm σ' F') := by
  have hnn : ∀ F, 0 ≤ (ReflectionPositivity.TupleForm.reflectionForm σ' F F).re :=
    fun F => (Complex.le_def.mp (h.nonneg F)).1
  have hcs : ∀ F F' : PositiveSpan, ‖ReflectionPositivity.TupleForm.reflectionForm σ' F F'‖ ^ 2 ≤
      (ReflectionPositivity.TupleForm.reflectionForm σ' F F).re *
        (ReflectionPositivity.TupleForm.reflectionForm σ' F' F').re := by
    intro F F'
    let _ : PreInnerProductSpace.Core ℂ PositiveSpan := HilbertSpaceBasics.toPreInnerCore h
    have key := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) F F'
    have hy := h.isHermitianForm F F'
    have e : ‖ReflectionPositivity.TupleForm.reflectionForm σ' F' F‖ =
        ‖ReflectionPositivity.TupleForm.reflectionForm σ' F F'‖ := by
      rw [hy, RCLike.norm_conj]
    have hcancelled' : ‖ReflectionPositivity.TupleForm.reflectionForm σ' F F'‖ *
        ‖ReflectionPositivity.TupleForm.reflectionForm σ' F' F‖ ≤
        (ReflectionPositivity.TupleForm.reflectionForm σ' F F).re *
          (ReflectionPositivity.TupleForm.reflectionForm σ' F' F').re := key
    rw [e] at hcancelled'
    rw [sq]
    exact hcancelled'
  have hcs' : ∀ F F' : PositiveSpan, ‖ReflectionPositivity.TupleForm.reflectionForm σ' F F'‖ ≤
      spanClassNorm σ' F * spanClassNorm σ' F' := by
    intro F F'
    unfold spanClassNorm
    rw [← Real.sqrt_mul (hnn F)]
    exact Real.le_sqrt_of_sq_le (hcs F F')
  refine ⟨hcs', fun F F' => ?_⟩
  have hexp : (ReflectionPositivity.TupleForm.reflectionForm σ' (F + F') (F + F')).re =
      (ReflectionPositivity.TupleForm.reflectionForm σ' F F).re +
        (ReflectionPositivity.TupleForm.reflectionForm σ' F' F').re +
        2 * (ReflectionPositivity.TupleForm.reflectionForm σ' F F').re := by
    rw [h.add_left, h.add_right, h.add_right, h.isHermitianForm F F']
    simp only [Complex.add_re, Complex.conj_re]
    ring
  have hre : (ReflectionPositivity.TupleForm.reflectionForm σ' F F').re ≤
      spanClassNorm σ' F * spanClassNorm σ' F' :=
    (Complex.re_le_norm _).trans (hcs' F F')
  have hF : spanClassNorm σ' F ^ 2 = (ReflectionPositivity.TupleForm.reflectionForm σ' F F).re :=
    Real.sq_sqrt (hnn F)
  have hF' : spanClassNorm σ' F' ^ 2 =
      (ReflectionPositivity.TupleForm.reflectionForm σ' F' F').re := Real.sq_sqrt (hnn F')
  have h0 : 0 ≤ spanClassNorm σ' F + spanClassNorm σ' F' :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine Real.sqrt_le_iff.2 ⟨h0, ?_⟩
  rw [hexp, add_sq, hF, hF']
  nlinarith [hre]
open ReflectionPositivity.TupleForm (reflectionForm reflectedCorrelation reflectConj
  isSesquilinear_reflectionForm)
theorem shiftedSpan_val (hTr : SeparatedTuples.PositiveTranslates.Statement)
    (F : PositiveSpan) {v : InfiniteLattice.AmbientSpace} (hv : 0 ≤ v TimeAxis.timeIdx) :
    (ReflectionPositivity.FormProperties.shiftedSpan v F).1 = pushSpan (translate v) F.1 := by
  unfold ReflectionPositivity.FormProperties.shiftedSpan
  rw [dif_pos (hTr F F v hv).1]
theorem isTranslateInvariant_toTupleFunctional (hσ : IsTupleFunctional σ)
    (hinv : ∀ (y : Fin 4 → ℝ) (Ξ : FormalSpan),
      realSpanLift σ (pushSpan (translate y) Ξ) = realSpanLift σ Ξ) :
    (toTupleFunctional σ hσ).IsTranslateInvariant := by
  intro v X
  have h := hinv v (basisVec X)
  rw [← R4TupleForms.spanExtension_toTupleFunctional σ hσ] at h
  have h₁ : pushSpan (translate v) (basisVec X) = basisVec (push (translate v) X) :=
    linearExtend_basisVec _ _
  rw [h₁] at h
  simp only [TupleFunctional.spanExtension, linearExtend_basisVec] at h
  exact_mod_cast h
theorem reflectedCorrelation_bounded {σ' : TupleFunctional} (F : PositiveSpan)
    (hB : ∀ X ∈ F.1.support, ∀ Y ∈ F.1.support, ∃ B : ℝ, ∀ v : InfiniteLattice.AmbientSpace,
      0 ≤ v TimeAxis.timeIdx →
        |σ' (SepTuple.juxt (push TimeAxis.timeReflection X) (push (translate v) Y))| ≤ B) :
    ∃ C : ℝ, ∀ v : InfiniteLattice.AmbientSpace, 0 ≤ v TimeAxis.timeIdx →
      ‖reflectedCorrelation σ' F v‖ ≤ C := by
  classical
  choose! B hB using hB
  set c : FormalSpan := F.1 with hc
  have hexp : ∀ Z : FormalSpan, Z = ∑ X ∈ Z.support, Z X • basisVec X := by
    intro Z
    conv_lhs => rw [← Finsupp.sum_single Z]
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun X _ => ?_
    ext Y
    by_cases h : X = Y <;> simp [basisVec, h]
  refine ⟨∑ X ∈ c.support, ∑ Y ∈ c.support, ‖c X‖ * ‖c Y‖ * B X Y, fun v hv => ?_⟩
  have hrefl : reflectConj F =
      ∑ X ∈ c.support, (starRingEnd ℂ) (c X) • basisVec (push TimeAxis.timeReflection X) := by
    unfold reflectConj
    rw [← hc]
    conv_lhs => rw [hexp c]
    rw [conjugation_sum, map_sum]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [map_smul]
    congr 1
    exact linearExtend_basisVec _ _
  have hact : pushSpan (translate v) c =
      ∑ Y ∈ c.support, c Y • basisVec (push (translate v) Y) := by
    conv_lhs => rw [hexp c]
    rw [map_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [map_smul]
    congr 1
    exact linearExtend_basisVec _ _
  unfold reflectedCorrelation
  rw [← hc, hrefl, hact, formalMul_sum, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun X hX => ?_)
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun Y hY => ?_)
  rw [map_smul, smul_eq_mul, norm_mul, norm_mul, RCLike.norm_conj]
  simp only [TupleFunctional.spanExtension, linearExtend_basisVec, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB X hX Y hY v hv) (by positivity)
theorem spanClassNorm_shift_le {σ' : TupleFunctional}
    (hP : HilbertSpaceBasics.IsPosSemidef (reflectionForm σ'))
    (hProp : ReflectionPositivity.FormProperties.Assertion)
    (hTr : SeparatedTuples.PositiveTranslates.Statement)
    (hTI : σ'.IsTranslateInvariant) (F : PositiveSpan)
    (hC : ∃ C : ℝ, ∀ v : InfiniteLattice.AmbientSpace, 0 ≤ v TimeAxis.timeIdx →
      ‖reflectedCorrelation σ' F v‖ ≤ C) :
    ∀ (u : ℝ), 0 ≤ u → ∃ G : PositiveSpan,
      G.1 = pushSpan (translate (u • timeUnitVec)) F.1 ∧
        spanClassNorm σ' G ≤ spanClassNorm σ' F := by
  obtain ⟨C, hC⟩ := hC
  have hnn : ∀ F, 0 ≤ (reflectionForm σ' F F).re :=
    fun F => (Complex.le_def.mp (hP.nonneg F)).1
  have htime : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (t • timeUnitVec : InfiniteLattice.AmbientSpace) TimeAxis.timeIdx := by
    intro t ht
    simpa [timeUnitVec, ChessboardTori.coordVec, TimeAxis.timeIdx] using ht
  set T : ℝ → PositiveSpan :=
    fun t => ReflectionPositivity.FormProperties.shiftedSpan (t • timeUnitVec) F with hT
  have hTval : ∀ t, 0 ≤ t → (T t).1 = pushSpan (translate (t • timeUnitVec)) F.1 :=
    fun t ht => shiftedSpan_val hTr F (htime t ht)
  set a : ℝ → ℝ := fun t => spanClassNorm σ' (T t) with ha
  have ha0 : ∀ t, 0 ≤ a t := fun t => Real.sqrt_nonneg _
  have hkey : ∀ t, 0 ≤ t → reflectionForm σ' (T t) (T t) = reflectionForm σ' F (T (2 * t)) := by
    intro t ht
    have h := ((hProp σ' F F).2.2.1 hTI).1 t ht
    have h₂ := h.2
    have h₃ : reflectedCorrelation σ' F ((2 * t) • PeriodicLattice.coordVec TimeAxis.timeIdx) =
          reflectionForm σ' F (T (2 * t)) := by
      unfold reflectedCorrelation reflectionForm
      rw [hTval (2 * t) (by positivity)]
      rfl
    exact h₂.symm.trans h₃
  have hsq : ∀ t, 0 ≤ t → a t ^ 2 ≤ spanClassNorm σ' F * a (2 * t) := by
    intro t ht
    have h₁ : a t ^ 2 = (reflectionForm σ' (T t) (T t)).re := Real.sq_sqrt (hnn _)
    rw [h₁, hkey t ht]
    exact (Complex.re_le_norm _).trans ((reflectionForm_cauchySchwarz_triangle hP).1 F (T (2 * t)))
  have hbdd : ∀ t, 0 ≤ t → a t ^ 2 ≤ C := by
    intro t ht
    have h₁ : a t ^ 2 = (reflectionForm σ' (T t) (T t)).re := Real.sq_sqrt (hnn _)
    rw [h₁, hkey t ht]
    refine (Complex.re_le_norm _).trans ?_
    have h₃ : reflectedCorrelation σ' F ((2 * t) • timeUnitVec) =
          reflectionForm σ' F (T (2 * t)) := by
      unfold reflectedCorrelation reflectionForm
      rw [hTval (2 * t) (by positivity)]
    rw [← h₃]
    exact hC _ (htime _ (by positivity))
  have hbound : BddAbove (a '' Set.Ici 0) := by
    refine ⟨Real.sqrt (max C 0), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    refine Real.le_sqrt_of_sq_le ((hbdd t ht).trans (le_max_left _ _))
  set S := sSup (a '' Set.Ici 0) with hS
  have hle : ∀ t, 0 ≤ t → a t ≤ S := fun t ht => le_csSup hbound ⟨t, ht, rfl⟩
  have hS0 : 0 ≤ S := (ha0 0).trans (hle 0 le_rfl)
  have hF0 : 0 ≤ spanClassNorm σ' F := Real.sqrt_nonneg _
  have hroot : ∀ t, 0 ≤ t → a t ≤ Real.sqrt (spanClassNorm σ' F * S) := fun t ht =>
    Real.le_sqrt_of_sq_le ((hsq t ht).trans
      (mul_le_mul_of_nonneg_left (hle (2 * t) (by positivity)) hF0))
  have hSroot : S ≤ Real.sqrt (spanClassNorm σ' F * S) :=
    csSup_le ⟨a 0, 0, Set.mem_Ici.2 le_rfl, rfl⟩ (by
      rintro _ ⟨t, ht, rfl⟩
      exact hroot t ht)
  have hSle : S ≤ spanClassNorm σ' F := by
    rcases hS0.eq_or_lt with h0 | hpos
    · rw [← h0]
      exact hF0
    · have h₁ : S ^ 2 ≤ spanClassNorm σ' F * S := by
        have := Real.sq_sqrt (mul_nonneg hF0 hS0)
        nlinarith [Real.sqrt_nonneg (spanClassNorm σ' F * S)]
      nlinarith
  intro u hu
  exact ⟨T u, hTval u hu, (hle u hu).trans hSle⟩
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_sub_comm (a b : Fin 4 → ℝ) :
    euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem abs_coord_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
def ListLipAt (d R : ℝ) (l : List RealValued) : Prop :=
  (∀ f ∈ l, IsLipschitzFor euclidDistR4 f ∧ ∃ x, tsupport f ⊆ closedBallR4 x R) ∧
  l.Pairwise fun f h => ∀ a ∈ tsupport f, ∀ b ∈ tsupport h, d ≤ euclidNormVec (a - b)
theorem tupleLipAt_iff_listLipAt {N : FreeMomentConstants} {d R : ℝ} (hR : 0 < R)
    (X : SeparatedTuples.SepTuple) :
    TupleLipAt N ((finTupleEquiv s).symm X) d R ↔ ListLipAt d R X.1 := by
  set Y := LipschitzClasses.params s N.M N.one_le_M with hY
  have hde : ∀ x y : Fin 4 → ℝ, quotDist Y .euclidean x y = euclidNormVec (x - y) :=
    quotDist_euclidean_eq Y
  have hs : ∀ f : RealValued, supportQ Y .euclidean f = tsupport f :=
    fun f => SeparatedTuplesR4.closureWrt_euclid_eq_closure hde _
  have hlip : ∀ f : RealValued, IsLipschitzQ Y .euclidean f ↔ IsLipschitzFor euclidDistR4 f := by
    intro f
    have h : quotDist Y .euclidean = euclidDistR4 := funext₂ hde
    unfold IsLipschitzQ
    rw [h]
    exact Iff.rfl
  have hball : ∀ x : Fin 4 → ℝ, closedBallAbout Y .euclidean x R = closedBallR4 x R := by
    intro x
    refine Set.ext fun y => ?_
    exact iff_of_eq (congrArg (· ≤ R) (hde y x))
  have hdist : ∀ A B : Set (Fin 4 → ℝ),
      ENNReal.ofReal d ≤ setInfDist Y .euclidean A B ↔
      ∀ a ∈ A, ∀ b ∈ B, d ≤ euclidNormVec (a - b) := by
    intro A B
    unfold setInfDist
    simp only [le_iInf_iff]
    refine forall₂_congr fun a _ => forall₂_congr fun b _ => ?_
    refine Iff.trans ?_ (ENNReal.ofReal_le_ofReal_iff (euclidNormVec_nonneg _))
    exact iff_of_eq (congrArg (fun t => ENNReal.ofReal d ≤ ENNReal.ofReal t) (hde a b))
  constructor
  · rintro ⟨hl, hb, hp⟩
    refine ⟨fun f hf => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := List.get_of_mem hf
      refine ⟨(hlip _).1 (hl i), ?_⟩
      obtain ⟨B, ⟨-, x, rfl⟩, hB⟩ := hb i
      refine ⟨x, fun y hy => ?_⟩
      have h₁ : y ∈ closedBallAbout Y .euclidean x R := hB ((hs (X.1.get i)).ge hy)
      exact (hball x).le h₁
    · refine List.pairwise_iff_get.2 fun i k hik => ?_
      have h := hp i k hik.ne
      intro a ha b hb'
      have h' := (hdist _ _).1 h
      exact h' a ((hs _).ge ha) b ((hs _).ge hb')
  · rintro ⟨hl, hp⟩
    refine ⟨fun i => (hlip _).2 (hl _ (List.get_mem _ _)).1, fun i => ?_, fun i k hik => ?_⟩
    · obtain ⟨x, hx⟩ := (hl _ (List.get_mem X.1 i)).2
      refine ⟨_, ⟨hR, x, rfl⟩, fun y hy => ?_⟩
      exact (hball x).ge (hx ((hs (X.1.get i)).le hy))
    · have hget := List.pairwise_iff_get.1 hp
      refine (hdist _ _).2 fun a ha b hb' => ?_
      have ha' : a ∈ tsupport (X.1.get i) := (hs _).le ha
      have hb'' : b ∈ tsupport (X.1.get k) := (hs _).le hb'
      rcases lt_or_gt_of_ne hik with h | h
      · exact hget i k h a ha' b hb''
      · rw [euclidNormVec_sub_comm]
        exact hget k i h b hb'' a ha'
theorem exists_listLipAt {N : FreeMomentConstants}
    (hread : ∀ X : FinTuple s, 1 ≤ tupleLength X →
      ∃ d R : ℝ, 0 < d ∧ 0 < R ∧ TupleLipAt N X d R) (X : SeparatedTuples.SepTuple) :
    ∃ d R : ℝ, 0 < d ∧ 0 < R ∧ ListLipAt d R X.1 := by
  rcases hX : X.1 with _ | ⟨f, l⟩
  · exact ⟨1, 1, one_pos, one_pos, by simp [ListLipAt]⟩
  · obtain ⟨d, R, hd, hR, h⟩ := hread ((finTupleEquiv s).symm X) (by
      change 1 ≤ X.1.length
      simp [hX])
    refine ⟨d, R, hd, hR, ?_⟩
    rw [← hX]
    exact (tupleLipAt_iff_listLipAt hR X).1 h
theorem listLipAt_mono {d d' R R' : ℝ} (hd : d' ≤ d) (hR : R ≤ R') {l : List RealValued}
    (h : ListLipAt d R l) : ListLipAt d' R' l := by
  refine ⟨fun f hf => ⟨(h.1 f hf).1, ?_⟩, h.2.imp fun hp a ha b hb => hd.trans (hp a ha b hb)⟩
  obtain ⟨x, hx⟩ := (h.1 f hf).2
  exact ⟨x, hx.trans fun y (hy : _ ≤ R) => hy.trans hR⟩
theorem sharpNormR4_comp_isometry (e : InfiniteLattice.AmbientSpace ≃ InfiniteLattice.AmbientSpace)
    (he : ∀ x y, euclidNormVec (e x - e y) = euclidNormVec (x - y))
    (M : ℝ) (f : RealValued) :
    sharpNormR4 M (f ∘ e.symm) = sharpNormR4 M f := by
  unfold sharpNormR4 uniformNorm lipConstR4 bestLipschitzConstant
  have h₁ : (⨆ x, ‖(f ∘ e.symm) x‖) = ⨆ x, ‖f x‖ := e.symm.iSup_comp (g := fun x => ‖f x‖)
  have h₂ : {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖(f ∘ e.symm) x - (f ∘ e.symm) y‖ ≤
      C * euclidDistR4 x y} =
      {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y} := by
    ext C
    refine and_congr_right fun _ => ⟨fun h x y => ?_, fun h x y => ?_⟩
    · have := h (e x) (e y)
      simpa [euclidDistR4, he] using this
    · have := h (e.symm x) (e.symm y)
      have h₃ := he (e.symm x) (e.symm y)
      simp only [Equiv.apply_symm_apply] at h₃
      simpa [euclidDistR4, h₃] using this
  rw [h₁, h₂]
theorem listLipAt_map (e : InfiniteLattice.AmbientSpace ≃ₜ InfiniteLattice.AmbientSpace)
    (he : ∀ x y, euclidNormVec (e x - e y) = euclidNormVec (x - y))
    {d R : ℝ} {l : List RealValued} (h : ListLipAt d R l) :
    ListLipAt d R (l.map fun f => f ∘ e.symm) := by
  have hsymm : ∀ x y, euclidNormVec (e.symm x - e.symm y) = euclidNormVec (x - y) := fun x y => by
    have h₃ := he (e.symm x) (e.symm y)
    simp only [Homeomorph.apply_symm_apply] at h₃
    exact h₃.symm
  have hsupp : ∀ f : RealValued, tsupport (f ∘ e.symm) = e.symm ⁻¹' tsupport f :=
    fun f => Continuum.SeparatedFourTuples.tsupport_comp_homeo e.symm f
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    obtain ⟨⟨C, hC, hL⟩, x, hx⟩ := h.1 f hf
    refine ⟨⟨C, hC, fun y z => ?_⟩, e x, ?_⟩
    · have := hL (e.symm y) (e.symm z)
      simpa [euclidDistR4, hsymm] using this
    · intro y hy
      rw [hsupp] at hy
      have hb := hx hy
      change euclidNormVec (y - e x) ≤ R
      have hb' : euclidNormVec (e.symm y - x) ≤ R := hb
      have h₃ := he (e.symm y) x
      simp only [Homeomorph.apply_symm_apply] at h₃
      rw [h₃]
      exact hb'
  · refine List.pairwise_map.2 (h.2.imp fun hp a ha b hb => ?_)
    rw [hsupp] at ha hb
    have := hp _ ha _ hb
    rwa [hsymm] at this
def timeReflectionHomeo : InfiniteLattice.AmbientSpace ≃ₜ InfiniteLattice.AmbientSpace where
  toFun := TimeAxis.timeReflection
  invFun := TimeAxis.timeReflection
  left_inv x := by
    funext i
    fin_cases i <;> simp [TimeAxis.timeReflection]
  right_inv x := by
    funext i
    fin_cases i <;> simp [TimeAxis.timeReflection]
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp only [TimeAxis.timeReflection] <;> fun_prop
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp only [TimeAxis.timeReflection] <;> fun_prop
theorem timeReflectionHomeo_apply (x : InfiniteLattice.AmbientSpace) :
    timeReflectionHomeo x = TimeAxis.timeReflection x := rfl
theorem timeReflectionHomeo_isometry (x y : InfiniteLattice.AmbientSpace) :
    euclidNormVec (timeReflectionHomeo x - timeReflectionHomeo y) = euclidNormVec (x - y) := by
  unfold euclidNormVec
  simp only [timeReflectionHomeo_apply, TimeAxis.timeReflection, Fin.sum_univ_four, Pi.sub_apply]
  simp
  ring_nf
def shiftHomeo (v : InfiniteLattice.AmbientSpace) :
    InfiniteLattice.AmbientSpace ≃ₜ InfiniteLattice.AmbientSpace :=
  Homeomorph.addRight v
theorem shiftHomeo_isometry (v x y : InfiniteLattice.AmbientSpace) :
    euclidNormVec (shiftHomeo v x - shiftHomeo v y) = euclidNormVec (x - y) := by
  have : shiftHomeo v x - shiftHomeo v y = x - y := by
    simp [shiftHomeo]
  rw [this]
theorem invMap_homeo_eq (e : InfiniteLattice.AmbientSpace ≃ₜ InfiniteLattice.AmbientSpace) :
    SeparatedTuples.invMap e = e.symm := by
  funext x
  have h := Function.leftInverse_invFun e.injective (e.symm x)
  simpa [SeparatedTuples.invMap] using h
theorem push_val_of_isometry (s : Conventions.StandingParameters)
    (e : InfiniteLattice.AmbientSpace ≃ₜ InfiniteLattice.AmbientSpace)
    (he : ∀ x y, euclidNormVec (e x - e y) = euclidNormVec (x - y))
    (X : SeparatedTuples.SepTuple) :
    (push e X).1 = X.1.map fun f => f ∘ e.symm := by
  have hl : pushList e X.1 = X.1.map fun f => f ∘ e.symm := by
    simp only [pushList, invMap_homeo_eq]
  have hsep : IsDisjointlySupported (pushList e X.1) := by
    have hm : (X.1.get : Fin X.1.length → Pt s .euclidean → ℝ) ∈
        separatedTuples s .euclidean X.1.length := ((finTupleEquiv s).symm X).2
    have hmem := Continuum.SeparatedFourTuples.transportTuple_mem (s := s) ⟨e.toEquiv, he⟩ hm
    have h₁ := (R4TupleForms.mem_separatedTuples_iff_ofFn _).1 hmem
    let e' : Pt s .euclidean ≃ Pt s .euclidean := e.toEquiv
    let g : Fin X.1.length → Pt s .euclidean → ℝ := X.1.get
    have h₂ : List.ofFn (transportTuple e' g) = pushList e X.1 := by
      rw [R4TupleForms.ofFn_transportTuple]
      exact congrArg (pushList e) (List.ofFn_get X.1)
    exact Eq.mp (congrArg IsDisjointlySupported h₂) h₁
  unfold push
  rw [dif_pos hsep]
  exact hl
theorem exists_time_floor {Q : Set InfiniteLattice.AmbientSpace} (hQ : IsCompact Q)
    (h : ∀ x ∈ Q, 0 < x TimeAxis.timeIdx) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, δ ≤ x TimeAxis.timeIdx := by
  rcases Q.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨m, hm, hmin⟩ := hQ.exists_isMinOn hne (continuous_apply TimeAxis.timeIdx).continuousOn
    exact ⟨m TimeAxis.timeIdx, h m hm, fun x hx => hmin hx⟩
theorem exists_time_floor_tuple {X : SeparatedTuples.SepTuple}
    (hX : X ∈ supportedIn TimeAxis.upperHalfSpace) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ X.1, ∀ x ∈ tsupport f, δ ≤ x TimeAxis.timeIdx := by
  have hc : IsCompact (⋃ f ∈ X.1, tsupport f) :=
    (List.finite_toSet X.1).isCompact_biUnion fun f hf => (X.2.1 f hf).2
  obtain ⟨δ, hδ, h⟩ := exists_time_floor hc (by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨f, hf, hxf⟩ := hx
    exact hX f hf hxf)
  exact ⟨δ, hδ, fun f hf x hx => h x (Set.mem_biUnion hf hx)⟩
theorem reflected_pair_bounded (hσ : IsTupleFunctional σ)
    (hread : ∀ X : FinTuple s, 1 ≤ tupleLength X →
      ∃ d R : ℝ, 0 < d ∧ 0 < R ∧ TupleLipAt N X d R)
    (hle : ∀ (X : FinTuple s), 1 ≤ tupleLength X → ∀ d R : ℝ, 0 < d → 0 < R →
      TupleLipAt N X d R →
      |σ X| ≤ (N.momentBound (tupleLength X) d R).toReal * sharpNormProd N X)
    {X Y : SeparatedTuples.SepTuple} (hX : X ∈ supportedIn TimeAxis.upperHalfSpace)
    (hY : Y ∈ supportedIn TimeAxis.upperHalfSpace) :
    ∃ B : ℝ, ∀ v : InfiniteLattice.AmbientSpace, 0 ≤ v TimeAxis.timeIdx →
      |toTupleFunctional σ hσ
        (SepTuple.juxt (push TimeAxis.timeReflection X) (push (translate v) Y))| ≤ B := by
  obtain ⟨dX, RX, hdX, hRX, hrX⟩ := exists_listLipAt hread X
  obtain ⟨dY, RY, hdY, hRY, hrY⟩ := exists_listLipAt hread Y
  obtain ⟨δX, hδX, hX'⟩ := exists_time_floor_tuple hX
  obtain ⟨δY, hδY, hY'⟩ := exists_time_floor_tuple hY
  set d := min (min dX dY) (δX + δY) with hd
  set R := max RX RY with hR
  have hd0 : 0 < d := lt_min (lt_min hdX hdY) (add_pos hδX hδY)
  have hR0 : 0 < R := lt_of_lt_of_le hRX (le_max_left _ _)
  set P : ℝ := (X.1.map (sharpNormR4 N.M)).prod * (Y.1.map (sharpNormR4 N.M)).prod with hP
  refine ⟨max 1 ((N.momentBound (X.1.length + Y.1.length) d R).toReal * P), fun v hv => ?_⟩
  have hlX : (push TimeAxis.timeReflection X).1 = X.1.map fun f => f ∘ timeReflectionHomeo.symm :=
    push_val_of_isometry s timeReflectionHomeo timeReflectionHomeo_isometry X
  have hlY : (push (translate v) Y).1 = Y.1.map fun f => f ∘ (shiftHomeo v).symm :=
    push_val_of_isometry s (shiftHomeo v) (shiftHomeo_isometry v) Y
  have hcross : ∀ f ∈ X.1, ∀ g ∈ Y.1, ∀ a ∈ tsupport (f ∘ timeReflectionHomeo.symm),
      ∀ b ∈ tsupport (g ∘ (shiftHomeo v).symm),
        δX + δY ≤ euclidNormVec (a - b) := by
    intro f hf g hg a ha b hb
    rw [Continuum.SeparatedFourTuples.tsupport_comp_homeo] at ha hb
    have h₁ := hX' f hf _ ha
    have h₂ := hY' g hg _ hb
    have h₃ : (timeReflectionHomeo.symm a) TimeAxis.timeIdx = -a TimeAxis.timeIdx := rfl
    have h₄ : ((shiftHomeo v).symm b) TimeAxis.timeIdx =
        b TimeAxis.timeIdx - v TimeAxis.timeIdx := by
      change (b + -v) TimeAxis.timeIdx = _
      simp [sub_eq_add_neg]
    rw [h₃] at h₁
    rw [h₄] at h₂
    have h₅ := abs_coord_le_euclidNormVec (a - b) TimeAxis.timeIdx
    have h₆ : (a - b) TimeAxis.timeIdx = a TimeAxis.timeIdx - b TimeAxis.timeIdx := rfl
    rw [h₆] at h₅
    have h₇ := neg_abs_le (a TimeAxis.timeIdx - b TimeAxis.timeIdx)
    linarith
  have hdef : SepTuple.Composable (push TimeAxis.timeReflection X) (push (translate v) Y) := by
    intro f' hf' g' hg'
    rw [hlX] at hf'
    rw [hlY] at hg'
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hf'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    refine Set.disjoint_left.2 fun a ha hb => ?_
    have h := hcross f hf g hg a ha a hb
    have h0 : euclidNormVec (a - a) = 0 := by
      simp [euclidNormVec]
    rw [h0] at h
    linarith
  set Z := SepTuple.juxt (push TimeAxis.timeReflection X) (push (translate v) Y) with hZ
  have hZ1 : Z.1 = (X.1.map fun f => f ∘ timeReflectionHomeo.symm) ++
      (Y.1.map fun f => f ∘ (shiftHomeo v).symm) := by
    rw [hZ, SepTuple.juxt_val hdef, hlX, hlY]
  have hread' : ListLipAt d R Z.1 := by
    have h₁ := listLipAt_map timeReflectionHomeo timeReflectionHomeo_isometry
      (listLipAt_mono (d' := d) ((min_le_left _ _).trans (min_le_left _ _))
        (le_max_left RX RY) hrX)
    have h₂ := listLipAt_map (shiftHomeo v) (shiftHomeo_isometry v)
      (listLipAt_mono (d' := d) ((min_le_left _ _).trans (min_le_right _ _))
        (le_max_right RX RY) hrY)
    rw [hZ1]
    refine ⟨fun f hf => ?_, List.pairwise_append.2 ⟨h₁.2, h₂.2, ?_⟩⟩
    · rcases List.mem_append.1 hf with hf | hf
      · exact h₁.1 f hf
      · exact h₂.1 f hf
    · intro f' hf' g' hg' a ha b hb
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hf'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
      exact (min_le_right _ _).trans (hcross f hf g hg a ha b hb)
  rcases hlen : Z.1 with _ | ⟨z, l⟩
  · have hZe : Z = SepTuple.nil := Subtype.ext hlen
    rw [hZe, (toTupleFunctional σ hσ).map_nil]
    simp
  · have h₁ := hle ((finTupleEquiv s).symm Z) (by
      change 1 ≤ Z.1.length
      simp [hlen]) d R hd0 hR0 ((tupleLipAt_iff_listLipAt hR0 Z).2 hread')
    have hlength : tupleLength ((finTupleEquiv s).symm Z) = X.1.length + Y.1.length := by
      change Z.1.length = _
      simp [hZ1]
    have hprod : sharpNormProd N ((finTupleEquiv s).symm Z) = P := by
      have h₂ : sharpNormProd N ((finTupleEquiv s).symm Z) =
          (Z.1.map (sharpNormR4 N.M)).prod := by
        change ∏ i : Fin Z.1.length, sharpNormR4 N.M (Z.1.get i) = _
        exact Fin.prod_univ_fun_getElem Z.1 _
      rw [h₂, hZ1, List.map_append, List.prod_append, List.map_map, List.map_map, hP]
      congr 2
      · refine List.map_congr_left fun f _ => ?_
        exact sharpNormR4_comp_isometry timeReflectionHomeo.toEquiv timeReflectionHomeo_isometry
          N.M f
      · refine List.map_congr_left fun f _ => ?_
        exact sharpNormR4_comp_isometry (shiftHomeo v).toEquiv (shiftHomeo_isometry v) N.M f
    rw [hlength, hprod] at h₁
    exact h₁.trans (le_max_right _ _)
theorem contraction_of (hσ : IsTupleFunctional σ)
    (hP : HilbertSpaceBasics.IsPosSemidef (reflectionForm (toTupleFunctional σ hσ)))
    (hProp : ReflectionPositivity.FormProperties.Assertion)
    (hTr : SeparatedTuples.PositiveTranslates.Statement)
    (hinv : ∀ (y : Fin 4 → ℝ) (Ξ : FormalSpan),
      realSpanLift σ (pushSpan (translate y) Ξ) = realSpanLift σ Ξ)
    (hread : ∀ X : FinTuple s, 1 ≤ tupleLength X →
      ∃ d R : ℝ, 0 < d ∧ 0 < R ∧ TupleLipAt N X d R)
    (hle : ∀ (X : FinTuple s), 1 ≤ tupleLength X → ∀ d R : ℝ, 0 < d → 0 < R →
      TupleLipAt N X d R →
      |σ X| ≤ (N.momentBound (tupleLength X) d R).toReal * sharpNormProd N X) :
    ∀ (u : ℝ), 0 ≤ u → ∀ F : PositiveSpan, ∃ G : PositiveSpan,
      G.1 = pushSpan (translate (u • timeUnitVec)) F.1 ∧
        spanClassNorm (toTupleFunctional σ hσ) G ≤ spanClassNorm (toTupleFunctional σ hσ) F := by
  intro u hu F
  refine spanClassNorm_shift_le hP hProp hTr (isTranslateInvariant_toTupleFunctional hσ hinv) F
    (reflectedCorrelation_bounded F fun X hX Y hY => ?_) u hu
  have hF := (R4TupleForms.mem_spanIn_iff TimeAxis.upperHalfSpace F.1).1 F.2
  exact reflected_pair_bounded hσ hread hle (hF X hX) (hF Y hY)
theorem integrable_centredProduct (hCI : InfiniteLattice.CenteredIdentity.Statement) {k : ℕ}
    (hk : 0 < k) (μ ν' : Measure (InfiniteLattice.GaugeField (meshSize s.L (k : ℤ))))
    [hμ : IsProbabilityMeasure μ] (Y : SeparatedTuples.SepTuple) :
    Integrable (fun U => centredProduct s.L k ν' (TupleLists.ofList Y) U) μ := by
  have hb : ∀ i : Fin Y.1.length, Probability.IsBoundedRealRV
      (InfiniteLattice.smearedEnergy (Y.1.get i) :
        InfiniteLattice.GaugeField (meshSize s.L (k : ℤ)) → ℝ) := by
    intro i
    obtain ⟨h₁, h₂⟩ := Y.2.1 _ (List.get_mem Y.1 i)
    have hc : Continuous (Y.1.get i) := ContDiff.continuous h₁
    obtain ⟨C, hC⟩ := h₂.exists_bound_of_continuous hc
    have hf : Y.1.get i ∈ InfiniteLattice.compactTestFunctions :=
      ⟨hc.measurable, ⟨C, hC⟩, h₂⟩
    exact ((hCI { s with K := ⟨k, hk⟩ } μ hμ).1.1 _ hf).2
  choose C hC using fun i => (hb i).bounded
  have hm : Measurable (fun U => centredProduct s.L k ν' (TupleLists.ofList Y) U) :=
    Finset.measurable_prod _ fun i _ => (hb i).measurable.sub_const _
  refine Integrable.of_bound hm.aestronglyMeasurable
    (∏ i, (C i + |∫ V, InfiniteLattice.smearedEnergy (Y.1.get i) V ∂ν'|))
    (Filter.Eventually.of_forall fun U => ?_)
  change ‖∏ i, (InfiniteLattice.smearedEnergy (Y.1.get i) U -
    ∫ V, InfiniteLattice.smearedEnergy (Y.1.get i) V ∂ν')‖ ≤ _
  rw [Real.norm_eq_abs, Finset.abs_prod]
  refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
  exact (abs_sub _ _).trans (add_le_add (hC i U) le_rfl)
theorem realSpanLift_eq_integral (hCI : InfiniteLattice.CenteredIdentity.Statement)
    (hKpos : ∀ j, 0 < K j) (hρ : ∀ j, IsProbabilityMeasure (ρ j)) (j : ℕ) (Ξ : FormalSpan) :
    Integrable (centredProductLinear s.L (K j) (ν j) Ξ) (ρ j) ∧
      realSpanLift (pairedValue K ρ ν j) Ξ =
        ∫ U, centredProductLinear s.L (K j) (ν j) Ξ U ∂ρ j := by
  have := hρ j
  induction Ξ using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero]
    exact ⟨integrable_zero _ _ _, by simp⟩
  | add f g hf hg =>
    simp only [map_add]
    refine ⟨hf.1.add hg.1, ?_⟩
    rw [hf.2, hg.2]
    exact (integral_add hf.1 hg.1).symm
  | single X c =>
    have hs : (Finsupp.single X c : FormalSpan) = c • basisVec X := by
      simp [basisVec]
    have hval : centredProductLinear s.L (K j) (ν j) (basisVec X) =
        fun U => ((centredProduct s.L (K j) (ν j) (TupleLists.ofList X) U : ℝ) : ℂ) := by
      funext U
      simp [centredProductLinear, linearExtend_basisVec]
    have hint := integrable_centredProduct (s := s) hCI (hKpos j) (ρ j) (ν j) X
    rw [hs, map_smul, map_smul, hval]
    refine ⟨hint.ofReal.smul c, ?_⟩
    have h₁ : realSpanLift (pairedValue K ρ ν j) (basisVec X) =
        ((pairedValue K ρ ν j ((finTupleEquiv s).symm X) : ℝ) : ℂ) :=
      linearExtend_basisVec _ _
    rw [h₁]
    have h₂ : pairedValue K ρ ν j ((finTupleEquiv s).symm X) =
        ∫ U, centredProduct s.L (K j) (ν j) (TupleLists.ofList X) U ∂ρ j := rfl
    rw [h₂, smul_eq_mul, ← integral_complex_ofReal, ← integral_const_mul]
    rfl
theorem tendsto_realSpanLift (hlim : StateLimits.IsPointwiseLimit K ρ ν σ) (Ξ : FormalSpan) :
    Tendsto (fun j => realSpanLift (pairedValue K ρ ν j) Ξ) atTop
      (𝓝 (realSpanLift σ Ξ)) := by
  induction Ξ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add]
    exact hf.add hg
  | single X c =>
    have hs : (Finsupp.single X c : FormalSpan) = c • basisVec X := by
      simp [basisVec]
    rw [hs]
    simp only [map_smul, smul_eq_mul]
    refine Tendsto.const_mul c ?_
    have h₁ := (Complex.continuous_ofReal.tendsto _).comp
      (hlim ((finTupleEquiv s).symm X))
    have h₂ : (fun j => realSpanLift (pairedValue K ρ ν j) (basisVec X)) =
        Complex.ofReal ∘ fun j => pairedValue K ρ ν j ((finTupleEquiv s).symm X) :=
      funext fun j => linearExtend_basisVec _ _
    have h₃ : realSpanLift σ (basisVec X) = ((σ ((finTupleEquiv s).symm X) : ℝ) : ℂ) :=
      linearExtend_basisVec _ _
    rw [h₂, h₃]
    exact h₁
theorem tendsto_meshSize (hL : 2 ≤ s.L) (hK : Tendsto K atTop atTop) :
    Tendsto (fun j => meshSize s.L (K j : ℤ)) atTop (𝓝 0) := by
  have hL' : (1 : ℝ) < s.L := by exact_mod_cast (by omega : 1 < s.L)
  have h₁ : Tendsto (fun n : ℕ => ((s.L : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (by positivity))
      (inv_lt_one_of_one_lt₀ hL')
  refine (h₁.comp hK).congr fun j => ?_
  simp [meshSize, zpow_neg]
theorem timeReflectAtOrigin_toFun (a : ℝ) :
    (InfiniteLattice.timeReflectAtOrigin a).toFun = TimeAxis.timeReflection := by
  funext x
  unfold InfiniteLattice.timeReflectAtOrigin
  rw [InfiniteLattice.timeReflect_apply]
  funext i
  fin_cases i <;>
    simp [TimeAxis.timeReflection, InfiniteLattice.originTime, InfiniteLattice.timeAxis] <;> ring
open scoped ComplexOrder in
theorem isPosSemidef_of_limit (hσ : IsTupleFunctional σ)
    {β : ℕ → ℝ} (hβ : ∀ j, 0 < β j) (hL : 2 ≤ s.L) (hK : Tendsto K atTop atTop)
    (hKpos : ∀ j, 0 < K j)
    (hρ : ∀ j, ρ j ∈ InfiniteLattice.periodicGibbsSet s.L (K j) (β j))
    (hν : ∀ j, ν j ∈ InfiniteLattice.periodicGibbsSet s.L (K j) (β j))
    (hνθ : ∀ j (t : InfiniteLattice.halfSpacingTimes (meshSize s.L (K j : ℤ))),
      InfiniteLattice.IsSymmetricUnder (ν j) (InfiniteLattice.timeReflect t))
    (hCalc : CentredProductCalculus)
    (hCI : InfiniteLattice.CenteredIdentity.Statement)
    (hPos : InfiniteLattice.ReflectionFormPosAndSupBound)
    (hTr : SeparatedTuples.PositiveTranslates.Statement)
    (hlim : StateLimits.IsPointwiseLimit K ρ ν σ) :
    HilbertSpaceBasics.IsPosSemidef (reflectionForm (toTupleFunctional σ hσ)) := by
  have hρp : ∀ j, IsProbabilityMeasure (ρ j) := fun j => (hρ j).1.1
  have hνp : ∀ j, IsProbabilityMeasure (ν j) := fun j => (hν j).1.1
  refine { toIsSesquilinear := isSesquilinear_reflectionForm _, nonneg := fun F => ?_ }
  set Ξ := formalMul (reflectConj F) F.1 with hΞ
  have hform : reflectionForm (toTupleFunctional σ hσ) F F = realSpanLift σ Ξ := rfl
  have hF := (R4TupleForms.mem_spanIn_iff TimeAxis.upperHalfSpace F.1).1 F.2
  have hcompact : IsCompact (⋃ X ∈ F.1.support, ⋃ f ∈ X.1, tsupport f) :=
    F.1.support.isCompact_biUnion fun X _ =>
      (List.finite_toSet X.1).isCompact_biUnion fun f hf => (X.2.1 f hf).2
  obtain ⟨δ, hδ, hsupp⟩ := exists_time_floor hcompact (by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨X, hX, f, hf, hxf⟩ := hx
    exact hF X hX f hf hxf)
  have hsp : ∀ᶠ j in atTop, meshSize s.L (K j : ℤ) / 2 < δ := by
    have h₁ := (tendsto_meshSize hL hK).div_const 2
    rw [zero_div] at h₁
    exact h₁.eventually (gt_mem_nhds hδ)
  have hev : ∀ᶠ j in atTop, 0 ≤ realSpanLift (pairedValue K ρ ν j) Ξ := by
    filter_upwards [hsp] with j hj
    have hνj := hνp j
    let sj : Conventions.StandingParameters := { s with K := ⟨K j, hKpos j⟩ }
    obtain ⟨-, -, ⟨hprod, hconj, -⟩, hinv, hloc⟩ := hCalc sj (ν j) hνj
    set t₀ := InfiniteLattice.originTime (meshSize s.L (K j : ℤ)) with ht₀
    set rep := centredProductLinear s.L (K j) (ν j) with hrep
    set A := rep F.1 with hA
    have hAloc : A ∈ InfiniteLattice.localObsAbove t₀ := by
      refine hloc t₀ δ hj F.1 ((R4TupleForms.mem_spanIn_iff _ F.1).2 ?_)
      intro X hX f hf x hx
      have h₂ : δ ≤ x TimeAxis.timeIdx :=
        hsupp x (Set.mem_biUnion hX (Set.mem_biUnion hf hx))
      change ((t₀ : ℝ)) + δ ≤ x InfiniteLattice.timeAxis
      have h₀ : ((t₀ : ℝ)) = 0 := rfl
      rw [h₀, zero_add]
      exact h₂
    have hrefl : rep (reflectConj F) = InfiniteLattice.timeConj t₀ A := by
      have h₁ := hinv (InfiniteLattice.timeReflectAtOrigin _) (hνθ j t₀) (conjugation F.1)
      rw [timeReflectAtOrigin_toFun] at h₁
      funext U
      have h₂ := congrFun h₁ U
      unfold reflectConj
      refine h₂.symm.trans ?_
      exact (hconj F.1 _).symm
    have hdef : R4TupleForms.FormalMulDefined (reflectConj F) F.1 := (hTr F F 0 le_rfl).2.1
    have hEq : realSpanLift (pairedValue K ρ ν j) Ξ =
        InfiniteLattice.reflectionForm (ρ j) t₀ A A := by
      rw [(realSpanLift_eq_integral hCI hKpos hρp j Ξ).2]
      unfold InfiniteLattice.reflectionForm
      refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      have h₁ := congrFun (hprod _ _ hdef) U
      change rep Ξ U = _
      rw [hΞ]
      refine h₁.trans ?_
      change rep (reflectConj F) U * A U = _
      rw [hrefl]
    have hroot : InfiniteLattice.ReflectionFormNonneg (ρ j) t₀ A :=
      ((hPos sj (β j) (hβ j) (ρ j) (hρ j) t₀).2.1).2.2.2 A hAloc
    rw [hEq, Complex.le_def]
    exact ⟨hroot.2, hroot.1.symm⟩
  rw [hform]
  exact ge_of_tendsto (tendsto_realSpanLift hlim Ξ) hev
section Conclusion
theorem periodicGibbs_facts
    (hSym : InfiniteLattice.PeriodicStatesAllScales.AllScalesAllCouplings)
    {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 0 < k) {b : ℝ} (hb : 0 < b)
    {μ : Measure (InfiniteLattice.GaugeField (meshSize L (k : ℤ)))}
    (h : μ ∈ InfiniteLattice.periodicGibbsSet L k b) :
    IsProbabilityMeasure μ ∧
      (∀ v : InfiniteLattice.LatticePoint (meshSize L (k : ℤ)),
        InfiniteLattice.IsSymmetricUnder μ (InfiniteLattice.shift v)) ∧
      ∀ t : InfiniteLattice.halfSpacingTimes (meshSize L (k : ℤ)),
        InfiniteLattice.IsSymmetricUnder μ (InfiniteLattice.timeReflect t) := by
  have hp : IsProbabilityMeasure μ := h.1.1
  have hm := (hSym L k hL.1 hL.2 hk b hb).1 ⟨μ, hp⟩ h
  exact ⟨hp, hm.1, fun t => (hm.2.2 (InfiniteLattice.equalTimeMirror t)).1⟩
theorem pairedValue_multilinear (hCalc : CentredProductCalculus)
    (hCI : InfiniteLattice.CenteredIdentity.Statement) (hKpos : ∀ j, 0 < K j)
    (hρ : ∀ j, IsProbabilityMeasure (ρ j)) (hν : ∀ j, IsProbabilityMeasure (ν j)) (j : ℕ)
    {k : ℕ} (i : Fin k) (t t' : ℝ) (X X' X'' : Continuum.SeparatedFourTuples.SepTupleLen s k)
    (h₁ : ∀ l, l ≠ i → X.1 l = X'.1 l) (h₂ : X''.1 i = t • X.1 i + t' • X'.1 i)
    (h₃ : ∀ l, l ≠ i → X''.1 l = X.1 l) :
    pairedValue K ρ ν j (Continuum.SeparatedFourTuples.ofFixedLength X'') =
      t * pairedValue K ρ ν j (Continuum.SeparatedFourTuples.ofFixedLength X) +
        t' * pairedValue K ρ ν j (Continuum.SeparatedFourTuples.ofFixedLength X') := by
  have hc := (hCalc { s with K := ⟨K j, hKpos j⟩ } (ν j) (hν j)).2.1.2.2 k
    (Continuum.SeparatedFourTuples.sepLenEquiv s k X'')
    (Continuum.SeparatedFourTuples.sepLenEquiv s k X)
    (Continuum.SeparatedFourTuples.sepLenEquiv s k X') i t t'
    (fun l hl => ⟨h₃ l hl, (h₃ l hl).trans (h₁ l hl)⟩) h₂
  have hm : ∀ Y : Continuum.SeparatedFourTuples.SepTupleLen s k, ∀ l,
      Y.1 l ∈ InfiniteLattice.compactTestFunctions :=
    fun Y l => mem_compactTestFunctions (isC1c_of_mem Y.2 l)
  have hi : ∀ Y : Continuum.SeparatedFourTuples.SepTupleLen s k,
      Integrable (StateLimits.centeredProduct (K j) (ν j)
        (Continuum.SeparatedFourTuples.ofFixedLength Y)) (ρ j) :=
    fun Y => by
      haveI := hρ j
      exact integrable_prod_centered hCI (hKpos j) (ρ j) (hm Y) _
  have hp : StateLimits.centeredProduct (K j) (ν j) (Continuum.SeparatedFourTuples.ofFixedLength X'') =
      fun U => t * StateLimits.centeredProduct (K j) (ν j)
          (Continuum.SeparatedFourTuples.ofFixedLength X) U +
        t' * StateLimits.centeredProduct (K j) (ν j)
          (Continuum.SeparatedFourTuples.ofFixedLength X') U := by
    funext U
    exact congrFun hc U
  unfold pairedValue
  rw [hp, integral_add ((hi X).const_mul t) ((hi X').const_mul t'), integral_const_mul,
    integral_const_mul]
theorem limit_isMultilin (hCalc : CentredProductCalculus)
    (hCI : InfiniteLattice.CenteredIdentity.Statement) (hKpos : ∀ j, 0 < K j)
    (hρ : ∀ j, IsProbabilityMeasure (ρ j)) (hν : ∀ j, IsProbabilityMeasure (ν j))
    (hlim : StateLimits.IsPointwiseLimit K ρ ν σ) : Continuum.SeparatedFourTuples.IsMultilin σ := by
  intro k _ i t t' X X' X'' h₁ h₂ h₃
  refine tendsto_nhds_unique (hlim (Continuum.SeparatedFourTuples.ofFixedLength X'')) ?_
  have h := ((hlim (Continuum.SeparatedFourTuples.ofFixedLength X)).const_mul t).add
    ((hlim (Continuum.SeparatedFourTuples.ofFixedLength X')).const_mul t')
  refine h.congr fun j => ?_
  exact (pairedValue_multilinear hCalc hCI hKpos hρ hν j i t t' X X' X'' h₁ h₂ h₃).symm
theorem isSymm_of_symmetricFunctional (h : IsSymmetricTupleFunctional σ) :
    Continuum.SeparatedFourTuples.IsSymm σ := by
  intro k X ς
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact congrArg (fun Y => σ (Continuum.SeparatedFourTuples.ofFixedLength Y))
      (Subtype.ext (funext fun i => i.elim0))
  · exact h k hk X ς
theorem statement_holds (hMaps : StateMapsAndLimitsAreSeparatedFunctionals)
    (hCalc : CentredProductCalculus)
    (hCI : InfiniteLattice.CenteredIdentity.Statement)
    (hSym : InfiniteLattice.PeriodicStatesAllScales.AllScalesAllCouplings)
    (hPos : InfiniteLattice.ReflectionFormPosAndSupBound)
    (hProp : ReflectionPositivity.FormProperties.Assertion)
    (hTr : SeparatedTuples.PositiveTranslates.Statement)
    (hT : ToriLimits.EuclideanSymmetryFacts.Statement) : Statement := by
  intro s N K β ρ ν σ hlimit hβ B
  have hSeq := hlimit.periodicGibbs
  have hKpos := hlimit.cutoff_pos
  have hLs : Conventions.IsAdmissibleBlockingFactor s.L := s.isAdmissible
  have hL2 : 2 ≤ s.L := by
    have := hLs.2
    omega
  have fρ := fun j => periodicGibbs_facts hSym hLs (hKpos j) (hβ j) (hSeq.left_mem j)
  have fν := fun j => periodicGibbs_facts hSym hLs (hKpos j) (hβ j) (hSeq.right_mem j)
  have hρ := fun j => (fρ j).1
  have hν := fun j => (fν j).1
  obtain ⟨hall, hSum⟩ := hMaps
  obtain ⟨hMap, hlims⟩ := hall s K β ρ ν hKpos hSeq
  obtain ⟨⟨hFun, hSymF⟩, -, -, -, hconn, -⟩ := hlims σ hlimit
  have hSum' := hSum s
  have hle := abs_pairedValue_le B hMap (fun τ => hSum' τ)
  have hlimit_le : ∀ (X : FinTuple s), 1 ≤ tupleLength X → ∀ d R : ℝ, 0 < d → 0 < R →
      TupleLipAt N X d R →
      |σ X| ≤ (N.momentBound (tupleLength X) d R).toReal * sharpNormProd N X :=
    fun X hX d R hd hR hr =>
      le_of_tendsto ((hlimit.pointwise X).abs) (Eventually.of_forall (hle X hX d R hd hR hr))
  have hEq := abs_shift_sub_le_of hKpos hCI hρ hν hle
  have hTend := shift_bound_tendsto_of (N := N) (s := s) hT
  have hMov := tendsto_shifted_of hρ hlimit.pointwise hEq hTend
  have hInv := translate_invariant_of hL2 hSeq.cutoff_tendsto hKpos hρ hν (fun j => (fρ j).2.1)
    (fun j => (fν j).2.1) hCalc hlimit.pointwise hMov
  have hP := isPosSemidef_of_limit hFun hβ hL2 hSeq.cutoff_tendsto hKpos hSeq.left_mem
    hSeq.right_mem (fun j => (fν j).2.2) hCalc hCI hPos hTr hlimit.pointwise
  exact
    { momentBound_ne_top := momentBound_ne_top_of_hyp B
      abs_value_le := hle
      abs_limit_le := hlimit_le
      abs_shift_sub_le := hEq
      shift_bound_tendsto := hTend
      tendsto_shifted := hMov
      symm := isSymm_of_symmetricFunctional hSymF
      multilin := limit_isMultilin hCalc hCI hKpos hρ hν hlimit.pointwise
      translate_invariant := hInv
      connected := fun n hn => (hconn n (by omega)).2
      partition_expansion := fun n hn f => hSum' σ hFun n hn f
      reflection_positive := ⟨hFun, hP, hP.isHermitianForm,
        (reflectionForm_cauchySchwarz_triangle hP).1, (reflectionForm_cauchySchwarz_triangle hP).2,
        contraction_of hFun hP hProp hTr hInv (fun X hX => exists_tupleLipAt X hX) hlimit_le⟩ }
end Conclusion
end TranslatedTuples
end BoundsOnEverySide
end YangMills.Construction
