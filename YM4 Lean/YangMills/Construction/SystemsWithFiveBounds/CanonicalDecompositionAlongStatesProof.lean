import YangMills.Construction.SystemOfAdmissibleConstants.CumulantOfVariablesWithBoundedCentredMomentsProof
import YangMills.Construction.BoundsOnEverySide.MovingTuplesOfALimitAlongStatesProof
import YangMills.Construction.Continuum.MomentsOfComponentsThatFactoriseFarAway
import YangMills.Construction.Continuum.SeparatingFamilyIsCountableStableAndApproximating
import YangMills.Construction.Continuum.SharpNormOfATestFunctionAndNeighbourhoodsOfDisjointCompactSets
import YangMills.Construction.Continuum.WhatACanonicalDecompositionOfAFunctionalDeterminesProof
import YangMills.Construction.Cumulants.MomentCumulantFormulaAndThreeConsequences
import YangMills.Construction.InfiniteLattice.AlmostEveryConditionalMeasureIsErgodicUnderTheTranslations
import YangMills.Construction.InfiniteLattice.TestExistenceVersionsAndIntegralOfRegularConditionalProbabilities
import YangMills.Construction.Lattice.DoubleBlockContourPaths
import YangMills.Construction.LimitTheorem.CanonicalDecompositionOnTuplesAndOnMaps
import YangMills.Construction.LimitTheorem.RepresentativeAndTheIdentificationsProof
import YangMills.Construction.Measures.SupportFullMeasureAndL2Rank
import YangMills.Construction.PassageToTheLimit.WhatPassesToTheLimitProof
import YangMills.Construction.ReflectionPositiveLimits.EveryLimitOfALatticeApproximationIsContinuous
import YangMills.Construction.ReflectionPositiveLimits.PeriodicGibbsStateLimitsDefs
import YangMills.Construction.ReflectionPositiveLimits.PlateauxOfLimitsOfLatticeStates
import YangMills.Construction.ReflectionPositiveLimits.PurePeriodicGibbsStatesAreTheErgodicOnes
import YangMills.Construction.SystemsWithFiveBounds.CanonicalDecompositionAlongStates
import YangMills.Construction.SystemsWithFiveBounds.ConditionsUsedOfALimitAlongStates
import YangMills.Construction.SystemsWithFiveBounds.GrowthOfAFunctionalAtNumbers
import YangMills.Construction.SystemsWithFiveBounds.WhatALimitAlongStatesHas
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ClusterMoments
private theorem exists_finEquiv_of_perm {α : Type*} {A B : List α} (h : A.Perm B) :
    ∃ e : Fin A.length ≃ Fin B.length, ∀ i, A.get i = B.get (e i) := by apply _root_.YangMills.Construction.PeriodicLattice.DoubleBlock.Contours.exists_equiv_get_of_perm <;> assumption
end ClusterMoments
section
open MeasureTheory Filter InfiniteLattice
open scoped Topology ComplexOrder Matrix
namespace WindowLimits
section Observables
variable {a : ℝ}
private theorem finite_faces_center_ne_zero (ha : 0 < a) {f : AmbientSpace → ℝ} (hf : HasCompactSupport f) :
    {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.finite_center_support <;> assumption
end Observables
private theorem mem_compactTestFunctions_of_c1 {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    f ∈ compactTestFunctions := by
  obtain ⟨h₁, h₂, -⟩ := hf
  exact ⟨h₁.continuous.measurable, h₂.exists_bound_of_continuous h₁.continuous, h₂⟩
section OfTheStates
variable {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (Q : CutoffCouplingSequence L)
include hL in
private theorem mesh_pos (j : ℕ+) : 0 < Q.mesh j := by
  have hL' : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 13) hL.2
  exact zpow_pos (by exact_mod_cast hL') _
variable {Q} {ρ ν : ∀ j, Measure (Q.Fields j)} {hρ : ∀ j, ρ j ∈ Q.gibbsStates j}
end OfTheStates
end WindowLimits
end
section
open MeasureTheory Filter InfiniteLattice
open scoped Topology
namespace WindowLimits
open BoundsOnEverySide TestFunctions
private theorem isLipschitzFor_of_c1 {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f := by
  obtain ⟨h₁, h₂, -⟩ := hf
  obtain ⟨C, hC⟩ := h₁.lipschitzWith_of_hasCompactSupport h₂ one_ne_zero
  refine ⟨C, C.2, fun x y => ?_⟩
  have h := hC.dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ C.2)
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun μ => ?_
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt
    (Finset.single_le_sum (f := fun κ => (x - y) κ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ))
abbrev _root_.YangMills.DeltaSharedProofs.p3475 := @isLipschitzFor_of_c1
private theorem prod_parts_prod_eq {n : ℕ} (π : SetPartition.Partitions (Finset.univ : Finset (Fin n))) (a : Fin n → ℝ) :
    ∏ J ∈ π.parts, ∏ i ∈ J, a i = ∏ i, a i := by apply _root_.YangMills.DeltaSharedProofs.p21832 <;> assumption
private theorem prod_orderEmbOfFin_eq {n : ℕ} (J : Finset (Fin n)) (a : Fin n → ℝ) :
    ∏ k, a (J.orderEmbOfFin rfl k) = ∏ i ∈ J, a i := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.LimitPassage.prod_comp_orderEmbOfFin <;> assumption
private theorem sharpNormR4_nonneg (M : ℝ) (f : (Fin 4 → ℝ) → ℝ) : 0 ≤ sharpNormR4 M f := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.sharpNormR4_nonneg <;> assumption
end WindowLimits
end
section
open MeasureTheory Filter InfiniteLattice
open scoped Topology
namespace SystemsWithFiveBounds
open Probability (IsBoundedRealRV)
open WindowLimits TestFunctions
section Moments
variable {F : StatedSideFamily} {N : BoundConstants} (B : BoundsHoldAt F N) {K : ℕ+} {β : ℝ}
  {ρ ν : Measure (GaugeField (PeriodicLattice.meshSize F.L ((K : ℕ) : ℤ)))}
include B in
private theorem abs_centredMoment_le (hMC : Cumulants.MomentCumulantFormula.Claim)
    (hM : SmearedObservablesWellDefined)
    (hD : F.IsFirstPassage K β) (hρs : ρ ∈ F.stateSet F.L K β) (hνs : ν ∈ F.stateSet F.L K β)
    {n : ℕ} (f : Fin n → AmbientSpace → ℝ)
    (hf : ∀ i, f i ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)))
    {d R : ℝ} (hd : 0 < d) (hR : 0 < R) (hb : ∀ i, ∃ x, tsupport (f i) ⊆ closedBallR4 x R)
    (hs : HasSeparatedSupportsR4 f d) :
    |∫ U, ∏ i, (smearedEnergy (f i) U - ∫ V, smearedEnergy (f i) V ∂ν) ∂ρ| ≤
      momentWeight N n d R * ∏ i, sharpNormR4 F.M (f i) := by
  have hρ := F.stateSet_subset K β hD hρs
  have ha : 0 < PeriodicLattice.meshSize F.L ((K : ℕ) : ℤ) := by
    have hL' : 0 < F.L := lt_of_lt_of_le (by norm_num : 0 < 13) F.admissible.2
    exact zpow_pos (by exact_mod_cast hL') _
  have hprob : IsProbabilityMeasure ρ := hρ.1.1
  set Y : Fin n → GaugeField (PeriodicLattice.meshSize F.L ((K : ℕ) : ℤ)) → ℝ :=
    fun i U => smearedEnergy (f i) U with hY
  set c : Fin n → ℝ := fun i => -∫ V, smearedEnergy (f i) V ∂ν with hc
  have hYb : ∀ i, IsBoundedRealRV (Y i) := fun i =>
    ((hM _ ha).1 (f i) (mem_compactTestFunctions_of_c1 (hf i))).2
  have hWb : ∀ i, IsBoundedRealRV (fun U => Y i U + c i) := by
    intro i
    obtain ⟨hm, C, hC⟩ := hYb i
    refine ⟨hm.add measurable_const, C + |c i|, fun U => ?_⟩
    exact (abs_add_le _ _).trans (by linarith [hC U])
  obtain ⟨-, h₂, h₃, -⟩ := hMC _ ρ n (fun i U => Y i U + c i) ⟨hprob, hWb⟩
  obtain ⟨g₁, -, -, g₄, -⟩ := hMC _ ρ n Y ⟨hprob, hYb⟩
  have hint : ∀ i, Integrable (Y i) ρ := fun i => by
    obtain ⟨hm, C, hC⟩ := hYb i
    exact Integrable.of_bound hm.aestronglyMeasurable C
      (Eventually.of_forall fun U => by rw [Real.norm_eq_abs]; exact hC U)
  have hlip : ∀ i, TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 (f i) := fun i => isLipschitzFor_of_c1 (hf i)
  have hblock : ∀ J : Finset (Fin n), J.Nonempty →
      ‖Cumulants.mixedPartialLogCumulant ρ (fun i U => Y i U + c i) J‖ ≤
        blockWeight N d R J * ∏ i ∈ J, sharpNormR4 F.M (f i) := by
    intro J hJ
    by_cases h1 : J.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h1
      rw [h₃ i]
      have e : Probability.complexExpectation ρ (fun ω => ((Y i ω + c i : ℝ) : ℂ)) =
          (((∫ U, smearedEnergy (f i) U ∂ρ) - ∫ V, smearedEnergy (f i) V ∂ν : ℝ) : ℂ) := by
        unfold Probability.complexExpectation
        rw [integral_complex_ofReal, integral_add (hint i) (integrable_const _)]
        simp [hc, hY, sub_eq_add_neg]
      rw [e, Complex.norm_real, Real.norm_eq_abs]
      obtain ⟨x, hx⟩ := hb i
      have hbd := B.mean_sub_le K β hD ρ hρs ν hνs R hR (f i) (hlip i) ⟨x, hx⟩
      simpa [blockWeight] using hbd
    · have h2 : 2 ≤ J.card := by
        have := hJ.card_pos
        omega
      rw [g₄ J c h2, g₁ J hJ]
      have hbd := B.cumulant_le K β hD ρ hρs J.card h2 R d hR hd
        (fun k => f (J.orderEmbOfFin rfl k)) (fun k => hlip _) (fun k => hb _)
        ⟨hd, fun i k hik => hs.2 _ _ fun e => hik ((J.orderEmbOfFin rfl).injective e)⟩
      rw [prod_orderEmbOfFin_eq J fun i => sharpNormR4 F.M (f i)] at hbd
      have e : Probability.subfamilyCumulant ρ Y J =
          smearedEnergyCumulant ρ (fun k => f (J.orderEmbOfFin rfl k)) := rfl
      rw [e]
      simpa [blockWeight, h1] using hbd
  have hexp := h₂ Finset.univ
  have e₀ : Probability.complexExpectation ρ (fun ω => ((∏ i ∈ Finset.univ, (Y i ω + c i) : ℝ) : ℂ)) =
      ((∫ U, ∏ i, (smearedEnergy (f i) U - ∫ V, smearedEnergy (f i) V ∂ν) ∂ρ : ℝ) : ℂ) := by
    unfold Probability.complexExpectation
    rw [integral_complex_ofReal]
    simp [hc, hY, sub_eq_add_neg]
  rw [e₀] at hexp
  have hn := congrArg norm hexp
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  rw [hn]
  refine (norm_sum_le _ _).trans ?_
  unfold momentWeight
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun π _ => ?_
  rw [norm_prod, ← prod_parts_prod_eq π fun i => sharpNormR4 F.M (f i), ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    fun J hJ => hblock J (π.nonempty_of_mem_parts hJ)
abbrev _root_.YangMills.SharedProofs.p95142 := @abs_centredMoment_le
end Moments
end SystemsWithFiveBounds
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace SystemsWithFiveBounds
open WindowLimits TestFunctions LimitTheorem
section ALimit
variable {F : StatedSideFamily} {N : BoundConstants} (Q : WindowStates F) {σ : SeparatedTuples.TupleFunctional}
private theorem pairedValue_singleton (hM : SmearedObservablesWellDefined)
    (j : ℕ+) (X : TestSpaces.SepTupleOfCard 1) :
    Q.toCutoffCouplingSequence.pairedValue Q.ρ Q.ν j ⟨1, X⟩ =
      (∫ U, smearedEnergy (X.1 0) U ∂Q.ρ j) - ∫ U, smearedEnergy (X.1 0) U ∂Q.ν j := by
  have hp : IsProbabilityMeasure (Q.ρ j) := (Q.ρ_mem j).1.1
  have ha := mesh_pos F.admissible Q.toCutoffCouplingSequence j
  have hi : Integrable (fun U => smearedEnergy (X.1 0) U) (Q.ρ j) := by
    obtain ⟨hm, C, hC⟩ := ((hM _ ha).1 (X.1 0) (mem_compactTestFunctions_of_c1 (X.2.1 0))).2
    exact Integrable.of_bound hm.aestronglyMeasurable C
      (Eventually.of_forall fun U => by rw [Real.norm_eq_abs]; exact hC U)
  have e : ∀ U, CutoffRepresentative.centredProduct F.L (Q.K j) (Q.ν j) ⟨1, X⟩ U =
      smearedEnergy (X.1 0) U - ∫ V, smearedEnergy (X.1 0) V ∂Q.ν j := fun U => by
    simp [CutoffRepresentative.centredProduct, CutoffRepresentative.centredSmearedField]
  show ∫ U, CutoffRepresentative.centredProduct F.L (Q.K j) (Q.ν j) ⟨1, X⟩ U ∂Q.ρ j = _
  rw [integral_congr_ae (Eventually.of_forall e), integral_sub hi (integrable_const _)]
  simp
abbrev _root_.YangMills.SharedProofs.p1691 := @pairedValue_singleton
private theorem tendsto_K_coe : Tendsto (fun j => ((Q.K j : ℕ+) : ℕ)) atTop atTop := by
  have hcoe : Tendsto (fun p : ℕ+ => (p : ℕ)) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b.succPNat, fun a ha => by
      have h : ((b.succPNat : ℕ+) : ℕ) ≤ (a : ℕ) := PNat.coe_le_coe _ _ |>.2 ha
      rw [Nat.succPNat_coe] at h
      omega⟩
  exact hcoe.comp Q.tendsto_K
abbrev _root_.YangMills.SharedProofs.p107289 := @tendsto_K_coe
private theorem abs_onePointConst_le (hM : SmearedObservablesWellDefined)
    (hOP : OnePointLimitWithConstants) (B : BoundsHoldAt F N) (hσ : Q.HasLimit σ) {c : ℝ}
    (hc : ∀ X : TestSpaces.SepTupleOfCard 1, evalOnMap σ ⟨1, X⟩ = c * ∫ x, X.1 0 x) :
    |c| ≤ unitBallBound F.M N := by
  refine (hOP F N B Q.K Q.β Q.ρ Q.ν Q.isFirstPassage Q.ρ_state Q.ν_state).2 c fun f hf => ?_
  obtain ⟨hc1, -, hint⟩ := hf
  have h := hσ ⟨1, TestSpaces.singletonSepTuple f hc1⟩
  have e : evalOnMap σ ⟨1, TestSpaces.singletonSepTuple f hc1⟩ = c := by
    rw [hc]
    have e₁ : ∫ x, (TestSpaces.singletonSepTuple f hc1).1 0 x = 1 := hint
    rw [e₁, mul_one]
  rw [e] at h
  exact h.congr fun j => pairedValue_singleton Q hM j _
end ALimit
end SystemsWithFiveBounds
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace WindowLimits
open Probability (IsBoundedRealRV)
open BoundsOnEverySide TestFunctions LimitTheorem
private theorem prod_sub_prod_telescope {n : ℕ} (a b : Fin n → ℝ) :
    ∏ i, a i - ∏ i, b i =
      ∑ i, ∏ l, (if l < i then b l else if l = i then a i - b i else a l) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : ∏ l : Fin (n + 1), (if l < 0 then b l else if l = 0 then a 0 - b 0 else a l) =
        (a 0 - b 0) * ∏ l : Fin n, a l.succ := by
      rw [Fin.prod_univ_succ]
      simp [Fin.succ_ne_zero]
    have hs : ∀ i : Fin n, ∏ l : Fin (n + 1),
        (if l < i.succ then b l else if l = i.succ then a i.succ - b i.succ else a l) =
        b 0 * ∏ l : Fin n, (if l < i then b l.succ else
          if l = i then a i.succ - b i.succ else a l.succ) := by
      intro i
      rw [Fin.prod_univ_succ]
      simp [Fin.succ_pos, Fin.succ_lt_succ_iff, Fin.succ_inj]
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ, h0]
    simp only [hs]
    rw [← Finset.mul_sum, ← ih (fun i => a i.succ) (fun i => b i.succ)]
    ring
private def mixedTuple {n : ℕ} (x y : Fin n → AmbientSpace → ℝ) (i : Fin n) : Fin n → AmbientSpace → ℝ :=
  fun l => if l < i then y l else if l = i then x i - y i else x l
private theorem smearedEnergy_sub {a : ℝ} (ha : 0 < a) {f g : AmbientSpace → ℝ} (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) (U : GaugeField a) :
    smearedEnergy (f - g) U = smearedEnergy f U - smearedEnergy g U := by
  have hfin : ∀ {h : AmbientSpace → ℝ}, HasCompactSupport h →
      (Function.support fun p : ElementaryPlaquette a => faceEnergy U p • h p.center).Finite := by
    intro h hh
    refine (finite_faces_center_ne_zero ha hh).subset fun p hp => ?_
    have hp' : faceEnergy U p • h p.center ≠ 0 := hp
    show h p.center ≠ 0
    exact fun h0 => hp' (by simp [h0])
  unfold smearedEnergy
  rw [← finsum_sub_distrib (hfin hf) (hfin hg)]
  refine finsum_congr fun p => ?_
  simp only [Pi.sub_apply, smul_sub]
private theorem tsupport_sub_subset_of {f g : AmbientSpace → ℝ} {O : Set AmbientSpace} (hf : tsupport f ⊆ O)
    (hg : tsupport g ⊆ O) : tsupport (f - g) ⊆ O := by
  refine (closure_minimal (t := tsupport f ∪ tsupport g) (fun x hx => ?_)
    ((isClosed_tsupport f).union (isClosed_tsupport g))).trans (union_subset hf hg)
  by_contra hn
  have h₁ : f x = 0 := by
    by_contra h
    exact hn (Or.inl (subset_tsupport _ h))
  have h₂ : g x = 0 := by
    by_contra h
    exact hn (Or.inr (subset_tsupport _ h))
  exact hx (by simp [h₁, h₂])
private theorem integrable_prod_of_bdd {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {F : Fin n → Ω → ℝ} (hm : ∀ i, Measurable (F i)) (hb : ∀ i, ∃ C, ∀ ω, |F i ω| ≤ C) :
    Integrable (fun ω => ∏ i, F i ω) μ := by
  choose C hC using hb
  refine Integrable.of_bound (Finset.measurable_prod _ fun i _ => hm i).aestronglyMeasurable (∏ i, C i)
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => hC i ω
private theorem exists_ballAndGap (X : TestSpaces.SepTuple) : ∃ d R : ℝ, 0 < d ∧ 0 < R ∧
    (∀ i, ∃ c, tsupport (X.2.1 i) ⊆ closedBallR4 c R) ∧ HasSeparatedSupportsR4 X.2.1 d := by
  obtain ⟨n, Xf⟩ := X
  obtain ⟨δ, R, hδ, hR, O, -, hKO, h₂, h₃⟩ := exists_open_nbhds_separated_bounded (fun i => tsupport (Xf.1 i))
    (fun i => (Xf.2.1 i).2.1) (fun i l hil => Xf.2.2 hil)
  refine ⟨δ, R, hδ, hR, fun i => ⟨0, fun x hx => ?_⟩, hδ, fun i l hil => ?_⟩
  · show TorusMetric.euclidNormVec (x - 0) ≤ R
    rw [sub_zero]
    exact h₃ i x (hKO i hx)
  · exact le_iInf₂ fun x hx => le_iInf₂ fun y hy =>
      ENNReal.ofReal_le_ofReal (h₂ i l hil x (hKO i hx) y (hKO l hy))
end WindowLimits
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace SystemsWithFiveBounds
open Probability (IsBoundedRealRV)
open WindowLimits TestFunctions LimitTheorem
section Values
variable {F : StatedSideFamily} {N : BoundConstants} (B : BoundsHoldAt F N) (Q : WindowStates F)
private def momentIn (j : ℕ+) (ρ : Measure (GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ))))
    (X : TestSpaces.SepTuple) : ℝ :=
  ∫ U, CutoffRepresentative.centredProduct F.L (Q.K j) (Q.ν j) X U ∂ρ
private def tupleBound (F : StatedSideFamily) (N : BoundConstants) (X : TestSpaces.SepTuple) : ℝ :=
  momentWeight N X.1 (exists_ballAndGap X).choose (exists_ballAndGap X).choose_spec.choose *
    ∏ i, sharpNormR4 F.M (X.2.1 i)
variable {Q}
variable {j : ℕ+} {ρ : Measure (GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)))}
include B in
private theorem abs_momentIn_le (hMC : Cumulants.MomentCumulantFormula.Claim)
    (hM : SmearedObservablesWellDefined)
    (hρ : ρ ∈ F.stateSet F.L (Q.K j) (Q.β j)) (X : TestSpaces.SepTuple) :
    |momentIn Q j ρ X| ≤ tupleBound F N X := by
  obtain ⟨hd, hR, hb, hs⟩ := (exists_ballAndGap X).choose_spec.choose_spec
  exact abs_centredMoment_le B hMC hM (Q.isFirstPassage j) hρ (Q.ν_state j) X.2.1 X.2.2.1 hd hR hb hs
include B in
private theorem abs_momentIn_sub_le (hMC : Cumulants.MomentCumulantFormula.Claim)
    (hM : SmearedObservablesWellDefined)
    (hρ : ρ ∈ F.stateSet F.L (Q.K j) (Q.β j)) {n : ℕ}
    (x y : TestSpaces.SepTupleOfCard n) {O : Fin n → Set AmbientSpace} (sx : ∀ i, tsupport (x.1 i) ⊆ O i)
    (sy : ∀ i, tsupport (y.1 i) ⊆ O i) {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (hball : ∀ i, ∃ c, O i ⊆ closedBallR4 c R)
    (hsep : ∀ i l, i ≠ l → ENNReal.ofReal d ≤ setDistR4 (O i) (O l))
    {Bd : ℝ} (hBd : 0 ≤ Bd) (hxB : ∀ i, sharpNormR4 F.M (x.1 i) ≤ Bd)
    (hyB : ∀ i, sharpNormR4 F.M (y.1 i) ≤ Bd)
    (hdB : ∀ i, sharpNormR4 F.M (x.1 i - y.1 i) ≤ Bd) :
    |momentIn Q j ρ ⟨n, x⟩ - momentIn Q j ρ ⟨n, y⟩| ≤
      |momentWeight N n d R| * ((∑ i, sharpNormR4 F.M (x.1 i - y.1 i)) * Bd ^ (n - 1)) := by
  have ha : 0 < PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ) :=
    mesh_pos F.admissible Q.toCutoffCouplingSequence j
  have hρp : IsProbabilityMeasure ρ := (F.stateSet_subset _ _ (Q.isFirstPassage j) hρ).1.1
  have hνp : IsProbabilityMeasure (Q.ν j) := (Q.ν_mem j).1.1
  have hbdd : ∀ f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)),
      IsBoundedRealRV (smearedEnergy f :
        GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)) → ℝ) := fun f hf =>
    ((hM _ ha).1 f (mem_compactTestFunctions_of_c1 hf)).2
  have hintν : ∀ f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)),
      Integrable (smearedEnergy f : GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)) → ℝ) (Q.ν j) :=
    fun f hf => by
      obtain ⟨hm, C, hC⟩ := hbdd f hf
      exact Integrable.of_bound hm.aestronglyMeasurable C
        (Eventually.of_forall fun U => by rw [Real.norm_eq_abs]; exact hC U)
  let c : (AmbientSpace → ℝ) → GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)) → ℝ :=
    fun f U => smearedEnergy f U - ∫ V, smearedEnergy f V ∂Q.ν j
  have hcm : ∀ f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)), Measurable (c f) ∧
      ∃ C, ∀ U, |c f U| ≤ C := fun f hf => by
    obtain ⟨hm, C, hC⟩ := hbdd f hf
    refine ⟨hm.sub measurable_const, C + |∫ V, smearedEnergy f V ∂Q.ν j|, fun U => ?_⟩
    exact (abs_sub _ _).trans (by linarith [hC U])
  have hsubmem : ∀ i, x.1 i - y.1 i ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := fun i =>
    ⟨(x.2.1 i).1.sub (y.2.1 i).1, (x.2.1 i).2.1.sub (y.2.1 i).2.1, Set.subset_univ _⟩
  have hcsub : ∀ i, c (x.1 i - y.1 i) = fun U => c (x.1 i) U - c (y.1 i) U := fun i => by
    funext U
    have e₁ := smearedEnergy_sub ha (x.2.1 i).2.1 (y.2.1 i).2.1 U
    have e₂ : ∫ V, smearedEnergy (x.1 i - y.1 i) V ∂Q.ν j =
        (∫ V, smearedEnergy (x.1 i) V ∂Q.ν j) - ∫ V, smearedEnergy (y.1 i) V ∂Q.ν j := by
      rw [← integral_sub (hintν _ (x.2.1 i)) (hintν _ (y.2.1 i))]
      exact integral_congr_ae (Eventually.of_forall fun V => smearedEnergy_sub ha (x.2.1 i).2.1 (y.2.1 i).2.1 V)
    simp only [c, e₁, e₂]
    ring
  set H : Fin n → Fin n → AmbientSpace → ℝ := fun i => mixedTuple x.1 y.1 i with hH
  have hHmem : ∀ i l, H i l ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := by
    intro i l
    simp only [hH, mixedTuple]
    split_ifs
    · exact y.2.1 l
    · exact hsubmem i
    · exact x.2.1 l
  have hHs : ∀ i l, tsupport (H i l) ⊆ O l := by
    intro i l
    simp only [hH, mixedTuple]
    split_ifs with h₁ h₂
    · exact sy l
    · subst h₂
      exact tsupport_sub_subset_of (sx _) (sy _)
    · exact sx l
  have hHc : ∀ i (U : GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ))),
      ∏ l, c (H i l) U =
        ∏ l, (if l < i then c (y.1 l) U else if l = i then c (x.1 i) U - c (y.1 i) U else c (x.1 l) U) := by
    intro i U
    refine Finset.prod_congr rfl fun l _ => ?_
    simp only [hH, mixedTuple]
    split_ifs with h₁ h₂
    · rfl
    · rw [hcsub]
    · rfl
  have hsum : ∀ U, ∏ l, c (x.1 l) U - ∏ l, c (y.1 l) U = ∑ i, ∏ l, c (H i l) U := by
    intro U
    rw [prod_sub_prod_telescope]
    exact Finset.sum_congr rfl fun i _ => (hHc i U).symm
  have hix : Integrable (fun U => ∏ l, c (x.1 l) U) ρ :=
    integrable_prod_of_bdd (fun l => (hcm _ (x.2.1 l)).1) fun l => (hcm _ (x.2.1 l)).2
  have hiy : Integrable (fun U => ∏ l, c (y.1 l) U) ρ :=
    integrable_prod_of_bdd (fun l => (hcm _ (y.2.1 l)).1) fun l => (hcm _ (y.2.1 l)).2
  have hiH : ∀ i, Integrable (fun U => ∏ l, c (H i l) U) ρ := fun i =>
    integrable_prod_of_bdd (fun l => (hcm _ (hHmem i l)).1) fun l => (hcm _ (hHmem i l)).2
  have e₀ : momentIn Q j ρ ⟨n, x⟩ - momentIn Q j ρ ⟨n, y⟩ = ∑ i, ∫ U, ∏ l, c (H i l) U ∂ρ := by
    show (∫ U, ∏ l, c (x.1 l) U ∂ρ) - ∫ U, ∏ l, c (y.1 l) U ∂ρ = _
    rw [← integral_sub hix hiy, ← integral_finsetSum _ fun i _ => hiH i]
    exact integral_congr_ae (Eventually.of_forall hsum)
  rw [e₀]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hball' : ∀ l, ∃ z, tsupport (H i l) ⊆ closedBallR4 z R := fun l => by
    obtain ⟨z, hz⟩ := hball l
    exact ⟨z, (hHs i l).trans hz⟩
  have hs' : HasSeparatedSupportsR4 (H i) d := ⟨hd, fun a b hab =>
    (hsep a b hab).trans (iInf₂_mono' fun u hu => ⟨u, hHs i a hu, iInf₂_mono' fun v hv => ⟨v, hHs i b hv, le_rfl⟩⟩)⟩
  have hm := abs_centredMoment_le B hMC hM (Q.isFirstPassage j) hρ (Q.ν_state j) (H i) (hHmem i) hd hR hball' hs'
  refine hm.trans ?_
  have hprod : ∏ l, sharpNormR4 F.M (H i l) ≤
      sharpNormR4 F.M (x.1 i - y.1 i) * Bd ^ (n - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have hii : H i i = x.1 i - y.1 i := by simp [hH, mixedTuple]
    rw [hii]
    refine mul_le_mul_of_nonneg_left ?_ (sharpNormR4_nonneg _ _)
    have hle : ∀ l ∈ Finset.univ.erase i, sharpNormR4 F.M (H i l) ≤ Bd := by
      intro l _
      simp only [hH, mixedTuple]
      split_ifs
      · exact hyB l
      · exact hdB i
      · exact hxB l
    calc ∏ l ∈ Finset.univ.erase i, sharpNormR4 F.M (H i l)
        ≤ ∏ _l ∈ Finset.univ.erase i, Bd :=
          Finset.prod_le_prod (fun _ _ => sharpNormR4_nonneg _ _) hle
      _ = Bd ^ (n - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin]
  have hp0 : 0 ≤ ∏ l, sharpNormR4 F.M (H i l) :=
    Finset.prod_nonneg fun _ _ => sharpNormR4_nonneg _ _
  exact (mul_le_mul_of_nonneg_right (le_abs_self _) hp0).trans
    (mul_le_mul_of_nonneg_left hprod (abs_nonneg _))
end Values
end SystemsWithFiveBounds
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace WindowLimits
open BoundsOnEverySide TestFunctions LimitTheorem
section Approximants
variable (s : Conventions.StandingParameters)
private def familyTuples : Set TestSpaces.SepTuple :=
  (fun Y => TupleLists.ofList (R4TupleForms.finTupleEquiv s Y)) '' CanonicalDecomposition.separatingTuples s
private theorem familyTuples_countable
    (hfam : CanonicalDecomposition.SeparatingTuplesProperties.Claim) :
    (familyTuples s).Countable :=
  (hfam s 1 le_rfl).countable.image _
private theorem exists_family_approximants
    (hfam : CanonicalDecomposition.SeparatingTuplesProperties.Claim)
    {M : ℝ} (hM : 1 ≤ M) (X : SeparatedTuples.SepTuple) (hk : 1 ≤ X.1.length) (O : Fin X.1.length → Set AmbientSpace)
    (hO : ∀ i, IsOpen (O i)) (hKO : ∀ i, tsupport (X.1.get i) ⊆ O i) :
    ∃ b : ℕ → Fin X.1.length → SeparatedTuples.RealValued,
      (∀ n, ∃ Y ∈ CanonicalDecomposition.separatingTuples s,
        (R4TupleForms.finTupleEquiv s Y).1 = List.ofFn (b n)) ∧
      (∀ n i, tsupport (b n i) ⊆ O i) ∧
      ∀ i, Tendsto (fun n => sharpNormR4 M (b n i - X.1.get i)) atTop (𝓝 0) := by
  have hOo' : ∀ i, @IsOpen (Continuum.SeparatedFourTuples.EuclideanFour s) _ (O i) := fun i => by
    let P' : Set (Continuum.SeparatedFourTuples.EuclideanFour s) := O i
    have hcl : closure (P'ᶜ) = P'ᶜ :=
      (R4TupleForms.closure_pt_euclidean (s := s) ((O i)ᶜ)).trans (hO i).isClosed_compl.closure_eq
    exact isClosed_compl_iff.1 (closure_eq_iff_isClosed.1 hcl)
  obtain ⟨Y, hYT, hYs, hYt⟩ := (hfam s M hM).approx ((R4TupleForms.finTupleEquiv s).symm X) hk
    O hOo' (fun i => (R4TupleForms.tsupport_pt_euclidean (s := s) (X.1.get i)).le.trans (hKO i))
  refine ⟨fun n => (Y n).1, fun n => ⟨_, hYT n, rfl⟩, fun n i => ?_, hYt⟩
  exact (R4TupleForms.tsupport_pt_euclidean (s := s) ((Y n).1 i)).ge.trans (hYs n i)
end Approximants
end WindowLimits
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace SystemsWithFiveBounds
open WindowLimits TestFunctions LimitTheorem
section Space
variable {F : StatedSideFamily} {N : BoundConstants} (Q : WindowStates F)
private def momentFunctions : Set (TestSpaces.SepTuple → ℝ) :=
  {s | ∃ j ρ, ρ ∈ F.stateSet F.L (Q.K j) (Q.β j) ∧ s = momentIn Q j ρ}
private def MomentHull : Type := ↥(closure (momentFunctions Q))
private instance : TopologicalSpace (MomentHull Q) :=
  inferInstanceAs (TopologicalSpace ↥(closure (momentFunctions Q)))
private instance : T2Space (MomentHull Q) := inferInstanceAs (T2Space ↥(closure (momentFunctions Q)))
private instance : MeasurableSpace (MomentHull Q) := borel _
private instance : BorelSpace (MomentHull Q) := ⟨rfl⟩
variable {Q}
private def MomentHull.eval (s : MomentHull Q) (X : TestSpaces.SepTuple) : ℝ := s.1 X
private theorem MomentHull.continuous_eval (X : TestSpaces.SepTuple) :
    Continuous fun s : MomentHull Q => s.eval X :=
  (continuous_apply X).comp continuous_subtype_val
private theorem MomentHull.closure_induction {P : (TestSpaces.SepTuple → ℝ) → Prop} (hc : IsClosed {s | P s})
    (h : ∀ j ρ, ρ ∈ F.stateSet F.L (Q.K j) (Q.β j) → P (momentIn Q j ρ)) (s : MomentHull Q) :
    P s.1 :=
  closure_minimal (t := {s | P s}) (by
    rintro _ ⟨j, ρ, hρ, rfl⟩
    exact h j ρ hρ) hc s.2
variable (B : BoundsHoldAt F N)
  (hMC : Cumulants.MomentCumulantFormula.Claim)
  (hM : SmearedObservablesWellDefined)
include B hMC hM in
private theorem compactSpace_momentHull : CompactSpace (MomentHull Q) := by
  have hbox : IsCompact (Set.pi Set.univ fun X : TestSpaces.SepTuple =>
      Icc (-tupleBound F N X) (tupleBound F N X)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : closure (momentFunctions Q) ⊆ Set.pi Set.univ fun X : TestSpaces.SepTuple =>
      Icc (-tupleBound F N X) (tupleBound F N X) := by
    refine closure_minimal ?_ hbox.isClosed
    rintro _ ⟨j, ρ, hρ, rfl⟩ X -
    exact abs_le.1 (abs_momentIn_le B hMC hM hρ X)
  exact isCompact_iff_compactSpace.1 (hbox.of_isClosed_subset isClosed_closure hsub)
include B hMC hM in
private theorem ext_of_familyTuples
    (hfam : CanonicalDecomposition.SeparatingTuplesProperties.Claim)
    (hnorm : Continuum.SeparatedFourTuples.SharpNormAndThickenings.Statement)
    (hMone : (1 : ℝ) ≤ F.M) (s₀ : Conventions.StandingParameters) {s s' : MomentHull Q}
    (h : ∀ t ∈ familyTuples s₀, s.eval t = s'.eval t) : s = s' := by
  refine Subtype.ext (funext fun X => ?_)
  obtain ⟨Xl, rfl⟩ : ∃ Xl, X = TupleLists.ofList Xl := ⟨TupleLists.toList X, (TupleLists.ofList_toList X).symm⟩
  by_cases hk : Xl.1.length = 0
  · have hX : Xl = SeparatedTuples.SepTuple.nil := Subtype.ext (List.length_eq_zero_iff.1 hk)
    refine h _ ⟨(R4TupleForms.finTupleEquiv s₀).symm Xl, ?_, by simp⟩
    rw [hX]
    exact Or.inl ((Equiv.symm_apply_eq _).2 R4TupleForms.listOf_nilTuple.symm)
  have hk1 : 1 ≤ Xl.1.length := Nat.pos_of_ne_zero hk
  set n := Xl.1.length with hn
  set g : Fin n → SeparatedTuples.RealValued := Xl.1.get with hgdef
  have hmemg : ∀ i, g i ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := (TupleLists.ofList Xl).2.2.1
  have hdisj : ∀ i l, i ≠ l → Disjoint (tsupport (g i)) (tsupport (g l)) :=
    fun i l hil => (TupleLists.ofList Xl).2.2.2 hil
  obtain ⟨δ, R, hδ, hR, O, hOo, hKO, h₂, h₃⟩ := exists_open_nbhds_separated_bounded (fun i => tsupport (g i))
    (fun i => (hmemg i).2.1) hdisj
  obtain ⟨b, hbT, hbs, hbt⟩ := exists_family_approximants s₀ hfam hMone Xl hk1 O hOo hKO
  obtain ⟨⟨-, hnormed⟩, -⟩ := hnorm s₀ ⟨F.M, hMone⟩
  obtain ⟨⟨Wv, hWv⟩, hN⟩ := hnormed Set.univ
  have hmemV : ∀ f, f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) → f ∈ Wv := fun f hf => by
    exact show f ∈ (Wv : Set (Continuum.SeparatedFourTuples.EuclideanFour s₀ → ℝ)) from by
      rw [hWv]
      exact (R4TupleForms.mem_c1CompactlySupportedIn_univ_iff f).2 ⟨hf.1, hf.2.1⟩
  have hV : ∀ f, f ∈ Wv → f ∈ (Continuum.SeparatedFourTuples.c1SupportedIn
      (Set.univ : Set (Continuum.SeparatedFourTuples.EuclideanFour s₀))) :=
    fun f hf => by
      have hc : f ∈ (Wv : Set (Continuum.SeparatedFourTuples.EuclideanFour s₀ → ℝ)) := hf
      rw [hWv] at hc
      exact hc
  have hbmem : ∀ m i, b m i ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := fun m i => by
    obtain ⟨Y, -, hY⟩ := hbT m
    have hmem : b m i ∈ (R4TupleForms.finTupleEquiv s₀ Y).1 := by
      rw [hY]
      exact (List.mem_ofFn' _ _).2 ⟨i, rfl⟩
    have := (R4TupleForms.finTupleEquiv s₀ Y).2.1 _ hmem
    exact ⟨this.1, this.2, Set.subset_univ _⟩
  have hOd : ∀ i l, i ≠ l → Disjoint (O i) (O l) := fun i l hil =>
    Set.disjoint_left.2 fun x hx hx' => by
      have := h₂ i l hil x hx x hx'
      have e : TorusMetric.euclidNormVec (x - x) = 0 := by simp [TorusMetric.euclidNormVec]
      linarith
  let Yt : ℕ → TestSpaces.SepTupleOfCard n := fun m => ⟨b m, hbmem m, fun i l hil =>
    (hOd i l hil).mono (hbs m i) (hbs m l)⟩
  have hYT : ∀ m, (⟨n, Yt m⟩ : TestSpaces.SepTuple) ∈ familyTuples s₀ := fun m => by
    obtain ⟨Y, hYf, hY⟩ := hbT m
    refine ⟨Y, hYf, ?_⟩
    have e : R4TupleForms.finTupleEquiv s₀ Y = TupleLists.toList ⟨n, Yt m⟩ := Subtype.ext hY
    show TupleLists.ofList _ = _
    rw [e, TupleLists.ofList_toList]
  set e : ℕ → ℝ := fun m => ∑ i, sharpNormR4 F.M (b m i - g i) with he
  have het : Tendsto e atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun i _ => hbt i
    rw [Finset.sum_const_zero] at this
    exact this
  obtain ⟨b₀, hb₀⟩ := het.bddAbove_range
  have heb : ∀ m, e m ≤ b₀ := fun m => hb₀ ⟨m, rfl⟩
  have hnn : ∀ f : SeparatedTuples.RealValued, 0 ≤ sharpNormR4 F.M f := sharpNormR4_nonneg _
  have hen : ∀ m, 0 ≤ e m := fun m => Finset.sum_nonneg fun i _ => hnn _
  set S : ℝ := ∑ i, sharpNormR4 F.M (g i) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hnn _
  have hgS : ∀ i, sharpNormR4 F.M (g i) ≤ S := fun i =>
    Finset.single_le_sum (f := fun i => sharpNormR4 F.M (g i)) (fun i _ => hnn _) (Finset.mem_univ i)
  set Bd : ℝ := S + b₀ with hBd
  have hb0 : 0 ≤ b₀ := (hen 0).trans (heb 0)
  have hdi : ∀ m i, sharpNormR4 F.M (b m i - g i) ≤ e m := fun m i =>
    Finset.single_le_sum (f := fun i => sharpNormR4 F.M (b m i - g i)) (fun i _ => hnn _)
      (Finset.mem_univ i)
  have hxB : ∀ m i, sharpNormR4 F.M (b m i) ≤ Bd := fun m i => by
    have ht : sharpNormR4 F.M ((b m i - g i) + g i) ≤
        sharpNormR4 F.M (b m i - g i) + sharpNormR4 F.M (g i) :=
      hN.2.2.2 (b m i - g i) (hV _ (Wv.sub_mem (hmemV _ (hbmem m i)) (hmemV _ (hmemg i)))) (g i)
        (hV _ (hmemV _ (hmemg i)))
    rw [sub_add_cancel] at ht
    linarith [hgS i, heb m, hdi m i]
  have hyB : ∀ i, sharpNormR4 F.M (g i) ≤ Bd := fun i => by linarith [hgS i]
  have hdB : ∀ m i, sharpNormR4 F.M (b m i - g i) ≤ Bd := fun m i => by
    linarith [hdi m i, heb m]
  have hball : ∀ i, ∃ c, O i ⊆ closedBallR4 c R := fun i => ⟨0, fun x hx => by
    show TorusMetric.euclidNormVec (x - 0) ≤ R
    rw [sub_zero]
    exact h₃ i x hx⟩
  have hsep : ∀ i l, i ≠ l → ENNReal.ofReal δ ≤ setDistR4 (O i) (O l) := fun i l hil =>
    le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal (h₂ i l hil x hx y hy)
  have hclosed : ∀ m, ∀ s : MomentHull Q, |s.eval ⟨n, Yt m⟩ - s.eval (TupleLists.ofList Xl)| ≤
      |momentWeight N n δ R| * (e m * Bd ^ (n - 1)) := fun m s => by
    refine MomentHull.closure_induction (P := fun s => |s ⟨n, Yt m⟩ - s (TupleLists.ofList Xl)| ≤
      |momentWeight N n δ R| * (e m * Bd ^ (n - 1))) ?_ (fun j ρ hρ => ?_) s
    · have hcc : Continuous fun s : TestSpaces.SepTuple → ℝ => |s ⟨n, Yt m⟩ - s (TupleLists.ofList Xl)| :=
        ((continuous_apply (⟨n, Yt m⟩ : TestSpaces.SepTuple)).sub (continuous_apply (TupleLists.ofList Xl))).abs
      exact isClosed_le hcc continuous_const
    · exact abs_momentIn_sub_le B hMC hM hρ (Yt m) (TupleLists.ofList Xl).2 (fun i => hbs m i) (fun i => hKO i) hδ hR
        hball hsep (by linarith) (hxB m) hyB (hdB m)
  have hlim : Tendsto (fun m => |momentWeight N n δ R| * (e m * Bd ^ (n - 1))) atTop (𝓝 0) := by
    simpa using (het.mul_const (Bd ^ (n - 1))).const_mul |momentWeight N n δ R|
  have hconv : ∀ s : MomentHull Q, Tendsto (fun m => s.eval ⟨n, Yt m⟩) atTop
      (𝓝 (s.eval (TupleLists.ofList Xl))) :=
    fun s => tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun m => by
      rw [Real.dist_eq]
      exact hclosed m s) hlim)
  refine tendsto_nhds_unique (hconv s) ((hconv s').congr fun m => ?_)
  exact (h _ (hYT m)).symm
include B hMC hM in
private theorem momentHull_metrizable
    (hfam : CanonicalDecomposition.SeparatingTuplesProperties.Claim)
    (hnorm : Continuum.SeparatedFourTuples.SharpNormAndThickenings.Statement)
    (hMone : (1 : ℝ) ≤ F.M) (s₀ : Conventions.StandingParameters) :
    ∃ e : MomentHull Q → (familyTuples s₀ → ℝ), Topology.IsClosedEmbedding e ∧
      (∀ (s : MomentHull Q) (t : familyTuples s₀), e s t = s.eval t.1) ∧
      TopologicalSpace.MetrizableSpace (MomentHull Q) := by
  have hK := compactSpace_momentHull (Q := Q) B hMC hM
  have : Countable (familyTuples s₀) := (familyTuples_countable s₀ hfam).to_subtype
  let e : MomentHull Q → (familyTuples s₀ → ℝ) := fun s t => s.eval t.1
  have hc : Continuous e := continuous_pi fun t => MomentHull.continuous_eval _
  have hi : Function.Injective e := fun s s' hss =>
    ext_of_familyTuples B hMC hM hfam hnorm hMone s₀ fun t ht => congrFun hss ⟨t, ht⟩
  have hemb := hc.isClosedEmbedding hi
  exact ⟨e, hemb, fun _ _ => rfl, hemb.isEmbedding.metrizableSpace⟩
end Space
end SystemsWithFiveBounds
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace WindowLimits
open BoundsOnEverySide LimitTheorem
open ReflectionPositivity (EuclidIsometry pushFn)
private theorem sharpNormR4_pushFn (M : ℝ) (r : EuclidIsometry) (f : (Fin 4 → ℝ) → ℝ) :
    TestFunctions.sharpNormR4 M (pushFn r f) = TestFunctions.sharpNormR4 M f := by
  have hs : Function.Surjective r.symm.toFun := r.symm.bijective_toFun.2
  have e₁ : TestFunctions.uniformNorm (f ∘ r.symm.toFun) = TestFunctions.uniformNorm f :=
    hs.iSup_comp fun x => ‖f x‖
  have hd : ∀ x y, TestFunctions.euclidDistR4 (r.symm.toFun x) (r.symm.toFun y) =
      TestFunctions.euclidDistR4 x y := r.symm.preserves_dist
  have e₂ : TestFunctions.lipConstR4 (f ∘ r.symm.toFun) = TestFunctions.lipConstR4 f := by
    unfold TestFunctions.lipConstR4 TestFunctions.bestLipschitzConstant
    congr 1
    ext C
    refine and_congr_right fun _ => ⟨fun h x y => ?_, fun h x y => ?_⟩
    · obtain ⟨x', rfl⟩ := hs x
      obtain ⟨y', rfl⟩ := hs y
      simpa [hd] using h x' y'
    · simpa [hd] using h (r.symm.toFun x) (r.symm.toFun y)
  simp only [TestFunctions.sharpNormR4, pushFn, e₁, e₂]
section PurePhases
open ReflectionPositivity (Concatenable centredCube posAdicGridPoints functionalSize)
open PeriodicGibbsLimits (toSepTuple)
open TorusMetric (euclidNormVec)
private def onMirrorTuples (σ : SeparatedTuples.TupleFunctional) (X : ReflectionPositivity.Tuple) : ℝ :=
  evalOnMap σ (toSepTuple X)
variable {σ : SeparatedTuples.TupleFunctional}
private theorem isNormalizedFunctional_onMirrorTuples :
    ReflectionPositivity.IsNormalizedFunctional (onMirrorTuples σ) := by
  have h : toSepTuple ReflectionPositivity.nilTuple = TestSpaces.sepTupleNil :=
    TestSpaces.sepTuple_ext _ _ rfl fun k => k.elim0
  rw [ReflectionPositivity.IsNormalizedFunctional, onMirrorTuples, h, evalOnMap,
    TupleLists.toList_sepTupleNil]
  exact σ.map_nil
private def asBorelProb {L : ℕ} {K : ℕ+} {β : ℝ}
    (ν : Measure (GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))))
    (hν : ν ∈ periodicGibbsSet L K β) : GibbsAtFixedSpacing.BorelProb (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)) :=
  ⟨ν, hν.1.1⟩
private theorem centeredProduct_eq_centredProduct (L K : ℕ)
    (ν : GibbsAtFixedSpacing.BorelProb (PeriodicLattice.meshSize L (K : ℤ)))
    (X : ReflectionPositivity.Tuple) (U : ReflectionPositivity.GaugeFieldsAtLevel L K) :
    ReflectionPositivity.centeredProduct L K ν X U =
      CutoffRepresentative.centredProduct L K ν.1 (toSepTuple X) U := by
  have h : ∀ l : List ReflectionPositivity.ScalarField,
      (l.map fun f U => smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν.1).prod U =
        (l.map fun f => smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν.1).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => simp [ih]
  refine (h X.1).trans ?_
  rw [← Fin.prod_univ_fun_getElem]
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p501816 := @centeredProduct_eq_centredProduct
private theorem exists_strictMono_subseq_of_tendsto (K : ℕ+ → ℕ+)
    (hK : Tendsto (fun j => (K j : ℕ)) atTop atTop) :
    ∃ ψ : ℕ+ → ℕ+, StrictMono ψ ∧ StrictMono fun j => K (ψ j) := by
  have hsucc : Tendsto Nat.succPNat atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨(b : ℕ), fun a ha => by
      rw [← PNat.coe_le_coe, Nat.succPNat_coe]
      omega⟩
  obtain ⟨φ, hφ, hKφ⟩ := strictMono_subseq_of_tendsto_atTop (hK.comp hsucc)
  refine ⟨fun j => (φ j.natPred).succPNat, ?_, ?_⟩
  · exact Nat.succPNat_strictMono.comp (hφ.comp PNat.natPred_strictMono)
  · intro i j hij
    have h := hKφ (PNat.natPred_strictMono hij)
    exact PNat.coe_lt_coe _ _ |>.1 h
private structure PureLimitConditions (L : ℕ) (σ : ReflectionPositivity.Tuple → ℝ) : Prop where
  productDefined : ∀ ϖ ∈ posAdicGridPoints L, ∀ X ∈ ReflectionPositivity.tuplesSupportedIn (centredCube ϖ),
    ∀ (μ : Fin 4) (γ : ReflectionPositivity.reflectionGroup),
      Concatenable (ReflectionPositivity.mirrorTuple μ γ X)
        (ReflectionPositivity.translatedTuple ϖ μ γ X)
  clusters : ∀ ϖ ∈ posAdicGridPoints L, ∀ X ∈ ReflectionPositivity.tuplesSupportedIn (centredCube ϖ),
    ∀ Y ∈ ReflectionPositivity.tuplesSupportedIn (centredCube ϖ), ∀ v : Fin 4 → ℝ, 8 * ϖ ≤ euclidNormVec v →
      ∃ h : Concatenable X (ReflectionPositivity.push (EuclidIsometry.translate v) Y),
        |σ (ReflectionPositivity.concat X _ h) - σ X * σ Y| ≤
          32 * SmearingFilter.spectralRateConst * √(functionalSize σ ϖ X) * √(functionalSize σ ϖ Y) *
            (ϖ / euclidNormVec v) ^ 2
end PurePhases
section Sizes
open ReflectionPositivity (Concatenable centredCube posAdicGridPoints functionalSize mirrorTuple translatedTuple
  reflectionGroupIsometry axisReflectionElem)
open TorusMetric (euclidNormVec)
open TestFunctions (closedBallR4 setDistR4)
private theorem functionalSize_le {σ : ReflectionPositivity.Tuple → ℝ} {ϖ b : ℝ} {X : ReflectionPositivity.Tuple}
    (hdef : ∀ (μ : Fin 4) (γ : ReflectionPositivity.reflectionGroup),
      Concatenable (mirrorTuple μ γ X) (translatedTuple ϖ μ γ X))
    (hb : ∀ (μ : Fin 4) (γ : ReflectionPositivity.reflectionGroup)
      (h : Concatenable (mirrorTuple μ γ X) (translatedTuple ϖ μ γ X)),
      σ (ReflectionPositivity.concat _ _ h) ≤ b) : functionalSize σ ϖ X ≤ b := by
  obtain ⟨p, hp⟩ := (ReflectionPositivity.isGreatest_functionalSize σ ϖ X).1
  rw [← hp]
  unfold ReflectionPositivity.mirrorCorrelation
  rw [dif_pos (hdef _ _)]
  exact hb _ _ _
private theorem abs_reflectionGroupIsometry (γ : ReflectionPositivity.reflectionGroup) (z : Fin 4 → ℝ) (μ : Fin 4) :
    |(reflectionGroupIsometry γ).toFun z μ| = |z μ| := by
  obtain ⟨s, hs⟩ := (ReflectionPositivity.mem_reflectionGroup_iff γ.1).1 γ.2
  have e : (reflectionGroupIsometry γ).toFun z = γ.1 z := rfl
  have h1 : |((s μ : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (s μ) with h | h <;> simp [h]
  rw [e, hs, ReflectionPositivity.flipSigns_apply, abs_mul, h1, one_mul]
private theorem abs_reflectionGroupIsometry_symm (γ : ReflectionPositivity.reflectionGroup) (z : Fin 4 → ℝ)
    (μ : Fin 4) : |(reflectionGroupIsometry γ).symm.toFun z μ| = |z μ| := by
  have h := abs_reflectionGroupIsometry γ ((reflectionGroupIsometry γ).symm.toFun z) μ
  rw [EuclidIsometry.toFun_symm] at h
  exact h.symm
private theorem abs_apply_le_maxNorm (x : Fin 4 → ℝ) (μ : Fin 4) : |x μ| ≤ ReflectionPositivity.maxNorm x :=
  Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ μ)
private theorem tsupport_pushFn_subset_ball (r : EuclidIsometry) {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} {R : ℝ}
    (h : tsupport f ⊆ closedBallR4 x R) : tsupport (pushFn r f) ⊆ closedBallR4 (r.toFun x) R := by
  rw [ReflectionPositivity.tsupport_pushFn]
  intro y hy
  have h₁ : euclidNormVec (r.symm.toFun y - x) ≤ R := h hy
  have h₂ := r.preserves_dist (r.symm.toFun y) x
  rw [EuclidIsometry.toFun_symm] at h₂
  show euclidNormVec (y - r.toFun x) ≤ R
  rw [h₂]
  exact h₁
private theorem setDistR4_pushFn (r : EuclidIsometry) {f g : (Fin 4 → ℝ) → ℝ} {d : ℝ}
    (h : ENNReal.ofReal d ≤ setDistR4 (tsupport f) (tsupport g)) :
    ENNReal.ofReal d ≤ setDistR4 (tsupport (pushFn r f)) (tsupport (pushFn r g)) := by
  rw [ReflectionPositivity.tsupport_pushFn, ReflectionPositivity.tsupport_pushFn]
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  have h₁ : ENNReal.ofReal d ≤ ENNReal.ofReal (euclidNormVec (r.symm.toFun x - r.symm.toFun y)) :=
    h.trans ((iInf₂_le (r.symm.toFun x) hx).trans (iInf₂_le (r.symm.toFun y) hy))
  rw [r.symm.preserves_dist] at h₁
  exact h₁
private theorem mirror_translated_separated {ϖ d : ℝ} (hd : 0 < d) (μ : Fin 4)
    (γ : ReflectionPositivity.reflectionGroup)
    {f g : (Fin 4 → ℝ) → ℝ} (hf : tsupport f ⊆ centredCube (ϖ - d / 2)) (hg : tsupport g ⊆ centredCube (ϖ - d / 2)) :
    ENNReal.ofReal d ≤ setDistR4
      (tsupport (pushFn (reflectionGroupIsometry (axisReflectionElem μ)) (pushFn (reflectionGroupIsometry γ) f)))
      (tsupport (pushFn (EuclidIsometry.translate ((2 * ϖ) • PeriodicLattice.coordVec μ))
        (pushFn (reflectionGroupIsometry γ) g))) := by
  simp only [ReflectionPositivity.tsupport_pushFn]
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal ?_
  have hx' : ReflectionPositivity.maxNorm ((reflectionGroupIsometry γ).symm.toFun
      ((reflectionGroupIsometry (axisReflectionElem μ)).symm.toFun x)) < ϖ - d / 2 := hf hx
  have hy' : ReflectionPositivity.maxNorm ((reflectionGroupIsometry γ).symm.toFun
      ((EuclidIsometry.translate ((2 * ϖ) • PeriodicLattice.coordVec μ)).symm.toFun y)) < ϖ - d / 2 := hg hy
  have hxμ : |x μ| < ϖ - d / 2 := by
    have := abs_apply_le_maxNorm ((reflectionGroupIsometry γ).symm.toFun
      ((reflectionGroupIsometry (axisReflectionElem μ)).symm.toFun x)) μ
    rw [abs_reflectionGroupIsometry_symm, abs_reflectionGroupIsometry_symm] at this
    linarith
  have hyμ : |y μ - 2 * ϖ| < ϖ - d / 2 := by
    have := abs_apply_le_maxNorm ((reflectionGroupIsometry γ).symm.toFun
      ((EuclidIsometry.translate ((2 * ϖ) • PeriodicLattice.coordVec μ)).symm.toFun y)) μ
    rw [abs_reflectionGroupIsometry_symm] at this
    have e : (EuclidIsometry.translate ((2 * ϖ) • PeriodicLattice.coordVec μ)).symm.toFun y μ =
        y μ - 2 * ϖ := by
      rw [EuclidIsometry.symm_translate]
      simp [PeriodicLattice.coordVec]
    rw [e] at this
    linarith
  have h₁ := abs_lt.1 hxμ
  have h₂ := abs_lt.1 hyμ
  have h₃ : |(x - y) μ| ≤ euclidNormVec (x - y) := abs_apply_le_euclidNormVec _ μ
  have h₄ : d ≤ |(x - y) μ| := by
    rw [Pi.sub_apply, abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self _)
  linarith
end Sizes
end WindowLimits
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace SystemsWithFiveBounds
open WindowLimits LimitTheorem
section ALimit
variable {F : StatedSideFamily} {N : BoundConstants} (Q : WindowStates F) {σ : SeparatedTuples.TupleFunctional}
private theorem abs_limitValue_le (hMC : Cumulants.MomentCumulantFormula.Claim)
    (hM : SmearedObservablesWellDefined) (B : BoundsHoldAt F N)
    (hσ : Q.HasLimit σ) {n : ℕ} (X : TestSpaces.SepTupleOfCard n) {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (hb : ∀ i, ∃ x, tsupport (X.1 i) ⊆ TestFunctions.closedBallR4 x R)
    (hs : TestFunctions.HasSeparatedSupportsR4 X.1 d) :
    |evalOnMap σ ⟨n, X⟩| ≤ momentWeight N n d R * ∏ i, TestFunctions.sharpNormR4 F.M (X.1 i) := by
  refine le_of_tendsto (hσ ⟨n, X⟩).abs (Eventually.of_forall fun j => ?_)
  exact abs_centredMoment_le B hMC hM (Q.isFirstPassage j) (Q.ρ_state j) (Q.ν_state j) X.1 X.2.1 hd hR hb hs
end ALimit
section PurePhases
open PeriodicGibbsLimits (toSepTuple)
variable {F : StatedSideFamily} (Q : WindowStates F) {σ : SeparatedTuples.TupleFunctional}
private theorem pureLimitProperties
    (hG : ReflectionPositivity.PeriodicGibbs.periodicGibbsTheorem)
    (hE : ReflectionPositivity.ExtremalIffErgodic.ExtremalIffErgodicTheorem)
    (hC : ReflectionPositivity.LimitContinuity.LimitIsContinuous)
    (hP : ReflectionPositivity.LimitPlateaux.LimitPlateauxTheorem)
    (hσ : Q.HasLimit σ) (hpure : ∀ j, Q.ρ j ∈ cutoffExtremalSet F.L (Q.K j) (Q.β j)) :
    PureLimitConditions F.L (onMirrorTuples σ) := by
  have hL := F.admissible
  obtain ⟨ψ, hψ, hK⟩ := exists_strictMono_subseq_of_tendsto Q.K (tendsto_K_coe Q)
  have hψt : Tendsto ψ atTop atTop :=
    hψ.monotone.tendsto_atTop_atTop fun b => ⟨b, hψ.le_apply⟩
  have hβ : ∀ j, 0 < Q.β (ψ j) := fun j => F.pos_of_isFirstPassage _ _ (Q.isFirstPassage _)
  obtain ⟨-, -, hForm⟩ := hG F.L hL
  obtain ⟨ō, hō, hRP, -, -, hlim⟩ := hForm (fun j => Q.K (ψ j)) hK (fun j => Q.β (ψ j)) hβ
    (fun j => asBorelProb (Q.ρ (ψ j)) (Q.ρ_mem _)) (fun j => asBorelProb (Q.ν (ψ j)) (Q.ν_mem _))
    (fun j => Q.ρ_mem _) (fun j => Q.ν_mem _)
  let Bp := (ReflectionPositivity.PeriodicGibbs.plaquetteCentredStates (fun j => Q.K (ψ j)) hK
    (fun j => Q.β (ψ j)) hβ
    (fun j => asBorelProb (Q.ν (ψ j)) (Q.ν_mem _)) (fun j => Q.ν_mem _) ō hō).toSequence
      (fun j => asBorelProb (Q.ρ (ψ j)) (Q.ρ_mem _))
  have hBlim : Bp.HasLimit (onMirrorTuples σ) := (hlim _ isNormalizedFunctional_onMirrorTuples).2 fun X => by
    refine ((hσ (toSepTuple X)).comp hψt).congr fun j => ?_
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    exact (centeredProduct_eq_centredProduct _ _ (asBorelProb (Q.ν (ψ j)) (Q.ν_mem _)) X U).symm
  have hcont : ReflectionPositivity.IsAdmissiblyContinuous (onMirrorTuples σ) :=
    (hC F.L hL.1 hL.2 Bp _ hBlim).2
  have hErg : Bp.IsErgodicSeq :=
    ((hE F.L hL).2.2.1 (fun j => Q.K (ψ j)) hK (fun j => Q.β (ψ j)) hβ
      (fun j => asBorelProb (Q.ρ (ψ j)) (Q.ρ_mem _)) (fun j => asBorelProb (Q.ν (ψ j)) (Q.ν_mem _))
      (fun j => Q.ρ_mem _) (fun j => Q.ν_mem _) ō hō).2 fun j => hpure (ψ j)
  have hPl := hP F.L hL Bp _ hcont hRP hBlim
  have hU := hPl.2 hErg
  refine ⟨fun ϖ hϖ X hX μ γ => (hPl.1 ϖ hϖ X hX X hX).1.products_defined μ γ, ?_⟩
  intro ϖ hϖ X hX Y hY v hv
  obtain ⟨h, b⟩ := (hPl.1 ϖ hϖ X hX Y hY).2.euclid_bound v hv
  refine ⟨h, ?_⟩
  rw [hU.plateau_eq_mul ϖ hϖ X hX Y hY] at b
  exact b
end PurePhases
end SystemsWithFiveBounds
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace WindowLimits
open BoundsOnEverySide LimitTheorem
open ReflectionPositivity (EuclidIsometry pushFn centredCube posAdicGridPoints)
open PeriodicGibbsLimits (toSepTuple)
open TorusMetric (euclidNormVec)
open TestFunctions (closedBallR4 setDistR4 sharpNormR4 HasSeparatedSupportsR4)
private theorem setDistR4_comm (S T : Set (Fin 4 → ℝ)) : setDistR4 S T = setDistR4 T S := by
  unfold setDistR4
  rw [iInf₂_comm]
  refine iInf_congr fun y => iInf_congr fun _ => iInf_congr fun x => iInf_congr fun _ => ?_
  congr 1
  unfold euclidNormVec
  congr 1
  exact Finset.sum_congr rfl fun μ _ => by simp only [Pi.sub_apply]; ring
abbrev _root_.YangMills.SharedProofs.p12154 := @setDistR4_comm
private def asMirrorTuple (X : SeparatedTuples.SepTuple) : ReflectionPositivity.Tuple :=
  ⟨X.1, fun f hf => ⟨(X.2.1 f hf).1, (X.2.1 f hf).2, Set.subset_univ _⟩, X.2.2⟩
private theorem onMirrorTuples_eq {σ : SeparatedTuples.TupleFunctional} (Z : ReflectionPositivity.Tuple)
    (W : SeparatedTuples.SepTuple) (e : Z.1 = W.1) : onMirrorTuples σ Z = σ W := by
  unfold onMirrorTuples evalOnMap
  exact congrArg σ (Subtype.ext ((List.ofFn_get _).trans e))
private theorem supportGapOf_pos (X : SeparatedTuples.SepTuple) : 0 < supportGapOf X :=
  (exists_support_ball_and_gap X).choose_spec.choose_spec.1
private theorem supportRadiusOf_pos (X : SeparatedTuples.SepTuple) : 0 < supportRadiusOf X :=
  (exists_support_ball_and_gap X).choose_spec.choose_spec.2.1
private theorem tsupport_subset_supportBall (X : SeparatedTuples.SepTuple) {f : SeparatedTuples.RealValued}
    (hf : f ∈ X.1) : tsupport f ⊆ closedBallR4 0 (supportRadiusOf X) :=
  (exists_support_ball_and_gap X).choose_spec.choose_spec.2.2.1 f hf
private theorem pairwise_supportGap (X : SeparatedTuples.SepTuple) :
    X.1.Pairwise fun f g => ENNReal.ofReal (supportGapOf X) ≤ setDistR4 (tsupport f) (tsupport g) :=
  (exists_support_ball_and_gap X).choose_spec.choose_spec.2.2.2
private theorem enclosingSideOf_pos (X Y : SeparatedTuples.SepTuple) : 0 < (enclosingSideOf X Y : ℝ) := by
  unfold enclosingSideOf
  positivity
private theorem clusteringRadiusOf_pos (X Y : SeparatedTuples.SepTuple) : 0 < clusteringRadiusOf X Y := by
  unfold clusteringRadiusOf
  have := enclosingSideOf_pos X Y
  positivity
private theorem natCast_mem_posAdicGridPoints {L n : ℕ} (hL : 0 < L) (hn : 0 < n) :
    (n : ℝ) ∈ posAdicGridPoints L := by
  refine ⟨Set.mem_iUnion.2 ⟨0, (n : ℤ), ?_⟩, Set.mem_Ioi.2 (by exact_mod_cast hn)⟩
  simp [PeriodicLattice.meshSize]
private theorem maxNorm_le_euclidNormVec (x : Fin 4 → ℝ) : ReflectionPositivity.maxNorm x ≤ euclidNormVec x :=
  Finset.sup'_le _ _ fun μ _ => abs_apply_le_euclidNormVec x μ
private theorem tsupport_subset_centredCube_left (X Y : SeparatedTuples.SepTuple) {f : SeparatedTuples.RealValued}
    (hf : f ∈ X.1) : tsupport f ⊆ centredCube ((enclosingSideOf X Y : ℝ) - supportGapOf X / 2) := by
  intro x hx
  have h₁ : euclidNormVec (x - 0) ≤ supportRadiusOf X := tsupport_subset_supportBall X hf hx
  rw [sub_zero] at h₁
  have h₂ := Nat.le_ceil (supportRadiusOf X + supportRadiusOf Y + supportGapOf X + supportGapOf Y)
  have hp₁ := supportRadiusOf_pos Y
  have hp₂ := supportGapOf_pos X
  have hp₃ := supportGapOf_pos Y
  show ReflectionPositivity.maxNorm x < _
  have e : ((enclosingSideOf X Y : ℕ) : ℝ) =
      (⌈supportRadiusOf X + supportRadiusOf Y + supportGapOf X + supportGapOf Y⌉₊ : ℝ) + 1 := by
    simp [enclosingSideOf]
  rw [e]
  linarith [maxNorm_le_euclidNormVec x]
private theorem tsupport_subset_centredCube_right (X Y : SeparatedTuples.SepTuple) {f : SeparatedTuples.RealValued}
    (hf : f ∈ Y.1) : tsupport f ⊆ centredCube ((enclosingSideOf X Y : ℝ) - supportGapOf Y / 2) := by
  intro x hx
  have h₁ : euclidNormVec (x - 0) ≤ supportRadiusOf Y := tsupport_subset_supportBall Y hf hx
  rw [sub_zero] at h₁
  have h₂ := Nat.le_ceil (supportRadiusOf X + supportRadiusOf Y + supportGapOf X + supportGapOf Y)
  have hp₁ := supportRadiusOf_pos X
  have hp₂ := supportGapOf_pos X
  have hp₃ := supportGapOf_pos Y
  show ReflectionPositivity.maxNorm x < _
  have e : ((enclosingSideOf X Y : ℕ) : ℝ) =
      (⌈supportRadiusOf X + supportRadiusOf Y + supportGapOf X + supportGapOf Y⌉₊ : ℝ) + 1 := by
    simp [enclosingSideOf]
  rw [e]
  linarith [maxNorm_le_euclidNormVec x]
end WindowLimits
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace SystemsWithFiveBounds
open WindowLimits LimitTheorem
open ReflectionPositivity (EuclidIsometry pushFn Concatenable centredCube posAdicGridPoints functionalSize
  mirrorTuple translatedTuple reflectionGroupIsometry axisReflectionElem)
open PeriodicGibbsLimits (toSepTuple)
open TorusMetric (euclidNormVec)
open TestFunctions (closedBallR4 setDistR4 sharpNormR4 HasSeparatedSupportsR4)
section Sizes
variable {F : StatedSideFamily} {N : BoundConstants} (Q : WindowStates F) {σ : SeparatedTuples.TupleFunctional}
set_option maxHeartbeats 1600000 in
private theorem limitValue_concat_le (hMC : Cumulants.MomentCumulantFormula.Claim)
    (hM : SmearedObservablesWellDefined) (B : BoundsHoldAt F N)
    (hσ : Q.HasLimit σ) (X : SeparatedTuples.SepTuple) {ϖ : ℝ}
    (hcube : ∀ f ∈ X.1, tsupport f ⊆ centredCube (ϖ - supportGapOf X / 2)) (μ : Fin 4)
    (γ : ReflectionPositivity.reflectionGroup)
    (h : Concatenable (mirrorTuple μ γ (asMirrorTuple X)) (translatedTuple ϖ μ γ (asMirrorTuple X))) :
    onMirrorTuples σ (ReflectionPositivity.concat _ _ h) ≤ sizeWeight F.M N X := by
  set Z := ReflectionPositivity.concat _ _ h with hZ
  set a : SeparatedTuples.RealValued → SeparatedTuples.RealValued := fun f =>
    pushFn (reflectionGroupIsometry (axisReflectionElem μ)) (pushFn (reflectionGroupIsometry γ) f) with ha
  set b : SeparatedTuples.RealValued → SeparatedTuples.RealValued := fun f =>
    pushFn (EuclidIsometry.translate ((2 * ϖ) • PeriodicLattice.coordVec μ))
      (pushFn (reflectionGroupIsometry γ) f) with hb
  have hval : Z.1 = X.1.map a ++ X.1.map b := by
    simp [hZ, ReflectionPositivity.concat, mirrorTuple, translatedTuple, ReflectionPositivity.push, asMirrorTuple,
      List.map_map, ha, hb, Function.comp_def]
  have hlen : Z.1.length = X.1.length + X.1.length := by simp [hval]
  have hd := supportGapOf_pos X
  have hR := supportRadiusOf_pos X
  have hball : ∀ g ∈ Z.1, ∃ c, tsupport g ⊆ closedBallR4 c (supportRadiusOf X) := by
    intro g hg
    rw [hval] at hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
      exact ⟨_, tsupport_pushFn_subset_ball _ (tsupport_pushFn_subset_ball _ (tsupport_subset_supportBall X hf))⟩
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
      exact ⟨_, tsupport_pushFn_subset_ball _ (tsupport_pushFn_subset_ball _ (tsupport_subset_supportBall X hf))⟩
  have hsepZ : Z.1.Pairwise fun f g => ENNReal.ofReal (supportGapOf X) ≤ setDistR4 (tsupport f) (tsupport g) := by
    rw [hval]
    refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
    · exact List.pairwise_map.2 ((pairwise_supportGap X).imp fun hfg =>
        setDistR4_pushFn _ (setDistR4_pushFn _ hfg))
    · exact List.pairwise_map.2 ((pairwise_supportGap X).imp fun hfg =>
        setDistR4_pushFn _ (setDistR4_pushFn _ hfg))
    · intro g hg g' hg'
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
      obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hg'
      exact mirror_translated_separated hd μ γ (hcube f hf) (hcube f' hf')
  have hs : HasSeparatedSupportsR4 (toSepTuple Z).2.1 (supportGapOf X) := by
    refine ⟨hd, fun i k hik => ?_⟩
    rcases lt_or_gt_of_ne hik with hlt | hlt
    · exact List.pairwise_iff_get.1 hsepZ i k hlt
    · rw [setDistR4_comm]
      exact List.pairwise_iff_get.1 hsepZ k i hlt
  have hv := abs_limitValue_le Q hMC hM B hσ (toSepTuple Z).2 hd hR
    (fun i => hball _ (List.get_mem _ _)) hs
  have hprod : ∏ i, sharpNormR4 F.M ((toSepTuple Z).2.1 i) =
      ((X.1.map (sharpNormR4 F.M)).prod) ^ 2 := by
    have e₁ : ∏ i, sharpNormR4 F.M ((toSepTuple Z).2.1 i) =
        (Z.1.map (sharpNormR4 F.M)).prod := Fin.prod_univ_fun_getElem _ _
    have e₂ : (sharpNormR4 F.M) ∘ a = sharpNormR4 F.M := by
      funext f
      simp only [Function.comp, ha, sharpNormR4_pushFn]
    have e₃ : (sharpNormR4 F.M) ∘ b = sharpNormR4 F.M := by
      funext f
      simp only [Function.comp, hb, sharpNormR4_pushFn]
    rw [e₁, hval, List.map_append, List.prod_append, List.map_map, List.map_map, e₂, e₃, sq]
  have hn : (toSepTuple Z).1 = X.1.length + X.1.length := hlen
  rw [hprod] at hv
  have hle : evalOnMap σ ⟨(toSepTuple Z).1, (toSepTuple Z).2⟩ ≤ _ := (le_abs_self _).trans hv
  refine hle.trans ?_
  rw [hn]
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
private theorem functionalSize_le_sizeWeight (hMC : Cumulants.MomentCumulantFormula.Claim)
    (hM : SmearedObservablesWellDefined) (B : BoundsHoldAt F N)
    (hσ : Q.HasLimit σ) (X : SeparatedTuples.SepTuple) {ϖ : ℝ}
    (hcube : ∀ f ∈ X.1, tsupport f ⊆ centredCube (ϖ - supportGapOf X / 2))
    (hdef : ∀ (μ : Fin 4) (γ : ReflectionPositivity.reflectionGroup),
      Concatenable (mirrorTuple μ γ (asMirrorTuple X)) (translatedTuple ϖ μ γ (asMirrorTuple X))) :
    functionalSize (onMirrorTuples σ) ϖ (asMirrorTuple X) ≤ sizeWeight F.M N X :=
  functionalSize_le hdef fun μ γ h => limitValue_concat_le Q hMC hM B hσ X hcube μ γ h
private theorem cluster_of_extremal (hG : ReflectionPositivity.PeriodicGibbs.periodicGibbsTheorem)
    (hE : ReflectionPositivity.ExtremalIffErgodic.ExtremalIffErgodicTheorem)
    (hC : ReflectionPositivity.LimitContinuity.LimitIsContinuous)
    (hP : ReflectionPositivity.LimitPlateaux.LimitPlateauxTheorem)
    (hMC : Cumulants.MomentCumulantFormula.Claim)
    (hM : SmearedObservablesWellDefined) (B : BoundsHoldAt F N)
    (hσ : Q.HasLimit σ) (hpure : ∀ j, Q.ρ j ∈ cutoffExtremalSet F.L (Q.K j) (Q.β j))
    (X Y : SeparatedTuples.SepTuple) (v : Fin 4 → ℝ)
    (hv : clusteringRadiusOf X Y ≤ euclidNormVec v) :
    SeparatedTuples.SepTuple.Composable X (SeparatedTuples.push (SeparatedTuples.translate v) Y) ∧
      |σ (SeparatedTuples.SepTuple.juxt X (SeparatedTuples.push (SeparatedTuples.translate v) Y)) - σ X * σ Y| ≤
        clusteringConstOf F.M N X Y * (euclidNormVec v ^ 2)⁻¹ := by
  have cl := pureLimitProperties Q hG hE hC hP hσ hpure
  set ϖ : ℝ := (enclosingSideOf X Y : ℝ) with hϖ
  have hL0 : 0 < F.L := lt_of_lt_of_le (by norm_num : 0 < 13) F.admissible.2
  have hpos : 0 < enclosingSideOf X Y := by
    unfold enclosingSideOf
    omega
  have hmem : ϖ ∈ posAdicGridPoints F.L := natCast_mem_posAdicGridPoints hL0 hpos
  have hdX := supportGapOf_pos X
  have hdY := supportGapOf_pos Y
  have hX : asMirrorTuple X ∈ ReflectionPositivity.tuplesSupportedIn (centredCube ϖ) := fun f hf x hx => by
    have h₁ : ReflectionPositivity.maxNorm x < ϖ - supportGapOf X / 2 := tsupport_subset_centredCube_left X Y hf hx
    show ReflectionPositivity.maxNorm x < ϖ
    linarith
  have hY : asMirrorTuple Y ∈ ReflectionPositivity.tuplesSupportedIn (centredCube ϖ) := fun f hf x hx => by
    have h₁ : ReflectionPositivity.maxNorm x < ϖ - supportGapOf Y / 2 := tsupport_subset_centredCube_right X Y hf hx
    show ReflectionPositivity.maxNorm x < ϖ
    linarith
  obtain ⟨h, b⟩ := cl.clusters ϖ hmem _ hX _ hY v hv
  have hact : (SeparatedTuples.push (SeparatedTuples.translate v) Y).1 =
      (ReflectionPositivity.push (EuclidIsometry.translate v) (asMirrorTuple Y)).1 := by
    rw [SeparatedTuples.push_translate_val, SeparatedTuples.pushList_translate,
      ReflectionPositivity.push_translate]
    rfl
  have hprod : SeparatedTuples.SepTuple.Composable X (SeparatedTuples.push (SeparatedTuples.translate v) Y) :=
    fun f hf g hg => h f hf g (hact ▸ hg)
  refine ⟨hprod, ?_⟩
  have e₁ : onMirrorTuples σ (ReflectionPositivity.concat _ _ h) =
      σ (SeparatedTuples.SepTuple.juxt X (SeparatedTuples.push (SeparatedTuples.translate v) Y)) :=
    onMirrorTuples_eq _ _ (by
      rw [SeparatedTuples.SepTuple.juxt_val hprod, hact]
      rfl)
  have e₂ : onMirrorTuples σ (asMirrorTuple X) = σ X := onMirrorTuples_eq _ _ rfl
  have e₃ : onMirrorTuples σ (asMirrorTuple Y) = σ Y := onMirrorTuples_eq _ _ rfl
  rw [e₁, e₂, e₃] at b
  refine b.trans ?_
  have hNX := functionalSize_le_sizeWeight Q hMC hM B hσ X
    (fun f hf => tsupport_subset_centredCube_left X Y hf) (cl.productDefined ϖ hmem _ hX)
  have hNY := functionalSize_le_sizeWeight Q hMC hM B hσ Y
    (fun f hf => tsupport_subset_centredCube_right X Y hf) (cl.productDefined ϖ hmem _ hY)
  have hv0 : 0 < euclidNormVec v := lt_of_lt_of_le (clusteringRadiusOf_pos X Y) hv
  have hsq : (ϖ / euclidNormVec v) ^ 2 = ϖ ^ 2 * (euclidNormVec v ^ 2)⁻¹ := by
    rw [div_pow, div_eq_mul_inv]
  rw [hsq]
  have hinv : 0 ≤ (euclidNormVec v ^ 2)⁻¹ := by positivity
  unfold clusteringConstOf
  have hA : 32 * SmearingFilter.spectralRateConst * √(functionalSize (onMirrorTuples σ) ϖ (asMirrorTuple X)) *
        √(functionalSize (onMirrorTuples σ) ϖ (asMirrorTuple Y)) * ϖ ^ 2 ≤
      1 + 32 * |SmearingFilter.spectralRateConst| * ϖ ^ 2 * √(sizeWeight F.M N X) *
        √(sizeWeight F.M N Y) := by
    have s₁ := Real.sqrt_le_sqrt hNX
    have s₂ := Real.sqrt_le_sqrt hNY
    have s₃ := le_abs_self SmearingFilter.spectralRateConst
    have n₁ := Real.sqrt_nonneg (functionalSize (onMirrorTuples σ) ϖ (asMirrorTuple X))
    have n₂ := Real.sqrt_nonneg (functionalSize (onMirrorTuples σ) ϖ (asMirrorTuple Y))
    have step : SmearingFilter.spectralRateConst *
          (√(functionalSize (onMirrorTuples σ) ϖ (asMirrorTuple X)) *
            √(functionalSize (onMirrorTuples σ) ϖ (asMirrorTuple Y))) ≤
        |SmearingFilter.spectralRateConst| *
          (√(sizeWeight F.M N X) * √(sizeWeight F.M N Y)) :=
      mul_le_mul s₃ (mul_le_mul s₁ s₂ n₂ (Real.sqrt_nonneg _)) (mul_nonneg n₁ n₂) (abs_nonneg _)
    have hp2 : 0 ≤ 32 * ϖ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left step hp2]
  calc _ = (32 * SmearingFilter.spectralRateConst * √(functionalSize (onMirrorTuples σ) ϖ (asMirrorTuple X)) *
        √(functionalSize (onMirrorTuples σ) ϖ (asMirrorTuple Y)) * ϖ ^ 2) *
          (euclidNormVec v ^ 2)⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hA hinv
end Sizes
end SystemsWithFiveBounds
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace WindowLimits
open BoundsOnEverySide TestFunctions LimitTheorem
private theorem restrictToTestTuples_connectedFamilyOf (s₀ : Conventions.StandingParameters)
    (σ : TestSpaces.SepTuple → ℝ) (n : ℕ) (hn : 2 ≤ n) (X : TestSpaces.SepTupleOfCard n) :
    TestSpaces.cumulant σ X =
      LimitGrowthFromCutoffBound.restrictToTestTuples (connectedFamilyOf s₀ σ) n hn X := rfl
end WindowLimits
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace SystemsWithFiveBounds
open WindowLimits TestFunctions LimitTheorem
section ALimit
variable {F : StatedSideFamily} {N : BoundConstants} (Q : WindowStates F) {σ : SeparatedTuples.TupleFunctional}
private theorem tendsToFamily_of_hasLimit
    (hInh : GibbsLimitInheritance.InheritanceTheorem) (hσ : Q.HasLimit σ) :
    BoundsOnEverySide.GibbsStateSequence.TendsToFamily Q.toGibbsStateSequence
      (connectedFamilyOf (standingParamsOfFamily F) (evalOnMap σ)) := by
  obtain ⟨hA, -⟩ := (hInh.1 F.L F.admissible F.M 0 Q.K Q.ρ Q.ν σ (fun j => (Q.ρ_mem j).1.1) hσ)
  intro n hn f
  exact hA.2 n hn ⟨f.1, (AmbientPoints.mem_separatedTuples_r4_iff f.1).1 f.2⟩
private theorem growthBound_of_hasLimit (hG : FunctionalGrowthAtConstants)
    (hInh : GibbsLimitInheritance.InheritanceTheorem)
    (B : BoundsHoldAt F N) (hσ : Q.HasLimit σ)
    (hf : TestSpaces.IsSepFunctional (evalOnMap σ)) {c cBar : ℝ} (hbar : 0 ≤ cBar)
    (hc : ∀ X : TestSpaces.SepTupleOfCard 1, evalOnMap σ ⟨1, X⟩ = c * ∫ x, X.1 0 x) (habs : |c| ≤ cBar) :
    TestSpaces.GrowthBound (growthOrder N)
      (1 + 2 * SeparatedBound.extFactorAbs) (growthConst F.M N cBar)
      (20 + N.factorialExponent) (evalOnMap σ) := by
  have hone : ∀ X : TestSpaces.SepTupleOfCard 1, TestSpaces.cumulant (evalOnMap σ) X = c * ∫ u, X.1 0 u :=
    fun X => (TestSpaces.cumulant_single _ X).trans (hc X)
  exact hG F N B (standingParamsOfFamily F) (connectedFamilyOf (standingParamsOfFamily F) (evalOnMap σ))
    Q.toGibbsStateSequence Q.isFirstPassage Q.ρ_state
    (tendsToFamily_of_hasLimit Q hInh hσ) (evalOnMap σ) c cBar hbar hf hone habs
    (restrictToTestTuples_connectedFamilyOf (standingParamsOfFamily F) (evalOnMap σ))
end ALimit
end SystemsWithFiveBounds
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology ENNReal
namespace WindowLimits
section Triple
private theorem tendsto_natPred_atTop : Tendsto PNat.natPred atTop atTop := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicExtensions.tendsto_pnatNatPred_atTop <;> assumption
private theorem tendsto_succPNat_atTop : Tendsto Nat.succPNat atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨(b : ℕ), fun a ha => by
    rw [← PNat.coe_le_coe, Nat.succPNat_coe]
    omega⟩
abbrev _root_.YangMills.SharedProofs.p14344 := @tendsto_succPNat_atTop
end Triple
end WindowLimits
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology ENNReal
namespace SystemsWithFiveBounds
open WindowLimits TestFunctions LimitTheorem
section Decomposition
variable {F : StatedSideFamily} (Q : WindowStates F)
private structure ExtremalDecomposition (j : ℕ+) where
  κ : GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)) →
    Measure (GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)))
  V : Set (GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)))
  measurableSet : MeasurableSet V
  measure_V : Q.ν j V = 1
  isProbability : ∀ U, IsProbabilityMeasure (κ U)
  pure : ∀ U ∈ V, κ U ∈ cutoffExtremalSet F.L (Q.K j) (Q.β j)
  state : ∀ U ∈ V, κ U ∈ F.stateSet F.L (Q.K j) (Q.β j)
  measurable : ∀ G : GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)) → ℂ, IsBoundedObservable G →
    Measurable fun U => ∫ x, G x ∂κ U
  integral_eq : ∀ G : GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)) → ℂ, IsBoundedObservable G →
    ∫ x, G x ∂Q.ν j = ∫ U, (∫ x, G x ∂κ U) ∂Q.ν j
private def latticeSetupAt (j : ℕ+) : LatticePhases.Setup :=
  ⟨F.L, F.admissible, Q.K j, Q.β j, F.pos_of_isFirstPassage _ _ (Q.isFirstPassage j)⟩
private theorem nonempty_extremalDecomposition
    (hT : LatticePhases.InvariantConditionalFamilies.Statement)
    (hErg : LatticePhases.AlmostEveryConditionalIsErgodic)
    (hPE : ReflectionPositivity.ExtremalIffErgodic.ExtremalIffErgodicTheorem)
    (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j)) (j : ℕ+) :
    Nonempty (ExtremalDecomposition Q j) := by
  let νD : periodicGibbsSet (latticeSetupAt Q j).L (latticeSetupAt Q j).K (latticeSetupAt Q j).β := ⟨Q.ν j, Q.ν_mem j⟩
  obtain ⟨κ, hκ⟩ := (hT (latticeSetupAt Q j) νD).2.1
  obtain ⟨h₁, h₂, h₃⟩ := hErg (latticeSetupAt Q j) νD κ hκ
  let Pst : GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)) → Prop :=
    fun U => (κ U).toMeasure ∈ F.stateSet F.L (Q.K j) (Q.β j)
  have hst : ∀ᵐ U ∂Q.ν j, Pst U :=
    F.ergodicComponents_mem (Q.K j) (Q.β j) (Q.isFirstPassage j) (F.pos_of_isFirstPassage _ _ (Q.isFirstPassage j))
      νD (hvol j) κ hκ
  obtain ⟨t, ht, hmt, hnull⟩ := exists_measurable_superset_of_null (ae_iff.1 hst)
  let W : Set (GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ))) :=
    LatticePhases.ergodicConditionalLocus (latticeSetupAt Q j) κ
  have hW : MeasurableSet W := h₁.1
  have hνp : IsProbabilityMeasure (Q.ν j) := (Q.ν_mem j).1.1
  have hW₁ : Q.ν j W = 1 := h₂
  have hm : MeasurableSet (W ∩ tᶜ) := hW.inter hmt.compl
  have hV : Q.ν j (W ∩ tᶜ) = 1 := by
    refine (prob_compl_eq_zero_iff hm).1 ?_
    rw [Set.compl_inter, compl_compl]
    exact measure_union_null ((prob_compl_eq_zero_iff hW).2 hW₁) hnull
  exact ⟨⟨fun U => (κ U).toMeasure, _, hm, hV, fun U => (κ U).2,
    fun U hU => (hPE F.L F.admissible).2.1 (Q.K j) (Q.β j) (F.pos_of_isFirstPassage _ _ (Q.isFirstPassage j)) _
      (h₃ U hU.1).1 (h₃ U hU.1).2.2.2.2,
    fun U hU => by
      by_contra hn
      exact hU.2 (ht hn),
    fun G hG => (hκ G hG).1.mono (fun I hI => hI.1) le_rfl,
    fun G hG => (hT (latticeSetupAt Q j) νD).2.2.2 κ hκ G hG⟩⟩
private theorem isBoundedObservable_centredProduct (hM : SmearedObservablesWellDefined)
    (j : ℕ+) (X : TestSpaces.SepTuple) :
    IsBoundedObservable (fun U : GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)) =>
      ((CutoffRepresentative.centredProduct F.L (Q.K j) (Q.ν j) X U : ℝ) : ℂ)) := by
  have ha := mesh_pos F.admissible Q.toCutoffCouplingSequence j
  have hb : ∀ i, Measurable (fun U : GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)) =>
      smearedEnergy (X.2.1 i) U - ∫ V, smearedEnergy (X.2.1 i) V ∂Q.ν j) ∧
      ∃ C, ∀ U : GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ)),
        |smearedEnergy (X.2.1 i) U - ∫ V, smearedEnergy (X.2.1 i) V ∂Q.ν j| ≤ C := fun i => by
    obtain ⟨hm, C, hC⟩ := ((hM _ ha).1 (X.2.1 i) (mem_compactTestFunctions_of_c1 (X.2.2.1 i))).2
    refine ⟨hm.sub measurable_const, C + |∫ V, smearedEnergy (X.2.1 i) V ∂Q.ν j|, fun U => ?_⟩
    exact (abs_sub _ _).trans (by linarith [hC U])
  choose hm C hC using hb
  refine ⟨Complex.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ => hm i), ∏ i, C i, fun U => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  show |∏ i, (smearedEnergy (X.2.1 i) U - ∫ V, smearedEnergy (X.2.1 i) V ∂Q.ν j)| ≤ _
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => hC i U
variable {Q} {j : ℕ+} (D : ExtremalDecomposition Q j)
open Classical in
private def ExtremalDecomposition.hullPoint (U : GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ))) :
    MomentHull Q :=
  if h : U ∈ D.V then
    ⟨momentIn Q j (D.κ U), subset_closure ⟨j, D.κ U, D.state U h, rfl⟩⟩
  else ⟨momentIn Q j (Q.ν j), subset_closure ⟨j, Q.ν j, Q.ν_state j, rfl⟩⟩
private theorem ExtremalDecomposition.eval_hullPoint_of_mem
    {U : GaugeField (PeriodicLattice.meshSize F.L ((Q.K j : ℕ) : ℤ))}
    (h : U ∈ D.V) (X : TestSpaces.SepTuple) : (D.hullPoint U).eval X = momentIn Q j (D.κ U) X := by
  simp [ExtremalDecomposition.hullPoint, h, MomentHull.eval]
private theorem ExtremalDecomposition.measurable_momentIn
    (hM : SmearedObservablesWellDefined) (X : TestSpaces.SepTuple) :
    Measurable fun U => momentIn Q j (D.κ U) X := by
  have h := D.measurable _ (isBoundedObservable_centredProduct Q hM j X)
  have e : (fun U => momentIn Q j (D.κ U) X) = fun U => (∫ x,
      ((CutoffRepresentative.centredProduct F.L (Q.K j) (Q.ν j) X x : ℝ) : ℂ) ∂D.κ U).re := by
    funext U
    rw [integral_complex_ofReal, Complex.ofReal_re]
    rfl
  rw [e]
  exact Complex.measurable_re.comp h
private theorem ExtremalDecomposition.measurable_eval_hullPoint
    (hM : SmearedObservablesWellDefined) (X : TestSpaces.SepTuple) :
    Measurable fun U => (D.hullPoint U).eval X := by
  classical
  have e : (fun U => (D.hullPoint U).eval X) =
      D.V.piecewise (fun U => momentIn Q j (D.κ U) X) (fun _ => momentIn Q j (Q.ν j) X) := by
    funext U
    by_cases h : U ∈ D.V
    · simp [ExtremalDecomposition.hullPoint, h, MomentHull.eval, Set.piecewise]
    · simp [ExtremalDecomposition.hullPoint, h, MomentHull.eval, Set.piecewise]
  rw [e]
  exact (D.measurable_momentIn hM X).piecewise D.measurableSet measurable_const
private theorem ExtremalDecomposition.integral_eval_hullPoint
    (hM : SmearedObservablesWellDefined) (X : TestSpaces.SepTuple) :
    ∫ U, (D.hullPoint U).eval X ∂Q.ν j = momentIn Q j (Q.ν j) X := by
  have hν : IsProbabilityMeasure (Q.ν j) := (Q.ν_mem j).1.1
  have hae : ∀ᵐ U ∂Q.ν j, U ∈ D.V :=
    (prob_compl_eq_zero_iff D.measurableSet).2 D.measure_V
  have e₁ : ∫ U, (D.hullPoint U).eval X ∂Q.ν j = ∫ U, momentIn Q j (D.κ U) X ∂Q.ν j :=
    integral_congr_ae (hae.mono fun U h => D.eval_hullPoint_of_mem h X)
  have e₂ := D.integral_eq _ (isBoundedObservable_centredProduct Q hM j X)
  have e₃ : ∀ U, ∫ x, ((CutoffRepresentative.centredProduct F.L (Q.K j) (Q.ν j) X x : ℝ) : ℂ) ∂D.κ U =
      ((momentIn Q j (D.κ U) X : ℝ) : ℂ) := fun U => integral_complex_ofReal
  simp only [e₃] at e₂
  rw [integral_complex_ofReal, integral_complex_ofReal] at e₂
  rw [e₁]
  exact (Complex.ofReal_injective e₂).symm
end Decomposition
section Triple
variable {F : StatedSideFamily} {N : BoundConstants} {Q : WindowStates F} (B : BoundsHoldAt F N)
private theorem eval_nil (s : MomentHull Q) : s.eval (TupleLists.ofList SeparatedTuples.SepTuple.nil) = 1 := by
  refine MomentHull.closure_induction (P := fun s => s (TupleLists.ofList SeparatedTuples.SepTuple.nil) = 1)
    (isClosed_eq (continuous_apply _) continuous_const) (fun j ρ hρ => ?_) s
  have hp : IsProbabilityMeasure ρ := (F.stateSet_subset _ _ (Q.isFirstPassage j) hρ).1.1
  have e : ∀ U, CutoffRepresentative.centredProduct F.L (Q.K j) (Q.ν j)
      (TupleLists.ofList SeparatedTuples.SepTuple.nil) U = 1 := fun U => by
    have : IsEmpty (Fin (TupleLists.ofList SeparatedTuples.SepTuple.nil).1) := inferInstanceAs (IsEmpty (Fin 0))
    exact Fintype.prod_empty _
  show ∫ U, CutoffRepresentative.centredProduct F.L (Q.K j) (Q.ν j)
    (TupleLists.ofList SeparatedTuples.SepTuple.nil) U ∂ρ = 1
  simp [e]
include B in
private theorem exists_decompositionTriple (hMC : Cumulants.MomentCumulantFormula.Claim)
    (hM : SmearedObservablesWellDefined)
    (hfam : CanonicalDecomposition.SeparatingTuplesProperties.Claim)
    (hnorm : Continuum.SeparatedFourTuples.SharpNormAndThickenings.Statement)
    (hT : LatticePhases.InvariantConditionalFamilies.Statement)
    (hErg : LatticePhases.AlmostEveryConditionalIsErgodic)
    (hPE : ReflectionPositivity.ExtremalIffErgodic.ExtremalIffErgodicTheorem)
    (hSup : Measures.SupportFullMeasureAndL2Rank)
    (s₀ : Conventions.StandingParameters) {σ : SeparatedTuples.TupleFunctional} (hρν : Q.ρ = Q.ν)
    (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j)) (hσ : Q.HasLimit σ) :
    ∃ Tr : CanonicalDecomposition.DecompositionTriple,
      CompactSpace Tr.space ∧ TopologicalSpace.MetrizableSpace Tr.space ∧
      IsProbabilityMeasure Tr.law ∧ (∀ O : Set Tr.space, IsOpen O → O.Nonempty → 0 < Tr.law O) ∧
      (∀ X, Continuous fun ξ => Tr.comp ξ X) ∧ Function.Injective Tr.comp ∧
      (∀ X, evalOnMap σ X = ∫ ξ, Tr.comp ξ X ∂Tr.law) ∧
      ∀ ξ, ∃ (τ : SeparatedTuples.TupleFunctional) (Q' : WindowStates F), evalOnMap τ = Tr.comp ξ ∧ Q'.HasLimit τ ∧
        ∀ j, Q'.ρ j ∈ cutoffExtremalSet F.L (Q'.K j) (Q'.β j) := by
  classical
  have hK := compactSpace_momentHull (Q := Q) B hMC hM
  obtain ⟨e, he, hev, hmet⟩ := momentHull_metrizable (Q := Q) B hMC hM hfam hnorm F.one_le_M s₀
  haveI := hmet
  haveI : Countable (familyTuples s₀) := (familyTuples_countable s₀ hfam).to_subtype
  let D := fun j => (nonempty_extremalDecomposition Q hT hErg hPE hvol j).some
  have hmeas : ∀ j, Measurable (D j).hullPoint := fun j => by
    refine he.measurableEmbedding.measurable_comp_iff.1 ?_
    refine measurable_pi_iff.2 fun t => ?_
    have : (fun U => e ((D j).hullPoint U) t) = fun U => ((D j).hullPoint U).eval t.1 :=
      funext fun U => hev _ t
    simpa [Function.comp_def, this] using (D j).measurable_eval_hullPoint hM t.1
  have hνp : ∀ j, IsProbabilityMeasure (Q.ν j) := fun j => (Q.ν_mem j).1.1
  let μ : ℕ+ → ProbabilityMeasure (MomentHull Q) := fun j =>
    ⟨(Q.ν j).map (D j).hullPoint, Measure.isProbabilityMeasure_map (hmeas j).aemeasurable⟩
  obtain ⟨m, ϕ, hϕ, hconv⟩ := CompactSpace.tendsto_subseq (fun n : ℕ => μ n.succPNat)
  set mm : Measure (MomentHull Q) := (m : Measure (MomentHull Q)) with hmm
  haveI : IsProbabilityMeasure mm := m.2
  have hsucc : Tendsto (fun n => (ϕ n).succPNat) atTop atTop :=
    tendsto_succPNat_atTop.comp hϕ.tendsto_atTop
  have hint : ∀ X, Tendsto (fun n => momentIn Q (ϕ n).succPNat (Q.ν _) X) atTop (𝓝 (∫ s, s.eval X ∂mm)) := by
    intro X
    have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv)
      (BoundedContinuousFunction.mkOfCompact ⟨fun s => s.eval X, MomentHull.continuous_eval X⟩)
    refine hf.congr fun n => ?_
    show ∫ s, s.eval X ∂((Q.ν _).map (D _).hullPoint) = _
    rw [integral_map (hmeas _).aemeasurable (MomentHull.continuous_eval X).aestronglyMeasurable]
    exact (D _).integral_eval_hullPoint hM X
  have hmean : ∀ X, evalOnMap σ X = ∫ s, s.eval X ∂mm := fun X => by
    have e₁ : ∀ j, Q.toCutoffCouplingSequence.pairedValue Q.ρ Q.ν j X = momentIn Q j (Q.ν j) X := fun j => by
      show ∫ U, CutoffRepresentative.centredProduct F.L (Q.K j) (Q.ν j) X U ∂Q.ρ j = _
      rw [hρν]
      rfl
    exact tendsto_nhds_unique (((hσ X).comp hsucc).congr fun n => e₁ _) (hint X)
  letI := TopologicalSpace.metrizableSpaceMetric (MomentHull Q)
  obtain ⟨⟨hcl, hfull⟩, -⟩ := hSup (MomentHull Q) mm
  set Xs := Measures.probabilitySupport mm with hXs
  have hXm : MeasurableSet Xs := hcl.measurableSet
  have hae : ∀ᵐ s ∂mm, s ∈ Xs := by
    have : mm Xsᶜ = 0 := (prob_compl_eq_zero_iff hXm).2 hfull
    exact this
  have hrestrict : mm.restrict Xs = mm := Measure.restrict_eq_self_of_ae_mem hae
  refine ⟨CanonicalDecomposition.DecompositionTriple.mk (space := ↥Xs) (law := Measure.comap Subtype.val mm)
    (comp := fun ξ X => ξ.1.eval X), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isCompact_iff_compactSpace.1 hcl.isCompact
  · exact inferInstanceAs (TopologicalSpace.MetrizableSpace ↥Xs)
  · refine ⟨?_⟩
    show Measure.comap Subtype.val mm Set.univ = 1
    rw [comap_subtype_coe_apply hXm]
    simpa using hfull
  · intro O hO ⟨ξ, hξ⟩
    obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 hO
    show 0 < Measure.comap Subtype.val mm (Subtype.val ⁻¹' O')
    rw [comap_subtype_coe_apply hXm, Subtype.image_preimage_coe]
    have h₁ : 0 < mm O' := ξ.2 O' hO' hξ
    have h₂ : mm (Xs ∩ O') = mm O' :=
      measure_congr (eventuallyEq_set.2 (hae.mono fun s hs => ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩))
    rw [h₂]
    exact h₁
  · intro X
    exact (MomentHull.continuous_eval X).comp continuous_subtype_val
  · intro ξ ξ' h
    exact Subtype.ext (Subtype.ext (funext fun X => congrFun h X))
  · intro X
    rw [hmean X]
    show _ = ∫ ξ : ↥Xs, (ξ.1 : MomentHull Q).eval X ∂Measure.comap Subtype.val mm
    rw [integral_subtype_comap hXm fun s : MomentHull Q => s.eval X, hrestrict]
  · intro ξ
    have hξ : ξ.1 ∈ Xs := ξ.2
    obtain ⟨N, hN⟩ := (𝓝 ξ.1).exists_antitone_basis
    have hpos : ∀ l, 0 < mm (interior (N l)) := fun l =>
      hξ _ isOpen_interior (mem_interior_iff_mem_nhds.2 (hN.mem l))
    have hfreq : ∀ l, ∃ᶠ k in atTop,
        0 < ((μ (ϕ k).succPNat : ProbabilityMeasure _) : Measure _) (interior (N l)) := by
      intro l
      have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv (isOpen_interior (s := N l))
      exact (eventually_lt_of_lt_liminf (lt_of_lt_of_le (hpos l) h)).frequently
    obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_frequently hfreq
    let jj : ℕ → ℕ+ := fun l => (ϕ (φ l)).succPNat
    have hU : ∀ l, ∃ U, U ∈ (D (jj l)).V ∧ (D (jj l)).hullPoint U ∈ interior (N l) := fun l => by
      have h₁ := hP l
      change 0 < ((Q.ν (jj l)).map (D (jj l)).hullPoint) (interior (N l)) at h₁
      rw [Measure.map_apply (hmeas _) isOpen_interior.measurableSet] at h₁
      by_contra hcon
      push Not at hcon
      have hsub : (D (jj l)).hullPoint ⁻¹' interior (N l) ⊆ (D (jj l)).Vᶜ := fun U hU hV => hcon U hV hU
      have h0 : Q.ν (jj l) (D (jj l)).Vᶜ = 0 :=
        (prob_compl_eq_zero_iff (D (jj l)).measurableSet).2 (D (jj l)).measure_V
      exact absurd (measure_mono_null hsub h0) h₁.ne'
    choose U hUV hUN using hU
    have hs : Tendsto (fun l => (D (jj l)).hullPoint (U l)) atTop (𝓝 ξ.1) :=
      hN.tendsto fun l => interior_subset (hUN l)
    have hjj : Tendsto jj atTop atTop := hsucc.comp hφ.tendsto_atTop
    let Q' : WindowStates F :=
      { K := fun p => Q.K (jj p.natPred)
        tendsto_K := Q.tendsto_K.comp (hjj.comp tendsto_natPred_atTop)
        β := fun p => Q.β (jj p.natPred)
        isFirstPassage := fun p => Q.isFirstPassage _
        ρ := fun p => (D (jj p.natPred)).κ (U p.natPred)
        ν := fun p => Q.ν (jj p.natPred)
        ρ_mem := fun p => ((D _).pure _ (hUV _)).1
        ν_mem := fun p => Q.ν_mem _
        ρ_state := fun p => (D _).state _ (hUV _)
        ν_state := fun p => Q.ν_state _ }
    let τ : SeparatedTuples.TupleFunctional := ⟨fun X => ξ.1.eval (TupleLists.ofList X), eval_nil _⟩
    have hτ : ∀ X, evalOnMap τ X = ξ.1.eval X := fun X => by
      show ξ.1.eval (TupleLists.ofList (TupleLists.toList X)) = _
      rw [TupleLists.ofList_toList]
    refine ⟨τ, Q', funext hτ, fun X => ?_, fun p => (D _).pure _ (hUV _)⟩
    rw [hτ]
    have hc := (((MomentHull.continuous_eval (Q := Q) X).tendsto ξ.1).comp hs).comp tendsto_natPred_atTop
    refine hc.congr fun p => ?_
    exact (D _).eval_hullPoint_of_mem (hUV _) X
end Triple
end SystemsWithFiveBounds
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace WindowLimits
open TorusMetric (euclidNormVec)
private theorem tupleFunctional_ext {σ τ : SeparatedTuples.TupleFunctional} (h : ∀ Y, σ Y = τ Y) : σ = τ := by apply _root_.YangMills.SharedProofs.p5793 <;> assumption
open BoundsOnEverySide TestFunctions LimitTheorem
private theorem evalOnMap_ofList (τ : SeparatedTuples.TupleFunctional) (W : SeparatedTuples.SepTuple) :
    evalOnMap τ (TupleLists.ofList W) = τ W := by
  unfold evalOnMap
  rw [TupleLists.toList_ofList]
abbrev _root_.YangMills.SharedProofs.p25328 := @evalOnMap_ofList
private theorem apply_eq_of_perm {τ : SeparatedTuples.TupleFunctional} (h : τ.IsPermInvariant)
    {A B : SeparatedTuples.SepTuple} (hp : A.1.Perm B.1) : τ A = τ B := by
  obtain ⟨e, he⟩ := ClusterMoments.exists_finEquiv_of_perm hp
  have hlen := hp.length_eq
  let ς : Equiv.Perm (Fin A.1.length) := e.trans (finCongr hlen.symm)
  have hB : A.reorder ς.symm = B := by
    refine Subtype.ext (List.ext_getElem (by simp [SeparatedTuples.SepTuple.reorder, hlen]) fun i h₁ h₂ => ?_)
    have hi : i < A.1.length := hlen ▸ h₂
    have e₁ : e (ς.symm ⟨i, hi⟩) = ⟨i, h₂⟩ := by
      exact Fin.ext (show ((e (ς.symm ⟨i, hi⟩) : Fin B.1.length) : ℕ) = i from
        congrArg Fin.val (ς.apply_symm_apply ⟨i, hi⟩))
    have e₂ : (A.reorder ς.symm).1[i] = A.1.get (ς.symm ⟨i, hi⟩) := by
      simp [SeparatedTuples.SepTuple.reorder]
    rw [e₂, he, e₁]
    rfl
  rw [← hB]
  exact (h A _).symm
private theorem isPermutationInvariant_evalOnMap {τ : SeparatedTuples.TupleFunctional} (h : τ.IsPermInvariant) :
    WightmanReconstruction.IsPermutationInvariant (evalOnMap τ) := by
  intro n _ X ς
  refine apply_eq_of_perm h ?_
  exact show (List.ofFn (X.1 ∘ ς)).Perm (List.ofFn X.1) from Equiv.Perm.ofFn_comp_perm ς X.1
abbrev _root_.YangMills.SharedProofs.p108250 := @isPermutationInvariant_evalOnMap
section Canonical
variable {S : CumulantFamily}
private theorem evalOnMap_centredOf (S : CumulantFamily) (X : TestSpaces.SepTuple) :
    evalOnMap (centredOf S) X = TestSpaces.centredOfCumulants S X := by apply _root_.YangMills.SharedProofs.p13412 <;> assumption
private theorem tendsto_mul_inv_sq_atInfinity (c : ℝ) :
    Tendsto (fun v : Fin 4 → ℝ => c * (euclidNormVec v ^ 2)⁻¹) SeparatedTuples.atInfinity (𝓝 0) := by
  have h₁ : Tendsto euclidNormVec SeparatedTuples.atInfinity atTop := tendsto_comap
  have h₂ := (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp h₁)).const_mul c
  simpa using h₂
end Canonical
end WindowLimits
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
namespace SystemsWithFiveBounds
open TorusMetric (euclidNormVec)
open WindowLimits TestFunctions LimitTheorem
private structure Inputs : Prop where
  formed : SmearedObservablesWellDefined
  momentCumulant : Cumulants.MomentCumulantFormula.Claim
  separating : CanonicalDecomposition.SeparatingTuplesProperties.Claim
  sharp : Continuum.SeparatedFourTuples.SharpNormAndThickenings.Statement
  inherit : GibbsLimitInheritance.InheritanceTheorem
  growth : FunctionalGrowthAtConstants
  onePoint : OnePointLimitWithConstants
  periodicGibbs : ReflectionPositivity.PeriodicGibbs.periodicGibbsTheorem
  extremalErgodic : ReflectionPositivity.ExtremalIffErgodic.ExtremalIffErgodicTheorem
  continuous : ReflectionPositivity.LimitContinuity.LimitIsContinuous
  plateaux : ReflectionPositivity.LimitPlateaux.LimitPlateauxTheorem
  conditional : LatticePhases.InvariantConditionalFamilies.Statement
  ergodic : LatticePhases.AlmostEveryConditionalIsErgodic
  support : Measures.SupportFullMeasureAndL2Rank
  moments : ClusterMoments.IteratedLimitIsMoment
  maps : LimitTheorem.DecompositionOnListsAndMaps.ListAndMapFormsAgree
  determines : CanonicalDecompositionUniqueness.DecompositionDeterminations
  limit : WindowLimitConditions
section ALimit
variable {F : StatedSideFamily} {N : BoundConstants} (P : Inputs) (B : BoundsHoldAt F N) (Q : WindowStates F)
  {σ : SeparatedTuples.TupleFunctional}
include P B in
private theorem exists_onePointConst (hσ : Q.HasLimit σ) :
    ∃ c : ℝ, (∀ X : TestSpaces.SepTupleOfCard 1, evalOnMap σ ⟨1, X⟩ = c * ∫ x, X.1 0 x) ∧
      |c| ≤ unitBallBound F.M N := by
  obtain ⟨c, hc⟩ := (P.limit.limit_conditions Q hσ).onePoint_eq
  exact ⟨c, hc, abs_onePointConst_le Q P.formed P.onePoint B hσ hc⟩
include P in
private theorem isSepFunctional_of_hasLimit (hσ : Q.HasLimit σ) : TestSpaces.IsSepFunctional (evalOnMap σ) :=
  (P.limit.limit_conditions Q hσ).isSepFunctional
include P in
private theorem limitSymmetries_of_hasLimit (hσ : Q.HasLimit σ) : LimitSymmetries σ :=
  (P.limit.limit_conditions Q hσ).symmetries
include P B in
private theorem growthBound_of_limit (hσ : Q.HasLimit σ) :
    TestSpaces.GrowthBound (growthOrder N)
      (1 + 2 * SeparatedBound.extFactorAbs)
      (growthConst F.M N (unitBallBound F.M N)) (20 + N.factorialExponent) (evalOnMap σ) := by
  obtain ⟨c, hc, habs⟩ := exists_onePointConst P B Q hσ
  exact growthBound_of_hasLimit Q P.growth P.inherit B hσ (isSepFunctional_of_hasLimit P Q hσ)
    ((abs_nonneg _).trans habs) hc habs
include P B in
private theorem cluster_of_extremal_at (hσ : Q.HasLimit σ)
    (hpure : ∀ j, Q.ρ j ∈ cutoffExtremalSet F.L (Q.K j) (Q.β j))
    (X Y : SeparatedTuples.SepTuple) (v : Fin 4 → ℝ) (hv : clusteringRadiusOf X Y ≤ euclidNormVec v) :
    SeparatedTuples.SepTuple.Composable X (SeparatedTuples.push (SeparatedTuples.translate v) Y) ∧
      |σ (SeparatedTuples.SepTuple.juxt X (SeparatedTuples.push (SeparatedTuples.translate v) Y)) - σ X * σ Y| ≤
        clusteringConstOf F.M N X Y * (euclidNormVec v ^ 2)⁻¹ :=
  cluster_of_extremal Q P.periodicGibbs P.extremalErgodic P.continuous P.plateaux P.momentCumulant P.formed B hσ
    hpure X Y v hv
end ALimit
section Canonical
variable {F : StatedSideFamily} {N : BoundConstants} (P : Inputs) (B : BoundsHoldAt F N) {Q : WindowStates F}
  {S : CumulantFamily}
include P B in
private theorem exists_canonical_decompositionTriple (hρν : Q.ρ = Q.ν)
    (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j)) (hσ : Q.HasLimit (centredOf S)) :
    ∃ Tr : CanonicalDecomposition.DecompositionTriple, Tr.IsCanonical S ∧
      ∀ ξ, ∃ (τ : SeparatedTuples.TupleFunctional) (Q' : WindowStates F),
        evalOnMap τ = Tr.comp ξ ∧ Q'.HasLimit τ ∧ ∀ j, Q'.ρ j ∈ cutoffExtremalSet F.L (Q'.K j) (Q'.β j) := by
  obtain ⟨Tr, hcpt, hmet, hpr, hpos, hcont, hinj, hmean, hcomp⟩ :=
    exists_decompositionTriple B P.momentCumulant P.formed P.separating P.sharp P.conditional P.ergodic
      P.extremalErgodic P.support (standingParamsOfFamily F) hρν hvol hσ
  refine ⟨Tr, ?_, hcomp⟩
  have hfunc : ∀ ξ, TestSpaces.IsSepFunctional (Tr.comp ξ) := fun ξ => by
    obtain ⟨τ, Q', e, hl, -⟩ := hcomp ξ
    rw [← e]
    exact isSepFunctional_of_hasLimit P Q' hl
  have hsym : ∀ ξ, WightmanReconstruction.IsPermutationInvariant (Tr.comp ξ) := fun ξ => by
    obtain ⟨τ, Q', e, hl, -⟩ := hcomp ξ
    rw [← e]
    exact isPermutationInvariant_evalOnMap (limitSymmetries_of_hasLimit P Q' hl).isPermInvariant
  have hfac : ClusterMoments.ClusterFactorises Tr.comp := by
    intro Y Z
    refine ⟨fun v => clusteringConstOf F.M N Y Z * (euclidNormVec v ^ 2)⁻¹, tendsto_mul_inv_sq_atInfinity _, ?_⟩
    have hfar : ∀ᶠ v in SeparatedTuples.atInfinity, clusteringRadiusOf Y Z ≤ euclidNormVec v :=
      (tendsto_comap (f := euclidNormVec) (x := atTop)).eventually (eventually_ge_atTop _)
    filter_upwards [hfar] with v hv ξ
    obtain ⟨τ, Q', e, hl, hp⟩ := hcomp ξ
    rw [← e, evalOnMap_ofList, evalOnMap_ofList, evalOnMap_ofList]
    exact (cluster_of_extremal_at P B Q' hl hp Y Z v hv).2
  have hmean' : ∀ X, TestSpaces.centredOfCumulants S X = ∫ ξ, Tr.comp ξ X ∂Tr.law := fun X => by
    rw [← evalOnMap_centredOf]
    exact hmean X
  have hM := fun X Y => P.moments Tr.space Tr.law Tr.comp (TestSpaces.centredOfCumulants S)
    hcont hsym hmean' hfac X Y
  refine ⟨hcpt, hmet, hpr, ?_, hfunc, hsym, hcont, hinj, fun X Y => (hM X Y).1, fun X Y => (hM X Y).2⟩
  refine Set.eq_univ_of_forall fun y O hO hy => hpos O hO ⟨y, hy⟩
include P B in
private theorem exists_canonical_decompositionData (hρν : Q.ρ = Q.ν)
    (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j)) (hσ : Q.HasLimit (centredOf S)) :
    ∃ Bt : SeparatedTuples.DecompositionData, Bt.IsCanonical (centredOf S) ∧
      ∀ ξ, ∃ Q' : WindowStates F, Q'.HasLimit (Bt.comp ξ) ∧
        ∀ j, Q'.ρ j ∈ cutoffExtremalSet F.L (Q'.K j) (Q'.β j) := by
  obtain ⟨Tr, hTr, hcomp⟩ := exists_canonical_decompositionTriple P B hρν hvol hσ
  refine ⟨DecompositionOnListsAndMaps.listData Tr fun ξ => (hTr.comp_isSepFunctional ξ).1,
    (P.maps.1 S _).2 ?_, fun ξ => ?_⟩
  · rw [P.maps.2.1 S Tr hTr]
    exact hTr
  · obtain ⟨τ, Q', e, hl, hp⟩ := hcomp ξ
    have hτ : (DecompositionOnListsAndMaps.listData Tr fun ξ => (hTr.comp_isSepFunctional ξ).1).comp ξ = τ :=
      tupleFunctional_ext fun Y => by
        show Tr.comp ξ (TupleLists.ofList Y) = τ Y
        rw [← e, evalOnMap_ofList]
    exact ⟨Q', hτ ▸ hl, hp⟩
include P B in
private theorem exists_windowStates_of_component (hρν : Q.ρ = Q.ν)
    (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j)) (hσ : Q.HasLimit (centredOf S))
    {A' : SeparatedTuples.DecompositionData} (hA : A'.IsCanonical (centredOf S)) (ξ : A'.space) :
    ∃ Q' : WindowStates F, Q'.HasLimit (A'.comp ξ) ∧
      ∀ j, Q'.ρ j ∈ cutoffExtremalSet F.L (Q'.K j) (Q'.β j) := by
  obtain ⟨Bt, hB, hcomp⟩ := exists_canonical_decompositionData P B hρν hvol hσ
  have := (P.determines (centredOf S)).2.1 A' Bt hA hB
  obtain ⟨ζ, hζ⟩ : A'.comp ξ ∈ Set.range Bt.comp := this ▸ ⟨ξ, rfl⟩
  rw [← hζ]
  exact hcomp ζ
end Canonical
end SystemsWithFiveBounds
end
namespace SystemsWithFiveBounds
open LimitTheorem
theorem canonicalDecompositionOfLimits_holds
    (h1 : WindowLimitProperties)
    (h2 : PeriodicGibbsLimits.ObservablesAndMomentsDefined.Statement)
    (h3 : Cumulants.MomentCumulantFormula.Claim)
    (h4 : CanonicalDecomposition.SeparatingTuplesProperties.Claim)
    (h5 : Continuum.SeparatedFourTuples.SharpNormAndThickenings.Statement)
    (h6 : GibbsLimitInheritance.InheritanceTheorem)
    (h7 : FunctionalGrowthAtConstants)
    (h8 : OnePointLimitWithConstants)
    (h9 : ReflectionPositivity.PeriodicGibbs.periodicGibbsTheorem)
    (h10 : ReflectionPositivity.ExtremalIffErgodic.ExtremalIffErgodicTheorem)
    (h11 : ReflectionPositivity.LimitContinuity.LimitIsContinuous)
    (h12 : ReflectionPositivity.LimitPlateaux.LimitPlateauxTheorem)
    (h13 : LatticePhases.InvariantConditionalFamilies.Statement)
    (h14 : LatticePhases.AlmostEveryConditionalIsErgodic)
    (h15 : Measures.SupportFullMeasureAndL2Rank)
    (h16 : ClusterMoments.IteratedLimitIsMoment)
    (h17 : LimitTheorem.DecompositionOnListsAndMaps.ListAndMapFormsAgree)
    (h18 : CanonicalDecompositionUniqueness.DecompositionDeterminations) :
    CanonicalDecompositionOfLimits :=
  have P : Inputs :=
    { formed := smearedObservablesWellDefined_of h2, momentCumulant := h3, separating := h4,
      sharp := h5, inherit := h6, growth := h7, onePoint := h8, periodicGibbs := h9,
      extremalErgodic := h10, continuous := h11, plateaux := h12, conditional := h13,
      ergodic := h14, support := h15, moments := h16, maps := h17, determines := h18, limit := h1 }
  show CanonicalDecompositionConditions from
  { growth_bound := fun B Q _ hσ => growthBound_of_limit P B Q hσ
    cluster_law := fun B Q _ hσ hpure X Y v hv => cluster_of_extremal_at P B Q hσ hpure X Y v hv
    exists_canonical_decomposition := fun B _ _ hρν hvol hσ => exists_canonical_decompositionData P B hρν hvol hσ
    exists_states_of_component := fun B _ _ hρν hvol hσ _ hA ξ =>
      exists_windowStates_of_component P B hρν hvol hσ hA ξ }
end SystemsWithFiveBounds
end YangMills.Construction
end
