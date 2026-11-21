import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Lattice.CovarianceOfComplexAverages
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActionsProof
import YangMills.Construction.Lattice.PositiveOneOfABondAndItsReverse
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometries
import YangMills.Construction.Towers.DilationCarriesObjectsAtAStepOfASideProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.ComplexAveragesCommuteWithIsometries
section Values
variable {L m : ℕ} {j j' : ℤ}
theorem isRelativelyOpen_of_local {E : Type} [TopologicalSpace E] {P D : Set E} (hD : D ⊆ P)
    (h : ∀ x ∈ D, ∃ N : Set E, IsOpen N ∧ x ∈ N ∧ N ∩ P ⊆ D) : ComplexMatrix2.IsRelativelyOpen P D := by
  refine ⟨⋃₀ {N | IsOpen N ∧ N ∩ P ⊆ D}, isOpen_sUnion fun N hN => hN.1, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨N, hN, hxN, hs⟩ := h x hx
    exact ⟨⟨N, ⟨hN, hs⟩, hxN⟩, hD hx⟩
  · rintro ⟨⟨N, hN, hxN⟩, hxP⟩
    exact hN.2 ⟨hxN, hxP⟩
theorem holomorphicOnFields_data {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P D : Set (Bond L m j → ComplexMatrix2)} {ℬ : Set (Bond L m j)} [inst : Fintype ↥ℬ]
    {f : (Bond L m j → ComplexMatrix2) → E} (h : IsAnalyticOnSupport P ℬ D f) :
    D ⊆ P ∧ ComplexMatrix2.IsRelativelyOpen (restrictToBonds ℬ '' P) (restrictToBonds ℬ '' D) ∧
      ∀ U ∈ D, ∃ F : (↥ℬ → ComplexMatrix2) → E, AnalyticAt ℂ F (restrictToBonds ℬ U) ∧
        ∀ᶠ w in 𝓝 (restrictToBonds ℬ U), ∀ W ∈ D, restrictToBonds ℬ W = w → f W = F w := by
  obtain ⟨i, h⟩ := h
  obtain rfl := Subsingleton.elim i inst
  exact h
theorem holomorphicOnFields_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P D : Set (Bond L m j → ComplexMatrix2)} {ℬ : Set (Bond L m j)}
    {f g : (Bond L m j → ComplexMatrix2) → E}
    (h : IsAnalyticOnSupport P ℬ D f) (hfg : ∀ U ∈ D, g U = f U) :
    IsAnalyticOnSupport P ℬ D g := by
  obtain ⟨i, hDP, hD, hf⟩ := h
  refine ⟨i, hDP, hD, fun U hU => ?_⟩
  obtain ⟨F, hF, hev⟩ := hf U hU
  exact ⟨F, hF, hev.mono fun w hw W hW e => (hfg W hW).trans (hw W hW e)⟩
structure HolomorphicFieldFamily (ℬ : Set (Bond L m j))
    (Φ : (Bond L m j → ComplexMatrix2) → PartialGaugeField L m j') : Prop where
  determined : ∀ U W, restrictToBonds ℬ U = restrictToBonds ℬ W →
    (Φ U).support = (Φ W).support ∧ ∀ b ∈ (Φ U).support, (Φ U).field b = (Φ W).field b
  reversalClosed : ∀ U, IsReversalClosed (Φ U).support
  gaugeField : ∀ U ∈ complexGaugeFields ℬ,
    IsGaugeField complexGaugeGroup (Φ U).support (Φ U).field
  holomorphic : ∀ c, IsAnalyticOnSupport (complexGaugeFields ℬ) ℬ
    {U ∈ complexGaugeFields ℬ | c ∈ (Φ U).support} fun U => (Φ U).field c
theorem holomorphicFamily_id {ℬ : Set (Bond L m j)} [Fintype ↥ℬ] (hℬ : IsReversalClosed ℬ) :
    HolomorphicFieldFamily ℬ fun U => (⟨ℬ, U⟩ : PartialGaugeField L m j) := by
  refine ⟨fun U W h => ⟨rfl, fun b hb => congrFun h ⟨b, hb⟩⟩, fun _ => hℬ, fun U hU => hU,
    fun c => ?_⟩
  by_cases hc : c ∈ ℬ
  · have e : {U ∈ complexGaugeFields ℬ |
        c ∈ (⟨ℬ, U⟩ : PartialGaugeField L m j).support} = complexGaugeFields ℬ :=
      sep_eq_self_iff_mem_true.2 fun _ _ => hc
    rw [e]
    refine IsHolomorphicOnFields.of_analytic_formula (fun w => w ⟨c, hc⟩) subset_rfl
      (isRelativelyOpen_self _) (fun U _ => ?_) fun U _ => rfl
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ↥ℬ => ComplexMatrix2) ⟨c, hc⟩).analyticAt _
  · have e : {U ∈ complexGaugeFields ℬ |
        c ∈ (⟨ℬ, U⟩ : PartialGaugeField L m j).support} = ∅ :=
      sep_eq_empty_iff_mem_false.2 fun _ _ => hc
    rw [e]
    refine ⟨inferInstance, empty_subset _, ⟨∅, isOpen_empty, by simp⟩, fun U hU => absurd hU ?_⟩
    simp
end Values
section Step
variable {L m K n : ℕ}
theorem isReversalClosed_bondsInDoubleBlock {j j' : ℤ} (c : Bond L m j) :
    IsReversalClosed (bondsInDoubleBlock c : Set (Bond L m j')) :=
  fun _ hb => ⟨hb.2, hb.1⟩
structure LatticeHypotheses (L m K : ℕ) : Prop where
  admissible : Conventions.IsAdmissibleBlockingFactor L
  m_pos : 0 < m
  schemes : AveragingSchemeProperties
  orientation : PositiveOrientationOfBondAndOpposite
  dichotomy : BondOrientationDichotomy
  locality : ComplexAverageIsLocal
theorem LatticeHypotheses.opposite_isPositivelyOriented (S : LatticeHypotheses L m K) {n : ℕ}
    (hn : n ≤ K) {b : BondAtLevel L m K n} (hb : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by
  have hd : -(m : ℤ) < levelDepth K n := by
    have := S.m_pos
    simp only [levelDepth]
    omega
  rcases S.dichotomy L m S.admissible S.m_pos _ hd b with h | h
  · exact absurd h.1 hb
  · exact h.1
theorem LatticeHypotheses.extendFromPositive_restrict (S : LatticeHypotheses L m K) {n : ℕ}
    (hn : n ≤ K) {P : Set (BondAtLevel L m K n)} (hP : IsReversalClosed P)
    {W : BondAtLevel L m K n → ComplexMatrix2}
    (hW : IsGaugeField complexGaugeGroup P W) {b : BondAtLevel L m K n} (hb : b ∈ P) :
    extendFromPositive P (restrictToPositive P W) b = W b := by
  by_cases hp : b.IsPositivelyOriented
  · have h : b ∈ P ∧ b.IsPositivelyOriented := ⟨hb, hp⟩
    simp only [extendFromPositive, dif_pos h, restrictToPositive]
  · have h : ¬(b ∈ P ∧ b.IsPositivelyOriented) := fun t => hp t.2
    have h' : b.opposite ∈ P ∧ b.opposite.IsPositivelyOriented :=
      ⟨hP b hb, S.opposite_isPositivelyOriented hn hp⟩
    simp only [extendFromPositive, dif_neg h, dif_pos h', restrictToPositive]
    have hrr : b.opposite.opposite = b := Bond.ext rfl rfl
    have e := hW.2 _ h'.1
    rw [hrr] at e
    exact e.symm
theorem isGaugeField_extendByOne {j : ℤ} {P S : Set (Bond L m j)}
    (hP : IsReversalClosed P) (hPS : P ⊆ S) {V : Bond L m j → ComplexMatrix2}
    (hV : IsGaugeField complexGaugeGroup S V) :
    IsGaugeField complexGaugeGroup P (onSetElseOne P V) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · simp only [onSetElseOne, if_pos hb]
    exact hV.1 b (hPS hb)
  · simp only [onSetElseOne, if_pos hb, if_pos (hP b hb)]
    exact hV.2 b (hPS hb)
theorem LatticeHypotheses.centred_average_on_restrictions (S : LatticeHypotheses L m K) (hn : n < K)
    (d : BondAtLevel L m K (n + 1)) (hd : d.IsPositivelyOriented) [inst₀ : Fintype (PositiveBondOf
      (bondsInDoubleBlock d : Set (BondAtLevel L m K n)))] :
    ∃ O : Set (PositiveBondOf (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) → ComplexMatrix2),
      IsOpen O ∧
      restrictToPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) ''
          (complexAveragingDomainNearOne d : Set (BondAtLevel L m K n → ComplexMatrix2)) =
        O ∩ (ComplexMatrix2.complexifiedProduct fun _ => ComplexMatrix2.FactorKind.group) ∧
      ∀ v ∈ restrictToPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) ''
          (complexAveragingDomainNearOne d : Set (BondAtLevel L m K n → ComplexMatrix2)),
        complexBlockAverageOnPositive
            (extendFromPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) v) d ∈
          complexGaugeGroup ∧
        ∃ G : (PositiveBondOf (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) → ComplexMatrix2) →
            ComplexMatrix2,
          AnalyticAt ℂ G v ∧
          ∀ᶠ y in 𝓝 v, y ∈ restrictToPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) ''
              (complexAveragingDomainNearOne d : Set (BondAtLevel L m K n → ComplexMatrix2)) →
            complexBlockAverageOnPositive
              (extendFromPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) y) d =
              G y := by
  obtain ⟨-, hDom, hMean, -⟩ :=
    (S.schemes L S.admissible m K n S.m_pos hn .centred).2.1 d hd
  have reads := S.locality L m K n S.admissible.1 S.admissible.2 S.m_pos hn d hd
  obtain ⟨O, hO, hOe⟩ := hDom.isOpen
  rw [hMean.domain_eq] at hOe
  obtain ⟨⟨inst, hol⟩, -⟩ := hDom.average_holomorphic
  obtain rfl := Subsingleton.elim inst inst₀
  obtain ⟨-, hmaps, hloc⟩ := hol
  rw [hMean.domain_eq] at hmaps hloc
  have hmem : ∀ v ∈ restrictToPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) ''
      (complexAveragingDomainNearOne d : Set (BondAtLevel L m K n → ComplexMatrix2)),
      extendFromPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) v ∈
        (complexAveragingDomainNearOne d : Set (BondAtLevel L m K n → ComplexMatrix2)) := by
    rintro _ ⟨W, hW, rfl⟩
    exact (reads.mem_domain_iff _ _ fun b hb =>
      S.extendFromPositive_restrict hn.le (isReversalClosed_bondsInDoubleBlock d) hW.1.1 hb).2 hW
  have hval : ∀ v ∈ restrictToPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) ''
      (complexAveragingDomainNearOne d : Set (BondAtLevel L m K n → ComplexMatrix2)),
      schemeBlockAverage .centred (extendFromPositive
          (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) v) d =
        complexBlockAverageOnPositive (extendFromPositive
          (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) v) d := by
    intro v hv
    have h₁ := hMean.average_eq _ (by rw [hMean.domain_eq]; exact hmem v hv)
    rw [h₁, complexBlockAverage, if_pos hd]
  refine ⟨O, hO, hOe, fun v hv => ⟨?_, ?_⟩⟩
  · have t := hmaps hv ()
    rw [← hval v hv]
    exact t
  · obtain ⟨F, hF, hev⟩ := hloc v hv
    refine ⟨fun y => F y (), analyticAt_pi_iff.1 hF (), ?_⟩
    filter_upwards [eventually_nhdsWithin_iff.1 hev] with y hy hyD
    rw [← hval y hyD]
    exact congrFun (hy hyD) ()
end Step
section Family
variable {L m K n : ℕ} {j : ℤ} {ℬ : Set (Bond L m j)} [Fintype ↥ℬ]
  {Φ : (Bond L m j → ComplexMatrix2) → PartialGaugeField L m (levelDepth K n)}
theorem LatticeHypotheses.finite_bond (S : LatticeHypotheses L m K) (j' : ℤ) :
    Finite (Bond L m j') := by
  have hL0 : 0 < L := by
    have := S.admissible.2
    omega
  have : Finite (Site L m j') := SeparatedSequences.BaseParameters.site_finite hL0 m _
  exact Finite.of_injective (fun b : Bond L m j' => (b.source, b.target)) fun b b' hb =>
    Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
theorem LatticeHypotheses.average_eventually (S : LatticeHypotheses L m K) (hn : n < K)
    (d : BondAtLevel L m K (n + 1))
    (hd : d.IsPositivelyOriented) (hΦ : HolomorphicFieldFamily ℬ Φ) {U₀ : Bond L m j → ComplexMatrix2}
    (hU₀ : U₀ ∈ complexGaugeFields ℬ)
    (hP : (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) ⊆ (Φ U₀).support)
    (hdom : onSetElseOne (bondsInDoubleBlock d) (Φ U₀).field ∈
      (complexAveragingDomainNearOne d : Set (BondAtLevel L m K n → ComplexMatrix2))) :
    ∃ G : (↥ℬ → ComplexMatrix2) → ComplexMatrix2, AnalyticAt ℂ G (restrictToBonds ℬ U₀) ∧
      G (restrictToBonds ℬ U₀) ∈ complexGaugeGroup ∧
      ∀ᶠ w in 𝓝 (restrictToBonds ℬ U₀), ∀ U ∈ complexGaugeFields ℬ, restrictToBonds ℬ U = w →
        (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) ⊆ (Φ U).support ∧
        onSetElseOne (bondsInDoubleBlock d) (Φ U).field ∈
          (complexAveragingDomainNearOne d : Set (BondAtLevel L m K n → ComplexMatrix2)) ∧
        complexBlockAverageOnPositive (onSetElseOne (bondsInDoubleBlock d) (Φ U).field) d =
          G w := by
  have := S.finite_bond (levelDepth K n)
  have hclosed := isReversalClosed_bondsInDoubleBlock (j' := levelDepth K n) d
  let _ : Fintype (PositiveBondOf (bondsInDoubleBlock d : Set (BondAtLevel L m K n))) :=
    Fintype.ofFinite _
  have reads := S.locality L m K n S.admissible.1 S.admissible.2 S.m_pos hn d hd
  obtain ⟨O, hO, hOe, hloc⟩ := S.centred_average_on_restrictions hn d hd
  have hv₀ : restrictToPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n))
      (onSetElseOne (bondsInDoubleBlock d) (Φ U₀).field) ∈
      restrictToPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) ''
        (complexAveragingDomainNearOne d : Set (BondAtLevel L m K n → ComplexMatrix2)) :=
    ⟨_, hdom, rfl⟩
  obtain ⟨hgrp, G, hG, hGe⟩ := hloc _ hv₀
  have hv₀O := hv₀
  rw [hOe] at hv₀O
  have hF : ∀ b : PositiveBondOf (bondsInDoubleBlock d : Set (BondAtLevel L m K n)),
      ∃ F : (↥ℬ → ComplexMatrix2) → ComplexMatrix2, AnalyticAt ℂ F (restrictToBonds ℬ U₀) ∧
        F (restrictToBonds ℬ U₀) = (Φ U₀).field b.1 ∧
        ∀ᶠ w in 𝓝 (restrictToBonds ℬ U₀), ∀ U ∈ complexGaugeFields ℬ, restrictToBonds ℬ U = w →
          b.1 ∈ (Φ U).support ∧ (Φ U).field b.1 = F w := by
    intro b
    obtain ⟨-, ⟨Ob, hOb, hOeb⟩, hl⟩ := holomorphicOnFields_data (hΦ.holomorphic b.1)
    have hb₀ : U₀ ∈ {U ∈ complexGaugeFields ℬ | b.1 ∈ (Φ U).support} := ⟨hU₀, hP b.2.1⟩
    obtain ⟨F, hFa, hev⟩ := hl U₀ hb₀
    have hw₀ : restrictToBonds ℬ U₀ ∈ Ob := by
      have t : restrictToBonds ℬ U₀ ∈ restrictToBonds ℬ ''
          {U ∈ complexGaugeFields ℬ | b.1 ∈ (Φ U).support} := ⟨U₀, hb₀, rfl⟩
      rw [hOeb] at t
      exact t.1
    refine ⟨F, hFa, (hev.self_of_nhds U₀ hb₀ rfl).symm, ?_⟩
    filter_upwards [hev, hOb.mem_nhds hw₀] with w hw hwO U hU e
    have t : w ∈ restrictToBonds ℬ '' {U ∈ complexGaugeFields ℬ | b.1 ∈ (Φ U).support} := by
      rw [hOeb]
      exact ⟨hwO, U, hU, e⟩
    obtain ⟨U', hU', e'⟩ := t
    have hbU : b.1 ∈ (Φ U).support := by
      rw [← (hΦ.determined U' U (e'.trans e.symm)).1]
      exact hU'.2
    exact ⟨hbU, hw U ⟨hU, hbU⟩ e⟩
  choose F hFa hF0 hFe using hF
  let H : (↥ℬ → ComplexMatrix2) → PositiveBondOf (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) →
      ComplexMatrix2 :=
    fun w b => F b w
  have hHa : AnalyticAt ℂ H (restrictToBonds ℬ U₀) := analyticAt_pi_iff.2 hFa
  have hH0 : H (restrictToBonds ℬ U₀) = restrictToPositive
      (bondsInDoubleBlock d : Set (BondAtLevel L m K n))
      (onSetElseOne (bondsInDoubleBlock d) (Φ U₀).field) := by
    funext b
    change F b _ = onSetElseOne (bondsInDoubleBlock d) (Φ U₀).field b.1
    rw [hF0 b]
    simp only [onSetElseOne, if_pos b.2.1]
  have hall := Filter.eventually_all.2 hFe
  have hcont := hHa.continuousAt
  have hOev : ∀ᶠ w in 𝓝 (restrictToBonds ℬ U₀), H w ∈ O :=
    hcont.eventually (by rw [hH0]; exact hO.mem_nhds hv₀O.1)
  have hGev : ∀ᶠ w in 𝓝 (restrictToBonds ℬ U₀),
      H w ∈ restrictToPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) ''
          (complexAveragingDomainNearOne d : Set (BondAtLevel L m K n → ComplexMatrix2)) →
        complexBlockAverageOnPositive (extendFromPositive
          (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) (H w)) d = G (H w) :=
    hcont.eventually (by rw [hH0]; exact hGe)
  refine ⟨fun w => G (H w), AnalyticAt.comp (by rw [hH0]; exact hG) hHa, ?_, ?_⟩
  · change G (H _) ∈ complexGaugeGroup
    rw [hH0, ← hGe.self_of_nhds hv₀]
    exact hgrp
  · filter_upwards [hall, hOev, hGev] with w h₁ h₂ h₃ U hU e
    have hPU : (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) ⊆ (Φ U).support := by
      intro b hb
      by_cases hp : b.IsPositivelyOriented
      · exact (h₁ ⟨b, hb, hp⟩ U hU e).1
      · have t := (h₁ ⟨b.opposite, hclosed b hb, S.opposite_isPositivelyOriented hn.le hp⟩ U hU e).1
        have hrr : b.opposite.opposite = b := Bond.ext rfl rfl
        have t' := hΦ.reversalClosed U _ t
        rwa [hrr] at t'
    have hWc := isGaugeField_extendByOne hclosed hPU (hΦ.gaugeField U hU)
    have hHW : H w = restrictToPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n))
        (onSetElseOne (bondsInDoubleBlock d) (Φ U).field) := by
      funext b
      change F b w = onSetElseOne (bondsInDoubleBlock d) (Φ U).field b.1
      simp only [onSetElseOne, if_pos b.2.1]
      exact (h₁ b U hU e).2.symm
    have himg : H w ∈ restrictToPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) ''
        (complexAveragingDomainNearOne d : Set (BondAtLevel L m K n → ComplexMatrix2)) := by
      rw [hOe]
      refine ⟨h₂, fun b => ?_⟩
      rw [hHW]
      exact hWc.1 _ b.2.1
    have hagree : ∀ b ∈ (bondsInDoubleBlock d : Set (BondAtLevel L m K n)),
        extendFromPositive (bondsInDoubleBlock d : Set (BondAtLevel L m K n)) (H w) b =
          onSetElseOne (bondsInDoubleBlock d) (Φ U).field b := fun b hb => by
      rw [hHW]
      exact S.extendFromPositive_restrict hn.le hclosed hWc hb
    obtain ⟨W', hW', e'⟩ := himg
    have hW'agree : ∀ b ∈ (bondsInDoubleBlock d : Set (BondAtLevel L m K n)),
        W' b = onSetElseOne (bondsInDoubleBlock d) (Φ U).field b := fun b hb => by
      rw [← hagree b hb, ← e']
      exact (S.extendFromPositive_restrict hn.le hclosed hW'.1.1 hb).symm
    refine ⟨hPU, (reads.mem_domain_iff _ _ hW'agree).1 hW', ?_⟩
    rw [← reads.average_eq _ _ hagree]
    exact h₃ ⟨W', hW', e'⟩
theorem inv_mem_complexGaugeGroup {g : ComplexMatrix2} (hg : g ∈ complexGaugeGroup) :
    g⁻¹ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
theorem LatticeHypotheses.partialAverage_field (S : LatticeHypotheses L m K) (hn : n < K)
    (V : PartialGaugeField L m (levelDepth K n)) (c : BondAtLevel L m K (n + 1)) :
    (complexPartialBlockAverage V).field c =
      open Classical in
      if c.IsPositivelyOriented then
        complexBlockAverageOnPositive
          (onSetElseOne (bondsInDoubleBlock c.positivelyOriented) V.field) c.positivelyOriented
      else (complexBlockAverageOnPositive
        (onSetElseOne (bondsInDoubleBlock c.positivelyOriented) V.field)
          c.positivelyOriented)⁻¹ := by
  have hK : 0 < K := by omega
  obtain ⟨-, -, -, -, -, -, hP⟩ := S.orientation L m K S.admissible S.m_pos hK n hn c
  change complexBlockAverage (onSetElseOne (bondsInDoubleBlock c) V.field) c = _
  rw [hP]
  by_cases hc : c.IsPositivelyOriented
  · simp only [complexBlockAverage, if_pos hc, Bond.positivelyOriented]
  · simp only [complexBlockAverage, if_neg hc, Bond.positivelyOriented]
theorem LatticeHypotheses.mem_partialAverage_support (S : LatticeHypotheses L m K) (hn : n < K)
    (V : PartialGaugeField L m (levelDepth K n)) (c : BondAtLevel L m K (n + 1)) :
    c ∈ (complexPartialBlockAverage V).support ↔
      (bondsInDoubleBlock c.positivelyOriented : Set (BondAtLevel L m K n)) ⊆ V.support ∧
      onSetElseOne (bondsInDoubleBlock c.positivelyOriented) V.field ∈
        (complexAveragingDomainNearOne c.positivelyOriented :
          Set (BondAtLevel L m K n → ComplexMatrix2)) := by
  have hK : 0 < K := by omega
  obtain ⟨-, -, -, -, -, -, hP⟩ := S.orientation L m K S.admissible S.m_pos hK n hn c
  rw [hP]
  exact Iff.rfl
theorem LatticeHypotheses.holomorphicFamily_average (S : LatticeHypotheses L m K) (hn : n < K)
    (hΦ : HolomorphicFieldFamily ℬ Φ) :
    HolomorphicFieldFamily ℬ fun U =>
      (complexPartialBlockAverage (Φ U) : PartialGaugeField L m (levelDepth K (n + 1))) := by
  have hK : 0 < K := by omega
  refine ⟨fun U W h => ?_, fun U c hc => ?_, fun U hU => ⟨fun c hc => ?_, fun c hc => ?_⟩,
    fun c => ?_⟩
  · obtain ⟨hb, hv⟩ := hΦ.determined U W h
    have key : ∀ c : BondAtLevel L m K (n + 1),
        (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) ⊆ (Φ U).support →
        onSetElseOne (bondsInDoubleBlock c) (Φ U).field =
          onSetElseOne (bondsInDoubleBlock c) (Φ W).field := by
      intro c hs
      funext b
      by_cases hbP : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))
      · simp only [onSetElseOne, if_pos hbP]
        exact hv b (hs hbP)
      · simp only [onSetElseOne, if_neg hbP]
    refine ⟨?_, fun c hc => ?_⟩
    · ext c
      constructor
      · rintro ⟨h₁, h₂⟩
        refine ⟨by rw [← hb]; exact h₁, ?_⟩
        rw [← key c h₁]
        exact h₂
      · rintro ⟨h₁, h₂⟩
        have h₁' : (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) ⊆ (Φ U).support := by
          rw [hb]
          exact h₁
        refine ⟨h₁', ?_⟩
        rw [key c h₁']
        exact h₂
    · change complexBlockAverage _ c = complexBlockAverage _ c
      rw [key c hc.1]
  · obtain ⟨-, -, -, -, -, hrp, -⟩ := S.orientation L m K S.admissible S.m_pos hK n hn c
    obtain ⟨h₁, h₂⟩ := hc
    refine ⟨by rw [bondsInDoubleBlock_opposite]; exact h₁, ?_⟩
    rw [bondsInDoubleBlock_opposite, hrp]
    exact h₂
  · obtain ⟨-, -, hp, -, -, -, -⟩ := S.orientation L m K S.admissible S.m_pos hK n hn c
    obtain ⟨h₁, h₂⟩ := (S.mem_partialAverage_support hn (Φ U) c).1 hc
    obtain ⟨G, -, hg, hev⟩ := S.average_eventually hn _ hp hΦ hU h₁ h₂
    have e := (hev.self_of_nhds U hU rfl).2.2
    rw [S.partialAverage_field hn, e]
    by_cases hcp : c.IsPositivelyOriented
    · rw [if_pos hcp]
      exact hg
    · rw [if_neg hcp]
      exact inv_mem_complexGaugeGroup hg
  · obtain ⟨-, hxor, hp, -, -, hrp, -⟩ := S.orientation L m K S.admissible S.m_pos hK n hn c
    obtain ⟨h₁, h₂⟩ := (S.mem_partialAverage_support hn (Φ U) c).1 hc
    obtain ⟨G, -, hg, hev⟩ := S.average_eventually hn _ hp hΦ hU h₁ h₂
    have e := (hev.self_of_nhds U hU rfl).2.2
    have hdet : IsUnit (G (restrictToBonds ℬ U)).det := by
      have t : (G (restrictToBonds ℬ U)).det = 1 := hg
      rw [t]
      exact isUnit_one
    rw [S.partialAverage_field hn, S.partialAverage_field hn, hrp, e]
    rcases hxor with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [if_pos h, if_neg h']
    · rw [if_neg h', if_pos h, Matrix.nonsing_inv_nonsing_inv _ hdet]
  · obtain ⟨-, -, hp, -, -, -, -⟩ := S.orientation L m K S.admissible S.m_pos hK n hn c
    refine ⟨inferInstance, sep_subset _ _, ?_, fun U₀ hU₀ => ?_⟩
    · refine isRelativelyOpen_of_local (image_mono (sep_subset _ _)) ?_
      rintro _ ⟨U₀, hU₀, rfl⟩
      obtain ⟨h₁, h₂⟩ := (S.mem_partialAverage_support hn (Φ U₀) c).1 hU₀.2
      obtain ⟨G, -, -, hev⟩ := S.average_eventually hn _ hp hΦ hU₀.1 h₁ h₂
      obtain ⟨N, hNs, hNo, hxN⟩ := eventually_nhds_iff.1 hev
      refine ⟨N, hNo, hxN, ?_⟩
      rintro w ⟨hwN, U, hU, rfl⟩
      obtain ⟨t₁, t₂, -⟩ := hNs _ hwN U hU rfl
      exact ⟨U, ⟨hU, (S.mem_partialAverage_support hn (Φ U) c).2 ⟨t₁, t₂⟩⟩, rfl⟩
    · obtain ⟨h₁, h₂⟩ := (S.mem_partialAverage_support hn (Φ U₀) c).1 hU₀.2
      obtain ⟨G, hG, hg, hev⟩ := S.average_eventually hn _ hp hΦ hU₀.1 h₁ h₂
      by_cases hcp : c.IsPositivelyOriented
      · refine ⟨G, hG, hev.mono fun w hw W hW e => ?_⟩
        change (complexPartialBlockAverage (Φ W)).field c = _
        rw [S.partialAverage_field hn, if_pos hcp]
        exact (hw W hW.1 e).2.2
      · have hdet : (G (restrictToBonds ℬ U₀)).det ≠ 0 := by
          have t : (G (restrictToBonds ℬ U₀)).det = 1 := hg
          rw [t]
          exact one_ne_zero
        refine ⟨fun w => (G w)⁻¹, AnalyticAt.comp (analyticAt_inv_of_det_ne_zero hdet) hG,
          hev.mono fun w hw W hW e => ?_⟩
        change (complexPartialBlockAverage (Φ W)).field c = _
        rw [S.partialAverage_field hn, if_neg hcp, (hw W hW.1 e).2.2]
end Family
section Bonds
variable {L m : ℕ} {j : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
theorem bondPreimage_bondImage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    bondPreimage σ (bondImage σ b) = b := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.bondPreimage_bondImage <;> assumption
theorem bondImage_bondPreimage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    bondImage σ (bondPreimage σ b) = b :=
  bondPreimage_bondImage (σ := σ.symm) h' h b
theorem bondImage_opposite (h : MapsCellsAndCubes σ j) (b : Bond L m j) :
    bondImage σ b.opposite = (bondImage σ b).opposite := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.bondImage_opposite <;> assumption
theorem bondImage_injective (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) :
    Function.Injective (bondImage σ : Bond L m j → Bond L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.bondImage_injective <;> assumption
theorem transportGaugeField_bondImage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (U : Bond L m j → ComplexMatrix2) (b : Bond L m j) :
    transportGaugeField σ U (bondImage σ b) = U b :=
  congrArg U (bondPreimage_bondImage h h' b)
theorem isGaugeField_image_iff (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (ℬ : Set (Bond L m j))
    (V : Bond L m j → ComplexMatrix2) :
    IsGaugeField complexGaugeGroup (bondImage σ '' ℬ) (transportGaugeField σ V) ↔
      IsGaugeField complexGaugeGroup ℬ V := by
  have e := transportGaugeField_bondImage h h' V
  have e' : ∀ b, transportGaugeField σ V (bondImage σ b).opposite = V b.opposite := fun b => by
    rw [← bondImage_opposite h, e]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · rw [← e]
      exact h₁ _ (mem_image_of_mem _ hb)
    · rw [← e', ← e]
      exact h₂ _ (mem_image_of_mem _ hb)
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [e]
      exact h₁ b hb
    · rintro _ ⟨b, hb, rfl⟩
      rw [e', e]
      exact h₂ b hb
theorem extendByOne_image (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) {P : Set (Bond L m j)}
    {V V' : Bond L m j → ComplexMatrix2} (hV : ∀ b ∈ P, V' (bondImage σ b) = V b) :
    onSetElseOne (bondImage σ '' P) V' = transportGaugeField σ (onSetElseOne P V) := by
  funext b'
  obtain ⟨b, rfl⟩ : ∃ b, bondImage σ b = b' := ⟨_, bondImage_bondPreimage h h' b'⟩
  rw [transportGaugeField_bondImage h h']
  by_cases hb : b ∈ P
  · simp only [onSetElseOne, if_pos hb, if_pos (mem_image_of_mem (bondImage σ) hb), hV b hb]
  · have hb' : bondImage σ b ∉ bondImage σ '' P := fun t =>
      hb ((bondImage_injective h h').mem_set_image.1 t)
    simp only [onSetElseOne, if_neg hb, if_neg hb']
theorem commutesHolomorphically_of_families {j' : ℤ} (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j)
    (g : MapsCellsAndCubes σ j') (g' : MapsCellsAndCubes σ.symm j')
    {ℬ : Set (Bond L m j)} [Fintype ↥ℬ] [Fintype ↥(bondImage σ '' ℬ)]
    {F : PartialGaugeField L m j → PartialGaugeField L m j'}
    (hf : HolomorphicFieldFamily ℬ fun U => F ⟨ℬ, U⟩)
    (hf' : HolomorphicFieldFamily (bondImage σ '' ℬ) fun U => F ⟨bondImage σ '' ℬ, U⟩)
    (hcarry : ∀ c, ∀ U ∈ complexGaugeFields ℬ, c ∈ (F ⟨ℬ, U⟩).support →
      bondImage σ c ∈ (F ⟨bondImage σ '' ℬ, transportGaugeField σ U⟩).support →
      (F ⟨bondImage σ '' ℬ, transportGaugeField σ U⟩).field (bondImage σ c) =
        (F ⟨ℬ, U⟩).field c)
    (htrans : IsTorusTranslation σ → ∀ c, ∀ U ∈ complexGaugeFields ℬ,
      (bondImage σ c ∈ (F ⟨bondImage σ '' ℬ, transportGaugeField σ U⟩).support ↔
        c ∈ (F ⟨ℬ, U⟩).support)) :
    CommutesHolomorphically σ ℬ F := by
  intro c
  have hcfg : ∀ U ∈ complexGaugeFields ℬ, transportGaugeField σ U ∈
      complexGaugeFields (bondImage σ '' ℬ) := fun U hU =>
    (isGaugeField_image_iff h h' ℬ U).2 hU
  have hpb : ∀ b' : ↥(bondImage σ '' ℬ), bondPreimage σ b'.1 ∈ ℬ := by
    rintro ⟨_, b, hb, rfl⟩
    rw [bondPreimage_bondImage h h']
    exact hb
  let T : (↥ℬ → ComplexMatrix2) → ↥(bondImage σ '' ℬ) → ComplexMatrix2 := fun w b' => w ⟨_, hpb b'⟩
  have hT : Continuous T := continuous_pi fun b' => continuous_apply _
  obtain ⟨-, ⟨O₂, hO₂, e₂⟩, -⟩ := holomorphicOnFields_data (hf.holomorphic c)
  obtain ⟨-, ⟨O₁, hO₁, e₁⟩, -⟩ := holomorphicOnFields_data (hf'.holomorphic (bondImage σ c))
  have hopen : ComplexMatrix2.IsRelativelyOpen (restrictToBonds ℬ '' complexGaugeFields ℬ)
      (restrictToBonds ℬ '' ({U ∈ complexGaugeFields ℬ |
          bondImage σ c ∈ (F ⟨bondImage σ '' ℬ, transportGaugeField σ U⟩).support} ∩
        {U ∈ complexGaugeFields ℬ | c ∈ (F ⟨ℬ, U⟩).support})) := by
    refine ⟨O₂ ∩ T ⁻¹' O₁, hO₂.inter (hO₁.preimage hT), ?_⟩
    ext w
    constructor
    · rintro ⟨U, ⟨hU₁, hU₂⟩, rfl⟩
      have t₂ : restrictToBonds ℬ U ∈ restrictToBonds ℬ ''
          {U ∈ complexGaugeFields ℬ | c ∈ (F ⟨ℬ, U⟩).support} := ⟨U, hU₂, rfl⟩
      rw [e₂] at t₂
      have t₁ : restrictToBonds (bondImage σ '' ℬ) (transportGaugeField σ U) ∈
          restrictToBonds (bondImage σ '' ℬ) '' {U' ∈ complexGaugeFields (bondImage σ '' ℬ) |
            bondImage σ c ∈ (F ⟨bondImage σ '' ℬ, U'⟩).support} :=
        ⟨_, ⟨hcfg U hU₁.1, hU₁.2⟩, rfl⟩
      rw [e₁] at t₁
      exact ⟨⟨t₂.1, t₁.1⟩, U, hU₁.1, rfl⟩
    · rintro ⟨⟨hw₂, hw₁⟩, U, hU, rfl⟩
      have t₂ : restrictToBonds ℬ U ∈ restrictToBonds ℬ ''
          {U ∈ complexGaugeFields ℬ | c ∈ (F ⟨ℬ, U⟩).support} := by
        rw [e₂]
        exact ⟨hw₂, U, hU, rfl⟩
      obtain ⟨U', hU', ee⟩ := t₂
      have t₁ : restrictToBonds (bondImage σ '' ℬ) (transportGaugeField σ U) ∈
          restrictToBonds (bondImage σ '' ℬ) '' {U' ∈ complexGaugeFields (bondImage σ '' ℬ) |
            bondImage σ c ∈ (F ⟨bondImage σ '' ℬ, U'⟩).support} := by
        rw [e₁]
        exact ⟨hw₁, _, hcfg U hU, rfl⟩
      obtain ⟨U'', hU'', ee'⟩ := t₁
      refine ⟨U, ⟨⟨hU, ?_⟩, hU, ?_⟩, rfl⟩
      · rw [← (hf'.determined U'' _ ee').1]
        exact hU''.2
      · rw [← (hf.determined U' U ee).1]
        exact hU'.2
  have hright : IsAnalyticOnSupport (complexGaugeFields ℬ) ℬ
      ({U ∈ complexGaugeFields ℬ |
          bondImage σ c ∈ (F ⟨bondImage σ '' ℬ, transportGaugeField σ U⟩).support} ∩
        {U ∈ complexGaugeFields ℬ | c ∈ (F ⟨ℬ, U⟩).support}) (fun U => (F ⟨ℬ, U⟩).field c) :=
    (hf.holomorphic c).restrict inter_subset_right hopen
  refine ⟨holomorphicOnFields_congr hright fun U hU => hcarry c U hU.2.1 hU.2.2 hU.1.2,
    holomorphicOnFields_congr hright fun U _ => transportGaugeField_bondImage g g' _ c,
    fun U hU => ?_, fun ht => ?_⟩
  · exact (hcarry c U hU.2.1 hU.2.2 hU.1.2).trans (transportGaugeField_bondImage g g' _ c).symm
  · ext U
    constructor
    · rintro ⟨hU, t⟩
      exact ⟨hU, (htrans ht c U hU).1 t⟩
    · rintro ⟨hU, t⟩
      exact ⟨hU, (htrans ht c U hU).2 t⟩
end Bonds
section Carried
variable {L m K n : ℕ} {i : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
structure IsometryHypotheses (L m K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop where
  lattice : LatticeHypotheses L m K
  lower : -(m : ℤ) ≤ i
  mem : σ ∈ latticeIsometries L m i
  maps : ∀ j : ℤ, i ≤ j → MapsCellsAndCubes σ j
  mapsSymm : ∀ j : ℤ, i ≤ j → MapsCellsAndCubes σ.symm j
  objects : ∀ k : ℕ, k < K → i ≤ levelDepth K (k + 1) →
    IsometryInvariance.MapsBondObjects σ K k
  equivariance : ComplexAverageEquivariance
  preservesOrientation : IsTorusTranslation σ → ∀ j : ℤ, -(m : ℤ) < j → i ≤ j →
    ∀ b : Bond L m j, b.IsPositivelyOriented → (bondImage σ b).IsPositivelyOriented
theorem levelDepth_succ_le (K n : ℕ) : levelDepth K (n + 1) ≤ levelDepth K n := by apply _root_.YangMills.Construction.Tower.ScalingPreservesStepsAtSide.levelDepth_succ_le <;> assumption
namespace IsometryHypotheses
variable (T : IsometryHypotheses L m K i σ)
include T
theorem bondImage_doubleBlock (hn : n < K) (hi : i ≤ levelDepth K (n + 1))
    (c : BondAtLevel L m K (n + 1)) :
    bondImage σ '' (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) =
      bondsInDoubleBlock (bondImage σ c) := by
  have hK : 0 < K := by omega
  have S := T.lattice
  have e := (T.objects n hn hi c).2.2.2
  rw [(S.orientation L m K S.admissible S.m_pos hK n hn c).2.2.2.2.2.2,
    (S.orientation L m K S.admissible S.m_pos hK n hn (bondImage σ c)).2.2.2.2.2.2] at e
  exact e
theorem positivelyOriented_bondImage (hn : n < K) (hi : i ≤ levelDepth K (n + 1))
    (c : BondAtLevel L m K (n + 1)) :
    (bondImage σ c).positivelyOriented = bondImage σ c.positivelyOriented ∨
      (bondImage σ c).positivelyOriented = (bondImage σ c.positivelyOriented).opposite := by
  have hK : 0 < K := by omega
  have S := T.lattice
  have hc := T.maps _ hi
  obtain ⟨-, -, -, h₁, -⟩ := S.orientation L m K S.admissible S.m_pos hK n hn c
  obtain ⟨-, -, -, h₂, -⟩ := S.orientation L m K S.admissible S.m_pos hK n hn (bondImage σ c)
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (by rw [h₁, h₂])
  · exact Or.inr (by rw [h₁, h₂])
  · refine Or.inr ?_
    rw [h₁, h₂, bondImage_opposite hc]
    exact Bond.ext rfl rfl
  · exact Or.inl (by rw [h₁, h₂, bondImage_opposite hc])
end IsometryHypotheses
theorem complexBlockAverage_of_pos {j j' : ℤ} (W : Bond L m j' → ComplexMatrix2) {c : Bond L m j}
    (hc : c.IsPositivelyOriented) :
    complexBlockAverage W c = complexBlockAverageOnPositive W c := by
  rw [complexBlockAverage, if_pos hc]
theorem complexBlockAverage_of_not_pos {j j' : ℤ} (W : Bond L m j' → ComplexMatrix2) {c : Bond L m j}
    (hc : ¬c.IsPositivelyOriented) (hr : c.opposite.IsPositivelyOriented) :
    complexBlockAverage W c = (complexBlockAverage W c.opposite)⁻¹ := by
  rw [complexBlockAverage_of_pos W hr, complexBlockAverage, if_neg hc]
theorem LatticeHypotheses.average_mem_gaugeGroup (S : LatticeHypotheses L m K) (hn : n < K)
    {d : BondAtLevel L m K (n + 1)} (hd : d.IsPositivelyOriented)
    {W : BondAtLevel L m K n → ComplexMatrix2}
    (hW : W ∈ (complexAveragingDomainNearOne d : Set (BondAtLevel L m K n → ComplexMatrix2))) :
    complexBlockAverageOnPositive W d ∈ complexGaugeGroup := by
  have := S.finite_bond (levelDepth K n)
  let _ : Fintype (PositiveBondOf (bondsInDoubleBlock d : Set (BondAtLevel L m K n))) :=
    Fintype.ofFinite _
  have reads := S.locality L m K n S.admissible.1 S.admissible.2 S.m_pos hn d hd
  obtain ⟨O, -, -, hloc⟩ := S.centred_average_on_restrictions hn d hd
  have t := (hloc _ ⟨W, hW, rfl⟩).1
  rwa [reads.average_eq _ W fun b hb =>
    S.extendFromPositive_restrict hn.le (isReversalClosed_bondsInDoubleBlock d) hW.1.1 hb] at t
namespace IsometryHypotheses
variable (T : IsometryHypotheses L m K i σ)
include T
theorem average_bondImage (hn : n < K) (hi : i ≤ levelDepth K (n + 1))
    (c : BondAtLevel L m K (n + 1)) {W : BondAtLevel L m K n → ComplexMatrix2}
    (hW : W ∈ (complexAveragingDomainNearOne c.positivelyOriented :
      Set (BondAtLevel L m K n → ComplexMatrix2)))
    (hW' : transportGaugeField σ W ∈
      (complexAveragingDomainNearOne (bondImage σ c).positivelyOriented :
        Set (BondAtLevel L m K n → ComplexMatrix2))) :
    complexBlockAverage (transportGaugeField σ W) (bondImage σ c) =
      complexBlockAverage W c := by
  have hK : 0 < K := by omega
  have S := T.lattice
  have hcar := T.maps _ hi
  obtain ⟨-, hx₁, hp₁, -⟩ := S.orientation L m K S.admissible S.m_pos hK n hn c
  obtain ⟨-, hx₂, hp₂, -⟩ := S.orientation L m K S.admissible S.m_pos hK n hn (bondImage σ c)
  have A := T.equivariance L m K n i σ S.admissible S.m_pos T.lower T.mem hn hi W
    c.positivelyOriented (bondImage σ c).positivelyOriented hp₁ hp₂
    (T.positivelyOriented_bondImage hn hi c) hW.1.1
  have hrr : ∀ b : BondAtLevel L m K (n + 1), b.opposite.opposite = b := fun b => Bond.ext rfl rfl
  by_cases hc : c.IsPositivelyOriented <;> by_cases hc' : (bondImage σ c).IsPositivelyOriented
  · rw [positivelyOriented_eq_self hc] at A hW
    rw [positivelyOriented_eq_self hc'] at A hW'
    exact A.average_image rfl hW
  · have hr' : (bondImage σ c).opposite.IsPositivelyOriented := by
      rcases hx₂ with h | h
      · exact absurd h.1 hc'
      · exact h.1
    have ed' : (bondImage σ c).positivelyOriented = (bondImage σ c).opposite := if_neg hc'
    rw [positivelyOriented_eq_self hc] at A hW
    rw [ed'] at A hW'
    have e := A.average_opposite rfl hW hW'
    have hu : IsUnit (complexBlockAverage W c).det := by
      have t : (complexBlockAverage W c).det = 1 := by
        rw [complexBlockAverage_of_pos W hc]
        exact S.average_mem_gaugeGroup hn hc hW
      rw [t]
      exact isUnit_one
    rw [complexBlockAverage_of_not_pos _ hc' hr', e, Matrix.nonsing_inv_nonsing_inv _ hu]
  · have hr : c.opposite.IsPositivelyOriented := by
      rcases hx₁ with h | h
      · exact absurd h.1 hc
      · exact h.1
    have ed : c.positivelyOriented = c.opposite := if_neg hc
    rw [ed] at A hW
    rw [positivelyOriented_eq_self hc'] at A hW'
    have e := A.average_opposite
      (by rw [bondImage_opposite hcar, hrr]) hW hW'
    rw [complexBlockAverage_of_not_pos W hc hr, e]
  · have hr : c.opposite.IsPositivelyOriented := by
      rcases hx₁ with h | h
      · exact absurd h.1 hc
      · exact h.1
    have hr' : (bondImage σ c).opposite.IsPositivelyOriented := by
      rcases hx₂ with h | h
      · exact absurd h.1 hc'
      · exact h.1
    have ed : c.positivelyOriented = c.opposite := if_neg hc
    have ed' : (bondImage σ c).positivelyOriented = (bondImage σ c).opposite := if_neg hc'
    rw [ed] at A hW
    rw [ed'] at A hW'
    have e := A.average_image (bondImage_opposite hcar c).symm hW
    rw [complexBlockAverage_of_not_pos W hc hr, complexBlockAverage_of_not_pos _ hc' hr', e]
theorem field_step (hn : n < K) (hi : i ≤ levelDepth K (n + 1))
    {V V' : PartialGaugeField L m (levelDepth K n)}
    (hVV : ∀ b ∈ V.support, bondImage σ b ∈ V'.support → V'.field (bondImage σ b) = V.field b)
    {c : BondAtLevel L m K (n + 1)} (hc : c ∈ (complexPartialBlockAverage V).support)
    (hc' : bondImage σ c ∈ (complexPartialBlockAverage V').support) :
    (complexPartialBlockAverage V').field (bondImage σ c) =
      (complexPartialBlockAverage V).field c := by
  have hi' : i ≤ levelDepth K n := hi.trans (levelDepth_succ_le K n)
  have hb := T.bondImage_doubleBlock hn hi c
  have hW : onSetElseOne (bondsInDoubleBlock (bondImage σ c)) V'.field =
      transportGaugeField σ (onSetElseOne (bondsInDoubleBlock c) V.field) := by
    rw [← hb]
    exact extendByOne_image (T.maps _ hi') (T.mapsSymm _ hi') fun b hbP =>
      hVV b (hc.1 hbP) (hc'.1 (hb ▸ mem_image_of_mem _ hbP))
  change complexBlockAverage (onSetElseOne (bondsInDoubleBlock (bondImage σ c)) V'.field)
    (bondImage σ c) = complexBlockAverage (onSetElseOne (bondsInDoubleBlock c) V.field) c
  have h₂ := hc'.2
  rw [hW] at h₂ ⊢
  exact T.average_bondImage hn hi c hc.2 h₂
theorem support_step (ht : IsTorusTranslation σ) (hn : n < K) (hi : i ≤ levelDepth K (n + 1))
    {V V' : PartialGaugeField L m (levelDepth K n)}
    (hmem : ∀ b, bondImage σ b ∈ V'.support ↔ b ∈ V.support)
    (hVV : ∀ b ∈ V.support, V'.field (bondImage σ b) = V.field b)
    (c : BondAtLevel L m K (n + 1)) :
    bondImage σ c ∈ (complexPartialBlockAverage V').support ↔
      c ∈ (complexPartialBlockAverage V).support := by
  have hK : 0 < K := by omega
  have S := T.lattice
  have hi' : i ≤ levelDepth K n := hi.trans (levelDepth_succ_le K n)
  have hcar := T.maps _ hi
  have hcar' := T.maps _ hi'
  have hinv' := T.mapsSymm _ hi'
  have hm := S.m_pos
  have hd : -(m : ℤ) < levelDepth K (n + 1) := by
    simp only [levelDepth]
    omega
  have hkeep := T.preservesOrientation ht _ hd hi
  have ho : (bondImage σ c).positivelyOriented = bondImage σ c.positivelyOriented := by
    by_cases hc : c.IsPositivelyOriented
    · rw [positivelyOriented_eq_self hc, positivelyOriented_eq_self (hkeep c hc)]
    · obtain ⟨-, hx₁, -⟩ := S.orientation L m K S.admissible S.m_pos hK n hn c
      obtain ⟨-, hx₂, -⟩ := S.orientation L m K S.admissible S.m_pos hK n hn (bondImage σ c)
      have hr : c.opposite.IsPositivelyOriented := by
        rcases hx₁ with h | h
        · exact absurd h.1 hc
        · exact h.1
      have hr' : (bondImage σ c).opposite.IsPositivelyOriented := by
        rw [← bondImage_opposite hcar]
        exact hkeep _ hr
      have hc' : ¬(bondImage σ c).IsPositivelyOriented := by
        rcases hx₂ with h | h
        · exact absurd hr' h.2
        · exact h.2
      have e₁ : c.positivelyOriented = c.opposite := if_neg hc
      have e₂ : (bondImage σ c).positivelyOriented = (bondImage σ c).opposite := if_neg hc'
      rw [e₁, e₂, bondImage_opposite hcar]
  have hb := T.bondImage_doubleBlock hn hi c
  obtain ⟨-, -, hp₁, -, -, -, hP₁⟩ := S.orientation L m K S.admissible S.m_pos hK n hn c
  obtain ⟨-, -, hp₂, -, -, -, hP₂⟩ :=
    S.orientation L m K S.admissible S.m_pos hK n hn (bondImage σ c)
  have hW : (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) ⊆ V.support →
      onSetElseOne (bondsInDoubleBlock (bondImage σ c)) V'.field =
      transportGaugeField σ (onSetElseOne (bondsInDoubleBlock c) V.field) := fun hs => by
    rw [← hb]
    exact extendByOne_image hcar' hinv' fun b hbP => hVV b (hs hbP)
  have key : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c.positivelyOriented)
      (onSetElseOne (bondsInDoubleBlock c) V.field) →
      (transportGaugeField σ (onSetElseOne (bondsInDoubleBlock c) V.field) ∈
        (complexAveragingDomainNearOne (bondImage σ c).positivelyOriented :
          Set (BondAtLevel L m K n → ComplexMatrix2)) ↔
      onSetElseOne (bondsInDoubleBlock c) V.field ∈
        (complexAveragingDomainNearOne c.positivelyOriented :
          Set (BondAtLevel L m K n → ComplexMatrix2))) :=
    fun hcfg => (T.equivariance L m K n i σ S.admissible S.m_pos T.lower T.mem hn hi _
      c.positivelyOriented (bondImage σ c).positivelyOriented hp₁ hp₂
      (T.positivelyOriented_bondImage hn hi c) hcfg).mem_domain_iff ho
  constructor
  · rintro ⟨h₁, h₂⟩
    have hs : (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) ⊆ V.support := fun b hbP =>
      (hmem b).1 (h₁ (hb ▸ mem_image_of_mem _ hbP))
    rw [hW hs] at h₂
    have hcfg := h₂.1.1
    rw [hP₂, ← hb, isGaugeField_image_iff hcar' hinv'] at hcfg
    exact ⟨hs, (key (by rw [hP₁]; exact hcfg)).1 h₂⟩
  · rintro ⟨hs, h₂⟩
    have h₁ : (bondsInDoubleBlock (bondImage σ c) : Set (BondAtLevel L m K n)) ⊆ V'.support := by
      rw [← hb]
      rintro _ ⟨b, hbP, rfl⟩
      exact (hmem b).2 (hs hbP)
    refine ⟨h₁, ?_⟩
    rw [hW hs]
    exact (key h₂.1.1).2 h₂
theorem iterate_field (ℬ : Set (BondAtLevel L m K 0)) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    ∀ n : ℕ, n ≤ K → i ≤ levelDepth K n → ∀ c : BondAtLevel L m K n,
      c ∈ (complexIteratePartial ℬ U n).support →
      bondImage σ c ∈ (complexIteratePartial (bondImage σ '' ℬ)
        (transportGaugeField σ U) n).support →
      (complexIteratePartial (bondImage σ '' ℬ) (transportGaugeField σ U) n).field
        (bondImage σ c) = (complexIteratePartial ℬ U n).field c
  | 0, _, hi, c, _, _ => transportGaugeField_bondImage (T.maps _ hi) (T.mapsSymm _ hi) U c
  | n + 1, hn, hi, _, hc, hc' =>
    T.field_step hn hi (fun b hb hb' =>
      iterate_field ℬ U n (by omega) (hi.trans (levelDepth_succ_le K n)) b hb hb') hc hc'
theorem iterate_support (ht : IsTorusTranslation σ) (ℬ : Set (BondAtLevel L m K 0))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    ∀ n : ℕ, n ≤ K → i ≤ levelDepth K n → ∀ c : BondAtLevel L m K n,
      (bondImage σ c ∈ (complexIteratePartial (bondImage σ '' ℬ)
        (transportGaugeField σ U) n).support ↔ c ∈ (complexIteratePartial ℬ U n).support)
  | 0, _, hi, _ => (bondImage_injective (T.maps _ hi) (T.mapsSymm _ hi)).mem_set_image
  | n + 1, hn, hi, c => by
    have hi' := hi.trans (levelDepth_succ_le K n)
    have ih := iterate_support ht ℬ U n (by omega) hi'
    exact T.support_step ht hn hi ih (fun b hb =>
      T.iterate_field ℬ U n (by omega) hi' b hb ((ih b).2 hb)) c
end IsometryHypotheses
theorem LatticeHypotheses.holomorphicFamily_iterate (S : LatticeHypotheses L m K)
    {ℬ : Set (BondAtLevel L m K 0)} [Fintype ↥ℬ] (hℬ : IsReversalClosed ℬ) :
    ∀ n : ℕ, n ≤ K → HolomorphicFieldFamily ℬ fun U => complexIteratePartial ℬ U n
  | 0, _ => holomorphicFamily_id hℬ
  | n + 1, hn => S.holomorphicFamily_average hn (S.holomorphicFamily_iterate hℬ n (by omega))
theorem isReversalClosed_image {j : ℤ} (h : MapsCellsAndCubes σ j) {ℬ : Set (Bond L m j)}
    (hℬ : IsReversalClosed ℬ) : IsReversalClosed (bondImage σ '' ℬ) := by
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨b.opposite, hℬ b hb, bondImage_opposite h b⟩
end Carried
theorem statement_holds (hG : LatticeIsometryGroupActionStatement)
    (hB : IsometryInvariance.InvariantUnderIsometries)
    (hC : ComplexAverageEquivariance)
    (hT : AveragingSchemeProperties)
    (hO : PositiveOrientationOfBondAndOpposite)
    (hE : BondOrientationDichotomy)
    (hR : ComplexAverageIsLocal)
    (hM : TwistedTransportIsometryInvariance) : Statement := by
  intro L m i σ hL hm hi hσ K
  obtain ⟨⟨⟨H, hH⟩, -⟩, -, -, -, hall⟩ := hG L m i hL hm hi
  have hτ : σ.symm ∈ latticeIsometries L m i := by
    have h₁ : σ ∈ H := by
      rw [← SetLike.mem_coe, hH]
      exact hσ
    have h₂ : σ⁻¹ ∈ H := H.inv_mem h₁
    rw [← hH]
    exact h₂
  have S : LatticeHypotheses L m K := ⟨hL, hm, hT, hO, hE, hR⟩
  have T : IsometryHypotheses L m K i σ :=
    ⟨S, hi, hσ, fun j hj => (hall σ hσ j hj).1, fun j hj => (hall σ.symm hτ j hj).1,
      fun k hk hik => (hB L m hL hm i hi σ hσ).2.1 K k hk hik, hC,
      fun ht => (hM L m i σ hL hm hi hσ).1 (Or.inl ht)⟩
  refine ⟨fun k hk hik ℬ hℬ => ?_, fun n hn hin ℬ hℬ => ?_⟩
  · have hik' := hik.trans (levelDepth_succ_le K k)
    have hc := T.maps _ hik'
    have hc' := T.mapsSymm _ hik'
    have := S.finite_bond (levelDepth K k)
    let _ : Fintype ↥ℬ := Fintype.ofFinite _
    let _ : Fintype ↥(bondImage σ '' ℬ) := Fintype.ofFinite _
    refine commutesHolomorphically_of_families hc hc' (T.maps _ hik) (T.mapsSymm _ hik)
      (S.holomorphicFamily_average hk (holomorphicFamily_id hℬ))
      (S.holomorphicFamily_average hk (holomorphicFamily_id (isReversalClosed_image hc hℬ)))
      (fun c U _ h₁ h₂ => ?_) fun ht c U _ => ?_
    · exact T.field_step hk hik (fun b _ _ => transportGaugeField_bondImage hc hc' U b) h₁ h₂
    · exact T.support_step ht hk hik (fun b => (bondImage_injective hc hc').mem_set_image)
        (fun b _ => transportGaugeField_bondImage hc hc' U b) c
  · have h0 : i ≤ levelDepth K 0 := by
      refine hin.trans ?_
      simp only [levelDepth]
      push_cast
      omega
    have hc := T.maps _ h0
    have hc' := T.mapsSymm _ h0
    have := S.finite_bond (levelDepth K 0)
    let _ : Fintype ↥ℬ := Fintype.ofFinite _
    let _ : Fintype ↥(bondImage σ '' ℬ) := Fintype.ofFinite _
    exact commutesHolomorphically_of_families hc hc' (T.maps _ hin) (T.mapsSymm _ hin)
      (S.holomorphicFamily_iterate hℬ n hn) (S.holomorphicFamily_iterate (isReversalClosed_image hc hℬ) n hn)
      (fun c U _ h₁ h₂ => T.iterate_field ℬ U n hn hin c h₁ h₂)
      fun ht c U _ => T.iterate_support ht ℬ U n hn hin c
end PeriodicLattice.ComplexAveragesCommuteWithIsometries
end YangMills.Construction
