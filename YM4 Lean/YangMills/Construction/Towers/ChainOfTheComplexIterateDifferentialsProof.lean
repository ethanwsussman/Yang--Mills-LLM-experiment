import YangMills.Construction.Towers.ChainOfTheComplexIterateDifferentials
import YangMills.Construction.Towers.ChainRuleAtAFiniteSideInTheLeftChartProof
import YangMills.Construction.Towers.ExpansionOfTheIterateInTheLeftChartProof
import YangMills.Construction.Towers.WritingsOfAChainInTheLeftChartProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Tower.ComplexIterDerivChainProof
open LeftChartFields (leftExpMul)
open MeanStableFields
  (meanStableFields fieldsNearOne levelwiseMeanAt IsHolomorphicOnFields IsMeanSequenceFrom)
open LevelwiseMeans (IsMeanSequence levelwiseMean valuesOrOne)
variable {L n k j j' : ℕ}
abbrev OppositeOrientation (L n k j : ℕ) : Prop :=
  ∀ b : Edge L n k j, (b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented) ∧
    (¬ b.IsPositivelyOriented → b.opposite.IsPositivelyOriented)
theorem oppositeOrientation_of (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) : OppositeOrientation L n k j := by apply _root_.YangMills.Construction.Tower.FiniteLevelChainRule.exactlyOneOriented <;> assumption
theorem isUnit_det_of_mem {g : Matrices.ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.complexGaugeGroup) : IsUnit g.det := by apply _root_.YangMills.Construction.Tower.FullSpace.ChainRule.isUnit_det_of_complex <;> assumption
theorem inv_mem_complexGaugeGroup {M : Matrices.ComplexMatrix2}
    (hM : M ∈ PeriodicLattice.complexGaugeGroup) : M⁻¹ ∈ PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
theorem fieldOfPositiveValues_restrict (ho : OppositeOrientation L n k j)
    {V : Edge L n k j → Matrices.ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    fieldOfPositiveValues (restrictToPositiveEdges V) = V := by
  funext b
  unfold fieldOfPositiveValues
  by_cases hb : b.IsPositivelyOriented
  · rw [dif_pos hb]
    rfl
  · have hr := (ho b).2 hb
    rw [dif_neg hb, dif_pos hr]
    have h : V b.opposite = (V b)⁻¹ := hV.2 b trivial
    show (V b.opposite)⁻¹ = V b
    rw [h, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hV.1 b trivial))]
theorem eq_of_restrict_eq (ho : OppositeOrientation L n k j)
    {U V : Edge L n k j → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (h : restrictToPositiveEdges U = restrictToPositiveEdges V) : U = V := by
  have := congrArg fieldOfPositiveValues h
  rwa [fieldOfPositiveValues_restrict ho hU, fieldOfPositiveValues_restrict ho hV] at this
theorem hasDerivAt_leftExpMul (X V : Matrices.ComplexMatrix2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => leftExpMul ((s : ℂ) • X) V)
      (Matrices.ComplexMatrix2.matExp ((t : ℂ) • (Complex.I • X)) * (Complex.I • X) * V) t := by apply _root_.YangMills.Construction.Tower.FiniteLevelChainRule.hasDerivAt_leftExpMul <;> assumption
def expCurve (U B : Edge L n k j → Matrices.ComplexMatrix2) (t : ℝ) :
    Edge L n k j → Matrices.ComplexMatrix2 :=
  PeriodicLattice.expTwist ((t : ℂ) • B) U
theorem expCurve_of_pos (U B : Edge L n k j → Matrices.ComplexMatrix2) (t : ℝ)
    {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    expCurve U B t b = leftExpMul ((t : ℂ) • B b) (U b) := by apply _root_.YangMills.Construction.Tower.FiniteLevelChainRule.leftExpCurve_pos <;> assumption
theorem expCurve_of_not_pos (U B : Edge L n k j → Matrices.ComplexMatrix2) (t : ℝ)
    {b : Edge L n k j} (hb : ¬ b.IsPositivelyOriented) :
    expCurve U B t b = (leftExpMul ((t : ℂ) • B b.opposite) (U b.opposite))⁻¹ := by apply _root_.YangMills.Construction.Tower.FiniteLevelChainRule.leftExpCurve_neg <;> assumption
theorem isDifferentiableFieldCurve_expCurve (ho : OppositeOrientation L n k j)
    {U B : Edge L n k j → Matrices.ComplexMatrix2}
    (hval : ∀ b : Edge L n k j, b.IsPositivelyOriented → ∀ t : ℝ,
      leftExpMul ((t : ℂ) • B b) (U b) ∈ PeriodicLattice.complexGaugeGroup) :
    IsDifferentiableFieldCurve PeriodicLattice.complexGaugeGroup univ (expCurve U B) := by
  refine ⟨⟨isOpen_univ, ordConnected_univ, mem_univ _⟩, fun t _ => ⟨fun b _ => ?_, fun b _ => ?_⟩,
    fun b hb => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [expCurve_of_pos U B t hb]
      exact hval b hb t
    · rw [expCurve_of_not_pos U B t hb]
      exact inv_mem_complexGaugeGroup (hval _ ((ho b).2 hb) t)
  · by_cases hb : b.IsPositivelyOriented
    · rw [expCurve_of_not_pos U B t ((ho b).1 hb), expCurve_of_pos U B t hb]
      rfl
    · rw [expCurve_of_not_pos U B t hb, expCurve_of_pos U B t ((ho b).2 hb),
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hval _ ((ho b).2 hb) t))]
  · have he : (fun t => expCurve U B t b) = fun t : ℝ => leftExpMul ((t : ℂ) • B b) (U b) :=
      funext fun t => expCurve_of_pos U B t hb
    rw [he]
    exact fun t _ => (hasDerivAt_leftExpMul (B b) (U b) t).differentiableAt.differentiableWithinAt
theorem expCurve_zero {U : Edge L n k j → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (B : Edge L n k j → Matrices.ComplexMatrix2) : expCurve U B 0 = U := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [expCurve_of_pos U B 0 hb]
    simp [leftExpMul]
  · rw [expCurve_of_not_pos U B 0 hb]
    have h : U b.opposite = (U b)⁻¹ := hU.2 b trivial
    simp only [leftExpMul, Complex.ofReal_zero, zero_smul, smul_zero,
      Matrices.ComplexMatrix2.matExp, NormedSpace.exp_zero, one_mul]
    rw [h, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hU.1 b trivial))]
theorem curveTangent_expCurve (ho : OppositeOrientation L n k j)
    {U B : Edge L n k j → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hrev : ∀ b : Edge L n k j, B b.opposite = -B b) : curveTangent (expCurve U B) = B := by
  have key : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      Complex.I⁻¹ • (deriv (fun t => expCurve U B t b) 0 * (expCurve U B 0 b)⁻¹) = B b := by
    intro b hb
    have he : (fun t => expCurve U B t b) = fun t : ℝ => leftExpMul ((t : ℂ) • B b) (U b) :=
      funext fun t => expCurve_of_pos U B t hb
    rw [he, (hasDerivAt_leftExpMul (B b) (U b) 0).deriv, expCurve_zero hU B]
    simp only [Complex.ofReal_zero, zero_smul, Matrices.ComplexMatrix2.matExp,
      NormedSpace.exp_zero, one_mul]
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_of_mem (hU.1 b trivial))]
    exact inv_smul_smul₀ Complex.I_ne_zero _
  funext b
  unfold curveTangent extendOddly
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb]
    exact key b hb
  · rw [if_neg hb]
    beta_reduce
    rw [key _ ((ho b).2 hb), hrev, neg_neg]
theorem curve_mem_near_zero (ho : OppositeOrientation L n k j)
    {𝔇 : Set (Edge L n k j → Matrices.ComplexMatrix2)}
    (h𝔇 : IsOpenFieldSet PeriodicLattice.complexGaugeGroup 𝔇)
    {γ : ℝ → Edge L n k j → Matrices.ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve PeriodicLattice.complexGaugeGroup univ γ) (h0 : γ 0 ∈ 𝔇) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → γ t ∈ 𝔇 := by
  obtain ⟨hsub, A, hA, hAe⟩ := h𝔇
  have hc : Continuous fun t => restrictToPositiveEdges (γ t) :=
    continuous_pi fun b => (differentiableOn_univ.1 (hγ.2.2 b.1 b.2)).continuous
  have hmem : restrictToPositiveEdges (γ 0) ∈ A := by
    have h : restrictToPositiveEdges (γ 0) ∈ restrictToPositiveEdges '' 𝔇 := mem_image_of_mem _ h0
    rw [hAe] at h
    exact h.1
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1
    (hc.continuousAt.eventually_mem (hA.mem_nhds hmem))
  refine ⟨ε, hε, fun t ht => ?_⟩
  have hconf : γ t ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := hγ.2.1 (mem_univ t)
  have hin : restrictToPositiveEdges (γ t) ∈ restrictToPositiveEdges '' 𝔇 := by
    rw [hAe]
    exact ⟨h (by simpa [Real.dist_eq] using ht), fun b => hconf.1 b trivial⟩
  obtain ⟨V, hV, hVe⟩ := hin
  rwa [← eq_of_restrict_eq ho (hsub hV) hconf hVe]
theorem complexIterDeriv_zero (left : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {U B : Edge L n k 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k 0) : complexIterDeriv L n k 0 U B = B := by
  have ho := oppositeOrientation_of (j := 0) hL hn (Nat.zero_le k)
  have hlv := ((left.2.2 L k 0 hL (Nat.zero_le k)).1 n hn).1.1
  have key : ∀ c : Edge L n k 0, c.IsPositivelyOriented →
      logDirectionalDeriv ℂ (fun X => PeriodicLattice.complexBlockFieldAtLevel 0
          (PeriodicLattice.expTwist X U) c)
        (PeriodicLattice.complexBlockFieldAtLevel 0 U c) B = B c := by
    intro c hc
    obtain ⟨hmem, hder⟩ := hlv.2 U hU B hB ⟨c, hc⟩
    have hmem' : ∀ t : ℂ, leftExpMul (t • B c) (U c) ∈ PeriodicLattice.complexGaugeGroup := hmem
    have hder' : HasDerivAt (fun t : ℂ => leftExpMul (t • B c) (U c))
        (Complex.I • B c * U c) 0 := hder
    have hlog := left.2.1 1 one_pos (fun t : ℂ => leftExpMul (t • B c) (U c))
      (fun t _ => hmem' t) hder'.differentiableAt
    have hW0 : leftExpMul ((0 : ℂ) • B c) (U c) = U c := by simp [leftExpMul]
    have hfun : (fun t : ℂ => Matrices.ComplexMatrix2.logSeries
          (PeriodicLattice.complexBlockFieldAtLevel 0
            (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • B) U) c *
            (PeriodicLattice.complexBlockFieldAtLevel 0 U c)⁻¹)) =
        fun t : ℂ => Matrices.ComplexMatrix2.logSeries
          (leftExpMul (t • B c) (U c) * (leftExpMul ((0 : ℂ) • B c) (U c))⁻¹) := by
      funext t
      rw [hW0]
      have e : PeriodicLattice.complexBlockFieldAtLevel 0
          (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • B) U) c =
          leftExpMul (t • B c) (U c) := if_pos hc
      rw [e]
      rfl
    unfold logDirectionalDeriv
    have hgoal := hlog.2.2.1
    simp only [hW0] at hgoal
    rw [hder'.deriv] at hgoal
    simp only [hW0] at hfun
    rw [hfun, hgoal, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_of_mem (hU.1 c trivial))]
    exact inv_smul_smul₀ Complex.I_ne_zero _
  funext c
  unfold complexIterDeriv holLeftDifferential extendOddly
  by_cases hc : c.IsPositivelyOriented
  · rw [if_pos hc]
    exact key c hc
  · rw [if_neg hc]
    beta_reduce
    rw [key _ ((ho c).2 hc), hB.2, neg_neg]
theorem holLeftDifferential_mem (curves : FiniteLevelCurveDifferentials.Statement)
    (left : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (hj' : j' ≤ k)
    {β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless}
    {𝔇 : Set (Edge L n k j → Matrices.ComplexMatrix2)}
    {F : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2}
    (hm : IsHolomorphicFieldMap β 𝔇 F)
    {U B : Edge L n k j → Matrices.ComplexMatrix2} (hU : U ∈ 𝔇)
    (hB : B ∈ complexEdgeForms L n k j) :
    holLeftDifferential F U B ∈ complexEdgeForms L n k j' := by
  have ho := oppositeOrientation_of (j := j) hL hn hj
  have ho' := oppositeOrientation_of (j := j') hL hn hj'
  have hlv := ((left.2.2 L k j hL hj).1 n hn).1.1
  have hUc : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := hm.1.1 hU
  have hγ := isDifferentiableFieldCurve_expCurve (U := U) (B := B) ho
    fun b hb t => (hlv.2 U hUc B hB ⟨b, hb⟩).1 t
  have h0 := expCurve_zero hUc B
  obtain ⟨ε, hε, hin⟩ := curve_mem_near_zero ho hm.1 hγ (by rw [h0]; exact hU)
  have hc := (curves L k j j' hL hj hj' n hn).2.2.1 β 𝔇 F hm U hU univ (expCurve U B) hγ h0
  rw [curveTangent_expCurve ho hUc hB.2] at hc
  rw [← hc.2]
  refine ⟨fun c hcp => ?_, fun c => ?_⟩
  · have hval : curveTangent (fun t => F (expCurve U B t)) c =
        Complex.I⁻¹ • (deriv (fun t => F (expCurve U B t) c) 0 * (F (expCurve U B 0) c)⁻¹) :=
      if_pos hcp
    rw [hval]
    have hI : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) ε) :=
      ⟨Metric.isOpen_ball, (convex_ball (0 : ℝ) ε).ordConnected, Metric.mem_ball_self hε⟩
    have hmaps : MapsTo (fun t => F (expCurve U B t) c) (Metric.ball (0 : ℝ) ε)
        PeriodicLattice.complexGaugeGroup := fun t ht =>
      (hm.2.1 (hin t (by simpa [Real.dist_eq] using ht))).1 c trivial
    exact ((left.1 _ hI).2 _ hmaps (hc.1 c hcp)).2.2.2
  · unfold curveTangent extendOddly
    by_cases hcp : c.IsPositivelyOriented
    · rw [if_neg ((ho' c).1 hcp), if_pos hcp]
      rfl
    · rw [if_pos ((ho' c).2 hcp), if_neg hcp, neg_neg]
theorem isHolomorphicIn_congr {N N' : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    {f g : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn O f)
    (he : ∀ a ∈ O, g a = f a) : Coordinates.ComplexCoordinates.IsHolomorphicIn O g := by apply _root_.YangMills.SharedProofs.p63802 <;> assumption
theorem isHolomorphicToUnimodular_congr
    {β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless}
    {ι κ : Type} [Fintype ι] [Fintype κ] {W : Set (ι ⊕ κ → Matrices.ComplexMatrix2)}
    {Φ Φ' : (ι ⊕ κ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (h : Matrices.GroupLieProduct.IsHolomorphicToUnimodular β W Φ)
    (he : ∀ p ∈ W, Φ' p = Φ p) : Matrices.GroupLieProduct.IsHolomorphicToUnimodular β W Φ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun p hp => he p hp ▸ h2 hp, h3.congr he, fun p hp => ?_⟩
  obtain ⟨O, h0, hO, hh⟩ := h4 p hp
  refine ⟨O, h0, fun A hA => ?_, hh.1, fun ν => ?_⟩
  · rw [he _ (hO A hA).1, he p hp]
    exact hO A hA
  · refine isHolomorphicIn_congr (hh.2 ν) fun a ha => ?_
    simp only [Function.comp_apply]
    rw [he _ (hO _ ha).1, he p hp]
theorem isHolomorphicFieldMap_of_components {i i' : ℕ} [f' : Fintype (PositiveEdge L n k i')]
    (hne : Nonempty (PositiveEdge L n k i'))
    {β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless}
    {𝔇 : Set (Edge L n k i → Matrices.ComplexMatrix2)}
    {F : (Edge L n k i → Matrices.ComplexMatrix2) → Edge L n k i' → Matrices.ComplexMatrix2}
    (hopen : IsOpenFieldSet PeriodicLattice.complexGaugeGroup 𝔇)
    (hmaps : MapsTo F 𝔇 (fieldsIn L n k i' PeriodicLattice.complexGaugeGroup))
    (hmem : ∀ c : Edge L n k i', c.IsPositivelyOriented →
      IsHolomorphicOnFields β 𝔇 fun V => F V c) : IsHolomorphicFieldMap β 𝔇 F := by
  obtain ⟨c₀⟩ := hne
  obtain ⟨-, f, hf⟩ := hmem c₀.1 c₀.2
  refine ⟨hopen, hmaps, f, f', hf.1, fun c => ?_, fun e => e.elim⟩
  obtain ⟨-, f₂, h₂⟩ := hmem c.1 c.2
  obtain rfl : f₂ = f := Subsingleton.elim _ _
  exact h₂
section MeanStable
variable (hP : MeanStableFields.MeanStableConditions L n k)
  (hF : IteratedMeans.TorusConditions L n k)
include hF in
theorem mem_meanStableFields {U : Edge L n k 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ smallIterateFields L n k) : U ∈ meanStableFields L n k k := by
  refine ⟨fun i => PeriodicLattice.complexBlockFieldAtLevel i U, ⟨fun i hi => ?_, fun i hi b => ?_,
    fun i _ c _ => rfl⟩, rfl⟩
  · cases i with
    | zero => exact hU.1
    | succ i => exact hF.meanStep_mem i hi _ (hU.2 i hi)
  · exact (hU.2 i hi).2 b
include hF in
theorem meanSequence_eq {W : Edge L n k 0 → Matrices.ComplexMatrix2}
    {V : ∀ i : ℕ, Edge L n k i → Matrices.ComplexMatrix2}
    (hV : IsMeanSequenceFrom k W V) :
    ∀ i ≤ k, V i = PeriodicLattice.complexBlockFieldAtLevel i W := by apply _root_.YangMills.Construction.Tower.IterLeftChart.meanSequence_eq <;> assumption
include hP hF in
theorem complexBlockField_of_mem {W : Edge L n k 0 → Matrices.ComplexMatrix2}
    (hW : W ∈ meanStableFields L n k k) {i : ℕ} (hi : i ≤ k) :
    PeriodicLattice.complexBlockFieldAtLevel i W ∈
        fieldsIn L n k i PeriodicLattice.complexGaugeGroup ∧
      ∀ c : Edge L n k i, levelwiseMeanAt i c W = PeriodicLattice.complexBlockFieldAtLevel i W c := by
  obtain ⟨V, hV⟩ := hW
  have e := meanSequence_eq hF hV i hi
  refine ⟨e ▸ hV.1.mem_fields i hi, fun c => ?_⟩
  have h := hP.eq_levelwiseMean k le_rfl W V hV i hi c
  rw [← e]
  simp [levelwiseMeanAt, valuesOrOne, h]
include hP hF in
theorem isHolomorphicFieldMap_complexBlockField
    (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    (ho₀ : OppositeOrientation L n k 0) {i : ℕ} (hi : i ≤ k) [Fintype (PositiveEdge L n k i)]
    (hne : Nonempty (PositiveEdge L n k i)) :
    IsHolomorphicFieldMap β (meanStableFields L n k k)
      (PeriodicLattice.complexBlockFieldAtLevel i) := by
  refine isHolomorphicFieldMap_of_components hne hP.isOpen
    (fun W hW => (complexBlockField_of_mem hP hF hW hi).1) fun c hc => ?_
  obtain ⟨hopen, f, hh⟩ := hP.holomorphic_mean i hi c hc β
  refine ⟨hopen, f, isHolomorphicToUnimodular_congr hh fun p hp => ?_⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, rfl⟩ := hp
  have hc' : fieldOfPositiveValues
      (fun b => Matrices.GroupLieProduct.asGroupFactors (restrictToPositiveEdges U) (.inl b)) = U :=
    fieldOfPositiveValues_restrict ho₀ (hP.isOpen.1 hU)
  simp only [hc']
  exact ((complexBlockField_of_mem hP hF hU hi).2 c).symm
include hP hF in
theorem isHolomorphicFieldMap_averageStep
    (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless) {i : ℕ} (hi : i < k)
    [Fintype (PositiveEdge L n k (i + 1))] (hne : Nonempty (PositiveEdge L n k (i + 1))) :
    IsHolomorphicFieldMap β (smallComplexFields L n k i)
      (PeriodicLattice.complexBlockAverageStep i) :=
  isHolomorphicFieldMap_of_components hne (hP.isOpen_nearOne i hi)
    (fun V hV => hF.meanStep_mem i hi V hV)
    fun c hc => hP.holomorphic_smoothing i hi c hc β
end MeanStable
theorem complexIterDerivChain_holds
    (chain : FiniteLevelChainRule.Statement)
    (curves : FiniteLevelCurveDifferentials.Statement)
    (left : LeftChartFields.Claim)
    (stay : MeanStableFields.MeanStableFieldsHold)
    (formed : IteratedMeans.IteratedMeansHold) :
    ComplexIterDerivChain := by
  intro L hL n k hn U hU B hB
  have h0 := complexIterDeriv_zero left hL hn hU.1 hB
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨h0, fun j hj => absurd hj (Nat.not_lt_zero j), fun j hj => ?_⟩
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    rw [h0]
    exact hB
  have hP := (stay L hL k hk).1 n hn
  have hF := (formed L hL k hk).1 n hn
  have ho₀ := oppositeOrientation_of (j := 0) (k := k) hL hn (Nat.zero_le k)
  have hUs := mem_meanStableFields hF hU
  let β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless := OneLoop.pauliBasis
  have hne : ∀ i : ℕ, Nonempty (PositiveEdge L n k i) := fun i =>
    ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, ⟨0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩⟩
  have hfin : ∀ i ≤ k, Finite (PositiveEdge L n k i) := fun i hi =>
    ((left.2.2 L k i hL hi).1 n hn).2.1.1
  refine ⟨h0, fun j hj => ?_, fun j hj => ?_⟩
  · have := hfin j hj.le
    have := hfin (j + 1) hj
    have := Fintype.ofFinite (PositiveEdge L n k j)
    have := Fintype.ofFinite (PositiveEdge L n k (j + 1))
    have h₁ := isHolomorphicFieldMap_complexBlockField hP hF β ho₀ hj.le (hne j)
    have h₂ := isHolomorphicFieldMap_averageStep hP hF β hj (hne (j + 1))
    exact ((chain L k 0 j (j + 1) hL (Nat.zero_le k) hj.le hj n hn).2 β _ _ _ _ h₁ h₂).2 U
      ⟨hUs, hU.2 j hj⟩ B hB
  · have := hfin j hj
    have := Fintype.ofFinite (PositiveEdge L n k j)
    exact holLeftDifferential_mem curves left hL hn (Nat.zero_le k) hj
      (isHolomorphicFieldMap_complexBlockField hP hF β ho₀ hj (hne j)) hUs hB
end YangMills.Construction.Tower.ComplexIterDerivChainProof
end
