import YangMills.Construction.SystemsWithFiveBounds.FieldOperatorAndFreeSlabAtNumbersProof
import YangMills.Construction.Continuum.ConnectedFamiliesAreRealContinuumFamilies
import YangMills.Construction.FamiliesOfLimits.VolumeLimitPointsAreLimitsAlongGrowingTori
import YangMills.Construction.InfiniteLattice.ConnectedFunctionsOfAProbabilityMeasure
import YangMills.Construction.InfiniteLattice.ContinuousLocalFunctionsAreDenseAndTestMeasuresProof
import YangMills.Construction.InfiniteLattice.CubicToriAmongTheToriOfAnyShape
import YangMills.Construction.InfiniteLattice.CumulantsArePolynomialsInTheMomentsAndWeakLimits
import YangMills.Construction.InfiniteLattice.TorusConfigurationsAndMeasuresThroughTheCoveringMapOfACutoff
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfTheFamilyAreLimitsAlongSequences
import Mathlib
set_option autoImplicit false
open Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction
open TestSpaces (SepTupleOfCard)
open InfiniteLattice SeparatedFamilies GibbsAtFixedSpacing TestFunctions
open CutoffLattice (FieldsAt)
open TorusMetric (euclidNormVec)
namespace FamiliesOfLimits.GrowingToriProof
section Forms
variable {P : Type} [Fintype P] [DecidableEq P] {m : ℕ}
theorem norm_multilinear_le_of_basis (Ψ : MultilinearMap ℝ (fun _ : Fin m => P → ℝ) ℂ) {ε : ℝ}
    (hε : ∀ r : Fin m → P, ‖Ψ fun i => Pi.single (r i) (1 : ℝ)‖ ≤ ε) (v : Fin m → P → ℝ)
    {B : Fin m → ℝ} (hB : ∀ i p, |v i p| ≤ B i) :
    ‖Ψ v‖ ≤ (Fintype.card P : ℝ) ^ m * (ε * ∏ i, B i) := by
  have hv : v = fun i => ∑ p, v i p • (Pi.single p (1 : ℝ) : P → ℝ) := by
    funext i q
    simp [Finset.sum_apply, Pi.single_apply]
  have hterm : ∀ r : Fin m → P,
      ‖Ψ fun i => v i (r i) • (Pi.single (r i) (1 : ℝ) : P → ℝ)‖ ≤ ε * ∏ i, B i := by
    intro r
    rw [Ψ.map_smul_univ, norm_smul, mul_comm]
    have h₁ : ‖∏ i, v i (r i)‖ ≤ ∏ i, B i := by
      rw [Real.norm_eq_abs, Finset.abs_prod]
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => hB i (r i)
    exact mul_le_mul (hε r) h₁ (norm_nonneg _) ((norm_nonneg _).trans (hε r))
  rw [hv, Ψ.map_sum]
  calc ‖∑ r : Fin m → P, Ψ fun i => v i (r i) • (Pi.single (r i) (1 : ℝ) : P → ℝ)‖
      ≤ ∑ _r : Fin m → P, ε * ∏ i, B i := norm_sum_le_of_le _ fun r _ => hterm r
    _ = (Fintype.card P : ℝ) ^ m * (ε * ∏ i, B i) := by
        simp [Finset.sum_const, Finset.card_univ]
end Forms
def pointIndicator (x : AmbientSpace) : AmbientSpace → ℝ := Set.indicator {x} 1
theorem abs_pointIndicator_le (x y : AmbientSpace) : |pointIndicator x y| ≤ 1 := by
  by_cases h : y = x
  · simp [pointIndicator, h]
  · simp [pointIndicator, h]
theorem pointIndicator_apply_of_ne {x y : AmbientSpace} (h : y ≠ x) : pointIndicator x y = 0 := by
  simp [pointIndicator, h]
theorem pointIndicator_self (x : AmbientSpace) : pointIndicator x x = 1 := by
  simp [pointIndicator]
theorem hasCompactSupport_pointIndicator (x : AmbientSpace) : HasCompactSupport (pointIndicator x) :=
  HasCompactSupport.intro isCompact_singleton fun _ hy => Set.indicator_of_notMem hy _
theorem pointIndicator_mem (x : AmbientSpace) : pointIndicator x ∈ boundedCompactlySupported :=
  ⟨⟨1, abs_pointIndicator_le x⟩, hasCompactSupport_pointIndicator x⟩
theorem isBoundedBorelCompactlySupported_pointIndicator (x : AmbientSpace) :
    IsBoundedBorelCompactlySupported (pointIndicator x) :=
  ⟨measurable_const.indicator (measurableSet_singleton x),
    ⟨1, fun y => by simpa using abs_pointIndicator_le x y⟩, hasCompactSupport_pointIndicator x⟩
def indicatorCombination {P : Type} [Fintype P] (pt : P → AmbientSpace) (w : P → ℝ) :
    AmbientSpace → ℝ :=
  ∑ q, w q • pointIndicator (pt q)
theorem indicatorCombination_add {P : Type} [Fintype P] (pt : P → AmbientSpace) (w w' : P → ℝ) :
    indicatorCombination pt (w + w') =
      (1 : ℝ) • indicatorCombination pt w + (1 : ℝ) • indicatorCombination pt w' := by
  simp [indicatorCombination, add_smul, Finset.sum_add_distrib]
theorem indicatorCombination_smul {P : Type} [Fintype P] (pt : P → AmbientSpace) (c : ℝ)
    (w : P → ℝ) :
    indicatorCombination pt (c • w) =
      c • indicatorCombination pt w + (0 : ℝ) • indicatorCombination pt w := by
  simp [indicatorCombination, Finset.smul_sum, smul_smul]
theorem indicatorCombination_single {P : Type} [Fintype P] [DecidableEq P] (pt : P → AmbientSpace)
    (q : P) : indicatorCombination pt (Pi.single q (1 : ℝ)) = pointIndicator (pt q) := by
  simp [indicatorCombination, Pi.single_apply, ite_smul]
def IsSlotLinear {m : ℕ} (T : (Fin m → AmbientSpace → ℝ) → ℂ) : Prop :=
  ∀ f : Fin m → AmbientSpace → ℝ, (∀ i, f i ∈ boundedCompactlySupported) →
    ∀ (l : Fin m) (g g' : AmbientSpace → ℝ) (a a' : ℝ), g ∈ boundedCompactlySupported →
      g' ∈ boundedCompactlySupported →
      T (update f l (a • g + a' • g')) = (a : ℂ) * T (update f l g) + (a' : ℂ) * T (update f l g')
def slotLinearForm {m : ℕ} {P : Type} [Fintype P] (pt : P → AmbientSpace)
    (hc : ∀ w : P → ℝ, indicatorCombination pt w ∈ boundedCompactlySupported)
    (T : (Fin m → AmbientSpace → ℝ) → ℂ) (hT : IsSlotLinear T) :
    MultilinearMap ℝ (fun _ : Fin m => P → ℝ) ℂ where
  toFun v := T fun i => indicatorCombination pt (v i)
  map_update_add' := by
    intro inst v l x y
    obtain rfl : inst = instDecidableEqFin m := Subsingleton.elim _ _
    have e : ∀ w : P → ℝ, (fun i => indicatorCombination pt (update v l w i)) =
        update (fun i => indicatorCombination pt (v i)) l (indicatorCombination pt w) := fun w => by
      funext i
      by_cases h : i = l
      · subst h
        simp
      · simp [update_of_ne h]
    simp only [e, indicatorCombination_add]
    simpa using hT _ (fun i => hc _) l _ _ 1 1 (hc x) (hc y)
  map_update_smul' := by
    intro inst v l c x
    obtain rfl : inst = instDecidableEqFin m := Subsingleton.elim _ _
    have e : ∀ w : P → ℝ, (fun i => indicatorCombination pt (update v l w i)) =
        update (fun i => indicatorCombination pt (v i)) l (indicatorCombination pt w) := fun w => by
      funext i
      by_cases h : i = l
      · subst h
        simp
      · simp [update_of_ne h]
    simp only [e, indicatorCombination_smul]
    simpa [Complex.real_smul] using hT _ (fun i => hc _) l _ _ c 0 (hc x) (hc x)
variable {L K : ℕ}
theorem truncatedCorrelation_congr_center (μ : Measure (FieldsAt L K)) {n : ℕ}
    {f f' : Fin n → AmbientSpace → ℝ}
    (h : ∀ i (q : ElementaryPlaquette (CutoffLattice.spacingAt L K)),
      f i q.center = f' i q.center) :
    truncatedCorrelation μ f = truncatedCorrelation μ f' := by
  unfold truncatedCorrelation
  congr 1
  funext i U
  unfold smearedObservable
  have hS : {q : ElementaryPlaquette (CutoffLattice.spacingAt L K) | f i q.center ≠ 0} =
      {q | f' i q.center ≠ 0} := Set.ext fun q => by simp only [Set.mem_ofPred_eq, h i q]
  exact finsum_mem_congr hS fun q _ => by rw [h i q]
theorem isSlotLinear_sub (hform : ∀ (μ : Measure (FieldsAt L K)),
      IsProbabilityMeasure μ → ∀ n : ℕ, 1 ≤ n → TruncatedCorrelationWellDefined μ n)
    (μ μ' : Measure (FieldsAt L K)) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {n : ℕ} (hn : 1 ≤ n) :
    IsSlotLinear fun f : Fin n → AmbientSpace → ℝ =>
      truncatedCorrelation μ f - truncatedCorrelation μ' f := by
  intro f hf l g g' a a' hg hg'
  have h₁ := (hform μ inferInstance n hn).slot_linear f hf l g g' a a' hg hg'
  have h₂ := (hform μ' inferInstance n hn).slot_linear f hf l g g' a a' hg hg'
  simp only [h₁, h₂]
  ring
theorem eventually_truncatedCorrelation_near
    (hM : TruncatedCorrelationsOfProbabilityMeasures)
    (hCum : CumulantsPolynomialInMomentsAndWeakLimits)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (ha : 0 < refinedSpacing L K)
    {ρ : ℕ → BorelProb (refinedSpacing L K)} {p : BorelProb (refinedSpacing L K)}
    (hρ : BorelProb.TendstoWeak ρ p) (R : ℝ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ n, 2 ≤ n → n ≤ N → ∀ f : Fin n → AmbientSpace → ℝ,
      (∀ k, f k ∈ boundedCompactlySupported) →
      (∀ k, Function.support (f k) ⊆ Metric.closedBall (0 : AmbientSpace) R) →
      ∀ B : Fin n → ℝ, (∀ k x, |f k x| ≤ B k) →
        ‖truncatedCorrelation (L := L) (K := K) (ρ i).1 f -
          truncatedCorrelation (L := L) (K := K) p.1 f‖ ≤ ε * ∏ k, B k := by
  classical
  have hform : ∀ (μ : Measure (FieldsAt L K)),
      IsProbabilityMeasure μ → ∀ n : ℕ, 1 ≤ n → TruncatedCorrelationWellDefined μ n :=
    fun μ hμ n hn => (hM L hL).2.1 K hK μ hμ n hn
  have hpp : IsProbabilityMeasure p.1 := p.2
  have hρρ : ∀ i, IsProbabilityMeasure (ρ i).1 := fun i => (ρ i).2
  have hind : Set.indicator (Metric.closedBall (0 : AmbientSpace) R) (1 : AmbientSpace → ℝ) ∈
      boundedCompactlySupported := by
    refine ⟨⟨1, fun x => ?_⟩, HasCompactSupport.intro (isCompact_closedBall 0 R)
      fun _ hy => Set.indicator_of_notMem hy _⟩
    by_cases h : x ∈ Metric.closedBall (0 : AmbientSpace) R <;> simp [h]
  have hfin : {x : AmbientSpace | x ∈ Metric.closedBall (0 : AmbientSpace) R ∧
      ∃ q : ElementaryPlaquette (CutoffLattice.spacingAt L K), q.center = x}.Finite := by
    refine ((hform p.1 hpp 1 le_rfl).finite_support_faces _ hind).image
      (fun q => q.center) |>.subset ?_
    rintro x ⟨hx, q, rfl⟩
    exact ⟨q, by rw [Set.mem_ofPred_eq, Set.indicator_of_mem hx]; simp, rfl⟩
  let Pts := hfin.toFinset
  have hPts : ∀ y, y ∈ Pts ↔ y ∈ Metric.closedBall (0 : AmbientSpace) R ∧
      ∃ q : ElementaryPlaquette (CutoffLattice.spacingAt L K), q.center = y :=
    fun y => Set.Finite.mem_toFinset hfin
  let P : Type := {x // x ∈ Pts}
  let pt : P → AmbientSpace := Subtype.val
  have hc : ∀ w : P → ℝ, indicatorCombination pt w ∈ boundedCompactlySupported := by
    obtain ⟨V, hV⟩ := (hM L hL).1
    intro w
    have : indicatorCombination pt w ∈ (V : Set (AmbientSpace → ℝ)) :=
      V.sum_mem fun q _ => V.smul_mem _ (by
        have := pointIndicator_mem (pt q)
        rw [← hV] at this
        exact this)
    rwa [hV] at this
  set ε' : ℝ := ε / ((Fintype.card P : ℝ) + 1) ^ N with hε'
  have hε'0 : 0 < ε' := by positivity
  have hev : ∀ᶠ i in atTop, ∀ n ∈ Finset.range (N + 1), 2 ≤ n → ∀ r : Fin n → P,
      ‖truncatedCorrelation (L := L) (K := K) (ρ i).1 (fun k => pointIndicator (pt (r k))) -
        truncatedCorrelation (L := L) (K := K) p.1 (fun k => pointIndicator (pt (r k)))‖ ≤ ε' := by
    refine (Filter.eventually_all_finset _).2 fun n _ => ?_
    by_cases hn : 2 ≤ n
    · have : ∀ᶠ i in atTop, ∀ r : Fin n → P,
          ‖truncatedCorrelation (L := L) (K := K) (ρ i).1 (fun k => pointIndicator (pt (r k))) -
            truncatedCorrelation (L := L) (K := K) p.1 (fun k => pointIndicator (pt (r k)))‖ ≤
              ε' := by
        refine Filter.eventually_all.2 fun r => ?_
        have ht := hCum.2.2.1 L K ha ρ p hρ n (fun k => pointIndicator (pt (r k))) hn
          fun k => isBoundedBorelCompactlySupported_pointIndicator _
        have ht' : Tendsto (fun i => truncatedCorrelation (L := L) (K := K) (ρ i).1
            (fun k => pointIndicator (pt (r k)))) atTop
            (𝓝 (truncatedCorrelation (L := L) (K := K) p.1
              (fun k => pointIndicator (pt (r k))))) := by
          simpa only [ursellFunctionOfMeasure, truncatedCorrelation_eq_ursellFunction] using ht
        filter_upwards [(Metric.tendsto_nhds.1 ht') ε' hε'0] with i hi
        rw [← dist_eq_norm]
        exact hi.le
      filter_upwards [this] with i hi _ r using hi r
    · exact Eventually.of_forall fun i h => absurd h hn
  filter_upwards [hev] with i hi n hn hnN f hf hs B hB
  have hB0 : ∀ k, 0 ≤ B k := fun k => (abs_nonneg _).trans (hB k 0)
  let T : (Fin n → AmbientSpace → ℝ) → ℂ := fun f =>
    truncatedCorrelation (L := L) (K := K) (ρ i).1 f - truncatedCorrelation (L := L) (K := K) p.1 f
  have hT : IsSlotLinear T := isSlotLinear_sub hform (ρ i).1 p.1 (by omega)
  let Ψ := slotLinearForm pt hc T hT
  let v : Fin n → P → ℝ := fun k q => f k (pt q)
  have hagree : ∀ k (q : ElementaryPlaquette (CutoffLattice.spacingAt L K)),
      f k q.center = indicatorCombination pt (v k) q.center := by
    intro k q
    have hsum : indicatorCombination pt (v k) q.center =
        ∑ x : P, v k x * pointIndicator (pt x) q.center := by
      simp [indicatorCombination, Finset.sum_apply]
    rw [hsum]
    by_cases hq : q.center ∈ Metric.closedBall (0 : AmbientSpace) R
    · have hmem : q.center ∈ Pts := (hPts _).2 ⟨hq, q, rfl⟩
      rw [Finset.sum_eq_single (⟨q.center, hmem⟩ : P)]
      · simp [v, pt, pointIndicator_self]
      · intro b _ hb
        have : q.center ≠ pt b := fun h => hb (Subtype.ext h.symm)
        simp [pointIndicator_apply_of_ne this]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have h0 : f k q.center = 0 := by
        by_contra h
        exact hq (hs k h)
      rw [h0]
      refine (Finset.sum_eq_zero fun x _ => ?_).symm
      have hx : pt x ∈ Metric.closedBall (0 : AmbientSpace) R := ((hPts _).1 x.2).1
      have : q.center ≠ pt x := fun h => hq (h ▸ hx)
      rw [pointIndicator_apply_of_ne this, mul_zero]
  have hval : T f = Ψ v := by
    change truncatedCorrelation (L := L) (K := K) (ρ i).1 f -
        truncatedCorrelation (L := L) (K := K) p.1 f =
      truncatedCorrelation (L := L) (K := K) (ρ i).1 (fun k => indicatorCombination pt (v k)) -
        truncatedCorrelation (L := L) (K := K) p.1 (fun k => indicatorCombination pt (v k))
    rw [truncatedCorrelation_congr_center (ρ i).1 hagree,
      truncatedCorrelation_congr_center p.1 hagree]
  have hbound := norm_multilinear_le_of_basis Ψ (ε := ε') (fun r => by
      have e : (fun k => indicatorCombination pt (Pi.single (r k) (1 : ℝ))) =
          fun k => pointIndicator (pt (r k)) :=
        funext fun k => indicatorCombination_single pt (r k)
      show ‖T fun k => indicatorCombination pt (Pi.single (r k) (1 : ℝ))‖ ≤ ε'
      rw [e]
      exact hi n (Finset.mem_range.2 (by omega)) hn r) v (B := B) fun k q => hB k _
  rw [← hval] at hbound
  refine hbound.trans ?_
  have hprod : 0 ≤ ∏ k, B k := Finset.prod_nonneg fun k _ => hB0 k
  have hcard : (Fintype.card P : ℝ) ^ n ≤ ((Fintype.card P : ℝ) + 1) ^ N :=
    calc (Fintype.card P : ℝ) ^ n ≤ ((Fintype.card P : ℝ) + 1) ^ n :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) n
      _ ≤ ((Fintype.card P : ℝ) + 1) ^ N :=
          pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card P)]) hnN
  have e : ((Fintype.card P : ℝ) + 1) ^ N * ε' = ε := by
    rw [hε']
    field_simp
  calc (Fintype.card P : ℝ) ^ n * (ε' * ∏ k, B k)
      ≤ ((Fintype.card P : ℝ) + 1) ^ N * (ε' * ∏ k, B k) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ε * ∏ k, B k := by rw [← mul_assoc, e]
theorem exists_mem_cubicTorusLimitStates
    (hP : CutoffCovering.CoveringIdentification)
    (hW : PeriodicLiftAtCutoff.ClusterPointsAreSequentialLimits)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ+) {β : ℝ} (hβ : 0 < β)
    {ν : Measure (GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)))}
    (hν : IsInfiniteVolumeLimit L K β ν) : ∃ p ∈ cubicTorusLimitStates L K β, p.1 = ν := by
  have h₁ := (hP ⟨⟨L, hL, K, ⟨1, one_pos⟩⟩, β, hβ⟩).2.2.2
  have h₂ := (hW L K hL K.pos β hβ).2.1
  have hmem : ν ∈ weakLimitsAlongSides L K β := (Set.ext_iff.1 (h₁.trans h₂.symm) ν).1 hν
  obtain ⟨hp, n, hn, hside, hconv⟩ := hmem
  have hprob : ∀ i, IsProbabilityMeasure (liftedWilsonMeasure L (n i) K β) :=
    fun i => (hP ⟨⟨L, hL, K, ⟨n i, hn i⟩⟩, β, hβ⟩).2.2.1.2.2.1
  exact ⟨⟨ν, hp⟩, ⟨n, fun i => ⟨liftedWilsonMeasure L (n i) K β, hprob i⟩, hn, hside, fun _ => rfl,
    fun F hF => hconv F hF⟩, rfl⟩
theorem exists_torus_exponent
    (hM : TruncatedCorrelationsOfProbabilityMeasures)
    (hCum : CumulantsPolynomialInMomentsAndWeakLimits)
    (hP : CutoffCovering.CoveringIdentification)
    (hW : PeriodicLiftAtCutoff.ClusterPointsAreSequentialLimits)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ+) {β : ℝ} (hβ : 0 < β)
    {ν : Measure (GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)))}
    (hν : IsInfiniteVolumeLimit L K β ν) (R : ℝ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) (ℓ : ℝ) :
    ∃ m : ℕ, 0 < m ∧ ℓ ≤ PeriodicLattice.torusSide L m ∧ ∀ n, 2 ≤ n → n ≤ N →
      ∀ f : Fin n → AmbientSpace → ℝ, (∀ k, f k ∈ boundedCompactlySupported) →
        (∀ k, Function.support (f k) ⊆ Metric.closedBall (0 : AmbientSpace) R) →
        ∀ B : Fin n → ℝ, (∀ k x, |f k x| ≤ B k) →
          ‖ursellFunctionOfMeasure (L := L) (K := K) (liftedWilsonMeasure L m K β) f -
            smearedEnergyCumulant ν f‖ ≤ ε * ∏ k, B k := by
  obtain ⟨p, ⟨m, ρ, hm, hside, hρ, hc⟩, rfl⟩ := exists_mem_cubicTorusLimitStates hP hW hL K hβ hν
  have ha : 0 < refinedSpacing L K := CutoffLattice.spacingAt_pos hL K
  obtain ⟨i, hi₁, hi₂⟩ :=
    ((eventually_truncatedCorrelation_near hM hCum hL K.pos ha hc R N hε).and
      (hside.eventually_ge_atTop ℓ)).exists
  refine ⟨m i, hm i, hi₂, fun n hn hnN f hf hs B hB => ?_⟩
  have h := hi₁ n hn hnN f hf hs B hB
  rw [hρ i, truncatedCorrelation_eq_ursellFunction,
    truncatedCorrelation_eq_ursellFunction] at h
  exact h
theorem norm_le_euclidNormVec (v : AmbientSpace) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.InfiniteLattice.ContinuousLocalDensity.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : AmbientSpace) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.SharedProofs.p8643 <;> assumption
theorem isLipschitzFor_of_isC1c {f : AmbientSpace → ℝ}
    (h : SchwingerFunctions.IsC1c f) : IsLipschitzFor euclidDistR4 f := by apply _root_.YangMills.DeltaSharedProofs.p501087 <;> assumption
theorem exists_pos_real_lower_bound {ι : Type*} (s : Finset ι) (D : ι → ENNReal)
    (hD : ∀ p ∈ s, 0 < D p) :
    ∃ d : ℝ, 0 < d ∧ ∀ p ∈ s, ENNReal.ofReal d ≤ D p := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s _ ih =>
    obtain ⟨d, hd, h⟩ := ih fun p hp => hD p (Finset.mem_insert_of_mem hp)
    obtain ⟨r, hr, hlt⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ D a := by
      obtain ⟨r, -, h0, hlt⟩ :=
        ENNReal.lt_iff_exists_real_btwn.1 (hD a (Finset.mem_insert_self a s))
      exact ⟨r, ENNReal.ofReal_pos.1 h0, hlt.le⟩
    refine ⟨min d r, lt_min hd hr, fun p hp => ?_⟩
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans hlt
    · exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (h p hp)
theorem exists_separation (hO : SchwingerFunctions.RealConnected.ConnectedRealFamilies)
    {n : ℕ} (X : SepTupleOfCard n) : ∃ d : ℝ, HasSeparatedSupportsR4 X.1 d := by
  obtain ⟨d, hd, h⟩ := exists_pos_real_lower_bound
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2)
    (fun p => setDistR4 (tsupport (X.1 p.1)) (tsupport (X.1 p.2)))
    (fun p hp => hO.1.1 _ _ (X.2.1 p.1).2.1 (X.2.1 p.2).2.1 (X.2.2 (Finset.mem_filter.1 hp).2))
  exact ⟨d, hd, fun i k hik => h (i, k) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hik⟩)⟩
theorem infiniteVolumeLimitsAlongGrowingTori_holds
    (hM : TruncatedCorrelationsOfProbabilityMeasures)
    (hCum : CumulantsPolynomialInMomentsAndWeakLimits)
    (hCub : CubicTorusAsQuotient.Statement)
    (hP : CutoffCovering.CoveringIdentification)
    (hW : PeriodicLiftAtCutoff.ClusterPointsAreSequentialLimits)
    (hO : SchwingerFunctions.RealConnected.ConnectedRealFamilies) :
    InfiniteVolumeLimitsAlongGrowingTori := by
  intro L hL sides ℓ₀ hs K β ν hβ hν
  have key : ∀ j : ℕ+, ∃ m : ℕ, 0 < m ∧
      max ℓ₀ (8 * ((j : ℕ) : ℝ) + 8) ≤ PeriodicLattice.torusSide L m ∧
      ∀ n, 2 ≤ n → n ≤ (j : ℕ) →
      ∀ f : Fin n → AmbientSpace → ℝ, (∀ k, f k ∈ boundedCompactlySupported) →
        (∀ k, Function.support (f k) ⊆ Metric.closedBall (0 : AmbientSpace) ((j : ℕ) : ℝ)) →
        ∀ B : Fin n → ℝ, (∀ k x, |f k x| ≤ B k) →
          ‖ursellFunctionOfMeasure (L := L) (K := K j)
              (liftedWilsonMeasure L m (K j) (β j)) f - smearedEnergyCumulant (ν j) f‖ ≤
            1 / ((j : ℕ) : ℝ) * ∏ k, B k := fun j =>
    exists_torus_exponent hM hCum hP hW hL (K j) (hβ j) (hν j) _ _ (by positivity) _
  choose m hm hside hnear using key
  have hj : ∀ j, 8 * (((j : ℕ+) : ℕ) : ℝ) + 8 ≤ PeriodicLattice.torusSide L (m j) := fun j =>
    (le_max_right _ _).trans (hside j)
  have hpnat : Tendsto (fun j : ℕ+ => (j : ℕ)) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b.succPNat, fun a ha => by
      have h₁ : (b.succPNat : ℕ) ≤ (a : ℕ) := ha
      have h₂ : (b.succPNat : ℕ) = b + 1 := rfl
      omega⟩
  have hreal : Tendsto (fun j : ℕ+ => ((j : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpnat
  refine ⟨m, fun j => hs _ (hm j) ((le_max_left _ _).trans (hside j)),
    tendsto_atTop_mono hj (tendsto_atTop_add_const_right _ _
      (hreal.const_mul_atTop (by norm_num))), fun n hn X => ?_⟩
  have hXc : ∀ i, SchwingerFunctions.IsC1c (X.1 i) :=
    fun i => ⟨(X.2.1 i).1, (X.2.1 i).2.1⟩
  obtain ⟨r, hr⟩ :=
    (isCompact_iUnion fun i => (hXc i).2).isBounded.subset_closedBall (0 : AmbientSpace)
  obtain ⟨R, hR⟩ := exists_nat_ge r
  have hbd : ∀ i, ∃ b : ℝ, ∀ x, |X.1 i x| ≤ b := fun i => by
    obtain ⟨b, hb⟩ := (hXc i).2.exists_bound_of_continuous (hXc i).1.continuous
    exact ⟨b, fun x => by simpa using hb x⟩
  choose B hB using hbd
  have hmem : ∀ i, X.1 i ∈ boundedCompactlySupported := fun i => ⟨⟨B i, hB i⟩, (hXc i).2⟩
  have hsupp : ∀ (j : ℕ+), R ≤ (j : ℕ) → ∀ i,
      tsupport (X.1 i) ⊆ Metric.closedBall (0 : AmbientSpace) ((j : ℕ) : ℝ) := fun j hRj i =>
    (Set.subset_iUnion (fun i => tsupport (X.1 i)) i).trans (hr.trans
      (Metric.closedBall_subset_closedBall (hR.trans (by exact_mod_cast hRj))))
  have hdiam : ∀ j : ℕ+, HasDiameterLE (Metric.closedBall (0 : AmbientSpace) ((j : ℕ) : ℝ))
      (PeriodicLattice.torusSide L (m j) / 2) := fun j x hx y hy => by
    have h₁ := euclidNormVec_le_two_mul_norm (x - y)
    have h₂ : ‖x‖ ≤ ((j : ℕ) : ℝ) := by simpa using hx
    have h₃ : ‖y‖ ≤ ((j : ℕ) : ℝ) := by simpa using hy
    have h₄ := norm_sub_le x y
    have h₅ := hj j
    linarith
  have hev : ∀ᶠ j : ℕ+ in atTop, R ≤ (j : ℕ) ∧ n ≤ (j : ℕ) :=
    (hpnat.eventually_ge_atTop R).and (hpnat.eventually_ge_atTop n)
  refine ⟨?_, ?_⟩
  · filter_upwards [hev] with j hj'
    exact ⟨fun i => (hXc i).2, exists_separation hO X, _, fun i =>
      ⟨hdiam j, subset_tsupport _ |>.trans (hsupp j hj'.1 i)⟩⟩
  · have hlim : Tendsto (fun j : ℕ+ => 1 / ((j : ℕ) : ℝ) * ∏ k, B k) atTop (𝓝 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hpnat
      simpa using h.mul_const (∏ k, B k)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev] with j hj'
    have hwithin : IsSeparatedLipschitzTuple (PeriodicLattice.torusSide L (m j)) X.1 :=
      ⟨hn, fun i => isLipschitzFor_of_isC1c (hXc i), fun i => (hXc i).2,
        fun i k hik => X.2.2 hik, _, hdiam j, hsupp j hj'.1⟩
    have e : ursellFunctionOfMeasure (L := L) (K := K j)
        (liftedWilsonMeasure L (m j) (K j) (β j)) X.1 =
        SchwingerFunctions.connectedSchwingerR4 L (m j) (K j) (β j) X.1 :=
      ((hCub ⟨L, hL, K j, ⟨m j, hm j⟩⟩ (β j) (hβ j)).2.2.2).ursellFunctionOfMeasure_eq X.1 hwithin
    rw [← e]
    exact hnear j n hn hj'.2 X.1 hmem (fun k => (subset_tsupport _).trans (hsupp j hj'.1 k)) B
      fun k x => hB k x
end FamiliesOfLimits.GrowingToriProof
end YangMills.Construction
end
