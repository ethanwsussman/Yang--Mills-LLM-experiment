import YangMills.Construction.InfiniteLattice.AlmostEveryConditionalMeasureIsErgodicUnderTheTranslations
import YangMills.Construction.InfiniteLattice.SymmetriesOfAVolumeLimitPoint
import YangMills.Construction.ReflectionPositiveLimits.TheSizesDoNotSeeTheSpacing
import YangMills.Construction.ReflectionPositivity.EnergyMomentumBoundAtCoarseStepsAndInverseSquareLaw
import YangMills.Construction.TotalDensitiesGiveASystem.FarTranslatesFactoriseOverThePhases
import YangMills.Construction.TotalDensitiesGiveASystem.TheMomentsOfThePhasesAreBounded
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped ComplexConjugate Topology
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem.FarTranslatesFactor
open SystemsWithFiveBounds LimitTheorem SeparatedTuples
open InfiniteLattice (GaugeField IsBoundedObservable IsLocalObservable LatticePoint regionObservables
  scaledCube periodicGibbsSet extremalPhases)
open GibbsAtFixedSpacing (BorelProb linfNorm)
open ReflectionPositivity (centeredProduct concat Concatenable latticeSymmetryToEuclid basisOf
  centeredProductLinear pushComb admissibleClass)
open ReflectionPositivity.LatticeRepresentatives (toComplexObs)
open ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare
  (cubeGap reflectionSizeRoots shiftedCorrelation reflectionSize cubeReflectedCorrelation axisReflectObs)
open SmearingFilter (spectralRateFn)
private def asRPTuple (X : SepTuple) : ReflectionPositivity.Tuple :=
  ⟨X.1, fun f hf => ⟨(X.2.1 f hf).1, (X.2.1 f hf).2, Set.subset_univ _⟩, X.2.2⟩
private def ofRPTuple (X : ReflectionPositivity.Tuple) : SepTuple :=
  ⟨X.1, fun f hf => ⟨(X.2.1 f hf).1, (X.2.1 f hf).2.1⟩, X.2.2⟩
private theorem centeredRep_eq_centeredProduct (L K : ℕ)
    (ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ)))
    (X : DisjointTuples.DisjointTuple) (Y : ReflectionPositivity.Tuple) (h : X.1 = Y.1) :
    CenteredRepresentatives.centeredRep L K ν.1 X = centeredProduct L K ν Y := by
  funext U
  unfold CenteredRepresentatives.centeredRep ReflectionPositivity.centeredProduct
  rw [h]
  generalize Y.1 = l
  induction l with
  | nil => simp
  | cons f l ih => simp [List.prod_cons, Pi.mul_apply, ih]
section Phase
variable {s : Conventions.StandingParameters} {K : ℕ+}
private theorem pure_phase_clustering
    (hE : ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare.CombinedBound)
    (hC : ReflectionPositivity.LatticeRepresentatives.Statement)
    {β : ℝ} (hβ : 0 < β) (ν ρ : BorelProb (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)))
    (hν : ν.1 ∈ periodicGibbsSet s.L K β)
    (hρ : ρ.1 ∈ extremalPhases s.L K β) (ha : 0 < (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)))
    (r : ℕ+) (X Y : ReflectionPositivity.Tuple)
    (hX : toComplexObs (centeredProduct s.L K ν X) ∈ regionObservables
      (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) (scaledCube (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) r))
    (hY : toComplexObs (centeredProduct s.L K ν Y) ∈ regionObservables
      (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) (scaledCube (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) r))
    (y : LatticePoint (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)))
    (hy : 1 ≤ cubeGap (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) r y)
    (hd : Concatenable X (ReflectionPositivity.push (latticeSymmetryToEuclid (InfiniteLattice.shift y)) Y)) :
    |(∫ U, centeredProduct s.L K ν (concat _ _ hd) U ∂ρ.1) -
        (∫ U, centeredProduct s.L K ν X U ∂ρ.1) * ∫ U, centeredProduct s.L K ν Y U ∂ρ.1| ≤
      spectralRateFn (((r : ℕ) : ℝ) / cubeGap (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) r y) *
        reflectionSizeRoots ha ρ r (toComplexObs (centeredProduct s.L K ν X))
          (toComplexObs (centeredProduct s.L K ν Y)) := by
  obtain ⟨h1, -, h3⟩ := hE (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) ha
  have hRP : ρ ∈ ReflectionPositivity.LatticeAtSpacing.reflectionPositiveSet
      (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) := h3 β hβ ρ hρ.1
  obtain ⟨-, hlaw, -, -, herg, -⟩ := (h1 ρ hRP).2.2 r _ hX _ hY 0
  have hpl := herg ⟨hρ.1.2, hρ.2.2.2.2⟩
  obtain ⟨-, -, -, hconcat, hmove, -⟩ := (hC s K β ν hβ hν).2.2.1
  have hτ : (InfiniteLattice.shift y).actOn (toComplexObs (centeredProduct s.L K ν Y)) =
      toComplexObs (centeredProduct s.L K ν
        (ReflectionPositivity.push (latticeSymmetryToEuclid (InfiniteLattice.shift y)) Y)) := by
    have h := hmove (InfiniteLattice.shift y) (basisOf Y)
    simp only [basisOf, pushComb, centeredProductLinear,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      one_smul] at h
    exact h.symm
  have hcorr : shiftedCorrelation ρ (toComplexObs (centeredProduct s.L K ν X))
      (toComplexObs (centeredProduct s.L K ν Y)) y =
      ((∫ U, centeredProduct s.L K ν (concat _ _ hd) U ∂ρ.1 : ℝ) : ℂ) := by
    unfold ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare.shiftedCorrelation
    rw [hτ, hconcat _ _ hd]
    refine Eq.trans ?_ (integral_ofReal (μ := ρ.1))
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    simp [toComplexObs]
  have hmean : ∀ T : ReflectionPositivity.Tuple, ρ.integral (toComplexObs (centeredProduct s.L K ν T)) =
      ((∫ U, centeredProduct s.L K ν T U ∂ρ.1 : ℝ) : ℂ) := fun T => by
    exact integral_ofReal (μ := ρ.1)
  have h := hlaw y hy
  rw [hcorr, hpl, hmean, hmean, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h
open Classical in
private def reflectedJoin (ϖ : ℝ) (p : Fin 4 × ReflectionPositivity.reflectionGroup)
    (X : ReflectionPositivity.Tuple) : ReflectionPositivity.Tuple :=
  if h : Concatenable (ReflectionPositivity.mirrorTuple p.1 p.2 X)
      (ReflectionPositivity.translatedTuple ϖ p.1 p.2 X) then concat _ _ h
  else ReflectionPositivity.nilTuple
private theorem reflectionSize_eq_integral
    (hE : ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare.CombinedBound)
    (hS : ReflectionPositivity.SpacingFreeSizes.SizesIndependentOfSpacing)
    {β : ℝ} (hβ : 0 < β) (ν ρ : BorelProb (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)))
    (hν : ν.1 ∈ periodicGibbsSet s.L K β)
    (hρ : ρ.1 ∈ periodicGibbsSet s.L K β) (ha : 0 < (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)))
    (X : ReflectionPositivity.Tuple)
    {ϖ d R : ℝ} (hϖ : ϖ ∈ ReflectionPositivity.posAdicGridPoints s.L) (hd : 0 < d) (hR : 0 < R)
    (hX : X ∈ admissibleClass s ϖ d R) (had : (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) ≤ d / 2)
    (r : ℕ+) (hr : (r : ℝ) = ϖ / (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ))) :
    toComplexObs (centeredProduct s.L K ν X) ∈ regionObservables
      (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) (scaledCube (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) r) ∧
    ∃ p, reflectionSize ha ρ r (toComplexObs (centeredProduct s.L K ν X)) =
      ∫ U, centeredProduct s.L K ν (reflectedJoin ϖ p X) U ∂ρ.1 := by
  obtain ⟨h1, -, h3⟩ := hE (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) ha
  have hRP : ρ ∈ ReflectionPositivity.LatticeAtSpacing.reflectionPositiveSet
      (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) := h3 β hβ ρ hρ
  obtain ⟨⟨hobs, -⟩, hmom, -⟩ := (hS s K β ν ρ hβ hν hρ X).2.2 ϖ hϖ d R hd hR hX had r hr
  refine ⟨hobs, ?_⟩
  have hsz := ((h1 ρ hRP).2.1 r).2.1 _ hobs
  obtain ⟨⟨p, hp⟩, -⟩ := hsz.2.2.2.2.1
  have hγ : p.2.1 ∈ ReflectionPositivity.reflectionGroup := by
    rw [← ReflectionPositivity.SpacingFreeSizes.axisReflectionGroup_eq_reflectionGroup]
    exact p.2.2
  obtain ⟨h, -, -, -, heq⟩ := hmom p.1 ⟨p.2.1, hγ⟩
  refine ⟨(p.1, ⟨p.2.1, hγ⟩), ?_⟩
  have hj : reflectedJoin ϖ (p.1, ⟨p.2.1, hγ⟩) X = concat _ _ h := dif_pos h
  rw [hj, ← hp]
  have hc : cubeReflectedCorrelation ρ p.1 r (axisReflectObs p.2 (toComplexObs (centeredProduct s.L K ν X))) =
      ReflectionPositivity.SpacingFreeSizes.sizeCorr ρ ν r p.1 ⟨p.2.1, hγ⟩ X := rfl
  simp only [hc, heq, Complex.ofReal_re]
  rfl
end Phase
private theorem exists_max_pow_le_sum (l : List ℝ) (hl : ∀ a ∈ l, 0 ≤ a) (n : ℕ) (hn : n ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ a ∈ l, a ≤ M) ∧ M ^ n ≤ (l.map (· ^ n)).sum := by
  induction l with
  | nil => exact ⟨0, le_rfl, by simp, by simp [hn]⟩
  | cons b l ih =>
    obtain ⟨M, hM, hle, hpow⟩ := ih fun a ha => hl a (List.mem_cons_of_mem _ ha)
    have hb := hl b List.mem_cons_self
    have hsum : 0 ≤ (l.map (· ^ n)).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      exact pow_nonneg (hl a (List.mem_cons_of_mem _ ha)) n)
    refine ⟨max b M, le_max_of_le_left hb, ?_, ?_⟩
    · intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · exact le_max_left _ _
      · exact (hle a ha).trans (le_max_right _ _)
    · rw [List.map_cons, List.sum_cons]
      rcases le_total b M with h | h
      · rw [max_eq_right h]
        have := pow_nonneg hb n
        linarith
      · rw [max_eq_left h]
        linarith
private theorem list_prod_le_sum_pow_length (l : List ℝ) (hl : ∀ a ∈ l, 0 ≤ a) (hne : l ≠ []) :
    l.prod ≤ (l.map (· ^ l.length)).sum := by
  have hn : l.length ≠ 0 := by simpa using hne
  obtain ⟨M, hM, hle, hpow⟩ := exists_max_pow_le_sum l hl l.length hn
  refine le_trans ?_ hpow
  clear hpow hn hne
  induction l with
  | nil => simp
  | cons b l ih =>
    have h := ih (fun a ha => hl a (List.mem_cons_of_mem _ ha))
      (fun a ha => hle a (List.mem_cons_of_mem _ ha))
    rw [List.prod_cons, List.length_cons, pow_succ']
    exact mul_le_mul (hle b List.mem_cons_self) h
      (List.prod_nonneg fun a ha => hl a (List.mem_cons_of_mem _ ha)) hM
private theorem sqrt_pow_le_one_add_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (x ^ (1 / 2 : ℝ)) ^ n ≤ 1 + x ^ n := by
  have hr : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx _
  rcases le_total x 1 with h | h
  · have h1 : x ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hx h (by norm_num)
    have := pow_le_one₀ (n := n) hr h1
    have := pow_nonneg hx n
    linarith
  · have h1 : x ^ (1 / 2 : ℝ) ≤ x := by
      calc x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h (by norm_num)
        _ = x := Real.rpow_one x
    have := pow_le_pow_left₀ hr h1 n
    linarith
private theorem exists_rate_mul_le {B ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u, 0 ≤ u → u ≤ δ → spectralRateFn u * B ≤ ε := by
  have hc : Continuous fun u : ℝ => spectralRateFn u * B := by
    unfold spectralRateFn
    fun_prop
  have h0 : spectralRateFn 0 * B = 0 := by simp [spectralRateFn]
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hc 0 ε hε
  refine ⟨δ / 2, by positivity, fun u hu hu' => ?_⟩
  have h1 := h u (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hu]; linarith)
  rw [h0, Real.dist_eq, sub_zero] at h1
  exact (le_abs_self _).trans h1.le
private theorem spectralRateFn_nonneg {u : ℝ} (hc : 0 ≤ SmearingFilter.spectralRateConst) (hu : 0 ≤ u) :
    0 ≤ spectralRateFn u := by
  unfold spectralRateFn
  positivity
private theorem cubeGap_bounds {a t w δ : ℝ} {r : ℕ+} (ha : 0 < a) (ha1 : a ≤ 1) (hδ : 0 < δ)
    (hw : w = (r : ℝ) * a) (ht : 2 * w + w / δ + 1 ≤ t) :
    1 ≤ t / a - 2 * ((r : ℕ) : ℝ) ∧ 0 ≤ ((r : ℕ) : ℝ) / (t / a - 2 * ((r : ℕ) : ℝ)) ∧
      ((r : ℕ) : ℝ) / (t / a - 2 * ((r : ℕ) : ℝ)) ≤ δ := by
  have hwpos : 0 < w := by rw [hw]; positivity
  have he : t / a - 2 * ((r : ℕ) : ℝ) = (t - 2 * w) / a := by
    rw [hw]
    field_simp
  have hq : 0 < w / δ := by positivity
  have h1 : 1 ≤ t / a - 2 * ((r : ℕ) : ℝ) := by
    rw [he, le_div_iff₀ ha]
    linarith
  refine ⟨h1, by positivity, ?_⟩
  rw [div_le_iff₀ (by linarith)]
  rw [he]
  have h2 : w / δ ≤ t - 2 * w := by linarith
  rw [div_le_iff₀ hδ] at h2
  have h3 : ((r : ℕ) : ℝ) = w / a := by
    rw [hw]
    field_simp
  rw [h3, mul_div_assoc', div_le_div_iff_of_pos_right ha]
  linarith
section Index
variable {s : Conventions.StandingParameters} {IsPair : ℕ+ → ℝ → Prop} (Q : PairSequence s.L IsPair)
private theorem meshSize_pos_at (K : ℕ+) : 0 < PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ) :=
  ReflectionPositivity.meshSize_pos s.isAdmissible _
private theorem meshSize_le_one (K : ℕ+) : PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ) ≤ 1 := by
  have hL : (1 : ℝ) ≤ s.L := by
    have := s.isAdmissible.2
    exact_mod_cast (by omega : 1 ≤ s.L)
  unfold PeriodicLattice.meshSize
  rw [zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hL)
private theorem state_isPeriodicGibbs (h₁ : InfiniteLattice.VolumeLimitSymmetries.Statement)
    (hβ : ∀ j, 0 < Q.coupling j) (j : ℕ+) :
    ∃ _ : IsProbabilityMeasure (Q.state j), Q.state j ∈ periodicGibbsSet s.L (Q.cutoff j) (Q.coupling j) := by
  obtain ⟨h, hper, -⟩ := h₁ s.L s.isAdmissible (Q.cutoff j) (Q.coupling j) (hβ j) (Q.state j)
    (Q.isLimit j)
  exact ⟨h, hper⟩
private theorem ae_extremal (h₂ : LatticePhases.AlmostEveryConditionalIsErgodic)
    (hβ : ∀ j, 0 < Q.coupling j)
    {κ : ∀ j, FieldAt Q j →
      InfiniteLattice.GaugeFieldProbability (PeriodicLattice.meshSize s.L (((Q.cutoff j : ℕ)) : ℤ))}
    (hκ : IsConditionalKernel Q κ) (j : ℕ+) [IsProbabilityMeasure (Q.state j)]
    (hper : Q.state j ∈ periodicGibbsSet s.L (Q.cutoff j) (Q.coupling j)) :
    ∀ᵐ U ∂Q.state j, (κ j U).1 ∈ extremalPhases s.L (Q.cutoff j) (Q.coupling j) := by
  let D : LatticePhases.Setup := ⟨s.L, s.isAdmissible, Q.cutoff j, Q.coupling j, hβ j⟩
  obtain ⟨hm, h1, hall⟩ := h₂ D ⟨Q.state j, hper⟩ (κ j) (hκ j)
  have hmeas : MeasurableSet (LatticePhases.ergodicConditionalLocus D (κ j)) :=
    hm.1
  let S : Set (FieldAt Q j) :=
    LatticePhases.ergodicConditionalLocus D (κ j)
  have hmeas' : MeasurableSet S := hmeas
  have h1' : Q.state j S = 1 := h1
  have hae : ∀ᵐ U ∂Q.state j, U ∈ S := mem_ae_iff.2 ((prob_compl_eq_zero_iff hmeas').2 h1')
  filter_upwards [hae] with U hU
  exact hall U hU
private def latticeSite (K : ℕ+) (z : Fin 4 → ℤ) : LatticePoint (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) :=
  ⟨latticePoint z, by
    have hL : (s.L : ℝ) ≠ 0 := by
      have := s.isAdmissible.2
      exact_mod_cast (by omega : s.L ≠ 0)
    refine ⟨fun μ => z μ * (s.L : ℤ) ^ (K : ℕ), fun μ => ?_⟩
    simp only [latticePoint, PeriodicLattice.meshSize, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [zpow_neg, zpow_natCast]
    field_simp⟩
private theorem push_shift_val (K : ℕ+) (z : Fin 4 → ℤ) (Y : SepTuple) :
    (ReflectionPositivity.push (latticeSymmetryToEuclid (InfiniteLattice.shift (latticeSite (s := s) K z)))
      (asRPTuple Y)).1 = (push (translate (latticePoint z)) Y).1 := by
  rw [push_translate_val, pushList_translate]
  refine List.map_congr_left fun f _ => ?_
  funext x
  have h : latticeSymmetryToEuclid (InfiniteLattice.shift (latticeSite (s := s) K z)) =
      ReflectionPositivity.EuclidIsometry.translate (latticePoint z) := rfl
  rw [h]
  simp [ReflectionPositivity.pushFn, ReflectionPositivity.EuclidIsometry.symm_translate]
private theorem centredMean_eq_integral (j : ℕ+) [IsProbabilityMeasure (Q.state j)]
    (ρ : Measure (FieldAt Q j))
    (X : DisjointTuples.DisjointTuple) (Y : ReflectionPositivity.Tuple) (h : X.1 = Y.1) :
    centredMean Q j ρ X = ∫ U, centeredProduct s.L (Q.cutoff j) ⟨Q.state j, inferInstance⟩ Y U ∂ρ := by
  unfold centredMean
  rw [centeredRep_eq_centeredProduct s.L (Q.cutoff j) ⟨Q.state j, inferInstance⟩ X Y h]
private theorem abs_list_prod_map {α : Type*} (l : List α) (g : α → ℝ) :
    |(l.map g).prod| = (l.map fun x => |g x|).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp [abs_mul, ih]
private theorem abs_integral_le_rate_mul
    (hE : ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare.CombinedBound)
    (hC : ReflectionPositivity.LatticeRepresentatives.Statement)
    (h₂ : LatticePhases.AlmostEveryConditionalIsErgodic)
    (hβ : ∀ j, 0 < Q.coupling j)
    {κ : ∀ j, FieldAt Q j →
      InfiniteLattice.GaugeFieldProbability (PeriodicLattice.meshSize s.L (((Q.cutoff j : ℕ)) : ℤ))}
    (hκ : IsConditionalKernel Q κ) (j : ℕ+) [IsProbabilityMeasure (Q.state j)]
    (hper : Q.state j ∈ periodicGibbsSet s.L (Q.cutoff j) (Q.coupling j)) (X Y : SepTuple)
    (W : List SepTuple) (r : ℕ+)
    (hX : toComplexObs (centeredProduct s.L (Q.cutoff j) ⟨Q.state j, inferInstance⟩ (asRPTuple X)) ∈
      regionObservables _ (scaledCube (PeriodicLattice.meshSize s.L (((Q.cutoff j : ℕ)) : ℤ)) r))
    (hY : toComplexObs (centeredProduct s.L (Q.cutoff j) ⟨Q.state j, inferInstance⟩ (asRPTuple Y)) ∈
      regionObservables _ (scaledCube (PeriodicLattice.meshSize s.L (((Q.cutoff j : ℕ)) : ℤ)) r))
    (G : FieldAt Q j → ℝ) (hGi : Integrable G (Q.state j))
    (hG : ∀ᵐ U ∂Q.state j, (κ j U).1 ∈ extremalPhases s.L (Q.cutoff j) (Q.coupling j) →
      reflectionSizeRoots (meshSize_pos_at (s := s) (Q.cutoff j)) (κ j U) r
          (toComplexObs (centeredProduct s.L (Q.cutoff j) ⟨Q.state j, inferInstance⟩ (asRPTuple X)))
          (toComplexObs (centeredProduct s.L (Q.cutoff j) ⟨Q.state j, inferInstance⟩ (asRPTuple Y))) *
        (W.map fun Z => |centredMean Q j (κ j U).1 Z|).prod ≤ G U)
    (z : Fin 4 → ℤ) (hz : 1 ≤ cubeGap _ r (latticeSite (s := s) (Q.cutoff j) z))
    (hq : 0 ≤ spectralRateFn (((r : ℕ) : ℝ) / cubeGap _ r (latticeSite (s := s) (Q.cutoff j) z)))
    (hd : SepTuple.Composable X (push (translate (latticePoint z)) Y)) :
    |∫ U, (centredMean Q j (κ j U).1 (SepTuple.juxt X (push (translate (latticePoint z)) Y)) -
          centredMean Q j (κ j U).1 X * centredMean Q j (κ j U).1 Y) *
        (W.map fun Z => centredMean Q j (κ j U).1 Z).prod ∂Q.state j| ≤
      spectralRateFn (((r : ℕ) : ℝ) / cubeGap _ r (latticeSite (s := s) (Q.cutoff j) z)) *
        ∫ U, G U ∂Q.state j := by
  set q := spectralRateFn (((r : ℕ) : ℝ) / cubeGap _ r (latticeSite (s := s) (Q.cutoff j) z)) with hqdef
  have hd' : Concatenable (asRPTuple X)
      (ReflectionPositivity.push (latticeSymmetryToEuclid (InfiniteLattice.shift (latticeSite (s := s) (Q.cutoff j) z)))
        (asRPTuple Y)) := fun f hf g hg => hd f hf g (by rw [← push_shift_val (s := s) (Q.cutoff j) z Y]; exact hg)
  have hae : ∀ᵐ U ∂Q.state j,
      |(centredMean Q j (κ j U).1 (SepTuple.juxt X (push (translate (latticePoint z)) Y)) -
          centredMean Q j (κ j U).1 X * centredMean Q j (κ j U).1 Y) *
        (W.map fun Z => centredMean Q j (κ j U).1 Z).prod| ≤ q * G U := by
    filter_upwards [ae_extremal Q h₂ hβ hκ j hper, hG] with U hU hGU
    have hcl := pure_phase_clustering hE hC (hβ j) (⟨Q.state j, inferInstance⟩ : BorelProb _) (κ j U) hper hU
      (meshSize_pos_at (s := s) (Q.cutoff j)) r (asRPTuple X) (asRPTuple Y) hX hY _ hz hd'
    rw [← centredMean_eq_integral Q j (κ j U).1 (SepTuple.juxt X (push (translate (latticePoint z)) Y)) _ (by
        rw [SepTuple.juxt_val hd]
        simp only [concat, push_shift_val]
        rfl),
      ← centredMean_eq_integral Q j (κ j U).1 X (asRPTuple X) rfl,
      ← centredMean_eq_integral Q j (κ j U).1 Y (asRPTuple Y) rfl] at hcl
    have hab : |(W.map fun Z => centredMean Q j (κ j U).1 Z).prod| =
        (W.map fun Z => |centredMean Q j (κ j U).1 Z|).prod := abs_list_prod_map W _
    rw [abs_mul, hab]
    have hP : 0 ≤ (W.map fun Z => |centredMean Q j (κ j U).1 Z|).prod :=
      List.prod_nonneg (by
        intro x hx
        obtain ⟨Z, -, rfl⟩ := List.mem_map.1 hx
        exact abs_nonneg _)
    calc _ ≤ (q * reflectionSizeRoots (meshSize_pos_at (s := s) (Q.cutoff j)) (κ j U) r
            (toComplexObs (centeredProduct s.L (Q.cutoff j) ⟨Q.state j, inferInstance⟩ (asRPTuple X)))
            (toComplexObs (centeredProduct s.L (Q.cutoff j) ⟨Q.state j, inferInstance⟩ (asRPTuple Y)))) *
          (W.map fun Z => |centredMean Q j (κ j U).1 Z|).prod := mul_le_mul_of_nonneg_right hcl hP
      _ ≤ q * G U := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hGU hU) hq
  calc _ ≤ ∫ U, |(centredMean Q j (κ j U).1 (SepTuple.juxt X (push (translate (latticePoint z)) Y)) -
          centredMean Q j (κ j U).1 X * centredMean Q j (κ j U).1 Y) *
        (W.map fun Z => centredMean Q j (κ j U).1 Z).prod| ∂Q.state j := abs_integral_le_integral_abs
    _ ≤ ∫ U, q * G U ∂Q.state j := integral_mono_of_nonneg
        (Eventually.of_forall fun U => abs_nonneg _) (hGi.const_mul q) hae
    _ = q * ∫ U, G U ∂Q.state j := integral_const_mul _ _
private theorem exists_cube_of_local {a : ℝ} (ha : 0 < a) {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (hl : IsLocalObservable A) : ∃ r : ℕ+, ∀ r' : ℕ+, r ≤ r' → A ∈ regionObservables a (scaledCube a r') := by
  obtain ⟨S, hb, hm⟩ := hl
  obtain ⟨c, hc⟩ := hb.subset_closedBall 0
  refine ⟨⟨⌈|c| / a⌉₊ + 1, Nat.succ_pos _⟩, fun r' hr' => ⟨hA, ?_⟩⟩
  have hle : (⌈|c| / a⌉₊ : ℝ) + 1 ≤ ((r' : ℕ) : ℝ) := by
    have : ⌈|c| / a⌉₊ + 1 ≤ (r' : ℕ) := hr'
    exact_mod_cast this
  have hca : |c| ≤ ((r' : ℕ) : ℝ) * a := by
    have h1 : |c| / a ≤ ((r' : ℕ) : ℝ) := (Nat.le_ceil _).trans (by linarith)
    rwa [div_le_iff₀ ha] at h1
  have hsub : S ⊆ scaledCube a r' := fun x hx => by
    rw [InfiniteLattice.mem_centeredCube ha]
    intro μ
    have h1 : ‖x‖ ≤ c := by simpa using hc hx
    have h2 : |x μ| ≤ ‖x‖ := norm_le_pi_norm x μ
    have h3 := abs_le.1 (h2.trans (h1.trans ((le_abs_self c).trans hca)))
    exact h3
  exact Measurable.mono hm (InfiniteLattice.regionSigma_mono hsub) le_rfl
section Sizes
open ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare (ReflectionSizeConditions)
variable {a : ℝ} (ha : 0 < a)
private theorem reflectionSize_nonneg {ρ : BorelProb a} (r : ℕ+) (hr : ReflectionSizeConditions ha ρ r)
    {A : GaugeField a → ℂ} (hA : A ∈ regionObservables a (scaledCube a r)) : 0 ≤ reflectionSize ha ρ r A := by
  have hsz := hr.2.1 A hA
  have h0 := hsz.2.2.2.2.2.1 0 1
  have h1 := hsz.2.2.2.2.1.2 ⟨(0, 1), rfl⟩
  exact ((Complex.le_def.1 h0).1).trans h1
private theorem reflectionSizeRoots_le {ρ : BorelProb a} (r : ℕ+) (hr : ReflectionSizeConditions ha ρ r)
    {A B : GaugeField a → ℂ} (hA : A ∈ regionObservables a (scaledCube a r))
    (hB : B ∈ regionObservables a (scaledCube a r)) :
    reflectionSizeRoots ha ρ r A B ≤
      InfiniteLattice.observableSupNorm A * InfiniteLattice.observableSupNorm B := by
  have hn : ∀ C : GaugeField a → ℂ, 0 ≤ InfiniteLattice.observableSupNorm C := fun C =>
    Real.iSup_nonneg fun U => norm_nonneg _
  have hroot : ∀ C ∈ regionObservables a (scaledCube a r),
      reflectionSize ha ρ r C ^ (1 / 2 : ℝ) ≤ InfiniteLattice.observableSupNorm C := fun C hC => by
    have h1 := (hr.2.2.1.2 C hC).2.2
    have h2 := Real.rpow_le_rpow (reflectionSize_nonneg ha r hr hC) h1
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h3 : (InfiniteLattice.observableSupNorm C ^ 2) ^ (1 / 2 : ℝ) =
        InfiniteLattice.observableSupNorm C := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (hn C)]
    rwa [h3] at h2
  exact mul_le_mul (hroot A hA) (hroot B hB) (Real.rpow_nonneg
    (reflectionSize_nonneg ha r hr hB) _) (hn A)
end Sizes
variable {S : CumulantFamily}
  {κ : ∀ j, FieldAt Q j →
      InfiniteLattice.GaugeFieldProbability (PeriodicLattice.meshSize s.L (((Q.cutoff j : ℕ)) : ℤ))}
private theorem sum_pow_moments_bounded (h₈ : phaseMomentsBoundedStatement) (hβ : ∀ j, 0 < Q.coupling j)
    (hS : Q.Defines S) (hκ : IsConditionalKernel Q κ) (n : ℕ) (T : List SepTuple) :
    ∃ C : ℝ, ∀ j, Integrable (fun U => (T.map fun Z => |centredMean Q j (κ j U).1 Z| ^ n).sum) (Q.state j) ∧
      ∫ U, (T.map fun Z => |centredMean Q j (κ j U).1 Z| ^ n).sum ∂Q.state j ≤ C := by
  induction T with
  | nil => exact ⟨0, fun j => ⟨integrable_zero _ _ _, (integral_zero _ _).le⟩⟩
  | cons Z T ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨C', hC'⟩ := h₈ s.L s.isAdmissible IsPair Q S hβ hS κ hκ Z n
    refine ⟨C' + C, fun j => ?_⟩
    exact ⟨(hC' j).1.add (hC j).1,
      (integral_add (hC' j).1 (hC j).1).le.trans (add_le_add (hC' j).2 (hC j).2)⟩
private theorem exists_means_prod_bound (hC : ReflectionPositivity.LatticeRepresentatives.Statement)
    (hβ : ∀ j, 0 < Q.coupling j) (j : ℕ+) [IsProbabilityMeasure (Q.state j)]
    (hper : Q.state j ∈ periodicGibbsSet s.L (Q.cutoff j) (Q.coupling j)) (W : List SepTuple) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : Measure (FieldAt Q j), IsProbabilityMeasure ρ →
      (W.map fun Z => |centredMean Q j ρ Z|).prod ≤ B := by
  induction W with
  | nil => exact ⟨1, zero_le_one, fun ρ _ => le_rfl⟩
  | cons Z W ih =>
    obtain ⟨B, hB, hle⟩ := ih
    have hobs := ((hC s (Q.cutoff j) (Q.coupling j) ⟨Q.state j, inferInstance⟩ (hβ j) hper).2.2.1.1
      (asRPTuple Z)).2.1
    obtain ⟨-, c, hc⟩ := hobs
    refine ⟨|c| * B, by positivity, fun ρ hρ => ?_⟩
    have h1 : |centredMean Q j ρ Z| ≤ |c| := by
      rw [centredMean_eq_integral Q j ρ Z (asRPTuple Z) rfl]
      have := norm_integral_le_of_norm_le_const (μ := ρ) (Eventually.of_forall fun U =>
        (by simpa [toComplexObs] using (hc U).trans (le_abs_self c) :
          ‖centeredProduct s.L (Q.cutoff j) ⟨Q.state j, inferInstance⟩ (asRPTuple Z) U‖ ≤ |c|))
      simpa using this
    exact mul_le_mul h1 (hle ρ hρ) (List.prod_nonneg (by
      intro x hx
      obtain ⟨Z', -, rfl⟩ := List.mem_map.1 hx
      exact abs_nonneg _)) (abs_nonneg _)
private theorem natCast_le_linfNorm {z : Fin 4 → ℤ} {R : ℕ} (hz : ∃ μ, (R : ℤ) ≤ |z μ|) :
    (R : ℝ) ≤ linfNorm (latticePoint z) := by
  obtain ⟨μ, hμ⟩ := hz
  have h1 : (R : ℝ) ≤ |(z μ : ℝ)| := by exact_mod_cast hμ
  exact h1.trans (Finset.le_sup' (fun μ => |latticePoint z μ|) (Finset.mem_univ μ))
private theorem small_at_coarse
    (h₁ : InfiniteLattice.VolumeLimitSymmetries.Statement)
    (hE : ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare.CombinedBound)
    (hC : ReflectionPositivity.LatticeRepresentatives.Statement)
    (h₂ : LatticePhases.AlmostEveryConditionalIsErgodic)
    (hβ : ∀ j, 0 < Q.coupling j) (hκ : IsConditionalKernel Q κ) (X Y : SepTuple) (W : List SepTuple)
    {ε : ℝ} (hε : 0 < ε) (R₀ : ℕ)
    (hfar : ∀ z : Fin 4 → ℤ, (∃ μ, (R₀ : ℤ) ≤ |z μ|) →
      SepTuple.Composable X (push (translate (latticePoint z)) Y)) (j : ℕ+) :
    ∃ R : ℕ, ∀ z : Fin 4 → ℤ, (∃ μ, (R : ℤ) ≤ |z μ|) →
      |∫ U, (centredMean Q j (κ j U).1 (SepTuple.juxt X (push (translate (latticePoint z)) Y)) -
            centredMean Q j (κ j U).1 X * centredMean Q j (κ j U).1 Y) *
          (W.map fun Z => centredMean Q j (κ j U).1 Z).prod ∂Q.state j| ≤ ε := by
  obtain ⟨hp, hper⟩ := state_isPeriodicGibbs Q h₁ hβ j
  have ha := meshSize_pos_at (s := s) (Q.cutoff j)
  have hcal := (hC s (Q.cutoff j) (Q.coupling j) ⟨Q.state j, inferInstance⟩ (hβ j) hper).2.2.1.1
  obtain ⟨r₁, hr₁⟩ := exists_cube_of_local ha (hcal (asRPTuple X)).2.1 (hcal (asRPTuple X)).2.2
  obtain ⟨r₂, hr₂⟩ := exists_cube_of_local ha (hcal (asRPTuple Y)).2.1 (hcal (asRPTuple Y)).2.2
  set r : ℕ+ := max r₁ r₂ with hr
  have hX := hr₁ r (le_max_left _ _)
  have hY := hr₂ r (le_max_right _ _)
  obtain ⟨BW, hBW, hbound⟩ := exists_means_prod_bound Q hC hβ j hper W
  set NA := InfiniteLattice.observableSupNorm
    (toComplexObs (centeredProduct s.L (Q.cutoff j) ⟨Q.state j, inferInstance⟩ (asRPTuple X))) with hNA
  set NB := InfiniteLattice.observableSupNorm
    (toComplexObs (centeredProduct s.L (Q.cutoff j) ⟨Q.state j, inferInstance⟩ (asRPTuple Y))) with hNB
  have hNA0 : 0 ≤ NA := Real.iSup_nonneg fun U => norm_nonneg _
  have hNB0 : 0 ≤ NB := Real.iSup_nonneg fun U => norm_nonneg _
  obtain ⟨δ, hδ, hsmall⟩ := exists_rate_mul_le (B := NA * NB * BW) hε
  set w : ℝ := (r : ℝ) * PeriodicLattice.meshSize s.L (((Q.cutoff j : ℕ)) : ℤ) with hw
  refine ⟨max R₀ ⌈2 * w + w / δ + 1⌉₊, fun z hz => ?_⟩
  have hz₀ : ∃ μ, (R₀ : ℤ) ≤ |z μ| := by
    obtain ⟨μ, hμ⟩ := hz
    exact ⟨μ, le_trans (by exact_mod_cast le_max_left _ _) hμ⟩
  have ht : 2 * w + w / δ + 1 ≤ linfNorm (latticePoint z) :=
    (Nat.le_ceil _).trans ((by exact_mod_cast le_max_right _ _ :
      ((⌈2 * w + w / δ + 1⌉₊ : ℕ) : ℝ) ≤ ((max R₀ ⌈2 * w + w / δ + 1⌉₊ : ℕ) : ℝ)).trans
        (natCast_le_linfNorm hz))
  obtain ⟨hs1, hs2, hs3⟩ := cubeGap_bounds (r := r) ha (meshSize_le_one (Q.cutoff j)) hδ hw ht
  have hrc : 0 ≤ SmearingFilter.spectralRateConst := by
    obtain ⟨h1, -, h3⟩ := hE _ ha
    have hRP := h3 _ (hβ j) (⟨Q.state j, inferInstance⟩ : BorelProb _) hper
    exact ((h1 _ hRP).2.2 r _ hX _ hY 0).2.2.2.1.1
  have hq := spectralRateFn_nonneg hrc hs2
  have hmain := abs_integral_le_rate_mul Q hE hC h₂ hβ hκ j hper X Y W r hX hY (fun _ => NA * NB * BW)
    (integrable_const _) ?_ z hs1 hq (hfar z hz₀)
  · have hi : ∫ _ : FieldAt Q j, NA * NB * BW ∂Q.state j = NA * NB * BW := by simp
    rw [hi] at hmain
    exact hmain.trans (hsmall _ hs2 hs3)
  · refine Eventually.of_forall fun U hU => ?_
    obtain ⟨h1, -, h3⟩ := hE _ ha
    have hRP := h3 _ (hβ j) (κ j U) hU.1
    have hsz := reflectionSizeRoots_le ha r ((h1 _ hRP).2.1 r) hX hY
    have hP := hbound (κ j U).1 (κ j U).2
    have hP0 : 0 ≤ (W.map fun Z => |centredMean Q j (κ j U).1 Z|).prod :=
      List.prod_nonneg (by
        intro x hx
        obtain ⟨Z, -, rfl⟩ := List.mem_map.1 hx
        exact abs_nonneg _)
    exact mul_le_mul hsz hP hP0 (mul_nonneg hNA0 hNB0)
private theorem le_list_sum_of_mem {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) {T : List α} {Z : α}
    (h : Z ∈ T) : f Z ≤ (T.map f).sum := by
  induction T with
  | nil => simp at h
  | cons b T ih =>
    have hs : 0 ≤ (T.map f).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      exact hf a)
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · linarith
    · have := ih h
      have := hf b
      linarith
private theorem sqrt_mul_sqrt_mul_prod_le {NX NY Sg : ℝ} (hX : 0 ≤ NX) (hY : 0 ≤ NY) (l : List ℝ)
    (hl : ∀ a ∈ l, 0 ≤ a) {n : ℕ} (hn : n = l.length + 2) (hXS : NX ^ n ≤ Sg) (hYS : NY ^ n ≤ Sg)
    (hlS : (l.map (· ^ n)).sum ≤ Sg) :
    NX ^ (1 / 2 : ℝ) * NY ^ (1 / 2 : ℝ) * l.prod ≤ 2 + 3 * Sg := by
  have hx := Real.rpow_nonneg hX (1 / 2 : ℝ)
  have hy := Real.rpow_nonneg hY (1 / 2 : ℝ)
  have h := list_prod_le_sum_pow_length (NX ^ (1 / 2 : ℝ) :: NY ^ (1 / 2 : ℝ) :: l) (by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hx
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hy
    · exact hl a ha) (by simp)
  have hlen : (NX ^ (1 / 2 : ℝ) :: NY ^ (1 / 2 : ℝ) :: l).length = n := by simp [hn]
  rw [hlen] at h
  simp only [List.prod_cons, List.map_cons, List.sum_cons] at h
  have h1 := sqrt_pow_le_one_add_pow hX n
  have h2 := sqrt_pow_le_one_add_pow hY n
  rw [mul_assoc]
  linarith
private theorem small_at_fine
    (h₁ : InfiniteLattice.VolumeLimitSymmetries.Statement)
    (hE : ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare.CombinedBound)
    (hC : ReflectionPositivity.LatticeRepresentatives.Statement)
    (h₂ : LatticePhases.AlmostEveryConditionalIsErgodic)
    (hZ : ReflectionPositivity.SpacingFreeSizes.SizesIndependentOfSpacing)
    (hβ : ∀ j, 0 < Q.coupling j) (hκ : IsConditionalKernel Q κ) (X Y : SepTuple) (W : List SepTuple)
    {ε : ℝ} (ϖ : ℕ+) (hϖ : ((ϖ : ℕ) : ℝ) ∈ ReflectionPositivity.posAdicGridPoints s.L)
    {d R₁ : ℝ} (hd : 0 < d) (hR₁ : 0 < R₁)
    (hXc : asRPTuple X ∈ admissibleClass s ((ϖ : ℕ) : ℝ) d R₁)
    (hYc : asRPTuple Y ∈ admissibleClass s ((ϖ : ℕ) : ℝ) d R₁)
    (TT : List SepTuple)
    (hTX : ∀ p, ofRPTuple (reflectedJoin ((ϖ : ℕ) : ℝ) p (asRPTuple X)) ∈ TT)
    (hTY : ∀ p, ofRPTuple (reflectedJoin ((ϖ : ℕ) : ℝ) p (asRPTuple Y)) ∈ TT)
    {C δ : ℝ} (hδ : 0 < δ) (hrc : 0 ≤ SmearingFilter.spectralRateConst)
    (hsmall : ∀ u, 0 ≤ u → u ≤ δ → spectralRateFn u * (2 + 3 * C) ≤ ε)
    (hmom : ∀ j, Integrable (fun U => ((TT ++ W).map fun Z =>
        |centredMean Q j (κ j U).1 Z| ^ (W.length + 2)).sum) (Q.state j) ∧
      ∫ U, ((TT ++ W).map fun Z => |centredMean Q j (κ j U).1 Z| ^ (W.length + 2)).sum ∂Q.state j ≤ C)
    (j : ℕ+) (hj : PeriodicLattice.meshSize s.L (((Q.cutoff j : ℕ)) : ℤ) ≤ d / 2)
    (z : Fin 4 → ℤ) (ht : 2 * ((ϖ : ℕ) : ℝ) + ((ϖ : ℕ) : ℝ) / δ + 1 ≤ linfNorm (latticePoint z))
    (hfar : SepTuple.Composable X (push (translate (latticePoint z)) Y)) :
    |∫ U, (centredMean Q j (κ j U).1 (SepTuple.juxt X (push (translate (latticePoint z)) Y)) -
          centredMean Q j (κ j U).1 X * centredMean Q j (κ j U).1 Y) *
        (W.map fun Z => centredMean Q j (κ j U).1 Z).prod ∂Q.state j| ≤ ε := by
  obtain ⟨hp, hper⟩ := state_isPeriodicGibbs Q h₁ hβ j
  have ha := meshSize_pos_at (s := s) (Q.cutoff j)
  have hLpos : 0 < s.L := by
    have := s.isAdmissible.2
    omega
  let r : ℕ+ := ϖ * ⟨s.L ^ (Q.cutoff j : ℕ), pow_pos hLpos _⟩
  have hr : (r : ℝ) = ((ϖ : ℕ) : ℝ) / PeriodicLattice.meshSize s.L (((Q.cutoff j : ℕ)) : ℤ) := by
    have hrn : (r : ℕ) = (ϖ : ℕ) * s.L ^ (Q.cutoff j : ℕ) := rfl
    show ((r : ℕ) : ℝ) = _
    rw [hrn, PeriodicLattice.meshSize, zpow_neg, zpow_natCast, div_inv_eq_mul]
    push_cast
    rfl
  have hw : ((ϖ : ℕ) : ℝ) = (r : ℝ) * PeriodicLattice.meshSize s.L (((Q.cutoff j : ℕ)) : ℤ) := by
    rw [hr]
    field_simp
  obtain ⟨hs1, hs2, hs3⟩ := cubeGap_bounds (r := r) ha (meshSize_le_one (Q.cutoff j)) hδ hw ht
  have hq := spectralRateFn_nonneg hrc hs2
  have hXs := fun ρ hρ => reflectionSize_eq_integral (s := s) (K := Q.cutoff j) hE hZ (hβ j)
    (⟨Q.state j, inferInstance⟩ : BorelProb _) ρ hper hρ ha (asRPTuple X) hϖ hd hR₁ hXc hj r hr
  have hYs := fun ρ hρ => reflectionSize_eq_integral (s := s) (K := Q.cutoff j) hE hZ (hβ j)
    (⟨Q.state j, inferInstance⟩ : BorelProb _) ρ hper hρ ha (asRPTuple Y) hϖ hd hR₁ hYc hj r hr
  have hX := (hXs (⟨Q.state j, inferInstance⟩ : BorelProb _) hper).1
  have hY := (hYs (⟨Q.state j, inferInstance⟩ : BorelProb _) hper).1
  have hGi : Integrable (fun U => 2 + 3 * ((TT ++ W).map fun Z =>
      |centredMean Q j (κ j U).1 Z| ^ (W.length + 2)).sum) (Q.state j) :=
    (integrable_const _).add ((hmom j).1.const_mul 3)
  have hmain := abs_integral_le_rate_mul Q hE hC h₂ hβ hκ j hper X Y W r hX hY _ hGi ?_ z hs1 hq hfar
  · refine hmain.trans ?_
    have hint : ∫ U, (2 + 3 * ((TT ++ W).map fun Z =>
        |centredMean Q j (κ j U).1 Z| ^ (W.length + 2)).sum) ∂Q.state j ≤ 2 + 3 * C := by
      rw [integral_add (integrable_const _) ((hmom j).1.const_mul 3), integral_const_mul]
      have := (hmom j).2
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      linarith
    exact (mul_le_mul_of_nonneg_left hint hq).trans (hsmall _ hs2 hs3)
  · refine Eventually.of_forall fun U hU => ?_
    obtain ⟨h1, -, h3⟩ := hE _ ha
    have hRP := h3 _ (hβ j) (κ j U) hU.1
    obtain ⟨-, p, hp₁⟩ := hXs (κ j U) hU.1
    obtain ⟨-, p', hp₂⟩ := hYs (κ j U) hU.1
    have hNX := reflectionSize_nonneg ha r ((h1 _ hRP).2.1 r) hX
    have hNY := reflectionSize_nonneg ha r ((h1 _ hRP).2.1 r) hY
    set f : SepTuple → ℝ := fun Z => |centredMean Q j (κ j U).1 Z| ^ (W.length + 2) with hf
    have hf0 : ∀ Z, 0 ≤ f Z := fun Z => pow_nonneg (abs_nonneg _) _
    have hpow : ∀ (N : ℝ) (Z : SepTuple) (J : ReflectionPositivity.Tuple), 0 ≤ N → Z.1 = J.1 →
        N = ∫ V, centeredProduct s.L (Q.cutoff j) ⟨Q.state j, inferInstance⟩ J V ∂(κ j U).1 →
        N ^ (W.length + 2) = f Z := fun N Z J hN hZJ h => by
      have hm := centredMean_eq_integral Q j (κ j U).1 Z J hZJ
      rw [hf]
      show _ = |centredMean Q j (κ j U).1 Z| ^ (W.length + 2)
      rw [hm, ← h, abs_of_nonneg hN]
    have hTXS := hpow _ (ofRPTuple (reflectedJoin _ p (asRPTuple X))) _ hNX rfl hp₁
    have hTYS := hpow _ (ofRPTuple (reflectedJoin _ p' (asRPTuple Y))) _ hNY rfl hp₂
    refine sqrt_mul_sqrt_mul_prod_le hNX hNY _ ?_ (congrArg (· + 2) (List.length_map _).symm) ?_ ?_ ?_
    · intro a ha'
      obtain ⟨Z, -, rfl⟩ := List.mem_map.1 ha'
      exact abs_nonneg _
    · exact hTXS.le.trans (le_list_sum_of_mem f hf0 (List.mem_append_left _ (hTX p)))
    · exact hTYS.le.trans (le_list_sum_of_mem f hf0 (List.mem_append_left _ (hTY p')))
    · have hTT : 0 ≤ (TT.map f).sum := List.sum_nonneg (by
        intro x hx
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
        exact hf0 a)
      have he : ((TT ++ W).map f).sum = (TT.map f).sum + (W.map f).sum := by
        rw [List.map_append, List.sum_append]
      have hle : (W.map f).sum ≤ ((TT ++ W).map f).sum := by
        rw [he]
        linarith
      exact (congrArg List.sum List.map_map).le.trans hle
end Index
private theorem composable_of_far {ϖ : ℝ} {X Y : SepTuple}
    (hX : asRPTuple X ∈ ReflectionPositivity.tuplesSupportedIn (ReflectionPositivity.centredCube ϖ))
    (hY : asRPTuple Y ∈ ReflectionPositivity.tuplesSupportedIn (ReflectionPositivity.centredCube ϖ))
    {R₀ : ℕ} (hR₀ : 2 * ϖ ≤ R₀) (z : Fin 4 → ℤ) (hz : ∃ μ, (R₀ : ℤ) ≤ |z μ|) :
    SepTuple.Composable X (push (translate (latticePoint z)) Y) := by
  intro f hf g hg
  rw [push_translate_val, pushList_translate] at hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hg
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  rw [tsupport_comp_sub] at hx'
  obtain ⟨μ, hμ⟩ := hz
  have h1 : ReflectionPositivity.maxNorm x < ϖ := hX f hf hx
  have h2 : ReflectionPositivity.maxNorm (x - latticePoint z) < ϖ := hY h hh hx'
  have h3 : |x μ| ≤ ReflectionPositivity.maxNorm x :=
    Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ μ)
  have h4 : |(x - latticePoint z) μ| ≤ ReflectionPositivity.maxNorm (x - latticePoint z) :=
    Finset.le_sup' (fun μ => |(x - latticePoint z) μ|) (Finset.mem_univ μ)
  have h5 : (R₀ : ℝ) ≤ |(z μ : ℝ)| := by exact_mod_cast hμ
  have h6 : |(z μ : ℝ)| ≤ |x μ| + |(x - latticePoint z) μ| := by
    have : (z μ : ℝ) = x μ - (x - latticePoint z) μ := by simp [latticePoint]
    rw [this]
    exact abs_sub _ _
  linarith
theorem farTranslatesFactor_holds (h₁ : InfiniteLattice.VolumeLimitSymmetries.Statement)
    (h₂ : LatticePhases.AlmostEveryConditionalIsErgodic)
    (hE : ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare.CombinedBound)
    (hC : ReflectionPositivity.LatticeRepresentatives.Statement)
    (hZ : ReflectionPositivity.SpacingFreeSizes.SizesIndependentOfSpacing)
    (h₈ : phaseMomentsBoundedStatement) : farTranslatesFactorStatement := by
  intro L hL IsPair Q S hβ hdef κ hκ X Y W ε hε
  obtain ⟨s, rfl⟩ : ∃ s : Conventions.StandingParameters, s.L = L := ⟨⟨L, hL, 1, 1⟩, rfl⟩
  obtain ⟨hp₁, hper₁⟩ := state_isPeriodicGibbs Q h₁ hβ 1
  have hcl := (hC s (Q.cutoff 1) (Q.coupling 1) ⟨Q.state 1, inferInstance⟩ (hβ 1) hper₁).2.2.2.2
  obtain ⟨ϖ, hϖ, d, R₁, hd, hR₁, hcls⟩ := hcl.1 2 ![asRPTuple X, asRPTuple Y]
  have hXc : asRPTuple X ∈ admissibleClass s ((ϖ : ℕ) : ℝ) d R₁ := hcls 0
  have hYc : asRPTuple Y ∈ admissibleClass s ((ϖ : ℕ) : ℝ) d R₁ := hcls 1
  have hXo := hcl.2.1 _ hϖ d R₁ hd hR₁ hXc
  have hYo := hcl.2.1 _ hϖ d R₁ hd hR₁ hYc
  have ha₁ := meshSize_pos_at (s := s) (Q.cutoff 1)
  obtain ⟨hE1, -, hE3⟩ := hE _ ha₁
  have hRP₁ := hE3 _ (hβ 1) (⟨Q.state 1, inferInstance⟩ : BorelProb _) hper₁
  have hcard := ((hE1 _ hRP₁).2.1 1).1.2.2
  have hfin : Finite ReflectionPositivity.DirectionPictures.axisReflectionGroup :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hfin' : Finite ReflectionPositivity.reflectionGroup := by
    rw [← ReflectionPositivity.SpacingFreeSizes.axisReflectionGroup_eq_reflectionGroup]
    exact hfin
  have := Fintype.ofFinite (Fin 4 × ReflectionPositivity.reflectionGroup)
  have hrc : 0 ≤ SmearingFilter.spectralRateConst := by
    have hobs := ((hC s (Q.cutoff 1) (Q.coupling 1) ⟨Q.state 1, inferInstance⟩ (hβ 1) hper₁).2.2.1.1
      (asRPTuple X)).2
    obtain ⟨r, hr⟩ := exists_cube_of_local ha₁ hobs.1 hobs.2
    exact ((hE1 _ hRP₁).2.2 r _ (hr r le_rfl) _ (hr r le_rfl) 0).2.2.2.1.1
  let TT : List SepTuple :=
    ((Finset.univ : Finset (Fin 4 × ReflectionPositivity.reflectionGroup)).toList.map
      fun p => ofRPTuple (reflectedJoin ((ϖ : ℕ) : ℝ) p (asRPTuple X))) ++
    ((Finset.univ : Finset (Fin 4 × ReflectionPositivity.reflectionGroup)).toList.map
      fun p => ofRPTuple (reflectedJoin ((ϖ : ℕ) : ℝ) p (asRPTuple Y)))
  have hTX : ∀ p, ofRPTuple (reflectedJoin ((ϖ : ℕ) : ℝ) p (asRPTuple X)) ∈ TT := fun p =>
    List.mem_append_left _ (List.mem_map.2 ⟨p, by simp, rfl⟩)
  have hTY : ∀ p, ofRPTuple (reflectedJoin ((ϖ : ℕ) : ℝ) p (asRPTuple Y)) ∈ TT := fun p =>
    List.mem_append_right _ (List.mem_map.2 ⟨p, by simp, rfl⟩)
  obtain ⟨C, hmom⟩ := sum_pow_moments_bounded (κ := κ) Q h₈ hβ hdef hκ (W.length + 2) (TT ++ W)
  obtain ⟨δ, hδ, hsmall⟩ := exists_rate_mul_le (B := 2 + 3 * C) hε
  set R₀ : ℕ := ⌈2 * ((ϖ : ℕ) : ℝ) + ((ϖ : ℕ) : ℝ) / δ + 1⌉₊ with hR₀
  have hRle : 2 * ((ϖ : ℕ) : ℝ) + ((ϖ : ℕ) : ℝ) / δ + 1 ≤ R₀ := Nat.le_ceil _
  have hϖ0 : (0 : ℝ) ≤ ((ϖ : ℕ) : ℝ) / δ := by positivity
  have hfar : ∀ z : Fin 4 → ℤ, (∃ μ, (R₀ : ℤ) ≤ |z μ|) →
      SepTuple.Composable X (push (translate (latticePoint z)) Y) :=
    composable_of_far hXo hYo (by linarith)
  have hfine : ∀ᶠ j in atTop, PeriodicLattice.meshSize s.L (((Q.cutoff j : ℕ)) : ℤ) ≤ d / 2 := by
    have hL1 : (1 : ℝ) < s.L := by
      have := s.isAdmissible.2
      exact_mod_cast (by omega : 1 < s.L)
    have h0 : Tendsto (fun n : ℕ => ((s.L : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hL1)
    have h1 := (h0.comp Q.tendsto_cutoff).eventually (ge_mem_nhds (by positivity : 0 < d / 2))
    filter_upwards [h1] with j hj
    have he : PeriodicLattice.meshSize s.L (((Q.cutoff j : ℕ)) : ℤ) = ((s.L : ℝ)⁻¹) ^ (Q.cutoff j : ℕ) := by
      rw [PeriodicLattice.meshSize, zpow_neg, zpow_natCast, inv_pow]
    rw [he]
    exact hj
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hfine
  have hcoarse := fun j => small_at_coarse (κ := κ) Q h₁ hE hC h₂ hβ hκ X Y W hε R₀ hfar j
  choose Rc hRc using hcoarse
  refine ⟨max R₀ ((Finset.Iio J).sup Rc), fun z hz j => ?_⟩
  have hz' : ∀ R : ℕ, R ≤ max R₀ ((Finset.Iio J).sup Rc) → ∃ μ, (R : ℤ) ≤ |z μ| := fun R hR => by
    obtain ⟨μ, hμ⟩ := hz
    exact ⟨μ, le_trans (by exact_mod_cast hR) hμ⟩
  rcases le_or_gt J j with hj | hj
  · exact small_at_fine Q h₁ hE hC h₂ hZ hβ hκ X Y W ϖ hϖ hd hR₁ hXc hYc TT hTX hTY hδ hrc
      hsmall hmom j (hJ j hj) z (hRle.trans (natCast_le_linfNorm (hz' R₀ (le_max_left _ _))))
      (hfar z (hz' R₀ (le_max_left _ _)))
  · exact hRc j z (hz' (Rc j) (le_trans (Finset.le_sup (Finset.mem_Iio.2 hj)) (le_max_right _ _)))
end YangMills.Construction.TotalDensitiesGiveASystem.FarTranslatesFactor
end
