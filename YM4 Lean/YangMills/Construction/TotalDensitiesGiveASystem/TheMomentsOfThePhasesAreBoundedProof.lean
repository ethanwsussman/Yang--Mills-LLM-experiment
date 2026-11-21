import YangMills.Construction.ReflectionPositivity.OneSideAndOneTranslationProof
import YangMills.Construction.SystemsWithFiveBounds.CanonicalDecompositionAlongStatesProof
import YangMills.Construction.InfiniteLattice.AlmostEveryConditionalStateIsAnErgodicPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.CentredIdentityInAState
import YangMills.Construction.InfiniteLattice.LimitPointsOfTheTorusMeasuresArePeriodicGibbsStates
import YangMills.Construction.ReflectionPositiveLimits.LatticeRepresentativesAtOneCutoff
import YangMills.Construction.ReflectionPositiveLimits.LimitsOfLatticeStatesProof
import YangMills.Construction.ReflectionPositiveLimits.PeriodicGibbsStatesAndLatticeApproximations
import YangMills.Construction.TotalDensitiesGiveASystem.TheMomentsOfThePhasesAreBounded
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate ComplexOrder Topology
namespace YangMills.Construction.TotalDensitiesGiveASystem.PhaseMoments
open ReflectionPositivity
open ReflectionPositivity.PeriodicGibbs
open GibbsAtFixedSpacing (BorelProb)
open InfiniteLattice (periodicGibbsSet)
private theorem euclidIsometry_ext {r r' : EuclidIsometry} (h : r.toFun = r'.toFun) : r = r' := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeLimits.euclidIsometry_ext <;> assumption
private def timeTranslationVector (m : ℕ+) : Space := Pi.single timeAxis (m : ℝ)
private theorem pow_mul_meshSize {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ) :
    ((L : ℝ) ^ K) * PeriodicLattice.meshSize L (K : ℤ) = 1 := by
  have h0 : (L : ℝ) ≠ 0 := by
    have := hL.2
    exact_mod_cast (by omega : L ≠ 0)
  unfold PeriodicLattice.meshSize
  rw [zpow_neg, zpow_natCast]
  exact mul_inv_cancel₀ (pow_ne_zero _ h0)
private def timeShiftPoint {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ) (m : ℕ+) :
    InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L (K : ℤ)) :=
  ⟨timeTranslationVector m, Pi.single timeAxis ((m : ℤ) * (L : ℤ) ^ K), fun μ => by
    by_cases h : μ = timeAxis
    · subst h
      have e := pow_mul_meshSize hL K
      simp only [timeTranslationVector, Pi.single_eq_same]
      push_cast
      rw [mul_assoc, e, mul_one]
    · simp [timeTranslationVector, Pi.single_eq_of_ne h]⟩
private theorem latticeSymmetryToEuclid_shift {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ)
    (m : ℕ+) :
    latticeSymmetryToEuclid (InfiniteLattice.shift (timeShiftPoint hL K m)) =
      EuclidIsometry.translate (timeTranslationVector m) :=
  euclidIsometry_ext rfl
private theorem latticeSymmetryToEuclid_timeMirror (a : ℝ) :
    latticeSymmetryToEuclid (LatticeAtSpacing.coordinateMirror a timeAxis).reflect =
      timeZeroMirror.reflectIso := by
  have hn : (LatticeAtSpacing.coordinateMirror a timeAxis).normal = timeZeroMirror.normal := rfl
  have ho : (LatticeAtSpacing.coordinateMirror a timeAxis).height = timeZeroMirror.offset := rfl
  refine euclidIsometry_ext ?_
  funext x
  change (LatticeAtSpacing.coordinateMirror a timeAxis).reflect.toFun x = timeZeroMirror.reflectPt x
  rw [LatticeAtSpacing.reflect_apply, NormalMirror.reflectPt, euclidNormVec_sq, hn, ho]
  congr 2
  change 2 * (euclidInner timeZeroMirror.normal timeZeroMirror.normal)⁻¹ *
    (euclidInner timeZeroMirror.normal x - timeZeroMirror.offset) = _
  ring
private theorem tsupport_push_shift {m : ℕ+} {X : Tuple}
    (hX : ∀ f ∈ X.1, tsupport f ⊆ {x | 1 - (m : ℝ) ≤ x timeAxis}) :
    ∀ f ∈ (push (EuclidIsometry.translate (timeTranslationVector m)) X).1,
      tsupport f ⊆ {x | 1 ≤ euclidInner (PeriodicLattice.coordVec timeAxis) x} := by
  intro g hg y hy
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  rw [tsupport_pushFn] at hy
  have h1 := hX f hf hy
  rw [EuclidIsometry.symm_translate] at h1
  simp only [Set.mem_ofPred_eq, Pi.sub_apply, timeTranslationVector, Pi.single_eq_same] at h1
  rw [Set.mem_ofPred_eq, euclidInner_coordVec]
  linarith
private theorem push_shift_mem_posSide {m : ℕ+} {X : Tuple}
    (hX : ∀ f ∈ X.1, tsupport f ⊆ {x | 1 - (m : ℝ) ≤ x timeAxis}) :
    push (EuclidIsometry.translate (timeTranslationVector m)) X ∈ tuplesSupportedIn timeZeroMirror.posSide := by
  intro f hf y hy
  have h := tsupport_push_shift hX f hf hy
  change 0 < euclidInner (PeriodicLattice.coordVec timeAxis) y
  have h' : 1 ≤ euclidInner (PeriodicLattice.coordVec timeAxis) y := h
  linarith
private theorem sq_integral_le_concat {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hC : LatticeRepresentatives.Statement)
    (hCent : PeriodicGibbsCentered L) (hRP : PeriodicGibbsReflectionPositive L)
    {K : ℕ+} {β : ℝ} (hβ : 0 < β) {ν ρ : BorelProb (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))}
    (hν : ν.1 ∈ periodicGibbsSet L K β) (hρ : ρ.1 ∈ periodicGibbsSet L K β)
    (m : ℕ+) (X : Tuple)
    (hX : ∀ f ∈ X.1, tsupport f ⊆ {x | 1 - (m : ℝ) ≤ x timeAxis})
    (h : Concatenable (push timeZeroMirror.reflectIso (push (EuclidIsometry.translate (timeTranslationVector m)) X))
      (push (EuclidIsometry.translate (timeTranslationVector m)) X)) :
    (∫ U, centeredProduct L K ν X U ∂ρ.1) ^ 2 ≤
      ∫ U, centeredProduct L K ν (concat _ _ h) U ∂ρ.1 := by
  have hρp := ρ.2
  obtain ⟨-, -, hCalc, hLoc, -⟩ := hC ⟨L, hL, K, 1⟩ K β ν hβ hν
  obtain ⟨hobs, -, -, hcat, hmove, -⟩ := hCalc
  have hLoc' := hLoc.2
  obtain ⟨hinvρ, -⟩ := hCent K β hβ ρ hρ
  obtain ⟨⟨-, hpos⟩, -, -⟩ := hRP K β hβ ρ hρ
  have hmeas : ∀ Z : Tuple, Measurable (centeredProduct L K ν Z) := fun Z => by
    have := Complex.measurable_re.comp (hobs Z).2.1.1
    exact this
  have hbd : ∀ Z : Tuple, ∃ C : ℝ, ∀ U, ‖centeredProduct L K ν Z U‖ ≤ C := fun Z => by
    obtain ⟨C, hC'⟩ := (hobs Z).2.1.2
    refine ⟨C, fun U => ?_⟩
    have := hC' U
    simpa [LatticeRepresentatives.toComplexObs] using this
  have hint : ∀ Z : Tuple, Integrable (centeredProduct L K ν Z) ρ.1 := fun Z => by
    obtain ⟨C, hC'⟩ := hbd Z
    exact Integrable.of_bound (hmeas Z).aestronglyMeasurable C (Eventually.of_forall hC')
  have hRC : ∀ A : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)) → ℝ,
      ∫ U, ((A U : ℝ) : ℂ) ∂ρ.1 = ((∫ U, A U ∂ρ.1 : ℝ) : ℂ) := fun A => integral_ofReal
  have hact : ∀ (r : InfiniteLattice.LatticeSymmetry (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)))
      (Z : Tuple) (U), centeredProduct L K ν (push (latticeSymmetryToEuclid r) Z) U =
        centeredProduct L K ν Z (r.pullbackField U) := fun r Z U => by
    have e := congrFun (hmove r (basisOf Z)) U
    have hb : pushComb (latticeSymmetryToEuclid r) (basisOf Z) =
        basisOf (push (latticeSymmetryToEuclid r) Z) := by
      simp [pushComb, basisOf]
    rw [hb] at e
    have e₁ : ∀ (Y : Tuple) V, centeredProductLinear L K ν (basisOf Y) V =
        ((centeredProduct L K ν Y V : ℝ) : ℂ) := fun Y V => by
      simp [centeredProductLinear, basisOf]
    change centeredProductLinear L K ν (basisOf _) U =
      centeredProductLinear L K ν (basisOf Z) (r.pullbackField U) at e
    rw [e₁, e₁] at e
    exact_mod_cast e
  have hinv : ∀ (r : InfiniteLattice.LatticeSymmetry (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)))
      (Z : Tuple), ∫ U, centeredProduct L K ν (push (latticeSymmetryToEuclid r) Z) U ∂ρ.1 =
        ∫ U, centeredProduct L K ν Z U ∂ρ.1 := fun r Z => by
    have e := hinvρ r _ (hobs Z).2.1
    have e₁ : (fun U => r.actOn (LatticeRepresentatives.toComplexObs
        (centeredProduct L K ν Z)) U) = fun U =>
          ((centeredProduct L K ν (push (latticeSymmetryToEuclid r) Z) U : ℝ) : ℂ) := by
      funext U
      rw [hact]
      rfl
    rw [e₁] at e
    have e₂ : ∫ U, LatticeRepresentatives.toComplexObs (centeredProduct L K ν Z) U ∂ρ.1 =
        ∫ U, ((centeredProduct L K ν Z U : ℝ) : ℂ) ∂ρ.1 := rfl
    rw [e₂] at e
    exact Complex.ofReal_injective ((hRC _).symm.trans (e.trans (hRC _)))
  set Y := push (EuclidIsometry.translate (timeTranslationVector m)) X with hYdef
  set P := LatticeAtSpacing.coordinateMirror (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)) timeAxis with hP
  set c := ∫ U, centeredProduct L K ν X U ∂ρ.1 with hc
  have hYc : ∫ U, centeredProduct L K ν Y U ∂ρ.1 = c := by
    rw [hYdef, ← latticeSymmetryToEuclid_shift hL K m]
    exact hinv _ X
  have hθ : ∫ U, centeredProduct L K ν (push timeZeroMirror.reflectIso Y) U ∂ρ.1 = c := by
    rw [← latticeSymmetryToEuclid_timeMirror (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)), hinv, hYc]
  have hcatU : ∀ U, centeredProduct L K ν (concat _ _ h) U =
      centeredProduct L K ν (push timeZeroMirror.reflectIso Y) U * centeredProduct L K ν Y U := fun U => by
    rw [hcat _ _ h]
    rfl
  have hsq : (0 : ℝ) ≤ ∫ U, (centeredProduct L K ν (push timeZeroMirror.reflectIso Y) U - c) *
      (centeredProduct L K ν Y U - c) ∂ρ.1 := by
    have ha1 : PeriodicLattice.meshSize L ((K : ℕ) : ℤ) ≤ 1 := by
      have e := pow_mul_meshSize hL (K : ℕ)
      have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ (K : ℕ) := one_le_pow₀ (by
        have := hL.2
        exact_mod_cast (by omega : 1 ≤ L))
      nlinarith
    have hs2 : (1 : ℝ) < √2 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have ha : PeriodicLattice.meshSize L ((K : ℕ) : ℤ) / √2 < 1 :=
      (div_lt_one (by linarith)).2 (by linarith)
    have hn1 : TorusMetric.euclidNormVec (PeriodicLattice.coordVec timeAxis) = 1 := by
      have e := euclidNormVec_sq (PeriodicLattice.coordVec timeAxis)
      rw [euclidInner_coordVec] at e
      have e₁ : (PeriodicLattice.coordVec timeAxis : Space) timeAxis = 1 := by
        simp [PeriodicLattice.coordVec]
      rw [e₁] at e
      exact (pow_eq_one_iff_of_nonneg (Real.sqrt_nonneg _) two_ne_zero).1 e
    obtain ⟨S', hb, hS', hF⟩ := hLoc' _ 1 hn1 ha Y (tsupport_push_shift hX)
    have hGS : Measurable[InfiniteLattice.regionSigma S'] (fun U =>
        LatticeRepresentatives.toComplexObs (centeredProduct L K ν Y) U - (c : ℂ)) :=
      hF.2.sub_const _
    have hGobs : InfiniteLattice.IsBoundedObservable (fun U =>
        LatticeRepresentatives.toComplexObs (centeredProduct L K ν Y) U - (c : ℂ)) := by
      obtain ⟨hm, C, hC'⟩ := hF.1
      exact ⟨hm.sub_const _, C + ‖(c : ℂ)‖, fun U => (norm_sub_le _ _).trans (by linarith [hC' U])⟩
    have hside : S' ⊆ P.upperHalf := by
      intro x hx
      have h1 : 0 < euclidInner (PeriodicLattice.coordVec timeAxis) x := hS' hx
      rw [euclidInner_coordVec] at h1
      change (0 : ℝ) ≤ MirrorHyperplanes.basisVec timeAxis ⬝ᵥ x
      rw [MirrorHyperplanes.basisVec_dotProduct]
      exact h1.le
    have hp := hpos P _ ⟨S', hb, hGS⟩
      ⟨hGobs, Measurable.mono hGS (InfiniteLattice.regionSigma_mono hside) le_rfl⟩
    have hθU : ∀ U, centeredProduct L K ν (push timeZeroMirror.reflectIso Y) U =
        centeredProduct L K ν Y (P.reflect.pullbackField U) := fun U => by
      rw [← latticeSymmetryToEuclid_timeMirror (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))]
      exact hact _ _ _
    have e : (fun U => conj (P.reflect.actOn (fun U =>
        LatticeRepresentatives.toComplexObs (centeredProduct L K ν Y) U - (c : ℂ)) U) *
        (LatticeRepresentatives.toComplexObs (centeredProduct L K ν Y) U - (c : ℂ))) =
        fun U => (((centeredProduct L K ν (push timeZeroMirror.reflectIso Y) U - c) *
          (centeredProduct L K ν Y U - c) : ℝ) : ℂ) := by
      funext U
      rw [hθU]
      simp [InfiniteLattice.LatticeSymmetry.actOn, LatticeRepresentatives.toComplexObs]
    have hp' : (0 : ℂ) ≤ ∫ U, (((centeredProduct L K ν (push timeZeroMirror.reflectIso Y) U - c) *
        (centeredProduct L K ν Y U - c) : ℝ) : ℂ) ∂ρ.1 := by
      rw [← e]
      exact hp
    rw [hRC] at hp'
    exact Complex.zero_le_real.1 hp'
  have hexp : ∫ U, (centeredProduct L K ν (push timeZeroMirror.reflectIso Y) U - c) *
      (centeredProduct L K ν Y U - c) ∂ρ.1 =
      (∫ U, centeredProduct L K ν (concat _ _ h) U ∂ρ.1) - c ^ 2 := by
    have e : ∀ U, (centeredProduct L K ν (push timeZeroMirror.reflectIso Y) U - c) *
        (centeredProduct L K ν Y U - c) =
        centeredProduct L K ν (concat _ _ h) U -
          c * centeredProduct L K ν (push timeZeroMirror.reflectIso Y) U -
          c * centeredProduct L K ν Y U + c ^ 2 := fun U => by
      rw [hcatU]
      ring
    have iA := hint (concat _ _ h)
    have iB := hint (push timeZeroMirror.reflectIso Y)
    have iD := hint Y
    have i₁ : Integrable (fun U => centeredProduct L K ν (concat _ _ h) U -
        c * centeredProduct L K ν (push timeZeroMirror.reflectIso Y) U) ρ.1 := iA.sub (iB.const_mul c)
    have i₂ : Integrable (fun U => centeredProduct L K ν (concat _ _ h) U -
        c * centeredProduct L K ν (push timeZeroMirror.reflectIso Y) U -
        c * centeredProduct L K ν Y U) ρ.1 := i₁.sub (iD.const_mul c)
    have h₁ := integral_add i₂ (integrable_const (μ := ρ.1) (c ^ 2))
    have h₂ := integral_sub i₁ (iD.const_mul c)
    have h₃ := integral_sub iA (iB.const_mul c)
    have h₄ : ∫ U, c * centeredProduct L K ν (push timeZeroMirror.reflectIso Y) U ∂ρ.1 = c * c := by
      rw [integral_const_mul, hθ]
    have h₅ : ∫ U, c * centeredProduct L K ν Y U ∂ρ.1 = c * c := by
      rw [integral_const_mul, hYc]
    have h₆ : ∫ _U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)), c ^ 2 ∂ρ.1 =
        c ^ 2 := by
      simp
    calc _ = _ := integral_congr_ae (Eventually.of_forall e)
      _ = _ := h₁
      _ = _ := by rw [h₂, h₃, h₄, h₅, h₆]; ring
  rw [hexp] at hsq
  linarith
private theorem exists_time_floor (X : Tuple) :
    ∃ m : ℕ+, ∀ f ∈ X.1, tsupport f ⊆ {x | 1 - (m : ℝ) ≤ x timeAxis} := by
  have hK : IsCompact (⋃ f ∈ X.1, tsupport f) :=
    (List.finite_toSet X.1).isCompact_biUnion fun f hf => (X.2.1 f hf).2.1
  obtain ⟨b, hb⟩ := (hK.image (continuous_apply timeAxis)).bddBelow
  refine ⟨⟨⌈1 - b⌉₊ + 1, Nat.succ_pos _⟩, fun f hf x hx => ?_⟩
  have h1 : b ≤ x timeAxis := hb ⟨x, Set.mem_iUnion₂.2 ⟨f, hf, hx⟩, rfl⟩
  have h2 : 1 - b ≤ (⌈1 - b⌉₊ : ℝ) := Nat.le_ceil _
  change 1 - (((⌈1 - b⌉₊ + 1 : ℕ)) : ℝ) ≤ x timeAxis
  push_cast
  linarith
private def PowerDominates (L e : ℕ) (X Z : Tuple) : Prop :=
  ∀ (K : ℕ+) (β : ℝ), 0 < β → ∀ ν ρ : BorelProb (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)),
    ν.1 ∈ periodicGibbsSet L K β → ρ.1 ∈ periodicGibbsSet L K β →
      (∫ U, centeredProduct L K ν X U ∂ρ.1) ^ (2 ^ (e + 1)) ≤ ∫ U, centeredProduct L K ν Z U ∂ρ.1
private theorem exists_powerDominates_zero {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hC : LatticeRepresentatives.Statement)
    (hCent : PeriodicGibbsCentered L) (hRP : PeriodicGibbsReflectionPositive L)
    (X : Tuple) : ∃ Z, PowerDominates L 0 X Z := by
  obtain ⟨m, hm⟩ := exists_time_floor X
  have hY := push_shift_mem_posSide hm
  refine ⟨concat _ _ (NormalMirror.concatenable_reflectIso hY hY), ?_⟩
  intro K β hβ ν ρ hν hρ
  simpa using sq_integral_le_concat hL hC hCent hRP hβ hν hρ m X hm
    (NormalMirror.concatenable_reflectIso hY hY)
private theorem exists_powerDominates {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hC : LatticeRepresentatives.Statement)
    (hCent : PeriodicGibbsCentered L) (hRP : PeriodicGibbsReflectionPositive L)
    (X : Tuple) (e : ℕ) : ∃ Z, PowerDominates L e X Z := by
  induction e with
  | zero => exact exists_powerDominates_zero hL hC hCent hRP X
  | succ e ih =>
    obtain ⟨Z, hZ⟩ := ih
    obtain ⟨Z', hZ'⟩ := exists_powerDominates_zero hL hC hCent hRP Z
    refine ⟨Z', ?_⟩
    intro K β hβ ν ρ hν hρ
    have h₁ := hZ K β hβ ν ρ hν hρ
    have h₂ := hZ' K β hβ ν ρ hν hρ
    set x := ∫ U, centeredProduct L K ν X U ∂ρ.1
    have e₁ : x ^ (2 ^ (e + 1 + 1)) = (x ^ (2 ^ (e + 1))) ^ 2 := by
      rw [← pow_mul, pow_succ 2 (e + 1)]
    have e₂ : 0 ≤ x ^ (2 ^ (e + 1)) := by
      rw [pow_succ 2 e, pow_mul]
      exact sq_nonneg _
    rw [e₁]
    have e₃ := pow_le_pow_left₀ e₂ h₁ 2
    simp only [zero_add, pow_one] at h₂
    exact e₃.trans h₂
private theorem abs_pow_le_one_add (x : ℝ) (t : ℕ) : |x| ^ t ≤ 1 + x ^ (2 ^ (t + 1)) := by
  have hev : x ^ (2 ^ (t + 1)) = |x| ^ (2 ^ (t + 1)) :=
    (Even.pow_abs ⟨2 ^ t, by rw [pow_succ]; ring⟩ x).symm
  rw [hev]
  have h0 : 0 ≤ |x| ^ (2 ^ (t + 1)) := pow_nonneg (abs_nonneg x) _
  rcases le_total |x| 1 with h | h
  · have := pow_le_one₀ (n := t) (abs_nonneg x) h
    linarith
  · have hlt : t ≤ 2 ^ (t + 1) := by
      have := Nat.lt_two_pow_self (n := t + 1)
      omega
    have := pow_le_pow_right₀ h hlt
    linarith
private def BddSeq (x : ℕ+ → ℂ) : Prop := ∃ B : ℝ, ∀ j, ‖x j‖ ≤ B
private theorem bddSeq_of_tendsto {x : ℕ+ → ℂ} {l : ℂ} (h : Tendsto x atTop (𝓝 l)) : BddSeq x := by
  have hev : ∀ᶠ j in atTop, ‖x j‖ ≤ ‖l‖ + 1 := by
    have := h.norm.eventually (gt_mem_nhds (show ‖l‖ < ‖l‖ + 1 by linarith))
    exact this.mono fun j hj => hj.le
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨‖l‖ + 1 + ∑ i ∈ Finset.Icc 1 N, ‖x i‖, fun j => ?_⟩
  have hs : 0 ≤ ∑ i ∈ Finset.Icc 1 N, ‖x i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rcases le_total N j with h' | h'
  · linarith [hN j h']
  · have := Finset.single_le_sum (f := fun i => ‖x i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_Icc.2 ⟨PNat.one_le j, h'⟩)
    have hl := norm_nonneg l
    linarith
private theorem bddSeq_sum {ι : Type*} (s : Finset ι) (x : ι → ℕ+ → ℂ) (h : ∀ i ∈ s, BddSeq (x i)) :
    BddSeq fun j => ∑ i ∈ s, x i j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun j => by simp⟩
  | insert a s ha ih =>
    obtain ⟨B₁, h₁⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨B₂, h₂⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨B₁ + B₂, fun j => ?_⟩
    change ‖∑ i ∈ insert a s, x i j‖ ≤ _
    rw [Finset.sum_insert ha]
    exact (norm_add_le _ _).trans (add_le_add (h₁ j) (h₂ j))
private theorem bddSeq_prod {ι : Type*} (s : Finset ι) (x : ι → ℕ+ → ℂ) (h : ∀ i ∈ s, BddSeq (x i)) :
    BddSeq fun j => ∏ i ∈ s, x i j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun j => by simp⟩
  | insert a s ha ih =>
    obtain ⟨B₁, h₁⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨B₂, h₂⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨B₁ * B₂, fun j => ?_⟩
    change ‖∏ i ∈ insert a s, x i j‖ ≤ _
    rw [Finset.prod_insert ha, norm_mul]
    exact mul_le_mul (h₁ j) (h₂ j) (norm_nonneg _) ((norm_nonneg _).trans (h₁ j))
private def toBorelProb {a : ℝ} (ν : Measure (InfiniteLattice.GaugeField a)) (h : IsProbabilityMeasure ν) :
    BorelProb a := Subtype.mk ν h
private theorem centeredProduct_apply (L K : ℕ) (ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ)))
    (Z : Tuple) (U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ))) :
    centeredProduct L K ν Z U = ∏ l : Fin Z.1.length, (InfiniteLattice.smearedEnergy (Z.1.get l) U -
      ∫ V, InfiniteLattice.smearedEnergy (Z.1.get l) V ∂ν.1) := by apply _root_.YangMills.DeltaSharedProofs.p501816 <;> assumption
private theorem integral_centeredProduct_eq_centeredMoment (L K : ℕ)
    (ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ))) (Z : Tuple) :
    ((∫ U, centeredProduct L K ν Z U ∂ν.1 : ℝ) : ℂ) =
      InfiniteLattice.centeredMoment ν.1 fun l : Fin Z.1.length => Z.1.get l := by
  unfold InfiniteLattice.centeredMoment Probability.complexExpectation
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only [centeredProduct_apply]
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [integral_complex_ofReal]
  push_cast
  rfl
private theorem exists_integral_centeredProduct_le {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hId : InfiniteLattice.CenteredIdentity.Statement) {IsPair : ℕ+ → ℝ → Prop}
    (Q : SystemsWithFiveBounds.PairSequence L IsPair) (S : LimitTheorem.CumulantFamily)
    (hdef : Q.Defines S) (hprob : ∀ j, IsProbabilityMeasure (Q.state j)) (Z : Tuple) :
    ∃ B : ℝ, ∀ j, ∫ U, centeredProduct L (Q.cutoff j) (toBorelProb (Q.state j) (hprob j)) Z U ∂(Q.state j) ≤ B := by
  set h : Fin Z.1.length → InfiniteLattice.AmbientSpace → ℝ := fun l => Z.1.get l with hh
  have hmem : ∀ l, h l ∈ InfiniteLattice.compactTestFunctions := fun l => by
    obtain ⟨h₁, h₂, -⟩ := Z.2.1 (Z.1.get l) (List.get_mem _ _)
    have hc : Continuous (Z.1.get l) := h₁.continuous
    exact ⟨hc.measurable, hc.bounded_above_of_compact_support h₂, h₂⟩
  have hpart : BddSeq fun j => InfiniteLattice.ursellPartitionSum (Q.state j) h := by
    unfold InfiniteLattice.ursellPartitionSum
    refine bddSeq_sum _ _ fun π hπ => bddSeq_prod _ _ fun J hJ => ?_
    have hJ2 : 2 ≤ J.card := (Finset.mem_filter.1 hπ).2 J hJ
    have hX : Cumulants.restrictTuple h J ∈ TestSpaces.disjointSupportTuples Set.univ J.card := by
      refine ⟨fun i => ?_, fun i i' hne => ?_⟩
      · obtain ⟨h₁, h₂, -⟩ := Z.2.1 (h (J.orderEmbOfFin rfl i)) (List.get_mem _ _)
        exact ⟨h₁, h₂, Set.subset_univ _⟩
      · have hp : J.orderEmbOfFin rfl i ≠ J.orderEmbOfFin rfl i' := fun e =>
          hne ((J.orderEmbOfFin rfl).injective e)
        rcases lt_or_gt_of_ne hp with hlt | hlt
        · exact List.pairwise_iff_get.1 Z.2.2 _ _ hlt
        · exact (List.pairwise_iff_get.1 Z.2.2 _ _ hlt).symm
    exact bddSeq_of_tendsto (hdef J.card hJ2 ⟨Cumulants.restrictTuple h J, hX⟩)
  obtain ⟨B, hB⟩ := hpart
  refine ⟨B, fun j => ?_⟩
  have e := integral_centeredProduct_eq_centeredMoment L (Q.cutoff j) (toBorelProb (Q.state j) (hprob j)) Z
  have e₁ := (hId ⟨L, hL, Q.cutoff j, 1⟩ (Q.state j) (hprob j)).2.2 _ h hmem
  have e₂ : ‖InfiniteLattice.ursellPartitionSum (Q.state j) h‖ ≤ B := hB j
  rw [← e₁] at e₂
  have e₃ : ‖((∫ U, centeredProduct L (Q.cutoff j) (toBorelProb (Q.state j) (hprob j)) Z U ∂(Q.state j) : ℝ) :
      ℂ)‖ ≤ B := by
    refine le_of_eq_of_le (congrArg _ e) e₂
  rw [Complex.norm_real] at e₃
  exact (le_abs_self _).trans e₃
private theorem norm_expect_le {a : ℝ} (ρ : InfiniteLattice.GaugeFieldProbability a)
    {F : InfiniteLattice.GaugeField a → ℂ} {C : ℝ} (hC : ∀ U, ‖F U‖ ≤ C) : ‖ρ.expect F‖ ≤ C := by apply _root_.YangMills.DeltaSharedProofs.p501847 <;> assumption
private theorem isInvariantDisintegration_of_byIntegrals {a : ℝ} {ν : Measure (InfiniteLattice.GaugeField a)}
    (hp : IsProbabilityMeasure ν) (hinv : InfiniteLattice.IsShiftInvariant ν)
    {κ : InfiniteLattice.GaugeField a → InfiniteLattice.GaugeFieldProbability a}
    (hκ : InfiniteLattice.IsRegularConditionalByIntegrals ν κ) :
    InfiniteLattice.IsInvariantDisintegration ν κ := by
  refine ⟨hp, hinv, fun F hF => ⟨(hκ F hF).1, ?_⟩⟩
  have hm : InfiniteLattice.shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (InfiniteLattice.GaugeField a)) :=
    fun I hI => hI.1
  obtain ⟨hFm, C, hC⟩ := id hF
  have hgm := (hκ F hF).1
  have hFi : Integrable F ν := Integrable.of_bound hFm.aestronglyMeasurable C (Eventually.of_forall hC)
  have hg : Measurable fun U => (κ U).expect F := hgm.mono hm le_rfl
  have hgi : Integrable (fun U => (κ U).expect F) ν :=
    Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun U => norm_expect_le (κ U) hC)
  unfold InfiniteLattice.condExpShiftInvariant
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hFi (fun I _ _ => hgi.integrableOn) (fun I hI _ => ?_)
    hgm.stronglyMeasurable.aestronglyMeasurable
  have hIb : MeasurableSet I := hm _ hI
  have hJ : Measurable[InfiniteLattice.shiftInvariantSigma a] (I.indicator fun _ => (1 : ℂ)) :=
    (@measurable_const _ _ _ (InfiniteLattice.shiftInvariantSigma _) _).indicator hI
  have hk := (hκ F hF).2 _ hJ ⟨1, fun U => by by_cases h : U ∈ I <;> simp [h]⟩
  have e₁ : (fun U => (I.indicator fun _ => (1 : ℂ)) U * (κ U).expect F) =
      I.indicator fun U => (κ U).expect F := by
    funext U
    by_cases h : U ∈ I <;> simp [h]
  have e₂ : (fun U => (I.indicator fun _ => (1 : ℂ)) U * F U) = I.indicator F := by
    funext U
    by_cases h : U ∈ I <;> simp [h]
  rw [e₁, e₂, integral_indicator hIb, integral_indicator hIb] at hk
  exact hk
private theorem conditionalMean_facts {a : ℝ} {ν : Measure (InfiniteLattice.GaugeField a)}
    (hp : IsProbabilityMeasure ν)
    {κ : InfiniteLattice.GaugeField a → InfiniteLattice.GaugeFieldProbability a}
    (hκ : InfiniteLattice.IsRegularConditionalByIntegrals ν κ)
    (f : InfiniteLattice.GaugeField a → ℝ) (hF : InfiniteLattice.IsBoundedObservable fun U => ((f U : ℝ) : ℂ)) :
    Measurable (fun U => ∫ V, f V ∂(κ U).1) ∧ (∃ C : ℝ, ∀ U, |∫ V, f V ∂(κ U).1| ≤ C) ∧
      ∫ U, (∫ V, f V ∂(κ U).1) ∂ν = ∫ U, f U ∂ν := by
  have hm : InfiniteLattice.shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (InfiniteLattice.GaugeField a)) :=
    fun I hI => hI.1
  have e : ∀ U, (κ U).expect (fun V => ((f V : ℝ) : ℂ)) = ((∫ V, f V ∂(κ U).1 : ℝ) : ℂ) := fun U =>
    integral_complex_ofReal
  obtain ⟨hg, hk⟩ := hκ _ hF
  refine ⟨?_, ?_, ?_⟩
  · have h₁ : Measurable fun U => (κ U).expect (fun V => ((f V : ℝ) : ℂ)) := hg.mono hm le_rfl
    have e₁ : (fun U => ∫ V, f V ∂(κ U).1) =
        fun U => ((κ U).expect (fun V => ((f V : ℝ) : ℂ))).re := by
      funext U
      rw [e, Complex.ofReal_re]
    rw [e₁]
    exact Complex.measurable_re.comp h₁
  · obtain ⟨-, C, hC⟩ := hF
    refine ⟨C, fun U => ?_⟩
    have h₁ := norm_expect_le (κ U) hC
    rw [e, Complex.norm_real] at h₁
    exact h₁
  · have h₁ := hk (fun _ => 1) (@measurable_const _ _ _ (InfiniteLattice.shiftInvariantSigma _) _)
      ⟨1, fun U => by simp⟩
    simp only [one_mul, e] at h₁
    rw [integral_complex_ofReal, integral_complex_ofReal] at h₁
    exact_mod_cast h₁
private theorem integral_abs_pow_conditionalMean_le {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hErg : InfiniteLattice.ErgodicDecompositionStatement)
    {K : ℕ+} {β : ℝ} (hβ : 0 < β)
    {ν : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)))}
    (hp : IsProbabilityMeasure ν) (hinv : InfiniteLattice.IsShiftInvariant ν)
    (hper : ν ∈ periodicGibbsSet L K β)
    {κ : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)) →
      InfiniteLattice.GaugeFieldProbability (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))}
    (hκ : InfiniteLattice.IsRegularConditionalByIntegrals ν κ)
    (hobs : ∀ Z : Tuple, InfiniteLattice.IsBoundedObservable
      fun U => ((centeredProduct L K (toBorelProb ν hp) Z U : ℝ) : ℂ))
    (X Z : Tuple) (t : ℕ)
    (hXZ : ∀ ρ : BorelProb (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)), ρ.1 ∈ periodicGibbsSet L K β →
      (∫ U, centeredProduct L K (toBorelProb ν hp) X U ∂ρ.1) ^ (2 ^ (t + 1)) ≤
        ∫ U, centeredProduct L K (toBorelProb ν hp) Z U ∂ρ.1) :
    Integrable (fun U => |∫ V, centeredProduct L K (toBorelProb ν hp) X V ∂(κ U).1| ^ t) ν ∧
      ∫ U, |∫ V, centeredProduct L K (toBorelProb ν hp) X V ∂(κ U).1| ^ t ∂ν ≤
        1 + ∫ U, centeredProduct L K (toBorelProb ν hp) Z U ∂ν := by
  obtain ⟨hXm, ⟨C, hC⟩, -⟩ := conditionalMean_facts hp hκ _ (hobs X)
  obtain ⟨hZm, ⟨C', hC'⟩, hZi⟩ := conditionalMean_facts hp hκ _ (hobs Z)
  obtain ⟨N, -, hN0, hN⟩ := (hErg L K hL.1 hL.2 K.pos β hβ).1 (Subtype.mk ν hp) hper κ
    (isInvariantDisintegration_of_byIntegrals hp hinv hκ)
  have hI : Integrable (fun U => |∫ V, centeredProduct L K (toBorelProb ν hp) X V ∂(κ U).1| ^ t) ν := by
    refine Integrable.of_bound (hXm.abs.pow_const t).aestronglyMeasurable (C ^ t)
      (Eventually.of_forall fun U => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC U) t
  have hZI : Integrable (fun U => ∫ V, centeredProduct L K (toBorelProb ν hp) Z V ∂(κ U).1) ν :=
    Integrable.of_bound hZm.aestronglyMeasurable C' (Eventually.of_forall hC')
  refine ⟨hI, ?_⟩
  have hae : ∀ᵐ U ∂ν, |∫ V, centeredProduct L K (toBorelProb ν hp) X V ∂(κ U).1| ^ t ≤
      1 + ∫ V, centeredProduct L K (toBorelProb ν hp) Z V ∂(κ U).1 := by
    have h₀ : ∀ᵐ U ∂ν, U ∉ N := compl_mem_ae_iff.2 hN0
    filter_upwards [h₀] with U hU
    exact (abs_pow_le_one_add _ t).trans (add_le_add_right (hXZ (κ U) (hN U hU).1) 1)
  have h₁ := integral_mono_ae hI ((integrable_const (1 : ℝ)).add hZI) hae
  refine h₁.trans (le_of_eq ?_)
  have h₂ := integral_add (integrable_const (μ := ν) (1 : ℝ)) hZI
  rw [hZi] at h₂
  simpa using h₂
private def ofDisjointTuple (X : DisjointTuples.DisjointTuple) : Tuple :=
  ⟨X.1, fun f hf => ⟨(X.2.1 f hf).1, (X.2.1 f hf).2, Set.subset_univ _⟩, X.2.2⟩
private theorem centeredRep_eq (L K : ℕ)
    (ν : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ))))
    (hp : IsProbabilityMeasure ν) (X : DisjointTuples.DisjointTuple) :
    CenteredRepresentatives.centeredRep L K ν X = centeredProduct L K (toBorelProb ν hp) (ofDisjointTuple X) := by
  funext U
  unfold CenteredRepresentatives.centeredRep centeredProduct
  rw [Pi.list_prod_apply, List.map_map]
  rfl
theorem phaseMomentsBoundedStatement_holds (hErg : InfiniteLattice.ErgodicDecompositionStatement)
    (hId : InfiniteLattice.CenteredIdentity.Statement)
    (hLim : InfiniteLattice.TorusWeakLimitsArePeriodicGibbs)
    (hCalc : LatticeRepresentatives.Statement)
    (hGibbs : PeriodicGibbs.periodicGibbsTheorem) : phaseMomentsBoundedStatement := by
  intro L hL IsPair Q S hβ hdef κ hκ X t
  obtain ⟨hRP, hCent, -⟩ := hGibbs L hL
  have hprob : ∀ j, IsProbabilityMeasure (Q.state j) := fun j => (Q.isLimit j).1
  obtain ⟨Z, hZ⟩ := exists_powerDominates hL hCalc hCent hRP (ofDisjointTuple X) t
  obtain ⟨B, hB⟩ := exists_integral_centeredProduct_le hL hId Q S hdef hprob Z
  refine ⟨1 + B, fun j => ?_⟩
  have hlim := hLim L (Q.cutoff j) hL (Q.cutoff j).pos (Q.coupling j) (hβ j)
  have hper : Q.state j ∈ periodicGibbsSet L (Q.cutoff j) (Q.coupling j) := hlim.2 (Q.isLimit j)
  have hinv : InfiniteLattice.IsShiftInvariant (Q.state j) := (hlim.1 _ (Q.isLimit j)).2.1
  have hobs : ∀ Y : Tuple, InfiniteLattice.IsBoundedObservable
      fun U => ((centeredProduct L (Q.cutoff j) (toBorelProb (Q.state j) (hprob j)) Y U : ℝ) : ℂ) := fun Y =>
    ((hCalc ⟨L, hL, Q.cutoff j, 1⟩ (Q.cutoff j) (Q.coupling j) (toBorelProb (Q.state j) (hprob j)) (hβ j)
      hper).2.2.1.1 Y).2.1
  have hmain := integral_abs_pow_conditionalMean_le hL hErg (hβ j) (hprob j) hinv hper (hκ j) hobs
    (ofDisjointTuple X) Z t fun ρ hρ => hZ (Q.cutoff j) (Q.coupling j) (hβ j) _ ρ hper hρ
  have e : ∀ ρ : Measure (FieldAt Q j), centredMean Q j ρ X =
      ∫ V, centeredProduct L (Q.cutoff j) (toBorelProb (Q.state j) (hprob j)) (ofDisjointTuple X) V ∂ρ := fun ρ => by
    unfold centredMean
    rw [centeredRep_eq L (Q.cutoff j) (Q.state j) (hprob j) X]
  simp only [e]
  exact ⟨hmain.1, hmain.2.trans (by linarith [hB j])⟩
end YangMills.Construction.TotalDensitiesGiveASystem.PhaseMoments
end
