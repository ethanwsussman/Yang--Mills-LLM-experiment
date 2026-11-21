import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.ChessboardTori.GroupOfAGridAndCopies
import YangMills.Construction.ChessboardTori.LimitingSeminormIsAFiniteSeminormProof
import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorus
import YangMills.Construction.ChessboardTori.ParitiesAndCoarseGrids
import YangMills.Construction.SixteenPointsOnASmallTorus.ArrayMeanIsTheMeanOfTheCopiesProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace GridChessboardNormProof
variable {D : ChessboardSetup} {g : ReflectionGrid D}
theorem cellsAcross_pos (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m) :
    0 < g.cellsAcross := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.cellsAcross_pos <;> assumption
theorem isBoundedObservable_prod {ι : Type*} (T : Finset ι) (G : ι → D.GaugeField → ℂ)
    (hG : ∀ i ∈ T, InfiniteLattice.IsBoundedObservable (G i)) :
    InfiniteLattice.IsBoundedObservable (fun U => ∏ i ∈ T, G i U) := by
  refine ⟨Finset.measurable_prod _ fun i hi => (hG i hi).1, ?_⟩
  choose! C hC using fun i (hi : i ∈ T) => (hG i hi).2
  refine ⟨∏ i ∈ T, C i, fun U => ?_⟩
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i hi => hC i hi U
theorem one_mem_cellObservables (S : Set AmbientSpace) :
    (fun _ : D.GaugeField => (1 : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) S := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.one_mem_cellObservables <;> assumption
theorem add_mem_cellObservables {S : Set AmbientSpace} {F F' : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S)
    (hF' : F' ∈ ReflectionGrid.cellObservables (D := D) S) :
    F + F' ∈ ReflectionGrid.cellObservables (D := D) S := by apply _root_.YangMills.Construction.ChessboardTori.LimChessboardNormSeminorm.add_mem_cellObservables <;> assumption
theorem expOfReal_mem_cellObservables {S : Set AmbientSpace} {H : D.GaugeField → ℝ}
    (hH : ReflectionGrid.ofRealFn H ∈ ReflectionGrid.cellObservables (D := D) S) :
    ReflectionGrid.expOfReal H ∈ ReflectionGrid.cellObservables (D := D) S := by
  obtain ⟨f, hf, ⟨C, hC⟩, e⟩ := hH
  refine ⟨fun u => Complex.exp (f u), Complex.measurable_exp.comp hf, ⟨Real.exp C, fun u => ?_⟩, ?_⟩
  · rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 ((Complex.re_le_norm _).trans (hC u))
  · funext U
    have h := congrFun e U
    show Complex.exp (ReflectionGrid.ofRealFn H U) = _
    rw [h]
    rfl
theorem signedConj_ofReal (σ : ℤˣ) (x : ℝ) : Conventions.signedConj σ (x : ℂ) = x := by apply _root_.YangMills.SharedProofs.p21399 <;> assumption
structure GridFacts (g : ReflectionGrid D) : Prop where
  isCoarse : g.IsCoarse
  side_le : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m
  expectation_props : ∀ B ∈ g.blocks, ∀ S ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
    (g.chessboardExpectation S B F).im = 0 ∧ 0 ≤ (g.chessboardExpectation S B F).re ∧
      ∀ B' ∈ g.blocks, g.chessboardExpectation S B' F = g.chessboardExpectation S B F
  block_bound : ∀ B ∈ g.blocks, ∀ F : Set AmbientSpace → D.GaugeField → ℂ,
    (∀ S ∈ g.cellsWithin B, F S ∈ ReflectionGrid.cellObservables (D := D) S) →
      ‖D.liftedExpectation fun U => ∏ᶠ S ∈ g.cellsWithin B, F S U‖ ≤
        ∏ᶠ S ∈ g.cellsWithin B, g.chessboardNorm S (F S)
  norm_props : ∀ S ∈ g.cellSet,
    (∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
      (∀ S' ∈ g.cellSet, g.chessboardNorm S' (g.transportTo S S' F) = g.chessboardNorm S F) ∧
      g.chessboardNorm S F = g.chessboardNorm S (fun U => starRingEnd ℂ (F U)) ∧
      g.chessboardNorm S F ≤ InfiniteLattice.observableSupNorm F) ∧
    g.chessboardNorm S (fun _ => 1) = 1
  unique_mover : g.UniqueElementMapsCell
  transport_laws : g.TransportLaws
  half_odd : g.HalfOddInBlock
  cells_eq : D.CellObservablesEqInteriorMeasurable
  lift_props : D.LiftedObservableProperties
  coord_form : g.ReflectionGroupCoordForm
  transport_rules : g.TransportRules
namespace GridFacts
variable {B S S' : Set AmbientSpace} {F F' : D.GaugeField → ℂ}
theorem ncard_cellsWithin (h : GridFacts g) (hB : B ∈ g.blocks) :
    ((g.cellsWithin B).ncard : ℝ) = g.cellsAcross ^ 4 :=
  (h.half_odd B hB (g.cell 0) ⟨0, rfl⟩).1
theorem ncard_cellsWithin_ne_zero (h : GridFacts g) (hB : B ∈ g.blocks) :
    (g.cellsWithin B).ncard ≠ 0 := by
  intro h0
  have h1 := h.ncard_cellsWithin hB
  rw [h0, Nat.cast_zero] at h1
  have h2 := pow_pos (cellsAcross_pos h.side_le) 4
  linarith
theorem cellsWithin_finite (h : GridFacts g) (hB : B ∈ g.blocks) : (g.cellsWithin B).Finite :=
  Set.finite_of_ncard_ne_zero (h.ncard_cellsWithin_ne_zero hB)
theorem isBoundedObservable_of_mem (h : GridFacts g) (hS : S ∈ g.cellSet)
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    InfiniteLattice.IsBoundedObservable F := by
  rw [h.cells_eq g h.isCoarse S hS] at hF
  exact hF.1
theorem mover_spec (h : GridFacts g) (hS : S ∈ g.cellSet) (hS' : S' ∈ g.cellSet) :
    (g.mover S S').1 '' S = S' :=
  Classical.epsilon_spec (p := fun r : g.reflectionGroup => r.1 '' S = S')
    (h.unique_mover S hS S' hS').exists
theorem transportTo_mem (h : GridFacts g) (hS : S ∈ g.cellSet) (hS' : S' ∈ g.cellSet)
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    g.transportTo S S' F ∈ ReflectionGrid.cellObservables (D := D) S' :=
  (h.transport_laws.1 S hS S' hS' S' hS' F hF F hF).1
theorem isBoundedObservable_finprod (h : GridFacts g) {C : Set (Set AmbientSpace)} (hC : C.Finite)
    (hCc : C ⊆ g.cellSet) {G : Set AmbientSpace → D.GaugeField → ℂ}
    (hG : ∀ S ∈ C, G S ∈ ReflectionGrid.cellObservables (D := D) S) :
    InfiniteLattice.IsBoundedObservable fun U => ∏ᶠ S ∈ C, G S U := by
  have e : (fun U => ∏ᶠ S ∈ C, G S U) = fun U => ∏ S ∈ hC.toFinset, G S U :=
    funext fun U => finprod_mem_eq_finite_toFinset_prod (fun S => G S U) hC
  rw [e]
  refine isBoundedObservable_prod _ _ fun S hS => ?_
  have hS' : S ∈ C := hC.mem_toFinset.1 hS
  exact h.isBoundedObservable_of_mem (hCc hS') (hG S hS')
theorem periodicExpectation_lift (h : GridFacts g) {A : D.GaugeField → ℂ}
    (hA : InfiniteLattice.IsBoundedObservable A) :
    D.periodicExpectation (D.liftedObservable A) = D.liftedExpectation A :=
  (h.lift_props A A hA hA).2.1
theorem productOfTransports_eq (h : GridFacts g) (hB : B ∈ g.blocks) (F : D.GaugeField → ℂ)
    (U : D.GaugeField) :
    g.productOfTransports S B F U =
      ∏ S' ∈ (h.cellsWithin_finite hB).toFinset, g.transportTo S S' F U :=
  finprod_mem_eq_finite_toFinset_prod (fun S' => g.transportTo S S' F U) (h.cellsWithin_finite hB)
theorem isBoundedObservable_productOfTransports (h : GridFacts g) (hB : B ∈ g.blocks)
    (hS : S ∈ g.cellSet) (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    InfiniteLattice.IsBoundedObservable (g.productOfTransports S B F) :=
  h.isBoundedObservable_finprod (h.cellsWithin_finite hB) (fun _ hx => hx.1)
    fun _ hS' => h.transportTo_mem hS hS'.1 hF
theorem chessboardNorm_nonneg (h : GridFacts g) (hS : S ∈ g.cellSet)
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) : 0 ≤ g.chessboardNorm S F :=
  Real.rpow_nonneg (h.expectation_props (g.block 0) ⟨0, rfl⟩ S hS F hF).2.1 _
theorem chessboardNorm_pow (h : GridFacts g) (hS : S ∈ g.cellSet)
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    g.chessboardNorm S F ^ (g.cellsWithin (g.block 0)).ncard =
      (g.chessboardExpectation S (g.block 0) F).re := by
  have hre := (h.expectation_props (g.block 0) ⟨0, rfl⟩ S hS F hF).2.1
  have hN := h.ncard_cellsWithin (B := g.block 0) ⟨0, rfl⟩
  have hpos : g.cellsAcross ^ 4 ≠ 0 := (pow_pos (cellsAcross_pos h.side_le) 4).ne'
  unfold ReflectionGrid.chessboardNorm
  rw [← Real.rpow_natCast, ← Real.rpow_mul hre, hN, one_div, inv_mul_cancel₀ hpos, Real.rpow_one]
theorem isProbabilityMeasure_liftedMeasure (h : GridFacts g) :
    IsProbabilityMeasure D.liftedMeasure := by
  have hS : g.cell 0 ∈ g.cellSet := ⟨0, rfl⟩
  have hB : g.block 0 ∈ g.blocks := ⟨0, rfl⟩
  have h1 : g.chessboardNorm (g.cell 0) (fun _ => 1) = 1 := (h.norm_props _ hS).2
  have hpow := h.chessboardNorm_pow hS (one_mem_cellObservables (D := D) (g.cell 0))
  rw [h1, one_pow] at hpow
  have hprod : g.productOfTransports (g.cell 0) (g.block 0) (fun _ => 1) = fun _ => 1 := by
    funext U
    rw [h.productOfTransports_eq hB]
    refine Finset.prod_eq_one fun S' hS' => ?_
    have hS'' : S' ∈ g.cellSet := ((h.cellsWithin_finite hB).mem_toFinset.1 hS').1
    exact congrFun (h.transport_laws.1 _ hS S' hS'' S' hS'' _ (one_mem_cellObservables _) _
      (one_mem_cellObservables _)).2.2.2.2.2.2.1 U
  have hnum : g.chessboardExpectation (g.cell 0) (g.block 0) (fun _ => 1) =
      ((D.liftedMeasure.real univ : ℝ) : ℂ) := by
    unfold ReflectionGrid.chessboardExpectation ChessboardSetup.liftedExpectation
    rw [hprod, integral_const]
    simp
  rw [hnum, Complex.ofReal_re, measureReal_def] at hpow
  exact ⟨(ENNReal.toReal_eq_one_iff _).1 hpow.symm⟩
theorem integrable_of_isBoundedObservable (h : GridFacts g) {A : D.GaugeField → ℂ}
    (hA : InfiniteLattice.IsBoundedObservable A) : Integrable A D.liftedMeasure := by
  have := h.isProbabilityMeasure_liftedMeasure
  obtain ⟨C, hC⟩ := hA.2
  exact Integrable.of_bound hA.1.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
theorem liftedCopiesExpectation_eq (h : GridFacts g) (hB : B ∈ g.blocks) (hS : S ∈ g.cellSet)
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    g.liftedCopiesExpectation S B F =
      ((g.chessboardNorm S F ^ (g.cellsAcross ^ 4) : ℝ) : ℂ) := by
  have h1 : g.liftedCopiesExpectation S B F =
      D.periodicExpectation (D.liftedObservable (g.productOfTransports S B F)) := rfl
  have h2 : D.liftedExpectation (g.productOfTransports S B F) = g.chessboardExpectation S B F := rfl
  obtain ⟨him, -, hblock⟩ := h.expectation_props (g.block 0) ⟨0, rfl⟩ S hS F hF
  rw [h1, h.periodicExpectation_lift (h.isBoundedObservable_productOfTransports hB hS hF), h2,
    hblock B hB, ← h.ncard_cellsWithin (B := g.block 0) ⟨0, rfl⟩, Real.rpow_natCast,
    h.chessboardNorm_pow hS hF]
  apply Complex.ext <;> simp [him]
theorem block_bound_subset (h : GridFacts g) (hB : B ∈ g.blocks) {C : Set (Set AmbientSpace)}
    (hC : C ⊆ g.cellsWithin B) {G : Set AmbientSpace → D.GaugeField → ℂ}
    (hG : ∀ S ∈ C, G S ∈ ReflectionGrid.cellObservables (D := D) S) :
    ‖D.liftedExpectation fun U => ∏ᶠ S ∈ C, G S U‖ ≤ ∏ᶠ S ∈ C, g.chessboardNorm S (G S) := by
  classical
  have hfin := h.cellsWithin_finite hB
  have hCfin := hfin.subset hC
  let G' : Set AmbientSpace → D.GaugeField → ℂ := fun S => if S ∈ C then G S else fun _ => 1
  have hin : ∀ S ∈ C, G' S = G S := fun S hS => if_pos hS
  have hout : ∀ S, S ∉ C → G' S = fun _ => 1 := fun S hS => if_neg hS
  have hG' : ∀ S ∈ g.cellsWithin B, G' S ∈ ReflectionGrid.cellObservables (D := D) S := by
    intro S _
    by_cases hS : S ∈ C
    · rw [hin S hS]
      exact hG S hS
    · rw [hout S hS]
      exact one_mem_cellObservables S
  have hb := h.block_bound B hB G' hG'
  have hsub : hCfin.toFinset ⊆ hfin.toFinset := fun S hS =>
    hfin.mem_toFinset.2 (hC (hCfin.mem_toFinset.1 hS))
  have e1 : (fun U => ∏ᶠ S ∈ g.cellsWithin B, G' S U) = fun U => ∏ᶠ S ∈ C, G S U := by
    funext U
    rw [finprod_mem_eq_finite_toFinset_prod (fun S => G' S U) hfin,
      finprod_mem_eq_finite_toFinset_prod (fun S => G S U) hCfin]
    refine (Finset.prod_subset hsub fun S _ hS => ?_).symm.trans
      (Finset.prod_congr rfl fun S hS => ?_)
    · rw [hout S fun hc => hS (hCfin.mem_toFinset.2 hc)]
    · rw [hin S (hCfin.mem_toFinset.1 hS)]
  have e2 : ∏ᶠ S ∈ g.cellsWithin B, g.chessboardNorm S (G' S) =
      ∏ᶠ S ∈ C, g.chessboardNorm S (G S) := by
    rw [finprod_mem_eq_finite_toFinset_prod (fun S => g.chessboardNorm S (G' S)) hfin,
      finprod_mem_eq_finite_toFinset_prod (fun S => g.chessboardNorm S (G S)) hCfin]
    refine (Finset.prod_subset hsub fun S hS' hS => ?_).symm.trans
      (Finset.prod_congr rfl fun S hS => ?_)
    · rw [hout S fun hc => hS (hCfin.mem_toFinset.2 hc)]
      exact (h.norm_props S (hfin.mem_toFinset.1 hS').1).2
    · rw [hin S (hCfin.mem_toFinset.1 hS)]
  rwa [e1, e2] at hb
theorem norm_liftedProductExpectation_le (h : GridFacts g) (hB : B ∈ g.blocks)
    {C : Set (Set AmbientSpace)} (hC : C ⊆ g.cellsWithin B) {G : Set AmbientSpace → D.GaugeField → ℂ}
    (hG : ∀ S ∈ C, G S ∈ ReflectionGrid.cellObservables (D := D) S) :
    ‖ReflectionGrid.liftedProductExpectation (D := D) C G‖ ≤
      ∏ᶠ S ∈ C, g.chessboardNorm S (G S) := by
  have hobs := h.isBoundedObservable_finprod ((h.cellsWithin_finite hB).subset hC)
    (fun _ hx => (hC hx).1) hG
  have e : ReflectionGrid.liftedProductExpectation (D := D) C G =
      D.liftedExpectation fun U => ∏ᶠ S ∈ C, G S U := h.periodicExpectation_lift hobs
  rw [e]
  exact h.block_bound_subset hB hC hG
theorem prod_signedConj_eq (h : GridFacts g) (hB : B ∈ g.blocks) (hS : S ∈ g.cellSet) (lam : ℂ) :
    ∏ S' ∈ (h.cellsWithin_finite hB).toFinset,
        Conventions.signedConj (orientationSign (g.mover S S').1.1) lam =
      ((‖lam‖ ^ (g.cellsWithin B).ncard : ℝ) : ℂ) := by
  classical
  have hfin := h.cellsWithin_finite hB
  set T := hfin.toFinset with hT
  have hcard : (g.cellsWithin B).ncard = T.card := Set.ncard_eq_toFinset_card _ hfin
  let P : Set AmbientSpace → Prop := fun S' => orientationSign (g.mover S S').1.1 = -1
  obtain ⟨hN, hhalf⟩ := h.half_odd B hB S hS
  have hset : {S' ∈ g.cellsWithin B | ∃ r : g.reflectionGroup, r.1 '' S = S' ∧
      orientationSign r.1 = -1} = ↑(T.filter P) := by
    ext S'
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, hT, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hS', r, hr, hs⟩
      refine ⟨hS', ?_⟩
      have e : g.mover S S' = r :=
        (h.unique_mover S hS S' hS'.1).unique (h.mover_spec hS hS'.1) hr
      show orientationSign (g.mover S S').1.1 = -1
      rw [e]
      exact hs
    · rintro ⟨hS', hs⟩
      exact ⟨hS', g.mover S S', h.mover_spec hS hS'.1, hs⟩
  rw [hset, Set.ncard_coe_finset] at hhalf
  have hM : 2 * (T.filter P).card = T.card := by
    have e : ((2 * (T.filter P).card : ℕ) : ℝ) = (T.card : ℝ) := by
      push_cast
      rw [hhalf, ← hcard, hN]
      ring
    exact_mod_cast e
  have hM' : (T.filter fun S' => ¬ P S').card = (T.filter P).card := by
    have e := Finset.card_filter_add_card_filter_not (s := T) P
    omega
  have h1 : ∏ S' ∈ T.filter P, Conventions.signedConj (orientationSign (g.mover S S').1.1) lam =
      starRingEnd ℂ lam ^ (T.filter P).card := by
    rw [Finset.prod_congr rfl (g := fun _ => starRingEnd ℂ lam), Finset.prod_const]
    intro S' hS'
    have hs : orientationSign (g.mover S S').1.1 = -1 := (Finset.mem_filter.1 hS').2
    unfold Conventions.signedConj
    rw [if_neg]
    rw [hs]
    decide
  have h2 : ∏ S' ∈ T.filter (fun S' => ¬ P S'),
      Conventions.signedConj (orientationSign (g.mover S S').1.1) lam =
      lam ^ (T.filter P).card := by
    rw [Finset.prod_congr rfl (g := fun _ => lam), Finset.prod_const, hM']
    intro S' hS'
    have hs : ¬ orientationSign (g.mover S S').1.1 = -1 := (Finset.mem_filter.1 hS').2
    have hs' : orientationSign (g.mover S S').1.1 = 1 := (Int.units_eq_one_or _).resolve_right hs
    unfold Conventions.signedConj
    rw [if_pos hs']
  rw [← Finset.prod_filter_mul_prod_filter_not T P, h1, h2, ← mul_pow, hcard, ← hM, pow_mul,
    mul_comm (starRingEnd ℂ lam), Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl
theorem chessboardExpectation_const_mul (h : GridFacts g) (hB : B ∈ g.blocks) (hS : S ∈ g.cellSet)
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) (lam : ℂ) :
    g.chessboardExpectation S B (fun U => lam * F U) =
      ((‖lam‖ ^ (g.cellsWithin B).ncard : ℝ) : ℂ) * g.chessboardExpectation S B F := by
  have e : g.productOfTransports S B (fun U => lam * F U) =
      fun U => ((‖lam‖ ^ (g.cellsWithin B).ncard : ℝ) : ℂ) * g.productOfTransports S B F U := by
    funext U
    rw [h.productOfTransports_eq hB, h.productOfTransports_eq hB, ← h.prod_signedConj_eq hB hS lam,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun S' hS' => ?_
    have hc : S' ∈ g.cellSet := ((h.cellsWithin_finite hB).mem_toFinset.1 hS').1
    exact congrFun (h.transport_rules S hS S' hc S hS (g.mover S S') (h.mover_spec hS hc) F hF F hF
      lam).2.2.2.2.2.2.1 U
  unfold ReflectionGrid.chessboardExpectation ChessboardSetup.liftedExpectation
  rw [e]
  exact integral_const_mul _ _
theorem chessboardNorm_smul (h : GridFacts g) (hS : S ∈ g.cellSet)
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) (lam : ℂ) :
    g.chessboardNorm S (lam • F) = ‖lam‖ * g.chessboardNorm S F := by
  have hB : g.block 0 ∈ g.blocks := ⟨0, rfl⟩
  have e : lam • F = fun U => lam * F U := funext fun U => by simp
  have hre := (h.expectation_props (g.block 0) hB S hS F hF).2.1
  have hN := h.ncard_cellsWithin hB
  have hpos : g.cellsAcross ^ 4 ≠ 0 := (pow_pos (cellsAcross_pos h.side_le) 4).ne'
  rw [e]
  unfold ReflectionGrid.chessboardNorm
  rw [h.chessboardExpectation_const_mul hB hS hF lam, Complex.re_ofReal_mul,
    Real.mul_rpow (pow_nonneg (norm_nonneg _) _) hre]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), hN, mul_one_div_cancel hpos,
    Real.rpow_one]
theorem expansion_term_bound (h : GridFacts g) (hB : B ∈ g.blocks) (hS : S ∈ g.cellSet)
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S)
    (hF' : F' ∈ ReflectionGrid.cellObservables (D := D) S)
    {t : Finset (Set AmbientSpace)} (ht : t ⊆ (h.cellsWithin_finite hB).toFinset) :
    Integrable (fun U => (∏ S' ∈ t, g.transportTo S S' F U) *
      ∏ S' ∈ (h.cellsWithin_finite hB).toFinset \ t, g.transportTo S S' F' U) D.liftedMeasure ∧
    ‖D.liftedExpectation fun U => (∏ S' ∈ t, g.transportTo S S' F U) *
      ∏ S' ∈ (h.cellsWithin_finite hB).toFinset \ t, g.transportTo S S' F' U‖ ≤
      g.chessboardNorm S F ^ t.card * g.chessboardNorm S F' ^
        ((h.cellsWithin_finite hB).toFinset.card - t.card) := by
  classical
  have hfin := h.cellsWithin_finite hB
  set T := hfin.toFinset with hT
  let G : Set AmbientSpace → D.GaugeField → ℂ :=
    fun S' => if S' ∈ t then g.transportTo S S' F else g.transportTo S S' F'
  have hin : ∀ S' ∈ t, G S' = g.transportTo S S' F := fun S' hS' => if_pos hS'
  have hout : ∀ S', S' ∉ t → G S' = g.transportTo S S' F' := fun S' hS' => if_neg hS'
  have hG : ∀ S' ∈ g.cellsWithin B, G S' ∈ ReflectionGrid.cellObservables (D := D) S' := by
    intro S' hS'
    by_cases hc : S' ∈ t
    · rw [hin S' hc]
      exact h.transportTo_mem hS hS'.1 hF
    · rw [hout S' hc]
      exact h.transportTo_mem hS hS'.1 hF'
  have eprod : (fun U => ∏ᶠ S' ∈ g.cellsWithin B, G S' U) =
      fun U => (∏ S' ∈ t, g.transportTo S S' F U) * ∏ S' ∈ T \ t, g.transportTo S S' F' U := by
    funext U
    rw [finprod_mem_eq_finite_toFinset_prod (fun S' => G S' U) hfin, ← Finset.prod_sdiff ht,
      mul_comm]
    congr 1
    · exact Finset.prod_congr rfl fun S' hS' => by rw [hin S' hS']
    · exact Finset.prod_congr rfl fun S' hS' => by
        rw [hout S' (Finset.mem_sdiff.1 hS').2]
  have eval : ∏ᶠ S' ∈ g.cellsWithin B, g.chessboardNorm S' (G S') =
      g.chessboardNorm S F ^ t.card * g.chessboardNorm S F' ^ (T.card - t.card) := by
    rw [finprod_mem_eq_finite_toFinset_prod (fun S' => g.chessboardNorm S' (G S')) hfin,
      ← Finset.prod_sdiff ht, mul_comm, ← Finset.card_sdiff_of_subset ht]
    congr 1
    · rw [Finset.prod_congr rfl (g := fun _ => g.chessboardNorm S F), Finset.prod_const]
      intro S' hS'
      rw [hin S' hS']
      exact ((h.norm_props S hS).1 F hF).1 S' (hfin.mem_toFinset.1 (ht hS')).1
    · rw [Finset.prod_congr rfl (g := fun _ => g.chessboardNorm S F'), Finset.prod_const]
      intro S' hS'
      rw [hout S' (Finset.mem_sdiff.1 hS').2]
      exact ((h.norm_props S hS).1 F' hF').1 S'
        (hfin.mem_toFinset.1 (Finset.mem_sdiff.1 hS').1).1
  have hobs := h.isBoundedObservable_finprod hfin (fun _ hx => hx.1) hG
  constructor
  · rw [← eprod]
    exact h.integrable_of_isBoundedObservable hobs
  · rw [← eprod, ← eval]
    exact h.block_bound B hB G hG
theorem chessboardNorm_add_le (h : GridFacts g) (hS : S ∈ g.cellSet)
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S)
    (hF' : F' ∈ ReflectionGrid.cellObservables (D := D) S) :
    g.chessboardNorm S (F + F') ≤ g.chessboardNorm S F + g.chessboardNorm S F' := by
  classical
  have hB : g.block 0 ∈ g.blocks := ⟨0, rfl⟩
  have hfin := h.cellsWithin_finite hB
  have hcard : (g.cellsWithin (g.block 0)).ncard = hfin.toFinset.card :=
    Set.ncard_eq_toFinset_card _ hfin
  have hexp : g.productOfTransports S (g.block 0) (F + F') = fun U =>
      ∑ t ∈ hfin.toFinset.powerset, (∏ S' ∈ t, g.transportTo S S' F U) *
        ∏ S' ∈ hfin.toFinset \ t, g.transportTo S S' F' U := by
    funext U
    rw [h.productOfTransports_eq hB, ← Finset.prod_add]
    refine Finset.prod_congr rfl fun S' hS' => ?_
    have hc : S' ∈ g.cellSet := (hfin.mem_toFinset.1 hS').1
    exact congrFun (h.transport_laws.1 S hS S' hc S' hc F hF F' hF').2.2.2.2.1 U
  have hnum : ‖g.chessboardExpectation S (g.block 0) (F + F')‖ ≤
      (g.chessboardNorm S F + g.chessboardNorm S F') ^ hfin.toFinset.card := by
    rw [← Finset.sum_pow_mul_eq_add_pow]
    unfold ReflectionGrid.chessboardExpectation
    rw [hexp]
    unfold ChessboardSetup.liftedExpectation
    rw [integral_finsetSum _ fun t ht =>
      (h.expansion_term_bound hB hS hF hF' (Finset.mem_powerset.1 ht)).1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => ?_)
    exact (h.expansion_term_bound hB hS hF hF' (Finset.mem_powerset.1 ht)).2
  have hpow := h.chessboardNorm_pow hS (add_mem_cellObservables hF hF')
  have hle : g.chessboardNorm S (F + F') ^ hfin.toFinset.card ≤
      (g.chessboardNorm S F + g.chessboardNorm S F') ^ hfin.toFinset.card := by
    rw [← hcard, hpow, hcard]
    exact (Complex.re_le_norm _).trans hnum
  have hne : hfin.toFinset.card ≠ 0 := hcard ▸ h.ncard_cellsWithin_ne_zero hB
  exact le_of_pow_le_pow_left₀ hne
    (add_nonneg (h.chessboardNorm_nonneg hS hF) (h.chessboardNorm_nonneg hS hF')) hle
theorem mover_image (h : GridFacts g) (hS : S ∈ g.cellSet) (r : g.reflectionGroup) :
    g.mover S (r.1 '' S) = r :=
  have hc : r.1 '' S ∈ g.cellSet := h.coord_form.2.2.2.2.2.1 r.1 r.2 S hS
  (h.unique_mover S hS _ hc).unique (h.mover_spec hS hc) rfl
theorem transportTo_ofRealFn (h : GridFacts g) (hS : S ∈ g.cellSet) (r : g.reflectionGroup)
    (H : D.GaugeField → ℝ) :
    g.transportTo S (r.1 '' S) (ReflectionGrid.ofRealFn H) =
      ReflectionGrid.ofRealFn ((g.toLatticeSym r).actOn H) := by
  unfold ReflectionGrid.transportTo
  rw [h.mover_image hS r]
  funext U
  exact signedConj_ofReal _ _
theorem transportTo_expOfReal (h : GridFacts g) (hS : S ∈ g.cellSet) (r : g.reflectionGroup)
    (H : D.GaugeField → ℝ) :
    g.transportTo S (r.1 '' S) (ReflectionGrid.expOfReal H) =
      fun U => Complex.exp (g.transportTo S (r.1 '' S) (ReflectionGrid.ofRealFn H) U) := by
  rw [h.transportTo_ofRealFn hS r H]
  unfold ReflectionGrid.transportTo
  rw [h.mover_image hS r]
  funext U
  show Conventions.signedConj _ (Complex.exp _) = Complex.exp _
  rw [← Complex.ofReal_exp, signedConj_ofReal, Complex.ofReal_exp]
  rfl
theorem transportTo_expOfReal_of_mem (h : GridFacts g) (hS : S ∈ g.cellSet) (hS' : S' ∈ g.cellSet)
    (H : D.GaugeField → ℝ) :
    g.transportTo S S' (ReflectionGrid.expOfReal H) =
      fun U => Complex.exp (g.transportTo S S' (ReflectionGrid.ofRealFn H) U) := by
  obtain ⟨r, rfl⟩ := (h.unique_mover S hS S' hS').exists
  exact h.transportTo_expOfReal hS r H
theorem liftedExpSumExpectation_eq (h : GridFacts g) (hB : B ∈ g.blocks) (hS : S ∈ g.cellSet)
    {H : D.GaugeField → ℝ}
    (hH : ReflectionGrid.ofRealFn H ∈ ReflectionGrid.cellObservables (D := D) S) :
    ((g.chessboardNorm S (ReflectionGrid.expOfReal H) ^ (g.cellsAcross ^ 4) : ℝ) : ℂ) =
      g.liftedExpSumExpectation S B H := by
  rw [← h.liftedCopiesExpectation_eq hB hS (expOfReal_mem_cellObservables hH)]
  unfold ReflectionGrid.liftedCopiesExpectation ReflectionGrid.liftedExpSumExpectation
  congr 1
  funext U
  have hfin := h.cellsWithin_finite hB
  show ∏ᶠ S' ∈ g.cellsWithin B, g.transportTo S S' (ReflectionGrid.expOfReal H) (D.liftField U) =
    Complex.exp (∑ᶠ S' ∈ g.cellsWithin B,
      g.transportTo S S' (ReflectionGrid.ofRealFn H) (D.liftField U))
  rw [finprod_mem_eq_finite_toFinset_prod
      (fun S' => g.transportTo S S' (ReflectionGrid.expOfReal H) (D.liftField U)) hfin,
    finsum_mem_eq_finite_toFinset_sum
      (fun S' => g.transportTo S S' (ReflectionGrid.ofRealFn H) (D.liftField U)) hfin,
    Complex.exp_sum]
  refine Finset.prod_congr rfl fun S' hS' => ?_
  exact congrFun (h.transportTo_expOfReal_of_mem hS (hfin.mem_toFinset.1 hS').1 H) _
theorem abs_le_supNorm {H : D.GaugeField → ℝ}
    (hH : InfiniteLattice.IsBoundedObservable (ReflectionGrid.ofRealFn H))
    (U : D.GaugeField) :
    |H U| ≤ InfiniteLattice.observableSupNorm (ReflectionGrid.ofRealFn H) := by
  obtain ⟨C, hC⟩ := hH.2
  have hb : BddAbove (range fun U => ‖ReflectionGrid.ofRealFn H U‖) :=
    ⟨C, by rintro _ ⟨U, rfl⟩; exact hC U⟩
  have h1 := le_ciSup hb U
  have h2 : ‖ReflectionGrid.ofRealFn H U‖ = |H U| := by
    show ‖((H U : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h2] at h1
  exact h1
theorem chessboardNorm_expOfReal_le (h : GridFacts g) (hS : S ∈ g.cellSet)
    {H : D.GaugeField → ℝ}
    (hH : ReflectionGrid.ofRealFn H ∈ ReflectionGrid.cellObservables (D := D) S) :
    g.chessboardNorm S (ReflectionGrid.expOfReal H) ≤
      Real.exp (InfiniteLattice.observableSupNorm (ReflectionGrid.ofRealFn H)) := by
  have hprob := h.isProbabilityMeasure_liftedMeasure
  have hne : Nonempty D.GaugeField := nonempty_of_isProbabilityMeasure D.liftedMeasure
  refine ((h.norm_props S hS).1 _ (expOfReal_mem_cellObservables hH)).2.2.trans
    (ciSup_le fun U => ?_)
  have e : ‖ReflectionGrid.expOfReal H U‖ = Real.exp (H U) := by
    show ‖Complex.exp ((H U : ℝ) : ℂ)‖ = _
    rw [Complex.norm_exp, Complex.ofReal_re]
  rw [e]
  exact Real.exp_le_exp.2
    ((le_abs_self _).trans (abs_le_supNorm (h.isBoundedObservable_of_mem hS hH) U))
theorem exp_neg_supNorm_le_chessboardNorm (h : GridFacts g) (hS : S ∈ g.cellSet)
    {H : D.GaugeField → ℝ}
    (hH : ReflectionGrid.ofRealFn H ∈ ReflectionGrid.cellObservables (D := D) S) :
    Real.exp (-InfiniteLattice.observableSupNorm (ReflectionGrid.ofRealFn H)) ≤
      g.chessboardNorm S (ReflectionGrid.expOfReal H) := by
  have hB : g.block 0 ∈ g.blocks := ⟨0, rfl⟩
  have hfin := h.cellsWithin_finite hB
  have hprob := h.isProbabilityMeasure_liftedMeasure
  have hobs := h.isBoundedObservable_of_mem hS hH
  set c := Real.exp (-InfiniteLattice.observableSupNorm (ReflectionGrid.ofRealFn H)) with hc
  have hcpos : 0 ≤ c := (Real.exp_pos _).le
  set N := (g.cellsWithin (g.block 0)).ncard with hNdef
  have hcard : N = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
  set P := g.productOfTransports S (g.block 0) (ReflectionGrid.expOfReal H) with hP
  have hint : Integrable P D.liftedMeasure :=
    h.integrable_of_isBoundedObservable
      (h.isBoundedObservable_productOfTransports hB hS (expOfReal_mem_cellObservables hH))
  have hpoint : ∀ U, c ^ N ≤ Complex.reCLM (P U) := by
    intro U
    have e : ∀ S' ∈ hfin.toFinset, g.transportTo S S' (ReflectionGrid.expOfReal H) U =
        ((Real.exp (H ((g.toLatticeSym (g.mover S S')).pullbackField U)) : ℝ) : ℂ) := by
      intro S' hS'
      have hc' : S' ∈ g.cellSet := (hfin.mem_toFinset.1 hS').1
      have hr := h.mover_spec hS hc'
      have e1 := congrFun (h.transportTo_expOfReal hS (g.mover S S') H) U
      have e2 := congrFun (h.transportTo_ofRealFn hS (g.mover S S') H) U
      rw [e2, hr] at e1
      rw [e1, Complex.ofReal_exp]
      rfl
    have e2 : P U = ((∏ S' ∈ hfin.toFinset,
        Real.exp (H ((g.toLatticeSym (g.mover S S')).pullbackField U)) : ℝ) : ℂ) := by
      rw [hP, h.productOfTransports_eq hB, Finset.prod_congr rfl e, Complex.ofReal_prod]
    rw [e2]
    show _ ≤ (((∏ S' ∈ hfin.toFinset, _ : ℝ)) : ℂ).re
    rw [Complex.ofReal_re, hcard, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => hcpos) fun S' _ => ?_
    refine Real.exp_le_exp.2 ?_
    have := abs_le_supNorm hobs ((g.toLatticeSym (g.mover S S')).pullbackField U)
    linarith [neg_abs_le (H ((g.toLatticeSym (g.mover S S')).pullbackField U))]
  have hre : (g.chessboardExpectation S (g.block 0) (ReflectionGrid.expOfReal H)).re =
      ∫ U, Complex.reCLM (P U) ∂D.liftedMeasure :=
    (Complex.reCLM.integral_comp_comm hint).symm
  have hle : c ^ N ≤ g.chessboardNorm S (ReflectionGrid.expOfReal H) ^ N := by
    rw [hNdef, h.chessboardNorm_pow hS (expOfReal_mem_cellObservables hH), hre, ← hNdef]
    have h1 : ∫ _ : D.GaugeField, c ^ N ∂D.liftedMeasure = c ^ N := by simp
    rw [← h1]
    exact integral_mono (integrable_const _) (Complex.reCLM.integrable_comp hint) hpoint
  exact le_of_pow_le_pow_left₀ (h.ncard_cellsWithin_ne_zero hB)
    (h.chessboardNorm_nonneg hS (expOfReal_mem_cellObservables hH)) hle
end GridFacts
end GridChessboardNormProof
theorem GridChessboardNorm.proof
    (hE : ChessboardInequality.Statement) (hG : ReflectionGroupAndTransport.Statement)
    (hP : CellParityAndCoarsening.Statement)
    (hO : MeasurableObservablesAndLifts.Statement)
    (hL : GridBasicProperties.Statement) : GridChessboardNorm.Statement := by
  intro D g hgrid hside B hB
  obtain ⟨e1, e2, e3, -⟩ := hE D g hside
  obtain ⟨-, gExact, -, gCopies, -⟩ := hG D g hgrid
  obtain ⟨-, pHalf, -⟩ := hP D g hgrid
  obtain ⟨-, -, oCells, -, oRead⟩ := hO D
  obtain ⟨-, -, -, lForm, lRules, -⟩ := hL D g
  have f : GridChessboardNormProof.GridFacts g :=
    ⟨hgrid, hside, e1, e2, e3, gExact, gCopies, pHalf hside, oCells, oRead, lForm, lRules⟩
  refine ⟨fun S hS F hF => f.liftedCopiesExpectation_eq hB hS hF,
    fun C hC F hF => f.norm_liftedProductExpectation_le hB hC hF,
    fun S hS => ⟨fun F hF => ⟨fun lam => f.chessboardNorm_smul hS hF lam,
      fun F' hF' => f.chessboardNorm_add_le hS hF hF', ((e3 S hS).1 F hF).1,
      ((e3 S hS).1 F hF).2.1.symm, ((e3 S hS).1 F hF).2.2⟩, (e3 S hS).2⟩,
    fun S hS H hH => ⟨GridChessboardNormProof.expOfReal_mem_cellObservables hH,
      fun r => ⟨f.transportTo_ofRealFn hS r H, f.transportTo_expOfReal hS r H⟩,
      f.liftedExpSumExpectation_eq hB hS hH, f.exp_neg_supNorm_le_chessboardNorm hS hH,
      f.chessboardNorm_expOfReal_le hS hH⟩⟩
end YangMills.Construction.ChessboardTori
end
