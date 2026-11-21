import YangMills.Construction.ChessboardTori.CellsBoxesAndParities
import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity
import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.ChessboardTori.ExpectationOnTheSideGroup
import YangMills.Construction.ChessboardTori.LengtheningATorusInOneDirection
import YangMills.Construction.ChessboardTori.RulesOfTheChessboardNumber
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLattice
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace ChessboardEstimateAndSubadditivity
section CellObservables
variable {D : ChessboardSetup}
theorem add_mem_cellObservables {S : Set AmbientSpace} {F F' : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S)
    (hF' : F' ∈ ReflectionGrid.cellObservables (D := D) S) :
    (fun U => F U + F' U) ∈ ReflectionGrid.cellObservables (D := D) S := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  obtain ⟨f', hf', ⟨C', hC'⟩, rfl⟩ := hF'
  exact ⟨fun u => f u + f' u, hf.add hf',
    ⟨C + C', fun u => (norm_add_le _ _).trans (add_le_add (hC u) (hC' u))⟩, rfl⟩
theorem const_mul_mem_cellObservables {S : Set AmbientSpace} {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) (ζ : ℂ) :
    (fun U => ζ * F U) ∈ ReflectionGrid.cellObservables (D := D) S := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  exact ⟨fun u => ζ * f u, hf.const_mul ζ,
    ⟨‖ζ‖ * C, fun u => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg _)⟩, rfl⟩
theorem conj_mem_cellObservables {S : Set AmbientSpace} {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    (fun U => starRingEnd ℂ (F U)) ∈ ReflectionGrid.cellObservables (D := D) S := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  exact ⟨fun u => starRingEnd ℂ (f u), Complex.continuous_conj.measurable.comp hf,
    ⟨C, fun u => by
      rw [Complex.norm_conj]
      exact hC u⟩, rfl⟩
theorem one_mem_cellObservables (S : Set AmbientSpace) :
    (fun _ => 1) ∈ ReflectionGrid.cellObservables (D := D) S :=
  ⟨fun _ => 1, measurable_const, ⟨1, by simp⟩, rfl⟩
theorem isBoundedObservable_of_mem_cellObservables {S : Set AmbientSpace} {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    InfiniteLattice.IsBoundedObservable F := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  refine ⟨hf.comp ?_, C, fun U => hC _⟩
  refine measurable_pi_iff.mpr fun b => ?_
  have hc : Continuous fun U : D.GaugeField => U b.1 :=
    (continuous_apply b.1).comp continuous_subtype_val
  exact hc.measurable
theorem isBoundedObservable_finset_prod {a : ℝ} {ι : Type*} (s : Finset ι)
    (A : ι → InfiniteLattice.GaugeField a → ℂ)
    (h : ∀ i ∈ s, InfiniteLattice.IsBoundedObservable (A i)) :
    InfiniteLattice.IsBoundedObservable fun U => ∏ i ∈ s, A i U := by
  refine ⟨Finset.measurable_prod _ fun i hi => (h i hi).1, ?_⟩
  have hb : ∀ i, ∃ C : ℝ, i ∈ s → ∀ U, ‖A i U‖ ≤ C := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨C, hC⟩ := (h i hi).2
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h' => absurd h' hi⟩
  choose C hC using hb
  refine ⟨∏ i ∈ s, C i, fun U => ?_⟩
  rw [norm_prod]
  exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => hC i hi U
end CellObservables
theorem finset_prod_ite_mem_of_subset {ι M : Type*} [CommMonoid M] [DecidableEq ι]
    {T E : Finset ι} (hE : E ⊆ T) (a b : ι → M) :
    ∏ i ∈ T, (if i ∈ E then a i else b i) = (∏ i ∈ E, a i) * ∏ i ∈ T \ E, b i := by
  rw [← Finset.prod_sdiff hE, mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => if_pos hi
  · exact Finset.prod_congr rfl fun i hi => if_neg (Finset.mem_sdiff.mp hi).2
section Expectations
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem cellSide_pos : 0 < g.cellSide :=
  zpow_pos (by linarith [D.one_lt_factor]) _
theorem cellsAcross_pos (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m) :
    0 < g.cellsAcross := by
  have hg := cellSide_pos g
  unfold ReflectionGrid.cellsAcross
  exact div_pos (by linarith) hg
theorem cellsWithin_finite_card (hCells : CellsBlocksAndSigns.Statement)
    (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m) {B S : Set AmbientSpace}
    (hB : B ∈ g.blocks) (hS : S ∈ g.cellSet) :
    (g.cellsWithin B).Finite ∧ ((g.cellsWithin B).ncard : ℝ) = g.cellsAcross ^ 4 ∧
      (g.cellsWithin B).ncard ≠ 0 := by
  have hcard := ((((hCells D g).2 hside).2 B hB).2 S hS).2.1
  have hpos : 0 < g.cellsAcross ^ 4 := pow_pos (cellsAcross_pos g hside) 4
  have hne : (g.cellsWithin B).ncard ≠ 0 := fun h0 => by
    rw [h0] at hcard
    simp only [Nat.cast_zero] at hcard
    linarith
  exact ⟨Set.finite_of_ncard_ne_zero hne, hcard, hne⟩
theorem mover_image_eq (hElem : GridBasicProperties.Statement) {S S' : Set AmbientSpace}
    (hS : S ∈ g.cellSet) (hS' : S' ∈ g.cellSet) : (g.mover S S').1 '' S = S' := by
  have h := (hElem D g).2.2.2.1.2.2.2.2.2.2.1 S hS S' hS'
  exact Classical.epsilon_spec (p := fun r : g.reflectionGroup => r.1 '' S = S') h.exists
theorem chessboardExpectation_const_mul (hElem : GridBasicProperties.Statement)
    (hCells : CellsBlocksAndSigns.Statement)
    (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m) {B S : Set AmbientSpace}
    (hB : B ∈ g.blocks) (hS : S ∈ g.cellSet) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) (ζ : ℂ) :
    g.chessboardExpectation S B (fun U => ζ * F U) =
      ((‖ζ‖ ^ (g.cellsWithin B).ncard : ℝ) : ℂ) * g.chessboardExpectation S B F := by
  classical
  obtain ⟨hfin, hcard, hne⟩ := cellsWithin_finite_card g hCells hside hB hS
  set T := hfin.toFinset with hT
  have hTm : ∀ S', S' ∈ T ↔ S' ∈ g.cellsWithin B := fun S' => hfin.mem_toFinset
  have hncard : (g.cellsWithin B).ncard = T.card := Set.ncard_eq_toFinset_card _ hfin
  have hcopies := (hElem D g).2.2.2.2.1
  have hform := (hElem D g).2.2.2.1
  have hsimple := hform.2.2.2.2.2.2.1
  let σ : Set AmbientSpace → ℤˣ := fun S' => orientationSign (g.mover S S').1
  have hrule : ∀ S' ∈ T, g.transportTo S S' (fun U => ζ * F U) =
      fun U => Conventions.signedConj (σ S') ζ * g.transportTo S S' F U := fun S' hS' => by
    have hc := ((hTm S').mp hS').1
    exact (hcopies S hS S' hc S' hc (g.mover S S') (mover_image_eq g hElem hS hc)
      F hF F hF ζ).2.2.2.2.2.2.1
  set Od := T.filter fun S' => σ S' = -1 with hOd
  have hOdset : (↑Od : Set (Set AmbientSpace)) =
      {S' ∈ g.cellsWithin B | ∃ r ∈ g.reflectionGroup, orientationSign r = -1 ∧ S' = r '' S} := by
    ext S'
    simp only [hOd, Finset.coe_filter, Set.mem_ofPred_eq, hTm]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, _, (g.mover S S').2, h2, (mover_image_eq g hElem hS h1.1).symm⟩
    · rintro ⟨h1, r, hr, h2, h3⟩
      refine ⟨h1, ?_⟩
      have hu := (hsimple S hS S' h1.1).unique (mover_image_eq g hElem hS h1.1)
        (y₂ := ⟨r, hr⟩) h3.symm
      have : (g.mover S S').1 = r := congrArg Subtype.val hu
      simp only [σ, this, h2]
  have hhalf := ((((hCells D g).2 hside).2 B hB).2 S hS).2.2.1
  have hOc : 2 * Od.card = T.card := by
    rw [← hOdset, Set.ncard_coe_finset, ← hcard, hncard] at hhalf
    have h2 : (2 : ℝ) * (Od.card : ℝ) = (T.card : ℝ) := by linarith
    exact_mod_cast h2
  have hEc : (T.filter fun S' => ¬ σ S' = -1).card = Od.card := by
    have h : Od.card + (T.filter fun S' => ¬ σ S' = -1).card = T.card :=
      Finset.card_filter_add_card_filter_not (s := T) (fun S' => σ S' = -1)
    omega
  have hconst : ∏ S' ∈ T, Conventions.signedConj (σ S') ζ = ((‖ζ‖ ^ T.card : ℝ) : ℂ) := by
    rw [← Finset.prod_filter_mul_prod_filter_not T (fun S' => σ S' = -1)]
    have h1 : ∏ S' ∈ T.filter (fun S' => σ S' = -1), Conventions.signedConj (σ S') ζ =
        starRingEnd ℂ ζ ^ Od.card := by
      rw [Finset.prod_congr rfl (g := fun _ => starRingEnd ℂ ζ), Finset.prod_const]
      intro S' hS'
      have hm := (Finset.mem_filter.mp hS').2
      simp [Conventions.signedConj, hm]
    have h2 : ∏ S' ∈ T.filter (fun S' => ¬ σ S' = -1), Conventions.signedConj (σ S') ζ =
        ζ ^ Od.card := by
      rw [Finset.prod_congr rfl (g := fun _ => ζ), Finset.prod_const, hEc]
      intro S' hS'
      have hm := (Finset.mem_filter.mp hS').2
      have h1 : σ S' = 1 := (Int.units_eq_one_or _).resolve_right hm
      simp [Conventions.signedConj, h1]
    rw [h1, h2, ← mul_pow, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← hOc]
    push_cast
    rw [pow_mul]
  have hfun : (fun U => ∏ᶠ S' ∈ g.cellsWithin B, g.transportTo S S' (fun U => ζ * F U) U) =
      fun U => (∏ S' ∈ T, Conventions.signedConj (σ S') ζ) *
        ∏ᶠ S' ∈ g.cellsWithin B, g.transportTo S S' F U := by
    funext U
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun S' hS' => congrFun (hrule S' hS') U
  unfold ReflectionGrid.chessboardExpectation ReflectionGrid.productOfTransports
    ChessboardSetup.liftedExpectation
  rw [hfun, integral_const_mul, hconst, hncard]
theorem chessboardNorm_const_mul (hElem : GridBasicProperties.Statement)
    (hCells : CellsBlocksAndSigns.Statement) (hEst : ChessboardInequality.Statement)
    (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m) {S : Set AmbientSpace}
    (hS : S ∈ g.cellSet) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) (ζ : ℂ) :
    g.chessboardNorm S (fun U => ζ * F U) = ‖ζ‖ * g.chessboardNorm S F := by
  obtain ⟨-, hcard, hne⟩ := cellsWithin_finite_card g hCells hside (B := g.block 0) ⟨0, rfl⟩ hS
  have hre := ((hEst D g hside).1 _ ⟨0, rfl⟩ S hS F hF).2.1
  unfold ReflectionGrid.chessboardNorm
  rw [chessboardExpectation_const_mul g hElem hCells hside ⟨0, rfl⟩ hS hF ζ,
    Complex.re_ofReal_mul, Real.mul_rpow (by positivity) hre, ← hcard, one_div,
    Real.pow_rpow_inv_natCast (norm_nonneg _) hne]
theorem chessboardNorm_add_le (hElem : GridBasicProperties.Statement)
    (hCells : CellsBlocksAndSigns.Statement) (hEst : ChessboardInequality.Statement)
    (hProb : IsProbabilityMeasure D.liftedMeasure)
    (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m) {S : Set AmbientSpace}
    (hS : S ∈ g.cellSet) {F F' : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S)
    (hF' : F' ∈ ReflectionGrid.cellObservables (D := D) S) :
    g.chessboardNorm S (fun U => F U + F' U) ≤ g.chessboardNorm S F + g.chessboardNorm S F' := by
  classical
  have hB : g.block 0 ∈ g.blocks := ⟨0, rfl⟩
  obtain ⟨hfin, hcard, hne⟩ := cellsWithin_finite_card g hCells hside hB hS
  set T := hfin.toFinset with hT
  have hTm : ∀ S', S' ∈ T ↔ S' ∈ g.cellsWithin (g.block 0) := fun S' => hfin.mem_toFinset
  have hncard : (g.cellsWithin (g.block 0)).ncard = T.card := Set.ncard_eq_toFinset_card _ hfin
  obtain ⟨hE1, hE2, hE3, -⟩ := hEst D g hside
  have hcopies := (hElem D g).2.2.2.2.1
  have hrule : ∀ S' ∈ g.cellSet, g.transportTo S S' (fun U => F U + F' U) =
      fun U => g.transportTo S S' F U + g.transportTo S S' F' U := fun S' hc =>
    (hcopies S hS S' hc S' hc (g.mover S S') (mover_image_eq g hElem hS hc)
      F hF F' hF' 1).2.2.2.2.2.1
  have hmem : ∀ S' ∈ g.cellSet,
      g.transportTo S S' F ∈ ReflectionGrid.cellObservables (D := D) S' := fun S' hc =>
    (hcopies S hS S' hc S' hc (g.mover S S') (mover_image_eq g hElem hS hc) F hF F hF 1).1
  have hmem' : ∀ S' ∈ g.cellSet,
      g.transportTo S S' F' ∈ ReflectionGrid.cellObservables (D := D) S' := fun S' hc =>
    (hcopies S hS S' hc S' hc (g.mover S S') (mover_image_eq g hElem hS hc) F' hF' F' hF' 1).1
  set x := g.chessboardNorm S F with hx
  set y := g.chessboardNorm S F' with hy
  have hx0 : 0 ≤ x := Real.rpow_nonneg (hE1 _ hB S hS F hF).2.1 _
  have hy0 : 0 ≤ y := Real.rpow_nonneg (hE1 _ hB S hS F' hF').2.1 _
  let G : Finset (Set AmbientSpace) → Set AmbientSpace → D.GaugeField → ℂ := fun E S' =>
    if S' ∈ E then g.transportTo S S' F else g.transportTo S S' F'
  have hG : ∀ E, ∀ S' ∈ g.cellSet, G E S' ∈ ReflectionGrid.cellObservables (D := D) S' := by
    intro E S' hc
    simp only [G]
    split_ifs
    · exact hmem S' hc
    · exact hmem' S' hc
  have hGprod : ∀ E ∈ T.powerset, ∀ U, ∏ S' ∈ T, G E S' U =
      (∏ S' ∈ E, g.transportTo S S' F U) * ∏ S' ∈ T \ E, g.transportTo S S' F' U := by
    intro E hE U
    rw [← finset_prod_ite_mem_of_subset (Finset.mem_powerset.mp hE)]
    refine Finset.prod_congr rfl fun S' _ => ?_
    simp only [G]
    split_ifs <;> rfl
  have hint : ∀ E ∈ T.powerset,
      Integrable (fun U => ∏ S' ∈ T, G E S' U) D.liftedMeasure := by
    intro E _
    obtain ⟨hm, C, hC⟩ := isBoundedObservable_finset_prod T (G E) fun S' hS' =>
      isBoundedObservable_of_mem_cellObservables (hG E S' ((hTm S').mp hS').1)
    exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
  have hN : g.chessboardExpectation S (g.block 0) (fun U => F U + F' U) =
      ∑ E ∈ T.powerset, D.liftedExpectation fun U => ∏ S' ∈ T, G E S' U := by
    unfold ReflectionGrid.chessboardExpectation ReflectionGrid.productOfTransports
      ChessboardSetup.liftedExpectation
    rw [← integral_finsetSum _ hint]
    congr 1
    funext U
    beta_reduce
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin,
      Finset.prod_congr rfl fun S' hS' => congrFun (hrule S' ((hTm S').mp hS').1) U,
      Finset.prod_add]
    exact Finset.sum_congr rfl fun E hE => (hGprod E hE U).symm
  have hbound : ∀ E ∈ T.powerset, ‖D.liftedExpectation fun U => ∏ S' ∈ T, G E S' U‖ ≤
      x ^ E.card * y ^ (T \ E).card := by
    intro E hE
    have h := hE2 _ hB (G E) fun S' hS' => hG E S' hS'.1
    have h1 : (fun U => ∏ᶠ S' ∈ g.cellsWithin (g.block 0), G E S' U) =
        fun U => ∏ S' ∈ T, G E S' U := by
      funext U
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
    rw [h1, finprod_mem_eq_finite_toFinset_prod _ hfin] at h
    refine h.trans (le_of_eq ?_)
    have h2 : ∏ S' ∈ T, g.chessboardNorm S' (G E S') =
        ∏ S' ∈ T, (if S' ∈ E then x else y) := by
      refine Finset.prod_congr rfl fun S' hS' => ?_
      have hc := ((hTm S').mp hS').1
      simp only [G]
      split_ifs
      · exact ((hE3 S hS).1 F hF).1 S' hc
      · exact ((hE3 S hS).1 F' hF').1 S' hc
    rw [h2, finset_prod_ite_mem_of_subset (Finset.mem_powerset.mp hE) (fun _ => x) (fun _ => y),
      Finset.prod_const, Finset.prod_const]
  have hsum : ‖g.chessboardExpectation S (g.block 0) (fun U => F U + F' U)‖ ≤
      (x + y) ^ T.card := by
    have h := Finset.prod_add (fun _ => x) (fun _ => y) T
    simp only [Finset.prod_const] at h
    rw [hN, h]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum hbound)
  have hmF := add_mem_cellObservables hF hF'
  have hre := (hE1 _ hB S hS _ hmF).2.1
  calc g.chessboardNorm S (fun U => F U + F' U)
      ≤ ((x + y) ^ T.card) ^ (1 / g.cellsAcross ^ 4) :=
        Real.rpow_le_rpow hre ((Complex.re_le_norm _).trans hsum) (by
          have := cellsAcross_pos g hside
          positivity)
    _ = x + y := by
        rw [← hcard, hncard, one_div, Real.pow_rpow_inv_natCast (add_nonneg hx0 hy0)
          (hncard ▸ hne)]
end Expectations
section Coupled
variable (O : CoupledGrid)
theorem evenIndexVector_ext {n n' : EvenIndexVector} (h : n.coord = n'.coord) : n = n' := by
  obtain ⟨_, _, _⟩ := n
  obtain ⟨_, _, _⟩ := n'
  cases h
  rfl
theorem stretch_all_four_axes (hLength : TorusStretchBound.Statement)
    {S : Set AmbientSpace} (hS : S ∈ O.grid.cellSet) {F : O.toChessboardSetup.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S) (c : ℤ)
    (n₀ n₄ : EvenIndexVector) (h₀ : n₀.coord = fun _ => c) (j : ℕ) (hj : 1 ≤ j)
    (h₄ : n₄.coord = fun _ => (j : ℤ) * c) :
    (O.chessboardPartitionOn n₀ S F).im = 0 ∧ (O.chessboardPartitionOn n₄ S F).im = 0 ∧
      0 ≤ (O.chessboardPartitionOn n₄ S F).re ∧
      (O.chessboardPartitionOn n₄ S F).re ≤ (O.chessboardPartitionOn n₀ S F).re ^ (j ^ 4) := by
  set n₁ := n₀.stretch 0 hj with hn₁
  set n₂ := n₁.stretch 1 hj with hn₂
  set n₃ := n₂.stretch 2 hj with hn₃
  have hU : n₃.stretch 3 hj = n₄ := by
    refine evenIndexVector_ext ?_
    rw [h₄]
    funext ν
    simp only [hn₃, hn₂, hn₁, EvenIndexVector.stretch, h₀]
    fin_cases ν <;> simp [scaleCoord, Function.update]
  obtain ⟨i0, -, p1, l1⟩ := (hLength O n₀ 0 j hj).2 S hS F hF
  obtain ⟨-, -, p2, l2⟩ := (hLength O n₁ 1 j hj).2 S hS F hF
  obtain ⟨-, -, p3, l3⟩ := (hLength O n₂ 2 j hj).2 S hS F hF
  obtain ⟨-, i4, p4, l4⟩ := (hLength O n₃ 3 j hj).2 S hS F hF
  rw [hU] at i4 p4 l4
  refine ⟨i0, i4, p4, l4.trans ?_⟩
  have s3 := pow_le_pow_left₀ p3 l3 j
  have s2 := pow_le_pow_left₀ (pow_nonneg p2 j) (pow_le_pow_left₀ p2 l2 j) j
  have s1 := pow_le_pow_left₀ (pow_nonneg (pow_nonneg p1 j) j)
    (pow_le_pow_left₀ (pow_nonneg p1 j) (pow_le_pow_left₀ p1 l1 j) j) j
  refine s3.trans (s2.trans (s1.trans (le_of_eq ?_)))
  rw [← pow_mul, ← pow_mul, ← pow_mul]
  congr 1
  ring
theorem chessboardPartition_eq_mul (hElem : GridBasicProperties.Statement)
    (hArith : ReflectionGridArithmetic.Statement)
    (hRules : ChessboardExpectationRules.Statement)
    (hSide : PeriodExpectation.Statement)
    (hCells : CellsBlocksAndSigns.Statement)
    (hWeights : ReflectionPeriodicWeightsAsCellFunctions.Statement)
    (hside : 2 * O.cellSide ≤ PeriodicLattice.torusSide O.L O.m) {S : Set AmbientSpace}
    (hS : S ∈ O.grid.cellSet) {F : O.toChessboardSetup.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S) :
    O.chessboardPartition S F =
      O.toChessboardSetup.partitionFunction 0 *
        O.grid.chessboardExpectation S (O.grid.block 0) F := by
  classical
  have hside' : 2 * O.grid.cellSide ≤ PeriodicLattice.torusSide O.L O.m := hside
  obtain ⟨⟨-, -, -, hn, hgrp, hZ⟩, hBox⟩ :=
    ((hArith O.toChessboardSetup).2.2.2 O.grid).2 hside'
  have hP : O.periodSubgroupOf O.diagonalCounts = O.toChessboardSetup.cubicPeriod := hgrp
  obtain ⟨Z, hZ0, hEx⟩ := hSide O.toChessboardSetup _ hP
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ0.ne'
  have hinj : Function.Injective O.grid.cell := fun k k' h => by
    have hpos := cellSide_pos O.grid
    have hle : ∀ {k k' : Fin 4 → ℤ}, O.grid.cell k ⊆ O.grid.cell k' → ∀ μ, k' μ ≤ k μ := by
      intro k k' h μ
      have hp : (fun ν => O.grid.origin ν + O.grid.cellSide * k ν) ∈ O.grid.cell k := fun ν => by
        simp [hpos.le]
      have h0 := (h hp μ).1
      have h1 : O.grid.cellSide * (k' μ : ℝ) ≤ O.grid.cellSide * (k μ : ℝ) := by linarith
      exact_mod_cast le_of_mul_le_mul_left h1 hpos
    funext μ
    exact le_antisymm (hle h.ge μ) (hle h.le μ)
  have hidx : O.grid.blockIndices 0 = (O.diagonalCounts.indexBox : Set (Fin 4 → ℤ)) := by
    ext j
    simp only [ReflectionGrid.blockIndices, EvenIndexVector.indexBox, Set.mem_ofPred_eq,
      Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico, Pi.zero_apply]
    have he : ∀ κ, O.diagonalCounts.coord κ = O.grid.cellsPerTorusSide := fun _ => rfl
    constructor
    · intro h μ
      have := h μ
      rw [he]
      omega
    · intro h μ
      have := h μ
      rw [he] at this
      omega
  have hprod : ∀ H : Set AmbientSpace → ℂ, ∏ᶠ S' ∈ O.grid.cellsWithin (O.grid.block 0), H S' =
      ∏ k ∈ O.diagonalCounts.indexBox, H (O.grid.cell k) := by
    intro H
    rw [(hBox 0).2.1, hidx, finprod_mem_image hinj.injOn, finprod_mem_coe_finset]
  obtain ⟨hfin, -, -⟩ :=
    cellsWithin_finite_card O.grid hCells hside' (B := O.grid.block 0) ⟨0, rfl⟩ hS
  have hcopies := (hElem O.toChessboardSetup O.grid).2.2.2.2.1
  have key : ∀ S ∈ O.grid.cellSet,
      ∀ F ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S,
      O.grid.chessboardExpectation S (O.grid.block 0) F =
        O.chessboardPartitionOn O.diagonalCounts S F / Z := by
    intro S hS F hF
    have hobs : InfiniteLattice.IsBoundedObservable
        (O.grid.productOfTransports S (O.grid.block 0) F) := by
      have h := isBoundedObservable_finset_prod O.diagonalCounts.indexBox
        (fun k => O.grid.transportTo S (O.grid.cell k) F) fun k _ => by
          have hc : O.grid.cell k ∈ O.grid.cellSet := ⟨k, rfl⟩
          exact isBoundedObservable_of_mem_cellObservables
            (hcopies S hS _ hc _ hc _ (mover_image_eq O.grid hElem hS hc) F hF F hF 1).1
      have he : O.grid.productOfTransports S (O.grid.block 0) F =
          fun U => ∏ k ∈ O.diagonalCounts.indexBox, O.grid.transportTo S (O.grid.cell k) F U := by
        funext U
        exact hprod fun S' => O.grid.transportTo S S' F U
      rw [he]
      exact h
    rw [ReflectionGrid.chessboardExpectation, hEx _ hobs]
    congr 1
    unfold CoupledGrid.chessboardPartitionOn
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    beta_reduce
    congr 1
    exact hprod fun S' => O.grid.transportTo S S' F _
  have hzero : O.grid.IsReflectionPeriodic 0 :=
    ⟨⟨0, fun _ => by simp⟩, fun _ _ => by
      funext x
      simp, fun _ _ => rfl⟩
  have hexp : O.cellExpWeight 0 S = fun _ => 1 := by
    funext U
    simp [CoupledGrid.cellExpWeight, ChessboardSetup.smeared, InfiniteLattice.smearedEnergy]
  have hw := (hWeights O 0 hzero).2.2.2.2 O.diagonalCounts S hS
  rw [hexp] at hw
  have h1 := (hRules O.toChessboardSetup O.grid hside' _ ⟨0, rfl⟩ S hS).2
  have h1' : O.grid.chessboardExpectation S (O.grid.block 0) (fun _ => 1) = 1 := h1
  rw [key S hS _ (one_mem_cellObservables S), hw, div_eq_one_iff_eq hZc] at h1'
  have hz : O.toChessboardSetup.partitionFunction 0 = Z := by
    have e : O.toChessboardSetup.partitionFunctionOfPeriodic 0 =
        O.toChessboardSetup.partitionFunction 0 := rfl
    rw [← e, ← hZ 0 ⟨0, fun _ => by simp⟩ (fun _ _ _ => rfl)]
    exact h1'
  rw [key S hS F hF, hz]
  unfold CoupledGrid.chessboardPartition
  field_simp
theorem exists_stretch_factor (hArith : ReflectionGridArithmetic.Statement) (m' : ℕ+)
    (h1 : PeriodicLattice.torusSide O.L m' ≤ PeriodicLattice.torusSide O.L O.m)
    (h2 : 2 * O.cellSide ≤ PeriodicLattice.torusSide O.L m') :
    ∃ (j : ℕ) (_ : 1 ≤ j),
      O.diagonalCounts.coord = (fun _ => (j : ℤ) * (O.withExponent m').grid.cellsPerTorusSide) ∧
      ((PeriodicLattice.torusSide O.L O.m / PeriodicLattice.torusSide O.L m') ^ 4 : ℝ) =
        ((j ^ 4 : ℕ) : ℝ) := by
  have hL : (1 : ℝ) < O.L := O.toChessboardSetup.one_lt_factor
  have hLn : 0 < O.L := by
    have := O.toChessboardSetup.isAdmissible.2
    omega
  have hmm : (m' : ℕ) ≤ (O.m : ℕ) := by
    have h : (O.L : ℝ) ^ (m' : ℕ) ≤ (O.L : ℝ) ^ (O.m : ℕ) := by
      simp only [PeriodicLattice.torusSide] at h1
      linarith
    exact (pow_le_pow_iff_right₀ hL).mp h
  obtain ⟨⟨hq', -⟩, -⟩ :=
    ((hArith (O.toChessboardSetup.withExponent m')).2.2.2 (O.grid.withExponent m')).2 h2
  have hq : O.grid.q ≤ ((m' : ℕ) : ℤ) := hq'
  refine ⟨O.L ^ ((O.m : ℕ) - (m' : ℕ)), Nat.one_le_pow _ _ hLn, ?_, ?_⟩
  · funext κ
    have hexp : (((O.m : ℕ) : ℤ) - O.grid.q).toNat =
        ((O.m : ℕ) - (m' : ℕ)) + (((m' : ℕ) : ℤ) - O.grid.q).toNat := by omega
    change 2 * (O.L : ℤ) ^ (((O.m : ℕ) : ℤ) - O.grid.q).toNat =
      ((O.L ^ ((O.m : ℕ) - (m' : ℕ)) : ℕ) : ℤ) *
        (2 * (O.L : ℤ) ^ (((m' : ℕ) : ℤ) - O.grid.q).toNat)
    rw [hexp, pow_add]
    push_cast
    ring
  · have hs : (O.L : ℝ) ^ (O.m : ℕ) =
        ((O.L ^ ((O.m : ℕ) - (m' : ℕ)) : ℕ) : ℝ) * (O.L : ℝ) ^ (m' : ℕ) := by
      push_cast
      rw [← pow_add, Nat.sub_add_cancel hmm]
    have hd : PeriodicLattice.torusSide O.L O.m / PeriodicLattice.torusSide O.L m' =
        ((O.L ^ ((O.m : ℕ) - (m' : ℕ)) : ℕ) : ℝ) := by
      simp only [PeriodicLattice.torusSide]
      rw [hs]
      field_simp
    rw [hd]
    push_cast
    rfl
end Coupled
end ChessboardEstimateAndSubadditivity
open ChessboardEstimateAndSubadditivity in
theorem ChessboardEstimateAndSubadditivity.holds (hElem : GridBasicProperties.Statement)
    (hArith : ReflectionGridArithmetic.Statement) (hEst : ChessboardInequality.Statement)
    (hCells : CellsBlocksAndSigns.Statement) (hRules : ChessboardExpectationRules.Statement)
    (hSide : PeriodExpectation.Statement) (hCover : LatticeCovering.CoveringStatement)
    (hWeights : ReflectionPeriodicWeightsAsCellFunctions.Statement)
    (hLength : TorusStretchBound.Statement)
    (hSub : PartitionFunctionSubmultiplicativity.Statement) :
    ChessboardEstimateAndSubadditivity.Statement := by
  intro O hside
  have hside' : 2 * O.grid.cellSide ≤ PeriodicLattice.torusSide O.L O.m := hside
  have hProb : IsProbabilityMeasure O.toChessboardSetup.liftedMeasure :=
    (hCover ⟨O.toChessboardSetup.toStandingParameters, O.β, O.beta_pos⟩).2.2.1.2.2.2.2.2
  obtain ⟨hE1, hE2, hE3, -⟩ := hEst O.toChessboardSetup O.grid hside'
  have hcopies := (hElem O.toChessboardSetup O.grid).2.2.2.2.1
  refine ⟨?_, ?_, fun m' h1 h2 => ?_⟩
  · intro S hS
    refine ⟨⟨one_mem_cellObservables S, (hE3 S hS).2⟩, fun F =>
      ⟨fun B hB => ?_, fun S' hS' => ?_, ?_, ((hE3 S hS).1 F.1 F.2).2.2, fun ζ => ?_,
        fun F' => ?_⟩⟩
    · obtain ⟨i, p, e⟩ := hE1 B hB S hS F.1 F.2
      refine ⟨(cellsWithin_finite_card O.grid hCells hside' hB hS).2.1, i, p, e, ?_⟩
      have e0 := e (O.grid.block 0) ⟨0, rfl⟩
      change _ = (O.grid.chessboardExpectation S (O.grid.block 0) F.1).re ^ _
      rw [e0]
    · exact ⟨(hcopies S hS S' hS' S' hS' _ (mover_image_eq O.grid hElem hS hS')
        F.1 F.2 F.1 F.2 1).1, ((hE3 S hS).1 F.1 F.2).1 S' hS'⟩
    · exact ⟨conj_mem_cellObservables F.2, ((hE3 S hS).1 F.1 F.2).2.1.symm⟩
    · exact ⟨const_mul_mem_cellObservables F.2 ζ,
        chessboardNorm_const_mul O.grid hElem hCells hEst hside' hS F.2 ζ⟩
    · exact ⟨add_mem_cellObservables F.2 F'.2,
        chessboardNorm_add_le O.grid hElem hCells hEst hProb hside' hS F.2 F'.2⟩
  · intro B hB F
    classical
    let G : Set AmbientSpace → O.toChessboardSetup.GaugeField → ℂ := fun S =>
      if h : S ∈ O.grid.cellsWithin B then (F ⟨S, h⟩).1 else 0
    have hG : ∀ S : O.grid.cellsWithin B, G S.1 = (F S).1 := fun S => by
      simp only [G, dif_pos S.2]
    have h := hE2 B hB G fun S hS => by
      rw [hG ⟨S, hS⟩]
      exact (F ⟨S, hS⟩).2
    have hl : (fun U => ∏ᶠ S : O.grid.cellsWithin B, (F S).1 U) =
        fun U => ∏ᶠ S ∈ O.grid.cellsWithin B, G S U := by
      funext U
      rw [← finprod_set_coe_eq_finprod_mem]
      exact finprod_congr fun S => by rw [hG S]
    have hr : ∏ᶠ S : O.grid.cellsWithin B, O.cellChessboardSeminorm hside S.2.1 (F S) =
        ∏ᶠ S ∈ O.grid.cellsWithin B, O.grid.chessboardNorm S (G S) := by
      rw [← finprod_set_coe_eq_finprod_mem]
      refine finprod_congr fun S => ?_
      rw [hG S]
      rfl
    rw [hl, hr]
    exact h
  · obtain ⟨j, hj, hent, hexp⟩ := exists_stretch_factor O hArith m' h1 h2
    refine ⟨fun W hW => (hSub O.toChessboardSetup O.grid W hW).2.2 m' h1 h2, fun S hS F => ?_,
      fun W hW S hS => ?_⟩
    · obtain ⟨i0, i4, p4, l4⟩ := stretch_all_four_axes O hLength hS F.2
        (O.withExponent m').grid.cellsPerTorusSide (O.withExponent m').diagonalCounts
        O.diagonalCounts rfl j hj hent
      obtain ⟨him, hre, -⟩ := hE1 _ ⟨0, rfl⟩ S hS F.1 F.2
      have hx : O.grid.cellsAcross ^ 4 ≠ 0 := (pow_pos (cellsAcross_pos O.grid hside') 4).ne'
      have hval : O.cellChessboardSeminorm hside hS F ^ (O.grid.cellsAcross ^ 4) =
          (O.grid.chessboardExpectation S (O.grid.block 0) F.1).re := by
        change ((O.grid.chessboardExpectation S (O.grid.block 0) F.1).re ^
          (1 / O.grid.cellsAcross ^ 4)) ^ (O.grid.cellsAcross ^ 4) = _
        rw [← Real.rpow_mul hre, one_div_mul_cancel hx, Real.rpow_one]
      refine ⟨?_, i4, i0, p4, ?_⟩
      · rw [hval, chessboardPartition_eq_mul O hElem hArith hRules hSide hCells hWeights hside hS F.2]
        congr 1
        exact Complex.ext (by simp) (by simp [him])
      · rw [hexp, Real.rpow_natCast]
        exact l4
    · obtain ⟨⟨-, -, hev, hn, hgrp, hZ⟩, -⟩ :=
        ((hArith O.toChessboardSetup).2.2.2 O.grid).2 hside'
      have hw := hWeights O W hW
      refine ⟨(hw.2.2.2.1 S hS).2.1, ?_⟩
      have hper := ((hSub O.toChessboardSetup O.grid W hW).2.1
        (fun _ => O.grid.cellsPerTorusSide) (fun _ => hn) fun _ => hev).1
      rw [hgrp] at hper
      exact (hw.2.2.2.2 O.diagonalCounts S hS).trans (hZ W hW.1 hper)
end ChessboardTori
end YangMills.Construction
end
