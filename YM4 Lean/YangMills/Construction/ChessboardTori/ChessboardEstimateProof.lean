import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGrids
import YangMills.Construction.ChessboardTori.ChessboardBoundOfAFamily
import YangMills.Construction.ChessboardTori.ChessboardEstimate
import YangMills.Construction.ChessboardTori.ChessboardNumberAcrossBoxes
import YangMills.Construction.ChessboardTori.CoarseGridsOfAGrid
import YangMills.Construction.ChessboardTori.NumberOfThePeriodisedSource
import YangMills.Construction.ChessboardTori.RulesOfTheChessboardNumber
import YangMills.Construction.ChessboardTori.TermsOfThePeriodisedSource
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace ChessboardInequality
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem cell_injective : Function.Injective g.cell := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGrid.cell_injective <;> assumption
theorem one_mem_cellObservables (S : Set AmbientSpace) :
    (fun _ => 1) ∈ ReflectionGrid.cellObservables (D := D) S := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.one_mem_cellObservables <;> assumption
end ChessboardInequality
open ChessboardInequality in
theorem ChessboardInequality.holds (hArith : ReflectionGridArithmetic.Statement)
    (hFamily : FamilyChessboardBound.Statement) (hBlocks : ChessboardBlockInvariance.Statement)
    (hRules : ChessboardExpectationRules.Statement) (hTerms : PeriodizedSourceTerms.Statement)
    (hExp : PeriodizedSourceExpectation.Statement) : ChessboardInequality.Statement := by
  intro D g hside
  have hA := (hArith D).2.2.2 g
  have hBlk := (hA.2 hside).2
  obtain ⟨-, hcps, -, h2, -⟩ := (hA.2 hside).1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = g.cellsPerTorusSide :=
    ⟨g.cellsPerTorusSide.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hnR : (n : ℝ) = g.cellsAcross := by
    rw [hcps, ← hn]
    simp
  have hn2 : 2 ≤ n := by omega
  have hidx : ∀ k₀ : Fin 4 → ℤ, g.blockIndices k₀ = (cubeIndexBox k₀ n : Set (Fin 4 → ℤ)) := by
    intro k₀
    ext j
    simp only [ReflectionGrid.blockIndices, cubeIndexBox, Set.mem_ofPred_eq, Finset.mem_coe,
      Fintype.mem_piFinset, Finset.mem_Ico]
    constructor
    · intro h μ
      have := h μ
      omega
    · intro h μ
      have := h μ
      omega
  have hprod : ∀ (k₀ : Fin 4 → ℤ) (H : Set AmbientSpace → ℂ),
      ∏ᶠ S ∈ g.cellsWithin (g.block k₀), H S = ∏ k ∈ cubeIndexBox k₀ n, H (g.cell k) := by
    intro k₀ H
    rw [(hBlk k₀).2.1, hidx, finprod_mem_image (cell_injective g).injOn, finprod_mem_coe_finset]
  have hprodR : ∀ (k₀ : Fin 4 → ℤ) (H : Set AmbientSpace → ℝ),
      ∏ᶠ S ∈ g.cellsWithin (g.block k₀), H S = ∏ k ∈ cubeIndexBox k₀ n, H (g.cell k) := by
    intro k₀ H
    rw [(hBlk k₀).2.1, hidx, finprod_mem_image (cell_injective g).injOn, finprod_mem_coe_finset]
  have hexp : ∀ (k₀ j : Fin 4 → ℤ) (F : D.GaugeField → ℂ),
      g.chessboardExpectation (g.cell j) (g.block k₀) F =
        D.familyExpectation k₀ n (g.transportedFamily j F) := by
    intro k₀ j F
    unfold ReflectionGrid.chessboardExpectation ReflectionGrid.productOfTransports
      ChessboardSetup.familyExpectation ReflectionGrid.transportedFamily
    congr 1
    funext U
    exact hprod k₀ fun S => g.transportTo (g.cell j) S F U
  have hacross : ∀ B ∈ g.blocks, ∀ B' ∈ g.blocks, ∀ S ∈ g.cellSet,
      ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
        g.chessboardExpectation S B' F = g.chessboardExpectation S B F := hBlocks D g hside
  have hnonneg : ∀ B ∈ g.blocks, ∀ S ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
      (g.chessboardExpectation S B F).im = 0 ∧ 0 ≤ (g.chessboardExpectation S B F).re := by
    rintro B hB S ⟨j, rfl⟩ F hF
    rw [hacross (g.block j) ⟨j, rfl⟩ B hB _ ⟨j, rfl⟩ F hF, hexp]
    classical
    let fam : (Fin 4 → ℤ) → D.GaugeField → ℂ := fun k => if k = j then F else fun _ => 1
    have hfam : ∀ k ∈ cubeIndexBox j n, fam k ∈ ReflectionGrid.cellObservables (D := D) (g.cell k) := by
      intro k _
      by_cases hk : k = j
      · subst hk
        simpa [fam] using hF
      · simpa [fam, hk] using one_mem_cellObservables (D := D) (g.cell k)
    have hj : j ∈ cubeIndexBox j n := by
      simp only [cubeIndexBox, Fintype.mem_piFinset, Finset.mem_Ico]
      intro μ
      omega
    have h := (hFamily D g hside j n hnR fam hfam).1 j hj
    have hfj : fam j = F := if_pos rfl
    rw [hfj] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB S hS F hF
    exact ⟨(hnonneg B hB S hS F hF).1, (hnonneg B hB S hS F hF).2,
      fun B' hB' => hacross B hB B' hB' S hS F hF⟩
  · rintro B ⟨k₀, rfl⟩ F hF
    have hfam : ∀ k ∈ cubeIndexBox k₀ n,
        F (g.cell k) ∈ ReflectionGrid.cellObservables (D := D) (g.cell k) := by
      intro k hk
      apply hF
      rw [(hBlk k₀).2.1, hidx]
      exact ⟨k, hk, rfl⟩
    have h := (hFamily D g hside k₀ n hnR (fun k => F (g.cell k)) hfam).2
    have hL : D.liftedExpectation (fun U => ∏ᶠ S ∈ g.cellsWithin (g.block k₀), F S U) =
        D.familyExpectation k₀ n fun k => F (g.cell k) := by
      unfold ChessboardSetup.familyExpectation
      congr 1
      funext U
      exact hprod k₀ fun S => F S U
    rw [hL, hprodR k₀ fun S => g.chessboardNorm S (F S)]
    refine h.trans (le_of_eq (Finset.prod_congr rfl fun j hj => ?_))
    rw [← hexp, hacross (g.block 0) ⟨0, rfl⟩ (g.block k₀) ⟨k₀, rfl⟩ _ ⟨j, rfl⟩ _ (hfam j hj), hnR]
    rfl
  · intro S hS
    have hR := hRules D g hside (g.block 0) ⟨0, rfl⟩ S hS
    refine ⟨fun F hF => ⟨fun S' hS' => ?_, ?_, ?_⟩, ?_⟩
    · have e : g.chessboardExpectation S' (g.block 0) (g.transportTo S S' F) =
          g.chessboardExpectation S (g.block 0) F := (hR.1 F hF).1 S' hS'
      simp only [ReflectionGrid.chessboardNorm, e]
    · have e : g.chessboardExpectation S (g.block 0) (fun U => starRingEnd ℂ (F U)) =
          starRingEnd ℂ (g.chessboardExpectation S (g.block 0) F) := (hR.1 F hF).2.1
      simp only [ReflectionGrid.chessboardNorm, e, Complex.conj_re]
    · have e : ‖g.chessboardExpectation S (g.block 0) F‖ ≤
          InfiniteLattice.observableSupNorm F ^ (g.cellsWithin (g.block 0)).ncard := (hR.1 F hF).2.2
      have hc : ((g.cellsWithin (g.block 0)).ncard : ℝ) = g.cellsAcross ^ 4 := by
        have h3 := (hBlk 0).2.2
        rw [← (hBlk 0).2.1, ← hn] at h3
        rw [← hnR]
        exact_mod_cast h3
      have hne : (g.cellsWithin (g.block 0)).ncard ≠ 0 := by
        intro h0
        rw [h0, ← hnR] at hc
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hpos : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
        rw [Nat.cast_zero] at hc
        exact hpos.ne hc
      have hC : 0 ≤ InfiniteLattice.observableSupNorm F :=
        Real.iSup_nonneg fun _ => norm_nonneg _
      have hre := (hnonneg _ ⟨0, rfl⟩ S hS F hF).2
      have hle : (g.chessboardExpectation S (g.block 0) F).re ≤
          InfiniteLattice.observableSupNorm F ^ (g.cellsWithin (g.block 0)).ncard :=
        (Complex.re_le_norm _).trans e
      calc g.chessboardNorm S F
          = (g.chessboardExpectation S (g.block 0) F).re ^
              (1 / ((g.cellsWithin (g.block 0)).ncard : ℝ)) := by
            rw [hc]
            rfl
        _ ≤ (InfiniteLattice.observableSupNorm F ^ (g.cellsWithin (g.block 0)).ncard) ^
              (1 / ((g.cellsWithin (g.block 0)).ncard : ℝ)) :=
            Real.rpow_le_rpow hre hle (by positivity)
        _ = InfiniteLattice.observableSupNorm F := by
            rw [one_div, Real.pow_rpow_inv_natCast hC hne]
    · have e : g.chessboardExpectation S (g.block 0) (fun _ => 1) = 1 := hR.2
      simp only [ReflectionGrid.chessboardNorm, e, Complex.one_re, Real.one_rpow]
  · intro S hS v Q hv hQ hQc hQS hd
    obtain ⟨t1, t2, t3⟩ := hTerms D g hside S hS v Q hv hQ hQc hQS hd
    obtain ⟨e1, e2⟩ := hExp D g hside S hS v Q hv hQ hQc hQS hd
    refine ⟨t1, t2, t3, e1, ?_⟩
    have hN : g.chessboardExpectation S (g.block 0) (fun U => Complex.exp (D.smeared v U)) =
        D.partitionFunctionOfPeriodic (g.periodizedSource v) / D.partitionFunction 0 :=
      e2 (g.block 0) ⟨0, rfl⟩
    obtain ⟨him, hre⟩ := hnonneg _ ⟨0, rfl⟩ S hS _ t1
    have hx : g.cellsAcross ^ 4 ≠ 0 := by
      rw [← hnR]
      have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      positivity
    have hval : g.chessboardNorm S (fun U => Complex.exp (D.smeared v U)) ^
        (g.cellsAcross ^ 4) =
        (g.chessboardExpectation S (g.block 0) fun U => Complex.exp (D.smeared v U)).re := by
      unfold ReflectionGrid.chessboardNorm
      rw [← Real.rpow_mul hre, one_div_mul_cancel hx, Real.rpow_one]
    rw [hval, ← hN]
    exact Complex.ext (by simp) (by simp [him])
end YangMills.Construction.ChessboardTori
end
