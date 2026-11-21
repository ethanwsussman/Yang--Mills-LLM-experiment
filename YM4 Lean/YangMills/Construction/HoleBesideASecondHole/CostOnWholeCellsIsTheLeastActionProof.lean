import YangMills.Construction.HoleBesideASecondHole.CutActionIsTheLeastActionProof
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.CostOnWholeCellsIsTheLeastAction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LumpContours
open BlockAverages
namespace WholeCellCost
variable {F : BlockFrame}
theorem sitesBelow_eq_image (j : ℕ) (z : F.Cell) :
    sitesBelow j z = (centredCube (F.blockSide ^ (F.top - j))).image
      fun h => cellCentre j z + siteOfCoords j h := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.sitesBelow_cell_eq <;> assumption
theorem cutBelow_eq_sitesOfCells (S : Finset F.Cell) (j : ℕ) : cutBelow j S = sitesOfCells S j := by
  unfold cutBelow sitesOfCells
  exact Finset.biUnion_congr rfl fun z _ => sitesBelow_eq_image j z
theorem cutBelow_sitesOfCells (hL : Odd F.blockSide) (S : Finset F.Cell) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ F.top) : cutBelow i (sitesOfCells S j) = sitesOfCells S i := by apply _root_.YangMills.Construction.LumpContours.CutAction.cutBelow_sitesOfCells <;> assumption
def partialChainEnergy (a : ℝ) (S : Finset F.Cell) (j : ℕ) (U : F.FieldChain) : ℝ :=
  wilsonAction S (U 0) +
    a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1), blockFit (U i) (U (i + 1)) c
theorem cutChainEnergy_eq (hL : Odd F.blockSide) (a : ℝ) (S : Finset F.Cell) {j : ℕ} (hj : j ≤ F.top)
    (U : F.FieldChain) : cutChainEnergy a j (cutBelow j S) U = partialChainEnergy a S j U := by
  rw [cutBelow_eq_sitesOfCells]
  unfold cutChainEnergy partialChainEnergy
  rw [cutBelow_sitesOfCells hL S (Nat.zero_le j) hj]
  congr 2
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cutBelow_sitesOfCells hL S (Finset.mem_range.1 hi) hj]
  rfl
theorem partialChainEnergy_succ (a : ℝ) (S : Finset F.Cell) (j : ℕ) (U : F.FieldChain) :
    partialChainEnergy a S (j + 1) U =
      partialChainEnergy a S j U + a * ∑ c ∈ innerBonds S (j + 1), blockFit (U j) (U (j + 1)) c := by apply _root_.YangMills.Construction.LumpContours.CutAction.chainEnergyUpTo_succ <;> assumption
theorem partialChainEnergy_nonneg (hV : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset F.Cell) (j : ℕ) (U : F.FieldChain) : 0 ≤ partialChainEnergy a S j U := by
  obtain ⟨hf, hl, -, -⟩ := hV F a S ha
  refine add_nonneg (hl 0 (U 0))
    (mul_nonneg ha (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ => hf _ _ _ _))
instance instNonemptyChainThrough (j : ℕ) (V : F.GaugeField j) :
    Nonempty {U : F.FieldChain // U j = V} :=
  ⟨⟨Function.update (fun _ _ _ => 1) j V, by simp⟩⟩
theorem minimalAction_eq_iInf (hV : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset F.Cell) (j : ℕ) (V : F.GaugeField j) :
    minimalAction a S j V = ⨅ U : {U : F.FieldChain // U j = V}, partialChainEnergy a S j U.1 := by
  have hbdd : ∀ (j : ℕ) (V : F.GaugeField j),
      BddBelow (Set.range fun U : {U : F.FieldChain // U j = V} => partialChainEnergy a S j U.1) := by
    intro j V
    refine ⟨0, ?_⟩
    rintro _ ⟨U, rfl⟩
    exact partialChainEnergy_nonneg hV a ha S j U.1
  obtain ⟨hf, hl, -, -⟩ := hV F a S ha
  induction j with
  | zero =>
    have : ∀ U : {U : F.FieldChain // U 0 = V}, partialChainEnergy a S 0 U.1 = minimalAction a S 0 V := by
      intro U
      simp [partialChainEnergy, minimalAction, U.2]
    simp_rw [this]
    rw [ciInf_const]
  | succ j ih =>
    have hbW : BddBelow (Set.range fun W : F.GaugeField j =>
        minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨W, rfl⟩
      exact add_nonneg (hl j W) (mul_nonneg ha (Finset.sum_nonneg fun c _ => hf _ _ _ _))
    apply le_antisymm
    · apply le_ciInf
      rintro ⟨U, hU⟩
      have h1 : minimalAction a S (j + 1) V ≤
          minimalAction a S j (U j) + a * ∑ c ∈ innerBonds S (j + 1), blockFit (U j) V c :=
        ciInf_le hbW (U j)
      have h2 : minimalAction a S j (U j) ≤ partialChainEnergy a S j U := by
        rw [ih (U j)]
        exact ciInf_le (hbdd j (U j)) ⟨U, rfl⟩
      have h3 : partialChainEnergy a S (j + 1) U =
          partialChainEnergy a S j U + a * ∑ c ∈ innerBonds S (j + 1), blockFit (U j) V c := by
        rw [partialChainEnergy_succ, hU]
      exact h1.trans ((add_le_add_left h2 _).trans_eq h3.symm)
    · show _ ≤ ⨅ W : F.GaugeField j,
        (minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c)
      apply le_ciInf
      intro W
      rw [ih W, ← sub_le_iff_le_add]
      apply le_ciInf
      rintro ⟨U, hU⟩
      rw [sub_le_iff_le_add]
      set U' : F.FieldChain := Function.update U (j + 1) V with hU'
      have e1 : U' (j + 1) = V := by simp [hU']
      have e2 : ∀ i, i ≤ j → U' i = U i := by
        intro i hi
        rw [hU', Function.update_of_ne (by omega)]
      have e3 : partialChainEnergy a S (j + 1) U' =
          partialChainEnergy a S j U + a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c := by
        have e5 : ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1), blockFit (U' i) (U' (i + 1)) c =
            ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1), blockFit (U i) (U (i + 1)) c := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have := Finset.mem_range.1 hi
          rw [e2 i (by omega), e2 (i + 1) (by omega)]
        have e4 : partialChainEnergy a S j U' = partialChainEnergy a S j U := by
          unfold partialChainEnergy
          rw [e2 0 (Nat.zero_le j), e5]
        rw [partialChainEnergy_succ, e4, e1, e2 j le_rfl, hU]
      have h4 : (⨅ U : {U : F.FieldChain // U (j + 1) = V}, partialChainEnergy a S (j + 1) U.1) ≤
          partialChainEnergy a S (j + 1) U' :=
        ciInf_le (hbdd (j + 1) V) ⟨U', e1⟩
      exact h4.trans_eq e3
theorem wholeCellCost_eq_minimalAction (hV : minimalChainExistenceStatement) :
    WholeCellCostEqualsMinimalAction := by
  intro F a S hL ha
  have hc : ∀ j, j ≤ F.top → ∀ V : F.GaugeField j,
      cutEffectiveAction a j (cutBelow j S) V = minimalAction a S j V := by
    intro j hj V
    rw [minimalAction_eq_iInf hV a ha S j V]
    unfold cutEffectiveAction
    exact iInf_congr fun U => cutChainEnergy_eq hL a S hj U.1
  refine ⟨fun j _ => cutBelow_eq_sitesOfCells S j, hc, fun W V => ?_⟩
  have hs : sitesOfCells S F.top = S := by
    ext y
    exact mem_sitesOfCells_top
  unfold plainBlockEnergy blockEnergy
  rw [hc F.depth (Nat.le_succ _) W]
  congr 2
  unfold innerBonds cutBonds
  rw [show sitesOfCells S (F.depth + 1) = S from hs]
end WholeCellCost
end YangMills.Construction.LumpContours
end
