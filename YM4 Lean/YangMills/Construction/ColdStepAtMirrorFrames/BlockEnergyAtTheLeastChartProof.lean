import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfTheSharesProof
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def CellEnergyShareAtMinimizingChart : Prop :=
  ∀ (F : BlockFrame) (a ρ : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
    0 ≤ a → Odd F.blockSide → (∀ i, 2 ≤ F.extent i) → IsMinimizingChart a (finiteCells F) V ρ w →
    (∀ X, IsMinimalChain a (finiteCells F) V X →
      ∀ Y, cellShare a (finiteCells F) Y X = minimalCellShare a (finiteCells F) Y V) →
    ∀ Y, cellEnergyShare a Y w V = minimalCellShare a (finiteCells F) Y V
end ColdStepAtMirrorFrames
end YangMills.Construction
end

noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace MinimizingChart
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem period_depth (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by
  simp [BlockFrame.period, BlockFrame.top]
theorem round_ediv_round_ediv (c : ℤ) (A M : ℤ) (hA : Odd A) (hM : Odd M) (hA0 : 0 < A) (hM0 : 0 < M) :
    ((c + (A - 1) / 2) / A + (M - 1) / 2) / M = (c + (A * M - 1) / 2) / (A * M) := by
  obtain ⟨p, rfl⟩ := hA
  obtain ⟨q, rfl⟩ := hM
  have e1 : (2 * p + 1 - 1) / 2 = p := by omega
  have e2 : (2 * q + 1 - 1) / 2 = q := by omega
  have e3 : ((2 * p + 1) * (2 * q + 1) - 1) / 2 = p + (2 * p + 1) * q := by
    have : (2 * p + 1) * (2 * q + 1) - 1 = 2 * (p + (2 * p + 1) * q) := by ring
    rw [this]
    omega
  rw [e1, e2, e3, ← Int.ediv_ediv_of_nonneg hA0.le]
  congr 1
  rw [← add_assoc, Int.add_mul_ediv_left _ _ hA0.ne']
theorem enclosingCell_ancestorSite (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j ≤ F.depth) (x : F.Site j) :
    enclosingCell (ancestorSite (F := F) F.depth x) = enclosingCell x := by
  funext i
  have hL : 0 < F.blockSide := hodd.pos
  have hLz : (0 : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast hL
  have hn : F.top - F.depth = 1 := by simp [BlockFrame.top]
  have hnj : F.top - j = (F.depth - j) + 1 := by
    simp only [BlockFrame.top]
    omega
  obtain ⟨u, hu⟩ : ∃ u : ℤ, u = (siteCoords x i + ((F.blockSide : ℤ) ^ (F.depth - j) - 1) / 2) /
      (F.blockSide : ℤ) ^ (F.depth - j) := ⟨_, rfl⟩
  have hcoord : siteCoords (ancestorSite (F := F) F.depth x) i = u % (F.period F.depth i : ℤ) := by
    unfold siteCoords ancestorSite siteOfCoords
    rw [ZMod.coe_intCast, hu]
  have hoddL : Odd (F.blockSide : ℤ) := by exact_mod_cast hodd
  have hP : (F.period F.depth i : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) := by
    rw [period_depth]
    push_cast
    ring
  simp only [enclosingCell, siteOfCoords, hn, pow_one]
  rw [hcoord, hnj]
  have hmod := Int.emod_add_mul_ediv u (F.period F.depth i : ℤ)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = u / (F.period F.depth i : ℤ) := ⟨_, rfl⟩
  rw [← hQ] at hmod
  have e1 : (u % (F.period F.depth i : ℤ) + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ) =
      (u + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ) - (F.extent i : ℤ) * Q := by
    have : u + ((F.blockSide : ℤ) - 1) / 2 = (u % (F.period F.depth i : ℤ) + ((F.blockSide : ℤ) - 1) / 2) +
        (F.blockSide : ℤ) * ((F.extent i : ℤ) * Q) := by
      rw [hP] at hmod ⊢
      nlinarith
    rw [this, Int.add_mul_ediv_left _ _ hLz.ne']
    ring
  rw [e1, hu, round_ediv_round_ediv _ _ _ (hoddL.pow) hoddL (by positivity) hLz]
  have hz : (((F.extent i : ℤ) : ZMod (F.period F.top i))) = 0 := by
    have h1 : ((F.period F.top i : ℕ) : ZMod (F.period F.top i)) = 0 := ZMod.natCast_self _
    have h2 : (F.period F.top i : ℤ) = (F.extent i : ℤ) := by rw [period_top]
    rw [← h2]
    exact_mod_cast h1
  rw [Int.cast_sub, Int.cast_mul, hz, zero_mul, sub_zero, pow_succ]
theorem enclosingCell_top (hs : ∀ i, 0 < F.extent i) (x : F.Site F.top) : (enclosingCell x : F.Cell) = x := by
  funext i
  have hne : NeZero (F.period F.top i) := ⟨by rw [period_top]; exact (hs i).ne'⟩
  simp only [enclosingCell, siteOfCoords, siteCoords, Nat.sub_self, pow_zero, sub_self, Int.zero_ediv,
    add_zero, Int.ediv_one]
  exact ZMod.intCast_zmod_cast (x i)
theorem unitStep_top_ne_zero (hs : ∀ i, 2 ≤ F.extent i) (i : Fin 4) : (unitStep F.top i : F.Site F.top) ≠ 0 := by apply _root_.YangMills.Construction.GaugeFixing.unitStep_top_ne_zero <;> assumption
theorem exists_minimizingChain_below (hLV : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset F.Cell) (j : ℕ) : ∀ W : F.GaugeField j, ∃ X : F.FieldChain, X j = W ∧
      wilsonAction S (X 0) + a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1), blockFit (X i) (X (i + 1)) c =
        minimalAction a S j W ∧
      ∀ X' : F.FieldChain, X' j = W → minimalAction a S j W ≤
        wilsonAction S (X' 0) + a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1),
          blockFit (X' i) (X' (i + 1)) c := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.exists_minimizing_chain_below <;> assumption
end MinimizingChart
open MinimizingChart in
theorem cellEnergyShareAtMinimizingChart_proof (hcover : BlocksCoverLowerLevel)
    (hLV : minimalChainExistenceStatement) : CellEnergyShareAtMinimizingChart := by
  classical
  intro F a ρ w V ha hodd hs hw hshare Y
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    have := hs i
    omega
  have hcov := hcover F hodd hpos
  obtain ⟨W, hWd⟩ : ∃ W, W = chartedField w V := ⟨_, rfl⟩
  obtain ⟨X₀, hX₀, htot, hmn⟩ := exists_minimizingChain_below hLV a ha (finiteCells F) F.depth W
  have hex : ∃ X, IsMinimizingChainBelow a (finiteCells F) W X :=
    ⟨X₀, hX₀, fun X' h => by
      have := hmn X' h
      unfold chainActionBelow
      rw [htot]
      exact this⟩
  obtain ⟨X, hXd⟩ : ∃ X, X = hex.choose := ⟨_, rfl⟩
  have hXm : IsMinimizingChainBelow a (finiteCells F) W X := by
    rw [hXd]
    exact hex.choose_spec
  have hXv : chainActionBelow a (finiteCells F) X = minimalAction a (finiteCells F) F.depth W := by
    have h1 := hXm.2 X₀ hX₀
    have h2 := hmn X hXm.1
    unfold chainActionBelow at h1 ⊢
    rw [htot] at h1
    exact le_antisymm h1 h2
  have hshareBelow : ∀ y, minimalSiteShare a y W = chainSiteShare a (finiteCells F) y X := by
    intro y
    unfold minimalSiteShare
    rw [dif_pos hex, hXd]
  obtain ⟨Z, hZd⟩ : ∃ Z : F.FieldChain, Z = Function.update X F.top V := ⟨_, rfl⟩
  have hZn : Z F.top = V := by
    rw [hZd]
    simp
  have hZlow : ∀ j, j ≤ F.depth → Z j = X j := by
    intro j hj
    rw [hZd, Function.update_of_ne]
    simp only [BlockFrame.top]
    omega
  have hZt : Z F.depth = W := by
    rw [hZlow _ le_rfl]
    exact hXm.1
  have hsplit : ∀ X' : F.FieldChain, chainAction a (finiteCells F) X' = chainActionBelow a (finiteCells F) X' +
      a * ∑ c ∈ innerBonds (finiteCells F) F.top, blockFit (X' F.depth) (X' F.top) c := by
    intro X'
    unfold chainAction chainActionBelow
    rw [Finset.sum_range_succ, mul_add, ← add_assoc]
  have hZsum : ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds (finiteCells F) (j + 1), blockFit (Z j) (Z (j + 1)) c =
      ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds (finiteCells F) (j + 1), blockFit (X j) (X (j + 1)) c := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < F.depth := Finset.mem_range.mp hj
    rw [hZlow j hj'.le, hZlow (j + 1) hj']
  have hZmin : IsMinimalChain a (finiteCells F) V Z := by
    refine ⟨hZn, fun X' hX' => ?_⟩
    rw [hsplit Z, hsplit X', hZn, hZt, hX']
    have h1 : chainActionBelow a (finiteCells F) Z = chainActionBelow a (finiteCells F) X := by
      unfold chainActionBelow
      rw [hZlow 0 (Nat.zero_le _), hZsum]
    obtain ⟨_, _, _, hm⟩ := exists_minimizingChain_below hLV a ha (finiteCells F) F.depth (X' F.depth)
    have h2 := hm X' rfl
    have h3 := hw.2.2 (X' F.depth)
    unfold blockEnergy at h3
    rw [← hWd] at h3
    rw [h1, hXv]
    unfold chainActionBelow
    linarith
  rw [← hshare Z hZmin Y]
  have hfil : ∀ (u : F.Site F.depth) (c : ℝ),
      ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
      (if u = y then c else 0) = if enclosingCell u = Y then c else 0 := by
    intro u c
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_filter, hcov u, true_and]
  have hA : ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
      chainSiteShare a (finiteCells F) y X =
      (∑ p ∈ innerPlaquettes (finiteCells F) 0,
        (∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0) *
        (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re)) +
      a * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds (finiteCells F) (j + 1),
        ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
          (if enclosingCell (c.1 + unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) *
        blockFit (X j) (X (j + 1)) c := by
    unfold chainSiteShare
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [hfil, enclosingCell_ancestorSite hodd hpos (Nat.zero_le _)]
    · congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < F.depth := Finset.mem_range.mp hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_add_distrib, hfil, hfil, enclosingCell_ancestorSite hodd hpos hj',
        enclosingCell_ancestorSite hodd hpos hj']
  have hB : a / 2 * ∑ c ∈ (innerBonds (finiteCells F) F.top).filter
      (fun c => c.1 = Y ∨ c.1 + unitStep F.top c.2 = Y),
      blockFit W V c = a * ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
        ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
          (if enclosingCell (c.1 + unitStep (F.depth + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) *
            blockFit W V c := by
    rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    have hc1 : (enclosingCell c.1 : F.Cell) = c.1 := enclosingCell_top hpos _
    have hc2 : (enclosingCell (c.1 + unitStep (F.depth + 1) c.2) : F.Cell) = c.1 + unitStep F.top c.2 :=
      enclosingCell_top hpos _
    rw [hc1, hc2]
    have hne : c.1 ≠ c.1 + unitStep F.top c.2 := by
      intro e
      apply unitStep_top_ne_zero hs c.2
      have h0 : c.1 + unitStep F.top c.2 = c.1 + 0 := by rw [add_zero]; exact e.symm
      exact add_left_cancel h0
    by_cases h1 : c.1 = Y
    · have h2 : c.1 + unitStep F.top c.2 ≠ Y := fun e => hne (h1.trans e.symm)
      rw [if_pos (Or.inl h1), if_pos h1, if_neg h2]
      ring
    · by_cases h2 : c.1 + unitStep F.top c.2 = Y
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]
        ring
      · rw [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg h1, if_neg h2]
        ring
  unfold cellEnergyShare cellShare
  rw [← hWd]
  simp only [hshareBelow]
  have hZn' : Z (F.depth + 1) = V := hZn
  have hZs2 : ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds (finiteCells F) (j + 1),
      ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
        (if enclosingCell (c.1 + unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) *
          blockFit (Z j) (Z (j + 1)) c =
      ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds (finiteCells F) (j + 1),
      ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
        (if enclosingCell (c.1 + unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) *
          blockFit (X j) (X (j + 1)) c := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < F.depth := Finset.mem_range.mp hj
    rw [hZlow j hj'.le, hZlow (j + 1) hj']
  rw [hA, hB, Finset.sum_range_succ, hZlow 0 (Nat.zero_le _), mul_add, ← add_assoc, hZs2, hZt, hZn']
end ColdStepAtMirrorFrames
end YangMills.Construction
end
