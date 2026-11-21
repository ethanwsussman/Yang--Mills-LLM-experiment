import YangMills.Construction.ColdChainAtEveryLevel.LeastValuesOfAChain
import YangMills.Construction.ColdStepAtMirrorFrames.BlocksCoverTheLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfTheShares
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace CellShares
theorem period_ge_two (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (j : ℕ) (i : Fin 4) :
    2 ≤ F.period j i := by
  unfold BlockFrame.period
  have : 1 ≤ F.blockSide ^ (F.top - j) := Nat.one_le_pow _ _ hL
  nlinarith [hs i]
theorem zmod_one_ne_zero {N : ℕ} (h : 2 ≤ N) : (1 : ZMod N) ≠ 0 := by
  have : Fact (1 < N) := ⟨h⟩
  exact one_ne_zero
theorem unitStep_apply_self {j : ℕ} (i : Fin 4) : (unitStep j i : F.Site j) i = 1 := by
  simp [unitStep, siteOfCoords]
theorem unitStep_apply_of_ne {j : ℕ} {i l : Fin 4} (h : l ≠ i) : (unitStep j i : F.Site j) l = 0 := by
  simp [unitStep, siteOfCoords, Pi.single_eq_of_ne h]
theorem unitStep_ne_zero (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (j : ℕ) (i : Fin 4) :
    (unitStep j i : F.Site j) ≠ 0 := by
  intro h
  have := congrFun h i
  rw [unitStep_apply_self] at this
  exact zmod_one_ne_zero (period_ge_two hL hs j i) this
theorem card_plaquetteCorners (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ}
    (x : F.Site j) {μ ν : Fin 4} (h : μ ≠ ν) : (plaquetteCorners (x, μ, ν)).card = 4 := by
  have hu := unitStep_ne_zero hL hs j μ
  have hv := unitStep_ne_zero hL hs j ν
  have h1 := zmod_one_ne_zero (period_ge_two hL hs j μ)
  have huv : (unitStep j μ : F.Site j) ≠ unitStep j ν := by
    intro e
    have := congrFun e μ
    rw [unitStep_apply_self, unitStep_apply_of_ne h] at this
    exact h1 this
  have hsum : (unitStep j μ : F.Site j) + unitStep j ν ≠ 0 := by
    intro e
    have := congrFun e μ
    simp only [Pi.add_apply, Pi.zero_apply] at this
    rw [unitStep_apply_self, unitStep_apply_of_ne h, add_zero] at this
    exact h1 this
  unfold plaquetteCorners
  simp only
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    intro e
    apply hu
    have : x + unitStep j ν + unitStep j μ = x + unitStep j ν + 0 := by
      rw [add_zero]
      conv_rhs => rw [e]
      abel
    exact add_left_cancel this
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro e
      exact huv (add_left_cancel e)
    · intro e
      apply hv
      have : x + unitStep j μ + unitStep j ν = x + unitStep j μ + 0 := by
        rw [add_zero]
        exact e.symm
      exact add_left_cancel this
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    · intro e
      apply hu
      have : x + unitStep j μ = x + 0 := by rw [add_zero]; exact e.symm
      exact add_left_cancel this
    · intro e
      apply hv
      have : x + unitStep j ν = x + 0 := by rw [add_zero]; exact e.symm
      exact add_left_cancel this
    · intro e
      apply hsum
      have : x + (unitStep j μ + unitStep j ν) = x + 0 := by
        rw [add_zero, ← add_assoc]
        exact e.symm
      exact add_left_cancel this
theorem mem_finiteCells (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by
  have hper : ∀ i, F.period F.top i = F.extent i := by
    intro i
    simp [BlockFrame.period]
  have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    rw [hper]
    have := hs i
    omega⟩
  have hfin : Finite F.Cell := by
    have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => by
      have := hne i
      exact inferInstance
    exact Pi.finite
  unfold finiteCells
  rw [dif_pos hfin]
  exact @Finset.mem_univ _ (Fintype.ofFinite _) z
theorem sum_ite_eq_of_mem {β : Type} (T : Finset β) (y : β) (hy : y ∈ T) (c : ℝ)
    [∀ Y, Decidable (y = Y)] :
    ∑ Y ∈ T, (if y = Y then c else 0) = c := by
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
  · intro h
    exact absurd hy h
theorem sum_quarter_weights (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {β : Type}
    (T : Finset β) (g : F.Site 0 → β) (hg : ∀ x, g x ∈ T) (p : F.Site 0 × Fin 4 × Fin 4)
    (hp : p.2.1 ≠ p.2.2) [∀ x Y, Decidable (g x = Y)] :
    ∑ Y ∈ T, ∑ x ∈ plaquetteCorners p, (if g x = Y then (1 / 4 : ℝ) else 0) = 1 := by
  rw [Finset.sum_comm]
  simp only [sum_ite_eq_of_mem T _ (hg _), Finset.sum_const, nsmul_eq_mul]
  obtain ⟨x, μ, ν⟩ := p
  rw [card_plaquetteCorners hL hs x hp]
  norm_num
theorem sum_half_weights {β γ : Type} (T : Finset β) (g : γ → β) (hg : ∀ x, g x ∈ T) (c c' : γ)
    [∀ x Y, Decidable (g x = Y)] :
    ∑ Y ∈ T, ((if g c = Y then (1 / 2 : ℝ) else 0) + (if g c' = Y then (1 / 2 : ℝ) else 0)) = 1 := by
  rw [Finset.sum_add_distrib, sum_ite_eq_of_mem T _ (hg c), sum_ite_eq_of_mem T _ (hg c')]
  norm_num
theorem ne_of_mem_innerPlaquettes {S : Finset F.Cell} {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S 0) : p.2.1 ≠ p.2.2 := by
  unfold innerPlaquettes at hp
  exact ne_of_lt (Finset.mem_filter.mp hp).2.1
theorem exists_minimizing_chain_below (hLV : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset F.Cell) (j : ℕ) : ∀ W : F.GaugeField j, ∃ X : F.FieldChain, X j = W ∧
      wilsonAction S (X 0) + a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1),
          blockFit (X i) (X (i + 1)) c = minimalAction a S j W ∧
      ∀ X' : F.FieldChain, X' j = W → minimalAction a S j W ≤
        wilsonAction S (X' 0) + a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1),
          blockFit (X' i) (X' (i + 1)) c := by
  induction j with
  | zero =>
    intro W
    refine ⟨Function.update (fun _ _ _ => 1 : F.FieldChain) 0 W, by simp, ?_, ?_⟩
    · simp [minimalAction]
    · intro X' h
      subst h
      simp [minimalAction]
  | succ j ih =>
    intro W
    obtain ⟨W', he, hmin⟩ := (hLV F a S ha).2.2.1 j W
    obtain ⟨X, hX, ht, _⟩ := ih W'
    refine ⟨Function.update X (j + 1) W, by simp, ?_, ?_⟩
    · have h0 : Function.update X (j + 1) W 0 = X 0 := by
        simp
      have hj : Function.update X (j + 1) W j = W' := by
        rw [Function.update_of_ne (by omega), hX]
      have hs : ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1),
            blockFit (Function.update X (j + 1) W i) (Function.update X (j + 1) W (i + 1)) c =
          ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1), blockFit (X i) (X (i + 1)) c := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < j := Finset.mem_range.mp hi
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rw [Finset.sum_range_succ, h0, hs, hj, Function.update_self, mul_add, ← add_assoc, ht, ← he]
      rfl
    · intro X' h
      subst h
      obtain ⟨_, _, _, hm⟩ := ih (X' j)
      have h1 := hm X' rfl
      have h2 := hmin (X' j)
      rw [he] at h2
      rw [Finset.sum_range_succ, mul_add, ← add_assoc]
      unfold BlockAverages.blockEnergy at h2
      linarith
end CellShares
open CellShares in
theorem sumCellSharesEqAction_of_cover (hcover : BlocksCoverLowerLevel)
    (hLV : minimalChainExistenceStatement) : sumCellSharesEqAction := by
  classical
  intro F a w V ha hodd hs
  have hL : 0 < F.blockSide := hodd.pos
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    have := hs i
    omega
  have hcov := hcover F hodd hpos
  have hmem := mem_finiteCells (F := F) hs
  constructor
  · obtain ⟨X₀, hX₀, htot⟩ := (hLV F a (finiteCells F) ha).2.2.2 V
    have hex : ∃ X, BlockAverages.IsMinimalChain a (finiteCells F) V X := ⟨X₀, hX₀⟩
    have hsum : ∀ X : F.FieldChain, ∑ Y ∈ finiteCells F, cellShare a (finiteCells F) Y X =
        chainAction a (finiteCells F) X := by
      intro X
      unfold cellShare chainAction
      rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        rw [← Finset.sum_mul,
          sum_quarter_weights hL hs _ _ (fun x => hmem _) p (ne_of_mem_innerPlaquettes hp), one_mul]
      · congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        rw [← Finset.sum_mul,
          sum_half_weights _ (fun x : F.Site (j + 1) => enclosingCell x) (fun x => hmem _), one_mul]
    have hshare : ∀ Y, minimalCellShare a (finiteCells F) Y V =
        cellShare a (finiteCells F) Y hex.choose := by
      intro Y
      unfold minimalCellShare
      rw [dif_pos hex]
    simp only [hshare]
    rw [hsum, ← htot]
    exact le_antisymm (hex.choose_spec.2 X₀ hX₀.1) (hX₀.2 _ hex.choose_spec.1)
  · set W := chartedField w V with hW
    obtain ⟨X₀, hX₀, htot, hmin⟩ := exists_minimizing_chain_below hLV a ha (finiteCells F) F.depth W
    have hex : ∃ X, IsMinimizingChainBelow a (finiteCells F) W X :=
      ⟨X₀, hX₀, fun X' h => by
        have := hmin X' h
        unfold chainActionBelow
        rw [htot]
        exact this⟩
    have hsum : ∀ X : F.FieldChain, ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        chainSiteShare a (finiteCells F) y X = chainActionBelow a (finiteCells F) X := by
      intro X
      unfold chainSiteShare chainActionBelow
      rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        rw [← Finset.sum_mul,
          sum_quarter_weights hL hs _ _ (fun x => hcov _) p (ne_of_mem_innerPlaquettes hp), one_mul]
      · congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        rw [← Finset.sum_mul,
          sum_half_weights _ (fun x : F.Site (j + 1) => ancestorSite F.depth x) (fun x => hcov _),
          one_mul]
    have hbelow : ∑ y ∈ sitesOfCells (finiteCells F) F.depth, minimalSiteShare a y W =
        minimalAction a (finiteCells F) F.depth W := by
      have hshare : ∀ y, minimalSiteShare a y W =
          chainSiteShare a (finiteCells F) y hex.choose := by
        intro y
        unfold minimalSiteShare
        rw [dif_pos hex]
      simp only [hshare]
      rw [hsum, ← htot]
      have h1 := hex.choose_spec.2 X₀ hX₀
      have h2 := hmin hex.choose hex.choose_spec.1
      rw [← htot] at h2
      exact le_antisymm h1 h2
    have hfib : ∑ Y ∈ finiteCells F, ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter
        (fun y => enclosingCell y = Y), minimalSiteShare a y W =
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, minimalSiteShare a y W := by
      exact Finset.sum_fiberwise_of_maps_to (fun y _ => hmem _) _
    have hends : ∑ Y ∈ finiteCells F, ∑ c ∈ (innerBonds (finiteCells F) F.top).filter
        (fun c => c.1 = Y ∨ c.1 + unitStep F.top c.2 = Y), blockFit W V c =
        2 * ∑ c ∈ innerBonds (finiteCells F) F.top, blockFit W V c := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      have hne : c.1 ≠ c.1 + unitStep F.top c.2 := by
        intro e
        apply unitStep_ne_zero hL hs F.top c.2
        have : c.1 + unitStep F.top c.2 = c.1 + 0 := by rw [add_zero]; exact e.symm
        exact add_left_cancel this
      have hsplit : ∀ Y, (if c.1 = Y ∨ c.1 + unitStep F.top c.2 = Y then blockFit W V c else 0) =
          (if c.1 = Y then blockFit W V c else 0) +
            (if c.1 + unitStep F.top c.2 = Y then blockFit W V c else 0) := by
        intro Y
        by_cases h1 : c.1 = Y
        · have h2 : c.1 + unitStep F.top c.2 ≠ Y := fun e => hne (h1.trans e.symm)
          simp [h1]
          intro h3
          exact absurd h3 (by simpa [h1] using h2)
        · simp [h1]
      simp only [hsplit]
      rw [Finset.sum_add_distrib, sum_ite_eq_of_mem _ _ (hmem _), sum_ite_eq_of_mem _ _ (hmem _)]
      ring
    unfold cellEnergyShare
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfib, hbelow, hends]
    unfold chartedEnergy BlockAverages.blockEnergy
    ring
end ColdStepAtMirrorFrames
end YangMills.Construction
end
