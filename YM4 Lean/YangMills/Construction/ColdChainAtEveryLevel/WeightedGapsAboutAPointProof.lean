import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesOfEveryLevelProof
import YangMills.Construction.ColdChainAtEveryLevel.GapsOfTheLevelsNearACellProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace WeightedLevelGaps
open BlockAverages BlockLines BlockWeights LatticePaths LatticeFractionalIntegration
variable {F : BlockFrame}
theorem chartGap_zero (R : F.FieldChain) (U : ChainChart F) (x : F.Site 0) (i : Fin 4) :
    chartGap R U 0 x i = expUnit (U.fine x i) := by apply _root_.YangMills.Construction.LevelGaps.chartGap_zero <;> assumption
theorem le_of_pow_four_le_pow_four {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 4 ≤ b ^ 4) : a ≤ b :=
  le_of_not_gt fun hlt => absurd h (not_le.2 (pow_lt_pow_left₀ hlt hb (by norm_num)))
theorem le_pow_four_of_sqrt_sqrt_le {x y : ℝ} (hy : 0 ≤ y) (h : Real.sqrt (Real.sqrt x) ≤ y) : x ≤ y ^ 4 := by
  have h1 := (Real.sqrt_le_iff.1 h).2
  have h2 := (Real.sqrt_le_iff.1 h1).2
  refine h2.trans (le_of_eq ?_)
  ring
theorem sqrt_sqrt_le_of_le_pow_four {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 4) : Real.sqrt (Real.sqrt x) ≤ y := by apply _root_.YangMills.Construction.BlockAverages.LevelCoordinates.sqrt_sqrt_le_of_le_pow_four <;> assumption
theorem localSums_le (hodd : Odd F.blockSide) {θ del : ℝ} (hθ : 0 ≤ θ) (S : Finset F.Cell) (R : F.FieldChain)
    (U : ChainChart F) (p : F.Site 0) {β : ℝ} (hβ : 0 ≤ β)
    (hN : ∀ y0 : F.Cell, weightedNorm S R U (decayWeights F del θ p y0) ≤ β) :
    (∑ b ∈ innerBonds (cellsNearPoint S p) 0, (shiftedWeight F θ p 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤ (25 * β) ^ 4) ∧
      (∀ j, j + 1 < F.top → ∑ c ∈ innerBonds (cellsNearPoint S p) (j + 1),
        (shiftedWeight F θ p (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤ (25 * β) ^ 2) ∧
      ∀ b ∈ innerBonds S 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ≤ β := by
  classical
  have hL := hodd.pos
  have hsub : cellsNearPoint S p ⊆ S := Finset.filter_subset _ _
  have hcard : ((cellsNearPoint S p).card : ℝ) ≤ 625 := by exact_mod_cast card_cellsNearPoint_le S p
  have hparts : ∀ z ∈ S, _ := fun z hz => localNorm_parts_le S R U (decayWeights F del θ p z) z hβ
    ((localNorm_le_weightedNorm S R U _ hz).trans (hN z))
  have hw : ∀ (z : F.Cell) {j : ℕ} (b : F.Site j × Fin 4), b ∈ bondsOver S {z} j →
      shiftedWeight F θ p j b.1 ≤ decayWeights F del θ p z j b.1 := by
    intro z j b hb
    have hc : enclosingCell b.1 = z := Finset.mem_singleton.1 (Finset.mem_filter.1 hb).2
    have := shiftedWeight_le_exp_mul_decayWeights hL hθ del p z j b.1
    rw [hc, cellSupDist_self] at this
    simpa using this
  have hw0 : ∀ {j : ℕ} (b : F.Site j × Fin 4), 0 ≤ shiftedWeight F θ p j b.1 := fun b =>
    zero_le_one.trans (one_le_shiftedWeight hL hθ p _ b.1)
  refine ⟨?_, ?_, ?_⟩
  · refine (sum_innerBonds_le_sum_cells hodd hsub 0 _ fun _ => by positivity).trans ?_
    have h1 : ∀ z ∈ cellsNearPoint S p, ∑ b ∈ bondsOver S {z} 0,
        (shiftedWeight F θ p 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤ β ^ 4 := by
      intro z hz
      have hzS := hsub hz
      refine le_trans ?_ (hparts z hzS).1
      refine le_trans (Finset.sum_le_sum fun b hb => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (bondsOver_singleton_subset hzS 0)
          fun _ _ _ => Even.pow_nonneg (by decide) _)
      exact pow_le_pow_left₀ (mul_nonneg (hw0 b) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hw z b hb) (norm_nonneg _)) 4
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hb4 : 0 ≤ β ^ 4 := by positivity
    nlinarith
  · intro j hj
    refine (sum_innerBonds_le_sum_cells hodd hsub (j + 1) _ fun _ => by positivity).trans ?_
    have h1 : ∀ z ∈ cellsNearPoint S p, ∑ c ∈ bondsOver S {z} (j + 1),
        (shiftedWeight F θ p (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤ β ^ 2 := by
      intro z hz
      have hzS := hsub hz
      refine le_trans ?_ ((hparts z hzS).2.2 j hj)
      refine le_trans (Finset.sum_le_sum fun b hb => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (bondsOver_singleton_subset hzS (j + 1))
          fun _ _ _ => Even.pow_nonneg (by decide) _)
      exact pow_le_pow_left₀ (mul_nonneg (hw0 b) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hw z b hb) (norm_nonneg _)) 2
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hb2 : 0 ≤ β ^ 2 := by positivity
    nlinarith
  · intro b hb
    have hz : enclosingCell b.1 ∈ S := by
      simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hb
      exact enclosingCell_mem hodd hb.1.1
    have hb' : b ∈ bondsOver S {enclosingCell b.1} 0 := Finset.mem_filter.2 ⟨hb, by simp⟩
    have h1 := Finset.single_le_sum (f := fun b' : F.Site 0 × Fin 4 =>
      (decayWeights F del θ p (enclosingCell b.1) 0 b'.1 * ‖U.fine b'.1 b'.2‖) ^ 4)
      (fun _ _ => Even.pow_nonneg (by decide) _) (bondsOver_singleton_subset hz 0 hb')
    have h2 := h1.trans (hparts _ hz).1
    have h4 := one_le_decayWeights_self hL hθ del p 0 b.1
    have h5 : (0 : ℝ) ≤ ‖U.fine b.1 b.2‖ := norm_nonneg _
    have h3 : decayWeights F del θ p (enclosingCell b.1) 0 b.1 * ‖U.fine b.1 b.2‖ ≤ β :=
      le_of_pow_four_le_pow_four (mul_nonneg (by linarith) h5) hβ h2
    calc ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ = ‖U.fine b.1 b.2‖ := rfl
      _ ≤ _ := le_mul_of_one_le_left h5 h4
      _ ≤ β := h3
theorem norm_levelCoordinate_zero (R : F.FieldChain) (U : ChainChart F) {x : F.Site 0} {i : Fin 4}
    (h : ‖(U.fine x i : ℍ[ℝ])‖ ≤ 1 / 8) : ‖levelCoordinate R U 0 x i‖ = ‖(U.fine x i : ℍ[ℝ])‖ := by
  unfold levelCoordinate
  rw [chartGap_zero, unitQuaternionLog_expUnit h]
theorem stepError_le {Ω Cs Db K t tA x2 x3 μ mis mm : ℝ} (hK : K = Cs * (1 + Db)) (hCs : 0 ≤ Cs)
    (hDb : 0 ≤ Db) (hΩt : Ω * tA = t) (htA0 : 0 ≤ tA) (htAt : tA ≤ t) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3)
    (hμ0 : 0 ≤ μ) (hmu : μ ≤ mm) (hmis : mis ≤ Db * x3) :
    Ω * (Cs * (tA ^ 2 + (x2 + μ + mis) * tA)) ≤ K * (t ^ 2 + (x2 + mm + x3) * t) := by apply _root_.YangMills.Construction.BlockAverages.ColdBelowTop.stepBound_weighted_le <;> assumption
theorem boundedOnAdjacentBlocks_div_weight (hL2 : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (p : F.Site 0)
    (R : F.FieldChain) (U : ChainChart F) {j : ℕ} (hjn : j < F.top) (c' : F.Site (j + 1) × Fin 4) {t : ℝ}
    (hBB : BoundedOnAdjacentBlocks (fun x i => shiftedWeight F θ p j x * ‖levelCoordinate R U j x i‖) c' t) :
    BoundedOnAdjacentBlocks (fun x i => ‖levelCoordinate R U j x i‖) c'
      (t / shiftedWeight F θ p (j + 1) c'.1) := by apply _root_.YangMills.Construction.BlockAverages.ColdBelowTop.boundedOnAdjacentBlocks_div_shiftedWeight <;> assumption
theorem shiftedWeight_mul_norm_parallelAverage_le (hodd : Odd F.blockSide) (hL2 : 2 ≤ F.blockSide) {θ : ℝ}
    (hθ : 0 ≤ θ) (p : F.Site 0) {j : ℕ} (hjn : j < F.top) (Rj : F.GaugeField j) (f : F.Site j → Fin 4 → ℍ[ℝ])
    (c' : F.Site (j + 1) × Fin 4) :
    shiftedWeight F θ p (j + 1) c'.1 * ‖parallelAverage Rj f c'‖ ≤
      lineBlockAverage (fun x i => shiftedWeight F θ p j x * ‖f x i‖) c' := by apply _root_.YangMills.Construction.BlockAverages.ColdBelowTop.shiftedWeight_mul_norm_parallelAverage_le <;> assumption
theorem norm_le_of_norm_sub_sub_le {A M Q : ℍ[ℝ]} {e : ℝ} (h : ‖A - M - Q‖ ≤ e) : ‖A‖ ≤ ‖M‖ + ‖Q‖ + e := by
  have e1 : A = (A - M - Q) + M + Q := by abel
  rw [e1]
  refine (norm_add_le _ _).trans ?_
  have := norm_add_le (A - M - Q) M
  linarith
end WeightedLevelGaps
namespace BlockAverages
open WeightedLevelGaps BlockLines BlockWeights
theorem weightedLevelGapsStatement_holds (hOne : levelCoordinateStepStatement)
    (hRec : UniformQuarticBoundAcrossLevels) (hB : referenceBoundsStatement) :
    weightedLevelGapsStatement := by
  obtain ⟨L0, hOne⟩ := hOne
  obtain ⟨Db, cb, L1, hDb, hcb, hBd⟩ := hB
  intro θ del hθ hθ8 hdel hdel8
  refine ⟨max (max L0 L1) 5, fun L hL hge => ?_⟩
  have hL0 : L0 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hge)
  have hL1 : L1 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hge)
  have hL5 : 5 ≤ L := (le_max_right _ _).trans hge
  obtain ⟨Cs, cs, hCs, hcs, hStep⟩ := hOne L hL hL0
  have hK0 : 0 < Cs * (1 + Db) := by positivity
  obtain ⟨c1, hc1, hRecL⟩ := hRec L 625 (Cs * (1 + Db)) cs hL hL5 hK0.le hcs
  have hmin0 : 0 < min (min c1 cs) (min cb (1 / 8)) := lt_min (lt_min hc1 hcs) (lt_min hcb (by norm_num))
  obtain ⟨c, hc0, hcm⟩ : ∃ c : ℝ, 0 < c ∧ 25 * c ≤ min (min c1 cs) (min cb (1 / 8)) :=
    ⟨min (min c1 cs) (min cb (1 / 8)) / 25, by positivity, by linarith⟩
  have hcc1 : 25 * c ≤ c1 := hcm.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hccs : 25 * c ≤ cs := hcm.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hccb : 25 * c ≤ cb := hcm.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc8 : 25 * c ≤ 1 / 8 := hcm.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c, 100, hc0, by norm_num, ?_⟩
  intro F m S hFL hamb hm hreg s V hs0 hsc hcold U p β hβ0 hβc hN j hj
  subst hFL
  have hodd : Odd F.blockSide := hL
  have hLpos : 0 < F.blockSide := hodd.pos
  have hL2 : 2 ≤ F.blockSide := by omega
  have hDS : cellsNearPoint S p ⊆ S := Finset.filter_subset _ _
  obtain ⟨-, -, c3, -, -, -⟩ := hBd F m S hodd hL1 hamb hm hreg s V hs0 (by linarith) hcold
  obtain ⟨i1, i2, i3⟩ := localSums_le hodd hθ.le S (referenceFieldChain S V) U p hβ0 hN
  have hΩ1 : ∀ {j : ℕ} (x : F.Site j), 1 ≤ shiftedWeight F θ p j x :=
    fun x => one_le_shiftedWeight hLpos hθ.le p _ x
  have hΩ0 : ∀ {j : ℕ} (x : F.Site j), 0 ≤ shiftedWeight F θ p j x := fun x => zero_le_one.trans (hΩ1 x)
  have hB0 : 0 ≤ 25 * β := by positivity
  have hfin := hRecL F (cellsNearPoint S p)
    (fun j x i => shiftedWeight F θ p j x * ‖levelCoordinate (referenceFieldChain S V) U j x i‖)
    (fun j y i => shiftedWeight F θ p (j + 1) y * ‖U.coarse j y i‖) s (25 * β) rfl
    (card_cellsNearPoint_le S p) hs0.le
    (by linarith) hB0 (by linarith)
    (fun j x i => mul_nonneg (hΩ0 x) (norm_nonneg _)) (fun j x i => mul_nonneg (hΩ0 x) (norm_nonneg _))
    ?_ ?_ ?_ j hj
  · have := le_pow_four_of_sqrt_sqrt_le (by positivity) hfin
    refine this.trans (le_of_eq ?_)
    ring
  · refine sqrt_sqrt_le_of_le_pow_four hB0 (le_trans (le_of_eq (Finset.sum_congr rfl fun b hb => ?_)) i1)
    have hu := i3 b (innerBonds_mono hDS 0 hb)
    have e : ‖levelCoordinate (referenceFieldChain S V) U 0 b.1 b.2‖ = ‖U.fine b.1 b.2‖ :=
      norm_levelCoordinate_zero _ U (by linarith)
    simp only [e]
  · intro j hj
    exact Real.sqrt_le_iff.2 ⟨hB0, i2 j hj⟩
  · intro j hj c' hc' t ht0 htc hmc hBB
    have hcS : c' ∈ innerBonds S (j + 1) := innerBonds_mono hDS _ hc'
    have hjn : j < F.top := by omega
    have hΩpos : 0 < shiftedWeight F θ p (j + 1) c'.1 := lt_of_lt_of_le one_pos (hΩ1 _)
    have htA0 : 0 ≤ t / shiftedWeight F θ p (j + 1) c'.1 := by positivity
    have htAt : t / shiftedWeight F θ p (j + 1) c'.1 ≤ t := div_le_self ht0 (hΩ1 _)
    have hΩt : shiftedWeight F θ p (j + 1) c'.1 * (t / shiftedWeight F θ p (j + 1) c'.1) = t := by
      field_simp
    have hBA := boundedOnAdjacentBlocks_div_weight hL2 hθ.le p (referenceFieldChain S V) U hjn c' hBB
    have hmu : ‖(U.coarse j c'.1 c'.2 : ℍ[ℝ])‖ ≤ shiftedWeight F θ p (j + 1) c'.1 * ‖U.coarse j c'.1 c'.2‖ :=
      le_mul_of_one_le_left (norm_nonneg _) (hΩ1 _)
    have hone := hStep F m S rfl hamb hm hreg s V hs0 (by linarith) hcold U j c' hj hcS _ htA0 (by linarith)
      (hmu.trans hmc) hBA
    have hlog := norm_le_of_norm_sub_sub_le hone
    have hmis : ‖((referenceDefect (referenceFieldChain S V) j c' : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        Db * (s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 3) := by
      have := c3 j hj c' hcS
      refine this.trans (le_of_eq ?_)
      simp only [levelScale]
      ring
    have hterm := stepError_le (Ω := shiftedWeight F θ p (j + 1) c'.1) rfl hCs.le hDb.le hΩt htA0 htAt
      (x2 := s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2)
      (x3 := s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 3)
      (by positivity) (by positivity) (norm_nonneg _) hmu hmis
    have hQ' := shiftedWeight_mul_norm_parallelAverage_le hodd hL2 hθ.le p hjn (referenceFieldChain S V j)
      (levelCoordinate (referenceFieldChain S V) U j) c'
    have hmul := mul_le_mul_of_nonneg_left hlog hΩpos.le
    calc _ ≤ _ := hmul
      _ = shiftedWeight F θ p (j + 1) c'.1 * ‖(U.coarse j c'.1 c'.2 : ℍ[ℝ])‖ +
            shiftedWeight F θ p (j + 1) c'.1 *
            ‖parallelAverage (referenceFieldChain S V j) (levelCoordinate (referenceFieldChain S V) U j) c'‖ +
            shiftedWeight F θ p (j + 1) c'.1 * _ := by ring
      _ ≤ _ := add_le_add (add_le_add le_rfl hQ') hterm
end BlockAverages
end YangMills.Construction
end
