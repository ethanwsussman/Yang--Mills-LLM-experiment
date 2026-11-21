import YangMills.Construction.ColdChainAtEveryLevel.CellFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.CellContexts
variable {F : BlockAverages.BlockFrame}
theorem hullBallRadius_pos {L : ℕ} (hL : 0 < L) : 0 < ComplexDifferences.hullBallRadius L := by
  unfold ComplexDifferences.hullBallRadius
  have : (0 : ℝ) < L := by exact_mod_cast hL
  positivity
theorem exists_smallParameter {L : ℕ} (hL : 0 < L) :
    ∃ y₀ : ℝ, 0 < y₀ ∧ ∀ y, 0 < y → y ≤ y₀ → CellNormBounds.SmallParameter L y := by
  have hr := hullBallRadius_pos hL
  set H := ComplexLevels.hullBondCount L with hH
  set Hf := HullBounds.hullFactor L with hHf
  set K := 200000 * (L : ℝ) ^ 2 with hK
  set r := ComplexDifferences.hullBallRadius L with hrd
  have hH0 : 0 ≤ H := ComplexCells.hullBondCount_nonneg L
  have hHf0 : 0 ≤ Hf := ComplexCells.hullFactor_nonneg L
  have hK0 : 0 ≤ K := by positivity
  set A₁ := 48 * (48 * H + 1) / r with hA₁
  set A₂ := 12 * K * (48 * H + 1) with hA₂
  set A₃ := 64 * H with hA₃
  set A₄ := 568 * (8 + 24 * K * (16 * Hf + 5)) * Hf with hA₄
  set A₅ := 568 * (72 + 24 * K * (48 * H + 1)) * Hf with hA₅
  set A₆ := 2 * K with hA₆
  set A₇ := 4608 * H * K with hA₇
  set A₈ := 6 / r with hA₈
  have p₁ : 0 ≤ A₁ := by positivity
  have p₂ : 0 ≤ A₂ := by positivity
  have p₄ : 0 ≤ A₄ := by positivity
  have p₅ : 0 ≤ A₅ := by positivity
  have p₇ : 0 ≤ A₇ := by positivity
  have p₈ : 0 ≤ A₈ := by positivity
  set T := 20000000 + A₁ + A₂ + A₃ + A₄ + A₅ + A₆ + A₇ + A₈ with hT
  have hT0 : 0 < T := by positivity
  refine ⟨1 / T, by positivity, fun y hy hyT => ?_⟩
  have hTy : T * y ≤ 1 := by
    rw [le_div_iff₀ hT0] at hyT
    linarith
  have key : ∀ x, x ≤ T → x * y ≤ 1 := fun x hx => (mul_le_mul_of_nonneg_right hx hy.le).trans hTy
  refine ⟨hy, ?_, ?_, key _ (by linarith), key _ (by linarith), key _ (by linarith), key _ (by linarith), key _ (by linarith),
    key _ (by linarith), ?_⟩
  · have := key 20000000 (by linarith)
    linarith
  · have h1 := key A₁ (by linarith)
    rw [hA₁, div_mul_eq_mul_div, div_le_one hr] at h1
    exact h1
  · have h1 := key A₈ (by linarith)
    rw [hA₈, div_mul_eq_mul_div, div_le_one hr] at h1
    exact h1
theorem norm_ofUnit_sub_one (g : BlockAverages.UnitQuaternion) :
    ‖BlockAverages.ofUnit g - 1‖ = BlockAverages.unitDeviation g := by
  have h1 : ComplexifiedQuaternions.ofQuat (1 : ℍ[ℝ]) = 1 := by
    have := BlockAverages.ofUnit_one
    simpa [BlockAverages.ofUnit] using this
  have e : BlockAverages.ofUnit g - 1 = ComplexifiedQuaternions.ofQuat ((g : ℍ[ℝ]) - 1) := by
    rw [CellSpans.ofQuat_sub, h1]
    rfl
  rw [e, ComplexifiedQuaternions.norm_ofQuat]
  rfl
theorem basePlaquetteHolonomy_eq_plaquetteHolonomy (R : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    ComplexPlaquettes.basePlaquetteHolonomy R p = BlockAverages.plaquetteHolonomy R p := by
  apply ComplexContours.ofUnit_injective
  have h1 : BlockAverages.ofUnit (BlockAverages.plaquetteHolonomy R p) =
      BlockAverages.complexPlaquetteHolonomy (BlockAverages.complexifyField R) p :=
    (BlockAverages.complexPathHolonomy_complexify R p.1 _).symm
  rw [h1, ComplexPlaquettes.complexPlaquetteHolonomy_eq]
  simp only [ComplexPlaquettes.basePlaquetteHolonomy, BlockAverages.ofUnit_mul, BlockAverages.ofUnit_inv,
    BlockAverages.complexifyField]
theorem lpNorm_referenceDefect_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) {D : Finset F.Cell}
    (hD : D.card ≤ 81) {R : F.FieldChain} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ x ∈ ComplexCells.lowerBonds D, ‖BlockAverages.ofUnit (BlockAverages.referenceDefect R x.1 x.2) - 1‖ ≤
      b * ((1 / (F.blockSide : ℝ)) ^ (F.top - (x.1 + 1))) ^ 3) :
    LevelRecursion.finsetLpNorm 2 (ComplexCells.lowerBonds D)
      (fun x => ‖BlockAverages.ofUnit (BlockAverages.referenceDefect R x.1 x.2) - 1‖) ≤ 26 * b := by
  have hL2 : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast h2
  have hL1 : (1 : ℝ) ≤ F.blockSide := by linarith
  refine LevelRecursion.finsetLpNorm_le_of_sum_pow_le (P := 2) (by norm_num) (ComplexCells.lowerBonds D)
    ({()} : Finset Unit) _ (fun _ => (1 : ℝ)) (C := 26 * b) (by positivity) ?_ |>.trans ?_
  · simp only [Finset.sum_singleton, abs_one, one_pow, mul_one]
    simp only [sq_abs]
    rw [ComplexCells.lowerBonds, Finset.sum_sigma]
    have hlevel : ∀ m ∈ Finset.range (F.top - 1), ∑ c ∈ BlockAverages.innerBonds D (m + 1),
        ‖BlockAverages.ofUnit (BlockAverages.referenceDefect R m c) - 1‖ ^ 2 ≤
        324 * b ^ 2 * (1 / (F.blockSide : ℝ)) ^ (F.top - 1 - 1 - m) := by
      intro m hm
      have hm' := Finset.mem_range.1 hm
      set M : ℝ := (F.blockSide : ℝ) ^ (F.top - (m + 1)) with hM
      have hM1 : 1 ≤ M := one_le_pow₀ hL1
      have hl : (1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1)) = 1 / M := by
        rw [hM, one_div, one_div, inv_pow]
      have hcard : ((BlockAverages.innerBonds D (m + 1)).card : ℝ) ≤ 324 * M ^ 4 := by
        have h1 := BlockLines.card_innerBonds_le hodd D (m + 1)
        have h3 : ((BlockAverages.innerBonds D (m + 1)).card : ℝ) ≤
            ((4 * (D.card * (F.blockSide ^ (F.top - (m + 1))) ^ 4) : ℕ) : ℝ) := by
          exact_mod_cast h1
        push_cast at h3
        have h4 : (D.card : ℝ) ≤ 81 := by exact_mod_cast hD
        calc _ ≤ 4 * ((D.card : ℝ) * M ^ 4) := h3
          _ ≤ 4 * (81 * M ^ 4) := by gcongr
          _ = _ := by ring
      have hterm : ∀ c ∈ BlockAverages.innerBonds D (m + 1),
          ‖BlockAverages.ofUnit (BlockAverages.referenceDefect R m c) - 1‖ ^ 2 ≤ (b * (1 / M) ^ 3) ^ 2 := by
        intro c hc
        have hx : (⟨m, c⟩ : Σ m : ℕ, F.Site (m + 1) × Fin 4) ∈ ComplexCells.lowerBonds D :=
          CellSources.mem_lowerBonds (by omega) hc
        have := h _ hx
        simp only at this
        rw [hl] at this
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
      refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
      rw [nsmul_eq_mul]
      have hq : (b * (1 / M) ^ 3) ^ 2 = b ^ 2 / M ^ 6 := by
        field_simp
      rw [hq]
      have h6 : ((BlockAverages.innerBonds D (m + 1)).card : ℝ) * (b ^ 2 / M ^ 6) ≤ 324 * M ^ 4 * (b ^ 2 / M ^ 6) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      refine h6.trans ?_
      have e1 : 324 * M ^ 4 * (b ^ 2 / M ^ 6) = 324 * b ^ 2 * (1 / M ^ 2) := by
        field_simp
      rw [e1]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have e2 : F.top - (m + 1) = (F.top - 1 - 1 - m) + 1 := by omega
      have h7 : 1 / M ^ 2 ≤ 1 / M := one_div_le_one_div_of_le (by positivity) (by nlinarith)
      refine h7.trans ?_
      rw [← hl, e2, pow_succ]
      exact mul_le_of_le_one_right (by positivity) (by
        rw [div_le_one (by positivity)]
        exact hL1)
    refine (Finset.sum_le_sum hlevel).trans ?_
    rw [← Finset.mul_sum]
    have hs := LevelRecursion.sum_inv_pow_le_two hL2 (F.top - 1)
    have h8 : 324 * b ^ 2 * ∑ i ∈ Finset.range (F.top - 1), (1 / (F.blockSide : ℝ)) ^ (F.top - 1 - 1 - i) ≤
        324 * b ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    refine h8.trans ?_
    nlinarith
  · simp [LevelRecursion.finsetLpNorm]
section Hypotheses
theorem cellHypotheses_of_referenceBounds (hrec : BlockAverages.UniformQuarticBoundAcrossLevels)
    (hbd : BlockAverages.referenceBoundsStatement) :
    ∃ (C : ℝ) (L1 : ℕ), 0 < C ∧ ∀ L : ℕ, Odd L → L1 ≤ L → 5 ≤ L → ∃ c y₀ : ℝ, 0 < c ∧ 0 < y₀ ∧
      ∀ (F : BlockAverages.BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L →
        BlockAverages.IsAdmissibleAmbient F → 1024 ≤ m → BlockAverages.IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → BlockAverages.IsCold S F.top s V →
          ∀ (z : F.Cell) (y : ℝ), 26 * C * s ≤ y → y ≤ y₀ →
            CellSpans.CellHypotheses S z (BlockAverages.referenceFieldChain S V) C s y := by
  obtain ⟨C, c, L1, hC, hc, hb⟩ := hbd
  refine ⟨C, L1, hC, fun L hodd hL1 h5 => ?_⟩
  obtain ⟨c₁, hc₁, -, hlev⟩ := ComplexLevels.quartic_levelDeviation_bound hrec L hodd h5 hC.le
  obtain ⟨y₀, hy₀, hsz⟩ := exists_smallParameter hodd.pos
  refine ⟨min c c₁, min y₀ (c₁ / 2), lt_min hc hc₁, lt_min hy₀ (by positivity), ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold z y hy hyy
  subst hFL
  have hoddF : Odd F.blockSide := hodd
  have h2 : 2 ≤ F.blockSide := by omega
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb F m S hoddF hL1 hamb hm hreg s V hs (hsc.trans (min_le_left _ _)) hcold
  set R := BlockAverages.referenceFieldChain S V with hR
  have hsub : ∀ k, BlockAverages.innerBonds (BlockAverages.cellBall S z 1) k ⊆ BlockAverages.innerBonds S k :=
    fun k => BlockLines.innerBonds_mono (BlockLines.cellBall_subset S z 1) k
  have hnear : ComplexLevels.ContoursNearUnit R (BlockAverages.cellBall S z 1) C s := by
    intro j hj c' hc' h' hh π
    rw [norm_ofUnit_sub_one]
    exact b5 j (by omega) c' (hsub _ hc') h' hh π
  refine ⟨hsz y hy0 (hyy.trans (min_le_left _ _)), hC, hs, ?_, hnear, ?_, ?_, ?_⟩
  · have : C * s ≤ 26 * C * s := by
      have := mul_pos hC hs
      nlinarith
    linarith
  · have h1 := lpNorm_referenceDefect_le (D := BlockAverages.cellBall S z 1) (R := R) hoddF h2
      (BlockLines.card_cellBall_one_le S z) (b := C * s)
      (mul_pos hC hs).le (fun x hx => by
        obtain ⟨hxn, hxb⟩ := ComplexCells.mem_lowerBonds hx
        rw [norm_ofUnit_sub_one]
        exact b3 x.1 hxn x.2 (hsub _ hxb))
    have e : 26 * (C * s) = 26 * C * s := by ring
    linarith
  · intro q hq
    have hqS : q ∈ BlockAverages.innerPlaquettes S 0 := (Finset.mem_filter.1 hq).1
    have := b2 0 (Nat.succ_pos _) q hqS
    rw [basePlaquetteHolonomy_eq_plaquetteHolonomy, norm_ofUnit_sub_one]
    have e : C * s * BlockAverages.levelScale F 0 ^ 2 = C * s / ((F.blockSide : ℝ) ^ F.top) ^ 2 := by
      simp only [BlockAverages.levelScale, Nat.sub_zero]
      rw [one_div, inv_pow, inv_pow]
      rfl
    rw [← e]
    exact this
  · intro W h0 hm'
    exact hlev F (BlockAverages.cellBall S z 1) R W s (2 * y) rfl (BlockLines.card_cellBall_one_le S z) hnear hs.le
      (hsc.trans (min_le_right _ _))
      (by positivity) (by
        have := hyy.trans (min_le_right _ _)
        linarith) h0 hm'
end Hypotheses
end YangMills.Construction.CellContexts
end
