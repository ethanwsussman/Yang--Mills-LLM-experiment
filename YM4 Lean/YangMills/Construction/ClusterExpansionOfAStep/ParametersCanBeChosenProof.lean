import YangMills.Construction.ClusterExpansionOfAStep.ParametersExist
import YangMills.Construction.ColdStepAtMirrorFrames.ACutExists
import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbers
import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainAtSmallCoordinates
import YangMills.Construction.HoleBesideASecondHole.CoercivityOfTheChain
import YangMills.Construction.HoleBesideASecondHole.WhatAHoleSaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours HoleBounds ColdChain RenormalizationStepParameters TorusLumps ColdStepAtMirrorFrames
namespace ParameterChoice
def lumpCount (h : ℤ) : ℤ := (h - 8192) / 16384
def lumpIndex (h o : ℤ) : ℤ :=
  if (o - 8193) / 16384 < lumpCount h - 1 then (o - 8193) / 16384 else lumpCount h - 1
def lumpLower (h o : ℤ) : ℤ := 8193 + lumpIndex h o * 16384
def lumpUpper (h o : ℤ) : ℤ :=
  if (o - 8193) / 16384 < lumpCount h - 1 then 8192 + (lumpIndex h o + 1) * 16384 else h
def intervalLower (h o : ℤ) : ℤ :=
  if |o| ≤ 8192 then -8192 else if 0 < o then lumpLower h o else -lumpUpper h (-o)
def intervalUpper (h o : ℤ) : ℤ :=
  if |o| ≤ 8192 then 8192 else if 0 < o then lumpUpper h o else -lumpLower h (-o)
def standardLumpGrid (L : ℕ) (hL : 2 ^ 16 ≤ L) : LumpGrid L where
  lower := intervalLower (((L : ℤ) - 1) / 2)
  upper := intervalUpper (((L : ℤ) - 1) / 2)
  mem_interval := by
    intro o ho
    have hL' : (2 : ℤ) ^ 16 ≤ L := by exact_mod_cast hL
    generalize hh : ((L : ℤ) - 1) / 2 = h at *
    have hh2 : 32767 ≤ h := by omega
    simp only [intervalLower, intervalUpper, lumpLower, lumpUpper, lumpIndex, lumpCount]
    split_ifs <;> simp only [abs_le, not_and_or, not_le] at * <;> omega
  interval_eq := by
    intro o o' ho h1 h2
    have hL' : (2 : ℤ) ^ 16 ≤ L := by exact_mod_cast hL
    generalize hh : ((L : ℤ) - 1) / 2 = h at *
    have hh2 : 32767 ≤ h := by omega
    simp only [intervalLower, intervalUpper, lumpLower, lumpUpper, lumpIndex, lumpCount] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ <;> simp only [abs_le, not_and_or, not_le] at * <;> first | omega | simp
  interval_length := by
    intro o ho
    have hL' : (2 : ℤ) ^ 16 ≤ L := by exact_mod_cast hL
    generalize hh : ((L : ℤ) - 1) / 2 = h at *
    have hh2 : 32767 ≤ h := by omega
    simp only [intervalLower, intervalUpper, lumpLower, lumpUpper, lumpIndex, lumpCount]
    norm_num
    split_ifs <;> simp only [abs_le, not_and_or, not_le] at * <;> omega
  lower_neg := by
    intro o ho
    simp only [intervalLower, intervalUpper, abs_neg, neg_neg]
    split_ifs <;> simp only [abs_le, not_and_or, not_le] at * <;> first | rfl | omega
end ParameterChoice
namespace ParameterChoice
theorem holeSavingAt_anti {L : ℕ} (g : LumpGrid L) {a κ Θ s cE cE' : ℝ} {J₀ : ℕ} (hle : cE' ≤ cE)
    (h : HoleSavingAt g a κ Θ s cE J₀) : HoleSavingAt g a κ Θ s cE' J₀ := by
  have key : ∀ (F : BlockFrame) (S S' : Finset F.Cell) (hV : Finset (Finset (F.Site F.top)))
      (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth)
      (Wl : F.GaugeField F.depth),
      HoleSavingInequality g a κ s cE J₀ S S' hV V W b Wl →
      HoleSavingInequality g a κ s cE' J₀ S S' hV V W b Wl := by
    intro F S S' hV V W b Wl hi
    unfold HoleSavingInequality at hi ⊢
    have : cE' * ((badCells (s / 128) S' V W Wl).card : ℝ) ≤
        cE * ((badCells (s / 128) S' V W Wl).card : ℝ) :=
      mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)
    linarith
  intro F hF hc
  obtain ⟨h1, h2⟩ := h F hF hc
  exact ⟨fun hd H hl V W b Wl hw hb hl' => key _ _ _ _ _ _ _ _ (h1 hd H hl V W b Wl hw hb hl'),
    fun V W b Wl hcold hb hl' => key _ _ _ _ _ _ _ _ (h2 V W b Wl hcold hb hl')⟩
section Monotone
variable {F : BlockFrame} {a δ ρ s : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top} {N N' : ℕ → ℝ}
theorem hasColdMinimizer_mono (hs : 0 < s) {n n' : ℝ} (h : n ≤ n') (h1 : HasColdMinimizer a ρ n s S V) :
    HasColdMinimizer a ρ n' s S V := by
  obtain ⟨w, ⟨h2, h3, h4⟩, h5, h6⟩ := h1
  exact ⟨w, ⟨h2, fun b hb => (h3 b hb).trans
    (min_le_min_left _ (mul_le_mul_of_nonneg_right h hs.le)), h4⟩, h5, h6⟩
theorem hasRegularCellShares_mono (hs : 0 < s) (hN : ∀ k, N k ≤ N' k)
    (h : HasRegularCellShares a δ s N S V) : HasRegularCellShares a δ s N' S V := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := h
  refine ⟨c1, c2, c3, c4, c5, fun k c X hk hX => ?_, fun Y k c X hk hX => ?_, fun Y => ?_,
    fun Y c X hX => ?_⟩
  · exact (c6 k c X hk hX).trans (mul_le_mul_of_nonneg_right (hN k) (Real.exp_pos _).le)
  · exact (c7 Y k c X hk hX).trans (mul_le_mul_of_nonneg_right (hN k) (Real.exp_pos _).le)
  · exact ⟨(c8 Y).1, (c8 Y).2.trans (mul_le_mul_of_nonneg_right (hN 0) (by positivity))⟩
  · refine (c9 Y c X hX).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    exact mul_le_mul_of_nonneg_right (hN 1) hs.le
theorem hasRegularCoordinates_mono (hN : ∀ k, N k ≤ N' k) (h : HasRegularCoordinates a δ ρ N S V) :
    HasRegularCoordinates a δ ρ N' S V := fun b hb =>
  ⟨(h b hb).1, fun k c X hk hX =>
    ((h b hb).2 k c X hk hX).trans (mul_le_mul_of_nonneg_right (hN k) (Real.exp_pos _).le)⟩
theorem hasComparableCellShares_mono {F' : BlockFrame} {S' : Finset F'.Cell} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} (hs : 0 < s) (hN : ∀ k, N k ≤ N' k)
    (h : HasComparableCellShares a δ s N S V S' V' Y Y' r) :
    HasComparableCellShares a δ s N' S V S' V' Y Y' r := by
  intro k hh X hb hX
  have hf : 0 ≤ derivativeScale s k := by
    unfold derivativeScale
    split_ifs <;> positivity
  refine (h k hh X hb hX).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  exact mul_le_mul_of_nonneg_left (hN k) hf
theorem hasComparableCoordinates_mono {F' : BlockFrame} {S' : Finset F'.Cell} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} (hs : 0 < s) (hN : ∀ k, N k ≤ N' k)
    (h : HasComparableCoordinates a δ ρ s N S V S' V' Y Y' r) :
    HasComparableCoordinates a δ ρ s N' S V S' V' Y Y' r := by
  intro hh o i ho hb hbox hd
  obtain ⟨h1, h2⟩ := h hh o i ho hb hbox hd
  refine ⟨h1.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hN 0) hs.le) (Real.exp_pos _).le), fun k h' X hk hb' hX => ?_⟩
  exact (h2 k h' X hk hb' hX).trans (mul_le_mul_of_nonneg_right (hN k) (Real.exp_pos _).le)
end Monotone
theorem coldChainConstants_mono {a δ lam ρ σA cg : ℝ} {L : ℕ} {N N' : ℕ → ℝ} (hN : ∀ k, N k ≤ N' k)
    (h : ColdChainConstants a δ L lam ρ σA cg N) : ColdChainConstants a δ L lam ρ σA cg N' := by
  obtain ⟨d0, d1, l0, r0, r1, s0, c0, n0, hb⟩ := h
  refine ⟨d0, d1, l0, r0, r1, s0, c0, fun k => lt_of_lt_of_le (n0 k) (hN k), ?_⟩
  intro F m S hF hA hm hR s V hs hsσ hc
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb F m S hF hA hm hR s V hs hsσ hc
  refine ⟨hasColdMinimizer_mono hs (hN 0) b1, b2, hasRegularCellShares_mono hs hN b3,
    hasRegularCoordinates_mono hN b4, b5, ?_⟩
  intro F' S' V' Y Y' r h1 h2 h3 h4 h5 h6
  obtain ⟨e1, e2⟩ := b6 F' S' V' Y Y' r h1 h2 h3 h4 h5 h6
  exact ⟨hasComparableCellShares_mono hs hN e1, hasComparableCoordinates_mono hs hN e2⟩
theorem le_clusterRange {y : ℝ} (hy : (2 : ℝ) ^ 1600 ≤ y) : 2 ^ 16 ≤ clusterRange y := by
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ 1600 := by positivity
  have h1 : ((2 : ℝ) ^ 1600) ^ ((1 : ℝ) / 100) ≤ y ^ ((1 : ℝ) / 100) :=
    Real.rpow_le_rpow h0 hy (by norm_num)
  have h2 : ((2 : ℝ) ^ 1600) ^ ((1 : ℝ) / 100) = 2 ^ 16 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h2] at h1
  have h3 : ((2 : ℝ) ^ 16) ≤ ((clusterRange y : ℕ) : ℝ) := h1.trans (Nat.le_ceil _)
  exact_mod_cast h3
theorem one_le_expansionConstant {Cs Na rt n₁ : ℝ} (hCs : 0 ≤ Cs) (hNa : 0 ≤ Na) :
    1 ≤ expansionConstant Cs Na rt n₁ := by
  have hS : 0 ≤ potentialDecaySum rt := tsum_nonneg fun cc =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_pos _).le
  have hF : 1 ≤ baseConstant Cs rt := by
    unfold baseConstant
    nlinarith [mul_nonneg hCs hS]
  have hG : 0 ≤ weightGrowthSup rt n₁ := Real.iSup_nonneg fun m =>
    mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.exp_pos _).le)
      (Real.exp_pos _).le
  unfold expansionConstant
  have : 0 ≤ weightGrowthSup rt n₁ * (2 * Cs + baseConstant Cs rt * Na) :=
    mul_nonneg hG (by nlinarith [mul_nonneg (le_trans zero_le_one hF) hNa])
  linarith
theorem admissible_stepParameters (T : ParameterAssignment) (ha : 1 ≤ T.coupling) (hodd : Odd T.side)
    (hL : 2 ^ 16 ≤ T.side) (hJ : 11 * 2 ^ 12 * T.baseDepth < T.side) (hσ : 0 < T.threshold)
    (hκ : 0 < T.κ) (hκ8 : T.κ ≤ 1 / 8) (hcE : 0 < T.cE) (hrt : 0 < T.rt) (hB : 1 ≤ T.B)
    (hη : 0 < T.η₃) (hCder : 1 ≤ T.derivBound) (hn : 4096 ≤ T.n₀) (hyC : 1 ≤ T.yC) (y : ℝ)
    (hy : T.floorMin ≤ y) : (T.stepParameters y).Admissible := by
  unfold ParameterAssignment.floorMin at hy
  obtain ⟨h1, h2⟩ := max_le_iff.1 hy
  have hLR : (0 : ℝ) < T.side := by
    have : 0 < T.side := lt_of_lt_of_le (by norm_num) hL
    exact_mod_cast this
  have hκ₁ : 0 < T.κ₁ := lt_min (by positivity) (by positivity)
  have hE1 : 1 ≤ T.E := by
    show 1 ≤ 4 * T.B
    linarith
  have hE : 0 < T.E := by linarith
  exact
    { a_ge := ha
      L_odd := hodd
      L_ge := hL
      σ_pos := hσ
      κ_pos := hκ
      κ_le := hκ8
      κ₁_pos := hκ₁
      rt_pos := hrt
      n₁_pos := Real.rpow_pos_of_pos hLR _
      E_pos := hE
      E_ge := hE1
      depth_lt := hJ
      E₃_pos := div_pos hE hη
      B_pos := by
        show 0 < T.B
        linarith
      Cder_ge := hCder
      n₀_ge := hn
      y₁_ge := hyC.trans h1
      range_ge := le_clusterRange h2 }
end ParameterChoice
theorem parametersCanBeChosen_holds (hK : ChainCoercivity)
    (hB : holeSavingStatement) (hA : ColdChainAtSmallCoordinates)
    (hG : AdmissibleParametersExist) (hP : ExistsCutoff) :
    ParametersCanBeChosen := by
  intro a ha
  obtain ⟨cK, hcK0, hcK1, LK, hK⟩ := hK
  obtain ⟨κ, hκ0, hκ8, hB⟩ := hB a ha
  obtain ⟨δ₁, hδ₁, LA, hA⟩ := hA a (by linarith)
  obtain ⟨Jf1, hJ1⟩ := hB 1 le_rfl
  obtain ⟨Jf2, hJ2⟩ := hB (9 / 8) (by norm_num)
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : ℕ, J₀ = max 625 (max Jf1 Jf2) := ⟨_, rfl⟩
  have hJ₀0 : 625 ≤ J₀ := by
    rw [hJ₀]
    exact le_max_left _ _
  have hJ₀1 : Jf1 ≤ J₀ := by
    rw [hJ₀]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hJ₀2 : Jf2 ≤ J₀ := by
    rw [hJ₀]
    exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨LB1, hB1⟩ := hJ1 J₀ hJ₀1
  obtain ⟨LB2, hB2⟩ := hJ2 J₀ hJ₀2
  refine ⟨cK, κ, δ₁, J₀, fun Q hQ => ?_⟩
  obtain ⟨LC, hC⟩ := hQ a ha
  refine ⟨max (max (max LK LA) (max LB1 LB2)) (max LC (max (2 ^ 40) (11 * 2 ^ 12 * J₀ + 1))),
    fun L hodd hL C₀ ceilRt ceilσ floorN floorCs floorK hr hs => ?_⟩
  have hLm := hL
  have hLK : LK ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hLm)
  have hLA : LA ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hLm)
  have hLB1 : LB1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hLm)
  have hLB2 : LB2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hLm)
  have hLC : LC ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLm)
  have hL40 : 2 ^ 40 ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hLm)
  have hLJ : 11 * 2 ^ 12 * J₀ + 1 ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hLm)
  have hL16 : 2 ^ 16 ≤ L := le_trans (by norm_num) hL40
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL16
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hnz : NeZero L := ⟨hLpos.ne'⟩
  obtain ⟨lam, ρA, σA, cg, N₁, hchain₁⟩ := hA L hodd hLA
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ → ℝ, N = fun k => max (N₁ k) (floorK k) := ⟨_, rfl⟩
  have hchain₂ : ColdChainConstants a δ₁ L lam ρA σA cg N :=
    ParameterChoice.coldChainConstants_mono (fun k => by rw [hNdef]; exact le_max_left _ _) hchain₁
  have hNfloor : ∀ k, floorK k ≤ N k := fun k => by
    rw [hNdef]
    exact le_max_right _ _
  obtain ⟨c, hc1, -, hc3, hc4, hc5, hc6, hc7, hcH⟩ := hG a δ₁ L lam ρA σA cg N ha hodd hchain₂
  have hchain : ColdChainConstants a δ₁ L c.lam c.ρA c.σA c.cg c.N := by
    rw [hc3, hc4, hc5, hc6, hc7]
    exact hchain₂
  have hN0 : 0 < c.N 0 := hchain.2.2.2.2.2.2.2.1 0
  have hρA : 0 < c.ρA := hchain.2.2.2.1
  have hσA : 0 < c.σA := hchain.2.2.2.2.2.1
  have hδc0 : 0 < c.δ₂ := hcH.classical.1.2.2.2.1
  have hδc1 : c.δ₂ ≤ δ₁ / 2 ^ 6 := by
    have := hcH.inequalities.2.1
    rw [hc1] at this
    linarith
  obtain ⟨Ct₀, hC⟩ := hC L hodd hLC c hcH
  obtain ⟨Ct, hCtdef⟩ : ∃ Ct : ℝ, Ct = max Ct₀ 1 := ⟨_, rfl⟩
  have hCta : Ct₀ ≤ Ct := by
    rw [hCtdef]
    exact le_max_left _ _
  have hCt : 0 < Ct := by
    rw [hCtdef]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨κ₀, hκ₀0, hC⟩ := hC Ct hCta
  let g : LumpGrid L := ParameterChoice.standardLumpGrid L hL16
  let D : ChainParameters :=
    { coupling := a, coercivity := cK, κ := κ, δ₁ := δ₁, baseDepth := J₀, side := L, side_ne := hnz,
      grid := g, lam := c.lam, ρA := c.ρA, σA := c.σA, cg := c.cg, N := c.N, δc := c.δ₂ }
  obtain ⟨rt, hrtdef⟩ : ∃ rt : ℝ, rt = min (min κ₀ (c.δ₂ / 2 ^ 14)) (ceilRt D) := ⟨_, rfl⟩
  have hrt0 : 0 < rt := by
    rw [hrtdef]
    exact lt_min (lt_min hκ₀0 (by positivity)) (hr D)
  have hrt1 : rt ≤ κ₀ := by
    rw [hrtdef]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hrt3 : rt ≤ c.δ₂ / 2 ^ 14 := by
    rw [hrtdef]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hrt2 : rt ≤ ceilRt D := by
    rw [hrtdef]
    exact min_le_right _ _
  obtain ⟨η₀, hη₀, hC⟩ := hC rt hrt0 hrt1
  obtain ⟨η₃, hη₃def⟩ : ∃ η₃ : ℝ, η₃ = min 1 η₀ := ⟨_, rfl⟩
  have hη0 : 0 < η₃ := by
    rw [hη₃def]
    exact lt_min one_pos hη₀
  have hη1 : η₃ ≤ 1 := by
    rw [hη₃def]
    exact min_le_left _ _
  have hη2 : η₃ ≤ η₀ := by
    rw [hη₃def]
    exact min_le_right _ _
  obtain ⟨nss, hC⟩ := hC η₃ hη0 hη1 hη2
  obtain ⟨σ₀, hσ₀, hC⟩ := hC nss le_rfl
  obtain ⟨s1, hs1, hB1⟩ := hB1 L hodd hLB1 g
  obtain ⟨s2, hs2, hB2⟩ := hB2 L hodd hLB2 g
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = min (min (min σ₀ s1) (min s2 (min (ceilσ D rt) (min 1 (1 / (2 ^ 10 * (L : ℝ) * (c.N 0 + 1)))))))
      (min (c.σA / 2) (min (c.ρA / (2 * c.N 0 + 1)) (c.σA / (8 * c.N 0 + 2)))) := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by
    rw [hσdef]
    exact lt_min (lt_min (lt_min hσ₀ hs1) (lt_min hs2 (lt_min (hs D rt) (lt_min one_pos (by positivity)))))
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hσa : σ ≤ σ₀ := by
    rw [hσdef]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hσb : σ ≤ s1 := by
    rw [hσdef]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hσc : σ ≤ s2 := by
    rw [hσdef]
    exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσd : σ ≤ ceilσ D rt := by
    rw [hσdef]
    exact (min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hσ1 : σ ≤ 1 := by
    rw [hσdef]
    exact (min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hσL : σ ≤ 1 / (2 ^ 10 * (L : ℝ) * (c.N 0 + 1)) := by
    rw [hσdef]
    exact (min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hσe : σ ≤ c.σA / 2 := by
    rw [hσdef]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hσf : σ ≤ c.ρA / (2 * c.N 0 + 1) := by
    rw [hσdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσg : σ ≤ c.σA / (8 * c.N 0 + 2) := by
    rw [hσdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨cE1, hcE1, hB1⟩ := hB1 σ hσ0 hσb
  obtain ⟨cE2, hcE2, hB2⟩ := hB2 σ hσ0 hσc
  obtain ⟨p, hp⟩ := hP (σ / 64) (by positivity)
  have hC := hC σ hσ0 hσa p hp
  obtain ⟨Cs₀, hC⟩ := hC
  obtain ⟨Cs, hCsdef⟩ : ∃ Cs : ℝ, Cs = max (max Cs₀ 1) (floorCs D rt σ) := ⟨_, rfl⟩
  have hCsa : Cs₀ ≤ Cs := by
    rw [hCsdef]
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hCsb : floorCs D rt σ ≤ Cs := by
    rw [hCsdef]
    exact le_max_right _ _
  have hCs : 0 < Cs := by
    rw [hCsdef]
    exact lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_left _ _))
  have hBv : 1 ≤ expansionConstant Cs (maxOfFirstFour c.N) rt ((L : ℝ) ^ (1 / 640 : ℝ)) :=
    ParameterChoice.one_le_expansionConstant hCs.le
      (hN0.le.trans ((le_max_left _ _).trans (le_max_left _ _)))
  obtain ⟨m₀, hC⟩ := hC Cs hCsa (4 * expansionConstant Cs (maxOfFirstFour c.N) rt ((L : ℝ) ^ (1 / 640 : ℝ)))
    (by linarith)
  obtain ⟨n₀, hn₀def⟩ : ∃ n₀ : ℕ, n₀ = max (max m₀ 4096) (floorN D rt σ) := ⟨_, rfl⟩
  have hn₀a : m₀ ≤ n₀ := by
    rw [hn₀def]
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hn₀b : 4096 ≤ n₀ := by
    rw [hn₀def]
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hn₀c : floorN D rt σ ≤ n₀ := by
    rw [hn₀def]
    exact le_max_right _ _
  obtain ⟨C₁, hC⟩ := hC n₀ hn₀a
  obtain ⟨CE, hCEdef⟩ : ∃ CE : ℝ, CE = max C₁ 1 := ⟨_, rfl⟩
  have hCEa : C₁ ≤ CE := by
    rw [hCEdef]
    exact le_max_left _ _
  have hCE : 0 < CE := by
    rw [hCEdef]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨y₀, hC⟩ := hC CE hCEa
  obtain ⟨yC, hyCdef⟩ : ∃ yC : ℝ, yC = max y₀ 1 := ⟨_, rfl⟩
  have hyCa : y₀ ≤ yC := by
    rw [hyCdef]
    exact le_max_left _ _
  have hyC : 1 ≤ yC := by
    rw [hyCdef]
    exact le_max_right _ _
  let T : ParameterAssignment :=
    { toChainParameters := D, rt := rt, η₃ := η₃, Ct := Ct, threshold := σ, cutoff := p, Cs := Cs,
      cE := min cE1 cE2, n₀ := n₀, CE := CE, yC := yC, derivBound := max (2 ^ 6 * (a + 1)) C₀ }
  have hTB : 1 ≤ T.B := hBv
  have hcE : 0 < min cE1 cE2 := lt_min hcE1 hcE2
  have hCder : 2 ^ 6 * (a + 1) ≤ T.derivBound := le_max_left _ _
  refine ⟨T, rfl, rfl, rfl, rfl, rfl, rfl, le_max_right _ _, hrt2, hσd, hn₀c, hCsb, ?_, ?_, ?_⟩
  · intro k
    show floorK k ≤ c.N k
    rw [hc7]
    exact hNfloor k
  · exact
    { a_ge := ha
      cK_pos := hcK0
      cK_le := hcK1
      coercive := hK a L ha hodd hLK
      κ_pos := hκ0
      κ_le := hκ8
      δ₁_pos := hδ₁
      J₀_ge := hJ₀0
      L_odd := hodd
      L_ge := hL40
      L_gt := hLJ
      chain := hchain
      δc_pos := hδc0
      δc_le := hδc1
      rt_pos := hrt0
      rt_le := hrt3
      η₃_pos := hη0
      η₃_le := hη1
      Ct_pos := hCt
      σ_pos := hσ0
      σ_one := hσ1
      σ_L := by
        show 2 ^ 10 * (L : ℝ) * (c.N 0 + 1) * σ ≤ 1
        have hpos : (0 : ℝ) < 2 ^ 10 * (L : ℝ) * (c.N 0 + 1) := by positivity
        have h1 := (le_div_iff₀ hpos).1 hσL
        linarith
      σ_le := by
        show 2 * σ ≤ c.σA
        linarith
      ρ_le := by
        show 2 * c.N 0 * σ + 2 * (σ / 64) ≤ c.ρA
        have h1 : σ * (2 * c.N 0 + 1) ≤ c.ρA := (le_div_iff₀ (by positivity)).1 hσf
        linarith
      cold_le := by
        show 9 / 8 * σ + 4 * (2 * c.N 0 * σ + 2 * (σ / 64)) ≤ c.σA
        have h1 : σ * (8 * c.N 0 + 2) ≤ c.σA := (le_div_iff₀ (by positivity)).1 hσg
        linarith
      hole_one := ParameterChoice.holeSavingAt_anti _ (min_le_left _ _) hB1
      hole_more := ParameterChoice.holeSavingAt_anti _ (min_le_right _ _) hB2
      cE_pos := hcE
      cut := hp
      Cs_pos := hCs
      B_ge := hTB
      n₀_ge := hn₀b
      CE_pos := hCE
      yC_ge := hyC
      Cder_ge := hCder
      fits := ParameterChoice.admissible_stepParameters T ha hodd hL16 hLJ hσ0 hκ0 hκ8 hcE hrt0 hTB hη0
        (by show 1 ≤ T.derivBound; linarith) hn₀b hyC }
  · exact ⟨c, nss, ⟨hc1, rfl, rfl, rfl, rfl, rfl, rfl, hcH⟩, fun y hy => hC y (hyCa.trans hy)⟩
end YangMills.Construction.ClusterExpansionOfAStep
end
