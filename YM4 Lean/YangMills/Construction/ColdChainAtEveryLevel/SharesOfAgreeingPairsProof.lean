import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOnOneFrame
import YangMills.Construction.ColdChainAtEveryLevel.SharesAtTheSameOffsets
import YangMills.Construction.ColdChainAtEveryLevel.TheShareNearACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace AgreeingPairShares
variable {F : BlockFrame} {sd : Fin 4 → ℕ}
theorem cellShareInChart_eq_zero_of_not_mem {S : Finset F.Cell} (hodd : Odd F.blockSide) (a : ℝ) {Y : F.Cell}
    (hY : Y ∉ S) (R : F.FieldChain) (V : F.GaugeField F.top) (U : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : localCellShare a S R V Y U v = 0 := by
  classical
  have e1 : ∀ p ∈ innerPlaquettes S 0, LowerShare.plaquetteWeight Y p = 0 := by
    intro p hp
    unfold LowerShare.plaquetteWeight
    refine Finset.sum_eq_zero fun x hx => if_neg fun e => hY ?_
    rw [← e]
    exact LocalPartition.enclosingCell_mem hodd ((Finset.mem_filter.1 hp).2.2 hx)
  have e2 : ∀ j, ∀ c ∈ innerBonds S j, LowerShare.bondWeight Y c = 0 := by
    intro j c hc
    have hb := ChartCoordinates.innerBonds_ends hc
    unfold LowerShare.bondWeight
    rw [if_neg, if_neg]
    · simp
    · intro e
      exact hY (e ▸ LocalPartition.enclosingCell_mem hodd hb.2)
    · intro e
      exact hY (e ▸ LocalPartition.enclosingCell_mem hodd hb.1)
  rw [LowerShare.cellShareInChart_eq_lowerShareInChart_add_topShareInChart]
  unfold LowerShare.lowerEvaluation LowerShare.topRestriction
  rw [Finset.sum_eq_zero fun p hp => by rw [e1 p hp, zero_mul],
    Finset.sum_eq_zero (s := Finset.range (F.top - 1)) fun j _ =>
      Finset.sum_eq_zero fun c hc => by rw [e2 _ c hc, zero_mul],
    Finset.sum_eq_zero (s := innerBonds S (F.depth + 1)) fun c hc => by rw [e2 _ c hc, zero_mul]]
  simp
theorem enclosingCell_top_eq {G : BlockFrame} (x : G.Cell) : enclosingCell x = x := by apply _root_.YangMills.Construction.PotentialMeans.enclosingCell_self <;> assumption
theorem mem_topBondsMeetingCell_of_bondWeight_ne_zero {S : Finset F.Cell} {Y : F.Cell}
    {b : F.Site (F.depth + 1) × Fin 4} (hS : b ∈ innerBonds S (F.depth + 1))
    (hb : LowerShare.bondWeight Y b ≠ 0) : b ∈ topBondsMeetingCell S Y := by
  classical
  refine Finset.mem_filter.2 ⟨hS, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hb
  unfold LowerShare.bondWeight
  rw [if_neg (by rw [enclosingCell_top_eq]; exact hcon.1), if_neg (by rw [enclosingCell_top_eq]; exact hcon.2)]
  simp
theorem siteAtSameOffset_eq_cellAtSameOffset (Y : F.Cell) (Y' : (SameOffsetCharts.sameShapeFrame F sd).Cell)
    (x : F.Site F.top) : siteAtSameOffset Y Y' x = cellAtSameOffset Y Y' x := by
  unfold siteAtSameOffset cellAtSameOffset
  rw [cellCentre_top (F := SameOffsetCharts.sameShapeFrame F sd) Y', cellCentre_top Y]
theorem chartAtSameOffsets_chartShiftAlong {m : ℕ} (Y : F.Cell) (Y' : (SameOffsetCharts.sameShapeFrame F sd).Cell)
    (U' : ChainChart (SameOffsetCharts.sameShapeFrame F sd))
    (A' : Fin m → ChainChart (SameOffsetCharts.sameShapeFrame F sd)) (t : Fin m → ℝ) :
    chartAtSameOffsets Y Y' (chartShiftAlong U' A' t) =
      chartShiftAlong (chartAtSameOffsets Y Y' U') (fun l => chartAtSameOffsets Y Y' (A' l)) t := rfl
end AgreeingPairShares
set_option maxHeartbeats 4000000 in
open Classical in
theorem agreeingPairsShareComparison_of_local (hNear : cellShareIsLocalStatement)
    (hLn : agreeingPairsLocalityStatement) : agreeingPairsShareComparisonStatement := by
  intro a ha
  obtain ⟨cl, hcl, hlines⟩ := hLn
  obtain ⟨L₀, h₁⟩ := hNear a ha
  refine ⟨L₀, fun L hL hge => ?_⟩
  obtain ⟨c₁, Ck, hc₁, hCk, hloc⟩ := h₁ L hL hge
  obtain ⟨c, hcv⟩ : ∃ c : ℝ, c = min (min (c₁ / 4) cl) (1 / 3) := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hcv]
    exact lt_min (lt_min (by positivity) hcl) (by norm_num)
  have d1 : c ≤ c₁ / 4 := by
    rw [hcv]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have d2 : c ≤ cl := by
    rw [hcv]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have d3 : c ≤ 1 / 3 := by
    rw [hcv]
    exact min_le_right _ _
  obtain ⟨Cm, hCmv⟩ : ∃ Cm : ℕ → ℝ, Cm = fun k => 2 * Ck 1 + 2 * Ck 2 + Ck (k + 1) + Ck k := ⟨_, rfl⟩
  have hCm : ∀ k, 0 ≤ Cm k := fun k => by
    rw [hCmv]
    have h1 := hCk 1
    have h2 := hCk 2
    have h3 := hCk (k + 1)
    have h4 := hCk k
    show 0 ≤ 2 * Ck 1 + 2 * Ck 2 + Ck (k + 1) + Ck k
    positivity
  refine ⟨c, 110, Cm, hc0, hCm, ?_⟩
  intro F F' m S S' hFL hF'L ht hamb hamb' hm hreg hreg' s V V' Y Y' r hs hsc hcold hcold' hr hag U U' hU hU'
  obtain ⟨L', t', sd⟩ := F'
  have hLL : L' = F.blockSide := hF'L.trans hFL.symm
  have htt : t' = F.depth := ht
  subst hLL
  subst htt
  have hodd : Odd F.blockSide := hFL ▸ hL
  obtain ⟨-, hl2⟩ := hlines F (SameOffsetCharts.sameShapeFrame F sd) m S S' s V V' Y Y' r rfl rfl hodd hamb hamb' hm
    hreg hreg' hs (hsc.trans d2) hcold hcold' hag
  obtain ⟨hs1, hs2, hSS, hVV⟩ := hag
  have hr8 : ∀ i, 8 ≤ 2 * r + 2 := fun _ => by omega
  have T : SameOffsetShares.NeighbourhoodsAgree (sd := sd) S S' Y Y' := by
    refine ⟨hamb, hamb', hodd, fun b hb => hSS b fun i => (hb i).trans ?_, fun i => ?_, fun i => ?_⟩
    · have : (4 : ℤ) ≤ r := by exact_mod_cast (by omega : 4 ≤ r)
      exact this
    · rcases hs1 i with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_le_of_lt (by omega : 8 ≤ 2 * r + 2) h)
    · rcases hs2 i with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_le_of_lt (by omega : 8 ≤ 2 * r + 2) h)
  have hR := SameOffsets.referenceFieldChain_agree (Y := Y) (Y' := Y') (D := cellBall S Y 1) hamb hodd
    (F' := SameOffsetCharts.sameShapeFrame F sd) rfl (SameOffsetShares.isNearCells_cellBall S Y)
    (by omega : 102 ≤ r) (BlockLines.cellBall_subset S Y 1) hl2
  obtain ⟨R, hRv⟩ : ∃ R : F.FieldChain, R = referenceFieldChain S V := ⟨_, rfl⟩
  obtain ⟨R', hR'v⟩ : ∃ R' : (SameOffsetCharts.sameShapeFrame F sd).FieldChain, R' = referenceFieldChain S' V' :=
    ⟨_, rfl⟩
  rw [← hRv, ← hR'v] at hR
  rw [← hRv] at hU
  rw [← hR'v] at hU'
  rw [← hRv, ← hR'v]
  have hR0 : ∀ x i, x ∈ sitesOfCells (cellBall S Y 4) 0 → x + unitStep 0 i ∈ sitesOfCells (cellBall S Y 4) 0 →
      R 0 x i = R' 0 (siteAtSameOffset Y Y' x) i := by
    intro x i hx hx'
    obtain ⟨a', g, ha', -, hg, -, e', hsm⟩ := SameOffsetShares.exists_offset_of_mem T (Nat.zero_le _) hx
    set p : LatticeFractionalIntegration.Lattice4 := (fun i => (F.blockSide : ℤ) ^ (F.top - 0) * a' i) + g with hp
    set K : ℤ := (F.blockSide : ℤ) ^ F.top with hK
    have hK1 : 1 ≤ K := one_le_pow₀ (by exact_mod_cast hodd.pos)
    have hpb : ∀ μ, |p μ| ≤ 5 * K := fun μ => by
      have hgc := (LatticePaths.mem_centredCube_iff _ _).1 hg μ
      have hcast : (((F.blockSide ^ (F.top - 0) : ℕ) : ℤ)) = K := by
        rw [hK]
        push_cast
        rfl
      rw [hcast] at hgc
      have hgb : |g μ| ≤ K := by
        rw [abs_le]
        constructor <;> omega
      have h1 := ha' μ
      simp only [hp, Pi.add_apply]
      refine (abs_add_le _ _).trans ?_
      have e0 : (F.blockSide : ℤ) ^ (F.top - 0) = K := rfl
      rw [abs_mul, e0, abs_of_pos (by omega : (0 : ℤ) < K)]
      nlinarith
    have hr' : (110 : ℤ) ≤ r := by exact_mod_cast hr
    have hin1 : IsInnerOffset F.blockSide F.top r 0 p := fun μ => by
      have h1 := hpb μ
      simp only [pow_zero, one_mul]
      nlinarith
    have hin2 : IsInnerOffset F.blockSide F.top r 0 (p + Pi.single i 1) := fun μ => by
      have h1 := hpb μ
      have h3 : |(Pi.single i (1 : ℤ) : LatticeFractionalIntegration.Lattice4) μ| ≤ 1 := by
        by_cases hμ : μ = i
        · subst hμ
          simp
        · simp [hμ]
      have h4 : |(p + Pi.single i 1 : LatticeFractionalIntegration.Lattice4) μ| ≤ 6 * K := by
        simp only [Pi.add_apply]
        refine (abs_add_le _ _).trans ?_
        omega
      simp only [pow_zero, one_mul]
      nlinarith
    have hbond : ((cellCentre 0 Y + siteOfCoords 0 p, i) : F.Site 0 × Fin 4) ∈ innerBonds S 0 := by
      have e0 : cellCentre 0 Y + siteOfCoords 0 p = x := e'.symm
      rw [e0]
      exact ChartCoordinates.mem_innerBonds (BlockLines.sitesOfCells_mono (BlockLines.cellBall_subset S Y 4) 0 hx)
        (BlockLines.sitesOfCells_mono (BlockLines.cellBall_subset S Y 4) 0 hx')
    have h5 := hl2 0 p i (Nat.succ_pos _) hin1 hin2 hbond
    have e1 : R 0 = referenceGaugeField S V 0 := by
      rw [hRv]
      unfold referenceFieldChain
      exact Function.update_of_ne (Nat.succ_pos F.depth).ne _ _
    have e2 : R' 0 = referenceGaugeField S' V' 0 := by
      rw [hR'v]
      unfold referenceFieldChain
      exact Function.update_of_ne (by simp [BlockFrame.top]) _ _
    have e3 : siteAtSameOffset Y Y' x = cellCentre 0 Y' + siteOfCoords 0 p := by
      rw [e', SameOffsets.siteAtSameOffset_siteAtOffset hamb hodd.pos Y Y' hsm]
      rfl
    rw [e1, e2, e3]
    have e4 : x = cellCentre 0 Y + siteOfCoords 0 p := e'
    rw [e4]
    exact h5
  have hVb : ∀ b ∈ topBondsMeetingCell S Y, V b.1 b.2 = V' (siteAtSameOffset Y Y' b.1) b.2 := by
    intro b hb
    obtain ⟨hbS, hY⟩ := Finset.mem_filter.1 hb
    have hbw : LowerShare.bondWeight Y (b : F.Site (F.depth + 1) × Fin 4) ≠ 0 := by
      unfold LowerShare.bondWeight
      rcases hY with h | h
      · rw [if_pos (by rw [AgreeingPairShares.enclosingCell_top_eq]; exact h)]
        split_ifs <;> norm_num
      · rw [if_pos (c := enclosingCell (b.1 + unitStep (F.depth + 1) b.2) = Y)
          (by rw [AgreeingPairShares.enclosingCell_top_eq]; exact h)]
        split_ifs <;> norm_num
    have hbox := ReferenceShare.mem_innerBonds_cellBall_of_bondWeight_ne_zero hamb hodd (by simp [BlockFrame.top])
      hbS hbw
    obtain ⟨e1, e2⟩ := ChartCoordinates.innerBonds_ends hbox
    have hc1 := BlockLines.enclosingCell_mem hodd e1
    have hc2 := BlockLines.enclosingCell_mem hodd e2
    rw [AgreeingPairShares.enclosingCell_top_eq] at hc1 hc2
    obtain ⟨-, hd1⟩ := Finset.mem_filter.1 hc1
    obtain ⟨-, hd2⟩ := Finset.mem_filter.1 hc2
    set o : LatticeFractionalIntegration.Lattice4 := fun i => ((b.1 - Y) i).valMinAbs with hod
    have hbo : b.1 = Y + siteOfCoords F.top o := SameOffsetShares.eq_add_siteOfCoords_valMinAbs Y b.1
    have ho1 : ∀ i, |o i| ≤ 1 := fun i => by exact_mod_cast SameOffsetShares.abs_valMinAbs_sub_le hd1 i
    have hbox' : BondWithinRadius r (o, b.2) := by
      have hr1 : (2 : ℤ) ≤ r := by exact_mod_cast (by omega : 2 ≤ r)
      refine ⟨fun i => (ho1 i).trans (by omega), fun i => ?_⟩
      have h3 : |(Pi.single b.2 (1 : ℤ) : LatticeFractionalIntegration.Lattice4) i| ≤ 1 := by
        by_cases hμ : i = b.2
        · subst hμ
          simp
        · simp [hμ]
      simp only [Pi.add_apply]
      refine (abs_add_le _ _).trans ?_
      have := ho1 i
      omega
    have h6 := hVV _ hbox'
    simp only at h6
    rw [AgreeingPairShares.siteAtSameOffset_eq_cellAtSameOffset]
    have e5 : cellAtSameOffset Y Y' b.1 = Y' + siteOfCoords (SameOffsetCharts.sameShapeFrame F sd).top o := rfl
    rw [e5, ← h6, ← hbo]
  set n₁ := localNorm S R U (oneSiteWeights F) Y with hn₁
  set n₂ := localNorm S' R' U' (oneSiteWeights (SameOffsetCharts.sameShapeFrame F sd)) Y' with hn₂
  set U₂ := chartAtSameOffsets Y Y' U' with hU₂
  set D := chartMove U U₂ (-1) with hD
  have hn₁0 : 0 ≤ n₁ := Real.sqrt_nonneg _
  have hn₂0 : 0 ≤ n₂ := Real.sqrt_nonneg _
  have hgap : offsetChartGapNorm S R Y Y Y' U U' = localNorm S R D (oneSiteWeights F) Y := rfl
  have hread : localNorm S R U₂ (oneSiteWeights F) Y ≤ n₂ :=
    SameOffsetShares.localNorm_chartAtSameOffsets_le T U' hR0
  have hDn : localNorm S R D (oneSiteWeights F) Y ≤ n₁ + n₂ := by
    have := CoordinateSeminorms.localNorm_chartMove_le S R U U₂ (-1) (oneSiteWeights F) (fun _ _ => zero_le_one) Y
    simp only [abs_neg, abs_one, one_mul] at this
    linarith
  have hseg : ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
      localNorm S R (chartMove U₂ D ρ) (oneSiteWeights F) Y ≤ 2 * (n₁ + n₂) := by
    intro ρ hρ
    have h1 := CoordinateSeminorms.localNorm_chartMove_le S R U₂ D ρ (oneSiteWeights F) (fun _ _ => zero_le_one) Y
    have h2 : |ρ| ≤ 1 := abs_le.2 ⟨by linarith [hρ.1], hρ.2⟩
    have hDn0 : 0 ≤ localNorm S R D (oneSiteWeights F) Y := Real.sqrt_nonneg _
    have h3 := mul_le_mul_of_nonneg_right h2 hDn0
    linarith
  have hBm : ∀ b, b ∈ topBondsMeetingCell S Y ↔
      b ∈ innerBonds S F.top ∧ (b.1 = Y ∨ b.1 + unitStep F.top b.2 = Y) := fun b => by
    unfold topBondsMeetingCell
    simp [Finset.mem_filter]
  have hsc₁ : s ≤ c₁ := by linarith
  by_cases hY : Y ∈ S
  swap
  · have hY' : Y' ∉ S' := by
      intro h
      have h0 := (hSS 0 (fun i => by simp)).2
      rw [siteOfCoords_zero, add_zero, siteOfCoords_zero, add_zero] at h0
      exact hY (h0 h)
    have z1 : localCellShare a S R V Y = fun _ _ => 0 := by
      funext U₃ v
      exact AgreeingPairShares.cellShareInChart_eq_zero_of_not_mem hodd a hY R V U₃ v
    have z2 : localCellShare a S' R' V' Y' = fun _ _ => 0 := by
      funext U₃ v
      exact AgreeingPairShares.cellShareInChart_eq_zero_of_not_mem (F := SameOffsetCharts.sameShapeFrame F sd)
        hodd a hY' R' V' U₃ v
    have hzd : ∀ (n : ℕ) (A : Fin n → ChainChart F) (e : Fin n → F.Site F.top → Fin 4 → imaginaryQuaternions)
        (A' : Fin n → ChainChart (SameOffsetCharts.sameShapeFrame F sd))
        (e' : Fin n → (SameOffsetCharts.sameShapeFrame F sd).Site (SameOffsetCharts.sameShapeFrame F sd).top →
          Fin 4 → imaginaryQuaternions),
        localIteratedDeriv (localCellShare a S R V Y) U A e -
          localIteratedDeriv (localCellShare a S' R' V' Y') U' A' e' = 0 := by
      intro n A e A' e'
      rw [z1, z2]
      unfold localIteratedDeriv
      simp
    have hg0 : ∀ A₁ A₂, 0 ≤ offsetChartGapNorm S R Y Y Y' A₁ A₂ := fun _ _ => Real.sqrt_nonneg _
    refine ⟨⟨?_, fun n A A' e e' _ _ => ?_⟩, ?_, fun n A A' e e' _ _ => ?_⟩
    · rw [z1, z2]
      simp only [sub_self, norm_zero]
      exact mul_nonneg (hCm 0) (hg0 _ _)
    · rw [hzd, norm_zero]
      refine mul_nonneg (hCm n) (add_nonneg (mul_nonneg (hg0 _ _)
        (Finset.prod_nonneg fun l _ => YangMills.Construction.ChartCoordinates.localDirectionSize_nonneg _ _)) ?_)
      exact Finset.sum_nonneg fun l _ => mul_nonneg (hg0 _ _) (Finset.prod_nonneg fun l' _ =>
        add_nonneg (YangMills.Construction.ChartCoordinates.localDirectionSize_nonneg _ _) (hg0 _ _))
    · rw [z1, z2]
      simp only [sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg (hCm 0) (by positivity)) (hg0 _ _)
    · rw [hzd, norm_zero]
      refine mul_nonneg (hCm 1) (add_nonneg (mul_nonneg (hg0 _ _)
        (Finset.prod_nonneg fun l _ => YangMills.Construction.ChartCoordinates.localDirectionSize_nonneg _ _)) ?_)
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => hg0 _ _)
  have hY' : Y' ∈ S' := by
    have h0 := (hSS 0 (fun i => by simp)).1
    rw [siteOfCoords_zero, add_zero, siteOfCoords_zero, add_zero] at h0
    exact h0 hY
  have hn₁c : n₁ ≤ c := hU Y hY
  have hn₂c : n₂ ≤ c := hU' Y' hY'
  have hloc' : ∀ W : ChainChart F, localNorm S R W (oneSiteWeights F) Y ≤ c₁ →
      IsLocalRepresentation S R Y (topBondsMeetingCell S Y) Ck W (localCellShare a S R V Y) ∧
      |localCellShare a S R V Y W fun _ _ => 0| ≤ Ck 0 * (s + localNorm S R W (oneSiteWeights F) Y) ^ 2 ∧
      ∀ (n : ℕ) (A : Fin n → ChainChart F) (e : Fin n → F.Site F.top → Fin 4 → imaginaryQuaternions), n = 1 →
        ‖localIteratedDeriv (localCellShare a S R V Y) W A e‖ ≤
          Ck 1 * (s + localNorm S R W (oneSiteWeights F) Y) *
            ∏ l, localDirectionSize S R (topBondsMeetingCell S Y) Y (A l) (e l) := by
    intro W hW
    rw [hRv]
    exact hloc F m S hFL hamb hm hreg s V hs hsc₁ hcold W Y _ hBm (fun _ => by rw [← hRv]; exact hW)
  have hsegc : ∀ ρ ∈ Set.Icc (0 : ℝ) 1, localNorm S R (chartMove U₂ D ρ) (oneSiteWeights F) Y ≤ c₁ :=
    fun ρ hρ => by
      have := hseg ρ hρ
      linarith
  have hLoc := fun ρ (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) => (hloc' _ (hsegc ρ hρ)).1
  have hend : chartMove U₂ D 1 = U := YangMills.Construction.ChartCoordinates.chartMove_chartMove_neg_one U U₂
  have hstart : chartMove U₂ D 0 = U₂ := by
    apply CoordinateSeminorms.chainChart_ext
    · funext x i
      simp [chartMove]
    · funext j x i
      simp [chartMove]
  have hL₂ : IsLocalRepresentation S R Y (topBondsMeetingCell S Y) Ck U₂ (localCellShare a S R V Y) := by
    have := hLoc 0 ⟨le_rfl, zero_le_one⟩
    rwa [hstart] at this
  have hsame : ∀ {n : ℕ} (A' : Fin n → ChainChart (SameOffsetCharts.sameShapeFrame F sd))
      (e : Fin n → F.Site F.top → Fin 4 → imaginaryQuaternions)
      (e' : Fin n → (SameOffsetCharts.sameShapeFrame F sd).Site (SameOffsetCharts.sameShapeFrame F sd).top →
        Fin 4 → imaginaryQuaternions),
      (∀ l, ∀ b ∈ topBondsMeetingCell S Y, e l b.1 b.2 = e' l (cellAtSameOffset Y Y' b.1) b.2) →
      localIteratedDeriv (localCellShare a S' R' V' Y') U' A' e' =
        localIteratedDeriv (localCellShare a S R V Y) U₂ (fun l => chartAtSameOffsets Y Y' (A' l)) e := by
    intro n A' e e' he
    unfold localIteratedDeriv
    have hfun : (fun t : Fin n → ℝ =>
        localCellShare a S' R' V' Y' (chartShiftAlong U' A' t) (topVariationAlong e' t)) =
        fun t => localCellShare a S R V Y
          (chartShiftAlong U₂ (fun l => chartAtSameOffsets Y Y' (A' l)) t) (topVariationAlong e t) := by
      funext t
      rw [← AgreeingPairShares.chartAtSameOffsets_chartShiftAlong]
      refine (SameOffsetShares.localCellShare_eq hR T a V V' _ _ _ fun b hbS hbw => ?_).symm
      have hbt := AgreeingPairShares.mem_topBondsMeetingCell_of_bondWeight_ne_zero hbS hbw
      show expUnit (topVariationAlong e t b.1 b.2) * V b.1 b.2 =
        expUnit (topVariationAlong e' t (siteAtSameOffset Y Y' b.1) b.2) * V' (siteAtSameOffset Y Y' b.1) b.2
      rw [hVb b hbt]
      congr 2
      simp only [topVariationAlong]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [he l b hbt, AgreeingPairShares.siteAtSameOffset_eq_cellAtSameOffset]
    rw [hfun]
  have hsame0 : localCellShare a S' R' V' Y' U' (fun _ _ => 0) = localCellShare a S R V Y U₂ (fun _ _ => 0) := by
    have := hsame (n := 0) (fun l => l.elim0) (fun l => l.elim0) (fun l => l.elim0) (fun l => l.elim0)
    rwa [YangMills.Construction.ChartCoordinates.localIteratedDeriv_zero,
      YangMills.Construction.ChartCoordinates.localIteratedDeriv_zero] at this
  have hK1 := hCk 1
  have hK2 := hCk 2
  have hsum0 : 0 ≤ s + n₁ + n₂ := by positivity
  have hval : |localCellShare a S R V Y U (fun _ _ => 0) - localCellShare a S' R' V' Y' U' fun _ _ => 0| ≤
      2 * Ck 1 * (s + n₁ + n₂) * localNorm S R D (oneSiteWeights F) Y := by
    rw [hsame0]
    have h := YangMills.Construction.ChartCoordinates.abs_evaluationIteratedDeriv_sub_le_of_segment (U := U₂) (D := D) hLoc
      (fun l : Fin 0 => l.elim0) (fun l : Fin 0 => l.elim0)
      (K := 2 * Ck 1 * (s + n₁ + n₂) * localNorm S R D (oneSiteWeights F) Y) (fun ρ hρ => by
        have h3 := (hloc' _ (hsegc ρ hρ)).2.2 1 (Fin.cons D fun l : Fin 0 => l.elim0)
          (Fin.cons 0 fun l : Fin 0 => l.elim0) rfl
        rw [Real.norm_eq_abs, YangMills.Construction.ChartCoordinates.prod_localDirectionSize_cons] at h3
        refine h3.trans ?_
        simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        have h4 := hseg ρ hρ
        nlinarith)
    rw [YangMills.Construction.ChartCoordinates.localIteratedDeriv_zero,
      YangMills.Construction.ChartCoordinates.localIteratedDeriv_zero, hend] at h
    exact h
  have hsmall : s + n₁ + n₂ ≤ 1 := by linarith
  have hCmk : ∀ k, Ck (k + 1) ≤ Cm k ∧ Ck k ≤ Cm k ∧ 2 * Ck 1 ≤ Cm k ∧ Ck 2 ≤ Cm k := fun k => by
    have h3 := hCk (k + 1)
    have h4 := hCk k
    rw [hCmv]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> show _ ≤ 2 * Ck 1 + 2 * Ck 2 + Ck (k + 1) + Ck k <;> linarith
  have hDn0 : 0 ≤ localNorm S R D (oneSiteWeights F) Y := Real.sqrt_nonneg _
  have hfirst : ∀ {n : ℕ} (A : Fin n → ChainChart F) (e : Fin n → F.Site F.top → Fin 4 → imaginaryQuaternions),
      |localIteratedDeriv (localCellShare a S R V Y) U A e -
          localIteratedDeriv (localCellShare a S R V Y) U₂ A e| ≤
        Ck (n + 1) * (localNorm S R D (oneSiteWeights F) Y *
          ∏ l, localDirectionSize S R (topBondsMeetingCell S Y) Y (A l) (e l)) := by
    intro n A e
    have h := YangMills.Construction.ChartCoordinates.abs_evaluationIteratedDeriv_sub_le_of_segment (U := U₂) (D := D)
      hLoc A e
      (K := Ck (n + 1) * (localNorm S R D (oneSiteWeights F) Y *
        ∏ l, localDirectionSize S R (topBondsMeetingCell S Y) Y (A l) (e l)))
      (fun ρ hρ => by
        have h3 := (hLoc ρ hρ).iteratedDeriv_le (n + 1) (Fin.cons D A) (Fin.cons 0 e)
        rwa [Real.norm_eq_abs, YangMills.Construction.ChartCoordinates.prod_localDirectionSize_cons] at h3)
    rwa [hend] at h
  refine ⟨⟨?_, fun n A A' e e' hn he => ?_⟩, ?_, fun n A A' e e' hn he => ?_⟩
  · rw [Real.norm_eq_abs, hgap]
    refine hval.trans ?_
    have h3 := (hCmk 0).2.2.1
    calc 2 * Ck 1 * (s + n₁ + n₂) * localNorm S R D (oneSiteWeights F) Y
        ≤ 2 * Ck 1 * 1 * localNorm S R D (oneSiteWeights F) Y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall (by positivity)) hDn0
      _ ≤ Cm 0 * localNorm S R D (oneSiteWeights F) Y := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right h3 hDn0
  · rw [hsame A' e e' he, Real.norm_eq_abs]
    set P := ∏ l, localDirectionSize S R (topBondsMeetingCell S Y) Y (A l) (e l) with hPd
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun l _ =>
      YangMills.Construction.ChartCoordinates.localDirectionSize_nonneg _ _
    have h1 := hfirst A e
    have h2 := YangMills.Construction.ChartCoordinates.abs_evaluationIteratedDeriv_sub_le hL₂ hCk A
      (fun l => chartAtSameOffsets Y Y' (A' l)) e
    set Q := ∑ l, localNorm S R (chartMove (A l) (chartAtSameOffsets Y Y' (A' l)) (-1)) (oneSiteWeights F) Y *
      ∏ l' ∈ Finset.univ.erase l, (localDirectionSize S R (topBondsMeetingCell S Y) Y (A l') (e l') +
        localNorm S R (chartMove (A l') (chartAtSameOffsets Y Y' (A' l')) (-1)) (oneSiteWeights F) Y) with hQd
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun l _ => mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg fun l' _ =>
      add_nonneg (YangMills.Construction.ChartCoordinates.localDirectionSize_nonneg _ _) (Real.sqrt_nonneg _))
    have hDP : 0 ≤ localNorm S R D (oneSiteWeights F) Y * P := mul_nonneg hDn0 hP0
    have htri := abs_sub_le (localIteratedDeriv (localCellShare a S R V Y) U A e)
      (localIteratedDeriv (localCellShare a S R V Y) U₂ A e)
      (localIteratedDeriv (localCellShare a S R V Y) U₂ (fun l => chartAtSameOffsets Y Y' (A' l)) e)
    have h3 : Ck (n + 1) * (localNorm S R D (oneSiteWeights F) Y * P) ≤
        Cm n * (localNorm S R D (oneSiteWeights F) Y * P) :=
      mul_le_mul_of_nonneg_right (hCmk n).1 hDP
    have h4 : Ck n * Q ≤ Cm n * Q := mul_le_mul_of_nonneg_right (hCmk n).2.1 hQ0
    have e9 : Cm n * (offsetChartGapNorm S R Y Y Y' U U' * P + ∑ l, offsetChartGapNorm S R Y Y Y' (A l) (A' l) *
        ∏ l' ∈ Finset.univ.erase l, (localDirectionSize S R (topBondsMeetingCell S Y) Y (A l') (e l') +
          offsetChartGapNorm S R Y Y Y' (A l') (A' l'))) =
        Cm n * (localNorm S R D (oneSiteWeights F) Y * P) + Cm n * Q := by
      rw [← mul_add]
      rfl
    rw [e9]
    linarith
  · rw [hgap]
    exact hval.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCmk 0).2.2.1 hsum0) hDn0)
  · subst hn
    rw [hsame A' e e' he, Real.norm_eq_abs]
    set P := ∏ l, localDirectionSize S R (topBondsMeetingCell S Y) Y (A l) (e l) with hPd
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun l _ =>
      YangMills.Construction.ChartCoordinates.localDirectionSize_nonneg _ _
    have h1 := hfirst A e
    have h2 := YangMills.Construction.ChartCoordinates.localIteratedDeriv_sub_of_one hL₂ A
      (fun l => chartAtSameOffsets Y Y' (A' l)) e
    have hU₂c : localNorm S R U₂ (oneSiteWeights F) Y ≤ c₁ := by
      have := hsegc 0 ⟨le_rfl, zero_le_one⟩
      rwa [hstart] at this
    have h3 := (hloc' U₂ hU₂c).2.2 1 (fun l => chartMove (A l) (chartAtSameOffsets Y Y' (A' l)) (-1))
      (fun _ => 0) rfl
    rw [← h2, Real.norm_eq_abs] at h3
    have hG : ∏ l : Fin 1, localDirectionSize S R (topBondsMeetingCell S Y) Y
        (chartMove (A l) (chartAtSameOffsets Y Y' (A' l)) (-1)) 0 =
        ∑ l : Fin 1, offsetChartGapNorm S R Y Y Y' (A l) (A' l) := by
      simp only [Fin.prod_univ_one, Fin.sum_univ_one, YangMills.Construction.ChartCoordinates.localDirectionSize_zero]
      rfl
    rw [hG] at h3
    have hG0 : 0 ≤ ∑ l : Fin 1, offsetChartGapNorm S R Y Y Y' (A l) (A' l) :=
      Finset.sum_nonneg fun l _ => Real.sqrt_nonneg _
    have htri := abs_sub_le (localIteratedDeriv (localCellShare a S R V Y) U A e)
      (localIteratedDeriv (localCellShare a S R V Y) U₂ A e)
      (localIteratedDeriv (localCellShare a S R V Y) U₂ (fun l => chartAtSameOffsets Y Y' (A' l)) e)
    have hDP : 0 ≤ localNorm S R D (oneSiteWeights F) Y * P := mul_nonneg hDn0 hP0
    have h4 : Ck 2 * (localNorm S R D (oneSiteWeights F) Y * P) ≤
        Cm 1 * (localNorm S R D (oneSiteWeights F) Y * P) :=
      mul_le_mul_of_nonneg_right (hCmk 1).2.2.2 hDP
    have h5 : Ck 1 * (s + localNorm S R U₂ (oneSiteWeights F) Y) *
        ∑ l : Fin 1, offsetChartGapNorm S R Y Y Y' (A l) (A' l) ≤
        Cm 1 * (s + n₁ + n₂) * ∑ l : Fin 1, offsetChartGapNorm S R Y Y Y' (A l) (A' l) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul ((hCmk 1).2.1) (by linarith)
        (add_nonneg hs.le (Real.sqrt_nonneg _)) (hCm 1)) hG0
    have e9 : Cm 1 * (offsetChartGapNorm S R Y Y Y' U U' * P +
        (s + n₁ + n₂) * ∑ l : Fin 1, offsetChartGapNorm S R Y Y Y' (A l) (A' l)) =
        Cm 1 * (localNorm S R D (oneSiteWeights F) Y * P) +
          Cm 1 * (s + n₁ + n₂) * ∑ l : Fin 1, offsetChartGapNorm S R Y Y Y' (A l) (A' l) := by
      rw [hgap]
      ring
    rw [e9]
    have e2 : Ck (1 + 1) = Ck 2 := rfl
    rw [e2] at h1
    linarith
end YangMills.Construction.BlockAverages
end
