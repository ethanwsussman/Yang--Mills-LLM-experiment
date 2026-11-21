import YangMills.Construction.Continuum.CompactSetsMeetFinitelyManyPieces
import YangMills.Construction.Continuum.LeastSupDistanceOfPointsOfPowersOfFourSpace
import YangMills.Construction.Continuum.PiecesOfTheShellsAndTheirBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PieceFiniteness
open ConfigSpace ShellPieces PieceScales ShellPieceBounds
variable {n : ℕ}
theorem dyadicScale_eq (j : ℕ) : dyadicScale j = ((2 : ℝ) ^ j)⁻¹ := by
  simp [dyadicScale, zpow_neg]
theorem dyadicScale_pos (j : ℕ) : 0 < dyadicScale j := by
  rw [dyadicScale_eq]; positivity
theorem pieceSide_pos (j : ℕ) : 0 < pieceSide j :=
  mul_pos isSideConstant_sideConstant.1 (dyadicScale_pos j)
theorem pieceSide_antitone {k m : ℕ} (hkm : k ≤ m) : pieceSide m ≤ pieceSide k := by
  refine mul_le_mul_of_nonneg_left ?_ isSideConstant_sideConstant.1.le
  rw [dyadicScale_eq, dyadicScale_eq]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hkm)
theorem mem_openBox_and_near_pieceCentre {j : ℕ} {z : LatticePt n} {x : Config n}
    (hz : PieceProperties j z) (hx : piece j z x ≠ 0) :
    x ∈ openBox j z ∧ ∀ i c, |x i c - pieceCentre j z i c| ≤ 3 / 8 * pieceSide j := by
  have hs : x ∈ tsupport (piece j z) := subset_tsupport _ (Function.mem_support.2 hx)
  have hb := hz.2.2.1 hs
  refine ⟨hz.2.2.2.1 hb, ?_⟩
  obtain ⟨w, hw, hwx⟩ := hb
  intro i c
  have hxw : x i c = pieceCentre j z i c + w i c := by rw [← hwx]; rfl
  rw [hxw, add_sub_cancel_left]
  exact abs_le.2 (hw i c)
theorem abs_latticePt_le {j J : ℕ} {z : LatticePt n} {x : Config n} {R : ℝ} {i : Fin n}
    {c : Fin 4} (hjJ : j ≤ J) (hR : |x i c| ≤ R)
    (hc : |x i c - pieceCentre j z i c| ≤ 3 / 8 * pieceSide j) :
    |(z i c : ℝ)| ≤ 2 * R / pieceSide J + 1 := by
  have hsj := pieceSide_pos j
  have hsJ := pieceSide_pos J
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hR
  have h1 : |pieceCentre j z i c| ≤ R + 3 / 8 * pieceSide j := by
    have := abs_sub_abs_le_abs_sub (pieceCentre j z i c) (x i c)
    rw [abs_sub_comm (pieceCentre j z i c)] at this
    linarith
  have h2 : |pieceCentre j z i c| = 1 / 2 * pieceSide j * |(z i c : ℝ)| := by
    simp only [pieceCentre, abs_mul, abs_of_pos hsj]
    norm_num
  rw [h2] at h1
  have h3 : |(z i c : ℝ)| ≤ (2 * R + 3 / 4 * pieceSide j) / pieceSide j := by
    rw [le_div_iff₀ hsj]; linarith
  have h4 : (2 * R + 3 / 4 * pieceSide j) / pieceSide j = 2 * R / pieceSide j + 3 / 4 := by
    field_simp
  have h5 : 2 * R / pieceSide j ≤ 2 * R / pieceSide J :=
    div_le_div_of_nonneg_left (by linarith) hsJ (pieceSide_antitone hjJ)
  linarith
theorem meetingPieces_finite (hsep : MinSeparation.mainClaim) (hpieces : ShellPiecesBound)
    (hn : 2 ≤ n) (S : Set (Config n))
    (hS : S ⊆ TestFunctions.injectiveTuples (Fin 4 → ℝ) n) (hc : IsCompact S) :
    (meetingPieces S).Finite := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp [meetingPieces]
  obtain ⟨hLip, hDiag, hComp⟩ := hsep.1 n hn
  obtain ⟨hfin, -, hcont⟩ := hLip
  obtain ⟨x₀, hx₀, hmin⟩ := hc.exists_isMinOn hne hcont.continuousOn
  have hε : 0 < (minSeparation x₀).toReal := by
    refine ENNReal.toReal_pos (fun h0 => ?_) (hfin x₀)
    have hd : x₀ ∈ {x | minSeparation x = 0} := h0
    rw [← hDiag.1] at hd
    have hnd := hS hx₀
    rw [← hComp.1] at hnd
    exact hnd hd
  obtain ⟨R, hR⟩ := hc.isBounded.exists_norm_le
  have hco : ∀ x ∈ S, ∀ i c, |x i c| ≤ R := fun x hx i c => by
    have e₁ := norm_le_pi_norm (x i) c
    have e₂ := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at e₁
    exact (e₁.trans e₂).trans (hR x hx)
  have hP := hpieces n (by omega)
  have hCm : 0 < pairDistConst := by
    have := isSideConstant_sideConstant.1
    unfold pairDistConst
    linarith
  set J : ℕ := ⌈pairDistConst / (minSeparation x₀).toReal⌉₊ with hJ
  have hjJ : ∀ p ∈ meetingPieces S, p.1 ≤ J := by
    rintro ⟨j, z⟩ ⟨hp, x, hxS, hx⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact Nat.zero_le _
    have hbox := (mem_openBox_and_near_pieceCentre (hP.2.1 j z) hx).1
    have hb := hP.2.2.2.2.1 (j, z) hp
    have e₁ := (hb.2.2.2.1 hj x hbox).1
    have e₂ : (minSeparation x).toReal ≤ pairDistConst * dyadicScale j :=
      ENNReal.toReal_le_of_le_ofReal (mul_pos hCm (dyadicScale_pos j)).le e₁
    have e₃ : (minSeparation x₀).toReal ≤ pairDistConst * dyadicScale j :=
      (isMinOn_iff.1 hmin x hxS).trans e₂
    rw [dyadicScale_eq, ← div_eq_mul_inv, le_div_iff₀ (by positivity)] at e₃
    have e₄ : (2 : ℝ) ^ j ≤ pairDistConst / (minSeparation x₀).toReal := by
      rw [le_div_iff₀ hε]; linarith
    have e₅ : (j : ℝ) ≤ (2 : ℝ) ^ j := by
      exact_mod_cast Nat.lt_two_pow_self.le
    have e₆ : (j : ℝ) ≤ (J : ℝ) := (e₅.trans e₄).trans (Nat.le_ceil _)
    exact_mod_cast e₆
  set M : ℤ := ⌈2 * R / pieceSide J + 1⌉ with hM
  refine ((Set.finite_Iic J).prod
    (Set.finite_Icc (fun _ _ => -M : LatticePt n) (fun _ _ => M))).subset ?_
  rintro ⟨j, z⟩ hp
  have hj := hjJ _ hp
  obtain ⟨-, x, hxS, hx⟩ := hp
  refine ⟨hj, ?_, ?_⟩ <;> intro i <;> intro c
  all_goals
    have e₁ := abs_latticePt_le hj (hco x hxS i c)
      ((mem_openBox_and_near_pieceCentre (hP.2.1 j z) hx).2 i c)
    have e₂ : 2 * R / pieceSide J + 1 ≤ (M : ℝ) := Int.le_ceil _
    have e₃ := abs_le.1 (e₁.trans e₂)
  · have : -M ≤ z i c := by exact_mod_cast e₃.1
    exact this
  · have : z i c ≤ M := by exact_mod_cast e₃.2
    exact this
theorem compactMeetsFinitelyMany_holds (hsep : MinSeparation.mainClaim)
    (hpieces : ShellPiecesBound) : CompactMeetsFinitelyMany := by
  intro n hn
  refine ⟨fun S hS hc => meetingPieces_finite hsep hpieces hn S hS hc, fun Ψ hΨ => ?_⟩
  obtain ⟨-, hcs, hsupp⟩ := hΨ
  have hsub : supportPieces Ψ ⊆ meetingPieces (tsupport Ψ) := by
    rintro p ⟨hp, hne⟩
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
    have hx' : (piece p.1 p.2 x : ℂ) * Ψ x ≠ 0 := hx
    refine ⟨hp, x, subset_tsupport _ (Function.mem_support.2 (right_ne_zero_of_mul hx')), ?_⟩
    exact_mod_cast left_ne_zero_of_mul hx'
  have hfin := (meetingPieces_finite hsep hpieces hn _ hsupp hcs).subset hsub
  refine ⟨hfin, ?_⟩
  funext x
  rw [Finset.sum_apply]
  by_cases hΨx : Ψ x = 0
  · rw [hΨx]
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    simp [pieceMul, hΨx]
  have hxd := hsupp (subset_tsupport _ (Function.mem_support.2 hΨx))
  have hone := ((hpieces n (by omega)).2.2.1 x hxd).2
  have hone' : ∑ p ∈ hfin.toFinset, piece p.1 p.2 x = 1 := by
    rw [← hone, tsum_subtype (activeIndices n) (fun p => piece p.1 p.2 x),
      tsum_eq_sum (s := hfin.toFinset)]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [Set.indicator_of_mem ((Set.Finite.mem_toFinset hfin).1 hp).1]
    · intro p hp
      by_cases hpi : p ∈ activeIndices n
      · rw [Set.indicator_of_mem hpi]
        by_contra hne
        refine hp ((Set.Finite.mem_toFinset hfin).2 ⟨hpi, fun h0 => ?_⟩)
        have e : (piece p.1 p.2 x : ℂ) * Ψ x = 0 := congrFun h0 x
        rcases mul_eq_zero.1 e with e | e
        · exact hne (by exact_mod_cast e)
        · exact hΨx e
      · rw [Set.indicator_of_notMem hpi]
  calc Ψ x = ((∑ p ∈ hfin.toFinset, piece p.1 p.2 x : ℝ) : ℂ) * Ψ x := by
        rw [hone']; simp
    _ = ∑ p ∈ hfin.toFinset, pieceMul p Ψ x := by
        rw [Complex.ofReal_sum, Finset.sum_mul]
        rfl
end YangMills.Construction.PieceFiniteness
end
