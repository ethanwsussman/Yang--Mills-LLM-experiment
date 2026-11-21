import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfCores
import YangMills.Construction.ClusterExpansionOfAStep.SumsOverATorusProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.CoreColumns
open TorusFields TorusLumps
variable {n : ℕ} [NeZero n]
theorem setGap_attained {X X' : Finset (TorusSite n)} (hX : X.Nonempty) (hX' : X'.Nonempty) :
    ∃ y ∈ X, ∃ y' ∈ X', supDist y y' = setGap X X' := by
  have hne : {d | ∃ y ∈ X, ∃ y' ∈ X', supDist y y' = d}.Nonempty := by
    obtain ⟨y, hy⟩ := hX
    obtain ⟨y', hy'⟩ := hX'
    exact ⟨_, y, hy, y', hy', rfl⟩
  exact Nat.sInf_mem hne
theorem setGap_le {X X' : Finset (TorusSite n)} {y y' : TorusSite n} (hy : y ∈ X) (hy' : y' ∈ X') :
    setGap X X' ≤ supDist y y' :=
  Nat.sInf_le ⟨y, hy, y', hy', rfl⟩
theorem supDist_le_siteDiameter {S : Finset (TorusSite n)} {y z : TorusSite n} (hy : y ∈ S) (hz : z ∈ S) :
    supDist y z ≤ siteDiameter S := by
  unfold siteDiameter
  exact (Finset.le_sup (f := fun z => supDist y z) hz).trans
    (Finset.le_sup (f := fun y => S.sup fun z => supDist y z) hy)
theorem setGap_singleton_le (Y : TorusSite n) {X X' : Finset (TorusSite n)} (hX : X.Nonempty) (hX' : X'.Nonempty) :
    setGap {Y} X' ≤ setGap {Y} X + siteDiameter X + setGap X X' := by
  obtain ⟨y₀, hy₀, y, hy, e⟩ := setGap_attained (Finset.singleton_nonempty Y) hX
  obtain ⟨u, hu, v, hv, e'⟩ := setGap_attained hX hX'
  have hY : y₀ = Y := Finset.mem_singleton.mp hy₀
  subst hY
  have h1 : setGap {y₀} X' ≤ supDist y₀ v := setGap_le (Finset.mem_singleton_self _) hv
  have h2 := supDist_triangle y₀ y v
  have h3 := supDist_triangle y u v
  have h4 := supDist_le_siteDiameter hy hu
  omega
theorem card_supDist_ball_le (y' : TorusSite n) (m : ℕ) :
    (((Finset.univ.filter fun y : TorusSite n => supDist y y' ≤ m).card : ℕ) : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 4 := by apply _root_.YangMills.Construction.TorusSums.card_supDist_ball_le <;> assumption
theorem sum_exp_neg_supDist_le (y' : TorusSite n) {κ : ℝ} (hκ : 0 < κ) :
    ∑ y : TorusSite n, Real.exp (-(κ * (supDist y y' : ℝ))) ≤ (2 / (1 - Real.exp (-(κ / 4)))) ^ 4 := by apply _root_.YangMills.Construction.TorusSums.sum_exp_neg_supDist_le <;> assumption
theorem columnSumBound_holds : ColumnSumBound := by
  intro n _ I _ core z c Y rt e Dn hrt hne hz hsum hc j
  classical
  set κ0 : ℝ := rt / 2 ^ 6 with hκ0
  set κ1 : ℝ := 7 * rt / 2 ^ 6 with hκ1
  have hκ1p : 0 < κ1 := by positivity
  set T : I → ℝ := fun i => ((core i).card : ℝ) with hT
  have hT1 : ∀ i, 1 ≤ T i := fun i => by
    simp only [hT]
    exact_mod_cast Finset.card_pos.mpr (hne i)
  set g : I → ℝ := fun i => z i * T i ^ 4 * Real.exp (2 * rt * (siteDiameter (core i) : ℝ)) with hg
  have hg0 : ∀ i, 0 ≤ g i := fun i => by
    have := hz i
    have := hT1 i
    simp only [hg]
    positivity
  set W : ℝ := Real.exp (-(κ0 * (setGap {Y} (core j) : ℝ))) with hW
  set h : ℕ → ℝ := fun D => (if D ≤ Dn then Real.exp (κ0 * Dn) else 0) + Real.exp (-(κ1 * D)) with hh
  have hh0 : ∀ D, 0 ≤ h D := fun D => by
    simp only [hh]
    split_ifs <;> positivity
  have he0 : 0 ≤ e := by
    obtain ⟨y, _⟩ := hne j
    refine le_trans (Finset.sum_nonneg fun i _ => ?_) (hsum y)
    exact hg0 i
  have hterm : ∀ i, coreWeight κ0 Y (core i) * c i j ≤ W * (8 * g i * h (setGap (core i) (core j))) := by
    intro i
    set D : ℕ := setGap (core i) (core j) with hD
    set dm : ℕ := siteDiameter (core i) with hdm
    set A : ℝ := Real.exp (-(κ0 * (setGap {Y} (core i) : ℝ))) with hA
    set E1 : ℝ := Real.exp (κ0 * dm) with hE1
    set ED : ℝ := Real.exp (κ0 * D) with hED
    have hzi := hz i
    have hTi := hT1 i
    have hAle : A ≤ W * E1 * ED := by
      have htri := setGap_singleton_le Y (hne i) (hne j)
      have htri' : (setGap {Y} (core j) : ℝ) ≤ setGap {Y} (core i) + dm + D := by
        exact_mod_cast htri
      rw [hA, hW, hE1, hED, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      nlinarith
    have hE1E : E1 ≤ Real.exp (2 * rt * (dm : ℝ)) := by
      rw [hE1, Real.exp_le_exp]
      have : (0 : ℝ) ≤ dm := Nat.cast_nonneg _
      rw [hκ0]
      nlinarith
    have hcw : coreWeight κ0 Y (core i) = T i * A := rfl
    have hT4 : T i ≤ T i ^ 4 := le_self_pow₀ hTi (by norm_num)
    have hT24 : T i ^ 2 ≤ T i ^ 4 := pow_le_pow_right₀ hTi (by norm_num)
    have hgi : g i = z i * T i ^ 4 * Real.exp (2 * rt * (dm : ℝ)) := rfl
    rw [hcw, hgi]
    rcases hc i j with ⟨hnear, hci⟩ | hci
    · have hnear' : D ≤ Dn := hnear
      have hhD : ED ≤ h D := by
        simp only [hh, if_pos hnear']
        have h1 : ED ≤ Real.exp (κ0 * Dn) := by
          rw [hED, Real.exp_le_exp]
          have : (D : ℝ) ≤ Dn := by exact_mod_cast hnear'
          nlinarith
        linarith [Real.exp_pos (-(κ1 * (D : ℝ)))]
      calc T i * A * c i j ≤ T i * A * (4 * z i) := by gcongr
        _ ≤ T i * (W * E1 * ED) * (4 * z i) := by gcongr
        _ = W * (4 * (z i * T i * E1) * ED) := by ring
        _ ≤ W * (8 * (z i * T i ^ 4 * Real.exp (2 * rt * (dm : ℝ))) * h D) := by
            gcongr
            norm_num
    · set G0 : ℝ := Real.exp (-(rt * (D : ℝ) / 8)) with hG0
      have hci' : c i j ≤ 8 * z i * (T i * G0) :=
        hci.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))
      have hhD : ED * G0 ≤ h D := by
        have h1 : ED * G0 = Real.exp (-(κ1 * (D : ℝ))) := by
          rw [hED, hG0, ← Real.exp_add]
          congr 1
          rw [hκ0, hκ1]
          ring
        rw [h1]
        simp only [hh]
        split_ifs
        · linarith [Real.exp_pos (κ0 * (Dn : ℝ))]
        · linarith
      calc T i * A * c i j ≤ T i * A * (8 * z i * (T i * G0)) := by gcongr
        _ ≤ T i * (W * E1 * ED) * (8 * z i * (T i * G0)) := by gcongr
        _ = W * (8 * (z i * T i ^ 2 * E1) * (ED * G0)) := by ring
        _ ≤ W * (8 * (z i * T i ^ 4 * Real.exp (2 * rt * (dm : ℝ))) * h D) := by
            gcongr
  have hgap : ∀ i, g i * h (setGap (core i) (core j)) ≤
      ∑ y' ∈ core j, ∑ y : TorusSite n, (if y ∈ core i then g i else 0) * h (supDist y y') := by
    intro i
    obtain ⟨u, hu, v, hv, euv⟩ := setGap_attained (hne i) (hne j)
    have hnn : ∀ (y y' : TorusSite n), 0 ≤ (if y ∈ core i then g i else 0) * h (supDist y y') := by
      intro y y'
      have := hg0 i
      have := hh0 (supDist y y')
      split_ifs <;> positivity
    calc g i * h (setGap (core i) (core j)) = (if u ∈ core i then g i else 0) * h (supDist u v) := by
          rw [if_pos hu, euv]
      _ ≤ ∑ y : TorusSite n, (if y ∈ core i then g i else 0) * h (supDist y v) :=
          Finset.single_le_sum (f := fun y => (if y ∈ core i then g i else 0) * h (supDist y v))
            (fun y _ => hnn y v) (Finset.mem_univ u)
      _ ≤ _ := Finset.single_le_sum
            (f := fun y' => ∑ y : TorusSite n, (if y ∈ core i then g i else 0) * h (supDist y y'))
            (fun y' _ => Finset.sum_nonneg fun y _ => hnn y y') hv
  have hsite : ∀ y' : TorusSite n, ∑ y : TorusSite n, h (supDist y y') ≤ columnConstant rt Dn := by
    intro y'
    have h1 : ∑ y : TorusSite n, (if supDist y y' ≤ Dn then Real.exp (κ0 * Dn) else 0) ≤
        Real.exp (κ0 * Dn) * (2 * (Dn : ℝ) + 1) ^ 4 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (card_supDist_ball_le y' Dn) (Real.exp_pos _).le
    have h2 := sum_exp_neg_supDist_le y' hκ1p
    have h3 : κ1 / 4 = 7 * rt / 2 ^ 8 := by
      rw [hκ1]
      ring
    rw [h3] at h2
    simp only [hh, Finset.sum_add_distrib, columnConstant]
    exact add_le_add h1 h2
  have hswap : ∑ i, ∑ y' ∈ core j, ∑ y : TorusSite n, (if y ∈ core i then g i else 0) * h (supDist y y') ≤
      (core j).card * (e * columnConstant rt Dn) := by
    rw [Finset.sum_comm]
    have : ∀ y' ∈ core j, ∑ i, ∑ y : TorusSite n, (if y ∈ core i then g i else 0) * h (supDist y y') ≤
        e * columnConstant rt Dn := by
      intro y' _
      rw [Finset.sum_comm]
      calc ∑ y : TorusSite n, ∑ i, (if y ∈ core i then g i else 0) * h (supDist y y')
          = ∑ y : TorusSite n, (∑ i with y ∈ core i, g i) * h (supDist y y') := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [← Finset.sum_mul, Finset.sum_filter]
        _ ≤ ∑ y : TorusSite n, e * h (supDist y y') :=
            Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hsum y) (hh0 _)
        _ = e * ∑ y : TorusSite n, h (supDist y y') := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hsite y') he0
    calc _ ≤ ∑ _y' ∈ core j, e * columnConstant rt Dn := Finset.sum_le_sum this
      _ = _ := by simp
  calc ∑ i, coreWeight κ0 Y (core i) * c i j
      ≤ ∑ i, W * (8 * g i * h (setGap (core i) (core j))) := Finset.sum_le_sum fun i _ => hterm i
    _ = W * 8 * ∑ i, g i * h (setGap (core i) (core j)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ W * 8 * ∑ i, ∑ y' ∈ core j, ∑ y : TorusSite n, (if y ∈ core i then g i else 0) * h (supDist y y') := by
        gcongr with i
        exact hgap i
    _ ≤ W * 8 * ((core j).card * (e * columnConstant rt Dn)) := by gcongr
    _ = coreWeight κ0 Y (core j) * (8 * e * columnConstant rt Dn) := by
        simp only [coreWeight, hW]
        ring
end YangMills.Construction.CoreColumns
end
