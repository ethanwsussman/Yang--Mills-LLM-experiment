import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import YangMills.Construction.SixteenPointsOnASmallTorus.LevelsOfARadius
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmallTorusCopies
open TorusLumps StepReturn ResponseInTheExpansion
private theorem one_le_clusterRange {x : ℝ} (hx : 0 < x) : 1 ≤ clusterRange x :=
  Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hx _)
private theorem clusterRange_mono {x x' : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x') :
    clusterRange x ≤ clusterRange x' := by apply _root_.YangMills.Construction.WilsonExpansion.clusterRange_mono <;> assumption
private theorem le_clusterRange {n : ℕ} {x : ℝ} (hnx : (n : ℝ) ^ 100 ≤ x) : n ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
private theorem clusterRange_le_two_mul {x x' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (hxx : x ≤ 2 * x') :
    clusterRange x ≤ 2 * clusterRange x' := by
  have hpow : x ≤ (2 : ℝ) ^ 100 * x' :=
    hxx.trans (mul_le_mul_of_nonneg_right (by norm_num) hx')
  have hroot : x ^ ((1 : ℝ) / 100) ≤ 2 * x' ^ ((1 : ℝ) / 100) := by
    calc x ^ ((1 : ℝ) / 100) ≤ ((2 : ℝ) ^ 100 * x') ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow hx hpow (by norm_num)
      _ = 2 * x' ^ ((1 : ℝ) / 100) := by
          rw [Real.mul_rpow (by positivity) hx', ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
  have hceil : x' ^ ((1 : ℝ) / 100) ≤ (clusterRange x' : ℝ) := Nat.le_ceil _
  refine Nat.ceil_le.mpr ?_
  push_cast
  linarith
abbrev _root_.YangMills.SharedProofs.p21096 := @clusterRange_le_two_mul
private theorem expansionCoupling_of_returns {p : StepParameters} (hret : ExpansionReturnsAt p) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hx : p.y₁ ≤ x) (hD : HasExpansion p t x D) :
    HasExpansion p (t + 1) (expansionCoupling p t x D) (kernelImage p x D) ∧
      |expansionCoupling p t x D - x| ≤ 2 * p.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem couplingFlow_hasExpansion {p : StepParameters} (hret : ExpansionReturnsAt p) {β : ℝ}
    (hzero : HasExpansion p 0 β (wilsonWeight β)) (K : ℕ)
    (hfloor : ∀ j ≤ K, p.y₁ ≤ (couplingFlow p β j).1) :
    ∀ t ≤ K, HasExpansion p t (couplingFlow p β t).1 (couplingFlow p β t).2 := by
  intro t
  induction t with
  | zero => exact fun _ => hzero
  | succ t ih =>
    intro ht
    exact (expansionCoupling_of_returns hret (hfloor t (by omega)) (ih (by omega))).1
private theorem lt_and_room_of_fits {L r ρ : ℝ} {K κ t : ℕ} (hL1 : 1 ≤ L) (hr : 1 ≤ r)
    (hfit : 2 ^ 11 * r * L ^ ((t : ℤ) - (K : ℤ)) ≤ ρ)
    (hρ : ρ ≤ L ^ κ * L ^ (((0 : ℕ) : ℤ) - (K : ℤ)) / 4) :
    t < κ ∧ 2 ^ 13 * r ≤ L ^ (κ - t) := by
  have hL : 0 < L := by linarith
  have hLt : 0 < L ^ t := pow_pos hL t
  have hsub : L ^ ((t : ℤ) - (K : ℤ)) = L ^ t / L ^ K := by
    rw [zpow_sub₀ hL.ne', zpow_natCast, zpow_natCast]
  have hinv : L ^ (((0 : ℕ) : ℤ) - (K : ℤ)) = 1 / L ^ K := by
    rw [zpow_sub₀ hL.ne', zpow_natCast]
    simp
  rw [hsub] at hfit
  rw [hinv] at hρ
  have hchain : 2 ^ 11 * r * (L ^ t / L ^ K) ≤ L ^ κ * (1 / L ^ K) / 4 := hfit.trans hρ
  have hmain : 2 ^ 13 * r * L ^ t ≤ L ^ κ := by
    have hscaled := mul_le_mul_of_nonneg_right hchain (by positivity : (0 : ℝ) ≤ 4 * L ^ K)
    have hleft : 2 ^ 11 * r * (L ^ t / L ^ K) * (4 * L ^ K) = 2 ^ 13 * r * L ^ t := by
      field_simp
      ring
    have hright : L ^ κ * (1 / L ^ K) / 4 * (4 * L ^ K) = L ^ κ := by
      field_simp
    rwa [hleft, hright] at hscaled
  have htκ : t < κ := by
    by_contra hc
    have hle : L ^ κ ≤ L ^ t := pow_le_pow_right₀ hL1 (not_lt.mp hc)
    have hone : 2 ^ 13 * r * L ^ t ≤ 1 * L ^ t := by
      rw [one_mul]
      exact hmain.trans hle
    have hcontra : 2 ^ 13 * r ≤ 1 := le_of_mul_le_mul_right hone hLt
    linarith
  refine ⟨htκ, ?_⟩
  have hsplit : L ^ κ = L ^ (κ - t) * L ^ t := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at hmain
  exact le_of_mul_le_mul_right hmain hLt
theorem levelsBelowRadius : levelsBelowRadiusStatement := by
  unfold levelsBelowRadiusStatement HoldsOnParameterFamilies
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ hT _ _ _ _
  refine ⟨max (max 1 (2 * T.B)) (((T.side * T.n₀ : ℕ) : ℝ) ^ 100), ?_⟩
  intro y hy hret hW Ξ β K κ ρ hD _ _ hρl s hs
  have hy1 : 1 ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have hyB : 2 * T.B ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
  have hyn : ((T.side * T.n₀ : ℕ) : ℝ) ^ 100 ≤ y := (le_max_right _ _).trans hy
  have hL2 : 2 ≤ T.side := le_trans (by norm_num) hT.L_ge
  have hL2R : (2 : ℝ) ≤ (T.side : ℝ) := by exact_mod_cast hL2
  have hfloor : ∀ j ≤ K, y ≤ (couplingFlow (T.stepParameters y) β j).1 := hD.coupling_ge
  have hβ : y ≤ β := hfloor 0 (Nat.zero_le _)
  have hexp := couplingFlow_hasExpansion hret (hW β hβ) K hD.coupling_ge
  have hstep : ∀ t < K, |(couplingFlow (T.stepParameters y) β (t + 1)).1 -
      (couplingFlow (T.stepParameters y) β t).1| ≤ 2 * T.B :=
    fun t ht => (expansionCoupling_of_returns hret (hD.coupling_ge t ht.le) (hexp t ht.le)).2
  have hpass : ∀ t, t + 1 ≤ K → FitsAtLevel (T.stepParameters y) β K ρ (t + 1) →
      FitsAtLevel (T.stepParameters y) β K ρ t := by
    intro t ht hf
    have hx := hfloor t (by omega)
    have hx' := hfloor (t + 1) ht
    have hst := (abs_le.mp (hstep t (by omega))).1
    have htwice : (couplingFlow (T.stepParameters y) β t).1 ≤ 2 * (couplingFlow (T.stepParameters y) β (t + 1)).1 := by
      linarith
    have hr := clusterRange_le_two_mul (by linarith) (by linarith) htwice
    have hrR : rangeAtLevel (T.stepParameters y) β t ≤ 2 * rangeAtLevel (T.stepParameters y) β (t + 1) := by
      unfold rangeAtLevel
      exact_mod_cast hr
    have hrpos : 0 ≤ rangeAtLevel (T.stepParameters y) β (t + 1) := Nat.cast_nonneg _
    have hsp_succ : levelSpacing T.side K (t + 1) = (T.side : ℝ) * levelSpacing T.side K t := by
      unfold levelSpacing
      rw [show ((t + 1 : ℕ) : ℤ) - (K : ℤ) = 1 + ((t : ℤ) - (K : ℤ)) by push_cast; ring,
        zpow_add₀ (by linarith), zpow_one]
    have hsp : 0 ≤ levelSpacing T.side K t := zpow_nonneg (by linarith) _
    have hf' : 2 ^ 11 * rangeAtLevel (T.stepParameters y) β (t + 1) * levelSpacing T.side K (t + 1) ≤ ρ := hf
    show 2 ^ 11 * rangeAtLevel (T.stepParameters y) β t * levelSpacing T.side K t ≤ ρ
    rw [hsp_succ] at hf'
    have hLr : rangeAtLevel (T.stepParameters y) β t ≤ (T.side : ℝ) * rangeAtLevel (T.stepParameters y) β (t + 1) :=
      hrR.trans (mul_le_mul_of_nonneg_right hL2R hrpos)
    calc 2 ^ 11 * rangeAtLevel (T.stepParameters y) β t * levelSpacing T.side K t
        ≤ 2 ^ 11 * ((T.side : ℝ) * rangeAtLevel (T.stepParameters y) β (t + 1)) * levelSpacing T.side K t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLr (by norm_num)) hsp
      _ = 2 ^ 11 * rangeAtLevel (T.stepParameters y) β (t + 1) * ((T.side : ℝ) * levelSpacing T.side K t) := by ring
      _ ≤ ρ := hf'
  unfold radiusLevel at hs
  split_ifs at hs with hex
  have hs' := Option.some.inj hs
  classical
  have hsK : s ≤ K := by
    rw [← hs']
    exact Nat.findGreatest_le K
  have hfs : FitsAtLevel (T.stepParameters y) β K ρ s := by
    obtain ⟨t₀, ht₀, hf₀⟩ := hex
    rw [← hs']
    exact Nat.findGreatest_spec ht₀ hf₀
  have hdown : ∀ d t : ℕ, t + d = s → FitsAtLevel (T.stepParameters y) β K ρ t := by
    intro d
    induction d with
    | zero =>
      intro t ht
      have : t = s := by omega
      rw [this]
      exact hfs
    | succ d ih =>
      intro t ht
      exact hpass t (by omega) (ih (t + 1) (by omega))
  refine ⟨hsK, fun t ht => ?_⟩
  have hf : FitsAtLevel (T.stepParameters y) β K ρ t := hdown (s - t) t (by omega)
  have hx := hfloor t (by omega)
  have hr1 : (1 : ℝ) ≤ rangeAtLevel (T.stepParameters y) β t := by
    unfold rangeAtLevel
    exact_mod_cast one_le_clusterRange (by linarith)
  have hroom := lt_and_room_of_fits (L := (T.side : ℝ)) (r := rangeAtLevel (T.stepParameters y) β t) (ρ := ρ)
    (K := K) (κ := κ) (t := t) (by linarith) hr1 hf hρl
  refine ⟨hf, hroom.1, hroom.2, ?_, ?_⟩
  · exact Dvd.dvd.mul_left (dvd_pow_self _ (by have := hroom.1; omega)) 2
  · have hn : T.side * T.n₀ ≤ clusterRange y := le_clusterRange hyn
    have hm : clusterRange y ≤ clusterRange (couplingFlow (T.stepParameters y) β t).1 :=
      clusterRange_mono (by linarith) hx
    have hcast : ((T.side * T.n₀ : ℕ) : ℝ) ≤ (T.side : ℝ) ^ (κ - t) := by
      have hlow : ((T.side * T.n₀ : ℕ) : ℝ) ≤ rangeAtLevel (T.stepParameters y) β t := by
        unfold rangeAtLevel
        exact_mod_cast hn.trans hm
      have hgrow : rangeAtLevel (T.stepParameters y) β t ≤ 2 ^ 13 * rangeAtLevel (T.stepParameters y) β t := by
        linarith
      exact hlow.trans (hgrow.trans hroom.2)
    have hnat : T.side * T.n₀ ≤ T.side ^ (κ - t) := by exact_mod_cast hcast
    exact hnat.trans (Nat.le_mul_of_pos_left _ two_pos)
end YangMills.Construction.SmallTorusCopies
end
