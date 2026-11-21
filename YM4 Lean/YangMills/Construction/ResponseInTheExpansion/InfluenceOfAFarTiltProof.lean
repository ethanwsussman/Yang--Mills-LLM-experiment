import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfCoresProof
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.GasSumsAtABlockProof
import YangMills.Construction.ResponseInTheExpansion.InfluenceOfAFarTilt
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings StepGas TorusFields CoreColumns TorusLumps RenormalizationStepParameters WeightedResponses
namespace FarTiltInfluence
set_option linter.unusedSectionVars false
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
private theorem setGap_le_supDist {X X' : Finset (TorusSite n)} {y y' : TorusSite n} (hy : y ∈ X) (hy' : y' ∈ X') :
    setGap X X' ≤ supDist y y' :=
  Nat.sInf_le ⟨y, hy, y', hy', rfl⟩
private theorem setGap_attained {X X' : Finset (TorusSite n)} (hX : X.Nonempty) (hX' : X'.Nonempty) :
    ∃ y ∈ X, ∃ y' ∈ X', supDist y y' = setGap X X' := by apply _root_.YangMills.Construction.CoreColumns.setGap_attained <;> assumption
private theorem core_nonempty (j : G.GasSpin) : j.1.core.Nonempty := by apply _root_.YangMills.Construction.StepGas.core_nonempty_of_gasSpin <;> assumption
private theorem exists_nearest_block {Q : Finset (TorusSite n)} (hQ : Q.Nonempty) (i : G.GasSpin) :
    ∃ Y ∈ Q, setGap {Y} i.1.core = setGap Q i.1.core := by
  obtain ⟨Y, hY, a, ha, e⟩ := setGap_attained hQ (core_nonempty i)
  refine ⟨Y, hY, le_antisymm ?_ ?_⟩
  · rw [← e]
    exact setGap_le_supDist (Finset.mem_singleton_self Y) ha
  · obtain ⟨y, hy, a', ha', e'⟩ := setGap_attained (X := {Y}) (Finset.singleton_nonempty Y) (core_nonempty i)
    rw [← e', Finset.mem_singleton.mp hy]
    exact setGap_le_supDist hY ha'
private theorem le_gap_add_diam_add_gap {S Q : Finset (TorusSite n)} (hS : S.Nonempty) (hQ : Q.Nonempty) {D : ℕ}
    (hD : ∀ Y ∈ S, ∀ Y' ∈ Q, D ≤ supDist Y Y') (i : G.GasSpin) :
    D ≤ setGap S i.1.core + siteDiameter i.1.core + setGap Q i.1.core := by
  obtain ⟨y, hy, a, ha, e₁⟩ := setGap_attained hS (core_nonempty i)
  obtain ⟨Y', hY', a', ha', e₂⟩ := setGap_attained hQ (core_nonempty i)
  have h1 := hD y hy Y' hY'
  have h2 := supDist_triangle y a Y'
  have h3 := supDist_triangle a a' Y'
  have h4 : supDist a a' ≤ siteDiameter i.1.core := by
    unfold siteDiameter
    exact (Finset.le_sup (f := fun z => supDist a z) ha').trans
      (Finset.le_sup (f := fun y => i.1.core.sup fun z => supDist y z) ha)
  rw [supDist_comm a' Y'] at h3
  omega
private def tiltCost (R : StepSetup) : ℝ :=
  Real.exp (R.params.rt / 2 ^ 4 + R.params.rt / 2 ^ 6 * ((R.range : ℝ) / R.params.side))
private theorem spinActivity_nonneg (c : ℝ) (i : G.GasSpin) : 0 ≤ G.spinActivity c i := by
  show 0 ≤ Real.exp _
  positivity
private theorem tiltActivity_le (c : ℝ) {e : ℝ} (he : 1 ≤ e) (hrt : 0 < R.params.rt) (Q : Finset (TorusSite n)) (i : G.GasSpin) :
    tiltActivity G c e Q i ≤
      8 * e * G.spinActivity c i * tiltCost R * Real.exp (-(2 * (R.params.rt / 2 ^ 6) * (setGap Q i.1.core : ℝ))) := by
  classical
  have hz := spinActivity_nonneg (G := G) c i
  set l : ℝ := (setGap Q i.1.core : ℝ) with hl
  set q : ℝ := (R.range : ℝ) / R.params.side with hq
  set w : ℝ := tiltCost R * Real.exp (-(2 * (R.params.rt / 2 ^ 6) * l)) with hw
  have hwe : w = Real.exp (R.params.rt / 2 ^ 4 + R.params.rt / 2 ^ 6 * q - 2 * (R.params.rt / 2 ^ 6) * l) := by
    rw [hw, tiltCost, ← Real.exp_add]
    congr 1
  have hgoal : 8 * e * G.spinActivity c i * tiltCost R * Real.exp (-(2 * (R.params.rt / 2 ^ 6) * l)) = 8 * G.spinActivity c i * (e * w) := by
    rw [hw]
    ring
  rw [hgoal]
  have h8 : 0 ≤ 8 * G.spinActivity c i := by positivity
  unfold tiltActivity
  rw [← hl]
  split_ifs with h
  · have h1 : Real.exp (-(R.params.rt * (l - 2) / 2 ^ 5)) ≤ w := by
      rw [hwe]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ R.params.rt / 2 ^ 6 * q := by positivity
      nlinarith only [this]
    have h2 : min 2 (e * Real.exp (-(R.params.rt * (l - 2) / 2 ^ 5))) ≤ e * w :=
      (min_le_right _ _).trans (mul_le_mul_of_nonneg_left h1 (by linarith only [he]))
    calc 4 * G.spinActivity c i * min 2 (e * Real.exp (-(R.params.rt * (l - 2) / 2 ^ 5)))
        ≤ 4 * G.spinActivity c i * (e * w) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 8 * G.spinActivity c i * (e * w) := by
          have : 0 ≤ G.spinActivity c i * (e * w) := by
            have : 0 < w := by rw [hwe]; exact Real.exp_pos _
            have : 0 < e := by linarith only [he]
            positivity
          linarith only [this]
  · have e1 : (R.range : ℝ) / (2 * R.params.side) = q / 2 := by
      rw [hq, div_div, mul_comm]
    rw [e1, not_le] at h
    have h1 : 1 ≤ w := by
      rw [hwe]
      apply Real.one_le_exp
      have h2 : 0 ≤ R.params.rt / 2 ^ 4 := by positivity
      have h3 : 0 ≤ R.params.rt / 2 ^ 6 * (q - 2 * l) :=
        mul_nonneg (by positivity) (by linarith only [h])
      nlinarith only [h2, h3]
    have h2 : 1 ≤ e * w := by nlinarith only [he, h1]
    calc 4 * G.spinActivity c i * 2 = 8 * G.spinActivity c i * 1 := by ring
      _ ≤ 8 * G.spinActivity c i * (e * w) := mul_le_mul_of_nonneg_left h2 h8
private theorem decay_arith {N g l dm Dr r rt z e b T : ℝ} (hN : 1 ≤ N) (hdm : 0 ≤ dm) (hr : 0 ≤ r)
    (hz : 0 ≤ z) (he : 0 ≤ e) (hb : 0 ≤ b) (hD : Dr ≤ g + dm + l) (hrt : r ≤ rt)
    (hT : T ≤ 8 * e * z * b * Real.exp (-(2 * r * l))) :
    N * Real.exp (-(r * g)) * T ≤
      (8 * e * b * Real.exp (-(r * Dr))) * (z * N ^ 4 * Real.exp (2 * rt * dm)) * Real.exp (-(r * l)) := by
  have hN4 : N ≤ N ^ 4 := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
  have hexp : Real.exp (-(r * g)) * Real.exp (-(2 * r * l)) ≤
      Real.exp (-(r * Dr)) * Real.exp (2 * rt * dm) * Real.exp (-(r * l)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : r * Dr ≤ r * (g + dm + l) := mul_le_mul_of_nonneg_left hD hr
    have h2 : r * dm ≤ rt * dm := mul_le_mul_of_nonneg_right hrt hdm
    have h3 : 0 ≤ rt * dm := mul_nonneg (hr.trans hrt) hdm
    nlinarith only [h1, h2, h3]
  have hpos : 0 ≤ 8 * e * z * b := by positivity
  have hN0 : 0 ≤ N * Real.exp (-(r * g)) := by
    have : 0 ≤ N := by linarith only [hN]
    positivity
  calc N * Real.exp (-(r * g)) * T
      ≤ N * Real.exp (-(r * g)) * (8 * e * z * b * Real.exp (-(2 * r * l))) := mul_le_mul_of_nonneg_left hT hN0
    _ = (8 * e * z * b) * N * (Real.exp (-(r * g)) * Real.exp (-(2 * r * l))) := by ring
    _ ≤ (8 * e * z * b) * N ^ 4 * (Real.exp (-(r * Dr)) * Real.exp (2 * rt * dm) * Real.exp (-(r * l))) := by
        have h0 : 0 ≤ Real.exp (-(r * g)) * Real.exp (-(2 * r * l)) := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hN4 hpos) hexp h0 (by positivity)
    _ = _ := by ring
private theorem sum_le_blocks (hgas : GasSumNearBlockBound) {c e : ℝ} (hfit : R.params.Admissible) (hc0 : 0 < c)
    (hcf : R.params.RangeFloor c) (hy : R.params.y₁ ≤ R.coupling) (he : 1 ≤ e) (hrt : 0 < R.params.rt) {S Q : Finset (TorusSite n)} {D : ℕ}
    (hS : S.Nonempty) (hQ : Q.Nonempty) (hD : ∀ Y ∈ S, ∀ Y' ∈ Q, D ≤ supDist Y Y') :
    ∑ i : G.GasSpin, decayFromSet G S i * tiltActivity G c e Q i ≤
      (Q.card : ℝ) * ((8 * e * tiltCost R * Real.exp (-(R.params.rt / 2 ^ 6 * (D : ℝ)))) * Real.exp (-(8 * c * R.coupling)) *
        (2 / (1 - Real.exp (-(R.params.rt / 2 ^ 6 / 4)))) ^ 4) := by
  classical
  have hrp : 0 < R.params.rt / 2 ^ 6 := by positivity
  have he0 : 0 ≤ e := by linarith only [he]
  have hnear0 : 0 ≤ tiltCost R := (Real.exp_pos _).le
  have hB : 0 ≤ 8 * e * tiltCost R * Real.exp (-(R.params.rt / 2 ^ 6 * (D : ℝ))) := by positivity
  choose nb hnb hgap using fun i : G.GasSpin => exists_nearest_block (G := G) hQ i
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Q) (g := nb) (fun i _ => hnb i)]
  calc _ ≤ ∑ _Y ∈ Q, (8 * e * tiltCost R * Real.exp (-(R.params.rt / 2 ^ 6 * (D : ℝ)))) * Real.exp (-(8 * c * R.coupling)) *
          (2 / (1 - Real.exp (-(R.params.rt / 2 ^ 6 / 4)))) ^ 4 := by
        refine Finset.sum_le_sum fun Y _ => ?_
        refine hgas R n G c (R.params.rt / 2 ^ 6) _ Y _ _ hfit hc0 hcf hy hrp hB fun i hi => ?_
        have hY : nb i = Y := (Finset.mem_filter.mp hi).2
        have hg := le_gap_add_diam_add_gap (G := G) hS hQ hD i
        have hg' : (D : ℝ) ≤ (setGap S i.1.core : ℝ) + (i.1.coreDiam : ℝ) + (setGap Q i.1.core : ℝ) := by
          exact_mod_cast hg
        have hN : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast (core_nonempty i).card_pos
        have key := decay_arith (rt := R.params.rt) (z := G.spinActivity c i) (e := e) (b := tiltCost R) hN
          (Nat.cast_nonneg _) hrp.le (spinActivity_nonneg c i) he0 hnear0 hg'
          (by linarith only [hrt]) (tiltActivity_le c he hrt Q i)
        rw [← hY, hgap i]
        exact key
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
private theorem range_arith {rt r L cx : ℝ} (hrt : 0 < rt) (hr : 1 ≤ r) (hL : 1 ≤ L)
    (h : (2 ^ 16 + 2 ^ 7 * rt) * r ^ 4 ≤ cx) : rt / 2 ^ 6 * (r / L) ≤ cx := by
  have h1 : r / L ≤ r := div_le_self (by linarith only [hr]) hL
  have h2 : r ≤ r ^ 4 := by
    calc r = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ 4 := pow_le_pow_right₀ hr (by norm_num)
  have h3 : rt / 2 ^ 6 * (r / L) ≤ rt / 2 ^ 6 * r ^ 4 :=
    mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
  have h4 : 0 ≤ r ^ 4 := by positivity
  nlinarith only [h, h3, h4, hrt]
end FarTiltInfluence
open FarTiltInfluence in
theorem farTiltInfluence (hgas : GasSumNearBlockBound) (hcf : CouplingFloorExists) :
    farTiltInfluenceStatement := by
  unfold farTiltInfluenceStatement HoldsAtEveryStepWithConstant
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT' _ K => ?_⟩
  have hrt0 := hT'.rt_pos
  have hch : 0 < T.gasRate := by
    have h1 := hT'.cE_pos
    have h2 := hT'.κ_pos
    have h3 := hT'.σ_pos
    unfold ParameterAssignment.gasRate ParameterAssignment.κ₁
    positivity
  obtain ⟨y₇, H₇⟩ := hcf T.gasRate T.side T.rt hch
  obtain ⟨W, hWd⟩ : ∃ W, W = (2 / (1 - Real.exp (-(T.rt / 2 ^ 6 / 4)))) ^ 4 := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWd]
    exact Even.pow_nonneg (by decide) _
  refine ⟨max T.floorMin y₇, 8 * Real.exp (T.rt / 2 ^ 4) * W, by positivity,
    fun y hy R A hK hAT n _ G hG S Q e D hS hQ he hDr hD => ?_⟩
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hy7 : y₇ ≤ y := (le_max_right _ _).trans hy
  obtain ⟨hR, hρA, hpc, hyx, hstep⟩ := id hAT.onFamily
  have hx1 : 1 ≤ R.coupling := by
    have h1 : (1 : ℝ) ≤ T.floorMin := by
      have h2 := hT'.yC_ge
      exact h2.trans (le_max_left _ _)
    linarith only [h1, hy0, hyx]
  have hx0 : 0 < R.coupling := by linarith only [hx1]
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hRrt : R.params.rt = T.rt := by rw [hR]; rfl
  have hRy : R.params.y₁ = y := by rw [hR]; rfl
  have hfit : R.params.Admissible := by rw [hR]; exact hT'.fits y hy0
  have hrtR : 0 < R.params.rt := by rw [hRrt]; exact hrt0
  have hcfR : R.params.RangeFloor T.gasRate := by
    intro x hx
    have := H₇ x (hy7.trans (hRy ▸ hx))
    rw [hL, hRrt]
    exact this
  have hyR : R.params.y₁ ≤ R.coupling := by rw [hRy]; exact hyx
  have res := sum_le_blocks (G := G) hgas hfit hch hcfR hyR he hrtR hS hQ hD
  obtain ⟨-, c2⟩ := hcfR R.coupling hyR
  have hr1 : (1 : ℝ) ≤ (clusterRange R.coupling : ℝ) := by
    have : 1 ≤ clusterRange R.coupling := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx0 _)
    exact_mod_cast this
  have hL1 : (1 : ℝ) ≤ (R.params.side : ℝ) := by
    have : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast this
  have hrange := range_arith hrtR hr1 hL1 c2
  have hrange' : R.params.rt / 2 ^ 6 * ((R.range : ℝ) / R.params.side) ≤ T.gasRate * R.coupling := hrange
  have hWR : (2 / (1 - Real.exp (-(R.params.rt / 2 ^ 6 / 4)))) ^ 4 = W := by rw [hWd, hRrt]
  rw [hWR] at res
  refine res.trans ?_
  have hexp : tiltCost R * Real.exp (-(R.params.rt / 2 ^ 6 * (D : ℝ))) * Real.exp (-(8 * T.gasRate * R.coupling)) ≤
      Real.exp (T.rt / 2 ^ 4) * Real.exp (-(7 * T.gasRate * R.coupling) - R.params.rt / 2 ^ 6 * D) := by
    unfold tiltCost
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← hRrt]
    apply Real.exp_le_exp.mpr
    linarith only [hrange']
  have hc : 0 ≤ (Q.card : ℝ) * (8 * e * W) := by
    have : 0 ≤ e := by linarith only [he]
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  calc (Q.card : ℝ) * ((8 * e * tiltCost R * Real.exp (-(R.params.rt / 2 ^ 6 * (D : ℝ)))) * Real.exp (-(8 * T.gasRate * R.coupling)) * W)
      = (Q.card : ℝ) * (8 * e * W) * (tiltCost R * Real.exp (-(R.params.rt / 2 ^ 6 * (D : ℝ))) * Real.exp (-(8 * T.gasRate * R.coupling))) := by ring
    _ ≤ (Q.card : ℝ) * (8 * e * W) * (Real.exp (T.rt / 2 ^ 4) * Real.exp (-(7 * T.gasRate * R.coupling) - R.params.rt / 2 ^ 6 * D)) :=
        mul_le_mul_of_nonneg_left hexp hc
    _ = _ := by ring
end YangMills.Construction.ResponseInTheExpansion
end
