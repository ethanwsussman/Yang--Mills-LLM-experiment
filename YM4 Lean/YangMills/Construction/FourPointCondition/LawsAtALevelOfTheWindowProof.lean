import YangMills.Construction.FourPointCondition.LawsAtALevelOfTheWindow
import YangMills.Construction.FourPointCondition.ObservablesOfTheExpansionCoincide
import YangMills.Construction.FourPointCondition.TuplesCarriedToASide
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
open PeriodicLattice ResponseInTheExpansion WeightedResponses TorusLumps StepReturn RenormalizationStepParameters FourPointBounds
private theorem expansion_next_of_returns {p : StepParameters} (hR : ExpansionReturnsAt p) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hx : p.y₁ ≤ x) (hD : HasExpansion p t x D) :
    HasExpansion p (t + 1) (expansionCoupling p t x D) (kernelImage p x D) ∧
      |expansionCoupling p t x D - x| ≤ 2 * p.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem hasExpansion_along_flow {p : StepParameters} (hR : ExpansionReturnsAt p) {β : ℝ}
    (h0 : HasExpansion p 0 β (wilsonWeight β)) :
    ∀ t : ℕ, (∀ j < t, p.y₁ ≤ (couplingFlow p β j).1) →
      HasExpansion p t (couplingFlow p β t).1 (couplingFlow p β t).2 := by apply _root_.YangMills.SharedProofs.p3977 <;> assumption
private theorem couplingFlow_step_bound {p : StepParameters} (hR : ExpansionReturnsAt p) {β : ℝ}
    (h0 : HasExpansion p 0 β (wilsonWeight β)) (t : ℕ) (hfl : ∀ j ≤ t, p.y₁ ≤ (couplingFlow p β j).1) :
    |(couplingFlow p β (t + 1)).1 - (couplingFlow p β t).1| ≤ 2 * p.B :=
  (expansion_next_of_returns hR (hfl t le_rfl)
    (hasExpansion_along_flow hR h0 t fun j hj => hfl j hj.le)).2
abbrev _root_.YangMills.SharedProofs.p4489 := @couplingFlow_step_bound
private theorem couplingFlow_stays_above {p : StepParameters} (hR : ExpansionReturnsAt p) {β : ℝ}
    (h0 : HasExpansion p 0 β (wilsonWeight β)) (k N : ℕ)
    (hk : ∀ j ≤ k, p.y₁ ≤ (couplingFlow p β j).1)
    (hx : p.y₁ + 2 * |p.B| * (N : ℝ) ≤ (couplingFlow p β k).1) :
    ∀ i ≤ N, (∀ j ≤ k + i, p.y₁ ≤ (couplingFlow p β j).1) ∧
      (couplingFlow p β k).1 - 2 * |p.B| * (i : ℝ) ≤ (couplingFlow p β (k + i)).1 := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨hk, by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2⟩ := ih (by omega)
    have h3 := (abs_le.1 (couplingFlow_step_bound hR h0 (k + i) h1)).1
    have h4 := le_abs_self p.B
    have e : k + (i + 1) = k + i + 1 := by omega
    have h5 : (couplingFlow p β k).1 - 2 * |p.B| * ((i + 1 : ℕ) : ℝ) ≤ (couplingFlow p β (k + i + 1)).1 := by
      have e2 : 2 * |p.B| * ((i + 1 : ℕ) : ℝ) = 2 * |p.B| * (i : ℝ) + 2 * |p.B| := by
        push_cast
        ring
      rw [e2]
      linarith
    have h6 : 2 * |p.B| * ((i + 1 : ℕ) : ℝ) ≤ 2 * |p.B| * (N : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hi) (by positivity)
    refine ⟨fun j hj => ?_, by rw [e]; exact h5⟩
    by_cases hj' : j ≤ k + i
    · exact h1 j hj'
    · have e3 : j = k + i + 1 := by omega
      rw [e3]
      linarith
private theorem exists_add_mul_log_sq_le (y b : ℝ) (hb : 0 ≤ b) :
    ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → y + b * (2 * Real.log x ^ 2) ≤ x := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).def (c := 1 / (4 * b + 1)) (by positivity)
  have h2 := (h.and (eventually_ge_atTop (max 1 (2 * y)))).and (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 h2
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨⟨h3, h4⟩, h5⟩ := hx₀ x hx
  have h6 : 2 * y ≤ x := (le_max_right _ _).trans h4
  have h7 : Real.log x ^ 2 ≤ 1 / (4 * b + 1) * x := by
    have e1 : ‖Real.log x ^ 2‖ = Real.log x ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have e2 : ‖id x‖ = x := by
      rw [id, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rwa [e1, e2] at h3
  have h8 : (4 * b + 1) * Real.log x ^ 2 ≤ x := by
    have := mul_le_mul_of_nonneg_left h7 (show (0 : ℝ) ≤ 4 * b + 1 by positivity)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
  nlinarith
abbrev _root_.YangMills.SharedProofs.p47765 := @exists_add_mul_log_sq_le
private theorem torusSide_div_levelMesh {L : ℕ} (hL : 0 < L) (m K k : ℕ) :
    torusSide L m / levelMesh L K k = 2 * (L : ℝ) ^ ((m : ℤ) + (K : ℤ) - (k : ℤ)) := by
  have hne : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold torusSide levelMesh meshSize
  rw [div_eq_mul_inv, ← zpow_neg, neg_neg, mul_assoc, ← zpow_natCast, ← zpow_add₀ hne]
  congr 2
  ring
theorem cumulantLawsAtWindowLevel_holds (hConn : connectedFunctionsStatement)
    (hObs : torusUrsellEqWeightedCurvatureStatement) (hCut : CutoffRescalingInvariance)
    (hTup : dilatedTupleToSideStatement) : cumulantLawsAtWindowLevel := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hr, H⟩ := hConn a ha
  refine ⟨L₀, rt₀, C₀, hr, fun L hodd hL Tb hTa hTL hD hC hHf hrt hc => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hodd hL Tb hTa hTL hD hC hHf hrt hc
  refine ⟨max y₀ Tb.floorMin, fun y hy hR hW Kr hKr vt hvt hvt1 => ?_⟩
  have hy₀ : y₀ ≤ y := (le_max_left _ _).trans hy
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y ((le_max_right _ _).trans hy)
  obtain ⟨C, x₀, hlaw⟩ := Hy y hy₀ hR hW Kr hKr vt hvt hvt1
  obtain ⟨X₁, hX₁⟩ := exists_add_mul_log_sq_le (Tb.stepParameters y).y₁
    (2 * |(Tb.stepParameters y).B|) (by positivity)
  refine ⟨C, max (max x₀ X₁) (max y (Real.exp 2)), ?_⟩
  intro β k al hrun hal K m d hside hlo hhi q hq f hf
  set x := (couplingFlow (Tb.stepParameters y) β k).1 with hx
  have hXk := hrun k le_rfl
  have hxx₀ : x₀ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hXk
  have hxX₁ : X₁ ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hXk
  have hxe : Real.exp 2 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hXk
  have hfl : ∀ j ≤ k, (Tb.stepParameters y).y₁ ≤ (couplingFlow (Tb.stepParameters y) β j).1 := fun j hj =>
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hrun j hj)
  have hβ : y ≤ β := hfl 0 (Nat.zero_le _)
  have h0 := hW β hβ
  have hL3 : 3 ≤ (Tb.stepParameters y).side := le_trans (by norm_num) hfit.L_ge
  have hLpos : 0 < (Tb.stepParameters y).side := by omega
  have hLR : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by exact_mod_cast hLpos
  have hLne : ((Tb.stepParameters y).side : ℝ) ≠ 0 := by linarith
  have hsd := torusSide_div_levelMesh hLpos m K k
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) hxe
  have hlog : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).2 hxe
  have hcube : 8 ≤ Real.log x ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log x - 2) (by linarith : (0 : ℝ) ≤ Real.log x)]
  have hbig : (2 : ℝ) < Real.exp (Real.log x ^ 3) := by
    have := Real.add_one_le_exp (Real.log x ^ 3)
    linarith
  have hMpos : (k : ℤ) < (m : ℤ) + (K : ℤ) := by
    by_contra hcon
    have h1 : ((Tb.stepParameters y).side : ℝ) ^ ((m : ℤ) + (K : ℤ) - (k : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ hLR (by omega)
    rw [hsd] at hside
    linarith
  obtain ⟨M, hMe⟩ : ∃ M : ℕ, (M : ℤ) = (m : ℤ) + (K : ℤ) - (k : ℤ) :=
    ⟨((m : ℤ) + (K : ℤ) - (k : ℤ)).toNat, by omega⟩
  have hM : M + k = m + K := by omega
  have hM1 : 1 ≤ M := by omega
  have hsM : torusSide (Tb.stepParameters y).side m / levelMesh (Tb.stepParameters y).side K k =
      2 * ((Tb.stepParameters y).side : ℝ) ^ M := by
    rw [hsd, ← hMe, zpow_natCast]
  have hsp : levelMesh (Tb.stepParameters y).side K k ≠ 0 := by
    unfold levelMesh meshSize
    exact zpow_ne_zero _ hLne
  rw [hsM] at hside
  set n := d / levelMesh (Tb.stepParameters y).side K k with hn
  have hnside : n * torusSide (Tb.stepParameters y).side m = d * torusSide (Tb.stepParameters y).side M := by
    have e : torusSide (Tb.stepParameters y).side M =
        torusSide (Tb.stepParameters y).side m / levelMesh (Tb.stepParameters y).side K k := by
      rw [hsM]
      rfl
    rw [e, hn]
    field_simp
  have hq1 : 1 ≤ q := by omega
  have hq3 : q ≤ 3 := by omega
  obtain ⟨htup, hconn⟩ := hTup (Tb.stepParameters y) m M (q + 1) d n vt hfit hnside f hf
  have hlawL := hconn q rfl f hf
  have hrunM : ∀ j ≤ k + 2 * chainDepth x,
      (Tb.stepParameters y).y₁ ≤ (couplingFlow (Tb.stepParameters y) β j).1 := by
    have h1 := hX₁ x hxX₁
    have h2 : ((chainDepth x : ℕ) : ℝ) ≤ Real.log x ^ 2 := Nat.floor_le (by positivity)
    have h3 : 2 * |(Tb.stepParameters y).B| * ((2 * chainDepth x : ℕ) : ℝ) ≤
        2 * |(Tb.stepParameters y).B| * (2 * Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_left (by push_cast; linarith) (by positivity)
    exact (couplingFlow_stays_above hR h0 k (2 * chainDepth x) hfl (by linarith) _ le_rfl).1
  have hwin : InScaleWindow (Tb.stepParameters y) β k M n x₀ := ⟨hxx₀, hrunM, hlo, hhi, hside⟩
  have : NeZero (Tb.stepParameters y).side := ⟨hLpos.ne'⟩
  have hmain := hlaw q β k M n al hq1 hq3 hwin hal
    (fun i => dilateToSide (Tb.stepParameters y).side m M (f i)) htup
  rw [add_zero, hCut (Tb.stepParameters y).side m K M k (q + 1) β hL3 hM f,
    hObs (Tb.stepParameters y).side M k (q + 1) β hL3 hM1
      (fun i => dilateToSide (Tb.stepParameters y).side m M (f i)), ← hlawL]
  exact hmain
end YangMills.Construction.FourPointCondition
end
