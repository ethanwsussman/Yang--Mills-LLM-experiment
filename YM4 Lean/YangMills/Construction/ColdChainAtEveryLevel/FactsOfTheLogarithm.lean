import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.ColdChainAtEveryLevel.LogarithmsOfTheCoordinates
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
theorem pureComponent_of_re_eq_zero {q : ℍ[ℝ]} (hq : q.re = 0) : pureComponent q = q := by
  have := re_add_pureComponent q
  rw [hq] at this
  simpa using this
theorem re_pureComponent (q : ℍ[ℝ]) : (pureComponent q).re = 0 := by
  simp [pureComponent]
theorem exp_eq_of_re_eq_zero {q : ℍ[ℝ]} (hq : q.re = 0) :
    NormedSpace.exp q = ((Real.cos ‖q‖ : ℝ) : ℍ[ℝ]) + (Real.sin ‖q‖ / ‖q‖) • q :=
  Quaternion.exp_of_re_eq_zero q hq
theorem re_exp_of_re_eq_zero {q : ℍ[ℝ]} (hq : q.re = 0) : (NormedSpace.exp q : ℍ[ℝ]).re = Real.cos ‖q‖ := by
  rw [exp_eq_of_re_eq_zero hq]
  simp [hq]
theorem pureComponent_exp {q : ℍ[ℝ]} (hq : q.re = 0) : pureComponent (NormedSpace.exp q) = Real.sinc ‖q‖ • q := by
  by_cases hzero : q = 0
  · subst hzero
    simp [pureComponent_one]
  · have hnorm : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hzero
    rw [exp_eq_of_re_eq_zero hq, pureComponent_add, pureComponent_coe, zero_add, pureComponent_smul,
      pureComponent_of_re_eq_zero hq, Real.sinc_of_ne_zero hnorm]
theorem abs_sinc_sub_one_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) : |Real.sinc r - 1| ≤ r ^ 2 / 4 := by
  rcases hr.eq_or_lt with rfl | hpos
  · simp
  · have hlow := Real.sin_gt_sub_cube hpos
    have hup := Real.sin_lt hpos
    rw [Real.sinc_of_ne_zero hpos.ne', abs_le]
    have e : Real.sin r / r - 1 = (Real.sin r - r) / r := by field_simp
    rw [e]
    constructor
    · rw [le_div_iff₀ hpos]
      nlinarith
    · rw [div_le_iff₀ hpos]
      nlinarith [pow_pos hpos 3]
theorem abs_sinc_sub_sinc_le {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    |Real.sinc a - Real.sinc b| ≤ |a - b| := by
  rcases ha.eq_or_lt with rfl | hapos
  · have := abs_sinc_sub_one_le hb hb1
    rw [Real.sinc_zero, abs_sub_comm, zero_sub, abs_neg, abs_of_nonneg hb]
    have e : b ^ 2 / 4 ≤ b := by nlinarith
    exact this.trans e
  rcases hb.eq_or_lt with rfl | hbpos
  · have := abs_sinc_sub_one_le ha ha1
    rw [Real.sinc_zero, sub_zero, abs_of_nonneg ha]
    have e : a ^ 2 / 4 ≤ a := by nlinarith
    exact this.trans e
  have hderiv : ∀ x ∈ Set.Ioc (0 : ℝ) 1, HasDerivWithinAt (fun r => Real.sin r / r)
      ((Real.cos x * x - Real.sin x * 1) / x ^ 2) (Set.Ioc (0 : ℝ) 1) x := by
    intro x hx
    exact ((Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx.1.ne').hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖(Real.cos x * x - Real.sin x * 1) / x ^ 2‖ ≤ 1 := by
    intro x hx
    have hpos := hx.1
    have hle := hx.2
    have hlow := Real.sin_gt_sub_cube hpos
    have hup := Real.sin_lt hpos
    have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
    have hcos1 := Real.cos_le_one x
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2), div_le_one (by positivity),
      abs_le]
    have hcube : x ^ 3 ≤ x ^ 2 := by nlinarith [sq_nonneg x]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right hcos hpos.le, mul_le_mul_of_nonneg_right hcos1 hpos.le]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Ioc 0 1)
    (⟨hbpos, hb1⟩ : b ∈ Set.Ioc (0 : ℝ) 1) (⟨hapos, ha1⟩ : a ∈ Set.Ioc (0 : ℝ) 1)
  rw [Real.sinc_of_ne_zero hapos.ne', Real.sinc_of_ne_zero hbpos.ne']
  simpa [Real.norm_eq_abs] using this
theorem norm_pureComponent_exp_sub_sub_le {x y : ℍ[ℝ]} (hx : x.re = 0) (hy : y.re = 0) (hx1 : ‖x‖ ≤ 1)
    (hy1 : ‖y‖ ≤ 1) :
    ‖pureComponent (NormedSpace.exp x) - pureComponent (NormedSpace.exp y) - (x - y)‖ ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  rw [pureComponent_exp hx, pureComponent_exp hy]
  have e : Real.sinc ‖x‖ • x - Real.sinc ‖y‖ • y - (x - y) =
      (Real.sinc ‖x‖ - 1) • (x - y) + (Real.sinc ‖x‖ - Real.sinc ‖y‖) • y := by
    module
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := abs_sinc_sub_one_le (norm_nonneg x) hx1
  have h2 := abs_sinc_sub_sinc_le (norm_nonneg x) hx1 (norm_nonneg y) hy1
  have h3 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have h4 : ‖x‖ ^ 2 / 4 ≤ ‖x‖ := by nlinarith [norm_nonneg x]
  calc |Real.sinc ‖x‖ - 1| * ‖x - y‖ + |Real.sinc ‖x‖ - Real.sinc ‖y‖| * ‖y‖
      ≤ ‖x‖ * ‖x - y‖ + ‖x - y‖ * ‖y‖ := by
        gcongr
        · exact h1.trans h4
        · exact h2.trans h3
    _ = (‖x‖ + ‖y‖) * ‖x - y‖ := by ring
theorem norm_pureComponent_exp_sub_self_le {x : ℍ[ℝ]} (hx : x.re = 0) (hx1 : ‖x‖ ≤ 1) :
    ‖pureComponent (NormedSpace.exp x) - x‖ ≤ ‖x‖ ^ 2 := by
  have := norm_pureComponent_exp_sub_sub_le hx (y := 0) (by simp) hx1 (by simp)
  simpa [pureComponent_one, sq] using this
theorem norm_sub_le_two_mul_pureComponent_exp {x y : ℍ[ℝ]} (hx : x.re = 0) (hy : y.re = 0)
    (h : ‖x‖ + ‖y‖ ≤ 1 / 2) :
    ‖x - y‖ ≤ 2 * ‖pureComponent (NormedSpace.exp x) - pureComponent (NormedSpace.exp y)‖ := by
  have hx1 : ‖x‖ ≤ 1 := by linarith [norm_nonneg y]
  have hy1 : ‖y‖ ≤ 1 := by linarith [norm_nonneg x]
  have h1 := norm_pureComponent_exp_sub_sub_le hx hy hx1 hy1
  have h2 : ‖x - y‖ ≤ ‖pureComponent (NormedSpace.exp x) - pureComponent (NormedSpace.exp y)‖ +
      ‖pureComponent (NormedSpace.exp x) - pureComponent (NormedSpace.exp y) - (x - y)‖ := by
    have := norm_sub_le (pureComponent (NormedSpace.exp x) - pureComponent (NormedSpace.exp y))
      (pureComponent (NormedSpace.exp x) - pureComponent (NormedSpace.exp y) - (x - y))
    simpa using this
  have h3 : (‖x‖ + ‖y‖) * ‖x - y‖ ≤ 1 / 2 * ‖x - y‖ := by gcongr
  linarith
theorem normSq_coe_unitQuaternion (g : UnitQuaternion) : Quaternion.normSq (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.normSq_unitQuaternion <;> assumption
theorem norm_coe_sub_one_sq (g : UnitQuaternion) : ‖(g : ℍ[ℝ]) - 1‖ ^ 2 = 2 - 2 * (g : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.GaugeFixing.norm_coe_sub_one_sq <;> assumption
theorem re_sq_add_norm_pureComponent_sq (g : UnitQuaternion) :
    (g : ℍ[ℝ]).re ^ 2 + ‖pureComponent (g : ℍ[ℝ])‖ ^ 2 = 1 := by
  have h := normSq_coe_unitQuaternion g
  rw [sq ‖pureComponent (g : ℍ[ℝ])‖, ← Quaternion.normSq_eq_norm_mul_self]
  rw [Quaternion.normSq_def'] at h ⊢
  simp only [pureComponent, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
    Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, smul_eq_mul] at h ⊢
  nlinarith
theorem re_coe_le_one (g : UnitQuaternion) : (g : ℍ[ℝ]).re ≤ 1 := by
  nlinarith [re_sq_add_norm_pureComponent_sq g, sq_nonneg ‖pureComponent (g : ℍ[ℝ])‖,
    sq_nonneg ((g : ℍ[ℝ]).re - 1)]
theorem neg_one_le_re_coe (g : UnitQuaternion) : -1 ≤ (g : ℍ[ℝ]).re := by
  nlinarith [re_sq_add_norm_pureComponent_sq g, sq_nonneg ‖pureComponent (g : ℍ[ℝ])‖,
    sq_nonneg ((g : ℍ[ℝ]).re + 1)]
def piImagI : ℍ[ℝ] := ⟨0, Real.pi, 0, 0⟩
theorem norm_piImagI : ‖piImagI‖ = Real.pi := by
  have h : ‖piImagI‖ * ‖piImagI‖ = Real.pi * Real.pi := by
    rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    have e0 : piImagI.re = 0 := rfl
    have e1 : piImagI.imI = Real.pi := rfl
    have e2 : piImagI.imJ = 0 := rfl
    have e3 : piImagI.imK = 0 := rfl
    rw [e0, e1, e2, e3]
    ring
  nlinarith [norm_nonneg piImagI, Real.pi_pos, sq_nonneg (‖piImagI‖ - Real.pi)]
theorem unitQuaternionLog_of_pure_zero_of_nonneg {g : UnitQuaternion} (h0 : pureComponent (g : ℍ[ℝ]) = 0)
    (h1 : 0 ≤ (g : ℍ[ℝ]).re) : unitQuaternionLog g = 0 := by
  unfold unitQuaternionLog
  exact (if_pos h0).trans (if_pos h1)
theorem unitQuaternionLog_of_pure_zero_of_neg {g : UnitQuaternion} (h0 : pureComponent (g : ℍ[ℝ]) = 0)
    (h1 : ¬ 0 ≤ (g : ℍ[ℝ]).re) : unitQuaternionLog g = piImagI := by
  unfold unitQuaternionLog
  exact (if_pos h0).trans (if_neg h1)
theorem unitQuaternionLog_of_pure_ne_zero {g : UnitQuaternion} (h0 : pureComponent (g : ℍ[ℝ]) ≠ 0) :
    unitQuaternionLog g =
      (Real.arccos (g : ℍ[ℝ]).re / ‖pureComponent (g : ℍ[ℝ])‖) • pureComponent (g : ℍ[ℝ]) := by
  unfold unitQuaternionLog
  exact if_neg h0
theorem re_unitQuaternionLog (g : UnitQuaternion) : (unitQuaternionLog g).re = 0 := by
  by_cases h0 : pureComponent (g : ℍ[ℝ]) = 0
  · by_cases h1 : 0 ≤ (g : ℍ[ℝ]).re
    · rw [unitQuaternionLog_of_pure_zero_of_nonneg h0 h1]; simp
    · rw [unitQuaternionLog_of_pure_zero_of_neg h0 h1]; rfl
  · rw [unitQuaternionLog_of_pure_ne_zero h0]
    simp [re_pureComponent]
theorem re_eq_one_or_neg_one_of_pure_zero {g : UnitQuaternion} (h0 : pureComponent (g : ℍ[ℝ]) = 0) :
    (g : ℍ[ℝ]).re = 1 ∨ (g : ℍ[ℝ]).re = -1 := by
  have hs := re_sq_add_norm_pureComponent_sq g
  rw [h0, norm_zero] at hs
  have : ((g : ℍ[ℝ]).re - 1) * ((g : ℍ[ℝ]).re + 1) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h | h
  · left; linarith
  · right; linarith
theorem norm_unitQuaternionLog (g : UnitQuaternion) : ‖unitQuaternionLog g‖ = Real.arccos (g : ℍ[ℝ]).re := by
  by_cases h0 : pureComponent (g : ℍ[ℝ]) = 0
  · rcases re_eq_one_or_neg_one_of_pure_zero h0 with h | h
    · rw [unitQuaternionLog_of_pure_zero_of_nonneg h0 (by rw [h]; norm_num), h]
      simp
    · rw [unitQuaternionLog_of_pure_zero_of_neg h0 (by rw [h]; norm_num), h, Real.arccos_neg_one, norm_piImagI]
  · rw [unitQuaternionLog_of_pure_ne_zero h0]
    have hn : ‖pureComponent (g : ℍ[ℝ])‖ ≠ 0 := norm_ne_zero_iff.2 h0
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.arccos_nonneg _), abs_of_nonneg (norm_nonneg _)]
    field_simp
theorem sin_arccos_re_coe (g : UnitQuaternion) :
    Real.sin (Real.arccos (g : ℍ[ℝ]).re) = ‖pureComponent (g : ℍ[ℝ])‖ := by
  rw [Real.sin_arccos]
  have hs := re_sq_add_norm_pureComponent_sq g
  have : 1 - (g : ℍ[ℝ]).re ^ 2 = ‖pureComponent (g : ℍ[ℝ])‖ ^ 2 := by linarith
  rw [this, Real.sqrt_sq (norm_nonneg _)]
theorem cos_arccos_re_coe (g : UnitQuaternion) : Real.cos (Real.arccos (g : ℍ[ℝ]).re) = (g : ℍ[ℝ]).re :=
  Real.cos_arccos (neg_one_le_re_coe g) (re_coe_le_one g)
theorem exp_unitQuaternionLog (g : UnitQuaternion) : NormedSpace.exp (unitQuaternionLog g) = (g : ℍ[ℝ]) := by
  rw [exp_eq_of_re_eq_zero (re_unitQuaternionLog g), norm_unitQuaternionLog, cos_arccos_re_coe, sin_arccos_re_coe]
  by_cases h0 : pureComponent (g : ℍ[ℝ]) = 0
  · rw [h0, norm_zero, zero_div, zero_smul, add_zero]
    have := re_add_pureComponent (g : ℍ[ℝ])
    rw [h0, add_zero] at this
    exact this
  · have hn : ‖pureComponent (g : ℍ[ℝ])‖ ≠ 0 := norm_ne_zero_iff.2 h0
    have hθ : Real.arccos (g : ℍ[ℝ]).re ≠ 0 := by
      intro h
      have := sin_arccos_re_coe g
      rw [h, Real.sin_zero] at this
      exact hn this.symm
    rw [unitQuaternionLog_of_pure_ne_zero h0, smul_smul]
    have : ‖pureComponent (g : ℍ[ℝ])‖ / Real.arccos (g : ℍ[ℝ]).re *
        (Real.arccos (g : ℍ[ℝ]).re / ‖pureComponent (g : ℍ[ℝ])‖) = 1 := by
      field_simp
    rw [this, one_smul]
    exact re_add_pureComponent _
theorem expUnit_unitQuaternionLog (g : UnitQuaternion) :
    expUnit ⟨unitQuaternionLog g, re_unitQuaternionLog g⟩ = g :=
  Subtype.ext (exp_unitQuaternionLog g)
theorem norm_exp_sub_one_le {q : ℍ[ℝ]} (hq : q.re = 0) : ‖NormedSpace.exp q - 1‖ ≤ ‖q‖ := by
  have h := norm_coe_sub_one_sq (expUnit ⟨q, hq⟩)
  have e : ((expUnit ⟨q, hq⟩ : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp q := rfl
  rw [e, re_exp_of_re_eq_zero hq] at h
  have hc := Real.one_sub_sq_div_two_le_cos (x := ‖q‖)
  have : ‖NormedSpace.exp q - 1‖ ^ 2 ≤ ‖q‖ ^ 2 := by rw [h]; linarith
  exact (abs_le_of_sq_le_sq' this (norm_nonneg _)).2
theorem norm_coe_sub_one_le_norm_unitQuaternionLog (g : UnitQuaternion) :
    ‖(g : ℍ[ℝ]) - 1‖ ≤ ‖unitQuaternionLog g‖ := by
  have := norm_exp_sub_one_le (re_unitQuaternionLog g)
  rwa [exp_unitQuaternionLog] at this
theorem norm_unitQuaternionLog_le_two_mul (g : UnitQuaternion) :
    ‖unitQuaternionLog g‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ := by
  set θ := ‖unitQuaternionLog g‖ with hθ
  have h0 : 0 ≤ θ := norm_nonneg _
  have hπ : θ ≤ Real.pi := by rw [hθ, norm_unitQuaternionLog]; exact Real.arccos_le_pi _
  have hre : (g : ℍ[ℝ]).re = Real.cos θ := by rw [hθ, norm_unitQuaternionLog, cos_arccos_re_coe]
  have h1 := norm_coe_sub_one_sq g
  rw [hre] at h1
  have h2 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    rw [this]
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have h3 := Real.mul_le_sin (x := θ / 2) (by positivity) (by linarith)
  have h4 : θ / 4 ≤ Real.sin (θ / 2) := by
    refine le_trans ?_ h3
    have : 2 / Real.pi * (θ / 2) = θ / Real.pi := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_left h0 Real.pi_pos Real.pi_le_four
  have h5 : (θ / 2) ^ 2 ≤ ‖(g : ℍ[ℝ]) - 1‖ ^ 2 := by
    rw [h1, h2]
    nlinarith
  have := (abs_le_of_sq_le_sq' h5 (norm_nonneg _)).2
  linarith
theorem unitQuaternionLog_expUnit {w : imaginaryQuaternions} (h : ‖(w : ℍ[ℝ])‖ ≤ 1 / 8) :
    unitQuaternionLog (expUnit w) = (w : ℍ[ℝ]) := by
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  have e : ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (w : ℍ[ℝ]) := rfl
  have h1 : ‖unitQuaternionLog (expUnit w)‖ ≤ 1 / 4 := by
    refine (norm_unitQuaternionLog_le_two_mul _).trans ?_
    rw [e]
    have := norm_exp_sub_one_le hw
    linarith
  have h2 := norm_sub_le_two_mul_pureComponent_exp (re_unitQuaternionLog (expUnit w)) hw (by linarith)
  rw [exp_unitQuaternionLog, e, sub_self, norm_zero, mul_zero] at h2
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
theorem star_eq_neg_of_re_eq_zero {q : ℍ[ℝ]} (hq : q.re = 0) : star q = -q := by
  ext <;> simp [hq]
theorem re_eq_zero_of_star_eq_neg {q : ℍ[ℝ]} (hq : star q = -q) : q.re = 0 := by
  have := congrArg QuaternionAlgebra.re hq
  simp at this
  linarith
theorem re_adjointAction {q : ℍ[ℝ]} (g : UnitQuaternion) (hq : q.re = 0) : (adjointAction g q).re = 0 := by
  apply re_eq_zero_of_star_eq_neg
  simp only [adjointAction, coe_unitQuaternion_inv, star_mul, star_star, star_eq_neg_of_re_eq_zero hq]
  noncomm_ring
theorem norm_adjointAction (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖adjointAction g q‖ = ‖q‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem adjointAction_sub (g : UnitQuaternion) (a b : ℍ[ℝ]) :
    adjointAction g (a - b) = adjointAction g a - adjointAction g b := by apply _root_.YangMills.Construction.BlockLines.adjointAction_sub <;> assumption
theorem pureComponent_adjointAction (g : UnitQuaternion) (q : ℍ[ℝ]) :
    pureComponent (adjointAction g q) = adjointAction g (pureComponent q) := by apply _root_.YangMills.Construction.BlockLines.pureComponent_adjointAction <;> assumption
theorem coe_conj_eq_adjointAction (g h : UnitQuaternion) :
    ((g * h * g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = adjointAction g (h : ℍ[ℝ]) := rfl
theorem pureComponent_coe_mul (a b : UnitQuaternion) :
    pureComponent ((a * b : UnitQuaternion) : ℍ[ℝ]) = pureComponent (a : ℍ[ℝ]) + pureComponent (b : ℍ[ℝ]) +
      pureComponent (((a : ℍ[ℝ]) - 1) * ((b : ℍ[ℝ]) - 1)) := by
  have e : ((a * b : UnitQuaternion) : ℍ[ℝ]) =
      (a : ℍ[ℝ]) + (b : ℍ[ℝ]) - 1 + ((a : ℍ[ℝ]) - 1) * ((b : ℍ[ℝ]) - 1) := by
    push_cast
    noncomm_ring
  rw [e, pureComponent_add, pureComponent_sub, pureComponent_add, pureComponent_one, sub_zero]
end BlockAverages
end YangMills.Construction
end
