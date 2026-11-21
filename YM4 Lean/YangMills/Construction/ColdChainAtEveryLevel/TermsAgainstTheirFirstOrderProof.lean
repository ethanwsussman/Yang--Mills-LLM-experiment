import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.MeansOfAPotential
import YangMills.Construction.ColdChainAtEveryLevel.GapsOfTheLevelsNearACellProof
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import YangMills.Construction.ColdChainAtEveryLevel.SizesAtAGoodCell
import YangMills.Construction.ColdChainAtEveryLevel.TermsAgainstTheirFirstOrder
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open LatticeFractionalIntegration
namespace TermwiseBounds
section
theorem quat_re_mul_comm (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.quaternion_re_mul_comm <;> assumption
theorem quat_re_star (a : ℍ[ℝ]) : (star a).re = a.re := by simp
theorem quat_abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem quat_abs_re_mul_le (a b : ℍ[ℝ]) : |(a * b).re| ≤ ‖a‖ * ‖b‖ :=
  (quat_abs_re_le_norm _).trans_eq (norm_mul a b)
theorem star_mul_self_of_norm_eq_one {q : ℍ[ℝ]} (h : ‖q‖ = 1) : star q * q = 1 := by apply _root_.YangMills.Construction.QuaternionLog.star_mul_self_of_norm_eq_one <;> assumption
theorem mul_star_self_of_norm_eq_one {q : ℍ[ℝ]} (h : ‖q‖ = 1) : q * star q = 1 := by apply _root_.YangMills.Construction.QuaternionLog.mul_star_self_of_norm_eq_one <;> assumption
theorem norm_sub_one_sq_of_norm_eq_one {q : ℍ[ℝ]} (h : ‖q‖ = 1) : ‖q - 1‖ ^ 2 = 2 - 2 * q.re := by
  have h1 : Quaternion.normSq q = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, h]
    norm_num
  have h2 : ‖q - 1‖ ^ 2 = Quaternion.normSq (q - 1) := by
    rw [Quaternion.normSq_eq_norm_mul_self]
    ring
  rw [h2]
  rw [Quaternion.normSq_def'] at h1 ⊢
  simp
  nlinarith
theorem re_pureComponent (q : ℍ[ℝ]) : (pureComponent q).re = 0 := by apply _root_.YangMills.Construction.BlockAverages.re_pureComponent <;> assumption
theorem star_pureComponent (q : ℍ[ℝ]) : star (pureComponent q) = - pureComponent q := by apply _root_.YangMills.Construction.GaugeMotions.star_pureComponent <;> assumption
theorem star_eq_re_sub_pureComponent (q : ℍ[ℝ]) : star q = (q.re : ℍ[ℝ]) - pureComponent q := by
  have h := re_add_pureComponent q
  have h2 : star q = star ((q.re : ℍ[ℝ]) + pureComponent q) := by rw [h]
  rw [h2, star_add, star_pureComponent, Quaternion.star_coe]
  rw [sub_eq_add_neg]
theorem quat_re_coe_mul (c : ℝ) (q : ℍ[ℝ]) : ((c : ℍ[ℝ]) * q).re = c * q.re := by
  simp [Quaternion.re_mul]
theorem quat_re_mul_coe (c : ℝ) (q : ℍ[ℝ]) : (q * (c : ℍ[ℝ])).re = c * q.re := by
  rw [quat_re_mul_comm, quat_re_coe_mul]
theorem quat_re_smul (c : ℝ) (q : ℍ[ℝ]) : (c • q).re = c * q.re := by simp
theorem pureComponent_mul_comm (q : ℍ[ℝ]) : pureComponent q * q = q * pureComponent q := by
  conv_lhs => rw [← re_add_pureComponent q]
  conv_rhs => rw [← re_add_pureComponent q]
  have hc : pureComponent ((q.re : ℍ[ℝ]) + pureComponent q) = pureComponent q := by rw [re_add_pureComponent]
  rw [hc, mul_add, add_mul]
  rw [Quaternion.coe_commutes]
theorem re_conj_mul_pureComponent {m : ℍ[ℝ]} (hm : ‖m‖ = 1) (c : ℍ[ℝ]) :
    (m * c * star m * pureComponent m).re = (c * pureComponent m).re := by
  have h1 : m * c * star m * pureComponent m = m * (c * (star m * pureComponent m)) := by
    simp only [mul_assoc]
  have h2 : (m * (c * (star m * pureComponent m))).re = (c * (star m * pureComponent m) * m).re :=
    quat_re_mul_comm _ _
  have h3 : star m * pureComponent m * m = pureComponent m := by
    rw [mul_assoc, pureComponent_mul_comm, ← mul_assoc, star_mul_self_of_norm_eq_one hm, one_mul]
  rw [h1, h2, mul_assoc, mul_assoc, ← mul_assoc (star m), h3]
theorem re_star_mul_of_re_eq_zero (h p : ℍ[ℝ]) (hp : p.re = 0) : (star h * p).re = - (h * p).re := by
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, hp]
  ring
theorem fit_change_eq {u u₀ m₀ g : ℍ[ℝ]} (Ad : ℍ[ℝ]) (r r₀ : ℝ) (hu₀ : ‖u₀‖ = 1)
    (hm₀ : ‖m₀‖ = 1) :
    r - ((r • u) * star (g * (m₀ * u₀))).re - (r₀ - ((r₀ • u₀) * star (m₀ * u₀)).re) -
        ((Ad * star u₀).re - (Ad * star (m₀ * u₀)).re + ((r₀ • u₀) * star (m₀ * u₀) * pureComponent g).re) =
      (r - r₀ - (Ad * star u₀).re) * (1 - m₀.re) +
        r * (1 - (g * (m₀ * u₀) * star u * star m₀).re) * m₀.re +
        (r₀ - r) * (pureComponent g * pureComponent m₀).re -
        r * ((g - 1) * (m₀ * star (u * star u₀) * star m₀ - 1) * pureComponent m₀).re +
        (((r • u - r₀ • u₀ - Ad) * star u₀) * pureComponent m₀).re := by
  set P := pureComponent m₀ with hP
  set x := pureComponent g with hx
  set μ := m₀.re with hμ
  set h := u * star u₀ with hh
  set f := m₀ * star h * star m₀ with hf
  set B := Ad * star u₀ with hB
  set E := (r • u - r₀ • u₀ - Ad) * star u₀ with hE
  set e := g * (m₀ * u₀) * star u * star m₀ with he
  have hPre : P.re = 0 := re_pureComponent _
  have hxre : x.re = 0 := re_pureComponent _
  have hm₀' : (μ : ℍ[ℝ]) + P = m₀ := re_add_pureComponent _
  have hst : star m₀ = (μ : ℍ[ℝ]) - P := star_eq_re_sub_pureComponent _
  have heg : e = g * f := by
    simp only [he, hf, hh, star_mul, star_star, mul_assoc]
  have hm : g * (m₀ * u₀) * star u = e * m₀ := by
    simp only [he]
    rw [mul_assoc _ (star m₀) m₀, star_mul_self_of_norm_eq_one hm₀, mul_one]
  have a1 : ((r • u) * star (g * (m₀ * u₀))).re = r * (e * m₀).re := by
    rw [← hm, smul_mul_assoc, quat_re_smul]
    congr 1
    have : u * star (g * (m₀ * u₀)) = star (g * (m₀ * u₀) * star u) := by
      simp only [star_mul, star_star]
    rw [this, quat_re_star]
  have a2 : ((r₀ • u₀) * star (m₀ * u₀)).re = r₀ * μ := by
    rw [smul_mul_assoc, quat_re_smul, star_mul, ← mul_assoc, mul_star_self_of_norm_eq_one hu₀, one_mul, quat_re_star]
  have a3 : (Ad * star (m₀ * u₀)).re = (B * star m₀).re := by
    simp only [hB, star_mul, mul_assoc]
  have a4 : ((r₀ • u₀) * star (m₀ * u₀) * x).re = - r₀ * (P * x).re := by
    have : (r₀ • u₀) * star (m₀ * u₀) * x = r₀ • (star m₀ * x) := by
      rw [smul_mul_assoc, smul_mul_assoc, star_mul, ← mul_assoc u₀, mul_star_self_of_norm_eq_one hu₀, one_mul]
    rw [this, quat_re_smul, hst, sub_mul, Quaternion.re_sub, quat_re_coe_mul, hxre]
    ring
  have a5 : (e * m₀).re = e.re * μ + (e * P).re := by
    conv_lhs => rw [← hm₀']
    rw [mul_add, Quaternion.re_add, quat_re_mul_coe]
    ring
  have a6 : (B * star m₀).re = B.re * μ - (B * P).re := by
    rw [hst, mul_sub, Quaternion.re_sub, quat_re_mul_coe]
    ring
  have hBeq : B = r • h - (r₀ : ℍ[ℝ]) - E := by
    have h1 : r₀ • u₀ * star u₀ = (r₀ : ℍ[ℝ]) := by
      rw [smul_mul_assoc, mul_star_self_of_norm_eq_one hu₀]
      ext <;> simp
    simp only [hE, hB, hh, sub_mul, smul_mul_assoc]
    rw [smul_mul_assoc] at h1
    rw [h1]
    abel
  have a8 : (B * P).re = r * (h * P).re - (E * P).re := by
    rw [hBeq, sub_mul, sub_mul, Quaternion.re_sub, Quaternion.re_sub, quat_re_coe_mul, hPre, smul_mul_assoc,
      quat_re_smul]
    ring
  have a10 : (f * P).re = - (h * P).re := by
    rw [hf, re_conj_mul_pureComponent hm₀, re_star_mul_of_re_eq_zero h P hPre]
  have a11 : ((g - 1) * P).re = (x * P).re := by
    have : g - 1 = ((g.re - 1 : ℝ) : ℍ[ℝ]) + x := by
      have h1 := re_add_pureComponent g
      have h2 : ((g.re - 1 : ℝ) : ℍ[ℝ]) = (g.re : ℍ[ℝ]) - 1 := by
        ext <;> simp
      rw [h2, hx]
      nth_rewrite 1 [← h1]
      abel
    rw [this, add_mul, Quaternion.re_add, quat_re_coe_mul, hPre]
    ring
  have a9 : (e * P).re = ((g - 1) * (f - 1) * P).re + (x * P).re + (f * P).re := by
    have : e * P = (g - 1) * (f - 1) * P + (g - 1) * P + f * P := by
      rw [heg]
      noncomm_ring
    rw [this, Quaternion.re_add, Quaternion.re_add, a11]
  have hPx : (P * x).re = (x * P).re := quat_re_mul_comm _ _
  rw [a1, a2, a3, a4, a5, a6, a8, a9, a10, hPx]
  ring
structure QuatClose (p q d : ℍ[ℝ]) (ε : ℝ) : Prop where
  left_le : ‖p‖ ≤ 1
  right_le : ‖q‖ ≤ 1
  sub_le : ‖q - p‖ ≤ ε
  deriv_le : ‖d‖ ≤ ε
  second_le : ‖q - p - d‖ ≤ ε ^ 2
theorem QuatClose.radius_nonneg {p q d : ℍ[ℝ]} {ε : ℝ} (h : QuatClose p q d ε) : 0 ≤ ε :=
  (norm_nonneg _).trans h.deriv_le
theorem QuatClose.mono {p q d : ℍ[ℝ]} {ε ε' : ℝ} (h : QuatClose p q d ε) (he : ε ≤ ε') : QuatClose p q d ε' :=
  ⟨h.left_le, h.right_le, h.sub_le.trans he, h.deriv_le.trans he,
    h.second_le.trans (pow_le_pow_left₀ h.radius_nonneg he 2)⟩
theorem QuatClose.mul {p q d p' q' d' : ℍ[ℝ]} {ε ε' : ℝ} (h : QuatClose p q d ε) (h' : QuatClose p' q' d' ε') :
    QuatClose (p * p') (q * q') (d * p' + p * d') (ε + ε') := by
  have e0 := h.radius_nonneg
  have e1 := h'.radius_nonneg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_mul]
    exact mul_le_one₀ h.left_le (norm_nonneg _) h'.left_le
  · rw [norm_mul]
    exact mul_le_one₀ h.right_le (norm_nonneg _) h'.right_le
  · have e : q * q' - p * p' = (q - p) * q' + p * (q' - p') := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have a1 := mul_le_mul h.sub_le h'.right_le (norm_nonneg _) e0
    have a2 := mul_le_mul h.left_le h'.sub_le (norm_nonneg _) zero_le_one
    linarith
  · refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have a1 := mul_le_mul h.deriv_le h'.left_le (norm_nonneg _) e0
    have a2 := mul_le_mul h.left_le h'.deriv_le (norm_nonneg _) zero_le_one
    linarith
  · have e : q * q' - p * p' - (d * p' + p * d') =
        (q - p - d) * p' + (q - p) * (q' - p') + p * (q' - p' - d') := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add_left (norm_add_le _ _) _).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have a1 := mul_le_mul h.second_le h'.left_le (norm_nonneg _) (sq_nonneg ε)
    have a2 := mul_le_mul h.sub_le h'.sub_le (norm_nonneg _) e0
    have a3 := mul_le_mul h.left_le h'.second_le (norm_nonneg _) zero_le_one
    nlinarith
theorem QuatClose.star {p q d : ℍ[ℝ]} {ε : ℝ} (h : QuatClose p q d ε) :
    QuatClose (star p) (star q) (star d) ε := by
  refine ⟨by rw [norm_star]; exact h.left_le, by rw [norm_star]; exact h.right_le, ?_,
    by rw [norm_star]; exact h.deriv_le, ?_⟩
  · rw [← star_sub, norm_star]
    exact h.sub_le
  · rw [← star_sub, ← star_sub, norm_star]
    exact h.second_le
theorem QuatClose.refl {p : ℍ[ℝ]} (h : ‖p‖ ≤ 1) : QuatClose p p 0 0 :=
  ⟨h, h, by simp, by simp, by simp⟩
theorem norm_smul_sum_le_of_mul_card_le_one {ι : Type*} (s : Finset ι) {c b : ℝ} (hc : 0 ≤ c)
    (hcs : c * s.card ≤ 1) (hb : 0 ≤ b)
    (v : ι → ℍ[ℝ]) (h : ∀ i ∈ s, ‖v i‖ ≤ b) : ‖c • ∑ i ∈ s, v i‖ ≤ b := by
  rw [norm_smul, Real.norm_of_nonneg hc]
  have h1 : ‖∑ i ∈ s, v i‖ ≤ s.card * b := by
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul s _ b h
    simpa using this
  calc c * ‖∑ i ∈ s, v i‖ ≤ c * (s.card * b) := mul_le_mul_of_nonneg_left h1 hc
    _ = (c * s.card) * b := by ring
    _ ≤ 1 * b := mul_le_mul_of_nonneg_right hcs hb
    _ = b := one_mul b
theorem QuatClose.average {ι : Type*} (s : Finset ι) {c ε : ℝ} (hc : 0 ≤ c) (hcs : c * s.card ≤ 1)
    (hε : 0 ≤ ε) (p q d : ι → ℍ[ℝ]) (h : ∀ i ∈ s, QuatClose (p i) (q i) (d i) ε) :
    QuatClose (c • ∑ i ∈ s, p i) (c • ∑ i ∈ s, q i) (c • ∑ i ∈ s, d i) ε := by
  refine ⟨norm_smul_sum_le_of_mul_card_le_one s hc hcs zero_le_one _ fun i hi => (h i hi).left_le,
    norm_smul_sum_le_of_mul_card_le_one s hc hcs zero_le_one _ fun i hi => (h i hi).right_le, ?_,
    norm_smul_sum_le_of_mul_card_le_one s hc hcs hε _ fun i hi => (h i hi).deriv_le, ?_⟩
  · rw [← smul_sub, ← Finset.sum_sub_distrib]
    exact norm_smul_sum_le_of_mul_card_le_one s hc hcs hε _ fun i hi => (h i hi).sub_le
  · rw [← smul_sub, ← smul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact norm_smul_sum_le_of_mul_card_le_one s hc hcs (sq_nonneg ε) _ fun i hi => (h i hi).second_le
theorem norm_pureComponent_le_norm_sub_one (q : ℍ[ℝ]) : ‖pureComponent q‖ ≤ ‖q - 1‖ := by
  have : pureComponent q = pureComponent (q - 1) := by
    rw [pureComponent_sub, pureComponent_one, sub_zero]
  rw [this]
  exact norm_pureComponent_le _
theorem pureComponent_eq_im (q : ℍ[ℝ]) : pureComponent q = q.im := by apply _root_.YangMills.Construction.PlaquetteExpansion.pureComponent_eq_im <;> assumption
theorem quatClose_of_norm_eq_one {W X : ℍ[ℝ]} (hW : ‖W‖ = 1) (hX : ‖X‖ = 1) :
    QuatClose W X (pureComponent (X * star W) * W) ‖X * star W - 1‖ := by
  set g := X * star W with hg
  have hgn : ‖g‖ = 1 := by rw [hg, norm_mul, norm_star, hW, hX, one_mul]
  have hgW : g * W = X := by rw [hg, mul_assoc, star_mul_self_of_norm_eq_one hW, mul_one]
  have hd : X - W = (g - 1) * W := by rw [sub_mul, hgW, one_mul]
  refine ⟨hW.le, hX.le, ?_, ?_, ?_⟩
  · rw [hd, norm_mul, hW, mul_one]
  · rw [norm_mul, hW, mul_one]
    exact norm_pureComponent_le_norm_sub_one g
  · have e : X - W - pureComponent g * W = (((g.re - 1 : ℝ) : ℍ[ℝ])) * W := by
      have h1 := re_add_pureComponent g
      have h2 : ((g.re - 1 : ℝ) : ℍ[ℝ]) = (g.re : ℍ[ℝ]) - 1 := by
        ext <;> simp
      rw [hd, ← sub_mul, h2]
      congr 1
      nth_rewrite 1 [← h1]
      abel
    rw [e, norm_mul, hW, mul_one, Quaternion.norm_coe, Real.norm_eq_abs]
    have h3 := norm_sub_one_sq_of_norm_eq_one hgn
    have h4 : |g.re - 1| = 1 - g.re := by
      rw [abs_of_nonpos]
      · ring
      · have := quaternion_re_le_norm g
        rw [hgn] at this
        linarith
    rw [h4]
    nlinarith [sq_nonneg ‖g - 1‖]
theorem norm_polarUnit_sub_one_le (q : ℍ[ℝ]) :
    ‖((polarUnit q : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * ‖q - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.normSubOne_polarUnit_le <;> assumption
theorem plaquette_change_lower_bound {P Q d : ℍ[ℝ]} {ε : ℝ} (hP : ‖P‖ = 1) (hs : ‖Q - P - d‖ ≤ ε ^ 2)
    (hQ : ‖Q‖ = 1) (ht : (d * star P).re = 0) :
    P.re * (‖Q - P‖ ^ 2 / 2) - ε ^ 2 * ‖pureComponent P‖ ≤ (1 - Q.re) - (1 - P.re) - (- d.re) := by
  set w := Q * star P with hw
  set E := (Q - P - d) * star P with hE
  have hwn : ‖w‖ = 1 := by rw [hw, norm_mul, norm_star, hP, hQ, one_mul]
  have hwP : w - 1 = (Q - P) * star P := by rw [hw, sub_mul, mul_star_self_of_norm_eq_one hP]
  have hEP : E * P = Q - P - d := by rw [hE, mul_assoc, star_mul_self_of_norm_eq_one hP, mul_one]
  have hEre : E.re = w.re - 1 := by
    have : E = w - 1 - d * star P := by rw [hE, hwP, sub_mul, sub_mul]
    rw [this]
    simp only [Quaternion.re_sub, ht, Quaternion.re_one]
    ring
  have hn : ‖w - 1‖ = ‖Q - P‖ := by rw [hwP, norm_mul, norm_star, hP, mul_one]
  have h1 := norm_sub_one_sq_of_norm_eq_one hwn
  rw [hn] at h1
  have h2 : (E * P).re = P.re * E.re + (E * pureComponent P).re := by
    conv_lhs => rw [← re_add_pureComponent P]
    have hc : pureComponent ((P.re : ℍ[ℝ]) + pureComponent P) = pureComponent P := by
      rw [re_add_pureComponent]
    rw [mul_add, Quaternion.re_add, quat_re_mul_coe]
  have h3 : Q.re - P.re - d.re = (E * P).re := by
    rw [hEP]
    simp
  have h4 := quat_abs_re_mul_le E (pureComponent P)
  have h5 : ‖E‖ ≤ ε ^ 2 := by rw [hE, norm_mul, norm_star, hP, mul_one]; exact hs
  have h6 : (E * pureComponent P).re ≤ ε ^ 2 * ‖pureComponent P‖ :=
    (le_abs_self _).trans (h4.trans (mul_le_mul_of_nonneg_right h5 (norm_nonneg _)))
  have h7 : E.re = - (‖Q - P‖ ^ 2 / 2) := by rw [hEre]; linarith
  rw [h7] at h2
  nlinarith
theorem norm_unit_ratio_sub_one_le {u u₀ : ℍ[ℝ]} {r r₀ G : ℝ} (hu₀ : ‖u₀‖ = 1) (hr : 1 / 2 ≤ r)
    (hD : ‖r • u - r₀ • u₀‖ ≤ G) (hrr : |r - r₀| ≤ G) : ‖u * star u₀ - 1‖ ≤ 4 * G := by
  have e : r • (u * star u₀ - 1) = (r • u - r₀ • u₀) * star u₀ + ((r₀ - r) • (1 : ℍ[ℝ])) := by
    rw [sub_mul, smul_mul_assoc, smul_mul_assoc, mul_star_self_of_norm_eq_one hu₀, smul_sub, sub_smul]
    abel
  have e2 : r * ‖u * star u₀ - 1‖ ≤ 2 * G := by
    have h0 : ‖r • (u * star u₀ - 1)‖ = r * ‖u * star u₀ - 1‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    rw [← h0, e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_star, hu₀, mul_one, norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_sub_comm]
    linarith
  have h1 := norm_nonneg (u * star u₀ - 1)
  nlinarith
theorem leading_factor_bound_real {r b G M e : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 4 * G)
    (he : |e| ≤ G ^ 2) (hM0 : 0 ≤ M) (hM : M ≤ 1 / 2) :
    |(r * (b ^ 2 / 2) + e) * (M ^ 2 / 2)| ≤ M * (3 * G ^ 2) := by
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ M ^ 2 / 2)]
  have b2 : b ^ 2 ≤ 16 * G ^ 2 := by nlinarith
  have a1 : |r * (b ^ 2 / 2) + e| ≤ 9 * G ^ 2 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by positivity)]
    have : r * (b ^ 2 / 2) ≤ 1 * (b ^ 2 / 2) := mul_le_mul_of_nonneg_right hr1 (by positivity)
    linarith
  have a2 : M ^ 2 / 2 ≤ M / 4 := by nlinarith
  have a3 : (9 * G ^ 2) * (M / 4) ≤ M * (3 * G ^ 2) := by nlinarith [sq_nonneg G]
  exact (mul_le_mul a1 a2 (by positivity) (by positivity)).trans a3
theorem leading_factor_bound {u u₀ m₀ Ad : ℍ[ℝ]} {r r₀ G : ℝ} (hu : ‖u‖ = 1) (hu₀ : ‖u₀‖ = 1)
    (hm₀ : ‖m₀‖ = 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hh : ‖u * star u₀ - 1‖ ≤ 4 * G)
    (hE : ‖r • u - r₀ • u₀ - Ad‖ ≤ G ^ 2) (hM : ‖m₀ - 1‖ ≤ 1 / 2) :
    |(r - r₀ - (Ad * star u₀).re) * (1 - m₀.re)| ≤ ‖m₀ - 1‖ * (3 * G ^ 2) := by
  have hhn : ‖u * star u₀‖ = 1 := by rw [norm_mul, norm_star, hu, hu₀, one_mul]
  have h3 : ((r • u - r₀ • u₀ - Ad) * star u₀).re = r * (u * star u₀).re - r₀ - (Ad * star u₀).re := by
    rw [sub_mul, sub_mul, smul_mul_assoc, smul_mul_assoc, mul_star_self_of_norm_eq_one hu₀]
    simp
  have h4 := norm_sub_one_sq_of_norm_eq_one hhn
  have hB : r - r₀ - (Ad * star u₀).re =
      r * (‖u * star u₀ - 1‖ ^ 2 / 2) + ((r • u - r₀ • u₀ - Ad) * star u₀).re := by
    rw [h3, h4]
    ring
  have hμ : 1 - m₀.re = ‖m₀ - 1‖ ^ 2 / 2 := by
    have := norm_sub_one_sq_of_norm_eq_one hm₀
    linarith
  rw [hB, hμ]
  refine leading_factor_bound_real hr0 hr1 (norm_nonneg _) hh ?_ (norm_nonneg _) hM
  refine (quat_abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_star, hu₀, mul_one]
  exact hE
theorem fit_lower_bound_real {t1 t2 t3 t4 t5 E2 G M a : ℝ} (h1 : |t1| ≤ M * (3 * G ^ 2)) (h2 : E2 ≤ t2)
    (h3 : |t3| ≤ G * (a * M)) (h4 : |t4| ≤ a * (4 * G) * M) (h5 : |t5| ≤ G ^ 2 * M) (hM : 0 ≤ M) :
    E2 - M * (13 * G ^ 2 + 3 * a ^ 2) ≤ t1 + t2 + t3 - t4 + t5 := by
  have x1 := (abs_le.1 h1).1
  have x3 := (abs_le.1 h3).1
  have x4 := (abs_le.1 h4).2
  have x5 := (abs_le.1 h5).1
  have hsq : 0 ≤ 9 * G ^ 2 + 3 * a ^ 2 - 5 * G * a := by
    nlinarith [sq_nonneg (G - a), sq_nonneg G, sq_nonneg a]
  have h6 := mul_nonneg hM hsq
  nlinarith
theorem fit_lower_bound_units {u u₀ m₀ g Ad : ℍ[ℝ]} {r r₀ G : ℝ} (hg : ‖g‖ = 1) (hu : ‖u‖ = 1)
    (hu₀ : ‖u₀‖ = 1) (hm₀ : ‖m₀‖ = 1)
    (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1) (hD : ‖r • u - r₀ • u₀‖ ≤ G) (hrr : |r - r₀| ≤ G)
    (hE : ‖r • u - r₀ • u₀ - Ad‖ ≤ G ^ 2) (hM : ‖m₀ - 1‖ ≤ 1 / 2) :
    ‖g * (m₀ * u₀) * star u * star m₀ - 1‖ ^ 2 / 8 - ‖m₀ - 1‖ * (13 * G ^ 2 + 3 * ‖g - 1‖ ^ 2) ≤
      r - ((r • u) * star (g * (m₀ * u₀))).re - (r₀ - ((r₀ • u₀) * star (m₀ * u₀)).re) -
        ((Ad * star u₀).re - (Ad * star (m₀ * u₀)).re + ((r₀ • u₀) * star (m₀ * u₀) * pureComponent g).re) := by
  rw [fit_change_eq Ad r r₀ hu₀ hm₀]
  have hG : 0 ≤ G := (norm_nonneg _).trans hD
  have hr0 : 0 ≤ r := by linarith
  have hh1 := norm_unit_ratio_sub_one_le hu₀ hr hD hrr
  have hμ1 : 1 / 2 ≤ m₀.re := by
    have h1 := quat_abs_re_le_norm (m₀ - 1)
    have h2 := (abs_le.1 h1).1
    simp only [Quaternion.re_sub, Quaternion.re_one] at h2
    linarith
  have hen : ‖g * (m₀ * u₀) * star u * star m₀‖ = 1 := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_star, norm_star, hg, hm₀, hu₀, hu]
    norm_num
  have ht2 : ‖g * (m₀ * u₀) * star u * star m₀ - 1‖ ^ 2 / 8 ≤
      r * (1 - (g * (m₀ * u₀) * star u * star m₀).re) * m₀.re := by
    have h1 := norm_sub_one_sq_of_norm_eq_one hen
    have h2 : 1 - (g * (m₀ * u₀) * star u * star m₀).re =
        ‖g * (m₀ * u₀) * star u * star m₀ - 1‖ ^ 2 / 2 := by
      linarith
    rw [h2]
    generalize ‖g * (m₀ * u₀) * star u * star m₀ - 1‖ = b
    have h3 : 0 ≤ b ^ 2 / 2 := by positivity
    calc b ^ 2 / 8 = (1 / 2) * (b ^ 2 / 2) * (1 / 2) := by ring
      _ ≤ r * (b ^ 2 / 2) * m₀.re :=
        mul_le_mul (mul_le_mul_of_nonneg_right hr h3) hμ1 (by norm_num) (by positivity)
  have hPn : ‖pureComponent m₀‖ ≤ ‖m₀ - 1‖ := norm_pureComponent_le_norm_sub_one m₀
  have hxn : ‖pureComponent g‖ ≤ ‖g - 1‖ := norm_pureComponent_le_norm_sub_one g
  have ht3 : |(r₀ - r) * (pureComponent g * pureComponent m₀).re| ≤ G * (‖g - 1‖ * ‖m₀ - 1‖) := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul hrr ((quat_abs_re_mul_le _ _).trans
      (mul_le_mul hxn hPn (norm_nonneg _) (norm_nonneg _))) (abs_nonneg _) hG
  have hf1 : ‖m₀ * star (u * star u₀) * star m₀ - 1‖ = ‖u * star u₀ - 1‖ := by
    have e1 : m₀ * star (u * star u₀) * star m₀ - 1 = m₀ * (star (u * star u₀) - 1) * star m₀ := by
      rw [mul_sub, sub_mul, mul_one, mul_star_self_of_norm_eq_one hm₀]
    rw [e1, norm_mul, norm_mul, norm_star, hm₀, one_mul, mul_one]
    have : star (u * star u₀) - 1 = star (u * star u₀ - 1) := by simp
    rw [this, norm_star]
  have ht4 : |r * ((g - 1) * (m₀ * star (u * star u₀) * star m₀ - 1) * pureComponent m₀).re| ≤
      ‖g - 1‖ * (4 * G) * ‖m₀ - 1‖ := by
    rw [abs_mul, abs_of_nonneg hr0]
    have b1 : |((g - 1) * (m₀ * star (u * star u₀) * star m₀ - 1) * pureComponent m₀).re| ≤
        ‖g - 1‖ * (4 * G) * ‖m₀ - 1‖ := by
      refine (quat_abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, hf1]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hh1 (norm_nonneg _)) hPn (norm_nonneg _) (by positivity)
    calc r * _ ≤ 1 * (‖g - 1‖ * (4 * G) * ‖m₀ - 1‖) := mul_le_mul hr1 b1 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hE₁n : ‖(r • u - r₀ • u₀ - Ad) * star u₀‖ ≤ G ^ 2 := by
    rw [norm_mul, norm_star, hu₀, mul_one]
    exact hE
  have ht5 : |(((r • u - r₀ • u₀ - Ad) * star u₀) * pureComponent m₀).re| ≤ G ^ 2 * ‖m₀ - 1‖ :=
    (quat_abs_re_mul_le _ _).trans (mul_le_mul hE₁n hPn (norm_nonneg _) (sq_nonneg G))
  exact fit_lower_bound_real (leading_factor_bound hu hu₀ hm₀ hr0 hr1 hh1 hE hM) ht2 ht3 ht4 ht5
    (norm_nonneg _)
theorem fit_lower_bound {A A₀ Ad g W' : ℍ[ℝ]} {G : ℝ} (hg : ‖g‖ = 1) (hW : ‖W'‖ = 1) (hr : 1 / 2 ≤ ‖A‖)
    (hr1 : ‖A‖ ≤ 1) (h0 : A₀ ≠ 0) (hD : ‖A - A₀‖ ≤ G) (hE : ‖A - A₀ - Ad‖ ≤ G ^ 2)
    (hm : ‖W' * star (‖A₀‖⁻¹ • A₀) - 1‖ ≤ 1 / 2) :
    ‖g * W' * star (‖A‖⁻¹ • A) * star (W' * star (‖A₀‖⁻¹ • A₀)) - 1‖ ^ 2 / 8 -
        ‖W' * star (‖A₀‖⁻¹ • A₀) - 1‖ * (13 * G ^ 2 + 3 * ‖g - 1‖ ^ 2) ≤
      ‖A‖ - (A * star (g * W')).re - (‖A₀‖ - (A₀ * star W').re) -
        ((Ad * star (‖A₀‖⁻¹ • A₀)).re - (Ad * star W').re + (A₀ * star W' * pureComponent g).re) := by
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, norm_zero] at hr
    linarith
  have hn₀ : ‖A₀‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hn : ‖A‖ ≠ 0 := norm_ne_zero_iff.2 hA0
  have hun : ‖‖A‖⁻¹ • A‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm]
    exact inv_mul_cancel₀ hn
  have hu₀n : ‖‖A₀‖⁻¹ • A₀‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm]
    exact inv_mul_cancel₀ hn₀
  have hm₀n : ‖W' * star (‖A₀‖⁻¹ • A₀)‖ = 1 := by rw [norm_mul, norm_star, hW, hu₀n, one_mul]
  have hAu : ‖A‖ • (‖A‖⁻¹ • A) = A := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hAu₀ : ‖A₀‖ • (‖A₀‖⁻¹ • A₀) = A₀ := by rw [smul_smul, mul_inv_cancel₀ hn₀, one_smul]
  have hWm : W' * star (‖A₀‖⁻¹ • A₀) * (‖A₀‖⁻¹ • A₀) = W' := by
    rw [mul_assoc, star_mul_self_of_norm_eq_one hu₀n, mul_one]
  have h := fit_lower_bound_units (g := g) (Ad := Ad) (G := G) (r := ‖A‖) (r₀ := ‖A₀‖) (u := ‖A‖⁻¹ • A)
    (u₀ := ‖A₀‖⁻¹ • A₀) (m₀ := W' * star (‖A₀‖⁻¹ • A₀)) hg hun hu₀n hm₀n hr hr1
    (by rw [hAu, hAu₀]; exact hD)
    ((abs_norm_sub_norm_le A A₀).trans hD) (by rw [hAu, hAu₀]; exact hE) hm
  rw [hWm, hAu, hAu₀] at h
  exact h
theorem top_density_bound {e m₀ K : ℍ[ℝ]} (he : ‖e‖ = 1) (hm : ‖m₀‖ = 1) (hK : ‖K‖ = 1)
    (hk : ‖K - 1‖ ≤ 1 / 8) :
    (1 / 32) * ‖(K * (e * m₀) * star K * star m₀).im‖ ^ 2 ≤
      ‖e - 1‖ ^ 2 / 8 + ‖K - 1‖ ^ 2 * ‖m₀ - 1‖ ^ 2 := by
  set m := e * m₀ with hmdef
  have hem : m * star m₀ = e := by rw [hmdef, mul_assoc, mul_star_self_of_norm_eq_one hm, mul_one]
  have h1 : ‖K * m * star K - m‖ ≤ 2 * ‖K - 1‖ * ‖m - 1‖ := by
    have e1 : K * m * star K - m = ((K - 1) * (m - 1) - (m - 1) * (K - 1)) * star K := by
      have : (K - 1) * (m - 1) - (m - 1) * (K - 1) = K * m - m * K := by noncomm_ring
      rw [this, sub_mul, mul_assoc m K, mul_star_self_of_norm_eq_one hK, mul_one]
    rw [e1, norm_mul, norm_star, hK, mul_one]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    linarith [mul_comm ‖K - 1‖ ‖m - 1‖]
  have h2 : ‖m - 1‖ ≤ ‖e - 1‖ + ‖m₀ - 1‖ := by
    have e1 : m - 1 = (e - 1) * m₀ + (m₀ - 1) := by rw [hmdef]; noncomm_ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hm, mul_one]
  have h3 : ‖K * m * star K * star m₀ - 1‖ ≤ ‖e - 1‖ + ‖K * m * star K - m‖ := by
    have e1 : K * m * star K * star m₀ - 1 = (e - 1) + (K * m * star K - m) * star m₀ := by
      rw [sub_mul, hem]
      abel
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_star, hm, mul_one]
  have h4 : ‖(K * m * star K * star m₀).im‖ ≤ ‖K * m * star K * star m₀ - 1‖ := by
    rw [← pureComponent_eq_im]
    exact norm_pureComponent_le_norm_sub_one _
  set a := ‖e - 1‖
  set b := ‖m₀ - 1‖
  set k := ‖K - 1‖
  have ha : 0 ≤ a := norm_nonneg _
  have h5 : ‖(K * m * star K * star m₀).im‖ ≤ (5 / 4) * a + 2 * k * b := by
    have h6 : ‖K * m * star K - m‖ ≤ 2 * k * (a + b) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    have h7 : 2 * k * a ≤ (1 / 4) * a := by nlinarith
    nlinarith
  have h8 := pow_le_pow_left₀ (norm_nonneg _) h5 2
  nlinarith [sq_nonneg ((5 / 4) * a - 2 * k * b)]
end
section
variable {F : BlockFrame} {j : ℕ}
def flowField (W : F.GaugeField j) (y : F.Site j → Fin 4 → imaginaryQuaternions) (τ : ℝ) : F.GaugeField j :=
  fun x i => expUnit (τ • y x i) * W x i
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem expUnit_zero_smul (y : imaginaryQuaternions) : expUnit ((0 : ℝ) • y) = 1 := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.expUnit_zero_smul <;> assumption
def starCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := star
      map_add' := star_add
      map_smul' := fun c q => by ext <;> simp }
theorem hasDerivAt_star_zero {f : ℝ → ℍ[ℝ]} {f' : ℍ[ℝ]} (h : HasDerivAt f f' 0) :
    HasDerivAt (fun τ => star (f τ)) (star f') 0 :=
  starCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
def reCLM : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => q.re
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
theorem flowField_zero (W : F.GaugeField j) (y : F.Site j → Fin 4 → imaginaryQuaternions) :
    flowField W y 0 = W := by
  funext x i
  simp [flowField, expUnit_zero]
def gapDirection (X W : F.GaugeField j) : F.Site j → Fin 4 → imaginaryQuaternions :=
  fun x i => imaginaryPart ((X x i * (W x i)⁻¹ : UnitQuaternion) : ℍ[ℝ])
def bondGap (X W : F.GaugeField j) (b : F.Site j × Fin 4) : ℝ :=
  ‖((X b.1 b.2 * (W b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖
theorem bondGap_nonneg (X W : F.GaugeField j) (b : F.Site j × Fin 4) : 0 ≤ bondGap X W b := norm_nonneg _
theorem hasDerivAt_expUnit_mul (y : imaginaryQuaternions) (W : UnitQuaternion) :
    HasDerivAt (fun τ : ℝ => ((expUnit (τ • y) * W : UnitQuaternion) : ℍ[ℝ])) ((y : ℍ[ℝ]) * (W : ℍ[ℝ])) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (y : ℍ[ℝ]) (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h.mul_const (W : ℍ[ℝ])
theorem quatClose_unitQuaternion (W X : UnitQuaternion) :
    QuatClose (W : ℍ[ℝ]) (X : ℍ[ℝ])
      (((imaginaryPart ((X * W⁻¹ : UnitQuaternion) : ℍ[ℝ]) : imaginaryQuaternions) : ℍ[ℝ]) * (W : ℍ[ℝ]))
      ‖((X * W⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
  quatClose_of_norm_eq_one (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion W) (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion X)
theorem re_tangent_mul_star (y : imaginaryQuaternions) (W : UnitQuaternion) :
    (((y : ℍ[ℝ]) * (W : ℍ[ℝ])) * star (W : ℍ[ℝ])).re = 0 := by
  rw [mul_assoc, mul_star_self_of_norm_eq_one (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion W), mul_one]
  exact y.2
theorem re_star_tangent_mul_star (y : imaginaryQuaternions) (W : UnitQuaternion) :
    (star ((y : ℍ[ℝ]) * (W : ℍ[ℝ])) * star (star (W : ℍ[ℝ]))).re = 0 := by
  rw [star_star, star_mul, quat_re_mul_comm, ← mul_assoc,
    mul_star_self_of_norm_eq_one (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion W), one_mul, quat_re_star]
  exact y.2
theorem re_tangent_product {ps pr d₁ d₂ : ℍ[ℝ]} (hps : ‖ps‖ = 1) (hpr : ‖pr‖ = 1)
    (t₁ : (d₁ * star ps).re = 0) (t₂ : (d₂ * star pr).re = 0) :
    ((d₁ * pr + ps * d₂) * star (ps * pr)).re = 0 := by
  rw [star_mul, add_mul, Quaternion.re_add]
  have e1 : d₁ * pr * (star pr * star ps) = d₁ * star ps := by
    rw [mul_assoc, ← mul_assoc pr, mul_star_self_of_norm_eq_one hpr, one_mul]
  have e2 : (ps * d₂ * (star pr * star ps)).re = (d₂ * star pr).re := by
    rw [mul_assoc, quat_re_mul_comm, mul_assoc, mul_assoc, star_mul_self_of_norm_eq_one hps, mul_one]
  rw [e1, e2, t₁, t₂, add_zero]
def bondOfStep (x : F.Site j) (st : PathStep) : F.Site j × Fin 4 :=
  if st.2 then (x, st.1) else (x - unitStep j st.1, st.1)
theorem linkValue_close (W X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    ∃ d : ℍ[ℝ], HasDerivAt (fun τ : ℝ =>
        ((linkValue (flowField W (gapDirection X W) τ) x st : UnitQuaternion) : ℍ[ℝ])) d 0 ∧
      QuatClose (linkValue W x st : UnitQuaternion) (linkValue X x st : UnitQuaternion) d
        (bondGap X W (bondOfStep x st)) ∧
      (d * star ((linkValue W x st : UnitQuaternion) : ℍ[ℝ])).re = 0 := by
  obtain ⟨i, b⟩ := st
  cases b
  · simp only [linkValue, bondOfStep, Bool.false_eq_true, if_false]
    refine ⟨star (((gapDirection X W (x - unitStep j i) i : imaginaryQuaternions) : ℍ[ℝ]) *
      (W (x - unitStep j i) i : ℍ[ℝ])), ?_, ?_, ?_⟩
    · exact hasDerivAt_star_zero (hasDerivAt_expUnit_mul (gapDirection X W (x - unitStep j i) i)
        (W (x - unitStep j i) i))
    · exact (quatClose_unitQuaternion (W (x - unitStep j i) i) (X (x - unitStep j i) i)).star
    · exact re_star_tangent_mul_star _ _
  · simp only [linkValue, bondOfStep, if_true]
    exact ⟨_, hasDerivAt_expUnit_mul (gapDirection X W x i) (W x i), quatClose_unitQuaternion (W x i) (X x i),
      re_tangent_mul_star _ _⟩
def HolonomyClose (W X : F.GaugeField j) (x : F.Site j) (l : List PathStep) (ε : ℝ) : Prop :=
  ∃ d : ℍ[ℝ], HasDerivAt (fun τ : ℝ =>
      ((pathHolonomy (flowField W (gapDirection X W) τ) x l : UnitQuaternion) : ℍ[ℝ])) d 0 ∧
    QuatClose (pathHolonomy W x l : UnitQuaternion) (pathHolonomy X x l : UnitQuaternion) d ε ∧
    (d * star ((pathHolonomy W x l : UnitQuaternion) : ℍ[ℝ])).re = 0
theorem holonomyClose_nil (W X : F.GaugeField j) (x : F.Site j) : HolonomyClose W X x [] 0 := by
  refine ⟨0, hasDerivAt_const _ _, QuatClose.refl (by simp [pathHolonomy]), by simp⟩
theorem HolonomyClose.mono {W X : F.GaugeField j} {x : F.Site j} {l : List PathStep} {ε ε' : ℝ}
    (h : HolonomyClose W X x l ε) (he : ε ≤ ε') : HolonomyClose W X x l ε' := by
  obtain ⟨d, h1, h2, h3⟩ := h
  exact ⟨d, h1, h2.mono he, h3⟩
theorem holonomyClose_cons {W X : F.GaugeField j} {x : F.Site j} {st : PathStep} {r : List PathStep} {ε : ℝ}
    (h : HolonomyClose W X (x + stepDisplacement j st) r ε) :
    HolonomyClose W X x (st :: r) (bondGap X W (bondOfStep x st) + ε) := by
  obtain ⟨d₁, hd₁, n₁, t₁⟩ := linkValue_close W X x st
  obtain ⟨d₂, hd₂, n₂, t₂⟩ := h
  have hm := hd₁.fun_mul hd₂
  simp only [flowField_zero] at hm
  exact ⟨_, hm, n₁.mul n₂, re_tangent_product (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _) (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _) t₁ t₂⟩
theorem holonomyClose_of_allAlong (W X : F.GaugeField j) (x0 : F.Site j) (p : Lattice4 → Prop) {ε : ℝ}
    (hb : ∀ v k, p v → p (v + basisVector k) → bondGap X W (x0 + siteOfCoords j v, k) ≤ ε) :
    ∀ (l : List PathStep) (v : Lattice4), LatticePaths.AllAlong p v l →
      HolonomyClose W X (x0 + siteOfCoords j v) l (l.length * ε) := by
  intro l
  induction l with
  | nil =>
    intro v _
    simpa using holonomyClose_nil W X _
  | cons st r ih =>
    intro v hp
    have hnext : x0 + siteOfCoords j v + stepDisplacement j st =
        x0 + siteOfCoords j (v + FlatPairing.stepDisplacement st) := by
      rw [ChartCoordinates.stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add]
    have h1 := ih _ hp.2
    rw [← hnext] at h1
    have h2 := holonomyClose_cons h1
    refine h2.mono ?_
    have hv : p v := hp.1
    have hw : p (v + FlatPairing.stepDisplacement st) := LatticePaths.allAlong_head hp.2
    have h3 : bondGap X W (bondOfStep (x0 + siteOfCoords j v) st) ≤ ε := by
      obtain ⟨i, b⟩ := st
      cases b
      · simp only [bondOfStep, Bool.false_eq_true, if_false]
        have e : x0 + siteOfCoords j v - unitStep j i = x0 + siteOfCoords j (v - basisVector i) := by
          rw [siteOfCoords_sub, unitStep_eq]
          abel
        rw [e]
        have e2 : v + FlatPairing.stepDisplacement (i, false) = v - basisVector i := by
          simp [FlatPairing.stepDisplacement, sub_eq_add_neg]
        rw [e2] at hw
        exact hb _ i hw (by simpa using hv)
      · simp only [bondOfStep, if_true]
        have e2 : v + FlatPairing.stepDisplacement (i, true) = v + basisVector i := by
          simp [FlatPairing.stepDisplacement]
        rw [e2] at hw
        exact hb _ i hv hw
    simp only [List.length_cons]
    push_cast
    linarith
theorem contourAverage_eq_smul_sum (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) :
    _root_.YangMills.Construction.BlockAverages.contourAverage X c = (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
      ∑ q ∈ centredCube F.blockSide ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4))),
        ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide q.1 q.2 c.2) : UnitQuaternion) : ℍ[ℝ]) := by
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage
  rw [Finset.sum_product]
theorem contour_weight_mul_card (hodd : Odd F.blockSide) :
    (1 / (24 * (F.blockSide : ℝ) ^ 4)) *
      ((centredCube F.blockSide ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4)))).card : ℝ) = 1 := by
  have hL : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hodd.pos.ne'
  rw [Finset.card_product, LatticePaths.card_centredCube hodd, Finset.card_univ, Fintype.card_perm]
  simp [Nat.factorial]
  field_simp
theorem contourAverage_close (hodd : Odd F.blockSide) (W X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ a k, a ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      a + basisVector k ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      bondGap X W (refineSite c.1 + siteOfCoords j a, k) ≤ ε) :
    ∃ d : ℍ[ℝ], HasDerivAt (fun τ : ℝ => _root_.YangMills.Construction.BlockAverages.contourAverage (flowField W (gapDirection X W) τ) c) d 0 ∧
      QuatClose (_root_.YangMills.Construction.BlockAverages.contourAverage W c) (_root_.YangMills.Construction.BlockAverages.contourAverage X c) d (5 * F.blockSide * ε) := by
  classical
  have hL : 1 ≤ F.blockSide := hodd.pos
  have key : ∀ q : Lattice4 × Equiv.Perm (Fin 4),
      q ∈ centredCube F.blockSide ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4))) →
      HolonomyClose W X (refineSite c.1) (bondContour F.blockSide q.1 q.2 c.2) (5 * F.blockSide * ε) := by
    intro q hq
    have hh := (Finset.mem_product.1 hq).1
    have h1 := holonomyClose_of_allAlong W X (refineSite c.1)
      (fun v => v ∈ FlatPairing.twoBlockHull F.blockSide c.2) hb
      (bondContour F.blockSide q.1 q.2 c.2) 0 (LatticePaths.bondContour_spec q.2 c.2 hL hh).1
    rw [ChartCoordinates.add_siteOfCoords_zero] at h1
    refine h1.mono (mul_le_mul_of_nonneg_right ?_ hε)
    exact_mod_cast LatticePaths.length_bondContour_le q.2 c.2 hL hh
  choose! d hd hn _ using key
  refine ⟨(1 / (24 * (F.blockSide : ℝ) ^ 4)) •
    ∑ q ∈ centredCube F.blockSide ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4))), d q, ?_, ?_⟩
  · have h2 := (HasDerivAt.fun_sum
      (u := centredCube F.blockSide ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4)))) hd).const_smul
      (1 / (24 * (F.blockSide : ℝ) ^ 4))
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
    exact contourAverage_eq_smul_sum _ c
  · rw [contourAverage_eq_smul_sum W, contourAverage_eq_smul_sum X]
    exact QuatClose.average _ (by positivity) (contour_weight_mul_card hodd).le (by positivity) _ _ d hn
theorem norm_balancingGauge_sub_one_le (hodd : Odd F.blockSide) (X W : F.GaugeField j) (y : F.Site (j + 1))
    (p : Lattice4 → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (hp : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4), LatticePaths.AllAlong p 0 (axisPath h π))
    (hb : ∀ v k, p v → p (v + basisVector k) → bondGap X W (refineSite y + siteOfCoords j v, k) ≤ ε) :
    ‖((balancingGauge X W y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * F.blockSide * ε := by
  classical
  have hL : 1 ≤ F.blockSide := hodd.pos
  rw [balancingGauge, norm_coe_inv_sub_one]
  refine (norm_polarUnit_sub_one_le _).trans ?_
  have hw := contour_weight_mul_card (F := F) hodd
  set s := centredCube F.blockSide ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4))) with hs
  set w : ℝ := 1 / (24 * (F.blockSide : ℝ) ^ 4) with hwdef
  have hw0 : 0 ≤ w := by positivity
  have e : relativePathAverage X W y - 1 = w • ∑ q ∈ s,
      (((pathHolonomy X (refineSite y) (axisPath q.1 q.2) *
        (pathHolonomy W (refineSite y) (axisPath q.1 q.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) := by
    rw [Finset.sum_sub_distrib, smul_sub]
    have h1 : w • ∑ _q ∈ s, (1 : ℍ[ℝ]) = 1 := by
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hw, one_smul]
    rw [h1]
    congr 1
    unfold relativePathAverage
    rw [hs, Finset.sum_product]
  rw [e]
  have h2 : ‖w • ∑ q ∈ s, (((pathHolonomy X (refineSite y) (axisPath q.1 q.2) *
      (pathHolonomy W (refineSite y) (axisPath q.1 q.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1)‖ ≤
        2 * F.blockSide * ε := by
    refine norm_smul_sum_le_of_mul_card_le_one s hw0 hw.le (by positivity) _ fun q hq => ?_
    have hh := (Finset.mem_product.1 hq).1
    have h1 := holonomyClose_of_allAlong W X (refineSite y) p hb (axisPath q.1 q.2) 0 (hp _ hh _)
    rw [ChartCoordinates.add_siteOfCoords_zero] at h1
    obtain ⟨d, _, hn, _⟩ := h1
    have e2 : ((pathHolonomy X (refineSite y) (axisPath q.1 q.2) *
        (pathHolonomy W (refineSite y) (axisPath q.1 q.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 =
        (((pathHolonomy X (refineSite y) (axisPath q.1 q.2) : UnitQuaternion) : ℍ[ℝ]) -
          ((pathHolonomy W (refineSite y) (axisPath q.1 q.2) : UnitQuaternion) : ℍ[ℝ])) *
          star ((pathHolonomy W (refineSite y) (axisPath q.1 q.2) : UnitQuaternion) : ℍ[ℝ]) := by
      rw [sub_mul, mul_star_self_of_norm_eq_one (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _)]
      rfl
    rw [e2, norm_mul, norm_star, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, mul_one]
    refine hn.sub_le.trans (mul_le_mul_of_nonneg_right ?_ hε)
    have hlen := LatticePaths.length_axisPath q.1 q.2
    have hb2 : ∀ μ, ((q.1 μ).natAbs : ℕ) ≤ (F.blockSide - 1) / 2 := by
      intro μ
      have h1 := ((LatticePaths.mem_centredCube_iff F.blockSide q.1).1 hh) μ
      omega
    have : (axisPath q.1 q.2).length ≤ 2 * F.blockSide := by
      have a0 := hb2 (q.2 0)
      have a1 := hb2 (q.2 1)
      have a2 := hb2 (q.2 2)
      have a3 := hb2 (q.2 3)
      omega
    exact_mod_cast this
  linarith
end
section
variable {F : BlockFrame} {j : ℕ}
def flowGauge (k : F.Site (j + 1) → UnitQuaternion) (l : F.Site (j + 1) → imaginaryQuaternions) (τ : ℝ) :
    F.Site (j + 1) → UnitQuaternion :=
  fun y => expUnit (τ • l y) * k y
def gaugeGapDirection (k' k : F.Site (j + 1) → UnitQuaternion) : F.Site (j + 1) → imaginaryQuaternions :=
  fun y => imaginaryPart ((k' y * (k y)⁻¹ : UnitQuaternion) : ℍ[ℝ])
def gaugeGap (k' k : F.Site (j + 1) → UnitQuaternion) (y : F.Site (j + 1)) : ℝ :=
  ‖((k' y * (k y)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖
theorem flowGauge_zero (k : F.Site (j + 1) → UnitQuaternion) (l : F.Site (j + 1) → imaginaryQuaternions) :
    flowGauge k l 0 = k := by
  funext y
  simp [flowGauge, expUnit_zero]
theorem gaugedContourAverage_close (hodd : Odd F.blockSide) (W X : F.GaugeField j)
    (kW k' : F.Site (j + 1) → UnitQuaternion)
    (c : F.Site (j + 1) × Fin 4) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ a i, a ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      a + basisVector i ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      bondGap X W (refineSite c.1 + siteOfCoords j a, i) ≤ ε) :
    ∃ d : ℍ[ℝ], HasDerivAt (fun τ : ℝ =>
        gaugedContourAverage (flowField W (gapDirection X W) τ) (flowGauge kW (gaugeGapDirection k' kW) τ) c) d 0 ∧
      QuatClose (gaugedContourAverage W kW c) (gaugedContourAverage X k' c) d
        (gaugeGap k' kW c.1 + 5 * F.blockSide * ε + gaugeGap k' kW (c.1 + unitStep (j + 1) c.2)) := by
  obtain ⟨d, hd, hn⟩ := contourAverage_close hodd W X c hε hb
  have h1 := hasDerivAt_expUnit_mul (gaugeGapDirection k' kW c.1) (kW c.1)
  have h2 := hasDerivAt_star_zero (hasDerivAt_expUnit_mul (gaugeGapDirection k' kW (c.1 + unitStep (j + 1) c.2))
    (kW (c.1 + unitStep (j + 1) c.2)))
  have hm := (h1.fun_mul hd).fun_mul h2
  simp only [flowField_zero, expUnit_zero_smul, one_mul] at hm
  exact ⟨_, hm, ((quatClose_unitQuaternion (kW c.1) (k' c.1)).mul hn).mul
    (quatClose_unitQuaternion (kW (c.1 + unitStep (j + 1) c.2)) (k' (c.1 + unitStep (j + 1) c.2))).star⟩
theorem hasDerivAt_norm_zero {f : ℝ → ℍ[ℝ]} {f' : ℍ[ℝ]} (h : HasDerivAt f f' 0) (h0 : f 0 ≠ 0) :
    HasDerivAt (fun τ => ‖f τ‖) ((f' * star (‖f 0‖⁻¹ • f 0)).re) 0 := by
  have hsq : ∀ q : ℍ[ℝ], (q * star q).re = ‖q‖ ^ 2 := by
    intro q
    rw [Quaternion.self_mul_star, Quaternion.re_coe, Quaternion.normSq_eq_norm_mul_self]
    ring
  have h1 := h.fun_mul (hasDerivAt_star_zero h)
  have h2 : HasDerivAt (fun τ => (f τ * star (f τ)).re) ((f' * star (f 0) + f 0 * star f').re) 0 :=
    reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have hn : ‖f 0‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hne : (f 0 * star (f 0)).re ≠ 0 := by
    rw [hsq]
    positivity
  have h3 := h2.sqrt hne
  have e : (fun τ => Real.sqrt ((f τ * star (f τ)).re)) = fun τ => ‖f τ‖ := by
    funext τ
    rw [hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [e] at h3
  convert h3 using 1
  have e2 : (f 0 * star f').re = (f' * star (f 0)).re := by
    rw [← quat_re_star, star_mul, star_star]
  rw [Quaternion.re_add, e2, hsq, Real.sqrt_sq (norm_nonneg _), quaternion_star_real_smul, mul_smul_comm,
    quat_re_smul]
  field_simp
  ring
theorem blockFit_change_lower_bound (hodd : Odd F.blockSide) {W X : F.GaugeField j} {Wu Xu : F.GaugeField (j + 1)}
    {kW k' : F.Site (j + 1) → UnitQuaternion}
    {c : F.Site (j + 1) × Fin 4} {ε G : ℝ} (Up : ℝ → F.GaugeField (j + 1))
    (hUp : HasDerivAt (fun τ : ℝ => ((Up τ c.1 c.2 : UnitQuaternion) : ℍ[ℝ]))
      (pureComponent ((Xu c.1 c.2 : ℍ[ℝ]) * star (Wu c.1 c.2 : ℍ[ℝ])) * (Wu c.1 c.2 : ℍ[ℝ])) 0)
    (hUp0 : Up 0 c.1 c.2 = Wu c.1 c.2) (hε : 0 ≤ ε)
    (hb : ∀ a i, a ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      a + basisVector i ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      bondGap X W (refineSite c.1 + siteOfCoords j a, i) ≤ ε)
    (hG : gaugeGap k' kW c.1 + 5 * F.blockSide * ε + gaugeGap k' kW (c.1 + unitStep (j + 1) c.2) ≤ G)
    (hG4 : G ≤ 1 / 4)
    (hr : 1 / 2 ≤ ‖gaugedContourAverage X k' c‖) (hm : normSubOne (bondMisfit W kW Wu c) ≤ 1 / 2) :
    ∃ l : ℝ, HasDerivAt (fun τ : ℝ =>
        gaugedBlockFit (flowField W (gapDirection X W) τ) (flowGauge kW (gaugeGapDirection k' kW) τ) (Up τ) c) l 0 ∧
      ‖((bondMisfit X k' Xu c * (bondMisfit W kW Wu c)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 / 8 -
          normSubOne (bondMisfit W kW Wu c) *
            (13 * G ^ 2 + 3 * ‖(Xu c.1 c.2 : ℍ[ℝ]) * star (Wu c.1 c.2 : ℍ[ℝ]) - 1‖ ^ 2) ≤
        gaugedBlockFit X k' Xu c - gaugedBlockFit W kW Wu c - l := by
  obtain ⟨d, hd, hn⟩ := gaugedContourAverage_close hodd W X kW k' c hε hb
  have hn' := hn.mono hG
  set A := gaugedContourAverage X k' c with hA
  set A₀ := gaugedContourAverage W kW c with hA₀
  have h0 : A₀ ≠ 0 := by
    intro h
    have h1 := hn'.sub_le
    rw [h, sub_zero] at h1
    linarith
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, norm_zero] at hr
    linarith
  have hf0 : gaugedContourAverage (flowField W (gapDirection X W) 0) (flowGauge kW (gaugeGapDirection k' kW) 0) c =
      A₀ := by
    rw [flowField_zero, flowGauge_zero]
  have hN := hasDerivAt_norm_zero hd (by rw [hf0]; exact h0)
  have hU := hasDerivAt_star_zero hUp
  have hm2 := hd.fun_mul hU
  rw [hUp0, hf0] at hm2
  have hRe : HasDerivAt (fun τ : ℝ => (gaugedContourAverage (flowField W (gapDirection X W) τ)
      (flowGauge kW (gaugeGapDirection k' kW) τ) c *
      star ((Up τ c.1 c.2 : UnitQuaternion) : ℍ[ℝ])).re) _ 0 := reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hm2
  rw [hf0] at hN
  have hfit := hN.sub hRe
  refine ⟨_, hfit, ?_⟩
  set W' : ℍ[ℝ] := (Wu c.1 c.2 : ℍ[ℝ]) with hW'
  set X' : ℍ[ℝ] := (Xu c.1 c.2 : ℍ[ℝ]) with hX'
  have hWn : ‖W'‖ = 1 := _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _
  have hXn : ‖X'‖ = 1 := _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _
  have hgW : X' * star W' * W' = X' := by rw [mul_assoc, star_mul_self_of_norm_eq_one hWn, mul_one]
  have hgn : ‖X' * star W'‖ = 1 := by rw [norm_mul, norm_star, hWn, hXn, one_mul]
  have hmis₀ : ((bondMisfit W kW Wu c : UnitQuaternion) : ℍ[ℝ]) = W' * star (‖A₀‖⁻¹ • A₀) := by
    show (Wu c.1 c.2 : ℍ[ℝ]) * star ((polarUnit (gaugedContourAverage W kW c) : UnitQuaternion) : ℍ[ℝ]) = _
    rw [coe_polarUnit h0]
  have hmis : ((bondMisfit X k' Xu c : UnitQuaternion) : ℍ[ℝ]) = X' * star (‖A‖⁻¹ • A) := by
    show (Xu c.1 c.2 : ℍ[ℝ]) * star ((polarUnit (gaugedContourAverage X k' c) : UnitQuaternion) : ℍ[ℝ]) = _
    rw [coe_polarUnit hA0]
  have hcore := fit_lower_bound (A := A) (A₀ := A₀) (Ad := d) (g := X' * star W') (W' := W') (G := G) hgn hWn hr
    hn'.right_le h0 hn'.sub_le hn'.second_le (by rw [← hmis₀]; exact hm)
  rw [hgW] at hcore
  have he : ((bondMisfit X k' Xu c * (bondMisfit W kW Wu c)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      X' * star (‖A‖⁻¹ • A) * star (W' * star (‖A₀‖⁻¹ • A₀)) := by
    rw [← hmis, ← hmis₀]
    rfl
  have hg : normSubOne (bondMisfit W kW Wu c) = ‖W' * star (‖A₀‖⁻¹ • A₀) - 1‖ := by
    unfold normSubOne
    rw [hmis₀]
  rw [he, hg]
  have hf1 : gaugedBlockFit X k' Xu c = ‖A‖ - (A * star X').re := rfl
  have hf2 : gaugedBlockFit W kW Wu c = ‖A₀‖ - (A₀ * star W').re := rfl
  rw [hf1, hf2]
  have hl : (d * star (‖A₀‖⁻¹ • A₀)).re - (d * star W' + A₀ * star (pureComponent (X' * star W') * W')).re =
      (d * star (‖A₀‖⁻¹ • A₀)).re - (d * star W').re + (A₀ * star W' * pureComponent (X' * star W')).re := by
    have e1 : A₀ * star (pureComponent (X' * star W') * W') = - (A₀ * star W' * pureComponent (X' * star W')) := by
      rw [star_mul, star_pureComponent, mul_neg, mul_neg, mul_assoc]
    rw [e1, Quaternion.re_add, Quaternion.re_neg]
    ring
  show _ ≤ _ - ((d * star (‖A₀‖⁻¹ • A₀)).re - (d * star W' + A₀ * star (pureComponent (X' * star W') * W')).re)
  rw [hl]
  linarith
end
section
variable {F : BlockFrame} {j : ℕ}
theorem conj_product_eq {A K g g' C A' K' : ℍ[ℝ]} (hg : ‖g‖ = 1) (hg' : ‖g'‖ = 1) :
    (A * K * star g) * (g * C * star g') * star (A' * K' * star g') = A * (K * C * star K') * star A' := by
  have h1 := star_mul_self_of_norm_eq_one hg
  have h2 := star_mul_self_of_norm_eq_one hg'
  calc (A * K * star g) * (g * C * star g') * star (A' * K' * star g')
      = A * K * (star g * g) * C * (star g' * g') * (star K' * star A') := by
        simp only [star_mul, star_star, mul_assoc]
    _ = _ := by
        rw [h1, h2]
        simp only [mul_one, mul_assoc]
theorem gaugedContourAverage_gaugedChain (hgc : gaugeCovarianceStatement) (hL : 0 < F.blockSide) (hj : j < F.top)
    (X : F.FieldChain) (k Γ : F.SiteGauge) (c : F.Site (j + 1) × Fin 4) :
    gaugedContourAverage (gaugedChainFields X Γ j) (gaugedLink k Γ j) c =
      (Γ (j + 1) c.1 : ℍ[ℝ]) * gaugedContourAverage (X j) (k (j + 1)) c *
        star (Γ (j + 1) (c.1 + unitStep (j + 1) c.2) : ℍ[ℝ]) := by
  obtain ⟨_, h2, _, _⟩ := hgc F j hj hL
  show (gaugedLink k Γ j c.1 : ℍ[ℝ]) * _root_.YangMills.Construction.BlockAverages.contourAverage (gaugeTransform (Γ j) (X j)) c *
    star (gaugedLink k Γ j (c.1 + unitStep (j + 1) c.2) : ℍ[ℝ]) = _
  rw [h2]
  have e1 : (gaugedLink k Γ j c.1 : ℍ[ℝ]) = (Γ (j + 1) c.1 : ℍ[ℝ]) * (k (j + 1) c.1 : ℍ[ℝ]) *
      star (Γ j (refineSite c.1) : ℍ[ℝ]) := rfl
  have e2 : (gaugedLink k Γ j (c.1 + unitStep (j + 1) c.2) : ℍ[ℝ]) =
      (Γ (j + 1) (c.1 + unitStep (j + 1) c.2) : ℍ[ℝ]) * (k (j + 1) (c.1 + unitStep (j + 1) c.2) : ℍ[ℝ]) *
      star (Γ j (refineSite (c.1 + unitStep (j + 1) c.2)) : ℍ[ℝ]) := rfl
  rw [e1, e2]
  exact conj_product_eq (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _) (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _)
theorem norm_gaugedContourAverage_gaugedChain (hgc : gaugeCovarianceStatement) (hL : 0 < F.blockSide)
    (hj : j < F.top) (X : F.FieldChain) (k Γ : F.SiteGauge) (c : F.Site (j + 1) × Fin 4) :
    ‖gaugedContourAverage (gaugedChainFields X Γ j) (gaugedLink k Γ j) c‖ =
      ‖gaugedContourAverage (X j) (k (j + 1)) c‖ := by
  rw [gaugedContourAverage_gaugedChain hgc hL hj, norm_mul, norm_mul, norm_star, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion,
    _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion]
  ring
theorem re_conj_mul_star_conj {A A' q x : ℍ[ℝ]} (hA : ‖A‖ = 1) (hA' : ‖A'‖ = 1) :
    (A * q * star A' * star (A * x * star A')).re = (q * star x).re := by
  have h1 := star_mul_self_of_norm_eq_one hA'
  have e : A * q * star A' * star (A * x * star A') = A * (q * star x) * star A := by
    calc A * q * star A' * star (A * x * star A') = A * q * (star A' * A') * star x * star A := by
          simp only [star_mul, star_star, mul_assoc]
      _ = _ := by
          rw [h1]
          simp only [mul_one, mul_assoc]
  rw [e, mul_assoc, quat_re_mul_comm, mul_assoc, star_mul_self_of_norm_eq_one hA, mul_one]
theorem gaugedBlockFit_gaugedChain (hgc : gaugeCovarianceStatement) (hL : 0 < F.blockSide) (hj : j < F.top)
    (X : F.FieldChain) (k Γ : F.SiteGauge) (c : F.Site (j + 1) × Fin 4) :
    gaugedBlockFit (gaugedChainFields X Γ j) (gaugedLink k Γ j) (gaugedChainFields X Γ (j + 1)) c =
      gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c := by
  show ‖gaugedContourAverage (gaugedChainFields X Γ j) (gaugedLink k Γ j) c‖ -
    (gaugedContourAverage (gaugedChainFields X Γ j) (gaugedLink k Γ j) c *
      star ((Γ (j + 1) c.1 : ℍ[ℝ]) * (X (j + 1) c.1 c.2 : ℍ[ℝ]) *
        star (Γ (j + 1) (c.1 + unitStep (j + 1) c.2) : ℍ[ℝ]))).re = _
  rw [norm_gaugedContourAverage_gaugedChain hgc hL hj, gaugedContourAverage_gaugedChain hgc hL hj,
    re_conj_mul_star_conj (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _) (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _)]
  rfl
theorem variedFieldChain_of_lt (W : F.FieldChain) (Y : GaugedVariation F) (τ : ℝ) (hj : j < F.top) :
    variedFieldChain W Y τ j = flowField (W j) (Y.bondVariation j) τ := by
  funext x i
  simp [variedFieldChain, flowField, hj]
theorem variedFieldChain_zero_apply (W : F.FieldChain) (Y : GaugedVariation F) (x : F.Site j) (i : Fin 4) :
    variedFieldChain W Y 0 j x i = W j x i := by
  by_cases hj : j < F.top
  · rw [variedFieldChain_of_lt W Y 0 hj, flowField_zero]
  · simp [variedFieldChain, hj]
theorem fitTerm_lower_bound (hgc : gaugeCovarianceStatement) (hodd : Odd F.blockSide) {a : ℝ} (ha : 0 < a)
    {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain} {k Γ : F.SiteGauge} (hj : j < F.top)
    {c : F.Site (j + 1) × Fin 4} {ε G : ℝ}
    (hΓ : ∀ y, Γ F.top y = 1) (htop : X F.top = W F.top) (hε : 0 ≤ ε)
    (hb : ∀ a i, a ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      a + basisVector i ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      bondGap (gaugedChainFields X Γ j) (W j) (refineSite c.1 + siteOfCoords j a, i) ≤ ε)
    (hG : gaugeGap (gaugedLink k Γ j) (kW (j + 1)) c.1 + 5 * F.blockSide * ε +
      gaugeGap (gaugedLink k Γ j) (kW (j + 1)) (c.1 + unitStep (j + 1) c.2) ≤ G) (hG4 : G ≤ 1 / 4)
    (hr : 1 / 2 ≤ ‖gaugedContourAverage (X j) (k (j + 1)) c‖)
    (hm : normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ≤ 1 / 2) :
    firstVariation a W kW (gaugeVariation W kW X k Γ) (Sum.inr ⟨j, c⟩) +
        a * (‖((bondMisfit (gaugedChainFields X Γ j) (gaugedLink k Γ j) (gaugedChainFields X Γ (j + 1)) c *
          (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 / 8) -
        a * (normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) *
          (13 * G ^ 2 + 3 * bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 2)) ≤
      actionTermValue a X k (Sum.inr ⟨j, c⟩) - actionTermValue a W kW (Sum.inr ⟨j, c⟩) := by
  set Y := gaugeVariation W kW X k Γ with hY
  have hUp : HasDerivAt (fun τ : ℝ => ((variedFieldChain W Y τ (j + 1) c.1 c.2 : UnitQuaternion) : ℍ[ℝ]))
      (pureComponent ((gaugedChainFields X Γ (j + 1) c.1 c.2 : ℍ[ℝ]) * star (W (j + 1) c.1 c.2 : ℍ[ℝ])) *
        (W (j + 1) c.1 c.2 : ℍ[ℝ])) 0 := by
    by_cases hju : j + 1 < F.top
    · have h1 := hasDerivAt_expUnit_mul (Y.bondVariation (j + 1) c.1 c.2) (W (j + 1) c.1 c.2)
      have e : (fun τ : ℝ => ((variedFieldChain W Y τ (j + 1) c.1 c.2 : UnitQuaternion) : ℍ[ℝ])) =
          fun τ : ℝ => ((expUnit (τ • Y.bondVariation (j + 1) c.1 c.2) * W (j + 1) c.1 c.2 : UnitQuaternion) :
            ℍ[ℝ]) := by
        funext τ
        rw [variedFieldChain_of_lt W Y τ hju]
        rfl
      rw [e]
      exact h1
    · have hjt : j = F.depth := by
        have hn : F.top = F.depth + 1 := rfl
        omega
      subst hjt
      have e : (fun τ : ℝ => ((variedFieldChain W Y τ (F.depth + 1) c.1 c.2 : UnitQuaternion) : ℍ[ℝ])) =
          fun _ : ℝ => ((W (F.depth + 1) c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) := by
        funext τ
        simp [variedFieldChain]
      rw [e]
      have e2 : gaugedChainFields X Γ (F.depth + 1) c.1 c.2 = W (F.depth + 1) c.1 c.2 := by
        show Γ F.top c.1 * X F.top c.1 c.2 * (Γ F.top (c.1 + unitStep F.top c.2))⁻¹ = W F.top c.1 c.2
        rw [hΓ, hΓ, htop]
        simp
      rw [e2, mul_star_self_of_norm_eq_one (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _), pureComponent_one, zero_mul]
      exact hasDerivAt_const _ _
  have hr' : 1 / 2 ≤ ‖gaugedContourAverage (gaugedChainFields X Γ j) (gaugedLink k Γ j) c‖ := by
    rw [norm_gaugedContourAverage_gaugedChain hgc hodd.pos hj]
    exact hr
  obtain ⟨l, hl, hineq⟩ := blockFit_change_lower_bound hodd (W := W j) (X := gaugedChainFields X Γ j)
    (Wu := W (j + 1)) (Xu := gaugedChainFields X Γ (j + 1)) (kW := kW (j + 1)) (k' := gaugedLink k Γ j) (c := c)
    (ε := ε) (G := G) (fun τ => variedFieldChain W Y τ (j + 1)) hUp (variedFieldChain_zero_apply W Y _ _) hε hb hG
    hG4 hr' hm
  have hfo : firstVariation a W kW Y (Sum.inr ⟨j, c⟩) = a * l := by
    unfold firstVariation
    have e : (fun τ : ℝ => actionTermValue a (variedFieldChain W Y τ) (variedGauge kW Y τ) (Sum.inr ⟨j, c⟩)) =
        fun τ : ℝ => a * gaugedBlockFit (flowField (W j) (gapDirection (gaugedChainFields X Γ j) (W j)) τ)
          (flowGauge (kW (j + 1)) (gaugeGapDirection (gaugedLink k Γ j) (kW (j + 1))) τ)
          (variedFieldChain W Y τ (j + 1)) c := by
      funext τ
      show a * gaugedBlockFit (variedFieldChain W Y τ j) (variedGauge kW Y τ (j + 1))
        (variedFieldChain W Y τ (j + 1)) c = _
      rw [variedFieldChain_of_lt W Y τ hj]
      rfl
    rw [e]
    exact (hl.const_mul a).deriv
  have hv : actionTermValue a X k (Sum.inr ⟨j, c⟩) = a * gaugedBlockFit (gaugedChainFields X Γ j) (gaugedLink k Γ j)
      (gaugedChainFields X Γ (j + 1)) c := by
    rw [gaugedBlockFit_gaugedChain hgc hodd.pos hj]
    rfl
  have hw : actionTermValue a W kW (Sum.inr ⟨j, c⟩) = a * gaugedBlockFit (W j) (kW (j + 1)) (W (j + 1)) c := rfl
  have hgs : bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c =
      ‖(gaugedChainFields X Γ (j + 1) c.1 c.2 : ℍ[ℝ]) * star (W (j + 1) c.1 c.2 : ℍ[ℝ]) - 1‖ := rfl
  rw [hfo, hv, hw, hgs]
  have := mul_le_mul_of_nonneg_left hineq ha.le
  linarith
def plaquetteGap (X W : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) : ℝ :=
  bondGap X W (p.1, p.2.1) + bondGap X W (p.1 + unitStep 0 p.2.1, p.2.2) +
    bondGap X W (p.1 + unitStep 0 p.2.2, p.2.1) + bondGap X W (p.1, p.2.2)
theorem plaquette_holonomyClose (W X : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    HolonomyClose W X p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] (plaquetteGap X W p) := by
  have h0 := holonomyClose_nil W X (p.1 + stepDisplacement 0 (p.2.1, true) + stepDisplacement 0 (p.2.2, true) +
    stepDisplacement 0 (p.2.1, false) + stepDisplacement 0 (p.2.2, false))
  have h4 := holonomyClose_cons (holonomyClose_cons (holonomyClose_cons (holonomyClose_cons h0)))
  refine h4.mono (le_of_eq ?_)
  have e3 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 + -unitStep 0 p.2.1 = p.1 + unitStep 0 p.2.2 := by abel
  have e3' : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 - unitStep 0 p.2.1 = p.1 + unitStep 0 p.2.2 := by abel
  have e4 : p.1 + unitStep 0 p.2.2 - unitStep 0 p.2.2 = p.1 := by abel
  simp only [bondOfStep, stepDisplacement, if_true, Bool.false_eq_true, if_false, e3, e3', e4, plaquetteGap]
  ring
theorem plaquetteTerm_lower_bound (hgc : gaugeCovarianceStatement) (hodd : Odd F.blockSide) {a : ℝ}
    {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain} {k Γ : F.SiteGauge} (p : F.Site 0 × Fin 4 × Fin 4)
    (hP : 1 / 2 ≤ ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).re) :
    firstVariation a W kW (gaugeVariation W kW X k Γ) (Sum.inl p) +
        (1 / 32) * ‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
          ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])‖ ^ 2 -
        plaquetteGap (gaugedChainFields X Γ 0) (W 0) p ^ 2 *
          ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).im‖ ≤
      actionTermValue a X k (Sum.inl p) - actionTermValue a W kW (Sum.inl p) := by
  obtain ⟨_, _, h3, _⟩ := hgc F 0 (Nat.succ_pos _) hodd.pos
  obtain ⟨d, hd, hn, ht⟩ := plaquette_holonomyClose (W 0) (gaugedChainFields X Γ 0) p
  have hre : ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re =
      ((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]).re := by
    have e : plaquetteHolonomy (gaugedChainFields X Γ 0) p =
        Γ 0 p.1 * plaquetteHolonomy (X 0) p * (Γ 0 p.1)⁻¹ := h3 _ _ _
    rw [e]
    show _ = ((Γ 0 p.1 : ℍ[ℝ]) * (plaquetteHolonomy (X 0) p : ℍ[ℝ]) * star (Γ 0 p.1 : ℍ[ℝ])).re
    rw [mul_assoc, quat_re_mul_comm, mul_assoc, star_mul_self_of_norm_eq_one (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _), mul_one]
  have hfo : firstVariation a W kW (gaugeVariation W kW X k Γ) (Sum.inl p) = - d.re := by
    unfold firstVariation
    have e : (fun τ : ℝ => actionTermValue a (variedFieldChain W (gaugeVariation W kW X k Γ) τ)
        (variedGauge kW (gaugeVariation W kW X k Γ) τ) (Sum.inl p)) =
        fun τ : ℝ => 1 - ((pathHolonomy (flowField (W 0) (gapDirection (gaugedChainFields X Γ 0) (W 0)) τ) p.1
          [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ]).re := by
      funext τ
      show 1 - ((plaquetteHolonomy (variedFieldChain W (gaugeVariation W kW X k Γ) τ 0) p : UnitQuaternion) :
        ℍ[ℝ]).re = _
      rw [variedFieldChain_of_lt W _ τ (Nat.succ_pos _)]
      rfl
    rw [e]
    have hRe : HasDerivAt (fun τ : ℝ =>
        ((pathHolonomy (flowField (W 0) (gapDirection (gaugedChainFields X Γ 0) (W 0)) τ) p.1
          [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ]).re) d.re 0 :=
      reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    exact (hRe.const_sub 1).deriv
  have hc := plaquette_change_lower_bound (P := ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]))
    (Q := ((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ])) (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _)
    hn.second_le (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _) ht
  rw [pureComponent_eq_im] at hc
  have hv : actionTermValue a X k (Sum.inl p) = 1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re := rfl
  have hw : actionTermValue a W kW (Sum.inl p) = 1 - ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).re :=
    rfl
  rw [hfo, hv, hw, hre]
  have h5 : (1 / 32) * ‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
      ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])‖ ^ 2 ≤
      ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).re *
        (‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
          ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])‖ ^ 2 / 2) := by
    have h6 := sq_nonneg ‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
      ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])‖
    nlinarith
  linarith
theorem bondMisfit_congr {X : F.GaugeField j} {k k₂ : F.Site (j + 1) → UnitQuaternion}
    {Xu : F.GaugeField (j + 1)}
    {c : F.Site (j + 1) × Fin 4} (h1 : k c.1 = k₂ c.1)
    (h2 : k (c.1 + unitStep (j + 1) c.2) = k₂ (c.1 + unitStep (j + 1) c.2)) :
    bondMisfit X k Xu c = bondMisfit X k₂ Xu c := by
  unfold bondMisfit gaugedContourAverage
  rw [h1, h2]
theorem polarUnit_coe_unitQuaternion (g : UnitQuaternion) : polarUnit (g : ℍ[ℝ]) = g := by apply _root_.YangMills.Construction.BlockLines.polarUnit_coe <;> assumption
theorem bondMisfit_gaugeTransform {X : F.GaugeField j} {k k₂ K : F.Site (j + 1) → UnitQuaternion}
    {Xu : F.GaugeField (j + 1)}
    {c : F.Site (j + 1) × Fin 4} (hA : gaugedContourAverage X k c ≠ 0) (h1 : k₂ c.1 = K c.1 * k c.1)
    (h2 : k₂ (c.1 + unitStep (j + 1) c.2) = K (c.1 + unitStep (j + 1) c.2) * k (c.1 + unitStep (j + 1) c.2)) :
    bondMisfit X k₂ (gaugeTransform K Xu) c = K c.1 * bondMisfit X k Xu c * (K c.1)⁻¹ := by
  have hm : gaugedContourAverage X k₂ c = (K c.1 : ℍ[ℝ]) * gaugedContourAverage X k c *
      (((K (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    unfold gaugedContourAverage
    rw [h1, h2, mul_inv_rev]
    simp only [Submonoid.coe_mul, mul_assoc]
  have hu : polarUnit (gaugedContourAverage X k₂ c) = K c.1 * polarUnit (gaugedContourAverage X k c) *
      (K (c.1 + unitStep (j + 1) c.2))⁻¹ := by
    rw [hm, polarUnit_mul (mul_ne_zero (coe_unitQuaternion_ne_zero _) hA) (coe_unitQuaternion_ne_zero _),
      polarUnit_mul (coe_unitQuaternion_ne_zero _) hA, polarUnit_coe_unitQuaternion, polarUnit_coe_unitQuaternion]
  unfold bondMisfit
  rw [hu]
  show K c.1 * Xu c.1 c.2 * (K (c.1 + unitStep (j + 1) c.2))⁻¹ * _ = _
  group
theorem norm_im_le_norm_sub_one (q : ℍ[ℝ]) : ‖q.im‖ ≤ ‖q - 1‖ := by
  rw [← pureComponent_eq_im]
  exact norm_pureComponent_le_norm_sub_one q
theorem density_le_of_ne_depth {a : ℝ} (ha : 0 < a) {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain}
    {k Γ : F.SiteGauge} {c : F.Site (j + 1) × Fin 4} (hjt : j ≠ F.depth)
    (h1 : gaugedLink k Γ j c.1 = balancedLinkAgainst W kW (gaugedChainFields X Γ) j c.1)
    (h2 : gaugedLink k Γ j (c.1 + unitStep (j + 1) c.2) =
      balancedLinkAgainst W kW (gaugedChainFields X Γ) j (c.1 + unitStep (j + 1) c.2)) :
    (1 / 32) * relativeEnergyDensity a W kW X k Γ (Sum.inr ⟨j, c⟩) ≤
      a * (‖((bondMisfit (gaugedChainFields X Γ j) (gaugedLink k Γ j) (gaugedChainFields X Γ (j + 1)) c *
        (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 / 8) := by
  have hup : framedUpperField W kW X k Γ j = gaugedChainFields X Γ (j + 1) := by
    unfold framedUpperField
    rw [dif_neg hjt]
  show (1 / 32) * (a * ‖((bondMisfit (gaugedChainFields X Γ j) (balancedLinkAgainst W kW (gaugedChainFields X Γ) j)
      (framedUpperField W kW X k Γ j) c * (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]).im‖ ^ 2) ≤ _
  rw [hup, ← bondMisfit_congr h1 h2]
  have h3 := norm_im_le_norm_sub_one ((bondMisfit (gaugedChainFields X Γ j) (gaugedLink k Γ j)
    (gaugedChainFields X Γ (j + 1)) c * (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)⁻¹ : UnitQuaternion) : ℍ[ℝ])
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  nlinarith
theorem density_le_at_depth {a : ℝ} (ha : 0 < a) {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain}
    {k Γ : F.SiteGauge}
    {c : F.Site (F.depth + 1) × Fin 4} (hΓ : ∀ y, Γ F.top y = 1)
    (hA : gaugedContourAverage (gaugedChainFields X Γ F.depth) (gaugedLink k Γ F.depth) c ≠ 0)
    (hK : ‖((topCorrection W kW X k Γ c.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 1 / 8) :
    (1 / 32) * relativeEnergyDensity a W kW X k Γ (Sum.inr ⟨F.depth, c⟩) ≤
      a * (‖((bondMisfit (gaugedChainFields X Γ F.depth) (gaugedLink k Γ F.depth)
        (gaugedChainFields X Γ (F.depth + 1)) c *
        (bondMisfit (W F.depth) (kW (F.depth + 1)) (W (F.depth + 1)) c)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 / 8) +
      a * (‖((topCorrection W kW X k Γ c.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 *
        normSubOne (bondMisfit (W F.depth) (kW (F.depth + 1)) (W (F.depth + 1)) c) ^ 2) := by
  have hup : framedUpperField W kW X k Γ F.depth = gaugeTransform (topCorrection W kW X k Γ) (X F.top) := by
    unfold framedUpperField
    rw [dif_pos rfl]
  have hlink : ∀ y, balancedLinkAgainst W kW (gaugedChainFields X Γ) F.depth y =
      topCorrection W kW X k Γ y * gaugedLink k Γ F.depth y := by
    intro y
    show _ = balancedLinkAgainst W kW (gaugedChainFields X Γ) F.depth y * (gaugedLink k Γ F.depth y)⁻¹ *
      gaugedLink k Γ F.depth y
    group
  have hm := bondMisfit_gaugeTransform (Xu := X F.top) (K := topCorrection W kW X k Γ) (c := c) hA (hlink _)
    (hlink _)
  have hx : bondMisfit (gaugedChainFields X Γ F.depth) (gaugedLink k Γ F.depth) (X F.top) c =
      bondMisfit (gaugedChainFields X Γ F.depth) (gaugedLink k Γ F.depth) (gaugedChainFields X Γ (F.depth + 1)) c := by
    unfold bondMisfit
    congr 1
    show X F.top c.1 c.2 = Γ F.top c.1 * X F.top c.1 c.2 * (Γ F.top (c.1 + unitStep F.top c.2))⁻¹
    rw [hΓ, hΓ]
    simp
  rw [hx] at hm
  show (1 / 32) * (a * ‖((bondMisfit (gaugedChainFields X Γ F.depth)
      (balancedLinkAgainst W kW (gaugedChainFields X Γ) F.depth)
      (framedUpperField W kW X k Γ F.depth) c *
        (bondMisfit (W F.depth) (kW (F.depth + 1)) (W (F.depth + 1)) c)⁻¹ : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2) ≤ _
  rw [hup, hm]
  set m' := bondMisfit (gaugedChainFields X Γ F.depth) (gaugedLink k Γ F.depth)
    (gaugedChainFields X Γ (F.depth + 1)) c with hm'
  set m₀ := bondMisfit (W F.depth) (kW (F.depth + 1)) (W (F.depth + 1)) c with hm₀
  set K := topCorrection W kW X k Γ c.1 with hKdef
  have hcore := top_density_bound (e := ((m' * m₀⁻¹ : UnitQuaternion) : ℍ[ℝ])) (m₀ := (m₀ : ℍ[ℝ]))
    (K := (K : ℍ[ℝ])) (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _) (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _) (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _) hK
  have e1 : ((m' * m₀⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (m₀ : ℍ[ℝ]) = (m' : ℍ[ℝ]) := by
    show (m' : ℍ[ℝ]) * star (m₀ : ℍ[ℝ]) * (m₀ : ℍ[ℝ]) = _
    rw [mul_assoc, star_mul_self_of_norm_eq_one (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _), mul_one]
  rw [e1] at hcore
  have e2 : ((K * m' * K⁻¹ * m₀⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (K : ℍ[ℝ]) * (m' : ℍ[ℝ]) * star (K : ℍ[ℝ]) * star (m₀ : ℍ[ℝ]) := rfl
  rw [e2]
  unfold normSubOne
  have := mul_le_mul_of_nonneg_left hcore ha.le
  linarith
end
section
variable {F : BlockFrame} {j : ℕ} {S : Finset F.Cell} {z : F.Cell}
def patchQuarticGap (S : Finset F.Cell) (z : F.Cell) (X W : F.GaugeField j) (b : F.Site j × Fin 4) : ℝ :=
  if baseSite b.1 ∈ patchBaseSites S z ∧ baseSite (b.1 + unitStep j b.2) ∈ patchBaseSites S z then
    ‖((X b.1 b.2 * (W b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 else 0
theorem patchQuarticGap_nonneg (X W : F.GaugeField j) (b : F.Site j × Fin 4) :
    0 ≤ patchQuarticGap S z X W b := by
  unfold patchQuarticGap
  split_ifs
  · positivity
  · exact le_rfl
theorem patchQuarticGap_eq {X W : F.GaugeField j} {b : F.Site j × Fin 4} (h1 : baseSite b.1 ∈ patchBaseSites S z)
    (h2 : baseSite (b.1 + unitStep j b.2) ∈ patchBaseSites S z) : patchQuarticGap S z X W b = bondGap X W b ^ 4 := by
  unfold patchQuarticGap bondGap
  rw [if_pos ⟨h1, h2⟩]
def hullGapBound (S : Finset F.Cell) (z : F.Cell) (X W : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  Real.sqrt (Real.sqrt (BlockLines.hullSum (patchQuarticGap S z X W) c))
theorem sqrt_sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt (x ^ 4)) = x := by
  have : x ^ 4 = (x ^ 2) ^ 2 := by ring
  rw [this, Real.sqrt_sq (by positivity), Real.sqrt_sq hx]
theorem le_sqrt_sqrt_of_pow_four_le {x y : ℝ} (hx : 0 ≤ x) (h : x ^ 4 ≤ y) : x ≤ Real.sqrt (Real.sqrt y) := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.le_sqrt_sqrt_of_pow_four_le <;> assumption
theorem sqrt_sqrt_le_of_le_pow_four {x y : ℝ} (hx : 0 ≤ x) (h : y ≤ x ^ 4) : Real.sqrt (Real.sqrt y) ≤ x := by
  calc Real.sqrt (Real.sqrt y) ≤ Real.sqrt (Real.sqrt (x ^ 4)) := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)
    _ = x := sqrt_sqrt_pow_four hx
theorem pow_mul_mem_centredCube (hodd : Odd F.blockSide) {m : ℕ} {a : Lattice4}
    (ha : a ∈ centredCube (F.blockSide ^ m)) (k : ℕ) :
    (fun i => (F.blockSide : ℤ) ^ k * a i) ∈ centredCube (F.blockSide ^ (m + k)) := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    have h0 : (0 : Lattice4) ∈ centredCube F.blockSide := (LatticePaths.mem_centredCube_iff _ _).2 fun l => by
      have := hodd.pos
      simp only [Pi.zero_apply]
      omega
    have h := ChartCoordinates.scale_add_mem_centredCube hodd ih h0
    have e : (fun i => (F.blockSide : ℤ) * ((F.blockSide : ℤ) ^ k * a i) + (0 : Lattice4) i) =
        fun i => (F.blockSide : ℤ) ^ (k + 1) * a i := by
      funext i
      simp only [Pi.zero_apply, add_zero]
      ring
    rw [e] at h
    exact h
theorem baseSite_mem_patch_of_mem_twoBlockHull (hodd : Odd F.blockSide) (hj : j < F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ patchFitBonds S z j)
    {a : Lattice4} (ha : a ∈ FlatPairing.twoBlockHull F.blockSide c.2) :
    baseSite (refineSite c.1 + siteOfCoords j a) ∈ patchBaseSites S z := by
  classical
  have hcf := (Finset.mem_filter.1 hc).2
  have hj1 : j + 1 ≤ F.top := hj
  have hle : j ≤ F.top := by omega
  by_cases hcase : a c.2 ≤ ((F.blockSide : ℤ) - 1) / 2
  · have hcube : a ∈ centredCube (F.blockSide ^ 1) := by
      rw [pow_one]
      refine (LatticePaths.mem_centredCube_iff _ _).2 fun μ => ?_
      have := ha μ
      by_cases hμ : μ = c.2
      · subst hμ
        simp only [if_true] at this
        exact ⟨this.1, hcase⟩
      · simpa [hμ] using this
    have hs := pow_mul_mem_centredCube hodd hcube j
    rw [show 1 + j = j + 1 by omega] at hs
    rw [baseSite_add j hle, baseSite_refineSite j hj1]
    exact (hcf _ hs).1
  · have e : refineSite c.1 + siteOfCoords j a =
        refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j (a - (F.blockSide : ℤ) • basisVector c.2) := by
      rw [unitStep_eq, refineSite_add j hj1, add_assoc, ← siteOfCoords_add]
      congr 2
      funext μ
      simp [basisVector]
    have hcube : a - (F.blockSide : ℤ) • basisVector c.2 ∈ centredCube (F.blockSide ^ 1) := by
      rw [pow_one]
      refine (LatticePaths.mem_centredCube_iff _ _).2 fun μ => ?_
      have := ha μ
      obtain ⟨m, hm⟩ := hodd
      have hL : ((F.blockSide : ℤ) - 1) / 2 = m := by rw [hm]; push_cast; omega
      have hL2 : (F.blockSide : ℤ) = 2 * m + 1 := by rw [hm]; push_cast; ring
      rw [hL] at this hcase ⊢
      by_cases hμ : μ = c.2
      · subst hμ
        simp only [if_true] at this
        simp [basisVector]
        constructor <;> omega
      · simp only [hμ, if_false] at this
        simp [basisVector, hμ]
        simpa using this
    have hs := pow_mul_mem_centredCube hodd hcube j
    rw [show 1 + j = j + 1 by omega] at hs
    rw [e, baseSite_add j hle, baseSite_refineSite j hj1]
    exact (hcf _ hs).2
theorem bondGap_le_hullGapBound (hodd : Odd F.blockSide) (hj : j < F.top) (X W : F.GaugeField j)
    {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ patchFitBonds S z j) {a : Lattice4} {i : Fin 4} (ha : a ∈ FlatPairing.twoBlockHull F.blockSide c.2)
    (ha' : a + basisVector i ∈ FlatPairing.twoBlockHull F.blockSide c.2) :
    bondGap X W (refineSite c.1 + siteOfCoords j a, i) ≤ hullGapBound S z X W c := by
  have h1 := baseSite_mem_patch_of_mem_twoBlockHull hodd hj hc ha
  have h2 := baseSite_mem_patch_of_mem_twoBlockHull hodd hj hc ha'
  have e : refineSite c.1 + siteOfCoords j (a + basisVector i) = refineSite c.1 + siteOfCoords j a + unitStep j i := by
    rw [siteOfCoords_add, unitStep_eq, add_assoc]
  rw [e] at h2
  have h3 := BlockLines.le_hullSum hodd.pos (patchQuarticGap S z X W) (patchQuarticGap_nonneg X W) c i ha ha'
  rw [patchQuarticGap_eq (b := (refineSite c.1 + siteOfCoords j a, i)) h1 h2] at h3
  exact le_sqrt_sqrt_of_pow_four_le (bondGap_nonneg _ _ _) h3
theorem hullGapBound_nonneg (X W : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) : 0 ≤ hullGapBound S z X W c :=
  Real.sqrt_nonneg _
theorem norm_conj_product_sub_one_le (T k B : UnitQuaternion) :
    ‖((T * (k * B) * k⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(T : ℍ[ℝ]) - 1‖ + ‖(B : ℍ[ℝ]) - 1‖ := by
  have e : T * (k * B) * k⁻¹ = T * (k * B * k⁻¹) := by group
  rw [e]
  refine (norm_coe_mul_sub_one_le _ _).trans ?_
  rw [norm_coe_conj_sub_one]
theorem balancingGauge_ends_le (hodd : Odd F.blockSide) (hj : j < F.top) (X W : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ a i, a ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      a + basisVector i ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      bondGap X W (refineSite c.1 + siteOfCoords j a, i) ≤ ε) :
    ‖((balancingGauge X W c.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * F.blockSide * ε ∧
      ‖((balancingGauge X W (c.1 + unitStep (j + 1) c.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        4 * F.blockSide * ε := by
  have hL : 1 ≤ F.blockSide := hodd.pos
  constructor
  · exact norm_balancingGauge_sub_one_le hodd X W c.1 (fun v => v ∈ FlatPairing.twoBlockHull F.blockSide c.2) hε
      (fun h hh π => LatticePaths.allAlong_mono (fun v hv => LatticePaths.mem_twoBlockHull_of_between hh hv hL)
        (LatticePaths.axisPath_spec h π).1) hb
  · refine norm_balancingGauge_sub_one_le hodd X W _
      (fun v => v + (F.blockSide : ℤ) • basisVector c.2 ∈ FlatPairing.twoBlockHull F.blockSide c.2) hε
      (fun h hh π => LatticePaths.allAlong_mono (fun v hv μ => ?_) (LatticePaths.axisPath_spec h π).1) ?_
    · have h1 := ((LatticePaths.mem_centredCube_iff _ _).1 hh) μ
      have h2 := hv μ
      have hk : (0 : ℤ) ≤ ((F.blockSide : ℤ) - 1) / 2 := by omega
      have a1 : min 0 (h μ) ≥ -(((F.blockSide : ℤ) - 1) / 2) := le_min (by omega) h1.1
      have a2 : max 0 (h μ) ≤ ((F.blockSide : ℤ) - 1) / 2 := max_le hk h1.2
      by_cases hμ : μ = c.2
      · subst hμ
        simp [basisVector]
        constructor <;> omega
      · simp [basisVector, hμ]
        constructor <;> omega
    · intro v i hv hv'
      have e : refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j v =
          refineSite c.1 + siteOfCoords j (v + (F.blockSide : ℤ) • basisVector c.2) := by
        rw [unitStep_eq, refineSite_add j hj, add_assoc, ← siteOfCoords_add]
        congr 2
        funext μ
        simp [add_comm]
      rw [e]
      refine hb _ i hv ?_
      have e2 : v + (F.blockSide : ℤ) • basisVector c.2 + basisVector i =
          v + basisVector i + (F.blockSide : ℤ) • basisVector c.2 := by abel
      rw [e2]
      exact hv'
def hullConstant (L : ℕ) : ℝ := 16 * ((BlockLines.hullBox L).card : ℝ)
def gapConstant (L : ℕ) : ℝ := 13 * L * hullConstant L + 2
def squareSumConstant (L : ℕ) : ℝ :=
  3 * ((4394 * (L : ℝ) ^ 2) ^ 2 * hullConstant L + 104 ^ 2 * (4 * 47 ^ 4) + 9)
def totalConstant (a : ℝ) (L : ℕ) : ℝ :=
  32 * 2209 + 2 * a * (2209 * Real.sqrt (squareSumConstant L)) + a * 47 ^ 4
theorem hullConstant_nonneg (L : ℕ) : 0 ≤ hullConstant L := by
  unfold hullConstant
  positivity
theorem two_le_gapConstant (L : ℕ) : 2 ≤ gapConstant L := by
  unfold gapConstant
  have := hullConstant_nonneg L
  have h2 : 0 ≤ 13 * (L : ℝ) * hullConstant L := by positivity
  linarith
theorem one_le_hullConstant (hL : 1 ≤ F.blockSide) : 1 ≤ hullConstant F.blockSide := by
  unfold hullConstant
  have h1 : (0 : Lattice4) ∈ BlockLines.hullBox F.blockSide := by
    refine Fintype.mem_piFinset.2 fun i => ?_
    simp only [Pi.zero_apply, Finset.mem_Icc]
    omega
  have h2 : 1 ≤ (BlockLines.hullBox F.blockSide).card := Finset.card_pos.2 ⟨_, h1⟩
  have h3 : (1 : ℝ) ≤ ((BlockLines.hullBox F.blockSide).card : ℝ) := by exact_mod_cast h2
  linarith
theorem hullGapBound_le (hodd : Odd F.blockSide) (hj : j < F.top) {X W : F.GaugeField j} {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hq : ∑ b ∈ innerBonds S j, patchQuarticGap S z X W b ≤ Q ^ 4) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds S (j + 1)) :
    hullGapBound S z X W c ≤ hullConstant F.blockSide * Q := by
  classical
  have h1 := BlockLines.sum_hullSum_le (B := S) hj hodd {c} (Finset.singleton_subset_iff.2 hc)
    (patchQuarticGap S z X W) (patchQuarticGap_nonneg X W)
  rw [Finset.sum_singleton] at h1
  have hk := one_le_hullConstant (F := F) hodd.pos
  refine sqrt_sqrt_le_of_le_pow_four (by positivity) ?_
  have h2 : hullConstant F.blockSide * Q ^ 4 ≤ (hullConstant F.blockSide * Q) ^ 4 := by
    rw [mul_pow]
    have h3 : hullConstant F.blockSide ≤ hullConstant F.blockSide ^ 4 := le_self_pow₀ hk (by norm_num)
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  have h4 : (16 * ((BlockLines.hullBox F.blockSide).card : ℝ)) *
      ∑ b ∈ innerBonds S j, patchQuarticGap S z X W b ≤ hullConstant F.blockSide * Q ^ 4 :=
    mul_le_mul_of_nonneg_left hq (hullConstant_nonneg _)
  linarith
theorem bondGap_le_of_quartic_sum_le {X W : F.GaugeField j} {b : F.Site j × Fin 4} {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hq : ∑ b ∈ innerBonds S j, patchQuarticGap S z X W b ≤ Q ^ 4) (hb : b ∈ innerBonds S j)
    (h1 : baseSite b.1 ∈ patchBaseSites S z)
    (h2 : baseSite (b.1 + unitStep j b.2) ∈ patchBaseSites S z) : bondGap X W b ≤ Q := by
  have h3 := Finset.single_le_sum (fun b _ => patchQuarticGap_nonneg (S := S) (z := z) X W b) hb
  rw [patchQuarticGap_eq h1 h2] at h3
  exact le_of_pow_le_pow_left₀ (by norm_num) hQ0 (h3.trans hq)
end
section
variable {F : BlockFrame} {j : ℕ} {S : Finset F.Cell} {z : F.Cell}
theorem baseSite_of_level_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem cellSupDist_enclosingCell_le_of_mem_patchFitBonds (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hj : j < F.top) {c : F.Site (j + 1) × Fin 4} (hc : c ∈ patchFitBonds S z j) :
    cellSupDist (enclosingCell c.1) z ≤ 23 := by
  classical
  have hcb : c ∈ innerBonds S (j + 1) := (Finset.mem_filter.1 hc).1
  obtain ⟨v, _, h, hh, e⟩ := mem_sitesOfCells.1 (ChartCoordinates.innerBonds_ends hcb).1
  have hcell : enclosingCell c.1 = v := by
    rw [e]
    exact PatchPoints.enclosingCell_cellCentre_add hodd v h hh
  have hpatch : baseSite c.1 ∈ patchBaseSites S z :=
    PatchLocality.actionTermSite_mem_patchBaseSites hodd (t := Sum.inr ⟨j, c⟩)
      (Finset.inr_mem_disjSum.2 (Finset.mem_sigma.2 ⟨Finset.mem_range.2 hj, hc⟩))
  have hj1 : j + 1 ≤ F.top := hj
  have etb : baseSite c.1 = cellCentre 0 v + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ (j + 1) * h i) := by
    rw [e, baseSite_add (j + 1) hj1, baseSite_cellCentre (j + 1) hj1]
  have hs := pow_mul_mem_centredCube hodd hh (j + 1)
  rw [Nat.sub_add_cancel hj1] at hs
  rw [hcell]
  exact PatchLocality.cellSupDist_le_of_mem_patchBaseSites hamb hodd he hpatch hs etb
theorem sum_patchFitBonds_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hj : j < F.top) (f : F.Site (j + 1) × Fin 4 → ℝ) (hf : ∀ c, 0 ≤ f c) {B : ℝ} (hB : 0 ≤ B)
    (hcell : ∀ v, ∑ c ∈ bondsOver S {v} (j + 1), f c ≤ B) :
    ∑ c ∈ patchFitBonds S z j, f c ≤ 47 ^ 4 * B := by
  classical
  set T := (patchFitBonds S z j).image (fun c => enclosingCell c.1) with hT
  have hcard : T.card ≤ (2 * 23 + 1) ^ 4 := by
    refine PatchLocality.card_le_of_cellSupDist_le z 23 T fun v hv => ?_
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hv
    exact cellSupDist_enclosingCell_le_of_mem_patchFitBonds hamb hodd he hj hc
  rw [← Finset.sum_fiberwise_of_maps_to (t := T) (g := fun c => enclosingCell c.1)
    (fun c hc => Finset.mem_image_of_mem _ hc) f]
  have h1 : ∀ v ∈ T, ∑ c ∈ (patchFitBonds S z j).filter (fun c => enclosingCell c.1 = v), f c ≤ B := by
    intro v _
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => hf c) (hcell v)
    intro c hc
    have h2 := Finset.mem_filter.1 hc
    unfold bondsOver
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h2.1).1, by simp [h2.2]⟩
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have h3 : (T.card : ℝ) ≤ 47 ^ 4 := by
    have : (T.card : ℝ) ≤ (((2 * 23 + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast hcard
    norm_num at this ⊢
    exact this
  exact mul_le_mul_of_nonneg_right h3 hB
theorem baseDistance_cellCentre_le (hodd : Odd F.blockSide) {x : F.Site 0} {v : F.Cell} {h : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ F.top))
    (e : x = cellCentre 0 v + siteOfCoords 0 h) :
    ((baseDistance x (cellCentre 0 v) : ℕ) : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := by
  have h1 : baseDistance x (cellCentre 0 v) ≤ F.blockSide ^ F.top := by
    refine Finset.sup_le fun i _ => ?_
    have e2 : (baseSite x - cellCentre 0 v) i = ((h i : ℤ) : ZMod (F.period 0 i)) := by
      rw [baseSite_of_level_zero, e]
      simp [siteOfCoords]
    rw [e2]
    refine (PatchPoints.natAbs_valMinAbs_intCast_le _ _).trans ?_
    have h2 := ((LatticePaths.mem_centredCube_iff _ _).1 hh) i
    have hp : 0 < F.blockSide ^ F.top := pow_pos hodd.pos _
    omega
  exact_mod_cast h1
theorem sum_patchPlaquettes_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (f : F.Site 0 × Fin 4 × Fin 4 → ℝ) (hf : ∀ c, 0 ≤ f c) {B : ℝ} (hB : 0 ≤ B)
    (hcell : ∀ v : F.Cell, ∑ q ∈ (innerPlaquettes S 0).filter
      (fun q => ((baseDistance q.1 (cellCentre 0 v) : ℕ) : ℝ) ≤ (F.blockSide : ℝ) ^ F.top), f q ≤ B) :
    ∑ p ∈ patchPlaquettes S z, f p ≤ 47 ^ 4 * B := by
  classical
  have hsite : ∀ p ∈ patchPlaquettes S z, ∃ v, ∃ h ∈ centredCube (F.blockSide ^ F.top),
      p.1 = cellCentre 0 v + siteOfCoords 0 h ∧ enclosingCell p.1 = v ∧ cellSupDist v z ≤ 23 := by
    intro p hp
    have hp1 : p ∈ innerPlaquettes S 0 := (Finset.mem_filter.1 hp).1
    have hs : p.1 ∈ sitesOfCells S 0 := (Finset.mem_product.1 (Finset.mem_filter.1 hp1).1).1
    obtain ⟨v, _, h, hh, e⟩ := mem_sitesOfCells.1 hs
    rw [Nat.sub_zero] at hh
    have hcell : enclosingCell p.1 = v := by
      rw [e]
      exact PatchPoints.enclosingCell_cellCentre_add hodd v h (by simpa using hh)
    have hpatch : p.1 ∈ patchBaseSites S z :=
      PatchLocality.actionTermSite_mem_patchBaseSites hodd (t := Sum.inl p) (Finset.inl_mem_disjSum.2 hp)
    exact ⟨v, h, hh, e, hcell, PatchLocality.cellSupDist_le_of_mem_patchBaseSites hamb hodd he hpatch hh e⟩
  set T := (patchPlaquettes S z).image (fun p => enclosingCell p.1) with hT
  have hcard : T.card ≤ (2 * 23 + 1) ^ 4 := by
    refine PatchLocality.card_le_of_cellSupDist_le z 23 T fun v hv => ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨v', _, _, _, e1, e2⟩ := hsite p hp
    rw [e1]
    exact e2
  rw [← Finset.sum_fiberwise_of_maps_to (t := T) (g := fun p => enclosingCell p.1)
    (fun p hp => Finset.mem_image_of_mem _ hp) f]
  have h1 : ∀ v ∈ T, ∑ p ∈ (patchPlaquettes S z).filter (fun p => enclosingCell p.1 = v), f p ≤ B := by
    intro v _
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => hf c) (hcell v)
    intro p hp
    have h2 := Finset.mem_filter.1 hp
    obtain ⟨v', h, hh, e, e1, _⟩ := hsite p h2.1
    have hv : v' = v := e1.symm.trans h2.2
    subst hv
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h2.1).1, baseDistance_cellCentre_le hodd hh e⟩
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have h3 : (T.card : ℝ) ≤ 47 ^ 4 := by
    have : (T.card : ℝ) ≤ (((2 * 23 + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast hcard
    norm_num at this ⊢
    exact this
  exact mul_le_mul_of_nonneg_right h3 hB
theorem sum_comp_le_four_mul {P B : Type} [DecidableEq B] (A : Finset P) (T : Finset B) (φ : P → B)
    (f : B → ℝ) (hf : ∀ b, 0 ≤ f b) (ψ : P → Fin 4) (hmap : ∀ p ∈ A, φ p ∈ T)
    (hinj : ∀ p ∈ A, ∀ p' ∈ A, φ p = φ p' → ψ p = ψ p' → p = p') :
    ∑ p ∈ A, f (φ p) ≤ 4 * ∑ b ∈ T, f b := by
  classical
  rw [← Finset.sum_fiberwise A ψ]
  have h1 : ∀ i : Fin 4, ∑ p ∈ A.filter (fun p => ψ p = i), f (φ p) ≤ ∑ b ∈ T, f b := by
    intro i
    have hin : Set.InjOn φ (A.filter (fun p => ψ p = i) : Finset P) := by
      intro p hp p' hp' e
      have a1 := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
      have a2 := Finset.mem_filter.1 (Finset.mem_coe.1 hp')
      exact hinj p a1.1 p' a2.1 e (a1.2.trans a2.2.symm)
    rw [← Finset.sum_image (f := f) hin]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => hf b
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb
    exact hmap p (Finset.mem_filter.1 hp).1
  refine (Finset.sum_le_sum fun i _ => h1 i).trans (le_of_eq ?_)
  simp
theorem plaquette_bond_mem {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ patchPlaquettes S z) {x : F.Site 0}
    {i : Fin 4} (hx : x ∈ plaquetteCorners p) (hy : x + unitStep 0 i ∈ plaquetteCorners p) :
    (x, i) ∈ innerBonds S 0 ∧ baseSite x ∈ patchBaseSites S z ∧ baseSite (x + unitStep 0 i) ∈ patchBaseSites S z := by
  classical
  have h1 := Finset.mem_filter.1 hp
  have h2 := (Finset.mem_filter.1 h1.1).2.2
  refine ⟨ChartCoordinates.mem_innerBonds (h2 hx) (h2 hy), ?_, ?_⟩
  · rw [baseSite_of_level_zero]
    exact h1.2 hx
  · rw [baseSite_of_level_zero]
    exact h1.2 hy
theorem plaquetteCorners_base (p : F.Site 0 × Fin 4 × Fin 4) : p.1 ∈ plaquetteCorners p := by
  simp [plaquetteCorners]
theorem plaquetteCorners_first (p : F.Site 0 × Fin 4 × Fin 4) : p.1 + unitStep 0 p.2.1 ∈ plaquetteCorners p := by
  simp [plaquetteCorners]
theorem plaquetteCorners_second (p : F.Site 0 × Fin 4 × Fin 4) : p.1 + unitStep 0 p.2.2 ∈ plaquetteCorners p := by
  simp [plaquetteCorners]
theorem plaquetteCorners_far (p : F.Site 0 × Fin 4 × Fin 4) :
    p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 ∈ plaquetteCorners p := by
  simp [plaquetteCorners]
theorem plaquetteCorners_far_comm (p : F.Site 0 × Fin 4 × Fin 4) :
    p.1 + unitStep 0 p.2.2 + unitStep 0 p.2.1 ∈ plaquetteCorners p := by
  rw [add_right_comm]
  exact plaquetteCorners_far p
theorem sum_range_pow_le_two_mul {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 2) (n : ℕ) :
    ∑ i ∈ Finset.range n, ρ ^ i ≤ 2 * (1 - ρ ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h2 : 0 ≤ ρ ^ n := pow_nonneg h0 n
    have h3 : ρ ^ (n + 1) = ρ ^ n * ρ := pow_succ _ _
    rw [h3]
    nlinarith
theorem sum_range_pow_reflect_le_two {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 2) (n : ℕ) :
    ∑ j ∈ Finset.range n, ρ ^ (n - 1 - j) ≤ 2 := by
  rw [Finset.sum_range_reflect (fun i => ρ ^ i) n]
  have h2 := sum_range_pow_le_two_mul h0 h1 n
  have h3 := pow_nonneg h0 n
  linarith
end
section
variable {F : BlockFrame} {j : ℕ} {S : Finset F.Cell} {z : F.Cell}
structure PatchComparison (a Q T : ℝ) (S : Finset F.Cell) (z : F.Cell) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (k Γ : F.SiteGauge) : Prop where
  gc : gaugeCovarianceStatement
  odd : Odd F.blockSide
  amb : IsAdmissibleAmbient F
  sign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1
  a_pos : 0 < a
  eight_le_side : 8 ≤ F.blockSide
  top_gauge : ∀ y, Γ F.top y = 1
  top_same : X F.top = W F.top
  link : ∀ j, j + 1 < F.top → ∀ y, baseSite y ∈ patchBaseSites S z →
    gaugedLink k Γ j y = balancedLinkAgainst W kW (gaugedChainFields X Γ) j y
  Q_nonneg : 0 ≤ Q
  quartic : ∀ j, j < F.top → ∑ b ∈ innerBonds S j, patchQuarticGap S z (gaugedChainFields X Γ j) (W j) b ≤ Q ^ 4
  rearrangedPathCorner : ∀ y : F.Site F.top, baseSite y ∈ patchBaseSites S z →
    ‖((topCorrection W kW X k Γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Q
  small : gapConstant F.blockSide * Q ≤ 1 / 8
  means : ∀ j, j < F.top → ∀ c ∈ patchFitBonds S z j, 1 / 2 ≤ ‖gaugedContourAverage (X j) (k (j + 1)) c‖
  plaq : ∀ p ∈ patchPlaquettes S z, normSubOne (plaquetteHolonomy (X 0) p) ≤ 1 / 4
  T_nonneg : 0 ≤ T
  T_small : T ≤ 1 / 2
  misfits : ∀ j, j < F.top → ∀ v, ∑ c ∈ bondsOver S {v} (j + 1),
    normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 2 ≤
      (T * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j)) ^ 2
  curvature : ∀ v : F.Cell, ∑ q ∈ (innerPlaquettes S 0).filter
      (fun q => ((baseDistance q.1 (cellCentre 0 v) : ℕ) : ℝ) ≤ (F.blockSide : ℝ) ^ F.top),
    ‖((plaquetteHolonomy (W 0) q : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 ≤ T ^ 2
def topVariationSize (F : BlockFrame) (Q : ℝ) (j : ℕ) : ℝ := if j = F.depth then Q else 0
def termRemainder (a Q : ℝ) (S : Finset F.Cell) (z : F.Cell) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (Γ : F.SiteGauge) : F.ActionTerm → ℝ
  | Sum.inl p => plaquetteGap (gaugedChainFields X Γ 0) (W 0) p ^ 2 *
      ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).im‖
  | Sum.inr ⟨j, c⟩ => a * (normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) *
      (13 * (13 * F.blockSide * hullGapBound S z (gaugedChainFields X Γ j) (W j) c + 2 * topVariationSize F Q j) ^ 2 +
        3 * bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 2)) +
      a * (topVariationSize F Q j ^ 2 * normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 2)
variable {a Q T : ℝ} {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain} {k Γ : F.SiteGauge}
theorem PatchComparison.topRotationSize_le (D : PatchComparison a Q T S z W kW X k Γ) (j : ℕ) :
    topVariationSize F Q j ≤ Q := by
  unfold topVariationSize
  split_ifs
  · exact le_rfl
  · exact D.Q_nonneg
theorem PatchComparison.size_le_one_sixteenth (D : PatchComparison a Q T S z W kW X k Γ) : Q ≤ 1 / 16 := by
  have h1 := two_le_gapConstant F.blockSide
  have h2 := D.small
  have h3 := D.Q_nonneg
  nlinarith
theorem PatchComparison.ratio_bounds (D : PatchComparison a Q T S z W kW X k Γ) :
    0 ≤ 4 / (F.blockSide : ℝ) ∧ 4 / (F.blockSide : ℝ) ≤ 1 / 2 := by
  have h1 : (8 : ℝ) ≤ F.blockSide := by exact_mod_cast D.eight_le_side
  constructor
  · positivity
  · rw [div_le_iff₀ (by linarith)]
    linarith
theorem PatchComparison.gaugeGap_le (D : PatchComparison a Q T S z W kW X k Γ) (hj : j < F.top)
    {y : F.Site (j + 1)}
    (hy : baseSite y ∈ patchBaseSites S z) {β : ℝ}
    (hB : ‖((balancingGauge (gaugedChainFields X Γ j) (W j) y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ β) :
    gaugeGap (gaugedLink k Γ j) (kW (j + 1)) y ≤ topVariationSize F Q j + β := by
  unfold gaugeGap
  by_cases hjt : j = F.depth
  · subst hjt
    have e : gaugedLink k Γ F.depth y = (topCorrection W kW X k Γ y)⁻¹ *
        (kW (F.depth + 1) y * balancingGauge (gaugedChainFields X Γ F.depth) (W F.depth) y) := by
      show _ = (balancedLinkAgainst W kW (gaugedChainFields X Γ) F.depth y * (gaugedLink k Γ F.depth y)⁻¹)⁻¹ *
        balancedLinkAgainst W kW (gaugedChainFields X Γ) F.depth y
      group
    rw [e]
    refine (norm_conj_product_sub_one_le _ _ _).trans ?_
    rw [norm_coe_inv_sub_one]
    have := D.rearrangedPathCorner y hy
    simp only [topVariationSize, if_true]
    linarith
  · have hj1 : j + 1 < F.top := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    have e : gaugedLink k Γ j y = 1 * (kW (j + 1) y * balancingGauge (gaugedChainFields X Γ j) (W j) y) := by
      rw [D.link j hj1 y hy, one_mul]
      rfl
    rw [e]
    refine (norm_conj_product_sub_one_le _ _ _).trans ?_
    simp only [topVariationSize, if_neg hjt]
    simpa using hB
theorem bond_ends_mem_patchBaseSites (hodd : Odd F.blockSide) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ patchFitBonds S z j) :
    baseSite c.1 ∈ patchBaseSites S z ∧ baseSite (c.1 + unitStep (j + 1) c.2) ∈ patchBaseSites S z := by
  classical
  have hcf := (Finset.mem_filter.1 hc).2
  have hz : (0 : Lattice4) ∈ centredCube (F.blockSide ^ (j + 1)) := by
    refine Fintype.mem_piFinset.2 fun i => ?_
    have : 0 < F.blockSide ^ (j + 1) := pow_pos hodd.pos _
    simp only [Pi.zero_apply, Finset.mem_Icc]
    omega
  have h := hcf 0 hz
  rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_zero, add_zero, add_zero] at h
  exact h
theorem PatchComparison.bondMisfit_le_half (D : PatchComparison a Q T S z W kW X k Γ) (hj : j < F.top)
    {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds S (j + 1)) : normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ≤ 1 / 2 := by
  classical
  have h1 := D.misfits j hj (enclosingCell c.1)
  have hmem : c ∈ bondsOver S {enclosingCell c.1} (j + 1) := by
    unfold bondsOver
    exact Finset.mem_filter.2 ⟨hc, by simp⟩
  have h2 := (Finset.single_le_sum (f := fun c => normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 2)
    (fun _ _ => sq_nonneg _) hmem).trans h1
  obtain ⟨r0, r1⟩ := D.ratio_bounds
  have h3 : (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) ≤ 1 := pow_le_one₀ r0 (by linarith)
  have hT := D.T_nonneg
  have h5 : T * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) ≤ 1 / 2 := by
    nlinarith [D.T_small]
  have h6 : normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ≤
      T * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h2
  exact h6.trans h5
theorem PatchComparison.fitTerm_ineq (D : PatchComparison a Q T S z W kW X k Γ) (hj : j < F.top)
    {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ patchFitBonds S z j) :
    firstVariation a W kW (gaugeVariation W kW X k Γ) (Sum.inr ⟨j, c⟩) +
        (1 / 32) * relativeEnergyDensity a W kW X k Γ (Sum.inr ⟨j, c⟩) -
          termRemainder a Q S z W kW X Γ (Sum.inr ⟨j, c⟩) ≤
      actionTermValue a X k (Sum.inr ⟨j, c⟩) - actionTermValue a W kW (Sum.inr ⟨j, c⟩) := by
  classical
  have hodd := D.odd
  have hcb : c ∈ innerBonds S (j + 1) := (Finset.mem_filter.1 hc).1
  have hb : ∀ a' i, a' ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      a' + basisVector i ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      bondGap (gaugedChainFields X Γ j) (W j) (refineSite c.1 + siteOfCoords j a', i) ≤
        hullGapBound S z (gaugedChainFields X Γ j) (W j) c :=
    fun a' i ha ha' => bondGap_le_hullGapBound hodd hj _ _ hc ha ha'
  have hε0 := hullGapBound_nonneg (S := S) (z := z) (gaugedChainFields X Γ j) (W j) c
  have hεQ := hullGapBound_le hodd hj D.Q_nonneg (D.quartic j hj) hcb
  obtain ⟨hB1, hB2⟩ := balancingGauge_ends_le hodd hj (gaugedChainFields X Γ j) (W j) c hε0 hb
  obtain ⟨he1, he2⟩ := bond_ends_mem_patchBaseSites hodd hc
  have hl1 := D.gaugeGap_le hj he1 hB1
  have hl2 := D.gaugeGap_le hj he2 hB2
  have hG4 : 13 * (F.blockSide : ℝ) * hullGapBound S z (gaugedChainFields X Γ j) (W j) c +
      2 * topVariationSize F Q j ≤ 1 / 8 := by
    have h1 := mul_le_mul_of_nonneg_left hεQ (by positivity : (0 : ℝ) ≤ 13 * (F.blockSide : ℝ))
    have h2 := D.small
    have h3 := D.topRotationSize_le j
    unfold gapConstant at h2
    nlinarith
  have hterm := fitTerm_lower_bound D.gc hodd D.a_pos hj D.top_gauge D.top_same hε0 hb
    (G := 13 * (F.blockSide : ℝ) * hullGapBound S z (gaugedChainFields X Γ j) (W j) c + 2 * topVariationSize F Q j)
    (by linarith) (by linarith)
    (D.means j hj c hc) (D.bondMisfit_le_half hj hcb)
  have herr : termRemainder a Q S z W kW X Γ (Sum.inr ⟨j, c⟩) =
      a * (normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) *
      (13 * (13 * F.blockSide * hullGapBound S z (gaugedChainFields X Γ j) (W j) c + 2 * topVariationSize F Q j) ^ 2 +
        3 * bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 2)) +
      a * (topVariationSize F Q j ^ 2 * normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 2) := rfl
  rw [herr]
  by_cases hjt : j = F.depth
  · subst hjt
    have hA : gaugedContourAverage (gaugedChainFields X Γ F.depth) (gaugedLink k Γ F.depth) c ≠ 0 := by
      intro h
      have h1 := D.means F.depth hj c hc
      rw [← norm_gaugedContourAverage_gaugedChain D.gc hodd.pos hj X k Γ c, h, norm_zero] at h1
      linarith
    have hK := D.rearrangedPathCorner c.1 he1
    have hQ := D.size_le_one_sixteenth
    have hden := density_le_at_depth (W := W) (kW := kW) (X := X) (k := k) (Γ := Γ) (c := c) D.a_pos
      D.top_gauge hA (by linarith)
    have hk : topVariationSize F Q F.depth = Q := by simp [topVariationSize]
    rw [hk] at hterm ⊢
    have h5 : ‖((topCorrection W kW X k Γ c.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 ≤ Q ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hK 2
    have h6 := mul_le_mul_of_nonneg_right h5
      (sq_nonneg (normSubOne (bondMisfit (W F.depth) (kW (F.depth + 1)) (W (F.depth + 1)) c)))
    have h7 := mul_le_mul_of_nonneg_left h6 D.a_pos.le
    linarith
  · have hj1 : j + 1 < F.top := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    have hden := density_le_of_ne_depth (W := W) (kW := kW) (X := X) (k := k) (Γ := Γ) (c := c) D.a_pos hjt
      (D.link j hj1 _ he1) (D.link j hj1 _ he2)
    have hk : 0 ≤ a * (topVariationSize F Q j ^ 2 * normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 2) :=
      mul_nonneg D.a_pos.le (by positivity)
    linarith
theorem PatchComparison.plaquetteGap_le (D : PatchComparison a Q T S z W kW X k Γ)
    {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ patchPlaquettes S z) : plaquetteGap (gaugedChainFields X Γ 0) (W 0) p ≤ 4 * Q := by
  have hq := D.quartic 0 (Nat.succ_pos _)
  have hb1 := plaquette_bond_mem hp (plaquetteCorners_base p) (plaquetteCorners_first p)
  have hb2 := plaquette_bond_mem hp (plaquetteCorners_first p) (plaquetteCorners_far p)
  have hb3 := plaquette_bond_mem hp (plaquetteCorners_second p) (plaquetteCorners_far_comm p)
  have hb4 := plaquette_bond_mem hp (plaquetteCorners_base p) (plaquetteCorners_second p)
  have g1 := bondGap_le_of_quartic_sum_le D.Q_nonneg hq hb1.1 hb1.2.1 hb1.2.2
  have g2 := bondGap_le_of_quartic_sum_le D.Q_nonneg hq hb2.1 hb2.2.1 hb2.2.2
  have g3 := bondGap_le_of_quartic_sum_le D.Q_nonneg hq hb3.1 hb3.2.1 hb3.2.2
  have g4 := bondGap_le_of_quartic_sum_le D.Q_nonneg hq hb4.1 hb4.2.1 hb4.2.2
  unfold plaquetteGap
  linarith
theorem PatchComparison.plaquetteTerm_ineq (D : PatchComparison a Q T S z W kW X k Γ)
    {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ patchPlaquettes S z) :
    firstVariation a W kW (gaugeVariation W kW X k Γ) (Sum.inl p) +
        (1 / 32) * relativeEnergyDensity a W kW X k Γ (Sum.inl p) - termRemainder a Q S z W kW X Γ (Sum.inl p) ≤
      actionTermValue a X k (Sum.inl p) - actionTermValue a W kW (Sum.inl p) := by
  have hodd := D.odd
  obtain ⟨_, _, h3, _⟩ := D.gc F 0 (Nat.succ_pos _) hodd.pos
  obtain ⟨d, _, hn, _⟩ := plaquette_holonomyClose (W 0) (gaugedChainFields X Γ 0) p
  have hdiff : ‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
      ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])‖ ≤
      plaquetteGap (gaugedChainFields X Γ 0) (W 0) p := hn.sub_le
  have hg := D.plaquetteGap_le hp
  have hQ := D.size_le_one_sixteenth
  have hs : ‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 1 / 4 := by
    have e : plaquetteHolonomy (gaugedChainFields X Γ 0) p =
        Γ 0 p.1 * plaquetteHolonomy (X 0) p * (Γ 0 p.1)⁻¹ := h3 _ _ _
    rw [e, norm_coe_conj_sub_one]
    exact D.plaq p hp
  have hP : 1 / 2 ≤ ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).re := by
    have e : ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]) - 1 =
        (((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) - 1) -
        (((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
          ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])) := by abel
    have h1 : ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 1 / 2 := by
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      linarith
    have h2 := (abs_le.1 ((quat_abs_re_le_norm _).trans h1)).1
    simp only [Quaternion.re_sub, Quaternion.re_one] at h2
    linarith
  exact plaquetteTerm_lower_bound D.gc hodd p hP
theorem PatchComparison.actionTerm_ineq (D : PatchComparison a Q T S z W kW X k Γ) {t : F.ActionTerm}
    (ht : t ∈ patchActionTerms S z) :
    firstVariation a W kW (gaugeVariation W kW X k Γ) t +
        (1 / 32) * relativeEnergyDensity a W kW X k Γ t - termRemainder a Q S z W kW X Γ t ≤
      actionTermValue a X k t - actionTermValue a W kW t := by
  rcases t with p | ⟨j, c⟩
  · exact D.plaquetteTerm_ineq (Finset.inl_mem_disjSum.1 ht)
  · have hc := Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 ht)
    exact D.fitTerm_ineq (Finset.mem_range.1 hc.1) hc.2
theorem PatchComparison.termRemainder_nonneg (D : PatchComparison a Q T S z W kW X k Γ) (t : F.ActionTerm) :
    0 ≤ termRemainder a Q S z W kW X Γ t := by
  rcases t with p | ⟨j, c⟩
  · show 0 ≤ plaquetteGap (gaugedChainFields X Γ 0) (W 0) p ^ 2 *
      ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).im‖
    positivity
  · have ha := D.a_pos
    have h1 : 0 ≤ normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) := norm_nonneg _
    show 0 ≤ a * (normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) *
      (13 * (13 * F.blockSide * hullGapBound S z (gaugedChainFields X Γ j) (W j) c + 2 * topVariationSize F Q j) ^ 2 +
        3 * bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 2)) +
      a * (topVariationSize F Q j ^ 2 * normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 2)
    positivity
end
section
variable {F : BlockFrame} {j : ℕ} {S : Finset F.Cell} {z : F.Cell}
variable {a Q T : ℝ} {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain} {k Γ : F.SiteGauge}
theorem sq_sq_add_four_le {a b c d : ℝ} :
    ((a + b + c + d) ^ 2) ^ 2 ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
  have h1 : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d),
      sq_nonneg (c - d)]
  have h2 : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 ≤ 4 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - d ^ 2),
      sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - d ^ 2), sq_nonneg (c ^ 2 - d ^ 2)]
  have h3 := pow_le_pow_left₀ (sq_nonneg (a + b + c + d)) h1 2
  nlinarith
section PlaquetteBonds
variable (f : F.Site 0 × Fin 4 → ℝ) (hf0 : ∀ b, 0 ≤ f b)
include hf0
theorem sum_patchPlaquettes_first_bond_le :
    ∑ p ∈ patchPlaquettes S z, f (p.1, p.2.1) ≤ 4 * ∑ b ∈ innerBonds S 0, f b := by
  refine sum_comp_le_four_mul _ _ (fun p => (p.1, p.2.1)) f hf0 (fun p => p.2.2)
    (fun p hp => (plaquette_bond_mem hp (plaquetteCorners_base p) (plaquetteCorners_first p)).1) ?_
  rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ e e'
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  cases e'
  rfl
theorem sum_patchPlaquettes_second_bond_le :
    ∑ p ∈ patchPlaquettes S z, f (p.1 + unitStep 0 p.2.1, p.2.2) ≤ 4 * ∑ b ∈ innerBonds S 0, f b := by
  refine sum_comp_le_four_mul _ _ (fun p => (p.1 + unitStep 0 p.2.1, p.2.2)) f hf0 (fun p => p.2.1)
    (fun p hp => (plaquette_bond_mem hp (plaquetteCorners_first p) (plaquetteCorners_far p)).1) ?_
  rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ e e'
  simp only [Prod.mk.injEq] at e
  obtain ⟨h1, rfl⟩ := e
  cases e'
  rw [add_right_cancel h1]
theorem sum_patchPlaquettes_third_bond_le :
    ∑ p ∈ patchPlaquettes S z, f (p.1 + unitStep 0 p.2.2, p.2.1) ≤ 4 * ∑ b ∈ innerBonds S 0, f b := by
  refine sum_comp_le_four_mul _ _ (fun p => (p.1 + unitStep 0 p.2.2, p.2.1)) f hf0 (fun p => p.2.2)
    (fun p hp => (plaquette_bond_mem hp (plaquetteCorners_second p) (plaquetteCorners_far_comm p)).1) ?_
  rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ e e'
  simp only [Prod.mk.injEq] at e
  obtain ⟨h1, rfl⟩ := e
  cases e'
  rw [add_right_cancel h1]
theorem sum_patchPlaquettes_fourth_bond_le :
    ∑ p ∈ patchPlaquettes S z, f (p.1, p.2.2) ≤ 4 * ∑ b ∈ innerBonds S 0, f b := by
  refine sum_comp_le_four_mul _ _ (fun p => (p.1, p.2.2)) f hf0 (fun p => p.2.1)
    (fun p hp => (plaquette_bond_mem hp (plaquetteCorners_base p) (plaquetteCorners_second p)).1) ?_
  rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ e e'
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  cases e'
  rfl
end PlaquetteBonds
theorem plaquetteGap_pow_four_le {X W : F.GaugeField 0} {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ patchPlaquettes S z) :
    (plaquetteGap X W p ^ 2) ^ 2 ≤ 64 * (patchQuarticGap S z X W (p.1, p.2.1) +
      patchQuarticGap S z X W (p.1 + unitStep 0 p.2.1, p.2.2) +
      patchQuarticGap S z X W (p.1 + unitStep 0 p.2.2, p.2.1) + patchQuarticGap S z X W (p.1, p.2.2)) := by
  have hb1 := plaquette_bond_mem hp (plaquetteCorners_base p) (plaquetteCorners_first p)
  have hb2 := plaquette_bond_mem hp (plaquetteCorners_first p) (plaquetteCorners_far p)
  have hb3 := plaquette_bond_mem hp (plaquetteCorners_second p) (plaquetteCorners_far_comm p)
  have hb4 := plaquette_bond_mem hp (plaquetteCorners_base p) (plaquetteCorners_second p)
  rw [patchQuarticGap_eq (b := (p.1, p.2.1)) hb1.2.1 hb1.2.2,
    patchQuarticGap_eq (b := (p.1 + unitStep 0 p.2.1, p.2.2)) hb2.2.1 hb2.2.2,
    patchQuarticGap_eq (b := (p.1 + unitStep 0 p.2.2, p.2.1)) hb3.2.1 hb3.2.2,
    patchQuarticGap_eq (b := (p.1, p.2.2)) hb4.2.1 hb4.2.2]
  exact sq_sq_add_four_le
theorem PatchComparison.sum_plaquetteGap_pow_four_le (D : PatchComparison a Q T S z W kW X k Γ) :
    ∑ p ∈ patchPlaquettes S z, (plaquetteGap (gaugedChainFields X Γ 0) (W 0) p ^ 2) ^ 2 ≤ (32 * Q ^ 2) ^ 2 := by
  have hq := D.quartic 0 (Nat.succ_pos _)
  have hf0 := patchQuarticGap_nonneg (S := S) (z := z) (gaugedChainFields X Γ 0) (W 0)
  have e1 := sum_patchPlaquettes_first_bond_le (S := S) (z := z) _ hf0
  have e2 := sum_patchPlaquettes_second_bond_le (S := S) (z := z) _ hf0
  have e3 := sum_patchPlaquettes_third_bond_le (S := S) (z := z) _ hf0
  have e4 := sum_patchPlaquettes_fourth_bond_le (S := S) (z := z) _ hf0
  refine (Finset.sum_le_sum fun p hp => plaquetteGap_pow_four_le hp).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e : (32 * Q ^ 2) ^ 2 = 1024 * Q ^ 4 := by ring
  rw [e]
  linarith
theorem PatchComparison.sum_plaquette_remainders_le (D : PatchComparison a Q T S z W kW X k Γ) :
    ∑ p ∈ patchPlaquettes S z, termRemainder a Q S z W kW X Γ (Sum.inl p) ≤ (32 * Q ^ 2) * (2209 * T) := by
  have hT := D.T_nonneg
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt (patchPlaquettes S z)
    (fun p => plaquetteGap (gaugedChainFields X Γ 0) (W 0) p ^ 2)
    (fun p => ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).im‖)
  refine h1.trans ?_
  have h2 : Real.sqrt (∑ p ∈ patchPlaquettes S z, (plaquetteGap (gaugedChainFields X Γ 0) (W 0) p ^ 2) ^ 2) ≤
      32 * Q ^ 2 :=
    Real.sqrt_le_iff.2 ⟨by positivity, D.sum_plaquetteGap_pow_four_le⟩
  have h3 : Real.sqrt (∑ p ∈ patchPlaquettes S z,
      ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2) ≤ 2209 * T := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h4 := sum_patchPlaquettes_le D.amb D.odd D.sign
      (fun p => ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2)
      (fun _ => sq_nonneg _) (sq_nonneg T) D.curvature
    nlinarith
  exact mul_le_mul h2 h3 (Real.sqrt_nonneg _) (by positivity)
theorem enclosingCell_top (x : F.Site F.top) : enclosingCell x = x := by apply _root_.YangMills.Construction.PotentialMeans.enclosingCell_self <;> assumption
theorem PatchComparison.card_patchFitBonds_depth_le (D : PatchComparison a Q T S z W kW X k Γ) :
    ((patchFitBonds S z F.depth).card : ℝ) ≤ 4 * 47 ^ 4 := by
  classical
  have h := sum_patchFitBonds_le D.amb D.odd D.sign (S := S) (z := z) (j := F.depth) (Nat.lt_succ_self _)
    (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (B := 4) (by norm_num) (fun v => ?_)
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
    linarith
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc : (bondsOver S {v} (F.depth + 1)).card ≤ (Finset.univ : Finset (Fin 4)).card := by
      refine Finset.card_le_card_of_injOn (fun c => c.2) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
      intro c hc c' hc' e
      have h1 : enclosingCell c.1 ∈ ({v} : Finset F.Cell) := by
        have := Finset.mem_coe.1 hc
        unfold bondsOver at this
        exact (Finset.mem_filter.1 this).2
      have h2 : enclosingCell c'.1 ∈ ({v} : Finset F.Cell) := by
        have := Finset.mem_coe.1 hc'
        unfold bondsOver at this
        exact (Finset.mem_filter.1 this).2
      have e1 : c.1 = v := by
        have := Finset.mem_singleton.1 h1
        rwa [show enclosingCell c.1 = c.1 from enclosingCell_top c.1] at this
      have e2 : c'.1 = v := by
        have := Finset.mem_singleton.1 h2
        rwa [show enclosingCell c'.1 = c'.1 from enclosingCell_top c'.1] at this
      exact Prod.ext (e1.trans e2.symm) e
    exact show ((bondsOver S {v} (F.depth + 1)).card : ℝ) ≤ 4 from by
      have : (Finset.univ : Finset (Fin 4)).card = 4 := by simp
      rw [this] at hc
      exact_mod_cast hc
theorem fit_weight_sq_le {L ε κ g : ℝ} :
    (13 * (13 * L * ε + 2 * κ) ^ 2 + 3 * g ^ 2) ^ 2 ≤
      3 * ((4394 * L ^ 2) ^ 2 * ε ^ 4 + 104 ^ 2 * κ ^ 4 + 9 * g ^ 4) := by
  have h1 : 13 * (13 * L * ε + 2 * κ) ^ 2 ≤ 4394 * L ^ 2 * ε ^ 2 + 104 * κ ^ 2 := by
    nlinarith [sq_nonneg (13 * L * ε - 2 * κ)]
  have h2 : 0 ≤ 13 * (13 * L * ε + 2 * κ) ^ 2 + 3 * g ^ 2 := by positivity
  have h3 : 13 * (13 * L * ε + 2 * κ) ^ 2 + 3 * g ^ 2 ≤ 4394 * L ^ 2 * ε ^ 2 + 104 * κ ^ 2 + 3 * g ^ 2 := by
    linarith
  have h4 := pow_le_pow_left₀ h2 h3 2
  have h5 : (4394 * L ^ 2 * ε ^ 2 + 104 * κ ^ 2 + 3 * g ^ 2) ^ 2 ≤
      3 * ((4394 * L ^ 2 * ε ^ 2) ^ 2 + (104 * κ ^ 2) ^ 2 + (3 * g ^ 2) ^ 2) := by
    nlinarith [sq_nonneg (4394 * L ^ 2 * ε ^ 2 - 104 * κ ^ 2), sq_nonneg (4394 * L ^ 2 * ε ^ 2 - 3 * g ^ 2),
      sq_nonneg (104 * κ ^ 2 - 3 * g ^ 2)]
  linarith
theorem sqrt_sqrt_pow_four_eq {y : ℝ} (hy : 0 ≤ y) : Real.sqrt (Real.sqrt y) ^ 4 = y := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sqrt_sqrt_pow_four <;> assumption
theorem hullSum_nonneg_of_nonneg (g : F.Site j × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b) (c : F.Site (j + 1) × Fin 4) :
    0 ≤ BlockLines.hullSum g c := by apply _root_.YangMills.Construction.LevelGaps.hullSum_nonneg <;> assumption
theorem PatchComparison.sum_upper_bondGap_pow_four_le (D : PatchComparison a Q T S z W kW X k Γ) (hj : j < F.top) :
    ∑ c ∈ patchFitBonds S z j, bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 4 ≤ Q ^ 4 := by
  classical
  by_cases hjt : j = F.depth
  · subst hjt
    have h0 : ∀ c ∈ patchFitBonds S z F.depth,
        bondGap (gaugedChainFields X Γ (F.depth + 1)) (W (F.depth + 1)) c ^ 4 = 0 := by
      intro c _
      have e2 : gaugedChainFields X Γ (F.depth + 1) c.1 c.2 = W (F.depth + 1) c.1 c.2 := by
        show Γ F.top c.1 * X F.top c.1 c.2 * (Γ F.top (c.1 + unitStep F.top c.2))⁻¹ = W F.top c.1 c.2
        rw [D.top_gauge, D.top_gauge, D.top_same]
        simp
      unfold bondGap
      rw [e2, mul_inv_cancel]
      simp
    rw [Finset.sum_eq_zero h0]
    have := D.Q_nonneg
    positivity
  · have hj1 : j + 1 < F.top := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    refine le_trans ?_ (D.quartic (j + 1) hj1)
    have h1 : ∑ c ∈ patchFitBonds S z j, bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 4 =
        ∑ c ∈ patchFitBonds S z j, patchQuarticGap S z (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c := by
      refine Finset.sum_congr rfl fun c hc => ?_
      obtain ⟨he1, he2⟩ := bond_ends_mem_patchBaseSites D.odd hc
      rw [patchQuarticGap_eq (b := c) he1 he2]
    rw [h1]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => patchQuarticGap_nonneg _ _ _
    intro c hc
    exact (Finset.mem_filter.1 hc).1
theorem PatchComparison.sum_topVariationSize_pow_four_le (D : PatchComparison a Q T S z W kW X k Γ) (j : ℕ) :
    ∑ _c ∈ patchFitBonds S z j, topVariationSize F Q j ^ 4 ≤ 4 * 47 ^ 4 * Q ^ 4 := by
  by_cases hjt : j = F.depth
  · subst hjt
    have hk : topVariationSize F Q F.depth = Q := by simp [topVariationSize]
    rw [hk, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right D.card_patchFitBonds_depth_le (by positivity)
  · have hk : topVariationSize F Q j = 0 := by simp [topVariationSize, hjt]
    rw [hk]
    simp
    positivity
theorem PatchComparison.sum_fit_weight_sq_le (D : PatchComparison a Q T S z W kW X k Γ) (hj : j < F.top) :
    ∑ c ∈ patchFitBonds S z j,
      (13 * (13 * F.blockSide * hullGapBound S z (gaugedChainFields X Γ j) (W j) c + 2 * topVariationSize F Q j) ^ 2 +
        3 * bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 2) ^ 2 ≤
      squareSumConstant F.blockSide * Q ^ 4 := by
  classical
  have hodd := D.odd
  have hg0 : ∀ b, 0 ≤ patchQuarticGap S z (gaugedChainFields X Γ j) (W j) b := patchQuarticGap_nonneg _ _
  have h1 : ∑ c ∈ patchFitBonds S z j, hullGapBound S z (gaugedChainFields X Γ j) (W j) c ^ 4 ≤
      hullConstant F.blockSide * Q ^ 4 := by
    have h2 := BlockLines.sum_hullSum_le (B := S) hj hodd (patchFitBonds S z j) (Finset.filter_subset _ _)
      (patchQuarticGap S z (gaugedChainFields X Γ j) (W j)) hg0
    have h3 : ∑ c ∈ patchFitBonds S z j, hullGapBound S z (gaugedChainFields X Γ j) (W j) c ^ 4 =
        ∑ c ∈ patchFitBonds S z j, BlockLines.hullSum (patchQuarticGap S z (gaugedChainFields X Γ j) (W j)) c :=
      Finset.sum_congr rfl fun c _ => sqrt_sqrt_pow_four_eq (hullSum_nonneg_of_nonneg _ hg0 c)
    rw [h3]
    exact h2.trans (mul_le_mul_of_nonneg_left (D.quartic j hj) (hullConstant_nonneg _))
  have h4 := D.sum_topVariationSize_pow_four_le j
  have h5 := D.sum_upper_bondGap_pow_four_le hj
  have h6 : ∀ c ∈ patchFitBonds S z j,
      (13 * (13 * F.blockSide * hullGapBound S z (gaugedChainFields X Γ j) (W j) c + 2 * topVariationSize F Q j) ^ 2 +
        3 * bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 2) ^ 2 ≤
      3 * ((4394 * (F.blockSide : ℝ) ^ 2) ^ 2 * hullGapBound S z (gaugedChainFields X Γ j) (W j) c ^ 4 +
        104 ^ 2 * topVariationSize F Q j ^ 4 +
        9 * bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 4) :=
    fun c _ => fit_weight_sq_le
  refine (Finset.sum_le_sum h6).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  unfold squareSumConstant
  have a1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (4394 * (F.blockSide : ℝ) ^ 2) ^ 2)
  nlinarith
theorem PatchComparison.level_remainder_sum_le (D : PatchComparison a Q T S z W kW X k Γ) (hj : j < F.top) :
    ∑ c ∈ patchFitBonds S z j, normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) *
      (13 * (13 * F.blockSide * hullGapBound S z (gaugedChainFields X Γ j) (W j) c + 2 * topVariationSize F Q j) ^ 2 +
        3 * bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 2) ≤
      (2209 * (T * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j))) *
        (Real.sqrt (squareSumConstant F.blockSide) * Q ^ 2) := by
  obtain ⟨r0, _⟩ := D.ratio_bounds
  have hT := D.T_nonneg
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt (patchFitBonds S z j)
    (fun c => normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c))
    (fun c => 13 * (13 * F.blockSide * hullGapBound S z (gaugedChainFields X Γ j) (W j) c +
        2 * topVariationSize F Q j) ^ 2 + 3 * bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 2)
  refine h1.trans ?_
  have h2 : Real.sqrt (∑ c ∈ patchFitBonds S z j,
      normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 2) ≤
      2209 * (T * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j)) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h4 := sum_patchFitBonds_le D.amb D.odd D.sign hj
      (fun c => normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 2)
      (fun _ => sq_nonneg _) (sq_nonneg _) (D.misfits j hj)
    nlinarith
  have h3 : Real.sqrt (∑ c ∈ patchFitBonds S z j,
      (13 * (13 * F.blockSide * hullGapBound S z (gaugedChainFields X Γ j) (W j) c + 2 * topVariationSize F Q j) ^ 2 +
        3 * bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 2) ^ 2) ≤
      Real.sqrt (squareSumConstant F.blockSide) * Q ^ 2 := by
    refine (Real.sqrt_le_sqrt (D.sum_fit_weight_sq_le hj)).trans (le_of_eq ?_)
    have hs0 : 0 ≤ squareSumConstant F.blockSide := by
      unfold squareSumConstant
      have := hullConstant_nonneg F.blockSide
      positivity
    rw [Real.sqrt_mul hs0]
    congr 1
    have e : Q ^ 4 = (Q ^ 2) ^ 2 := by ring
    rw [e, Real.sqrt_sq (by positivity)]
  exact mul_le_mul h2 h3 (Real.sqrt_nonneg _) (by positivity)
theorem PatchComparison.rotation_remainder_sum_le (D : PatchComparison a Q T S z W kW X k Γ) (hj : j < F.top) :
    ∑ c ∈ patchFitBonds S z j, topVariationSize F Q j ^ 2 * normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 2 ≤
      (if j = F.depth then Q ^ 2 * (47 ^ 4 * T) else 0) := by
  obtain ⟨r0, r1⟩ := D.ratio_bounds
  have hT := D.T_nonneg
  have hT1 := D.T_small
  rw [← Finset.mul_sum]
  by_cases hjt : j = F.depth
  · subst hjt
    rw [if_pos rfl]
    have hk : topVariationSize F Q F.depth = Q := by simp [topVariationSize]
    rw [hk]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Q)
    have h4 := sum_patchFitBonds_le D.amb D.odd D.sign hj
      (fun c => normSubOne (bondMisfit (W F.depth) (kW (F.depth + 1)) (W (F.depth + 1)) c) ^ 2)
      (fun _ => sq_nonneg _) (sq_nonneg _) (D.misfits F.depth hj)
    refine h4.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    have h3 : (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - F.depth) ≤ 1 := pow_le_one₀ r0 (by linarith)
    have h5 : 0 ≤ (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - F.depth) := pow_nonneg r0 _
    have h6 : T * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - F.depth) ≤ T := by nlinarith
    have h7 : 0 ≤ T * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - F.depth) := mul_nonneg hT h5
    nlinarith
  · have hk : topVariationSize F Q j = 0 := by simp [topVariationSize, hjt]
    rw [hk, if_neg hjt]
    simp
theorem PatchComparison.sum_termRemainder_le (D : PatchComparison a Q T S z W kW X k Γ) :
    ∑ t ∈ patchActionTerms S z, termRemainder a Q S z W kW X Γ t ≤ totalConstant a F.blockSide * T * Q ^ 2 := by
  classical
  obtain ⟨r0, r1⟩ := D.ratio_bounds
  have hT := D.T_nonneg
  have ha := D.a_pos
  rw [PatchLocality.sum_patchActionTerms]
  have h1 := D.sum_plaquette_remainders_le
  have h2 : ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j, termRemainder a Q S z W kW X Γ (Sum.inr ⟨j, c⟩) ≤
      ∑ j ∈ Finset.range F.top, (a * ((2209 * (T * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j))) *
        (Real.sqrt (squareSumConstant F.blockSide) * Q ^ 2)) +
        a * (if j = F.depth then Q ^ 2 * (47 ^ 4 * T) else 0)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjn := Finset.mem_range.1 hj
    have e : ∑ c ∈ patchFitBonds S z j, termRemainder a Q S z W kW X Γ (Sum.inr ⟨j, c⟩) =
        a * ∑ c ∈ patchFitBonds S z j, normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) *
          (13 * (13 * F.blockSide * hullGapBound S z (gaugedChainFields X Γ j) (W j) c +
            2 * topVariationSize F Q j) ^ 2 +
            3 * bondGap (gaugedChainFields X Γ (j + 1)) (W (j + 1)) c ^ 2) +
        a * ∑ c ∈ patchFitBonds S z j,
          topVariationSize F Q j ^ 2 * normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      rfl
    rw [e]
    exact add_le_add (mul_le_mul_of_nonneg_left (D.level_remainder_sum_le hjn) ha.le)
      (mul_le_mul_of_nonneg_left (D.rotation_remainder_sum_le hjn) ha.le)
  have h3 : ∑ j ∈ Finset.range F.top, (a * ((2209 * (T * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j))) *
      (Real.sqrt (squareSumConstant F.blockSide) * Q ^ 2)) +
        a * (if j = F.depth then Q ^ 2 * (47 ^ 4 * T) else 0)) ≤
      a * (2209 * T * (Real.sqrt (squareSumConstant F.blockSide) * Q ^ 2)) * 2 + a * (Q ^ 2 * (47 ^ 4 * T)) := by
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ (le_of_eq ?_)
    · have e : ∑ j ∈ Finset.range F.top, a * ((2209 * (T * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j))) *
          (Real.sqrt (squareSumConstant F.blockSide) * Q ^ 2)) =
          a * (2209 * T * (Real.sqrt (squareSumConstant F.blockSide) * Q ^ 2)) *
            ∑ j ∈ Finset.range F.top, (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (sum_range_pow_reflect_le_two r0 r1 F.top) (by positivity)
    · rw [← Finset.mul_sum, Finset.sum_ite_eq']
      simp
  unfold totalConstant
  nlinarith [mul_nonneg hT (sq_nonneg Q)]
end
end TermwiseBounds
theorem termwiseFirstVariation (hs : lowCostPatchBoundsStatement) (hgc : gaugeCovarianceStatement) :
    termwiseFirstVariationStatement := by
  intro a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨L₁, hL₁⟩ := hs a ha
  refine ⟨max L₁ 8, fun L hodd hL C₁ C Cd hC₁ hC hCd => ?_⟩
  obtain ⟨c₁, hc₁, hsz⟩ := hL₁ L hodd (le_trans (le_max_left _ _) hL)
  have hKg : 0 < TermwiseBounds.gapConstant L := by
    have := TermwiseBounds.two_le_gapConstant L
    linarith
  have htot : 0 < TermwiseBounds.totalConstant a L := by
    unfold TermwiseBounds.totalConstant
    have := Real.sqrt_nonneg (TermwiseBounds.squareSumConstant L)
    positivity
  refine ⟨C ^ 2 * C₁ * TermwiseBounds.totalConstant a L,
    min (min c₁ (1 / 8)) (1 / (8 * TermwiseBounds.gapConstant L * (C * Real.sqrt Cd + 1))),
    by positivity, by positivity, fun e0 he0 hec => ⟨1 / (2 * C₁), by positivity, ?_⟩⟩
  intro F m S hFL hamb hm hreg s V v hs0 hsσ hcold hv U hU X k Γ z hX hz hterm hframe
  subst hFL
  obtain ⟨hpin, henergy⟩ := hframe
  obtain ⟨hΓ, hlk, hq, hK⟩ := hpin
  have he1 : e0 ≤ c₁ := (hec.trans (min_le_left _ _)).trans (min_le_left _ _)
  have he8 : e0 ≤ 1 / 8 := (hec.trans (min_le_left _ _)).trans (min_le_right _ _)
  have he3 : e0 ≤ 1 / (8 * TermwiseBounds.gapConstant F.blockSide * (C * Real.sqrt Cd + 1)) :=
    hec.trans (min_le_right _ _)
  have hsign := (closedOrthant_spec hreg (by omega) z).1
  obtain ⟨hmean, _, hplq⟩ := hsz e0 he0 he1 F m S rfl hamb hm hreg X k z hz hterm
  set W := criticalFieldChain S V v U with hW
  set kW := criticalGauge S V U with hkW
  set D := relativeEnergy a S z W kW X k Γ with hD
  have hD0 : 0 ≤ D := by
    rw [hD]
    unfold relativeEnergy
    refine add_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (mul_nonneg ha.le ?_)
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hQ0 : 0 ≤ C * Real.sqrt D := by positivity
  have hroot2 : Real.sqrt D ≤ Real.sqrt Cd * e0 := by
    have h1 : D ≤ (Real.sqrt Cd * e0) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hCd.le]
      exact henergy
    exact Real.sqrt_le_iff.2 ⟨by positivity, h1⟩
  have hsmall : TermwiseBounds.gapConstant F.blockSide * (C * Real.sqrt D) ≤ 1 / 8 := by
    have hp : 0 < 8 * TermwiseBounds.gapConstant F.blockSide * (C * Real.sqrt Cd + 1) := by positivity
    have h1 : e0 * (8 * TermwiseBounds.gapConstant F.blockSide * (C * Real.sqrt Cd + 1)) ≤ 1 := by
      rwa [le_div_iff₀ hp] at he3
    have h2 : C * Real.sqrt D ≤ C * Real.sqrt Cd * e0 := by
      have := mul_le_mul_of_nonneg_left hroot2 hC.le
      linarith
    have h3 : TermwiseBounds.gapConstant F.blockSide * (C * Real.sqrt D) ≤
        TermwiseBounds.gapConstant F.blockSide * (C * Real.sqrt Cd * e0) :=
      mul_le_mul_of_nonneg_left h2 hKg.le
    nlinarith
  have hTs : C₁ * s ≤ 1 / 2 := by
    have h1 : s * (2 * C₁) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hsσ
    linarith
  have hnL : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := one_le_pow₀ (by exact_mod_cast hodd.pos)
  have P : TermwiseBounds.PatchComparison a (C * Real.sqrt D) (C₁ * s) S z W kW X k Γ :=
    { gc := hgc
      odd := hodd
      amb := hamb
      sign := hsign
      a_pos := ha
      eight_le_side := le_trans (le_max_right _ _) hL
      top_gauge := hΓ
      top_same := by rw [hX]; exact (ChartCoordinates.chartChain_top _ _ _).symm
      link := fun j hj y hy => hlk j hj y hy
      Q_nonneg := hQ0
      quartic := fun j hj => hq j hj
      rearrangedPathCorner := hK
      small := hsmall
      means := hmean
      plaq := by
        intro p hp
        have h1 := Finset.single_le_sum (f := fun p => normSubOne (plaquetteHolonomy (X 0) p) ^ 2)
          (fun _ _ => sq_nonneg _) hp
        have h2 := h1.trans hplq
        have h3 : normSubOne (plaquetteHolonomy (X 0) p) ^ 2 ≤ (1 / 4) ^ 2 := by nlinarith
        exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h3
      T_nonneg := by positivity
      T_small := hTs
      misfits := fun j hj v' => (hU.misfits_on_cells j v' hj).2
      curvature := by
        intro v'
        have h1 := (hU.curvature_and_misfits (cellCentre 0 v') ((F.blockSide : ℝ) ^ F.top) hnL le_rfl).1
        rw [div_self (by positivity), Real.one_rpow, mul_one] at h1
        have e0' : W 0 = chartField (referenceFieldChain S V) U 0 :=
          ChartCoordinates.chartChain_of_lt _ _ _ (Nat.succ_pos _)
        rw [e0']
        refine le_trans (le_of_eq ?_) h1
        unfold localCurvatureSum
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext q
        simp only [Finset.mem_filter] }
  refine ⟨TermwiseBounds.termRemainder a (C * Real.sqrt D) S z W kW X Γ, fun t ht => P.actionTerm_ineq ht,
    P.termRemainder_nonneg, ?_⟩
  refine P.sum_termRemainder_le.trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt hD0]
  ring
end YangMills.Construction.BlockAverages
end
