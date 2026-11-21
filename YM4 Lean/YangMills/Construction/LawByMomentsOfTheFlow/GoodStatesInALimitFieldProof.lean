import YangMills.Construction.CellOfTheFlow.TheDrawsStandOnGroundsProof
import YangMills.Construction.LawByMomentsOfTheFlow.ABoundAtClearStatesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.WindowInALimitField
import Mathlib
import YangMills.Construction.LawByMomentsOfTheFlow.HullsClearOfThePointInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheCurvatureInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.ResponsesOfAPointAreHeldByTheScores
import YangMills.Construction.LawByMomentsOfTheFlow.SitesAtTheFarLevelOfTheScale
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheScale
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsAGaussianChainProof
import YangMills.Construction.SixteenPointsOnASmallTorus.ErrorOfTheCopiesProof
set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction.MomentLaw
def goodStatesLimitStatement : Prop :=
  ForAllHullParameters fun Λ => ∃ (C : ℕ → ℝ) (X₀ : ℝ), Λ.floor ≤ X₀ ∧
    ∀ (S : MomentPoint Λ) (L : LimitLawAtPoint S), X₀ ≤ S.scaleCoupling →
    (∀ u : ℕ, (∀ i, (L.points i).lastSeparated ≤ u ∧ u ≤ (L.points i).lastSeparated + S.logIndex + 1) →
      (∀ (N : ℕ) (j : L.Index), L.observables j = notGoodIndicator u →
        ∀ᵐ ω ∂L.law, L.condMeanAt j ω ≤ C N * S.scaleCoupling ^ (-(N : ℝ))) ∧
      ∀ (k : ℕ) (j : L.Index), L.observables j = goodCurvaturePower u k →
        ∀ᵐ ω ∂L.law, L.condMeanAt j ω ≤ C k * S.scaleCoupling ^ ((1 : ℝ) / 4000)) ∧
    ∀ (B : Finset (Fin Λ.k)) (N : ℕ) (j : L.Index), L.observables j = badResponseProduct B →
      ∀ᵐ ω ∂L.law, L.condMeanAt j ω ≤ C N * S.scaleCoupling ^ (-(N : ℝ))
end YangMills.Construction.MomentLaw
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open MomentMethod TorusFields WeightedResponses
section Reals
private theorem pow_mul_exp_neg_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) (N : ℕ) :
    x ^ N * Real.exp (-(c * x)) ≤ (N.factorial : ℝ) / c ^ N := by apply _root_.YangMills.SharedProofs.p10986 <;> assumption
private theorem one_add_pow_le {x v T Z : ℝ} {k κ Q : ℕ} (hx : 1 ≤ x) (hv : 0 ≤ v) (hT : 1 ≤ T) (hk : k ≤ κ)
    (hκ : κ ≤ 2 * Q) (hZ : v ^ (2 * Q) ≤ Z) :
    (1 + x ^ ((1 : ℝ) / 2) * v) ^ k ≤ (2 * T) ^ κ + 2 ^ κ * T ^ κ / T ^ (2 * Q) * x ^ Q * Z := by
  have hx0 : 0 < x := by linarith
  set w := x ^ ((1 : ℝ) / 2) with hw
  have hww : w ^ (2 * Q) = x ^ Q := by
    rw [pow_mul, hw, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hx0.le]
    norm_num
  set s := w * v with hs
  have hs0 : 0 ≤ s := by positivity
  have hZ0 : 0 ≤ Z := (pow_nonneg hv _).trans hZ
  have hT0 : 0 < T := by linarith
  have hone : (1 + s) ^ k ≤ (1 + s) ^ κ := pow_le_pow_right₀ (by linarith) hk
  have hsec : 0 ≤ 2 ^ κ * T ^ κ / T ^ (2 * Q) * x ^ Q * Z := by positivity
  refine hone.trans ?_
  by_cases hsT : s ≤ T
  · have : (1 + s) ^ κ ≤ (2 * T) ^ κ := pow_le_pow_left₀ (by linarith) (by linarith) κ
    linarith
  · have hsT' : T < s := not_le.mp hsT
    have h1 : (1 + s) ^ κ ≤ (2 * s) ^ κ := pow_le_pow_left₀ (by linarith) (by linarith) κ
    have hs1 : 1 ≤ s / T := by rw [le_div_iff₀ hT0]; linarith
    have h2 : (s / T) ^ κ ≤ (s / T) ^ (2 * Q) := pow_le_pow_right₀ hs1 hκ
    rw [div_pow, div_pow] at h2
    have hTk : 0 < T ^ κ := by positivity
    have h3 : s ^ κ ≤ T ^ κ / T ^ (2 * Q) * s ^ (2 * Q) := by
      rw [div_le_iff₀ hTk] at h2
      calc s ^ κ ≤ s ^ (2 * Q) / T ^ (2 * Q) * T ^ κ := h2
        _ = T ^ κ / T ^ (2 * Q) * s ^ (2 * Q) := by ring
    have h4 : s ^ (2 * Q) ≤ x ^ Q * Z := by
      rw [hs, mul_pow, hww]
      gcongr
    have h5 : (2 * s) ^ κ ≤ 2 ^ κ * T ^ κ / T ^ (2 * Q) * x ^ Q * Z := by
      rw [mul_pow]
      calc 2 ^ κ * s ^ κ ≤ 2 ^ κ * (T ^ κ / T ^ (2 * Q) * (x ^ Q * Z)) := by
            gcongr
            exact h3.trans (by gcongr)
        _ = 2 ^ κ * T ^ κ / T ^ (2 * Q) * x ^ Q * Z := by ring
    have : 0 ≤ (2 * T) ^ κ := by positivity
    linarith
abbrev _root_.YangMills.SharedProofs.p20252 := @one_add_pow_le
private theorem clusterRange_bounds {x : ℝ} (hx : (8 : ℝ) ^ 100 ≤ x) :
    (8 : ℝ) ≤ (TorusLumps.clusterRange x : ℝ) ∧ (TorusLumps.clusterRange x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100) := by
  have e : ((8 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h8 : (8 : ℝ) ≤ x ^ ((1 : ℝ) / 100) := by
    have := Real.rpow_le_rpow (by positivity) hx (show (0 : ℝ) ≤ 1 / 100 by norm_num)
    rwa [e] at this
  have h1 : x ^ ((1 : ℝ) / 100) ≤ (TorusLumps.clusterRange x : ℝ) := Nat.le_ceil _
  have h2 : (TorusLumps.clusterRange x : ℝ) < x ^ ((1 : ℝ) / 100) + 1 := Nat.ceil_lt_add_one (by positivity)
  exact ⟨h8.trans h1, by linarith⟩
abbrev _root_.YangMills.SharedProofs.p89177 := @clusterRange_bounds
private theorem clusterRange_pow_eight_le {x : ℝ} (hx : (8 : ℝ) ^ 100 ≤ x) :
    (TorusLumps.clusterRange x : ℝ) ^ 8 ≤ 256 * x ^ ((2 : ℝ) / 25) := by
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have hr := clusterRange_bounds hx
  have e : (x ^ ((1 : ℝ) / 100)) ^ 8 = x ^ ((2 : ℝ) / 25) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  calc (TorusLumps.clusterRange x : ℝ) ^ 8 ≤ (2 * x ^ ((1 : ℝ) / 100)) ^ 8 := pow_le_pow_left₀ (by positivity) hr.2 8
    _ = 256 * x ^ ((2 : ℝ) / 25) := by rw [mul_pow, e]; norm_num
abbrev _root_.YangMills.SharedProofs.p28510 := @clusterRange_pow_eight_le
private theorem offsetCount_le {x : ℝ} (hx : (8 : ℝ) ^ 100 ≤ x) :
    ((16 * (2 * (2 * (TorusLumps.clusterRange x) ^ 2) + 1) ^ 4 : ℕ) : ℝ) ≤ 2560000 * x ^ ((2 : ℝ) / 25) := by
  have hr := clusterRange_bounds hx
  have h8 := clusterRange_pow_eight_le hx
  set R : ℝ := (TorusLumps.clusterRange x : ℝ) with hR
  push_cast
  rw [← hR]
  have h1 : 2 * (2 * R ^ 2) + 1 ≤ 5 * R ^ 2 := by nlinarith [hr.1]
  have h2 : (2 * (2 * R ^ 2) + 1) ^ 4 ≤ (5 * R ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
  nlinarith
abbrev _root_.YangMills.SharedProofs.p40573 := @offsetCount_le
private theorem firstConstant_bound {x c CH Cq Pc : ℝ} (N : ℕ) (hx : 1 ≤ x) (hc : 0 < c) (hCH : 0 ≤ CH) (hCq : 0 ≤ Cq)
    (hP : Pc ≤ 2560000 * x ^ ((2 : ℝ) / 25)) :
    2 * (CH * Real.exp (-(c * x))) + Pc * (Cq * x ^ (-((2 * N + 2 : ℕ) : ℝ)) / (x ^ (-(1 / 4) : ℝ)) ^ (2 * (2 * N + 2))) ≤
      (2 * CH * ((N.factorial : ℝ) / c ^ N) + 2560000 * Cq) * x ^ (-(N : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hy : x ^ (-(N : ℝ)) = (x ^ N)⁻¹ := by rw [Real.rpow_neg hx0.le, Real.rpow_natCast]
  have hxN : 0 < x ^ N := by positivity
  have e1 : Real.exp (-(c * x)) ≤ (N.factorial : ℝ) / c ^ N * x ^ (-(N : ℝ)) := by
    have h := pow_mul_exp_neg_le hx0.le hc N
    rw [hy, ← div_eq_mul_inv, le_div_iff₀ hxN, mul_comm]
    exact h
  have e2 : Cq * x ^ (-((2 * N + 2 : ℕ) : ℝ)) / (x ^ (-(1 / 4) : ℝ)) ^ (2 * (2 * N + 2)) =
      Cq * x ^ (-(N : ℝ) - 1) := by
    rw [← Real.rpow_natCast (x ^ (-(1 / 4) : ℝ)), ← Real.rpow_mul hx0.le, mul_div_assoc, ← Real.rpow_sub hx0]
    congr 2
    push_cast
    ring
  rw [e2]
  have hA : 0 ≤ Cq * x ^ (-(N : ℝ) - 1) := by positivity
  have e3 : x ^ ((2 : ℝ) / 25) * x ^ (-(N : ℝ) - 1) ≤ x ^ (-(N : ℝ)) := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have e4 : Pc * (Cq * x ^ (-(N : ℝ) - 1)) ≤ 2560000 * Cq * x ^ (-(N : ℝ)) := by
    calc Pc * (Cq * x ^ (-(N : ℝ) - 1)) ≤ 2560000 * x ^ ((2 : ℝ) / 25) * (Cq * x ^ (-(N : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right hP hA
      _ = 2560000 * Cq * (x ^ ((2 : ℝ) / 25) * x ^ (-(N : ℝ) - 1)) := by ring
      _ ≤ 2560000 * Cq * x ^ (-(N : ℝ)) := by gcongr
  have e5 : 2 * (CH * Real.exp (-(c * x))) ≤ 2 * CH * ((N.factorial : ℝ) / c ^ N) * x ^ (-(N : ℝ)) := by
    have := mul_le_mul_of_nonneg_left e1 hCH
    nlinarith
  nlinarith
abbrev _root_.YangMills.SharedProofs.p108377 := @firstConstant_bound
private theorem secondConstant_bound {x c CH Cq Pc : ℝ} (k : ℕ) (hx : 1 ≤ x) (hc : 0 < c) (hCH : 0 ≤ CH) (hCq : 0 ≤ Cq)
    (hP : Pc ≤ 2560000 * x ^ ((2 : ℝ) / 25)) :
    1 ≤ x ^ ((1 : ℝ) / (4000 * ((k + 1 : ℕ) : ℝ))) ∧
    (2 * x ^ ((1 : ℝ) / (4000 * ((k + 1 : ℕ) : ℝ)))) ^ (k + 1) +
        2 ^ (k + 1) * (x ^ ((1 : ℝ) / (4000 * ((k + 1 : ℕ) : ℝ)))) ^ (k + 1) /
          (x ^ ((1 : ℝ) / (4000 * ((k + 1 : ℕ) : ℝ)))) ^ (2 * (201 * (k + 1))) * x ^ (201 * (k + 1)) *
          (Pc * (Cq * x ^ (-((201 * (k + 1) : ℕ) : ℝ)))) +
        (1 + x ^ ((1 : ℝ) / 4)) ^ (k + 1) * (CH * Real.exp (-(c * x))) ≤
      2 ^ (k + 1) * (1 + 2560000 * Cq + CH * (((k + 1).factorial : ℝ) / c ^ (k + 1))) * x ^ ((1 : ℝ) / 4000) := by
  have hx0 : 0 < x := by linarith
  have hκ : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  set κr : ℝ := ((k + 1 : ℕ) : ℝ) with hκr
  set T : ℝ := x ^ ((1 : ℝ) / (4000 * κr)) with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow hx (by positivity)
  refine ⟨hT1, ?_⟩
  set A : ℝ := x ^ ((1 : ℝ) / 4000) with hA
  have hA1 : 1 ≤ A := Real.one_le_rpow hx (by norm_num)
  have hTk : T ^ (k + 1) = A := by
    rw [hT, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← hκr, hA]
    congr 1
    field_simp
  have hTQ : T ^ (2 * (201 * (k + 1))) = x ^ ((201 : ℝ) / 2000) := by
    rw [hT, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    have : ((2 * (201 * (k + 1)) : ℕ) : ℝ) = 402 * κr := by
      rw [hκr]
      push_cast
      ring
    rw [this]
    field_simp
    norm_num
  have hxQ : x ^ (201 * (k + 1)) * x ^ (-((201 * (k + 1) : ℕ) : ℝ)) = 1 := by
    rw [Real.rpow_neg hx0.le, Real.rpow_natCast]
    exact mul_inv_cancel₀ (by positivity)
  have t1 : (2 * T) ^ (k + 1) = 2 ^ (k + 1) * A := by rw [mul_pow, hTk]
  have t2 : 2 ^ (k + 1) * T ^ (k + 1) / T ^ (2 * (201 * (k + 1))) * x ^ (201 * (k + 1)) *
      (Pc * (Cq * x ^ (-((201 * (k + 1) : ℕ) : ℝ)))) ≤ 2 ^ (k + 1) * (2560000 * Cq) * A := by
    have hq : 0 < x ^ ((201 : ℝ) / 2000) := by positivity
    rw [hTk, hTQ]
    have e : 2 ^ (k + 1) * A / x ^ ((201 : ℝ) / 2000) * x ^ (201 * (k + 1)) *
        (Pc * (Cq * x ^ (-((201 * (k + 1) : ℕ) : ℝ)))) =
        2 ^ (k + 1) * A * Cq * (Pc / x ^ ((201 : ℝ) / 2000)) *
          (x ^ (201 * (k + 1)) * x ^ (-((201 * (k + 1) : ℕ) : ℝ))) := by ring
    rw [e, hxQ, mul_one]
    have h1 : Pc / x ^ ((201 : ℝ) / 2000) ≤ 2560000 := by
      rw [div_le_iff₀ hq]
      exact hP.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by norm_num)) (by norm_num))
    calc 2 ^ (k + 1) * A * Cq * (Pc / x ^ ((201 : ℝ) / 2000)) ≤ 2 ^ (k + 1) * A * Cq * 2560000 := by gcongr
      _ = 2 ^ (k + 1) * (2560000 * Cq) * A := by ring
  have t3 : (1 + x ^ ((1 : ℝ) / 4)) ^ (k + 1) * (CH * Real.exp (-(c * x))) ≤
      2 ^ (k + 1) * (CH * (((k + 1).factorial : ℝ) / c ^ (k + 1))) * A := by
    have h1 : x ^ ((1 : ℝ) / 4) ≤ x := by
      have := Real.rpow_le_rpow_of_exponent_le hx (show (1 : ℝ) / 4 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have h2 : (1 + x ^ ((1 : ℝ) / 4)) ^ (k + 1) ≤ (2 * x) ^ (k + 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have h3 := pow_mul_exp_neg_le hx0.le hc (k + 1)
    calc (1 + x ^ ((1 : ℝ) / 4)) ^ (k + 1) * (CH * Real.exp (-(c * x)))
        ≤ (2 * x) ^ (k + 1) * (CH * Real.exp (-(c * x))) := by gcongr
      _ = 2 ^ (k + 1) * (CH * (x ^ (k + 1) * Real.exp (-(c * x)))) := by rw [mul_pow]; ring
      _ ≤ 2 ^ (k + 1) * (CH * (((k + 1).factorial : ℝ) / c ^ (k + 1))) := by gcongr
      _ ≤ 2 ^ (k + 1) * (CH * (((k + 1).factorial : ℝ) / c ^ (k + 1))) * A :=
        le_mul_of_one_le_right (by positivity) hA1
  rw [t1]
  nlinarith
abbrev _root_.YangMills.SharedProofs.p80063 := @secondConstant_bound
private def thirdConstant (c₀ CS CN : ℝ) (k : ℕ) : ℝ :=
  (1 + |c₀| * |CS|) ^ (2 * k) * 256 ^ k * (1 + (1 + |CN|) ^ (2 * k) * ((2 * k).factorial : ℝ) ^ 6)
private theorem thirdConstant_bound {x c₀ CS CN C₁ : ℝ} {k p : ℕ} (N : ℕ) (hx : 1 ≤ x) (hC₁ : 0 ≤ C₁) (hp : p ≤ 2 * k) :
    x ^ (-((N + k : ℕ) : ℝ)) / 2 * ((1 + |c₀| * |CS|) ^ (2 * k) * 256 ^ k * x ^ k) * (CN ^ p * (p.factorial : ℝ) ^ 6) +
        1 / (2 * x ^ (-((N + k : ℕ) : ℝ))) * (C₁ * x ^ (-((2 * N + k : ℕ) : ℝ))) ≤
      (thirdConstant c₀ CS CN k + C₁) * x ^ (-(N : ℝ)) := by
  have hx0 : 0 < x := by linarith
  set G : ℝ := (1 + |c₀| * |CS|) ^ (2 * k) * 256 ^ k with hG
  set Mk : ℝ := 1 + (1 + |CN|) ^ (2 * k) * ((2 * k).factorial : ℝ) ^ 6 with hMk
  have hb : CN ^ p * (p.factorial : ℝ) ^ 6 ≤ Mk := by
    have h1 : CN ^ p ≤ (1 + |CN|) ^ (2 * k) := by
      have h2 : CN ^ p ≤ |CN| ^ p := by
        rw [← abs_pow]
        exact le_abs_self _
      exact h2.trans ((pow_le_pow_left₀ (abs_nonneg _) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg CN]) hp))
    have h3 : (p.factorial : ℝ) ≤ ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_le hp
    have h4 : (p.factorial : ℝ) ^ 6 ≤ ((2 * k).factorial : ℝ) ^ 6 := pow_le_pow_left₀ (by positivity) h3 6
    have h5 : CN ^ p * (p.factorial : ℝ) ^ 6 ≤ (1 + |CN|) ^ (2 * k) * ((2 * k).factorial : ℝ) ^ 6 :=
      mul_le_mul h1 h4 (by positivity) (by positivity)
    linarith
  have a₁ : x ^ (-((N + k : ℕ) : ℝ)) = (x ^ N * x ^ k)⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.rpow_natCast, pow_add]
  have a₂ : x ^ (-((2 * N + k : ℕ) : ℝ)) = (x ^ N * x ^ N * x ^ k)⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.rpow_natCast, pow_add, two_mul, pow_add]
  have a₃ : x ^ (-(N : ℝ)) = (x ^ N)⁻¹ := by rw [Real.rpow_neg hx0.le, Real.rpow_natCast]
  rw [a₁, a₂, a₃]
  have h1 : (x ^ N * x ^ k)⁻¹ / 2 * (G * x ^ k) * (CN ^ p * (p.factorial : ℝ) ^ 6) ≤ (x ^ N * x ^ k)⁻¹ / 2 * (G * x ^ k) * Mk := by
    gcongr
  have hmain : ((x ^ N * x ^ k)⁻¹ / 2 * (G * x ^ k) * Mk +
      1 / (2 * (x ^ N * x ^ k)⁻¹) * (C₁ * (x ^ N * x ^ N * x ^ k)⁻¹)) = (G * Mk + C₁) / 2 * (x ^ N)⁻¹ := by
    field_simp
  have hpos : 0 ≤ G * Mk + C₁ := by positivity
  have hthird : thirdConstant c₀ CS CN k = G * Mk := rfl
  rw [hthird]
  have hXi : 0 ≤ (x ^ N)⁻¹ := by positivity
  have h2 : (G * Mk + C₁) / 2 * (x ^ N)⁻¹ ≤ (G * Mk + C₁) * (x ^ N)⁻¹ := by
    apply mul_le_mul_of_nonneg_right _ hXi
    linarith
  linarith
private theorem prod_abs_sq_le {k : ℕ} (B : Finset (Fin k)) {Fv Nv A : Fin k → ℝ} {c₀ CS r x : ℝ} (hA0 : ∀ i, 0 ≤ A i)
    (hA : ∀ i, A i ≤ CS * r ^ 4) (hr8 : r ^ 8 ≤ 256 * x) (hx : 1 ≤ x)
    (hae : ∀ i, |Fv i| ≤ c₀ * A i * Nv i) :
    (∏ i ∈ B, |Fv i|) ^ 2 ≤ ((1 + |c₀| * |CS|) ^ (2 * k) * 256 ^ k * x ^ k) * (∏ i ∈ B, Nv i) ^ 2 := by
  classical
  have hb : B.card ≤ k := by simpa using Finset.card_le_univ B
  set Dn : ℝ := 1 + |c₀| * |CS| with hDn
  have hDn1 : 1 ≤ Dn := by
    have : 0 ≤ |c₀| * |CS| := by positivity
    linarith
  rw [← Finset.prod_pow, ← Finset.prod_pow]
  have h1 : ∀ i ∈ B, |Fv i| ^ 2 ≤ (Dn * r ^ 4) ^ 2 * Nv i ^ 2 := by
    intro i _
    have h2 : |Fv i| ^ 2 ≤ (c₀ * A i * Nv i) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hae i) 2
    have h3 : |c₀ * A i| ≤ Dn * r ^ 4 := by
      rw [abs_mul, abs_of_nonneg (hA0 i)]
      have h4 : A i ≤ |CS| * r ^ 4 :=
        (hA i).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      calc |c₀| * A i ≤ |c₀| * (|CS| * r ^ 4) := by gcongr
        _ = (|c₀| * |CS|) * r ^ 4 := by ring
        _ ≤ Dn * r ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
    have h5 : (c₀ * A i) ^ 2 ≤ (Dn * r ^ 4) ^ 2 := by
      rw [← sq_abs (c₀ * A i)]
      exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    calc |Fv i| ^ 2 ≤ (c₀ * A i * Nv i) ^ 2 := h2
      _ = (c₀ * A i) ^ 2 * Nv i ^ 2 := by ring
      _ ≤ (Dn * r ^ 4) ^ 2 * Nv i ^ 2 := by gcongr
  have h6 := Finset.prod_le_prod (fun i _ => sq_nonneg |Fv i|) h1
  refine h6.trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  have h7 : ((Dn * r ^ 4) ^ 2) ^ B.card ≤ Dn ^ (2 * k) * 256 ^ k * x ^ k := by
    have e : ((Dn * r ^ 4) ^ 2) ^ B.card = Dn ^ (2 * B.card) * (r ^ 8) ^ B.card := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
      ring_nf
    rw [e, mul_assoc, ← mul_pow]
    have h8 : (r ^ 8) ^ B.card ≤ (256 * x) ^ k :=
      (pow_le_pow_left₀ (by positivity) hr8 _).trans (pow_le_pow_right₀ (by linarith) hb)
    have h9 : Dn ^ (2 * B.card) ≤ Dn ^ (2 * k) := pow_le_pow_right₀ hDn1 (by omega)
    gcongr
  have h10 : 0 ≤ ∏ i ∈ B, Nv i ^ 2 := Finset.prod_nonneg fun i _ => sq_nonneg _
  exact mul_le_mul_of_nonneg_right h7 h10
end Reals
section Passing
variable {T : TranslatedLaws} {J : Type} {X : J → T.Family} {P : Measure (TranslateValues J)}
private theorem ae_eq_zero_of_jointLimit (hX : IsJointLimitLaw T X P) {l : ℕ} (a : Fin l → J) (G : (Fin l → ℝ) → ℝ) (hG : Continuous G)
    (hG0 : ∀ w, 0 ≤ G w) (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), G (fun c => X (a c) i ω) = 0) :
    ∀ᵐ v ∂P, G (fun c => v (a c, 0)) = 0 := by
  have := hX.isProbability
  have hb : ∀ w, |min (G w) 1| ≤ 1 := fun w => by
    rw [abs_of_nonneg (le_min (hG0 w) zero_le_one)]
    exact min_le_right _ _
  have hT := hX.tendsto l (fun c => (a c, 0)) (fun w => min (G w) 1) (hG.min continuous_const) ⟨1, hb⟩
  have h0 : Tendsto (fun i => ∫ ω, (fun w => min (G w) 1) (fun c => TranslatedLaws.translate (X ((fun c => (a c, 0)) c).1)
      ((fun c => (a c, 0)) c).2 i ω) ∂(T.μ i)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h] with i hi
    symm
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hi] with ω hω
    have e : (fun c => TranslatedLaws.translate (X ((fun c => (a c, 0)) c).1) ((fun c => (a c, 0)) c).2 i ω) = fun c => X (a c) i ω := rfl
    simp only [e, hω]
    simp
  have e := tendsto_nhds_unique hT h0
  have hmeas : Measurable fun v : TranslateValues J => min (G fun c => v (a c, 0)) 1 :=
    (hG.min continuous_const).measurable.comp (measurable_pi_lambda _ fun c => measurable_pi_apply _)
  have hint : Integrable (fun v : TranslateValues J => min (G fun c => v (a c, 0)) 1) P :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (ae_of_all _ fun v => by simpa [Real.norm_eq_abs] using hb _)
  have h2 := (integral_eq_zero_iff_of_nonneg (fun v => le_min (hG0 _) zero_le_one) hint).1 e
  filter_upwards [h2] with v hv
  have hv' : min (G fun c => v (a c, 0)) 1 = 0 := hv
  rcases min_choice (G fun c => v (a c, 0)) 1 with h3 | h3
  · rw [h3] at hv'
    exact hv'
  · rw [h3] at hv'
    exact absurd hv' one_ne_zero
abbrev _root_.YangMills.SharedProofs.p3582 := @ae_eq_zero_of_jointLimit
private theorem ae_le_of_jointLimit (hX : IsJointLimitLaw T X P) {l : ℕ} (a : Fin l → J) (A C : (Fin l → ℝ) → ℝ) (hA : Continuous A) (hC : Continuous C)
    (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), A (fun c => X (a c) i ω) ≤ C (fun c => X (a c) i ω)) :
    ∀ᵐ v ∂P, A (fun c => v (a c, 0)) ≤ C (fun c => v (a c, 0)) := by
  have h1 := ae_eq_zero_of_jointLimit hX a (fun w => max (A w - C w) 0) ((hA.sub hC).max continuous_const) (fun w => le_max_right _ _) (by
    filter_upwards [h] with i hi
    filter_upwards [hi] with ω hω
    exact max_eq_right (by linarith))
  filter_upwards [h1] with v hv
  have := le_max_left (A (fun c => v (a c, 0)) - C (fun c => v (a c, 0))) 0
  rw [hv] at this
  linarith
abbrev _root_.YangMills.SharedProofs.p29837 := @ae_le_of_jointLimit
private theorem ae_le_sum_of_jointLimit (hX : IsJointLimitLaw T X P) {α : Type} (I : Finset α) (a : α → J) (j₀ j₁ : J) (c₀ c₁ c₂ : ℝ)
    (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), X j₀ i ω ≤ c₀ + c₁ * ∑ e ∈ I, X (a e) i ω + c₂ * X j₁ i ω) :
    ∀ᵐ v ∂P, v (j₀, 0) ≤ c₀ + c₁ * ∑ e ∈ I, v (a e, 0) + c₂ * v (j₁, 0) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, I.card = n := ⟨_, rfl⟩
  let q : I ≃ Fin n := I.equivFinOfCardEq hn
  have hs : ∀ f : α → ℝ, ∑ c : Fin n, f (q.symm c) = ∑ e ∈ I, f e := fun f => by
    rw [Equiv.sum_comp q.symm (fun e : I => f e), Finset.sum_coe_sort I f]
  let a' : Fin (n + 2) → J := Fin.cons j₀ (Fin.cons j₁ fun c => a (q.symm c))
  have a0 : a' 0 = j₀ := rfl
  have a1 : a' 1 = j₁ := rfl
  have aS : ∀ c : Fin n, a' c.succ.succ = a (q.symm c) := fun c => rfl
  have h1 := ae_le_of_jointLimit hX a' (fun w => w 0) (fun w => c₀ + c₁ * ∑ c : Fin n, w c.succ.succ + c₂ * w 1)
    (continuous_apply 0) (by fun_prop) (by
      filter_upwards [h] with i hi
      filter_upwards [hi] with ω hω
      show X (a' 0) i ω ≤ c₀ + c₁ * ∑ c : Fin n, X (a' c.succ.succ) i ω + c₂ * X (a' 1) i ω
      simp only [a0, a1, aS]
      rw [hs fun e => X (a e) i ω]
      exact hω)
  filter_upwards [h1] with v hv
  have hv' : v (a' 0, 0) ≤ c₀ + c₁ * ∑ c : Fin n, v (a' c.succ.succ, 0) + c₂ * v (a' 1, 0) := hv
  simp only [a0, a1, aS] at hv'
  rw [hs fun e => v (a e, 0)] at hv'
  exact hv'
private theorem condMean_le_of_jointLimit (hX : IsJointLimitLaw T X P) (hint : ∀ j, Integrable (evalAtZero j) P) {α : Type} (I : Finset α) (a : α → J)
    (j₀ j₁ : J) {c₀ c₁ c₂ b b₁ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), X j₀ i ω ≤ c₀ + c₁ * ∑ e ∈ I, X (a e) i ω + c₂ * X j₁ i ω)
    (hb : ∀ e ∈ I, ∀ᵐ v ∂P, invariantCondExp P (evalAtZero (a e)) v ≤ b)
    (hb₁ : ∀ᵐ v ∂P, invariantCondExp P (evalAtZero j₁) v ≤ b₁) :
    ∀ᵐ v ∂P, invariantCondExp P (evalAtZero j₀) v ≤ c₀ + c₁ * ((I.card : ℝ) * b) + c₂ * b₁ := by
  classical
  have := hX.isProbability
  have hm : shiftInvariantSigma J ≤ MeasurableSpace.pi := inf_le_right
  have rel := ae_le_sum_of_jointLimit hX I a j₀ j₁ c₀ c₁ c₂ h
  have hsumI : Integrable (fun v : TranslateValues J => ∑ e ∈ I, evalAtZero (a e) v) P := integrable_finsetSum _ fun e _ => hint (a e)
  have hS : Integrable (fun v : TranslateValues J => c₁ * ∑ e ∈ I, evalAtZero (a e) v) P := hsumI.const_mul _
  have hT : Integrable (fun v : TranslateValues J => c₂ * evalAtZero j₁ v) P := (hint j₁).const_mul _
  have hC : Integrable (fun _ : TranslateValues J => c₀) P := integrable_const _
  have hCS : Integrable (fun v : TranslateValues J => c₀ + c₁ * ∑ e ∈ I, evalAtZero (a e) v) P := hC.add hS
  have hR : Integrable (fun v : TranslateValues J => c₀ + c₁ * ∑ e ∈ I, evalAtZero (a e) v + c₂ * evalAtZero j₁ v) P := hCS.add hT
  have hmono : P[evalAtZero j₀|shiftInvariantSigma J] ≤ᵐ[P]
      P[fun v : TranslateValues J => c₀ + c₁ * ∑ e ∈ I, evalAtZero (a e) v + c₂ * evalAtZero j₁ v|shiftInvariantSigma J] :=
    condExp_mono (hint j₀) hR rel
  have e1 : P[fun v : TranslateValues J => c₀ + c₁ * ∑ e ∈ I, evalAtZero (a e) v + c₂ * evalAtZero j₁ v|shiftInvariantSigma J] =ᵐ[P]
      (P[fun v : TranslateValues J => c₀ + c₁ * ∑ e ∈ I, evalAtZero (a e) v|shiftInvariantSigma J]) +
        P[fun v : TranslateValues J => c₂ * evalAtZero j₁ v|shiftInvariantSigma J] := condExp_add hCS hT _
  have e2 : P[fun v : TranslateValues J => c₀ + c₁ * ∑ e ∈ I, evalAtZero (a e) v|shiftInvariantSigma J] =ᵐ[P]
      (P[fun _ : TranslateValues J => c₀|shiftInvariantSigma J]) + P[fun v : TranslateValues J => c₁ * ∑ e ∈ I, evalAtZero (a e) v|shiftInvariantSigma J] :=
    condExp_add hC hS _
  have e3 : P[fun _ : TranslateValues J => c₀|shiftInvariantSigma J] = fun _ => c₀ := condExp_const hm c₀
  have e4 : P[fun v : TranslateValues J => c₁ * ∑ e ∈ I, evalAtZero (a e) v|shiftInvariantSigma J] =ᵐ[P]
      c₁ • P[fun v : TranslateValues J => ∑ e ∈ I, evalAtZero (a e) v|shiftInvariantSigma J] := condExp_smul c₁ _ _
  have e5 : P[fun v : TranslateValues J => c₂ * evalAtZero j₁ v|shiftInvariantSigma J] =ᵐ[P] c₂ • P[evalAtZero j₁|shiftInvariantSigma J] :=
    condExp_smul c₂ _ _
  have e6 : P[fun v : TranslateValues J => ∑ e ∈ I, evalAtZero (a e) v|shiftInvariantSigma J] =ᵐ[P]
      fun v => ∑ e ∈ I, (P[evalAtZero (a e)|shiftInvariantSigma J]) v := by
    have h6 := condExp_finsetSum (μ := P) (s := I) (f := fun e => evalAtZero (a e)) (fun e _ => hint (a e)) (shiftInvariantSigma J)
    have e7 : (∑ e ∈ I, evalAtZero (a e)) = fun v : TranslateValues J => ∑ e ∈ I, evalAtZero (a e) v := by
      funext v
      rw [Finset.sum_apply]
    rw [e7] at h6
    filter_upwards [h6] with v hv
    rw [hv, Finset.sum_apply]
  have hall : ∀ᵐ v ∂P, ∀ e ∈ I, invariantCondExp P (evalAtZero (a e)) v ≤ b := (Filter.eventually_all_finset I).2 hb
  filter_upwards [hmono, e1, e2, e4, e5, e6, hall, hb₁] with v m1 f1 f2 f4 f5 f6 g1 g2
  have s1 : ∑ e ∈ I, invariantCondExp P (evalAtZero (a e)) v ≤ (I.card : ℝ) * b := by
    have := Finset.sum_le_card_nsmul I (fun e => invariantCondExp P (evalAtZero (a e)) v) b g1
    rwa [nsmul_eq_mul] at this
  have s2 : invariantCondExp P (evalAtZero j₀) v = (P[evalAtZero j₀|shiftInvariantSigma J]) v := rfl
  have s3 : (P[evalAtZero j₁|shiftInvariantSigma J]) v ≤ b₁ := g2
  have s4 : ∑ e ∈ I, (P[evalAtZero (a e)|shiftInvariantSigma J]) v ≤ (I.card : ℝ) * b := s1
  rw [s2]
  refine m1.trans ?_
  rw [f1, Pi.add_apply, f2, Pi.add_apply, e3, f4, f5, Pi.smul_apply, Pi.smul_apply, f6, smul_eq_mul, smul_eq_mul]
  have := mul_le_mul_of_nonneg_left s4 hc₁
  have := mul_le_mul_of_nonneg_left s3 hc₂
  linarith
abbrev _root_.YangMills.SharedProofs.p37250 := @condMean_le_of_jointLimit
end Passing
section Offsets
private def plaquetteOffsets (R : ℕ) : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4) :=
  Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) (R : ℤ)) ×ˢ (Finset.univ.filter fun e : Fin 4 × Fin 4 => e.1 < e.2)
private theorem plaquetteOffsets_card (R : ℕ) : (plaquetteOffsets R).card ≤ 16 * (2 * R + 1) ^ 4 := by
  classical
  unfold plaquetteOffsets
  rw [Finset.card_product, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : (Finset.univ.filter fun e : Fin 4 × Fin 4 => e.1 < e.2).card ≤ 16 := by
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  have h2 : ((R : ℤ) + 1 - -(R : ℤ)).toNat = 2 * R + 1 := by omega
  rw [h2, mul_comm]
  exact Nat.mul_le_mul_right _ h1
variable {m : ℕ} [NeZero m]
open Classical in
private def plaquettesNear (o : TorusSite m) (R : ℝ) : Finset (OrientedPlaquette m) :=
  Finset.univ.filter fun p => (TorusFields.supDist p.1.1 o : ℝ) ≤ R
omit [NeZero m] in
private theorem exists_offset_of_near (o : TorusSite m) (p : OrientedPlaquette m) (R : ℕ) (h : (TorusFields.supDist p.1.1 o : ℝ) ≤ R) :
    ∃ e ∈ plaquetteOffsets R, p.1.1 = o + siteOfInt e.1 ∧ p.1.2.1 = e.2.1 ∧ p.1.2.2 = e.2.2 := by
  classical
  have h' : TorusFields.supDist p.1.1 o ≤ R := by exact_mod_cast h
  refine ⟨(fun i => (p.1.1 i - o i).valMinAbs, p.1.2.1, p.1.2.2), ?_, ?_, rfl, rfl⟩
  · refine Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, Finset.mem_filter.2 ⟨Finset.mem_univ _, p.2⟩⟩
    have h1 : ((p.1.1 i - o i).valMinAbs).natAbs ≤ R :=
      (Finset.le_sup (f := fun i => ((p.1.1 i - o i).valMinAbs).natAbs) (Finset.mem_univ i)).trans h'
    rw [Finset.mem_Icc]
    show -(R : ℤ) ≤ (p.1.1 i - o i).valMinAbs ∧ (p.1.1 i - o i).valMinAbs ≤ (R : ℤ)
    omega
  · funext i
    show p.1.1 i = o i + ((p.1.1 i - o i).valMinAbs : ZMod m)
    rw [ZMod.coe_valMinAbs]
    ring
private theorem boxCurvature_cases (o : TorusSite m) (R : ℝ) (W : TorusField m) :
    boxCurvature o R W = 0 ∨
      ∃ p ∈ plaquettesNear o R, boxCurvature o R W = curvature W p.1.1 p.1.2.1 p.1.2.2 := by
  classical
  unfold boxCurvature
  by_cases hE : IsEmpty {p : TorusPlaquette m // PlaquetteInBox o R p}
  · left
    exact Real.iSup_of_isEmpty _
  · rw [not_isEmpty_iff] at hE
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite
      (f := fun p : {p : TorusPlaquette m // PlaquetteInBox o R p} => curvature W p.1.1 p.1.2.1 p.1.2.2)
    right
    refine ⟨⟨i.1, i.2.1⟩, ?_, hi.symm⟩
    have h0 := i.2.2 i.1.1 (by simp [plaquetteVertices])
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.mp h0).2⟩
omit [NeZero m] in
private theorem curvature_nonneg' (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) : 0 ≤ curvature W x μ ν := norm_nonneg _
private theorem boxCurvature_nonneg (o : TorusSite m) (R : ℝ) (W : TorusField m) : 0 ≤ boxCurvature o R W :=
  Real.iSup_nonneg fun _ => curvature_nonneg' _ _ _ _
omit [NeZero m] in
private theorem curvature_le_two (W : TorusField m) (z : TorusSite m) (μ ν : Fin 4) : curvature W z μ ν ≤ 2 := by apply _root_.YangMills.SharedProofs.p28884 <;> assumption
omit [NeZero m] in
private theorem curvature_pow_le (W : TorusField m) (z : TorusSite m) (μ ν : Fin 4) (q : ℕ) : curvature W z μ ν ^ (2 * q) ≤ 4 ^ q := by
  have h : (0 : ℝ) ≤ curvature W z μ ν := norm_nonneg _
  calc curvature W z μ ν ^ (2 * q) ≤ 2 ^ (2 * q) := pow_le_pow_left₀ h (curvature_le_two W z μ ν) _
    _ = 4 ^ q := by rw [pow_mul]; norm_num
omit [NeZero m] in
private theorem measurable_curvature_comp {Ω₀ : Type} [MeasurableSpace Ω₀] {V : Ω₀ → TorusField m} (hV : Measurable V) (x : TorusSite m)
    (μ ν : Fin 4) : Measurable fun a => curvature (V a) x μ ν := by
  have hc : Measurable fun g : BlockAverages.UnitQuaternion => ‖((g : BlockAverages.UnitQuaternion) : Quaternion ℝ) - 1‖ :=
    ((continuous_subtype_val.sub continuous_const).norm).measurable
  have hp : Measurable fun a => holonomy (V a) x μ ν := by
    have h : ∀ (y : TorusSite m) (i : Fin 4), Measurable fun a => V a y i :=
      fun y i => (measurable_pi_apply i).comp ((measurable_pi_apply y).comp hV)
    unfold holonomy
    exact (((h _ _).mul (h _ _)).mul (h _ _).inv).mul (h _ _).inv
  exact hc.comp hp
abbrev _root_.YangMills.SharedProofs.p85954 := @measurable_curvature_comp
end Offsets
section Sums
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private theorem measurable_of_sigma_slices {X A : Type} [MeasurableSpace X] [Countable A] {B : A → Type}
    [∀ a, MeasurableSpace (B a)] {Z : Type} [MeasurableSpace Z] {f : X × Sigma B → Z}
    (h : ∀ a, Measurable fun p : X × B a => f (p.1, ⟨a, p.2⟩)) : Measurable f := by apply _root_.YangMills.SharedProofs.p5842 <;> assumption
private theorem one_le_list_prod {α : Type} (f : α → ℝ) (hf : ∀ a, 1 ≤ f a) (J : List α) : 1 ≤ (J.map f).prod := by
  induction J with
  | nil => simp
  | cons a J ih =>
    rw [List.map_cons, List.prod_cons]
    have := hf a
    nlinarith
abbrev _root_.YangMills.SharedProofs.p58552 := @one_le_list_prod
private theorem prod_flatten_replicate {α : Type} (f : α → ℝ) (J : List α) (q : ℕ) :
    (((List.replicate q J).flatten).map f).prod = ((J.map f).prod) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.replicate_succ, List.flatten_cons, List.map_append, List.prod_append, ih, pow_succ]
    ring
abbrev _root_.YangMills.SharedProofs.p31647 := @prod_flatten_replicate
private theorem length_flatten_replicate {α : Type} (J : List α) (q : ℕ) : ((List.replicate q J).flatten).length = q * J.length := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]
    ring
end Sums
section Point
variable {Λ : MomentParameters}
private theorem markedSampleLaw_cast (T : StageTower Λ.stepParams) (β : ℝ) {K K' : ℕ} (h : K = K') (n : ℕ) [NeZero n] :
    Measurable (fun w : MarkedSample Λ.stepParams K n => (h ▸ w : MarkedSample Λ.stepParams K' n)) ∧
      (markedSampleLaw T β K n).map (fun w : MarkedSample Λ.stepParams K n => (h ▸ w : MarkedSample Λ.stepParams K' n)) =
        markedSampleLaw T β K' n := by apply _root_.YangMills.SharedProofs.p48114 <;> assumption
private structure SampleFacts (S : MomentPoint Λ) (CS Cs : ℝ) : Prop where
  scale_ge : (8 : ℝ) ^ 100 ≤ S.scaleCoupling
  window : S.lastSeparated + 2 * S.logIndex + 3 ≤ S.data.windowLevel
  measurable_state : ∀ (u n : ℕ) [NeZero n], Measurable (stageState S.tower u n)
  sample_below : ∀ (s d n : ℕ) [NeZero n], Measurable (ResponseInTheExpansion.sampleBelow Λ.stepParams s d n) ∧
    Measure.map (ResponseInTheExpansion.sampleBelow Λ.stepParams s d n) (markedSampleLaw S.tower S.β (s + d) n) =
      markedSampleLaw S.tower S.β s (fineSide Λ.stepParams.side d n)
  held : ∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)), ∀ i : Fin Λ.k,
    |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ≤
      Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) *
        S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)
  card_le : ∀ i : Fin Λ.k, ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) ≤ CS * (S.range : ℝ) ^ 4
  scores : ∀ (p : ℕ), 1 ≤ p → ∀ J : List (Fin Λ.k), J.length = p →
    ∫⁻ w, ENNReal.ofReal (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤
      ENNReal.ofReal (Cs ^ p * (p.factorial : ℝ) ^ 6)
namespace MomentPoint
variable (S : MomentPoint Λ) {CS Cs : ℝ}
private theorem sideAtLevel_eq (u : ℕ) : S.sideAtLevel u = S.levelSide u := by apply _root_.YangMills.DeltaSharedProofs.p7007 <;> assumption
abbrev _root_.YangMills.SharedProofs.p7138 := @sideAtLevel_eq
private theorem sampleAtLevel_map (h : SampleFacts S CS Cs) (u : ℕ) (hu : u ≤ S.data.windowLevel) :
    Measurable (S.sampleAtLevel u hu) ∧
      (S.law S.data.windowLevel (S.data.period Λ.stepParams.side)).map (S.sampleAtLevel u hu) = S.law u (S.sideAtLevel u) := by
  have hc := markedSampleLaw_cast S.tower S.β (Nat.add_sub_of_le hu).symm (S.data.period Λ.stepParams.side)
  obtain ⟨m1, e1⟩ := h.sample_below u (S.data.windowLevel - u) (S.data.period Λ.stepParams.side)
  refine ⟨m1.comp hc.1, ?_⟩
  have e2 := Measure.map_map (μ := markedSampleLaw S.tower S.β S.data.windowLevel (S.data.period Λ.stepParams.side)) m1 hc.1
  rw [hc.2, e1] at e2
  exact e2.symm
private theorem ae_of_level (h : SampleFacts S CS Cs) (u : ℕ) (hu : u ≤ S.data.windowLevel)
    {p : MarkedSample Λ.stepParams u (S.sideAtLevel u) → Prop}
    (hp : ∀ᵐ x ∂(S.law u (S.sideAtLevel u)), p x) :
    ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)), p (S.sampleAtLevel u hu w) := by
  obtain ⟨m1, e1⟩ := S.sampleAtLevel_map h u hu
  rw [← e1] at hp
  exact ae_of_ae_map m1.aemeasurable hp
private theorem measurable_stateAtLevel (h : SampleFacts S CS Cs) (u : ℕ) (hu : u ≤ S.data.windowLevel) :
    Measurable (S.stateAtLevel u hu) :=
  (h.measurable_state u (S.sideAtLevel u)).comp (S.sampleAtLevel_map h u hu).1
private theorem measurable_fieldAtLevel (h : SampleFacts S CS Cs) (u : ℕ) (hu : u ≤ S.data.windowLevel) :
    Measurable fun w => (S.stateAtLevel u hu w).1 :=
  measurable_fst.comp (S.measurable_stateAtLevel h u hu)
private theorem measurableSet_disjoint (h : SampleFacts S CS Cs) (u : ℕ) (hu : u ≤ S.data.windowLevel)
    (B : Finset (TorusSite (S.sideAtLevel u))) :
    MeasurableSet {w | Disjoint (S.stateAtLevel u hu w).2.1 B} := by
  have e : {w | Disjoint (S.stateAtLevel u hu w).2.1 B} =
      ⋃ a ∈ {a : Finset (TorusSite (S.sideAtLevel u)) | Disjoint a B}, {w | (S.stateAtLevel u hu w).2.1 = a} := by
    ext w
    simp
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ =>
    (measurable_snd.comp (S.measurable_stateAtLevel h u hu)) (measurableSet_sigma_fst_eq a)
private theorem measurableSet_isClearFrom (h : SampleFacts S CS Cs) (u : ℕ) : MeasurableSet {w | S.IsClearFrom u w} := by
  have e : {w | S.IsClearFrom u w} = ⋂ (u' : ℕ), ⋂ (hK : u' ≤ S.data.windowLevel), ⋂ (_ : u ≤ u'),
      ⋂ (_ : u' ≤ S.lastSeparated + 2 * S.logIndex + 3),
      {w | Disjoint (S.stateAtLevel u' hK w).2.1
        (ResponseInTheExpansion.supBall (S.originSite u' (S.sideAtLevel u')) ((S.range : ℝ) ^ 3))} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rfl
  rw [e]
  exact MeasurableSet.iInter fun u' => MeasurableSet.iInter fun hK => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    S.measurableSet_disjoint h u' hK _
private theorem measurable_notClearIndicator (h : SampleFacts S CS Cs) (u : ℕ) : Measurable (notClearIndicator u S) := by
  classical
  exact Measurable.ite (S.measurableSet_isClearFrom h u) measurable_const measurable_const
private theorem notClearIndicator_nonneg (u : ℕ) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    0 ≤ notClearIndicator u S w := by
  classical
  unfold notClearIndicator
  split_ifs <;> norm_num
private theorem abs_notClearIndicator_le (u : ℕ) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    |notClearIndicator u S w| ≤ 1 := by
  classical
  unfold notClearIndicator
  split_ifs <;> norm_num
private theorem clearCurvaturePower_of_clear {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (μ ν : Fin 4) (q : ℕ)
    {w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)}
    (hc : S.IsClearFrom u w) :
    clearCurvaturePower u z μ ν q S w = curvature (S.stateAtLevel u hu w).1 (S.siteAt u z) μ ν ^ (2 * q) := by
  classical
  unfold clearCurvaturePower
  rw [dif_pos hu, if_pos hc]
private theorem clearCurvaturePower_nonneg (u : ℕ) (z : Fin 4 → ℤ) (μ ν : Fin 4) (q : ℕ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    0 ≤ clearCurvaturePower u z μ ν q S w := by
  classical
  unfold clearCurvaturePower
  split_ifs
  · exact pow_nonneg (curvature_nonneg' _ _ _ _) _
  · exact le_rfl
  · exact le_rfl
private theorem abs_clearCurvaturePower_le (u : ℕ) (z : Fin 4 → ℤ) (μ ν : Fin 4) (q : ℕ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    |clearCurvaturePower u z μ ν q S w| ≤ 4 ^ q := by
  classical
  rw [abs_of_nonneg (S.clearCurvaturePower_nonneg u z μ ν q w)]
  unfold clearCurvaturePower
  split_ifs
  · exact curvature_pow_le _ _ _ _ _
  · positivity
  · positivity
private theorem measurable_clearCurvaturePower (h : SampleFacts S CS Cs) (u : ℕ) (z : Fin 4 → ℤ) (μ ν : Fin 4) (q : ℕ) :
    Measurable (clearCurvaturePower u z μ ν q S) := by
  classical
  by_cases hu : u ≤ S.data.windowLevel
  · have e : clearCurvaturePower u z μ ν q S =
        fun w => if S.IsClearFrom u w then curvature (S.stateAtLevel u hu w).1 (S.siteAt u z) μ ν ^ (2 * q) else 0 := by
      funext w
      unfold clearCurvaturePower
      rw [dif_pos hu]
    rw [e]
    exact Measurable.ite (S.measurableSet_isClearFrom h u)
      ((measurable_curvature_comp (S.measurable_fieldAtLevel h u hu) _ _ _).pow_const _) measurable_const
  · have e : clearCurvaturePower u z μ ν q S = fun _ => 0 := by
      funext w
      unfold clearCurvaturePower
      rw [dif_neg hu]
    rw [e]
    exact measurable_const
open Classical in
private theorem notGoodIndicator_of_le {u : ℕ} (hu : u ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    notGoodIndicator u S w =
      if S.IsGoodConfig u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 (S.stateAtLevel u hu w).2.1 then 0 else 1 := dif_pos hu
open Classical in
private theorem goodCurvaturePower_of_le {u : ℕ} (k : ℕ) (hu : u ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    goodCurvaturePower u k S w = if S.IsGoodConfig u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 (S.stateAtLevel u hu w).2.1 then
      (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature u (S.sideAtLevel u) (S.stateAtLevel u hu w).1) ^ k else 0 := dif_pos hu
private theorem levelObservable_of_not_le {u : ℕ}
    {f : (S : MomentPoint Λ) → StageState S.tower u (S.sideAtLevel u) → ℝ} (hu : ¬ u ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : levelObservable u f S w = 0 := dif_neg hu
private theorem localCurvature_nonneg (u n : ℕ) [NeZero n] (W : TorusField n) : 0 ≤ S.localCurvature u n W :=
  boxCurvature_nonneg _ _ _
private theorem measurable_localCurvature (h : SampleFacts S CS Cs) (u : ℕ) (hu : u ≤ S.data.windowLevel) :
    Measurable fun w => S.localCurvature u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 :=
  Measurable.iSup fun _ => measurable_curvature_comp (S.measurable_fieldAtLevel h u hu) _ _ _
private theorem measurableSet_isGoodConfig (h : SampleFacts S CS Cs) (u : ℕ) (hu : u ≤ S.data.windowLevel) :
    MeasurableSet {w | S.IsGoodConfig u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 (S.stateAtLevel u hu w).2.1} := by
  have e : {w | S.IsGoodConfig u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 (S.stateAtLevel u hu w).2.1} =
      {w | Disjoint (S.stateAtLevel u hu w).2.1 (ResponseInTheExpansion.supBall (S.originSite u (S.sideAtLevel u)) (8 * S.rangeSq))} ∩
        {w | S.localCurvature u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 ≤ S.scaleCoupling ^ (-(1 / 4) : ℝ)} := by
    ext w
    exact ⟨fun h => ⟨h.disjoint_lumps, h.curvature_le⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [e]
  exact (S.measurableSet_disjoint h u hu _).inter (measurableSet_le (S.measurable_localCurvature h u hu) measurable_const)
private theorem measurable_notGoodIndicator (h : SampleFacts S CS Cs) (u : ℕ) : Measurable (notGoodIndicator u S) := by
  classical
  by_cases hu : u ≤ S.data.windowLevel
  · have e : notGoodIndicator u S = fun w =>
        if S.IsGoodConfig u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 (S.stateAtLevel u hu w).2.1 then 0 else 1 := by
      funext w
      rw [S.notGoodIndicator_of_le hu]
    rw [e]
    exact Measurable.ite (S.measurableSet_isGoodConfig h u hu) measurable_const measurable_const
  · have e : notGoodIndicator u S = fun _ => 0 := by
      funext w
      exact S.levelObservable_of_not_le hu w
    rw [e]
    exact measurable_const
private theorem notGoodIndicator_nonneg (u : ℕ) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    0 ≤ notGoodIndicator u S w := by
  classical
  by_cases hu : u ≤ S.data.windowLevel
  · rw [S.notGoodIndicator_of_le hu]
    split_ifs <;> norm_num
  · exact (S.levelObservable_of_not_le hu w).ge
abbrev _root_.YangMills.SharedProofs.p125034 := @notGoodIndicator_nonneg
private theorem abs_notGoodIndicator_le (u : ℕ) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    |notGoodIndicator u S w| ≤ 1 := by
  classical
  by_cases hu : u ≤ S.data.windowLevel
  · rw [S.notGoodIndicator_of_le hu]
    split_ifs <;> norm_num
  · have e : notGoodIndicator u S w = 0 := S.levelObservable_of_not_le hu w
    rw [e]
    norm_num
abbrev _root_.YangMills.SharedProofs.p4667 := @abs_notGoodIndicator_le
private theorem goodCurvaturePower_nonneg (hx : 0 ≤ S.scaleCoupling) (u k : ℕ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : 0 ≤ goodCurvaturePower u k S w := by
  classical
  by_cases hu : u ≤ S.data.windowLevel
  · rw [S.goodCurvaturePower_of_le k hu]
    split_ifs
    · have := S.localCurvature_nonneg u (S.sideAtLevel u) (S.stateAtLevel u hu w).1
      positivity
    · exact le_rfl
  · exact (S.levelObservable_of_not_le hu w).ge
private theorem localCurvature_pow_le_sum {u : ℕ} (hu : u ≤ S.data.windowLevel)
    {w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)} (hc : S.IsClearFrom u w) {Q : ℕ} (hQ : 1 ≤ Q) :
    S.localCurvature u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 ^ (2 * Q) ≤
      ∑ e ∈ plaquetteOffsets (2 * S.rangeSq), clearCurvaturePower u e.1 e.2.1 e.2.2 Q S w := by
  have hnn : ∀ e ∈ plaquetteOffsets (2 * S.rangeSq), 0 ≤ clearCurvaturePower u e.1 e.2.1 e.2.2 Q S w :=
    fun e _ => S.clearCurvaturePower_nonneg _ _ _ _ _ _
  rcases boxCurvature_cases (S.originSite u (S.sideAtLevel u)) (2 * (S.rangeSq : ℝ)) (S.stateAtLevel u hu w).1 with h0 | ⟨p, hp, h0⟩
  · have e0 : S.localCurvature u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 = 0 := h0
    rw [e0, zero_pow (by omega)]
    exact Finset.sum_nonneg hnn
  · have e0 : S.localCurvature u (S.sideAtLevel u) (S.stateAtLevel u hu w).1 =
        curvature (S.stateAtLevel u hu w).1 p.1.1 p.1.2.1 p.1.2.2 := h0
    have hp' : (TorusFields.supDist p.1.1 (S.originSite u (S.sideAtLevel u)) : ℝ) ≤ ((2 * S.rangeSq : ℕ) : ℝ) := by
      push_cast
      exact (Finset.mem_filter.mp hp).2
    obtain ⟨e, he, h1, h2, h3⟩ := exists_offset_of_near _ p (2 * S.rangeSq) hp'
    have h4 := Finset.single_le_sum hnn he
    rw [S.clearCurvaturePower_of_clear hu _ _ _ _ hc] at h4
    rw [e0, h1, h2, h3]
    exact h4
private theorem notGoodIndicator_le {x : ℝ} (hx : S.scaleCoupling = x) (hx0 : 0 < x) {R : ℕ} (hR : R = 2 * S.rangeSq) {u : ℕ}
    (hu : u ≤ S.lastSeparated + 2 * S.logIndex + 3)
    (h8 : 8 * (S.rangeSq : ℝ) ≤ (S.range : ℝ) ^ 3) {Q : ℕ} (hQ : 1 ≤ Q)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    notGoodIndicator u S w ≤ 0 + (1 / (x ^ (-(1 / 4) : ℝ)) ^ (2 * Q)) * ∑ e ∈ plaquetteOffsets R, clearCurvaturePower u e.1 e.2.1 e.2.2 Q S w +
      1 * notClearIndicator u S w := by
  classical
  subst hR hx
  have ha : 0 < S.scaleCoupling ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hS0 : 0 ≤ ∑ e ∈ plaquetteOffsets (2 * S.rangeSq), clearCurvaturePower u e.1 e.2.1 e.2.2 Q S w :=
    Finset.sum_nonneg fun e _ => S.clearCurvaturePower_nonneg _ _ _ _ _ _
  have hc1 : 0 ≤ 1 / (S.scaleCoupling ^ (-(1 / 4) : ℝ)) ^ (2 * Q) := by positivity
  have hn0 := S.notClearIndicator_nonneg u w
  have hpos : 0 ≤ (1 / (S.scaleCoupling ^ (-(1 / 4) : ℝ)) ^ (2 * Q)) *
      ∑ e ∈ plaquetteOffsets (2 * S.rangeSq), clearCurvaturePower u e.1 e.2.1 e.2.2 Q S w :=
    mul_nonneg hc1 hS0
  by_cases hK : u ≤ S.data.windowLevel
  · rw [S.notGoodIndicator_of_le hK]
    by_cases hC : S.IsClearFrom u w
    · by_cases hv : S.localCurvature u (S.sideAtLevel u) (S.stateAtLevel u hK w).1 ≤ S.scaleCoupling ^ (-(1 / 4) : ℝ)
      · have hg : S.IsGoodConfig u (S.sideAtLevel u) (S.stateAtLevel u hK w).1 (S.stateAtLevel u hK w).2.1 := by
          refine ⟨(hC u hK le_rfl hu).mono_right fun z hz => ?_, hv⟩
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.trans h8⟩
        rw [if_pos hg]
        linarith
      · have h1 := S.localCurvature_pow_le_sum hK hC hQ
        have h2 : (S.scaleCoupling ^ (-(1 / 4) : ℝ)) ^ (2 * Q) ≤
            ∑ e ∈ plaquetteOffsets (2 * S.rangeSq), clearCurvaturePower u e.1 e.2.1 e.2.2 Q S w :=
          (pow_le_pow_left₀ ha.le (not_le.mp hv).le _).trans h1
        have h3 : 1 ≤ (1 / (S.scaleCoupling ^ (-(1 / 4) : ℝ)) ^ (2 * Q)) *
            ∑ e ∈ plaquetteOffsets (2 * S.rangeSq), clearCurvaturePower u e.1 e.2.1 e.2.2 Q S w := by
          rw [one_div, inv_mul_eq_div, one_le_div (by positivity)]
          exact h2
        split_ifs <;> linarith
    · have hn : notClearIndicator u S w = 1 := if_neg hC
      rw [hn]
      split_ifs <;> linarith
  · have e : notGoodIndicator u S w = 0 := S.levelObservable_of_not_le hK w
    rw [e]
    linarith
private theorem goodCurvaturePower_le {x T : ℝ} (hx : S.scaleCoupling = x) (hx1 : 1 ≤ x) {R : ℕ} (hR : R = 2 * S.rangeSq)
    {u k κ Q : ℕ} (hT : 1 ≤ T) (hk : k ≤ κ) (hκ : κ ≤ 2 * Q) (hQ : 1 ≤ Q)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    goodCurvaturePower u k S w ≤ (2 * T) ^ κ +
      (2 ^ κ * T ^ κ / T ^ (2 * Q) * x ^ Q) * ∑ e ∈ plaquetteOffsets R, clearCurvaturePower u e.1 e.2.1 e.2.2 Q S w +
      (1 + x ^ ((1 : ℝ) / 4)) ^ κ * notClearIndicator u S w := by
  classical
  subst hR hx
  have hx0 : 0 < S.scaleCoupling := by linarith
  have hS0 : 0 ≤ ∑ e ∈ plaquetteOffsets (2 * S.rangeSq), clearCurvaturePower u e.1 e.2.1 e.2.2 Q S w :=
    Finset.sum_nonneg fun e _ => S.clearCurvaturePower_nonneg _ _ _ _ _ _
  have hB0 : 0 ≤ 2 ^ κ * T ^ κ / T ^ (2 * Q) * S.scaleCoupling ^ Q := by positivity
  have hn0 := S.notClearIndicator_nonneg u w
  have hA0 : 0 ≤ (2 * T) ^ κ := by positivity
  have hD0 : 0 ≤ (1 + S.scaleCoupling ^ ((1 : ℝ) / 4)) ^ κ := by positivity
  have hBS := mul_nonneg hB0 hS0
  have hDn := mul_nonneg hD0 hn0
  by_cases hK : u ≤ S.data.windowLevel
  · rw [S.goodCurvaturePower_of_le k hK]
    split_ifs with hg
    · have hv0 := S.localCurvature_nonneg u (S.sideAtLevel u) (S.stateAtLevel u hK w).1
      by_cases hC : S.IsClearFrom u w
      · have hr := one_add_pow_le hx1 hv0 hT hk hκ (S.localCurvature_pow_le_sum hK hC hQ)
        linarith
      · have hn : notClearIndicator u S w = 1 := if_neg hC
        have hs : S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature u (S.sideAtLevel u) (S.stateAtLevel u hK w).1 ≤
            S.scaleCoupling ^ ((1 : ℝ) / 4) := by
          have h1 := mul_le_mul_of_nonneg_left hg.curvature_le (Real.rpow_nonneg hx0.le ((1 : ℝ) / 2))
          refine h1.trans (le_of_eq ?_)
          rw [← Real.rpow_add hx0]
          norm_num
        have hs0 : 0 ≤ S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature u (S.sideAtLevel u) (S.stateAtLevel u hK w).1 :=
          mul_nonneg (by positivity) hv0
        have h2 : (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature u (S.sideAtLevel u) (S.stateAtLevel u hK w).1) ^ k ≤
            (1 + S.scaleCoupling ^ ((1 : ℝ) / 4)) ^ κ :=
          (pow_le_pow_right₀ (by linarith) hk).trans (pow_le_pow_left₀ (by linarith) (by linarith) κ)
        rw [hn]
        linarith
    · linarith
  · have e : goodCurvaturePower u k S w = 0 := S.levelObservable_of_not_le hK w
    rw [e]
    linarith
private theorem badResponseProduct_le (B : Finset (Fin Λ.k)) {ε G : ℝ} (hε : 0 < ε) (hG : 0 ≤ G)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side))
    (hsq : (∏ i ∈ B, |S.supportTotal S.lastSeparated (S.sideAtLevel S.lastSeparated) i
        (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)|) ^ 2 ≤
      G * (∏ i ∈ B, S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)) ^ 2) :
    badResponseProduct B S w ≤ 0 + (ε / 2 * G) * meanScoreProduct (B.toList ++ B.toList) S w +
      1 / (2 * ε) * notGoodIndicator S.lastSeparated S w := by
  classical
  have hM : meanScoreProduct (B.toList ++ B.toList) S w =
      (∏ i ∈ B, S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)) ^ 2 := by
    unfold meanScoreProduct
    rw [List.map_append, List.prod_append, Finset.prod_map_toList, sq]
  rw [hM, S.notGoodIndicator_of_le S.lastSeparated_le]
  unfold badResponseProduct
  have hc1 : 0 ≤ ε / 2 * G := by positivity
  have hc2 : 0 ≤ ε / 2 * G *
      (∏ i ∈ B, S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)) ^ 2 :=
    mul_nonneg hc1 (sq_nonneg _)
  by_cases hg : S.IsGoodConfig S.lastSeparated (S.sideAtLevel S.lastSeparated) (S.stateAtLevel S.lastSeparated S.lastSeparated_le w).1
      (S.stateAtLevel S.lastSeparated S.lastSeparated_le w).2.1
  · rw [if_pos hg, if_pos hg]
    linarith
  · rw [if_neg hg, if_neg hg]
    set f : ℝ := ∏ i ∈ B, |S.supportTotal S.lastSeparated (S.sideAtLevel S.lastSeparated) i
      (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)| with hf
    have key : f ≤ ε / 2 * f ^ 2 + 1 / (2 * ε) := by
      have h2 : 0 ≤ (ε * f - 1) ^ 2 / (2 * ε) := by positivity
      have e : ε / 2 * f ^ 2 + 1 / (2 * ε) - f = (ε * f - 1) ^ 2 / (2 * ε) := by field_simp; ring
      linarith
    have h3 : ε / 2 * f ^ 2 ≤ ε / 2 * (G *
        (∏ i ∈ B, S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)) ^ 2) := by
      gcongr
    nlinarith
private theorem badResponseProduct_nonneg (B : Finset (Fin Λ.k))
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : 0 ≤ badResponseProduct B S w := by
  classical
  unfold badResponseProduct
  split_ifs
  · exact le_rfl
  · exact Finset.prod_nonneg fun i _ => abs_nonneg _
private theorem badResponseProduct_empty (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    badResponseProduct ∅ S w = notGoodIndicator S.lastSeparated S w := by
  classical
  rw [S.notGoodIndicator_of_le S.lastSeparated_le]
  unfold badResponseProduct
  simp only [Finset.prod_empty]
end MomentPoint
end Point
section Scores
variable {Λ : MomentParameters}
namespace MomentPoint
variable (S : MomentPoint Λ) {CS Cs : ℝ}
private theorem supportTotal_held (h : SampleFacts S CS Cs) :
    ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)), ∀ i : Fin Λ.k,
    |S.supportTotal S.lastSeparated (S.sideAtLevel S.lastSeparated) i (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)| ≤
      Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) *
        S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i (S.stateAtLevel S.lastSeparated S.lastSeparated_le w) := by
  have key : ∀ (n : ℕ) [NeZero n], n = S.levelSide S.lastSeparated → ∀ᵐ x ∂(S.law S.lastSeparated n), ∀ i : Fin Λ.k,
      |S.supportTotal S.lastSeparated n i (S.state S.lastSeparated n x)| ≤
        Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) *
          S.meanScore S.lastSeparated n i (S.state S.lastSeparated n x) := by
    intro n _ hn
    subst hn
    exact h.held
  exact S.ae_of_level h S.lastSeparated S.lastSeparated_le (key (S.sideAtLevel S.lastSeparated) (S.sideAtLevel_eq _))
private theorem resp_admissible {u : ℕ} (hu : u ≤ S.data.windowLevel) : (S.resp u).IsAdmissible := by
  have h1 := (S.onFlow u hu).onFamily.admissible
  rw [← S.stage_eq u hu] at h1
  exact h1
abbrev _root_.YangMills.SharedProofs.p17647 := @resp_admissible
section
variable (u n : ℕ) [NeZero n]
private theorem measurable_meanScore (hs : Measurable (S.resp u).score) (i : Fin Λ.k) :
    Measurable fun q : StageState S.tower u n => S.meanScore u n i q := by
  refine measurable_of_sigma_slices fun Y => ?_
  simp only [MomentPoint.meanScore, ResponseInTheExpansion.meanSiteScore]
  refine measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun y _ => ?_))
  unfold siteScore
  by_cases hy : y ∈ Y
  · simp only [hy, dite_true]
    exact hs.comp ((measurable_pi_apply _).comp measurable_snd)
  · simp only [hy, dite_false]
    exact measurable_const
abbrev _root_.YangMills.SharedProofs.p9251 := @measurable_meanScore
private theorem one_le_meanScore (hs : ∀ w, 0 ≤ (S.resp u).score w) (i : Fin Λ.k) (q : StageState S.tower u n) :
    1 ≤ S.meanScore u n i q := by
  simp only [MomentPoint.meanScore, ResponseInTheExpansion.meanSiteScore]
  have : 0 ≤ ∑ y ∈ S.supportAt u n i, siteScore (S.resp u).score q.2.1 q.2.2 y := Finset.sum_nonneg fun y _ => by
    unfold siteScore
    split_ifs
    · exact hs _
    · exact le_rfl
  have h2 : 0 ≤ ((S.supportAt u n i).card : ℝ)⁻¹ := by positivity
  nlinarith [mul_nonneg h2 this]
abbrev _root_.YangMills.SharedProofs.p166 := @one_le_meanScore
end
private theorem measurable_meanScoreProduct (h : SampleFacts S CS Cs) (J : List (Fin Λ.k)) : Measurable (meanScoreProduct J S) := by
  have htK : S.lastSeparated ≤ S.data.windowLevel := S.lastSeparated_le
  have hq := (h.measurable_state S.lastSeparated (S.sideAtLevel S.lastSeparated)).comp (S.sampleAtLevel_map h S.lastSeparated htK).1
  have hsm : Measurable (S.resp S.lastSeparated).score := (resp_admissible S htK).price.borel
  have hN : ∀ i, Measurable fun w =>
      S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i (S.stateAtLevel S.lastSeparated S.lastSeparated_le w) := fun i =>
    (measurable_meanScore S S.lastSeparated _ hsm i).comp hq
  unfold meanScoreProduct
  induction J with
  | nil => simpa using measurable_const
  | cons a J ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hN a).mul ih
private theorem meanScoreProduct_moment (h : SampleFacts S CS Cs) {Cs : ℝ}
    (hsc : ∀ (p : ℕ), 1 ≤ p → ∀ J : List (Fin Λ.k), J.length = p →
      ∫⁻ w, ENNReal.ofReal (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤
        ENNReal.ofReal (Cs ^ p * (p.factorial : ℝ) ^ 6)) (J : List (Fin Λ.k)) (q : ℕ) :
    ∫⁻ w, ENNReal.ofReal (|meanScoreProduct J S w| ^ q) ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)) ≤
      ENNReal.ofReal (Cs ^ (q * J.length + 1) * ((q * J.length + 1).factorial : ℝ) ^ 6) := by
  have htK : S.lastSeparated ≤ S.data.windowLevel := S.lastSeparated_le
  have hsm : Measurable (S.resp S.lastSeparated).score := (resp_admissible S htK).price.borel
  have hs0 : ∀ w, 0 ≤ (S.resp S.lastSeparated).score w := (resp_admissible S htK).price.nonneg
  obtain ⟨m1, e1⟩ := S.sampleAtLevel_map h S.lastSeparated htK
  have hq := h.measurable_state S.lastSeparated (S.sideAtLevel S.lastSeparated)
  have hf : Measurable fun x => ENNReal.ofReal (|(J.map fun i => S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i
      (S.state S.lastSeparated (S.sideAtLevel S.lastSeparated) x)).prod| ^ q) := by
    refine ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp ?_).pow_const q)
    have hN : ∀ i, Measurable fun x => S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i
        (S.state S.lastSeparated (S.sideAtLevel S.lastSeparated) x) := fun i =>
      (measurable_meanScore S S.lastSeparated _ hsm i).comp hq
    induction J with
    | nil => simpa using measurable_const
    | cons a J ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (hN a).mul ih
  have key : ∀ (n : ℕ) [NeZero n], n = S.levelSide S.lastSeparated →
      ∫⁻ x, ENNReal.ofReal (|(J.map fun i => S.meanScore S.lastSeparated n i (S.state S.lastSeparated n x)).prod| ^ q)
        ∂(S.law S.lastSeparated n) ≤
      ENNReal.ofReal (Cs ^ (q * J.length + 1) * ((q * J.length + 1).factorial : ℝ) ^ 6) := by
    intro n _ hn
    subst hn
    refine le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_)
      (hsc _ (by omega) (0 :: (List.replicate q J).flatten) ?_)
    · have hN1 := fun i => one_le_meanScore S S.lastSeparated (S.levelSide S.lastSeparated) hs0 i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) x)
      rw [List.map_cons, List.prod_cons, prod_flatten_replicate]
      have h1 := one_le_list_prod _ hN1 J
      rw [abs_of_nonneg (by linarith)]
      exact le_mul_of_one_le_left (by positivity) (hN1 0)
    · simp [length_flatten_replicate]
  have k := key (S.sideAtLevel S.lastSeparated) (S.sideAtLevel_eq _)
  rw [← e1, lintegral_map hf m1] at k
  exact k
end MomentPoint
end Scores
section Field
variable {Λ : MomentParameters}
private theorem period_facts (S : MomentPoint Λ) (hfit : Λ.stepParams.Admissible) :
    Λ.stepParams.side ∣ S.data.period Λ.stepParams.side ∧ 64 ≤ S.data.period Λ.stepParams.side := by apply _root_.YangMills.SharedProofs.p32373 <;> assumption
private theorem hasBoundedMoments_of_bound {T : TranslatedLaws} {X : T.Family} (hp : ∀ i, IsProbabilityMeasure (T.μ i))
    (hb : ∀ i, AEMeasurable (X i) (T.μ i))
    {C : ℝ} (hC : ∀ i, ∀ᵐ ω ∂(T.μ i), |X i ω| ≤ C) : TranslatedLaws.HasBoundedMoments X := by apply _root_.YangMills.SharedProofs.p39822 <;> assumption
private abbrev ExtraSlot (Λ : MomentParameters) : Type :=
  (ℕ ⊕ (ℕ × (Fin 4 → ℤ) × Fin 4 × Fin 4 × ℕ)) ⊕ (ℕ ⊕ List (Fin Λ.k))
private def extraObservable : ExtraSlot Λ → SampleObservable Λ
  | .inl (.inl u) => notClearIndicator u
  | .inl (.inr e) => clearCurvaturePower e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2
  | .inr (.inl u) => notGoodIndicator u
  | .inr (.inr J) => meanScoreProduct J
private structure SubsequenceFacts (rule : ChainNoise.NoiseRule Λ.stepParams) (Sq : ℕ → MomentPoint Λ) (p t N : ℕ) (x : ℝ) (r : ℕ)
    (CS Cs : ℝ) : Prop where
  preserving : (translatedTori Sq p).IsPreserving
  sample_facts : ∀ i, SampleFacts (Sq i) CS Cs
  lastSeparated_eq : ∀ i, (Sq i).lastSeparated = t
  logIndex_eq : ∀ i, (Sq i).logIndex = N
  scaleCoupling_eq : ∀ i, (Sq i).scaleCoupling = x
  range_eq : ∀ i, (Sq i).range = r
  sample : ∀ i, Measurable ((Sq i).sampleOf rule) ∧
    (Sq i).sampleLaw.map ((Sq i).sampleOf rule) = (Sq i).law (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side)
namespace SubsequenceFacts
variable {rule : ChainNoise.NoiseRule Λ.stepParams} {Sq : ℕ → MomentPoint Λ} {p t N : ℕ} {x : ℝ} {r : ℕ} {CS Cs : ℝ}
private theorem aemeasurable_family (h : SubsequenceFacts rule Sq p t N x r CS Cs) {g : SampleObservable Λ} (i : ℕ)
    (hg : AEMeasurable (g (Sq i)) ((Sq i).law (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side))) :
    AEMeasurable (sampleFamily rule Sq p g i) ((translatedTori Sq p).μ i) := by
  rw [← (h.sample i).2] at hg
  exact hg.comp_measurable (h.sample i).1
private theorem ae_of_sample (h : SubsequenceFacts rule Sq p t N x r CS Cs) (i : ℕ)
    {P : MarkedSample Λ.stepParams (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side) → Prop}
    (hP : ∀ᵐ w ∂((Sq i).law (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side)), P w) :
    ∀ᵐ ω ∂((Sq i).sampleLaw), P ((Sq i).sampleOf rule ω) := by
  rw [← (h.sample i).2] at hP
  exact ae_of_ae_map (h.sample i).1.aemeasurable hP
private theorem hasBoundedMoments_family (h : SubsequenceFacts rule Sq p t N x r CS Cs) {g : SampleObservable Λ} {C : ℝ}
    (hg : ∀ i, Measurable (g (Sq i))) (hC : ∀ i w, |g (Sq i) w| ≤ C) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p g) :=
  hasBoundedMoments_of_bound h.preserving.isProbability (fun i => h.aemeasurable_family i (hg i).aemeasurable)
    (fun i => ae_of_all _ fun ω => hC i _)
private theorem extra_hasBoundedMoments (h : SubsequenceFacts rule Sq p t N x r CS Cs) :
    ∀ e : ExtraSlot Λ, TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (extraObservable e))
  | .inl (.inl u) => h.hasBoundedMoments_family (fun i => (Sq i).measurable_notClearIndicator (h.sample_facts i) u)
      (fun i w => (Sq i).abs_notClearIndicator_le u w)
  | .inl (.inr e) => h.hasBoundedMoments_family (fun i => (Sq i).measurable_clearCurvaturePower (h.sample_facts i) _ _ _ _ _)
      (fun i w => (Sq i).abs_clearCurvaturePower_le _ _ _ _ _ w)
  | .inr (.inl u) => h.hasBoundedMoments_family (fun i => (Sq i).measurable_notGoodIndicator (h.sample_facts i) u)
      (fun i w => (Sq i).abs_notGoodIndicator_le u w)
  | .inr (.inr J) => by
    refine ⟨fun i => h.aemeasurable_family i ((Sq i).measurable_meanScoreProduct (h.sample_facts i) _).aemeasurable, fun q =>
      ⟨Cs ^ (q * J.length + 1) * ((q * J.length + 1).factorial : ℝ) ^ 6, fun i => ?_⟩⟩
    have hm := (Sq i).measurable_meanScoreProduct (h.sample_facts i) J
    have k := (Sq i).meanScoreProduct_moment (h.sample_facts i) (h.sample_facts i).scores J q
    have hf : Measurable fun w => ENNReal.ofReal (|meanScoreProduct J (Sq i) w| ^ q) :=
      ((continuous_abs.measurable.comp hm).pow_const q).ennreal_ofReal
    rw [← (h.sample i).2, lintegral_map hf (h.sample i).1] at k
    exact k
end SubsequenceFacts
private def firstConstant (CM : ℕ → ℝ) (CH c : ℝ) (N : ℕ) : ℝ :=
  2 * CH * ((N.factorial : ℝ) / c ^ N) + 2560000 * |CM (2 * N + 2)|
private def secondConstant (CM : ℕ → ℝ) (CH c : ℝ) (k : ℕ) : ℝ :=
  2 ^ (k + 1) * (1 + 2560000 * |CM (201 * (k + 1))| + CH * (((k + 1).factorial : ℝ) / c ^ (k + 1)))
private theorem window_bounds {S : MomentPoint Λ} (F : LimitLawAtPoint S) {t : ℕ} {CS Cs CH c Cq : ℝ} {CM : ℕ → ℝ}
    (hq : SubsequenceFacts F.rule F.points F.period t S.logIndex S.scaleCoupling S.range CS Cs) (jw : ExtraSlot Λ → F.Index)
    (hjw : ∀ e, F.observables (jw e) = extraObservable e) (hc : 0 < c)
    (hint : ∀ j, Integrable (evalAtZero j) F.law)
    (hH : ∀ (u : ℕ) (j : F.Index), t ≤ u → F.observables j = notClearIndicator u →
      ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ CH * Real.exp (-(c * S.scaleCoupling)))
    (hM : ∀ u : ℕ, t ≤ u → u ≤ t + S.logIndex + 2 → ∀ (z : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν → (∀ a, (z a).natAbs ≤ 4 * S.range ^ 2) →
      ∀ (q : ℕ) (j : F.Index), 1 ≤ q → F.observables j = clearCurvaturePower u z μ ν q →
        ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ CM q * S.scaleCoupling ^ (-(q : ℝ)))
    (hQ : ∀ p : ℕ, 1 ≤ p → ∀ (J : List (Fin Λ.k)) (j : F.Index), J.length = p → F.observables j = meanScoreProduct J →
      ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ Cq ^ p * (p.factorial : ℝ) ^ 6) :
    (∀ u : ℕ, t ≤ u → u ≤ t + S.logIndex + 1 →
      (∀ (N : ℕ) (j : F.Index), F.observables j = notGoodIndicator u →
        ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ firstConstant CM |CH| c N * S.scaleCoupling ^ (-(N : ℝ))) ∧
      ∀ (k : ℕ) (j : F.Index), F.observables j = goodCurvaturePower u k →
        ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ secondConstant CM |CH| c k * S.scaleCoupling ^ ((1 : ℝ) / 4000)) ∧
    ∀ (B : Finset (Fin Λ.k)) (N : ℕ) (j : F.Index), F.observables j = badResponseProduct B → ∀ᵐ v ∂F.law,
      F.condMeanAt j v ≤ (thirdConstant Λ.response.C₀ CS Cq Λ.k + firstConstant CM |CH| c (2 * N + Λ.k)) *
        S.scaleCoupling ^ (-(N : ℝ)) := by
  classical
  have hx8 : (8 : ℝ) ^ 100 ≤ S.scaleCoupling := by
    have := (hq.sample_facts 0).scale_ge
    rwa [hq.scaleCoupling_eq 0] at this
  have hx1 : 1 ≤ S.scaleCoupling := le_trans (one_le_pow₀ (by norm_num)) hx8
  have hx0 : 0 < S.scaleCoupling := by linarith
  have hr := clusterRange_bounds hx8
  have hr' : (8 : ℝ) ≤ (S.range : ℝ) := hr.1
  have hmi : ∀ i, (F.points i).rangeSq = S.rangeSq := fun i => by
    show (F.points i).range ^ 2 = S.range ^ 2
    rw [hq.range_eq i]
  have h8 : ∀ i, 8 * ((F.points i).rangeSq : ℝ) ≤ ((F.points i).range : ℝ) ^ 3 := fun i => by
    rw [hmi i, hq.range_eq i]
    have h2 : (S.rangeSq : ℝ) = (S.range : ℝ) ^ 2 := by simp [MomentPoint.rangeSq]
    rw [h2]
    have : 0 ≤ (S.range : ℝ) ^ 2 := by positivity
    nlinarith
  obtain ⟨R, hR⟩ : ∃ R, R = 2 * S.rangeSq := ⟨_, rfl⟩
  have hRi : ∀ i, R = 2 * (F.points i).rangeSq := fun i => by rw [hmi i, hR]
  have hH' : ∀ u, t ≤ u → ∀ᵐ v ∂F.law, invariantCondExp F.law (evalAtZero (jw (.inl (.inl u)))) v ≤
      |CH| * Real.exp (-(c * S.scaleCoupling)) := fun u hu => by
    filter_upwards [hH u (jw (.inl (.inl u))) hu (hjw _)] with v hv
    exact hv.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  have hM' : ∀ u : ℕ, t ≤ u → u ≤ t + S.logIndex + 2 → ∀ Q : ℕ, 1 ≤ Q → ∀ e ∈ plaquetteOffsets R,
      ∀ᵐ v ∂F.law, invariantCondExp F.law (evalAtZero (jw (.inl (.inr (u, e.1, e.2.1, e.2.2, Q))))) v ≤
        |CM Q| * S.scaleCoupling ^ (-(Q : ℝ)) := by
    intro u h1 h2 Q hQ1 e he
    obtain ⟨a1, a2⟩ := Finset.mem_product.1 he
    have hz : ∀ a, (e.1 a).natAbs ≤ 4 * S.range ^ 2 := fun a => by
      have h3 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 a1 a)
      show (e.1 a).natAbs ≤ 4 * S.rangeSq
      omega
    filter_upwards [hM u h1 h2 e.1 e.2.1 e.2.2 (Finset.mem_filter.1 a2).2 hz Q (jw (.inl (.inr (u, e.1, e.2.1, e.2.2, Q)))) hQ1 (hjw _)]
      with v hv
    exact hv.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hcard : ((plaquetteOffsets R).card : ℝ) ≤
      ((16 * (2 * (2 * (TorusLumps.clusterRange S.scaleCoupling) ^ 2) + 1) ^ 4 : ℕ) : ℝ) := by
    have h1 := plaquetteOffsets_card R
    have e : R = 2 * (TorusLumps.clusterRange S.scaleCoupling) ^ 2 := hR
    rw [e] at h1 ⊢
    exact_mod_cast h1
  have hP := offsetCount_le hx8
  have hb1 : ∀ u : ℕ, t ≤ u → u ≤ t + S.logIndex + 1 → ∀ (N : ℕ) (j : F.Index), F.observables j = notGoodIndicator u →
      ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ firstConstant CM |CH| c N * S.scaleCoupling ^ (-(N : ℝ)) := by
    intro u h1 h2 N j hj
    have ha : 0 < S.scaleCoupling ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hs := condMean_le_of_jointLimit F.isJointLimitLaw hint (plaquetteOffsets R)
      (fun e => jw (.inl (.inr (u, e.1, e.2.1, e.2.2, 2 * N + 2)))) j (jw (.inl (.inl u)))
      (c₀ := 0) (c₁ := 1 / (S.scaleCoupling ^ (-(1 / 4) : ℝ)) ^ (2 * (2 * N + 2))) (c₂ := 1) (by positivity) zero_le_one ?_
      (hM' u h1 (by omega) (2 * N + 2) (by omega)) (hH' u h1)
    · filter_upwards [hs] with v hv
      refine hv.trans ?_
      have hf := firstConstant_bound (x := S.scaleCoupling) (c := c) (CH := |CH|) (Cq := |CM (2 * N + 2)|) N hx1 hc
        (abs_nonneg _) (abs_nonneg _) hP
      have hb0 : 0 ≤ |CM (2 * N + 2)| * S.scaleCoupling ^ (-((2 * N + 2 : ℕ) : ℝ)) := by positivity
      have he0 : 0 ≤ |CH| * Real.exp (-(c * S.scaleCoupling)) := by positivity
      have hm : 1 / (S.scaleCoupling ^ (-(1 / 4) : ℝ)) ^ (2 * (2 * N + 2)) *
            (((plaquetteOffsets R).card : ℝ) * (|CM (2 * N + 2)| * S.scaleCoupling ^ (-((2 * N + 2 : ℕ) : ℝ)))) ≤
          ((16 * (2 * (2 * (TorusLumps.clusterRange S.scaleCoupling) ^ 2) + 1) ^ 4 : ℕ) : ℝ) *
            (|CM (2 * N + 2)| * S.scaleCoupling ^ (-((2 * N + 2 : ℕ) : ℝ)) / (S.scaleCoupling ^ (-(1 / 4) : ℝ)) ^ (2 * (2 * N + 2))) := by
        have e : ((16 * (2 * (2 * (TorusLumps.clusterRange S.scaleCoupling) ^ 2) + 1) ^ 4 : ℕ) : ℝ) *
              (|CM (2 * N + 2)| * S.scaleCoupling ^ (-((2 * N + 2 : ℕ) : ℝ)) / (S.scaleCoupling ^ (-(1 / 4) : ℝ)) ^ (2 * (2 * N + 2))) =
            1 / (S.scaleCoupling ^ (-(1 / 4) : ℝ)) ^ (2 * (2 * N + 2)) *
              (((16 * (2 * (2 * (TorusLumps.clusterRange S.scaleCoupling) ^ 2) + 1) ^ 4 : ℕ) : ℝ) *
                (|CM (2 * N + 2)| * S.scaleCoupling ^ (-((2 * N + 2 : ℕ) : ℝ)))) := by
          ring
        rw [e]
        gcongr
      have e2 : firstConstant CM |CH| c N = 2 * |CH| * ((N.factorial : ℝ) / c ^ N) + 2560000 * |CM (2 * N + 2)| := rfl
      rw [e2]
      linarith
    · refine Eventually.of_forall fun i => ae_of_all _ fun ω => ?_
      have h := (F.points i).notGoodIndicator_le (hq.scaleCoupling_eq i) hx0 (hRi i) (u := u)
        (by rw [hq.lastSeparated_eq i, hq.logIndex_eq i]; omega) (h8 i) (Q := 2 * N + 2) (by omega)
        ((F.points i).sampleOf F.rule ω)
      simp only [sampleFamily, hj, hjw]
      exact h
  have hb2 : ∀ u : ℕ, t ≤ u → u ≤ t + S.logIndex + 1 → ∀ (k : ℕ) (j : F.Index), F.observables j = goodCurvaturePower u k →
      ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ secondConstant CM |CH| c k * S.scaleCoupling ^ ((1 : ℝ) / 4000) := by
    intro u h1 h2 k j hj
    obtain ⟨hT, hb⟩ := secondConstant_bound (x := S.scaleCoupling) (c := c) (CH := |CH|) (Cq := |CM (201 * (k + 1))|) k hx1 hc
      (abs_nonneg _) (abs_nonneg _) hP
    set T : ℝ := S.scaleCoupling ^ ((1 : ℝ) / (4000 * ((k + 1 : ℕ) : ℝ))) with hTd
    have hT0 : 0 < T := by linarith
    have hs := condMean_le_of_jointLimit F.isJointLimitLaw hint (plaquetteOffsets R)
      (fun e => jw (.inl (.inr (u, e.1, e.2.1, e.2.2, 201 * (k + 1))))) j (jw (.inl (.inl u)))
      (c₀ := (2 * T) ^ (k + 1)) (c₁ := 2 ^ (k + 1) * T ^ (k + 1) / T ^ (2 * (201 * (k + 1))) * S.scaleCoupling ^ (201 * (k + 1)))
      (c₂ := (1 + S.scaleCoupling ^ ((1 : ℝ) / 4)) ^ (k + 1)) (by positivity) (by positivity) ?_
      (hM' u h1 (by omega) (201 * (k + 1)) (by omega)) (hH' u h1)
    · filter_upwards [hs] with v hv
      refine hv.trans (le_trans ?_ hb)
      have hB0 : 0 ≤ 2 ^ (k + 1) * T ^ (k + 1) / T ^ (2 * (201 * (k + 1))) * S.scaleCoupling ^ (201 * (k + 1)) := by positivity
      have hb0 : 0 ≤ |CM (201 * (k + 1))| * S.scaleCoupling ^ (-((201 * (k + 1) : ℕ) : ℝ)) := by positivity
      have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hb0) hB0
      linarith
    · refine Eventually.of_forall fun i => ae_of_all _ fun ω => ?_
      have h := (F.points i).goodCurvaturePower_le (hq.scaleCoupling_eq i) hx1 (hRi i) (u := u) (k := k) (κ := k + 1)
        (Q := 201 * (k + 1)) hT (by omega) (by omega) (by omega)
        ((F.points i).sampleOf F.rule ω)
      simp only [sampleFamily, hj, hjw]
      exact h
  refine ⟨fun u h1 h2 => ⟨hb1 u h1 h2, hb2 u h1 h2⟩, fun B N j hj => ?_⟩
  obtain ⟨M, hMd⟩ : ∃ M, M = 2 * N + Λ.k := ⟨_, rfl⟩
  have hfirst0 : 0 ≤ firstConstant CM |CH| c M := by
    unfold firstConstant
    positivity
  have hthird0 : 0 ≤ thirdConstant Λ.response.C₀ CS Cq Λ.k := by
    unfold thirdConstant
    positivity
  have hbad : ∀ᵐ v ∂F.law, invariantCondExp F.law (evalAtZero (jw (.inr (.inl t)))) v ≤
      firstConstant CM |CH| c M * S.scaleCoupling ^ (-(M : ℝ)) :=
    hb1 t le_rfl (by omega) M (jw (.inr (.inl t))) (hjw _)
  by_cases hB : B = ∅
  · subst hB
    have hs := condMean_le_of_jointLimit F.isJointLimitLaw hint (∅ : Finset Unit) (fun _ => jw (.inr (.inl t))) j (jw (.inr (.inl t)))
      (c₀ := 0) (c₁ := 0) (c₂ := 1) (b := 0) le_rfl zero_le_one ?_ (by simp) hbad
    · filter_upwards [hs] with v hv
      refine hv.trans ?_
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add, one_mul]
      have h1 : S.scaleCoupling ^ (-(M : ℝ)) ≤ S.scaleCoupling ^ (-(N : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1 (by
        have : (N : ℝ) ≤ M := by exact_mod_cast (by omega : N ≤ M)
        linarith)
      rw [← hMd]
      have h2 := mul_le_mul_of_nonneg_left h1 hfirst0
      have h3 : 0 ≤ thirdConstant Λ.response.C₀ CS Cq Λ.k * S.scaleCoupling ^ (-(N : ℝ)) := by positivity
      linarith
    · refine Eventually.of_forall fun i => ae_of_all _ fun ω => ?_
      simp only [sampleFamily, hj, hjw, Finset.sum_empty, mul_zero, add_zero, zero_add, one_mul]
      have h := (F.points i).badResponseProduct_empty ((F.points i).sampleOf F.rule ω)
      rw [hq.lastSeparated_eq i] at h
      exact h.le
  · subst hMd
    have hp1 : 1 ≤ 2 * B.card := by
      have := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hB)
      omega
    have hJ : (B.toList ++ B.toList).length = 2 * B.card := by
      rw [List.length_append, Finset.length_toList]
      ring
    obtain ⟨ε, hε⟩ : ∃ ε, ε = S.scaleCoupling ^ (-((N + Λ.k : ℕ) : ℝ)) := ⟨_, rfl⟩
    have hε0 : 0 < ε := hε ▸ Real.rpow_pos_of_pos hx0 _
    obtain ⟨G, hG⟩ : ∃ G, G = (1 + |Λ.response.C₀| * |CS|) ^ (2 * Λ.k) * 256 ^ Λ.k * S.scaleCoupling ^ Λ.k := ⟨_, rfl⟩
    have hG0 : 0 ≤ G := by
      rw [hG]
      positivity
    have hr8 : (S.range : ℝ) ^ 8 ≤ 256 * S.scaleCoupling := by
      refine (clusterRange_pow_eight_le hx8).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      have := Real.rpow_le_rpow_of_exponent_le hx1 (show (2 : ℝ) / 25 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have hs := condMean_le_of_jointLimit F.isJointLimitLaw hint ({()} : Finset Unit)
      (fun _ => jw (.inr (.inr (B.toList ++ B.toList)))) j (jw (.inr (.inl t)))
      (c₀ := 0) (c₁ := ε / 2 * G) (c₂ := 1 / (2 * ε)) (b := Cq ^ (2 * B.card) * ((2 * B.card).factorial : ℝ) ^ 6)
      (by positivity) (by positivity) ?_
      (fun _ _ => hQ _ hp1 _ _ hJ (hjw _)) hbad
    · filter_upwards [hs] with v hv
      refine hv.trans ?_
      have hk : 2 * B.card ≤ 2 * Λ.k := by
        have := Finset.card_le_univ B
        simp only [Fintype.card_fin] at this
        omega
      have h3 := thirdConstant_bound (c₀ := Λ.response.C₀) (CS := CS) (CN := Cq) (C₁ := firstConstant CM |CH| c (2 * N + Λ.k))
        (k := Λ.k) (p := 2 * B.card) N hx1 hfirst0 hk
      simp only [Finset.card_singleton, Nat.cast_one, one_mul, zero_add]
      rw [hε, hG]
      exact h3
    · refine Eventually.of_forall fun i => ?_
      have hfa := hq.ae_of_sample i ((F.points i).supportTotal_held (hq.sample_facts i))
      filter_upwards [hfa] with ω hω
      have hr8i : ((F.points i).range : ℝ) ^ 8 ≤ 256 * S.scaleCoupling := by
        rw [hq.range_eq i]
        exact hr8
      have hsq := prod_abs_sq_le B (c₀ := Λ.response.C₀) (CS := CS) (r := ((F.points i).range : ℝ)) (x := S.scaleCoupling)
        (A := fun a => (((F.points i).data.supportSites Λ.stepParams.side (F.points i).lastSeparated a).card : ℝ))
        (fun a => Nat.cast_nonneg _) (hq.sample_facts i).card_le hr8i hx1 hω
      have h := (F.points i).badResponseProduct_le B hε0 hG0 ((F.points i).sampleOf F.rule ω) (by rw [hG]; exact hsq)
      rw [hq.lastSeparated_eq i] at h
      simp only [sampleFamily, hj, hjw, Finset.sum_singleton]
      exact h
private theorem point_parameters_eq (S : MomentPoint Λ) (F : LimitLawAtPoint S) (i : ℕ) :
    (F.points i).scaleCoupling = S.scaleCoupling ∧ (F.points i).range = S.range ∧ (F.points i).logIndex = S.logIndex ∧
      (F.points i).rangeSq = S.rangeSq := by
  obtain ⟨a, b, e⟩ := F.points_eq i
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl⟩
private theorem exists_constant_lastSeparated (S : MomentPoint Λ) (F : LimitLawAtPoint S) :
    ∃ (t : ℕ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ i, (F.points (φ i)).lastSeparated = t := by
  have hle : ∀ i, (F.points i).lastSeparated ≤ S.data.scaleLevel := fun i => by
    obtain ⟨a, b, e⟩ := F.points_eq i
    rw [e]
    classical
    unfold MomentPoint.lastSeparated
    exact Nat.findGreatest_le _
  let f : ℕ → Fin (S.data.scaleLevel + 1) := fun i => ⟨(F.points i).lastSeparated, Nat.lt_succ_of_le (hle i)⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
  have hfreq : ∃ᶠ i in atTop, f i = y := Nat.frequently_atTop_iff_infinite.2 hinf
  obtain ⟨φ, hφ, hy'⟩ := extraction_of_frequently_atTop hfreq
  exact ⟨y, φ, hφ, fun i => congrArg Fin.val (hy' i)⟩
abbrev _root_.YangMills.SharedProofs.p85868 := @exists_constant_lastSeparated
private theorem bound_in_any_limit (hExt : jointLimitExtendStatement) (hMn : jointLimitPropertiesStatement) {CS Cs X₀ : ℝ}
    (hSeq : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S), X₀ ≤ S.scaleCoupling → ∀ φ : ℕ → ℕ, StrictMono φ → ∀ t : ℕ,
      (∀ i, (F.points (φ i)).lastSeparated = t) →
      SubsequenceFacts F.rule (fun i => F.points (φ i)) F.period t S.logIndex S.scaleCoupling S.range CS Cs)
    (S : MomentPoint Λ) (hx : X₀ ≤ S.scaleCoupling) (F : LimitLawAtPoint S) (j : F.Index) {b : ℝ}
    (hnn : ∀ i w, 0 ≤ F.observables j (F.points i) w)
    (main : ∀ (F' : LimitLawAtPoint S) (t i₀ : ℕ), t = (F.points i₀).lastSeparated →
      SubsequenceFacts F'.rule F'.points F'.period t S.logIndex S.scaleCoupling S.range CS Cs →
      (∀ j' : F'.Index, Integrable (evalAtZero j') F'.law) → ∀ jw : ExtraSlot Λ → F'.Index,
      (∀ e, F'.observables (jw e) = extraObservable e) →
      ∀ j' : F'.Index, F'.observables j' = F.observables j → ∀ᵐ v ∂F'.law, F'.condMeanAt j' v ≤ b) :
    ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ b := by
  classical
  obtain ⟨t, φ, hφ, ht⟩ := exists_constant_lastSeparated S F
  have hcount := F.countable_index
  have hq₀ := hSeq S F hx φ hφ t ht
  have hXf : ∀ j, TranslatedLaws.HasBoundedMoments (sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j)) := fun j =>
    ⟨fun i => (F.hasBoundedMoments j).aemeasurable (φ i), fun q => by
      obtain ⟨C, hC⟩ := (F.hasBoundedMoments j).moment_bound q
      exact ⟨C, fun i => hC (φ i)⟩⟩
  have hlim₀ : IsJointLimitLaw (translatedTori (fun i => F.points (φ i)) F.period)
      (fun j => sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j)) F.law :=
    ⟨F.isJointLimitLaw.isProbability, fun l a G hG hb => (F.isJointLimitLaw.tendsto l a G hG hb).comp hφ.tendsto_atTop⟩
  obtain ⟨sub, P', hsub, hlim, -, htr⟩ := hExt (translatedTori (fun i => F.points (φ i)) F.period) F.Index (ExtraSlot Λ)
    (fun j => sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j))
    (fun c => sampleFamily F.rule (fun i => F.points (φ i)) F.period (extraObservable c)) F.law hq₀.preserving hXf
    hq₀.extra_hasBoundedMoments hlim₀
  have hφs : StrictMono fun i => φ (sub i) := hφ.comp hsub
  have hq := hSeq S F hx _ hφs t fun i => ht (sub i)
  have hlim' : IsJointLimitLaw (translatedTori (fun i => F.points (φ (sub i))) F.period)
      (fun c => sampleFamily F.rule (fun i => F.points (φ (sub i))) F.period (Sum.elim F.observables extraObservable c)) P' := by
    have e1 : (fun c => sampleFamily F.rule (fun i => F.points (φ (sub i))) F.period (Sum.elim F.observables extraObservable c)) =
        fun c i => Sum.elim (fun j => sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j))
          (fun c => sampleFamily F.rule (fun i => F.points (φ i)) F.period (extraObservable c)) c (sub i) := by
      funext c
      rcases c with c | c <;> rfl
    rw [e1]
    exact hlim
  let F' : LimitLawAtPoint S :=
    { rule := F.rule, rule_admissible := F.rule_admissible, period := F.period, one_le_period := F.one_le_period,
      exponents := fun i => F.exponents (φ (sub i)), strictMono_exponents := fun _ _ h => F.strictMono_exponents (hφs h),
      points := fun i => F.points (φ (sub i)), points_eq := fun i => F.points_eq _, Index := F.Index ⊕ ExtraSlot Λ,
      countable_index := inferInstance,
      observables := Sum.elim F.observables extraObservable,
      hasBoundedMoments := by
        rintro (j | c)
        · exact ⟨fun i => (hXf j).aemeasurable (sub i), fun q => by
            obtain ⟨C, hC⟩ := (hXf j).moment_bound q
            exact ⟨C, fun i => hC (sub i)⟩⟩
        · exact hq.extra_hasBoundedMoments c
      law := P', isJointLimitLaw := hlim' }
  have hint' : ∀ j' : F'.Index, Integrable (evalAtZero j') F'.law := by
    intro j'
    have hcount' : Countable F'.Index := F'.countable_index
    have hMean := hMn (translatedTori F'.points F'.period) F'.Index (fun j => sampleFamily F'.rule F'.points F'.period (F'.observables j))
      F'.law hq.preserving F'.hasBoundedMoments F'.isJointLimitLaw
    have h1 := (hMean.2.1 1 (fun _ => (j', 0))).1
    have e1 : (fun v : TranslateValues F'.Index => ∏ _c : Fin 1, v (j', 0)) = evalAtZero j' := by
      funext v
      simp [evalAtZero]
    rwa [e1] at h1
  have hb : ∀ᵐ v ∂P', invariantCondExp P' (evalAtZero (Sum.inl j)) v ≤ b :=
    main F' t (φ (sub 0)) (ht _).symm hq hint' Sum.inr (fun _ => rfl) (Sum.inl j) rfl
  have hprob := hlim'.isProbability
  have hnn' : ∀ᵐ v ∂P', 0 ≤ (evalAtZero (Sum.inl j) : TranslateValues (F.Index ⊕ ExtraSlot Λ) → ℝ) v := by
    have h1 := ae_le_of_jointLimit hlim' (fun _ : Fin 1 => (Sum.inl j : F.Index ⊕ ExtraSlot Λ)) (fun _ => 0) (fun w => w 0)
      continuous_const (continuous_apply 0)
      (Eventually.of_forall fun i => ae_of_all _ fun ω => hnn _ _)
    exact h1
  have hlow : 0 ≤ᵐ[P'] invariantCondExp P' (evalAtZero (Sum.inl j)) := condExp_nonneg hnn'
  have hMean := hMn (translatedTori (fun i => F.points (φ i)) F.period) F.Index
    (fun j => sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j)) F.law
    hq₀.preserving hXf hlim₀
  have hY : Integrable (evalAtZero j) F.law := by
    have h1 := (hMean.2.1 1 (fun _ => (j, 0))).1
    have e1 : (fun v : TranslateValues F.Index => ∏ _c : Fin 1, v (j, 0)) = evalAtZero j := by
      funext v
      simp [evalAtZero]
    rwa [e1] at h1
  have h2 := htr (evalAtZero j) 0 b hY (by
    filter_upwards [hb, hlow] with v h1 h3
    exact ⟨h3, h1⟩)
  filter_upwards [h2] with v hv
  exact hv.2
end Field
section Final
private theorem forAllHullParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁)
    (h₂ : ForAllHullParameters Q₂) : ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHullParameters_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ∀ Λ, Q₁ Λ → Q₂ Λ)
    (h₁ : ForAllHullParameters Q₁) : ForAllHullParameters Q₂ := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := h₁ a ha
  refine ⟨L₁, r₁, C₁, hr₁, ?_⟩
  intro L hL hLL Tb e1 e2 e3 e4 e5 e6 e7
  obtain ⟨M₁, K₁⟩ := H₁ L hL hLL Tb e1 e2 e3 e4 e5 e6 e7
  refine ⟨M₁, fun Kr hM f1 f2 f3 f4 => ?_⟩
  obtain ⟨y₁, Y₁⟩ := K₁ Kr hM f1 f2 f3 f4
  exact ⟨y₁, fun y hy hR hW g hg hgy k _ hk2 hk8 R d hd =>
    h _ (Y₁ y hy hR hW g hg hgy k hk2 hk8 R d hd)⟩
abbrev _root_.YangMills.SharedProofs.p16214 := @forAllHullParameters_mono
private theorem forAllHullParameters_of {Q : MomentParameters → Prop} (h : ForAllParameters Q) : ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllParameters_admissible : ForAllParameters fun Λ => Λ.table.Admissible ∧ Λ.table.floorMin ≤ Λ.floor := by apply _root_.YangMills.SharedProofs.p9852 <;> assumption
theorem goodStatesLimit_holds (h₁ : curvatureLimitMomentStatement) (h₂ : hullsClearLimitStatement)
    (h₃ : meanScoreLimitMomentStatement) (h₄ : jointLimitExtendStatement) (h₅ : jointLimitPropertiesStatement)
    (h₆ : largerToriStatement) (h₇ : supportTotalBoundedByScoresStatement) (h₈ : farLevelSupportSitesStatement)
    (h₉ : scaleWindowStatement) (h₁₀ : meanScoreMomentBoundStatement) (h₁₁ : ResponseInTheExpansion.StageStatesMeasurableStatement)
    (h₁₂ : ResponseInTheExpansion.sampleBelowLawStatement) (h₁₃ : ChainNoise.ruleDrawsChainStatement) : goodStatesLimitStatement := by
  unfold curvatureLimitMomentStatement at h₁
  unfold hullsClearLimitStatement at h₂
  unfold meanScoreLimitMomentStatement at h₃
  unfold largerToriStatement at h₆
  unfold supportTotalBoundedByScoresStatement ForAllPoints at h₇
  unfold farLevelSupportSitesStatement ForAllPoints at h₈
  unfold scaleWindowStatement ForAllPoints at h₉
  unfold meanScoreMomentBoundStatement ForAllHullPoints at h₁₀
  unfold goodStatesLimitStatement
  refine forAllHullParameters_mono ?_ (forAllHullParameters_and h₁ (forAllHullParameters_and h₂ (forAllHullParameters_and h₃
    (forAllHullParameters_and h₆ (forAllHullParameters_and (forAllHullParameters_of h₇)
    (forAllHullParameters_and (forAllHullParameters_of h₈) (forAllHullParameters_and (forAllHullParameters_of h₉)
    (forAllHullParameters_and h₁₀ (forAllHullParameters_of forAllParameters_admissible)))))))))
  rintro Λ ⟨⟨CM, XM, _, HM⟩, ⟨CH, c, XH, hc, _, HH⟩, ⟨Cq, HQ⟩, hP, ⟨_, _, XF, _, _, HF⟩, ⟨CS, _, _, _, _, HS⟩,
    ⟨_, _, XW, _, _, HW⟩, ⟨CN, _, _, _, _, HN⟩, hD, hy⟩
  have hfit : Λ.stepParams.Admissible := hD.fits Λ.floor hy
  have hL : 11 * 2 ^ 12 * Λ.stepParams.baseDepth < Λ.stepParams.side := hD.L_gt
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, X₀ = max Λ.floor (max XM (max XH (max XF (max XW ((8 : ℝ) ^ 100))))) := ⟨_, rfl⟩
  have eM : XM ≤ X₀ := by rw [hX₀]; simp
  have eH : XH ≤ X₀ := by rw [hX₀]; simp
  have eF : XF ≤ X₀ := by rw [hX₀]; simp
  have eW : XW ≤ X₀ := by rw [hX₀]; simp
  have e8 : (8 : ℝ) ^ 100 ≤ X₀ := by rw [hX₀]; simp
  have hPF : ∀ S : MomentPoint Λ, X₀ ≤ S.scaleCoupling → SampleFacts S (CS 0) (CN 0) := fun S hx =>
    { scale_ge := e8.trans hx
      window := (HW S (eW.trans hx)).2.2.2.2.2.1
      measurable_state := fun u n _ => h₁₁ Λ.stepParams hfit S.tower u n
      sample_below := fun s d n _ =>
        (h₁₂ Λ.stepParams hfit hL S.tower S.isCutoff S.marksMeasurable S.β (fun _ => 0)).1 s d n
      held := HF S (eF.trans hx)
      card_le := (HS S).1
      scores := fun p hp J hJ => (HN S p hp J hJ).2 }
  have hSeq : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S), X₀ ≤ S.scaleCoupling → ∀ φ : ℕ → ℕ, StrictMono φ → ∀ t : ℕ,
      (∀ i, (F.points (φ i)).lastSeparated = t) →
      SubsequenceFacts F.rule (fun i => F.points (φ i)) F.period t S.logIndex S.scaleCoupling S.range (CS 0) (CN 0) := by
    intro S F hx φ hφ t ht
    have hmom := (hP S).2.2.2 F.rule (fun i => F.exponents (φ i)) (fun i => F.points (φ i)) F.period F.rule_admissible
      F.one_le_period (fun _ _ h => F.strictMono_exponents (hφ h)) (fun i => F.points_eq _)
    have hxi : ∀ i, X₀ ≤ (F.points (φ i)).scaleCoupling := fun i => by
      rw [(point_parameters_eq S F _).1]
      exact hx
    refine
      { preserving := hmom.1, sample_facts := fun i => hPF _ (hxi i), lastSeparated_eq := ht,
        logIndex_eq := fun i => (point_parameters_eq S F _).2.2.1, scaleCoupling_eq := fun i => (point_parameters_eq S F _).1,
        range_eq := fun i => (point_parameters_eq S F _).2.1, sample := fun i => ?_ }
    obtain ⟨a, b, e⟩ := F.points_eq (φ i)
    have hr : F.rule.IsAdmissible (F.points (φ i)).tower := by
      rw [e]
      exact F.rule_admissible
    obtain ⟨d1, d2⟩ := period_facts (F.points (φ i)) hfit
    exact h₁₃ Λ.stepParams hfit (F.points (φ i)).tower F.rule (F.points (φ i)).β (F.points (φ i)).isCutoff
      (F.points (φ i)).marksMeasurable hr (F.points (φ i)).data.windowLevel _ d1 d2
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ, C₃ = thirdConstant Λ.response.C₀ (CS 0) Cq Λ.k := ⟨_, rfl⟩
  have hC₃0 : 0 ≤ C₃ := by
    rw [hC₃]
    unfold thirdConstant
    positivity
  have hf0 : ∀ N, 0 ≤ firstConstant CM |CH| c N := fun N => by
    unfold firstConstant
    positivity
  have hs0 : ∀ N, 0 ≤ secondConstant CM |CH| c N := fun N => by
    unfold secondConstant
    positivity
  refine ⟨fun N => firstConstant CM |CH| c N + secondConstant CM |CH| c N + (C₃ + firstConstant CM |CH| c (2 * N + Λ.k)), X₀,
    hX₀ ▸ le_max_left _ _, ?_⟩
  intro S F hx
  have hx1 : 1 ≤ S.scaleCoupling := le_trans (one_le_pow₀ (by norm_num)) (e8.trans hx)
  have hx0 : 0 < S.scaleCoupling := by linarith
  have hW : ∀ (F' : LimitLawAtPoint S) (t : ℕ),
      SubsequenceFacts F'.rule F'.points F'.period t S.logIndex S.scaleCoupling S.range (CS 0) (CN 0) →
      (∀ j' : F'.Index, Integrable (evalAtZero j') F'.law) → ∀ jw : ExtraSlot Λ → F'.Index,
        (∀ e, F'.observables (jw e) = extraObservable e) → _ :=
    fun F' t hq hint jw hjw => window_bounds F' hq jw hjw hc hint
      (fun u j h1 h2 => HH S F' t (eH.trans hx) hq.lastSeparated_eq u j h1 h2)
      (fun u h1 h2 z μ ν hμ hz q j hq1 hj => HM S F' t (eM.trans hx) hq.lastSeparated_eq u h1 h2 z μ ν hμ hz q j hq1 hj)
      (fun p hp J j hJ hj => HQ S F' p hp J j hJ hj)
  refine ⟨fun u hw => ⟨fun N j hj => ?_, fun k j hj => ?_⟩, fun B N j hj => ?_⟩
  · refine bound_in_any_limit h₄ h₅ hSeq S hx F j (fun i w => ?_) fun F' t i₀ ht hq hint jw hjw j' hj' => ?_
    · rw [hj]
      exact (F.points i).notGoodIndicator_nonneg u w
    · have hw₀ := hw i₀
      rw [← ht] at hw₀
      have h := ((hW F' t hq hint jw hjw).1 u hw₀.1 (by omega)).1 N j' (hj'.trans hj)
      filter_upwards [h] with v hv
      refine hv.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have := hs0 N
      have := hf0 (2 * N + Λ.k)
      linarith
  · refine bound_in_any_limit h₄ h₅ hSeq S hx F j (fun i w => ?_) fun F' t i₀ ht hq hint jw hjw j' hj' => ?_
    · rw [hj]
      have : 0 ≤ (F.points i).scaleCoupling := by
        rw [(point_parameters_eq S F i).1]
        exact hx0.le
      exact (F.points i).goodCurvaturePower_nonneg this u k w
    · have hw₀ := hw i₀
      rw [← ht] at hw₀
      have h := ((hW F' t hq hint jw hjw).1 u hw₀.1 (by omega)).2 k j' (hj'.trans hj)
      filter_upwards [h] with v hv
      refine hv.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have := hf0 k
      have := hf0 (2 * k + Λ.k)
      linarith
  · refine bound_in_any_limit h₄ h₅ hSeq S hx F j (fun i w => ?_) fun F' t i₀ ht hq hint jw hjw j' hj' => ?_
    · rw [hj]
      exact (F.points i).badResponseProduct_nonneg B w
    · have h := (hW F' t hq hint jw hjw).2 B N j' (hj'.trans hj)
      filter_upwards [h] with v hv
      refine hv.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      rw [← hC₃]
      have := hf0 N
      have := hs0 N
      linarith
end Final
end YangMills.Construction.MomentLaw
end
