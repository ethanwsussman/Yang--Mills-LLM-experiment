import YangMills.Construction.ClusterExpansionOfAStep.BallsAndBlocksOfATorusForm
import YangMills.Construction.LawByMomentsOfTheFlow.ContractionAtTheWeightsOfThePoint
import YangMills.Construction.LawByMomentsOfTheFlow.ContractionOfTheResponse
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps TorusBalls WeightedResponses RenormalizationStepParameters
section Sites
variable {n : ℕ}
private theorem eq_of_supDist_eq_zero [NeZero n] {x y : TorusSite n} (h : TorusFields.supDist x y = 0) : x = y := by
  funext i
  have h1 := (supDist_le_iff x y 0).1 h.le i
  have h2 : (x i - y i).valMinAbs = 0 := Int.natAbs_eq_zero.1 (Nat.le_zero.1 h1)
  exact sub_eq_zero.1 ((ZMod.valMinAbs_eq_zero _).1 h2)
private theorem supDist_parentBlock_le [NeZero n] {L : ℕ} [NeZero L] (hL : 2 ≤ L) (p q : TorusSite (n * L)) :
    TorusFields.supDist (parentBlock L p) (parentBlock L q) ≤ TorusFields.supDist p q := by
  rcases Nat.eq_zero_or_pos (TorusFields.supDist p q) with h | h
  · rw [eq_of_supDist_eq_zero h, supDist_self]
    exact Nat.zero_le _
  · have h1 := supDist_parentBlock_le_div_add_one L p q
    have h2 : TorusFields.supDist p q / L ≤ TorusFields.supDist p q / 2 := Nat.div_le_div_left hL (by norm_num)
    omega
abbrev _root_.YangMills.SharedProofs.p12740 := @supDist_parentBlock_le
private theorem parentBlock_apply_intCast [NeZero n] {L : ℕ} [NeZero L] (x : TorusSite (n * L)) (i : Fin 4) (N : ℤ)
    (hx : x i = (N : ZMod (n * L))) :
    parentBlock L x i = (((N + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) := by
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  set cp : ℤ := ((x i).cast : ℤ) with hcp
  have hc : ((cp : ℤ) : ZMod (n * L)) = x i := ZMod.intCast_zmod_cast _
  have hdvd : ((n * L : ℕ) : ℤ) ∣ cp - N := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, hc, hx]
  obtain ⟨k, hk⟩ := hdvd
  have h1 : cp + ((L : ℤ) - 1) / 2 = (N + ((L : ℤ) - 1) / 2) + (L : ℤ) * ((n : ℤ) * k) := by
    push_cast at hk
    linear_combination hk
  show (((cp + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) = _
  rw [h1, Int.add_mul_ediv_left _ _ hL]
  push_cast
  simp
private theorem natAbs_round_parentBlock_sub_round_le {L : ℤ} (hL : 2 ≤ L) (w : ℝ) :
    ((round ((L : ℝ) * w) + (L - 1) / 2) / L - round w).natAbs ≤ 1 := by
  obtain ⟨N, hN⟩ : ∃ N, N = round ((L : ℝ) * w) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = round w := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, h = (L - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (N + h) / L := ⟨_, rfl⟩
  rw [← hN, ← hB, ← hh, ← hA]
  have hLpos : 0 < L := by omega
  have h1 : L - 2 ≤ 2 * h := by omega
  have h2 : 2 * h ≤ L - 1 := by omega
  have a1 : L * A ≤ N + h := by rw [hA]; exact Int.mul_ediv_self_le hLpos.ne'
  have a2 : N + h < L * A + L := by rw [hA]; exact Int.lt_mul_ediv_self_add hLpos
  have n1 := abs_sub_round ((L : ℝ) * w)
  have b1 := abs_sub_round w
  rw [← hN, abs_le] at n1
  rw [← hB, abs_le] at b1
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have a1' : (L : ℝ) * A ≤ N + h := by exact_mod_cast a1
  have a2' : (N : ℝ) + h < L * A + L := by exact_mod_cast a2
  have h1' : (L : ℝ) - 2 ≤ 2 * h := by exact_mod_cast h1
  have h2' : 2 * (h : ℝ) ≤ L - 1 := by exact_mod_cast h2
  have e1 : 0 ≤ (L : ℝ) * ((B : ℝ) - w + 1 / 2) := mul_nonneg (by linarith) (by linarith [b1.2])
  have e2 : 0 ≤ (L : ℝ) * (w + 1 / 2 - (B : ℝ)) := mul_nonneg (by linarith) (by linarith [b1.1])
  have up : A - B ≤ 1 := by
    by_contra hc
    have h3 : 2 ≤ A - B := by omega
    have h4 : (2 : ℝ) ≤ (A : ℝ) - B := by exact_mod_cast h3
    have h5 : 0 ≤ (L : ℝ) * ((A : ℝ) - B - 2) := mul_nonneg (by linarith) (by linarith)
    nlinarith [n1.1, n1.2]
  have down : -1 ≤ A - B := by
    by_contra hc
    have h3 : A - B ≤ -2 := by omega
    have h4 : (A : ℝ) - B ≤ -2 := by exact_mod_cast h3
    have h5 : 0 ≤ (L : ℝ) * (-2 - ((A : ℝ) - B)) := mul_nonneg (by linarith) (by linarith)
    nlinarith [n1.1, n1.2]
  omega
private theorem supDist_ancestor_succ_le {L m e : ℕ} [NeZero L] [NeZero n] [NeZero m] (hn : n = m * L ^ e)
    (x : TorusSite (n * L)) (y : TorusSite n) :
    TorusFields.supDist (ancestor L (e + 1) m x) (ancestor L e m y) ≤
      1 + TorusFields.supDist (parentBlock L x) y := by
  rw [supDist_le_iff]
  intro i
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL0
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL0
  obtain ⟨cx, hcx⟩ : ∃ cx : ℤ, cx = ((x i).cast : ℤ) := ⟨_, rfl⟩
  have hcxv : (cx : ℝ) = ((x i).val : ℝ) := by
    rw [hcx, ← ZMod.natCast_val]
    simp
  obtain ⟨Bx, hBx⟩ : ∃ Bx : ℤ, Bx = (cx + ((L : ℤ) - 1) / 2) / (L : ℤ) := ⟨_, rfl⟩
  have hB : parentBlock L x i = ((Bx : ℤ) : ZMod n) := by
    rw [hBx, hcx]
    rfl
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℤ, Δ = (parentBlock L x i - y i).valMinAbs := ⟨_, rfl⟩
  have hΔD : Δ.natAbs ≤ TorusFields.supDist (parentBlock L x) y := by
    rw [hΔ]
    exact Finset.le_sup (f := fun i => ((parentBlock L x i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
  have hΔc : ((Δ : ℤ) : ZMod n) = parentBlock L x i - y i := by
    rw [hΔ]
    exact ZMod.coe_valMinAbs _
  obtain ⟨cy, hcy⟩ : ∃ cy : ℤ, cy = ((y i).val : ℤ) := ⟨_, rfl⟩
  have hcyc : ((cy : ℤ) : ZMod n) = y i := by
    rw [hcy]
    simp
  have hcyv : (cy : ℝ) = ((y i).val : ℝ) := by rw [hcy]; simp
  have hdvd : (n : ℤ) ∣ (Bx - Δ) - cy := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hΔc, hcyc, hB]
    ring
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ℤ, r₁ = round (((x i).val : ℝ) / (L : ℝ) ^ (e + 1)) := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r₂ : ℤ, r₂ = round (((y i).val : ℝ) / (L : ℝ) ^ e) := ⟨_, rfl⟩
  have hcast : ancestor L (e + 1) m x i - ancestor L e m y i =
      ((r₁ - r₂ - (m : ℤ) * k : ℤ) : ZMod m) := by
    show (((round (((x i).val : ℝ) / (L : ℝ) ^ (e + 1)) : ℤ)) : ZMod m) -
      (((round (((y i).val : ℝ) / (L : ℝ) ^ e) : ℤ)) : ZMod m) = _
    rw [← hr₁, ← hr₂]
    push_cast
    simp
  rw [hcast]
  refine (natAbs_valMinAbs_intCast_le _).trans ?_
  have b1 := abs_sub_round (((x i).val : ℝ) / (L : ℝ) ^ (e + 1))
  have b2 := abs_sub_round (((y i).val : ℝ) / (L : ℝ) ^ e)
  rw [← hr₁, abs_le] at b1
  rw [← hr₂, abs_le] at b2
  rw [← hcxv] at b1
  rw [← hcyv] at b2
  have hP : (0 : ℝ) < (L : ℝ) ^ e := pow_pos hLr e
  have hP1 : (1 : ℝ) ≤ (L : ℝ) ^ e := one_le_pow₀ hL1
  have a1 : (L : ℤ) * Bx ≤ cx + ((L : ℤ) - 1) / 2 := by rw [hBx]; exact Int.mul_ediv_self_le hLz.ne'
  have a2 : cx + ((L : ℤ) - 1) / 2 < (L : ℤ) * Bx + L := by rw [hBx]; exact Int.lt_mul_ediv_self_add hLz
  have g1 : 0 ≤ ((L : ℤ) - 1) / 2 := by omega
  have hv1 : -(L : ℤ) < cx - (L : ℤ) * Bx := by omega
  have hv2 : cx - (L : ℤ) * Bx < L := by omega
  have hv1' : -(L : ℝ) < (cx : ℝ) - L * Bx := by exact_mod_cast hv1
  have hv2' : (cx : ℝ) - L * Bx < L := by exact_mod_cast hv2
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = (cx : ℝ) / L - Bx := ⟨_, rfl⟩
  have hvabs : |v| < 1 := by
    have e0 : v = ((cx : ℝ) - L * Bx) / L := by rw [hv]; field_simp
    rw [e0, abs_lt]
    constructor
    · rw [lt_div_iff₀ hLr]; linarith
    · rw [div_lt_iff₀ hLr]; linarith
  have hk' : ((Bx : ℝ) - Δ) - cy = (n : ℝ) * k := by exact_mod_cast hk
  have hnr : (n : ℝ) = (m : ℝ) * (L : ℝ) ^ e := by rw [hn]; push_cast; ring
  have hdiff : (cx : ℝ) / (L : ℝ) ^ (e + 1) - (cy : ℝ) / (L : ℝ) ^ e - (m : ℝ) * k = (v + Δ) / (L : ℝ) ^ e := by
    have e1 : (cy : ℝ) = (Bx : ℝ) - Δ - (m : ℝ) * (L : ℝ) ^ e * k := by rw [← hnr]; linarith
    rw [e1, hv, pow_succ]
    field_simp
    ring
  have hsmall : |(v + (Δ : ℝ)) / (L : ℝ) ^ e| < 1 + |(Δ : ℝ)| := by
    rw [abs_div, abs_of_pos hP]
    calc |v + (Δ : ℝ)| / (L : ℝ) ^ e ≤ |v + (Δ : ℝ)| := div_le_self (abs_nonneg _) hP1
      _ ≤ |v| + |(Δ : ℝ)| := abs_add_le _ _
      _ < 1 + |(Δ : ℝ)| := by linarith
  have hT : |((r₁ - r₂ - (m : ℤ) * k : ℤ) : ℝ)| < 2 + |(Δ : ℝ)| := by
    rw [abs_lt] at hsmall ⊢
    push_cast
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, hsmall.1, hsmall.2]
  have hT' : |r₁ - r₂ - (m : ℤ) * k| < 2 + |Δ| := by exact_mod_cast hT
  have h3 : (((r₁ - r₂ - (m : ℤ) * k).natAbs : ℕ) : ℤ) < 2 + ((Δ.natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs]
    exact hT'
  omega
end Sites
section Slow
variable {n : ℕ} [NeZero n]
private theorem exp_mul_le_exp_mul_add {c a b D : ℝ} (hc : 0 ≤ c) (h : a ≤ b + 1 + D) :
    Real.exp (c * a) ≤ Real.exp (c * (1 + D)) * Real.exp (c * b) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_left h hc]
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem supDist_parentBlock_originSite_le (hL : 2 ≤ Λ.stepParams.side) (u : ℕ) :
    TorusFields.supDist (parentBlock Λ.stepParams.side (S.originSite u (n * Λ.stepParams.side)))
      (S.originSite (u + 1) n) ≤ 1 := by
  rw [supDist_le_iff]
  intro i
  have hLr : ((Λ.stepParams.side : ℕ) : ℝ) ≠ 0 := by
    have : 0 < Λ.stepParams.side := by omega
    positivity
  have e : S.data.center i * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ u =
      (((Λ.stepParams.side : ℤ) : ℝ)) *
        (S.data.center i * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ (u + 1)) := by
    push_cast
    rw [pow_succ]
    field_simp
  rw [parentBlock_apply_intCast _ i
    (round (S.data.center i * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ u)) rfl]
  show (((_ : ℤ) : ZMod n) - ((round (S.data.center i * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel /
    (Λ.stepParams.side : ℝ) ^ (u + 1)) : ℤ) : ZMod n)).valMinAbs.natAbs ≤ 1
  rw [← Int.cast_sub]
  refine (natAbs_valMinAbs_intCast_le _).trans ?_
  rw [e]
  exact natAbs_round_parentBlock_sub_round_le (by exact_mod_cast hL) _
abbrev _root_.YangMills.SharedProofs.p66617 := @supDist_parentBlock_originSite_le
private theorem isSlowlyVaryingPair_distanceWeight (hL : 2 ≤ Λ.stepParams.side)
    (hr : 0 ≤ Λ.stepParams.weightRate / 8) (u : ℕ) :
    IsSlowlyVaryingPair Λ.stepParams.side (Λ.stepParams.weightRate / 8)
      (S.distanceWeight u (n * Λ.stepParams.side)) (S.distanceWeight (u + 1) n) := by
  intro p p'
  have h1 : TorusFields.supDist p'.1 (S.originSite (u + 1) n) ≤
      TorusFields.supDist (parentBlock Λ.stepParams.side p.1) p'.1 +
        (TorusFields.supDist p.1 (S.originSite u (n * Λ.stepParams.side)) + 1) := by
    have t1 := supDist_triangle p'.1 (parentBlock Λ.stepParams.side p.1) (S.originSite (u + 1) n)
    have t2 := supDist_triangle (parentBlock Λ.stepParams.side p.1)
      (parentBlock Λ.stepParams.side (S.originSite u (n * Λ.stepParams.side))) (S.originSite (u + 1) n)
    have t3 := supDist_parentBlock_le hL p.1 (S.originSite u (n * Λ.stepParams.side))
    have t4 := supDist_parentBlock_originSite_le (n := n) S hL u
    have t5 := supDist_comm p'.1 (parentBlock Λ.stepParams.side p.1)
    omega
  have h1' : (TorusFields.supDist p'.1 (S.originSite (u + 1) n) : ℝ) ≤
      (TorusFields.supDist (parentBlock Λ.stepParams.side p.1) p'.1 : ℝ) +
        ((TorusFields.supDist p.1 (S.originSite u (n * Λ.stepParams.side)) : ℝ) + 1) := by
    exact_mod_cast h1
  have key := exp_mul_le_exp_mul_add (c := Λ.stepParams.weightRate / 8)
    (a := -max 0 ((TorusFields.supDist p.1 (S.originSite u (n * Λ.stepParams.side)) : ℝ) - (S.radius : ℝ)))
    (b := -max 0 ((TorusFields.supDist p'.1 (S.originSite (u + 1) n) : ℝ) - (S.radius : ℝ)))
    (D := (TorusFields.supDist (parentBlock Λ.stepParams.side p.1) p'.1 : ℝ)) hr (by
      have m1 : max 0 ((TorusFields.supDist p'.1 (S.originSite (u + 1) n) : ℝ) - (S.radius : ℝ)) ≤
          max 0 ((TorusFields.supDist p.1 (S.originSite u (n * Λ.stepParams.side)) : ℝ) - (S.radius : ℝ)) + 1 +
            (TorusFields.supDist (parentBlock Λ.stepParams.side p.1) p'.1 : ℝ) := by
        have m2 := le_max_left 0
          ((TorusFields.supDist p.1 (S.originSite u (n * Λ.stepParams.side)) : ℝ) - (S.radius : ℝ))
        have m3 := le_max_right 0
          ((TorusFields.supDist p.1 (S.originSite u (n * Λ.stepParams.side)) : ℝ) - (S.radius : ℝ))
        exact max_le (by linarith) (by linarith)
      linarith)
  simpa only [MomentPoint.distanceWeight, mul_neg] using key
private theorem isSlowlyVaryingPair_finsetDist {L : ℕ} [NeZero L] (hL : 2 ≤ L) {c : ℝ} (hc : 0 ≤ c)
    (A : Finset (TorusSite (n * L))) (A' : Finset (TorusSite n)) (hA : A.Nonempty)
    (hAA : ∀ z ∈ A, parentBlock L z ∈ A') :
    IsSlowlyVaryingPair (n := n) L c (fun p => Real.exp (-(c * (finsetDist A p.1 : ℝ))))
      (fun p => Real.exp (-(c * (finsetDist A' p.1 : ℝ)))) := by
  intro p p'
  have hne : ((fun z => TorusFields.supDist p.1 z) '' (A : Set (TorusSite (n * L)))).Nonempty :=
    (Finset.coe_nonempty.2 hA).image _
  obtain ⟨z, hz, hzd⟩ := Nat.sInf_mem hne
  have h1 : finsetDist A' p'.1 ≤ TorusFields.supDist (parentBlock L p.1) p'.1 + finsetDist A p.1 := by
    have h2 : finsetDist A' p'.1 ≤ TorusFields.supDist p'.1 (parentBlock L z) :=
      Nat.sInf_le ⟨parentBlock L z, hAA z hz, rfl⟩
    have t1 := supDist_triangle p'.1 (parentBlock L p.1) (parentBlock L z)
    have t2 := supDist_parentBlock_le hL p.1 z
    have t3 := supDist_comm p'.1 (parentBlock L p.1)
    have t4 : TorusFields.supDist p.1 z = finsetDist A p.1 := hzd
    omega
  have h1' : (finsetDist A' p'.1 : ℝ) ≤ (TorusFields.supDist (parentBlock L p.1) p'.1 : ℝ) + (finsetDist A p.1 : ℝ) := by
    exact_mod_cast h1
  have key := exp_mul_le_exp_mul_add (c := c) (a := -(finsetDist A p.1 : ℝ)) (b := -(finsetDist A' p'.1 : ℝ))
    (D := (TorusFields.supDist (parentBlock L p.1) p'.1 : ℝ)) hc (by linarith)
  simpa only [mul_neg] using key
private theorem isSlowlyVaryingPair_ancestor {L : ℕ} [NeZero L] {c : ℝ} (hc : 0 ≤ c) (e m : ℕ) [NeZero m]
    (b : TorusSite m) (hn : n = m * L ^ e) :
    IsSlowlyVaryingPair (n := n) L c (fun p => Real.exp (c * (TorusFields.supDist (ancestor L (e + 1) m p.1) b : ℝ)))
      (fun p => Real.exp (c * (TorusFields.supDist (ancestor L e m p.1) b : ℝ))) := by
  intro p p'
  have h1 : TorusFields.supDist (ancestor L (e + 1) m p.1) b ≤
      TorusFields.supDist (ancestor L e m p'.1) b + 1 + TorusFields.supDist (parentBlock L p.1) p'.1 := by
    have t1 := supDist_triangle (ancestor L (e + 1) m p.1) (ancestor L e m p'.1) b
    have t2 := supDist_ancestor_succ_le hn p.1 p'.1
    omega
  have h1' : (TorusFields.supDist (ancestor L (e + 1) m p.1) b : ℝ) ≤
      (TorusFields.supDist (ancestor L e m p'.1) b : ℝ) + 1 +
        (TorusFields.supDist (parentBlock L p.1) p'.1 : ℝ) := by
    exact_mod_cast h1
  exact exp_mul_le_exp_mul_add hc h1'
omit [NeZero n] in
private theorem isSlowlyVaryingPair_one {L : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    IsSlowlyVaryingPair L c (fun _ : TorusPlaquette (n * L) => 1) (fun _ : TorusPlaquette n => 1) := by
  intro p p'
  rw [mul_one]
  exact Real.one_le_exp (mul_nonneg hc (by linarith))
end Slow
section Descent
variable {n : ℕ} [NeZero n]
private theorem measurable_pushColours {a ρA : ℝ} {L u : ℕ} [NeZero L] {Ω : Type} [MeasurableSpace Ω]
    {X : Ω → ColourForm n} (hX : Measurable X) : Measurable fun e => pushColours a ρA L u (X e) := by
  refine measurable_pi_iff.2 fun c => measurable_pi_iff.2 fun b => ?_
  show Measurable fun e => ∑ c' : TorusBond n, responseKernel a ρA L u b c' * X e c c'
  refine Finset.measurable_sum _ fun c' _ => ?_
  exact ((measurable_pi_apply c').comp ((measurable_pi_apply c).comp hX)).const_mul _
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem weightedCurvatureNorm_descend_le {θ : ℝ} (hθ : 0 ≤ θ) (hL : 1 ≤ Λ.stepParams.side)
    (step : ∀ (u n : ℕ) [NeZero n], 64 ≤ n → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm n)
      (q : ENNReal), 1 ≤ q → Measurable X →
      weightedCurvatureNorm μ (S.distanceWeight u (n * Λ.stepParams.side)) q
          (fun e => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u (X e)) ≤
        ENNReal.ofReal θ * weightedCurvatureNorm μ (S.distanceWeight (u + 1) n) q X) (d : ℕ) :
    ∀ (n : ℕ) [NeZero n], 64 ≤ n → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm n)
      (q : ENNReal), 1 ≤ q → Measurable X →
      weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (fineSide Λ.stepParams.side d n)) q
          (fun e => descend Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d n (X e)) ≤
        ENNReal.ofReal (θ ^ d) * weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) q X := by
  induction d with
  | zero =>
    intro n _ _ Ω _ μ X q _ _
    simp only [pow_zero, ENNReal.ofReal_one, one_mul]
    exact le_rfl
  | succ d ih =>
    intro n _ h64 Ω _ μ X q hq hX
    have h1 := ih (n * Λ.stepParams.side) (le_trans h64 (Nat.le_mul_of_pos_right n hL)) Ω μ
      (fun e => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d) (X e))
      q hq (measurable_pushColours hX)
    have h2 := step (S.lastSeparated + d) n h64 Ω μ X q hq hX
    refine le_trans (show _ ≤ _ from h1) ?_
    refine le_trans (mul_le_mul_right h2 _) ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hθ d), pow_succ]
    exact le_rfl
end Descent
theorem weightContraction_of_responseContraction (h : responseContractionStatement) :
    weightContractionStatement := by
  unfold weightContractionStatement ForAllPoints ForAllParameters
  intro a ha
  obtain ⟨Cw, hCw, L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L hodd hL₀ Tb hTa hTL hD hCS hCH hrt' hCder Kr hKr
  obtain ⟨hθ, y₀, hy⟩ := H L hodd hL₀ Tb hTa hTL hD hCS hCH hrt' hCder
  subst hTL
  refine ⟨y₀, fun y hy₀ hR hW g _ _ k _ _ _ R d _ => ?_⟩
  refine ⟨fun _ => Cw, 1, y, one_pos, le_rfl, fun S => ?_⟩
  have hL2 : 2 ≤ Tb.side := le_trans (by norm_num) hD.L_ge
  have hr : 0 ≤ (Tb.stepParameters y).weightRate / 8 := by
    have := hD.rt_pos
    show 0 ≤ Tb.rt / 2 ^ 10 / 8
    positivity
  have hLpos : (0 : ℝ) < (Tb.side : ℝ) := by
    have : 0 < Tb.side := by omega
    exact_mod_cast this
  have hθ0 : 0 ≤ Cw * (Tb.side : ℝ) ^ (-(1 / 2) : ℝ) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hLpos.le _)
  refine ⟨hCw.le, hθ, fun u n _ => isSlowlyVaryingPair_distanceWeight S hL2 hr u,
    fun n _ A A' hA hAA => isSlowlyVaryingPair_finsetDist hL2 hr A A' hA hAA,
    fun e n m _ _ b hn => isSlowlyVaryingPair_ancestor hr e m b hn, fun n _ => isSlowlyVaryingPair_one hr, ?_⟩
  intro d n _ h64 Ω _ μ X q hq hX
  refine weightedCurvatureNorm_descend_le S hθ0 (show 1 ≤ Tb.side by omega)
    (fun u n _ h64 Ω _ μ X q hq hX => ?_) d n h64 Ω μ X q hq hX
  exact hy y hy₀ hR hW u n h64 _ _ (fun p => Real.exp_pos _) (fun p => Real.exp_pos _)
    (isSlowlyVaryingPair_distanceWeight S hL2 hr u) Ω μ X q hq hX
end YangMills.Construction.MomentLaw
end
