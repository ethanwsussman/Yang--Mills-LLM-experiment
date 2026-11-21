import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.RunningCouplingSlope.MomentOfASumOfForms
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
open YangMills.Construction.TorusLumps YangMills.Construction.SlopeCoefficient
open Classical
namespace YangMills.Construction.RunningCouplingSlope
set_option linter.unusedSectionVars false
variable {n : ℕ} [NeZero n] {r : ℕ}
private lemma valMinAbs_eq_of_cast {x : ZMod n} {k : ℤ} (hx : x = (k : ZMod n)) (h1 : -(n : ℤ) < k * 2)
    (h2 : k * 2 ≤ n) : x.valMinAbs = k :=
  (ZMod.valMinAbs_spec x k).2 ⟨hx, h1, h2⟩
private lemma natAbs_coord_le_supDist (a : TorusSite n) (i : Fin 4) :
    ((a i).valMinAbs).natAbs ≤ _root_.YangMills.Construction.TorusFields.supDist 0 a := by
  have h := Finset.le_sup (f := fun i => (((0 : TorusSite n) i - a i).valMinAbs).natAbs)
    (Finset.mem_univ i)
  simpa [_root_.YangMills.Construction.TorusFields.supDist, ZMod.natAbs_valMinAbs_neg] using h
private lemma supDist_zero_le_of_coord {a : TorusSite n} {s : ℕ} (h : ∀ i, ((a i).valMinAbs).natAbs ≤ s) :
    _root_.YangMills.Construction.TorusFields.supDist 0 a ≤ s := by
  unfold _root_.YangMills.Construction.TorusFields.supDist
  refine Finset.sup_le fun i _ => ?_
  simpa [ZMod.natAbs_valMinAbs_neg] using h i
private lemma supDist_add_unitStep_le (hn : 64 ≤ n) (x : TorusSite n) (μ : Fin 4) :
    _root_.YangMills.Construction.TorusFields.supDist 0 (x + TorusFields.unitStep n μ) ≤ _root_.YangMills.Construction.TorusFields.supDist 0 x + 1 := by
  refine supDist_zero_le_of_coord fun i => ?_
  have hx := natAbs_coord_le_supDist x i
  by_cases hi : i = μ
  · subst hi
    have h1 : ((1 : ZMod n)).valMinAbs = 1 := valMinAbs_eq_of_cast (by simp) (by omega) (by omega)
    have h2 := ZMod.natAbs_valMinAbs_add_le (x i) 1
    rw [h1] at h2
    simp only [Pi.add_apply, TorusFields.unitStep, Pi.single_eq_same]
    omega
  · have h3 : (x + TorusFields.unitStep n μ) i = x i := by simp [TorusFields.unitStep, hi]
    rw [h3]
    omega
private lemma le_supDist_of_not_nearOrigin (hn : 64 ≤ n) {b : TorusBond n} (hb : ¬ IsNearOriginBond r b) :
    r ≤ _root_.YangMills.Construction.TorusFields.supDist 0 b.1 := by
  by_contra hlt
  rw [not_le] at hlt
  exact hb ⟨hlt.le, (supDist_add_unitStep_le hn b.1 b.2).trans (by omega)⟩
private lemma abs_intCast_le_of_natAbs_le {k : ℤ} {s : ℕ} (h : k.natAbs ≤ s) : |(k : ℝ)| ≤ (s : ℝ) := by
  have h1 : |(k : ℝ)| = ((k.natAbs : ℕ) : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h1]
  exact_mod_cast h
private def truncatedSecondCoord (r : ℕ) (x : TorusSite n) : ℝ :=
  if _root_.YangMills.Construction.TorusFields.supDist 0 x ≤ r then (((x secondAxis).valMinAbs : ℤ) : ℝ) else 0
private lemma abs_truncatedSecondCoord_le (r : ℕ) (x : TorusSite n) : |truncatedSecondCoord r x| ≤ r := by
  unfold truncatedSecondCoord
  split_ifs with hx
  · exact abs_intCast_le_of_natAbs_le ((natAbs_coord_le_supDist x secondAxis).trans hx)
  · simp
private lemma abs_siteGradient_truncated_le (r : ℕ) (b : TorusBond n) :
    |siteGradient (truncatedSecondCoord r) b| ≤ 2 * (r : ℝ) := by
  unfold siteGradient
  have h1 := abs_truncatedSecondCoord_le r (b.1 + TorusFields.unitStep n b.2)
  have h2 := abs_truncatedSecondCoord_le r b.1
  have h3 := abs_sub (truncatedSecondCoord r (b.1 + TorusFields.unitStep n b.2)) (truncatedSecondCoord r b.1)
  linarith
private lemma siteGradient_truncated_of_near (hn : 64 ≤ n) (hr : 16 * r ≤ n) {b : TorusBond n}
    (hb : IsNearOriginBond r b) :
    siteGradient (truncatedSecondCoord r) b = if b.2 = secondAxis then 1 else 0 := by
  obtain ⟨x, μ⟩ := b
  obtain ⟨h1, h2⟩ := hb
  simp only at h1 h2
  unfold siteGradient truncatedSecondCoord
  simp only [if_pos h1, if_pos h2]
  have hx := natAbs_coord_le_supDist x secondAxis
  by_cases hμ : μ = secondAxis
  · subst hμ
    have h3 : ((x + TorusFields.unitStep n secondAxis) secondAxis).valMinAbs =
        (x secondAxis).valMinAbs + 1 :=
      valMinAbs_eq_of_cast (by simp [TorusFields.unitStep]) (by omega) (by omega)
    rw [h3]
    push_cast
    simp
  · have h3 : (x + TorusFields.unitStep n μ) secondAxis = x secondAxis := by
      simp [TorusFields.unitStep, Ne.symm hμ]
    rw [h3]
    simp [hμ]
private lemma sum_bonds_eq_sum_secondAxis (f : TorusBond n → ℝ)
    (hf : ∀ x μ, μ ≠ secondAxis → f (x, μ) = 0) :
    ∑ c, f c = ∑ x, f (x, secondAxis) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Finset.sum_eq_single secondAxis (fun μ _ hμ => hf x μ hμ) (by simp)
private def firstCoord (a : TorusSite n) : ℝ := (((a 0).valMinAbs : ℤ) : ℝ)
private def IsNearPair (r : ℕ) (a b : TorusSite n) : Prop :=
  IsNearOriginBond r (a, secondAxis) ∧ IsNearOriginBond r (b, secondAxis)
private def crossTerm (r : ℕ) (G : TorusBond n → TorusBond n → ℝ) (a b : TorusSite n) : ℝ :=
  if IsNearPair r a b then G (a, secondAxis) (b, secondAxis) * firstCoord a * firstCoord b
  else 0
private lemma formOnLinearPotential_eq_sum_crossTerm (r : ℕ) (G : TorusBond n → TorusBond n → ℝ) :
    formOnLinearPotential r G = ∑ a : TorusSite n, ∑ b : TorusSite n, crossTerm r G a b := by
  unfold formOnLinearPotential
  rw [sum_bonds_eq_sum_secondAxis]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_bonds_eq_sum_secondAxis]
    · refine Finset.sum_congr rfl fun b _ => ?_
      unfold crossTerm IsNearPair
      by_cases hN : IsNearOriginBond r (a, secondAxis) ∧ IsNearOriginBond r (b, secondAxis)
      · simp only [if_pos hN]
        simp [linearPotential, firstCoord]
      · simp only [if_neg hN]
    · intro x μ hμ
      simp [linearPotential, hμ]
  · intro x μ hμ
    refine Finset.sum_eq_zero fun c' _ => ?_
    simp [linearPotential, hμ]
private lemma sum_near_eq_neg_sum_far (hn : 64 ≤ n) (hr : 16 * r ≤ n) {M₀ v : ℝ}
    {H : TorusSite n → TorusBond n → TorusBond n → ℝ} (hH : IsDecayingFormFamily M₀ v H) (c : TorusBond n) :
    ∑ x : TorusSite n, (if IsNearOriginBond r (x, secondAxis) then H 0 (x, secondAxis) c else 0) =
      - ∑ e : TorusBond n, if IsNearOriginBond r e then 0 else H 0 e c * siteGradient (truncatedSecondCoord r) e := by
  have h0 := hH.vanish_on_gradient 0 (truncatedSecondCoord r) c
  have h1 : ∀ e : TorusBond n, H 0 e c * siteGradient (truncatedSecondCoord r) e =
      (if IsNearOriginBond r e ∧ e.2 = secondAxis then H 0 e c else 0) +
        (if IsNearOriginBond r e then 0 else H 0 e c * siteGradient (truncatedSecondCoord r) e) := by
    intro e
    by_cases he : IsNearOriginBond r e
    · rw [siteGradient_truncated_of_near hn hr he]
      by_cases hd : e.2 = secondAxis <;> simp [he, hd]
    · simp [he]
  have h2 : ∑ e : TorusBond n, (if IsNearOriginBond r e ∧ e.2 = secondAxis then H 0 e c else 0) =
      ∑ x : TorusSite n, if IsNearOriginBond r (x, secondAxis) then H 0 (x, secondAxis) c else 0 := by
    rw [sum_bonds_eq_sum_secondAxis _ (fun x μ hμ => by simp [hμ])]
    simp
  rw [Finset.sum_congr rfl (fun e _ => h1 e), Finset.sum_add_distrib, h2] at h0
  linarith
private def momentWeight (r : ℕ) (w : TorusSite n) : ℝ :=
  if _root_.YangMills.Construction.TorusFields.supDist 0 w ≤ 2 * r then (((w 0).valMinAbs : ℤ) : ℝ) ^ 2 else 0
private lemma kernelSecondMoment_eq_sum (H : TorusSite n → TorusBond n → TorusBond n → ℝ)
    (hc : ∀ (Y u : TorusSite n) (c c' : TorusBond n),
      H (Y + u) (c.1 + u, c.2) (c'.1 + u, c'.2) = H Y c c') :
    kernelSecondMoment (fun c c' => ∑ Y, H Y c c') = -(1 / 2) * ∑ a : TorusSite n, ∑ b : TorusSite n,
      momentWeight (momentCutoff n) (b - a) * H 0 (a, secondAxis) (b, secondAxis) := by
  unfold kernelSecondMoment
  congr 1
  have h1 : ∀ y : TorusSite n, (if _root_.YangMills.Construction.TorusFields.supDist 0 y ≤ 2 * momentCutoff n then
      ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 * ∑ Y, H Y (0, secondAxis) (y, secondAxis) else 0) =
      ∑ Y, momentWeight (momentCutoff n) y * H Y (0, secondAxis) (y, secondAxis) := by
    intro y
    rw [← Finset.mul_sum]
    unfold momentWeight firstCoordDiff
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun y _ => h1 y), Finset.sum_comm]
  refine Fintype.sum_equiv (Equiv.neg _) _ _ fun Y => ?_
  refine Fintype.sum_equiv (Equiv.subRight Y) _ _ fun y => ?_
  have h2 := hc 0 Y (-Y, secondAxis) (y - Y, secondAxis)
  simp only [zero_add, neg_add_cancel, sub_add_cancel] at h2
  simp only [Equiv.neg_apply, Equiv.subRight_apply, sub_neg_eq_add, sub_add_cancel, h2]
private lemma momentWeight_of_near (hn : 64 ≤ n) (hr : 16 * r ≤ n) {a b : TorusSite n}
    (ha : _root_.YangMills.Construction.TorusFields.supDist 0 a ≤ r) (hb : _root_.YangMills.Construction.TorusFields.supDist 0 b ≤ r) :
    momentWeight r (b - a) = (firstCoord b - firstCoord a) ^ 2 := by
  have hsub : ∀ i, ((b - a) i).valMinAbs = (b i).valMinAbs - (a i).valMinAbs := by
    intro i
    have h1 := (natAbs_coord_le_supDist a i).trans ha
    have h2 := (natAbs_coord_le_supDist b i).trans hb
    exact valMinAbs_eq_of_cast (by simp) (by omega) (by omega)
  have hd : _root_.YangMills.Construction.TorusFields.supDist 0 (b - a) ≤ 2 * r := by
    refine supDist_zero_le_of_coord fun i => ?_
    have h1 := (natAbs_coord_le_supDist a i).trans ha
    have h2 := (natAbs_coord_le_supDist b i).trans hb
    rw [hsub i]
    omega
  unfold momentWeight firstCoord
  rw [if_pos hd, hsub 0]
  push_cast
  ring
private lemma momentWeight_nonneg (r : ℕ) (w : TorusSite n) : 0 ≤ momentWeight r w := by
  unfold momentWeight
  split_ifs
  · positivity
  · exact le_rfl
private lemma momentWeight_le (r : ℕ) (w : TorusSite n) : momentWeight r w ≤ 4 * (r : ℝ) ^ 2 := by
  unfold momentWeight
  split_ifs with hw
  · have h1 := abs_intCast_le_of_natAbs_le ((natAbs_coord_le_supDist w 0).trans hw)
    have h2 : (((w 0).valMinAbs : ℤ) : ℝ) ^ 2 ≤ ((2 * r : ℕ) : ℝ) ^ 2 := sq_le_sq' (by
      have := (abs_le.1 h1).1
      linarith) (abs_le.1 h1).2
    push_cast at h2
    nlinarith
  · positivity
private lemma cube_mul_exp_le {v : ℝ} (hv : 0 < v) (h D s t : ℕ) (hD : h ≤ D) (hs : s ≤ D) (ht : t ≤ D) :
    (h : ℝ) ^ 3 * Real.exp (-(v * D)) ≤
      384 / v ^ 3 * Real.exp (-(v * h / 2)) *
        (Real.exp (-(v / 8 * s)) * Real.exp (-(v / 8 * t))) := by
  have hD' : (h : ℝ) ≤ D := by exact_mod_cast hD
  have hs' : (s : ℝ) ≤ D := by exact_mod_cast hs
  have ht' : (t : ℝ) ≤ D := by exact_mod_cast ht
  have e1 : Real.exp (-(v * D)) =
      Real.exp (-(v * D / 4)) * Real.exp (-(v * D / 2)) * Real.exp (-(v * D / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have b1 : (h : ℝ) ^ 3 * Real.exp (-(v * D / 4)) ≤ 384 / v ^ 3 := by
    have hx : 0 ≤ v * h / 4 := by positivity
    have h1 := Real.pow_div_factorial_le_exp _ hx 3
    have h2 : Real.exp (-(v * D / 4)) ≤ Real.exp (-(v * h / 4)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h3 : Real.exp (v * h / 4) * Real.exp (-(v * h / 4)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hp : 0 < Real.exp (-(v * h / 4)) := Real.exp_pos _
    have hc : 0 < 384 / v ^ 3 := by positivity
    calc (h : ℝ) ^ 3 * Real.exp (-(v * D / 4)) ≤ (h : ℝ) ^ 3 * Real.exp (-(v * h / 4)) := by gcongr
      _ = 384 / v ^ 3 * ((v * h / 4) ^ 3 / (Nat.factorial 3 : ℕ) * Real.exp (-(v * h / 4))) := by
          simp only [Nat.factorial]
          field_simp
          norm_num
          ring
      _ ≤ 384 / v ^ 3 * (Real.exp (v * h / 4) * Real.exp (-(v * h / 4))) := by gcongr
      _ = 384 / v ^ 3 := by rw [h3, mul_one]
  have b2 : Real.exp (-(v * D / 2)) ≤ Real.exp (-(v * h / 2)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have b3 : Real.exp (-(v * D / 4)) ≤ Real.exp (-(v / 8 * s)) * Real.exp (-(v / 8 * t)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  rw [e1]
  calc (h : ℝ) ^ 3 * (Real.exp (-(v * D / 4)) * Real.exp (-(v * D / 2)) * Real.exp (-(v * D / 4)))
      = ((h : ℝ) ^ 3 * Real.exp (-(v * D / 4))) * Real.exp (-(v * D / 2)) * Real.exp (-(v * D / 4)) := by
        ring
    _ ≤ 384 / v ^ 3 * Real.exp (-(v * h / 2)) *
        (Real.exp (-(v / 8 * s)) * Real.exp (-(v / 8 * t))) := by
        gcongr
private def intExpSum (u : ℝ) : ℝ := ∑' k : ℤ, Real.exp (-(u * (k.natAbs : ℝ)))
private lemma intExpSum_nonneg (u : ℝ) : 0 ≤ intExpSum u :=
  tsum_nonneg fun _ => (Real.exp_pos _).le
private lemma summable_exp_natAbs {u : ℝ} (hu : 0 < u) :
    Summable fun k : ℤ => Real.exp (-(u * (k.natAbs : ℝ))) := by apply _root_.YangMills.SharedProofs.p17292 <;> assumption
private lemma sum_zmod_exp_le {u : ℝ} (hu : 0 < u) :
    ∑ x : ZMod n, Real.exp (-(u * (x.valMinAbs.natAbs : ℝ))) ≤ intExpSum u := by
  have h1 : ∑ x : ZMod n, Real.exp (-(u * (x.valMinAbs.natAbs : ℝ))) =
      ∑ k ∈ Finset.univ.image (ZMod.valMinAbs : ZMod n → ℤ), Real.exp (-(u * (k.natAbs : ℝ))) :=
    (Finset.sum_image (f := fun k : ℤ => Real.exp (-(u * (k.natAbs : ℝ))))
      (ZMod.injective_valMinAbs.injOn)).symm
  rw [h1]
  exact (summable_exp_natAbs hu).sum_le_tsum _ fun _ _ => (Real.exp_pos _).le
abbrev _root_.YangMills.DeltaSharedProofs.p501961 := @sum_zmod_exp_le
private lemma sum_torusSite_exp_le {u : ℝ} (hu : 0 < u) :
    ∑ a : TorusSite n, Real.exp (-(4 * u * (_root_.YangMills.Construction.TorusFields.supDist 0 a : ℝ))) ≤ intExpSum u ^ 4 := by
  calc ∑ a : TorusSite n, Real.exp (-(4 * u * (_root_.YangMills.Construction.TorusFields.supDist 0 a : ℝ)))
      ≤ ∑ a : TorusSite n, ∏ i, Real.exp (-(u * (((a i).valMinAbs.natAbs : ℕ) : ℝ))) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [← Real.exp_sum]
        refine Real.exp_le_exp.2 ?_
        have hi : ∀ i, (((a i).valMinAbs.natAbs : ℕ) : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist 0 a : ℝ) := fun i => by
          exact_mod_cast natAbs_coord_le_supDist a i
        simp only [Fin.sum_univ_four]
        nlinarith [hi 0, hi 1, hi 2, hi 3]
    _ = (∑ x : ZMod n, Real.exp (-(u * (x.valMinAbs.natAbs : ℝ)))) ^ 4 :=
        (Fintype.sum_pow (fun x : ZMod n => Real.exp (-(u * (x.valMinAbs.natAbs : ℝ)))) 4).symm
    _ ≤ intExpSum u ^ 4 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) (sum_zmod_exp_le hu) 4
private def siteDecay (v : ℝ) (a : TorusSite n) : ℝ := Real.exp (-(v / 8 * (_root_.YangMills.Construction.TorusFields.supDist 0 a : ℝ)))
private lemma siteDecay_nonneg (v : ℝ) (a : TorusSite n) : 0 ≤ siteDecay v a := (Real.exp_pos _).le
private lemma sum_siteDecay_le {v : ℝ} (hv : 0 < v) :
    ∑ a : TorusSite n, siteDecay v a ≤ intExpSum (v / 32) ^ 4 := by
  have h1 := sum_torusSite_exp_le (n := n) (u := v / 32) (by positivity)
  have h2 : 4 * (v / 32) = v / 8 := by ring
  rw [h2] at h1
  exact h1
private lemma sum_siteDecay_nonneg (v : ℝ) : 0 ≤ ∑ a : TorusSite n, siteDecay v a :=
  Finset.sum_nonneg fun a _ => siteDecay_nonneg v a
private lemma supDist_le_supportDiam_left (c c' : TorusBond n) : _root_.YangMills.Construction.TorusFields.supDist 0 c.1 ≤ supportDiam 0 ![c, c'] := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.supDist_le_supportDiam_first <;> assumption
private lemma supDist_le_supportDiam_right (c c' : TorusBond n) : _root_.YangMills.Construction.TorusFields.supDist 0 c'.1 ≤ supportDiam 0 ![c, c'] := by
  unfold supportDiam
  refine le_max_of_le_left ?_
  exact Finset.le_sup (f := fun l : Fin 2 => _root_.YangMills.Construction.TorusFields.supDist 0 ((![c, c'] : Fin 2 → TorusBond n) l).1)
    (Finset.mem_univ (1 : Fin 2))
private def squareTerm (r : ℕ) (G : TorusBond n → TorusBond n → ℝ) (a b : TorusSite n) : ℝ :=
  if IsNearPair r a b then firstCoord a ^ 2 * G (a, secondAxis) (b, secondAxis) else 0
private def outerTerm (r : ℕ) (G : TorusBond n → TorusBond n → ℝ) (a b : TorusSite n) : ℝ :=
  if IsNearPair r a b then 0
  else momentWeight r (b - a) * G (a, secondAxis) (b, secondAxis)
private lemma momentWeight_mul_eq_split (hn : 64 ≤ n) (hr : 16 * r ≤ n) {G : TorusBond n → TorusBond n → ℝ}
    (hG : ∀ c c', G c c' = G c' c) (a b : TorusSite n) :
    momentWeight r (b - a) * G (a, secondAxis) (b, secondAxis) =
      squareTerm r G a b + squareTerm r G b a - 2 * crossTerm r G a b + outerTerm r G a b := by
  unfold squareTerm crossTerm outerTerm
  by_cases hN : IsNearPair r a b
  · have hN' : IsNearPair r b a := ⟨hN.2, hN.1⟩
    rw [if_pos hN, if_pos hN', if_pos hN, if_pos hN, momentWeight_of_near hn hr hN.1.1 hN.2.1,
      hG (b, secondAxis) (a, secondAxis)]
    ring
  · have hN' : ¬ IsNearPair r b a := fun h => hN ⟨h.2, h.1⟩
    rw [if_neg hN, if_neg hN', if_neg hN, if_neg hN]
    ring
private lemma abs_sum_outerTerm_le {v M₀ : ℝ} (hv : 0 < v) (hM : 0 ≤ M₀) (hn : 64 ≤ n) (hr1 : 1 ≤ r)
    {H : TorusSite n → TorusBond n → TorusBond n → ℝ} (hH : IsDecayingFormFamily M₀ v H) :
    |∑ a : TorusSite n, ∑ b : TorusSite n, outerTerm r (H 0) a b| ≤
      4 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) * (intExpSum (v / 32) ^ 4) ^ 2 := by
  have hE : 0 ≤ 4 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) := by positivity
  have hpt : ∀ a b : TorusSite n, |outerTerm r (H 0) a b| ≤
      4 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) * (siteDecay v a * siteDecay v b) := by
    intro a b
    unfold outerTerm
    by_cases hN : IsNearPair r a b
    · rw [if_pos hN, abs_zero]
      have := siteDecay_nonneg v a
      have := siteDecay_nonneg v b
      positivity
    · rw [if_neg hN, abs_mul, abs_of_nonneg (momentWeight_nonneg r _)]
      set D := supportDiam 0 ![((a, secondAxis) : TorusBond n), (b, secondAxis)] with hDdef
      have hDa : _root_.YangMills.Construction.TorusFields.supDist 0 a ≤ D := supDist_le_supportDiam_left (a, secondAxis) (b, secondAxis)
      have hDb : _root_.YangMills.Construction.TorusFields.supDist 0 b ≤ D := supDist_le_supportDiam_right (a, secondAxis) (b, secondAxis)
      have hrD : r ≤ D := by
        by_cases ha : IsNearOriginBond r (a, secondAxis)
        · have hb : ¬ IsNearOriginBond r (b, secondAxis) := fun hb => hN ⟨ha, hb⟩
          exact (le_supDist_of_not_nearOrigin hn hb).trans hDb
        · exact (le_supDist_of_not_nearOrigin hn ha).trans hDa
      have hdec := hH.exp_decay 0 (a, secondAxis) (b, secondAxis)
      have hk := cube_mul_exp_le hv r D (_root_.YangMills.Construction.TorusFields.supDist 0 a) (_root_.YangMills.Construction.TorusFields.supDist 0 b) hrD hDa hDb
      have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      have hsq : 4 * (r : ℝ) ^ 2 ≤ 4 * (r : ℝ) ^ 3 := by
        have : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := by nlinarith [sq_nonneg (r : ℝ)]
        linarith
      calc momentWeight r (b - a) * |H 0 (a, secondAxis) (b, secondAxis)|
          ≤ (4 * (r : ℝ) ^ 3) * (M₀ * Real.exp (-(v * (D : ℝ)))) := by
            refine mul_le_mul ((momentWeight_le r _).trans hsq) hdec (abs_nonneg _) (by positivity)
        _ = 4 * M₀ * ((r : ℝ) ^ 3 * Real.exp (-(v * (D : ℝ)))) := by ring
        _ ≤ 4 * M₀ * (384 / v ^ 3 * Real.exp (-(v * r / 2)) *
            (Real.exp (-(v / 8 * (_root_.YangMills.Construction.TorusFields.supDist 0 a : ℝ))) * Real.exp (-(v / 8 * (_root_.YangMills.Construction.TorusFields.supDist 0 b : ℝ))))) := by
            gcongr
        _ = 4 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) * (siteDecay v a * siteDecay v b) := by
            unfold siteDecay
            ring
  calc |∑ a : TorusSite n, ∑ b : TorusSite n, outerTerm r (H 0) a b|
      ≤ ∑ a : TorusSite n, ∑ b : TorusSite n, |outerTerm r (H 0) a b| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a : TorusSite n, ∑ b : TorusSite n,
        4 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) * (siteDecay v a * siteDecay v b) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
    _ = 4 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) *
        ((∑ a : TorusSite n, siteDecay v a) * ∑ b : TorusSite n, siteDecay v b) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ ≤ 4 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) * (intExpSum (v / 32) ^ 4) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hE
        rw [sq]
        exact mul_le_mul (sum_siteDecay_le hv) (sum_siteDecay_le hv) (sum_siteDecay_nonneg v)
          (pow_nonneg (intExpSum_nonneg _) 4)
private lemma abs_far_term_le {v M₀ : ℝ} (hv : 0 < v) (hM : 0 ≤ M₀) (hn : 64 ≤ n)
    {H : TorusSite n → TorusBond n → TorusBond n → ℝ} (hH : IsDecayingFormFamily M₀ v H) (a : TorusSite n) (e : TorusBond n)
    (ha : IsNearOriginBond r (a, secondAxis)) :
    |if IsNearOriginBond r e then 0 else
        firstCoord a ^ 2 * (H 0 e (a, secondAxis) * siteGradient (truncatedSecondCoord r) e)| ≤
      2 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) * (siteDecay v e.1 * siteDecay v a) := by
  have hE : 0 ≤ 2 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) := by positivity
  by_cases he : IsNearOriginBond r e
  · rw [if_pos he, abs_zero]
    exact mul_nonneg hE (mul_nonneg (siteDecay_nonneg v _) (siteDecay_nonneg v _))
  · rw [if_neg he, abs_mul, abs_mul]
    set D := supportDiam 0 ![e, ((a, secondAxis) : TorusBond n)] with hDdef
    have hDe : _root_.YangMills.Construction.TorusFields.supDist 0 e.1 ≤ D := supDist_le_supportDiam_left e (a, secondAxis)
    have hDa : _root_.YangMills.Construction.TorusFields.supDist 0 a ≤ D := supDist_le_supportDiam_right e (a, secondAxis)
    have hrD : r ≤ D := (le_supDist_of_not_nearOrigin hn he).trans hDe
    have hdec := hH.exp_decay 0 e (a, secondAxis)
    have hk := cube_mul_exp_le hv r D (_root_.YangMills.Construction.TorusFields.supDist 0 e.1) (_root_.YangMills.Construction.TorusFields.supDist 0 a) hrD hDe hDa
    have hz : |firstCoord a ^ 2| ≤ (r : ℝ) ^ 2 := by
      rw [abs_pow]
      have h1 := abs_intCast_le_of_natAbs_le ((natAbs_coord_le_supDist a 0).trans ha.1)
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hg := abs_siteGradient_truncated_le r e
    calc |firstCoord a ^ 2| * (|H 0 e (a, secondAxis)| * |siteGradient (truncatedSecondCoord r) e|)
        ≤ (r : ℝ) ^ 2 * ((M₀ * Real.exp (-(v * (D : ℝ)))) * (2 * (r : ℝ))) := by
          gcongr
      _ = 2 * M₀ * ((r : ℝ) ^ 3 * Real.exp (-(v * (D : ℝ)))) := by ring
      _ ≤ 2 * M₀ * (384 / v ^ 3 * Real.exp (-(v * r / 2)) *
          (Real.exp (-(v / 8 * (_root_.YangMills.Construction.TorusFields.supDist 0 e.1 : ℝ))) * Real.exp (-(v / 8 * (_root_.YangMills.Construction.TorusFields.supDist 0 a : ℝ))))) := by
          gcongr
      _ = 2 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) * (siteDecay v e.1 * siteDecay v a) := by
          unfold siteDecay
          ring
private lemma sum_bonds_siteDecay (v : ℝ) :
    ∑ e : TorusBond n, siteDecay v e.1 = 4 * ∑ x : TorusSite n, siteDecay v x := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  norm_num
private lemma abs_sum_squareTerm_row_le {v M₀ : ℝ} (hv : 0 < v) (hM : 0 ≤ M₀) (hn : 64 ≤ n) (hr : 16 * r ≤ n)
    {H : TorusSite n → TorusBond n → TorusBond n → ℝ} (hH : IsDecayingFormFamily M₀ v H) (a : TorusSite n) :
    |∑ b : TorusSite n, squareTerm r (H 0) a b| ≤
      2 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) *
        (siteDecay v a * (4 * ∑ x : TorusSite n, siteDecay v x)) := by
  have hE : 0 ≤ 2 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) := by positivity
  by_cases ha : IsNearOriginBond r (a, secondAxis)
  · have h1 : ∑ b : TorusSite n, squareTerm r (H 0) a b =
        firstCoord a ^ 2 * ∑ b : TorusSite n, (if IsNearOriginBond r (b, secondAxis) then
          H 0 (b, secondAxis) (a, secondAxis) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      unfold squareTerm IsNearPair
      by_cases hb : IsNearOriginBond r (b, secondAxis)
      · rw [if_pos ⟨ha, hb⟩, if_pos hb, hH.symm 0 (a, secondAxis) (b, secondAxis)]
      · rw [if_neg (fun h => hb h.2), if_neg hb, mul_zero]
    rw [h1, sum_near_eq_neg_sum_far hn hr hH (a, secondAxis), mul_neg, abs_neg, Finset.mul_sum]
    have h2 : ∀ e : TorusBond n, firstCoord a ^ 2 * (if IsNearOriginBond r e then 0 else
        H 0 e (a, secondAxis) * siteGradient (truncatedSecondCoord r) e) =
        if IsNearOriginBond r e then 0 else
          firstCoord a ^ 2 * (H 0 e (a, secondAxis) * siteGradient (truncatedSecondCoord r) e) := by
      intro e
      split_ifs <;> simp
    calc |∑ e : TorusBond n, firstCoord a ^ 2 * (if IsNearOriginBond r e then 0 else
          H 0 e (a, secondAxis) * siteGradient (truncatedSecondCoord r) e)|
        ≤ ∑ e : TorusBond n, 2 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) *
            (siteDecay v e.1 * siteDecay v a) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
          rw [h2 e]
          exact abs_far_term_le hv hM hn hH a e ha
      _ = 2 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) *
          (siteDecay v a * (4 * ∑ x : TorusSite n, siteDecay v x)) := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, sum_bonds_siteDecay]
          ring
  · have h1 : ∑ b : TorusSite n, squareTerm r (H 0) a b = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      unfold squareTerm IsNearPair
      rw [if_neg (fun h => ha h.1)]
    rw [h1, abs_zero]
    exact mul_nonneg hE (mul_nonneg (siteDecay_nonneg v a)
      (mul_nonneg (by norm_num) (sum_siteDecay_nonneg v)))
private lemma abs_sum_squareTerm_le {v M₀ : ℝ} (hv : 0 < v) (hM : 0 ≤ M₀) (hn : 64 ≤ n) (hr : 16 * r ≤ n)
    {H : TorusSite n → TorusBond n → TorusBond n → ℝ} (hH : IsDecayingFormFamily M₀ v H) :
    |∑ a : TorusSite n, ∑ b : TorusSite n, squareTerm r (H 0) a b| ≤
      8 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) * (intExpSum (v / 32) ^ 4) ^ 2 := by
  have hE8 : 0 ≤ 8 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) := by positivity
  calc |∑ a : TorusSite n, ∑ b : TorusSite n, squareTerm r (H 0) a b|
      ≤ ∑ a : TorusSite n, 2 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) *
          (siteDecay v a * (4 * ∑ x : TorusSite n, siteDecay v x)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun a _ => abs_sum_squareTerm_row_le hv hM hn hr hH a)
    _ = 8 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) *
        ((∑ a : TorusSite n, siteDecay v a) * ∑ a : TorusSite n, siteDecay v a) := by
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        ring
    _ ≤ 8 * M₀ * (384 / v ^ 3) * Real.exp (-(v * r / 2)) * (intExpSum (v / 32) ^ 4) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hE8
        rw [sq]
        exact mul_le_mul (sum_siteDecay_le hv) (sum_siteDecay_le hv) (sum_siteDecay_nonneg v)
          (pow_nonneg (intExpSum_nonneg _) 4)
theorem formFamilyMomentStatement_holds : formFamilyMomentStatement := by
  intro v hv _
  refine ⟨10 * (384 / v ^ 3) * (intExpSum (v / 32) ^ 4) ^ 2 + 1, by positivity, ?_⟩
  intro n _ M₀ H hn hM hH
  have hr16 : 16 * momentCutoff n ≤ n := by unfold momentCutoff; omega
  have hr32 : n ≤ 32 * momentCutoff n := by unfold momentCutoff; omega
  have hr1 : 1 ≤ momentCutoff n := by unfold momentCutoff; omega
  have hsq := abs_sum_squareTerm_le hv hM hn hr16 hH
  have hout := abs_sum_outerTerm_le hv hM hn hr1 hH
  have hcomm : ∑ a : TorusSite n, ∑ b : TorusSite n, squareTerm (momentCutoff n) (H 0) b a =
      ∑ a : TorusSite n, ∑ b : TorusSite n, squareTerm (momentCutoff n) (H 0) a b := Finset.sum_comm
  have hsum : ∑ a : TorusSite n, ∑ b : TorusSite n, momentWeight (momentCutoff n) (b - a) *
        H 0 (a, secondAxis) (b, secondAxis) =
      2 * (∑ a : TorusSite n, ∑ b : TorusSite n, squareTerm (momentCutoff n) (H 0) a b) -
        2 * (∑ a : TorusSite n, ∑ b : TorusSite n, crossTerm (momentCutoff n) (H 0) a b) +
        ∑ a : TorusSite n, ∑ b : TorusSite n, outerTerm (momentCutoff n) (H 0) a b := by
    have h1 : ∀ a : TorusSite n, ∑ b : TorusSite n, momentWeight (momentCutoff n) (b - a) *
          H 0 (a, secondAxis) (b, secondAxis) =
        ∑ b : TorusSite n, squareTerm (momentCutoff n) (H 0) a b +
          ∑ b : TorusSite n, squareTerm (momentCutoff n) (H 0) b a -
          2 * ∑ b : TorusSite n, crossTerm (momentCutoff n) (H 0) a b +
          ∑ b : TorusSite n, outerTerm (momentCutoff n) (H 0) a b := by
      intro a
      rw [Finset.sum_congr rfl fun b _ => momentWeight_mul_eq_split hn hr16 (hH.symm 0) a b,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hcomm, ← Finset.mul_sum]
    ring
  have hform : formOnLinearPotential (momentCutoff n) (H 0) =
      ∑ a : TorusSite n, ∑ b : TorusSite n, crossTerm (momentCutoff n) (H 0) a b :=
    formOnLinearPotential_eq_sum_crossTerm _ _
  rw [kernelSecondMoment_eq_sum H hH.translation_invariant, hsum, hform]
  set T := ∑ a : TorusSite n, ∑ b : TorusSite n, squareTerm (momentCutoff n) (H 0) a b
  set F := ∑ a : TorusSite n, ∑ b : TorusSite n, crossTerm (momentCutoff n) (H 0) a b
  set O := ∑ a : TorusSite n, ∑ b : TorusSite n, outerTerm (momentCutoff n) (H 0) a b
  set B := M₀ * (384 / v ^ 3) * Real.exp (-(v * (momentCutoff n : ℝ) / 2)) * (intExpSum (v / 32) ^ 4) ^ 2
    with hB
  have hT : |T| ≤ 8 * B := by rw [hB]; linarith
  have hO : |O| ≤ 4 * B := by rw [hB]; linarith
  have h1 : -(1 / 2) * (2 * T - 2 * F + O) - F = -T - O / 2 := by ring
  have hE : Real.exp (-(v * (momentCutoff n : ℝ) / 2)) ≤ Real.exp (-(v * (n : ℝ) / 64)) := by
    refine Real.exp_le_exp.2 ?_
    have : (n : ℝ) ≤ 32 * (momentCutoff n : ℝ) := by exact_mod_cast hr32
    nlinarith
  rw [h1]
  have hfin : |-T - O / 2| ≤ 10 * B := by
    have h2 := abs_le.1 hT
    have h3 := abs_le.1 hO
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
  refine hfin.trans ?_
  calc 10 * B = 10 * (384 / v ^ 3) * (intExpSum (v / 32) ^ 4) ^ 2 * M₀ *
        Real.exp (-(v * (momentCutoff n : ℝ) / 2)) := by rw [hB]; ring
    _ ≤ 10 * (384 / v ^ 3) * (intExpSum (v / 32) ^ 4) ^ 2 * M₀ * Real.exp (-(v * (n : ℝ) / 64)) := by
        gcongr
    _ ≤ (10 * (384 / v ^ 3) * (intExpSum (v / 32) ^ 4) ^ 2 + 1) * M₀ *
        Real.exp (-(v * (n : ℝ) / 64)) := by
        gcongr
        linarith
end YangMills.Construction.RunningCouplingSlope
end
