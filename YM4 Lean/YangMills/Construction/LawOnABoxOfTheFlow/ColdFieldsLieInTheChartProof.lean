import YangMills.Construction.FormsOnATorus.AxialLadderOnACubeProof
import YangMills.Construction.FormsOnATorus.InteriorRegularityProof
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawOnABoxOfTheFlow.FormOfACubeProof
import YangMills.Construction.ColdChainAtEveryLevel.TermsAgainstTheirFirstOrderProof
import YangMills.Construction.FourPointCondition.BareObservableIsAQuadraticFormProof
import YangMills.Construction.LawOnABoxOfTheFlow.AxialGaugeOfAColdFillingProof
import YangMills.Construction.LawOnABoxOfTheFlow.ColdFieldsLieInTheChart
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields ResponseInTheExpansion ColdStepAtMirrorFrames
open BlockAverages hiding unitStep
private lemma norm_coe_unit (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
private lemma star_mul_self_unit (g : UnitQuaternion) : star (g : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 :=
  (Unitary.mem_iff.mp g.2).1
private lemma mul_star_self_unit (g : UnitQuaternion) : (g : ℍ[ℝ]) * star (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.BlockAverages.GaugeChangeDensity.unitQuaternion_mul_star <;> assumption
private lemma coe_expUnit (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (w : ℍ[ℝ]) := rfl
private lemma re_imaginary (w : imaginaryQuaternions) : (w : ℍ[ℝ]).re = 0 := w.2
private lemma star_imaginary (w : imaginaryQuaternions) : star (w : ℍ[ℝ]) = -(w : ℍ[ℝ]) := by apply _root_.YangMills.Construction.GaugeMotions.star_coe_imaginary <;> assumption
private lemma norm_coe_imaginary (w : imaginaryQuaternions) : ‖(w : ℍ[ℝ])‖ = ‖w‖ := rfl
private lemma norm_exp_sub_one_sub_le (w : imaginaryQuaternions) (h1 : ‖w‖ ≤ 1) :
    ‖NormedSpace.exp (w : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])‖ ≤ ‖w‖ ^ 2 := by
  rcases eq_or_ne ‖w‖ 0 with h0 | h0
  · have hw : w = 0 := norm_eq_zero.mp h0
    subst hw
    simp
  set t := ‖w‖ with ht
  have tpos : 0 < t := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hre : (w : ℍ[ℝ]).re = 0 := re_imaginary w
  have he : NormedSpace.exp (w : ℍ[ℝ]) =
      ((Real.cos t : ℝ) : ℍ[ℝ]) + (Real.sin t / t) • (w : ℍ[ℝ]) := by
    have := Quaternion.exp_of_re_eq_zero (q := (w : ℍ[ℝ])) hre
    rw [this, norm_coe_imaginary]
  have hdec : NormedSpace.exp (w : ℍ[ℝ]) - 1 - (w : ℍ[ℝ]) =
      ((Real.cos t - 1 : ℝ) : ℍ[ℝ]) + (Real.sin t / t - 1) • (w : ℍ[ℝ]) := by
    rw [he, sub_smul, one_smul]
    push_cast
    abel
  rw [hdec]
  have hc : |Real.cos t - 1| ≤ t ^ 2 / 2 := by
    have a := Real.one_sub_sq_div_two_le_cos (x := t)
    have b := Real.cos_le_one t
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg t]
  have hs : |Real.sin t / t - 1| * t ≤ t ^ 2 / 2 := by
    have a := Real.sin_gt_sub_cube tpos
    have b := Real.sin_lt tpos
    have e : |Real.sin t / t - 1| * t = |Real.sin t - t| := by
      rw [← abs_of_pos tpos, ← abs_mul, abs_of_pos tpos]
      congr 1
      field_simp
    have c3 : t ^ 3 ≤ t ^ 2 := by nlinarith [pow_pos tpos 2]
    rw [e, abs_le]
    constructor <;> nlinarith [pow_pos tpos 3, pow_pos tpos 2]
  calc ‖((Real.cos t - 1 : ℝ) : ℍ[ℝ]) + (Real.sin t / t - 1) • (w : ℍ[ℝ])‖
      ≤ ‖((Real.cos t - 1 : ℝ) : ℍ[ℝ])‖ + ‖(Real.sin t / t - 1) • (w : ℍ[ℝ])‖ := norm_add_le _ _
    _ = |Real.cos t - 1| + |Real.sin t / t - 1| * t := by
        rw [Quaternion.norm_coe, norm_smul, norm_coe_imaginary, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ t ^ 2 := by linarith
abbrev _root_.YangMills.SharedProofs.p105988 := @norm_exp_sub_one_sub_le
private lemma norm_expUnit_sub_one_le (w : imaginaryQuaternions) (h1 : ‖w‖ ≤ 1) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * ‖w‖ := by
  have h := norm_exp_sub_one_sub_le w h1
  rw [coe_expUnit]
  have e : NormedSpace.exp (w : ℍ[ℝ]) - 1 =
      (NormedSpace.exp (w : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])) + (w : ℍ[ℝ]) := by abel
  rw [e]
  calc _ ≤ ‖NormedSpace.exp (w : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])‖ + ‖(w : ℍ[ℝ])‖ := norm_add_le _ _
    _ ≤ ‖w‖ ^ 2 + ‖w‖ := by rw [norm_coe_imaginary]; linarith
    _ ≤ 2 * ‖w‖ := by nlinarith [norm_nonneg w]
private def imPart (q : ℍ[ℝ]) : imaginaryQuaternions := ⟨q.im, by show q.im.re = 0; simp⟩
private lemma coe_imPart (q : ℍ[ℝ]) : ((imPart q : imaginaryQuaternions) : ℍ[ℝ]) = q.im := rfl
private lemma re_add_imPart (q : ℍ[ℝ]) : ((q.re : ℝ) : ℍ[ℝ]) + (imPart q : ℍ[ℝ]) = q := by
  rw [coe_imPart]; exact Quaternion.re_add_im q
private lemma norm_sq_eq_re_sq_add (q : ℍ[ℝ]) : ‖q‖ ^ 2 = q.re ^ 2 + ‖imPart q‖ ^ 2 := by
  have h1 : ‖q‖ ^ 2 = Quaternion.normSq q := by
    rw [Quaternion.normSq_eq_norm_mul_self, sq]
  have h2 : ‖imPart q‖ ^ 2 = Quaternion.normSq (q.im) := by
    rw [Quaternion.normSq_eq_norm_mul_self, sq]; rfl
  rw [h1, h2, Quaternion.normSq_def', Quaternion.normSq_def']
  simp
  ring
private lemma norm_sub_one_sq (q : ℍ[ℝ]) (hq : ‖q‖ = 1) : ‖q - 1‖ ^ 2 = 2 - 2 * q.re := by apply _root_.YangMills.Construction.BlockAverages.TermwiseBounds.norm_sub_one_sq_of_norm_eq_one <;> assumption
private lemma chart_form_eq (q : ℍ[ℝ]) (hq : ‖q‖ = 1) (h : ‖q - 1‖ ≤ 1) :
    (((Real.sqrt (1 - ‖imPart q‖ ^ 2) : ℝ) : ℍ[ℝ]) + (imPart q : ℍ[ℝ])) = q := by
  have h1 := norm_sub_one_sq q hq
  have h2 := norm_sq_eq_re_sq_add q
  rw [hq] at h2
  have hre : 0 ≤ q.re := by nlinarith [norm_nonneg (q - 1)]
  have e : Real.sqrt (1 - ‖imPart q‖ ^ 2) = q.re := by
    have : 1 - ‖imPart q‖ ^ 2 = q.re ^ 2 := by linarith
    rw [this, Real.sqrt_sq hre]
  rw [e]
  exact re_add_imPart q
private lemma fourfold_product_expansion (t₁ t₂ t₃ t₄ : ℍ[ℝ]) (τ : ℝ) (hτ : τ ≤ 1) (h₁ : ‖t₁‖ ≤ τ)
    (h₂ : ‖t₂‖ ≤ τ) (h₃ : ‖t₃‖ ≤ τ) (h₄ : ‖t₄‖ ≤ τ) :
    ‖(1 + t₁) * (1 + t₂) * (1 + t₃) * (1 + t₄) - 1 - (t₁ + t₂ + t₃ + t₄)‖ ≤ 11 * τ ^ 2 := by
  have τ0 : 0 ≤ τ := (norm_nonneg _).trans h₁
  set p := t₁ + t₂ + t₁ * t₂ with hp
  set r := t₃ + t₄ + t₃ * t₄ with hr
  have e : (1 + t₁) * (1 + t₂) * (1 + t₃) * (1 + t₄) - 1 - (t₁ + t₂ + t₃ + t₄) =
      p * r + t₁ * t₂ + t₃ * t₄ := by
    simp only [hp, hr]
    noncomm_ring
  have m₁ : ‖t₁ * t₂‖ ≤ τ ^ 2 := by
    rw [norm_mul]; nlinarith [norm_nonneg t₁, norm_nonneg t₂]
  have m₂ : ‖t₃ * t₄‖ ≤ τ ^ 2 := by
    rw [norm_mul]; nlinarith [norm_nonneg t₃, norm_nonneg t₄]
  have np : ‖p‖ ≤ 3 * τ := by
    calc ‖p‖ ≤ ‖t₁‖ + ‖t₂‖ + ‖t₁ * t₂‖ := norm_add₃_le
      _ ≤ 3 * τ := by nlinarith
  have nr : ‖r‖ ≤ 3 * τ := by
    calc ‖r‖ ≤ ‖t₃‖ + ‖t₄‖ + ‖t₃ * t₄‖ := norm_add₃_le
      _ ≤ 3 * τ := by nlinarith
  rw [e]
  calc ‖p * r + t₁ * t₂ + t₃ * t₄‖ ≤ ‖p * r‖ + ‖t₁ * t₂‖ + ‖t₃ * t₄‖ := norm_add₃_le
    _ ≤ 9 * τ ^ 2 + τ ^ 2 + τ ^ 2 := by
        have : ‖p * r‖ ≤ 9 * τ ^ 2 := by
          rw [norm_mul]; nlinarith [norm_nonneg p, norm_nonneg r]
        linarith
    _ = 11 * τ ^ 2 := by ring
section Geometry
variable {n : ℕ} [NeZero n]
private lemma natAbs_valMinAbs_one_le (hn : 2 < n) : ((1 : ZMod n)).valMinAbs.natAbs ≤ 1 := by
  have : ((1 : ZMod n)).valMinAbs = 1 := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨by simp, ?_, ?_⟩ <;> omega
  simp [this]
private def siteAt (o : TorusSite n) (c : Fin 4 → ℤ) : TorusSite n := o + siteOfInt c
private def coordsFrom (o z : TorusSite n) : Fin 4 → ℤ := fun i => (z i - o i).valMinAbs
private lemma siteAt_coordsFrom (o z : TorusSite n) : siteAt o (coordsFrom o z) = z := by apply _root_.YangMills.DeltaSharedProofs.p500399 <;> assumption
private lemma siteAt_add_single (o : TorusSite n) (c : Fin 4 → ℤ) (i : Fin 4) :
    siteAt o (c + Pi.single i 1) = siteAt o c + unitStep n i := by apply _root_.YangMills.DeltaSharedProofs.p500616 <;> assumption
private lemma mem_supBall_iff (o z : TorusSite n) (r : ℕ) :
    z ∈ supBall o (r : ℝ) ↔ ∀ i, |coordsFrom o z i| ≤ (r : ℤ) := by apply _root_.YangMills.DeltaSharedProofs.p501389 <;> assumption
private lemma coordsFrom_siteAt (o : TorusSite n) (c : Fin 4 → ℤ) (i : Fin 4) (h : 2 * |c i| < n) :
    coordsFrom o (siteAt o c) i = c i := by
  have e : siteAt o c i - o i = ((c i : ℤ) : ZMod n) := by
    simp [siteAt, siteOfInt]
  simp only [coordsFrom, e]
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩ <;> [skip; skip] <;> (have := abs_le.mp (le_refl |c i|); omega)
private lemma siteAt_mem_supBall_iff (o : TorusSite n) (c : Fin 4 → ℤ) (r : ℕ)
    (h : ∀ i, 2 * |c i| < n) :
    siteAt o c ∈ supBall o (r : ℝ) ↔ ∀ i, |c i| ≤ (r : ℤ) := by
  rw [mem_supBall_iff]
  constructor
  · intro a i
    rw [← coordsFrom_siteAt o c i (h i)]
    exact a i
  · intro a i
    rw [coordsFrom_siteAt o c i (h i)]
    exact a i
private lemma abs_coordsFrom_add_step_le (hn : 2 < n) (o z : TorusSite n) (i j : Fin 4) :
    |coordsFrom o (z + unitStep n j) i| ≤ |coordsFrom o z i| + 1 := by
  have e : (z + unitStep n j) i - o i = (z i - o i) + unitStep n j i := by
    simp only [Pi.add_apply]; ring
  simp only [coordsFrom, e]
  have h1 := ZMod.natAbs_valMinAbs_add_le (z i - o i) (unitStep n j i)
  have h2 : ((unitStep n j i : ZMod n)).valMinAbs.natAbs ≤ 1 := by
    by_cases hji : i = j
    · subst hji
      simp only [unitStep, Pi.single_eq_same]
      exact natAbs_valMinAbs_one_le hn
    · simp [unitStep, hji]
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  have h3 := Int.natAbs_add_le (z i - o i).valMinAbs (unitStep n j i).valMinAbs
  omega
private lemma abs_coordsFrom_le_add_step (hn : 2 < n) (o z : TorusSite n) (i j : Fin 4) :
    |coordsFrom o z i| ≤ |coordsFrom o (z + unitStep n j) i| + 1 := by
  have e : z i - o i = ((z + unitStep n j) i - o i) + (- unitStep n j i) := by
    simp only [Pi.add_apply]; ring
  simp only [coordsFrom]
  rw [e]
  have h1 := ZMod.natAbs_valMinAbs_add_le ((z + unitStep n j) i - o i) (- unitStep n j i)
  have h2 : ((- unitStep n j i : ZMod n)).valMinAbs.natAbs ≤ 1 := by
    rw [ZMod.natAbs_valMinAbs_neg]
    by_cases hji : i = j
    · subst hji
      simp only [unitStep, Pi.single_eq_same]
      exact natAbs_valMinAbs_one_le hn
    · simp [unitStep, hji]
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  have h3 := Int.natAbs_add_le ((z + unitStep n j) i - o i).valMinAbs (- unitStep n j i).valMinAbs
  omega
private def OnSphere (R : ℕ) (c : Fin 4 → ℤ) : Prop :=
  (∀ j, |c j| ≤ (R : ℤ) + 1) ∧ ∃ j, |c j| = (R : ℤ) + 1
private lemma norm_sub_along_line_le {E : Type} [NormedAddCommGroup E] (H : (Fin 4 → ℤ) → E) (R : ℕ)
    (η : ℝ)
    (hstep : ∀ c i, OnSphere R c → OnSphere R (c + Pi.single i 1) →
      ‖H c - H (c + Pi.single i 1)‖ ≤ η)
    (i : Fin 4) (m : ℕ) : ∀ c : Fin 4 → ℤ, c i + m = (R : ℤ) + 1 →
      (∀ t, c i ≤ t → t ≤ (R : ℤ) + 1 → OnSphere R (Function.update c i t)) →
      ‖H c - H (Function.update c i ((R : ℤ) + 1))‖ ≤ m * η := by
  induction m with
  | zero =>
    intro c hc _
    have : c i = (R : ℤ) + 1 := by simpa using hc
    rw [← this, Function.update_eq_self]
    simp
  | succ m ih =>
    intro c hc hs
    have ci : c i + 1 ≤ (R : ℤ) + 1 := by push_cast at hc; omega
    set c' := c + Pi.single i (1 : ℤ) with hc'
    have e' : c' = Function.update c i (c i + 1) := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [hc']
      · simp [hc', hji]
    have ci' : c' i = c i + 1 := by simp [hc']
    have hu : Function.update c' i ((R : ℤ) + 1) = Function.update c i ((R : ℤ) + 1) := by
      rw [e', Function.update_idem]
    have s0 : OnSphere R c := by
      have := hs (c i) le_rfl (by omega)
      rwa [Function.update_eq_self] at this
    have s1 : OnSphere R c' := by
      rw [e']; exact hs (c i + 1) (by omega) ci
    have h1 := hstep c i s0 s1
    have h2 := ih c' (by rw [ci']; push_cast at hc; omega) (by
      intro t ht ht'
      rw [e', Function.update_idem]
      exact hs t (by rw [ci'] at ht; omega) ht')
    rw [hu] at h2
    calc ‖H c - H (Function.update c i ((R : ℤ) + 1))‖
        ≤ ‖H c - H c'‖ + ‖H c' - H (Function.update c i ((R : ℤ) + 1))‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ((m + 1 : ℕ) : ℝ) * η := by push_cast; linarith
private lemma norm_sub_corner_le {E : Type} [NormedAddCommGroup E] (H : (Fin 4 → ℤ) → E) (R : ℕ)
    (η : ℝ) (η0 : 0 ≤ η)
    (hstep : ∀ c i, OnSphere R c → OnSphere R (c + Pi.single i 1) →
      ‖H c - H (c + Pi.single i 1)‖ ≤ η)
    (c : Fin 4 → ℤ) (hc : OnSphere R c) :
    ‖H c - H (fun _ => (R : ℤ) + 1)‖ ≤ 4 * (2 * R + 2) * η := by
  obtain ⟨hb, i, hi⟩ := hc
  have raise : ∀ (d : Fin 4 → ℤ) (j : Fin 4), (∀ l, |d l| ≤ (R : ℤ) + 1) →
      (∀ t, d j ≤ t → t ≤ (R : ℤ) + 1 → OnSphere R (Function.update d j t)) →
      ‖H d - H (Function.update d j ((R : ℤ) + 1))‖ ≤ (2 * R + 2) * η := by
    intro d j hd hs
    have hdj := abs_le.mp (hd j)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, d j + m = (R : ℤ) + 1 :=
      ⟨((R : ℤ) + 1 - d j).toNat, by omega⟩
    have := norm_sub_along_line_le H R η hstep j m d hm hs
    refine this.trans ?_
    have : (m : ℝ) ≤ 2 * R + 2 := by
      have : (m : ℤ) ≤ 2 * R + 2 := by omega
      exact_mod_cast this
    nlinarith
  have others : ∀ T : Finset (Fin 4), i ∉ T →
      ‖H c - H (fun j => if j ∈ T then (R : ℤ) + 1 else c j)‖ ≤ T.card * ((2 * R + 2) * η) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      simp
    | insert a T ha ih =>
      intro hiT
      have hia : i ≠ a := fun h => hiT (by simp [h])
      have hiT' : i ∉ T := fun h => hiT (by simp [h])
      set d : Fin 4 → ℤ := fun j => if j ∈ T then (R : ℤ) + 1 else c j with hd
      have e : (fun j => if j ∈ insert a T then (R : ℤ) + 1 else c j) =
          Function.update d a ((R : ℤ) + 1) := by
        funext j
        by_cases hj : j = a
        · subst hj; simp
        · simp [hj, hd, Finset.mem_insert]
      have dbound : ∀ l, |d l| ≤ (R : ℤ) + 1 := by
        intro l
        by_cases hl : l ∈ T
        · simp only [hd, hl, if_true]; rw [abs_of_nonneg (by omega)]
        · simp only [hd, hl, if_false]; exact hb l
      have di : d i = c i := by simp [hd, hiT']
      have step := raise d a dbound (by
        intro t h1 h2
        refine ⟨?_, i, ?_⟩
        · intro l
          by_cases hl : l = a
          · subst hl
            simp only [Function.update_self]
            have := abs_le.mp (dbound l)
            rw [abs_le]; omega
          · simp only [Function.update_of_ne hl]; exact dbound l
        · rw [Function.update_of_ne hia, di, hi])
      rw [e]
      have ih' := ih hiT'
      rw [Finset.card_insert_of_notMem ha]
      calc ‖H c - H (Function.update d a ((R : ℤ) + 1))‖
          ≤ ‖H c - H d‖ + ‖H d - H (Function.update d a ((R : ℤ) + 1))‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ((T.card + 1 : ℕ) : ℝ) * ((2 * R + 2) * η) := by push_cast; nlinarith
  have h3 := others (Finset.univ.erase i) (by simp)
  set d : Fin 4 → ℤ := fun j => if j ∈ Finset.univ.erase i then (R : ℤ) + 1 else c j with hd
  have dj : ∀ j, j ≠ i → d j = (R : ℤ) + 1 := by
    intro j hj; simp [hd, hj]
  have di : d i = c i := by simp [hd]
  have dbound : ∀ l, |d l| ≤ (R : ℤ) + 1 := by
    intro l
    by_cases hl : l = i
    · rw [hl, di]; exact hb i
    · rw [dj l hl, abs_of_nonneg (by omega)]
  obtain ⟨j, hj⟩ : ∃ j : Fin 4, j ≠ i := exists_ne i
  have last := raise d i dbound (by
    intro t h1 h2
    refine ⟨?_, j, ?_⟩
    · intro l
      by_cases hl : l = i
      · subst hl
        simp only [Function.update_self]
        have := abs_le.mp (dbound l)
        rw [abs_le]; omega
      · simp only [Function.update_of_ne hl]; exact dbound l
    · rw [Function.update_of_ne hj, dj j hj, abs_of_nonneg (by omega)])
  have e : Function.update d i ((R : ℤ) + 1) = fun _ => (R : ℤ) + 1 := by
    funext l
    by_cases hl : l = i
    · subst hl; simp
    · simp [hl, dj l hl]
  rw [e] at last
  have card : (Finset.univ.erase i).card = 3 := by simp
  rw [card] at h3
  calc ‖H c - H (fun _ => (R : ℤ) + 1)‖ ≤ ‖H c - H d‖ + ‖H d - H (fun _ => (R : ℤ) + 1)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4 * (2 * R + 2) * η := by push_cast at h3; nlinarith
private lemma card_supBall_le (o : TorusSite n) (r : ℕ) :
    ((supBall o (r : ℝ)).card : ℝ) ≤ (2 * r + 1) ^ 4 := by apply _root_.YangMills.SharedProofs.p88713 <;> assumption
end Geometry
section Main
variable {n : ℕ} [NeZero n]
private lemma coe_gaugeTransform (γ : TorusSite n → UnitQuaternion) (W : TorusField n) (x : TorusSite n)
    (i : Fin 4) :
    ((gaugeTransform γ W x i : UnitQuaternion) : ℍ[ℝ]) =
      (γ x : ℍ[ℝ]) * (W x i : ℍ[ℝ]) * star (γ (x + unitStep n i) : ℍ[ℝ]) := rfl
private lemma two_mul_natCast (R : ℕ) : 2 * (R : ℝ) = ((2 * R : ℕ) : ℝ) := by push_cast; ring
private lemma mem_supBall_two_mul_iff (o z : TorusSite n) (R : ℕ) :
    z ∈ supBall o (2 * (R : ℝ)) ↔ ∀ i, |coordsFrom o z i| ≤ 2 * (R : ℤ) := by apply _root_.YangMills.DeltaSharedProofs.p501575 <;> assumption
private lemma mem_bondsWithin_iff (S : Finset (TorusSite n)) (b : TorusBond n) :
    b ∈ bondsWithin S ↔ b.1 ∈ S ∧ b.1 + unitStep n b.2 ∈ S := by
  simp [bondsWithin]
private lemma mem_bondsTouching_iff (o : TorusSite n) (R : ℕ) (b : TorusBond n) :
    b ∈ bondsTouching o R ↔ b.1 ∈ supBall o (R : ℝ) ∨ b.1 + unitStep n b.2 ∈ supBall o (R : ℝ) := by
  simp [bondsTouching]
private lemma bondsTouching_ends (hn : 2 < n) (o : TorusSite n) (R : ℕ) (b : TorusBond n)
    (hb : b ∈ bondsTouching o R) :
    (∀ i, |coordsFrom o b.1 i| ≤ (R : ℤ) + 1) ∧
      ∀ i, |coordsFrom o (b.1 + unitStep n b.2) i| ≤ (R : ℤ) + 1 := by
  rcases (mem_bondsTouching_iff o R b).mp hb with h | h
  · have h' := (mem_supBall_iff o _ R).mp h
    refine ⟨fun i => by have := h' i; omega, fun i => ?_⟩
    have := h' i
    have := abs_coordsFrom_add_step_le hn o b.1 i b.2
    omega
  · have h' := (mem_supBall_iff o _ R).mp h
    refine ⟨fun i => ?_, fun i => by have := h' i; omega⟩
    have := h' i
    have := abs_coordsFrom_le_add_step hn o b.1 i b.2
    omega
private lemma bondsTouching_subset (hn : 2 < n) (o : TorusSite n) (R : ℕ) (hR : 1 ≤ R) (b : TorusBond n)
    (hb : b ∈ bondsTouching o R) :
    b ∈ bondsWithin (supBall o (2 * (R : ℝ))) := by
  obtain ⟨h1, h2⟩ := bondsTouching_ends hn o R b hb
  rw [mem_bondsWithin_iff, mem_supBall_two_mul_iff, mem_supBall_two_mul_iff]
  exact ⟨fun i => by have := h1 i; omega, fun i => by have := h2 i; omega⟩
private lemma card_bondsTouching_le (hn : 2 < n) (o : TorusSite n) (R : ℕ) :
    ((bondsTouching o R).card : ℝ) ≤ 4 * (2 * ((R + 1 : ℕ) : ℝ) + 1) ^ 4 := by
  have hsub : bondsTouching o R ⊆
      (supBall o ((R + 1 : ℕ) : ℝ)) ×ˢ (Finset.univ : Finset (Fin 4)) := by
    intro b hb
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [mem_supBall_iff]
    intro i
    have := (bondsTouching_ends hn o R b hb).1 i
    push_cast
    exact this
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_product] at h1
  have h2 := card_supBall_le o (R + 1)
  have h3 : ((bondsTouching o R).card : ℝ) ≤ ((supBall o ((R + 1 : ℕ) : ℝ)).card : ℝ) * 4 := by
    have := h1
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  linarith
private lemma card_plaquettesIn_le (o : TorusSite n) (r : ℕ) :
    ((plaquettesIn (supBall o (r : ℝ))).card : ℝ) ≤ 16 * (2 * (r : ℝ) + 1) ^ 4 := by
  have hsub : plaquettesIn (supBall o (r : ℝ)) ⊆
      (supBall o (r : ℝ)) ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4)) := by
    intro p hp
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    have : p.1 ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by simp [plaquetteVertices]
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp.2 _ this
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_product] at h1
  have h2 := card_supBall_le o r
  have h3 : ((plaquettesIn (supBall o (r : ℝ))).card : ℝ) ≤ ((supBall o (r : ℝ)).card : ℝ) * 16 := by
    have := h1
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at this
    exact_mod_cast this
  linarith
private lemma siteAt_not_mem_of_sphere (o : TorusSite n) (R : ℕ) (hn : 2 * ((R : ℤ) + 1) < n)
    (c : Fin 4 → ℤ) (hc : OnSphere R c) :
    siteAt o c ∉ supBall o (R : ℝ) := by
  rw [siteAt_mem_supBall_iff o c R (fun i => by have := hc.1 i; omega)]
  obtain ⟨j, hj⟩ := hc.2
  intro h
  have := h j
  omega
private lemma siteAt_mem_of_sphere (o : TorusSite n) (R : ℕ) (hR : 1 ≤ R) (hn : 2 * ((R : ℤ) + 1) < n)
    (c : Fin 4 → ℤ) (hc : OnSphere R c) : siteAt o c ∈ supBall o (2 * (R : ℝ)) := by
  rw [two_mul_natCast, siteAt_mem_supBall_iff o c (2 * R) (fun i => by have := hc.1 i; omega)]
  intro i
  have := hc.1 i
  push_cast
  omega
private lemma onSphere_of_not_mem (o z : TorusSite n) (R : ℕ) (hz : z ∉ supBall o (R : ℝ))
    (h : ∀ i, |coordsFrom o z i| ≤ (R : ℤ) + 1) : OnSphere R (coordsFrom o z) := by
  refine ⟨h, ?_⟩
  rw [mem_supBall_iff] at hz
  push Not at hz
  obtain ⟨j, hj⟩ := hz
  exact ⟨j, by have := h j; omega⟩
private lemma exists_gauge_near (o : TorusSite n) (R : ℕ) (hR : 1 ≤ R) (hn : 16 * R < n)
    (A A' : TorusBond n → imaginaryQuaternions)
    (W : TorusField n) (g : TorusSite n → UnitQuaternion) (a : ℝ) (ha : a ≤ 1) (a0 : 0 ≤ a)
    (hA : ∀ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), ‖A b‖ ≤ a)
    (hA' : ∀ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), ‖A' b‖ ≤ a)
    (hg : ∀ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), gaugeTransform g W b.1 b.2 = expUnit (A' b))
    (hW : ∀ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), b ∉ bondsTouching o R →
      W b.1 b.2 = expUnit (A b)) :
    ∃ γ : TorusSite n → UnitQuaternion, IsSupportedGauge o R γ ∧ ∀ b ∈ bondsTouching o R,
      ‖((gaugeTransform γ W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) -
        ((expUnit (A b) : UnitQuaternion) : ℍ[ℝ])‖ ≤ (16 * (2 * R + 2) + 4) * a := by
  classical
  have hn2 : 2 * ((R : ℤ) + 1) < n := by omega
  have hn3 : 2 < n := by omega
  set H : (Fin 4 → ℤ) → ℍ[ℝ] := fun c => (g (siteAt o c) : ℍ[ℝ]) with hH
  have hstep : ∀ c i, OnSphere R c → OnSphere R (c + Pi.single i 1) →
      ‖H c - H (c + Pi.single i 1)‖ ≤ 4 * a := by
    intro c i h0 h1
    have hv : siteAt o (c + Pi.single i 1) = siteAt o c + unitStep n i := siteAt_add_single o c i
    set u := siteAt o c with hu
    have hb : (u, i) ∈ bondsWithin (supBall o (2 * (R : ℝ))) := by
      rw [mem_bondsWithin_iff]
      exact ⟨siteAt_mem_of_sphere o R hR hn2 c h0, by
        show u + unitStep n i ∈ _; rw [← hv]; exact siteAt_mem_of_sphere o R hR hn2 _ h1⟩
    have hnb : (u, i) ∉ bondsTouching o R := by
      rw [mem_bondsTouching_iff, not_or]
      exact ⟨siteAt_not_mem_of_sphere o R hn2 c h0, by
        show u + unitStep n i ∉ _; rw [← hv]; exact siteAt_not_mem_of_sphere o R hn2 _ h1⟩
    have e1 : gaugeTransform g W u i = expUnit (A' (u, i)) := hg (u, i) hb
    have e2 : W u i = expUnit (A (u, i)) := hW (u, i) hb hnb
    have q1 : (g u : ℍ[ℝ]) * ((expUnit (A (u, i)) : UnitQuaternion) : ℍ[ℝ]) =
        ((expUnit (A' (u, i)) : UnitQuaternion) : ℍ[ℝ]) * (g (u + unitStep n i) : ℍ[ℝ]) := by
      have h := congrArg (fun h : UnitQuaternion => (h : ℍ[ℝ]) * (g (u + unitStep n i) : ℍ[ℝ])) e1
      simp only [coe_gaugeTransform, e2, mul_assoc, star_mul_self_unit, mul_one] at h
      exact h
    have d1 := norm_expUnit_sub_one_le (A (u, i)) ((hA _ hb).trans ha)
    have d2 := norm_expUnit_sub_one_le (A' (u, i)) ((hA' _ hb).trans ha)
    have b1 := hA _ hb
    have b2 := hA' _ hb
    have e3 : H c - H (c + Pi.single i 1) =
        (g u : ℍ[ℝ]) * (1 - ((expUnit (A (u, i)) : UnitQuaternion) : ℍ[ℝ])) +
          (((expUnit (A' (u, i)) : UnitQuaternion) : ℍ[ℝ]) - 1) * (g (u + unitStep n i) : ℍ[ℝ]) := by
      simp only [hH, hv, mul_sub, sub_mul, mul_one, one_mul, q1]
      rw [← hu]
      abel
    rw [e3]
    calc _ ≤ ‖(g u : ℍ[ℝ]) * (1 - ((expUnit (A (u, i)) : UnitQuaternion) : ℍ[ℝ]))‖ +
          ‖(((expUnit (A' (u, i)) : UnitQuaternion) : ℍ[ℝ]) - 1) * (g (u + unitStep n i) : ℍ[ℝ])‖ :=
          norm_add_le _ _
      _ = ‖((expUnit (A (u, i)) : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
          ‖((expUnit (A' (u, i)) : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
          rw [norm_mul, norm_mul, norm_coe_unit, norm_coe_unit, norm_sub_rev 1]; ring
      _ ≤ 4 * a := by linarith
  set top : Fin 4 → ℤ := fun _ => (R : ℤ) + 1 with htop
  have near : ∀ z, OnSphere R (coordsFrom o z) →
      ‖(g z : ℍ[ℝ]) - (g (siteAt o top) : ℍ[ℝ])‖ ≤ 4 * (2 * R + 2) * (4 * a) := by
    intro z hz
    have := norm_sub_corner_le H R (4 * a) (by linarith) hstep _ hz
    simpa only [hH, siteAt_coordsFrom] using this
  set k : TorusSite n → UnitQuaternion :=
    fun z => if z ∈ supBall o (R : ℝ) then g (siteAt o top) else g z with hk
  refine ⟨fun z => (k z)⁻¹ * g z, ?_, ?_⟩
  · intro z hz
    simp [hk, hz]
  · rintro ⟨x, i⟩ hb
    have hbS := bondsTouching_subset hn3 o R hR (x, i) hb
    obtain ⟨c1, c2⟩ := bondsTouching_ends hn3 o R (x, i) hb
    simp only at c1 c2
    have hkd : ‖(k x : ℍ[ℝ]) - (k (x + unitStep n i) : ℍ[ℝ])‖ ≤ 4 * (2 * R + 2) * (4 * a) := by
      by_cases hx : x ∈ supBall o (R : ℝ)
      · by_cases hv : x + unitStep n i ∈ supBall o (R : ℝ)
        · simp only [hk, hx, hv, if_true, sub_self, norm_zero]
          positivity
        · simp only [hk, hx, hv, if_true, if_false]
          rw [norm_sub_rev]
          exact near _ (onSphere_of_not_mem o _ R hv c2)
      · have hv : x + unitStep n i ∈ supBall o (R : ℝ) := by
          rcases (mem_bondsTouching_iff o R (x, i)).mp hb with h | h
          · exact absurd h hx
          · exact h
        simp only [hk, hx, hv, if_true, if_false]
        exact near _ (onSphere_of_not_mem o _ R hx c1)
    have ge : gaugeTransform (fun z => (k z)⁻¹ * g z) W x i =
        (k x)⁻¹ * expUnit (A' (x, i)) * k (x + unitStep n i) := by
      have h : gaugeTransform g W x i = expUnit (A' (x, i)) := hg (x, i) hbS
      rw [← h]
      simp only [TorusFields.gaugeTransform]
      group
    simp only
    rw [ge]
    set e' : ℍ[ℝ] := ((expUnit (A' (x, i)) : UnitQuaternion) : ℍ[ℝ]) with he'
    set kx : ℍ[ℝ] := (k x : ℍ[ℝ]) with hkx
    set kv : ℍ[ℝ] := (k (x + unitStep n i) : ℍ[ℝ]) with hkv
    have nkx : ‖kx‖ = 1 := norm_coe_unit _
    have nkv : ‖kv‖ = 1 := norm_coe_unit _
    have d1 := norm_expUnit_sub_one_le (A (x, i)) ((hA _ hbS).trans ha)
    have d2 := norm_expUnit_sub_one_le (A' (x, i)) ((hA' _ hbS).trans ha)
    have b1 := hA _ hbS
    have b2 := hA' _ hbS
    have cc : (((k x)⁻¹ * expUnit (A' (x, i)) * k (x + unitStep n i) : UnitQuaternion) : ℍ[ℝ]) =
        star kx * e' * kv := rfl
    have m1 : ‖star kx * e' * kv - 1‖ ≤ 2 * a + 4 * (2 * R + 2) * (4 * a) := by
      have e3 : kx * (star kx * e' * kv - 1) = (e' - 1) * kv + (kv - kx) := by
        have : kx * star kx = 1 := mul_star_self_unit _
        rw [mul_sub, ← mul_assoc, ← mul_assoc, this]
        noncomm_ring
      have e4 : ‖star kx * e' * kv - 1‖ = ‖kx * (star kx * e' * kv - 1)‖ := by
        rw [norm_mul, nkx, one_mul]
      rw [e4, e3]
      calc _ ≤ ‖(e' - 1) * kv‖ + ‖kv - kx‖ := norm_add_le _ _
        _ = ‖e' - 1‖ + ‖kx - kv‖ := by rw [norm_mul, nkv, mul_one, norm_sub_rev kv]
        _ ≤ _ := by linarith
    rw [cc]
    calc ‖star kx * e' * kv - ((expUnit (A (x, i)) : UnitQuaternion) : ℍ[ℝ])‖
        ≤ ‖star kx * e' * kv - 1‖ + ‖1 - ((expUnit (A (x, i)) : UnitQuaternion) : ℍ[ℝ])‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (16 * (2 * R + 2) + 4) * a := by
          rw [norm_sub_rev 1]
          nlinarith
private def gaugeDefect (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions) (W : TorusField n)
    (γ : TorusSite n → UnitQuaternion) : ℝ :=
  ∑ b ∈ bondsTouching o R,
    ‖((gaugeTransform γ W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - ((expUnit (A b) : UnitQuaternion) : ℍ[ℝ])‖ ^ 2
private lemma exists_minimal_gauge (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions)
    (W : TorusField n) (hne : ∃ γ, IsSupportedGauge o R γ) :
    ∃ γ, IsSupportedGauge o R γ ∧ ∀ γ', IsSupportedGauge o R γ' →
      gaugeDefect o R A W γ ≤ gaugeDefect o R A W γ' := by
  have hcl : IsClosed {γ : TorusSite n → UnitQuaternion | IsSupportedGauge o R γ} := by
    have : {γ : TorusSite n → UnitQuaternion | IsSupportedGauge o R γ} =
        ⋂ z : TorusSite n, {γ : TorusSite n → UnitQuaternion | z ∉ supBall o (R : ℝ) → γ z = 1} := by
      ext γ
      simp [IsSupportedGauge]
    rw [this]
    refine isClosed_iInter fun z => ?_
    by_cases hz : z ∈ supBall o (R : ℝ)
    · simp [hz]
    · simp only [hz, not_false_eq_true, forall_const]
      exact isClosed_eq (continuous_apply z) continuous_const
  have hc : IsCompact {γ : TorusSite n → UnitQuaternion | IsSupportedGauge o R γ} := hcl.isCompact
  have c1 : ∀ z, Continuous fun γ : TorusSite n → UnitQuaternion => (γ z : ℍ[ℝ]) := fun z =>
    continuous_subtype_val.comp (continuous_apply z)
  have hcont : Continuous (gaugeDefect o R A W) := by
    unfold gaugeDefect
    refine continuous_finsetSum _ fun b _ => ?_
    simp only [coe_gaugeTransform]
    exact ((((c1 _).mul continuous_const).mul (c1 _).star).sub continuous_const).norm.pow 2
  obtain ⟨γ, hγ, hmin⟩ := hc.exists_isMinOn hne hcont.continuousOn
  exact ⟨γ, hγ, fun γ' h' => hmin h'⟩
private def defectQuaternion (γ : TorusSite n → UnitQuaternion) (W : TorusField n)
    (A : TorusBond n → imaginaryQuaternions) (b : TorusBond n) : ℍ[ℝ] :=
  ((gaugeTransform γ W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) * star ((expUnit (A b) : UnitQuaternion) : ℍ[ℝ])
private lemma expUnit_zero_eq : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private lemma re_mul_comm' (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.quaternion_re_mul_comm <;> assumption
private lemma re_star_eq (a : ℍ[ℝ]) : (star a).re = a.re := by simp
private lemma inner_variation_identity (P V x y : ℍ[ℝ]) (hP : P * star P = 1) (hP' : star P * P = 1)
    (hV : star V * V = 1) (hx : star x = -x) (hy : star y = -y) :
    inner ℝ (P - V) (x * P + P * (-y)) =
      -((x * (P * star V)).re - ((P * star V) * (V * y * star V)).re) := by
  have hxr : x.re = 0 := by
    have := congrArg (fun q : ℍ[ℝ] => q.re) hx
    simp only [re_star_eq, Quaternion.re_neg] at this
    linarith
  have hyr : y.re = 0 := by
    have := congrArg (fun q : ℍ[ℝ] => q.re) hy
    simp only [re_star_eq, Quaternion.re_neg] at this
    linarith
  have e1 : (P * star V) * (V * y * star V) = P * y * star V := by
    calc (P * star V) * (V * y * star V) = P * (star V * V) * y * star V := by noncomm_ring
      _ = P * y * star V := by rw [hV, mul_one]
  have e2 : (P - V) * star (x * P + P * (-y)) =
      -((P * star P) * x) + P * y * star P + V * star P * x - V * y * star P := by
    rw [star_add, star_mul, star_mul, star_neg, hx, hy, neg_neg]
    noncomm_ring
  have t1 : (P * y * star P).re = 0 := by
    rw [re_mul_comm', ← mul_assoc, mul_assoc (star P), ← mul_assoc (star P) P y, hP', one_mul]
    exact hyr
  have t2 : (V * star P * x).re = -(x * (P * star V)).re := by
    have h : star (V * star P * x) = -(x * (P * star V)) := by
      rw [star_mul, star_mul, star_star, hx]
      noncomm_ring
    rw [← re_star_eq (V * star P * x), h]
    simp
  have t3 : (V * y * star P).re = -(P * y * star V).re := by
    have h : star (V * y * star P) = -(P * y * star V) := by
      rw [star_mul, star_mul, star_star, hy]
      noncomm_ring
    rw [← re_star_eq (V * y * star P), h]
    simp
  rw [Quaternion.inner_def, e2, e1, hP, one_mul]
  have e3 : (-x + P * y * star P + V * star P * x - V * y * star P).re =
      -x.re + (P * y * star P).re + (V * star P * x).re - (V * y * star P).re := by simp
  rw [e3, t1, t2, t3, hxr]
  ring
private lemma coe_smul_imaginary (τ : ℝ) (w : imaginaryQuaternions) :
    ((τ • w : imaginaryQuaternions) : ℍ[ℝ]) = τ • (w : ℍ[ℝ]) := rfl
private lemma star_coe_expUnit_smul (w : imaginaryQuaternions) (τ : ℝ) :
    star ((expUnit (τ • w) : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (τ • (-(w : ℍ[ℝ]))) := by
  rw [coe_expUnit, NormedSpace.star_exp, star_imaginary (τ • w), coe_smul_imaginary, smul_neg]
private lemma first_variation_eq_zero (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions)
    (W : TorusField n) (γ : TorusSite n → UnitQuaternion)
    (hγ : IsSupportedGauge o R γ)
    (hmin : ∀ γ', IsSupportedGauge o R γ' → gaugeDefect o R A W γ ≤ gaugeDefect o R A W γ')
    (χ : TorusSite n → imaginaryQuaternions) (hχ : ∀ z, z ∉ supBall o (R : ℝ) → χ z = 0) :
    ∑ b ∈ bondsTouching o R, ((((χ b.1 : imaginaryQuaternions) : ℍ[ℝ]) * defectQuaternion γ W A b).re -
      (defectQuaternion γ W A b *
        ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2)) : imaginaryQuaternions) : ℍ[ℝ])).re) = 0 := by
  set P : TorusBond n → ℍ[ℝ] := fun b => ((gaugeTransform γ W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) with hP
  set V : TorusBond n → ℍ[ℝ] := fun b => ((expUnit (A b) : UnitQuaternion) : ℍ[ℝ]) with hV
  set X : TorusBond n → ℍ[ℝ] := fun b => (χ b.1 : ℍ[ℝ]) with hX
  set Y : TorusBond n → ℍ[ℝ] := fun b => (χ (b.1 + unitStep n b.2) : ℍ[ℝ]) with hY
  let f : TorusBond n → ℝ → ℍ[ℝ] := fun b τ =>
    NormedSpace.exp (τ • X b) * P b * NormedSpace.exp (τ • (-Y b))
  have hf : ∀ b, HasDerivAt (f b) (X b * P b + P b * (-Y b)) 0 := by
    intro b
    have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X b) (0 : ℝ)
    have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Y b) (0 : ℝ)
    have h3 : HasDerivAt (f b) _ 0 := (h1.mul_const (P b)).mul h2
    exact h3.congr_deriv (by simp)
  have f0 : ∀ b, f b 0 = P b := by
    intro b
    simp [f]
  let γτ : ℝ → TorusSite n → UnitQuaternion := fun τ z => expUnit (τ • χ z) * γ z
  have hγτ : ∀ τ, IsSupportedGauge o R (γτ τ) := by
    intro τ z hz
    simp [γτ, hχ z hz, hγ z hz, expUnit_zero_eq]
  have fe : ∀ b τ, ((gaugeTransform (γτ τ) W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) = f b τ := by
    intro b τ
    show (((expUnit (τ • χ b.1) : UnitQuaternion) : ℍ[ℝ]) * (γ b.1 : ℍ[ℝ])) * (W b.1 b.2 : ℍ[ℝ]) *
      star (((expUnit (τ • χ (b.1 + unitStep n b.2)) : UnitQuaternion) : ℍ[ℝ]) *
        (γ (b.1 + unitStep n b.2) : ℍ[ℝ])) =
      NormedSpace.exp (τ • X b) *
        ((γ b.1 : ℍ[ℝ]) * (W b.1 b.2 : ℍ[ℝ]) * star (γ (b.1 + unitStep n b.2) : ℍ[ℝ])) *
        NormedSpace.exp (τ • (-Y b))
    rw [star_mul, star_coe_expUnit_smul, coe_expUnit, coe_smul_imaginary]
    simp only [mul_assoc, hX, hY]
  have hF : HasDerivAt (fun τ => ∑ b ∈ bondsTouching o R, ‖f b τ - V b‖ ^ 2)
      (∑ b ∈ bondsTouching o R, 2 * inner ℝ (f b 0 - V b) (X b * P b + P b * (-Y b))) 0 :=
    HasDerivAt.fun_sum fun b _ => ((hf b).sub_const (V b)).norm_sq
  have hloc : IsLocalMin (fun τ => ∑ b ∈ bondsTouching o R, ‖f b τ - V b‖ ^ 2) 0 := by
    refine Filter.Eventually.of_forall fun τ => ?_
    have h := hmin _ (hγτ τ)
    simp only [gaugeDefect, fe] at h
    simpa only [f0, hP, hV] using h
  have hz := hloc.hasDerivAt_eq_zero hF
  have hterm : ∀ b ∈ bondsTouching o R, 2 * inner ℝ (f b 0 - V b) (X b * P b + P b * (-Y b)) =
      -2 * ((((χ b.1 : imaginaryQuaternions) : ℍ[ℝ]) * defectQuaternion γ W A b).re -
      (defectQuaternion γ W A b *
        ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2)) : imaginaryQuaternions) : ℍ[ℝ])).re) := by
    intro b _
    rw [f0, inner_variation_identity (P b) (V b) (X b) (Y b) (mul_star_self_unit _) (star_mul_self_unit _)
      (star_mul_self_unit _) (star_imaginary _) (star_imaginary _)]
    have e : ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2)) : imaginaryQuaternions) : ℍ[ℝ]) =
        V b * Y b * star (V b) := rfl
    rw [e]
    show _ = -2 * ((X b * (P b * star (V b))).re - ((P b * star (V b)) * (V b * Y b * star (V b))).re)
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hz
  linarith
private lemma inner_imPart (q : ℍ[ℝ]) (d : imaginaryQuaternions) :
    inner ℝ (imPart q) d = -(((d : ℍ[ℝ])) * q).re := by
  rw [Submodule.coe_inner, Quaternion.inner_def, star_imaginary, coe_imPart]
  have hd := re_imaginary d
  simp only [Quaternion.re_mul, mul_neg, Quaternion.re_neg, hd]
  simp
  ring
private lemma curvature_gauge_invariant (γ : TorusSite n → UnitQuaternion) (W : TorusField n)
    (x : TorusSite n) (μ ν : Fin 4) :
    curvature (gaugeTransform γ W) x μ ν = curvature W x μ ν := by apply _root_.YangMills.SharedProofs.p70158 <;> assumption
private theorem exists_slice_in_chart (o : TorusSite n) (R : ℕ) (hR : 1 ≤ R) (hn : 16 * R < n)
    (A A' : TorusBond n → imaginaryQuaternions)
    (W : TorusField n) (g : TorusSite n → UnitQuaternion) (a ε δ : ℝ) (a0 : 0 ≤ a) (haε : a ≤ ε)
    (ε1 : ε ≤ 1 / 4)
    (hE : ((bondsTouching o R).card : ℝ) * ((16 * (2 * R + 2) + 4) * a) ^ 2 ≤ ε ^ 2)
    (hsm : 192 * ε ^ 2 ≤ δ)
    (hA : ∀ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), ‖A b‖ ≤ a)
    (hA' : ∀ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), ‖A' b‖ ≤ a)
    (hg : ∀ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), gaugeTransform g W b.1 b.2 = expUnit (A' b))
    (hW : ∀ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), b ∉ bondsTouching o R →
      W b.1 b.2 = expUnit (A b))
    (hcold : ∀ p ∈ plaquettesIn (supBall o (2 * (R : ℝ))), curvature W p.1 p.2.1 p.2.2 ≤ δ) :
    ∃ (γ : TorusSite n → UnitQuaternion) (ζ : TorusBond n → imaginaryQuaternions),
      IsSupportedGauge o R γ ∧ ζ ∈ gaugeSlice o R A ∧
      IsInChart (supBall o (2 * (R : ℝ))) A ζ (gaugeTransform γ W) ∧
      curlNormSq (supBall o (2 * (R : ℝ))) (A + ζ) ≤
        ((plaquettesIn (supBall o (2 * (R : ℝ)))).card : ℝ) * (2 * δ) ^ 2 := by
  classical
  have ε0 : 0 ≤ ε := a0.trans haε
  obtain ⟨γ₀, h₀, hB⟩ := exists_gauge_near o R hR hn A A' W g a (by linarith) a0 hA hA' hg hW
  obtain ⟨γ, hγ, hmin⟩ := exists_minimal_gauge o R A W ⟨γ₀, h₀⟩
  have gap₀ : gaugeDefect o R A W γ₀ ≤ ε ^ 2 := by
    refine le_trans ?_ hE
    unfold gaugeDefect
    calc _ ≤ ∑ b ∈ bondsTouching o R, ((16 * (2 * R + 2) + 4) * a) ^ 2 :=
          Finset.sum_le_sum fun b hb => pow_le_pow_left₀ (norm_nonneg _) (hB b hb) 2
      _ = _ := by simp
  have gapε := (hmin γ₀ h₀).trans gap₀
  set P : TorusBond n → ℍ[ℝ] := fun b => ((gaugeTransform γ W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) with hP
  set V : TorusBond n → ℍ[ℝ] := fun b => ((expUnit (A b) : UnitQuaternion) : ℍ[ℝ]) with hV
  set M : TorusBond n → ℍ[ℝ] := defectQuaternion γ W A with hMdef
  have Mdef : ∀ b, M b = P b * star (V b) := fun b => rfl
  have VV : ∀ b, star (V b) * V b = 1 := fun b => star_mul_self_unit _
  have VV' : ∀ b, V b * star (V b) = 1 := fun b => mul_star_self_unit _
  have nV : ∀ b, ‖V b‖ = 1 := fun b => norm_coe_unit _
  have nP : ∀ b, ‖P b‖ = 1 := fun b => norm_coe_unit _
  have nM : ∀ b, ‖M b‖ = 1 := by
    intro b
    rw [Mdef, norm_mul, norm_star, nV, nP, one_mul]
  have PMV : ∀ b, P b = M b * V b := by
    intro b
    rw [Mdef, mul_assoc, VV, mul_one]
  have hMd : ∀ b, ‖M b - 1‖ = ‖P b - V b‖ := by
    intro b
    have e : M b - 1 = (P b - V b) * star (V b) := by
      rw [sub_mul, VV', Mdef]
    rw [e, norm_mul, norm_star, nV, mul_one]
  have hM : ∀ b ∈ bondsTouching o R, ‖M b - 1‖ ≤ ε := by
    intro b hb
    rw [hMd]
    have h1 : ‖P b - V b‖ ^ 2 ≤ gaugeDefect o R A W γ :=
      Finset.single_le_sum (f := fun b : TorusBond n =>
        ‖((gaugeTransform γ W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) -
          ((expUnit (A b) : UnitQuaternion) : ℍ[ℝ])‖ ^ 2)
        (fun _ _ => sq_nonneg _) hb
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) ε0 two_ne_zero).mp (h1.trans gapε)
  set ζ : TorusBond n → imaginaryQuaternions :=
    fun b => if b ∈ bondsTouching o R then imPart (M b) else 0 with hζ
  have ζin : ∀ b ∈ bondsTouching o R, ζ b = imPart (M b) := by
    intro b hb
    simp [hζ, hb]
  have ζoff : ∀ b, b ∉ bondsTouching o R → ζ b = 0 := by
    intro b hb
    simp [hζ, hb]
  have Poff : ∀ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), b ∉ bondsTouching o R → P b = V b := by
    intro b hb hi
    rw [mem_bondsTouching_iff, not_or] at hi
    have e := hW b hb (by rw [mem_bondsTouching_iff, not_or]; exact hi)
    show (γ b.1 : ℍ[ℝ]) * (W b.1 b.2 : ℍ[ℝ]) * star (γ (b.1 + unitStep n b.2) : ℍ[ℝ]) = _
    rw [hγ _ hi.1, hγ _ hi.2, e]
    simp [hV]
  have hchart : IsInChart (supBall o (2 * (R : ℝ))) A ζ (gaugeTransform γ W) := by
    intro b hb
    show P b = chartPoint (A b) (ζ b)
    unfold chartPoint
    by_cases hi : b ∈ bondsTouching o R
    · rw [ζin b hi, chart_form_eq (M b) (nM b) ((hM b hi).trans (by linarith))]
      exact PMV b
    · rw [ζoff b hi, Poff b hb hi]
      simp [hV]
  have leg : ∀ b ∈ bondsWithin (supBall o (2 * (R : ℝ))),
      ‖P b - 1‖ ≤ 4 * ε ∧ ‖P b - 1 - ((A b + ζ b : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 4 * ε ^ 2 := by
    intro b hb
    have bA : ‖A b‖ ≤ ε := (hA b hb).trans haε
    have bA1 : ‖A b‖ ≤ 1 := by linarith
    have v1 : ‖V b - 1‖ ≤ 2 * ε := by
      have := norm_expUnit_sub_one_le (A b) bA1
      show ‖((expUnit (A b) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ _
      linarith
    have v2 : ‖V b - 1 - (A b : ℍ[ℝ])‖ ≤ ε ^ 2 := by
      have h := norm_exp_sub_one_sub_le (A b) bA1
      have h2 : ‖A b‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) bA 2
      show ‖((expUnit (A b) : UnitQuaternion) : ℍ[ℝ]) - 1 - (A b : ℍ[ℝ])‖ ≤ _
      rw [coe_expUnit]
      linarith
    by_cases hi : b ∈ bondsTouching o R
    · have m1 := hM b hi
      set m := M b - 1 with hm
      set v := V b - 1 with hv
      have mv : ‖m * v‖ ≤ 2 * ε ^ 2 := by
        rw [norm_mul]
        nlinarith [norm_nonneg m, norm_nonneg v]
      have eP : P b - 1 = m + v + m * v := by
        rw [PMV b, hm, hv]
        noncomm_ring
      have hre : |(M b).re - 1| ≤ ε ^ 2 / 2 := by
        have h1 := norm_sub_one_sq (M b) (nM b)
        have h2 : ‖M b - 1‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) m1 2
        have h3 : 0 ≤ ‖M b - 1‖ ^ 2 := sq_nonneg _
        rw [abs_le]
        constructor <;> linarith
      have eim : m - ((imPart (M b) : imaginaryQuaternions) : ℍ[ℝ]) = (((M b).re - 1 : ℝ) : ℍ[ℝ]) := by
        have := re_add_imPart (M b)
        rw [hm]
        nth_rewrite 1 [← this]
        push_cast
        abel
      constructor
      · rw [eP]
        calc ‖m + v + m * v‖ ≤ ‖m‖ + ‖v‖ + ‖m * v‖ := norm_add₃_le
          _ ≤ 4 * ε := by nlinarith
      · have e2 : P b - 1 - ((A b + ζ b : imaginaryQuaternions) : ℍ[ℝ]) =
            (m - ((imPart (M b) : imaginaryQuaternions) : ℍ[ℝ])) + (v - (A b : ℍ[ℝ])) + m * v := by
          rw [eP, ζin b hi]
          show m + v + m * v - ((A b : ℍ[ℝ]) + ((imPart (M b) : imaginaryQuaternions) : ℍ[ℝ])) = _
          abel
        rw [e2, eim]
        calc _ ≤ ‖(((M b).re - 1 : ℝ) : ℍ[ℝ])‖ + ‖v - (A b : ℍ[ℝ])‖ + ‖m * v‖ := norm_add₃_le
          _ ≤ ε ^ 2 / 2 + ε ^ 2 + 2 * ε ^ 2 := by
              rw [Quaternion.norm_coe, Real.norm_eq_abs]
              linarith
          _ ≤ 4 * ε ^ 2 := by nlinarith [sq_nonneg ε]
    · rw [Poff b hb hi, ζoff b hi]
      constructor
      · linarith
      · have : ((A b + 0 : imaginaryQuaternions) : ℍ[ℝ]) = (A b : ℍ[ℝ]) := by simp
        rw [this]
        nlinarith [sq_nonneg ε]
  refine ⟨γ, ζ, hγ, ⟨ζoff, fun χ hχ => ?_⟩, hchart, ?_⟩
  · have fv := first_variation_eq_zero o R A W γ hγ hmin χ hχ
    rw [← Finset.sum_subset (Finset.subset_univ (bondsTouching o R)) (fun b _ hb => by simp [ζoff b hb])]
    have hterm : ∀ b ∈ bondsTouching o R, inner ℝ (ζ b) (covariantGrad A χ b) =
        -((((χ b.1 : imaginaryQuaternions) : ℍ[ℝ]) * defectQuaternion γ W A b).re -
          (defectQuaternion γ W A b *
            ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2)) : imaginaryQuaternions) : ℍ[ℝ])).re) := by
      intro b hb
      rw [ζin b hb, inner_imPart]
      have e : ((covariantGrad A χ b : imaginaryQuaternions) : ℍ[ℝ]) = (χ b.1 : ℍ[ℝ]) -
          ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2)) : imaginaryQuaternions) : ℍ[ℝ]) := rfl
      rw [e, sub_mul, Quaternion.re_sub,
        re_mul_comm' ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2)) : imaginaryQuaternions) : ℍ[ℝ])]
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, fv, neg_zero]
  · unfold curlNormSq
    have hp2 : ∀ p ∈ plaquettesIn (supBall o (2 * (R : ℝ))), ‖lieFormCurl (A + ζ) p‖ ≤ 2 * δ := by
      rintro ⟨x, μ, ν⟩ hp
      have hc := hcold _ hp
      simp only at hc
      have hcor : ∀ z ∈ plaquetteVertices x μ ν, z ∈ supBall o (2 * (R : ℝ)) := by
        simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact hp.2
      have k1 : x ∈ supBall o (2 * (R : ℝ)) := hcor _ (by simp [plaquetteVertices])
      have k2 : x + unitStep n μ ∈ supBall o (2 * (R : ℝ)) := hcor _ (by simp [plaquetteVertices])
      have k3 : x + unitStep n ν ∈ supBall o (2 * (R : ℝ)) := hcor _ (by simp [plaquetteVertices])
      have k4 : x + unitStep n μ + unitStep n ν ∈ supBall o (2 * (R : ℝ)) :=
        hcor _ (by simp [plaquetteVertices])
      have b1 : (x, μ) ∈ bondsWithin (supBall o (2 * (R : ℝ))) := (mem_bondsWithin_iff _ _).mpr ⟨k1, k2⟩
      have b2 : (x + unitStep n μ, ν) ∈ bondsWithin (supBall o (2 * (R : ℝ))) :=
        (mem_bondsWithin_iff _ _).mpr ⟨k2, k4⟩
      have b3 : (x + unitStep n ν, μ) ∈ bondsWithin (supBall o (2 * (R : ℝ))) :=
        (mem_bondsWithin_iff _ _).mpr ⟨k3, by
          show x + unitStep n ν + unitStep n μ ∈ _; rw [add_right_comm]; exact k4⟩
      have b4 : (x, ν) ∈ bondsWithin (supBall o (2 * (R : ℝ))) := (mem_bondsWithin_iff _ _).mpr ⟨k1, k3⟩
      obtain ⟨s1, r1⟩ := leg _ b1
      obtain ⟨s2, r2⟩ := leg _ b2
      obtain ⟨s3, r3⟩ := leg _ b3
      obtain ⟨s4, r4⟩ := leg _ b4
      set t₁ := P (x, μ) - 1 with ht₁
      set t₂ := P (x + unitStep n μ, ν) - 1 with ht₂
      set t₃ := P (x + unitStep n ν, μ) - 1 with ht₃
      set t₄ := P (x, ν) - 1 with ht₄
      set a₁ : ℍ[ℝ] := ((A (x, μ) + ζ (x, μ) : imaginaryQuaternions) : ℍ[ℝ]) with ha₁
      set a₂ : ℍ[ℝ] := ((A (x + unitStep n μ, ν) + ζ (x + unitStep n μ, ν) : imaginaryQuaternions) : ℍ[ℝ])
        with ha₂
      set a₃ : ℍ[ℝ] := ((A (x + unitStep n ν, μ) + ζ (x + unitStep n ν, μ) : imaginaryQuaternions) : ℍ[ℝ])
        with ha₃
      set a₄ : ℍ[ℝ] := ((A (x, ν) + ζ (x, ν) : imaginaryQuaternions) : ℍ[ℝ]) with ha₄
      have s3a : star a₃ = -a₃ := star_imaginary _
      have s4a : star a₄ = -a₄ := star_imaginary _
      have hol : (((holonomy (gaugeTransform γ W) x μ ν : UnitQuaternion) : ℍ[ℝ])) =
          (1 + t₁) * (1 + t₂) * (1 + star t₃) * (1 + star t₄) := by
        have e : ((holonomy (gaugeTransform γ W) x μ ν : UnitQuaternion) : ℍ[ℝ]) =
            P (x, μ) * P (x + unitStep n μ, ν) *
            star (P (x + unitStep n ν, μ)) * star (P (x, ν)) := rfl
        rw [e]
        simp only [ht₁, ht₂, ht₃, ht₄, star_sub, star_one]
        noncomm_ring
      have fp := fourfold_product_expansion t₁ t₂ (star t₃) (star t₄) (4 * ε) (by linarith) s1 s2
        (by rw [norm_star]; exact s3) (by rw [norm_star]; exact s4)
      rw [← hol] at fp
      have hcv : ‖((holonomy (gaugeTransform γ W) x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ δ := by
        have := curvature_gauge_invariant γ W x μ ν
        unfold curvature at this
        rw [this]
        exact hc
      have ec : ((lieFormCurl (A + ζ) (x, μ, ν) : imaginaryQuaternions) : ℍ[ℝ]) = a₁ + a₂ - a₃ - a₄ := rfl
      have e5 : a₁ + a₂ - a₃ - a₄ =
          (((holonomy (gaugeTransform γ W) x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1) -
          ((((holonomy (gaugeTransform γ W) x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1 -
            (t₁ + t₂ + star t₃ + star t₄))) -
          ((t₁ - a₁) + (t₂ - a₂) + star (t₃ - a₃) + star (t₄ - a₄)) := by
        have e6 : star (t₃ - a₃) = star t₃ + a₃ := by rw [star_sub, s3a, sub_neg_eq_add]
        have e7 : star (t₄ - a₄) = star t₄ + a₄ := by rw [star_sub, s4a, sub_neg_eq_add]
        rw [e6, e7]
        abel
      show ‖((lieFormCurl (A + ζ) (x, μ, ν) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 2 * δ
      rw [ec, e5]
      have n3 : ‖star (t₃ - a₃)‖ ≤ 4 * ε ^ 2 := by rw [norm_star]; exact r3
      have n4 : ‖star (t₄ - a₄)‖ ≤ 4 * ε ^ 2 := by rw [norm_star]; exact r4
      have sum4 : ‖(t₁ - a₁) + (t₂ - a₂) + star (t₃ - a₃) + star (t₄ - a₄)‖ ≤ 16 * ε ^ 2 := by
        calc _ ≤ ‖(t₁ - a₁) + (t₂ - a₂) + star (t₃ - a₃)‖ + ‖star (t₄ - a₄)‖ := norm_add_le _ _
          _ ≤ ‖t₁ - a₁‖ + ‖t₂ - a₂‖ + ‖star (t₃ - a₃)‖ + ‖star (t₄ - a₄)‖ := by
              have := norm_add₃_le (a := t₁ - a₁) (b := t₂ - a₂) (c := star (t₃ - a₃))
              linarith
          _ ≤ 16 * ε ^ 2 := by linarith
      calc _ ≤ ‖((holonomy (gaugeTransform γ W) x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
            ‖((holonomy (gaugeTransform γ W) x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1 -
              (t₁ + t₂ + star t₃ + star t₄)‖ +
            ‖(t₁ - a₁) + (t₂ - a₂) + star (t₃ - a₃) + star (t₄ - a₄)‖ := by
            refine (norm_sub_le _ _).trans ?_
            have := norm_sub_le (((holonomy (gaugeTransform γ W) x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1)
              (((holonomy (gaugeTransform γ W) x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1 -
                (t₁ + t₂ + star t₃ + star t₄))
            linarith
        _ ≤ δ + 11 * (4 * ε) ^ 2 + 16 * ε ^ 2 := by linarith
        _ ≤ 2 * δ := by nlinarith
    calc _ ≤ ∑ p ∈ plaquettesIn (supBall o (2 * (R : ℝ))), (2 * δ) ^ 2 :=
          Finset.sum_le_sum fun p hp => pow_le_pow_left₀ (norm_nonneg _) (hp2 p hp) 2
      _ = _ := by simp
end Main
private lemma eventually_box_small (κ₀ : ℝ) (h1 : 1 / 27 ≤ κ₀) (h2 : κ₀ ≤ 1 / 21) (R₀ : ℕ) :
    ∃ xs : ℝ, ∀ x, xs ≤ x → 1 < x ∧ R₀ ≤ boxRadius κ₀ x ∧ 1 ≤ boxRadius κ₀ x ∧
      2 * 10 ^ 11 * (boxRadius κ₀ x : ℝ) ^ 8 * boxScale x ≤ 1 := by
  have κpos : 0 < κ₀ := by linarith
  set p : ℝ := 1 / 2 - 8 * κ₀ with hp
  have ppos : 0 < p := by rw [hp]; linarith
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, (R₀ : ℝ) ≤ x ^ κ₀ :=
    (tendsto_rpow_atTop κpos).eventually (Filter.eventually_ge_atTop _)
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ (1 / (1024 * 10 ^ 11)) * ‖x ^ p‖ :=
    (isLittleO_log_rpow_atTop ppos).def (by positivity)
  obtain ⟨xs, h⟩ := Filter.eventually_atTop.mp (e1.and (e2.and (Filter.eventually_gt_atTop (1 : ℝ))))
  refine ⟨xs, fun x hx => ?_⟩
  obtain ⟨a1, a2, a3⟩ := h x hx
  have x0 : 0 < x := by linarith
  have xk : 1 ≤ x ^ κ₀ := Real.one_le_rpow a3.le κpos.le
  have c1 : x ^ κ₀ ≤ (boxRadius κ₀ x : ℝ) := Nat.le_ceil _
  have c2 : (boxRadius κ₀ x : ℝ) < x ^ κ₀ + 1 := Nat.ceil_lt_add_one (by linarith)
  have r1 : 1 ≤ boxRadius κ₀ x := by
    have : (1 : ℝ) ≤ (boxRadius κ₀ x : ℝ) := by linarith
    exact_mod_cast this
  have r0 : R₀ ≤ boxRadius κ₀ x := by
    have : (R₀ : ℝ) ≤ (boxRadius κ₀ x : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨a3, r0, r1, ?_⟩
  set R : ℝ := (boxRadius κ₀ x : ℝ) with hR
  have lg : 0 < Real.log x := Real.log_pos a3
  set y : ℝ := x ^ p with hy
  have ypos : 0 < y := Real.rpow_pos_of_pos x0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos lg, abs_of_pos ypos] at a2
  have R8 : R ^ 8 ≤ 256 * (x ^ κ₀) ^ 8 := by
    have : R ≤ 2 * x ^ κ₀ := by linarith
    calc R ^ 8 ≤ (2 * x ^ κ₀) ^ 8 := pow_le_pow_left₀ (by linarith) this 8
      _ = 256 * (x ^ κ₀) ^ 8 := by ring
  have ex : (x ^ κ₀) ^ 8 * x ^ (-(1 / 2 : ℝ)) * y = 1 := by
    have e : (x ^ κ₀) ^ 8 = x ^ (8 * κ₀) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul x0.le]
      congr 1
      push_cast
      ring
    rw [e, hy, ← Real.rpow_add x0, ← Real.rpow_add x0, hp]
    have : 8 * κ₀ + -(1 / 2 : ℝ) + (1 / 2 - 8 * κ₀) = 0 := by ring
    rw [this, Real.rpow_zero]
  set w : ℝ := (x ^ κ₀) ^ 8 * x ^ (-(1 / 2 : ℝ)) with hw
  unfold boxScale
  calc 2 * 10 ^ 11 * R ^ 8 * (2 * x ^ (-(1 / 2 : ℝ)) * Real.log x)
      ≤ 2 * 10 ^ 11 * (256 * (x ^ κ₀) ^ 8) * (2 * x ^ (-(1 / 2 : ℝ)) * Real.log x) := by
        gcongr
    _ = 1024 * 10 ^ 11 * (w * Real.log x) := by rw [hw]; ring
    _ ≤ 1024 * 10 ^ 11 * (w * ((1 / (1024 * 10 ^ 11)) * y)) := by gcongr
    _ = w * y := by ring
    _ = 1 := ex
theorem coldFieldsInChart (h₁ : coldAxialGaugeStatement)
    (h₂ : cubeHessianStatement) : coldFieldsInChartStatement := by
  intro Tb hTb κ₀ hκ1 hκ2
  obtain ⟨CQ, R₀, hCQ, hform⟩ := h₂ Tb hTb
  obtain ⟨xs₁, hax⟩ := h₁ κ₀ hκ1 hκ2
  obtain ⟨xs₂, hlarge⟩ := eventually_box_small κ₀ hκ1 hκ2 R₀
  refine ⟨40000 * CQ, max xs₁ xs₂, by positivity, ?_⟩
  intro x R k n _ o A hx hRx hn hAx W hcold hW
  obtain ⟨hx1, hR0, hR1, hsmall⟩ := hlarge x ((le_max_right _ _).trans hx)
  rw [← hRx] at hR0 hR1 hsmall
  obtain ⟨gF, AF, -, -, hV⟩ := hax x R n o ((le_max_left _ _).trans hx) hRx hn
  obtain ⟨-, hg, hAF⟩ := hV W hcold
  set δ := boxScale x with hδ
  have δ0 : 0 ≤ δ := by
    have l : 0 < Real.log x := Real.log_pos hx1
    have : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    rw [hδ]; unfold boxScale; positivity
  have Rr : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have R4 : (R : ℝ) ^ 4 ≤ (R : ℝ) ^ 8 := pow_le_pow_right₀ Rr (by norm_num)
  have R1 : (R : ℝ) ≤ (R : ℝ) ^ 4 := by
    calc (R : ℝ) = (R : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (R : ℝ) ^ 4 := pow_le_pow_right₀ Rr (by norm_num)
  have hRδ : (R : ℝ) ^ 8 * δ ≤ 1 / (2 * 10 ^ 11) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  set ε : ℝ := 24000 * (R : ℝ) ^ 4 * δ with hε
  have hn3 : 2 < n := by omega
  have card := card_bondsTouching_le hn3 o R
  have hE : ((bondsTouching o R).card : ℝ) * ((16 * (2 * R + 2) + 4) * (7 * R * δ)) ^ 2 ≤ ε ^ 2 := by
    have c1 : (2 * ((R + 1 : ℕ) : ℝ) + 1) ^ 4 ≤ (5 * (R : ℝ)) ^ 4 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 4
      push_cast
      linarith
    have c2 : ((bondsTouching o R).card : ℝ) ≤ 2500 * (R : ℝ) ^ 4 := by
      calc _ ≤ 4 * (5 * (R : ℝ)) ^ 4 := by linarith
        _ = _ := by ring
    have c3 : (16 * (2 * (R : ℝ) + 2) + 4) * (7 * R * δ) ≤ 476 * (R : ℝ) ^ 2 * δ := by
      have : (16 * (2 * (R : ℝ) + 2) + 4) * (7 * R) ≤ 476 * (R : ℝ) ^ 2 := by nlinarith
      nlinarith
    have c4 : ((16 * (2 * (R : ℝ) + 2) + 4) * (7 * R * δ)) ^ 2 ≤ (476 * (R : ℝ) ^ 2 * δ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) c3 2
    calc _ ≤ (2500 * (R : ℝ) ^ 4) * (476 * (R : ℝ) ^ 2 * δ) ^ 2 := by gcongr
      _ = 566440000 * ((R : ℝ) ^ 4 * δ) ^ 2 * (R : ℝ) ^ 0 := by ring
      _ ≤ ε ^ 2 := by
          rw [hε]
          have : 0 ≤ ((R : ℝ) ^ 4 * δ) ^ 2 := sq_nonneg _
          nlinarith
  have haε : 7 * (R : ℝ) * δ ≤ ε := by
    rw [hε]
    nlinarith
  have ε1 : ε ≤ 1 / 4 := by
    have : (R : ℝ) ^ 4 * δ ≤ (R : ℝ) ^ 8 * δ := by gcongr
    rw [hε]
    nlinarith
  have hsm : 192 * ε ^ 2 ≤ δ := by
    have h8 : ((R : ℝ) ^ 4) ^ 2 = (R : ℝ) ^ 8 := by ring
    have : 192 * ε ^ 2 = 110592000000 * ((R : ℝ) ^ 8 * δ) * δ := by
      rw [hε, ← h8]; ring
    rw [this]
    have h9 : 110592000000 * ((R : ℝ) ^ 8 * δ) ≤ 1 := by
      have := hRδ
      norm_num at this ⊢
      linarith
    nlinarith
  obtain ⟨γ, ζ, hγ, hsl, hch, hcs⟩ := exists_slice_in_chart o R hR1 hn A (AF W) W (gF W) (7 * R * δ) ε δ
    (by positivity) haε ε1 hE hsm hAx.norm_le hAF.norm_le hg hW hcold
  refine ⟨γ, ζ, hγ, ⟨hsl, ?_⟩, hch⟩
  have hq := ((hform k n o R hR0 hn).2.2.2.2.1 (A + ζ)).2
  refine hq.trans ?_
  have hplaq := card_plaquettesIn_le o (2 * R)
  rw [← two_mul_natCast] at hplaq
  have c1 : (2 * ((2 * R : ℕ) : ℝ) + 1) ^ 4 ≤ (5 * (R : ℝ)) ^ 4 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 4
    push_cast
    linarith
  have c2 : ((plaquettesIn (supBall o (2 * (R : ℝ)))).card : ℝ) ≤ 10000 * (R : ℝ) ^ 4 := by
    have c1' : (2 * (2 * (R : ℝ)) + 1) ^ 4 ≤ (5 * (R : ℝ)) ^ 4 := by
      have := c1
      push_cast at this
      exact this
    calc _ ≤ 16 * (5 * (R : ℝ)) ^ 4 := by linarith
      _ = _ := by ring
  calc CQ * curlNormSq (supBall o (2 * (R : ℝ))) (A + ζ)
      ≤ CQ * ((10000 * (R : ℝ) ^ 4) * (2 * δ) ^ 2) := by
        have : curlNormSq (supBall o (2 * (R : ℝ))) (A + ζ) ≤ (10000 * (R : ℝ) ^ 4) * (2 * δ) ^ 2 :=
          hcs.trans (by gcongr)
        gcongr
    _ = 40000 * CQ * (R : ℝ) ^ 4 * δ ^ 2 := by ring
end YangMills.Construction.BoxGaussian
end
