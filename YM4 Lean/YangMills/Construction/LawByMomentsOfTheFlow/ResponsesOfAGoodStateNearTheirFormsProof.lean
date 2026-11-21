import YangMills.Construction.LawByMomentsOfTheFlow.ClassicalFormsNearTheResponsesProof
import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormAcrossAStepProof
import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOnACircle
import YangMills.Construction.LawByMomentsOfTheFlow.GradientsOfAStepAreFarApartProof
import YangMills.Construction.LawByMomentsOfTheFlow.ResponsesOfAGoodStateNearTheirForms
import YangMills.Construction.LawByMomentsOfTheFlow.TaylorAlongAForm
import YangMills.Construction.LawByMomentsOfTheFlow.TheCutOfAGoodState
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses
open BlockAverages hiding unitStep
section Sums
private theorem sum_triple_bonds_weight_le {κ : ℝ} (hκ : 0 < κ) : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (R : ℝ), 0 ≤ R →
    ∑ c : Fin 3 → TorusBond n, (∏ l, (R + 1 + (TorusFields.supDist (c l).1 y : ℝ))) *
      Real.exp (-(κ * (supportDiam y c : ℝ))) ≤ Cs * (R + 1) ^ 3 := by
  set θ := κ / 3 with hθd
  have hθ : 0 < θ := by positivity
  set Z : ℝ := (2 * (((1 : ℕ) : ℝ) + 1) / θ + 1) ^ 1 * (4 * ExponentialSums.expLatticeSum (θ / 2)) with hZ
  refine ⟨(max Z 0) ^ 3, by positivity, fun n _ y R hR => ?_⟩
  let f : TorusBond n → ℝ := fun b =>
    (R + 1 + (TorusFields.supDist b.1 y : ℝ)) * Real.exp (-θ * (TorusFields.supDist b.1 y : ℝ))
  have hf : ∀ c : Fin 3 → TorusBond n, (∏ l, (R + 1 + (TorusFields.supDist (c l).1 y : ℝ))) *
      Real.exp (-(κ * (supportDiam y c : ℝ))) ≤ ∏ l, f (c l) := by
    intro c
    simp only [f]
    rw [Finset.prod_mul_distrib]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun l _ => by positivity)
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    have hd : ∀ l, (TorusFields.supDist (c l).1 y : ℝ) ≤ (supportDiam y c : ℝ) := by
      intro l
      have h1 : TorusFields.supDist y (c l).1 ≤ supportDiam y c :=
        le_max_of_le_left (Finset.le_sup (f := fun l : Fin 3 => TorusFields.supDist y (c l).1) (Finset.mem_univ l))
      rw [supDist_comm]
      exact_mod_cast h1
    rw [Fin.sum_univ_three]
    have h0 := hd 0
    have h1 := hd 1
    have h2 := hd 2
    have e : κ = 3 * θ := by rw [hθd]; ring
    rw [e]
    nlinarith
  have hS : ∑ b : TorusBond n, f b ≤ (R + 1) * max Z 0 := by
    have h1 := LatticeSums.sum_torusBonds_pow_mul_exp_le hθ 1 y
    calc ∑ b : TorusBond n, f b
        ≤ ∑ b : TorusBond n, (R + 1) * ((1 + (TorusFields.supDist b.1 y : ℝ)) ^ 1 *
            Real.exp (-θ * (TorusFields.supDist b.1 y : ℝ))) := by
          refine Finset.sum_le_sum fun b _ => ?_
          simp only [f, pow_one]
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have : (0 : ℝ) ≤ TorusFields.supDist b.1 y := Nat.cast_nonneg _
          nlinarith
      _ = (R + 1) * ∑ b : TorusBond n,
            (1 + (TorusFields.supDist b.1 y : ℝ)) ^ 1 * Real.exp (-θ * (TorusFields.supDist b.1 y : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ (R + 1) * max Z 0 := by
          refine mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (by positivity)
  have hS0 : 0 ≤ ∑ b : TorusBond n, f b := Finset.sum_nonneg fun b _ => by
    simp only [f]
    positivity
  calc _ ≤ ∑ c : Fin 3 → TorusBond n, ∏ l, f (c l) := Finset.sum_le_sum fun c _ => hf c
    _ = (∑ b : TorusBond n, f b) ^ 3 := (Fintype.sum_pow f 3).symm
    _ ≤ ((R + 1) * max Z 0) ^ 3 := pow_le_pow_left₀ hS0 hS 3
    _ = (max Z 0) ^ 3 * (R + 1) ^ 3 := by ring
private theorem taylor_remainder_le (hTy : taylorAlongFormStatement) {n : ℕ} [NeZero n] (p : _root_.YangMills.Construction.TorusLumps.StepParameters)
    {G : TorusField n → ℝ} {B : TorusBond n → imaginaryQuaternions} {y : TorusSite n} {v₀ ρ Ct Ctr : ℝ}
    (hv₀ : 0 ≤ v₀) (hρ : 0 ≤ ρ) (hCt : 0 ≤ Ct)
    (hC3 : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ContDiffThreeAt G (expField v B))
    (hD : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ∀ (c : Fin 3 → TorusBond n) (X : Fin 3 → imaginaryQuaternions), AreUnitVectors X →
      |mixedDeriv G (expField v B) c X| ≤ Ct / p.weight (supportDiam y c))
    (hF : HasQuadraticFormAtIdentity G) (hB : ∀ b, ‖B b‖ ≤ 4 * v₀ * (ρ + 1 + (TorusFields.supDist b.1 y : ℝ)))
    (htr : ∑ c : Fin 3 → TorusBond n, (∏ l, (ρ + 1 + (TorusFields.supDist (c l).1 y : ℝ))) *
      Real.exp (-(p.weightRate * (supportDiam y c : ℝ))) ≤ Ctr * (ρ + 1) ^ 3) :
    |G (expField 1 B) - G (trivialField n) - 1 / 2 * colourEval (hessianAtIdentity G) (toColourForm B) (toColourForm B)| ≤
      64 * v₀ ^ 3 * Ct * (Ctr * (ρ + 1) ^ 3) := by
  refine (hTy n G B (fun c => Ct / p.weight (supportDiam y c)) hC3 hD hF).trans ?_
  have hw : ∀ m : ℕ, (p.weight m)⁻¹ ≤ Real.exp (-(p.weightRate * (m : ℝ))) := by
    intro m
    rw [Real.exp_neg]
    apply inv_anti₀ (Real.exp_pos _)
    unfold StepParameters.weight
    exact le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
  calc ∑ c : Fin 3 → TorusBond n, (∏ l, ‖B (c l)‖) * (Ct / p.weight (supportDiam y c))
      ≤ ∑ c : Fin 3 → TorusBond n, (64 * v₀ ^ 3 * Ct) *
          ((∏ l, (ρ + 1 + (TorusFields.supDist (c l).1 y : ℝ))) *
            Real.exp (-(p.weightRate * (supportDiam y c : ℝ)))) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 : ∏ l, ‖B (c l)‖ ≤ ∏ l, (4 * v₀ * (ρ + 1 + (TorusFields.supDist (c l).1 y : ℝ))) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun l _ => hB _
        have h2 : ∏ l, (4 * v₀ * (ρ + 1 + (TorusFields.supDist (c l).1 y : ℝ))) =
            64 * v₀ ^ 3 * ∏ l, (ρ + 1 + (TorusFields.supDist (c l).1 y : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
          simp only [Finset.card_univ, Fintype.card_fin]
          ring
        rw [h2] at h1
        have h3 : Ct / p.weight (supportDiam y c) ≤ Ct * Real.exp (-(p.weightRate * (supportDiam y c : ℝ))) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (hw _) hCt
        calc (∏ l, ‖B (c l)‖) * (Ct / p.weight (supportDiam y c))
            ≤ (64 * v₀ ^ 3 * ∏ l, (ρ + 1 + (TorusFields.supDist (c l).1 y : ℝ))) *
                (Ct * Real.exp (-(p.weightRate * (supportDiam y c : ℝ)))) := by
              refine mul_le_mul h1 h3 ?_ (by positivity)
              have : 0 < p.weight (supportDiam y c) := by
                unfold StepParameters.weight
                exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
              positivity
          _ = _ := by ring
    _ = (64 * v₀ ^ 3 * Ct) * ∑ c : Fin 3 → TorusBond n,
          (∏ l, (ρ + 1 + (TorusFields.supDist (c l).1 y : ℝ))) * Real.exp (-(p.weightRate * (supportDiam y c : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left htr (by positivity)
end Sums
section Forms
variable {n : ℕ} [NeZero n]
private theorem colourEval_sub (q q' : BondBilinear n) (X : ColourForm n) :
    colourEval (fun b b' => q b b' - q' b b') X X = colourEval q X X - colourEval q' X X := by
  simp only [colourEval, bilinearEval, mul_sub, sub_mul, Finset.sum_sub_distrib]
private theorem colourEval_sum {ι : Type} (A : Finset ι) (f : ι → BondBilinear n) (X : ColourForm n) :
    colourEval (fun b b' => ∑ y ∈ A, f y b b') X X = ∑ y ∈ A, colourEval (f y) X X := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [colourEval, bilinearEval]
  | insert a A ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    simp only [Finset.sum_insert ha, colourEval, bilinearEval, mul_add, add_mul, Finset.sum_add_distrib]
private theorem annihilatesGradients_sub {q q' : BondBilinear n} (h : AnnihilatesGradients q)
    (h' : AnnihilatesGradients q') : AnnihilatesGradients fun b b' => q b b' - q' b b' := by apply _root_.YangMills.SharedProofs.p90134 <;> assumption
private theorem annihilatesGradients_hessianAtIdentity {G : TorusField n → ℝ} (hF : HasQuadraticFormAtIdentity G) :
    AnnihilatesGradients (hessianAtIdentity G) := by apply _root_.YangMills.SharedProofs.p35629 <;> assumption
end Forms
section Floors
private theorem eventually_floor_bounds {σ a b : ℝ} (hσ : 0 < σ) : ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x →
    64 * x ^ (-(1 / 4) : ℝ) < σ ∧ a ≤ x ^ ((1 : ℝ) / 100) ∧ b * Real.log x ≤ x / 2 ∧
      8 * x ^ ((1 : ℝ) / 50) + 3 < x ^ 4 := by
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, x ^ (-(1 / 4) : ℝ) < σ / 64 :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually (gt_mem_nhds (by positivity))
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, a ≤ x ^ ((1 : ℝ) / 100) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).eventually_ge_atTop a
  have hb1 : 0 < |b| + 1 := by positivity
  have e3 : ∀ᶠ x : ℝ in Filter.atTop, |Real.log x| ≤ (1 / (2 * (|b| + 1))) * |x| := by
    have := Real.isLittleO_log_id_atTop.bound (by positivity : 0 < 1 / (2 * (|b| + 1)))
    simpa using this
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 (e1.and (e2.and e3))
  refine ⟨max X 3, (by norm_num : (1 : ℝ) ≤ 3).trans (le_max_right _ _), fun x hx => ?_⟩
  have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
  obtain ⟨p1, p2, p3⟩ := hX x ((le_max_left _ _).trans hx)
  refine ⟨by linarith, p2, ?_, ?_⟩
  · have hx0 : 0 ≤ x := by linarith
    rw [abs_of_nonneg hx0] at p3
    have h1 : b * Real.log x ≤ |b| * |Real.log x| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h2 : |b| * |Real.log x| ≤ (|b| + 1) * (1 / (2 * (|b| + 1)) * x) := by
      refine mul_le_mul (by linarith) p3 (abs_nonneg _) hb1.le
    have h3 : (|b| + 1) * (1 / (2 * (|b| + 1)) * x) = x / 2 := by
      field_simp
    linarith
  · have h1 : x ^ ((1 : ℝ) / 50) ≤ x := by
      calc x ^ ((1 : ℝ) / 50) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = x := Real.rpow_one x
    have h2 : 27 * x ≤ x ^ 4 := by
      have : (3 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx3 3
      nlinarith
    nlinarith
private theorem abs_sum_sub_half_sum_le {ι : Type} (A : Finset ι) {a b sc : ι → ℝ} {E Ka Kb Kc Cs r v xh : ℝ}
    (hE : 0 ≤ E) (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKc : 0 ≤ Kc) (hCs : 0 ≤ Cs) (hr : 1 ≤ r) (hv : 0 ≤ v)
    (hxh : 0 ≤ xh) (hsc : ∀ y ∈ A, 0 ≤ sc y)
    (h1 : ∀ y ∈ A, |a y - 1 / 2 * b y| ≤ (1 + sc y) * E + Ka * r ^ 3 * v ^ 3 + Kb * xh * v ^ 2)
    (h2 : ∀ y ∈ A, |b y| ≤ Kc * v ^ 2) (hA : (A.card : ℝ) ≤ Cs * r ^ 4) :
    |∑ y ∈ A, a y - 1 / 2 * ∑ y ∈ A, b y| ≤
        Cs * (Ka + Kb + Kc + 1) * (r ^ 7 * v ^ 3 + r ^ 4 * xh * v ^ 2 +
          r ^ 4 * E * (1 + (A.card : ℝ)⁻¹ * ∑ y ∈ A, sc y)) ∧
      |∑ y ∈ A, b y| ≤ Cs * (Ka + Kb + Kc + 1) * r ^ 4 * v ^ 2 := by
  have hS : 0 ≤ ∑ y ∈ A, sc y := Finset.sum_nonneg hsc
  set N := 1 + (A.card : ℝ)⁻¹ * ∑ y ∈ A, sc y with hN
  have hN1 : 1 ≤ N := by
    have : 0 ≤ (A.card : ℝ)⁻¹ * ∑ y ∈ A, sc y := by positivity
    rw [hN]
    linarith
  have hsum : ∑ y ∈ A, (1 + sc y) ≤ (A.card : ℝ) * N := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    by_cases hc : (A.card : ℝ) = 0
    · have hA0 : A = ∅ := by
        have : A.card = 0 := by exact_mod_cast hc
        exact Finset.card_eq_zero.1 this
      simp [hA0]
    · rw [hN]
      field_simp
      linarith
  set T := Ka * r ^ 3 * v ^ 3 + Kb * xh * v ^ 2 with hT
  have e1 : ∑ y ∈ A, a y - 1 / 2 * ∑ y ∈ A, b y = ∑ y ∈ A, (a y - 1 / 2 * b y) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  constructor
  · rw [e1]
    calc |∑ y ∈ A, (a y - 1 / 2 * b y)| ≤ ∑ y ∈ A, |a y - 1 / 2 * b y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ A, ((1 + sc y) * E + T) := Finset.sum_le_sum fun y hy => by
          have := h1 y hy
          rw [hT]
          linarith
      _ = (∑ y ∈ A, (1 + sc y)) * E + (A.card : ℝ) * T := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
          simp
      _ ≤ ((A.card : ℝ) * N) * E + (A.card : ℝ) * T := by gcongr
      _ ≤ ((Cs * r ^ 4) * N) * E + (Cs * r ^ 4) * T := by
          have : 0 ≤ N := by linarith
          gcongr
      _ = Cs * (Ka * (r ^ 7 * v ^ 3) + Kb * (r ^ 4 * xh * v ^ 2) + 1 * (r ^ 4 * E * N)) := by
          rw [hT]
          ring
      _ ≤ Cs * ((Ka + Kb + Kc + 1) * (r ^ 7 * v ^ 3) + (Ka + Kb + Kc + 1) * (r ^ 4 * xh * v ^ 2) +
            (Ka + Kb + Kc + 1) * (r ^ 4 * E * N)) := by
          have p1 : 0 ≤ r ^ 7 * v ^ 3 := by positivity
          have p2 : 0 ≤ r ^ 4 * xh * v ^ 2 := by positivity
          have p3 : 0 ≤ r ^ 4 * E * N := by positivity
          refine mul_le_mul_of_nonneg_left ?_ hCs
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul_of_nonneg_right (by linarith) p1
          · exact mul_le_mul_of_nonneg_right (by linarith) p2
          · exact mul_le_mul_of_nonneg_right (by linarith) p3
      _ = _ := by ring
  · calc |∑ y ∈ A, b y| ≤ ∑ y ∈ A, |b y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y ∈ A, Kc * v ^ 2 := Finset.sum_le_sum h2
      _ = (A.card : ℝ) * (Kc * v ^ 2) := by simp
      _ ≤ (Cs * r ^ 4) * (Kc * v ^ 2) := by gcongr
      _ ≤ (Cs * r ^ 4) * ((Ka + Kb + Kc + 1) * v ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
end Floors
section ResponsesNearForms
private theorem ForAllParameters.and {P Q : MomentParameters → Prop} (hP : ForAllParameters P)
    (hQ : ForAllParameters Q) : ForAllParameters fun Λ => P Λ ∧ Q Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem ForAllParameters.mono {P Q : MomentParameters → Prop} (hP : ForAllParameters P)
    (h : ∀ Λ, P Λ → Q Λ) : ForAllParameters Q := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem forAllParameters_admissible : ForAllParameters fun Λ => Λ.stepParams.Admissible := by apply _root_.YangMills.SharedProofs.p7443 <;> assumption
end ResponsesNearForms
section Cut
variable {n : ℕ} [NeZero n]
omit [NeZero n] in
private theorem cutoffProfile_eq_zero_of_far (o z : TorusSite n) {m : ℕ} (hm : 1 ≤ m)
    (h : 2 * (m : ℝ) - 1 ≤ (TorusFields.supDist z o : ℝ)) : cutoffProfile o m z = 0 := by
  unfold cutoffProfile
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (2 * (m : ℝ) - 1 - (TorusFields.supDist z o : ℝ)) / ((m : ℝ) - 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  exact max_eq_left ((min_le_right _ _).trans h1)
omit [NeZero n] in
private theorem abs_cutoffProfile_le_one (o z : TorusSite n) (m : ℕ) : |cutoffProfile o m z| ≤ 1 := by
  unfold cutoffProfile
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (min_le_left _ _)
private theorem norm_cutoffCoords_le {p : _root_.YangMills.Construction.TorusLumps.StepParameters} {W : TorusField n} {o y : TorusSite n} {m rd : ℕ} {v : ℝ}
    (hm : 1 ≤ m) (hv : 0 ≤ v)
    (cut1 : ∀ c : TorusBond n, c.1 ∈ ResponseInTheExpansion.supBall o (2 * m) →
      c.1 + unitStep n c.2 ∈ ResponseInTheExpansion.supBall o (2 * m) →
      ‖(axialCoords p W o c : Quaternion ℝ)‖ ≤ 4 * ((TorusFields.supDist c.1 o : ℝ) + 1) * v)
    (hyo : TorusFields.supDist y o ≤ rd) (b : TorusBond n) :
    ‖cutoffCoords p W o m b‖ ≤ 4 * v * ((rd : ℝ) + 1 + (TorusFields.supDist b.1 y : ℝ)) := by
  unfold cutoffCoords
  by_cases hfar : 2 * (m : ℝ) - 1 ≤ (TorusFields.supDist b.1 o : ℝ)
  · rw [cutoffProfile_eq_zero_of_far o b.1 hm hfar, zero_smul, norm_zero]
    positivity
  · push Not at hfar
    have hb1 : b.1 ∈ ResponseInTheExpansion.supBall o (2 * m) := by
      simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
      linarith
    have hb2 : b.1 + unitStep n b.2 ∈ ResponseInTheExpansion.supBall o (2 * m) := by
      simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : TorusFields.supDist (b.1 + unitStep n b.2) o ≤ 1 + TorusFields.supDist b.1 o := by
        have a1 := supDist_triangle (b.1 + unitStep n b.2) b.1 o
        have a2 := supDist_add_unitStep_le b.1 b.2
        rw [supDist_comm] at a2
        omega
      have h2 : (TorusFields.supDist (b.1 + unitStep n b.2) o : ℝ) ≤ 1 + (TorusFields.supDist b.1 o : ℝ) := by
        exact_mod_cast h1
      linarith
    have h1 : ‖axialCoords p W o b‖ ≤ 4 * ((TorusFields.supDist b.1 o : ℝ) + 1) * v := cut1 b hb1 hb2
    have hd : (TorusFields.supDist b.1 o : ℝ) ≤ (TorusFields.supDist b.1 y : ℝ) + rd := by
      have := (supDist_triangle b.1 y o).trans (Nat.add_le_add_left hyo _)
      exact_mod_cast this
    rw [norm_smul, Real.norm_eq_abs]
    calc |cutoffProfile o m b.1| * ‖axialCoords p W o b‖ ≤ 1 * (4 * ((TorusFields.supDist b.1 o : ℝ) + 1) * v) :=
          mul_le_mul (abs_cutoffProfile_le_one o b.1 m) h1 (norm_nonneg _) zero_le_one
      _ ≤ 4 * v * ((rd : ℝ) + 1 + (TorusFields.supDist b.1 y : ℝ)) := by nlinarith
omit [NeZero n] in
private theorem unitStep_eq_siteOfInt (i : Fin 4) : (unitStep n i : TorusSite n) = siteOfInt (Pi.single i 1) := by apply _root_.YangMills.Construction.BlockOffsets.unitStep_eq_siteOfInt <;> assumption
end Cut
private theorem abs_sub_half_le_of_three {a b c d e1 e2 e3 : ℝ} (h1 : |a - b| ≤ e1) (h2 : |b - 1 / 2 * c| ≤ e2)
    (h3 : |c - d| ≤ e3) : |a - 1 / 2 * d| ≤ e1 + e2 + 1 / 2 * e3 := by
  obtain ⟨p1, q1⟩ := abs_le.1 h1
  obtain ⟨p2, q2⟩ := abs_le.1 h2
  obtain ⟨p3, q3⟩ := abs_le.1 h3
  exact abs_le.2 ⟨by linarith, by linarith⟩
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem resp_isAdmissible {u : ℕ} (hu : u ≤ S.data.windowLevel) : (S.resp u).IsAdmissible := by apply _root_.YangMills.SharedProofs.p17647 <;> assumption
private theorem stage_depth_eq {u : ℕ} (hu : u ≤ S.data.windowLevel) : (S.tower.stage u).depth = u := by
  have h1 := (S.onFlow u hu).depth_eq
  rw [← S.stage_eq u hu] at h1
  exact h1
private theorem stage_coupling_eq {u : ℕ} (hu : u ≤ S.data.windowLevel) :
    (S.tower.stage u).coupling = S.coupling u := by
  have h1 := (S.onFlow u hu).coupling_eq
  rw [← S.stage_eq u hu] at h1
  exact h1
private theorem supDist_originSite_le (hc : LevelTestFunctions.CircleRepProperties) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) {b : ℕ} (y : TorusSite (S.levelSide u))
    (hy : S.data.distFromCenter Λ.stepParams.side u y ≤ b) :
    TorusFields.supDist y (S.originSite u (S.levelSide u)) ≤ b := by
  obtain ⟨c1, c2, c3, -, -, c6, c7⟩ := hc
  have hL : (0 : ℝ) < (Λ.stepParams.side : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  set M : ℝ := (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ u with hMd
  have hM : 0 < M := by positivity
  set c : ℝ := ((S.data.period Λ.stepParams.side : ℕ) : ℝ) with hcd
  have hc0 : 0 < c := by
    have : 0 < S.data.period Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
    rw [hcd]
    exact_mod_cast this
  have hN : ((S.levelSide u : ℕ) : ℝ) = c * M := by
    show ((S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - u) : ℕ) : ℝ) = _
    push_cast
    rw [hMd, pow_sub₀ _ hL.ne' hu, div_eq_mul_inv]
  have hN0 : 0 < ((S.levelSide u : ℕ) : ℝ) := by rw [hN]; positivity
  unfold TorusFields.supDist
  refine Finset.sup_le fun a _ => ?_
  set ρ : ℤ := round (S.data.center a * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel /
    (Λ.stepParams.side : ℝ) ^ u) with hρ
  have hoa : S.originSite u (S.levelSide u) a = (ρ : ZMod (S.levelSide u)) := rfl
  obtain ⟨e', he⟩ : ∃ e' : ℤ, (((S.originSite u (S.levelSide u) a).val : ℕ) : ℤ) = ρ + (S.levelSide u : ℤ) * e' := by
    have h1 : ((((S.originSite u (S.levelSide u) a).val : ℕ) : ℤ) : ZMod (S.levelSide u)) =
        (ρ : ZMod (S.levelSide u)) := by
      rw [← hoa]
      simp
    obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
    exact ⟨-e, by linarith⟩
  have hreal : (((S.originSite u (S.levelSide u) a).val : ℕ) : ℝ) = ρ + ((S.levelSide u : ℕ) : ℝ) * e' := by
    exact_mod_cast he
  have key : (((y a - S.originSite u (S.levelSide u) a).valMinAbs.natAbs : ℕ) : ℝ) ≤ b + 1 / 2 := by
    rw [← c7 (S.levelSide u) (y a) (S.originSite u (S.levelSide u) a)]
    have e1 : ((y a).val : ℝ) - ((S.originSite u (S.levelSide u) a).val : ℝ) =
        (((y a).val : ℝ) - S.data.center a * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel /
            (Λ.stepParams.side : ℝ) ^ u) +
          (S.data.center a * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ u - ρ) +
          ((S.levelSide u : ℕ) : ℝ) * ((-e' : ℤ) : ℝ) := by
      rw [hreal]
      push_cast
      ring
    rw [e1, c1 _ hN0]
    refine (c3 _ hN0 _ _).trans ?_
    have p2 : |LevelTestFunctions.circleRep ((S.levelSide u : ℕ) : ℝ)
        (S.data.center a * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ u - ρ)| ≤
          1 / 2 :=
      (c2 _ hN0 _).trans (abs_sub_round _)
    have p1 : |LevelTestFunctions.circleRep ((S.levelSide u : ℕ) : ℝ) (((y a).val : ℝ) -
        S.data.center a * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ u)| ≤ b := by
      have e2 : ((y a).val : ℝ) - S.data.center a * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel /
            (Λ.stepParams.side : ℝ) ^ u =
          (((y a).val : ℝ) * (Λ.stepParams.side : ℝ) ^ u / (Λ.stepParams.side : ℝ) ^ S.data.windowLevel -
            S.data.center a) * M := by
        rw [hMd]
        field_simp
      rw [e2, hN, c6 c M hc0 hM, abs_mul, abs_of_pos hM]
      refine le_trans ?_ hy
      unfold LevelTestFunctions.LevelData.distFromCenter
      have := le_ciSup (f := fun a : Fin 4 => |LevelTestFunctions.circleRep (S.data.period Λ.stepParams.side)
        (((y a).val : ℝ) * (Λ.stepParams.side : ℝ) ^ u / (Λ.stepParams.side : ℝ) ^ S.data.windowLevel -
          S.data.center a)| * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ u)
        (Set.finite_range _).bddAbove a
      refine le_trans (le_of_eq ?_) this
      exact (mul_div_assoc _ _ _).symm
    linarith
  have : ((y a - S.originSite u (S.levelSide u) a).valMinAbs.natAbs : ℝ) < (b : ℝ) + 1 := by linarith
  have h3 : (y a - S.originSite u (S.levelSide u) a).valMinAbs.natAbs < b + 1 := by exact_mod_cast this
  omega
private theorem abs_centeredHull_sub_centeredResponse_le {y : TorusSite (S.levelSide S.lastSeparated)}
    {h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
      (S.levelSide S.lastSeparated))}
    {q : StageState S.tower S.lastSeparated (S.levelSide S.lastSeparated)}
    {g : TorusSite (S.levelSide S.lastSeparated) → UnitQuaternion} {m' : ℕ}
    (hrow : (S.resp S.lastSeparated).IsAdmissible)
    (hb : IsBlockTorusSide Λ.stepParams (S.levelSide S.lastSeparated))
    (hn₀ : Λ.stepParams.n₀ ≤ S.levelSide S.lastSeparated)
    (hlive : IsLiveState Λ.stepParams (S.tower.stage S.lastSeparated).coupling
      (S.tower.stage S.lastSeparated).labelWeight q.1 q.2.1 q.2.2)
    (hcold : IsCold Λ.stepParams.threshold (S.smoothedField S.lastSeparated (S.levelSide S.lastSeparated) q.1))
    (cut4 : ∀ c : TorusBond (S.levelSide S.lastSeparated),
      c.1 ∈ ResponseInTheExpansion.supBall (S.originSite S.lastSeparated (S.levelSide S.lastSeparated)) S.rangeSq →
      c.1 + unitStep (S.levelSide S.lastSeparated) c.2 ∈
        ResponseInTheExpansion.supBall (S.originSite S.lastSeparated (S.levelSide S.lastSeparated)) S.rangeSq →
      S.smoothedField S.lastSeparated (S.levelSide S.lastSeparated) q.1 c.1 c.2 =
        ResponseInTheExpansion.gaugeTransform g q.1 c)
    (hnh : Disjoint q.2.1
      (ResponseInTheExpansion.supBall (S.originSite S.lastSeparated (S.levelSide S.lastSeparated)) (8 * S.rangeSq)))
    (hyo : TorusFields.supDist y (S.originSite S.lastSeparated (S.levelSide S.lastSeparated)) ≤ S.radius)
    (hmle : m' + S.radius ≤ S.rangeSq)
    (hrange : (clusterRange (S.tower.stage S.lastSeparated).coupling : ℝ) / 64 ≤ m')
    (hside : 2 * m' + 2 < S.levelSide S.lastSeparated) :
    |centeredHullResponse (S.resp S.lastSeparated).cold (S.resp S.lastSeparated).hull
        (S.levelSide S.lastSeparated) y q.1 q.2.1 q.2.2 h -
        centeredResponse (S.resp S.lastSeparated).cold (S.levelSide S.lastSeparated) y
          (S.smoothedField S.lastSeparated (S.levelSide S.lastSeparated) q.1) h| ≤
      (1 + siteScore (S.resp S.lastSeparated).score q.2.1 q.2.2 y) * Real.exp (-Λ.stepParams.decayRate * m') *
        weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth h := by
  let W' : TorusField (S.levelSide S.lastSeparated) :=
    TorusFields.gaugeTransform (fun z => (g z)⁻¹) (S.smoothedField S.lastSeparated (S.levelSide S.lastSeparated) q.1)
  have hW' : IsCold Λ.stepParams.threshold W' := fun x μ ν hμ => by
    simp only [W']
    rw [_root_.YangMills.Construction.TorusFields.curvature_gaugeTransform]
    exact hcold x μ ν hμ
  have hres : centeredResponse (S.resp S.lastSeparated).cold (S.levelSide S.lastSeparated) y W' h =
      centeredResponse (S.resp S.lastSeparated).cold (S.levelSide S.lastSeparated) y
        (S.smoothedField S.lastSeparated (S.levelSide S.lastSeparated) q.1) h := by
    unfold centeredResponse
    rw [hrow.bounds.cold_gauge _ hn₀ y _ _ hcold h]
  have hbox : ∀ e : Fin 4 → ℤ, OffsetInBox m' e →
      TorusFields.supDist (y + siteOfInt e) (S.originSite S.lastSeparated (S.levelSide S.lastSeparated)) ≤ S.rangeSq := by
    intro e he
    have h1 : TorusFields.supDist y (y + siteOfInt e) ≤ m' := supDist_add_siteOfInt_le y e m' fun i => by
      have := he i
      rw [Int.abs_eq_natAbs] at this
      exact_mod_cast this
    have h2 := supDist_triangle (y + siteOfInt e) y (S.originSite S.lastSeparated (S.levelSide S.lastSeparated))
    rw [supDist_comm (y + siteOfInt e) y] at h2
    exact h2.trans ((Nat.add_le_add h1 hyo).trans hmle)
  have hmem : ∀ e : Fin 4 → ℤ, OffsetInBox m' e →
      y + siteOfInt e ∈ ResponseInTheExpansion.supBall (S.originSite S.lastSeparated (S.levelSide S.lastSeparated))
        S.rangeSq := by
    intro e he
    simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
    exact_mod_cast hbox e he
  have hnot : ∀ e : Fin 4 → ℤ, OffsetInBox m' e → y + siteOfInt e ∉ q.2.1 := by
    intro e he hz
    refine Finset.disjoint_left.1 hnh hz ?_
    simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : (TorusFields.supDist (y + siteOfInt e) (S.originSite S.lastSeparated (S.levelSide S.lastSeparated)) : ℝ) ≤
        S.rangeSq := by exact_mod_cast hbox e he
    have h2 : (0 : ℝ) ≤ S.rangeSq := Nat.cast_nonneg _
    linarith
  have hagree : FieldsAgreeNear q.1 W' y y m' := by
    rintro ⟨e, i⟩ ⟨h1, h2⟩
    have c1 := hmem e h1
    have c2 : (y + siteOfInt e) + unitStep (S.levelSide S.lastSeparated) i ∈
        ResponseInTheExpansion.supBall (S.originSite S.lastSeparated (S.levelSide S.lastSeparated)) S.rangeSq := by
      have := hmem (e + Pi.single i 1) h2
      rwa [siteOfInt_add, ← unitStep_eq_siteOfInt, ← add_assoc] at this
    have c3 := cut4 (y + siteOfInt e, i) c1 c2
    show q.1 (y + siteOfInt e) i = (g (y + siteOfInt e))⁻¹ *
      S.smoothedField S.lastSeparated (S.levelSide S.lastSeparated) q.1 (y + siteOfInt e) i *
        ((g (y + siteOfInt e + unitStep (S.levelSide S.lastSeparated) i))⁻¹)⁻¹
    rw [c3]
    simp [ResponseInTheExpansion.gaugeTransform, mul_assoc]
  let ω' : (∅ : Finset (TorusSite (S.levelSide S.lastSeparated))) → (S.tower.stage S.lastSeparated).labels.Ω :=
    fun z => (Finset.notMem_empty _ z.2).elim
  have hsa : StatesAgreeNear Λ.stepParams q.1 W' q.2.1 ∅ q.2.2 ω' y y m' := by
    refine ⟨hside, hside, hagree, fun e he => ⟨fun hz => absurd hz (hnot e he), fun hz => by simp at hz⟩, ?_, ?_⟩
    · intro e _ _ hz'
      simp at hz'
    · rintro ⟨e, he, hz⟩
      exact absurd hz (hnot e he)
  have fc := hrow.bounds.forget_cold _ _ hb hn₀ q.1 W' q.2.1 q.2.2 ω' y y m' h h hlive hW' hrange hsa
    (fun _ _ _ _ _ => rfl)
  rwa [hres] at fc
private theorem scale_bounds {Cs C : ℝ} (hCs : 1 ≤ Cs) (hxone : 1 ≤ S.scaleCoupling)
    (fa : 2 * Cs ≤ S.scaleCoupling ^ ((1 : ℝ) / 100))
    (fb : |C| * Real.log S.scaleCoupling ≤ S.scaleCoupling / 2)
    (fc : 8 * S.scaleCoupling ^ ((1 : ℝ) / 50) + 3 < S.scaleCoupling ^ 4)
    (hrd : (S.radius : ℝ) ≤ Cs * S.range)
    (hxt : |S.coupling S.lastSeparated - S.scaleCoupling| ≤ C * Real.log S.scaleCoupling)
    (hL4 : (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) ≤ S.scaleCoupling⁻¹)
    (hsd : Λ.stepParams.side ^ S.logIndex ≤ S.levelSide S.lastSeparated)
    (htK : S.lastSeparated ≤ S.data.windowLevel) :
    (1 : ℝ) ≤ S.range ∧ 1 ≤ S.rangeSq ∧
      S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ) ≤ 2 * S.scaleCoupling ^ (-(1 / 2) : ℝ) ∧
      0 < S.coupling S.lastSeparated ∧
      ∃ m' : ℕ, m' + S.radius ≤ S.rangeSq ∧ (S.range : ℝ) ^ 2 / 2 ≤ m' ∧
        (clusterRange (S.tower.stage S.lastSeparated).coupling : ℝ) / 64 ≤ m' ∧
        2 * m' + 2 < S.levelSide S.lastSeparated := by
  have hxpos : 0 < S.scaleCoupling := by linarith
  have hy1 : (1 : ℝ) ≤ S.scaleCoupling ^ ((1 : ℝ) / 100) := Real.one_le_rpow hxone (by norm_num)
  have hrl : S.scaleCoupling ^ ((1 : ℝ) / 100) ≤ (S.range : ℝ) := Nat.le_ceil _
  have hr1 : (1 : ℝ) ≤ S.range := hy1.trans hrl
  have hru : (S.range : ℝ) ≤ 2 * S.scaleCoupling ^ ((1 : ℝ) / 100) := by
    have : (S.range : ℝ) < S.scaleCoupling ^ ((1 : ℝ) / 100) + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hLpos : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hmr : ((S.rangeSq : ℕ) : ℝ) = (S.range : ℝ) ^ 2 := by simp [MomentPoint.rangeSq]
  have hrdm : (S.radius : ℝ) ≤ (S.range : ℝ) ^ 2 / 2 := by
    have h1 : Cs * S.range ≤ ((S.range : ℝ) / 2) * S.range := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : ((S.range : ℝ) / 2) * S.range = (S.range : ℝ) ^ 2 / 2 := by ring
    linarith
  have hrdn : S.radius ≤ S.rangeSq := by
    have : (S.radius : ℝ) ≤ (S.rangeSq : ℝ) := by rw [hmr]; nlinarith
    exact_mod_cast this
  have hm1 : 1 ≤ S.rangeSq := by
    have : (1 : ℝ) ≤ (S.rangeSq : ℝ) := by rw [hmr]; nlinarith
    exact_mod_cast this
  obtain ⟨m', hm'd⟩ : ∃ m' : ℕ, m' = S.rangeSq - S.radius := ⟨_, rfl⟩
  have hm' : (m' : ℝ) = (S.range : ℝ) ^ 2 - S.radius := by rw [hm'd, Nat.cast_sub hrdn, hmr]
  have hm2 : (S.range : ℝ) ^ 2 / 2 ≤ m' := by rw [hm']; linarith
  have hmle : m' + S.radius ≤ S.rangeSq := by omega
  have hlog : 0 ≤ Real.log S.scaleCoupling := Real.log_nonneg hxone
  have hxt' : |S.coupling S.lastSeparated - S.scaleCoupling| ≤ S.scaleCoupling / 2 :=
    (hxt.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hlog)).trans fb
  have hxtl : S.scaleCoupling / 2 ≤ S.coupling S.lastSeparated := by linarith [(abs_le.1 hxt').1]
  have hxtu : S.coupling S.lastSeparated ≤ 2 * S.scaleCoupling := by linarith [(abs_le.1 hxt').2]
  have hxtp : 0 < S.coupling S.lastSeparated := by linarith
  have hxp : S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ) ≤ 2 * S.scaleCoupling ^ (-(1 / 2) : ℝ) := by
    rw [Real.rpow_neg hxtp.le, Real.rpow_neg hxpos.le]
    have hs0 : 0 < S.scaleCoupling ^ ((1 : ℝ) / 2) := by positivity
    have a1 : (S.scaleCoupling / 2) ^ ((1 : ℝ) / 2) ≤ S.coupling S.lastSeparated ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hxtl (by norm_num)
    have a2 : S.scaleCoupling ^ ((1 : ℝ) / 2) / 2 ≤ (S.scaleCoupling / 2) ^ ((1 : ℝ) / 2) := by
      rw [Real.div_rpow hxpos.le (by norm_num)]
      have b1 : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
        calc (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have b0 : 0 < (2 : ℝ) ^ ((1 : ℝ) / 2) := by positivity
      exact div_le_div_of_nonneg_left hs0.le b0 b1
    have a3 := inv_anti₀ (by positivity) (a2.trans a1)
    calc _ ≤ (S.scaleCoupling ^ ((1 : ℝ) / 2) / 2)⁻¹ := a3
      _ = 2 * (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ := by field_simp
  have hrange : (clusterRange (S.tower.stage S.lastSeparated).coupling : ℝ) / 64 ≤ m' := by
    rw [stage_coupling_eq S htK]
    have h0 : (clusterRange (S.coupling S.lastSeparated) : ℝ) < S.coupling S.lastSeparated ^ ((1 : ℝ) / 100) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h1 : S.coupling S.lastSeparated ^ ((1 : ℝ) / 100) ≤ (2 * S.scaleCoupling) ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow hxtp.le hxtu (by norm_num)
    have h2 : (2 * S.scaleCoupling) ^ ((1 : ℝ) / 100) ≤ 2 * S.scaleCoupling ^ ((1 : ℝ) / 100) := by
      rw [Real.mul_rpow (by norm_num) hxpos.le]
      have b1 : (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 := by
        calc (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      exact mul_le_mul_of_nonneg_right b1 (by positivity)
    nlinarith
  have hside : 2 * m' + 2 < S.levelSide S.lastSeparated := by
    have hLr : (0 : ℝ) < (Λ.stepParams.side : ℝ) := by exact_mod_cast hLpos
    have hA : S.scaleCoupling ≤ (Λ.stepParams.side : ℝ) ^ ((S.logIndex : ℝ) / 4) := by
      have e : -(S.logIndex : ℝ) / 4 = -((S.logIndex : ℝ) / 4) := by ring
      rw [e, Real.rpow_neg hLr.le] at hL4
      exact (inv_le_inv₀ (by positivity) hxpos).1 hL4
    have h4 : S.scaleCoupling ^ 4 ≤ (Λ.stepParams.side : ℝ) ^ S.logIndex := by
      have e : ((Λ.stepParams.side : ℝ) ^ ((S.logIndex : ℝ) / 4)) ^ 4 = (Λ.stepParams.side : ℝ) ^ S.logIndex := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLr.le, ← Real.rpow_natCast]
        congr 1
        push_cast
        ring
      rw [← e]
      exact pow_le_pow_left₀ hxpos.le hA 4
    have h5 : (Λ.stepParams.side : ℝ) ^ S.logIndex ≤ ((S.levelSide S.lastSeparated : ℕ) : ℝ) := by
      exact_mod_cast hsd
    have h6 : (S.range : ℝ) ^ 2 ≤ 4 * S.scaleCoupling ^ ((1 : ℝ) / 50) := by
      have e : S.scaleCoupling ^ ((1 : ℝ) / 50) = (S.scaleCoupling ^ ((1 : ℝ) / 100)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
        norm_num
      rw [e]
      nlinarith
    have h8 : ((2 * m' + 2 : ℕ) : ℝ) < ((S.levelSide S.lastSeparated : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h8
  exact ⟨hr1, hm1, hxp, hxtp, m', hmle, hm2, hrange, hside⟩
end Point
theorem supportTotalNearQuadraticStatement_holds (hCl : classicalFormsApproxStatement)
    (hTh : thirdDerivativeBoundsStatement) (hCut : goodConfigCutoffStatement) (hRd : formsReadCurvatureStatement)
    (hAt : responsesHaveFormsStatement) (hKl : classicalFormsAnnihilateClosedStatement)
    (hWin : scaleWindowStatement) (hWt : weightsSitesBelowScaleStatement)
    (hSi : farLevelSupportSitesStatement) (hTy : taylorAlongFormStatement)
    (hCi : LevelTestFunctions.CircleRepProperties) : supportTotalNearQuadraticStatement := by
  unfold classicalFormsApproxStatement ForAllPoints at hCl
  unfold thirdDerivativeBoundsStatement ForAllPoints at hTh
  unfold goodConfigCutoffStatement ForAllPoints at hCut
  unfold formsReadCurvatureStatement ForAllPoints at hRd
  unfold responsesHaveFormsStatement ForAllPoints at hAt
  unfold classicalFormsAnnihilateClosedStatement ForAllPoints at hKl
  unfold scaleWindowStatement ForAllPoints at hWin
  unfold weightsSitesBelowScaleStatement ForAllPoints at hWt
  unfold farLevelSupportSitesStatement ForAllPoints at hSi
  unfold supportTotalNearQuadraticStatement ForAllPoints
  refine ForAllParameters.mono (ForAllParameters.and hCl (ForAllParameters.and hTh (ForAllParameters.and hCut
    (ForAllParameters.and hRd (ForAllParameters.and hAt (ForAllParameters.and hKl (ForAllParameters.and hWin
      (ForAllParameters.and hWt (ForAllParameters.and hSi forAllParameters_admissible))))))))) ?_
  clear hCl hTh hCut hRd hAt hKl hWin hWt hSi
  rintro Λ ⟨⟨C₁, _, _, _, _, h₁⟩, ⟨C₂, _, _, _, _, h₂⟩, ⟨_, _, X₃, _, _, h₃⟩, ⟨C₄, _, X₄, _, _, h₄⟩,
    ⟨_, _, _, _, _, h₅⟩, ⟨_, _, _, _, _, h₆⟩, ⟨C₇, _, X₇, _, _, h₇⟩, ⟨_, _, _, _, _, h₈⟩, ⟨C₉, _, _, _, _, h₉⟩, hfit⟩
  have hrate : 0 < Λ.stepParams.weightRate := by
    unfold StepParameters.weightRate
    exact div_pos hfit.rt_pos (by positivity)
  have hforget : 0 < Λ.stepParams.decayRate := by
    unfold StepParameters.decayRate
    exact div_pos hfit.rt_pos (by positivity)
  obtain ⟨Ctr, hCtr0, hCtr⟩ := sum_triple_bonds_weight_le hrate
  let Ct : ℝ := max (C₂ 0) 0
  have hCt0 : 0 ≤ Ct := le_max_right _ _
  let Cq : ℝ := max (C₂ 1) 0 + 1
  have hCq0 : 0 < Cq := by have : 0 ≤ max (C₂ 1) 0 := le_max_right _ _; simp only [Cq]; linarith
  let Cn : ℝ := max (C₁ 1) 0 + 1
  have hCn0 : 0 < Cn := by have : 0 ≤ max (C₁ 1) 0 := le_max_right _ _; simp only [Cn]; linarith
  let Cf : ℝ := max (C₄ 1) 0
  have hCf0 : 0 ≤ Cf := le_max_right _ _
  let Cs : ℝ := |C₉ 0| + 1
  have hCs1 : 1 ≤ Cs := by have := abs_nonneg (C₉ 0); simp only [Cs]; linarith
  let Ka : ℝ := 64 * Ct * Ctr * (Cs + 1) ^ 3
  have hKa0 : 0 ≤ Ka := by positivity
  let Kb : ℝ := Cf * Cn
  have hKb0 : 0 ≤ Kb := by positivity
  let Kc : ℝ := Cf * Cq
  have hKc0 : 0 ≤ Kc := by positivity
  obtain ⟨X₆, hX₆1, hX₆⟩ := eventually_floor_bounds (a := 2 * Cs) (b := |C₇ 0|) (σ := Λ.stepParams.threshold)
    hfit.σ_pos
  refine ⟨fun _ => Cs * (Ka + Kb + Kc + 1), Λ.stepParams.decayRate / 2,
    max (max X₃ X₄) (max X₇ (max X₆ Λ.floor)), by positivity,
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)), fun S hx i q hlive hgood => ?_⟩
  have hx3 : X₃ ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx4 : X₄ ≤ S.scaleCoupling := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx7 : X₇ ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx6 : X₆ ≤ S.scaleCoupling :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hx
  have hxone : 1 ≤ S.scaleCoupling := hX₆1.trans hx6
  have hxpos : 0 < S.scaleCoupling := by linarith
  obtain ⟨fσ, fa, fb, fc⟩ := hX₆ S.scaleCoupling hx6
  obtain ⟨hL4, -, -, -, -, hwin, hu⟩ := h₇ S hx7
  have htK : S.lastSeparated ≤ S.data.windowLevel := by omega
  have hts : S.lastSeparated ≤ S.data.scaleLevel := by
    unfold MomentPoint.lastSeparated
    classical
    exact Nat.findGreatest_le _
  obtain ⟨hxt, hsd⟩ := hu S.lastSeparated le_rfl (by omega)
  have hlev := stage_depth_eq S htK
  have hrow := resp_isAdmissible S htK
  have hLpos : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hb : IsBlockTorusSide Λ.stepParams (S.levelSide S.lastSeparated) :=
    ⟨Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _,
      S.side_le.trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos hLpos))⟩
  have hn₀ : Λ.stepParams.n₀ ≤ S.levelSide S.lastSeparated := (Nat.le_mul_of_pos_left _ hLpos).trans hb.2
  obtain ⟨hs1, hs2, hs3⟩ := h₉ S
  have hrd : (S.radius : ℝ) ≤ Cs * S.range := hs2.trans (mul_le_mul_of_nonneg_right (by
    have := le_abs_self (C₉ 0)
    simp only [Cs]
    linarith) (Nat.cast_nonneg _))
  obtain ⟨hr1, hm1, hxp, hxtp, m', hmle, hm2, hrange, hside⟩ :=
    scale_bounds S hCs1 hxone fa fb fc hrd hxt hL4 hsd htK
  obtain ⟨cut1, cut2, cut3, g, cut4⟩ :=
    h₃ S hx3 S.lastSeparated le_rfl (by omega) (S.levelSide S.lastSeparated) rfl q.1 q.2.1 hgood
  have hv0 : 0 ≤ S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  have hvx : S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ≤
      S.scaleCoupling ^ (-(1 / 4) : ℝ) := hgood.curvature_le
  have hcold : ∀ w : ℝ, 0 ≤ w → w ≤ 1 → IsCold Λ.stepParams.threshold
      (expField w (S.cutoffLie S.lastSeparated (S.levelSide S.lastSeparated) q.1)) :=
    fun w h0 h1 x μ ν hμ => lt_of_le_of_lt (cut3 w h0 h1 x μ ν hμ) (by linarith)
  let h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
      (S.levelSide S.lastSeparated)) :=
    S.weight i (fineSide Λ.stepParams.side (S.tower.stage S.lastSeparated).depth (S.levelSide S.lastSeparated))
  have hsz1 : weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth h ≤ 1 := by
    have := (h₈ S S.lastSeparated hts i).1
    show weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
        (S.levelSide S.lastSeparated))) ≤ 1
    rw [hlev]
    exact this
  have hsz0 : 0 ≤ weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth h :=
    le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
  have hsites : ResponseInTheExpansion.weightSupportSites Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
      (S.levelSide S.lastSeparated) h = S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i := by
    show ResponseInTheExpansion.weightSupportSites Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
        (S.levelSide S.lastSeparated)
        (S.weight i (fineSide Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
          (S.levelSide S.lastSeparated))) =
      ResponseInTheExpansion.weightSupportSites Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated)
        (S.weight i (fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated)))
    rw [hlev]
  have hFeq : S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i q =
      ∑ y ∈ S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i,
        centeredHullResponse (S.resp S.lastSeparated).cold (S.resp S.lastSeparated).hull
          (S.levelSide S.lastSeparated) y q.1 q.2.1 q.2.2 h := by
    rw [← hsites]
    rfl
  have hQeq : ∀ X : ColourForm (S.levelSide S.lastSeparated),
      colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i) X X =
        ∑ y ∈ S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i,
          colourEval (classicalQuadratic S.tower S.resp S.lastSeparated (S.levelSide S.lastSeparated) h y) X X :=
    fun X => colourEval_sum _
      (fun y => classicalQuadratic S.tower S.resp S.lastSeparated (S.levelSide S.lastSeparated) h y) X
  have hsc : ∀ y, 0 ≤ siteScore (S.resp S.lastSeparated).score q.2.1 q.2.2 y := fun y => by
    unfold siteScore
    split_ifs
    · exact hrow.price.nonneg _
    · exact le_rfl
  have hweight : ∀ m : ℕ, 0 < Λ.stepParams.weight m := fun m => by
    unfold StepParameters.weight
    exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
  have hxh : 0 ≤ S.scaleCoupling ^ (-(1 / 2) : ℝ) := by positivity
  have site : ∀ y ∈ S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i,
      |centeredHullResponse (S.resp S.lastSeparated).cold (S.resp S.lastSeparated).hull
          (S.levelSide S.lastSeparated) y q.1 q.2.1 q.2.2 h - 1 / 2 *
          colourEval (classicalQuadratic S.tower S.resp S.lastSeparated (S.levelSide S.lastSeparated) h y)
            (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)
            (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)| ≤
        (1 + siteScore (S.resp S.lastSeparated).score q.2.1 q.2.2 y) *
            Real.exp (-(Λ.stepParams.decayRate / 2 * (S.range : ℝ) ^ 2)) +
          Ka * (S.range : ℝ) ^ 3 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 3 +
          Kb * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
            S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2 ∧
      |colourEval (classicalQuadratic S.tower S.resp S.lastSeparated (S.levelSide S.lastSeparated) h y)
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)| ≤
        Kc * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2 := by
    intro y hy
    have hyo : TorusFields.supDist y (S.originSite S.lastSeparated (S.levelSide S.lastSeparated)) ≤ S.radius :=
      supDist_originSite_le S hCi htK y (hs3 S.lastSeparated le_rfl htK i y hy)
    have ht := h₂ S S.lastSeparated htK (S.levelSide S.lastSeparated) hn₀ y h
    have hform := (h₅ S S.lastSeparated htK (S.levelSide S.lastSeparated) hn₀ y h).2.2
    have hkl := h₆ S S.lastSeparated htK (S.levelSide S.lastSeparated) hn₀ y h
    have hC2 : C₂ 0 * weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth h ≤ Ct := by
      calc C₂ 0 * weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth h
          ≤ Ct * weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth h :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hsz0
        _ ≤ Ct * 1 := mul_le_mul_of_nonneg_left hsz1 hCt0
        _ = Ct := mul_one _
    have tay := taylor_remainder_le hTy Λ.stepParams
      (G := fun W' => (S.resp S.lastSeparated).cold (S.levelSide S.lastSeparated) y W' h)
      (B := S.cutoffLie S.lastSeparated (S.levelSide S.lastSeparated) q.1) (y := y)
      (v₀ := S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1) (ρ := S.radius) (Ct := Ct)
      (Ctr := Ctr) hv0 (Nat.cast_nonneg _) hCt0
      (fun w a b => (ht.1 _ (hcold w a b)).1)
      (fun w a b c X hX => ((ht.1 _ (hcold w a b)).2 c X hX).trans
        (div_le_div_of_nonneg_right hC2 (hweight _).le))
      hform (fun b => norm_cutoffCoords_le hm1 hv0 cut1 hyo b) (hCtr _ y _ (Nat.cast_nonneg _))
    have kg := annihilatesGradients_sub (annihilatesGradients_hessianAtIdentity hform) hkl.2.1.1
    have hsz : 0 < Cn * S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ) := by positivity
    have hsize : IsDecayingAbout Λ.stepParams (Cn * S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ)) y (fun b b' =>
        hessianAtIdentity (fun W' => (S.resp S.lastSeparated).cold (S.levelSide S.lastSeparated) y W' h) b b' -
          classicalQuadratic S.tower S.resp S.lastSeparated (S.levelSide S.lastSeparated) h y b b') := by
      intro b b'
      refine ((h₁ S S.lastSeparated htK (S.levelSide S.lastSeparated) hn₀ y h b b').2.2).trans
        (div_le_div_of_nonneg_right ?_ (hweight _).le)
      have hxq : 0 ≤ S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ) := by positivity
      have a1 : C₁ 1 ≤ Cn := by
        have := le_max_left (C₁ 1) 0
        simp only [Cn]
        linarith
      calc C₁ 1 * S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ) *
            weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth h
          ≤ Cn * S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ) *
              weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth h :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right a1 hxq) hsz0
        _ ≤ Cn * S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ) * 1 := mul_le_mul_of_nonneg_left hsz1 (by positivity)
        _ = Cn * S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ) := mul_one _
    have rd1 := (h₄ S S.lastSeparated htK (S.levelSide S.lastSeparated) rfl y _ _ hsz hsize).2 hx4 le_rfl
      (by omega) kg hyo q.1 q.2.1 hgood
    rw [colourEval_sub] at rd1
    have hcs : IsDecayingAbout Λ.stepParams Cq y
        (classicalQuadratic S.tower S.resp S.lastSeparated (S.levelSide S.lastSeparated) h y) := by
      intro b b'
      refine (ht.2 b b').trans (div_le_div_of_nonneg_right ?_ (hweight _).le)
      have a1 : C₂ 1 ≤ Cq := by
        have := le_max_left (C₂ 1) 0
        simp only [Cq]
        linarith
      calc C₂ 1 * weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth h
          ≤ Cq * weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth h :=
            mul_le_mul_of_nonneg_right a1 hsz0
        _ ≤ Cq * 1 := mul_le_mul_of_nonneg_left hsz1 hCq0.le
        _ = Cq := mul_one _
    have rd2 := (h₄ S S.lastSeparated htK (S.levelSide S.lastSeparated) rfl y Cq _ hCq0 hcs).2 hx4 le_rfl
      (by omega) hkl.2.1.1 hyo q.1 q.2.1 hgood
    have fg := abs_centeredHull_sub_centeredResponse_le S (y := y) (h := h) (q := q) (g := g) (m' := m') hrow hb
      hn₀ hlive (hcold 1 zero_le_one le_rfl) cut4 hgood.disjoint_lumps hyo hmle hrange hside
    have hC4 : C₄ 1 ≤ Cf := le_max_left _ _
    have hv2 : 0 ≤ S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2 := by positivity
    refine ⟨(abs_sub_half_le_of_three fg tay rd1).trans ?_, rd2.trans ?_⟩
    · have hsc1 : 0 ≤ 1 + siteScore (S.resp S.lastSeparated).score q.2.1 q.2.2 y := by
        have := hsc y
        linarith
      have p1 : (1 + siteScore (S.resp S.lastSeparated).score q.2.1 q.2.2 y) *
            Real.exp (-Λ.stepParams.decayRate * m') *
            weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth h ≤
          (1 + siteScore (S.resp S.lastSeparated).score q.2.1 q.2.2 y) *
            Real.exp (-(Λ.stepParams.decayRate / 2 * (S.range : ℝ) ^ 2)) := by
        have e1 : Real.exp (-Λ.stepParams.decayRate * m') ≤
            Real.exp (-(Λ.stepParams.decayRate / 2 * (S.range : ℝ) ^ 2)) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_left hm2 hforget.le
          have e : Λ.stepParams.decayRate * ((S.range : ℝ) ^ 2 / 2) =
              Λ.stepParams.decayRate / 2 * (S.range : ℝ) ^ 2 := by ring
          linarith
        calc _ ≤ (1 + siteScore (S.resp S.lastSeparated).score q.2.1 q.2.2 y) *
              Real.exp (-Λ.stepParams.decayRate * m') * 1 :=
              mul_le_mul_of_nonneg_left hsz1 (by positivity)
          _ = (1 + siteScore (S.resp S.lastSeparated).score q.2.1 q.2.2 y) *
              Real.exp (-Λ.stepParams.decayRate * m') := mul_one _
          _ ≤ _ := mul_le_mul_of_nonneg_left e1 hsc1
      have p2 : 64 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 3 * Ct *
            (Ctr * ((S.radius : ℝ) + 1) ^ 3) ≤
          Ka * (S.range : ℝ) ^ 3 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 3 := by
        have a0 : (S.radius : ℝ) + 1 ≤ (Cs + 1) * S.range := by linarith
        have a1 : ((S.radius : ℝ) + 1) ^ 3 ≤ ((Cs + 1) * S.range) ^ 3 := pow_le_pow_left₀ (by positivity) a0 3
        have a2 : 0 ≤ 64 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 3 * Ct * Ctr := by
          positivity
        calc 64 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 3 * Ct *
              (Ctr * ((S.radius : ℝ) + 1) ^ 3)
            = (64 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 3 * Ct * Ctr) *
                ((S.radius : ℝ) + 1) ^ 3 := by ring
          _ ≤ (64 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 3 * Ct * Ctr) *
                ((Cs + 1) * S.range) ^ 3 :=
              mul_le_mul_of_nonneg_left a1 a2
          _ = Ka * (S.range : ℝ) ^ 3 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 3 := by
              simp only [Ka]
              ring
      have p3 : 1 / 2 * (C₄ 1 * (Cn * S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ)) *
            S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2) ≤
          Kb * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
            S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2 := by
        have a0 : 0 ≤ Cn * S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ) := hsz.le
        have a1 : C₄ 1 * (Cn * S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ)) ≤
            Cf * (Cn * (2 * S.scaleCoupling ^ (-(1 / 2) : ℝ))) :=
          (mul_le_mul_of_nonneg_right hC4 a0).trans
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxp hCn0.le) hCf0)
        calc 1 / 2 * (C₄ 1 * (Cn * S.coupling S.lastSeparated ^ (-(1 / 2) : ℝ)) *
              S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2)
            ≤ 1 / 2 * (Cf * (Cn * (2 * S.scaleCoupling ^ (-(1 / 2) : ℝ))) *
                S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right a1 hv2) (by norm_num)
          _ = _ := by
              simp only [Kb]
              ring
      exact add_le_add (add_le_add p1 p2) p3
    · calc C₄ 1 * Cq * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2
          ≤ Cf * Cq * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC4 hCq0.le) hv2
        _ = Kc * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2 := rfl
  have hcard : ((S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i).card : ℝ) ≤
      Cs * (S.range : ℝ) ^ 4 := by
    refine (hs1 i).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have := le_abs_self (C₉ 0)
    simp only [Cs]
    linarith
  obtain ⟨r1, r2⟩ := abs_sum_sub_half_sum_le (S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i)
    (a := fun y => centeredHullResponse (S.resp S.lastSeparated).cold (S.resp S.lastSeparated).hull
      (S.levelSide S.lastSeparated) y q.1 q.2.1 q.2.2 h)
    (b := fun y => colourEval (classicalQuadratic S.tower S.resp S.lastSeparated (S.levelSide S.lastSeparated) h y)
      (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)
      (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1))
    (sc := fun y => siteScore (S.resp S.lastSeparated).score q.2.1 q.2.2 y)
    (E := Real.exp (-(Λ.stepParams.decayRate / 2 * (S.range : ℝ) ^ 2)))
    (Ka := Ka) (Kb := Kb) (Kc := Kc) (Cs := Cs) (r := S.range)
    (v := S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1)
    (xh := S.scaleCoupling ^ (-(1 / 2) : ℝ))
    (Real.exp_pos _).le hKa0 hKb0 hKc0 (by linarith) hr1 hv0 hxh (fun y _ => hsc y) (fun y hy => (site y hy).1)
    (fun y hy => (site y hy).2) hcard
  refine ⟨?_, ?_⟩
  · rw [hFeq, hQeq]
    exact r1
  · rw [hQeq]
    exact r2
end YangMills.Construction.MomentLaw
end
