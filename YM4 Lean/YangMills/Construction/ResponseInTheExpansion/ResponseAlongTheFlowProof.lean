import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ResponseInTheExpansion.ColdHalfOfTheResponseProof
import YangMills.Construction.ResponseInTheExpansion.ResponseAlongTheFlow
import YangMills.Construction.ResponseInTheExpansion.TheResponseReturns
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion.ResponseAlongFlow
open WeightedResponses StepSettings TorusLumps RenormalizationStepParameters StepReturn ClusterExpansionOfAStep
section Sum
theorem rpow_neg_half_eq_inv_sqrt {u : ℝ} (hu : 0 < u) : u ^ (-(1 / 2) : ℝ) = (Real.sqrt u)⁻¹ := by
  rw [Real.rpow_neg hu.le, Real.sqrt_eq_rpow]
theorem rpow_neg_three_halves_eq_inv_sqrt_cube {u : ℝ} (hu : 0 < u) :
    u ^ (-(3 / 2) : ℝ) = ((Real.sqrt u) ^ 3)⁻¹ := by apply _root_.YangMills.Construction.ResponseInTheExpansion.ColdResponseCoefficient.rpow_neg_three_halves_eq_inv_sqrt_pow <;> assumption
theorem sub_mul_rpow_le_rpow_sub_rpow {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (v - u) / 2 * v ^ (-(3 / 2) : ℝ) ≤ u ^ (-(1 / 2) : ℝ) - v ^ (-(1 / 2) : ℝ) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  rw [rpow_neg_half_eq_inv_sqrt hu, rpow_neg_half_eq_inv_sqrt hv, rpow_neg_three_halves_eq_inv_sqrt_cube hv]
  set a := Real.sqrt u with ha
  set b := Real.sqrt v with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr hu
  have hb0 : 0 < b := Real.sqrt_pos.mpr hv
  have hab : a ≤ b := Real.sqrt_le_sqrt huv
  have hua : u = a ^ 2 := (Real.sq_sqrt hu.le).symm
  have hvb : v = b ^ 2 := (Real.sq_sqrt hv.le).symm
  rw [hua, hvb]
  have e : a⁻¹ - b⁻¹ - (b ^ 2 - a ^ 2) / 2 * (b ^ 3)⁻¹ =
      (b - a) * (2 * b ^ 2 - a * (a + b)) / (2 * a * b ^ 3) := by
    field_simp
    ring
  have h1 : 0 ≤ (b - a) * (2 * b ^ 2 - a * (a + b)) / (2 * a * b ^ 3) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by linarith)
    nlinarith
  linarith
theorem sum_rpow_neg_three_halves_le {lam A : ℝ} (hlam : 0 < lam) (hA : 0 < A) (t : ℕ) :
    ∑ i ∈ Finset.range t, (A + lam * ((i : ℝ) + 1)) ^ (-(3 / 2) : ℝ) ≤
      2 / lam * (A ^ (-(1 / 2) : ℝ) - (A + lam * t) ^ (-(1 / 2) : ℝ)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have hu : 0 < A + lam * t := by positivity
    have hs := sub_mul_rpow_le_rpow_sub_rpow hu (show A + lam * t ≤ A + lam * ((t : ℝ) + 1) by nlinarith)
    have e : A + lam * ((t : ℝ) + 1) - (A + lam * t) = lam := by ring
    rw [e] at hs
    push_cast
    have h2 : (A + lam * ((t : ℝ) + 1)) ^ (-(3 / 2) : ℝ) ≤
        2 / lam * ((A + lam * t) ^ (-(1 / 2) : ℝ) - (A + lam * ((t : ℝ) + 1)) ^ (-(1 / 2) : ℝ)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
      nlinarith
    linarith
theorem sum_rpow_le_of_linear_descent {x : ℕ → ℝ} {lam c₅ : ℝ} {t : ℕ} (hlam : 0 < lam) (hx : 0 < x t)
    (hc : 2 * c₅ ≤ x t) (hs : ∀ i ≤ t, lam * ((t : ℝ) - i) - c₅ ≤ x i - x t) :
    ∑ j ∈ Finset.range t, x j ^ (-(3 / 2) : ℝ) ≤ 6 / lam * x t ^ (-(1 / 2) : ℝ) := by
  have hterm : ∀ j ∈ Finset.range t,
      x j ^ (-(3 / 2) : ℝ) ≤ 3 * (x t + lam * (((t - 1 - j : ℕ) : ℝ) + 1)) ^ (-(3 / 2) : ℝ) := by
    intro j hj
    have hj' : j < t := Finset.mem_range.mp hj
    have hle := hs j hj'.le
    have hcast : (((t - 1 - j : ℕ) : ℝ) + 1) = (t : ℝ) - j := by
      have : t - 1 - j + 1 = t - j := by omega
      rw [show (((t - 1 - j : ℕ) : ℝ) + 1) = (((t - 1 - j + 1 : ℕ)) : ℝ) by push_cast; ring, this,
        Nat.cast_sub hj'.le]
    rw [hcast]
    have htj : (1 : ℝ) ≤ (t : ℝ) - j := by
      have : ((j + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast hj'
      push_cast at this
      linarith
    set A := x t + lam * ((t : ℝ) - j) with hA
    have hA0 : 0 < A := by
      have : 0 ≤ lam * ((t : ℝ) - j) := by positivity
      linarith
    have hxj : A / 2 ≤ x j := by
      have : 0 ≤ lam * ((t : ℝ) - j) := by positivity
      nlinarith
    have h1 : x j ^ (-(3 / 2) : ℝ) ≤ (A / 2) ^ (-(3 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hxj (by norm_num)
    have h2 : (A / 2) ^ (-(3 / 2) : ℝ) ≤ 3 * A ^ (-(3 / 2) : ℝ) := by
      rw [rpow_neg_three_halves_eq_inv_sqrt_cube (by positivity), rpow_neg_three_halves_eq_inv_sqrt_cube hA0]
      have hs2 : Real.sqrt (A / 2) = Real.sqrt A / Real.sqrt 2 := Real.sqrt_div hA0.le 2
      rw [hs2, div_pow, inv_div]
      have hA1 : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA0
      have h21 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h22 : Real.sqrt 2 ≤ 3 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
      have h23 : Real.sqrt 2 ^ 3 ≤ 3 := by
        have : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
          rw [pow_succ, h21]
        rw [this]
        linarith
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h23 (by positivity)
    exact h1.trans h2
  have hsum := Finset.sum_le_sum hterm
  have hrefl := Finset.sum_range_reflect (fun i : ℕ => 3 * (x t + lam * ((i : ℝ) + 1)) ^ (-(3 / 2) : ℝ)) t
  rw [hrefl, ← Finset.mul_sum] at hsum
  have h3 := sum_rpow_neg_three_halves_le hlam hx t
  have hnn : 0 ≤ (x t + lam * t) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by positivity) _
  have h4 : 2 / lam * (x t ^ (-(1 / 2) : ℝ) - (x t + lam * t) ^ (-(1 / 2) : ℝ)) ≤
      2 / lam * x t ^ (-(1 / 2) : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  calc _ ≤ 3 * ∑ i ∈ Finset.range t, (x t + lam * ((i : ℝ) + 1)) ^ (-(3 / 2) : ℝ) := hsum
    _ ≤ 3 * (2 / lam * x t ^ (-(1 / 2) : ℝ)) := by linarith
    _ = _ := by ring
end Sum
section Flow
variable {ℓ : StepParameters}
theorem expansion_step (hR : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ} {D : TorusFunctional} (hx : ℓ.y₁ ≤ x)
    (h : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B ∧
      ∀ (x'' : ℝ) (f'' : LocalDensity), ColdExpansion ℓ (t + 1) x'' (kernelImage ℓ x D) f'' →
        x'' = expansionCoupling ℓ t x D := by
  obtain ⟨x', ⟨h1, h2⟩, h3⟩ := hR t x D hx h
  have hex : ∃ x' : ℝ, HasExpansion ℓ (t + 1) x' (kernelImage ℓ x D) := ⟨x', h1⟩
  have hc : expansionCoupling ℓ t x D = hex.choose := dif_pos hex
  obtain ⟨-, f, hf, -⟩ := hex.choose_spec
  have e : hex.choose = x' := h3 _ f hf
  rw [hc, e]
  exact ⟨h1, h2, h3⟩
end Flow
structure StageInvariant (T : ParameterAssignment) (K : ResponseParameters) (y β : ℝ) (t : ℕ)
    (z : StageWithResponse (T.stepParameters y)) : Prop where
  anchorRadius_eq : z.1.anchorRadius = T.ρA
  barrierFn_eq : z.1.barrierFn = T.cutoff
  depth_eq : z.1.depth = t
  coupling_eq : z.1.coupling = couplingsAlongFlow (T.stepParameters y) β t
  nextCoupling_eq : z.1.nextCoupling = couplingsAlongFlow (T.stepParameters y) β (t + 1)
  functional_eq : z.1.functional = (couplingFlow (T.stepParameters y) β t).2
  params_eq : z.2.responseParams = K
  hasExpansions : z.1.toStepSetup.HasExpansions
  admissible : z.2.IsAdmissible
  hasExpansion : HasExpansion (T.stepParameters y) t (couplingsAlongFlow (T.stepParameters y) β t)
    (couplingFlow (T.stepParameters y) β t).2
theorem StageInvariant.onParameterFamily {T : ParameterAssignment} {K : ResponseParameters} {y β : ℝ} {t : ℕ}
    {z : StageWithResponse (T.stepParameters y)}
    (h : StageInvariant T K y β t z) (hNK : K.N₀ = T.N 0) (hy : y ≤ z.1.coupling)
    (hmv : |z.1.nextCoupling - z.1.coupling| ≤ 2 * T.B)
    (h1 : z.1.coupling ≤ 1.01 * z.1.nextCoupling)
    (h2 : z.1.toStepSetup.range ≤ z.1.toStepSetup.nextRange + 1) : OnStepParameters T y z.2 :=
  ⟨⟨rfl, h.anchorRadius_eq, h.barrierFn_eq, hy, ⟨h.hasExpansions, h1, h2⟩⟩, hmv, h.admissible,
    by rw [h.params_eq]; exact hNK⟩
theorem StageInvariant.onFamily_and_step {T : ParameterAssignment} {K : ResponseParameters} {y β : ℝ} {t : ℕ}
    {z : StageWithResponse (T.stepParameters y)}
    (hNK : K.N₀ = T.N 0) (hR : ExpansionReturnsAt (T.stepParameters y))
    (hCold : ∀ R : StepSetup, R.OnParameters T y → R.IsSymmetricWeight →
      ColdExpansion R.params (R.depth + 1) (R.shiftedCoupling T.lam) (kernelImage R.params R.coupling R.functional)
        (R.renormalizedDensity T.lam))
    (hFl : ∀ x x' : ℝ, y ≤ x → |x' - x| ≤ 2 * T.B → x ≤ 1.01 * x' ∧ clusterRange x ≤ clusterRange x' + 1)
    (hI : StageInvariant T K y β t z) (hxt : y ≤ couplingsAlongFlow (T.stepParameters y) β t) :
    OnStepParameters T y z.2 ∧ z.1.toStepSetup.IsSymmetricWeight ∧
      z.1.nextCoupling = z.1.toStepSetup.shiftedCoupling T.lam := by
  obtain ⟨hrow', hmv', hun⟩ := expansion_step hR (t := t) (x := couplingsAlongFlow (T.stepParameters y) β t)
    (D := (couplingFlow (T.stepParameters y) β t).2) hxt hI.hasExpansion
  have hnext : couplingsAlongFlow (T.stepParameters y) β (t + 1) =
      expansionCoupling (T.stepParameters y) t (couplingsAlongFlow (T.stepParameters y) β t)
        (couplingFlow (T.stepParameters y) β t).2 := rfl
  have hmv : |z.1.nextCoupling - z.1.coupling| ≤ 2 * T.B := by
    rw [hI.nextCoupling_eq, hI.coupling_eq, hnext]
    exact hmv'
  have hfl := hFl z.1.coupling z.1.nextCoupling (by rw [hI.coupling_eq]; exact hxt) hmv
  have hAt : OnStepParameters T y z.2 :=
    hI.onParameterFamily hNK (by rw [hI.coupling_eq]; exact hxt) hmv hfl.1 hfl.2
  have hArr : z.1.toStepSetup.IsSymmetricWeight := by
    intro n _ hn
    show _ ∧ _
    have e : z.1.toStepSetup.functional = (couplingFlow (T.stepParameters y) β t).2 := hI.functional_eq
    rw [e]
    exact hI.hasExpansion.1 n hn
  refine ⟨hAt, hArr, ?_⟩
  have hc := hCold z.1.toStepSetup hAt.onFamily hArr
  have e₁ : z.1.toStepSetup.depth = t := hI.depth_eq
  have e₂ : z.1.toStepSetup.coupling = _ := hI.coupling_eq
  have e₃ : z.1.toStepSetup.functional = _ := hI.functional_eq
  have e₄ : z.1.toStepSetup.params = T.stepParameters y := rfl
  rw [e₁, e₂, e₃, e₄] at hc
  rw [hI.nextCoupling_eq, hnext]
  exact (hun _ _ hc).symm
theorem stageInvariant_of_initial {T : ParameterAssignment} {K : ResponseParameters} {y β Cs lam c₅ : ℝ}
    (hNK : K.N₀ = T.N 0)
    (hRet : ReturnsAtParameters T K Cs y) (hS : HasLinearDescent (T.stepParameters y) lam c₅) (hlam : 0 < lam)
    (hCs : 0 ≤ Cs) (hR : ExpansionReturnsAt (T.stepParameters y)) (hyβ : y ≤ β) (hy0 : 0 < y)
    (hCold : ∀ R : StepSetup, R.OnParameters T y → R.IsSymmetricWeight →
      ColdExpansion R.params (R.depth + 1) (R.shiftedCoupling T.lam) (kernelImage R.params R.coupling R.functional)
        (R.renormalizedDensity T.lam))
    (hFl : ∀ x x' : ℝ, y ≤ x → |x' - x| ≤ 2 * T.B → x ≤ 1.01 * x' ∧ clusterRange x ≤ clusterRange x' + 1)
    (hc₅ : 2 * c₅ ≤ y) (hnum : ∀ x : ℝ, y ≤ x → Cs * (6 / lam * x ^ (-(1 / 2) : ℝ)) ≤ 1 / 4)
    (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
    {z₀ : StageWithResponse (T.stepParameters y)} (h₀ : StageInvariant T K y β 0 z₀) (hal₀ : z₀.2.coeff = 1) :
    ∀ t : ℕ, FlowStaysAbove (T.stepParameters y) β (t + 1) →
      StageInvariant T K y β t (stagesFrom hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ t) ∧
      |(stagesFrom hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ t).2.coeff - 1| ≤
        Cs * ∑ j ∈ Finset.range t, couplingsAlongFlow (T.stepParameters y) β j ^ (-(3 / 2) : ℝ) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨h₀, ?_⟩
    simp [stagesFrom, hal₀]
  | succ t ih =>
    intro hst
    have hst' : FlowStaysAbove (T.stepParameters y) β (t + 1) := fun k hk => hst k (by omega)
    obtain ⟨hI, hal⟩ := ih hst'
    set z := stagesFrom hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ t with hz
    have hxt : y ≤ couplingsAlongFlow (T.stepParameters y) β t := hst' t (by omega)
    obtain ⟨hrow', -, -⟩ := expansion_step hR (t := t) (x := couplingsAlongFlow (T.stepParameters y) β t)
      (D := (couplingFlow (T.stepParameters y) β t).2) hxt hI.hasExpansion
    obtain ⟨hAt, hArr, hmove⟩ := StageInvariant.onFamily_and_step hNK hR hCold hFl hI hxt
    obtain ⟨⟨c₁, c₂, c₃⟩, al', hal', hresp, huniq⟩ :=
      hRet z.1.toStepSetup z.2 (hL z.1) hI.params_eq hAt hArr hmove
    have hex : ∃ al, StepHasResponseBounds z.1.toStepSetup z.2 (hL z.1) al := ⟨al', hresp⟩
    have hnum' : nextCoeff z.1.toStepSetup z.2 (hL z.1) = al' := by
      have e : nextCoeff z.1.toStepSetup z.2 (hL z.1) = hex.choose := dif_pos hex
      rw [e]
      exact huniq _ hex.choose_spec
    have hresp' : StepHasResponseBounds z.1.toStepSetup z.2 (hL z.1) (nextCoeff z.1.toStepSetup z.2 (hL z.1)) := by
      rw [hnum']
      exact hresp
    have hRa : nextSiteRemainder z.1.toStepSetup z.2 (hL z.1) = hresp'.choose := dif_pos hresp'
    have hRb : nextTotalRemainder z.1.toStepSetup z.2 (hL z.1) = hresp'.choose_spec.choose := dif_pos hresp'
    have hrow : ResponseBounds (T.stepParameters y) z.2.responseParams (z.1.depth + 1) z.1.nextCoupling
        (nextCoeff z.1.toStepSetup z.2 (hL z.1))
        (coarseLabelSpace z.1.toStepSetup (hL z.1)) (coarseWeightExpansion z.1.toStepSetup)
        (coarseLabelScore z.2.responseParams.s₁ z.2.score) z.2.coldStep z.2.hullStep
        (nextSiteRemainder z.1.toStepSetup z.2 (hL z.1)) (nextTotalRemainder z.1.toStepSetup z.2 (hL z.1)) := by
      rw [hRa, hRb]
      exact hresp'.choose_spec.choose_spec
    have hsum : |al' - 1| ≤
        Cs * ∑ j ∈ Finset.range (t + 1), couplingsAlongFlow (T.stepParameters y) β j ^ (-(3 / 2) : ℝ) := by
      rw [Finset.sum_range_succ, mul_add]
      have h1 : |al' - z.2.coeff| ≤ Cs * couplingsAlongFlow (T.stepParameters y) β t ^ (-(3 / 2) : ℝ) := by
        have := hal'
        have e : z.1.toStepSetup.coupling = couplingsAlongFlow (T.stepParameters y) β t := hI.coupling_eq
        rwa [e] at this
      have h2 := abs_sub_le al' z.2.coeff 1
      linarith
    have hxt1 : y ≤ couplingsAlongFlow (T.stepParameters y) β (t + 1) := hst (t + 1) (by omega)
    have hslope := sum_rpow_le_of_linear_descent (x := couplingsAlongFlow (T.stepParameters y) β) (t := t + 1)
      (c₅ := c₅) hlam (lt_of_lt_of_le hy0 hxt1) (hc₅.trans hxt1)
      (fun i hi => hS β hyβ (t + 1) hst' i hi)
    have hle : |al' - 1| ≤ 1 / 4 := by
      refine hsum.trans ((mul_le_mul_of_nonneg_left hslope hCs).trans (hnum _ hxt1))
    have hal2 : |al'| ≤ 2 := by
      have h3 := abs_sub_abs_le_abs_sub al' 1
      simp only [abs_one] at h3
      linarith
    refine ⟨?_, ?_⟩
    · exact
        { anchorRadius_eq := hI.anchorRadius_eq
          barrierFn_eq := hI.barrierFn_eq
          depth_eq := by
            show z.1.depth + 1 = t + 1
            rw [hI.depth_eq]
          coupling_eq := hI.nextCoupling_eq
          nextCoupling_eq := rfl
          functional_eq := by
            show kernelImage (T.stepParameters y) z.1.coupling z.1.functional = _
            rw [hI.coupling_eq, hI.functional_eq]
            rfl
          params_eq := hI.params_eq
          hasExpansions := ⟨c₁, c₂⟩
          admissible := ⟨hI.admissible.params_admissible, c₃, hrow, by
            show |nextCoeff z.1.toStepSetup z.2 (hL z.1)| ≤ 2
            rw [hnum']
            exact hal2⟩
          hasExpansion := hrow' }
    · show |nextCoeff z.1.toStepSetup z.2 (hL z.1) - 1| ≤ _
      rw [hnum']
      exact hsum
theorem mul_rpow_neg_half_le_quarter {x Cs lam : ℝ} (hCs : 0 ≤ Cs) (hlam : 0 < lam) (hx0 : 0 < x)
    (hx : (24 * Cs / lam) ^ 2 ≤ x) :
    Cs * (6 / lam * x ^ (-(1 / 2) : ℝ)) ≤ 1 / 4 := by
  rw [rpow_neg_half_eq_inv_sqrt hx0]
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx0
  have h1 : 24 * Cs / lam ≤ s := Real.le_sqrt_of_sq_le hx
  rw [div_le_iff₀ hlam] at h1
  have e : Cs * (6 / lam * s⁻¹) = 24 * Cs / (4 * lam * s) := by
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  nlinarith
theorem responseAlongFlow (hT3 : responseReturnsStatement)
    (hT2 : WilsonWeightHasResponseBoundsStatement) (hSl : FlowDescendsLinearly)
    (hCI : ImageColdExpansion.ImageHasColdExpansion) (hFlr : StepFloors.EventuallyFloorConditions) :
    responseAlongFlowStatement := by
  intro a ha
  obtain ⟨L₃, r₃, hr₃, g₃⟩ := hT3 a ha
  obtain ⟨L₁, r₁, hr₁, g₁⟩ := hSl a ha
  obtain ⟨r₂, hr₂, g₂⟩ := hCI
  obtain ⟨C₀, M₂, g₀⟩ := hT2
  refine ⟨max L₃ L₁, fun c => min (r₃ c) (min (r₁ c) (r₂ c)), C₀,
    fun c => lt_min (hr₃ c) (lt_min (hr₁ c) (hr₂ c)), fun L hLo hL T hTa hTL hT hCS hOn hrt hC M => ?_⟩
  have hrt₃ := hrt.trans (min_le_left _ _)
  have hrt₁ := (hrt.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrt₂ := (hrt.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨lam, c₅, hlam, g₁⟩ := g₁ L hLo ((le_max_right _ _).trans hL)
  have hL₃ : L₃ ≤ T.side := by
    rw [hTL]
    exact (le_max_left _ _).trans hL
  obtain ⟨K, hMK, hη, hN, hFit, Cs, y₃, hCs, g₃⟩ := g₃ T hTa hL₃ hT hCS hOn hrt₃ (max M (M₂ * T.weight 2))
  refine ⟨K, (le_max_left _ _).trans hMK, hη, hN, hFit, ?_⟩
  obtain ⟨y₁, g₁⟩ := g₁ T hTa hTL hT hrt₁
  obtain ⟨y₂, g₂⟩ := g₂ T hT hCS hrt₂
  obtain ⟨y₄, g₄⟩ := hFlr T hT 1 1 one_pos one_pos
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max T.floorMin (max (2 * c₅) (max 1 ((24 * Cs / lam) ^ 2)))),
    fun y hy hR hW β hLf hyβ => ?_⟩
  have e₁ : y₁ ≤ y := by
    refine le_trans ?_ hy
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have e₂ : y₂ ≤ y := by
    refine le_trans ?_ hy
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have e₃ : y₃ ≤ y := by
    refine le_trans ?_ hy
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have e₄ : y₄ ≤ y := by
    refine le_trans ?_ hy
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have e₅ : T.floorMin ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have e₆ : 2 * c₅ ≤ y := by
    refine le_trans ?_ hy
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have e₇ : 1 ≤ y := by
    refine le_trans ?_ hy
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have e₈ : (24 * Cs / lam) ^ 2 ≤ y := by
    refine le_trans ?_ hy
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hy0 : 0 < y := by linarith
  have hS : HasLinearDescent (T.stepParameters y) lam c₅ := g₁ y e₁ hR hW
  have hRet := g₃ y e₃
  have hCold : ∀ R : StepSetup, R.OnParameters T y → R.IsSymmetricWeight →
      ColdExpansion R.params (R.depth + 1) (R.shiftedCoupling T.lam) (kernelImage R.params R.coupling R.functional)
        (R.renormalizedDensity T.lam) :=
    fun R h₁ h₂ => (g₂ y e₂ R h₁ h₂).1
  have hFl : ∀ x x' : ℝ, y ≤ x → |x' - x| ≤ 2 * T.B → x ≤ 1.01 * x' ∧ clusterRange x ≤ clusterRange x' + 1 := by
    intro x x' hx hxx
    obtain ⟨p₁, -, p₃, -⟩ := (g₄ x (e₄.trans hx)).stable_nearby.2 x' hxx
    exact ⟨p₁, p₃⟩
  have hnum : ∀ x : ℝ, y ≤ x → Cs * (6 / lam * x ^ (-(1 / 2) : ℝ)) ≤ 1 / 4 :=
    fun x hx => mul_rpow_neg_half_le_quarter hCs hlam (hy0.trans_le hx) (e₈.trans hx)
  have hfit := hT.fits y e₅
  obtain ⟨Λ, -, f, hf, Dq, Φ, φ, hh, hsp, hrr⟩ := g₀ (T.stepParameters y) K hfit (hFit y) hC
    ((le_max_right _ _).trans hMK) β hyβ
  let R₀ : ChainStage (T.stepParameters y) :=
    { depth := 0, coupling := β, nextCoupling := couplingsAlongFlow (T.stepParameters y) β 1,
      functional := wilsonWeight β, density := f, labels := Λ, labelWeight := Dq, clusterFactor := Φ,
      siteDensity := φ, anchorRadius := T.ρA, barrierFn := T.cutoff }
  let A₀ : ResponseSetup R₀.toStepSetup :=
    { responseParams := K, coeff := 1, score := fun _ => 0, cold := wilsonColdResponse (T.stepParameters y).side,
      hull := wilsonHullResponse (T.stepParameters y).side Λ.Ω,
      siteRemainder := fun _ _ _ => 0, totalRemainder := fun _ _ _ => 0 }
  have h₀ : StageInvariant T K y β 0 ⟨R₀, A₀⟩ :=
    { anchorRadius_eq := rfl, barrierFn_eq := rfl, depth_eq := rfl, coupling_eq := rfl, nextCoupling_eq := rfl,
      functional_eq := rfl, params_eq := rfl
      hasExpansions := ⟨hf, hh⟩
      admissible := ⟨hFit y, hsp, hrr, by norm_num⟩
      hasExpansion := hW β hyβ }
  refine ⟨⟨R₀, A₀⟩, ⟨⟨K, f, Λ, Dq, Φ, φ, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩, fun t hst => ?_⟩
  obtain ⟨hI, hb⟩ := stageInvariant_of_initial hN hRet hS hlam hCs hR hyβ hy0 hCold hFl e₆ hnum hLf h₀ rfl t hst
  have hxt : y ≤ couplingsAlongFlow (T.stepParameters y) β t := hst t (by omega)
  obtain ⟨hAt, hArr, hmv⟩ := StageInvariant.onFamily_and_step hN hR hCold hFl hI hxt
  have hst' : FlowStaysAbove (T.stepParameters y) β t := fun k hk => hst k (by omega)
  have hslope := sum_rpow_le_of_linear_descent (x := couplingsAlongFlow (T.stepParameters y) β) (t := t)
    (c₅ := c₅) hlam (hy0.trans_le hxt) (e₆.trans hxt) (fun i hi => hS β hyβ t hst' i hi)
  exact ⟨hI.depth_eq, hI.coupling_eq, hI.nextCoupling_eq, hI.functional_eq, hI.params_eq, hAt, hArr, hmv,
    hb.trans ((mul_le_mul_of_nonneg_left hslope hCs).trans (hnum _ hxt))⟩
end YangMills.Construction.ResponseInTheExpansion.ResponseAlongFlow
end
