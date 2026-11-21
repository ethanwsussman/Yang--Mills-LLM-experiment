import YangMills.Construction.FreeEnergiesOfTheFlow.WilsonResponseOnEverySplitting
import YangMills.Construction.HullsInEveryVolume.LevelsFromAnExpansionWhereTheResponseReturns
import YangMills.Construction.ResponseInTheExpansion.ResponseAlongTheFlowProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HullTrees
open TorusLumps RenormalizationStepParameters StepSettings StepReturn WeightedResponses ResponseInTheExpansion ClusterExpansionOfAStep
section PowerSums
private theorem sum_rpow_le_of_linear_descent {x : ℕ → ℝ} {lam c₅ : ℝ} {t : ℕ} (hlam : 0 < lam)
    (hx : 0 < x t) (hc : 2 * c₅ ≤ x t)
    (hs : ∀ i ≤ t, lam * ((t : ℝ) - i) - c₅ ≤ x i - x t) :
    ∑ j ∈ Finset.range t, x j ^ (-(3 / 2) : ℝ) ≤ 6 / lam * x t ^ (-(1 / 2) : ℝ) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.ResponseAlongFlow.sum_rpow_le_of_linear_descent <;> assumption
end PowerSums
section Flow
variable {ℓ : TorusLumps.StepParameters}
private theorem expansion_step (hR : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ} {D : TorusFunctional}
    (hx : ℓ.y₁ ≤ x) (h : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B ∧
      ∀ (x'' : ℝ) (f'' : LocalDensity), ColdExpansion ℓ (t + 1) x'' (kernelImage ℓ x D) f'' →
        x'' = expansionCoupling ℓ t x D := by apply _root_.YangMills.Construction.ResponseInTheExpansion.ResponseAlongFlow.expansion_step <;> assumption
end Flow
private structure StageInvariant (T : ParameterAssignment) (K : ResponseParameters) (y β : ℝ) (t : ℕ)
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
private theorem onParameterFamily_of_invariant {T : ParameterAssignment} {K : ResponseParameters} {y β : ℝ} {t : ℕ}
    {z : StageWithResponse (T.stepParameters y)}
    (h : StageInvariant T K y β t z) (hNK : K.N₀ = T.N 0) (hy : y ≤ z.1.coupling)
    (hmv : |z.1.nextCoupling - z.1.coupling| ≤ 2 * T.B)
    (h1 : z.1.coupling ≤ 1.01 * z.1.nextCoupling)
    (h2 : z.1.toStepSetup.range ≤ z.1.toStepSetup.nextRange + 1) : OnStepParameters T y z.2 :=
  ⟨⟨rfl, h.anchorRadius_eq, h.barrierFn_eq, hy, ⟨h.hasExpansions, h1, h2⟩⟩, hmv, h.admissible,
    by rw [h.params_eq]; exact hNK⟩
private theorem onParameterFamily_and_shift {T : ParameterAssignment} {K : ResponseParameters} {y β : ℝ} {t : ℕ}
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
    onParameterFamily_of_invariant hI hNK (by rw [hI.coupling_eq]; exact hxt) hmv hfl.1 hfl.2
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
private theorem stageInvariant_all {T : ParameterAssignment} {K : ResponseParameters} {y β Cs lam c₅ : ℝ}
    (hNK : K.N₀ = T.N 0)
    (hRet : ReturnsAtParameters T K Cs y) (hS : HasLinearDescent (T.stepParameters y) lam c₅) (hlam : 0 < lam)
    (hCs : 0 ≤ Cs)
    (hR : ExpansionReturnsAt (T.stepParameters y)) (hyβ : y ≤ β) (hy0 : 0 < y)
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
    obtain ⟨hAt, hArr, hmove⟩ := onParameterFamily_and_shift hNK hR hCold hFl hI hxt
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
private theorem coeff_drift_le_quarter {x Cs lam : ℝ} (hCs : 0 ≤ Cs) (hlam : 0 < lam) (hx0 : 0 < x)
    (hx : (24 * Cs / lam) ^ 2 ≤ x) :
    Cs * (6 / lam * x ^ (-(1 / 2) : ℝ)) ≤ 1 / 4 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.ResponseAlongFlow.mul_rpow_neg_half_le_quarter <;> assumption
theorem stagesFromReturningExpansion_holds
    (hT2 : FreeEnergiesOfTheFlow.WilsonResponseEverySplitting)
    (hSl : FlowDescendsLinearly) (hCI : ImageColdExpansion.ImageHasColdExpansion)
    (hFlr : StepFloors.EventuallyFloorConditions) :
    stagesFromReturningExpansionStatement := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, g₁⟩ := hSl a ha
  obtain ⟨r₂, hr₂, g₂⟩ := hCI
  obtain ⟨M₂, g₀⟩ := hT2
  refine ⟨L₁, fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c),
    fun L hLo hL T hTa hTL hT hCS hrt => ?_⟩
  have hrt₁ := hrt.trans (min_le_left _ _)
  have hrt₂ := hrt.trans (min_le_right _ _)
  obtain ⟨lam, c₅, hlam, g₁⟩ := g₁ L hLo hL
  refine ⟨M₂ * T.weight 2, fun K hMK hN hFit hRet₀ => ?_⟩
  obtain ⟨Cs, y₃, hCs, g₃⟩ := hRet₀
  obtain ⟨y₁, g₁⟩ := g₁ T hTa hTL hT hrt₁
  obtain ⟨y₂, g₂⟩ := g₂ T hT hCS hrt₂
  obtain ⟨y₄, g₄⟩ := hFlr T hT 1 1 one_pos one_pos
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max T.floorMin (max (2 * c₅) (max 1 ((24 * Cs / lam) ^ 2)))),
    fun y hy hR hW β hLf z₀ hyβ hfirst hzK hrow => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨⟨⟨e₁, e₂⟩, e₃, e₄⟩, e₅, e₆, e₇, e₈⟩ := hy
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
    fun x hx => coeff_drift_le_quarter hCs hlam (hy0.trans_le hx) (e₈.trans hx)
  have hfit := hT.fits y e₅
  have hβ₁ : (T.stepParameters y).y₁ ≤ β := hyβ
  have hresp : z₀.2.IsAdmissible := by
    obtain ⟨K', f, Λ, Dq, Φ, φ, hz⟩ := hfirst.isWilson
    subst hz
    obtain ⟨h₁, h₂⟩ := g₀ (T.stepParameters y) K hfit (hFit y) hMK β hβ₁ f Λ Dq Φ φ hrow.2
    obtain rfl : K' = K := hzK
    exact ⟨hFit y, h₁, h₂, by show |(1 : ℝ)| ≤ 2; norm_num⟩
  have h₀ : StageInvariant T K y β 0 z₀ :=
    { anchorRadius_eq := hfirst.anchorRadius_eq, barrierFn_eq := hfirst.barrierFn_eq
      depth_eq := hfirst.depth_eq, coupling_eq := hfirst.coupling_eq
      nextCoupling_eq := hfirst.nextCoupling_eq, functional_eq := hfirst.functional_eq, params_eq := hzK
      hasExpansions := hrow, admissible := hresp
      hasExpansion := hW β hyβ }
  intro t hst
  obtain ⟨hI, hb⟩ :=
    stageInvariant_all hN hRet hS hlam hCs hR hyβ hy0 hCold hFl e₆ hnum hLf h₀ hfirst.coeff_eq t hst
  have hxt : y ≤ couplingsAlongFlow (T.stepParameters y) β t := hst t (by omega)
  obtain ⟨hAt, hArr, hmv⟩ := onParameterFamily_and_shift hN hR hCold hFl hI hxt
  have hst' : FlowStaysAbove (T.stepParameters y) β t := fun k hk => hst k (by omega)
  have hslope := sum_rpow_le_of_linear_descent (x := couplingsAlongFlow (T.stepParameters y) β) (t := t)
    (c₅ := c₅) hlam (hy0.trans_le hxt) (e₆.trans hxt) (fun i hi => hS β hyβ t hst' i hi)
  exact ⟨hI.depth_eq, hI.coupling_eq, hI.nextCoupling_eq, hI.functional_eq, hI.params_eq, hAt, hArr, hmv,
    hb.trans ((mul_le_mul_of_nonneg_left hslope hCs).trans (hnum _ hxt))⟩
end YangMills.Construction.HullTrees
end
