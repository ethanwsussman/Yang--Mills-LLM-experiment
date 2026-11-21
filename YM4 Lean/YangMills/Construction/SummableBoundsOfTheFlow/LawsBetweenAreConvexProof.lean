import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexAboveAChartPoint
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMembersAreClosed
import YangMills.Construction.ColdStepAtMirrorFrames.SumsOverCellsAndBonds
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenStayNear
import YangMills.Construction.SummableBoundsOfTheFlow.LawsBetweenAreConvex
import YangMills.Construction.SummableBoundsOfTheFlow.MemberThroughAnInjection
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeOfTheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.FamilyNorms
namespace YangMills.Construction.Interpolation
section Calculus
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem eventually_norm_lt {ρ : ℝ} {η : BondField ι} (h : ∀ b, ‖η b‖ < ρ) :
    ∀ᶠ ζ in 𝓝 η, ∀ b, ‖ζ b‖ < ρ := by
  refine Filter.eventually_all.2 fun b => ?_
  have hc : Continuous fun ζ : BondField ι => ‖ζ b‖ := (continuous_apply b).norm
  exact hc.continuousAt.eventually_lt continuousAt_const (h b)
private theorem differentiableAt_of_member {ρ m κ : ℝ} {d : ι → ι → ℝ} {P : BondField ι → ℝ}
    (hP : IsConvexClassMember ρ m κ d P) {η : BondField ι} (h : ∀ b, ‖η b‖ < ρ) :
    DifferentiableAt ℝ P η := by
  obtain ⟨Ψ, K, hag, hc, _⟩ := hP
  have h1 : DifferentiableAt ℝ Ψ η := (hc.smooth.differentiable (by norm_num)) η
  exact h1.congr_of_eventuallyEq ((eventually_norm_lt h).mono fun ζ hζ => (hag ζ hζ).symm)
private def weightedSquares (S : Finset ι) (c : ℝ) (ζ : BondField ι) : ℝ := ∑ i ∈ S, c * ‖ζ i‖ ^ 2
private theorem weightedSquares_hasFDerivAt (S : Finset ι) (c : ℝ) (ζ : BondField ι) :
    HasFDerivAt (weightedSquares S c) (∑ i ∈ S, c • ((2 : ℕ) • (innerSL ℝ (ζ i)).comp
      (ContinuousLinearMap.proj i : BondField ι →L[ℝ] BondVector))) ζ := by
  have h : ∀ i ∈ S, HasFDerivAt (fun ξ : BondField ι => c * ‖ξ i‖ ^ 2)
      (c • ((2 : ℕ) • (innerSL ℝ (ζ i)).comp
        (ContinuousLinearMap.proj i : BondField ι →L[ℝ] BondVector))) ζ := fun i _ =>
    (((ContinuousLinearMap.proj i : BondField ι →L[ℝ] BondVector).hasFDerivAt).norm_sq).const_mul c
  exact HasFDerivAt.fun_sum h
private theorem bondPartialDeriv_weightedSquares (S : Finset ι) (c : ℝ) (ζ : BondField ι) (b : ι)
    (e : BondVector) :
    bondPartialDeriv (weightedSquares S c) b ζ e = if b ∈ S then 2 * c * inner ℝ (ζ b) e else 0 := by
  unfold bondPartialDeriv
  rw [(weightedSquares_hasFDerivAt S c ζ).fderiv, ContinuousLinearMap.sum_apply]
  have hterm : ∀ i, (c • ((2 : ℕ) • (innerSL ℝ (ζ i)).comp
      (ContinuousLinearMap.proj i : BondField ι →L[ℝ] BondVector))) (bondVariation b e) =
      if i = b then 2 * c * inner ℝ (ζ b) e else 0 := by
    intro i
    by_cases hi : i = b
    · subst hi
      simp [bondVariation]
      ring
    · have h0 : (bondVariation b e : BondField ι) i = 0 := Pi.single_eq_of_ne hi _
      simp [hi, h0]
  simp only [hterm]
  rw [Finset.sum_ite_eq' S b]
private theorem abs_bondPartialDeriv_weightedSquares_le (S : Finset ι) {c : ℝ} (hc : 0 ≤ c)
    (ζ : BondField ι) (b : ι) (e : BondVector) :
    |bondPartialDeriv (weightedSquares S c) b ζ e| ≤ 2 * c * ‖ζ b‖ * ‖e‖ := by
  rw [bondPartialDeriv_weightedSquares]
  have h1 : |(inner ℝ (ζ b) e : ℝ)| ≤ ‖ζ b‖ * ‖e‖ := abs_real_inner_le_norm _ _
  split_ifs
  · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c)]
    calc _ ≤ 2 * c * (‖ζ b‖ * ‖e‖) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  · simp only [abs_zero]
    positivity
private theorem member_finset_mixture {ρ m κ : ℝ} {d : ι → ι → ℝ} {α : Type}
    (hcl : ∀ (P Q : BondField ι → ℝ) (t : ℝ), 0 ≤ t → t ≤ 1 → IsConvexClassMember ρ m κ d P →
      IsConvexClassMember ρ m κ d Q → IsConvexClassMember ρ m κ d fun η => t * P η + (1 - t) * Q η)
    (w : α → ℝ) (P : α → BondField ι → ℝ) (s : Finset α) :
    (∀ l ∈ s, 0 ≤ w l) → (∀ l ∈ s, IsConvexClassMember ρ m κ d (P l)) → 0 < ∑ l ∈ s, w l →
      IsConvexClassMember ρ m κ d fun η => (∑ l ∈ s, w l * P l η) / ∑ l ∈ s, w l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ h
    simp at h
  | insert a s ha ih =>
    intro hw hP hpos
    rw [Finset.sum_insert ha] at hpos
    have hwa := hw a (Finset.mem_insert_self a s)
    have hws : ∀ l ∈ s, 0 ≤ w l := fun l hl => hw l (Finset.mem_insert_of_mem hl)
    have hPs : ∀ l ∈ s, IsConvexClassMember ρ m κ d (P l) := fun l hl =>
      hP l (Finset.mem_insert_of_mem hl)
    have hW0 : 0 ≤ ∑ l ∈ s, w l := Finset.sum_nonneg hws
    rcases hW0.eq_or_lt with hW | hW
    · have hz : ∀ l ∈ s, w l = 0 := (Finset.sum_eq_zero_iff_of_nonneg hws).1 hW.symm
      have ha0 : 0 < w a := by linarith
      have hfun : (fun η => (∑ l ∈ insert a s, w l * P l η) / ∑ l ∈ insert a s, w l) = P a := by
        funext η
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ← hW,
          Finset.sum_eq_zero fun l hl => by rw [hz l hl, zero_mul]]
        rw [add_zero, add_zero, mul_comm, mul_div_assoc, div_self ha0.ne', mul_one]
      rw [hfun]
      exact hP a (Finset.mem_insert_self a s)
    · have hsum : 0 < w a + ∑ l ∈ s, w l := by linarith
      have hfun : (fun η => (∑ l ∈ insert a s, w l * P l η) / ∑ l ∈ insert a s, w l) =
          fun η => (w a / (w a + ∑ l ∈ s, w l)) * P a η +
            (1 - w a / (w a + ∑ l ∈ s, w l)) * ((∑ l ∈ s, w l * P l η) / ∑ l ∈ s, w l) := by
        funext η
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        field_simp
        ring
      rw [hfun]
      refine hcl _ _ _ (by positivity) ?_ (hP a (Finset.mem_insert_self a s)) (ih hws hPs hW)
      rw [div_le_one hsum]
      linarith
end Calculus
section EvaluationMaps
variable {F : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι]
private abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
private def extendByZeroCLM (j : ι → ChordBond F) (Λ : Finset ι) :
    BondField ι →L[ℝ] StepVariable (finiteCells F) :=
  ContinuousLinearMap.pi fun b => ∑ i ∈ Λ, if j i = b then
    (ContinuousLinearMap.proj i : BondField ι →L[ℝ] BondVector) else 0
private theorem extendByZeroCLM_apply (j : ι → ChordBond F) (Λ : Finset ι) (ζ : BondField ι) :
    extendByZeroCLM j Λ ζ = extendByZero j Λ ζ := by
  funext b
  simp only [extendByZeroCLM, extendByZero, ContinuousLinearMap.coe_pi', ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp
private theorem extendByZeroCLM_bondVariation {j : ι → ChordBond F} (hj : Function.Injective j)
    (Λ : Finset ι) (i : ι) (e : BondVector) :
    extendByZeroCLM j Λ (bondVariation i e) = if i ∈ Λ then bondVariation (j i) e else 0 := by
  rw [extendByZeroCLM_apply]
  funext b
  unfold extendByZero
  have hoff : ∀ k, k ≠ i → (if j k = b then (bondVariation i e : BondField ι) k else 0) = 0 := by
    intro k hk
    have h0 : (bondVariation i e : BondField ι) k = 0 := Pi.single_eq_of_ne hk _
    simp [h0]
  by_cases hi : i ∈ Λ
  · rw [if_pos hi, Finset.sum_eq_single i (fun k _ hk => hoff k hk) (fun h => absurd hi h)]
    by_cases hb : j i = b
    · subst hb
      simp [bondVariation]
    · have h0 : (bondVariation (j i) e : StepVariable (finiteCells F)) b = 0 :=
        Pi.single_eq_of_ne (Ne.symm hb) _
      rw [if_neg hb, h0]
  · rw [if_neg hi, Finset.sum_eq_zero fun k hk => hoff k fun h => hi (h ▸ hk)]
    rfl
private theorem norm_extendByZero_lt {j : ι → ChordBond F} (hj : Function.Injective j)
    (Λ : Finset ι) {ρ : ℝ} (hρ : 0 < ρ) {ζ : BondField ι} (h : ∀ i, ‖ζ i‖ < ρ) (b : ChordBond F) :
    ‖extendByZero j Λ ζ b‖ < ρ := by
  unfold extendByZero
  by_cases hb : ∃ i ∈ Λ, j i = b
  · obtain ⟨i, hi, rfl⟩ := hb
    rw [Finset.sum_eq_single i (fun k _ hk => if_neg fun hc => hk (hj hc))
      (fun h' => absurd hi h'), if_pos rfl]
    exact h i
  · rw [Finset.sum_eq_zero fun k hk => if_neg fun hc => hb ⟨k, hk, hc⟩]
    simpa using hρ
abbrev _root_.YangMills.DeltaSharedProofs.p501821 := @norm_extendByZero_lt
private theorem frozenExponent_eq (lam x : ℝ) (j : ι → ChordBond F) (Λ : Finset ι)
    (Ψ : StepVariable (finiteCells F) → ℝ) :
    frozenExponent lam x j Λ Ψ = fun ζ => Ψ (extendByZeroCLM j Λ ζ) +
      weightedSquares (Finset.univ \ Λ) (x * lam / 2) ζ := by
  funext ζ
  rw [extendByZeroCLM_apply]
  rfl
private theorem frozenExponent_hasFDerivAt (lam x : ℝ) (j : ι → ChordBond F) (Λ : Finset ι)
    {Ψ : StepVariable (finiteCells F) → ℝ} {ζ : BondField ι}
    (hd : DifferentiableAt ℝ Ψ (extendByZero j Λ ζ)) :
    HasFDerivAt (frozenExponent lam x j Λ Ψ)
      ((fderiv ℝ Ψ (extendByZero j Λ ζ)).comp (extendByZeroCLM j Λ) +
        fderiv ℝ (weightedSquares (Finset.univ \ Λ) (x * lam / 2)) ζ) ζ := by
  rw [frozenExponent_eq]
  have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (extendByZero j Λ ζ)) (extendByZeroCLM j Λ ζ) := by
    rw [extendByZeroCLM_apply]
    exact hd.hasFDerivAt
  have h2 := h1.comp ζ (extendByZeroCLM j Λ).hasFDerivAt
  exact h2.add (weightedSquares_hasFDerivAt _ _ ζ).differentiableAt.hasFDerivAt
private theorem abs_bondPartialDeriv_frozenExponent_le {lam x ρ C : ℝ} {j : ι → ChordBond F}
    (hj : Function.Injective j) (Λ : Finset ι) {Ψ : StepVariable (finiteCells F) → ℝ} (hρ : 0 < ρ)
    (hc : 0 ≤ x * lam) (hC : x * lam * ρ ≤ C)
    (hd : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → DifferentiableAt ℝ Ψ η)
    (hs : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → ∀ (b : ChordBond F) (e : BondVector),
      |bondPartialDeriv Ψ b η e| ≤ C * ‖e‖) {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < ρ) (i : ι)
    (e : BondVector) : |bondPartialDeriv (frozenExponent lam x j Λ Ψ) i ζ e| ≤ C * ‖e‖ := by
  have hb := norm_extendByZero_lt hj Λ hρ hζ
  have hf := frozenExponent_hasFDerivAt lam x j Λ (hd _ hb)
  have hne := norm_nonneg e
  have hval : bondPartialDeriv (frozenExponent lam x j Λ Ψ) i ζ e =
      (if i ∈ Λ then bondPartialDeriv Ψ (j i) (extendByZero j Λ ζ) e else 0) +
        bondPartialDeriv (weightedSquares (Finset.univ \ Λ) (x * lam / 2)) i ζ e := by
    unfold bondPartialDeriv
    rw [hf.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
    rw [extendByZeroCLM_bondVariation hj]
    by_cases hi : i ∈ Λ
    · simp [hi]
    · simp [hi]
  rw [hval]
  by_cases hi : i ∈ Λ
  · have h0 : bondPartialDeriv (weightedSquares (Finset.univ \ Λ) (x * lam / 2)) i ζ e = 0 := by
      rw [bondPartialDeriv_weightedSquares, if_neg]
      simpa using hi
    rw [if_pos hi, h0, add_zero]
    exact hs _ hb _ _
  · rw [if_neg hi, zero_add]
    have h1 := abs_bondPartialDeriv_weightedSquares_le (Finset.univ \ Λ)
      (by positivity : 0 ≤ x * lam / 2) ζ i e
    have h2 : 2 * (x * lam / 2) * ‖ζ i‖ * ‖e‖ ≤ x * lam * ρ * ‖e‖ := by
      have h3 := (hζ i).le
      have h4 : x * lam * ‖ζ i‖ ≤ x * lam * ρ := mul_le_mul_of_nonneg_left h3 hc
      calc _ = x * lam * ‖ζ i‖ * ‖e‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h4 hne
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right hC hne))
private theorem extendByZero_restrictToSupport (j : ι → ChordBond F) (Λ : Finset ι) (ζ : BondField ι) :
    ConvexRestriction.extendByZero j (restrictToSupport Λ ζ) = extendByZero j Λ ζ := by
  funext b
  unfold ConvexRestriction.extendByZero extendByZero restrictToSupport
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Λ)]
  have h1 : ∑ i ∈ Finset.univ.filter (· ∉ Λ), (if j i = b then (if i ∈ Λ then ζ i else 0) else 0) =
      (0 : BondVector) := Finset.sum_eq_zero fun i hi => by
    have := (Finset.mem_filter.1 hi).2
    simp [this]
  rw [h1, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [hi]
private theorem frozenExponent_member {lam x ρ κ : ℝ} {d : ι → ι → ℝ} {j : ι → ChordBond F}
    (hj : Function.Injective j) (Λ : Finset ι) {Ψ : StepVariable (finiteCells F) → ℝ} (hρ : 0 < ρ)
    (hκ : 0 ≤ κ) (hm : 0 < x * lam / 4)
    (hI : ConvexRestriction.IsConvexClassMemberCompInjective) (hCl : ConvexClassClosure)
    (hbd : IsPseudoMetricOnBonds d) (hnn : ∀ b b', 0 ≤ d b b') (hdist : PreservesCellDist j d)
    (hcn : ∀ b b' : ChordBond F, 0 ≤ chordBondDist F b b')
    (hΨ : IsConvexClassMember ρ (x * lam / 4) κ (chordBondDist F) Ψ) :
    IsConvexClassMember ρ (x * lam / 4) κ d (frozenExponent lam x j Λ Ψ) := by
  have h1 := hI ι (ChordBond F) ρ (x * lam / 4) κ d (chordBondDist F) j Ψ hρ hκ hj hdist hcn hΨ
  have h2 := (hCl ι ρ (x * lam / 4) κ d hρ hm hκ hbd hnn).2.2 _ Λ h1
  have e : (fun η => Ψ (ConvexRestriction.extendByZero j (restrictToSupport Λ η)) +
      ∑ b ∈ Finset.univ \ Λ, 2 * (x * lam / 4) * ‖η b‖ ^ 2) = frozenExponent lam x j Λ Ψ := by
    funext η
    unfold frozenExponent
    rw [extendByZero_restrictToSupport]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [← e]
  exact h2
end EvaluationMaps
section Frames
variable {F : BlockFrame}
private def toImaginaryCLM : BondVector →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => toImaginary v
      map_add' := fun u v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = 0 + 0
          simp
        · change (u + v) 0 = u 0 + v 0
          simp
        · change (u + v) 1 = u 1 + v 1
          simp
        · change (u + v) 2 = u 2 + v 2
          simp
      map_smul' := fun c v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = c * 0
          simp
        · change (c • v) 0 = c * v 0
          simp
        · change (c • v) 1 = c * v 1
          simp
        · change (c • v) 2 = c * v 2
          simp }
private theorem toImaginaryCLM_apply (v : BondVector) : toImaginaryCLM v = toImaginary v := rfl
private theorem norm_toImaginaryCLM (v : BondVector) : ‖toImaginaryCLM v‖ = ‖v‖ := by
  have h1 : ‖toImaginaryCLM v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h := Quaternion.normSq_eq_norm_mul_self ((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])
    rw [Quaternion.normSq_def'] at h
    have h2 : ‖(toImaginaryCLM v : imaginaryQuaternions)‖ =
        ‖((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
    rw [h2, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, pow_two]
    simp only [toImaginaryCLM_apply, toImaginary, Real.norm_eq_abs, sq_abs] at h ⊢
    linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
private theorem stepCoordinates_smul_bondVariation (b : ChordBond F) (e : BondVector) (u : ℝ)
    (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (u • (bondVariation b e : StepVariable (finiteCells F))) x i =
      if (x, i) = b.1 then u • toImaginaryCLM e else 0 := by
  classical
  unfold stepCoordinates
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos h]
    by_cases hb : (x, i) = b.1
    · have hbb : (⟨(x, i), h⟩ : ChordBond F) = b := Subtype.ext hb
      rw [if_pos hb, hbb, ← toImaginaryCLM_apply]
      simp [bondVariation]
    · have hbb : (⟨(x, i), h⟩ : ChordBond F) ≠ b := fun hc => hb (congrArg Subtype.val hc)
      have h0 : (bondVariation b e : StepVariable (finiteCells F)) ⟨(x, i), h⟩ = 0 :=
        Pi.single_eq_of_ne hbb _
      rw [if_neg hb, ← toImaginaryCLM_apply]
      simp [h0]
  · rw [dif_neg h, if_neg]
    intro hc
    exact h (hc ▸ b.2)
private theorem stepCoordinates_zero (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  classical
  unfold stepCoordinates
  split_ifs
  · rw [Pi.zero_apply, ← toImaginaryCLM_apply, map_zero]
  · rfl
private theorem bondPartialDeriv_chartedEnergyAt_eq {a : ℝ}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    (hA : DifferentiableAt ℝ (chartedEnergyAt a w V) 0) (b : ChordBond F) (e : BondVector) :
    bondPartialDeriv (chartedEnergyAt a w V) b 0 e = chartedSlope a w V b.1 (toImaginaryCLM e) := by
  have hline : (fun u : ℝ => chartedEnergy a (Function.update w b.1.1 (Function.update (w b.1.1) b.1.2
      (w b.1.1 b.1.2 + u • toImaginaryCLM e))) V) =
      fun u : ℝ => chartedEnergyAt a w V (u • (bondVariation b e : StepVariable (finiteCells F))) := by
    funext u
    unfold chartedEnergyAt
    congr 1
    funext x i
    rw [stepCoordinates_smul_bondVariation]
    by_cases hx : x = b.1.1
    · subst hx
      by_cases hi : i = b.1.2
      · subst hi
        simp
      · have hne : (b.1.1, i) ≠ b.1 := fun h => hi (congrArg Prod.snd h)
        simp [hi, hne]
    · have hne : (x, i) ≠ b.1 := fun h => hx (congrArg Prod.fst h)
      simp [hx, hne]
  unfold chartedSlope
  rw [hline]
  have h1 : HasDerivAt (fun u : ℝ => u • (bondVariation b e : StepVariable (finiteCells F)))
      (bondVariation b e) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (bondVariation b e : StepVariable (finiteCells F))
  have h2 : HasFDerivAt (chartedEnergyAt a w V) (fderiv ℝ (chartedEnergyAt a w V) 0)
      ((0 : ℝ) • (bondVariation b e : StepVariable (finiteCells F))) := by
    simpa using hA.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  exact h3.deriv.symm
private structure SlopeBounds (T : StepParameters) : Prop where
  lam_pos : 0 < T.chainParams.lam
  Ct_ge : 2 * (T.chainParams.lam + 1) ≤ T.Ct
  σ_le_one : T.σ ≤ 1
  size_bound : T.Ct * T.σ + T.σ / 64 ≤ 1 / (64 * (T.L : ℝ))
  contour_bound : T.Ct * T.σ + 5 * (T.L : ℝ) * (T.σ / 64) ≤ 1 / 2
  one_le_coupling : 1 ≤ T.coupling
  one_le_n₀ : 1 ≤ T.n₀
private theorem slopeBounds_eventually : EventuallyInParameters SlopeBounds := by
  intro a _
  refine ⟨0, fun L hL _ c hc => ⟨2 * (c.lam + 1), fun Ct hCt => ⟨1, one_pos, fun κ _ _ =>
    ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun nss _ => ?_⟩⟩⟩⟩⟩
  have hlam : 0 < c.lam := hc.positivity.2.2.1
  have hB : 1 ≤ Ct + 1 := by linarith
  have hL0 : (0 : ℝ) < L := by
    have : 0 < L := hL.pos
    exact_mod_cast this
  refine ⟨1 / (128 * ((L : ℝ) + 1) * (Ct + 1)), by positivity, fun σ hσ0 hσ p _ =>
    ⟨0, fun Cs _ E _ => ⟨1, fun n₀ hn₀ => ⟨0, fun CE _ => ⟨1, fun y₁ hy => ?_⟩⟩⟩⟩⟩
  have hs : σ * (((L : ℝ) + 1) * (Ct + 1)) ≤ 1 / 128 := by
    have h1 : σ * (128 * ((L : ℝ) + 1) * (Ct + 1)) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at hσ
    nlinarith
  have hsB : σ * (Ct + 1) ≤ σ * (((L : ℝ) + 1) * (Ct + 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ hσ0.le
    nlinarith
  have hsA : σ * ((L : ℝ) + 1) ≤ σ * (((L : ℝ) + 1) * (Ct + 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ hσ0.le
    nlinarith
  have hs1 : σ ≤ σ * (((L : ℝ) + 1) * (Ct + 1)) := by nlinarith
  refine ⟨hlam, hCt, ?_, ?_, ?_, hy, hn₀⟩
  · show σ ≤ 1
    linarith
  · show Ct * σ + σ / 64 ≤ 1 / (64 * (L : ℝ))
    rw [le_div_iff₀ (by positivity)]
    have h1 : Ct * σ + σ / 64 ≤ σ * (Ct + 1) := by nlinarith
    have h2 : (Ct * σ + σ / 64) * (64 * (L : ℝ)) ≤ σ * (Ct + 1) * (64 * ((L : ℝ) + 1)) := by
      have h3 : 0 ≤ Ct * σ + σ / 64 := by
        have : 0 ≤ Ct := by linarith
        positivity
      have h4 : 64 * (L : ℝ) ≤ 64 * ((L : ℝ) + 1) := by linarith
      calc _ ≤ (Ct * σ + σ / 64) * (64 * ((L : ℝ) + 1)) := mul_le_mul_of_nonneg_left h4 h3
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)
    nlinarith
  · show Ct * σ + 5 * (L : ℝ) * (σ / 64) ≤ 1 / 2
    nlinarith
variable {T : StepParameters}
private theorem interpolatedFrame_isChartBasePoint (hf : SlopeBounds T) {t : ℕ} {m : ℕ} {s : ℝ}
    {V : F.GaugeField F.top} (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hsm : InterpolatedFrameSmall s T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ m V) :
    IsChartBasePoint T (fun z i => interpolatedFrame s T.a T.chainParams.ρA m (z, i) V) V := by
  have hρ : T.ballRadius = T.σ / 64 := rfl
  refine ⟨fun b hb => hsm.norm_add_le b hb, fun b hb => ?_, ?_, fun c h π hh => ?_⟩
  · have h1 := hsm.norm_le b hb
    have h2 := hf.size_bound
    rw [hρ]
    linarith
  · have h1 := hsm.small_curvature
    have e : interpolatedCoords s T.a T.chainParams.ρA m V 0 =
        fun z i => interpolatedFrame s T.a T.chainParams.ρA m (z, i) V := by
      funext z i
      unfold interpolatedCoords
      rw [stepCoordinates_zero, add_zero]
    unfold interpolatedField at h1
    rwa [e] at h1
  · have h1 := hsm.contour_near_one c h π (hF.1 ▸ hh)
    have h2 := hf.contour_bound
    rw [hρ]
    linarith
private theorem mul_abs_slope_le_one {x : ℝ} {m : ℕ} {s C ω δ : ℝ} {V : F.GaugeField F.top}
    (hst : InterpolatedSlopeSmall s T.a T.chainParams.ρA δ C ω x m V) (b : ChordBond F) (e : BondVector)
    (he : ‖e‖ = 1) :
    x * |bondPartialDeriv (chartedEnergyAt T.a
      (fun z i => interpolatedFrame s T.a T.chainParams.ρA m (z, i) V) V) b 0 e| ≤ 1 := by
  by_cases hd : DifferentiableAt ℝ
      (chartedEnergyAt T.a (fun z i => interpolatedFrame s T.a T.chainParams.ρA m (z, i) V) V) 0
  · rw [bondPartialDeriv_chartedEnergyAt_eq hd]
    exact hst.norm_le b.1 b.2 (toImaginaryCLM e) (by rw [norm_toImaginaryCLM, he])
  · unfold bondPartialDeriv
    rw [fderiv_zero_of_not_differentiableAt hd]
    simp
private theorem familyLawExponent_eq (s a ρA x : ℝ) (m : ℕ) (φ : LocalFamily) (V : F.GaugeField F.top) :
    familyLawExponent s a ρA x m φ V =
      exponentInChart a x (fun z i => interpolatedFrame s a ρA m (z, i) V) φ 1 V := by
  funext η
  unfold familyLawExponent interpolatedExponent exponentInChart
  rw [one_mul]
  rfl
private def zeroFamily : LocalFamily := fun _ _ _ => 0
private theorem zeroFamily_hasDecayingDerivs (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃) :
    HasDecayingDerivs L t n₀ σ δ E E₃ zeroFamily := by
  refine ⟨fun F _ y W _ k c X => contDiffAt_const, fun F _ y W k c X _ hk _ _ => ?_⟩
  have h0 : bondDeriv (zeroFamily F y) W c X = 0 := by
    unfold bondDeriv zeroFamily
    rw [iteratedFDeriv_const_of_ne (by omega)]
    rfl
  rw [h0, abs_zero]
  have hw : 0 ≤ torusDecayFactor L δ (bondSpan y c) := by
    unfold torusDecayFactor
    have : (0 : ℝ) < max 1 (((bondSpan y c : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) :=
      lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  split_ifs
  · exact div_nonneg hE₃ hw
  · exact div_nonneg hE hw
private theorem interpolatedExponent_eq (s a ρA x : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    interpolatedExponent s a ρA x m V =
      exponentInChart a x (fun z i => interpolatedFrame s a ρA m (z, i) V) zeroFamily 0 V := by
  funext η
  unfold interpolatedExponent exponentInChart
  rw [zero_mul, sub_zero]
  rfl
end Frames
section Laws
variable {F : BlockFrame} {T : StepParameters}
private theorem chordBondDist_isPseudoMetric (hs : ∀ i, 0 < F.extent i) :
    IsPseudoMetricOnBonds (chordBondDist F) := by
  refine ⟨fun b => ?_, fun b b' => ?_, fun b b' b'' => ?_⟩
  · simp [chordBondDist, cellSupDist]
  · unfold chordBondDist
    exact_mod_cast CellSums.cellSupDist_comm _ _
  · unfold chordBondDist
    exact_mod_cast CellSums.cellSupDist_triangle hs _ _ _
private theorem chordBondDist_nonneg (b b' : ChordBond F) : 0 ≤ chordBondDist F b b' := Nat.cast_nonneg _
private theorem extent_pos (hf : SlopeBounds T) {t : ℕ} (hF : IsCubicTopTorus T.L t T.n₀ F) (i : Fin 4) :
    0 < F.extent i := by
  obtain ⟨_, _, n, hside, hn⟩ := hF
  rw [hside i]
  have := hf.one_le_n₀
  omega
private theorem intermediateLaw_member (hT : T.IsOrdered) (hf : SlopeBounds T)
    (hA : ConvexAboveChartPointAt T) {t : ℕ} {x : ℝ} (hx : T.coupling ≤ x)
    (hN : InterpolatedFramesControlledAt T t x)
    (hS : ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
      InterpolatedSlopeSmall s T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct
        (frameGapBound T (frameRadius x)) x (frameRadius x) V)
    (hCl : ConvexClassClosure) {V : F.GaugeField F.top}
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    {Ψ : StepVariable (finiteCells F) → ℝ}
    (hl : IsIntermediateLaw T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
      (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V Ψ) :
    IsConvexClassMember T.ballRadius (x * T.chainParams.lam / 4) T.κ (chordBondDist F) Ψ ∧
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        ∀ (b : ChordBond F) (e : BondVector), |bondPartialDeriv Ψ b η e| ≤ T.Ct * x * ‖e‖ := by
  have hlam := hf.lam_pos
  have hx1 : 1 ≤ x := hf.one_le_coupling.trans hx
  have hx0 : 0 < x := by linarith
  have hσ0 : 0 < T.σ := hT.σ_pos
  have hρ0 : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hρ1 : T.ballRadius ≤ 1 / 64 := by
    show T.σ / 64 ≤ 1 / 64
    linarith [hf.σ_le_one]
  have hCt : 0 ≤ T.Ct := by linarith [hf.Ct_ge]
  have hD : T.Ct * T.ballRadius + T.chainParams.lam + 1 ≤ T.Ct := by nlinarith [hf.Ct_ge]
  have above : ∀ (s : ℝ) (f : LocalFamily) (ν : ℝ), 0 ≤ s → s ≤ 1 →
      HasDecayingDerivs T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → 0 ≤ ν → ν ≤ 1 →
      IsConvexClassMember T.ballRadius (x * T.chainParams.lam / 4) T.κ (chordBondDist F)
        (exponentInChart T.a x
          (fun z i => interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (z, i) V) f ν V) ∧
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        ∀ (b : ChordBond F) (e : BondVector),
        |bondPartialDeriv (exponentInChart T.a x
          (fun z i => interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (z, i) V)
          f ν V) b η e| ≤ T.Ct * x * ‖e‖ := by
    intro s f ν hs0 hs1 hfam hν0 hν1
    have hpt := interpolatedFrame_isChartBasePoint hf hF (hN.single F V s hF hV hs0 hs1).2
    have hsl := mul_abs_slope_le_one (hS F V s hF hV hs0 hs1)
    obtain ⟨h1, h2⟩ := hA t x f F V _ ν hx hfam hF hV hpt hsl hν0 hν1
    refine ⟨h1, fun η hη b e => (h2 η hη b e).trans ?_⟩
    have hne := norm_nonneg e
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD hx0.le) hne
  rcases hl with ⟨s, φ, hs0, hs1, hφ⟩ | ⟨s, τ, hs0, hs1, hτ0, hτ1⟩
  · rw [familyLawExponent_eq]
    exact above s φ 1 hs0 hs1 ⟨hφ.smooth, hφ.decay⟩ zero_le_one le_rfl
  · have hE : (0 : ℝ) ≤ T.E := by linarith [hT.one_le_E]
    have hE₃ : 0 ≤ T.energyRatio := div_nonneg hE hT.η₃_pos.le
    obtain ⟨hP, hPs⟩ := above s zeroFamily 0 hs0 hs1
      (zeroFamily_hasDecayingDerivs _ _ _ _ _ _ _ hE hE₃) le_rfl zero_le_one
    set P := exponentInChart T.a x
      (fun z i => interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (z, i) V)
      zeroFamily 0 V with hPdef
    have hm : 0 < x * T.chainParams.lam / 4 := by positivity
    have hcl := hCl (ChordBond F) T.ballRadius (x * T.chainParams.lam / 4) T.κ (chordBondDist F) hρ0 hm
      hT.κ_pos.le (chordBondDist_isPseudoMetric (extent_pos hf hF)) chordBondDist_nonneg
    have e : weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V =
        fun η => τ * P η + (1 - τ) * weightedSquares Finset.univ (2 * (x * T.chainParams.lam / 4)) η := by
      funext η
      unfold weightLawExponent
      rw [interpolatedExponent_eq]
      congr 2
      unfold totalQuadratic weightedSquares
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [e]
    refine ⟨hcl.2.1 P _ τ hτ0 hτ1 hP hcl.1, fun η hη b e => ?_⟩
    have hdP : DifferentiableAt ℝ P η := differentiableAt_of_member hP hη
    have hval : bondPartialDeriv
        (fun η => τ * P η + (1 - τ) * weightedSquares Finset.univ (2 * (x * T.chainParams.lam / 4)) η)
        b η e = τ * bondPartialDeriv P b η e +
          (1 - τ) * bondPartialDeriv (weightedSquares Finset.univ (2 * (x * T.chainParams.lam / 4))) b η e := by
      have h1 : HasFDerivAt
          (fun η => τ * P η + (1 - τ) * weightedSquares Finset.univ (2 * (x * T.chainParams.lam / 4)) η)
          (τ • fderiv ℝ P η + (1 - τ) •
            fderiv ℝ (weightedSquares Finset.univ (2 * (x * T.chainParams.lam / 4))) η) η :=
        (hdP.hasFDerivAt.const_mul τ).add
          ((weightedSquares_hasFDerivAt Finset.univ
            (2 * (x * T.chainParams.lam / 4)) η).differentiableAt.hasFDerivAt.const_mul (1 - τ))
      unfold bondPartialDeriv
      rw [h1.fderiv]
      simp
    have hne := norm_nonneg e
    have h1 := hPs η hη b e
    have h2 := abs_bondPartialDeriv_weightedSquares_le Finset.univ
      (by positivity : 0 ≤ 2 * (x * T.chainParams.lam / 4)) η b e
    have h3 : 2 * (2 * (x * T.chainParams.lam / 4)) * ‖η b‖ * ‖e‖ ≤ T.Ct * x * ‖e‖ := by
      have h4 : T.chainParams.lam * ‖η b‖ ≤ T.Ct := by
        have h5 := (hη b).le
        have h6 : ‖η b‖ ≤ 1 := by linarith
        nlinarith [hf.Ct_ge, norm_nonneg (η b)]
      have h7 : x * (T.chainParams.lam * ‖η b‖) ≤ x * T.Ct := mul_le_mul_of_nonneg_left h4 hx0.le
      calc _ = x * (T.chainParams.lam * ‖η b‖) * ‖e‖ := by ring
        _ ≤ x * T.Ct * ‖e‖ := mul_le_mul_of_nonneg_right h7 hne
        _ = _ := by ring
    rw [hval]
    have h8 : 0 ≤ 1 - τ := by linarith
    calc _ ≤ |τ * bondPartialDeriv P b η e| + |(1 - τ) * bondPartialDeriv (weightedSquares Finset.univ
            (2 * (x * T.chainParams.lam / 4))) b η e| := abs_add_le _ _
      _ = τ * |bondPartialDeriv P b η e| + (1 - τ) * |bondPartialDeriv (weightedSquares Finset.univ
            (2 * (x * T.chainParams.lam / 4))) b η e| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hτ0, abs_of_nonneg h8]
      _ ≤ τ * (T.Ct * x * ‖e‖) + (1 - τ) * (T.Ct * x * ‖e‖) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hτ0)
            (mul_le_mul_of_nonneg_left (h2.trans h3) h8)
      _ = _ := by ring
end Laws
theorem mixturesOfIntermediateLawsConvex_proof (hA : ConvexAboveChartPoint)
    (hN : interpolatedFramesControlled) (hS : interpolatedSlopeSmallOnTorus)
    (hI : ConvexRestriction.IsConvexClassMemberCompInjective) (hCl : ConvexClassClosure)
    (hJ : EventuallyInParametersCombines) :
    mixturesOfIntermediateLawsConvex := by
  refine hJ.2 _ _ ?_ (hJ.1 _ _ hA (hJ.1 _ _ hN (hJ.1 _ _ hS slopeBounds_eventually)))
  rintro T hT ⟨hAt, hNt, hSt, hf⟩ t x hx ι _ _ d n w M hw hM
  have hlam := hf.lam_pos
  have hx0 : 0 < x := by linarith [hf.one_le_coupling]
  have hρ0 : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    have := hT.σ_pos
    positivity
  have hm : 0 < x * T.chainParams.lam / 4 := by positivity
  have hκ : 0 ≤ T.κ := hT.κ_pos.le
  have hρ1 : T.ballRadius ≤ 1 := by
    show T.σ / 64 ≤ 1
    linarith [hf.σ_le_one, hT.σ_pos]
  have hn : n ≠ 0 := by
    rintro rfl
    have := hw.2
    simp at this
  have hnn : ∀ b b', 0 ≤ d b b' := by
    intro b b'
    have l₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    rw [(hM l₀).preservesCellDist b b']
    exact Nat.cast_nonneg _
  have hbd : IsPseudoMetricOnBonds d := by
    have l₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hs := extent_pos hf (hM l₀).isCubicTopTorus
    have hc := chordBondDist_isPseudoMetric hs
    have hk := (hM l₀).preservesCellDist
    refine ⟨fun b => ?_, fun b b' => ?_, fun b b' b'' => ?_⟩
    · rw [hk b b]
      exact hc.self _
    · rw [hk b b', hk b' b]
      exact hc.symm _ _
    · rw [hk b b'', hk b b', hk b' b'']
      exact hc.triangle _ _ _
  have hlaw := fun l => intermediateLaw_member hT hf hAt hx (hNt t x hx)
    (fun F V s h1 h2 h3 h4 => hSt t x hx F V s h1 h2 h3 h4) hCl (hM l).isCubicTopTorus
    (hM l).isSmallCurvature (hM l).isIntermediateLaw
  have hmem : ∀ l, IsConvexClassMember T.ballRadius (x * T.chainParams.lam / 4) T.κ d
      ((M l).exponent T.chainParams.lam x) :=
    fun l => frozenExponent_member (hM l).embed_injective (M l).active hρ0 hκ hm hI hCl hbd hnn
      (hM l).preservesCellDist chordBondDist_nonneg (hlaw l).1
  have hdiff : ∀ l (η : BondField ι), (∀ b, ‖η b‖ < T.ballRadius) →
      DifferentiableAt ℝ ((M l).exponent T.chainParams.lam x) η := fun l η hη =>
    differentiableAt_of_member (hmem l) hη
  have hslope : ∀ l (η : BondField ι), (∀ b, ‖η b‖ < T.ballRadius) → ∀ (b : ι) (e : BondVector),
      |bondPartialDeriv ((M l).exponent T.chainParams.lam x) b η e| ≤ T.Ct * x * ‖e‖ := by
    intro l η hη b e
    have hC : x * T.chainParams.lam * T.ballRadius ≤ T.Ct * x := by
      have h1 : T.chainParams.lam * T.ballRadius ≤ T.Ct := by nlinarith [hf.Ct_ge]
      nlinarith
    exact abs_bondPartialDeriv_frozenExponent_le (hM l).embed_injective (M l).active hρ0
      (by positivity) hC (fun η' hη' => differentiableAt_of_member (hlaw l).1 hη') (hlaw l).2 hη b e
  have hmix : IsConvexClassMember T.ballRadius (x * T.chainParams.lam / 4) T.κ d
      (convexCombinationExponent T.chainParams.lam x w M) := by
    have h1 := member_finset_mixture
      (hCl ι T.ballRadius (x * T.chainParams.lam / 4) T.κ d hρ0 hm hκ hbd hnn).2.1 w
      (fun l => (M l).exponent T.chainParams.lam x) Finset.univ (fun l _ => hw.1 l)
      (fun l _ => hmem l) (by rw [hw.2]; exact one_pos)
    have e : (fun η => (∑ l, w l * (M l).exponent T.chainParams.lam x η) / ∑ l, w l) =
        convexCombinationExponent T.chainParams.lam x w M := by
      funext η
      rw [hw.2, div_one]
      rfl
    rw [← e]
    exact h1
  obtain ⟨Ψ, K, hag, hc, h0⟩ := hmix
  refine ⟨Ψ, K, hag, hc, h0, fun η hη b e => ?_⟩
  have hev : Ψ =ᶠ[𝓝 η] convexCombinationExponent T.chainParams.lam x w M :=
    (eventually_norm_lt hη).mono fun ζ hζ => hag ζ hζ
  have hder : HasFDerivAt (convexCombinationExponent T.chainParams.lam x w M)
      (∑ l, w l • fderiv ℝ ((M l).exponent T.chainParams.lam x) η) η :=
    HasFDerivAt.fun_sum fun l _ => (hdiff l η hη).hasFDerivAt.const_mul (w l)
  have hval : bondPartialDeriv Ψ b η e =
      ∑ l, w l * bondPartialDeriv ((M l).exponent T.chainParams.lam x) b η e := by
    unfold bondPartialDeriv
    rw [hev.fderiv_eq, hder.fderiv, ContinuousLinearMap.sum_apply]
    simp
  rw [hval]
  calc _ ≤ ∑ l, |w l * bondPartialDeriv ((M l).exponent T.chainParams.lam x) b η e| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, w l * (T.Ct * x * ‖e‖) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul, abs_of_nonneg (hw.1 l)]
        exact mul_le_mul_of_nonneg_left (hslope l η hη b e) (hw.1 l)
    _ = _ := by rw [← Finset.sum_mul, hw.2, one_mul]
end YangMills.Construction.Interpolation
end
