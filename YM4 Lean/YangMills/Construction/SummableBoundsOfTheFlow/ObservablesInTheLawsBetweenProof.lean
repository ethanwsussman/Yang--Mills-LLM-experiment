import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenBoundsProof
import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.ColdStepAtMirrorFrames.DistancesOfSitesAndCells
import YangMills.Construction.SummableBoundsOfTheFlow.BoundAlongMovesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentIsSmoothAbove
import YangMills.Construction.SummableBoundsOfTheFlow.LawsBetweenAreConvex
import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsFieldProof
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetween
import YangMills.Construction.SummableBoundsOfTheFlow.ReadAboveFromMoves
import YangMills.Construction.SummableBoundsOfTheFlow.SizeFromSquareBounds
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.IteratedDerivative YangMills.Construction.Estimates YangMills.Construction.FamilyNorms YangMills.Construction.CellCounting
namespace YangMills.Construction.Interpolation
namespace ObservableSizes
section Extension
variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : BlockFrame}
  (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι)
theorem extendByZero_apply_embed (hj : Function.Injective j) (ζ : BondField ι) {i : ι} (hi : i ∈ Λ) :
    extendByZero j Λ ζ (j i) = ζ i := by
  unfold extendByZero
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hne
    rw [if_neg (fun h => hne (hj h))]
  · intro h
    exact absurd hi h
theorem extendByZero_apply_of_forall_ne (ζ : BondField ι) {b : ↥(chordBonds (finiteCells F))}
    (hb : ∀ i ∈ Λ, j i ≠ b) : extendByZero j Λ ζ b = 0 := by
  unfold extendByZero
  exact Finset.sum_eq_zero fun i hi => if_neg (hb i hi)
theorem norm_extendByZero_lt (hj : Function.Injective j) {ρ : ℝ} (hρ : 0 < ρ) (ζ : BondField ι)
    (h : ∀ i, ‖ζ i‖ < ρ) (b : ↥(chordBonds (finiteCells F))) : ‖extendByZero j Λ ζ b‖ < ρ := by
  by_cases hb : ∃ i ∈ Λ, j i = b
  · obtain ⟨i, hi, rfl⟩ := hb
    rw [extendByZero_apply_embed j Λ hj ζ hi]
    exact h i
  · push_neg at hb
    rw [extendByZero_apply_of_forall_ne j Λ ζ hb]
    simpa using hρ
def extendByZeroCLM : BondField ι →L[ℝ] StepVariable (finiteCells F) :=
  ContinuousLinearMap.pi fun b => ∑ i ∈ Λ, if j i = b then
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) i else 0
theorem extendByZeroCLM_apply (ζ : BondField ι) : extendByZeroCLM j Λ ζ = extendByZero j Λ ζ := by
  funext b
  simp only [extendByZeroCLM, extendByZero, ContinuousLinearMap.coe_pi', ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp
theorem extendByZero_single (hj : Function.Injective j) (i : ι) (e : BondVector) :
    extendByZero j Λ (Pi.single i e) = if i ∈ Λ then Pi.single (j i) e else 0 := by
  funext b
  unfold extendByZero
  split_ifs with hi
  · by_cases hb : j i = b
    · subst hb
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' _ hne
        rw [if_neg (fun h => hne (hj h))]
      · intro h
        exact absurd hi h
    · rw [Pi.single_eq_of_ne (Ne.symm hb)]
      refine Finset.sum_eq_zero fun i' _ => ?_
      split_ifs with h
      · have : i' ≠ i := fun e' => hb (e' ▸ h)
        exact Pi.single_eq_of_ne this _
      · rfl
  · refine Finset.sum_eq_zero fun i' hi' => ?_
    split_ifs with h
    · have : i' ≠ i := fun e' => hi (e' ▸ hi')
      exact Pi.single_eq_of_ne this _
    · rfl
theorem localSqNorm_extendByZero_le (hj : Function.Injective j) (κ : ℝ) (Y : F.Cell) (ζ : BondField ι) :
    localSqNorm κ Y (extendByZero j Λ ζ) ≤
      ∑ i, Real.exp (-(2 ^ 6 * κ * embeddedCellDist j Y i)) * ‖ζ i‖ ^ 2 := by
  classical
  unfold localSqNorm
  have h1 : ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) * ‖extendByZero j Λ ζ b‖ ^ 2 =
      ∑ b ∈ Λ.image j, Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) *
        ‖extendByZero j Λ ζ b‖ ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_
    have : ∀ i ∈ Λ, j i ≠ b := fun i hi h => hb (Finset.mem_image.2 ⟨i, hi, h⟩)
    rw [extendByZero_apply_of_forall_ne j Λ ζ this]
    simp
  rw [h1, Finset.sum_image fun a _ a' _ h => hj h]
  have h2 : ∑ i ∈ Λ, Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell (j i).1.1) Y : ℝ))) *
      ‖extendByZero j Λ ζ (j i)‖ ^ 2 =
      ∑ i ∈ Λ, Real.exp (-(2 ^ 6 * κ * embeddedCellDist j Y i)) * ‖ζ i‖ ^ 2 :=
    Finset.sum_congr rfl fun i hi => by rw [extendByZero_apply_embed j Λ hj ζ hi]; rfl
  rw [h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
theorem abs_le_mul_norm_of_homogeneous {g : BondVector → ℝ} {B : ℝ}
    (hg : ∀ (c : ℝ) (e : BondVector), g (c • e) = c * g e)
    (h : ∀ e, ‖e‖ = 1 → |g e| ≤ B) (e : BondVector) : |g e| ≤ B * ‖e‖ := by
  by_cases he : e = 0
  · subst he
    have := hg 0 0
    simp at this
    simp [this]
  · have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
    have hu : ‖‖e‖⁻¹ • e‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have e1 : e = ‖e‖ • (‖e‖⁻¹ • e) := by
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    have h1 := h _ hu
    have e2 : g e = ‖e‖ * g (‖e‖⁻¹ • e) := by
      conv_lhs => rw [e1]
      exact hg _ _
    rw [e2, abs_mul, abs_of_nonneg (norm_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
theorem bondGradNorm_comp_extendByZero_le (hj : Function.Injective j) (T : StepVariable (finiteCells F) → ℝ)
    (ζ : BondField ι) (i : ι) {g : ℝ} (hg0 : 0 ≤ g) (hd : DifferentiableAt ℝ T (extendByZero j Λ ζ))
    (hb : ∀ e : BondVector, ‖e‖ = 1 → |fderiv ℝ T (extendByZero j Λ ζ) (bondVariation (j i) e)| ≤ g) :
    bondGradNorm (fun ζ' => T (extendByZero j Λ ζ')) i ζ ≤ g := by
  have hd' : HasFDerivAt T (fderiv ℝ T (extendByZero j Λ ζ)) (extendByZeroCLM j Λ ζ) := by
    rw [extendByZeroCLM_apply]
    exact hd.hasFDerivAt
  have h1 : (fun ζ' => T (extendByZero j Λ ζ')) = T ∘ extendByZeroCLM j Λ := by
    funext ζ'
    simp [extendByZeroCLM_apply]
  have h2 := (hd'.comp ζ (extendByZeroCLM j Λ).hasFDerivAt).fderiv
  unfold bondGradNorm
  rw [h1, h2]
  refine ContinuousLinearMap.opNorm_le_bound _ hg0 fun e => ?_
  simp only [ContinuousLinearMap.comp_apply]
  have e0 : (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) i) e = Pi.single i e := rfl
  have e1 : extendByZeroCLM j Λ (Pi.single i e) = if i ∈ Λ then Pi.single (j i) e else 0 := by
    rw [extendByZeroCLM_apply, extendByZero_single j Λ hj]
  rw [e0, e1, Real.norm_eq_abs]
  split_ifs with hi
  · exact abs_le_mul_norm_of_homogeneous (g := fun e => fderiv ℝ T (extendByZero j Λ ζ) (bondVariation (j i) e))
      (fun c e => by simp [bondVariation, Pi.single_smul]) hb e
  · simp
    positivity
structure SizeSetting (ρ x lam κ W C : ℝ) (d : ι → ι → ℝ) (Φ : BondField ι → ℝ) (p : ℝ → ℝ) : Prop where
  radius_pos : 0 < ρ
  one_le_x : 1 ≤ x
  lam_pos : 0 < lam
  rate_pos : 0 < κ
  total_nonneg : 0 ≤ W
  cutoff : IsCutoff ρ p
  pseudoMetric : IsPseudoMetricOnBonds d
  convexLaw : HasUniformlyConvexLaw ρ lam x κ C d Φ
  injective : Function.Injective j
  preserves : PreservesCellDist j d
  cellSums : ∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
    Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ W
variable {ρ x lam κ W C : ℝ} {d : ι → ι → ℝ} {Φ : BondField ι → ℝ} {p : ℝ → ℝ}
theorem sum_exp_embed_le (S : SizeSetting j ρ x lam κ W C d Φ p) (z : F.Cell) :
    ∑ i, Real.exp (-(2 * κ * (cellSupDist (enclosingCell (j i).1.1) z : ℝ))) ≤ W := by
  classical
  have h1 : ∑ i, Real.exp (-(2 * κ * (cellSupDist (enclosingCell (j i).1.1) z : ℝ))) =
      ∑ b ∈ Finset.univ.image j, Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) := by
    rw [Finset.sum_image fun a _ a' _ h => S.injective h]
  rw [h1]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ => (Real.exp_pos _).le).trans (S.cellSums z)
theorem hasLocalSize_comp_extendByZero (hSz : localSizeOfQuadraticBoundsStatement)
    (S : SizeSetting j ρ x lam κ W C d Φ p)
    (T : StepVariable (finiteCells F) → ℝ) (H₀ h A : ℝ) (Y : F.Cell) (hh : 0 ≤ h) (hA : 0 < A)
    (hC : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) T η)
    (hv : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      |T η - H₀| ≤ A * h * (x * localSqNorm κ Y η + 1))
    (hg : ∀ (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
      (∀ b, ‖η b‖ < ρ) → ‖e‖ = 1 → |fderiv ℝ T η (bondVariation b e)| ≤
        Real.sqrt x * (A * h) * Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) *
          (x * localSqNorm κ Y η + 1)) :
    HasLocalSize ρ (cutoffFactor ρ p) Φ (fun q => A * lpMomentConstant lam W W q) x κ h (embeddedCellDist j Y)
      (fun ζ => T (extendByZero j Λ ζ)) := by
  have hx0 : 0 ≤ x := by linarith [S.one_le_x]
  have hAh : 0 ≤ A * h := by positivity
  set w : ι → ℝ := fun i => Real.exp (-(2 ^ 6 * κ * embeddedCellDist j Y i)) with hw
  have hκ := S.rate_pos
  have hws : ∑ i, w i ≤ W := by
    refine (Finset.sum_le_sum fun i _ => ?_).trans (sum_exp_embed_le j S Y)
    refine Real.exp_le_exp.2 ?_
    have e : embeddedCellDist j Y i = (cellSupDist (enclosingCell (j i).1.1) Y : ℝ) := rfl
    rw [e]
    nlinarith
  have hsq : ∀ ζ : BondField ι, x * localSqNorm κ Y (extendByZero j Λ ζ) + 1 ≤
      x * ∑ b, w b * ‖ζ b‖ ^ 2 + 1 := fun ζ => by
    have := mul_le_mul_of_nonneg_left (localSqNorm_extendByZero_le j Λ S.injective κ Y ζ) hx0
    linarith
  have hdist : IsPseudoMetricOnBonds d := S.pseudoMetric
  have hWs : ∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W := fun b₀ => by
    have := sum_exp_embed_le j S (enclosingCell (j b₀).1.1)
    simpa only [S.preserves _ _] using this
  have hs := hSz ι ρ x lam κ W W C (A * h) H₀ d Φ p (embeddedCellDist j Y) w
    (fun ζ => T (extendByZero j Λ ζ)) S.radius_pos S.one_le_x S.lam_pos hκ.le S.total_nonneg S.total_nonneg hAh
    S.cutoff hdist S.convexLaw hWs (fun _ => (Real.exp_pos _).le) hws ?_ ?_ ?_
  · refine ⟨hs.1, ?_⟩
    obtain ⟨H₁, hq⟩ := hs.2
    refine ⟨H₁, fun q hq1 => ?_⟩
    obtain ⟨h1, h2⟩ := hq q hq1
    refine ⟨?_, fun b => ?_⟩
    · have e : (A * lpMomentConstant lam W W q) * h = lpMomentConstant lam W W q * (A * h) := by ring
      simp only [e]
      exact h1
    · have e : (A * lpMomentConstant lam W W q) * Real.sqrt x * h *
            Real.exp (-(2 * κ * embeddedCellDist j Y b)) =
          lpMomentConstant lam W W q * Real.sqrt x * (A * h) *
            Real.exp (-(2 * κ * embeddedCellDist j Y b)) := by ring
      simp only [e]
      exact h2 b
  · intro ζ hζ
    have h1 := hC _ (norm_extendByZero_lt j Λ S.injective S.radius_pos ζ hζ)
    have h2 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) T (extendByZeroCLM j Λ ζ) := by
      rw [extendByZeroCLM_apply]
      exact h1
    have h3 := ContDiffAt.comp ζ h2 (extendByZeroCLM j Λ).contDiff.contDiffAt
    have e : (T ∘ extendByZeroCLM j Λ) = fun ζ' => T (extendByZero j Λ ζ') := by
      funext ζ'
      simp [extendByZeroCLM_apply]
    rwa [e] at h3
  · intro ζ hζ
    refine (hv _ (norm_extendByZero_lt j Λ S.injective S.radius_pos ζ hζ)).trans ?_
    exact mul_le_mul_of_nonneg_left (hsq ζ) hAh
  · intro ζ i hζ
    have hb := norm_extendByZero_lt j Λ S.injective S.radius_pos ζ hζ
    have hG : 0 ≤ Real.sqrt x * (A * h) * Real.exp (-(2 * κ * embeddedCellDist j Y i)) *
        (x * ∑ b, w b * ‖ζ b‖ ^ 2 + 1) := by
      have : 0 ≤ ∑ b, w b * ‖ζ b‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
      positivity
    refine bondGradNorm_comp_extendByZero_le j Λ S.injective T ζ i hG
      ((hC _ hb).differentiableAt (by simp)) fun e he => ?_
    refine (hg _ _ e hb he).trans ?_
    have hnn : 0 ≤ Real.sqrt x * (A * h) * Real.exp (-(2 * κ * embeddedCellDist j Y i)) := by positivity
    exact mul_le_mul_of_nonneg_left (hsq ζ) hnn
end Extension
section Parameters
variable {F : BlockFrame} {k : ℕ}
abbrev JointSpace (F : BlockFrame) (k : ℕ) : Type := StepVariable (finiteCells F) × (Fin k → ℝ)
abbrev parameterList (F : BlockFrame) (k : ℕ) : List (JointSpace F k) :=
  parameterDirections _ _ (parameterBasis k)
theorem parameterList_length : (parameterList F k).length = k := by
  simp [parameterDirections, parameterBasis]
theorem iteratedFDeriv_parameters_eq (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ)
    (ζ : StepVariable (finiteCells F)) (hf : ContDiffAt ℝ (k : WithTop ℕ∞) f (ζ, 0)) :
    iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => f (ζ, τ)) 0 (fun l => Pi.single l 1) =
      derivAlong f (parameterList F k) (ζ, 0) := by
  have hc : ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ : Fin k → ℝ => f (ζ, τ)) 0 :=
    ContDiffAt.comp (g := f) (f := fun τ : Fin k → ℝ => (ζ, τ)) (0 : Fin k → ℝ) hf
      (contDiff_const.prodMk contDiff_id).contDiffAt
  rw [(h.1 _ ℝ).iteratedFDeriv_eq _ _ _ _ hc]
  have e := h.2 (JointSpace F k) (Fin k → ℝ) ℝ f (ContinuousLinearMap.inr ℝ _ _) (ζ, 0) 0
    (List.ofFn fun l : Fin k => Pi.single l 1) (by simpa using hf)
  have e1 : (fun t' : Fin k → ℝ =>
      f ((ζ, 0) + ContinuousLinearMap.inr ℝ (StepVariable (finiteCells F)) (Fin k → ℝ) t')) =
      fun τ => f (ζ, τ) := by
    funext t'
    simp
  rw [e1] at e
  rw [e]
  simp only [map_zero, add_zero]
  rfl
theorem iteratedFDeriv_parameters_fderiv_eq (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ)
    (ζ w : StepVariable (finiteCells F)) (hf : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f (ζ, 0)) :
    iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => fderiv ℝ (fun ζ' => f (ζ', τ)) ζ w) 0
      (fun l => Pi.single l 1) =
      derivAlong f (parameterList F k ++ [(w, 0)]) (ζ, 0) := by
  have hev := hf.eventually (by simp)
  have hc : Filter.Tendsto (fun τ : Fin k → ℝ => (ζ, τ)) (𝓝 0) (𝓝 (ζ, 0)) :=
    (by fun_prop : Continuous fun τ : Fin k → ℝ => (ζ, τ)).tendsto 0
  have e1 : (fun τ : Fin k → ℝ => fderiv ℝ (fun ζ' => f (ζ', τ)) ζ w) =ᶠ[𝓝 0]
      fun τ => derivAlong f [(w, 0)] (ζ, τ) := by
    filter_upwards [hc.eventually hev] with τ hτ
    have hd : DifferentiableAt ℝ f (ζ, τ) := hτ.differentiableAt (by simp)
    have := (HasFDerivAt.comp (g := f) (f := fun ζ' => (ζ', τ)) ζ hd.hasFDerivAt
      (hasFDerivAt_prodMk_left ζ τ)).fderiv
    change fderiv ℝ (f ∘ fun ζ' => (ζ', τ)) ζ w = _
    rw [this]
    simp [derivAlong]
  have hH : ContDiffAt ℝ (k : WithTop ℕ∞) (derivAlong f [((w, 0) : JointSpace F k)]) (ζ, 0) :=
    (h.1 _ ℝ).contDiffAt _ _ k _ (by simpa using hf)
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ e1 k).self_of_nhds, iteratedFDeriv_parameters_eq h _ ζ hH,
    (h.1 _ ℝ).append]
theorem contDiffAt_iteratedFDeriv_parameters (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ)
    (ζ₀ : StepVariable (finiteCells F))
    (hf : ∀ᶠ ζ in 𝓝 ζ₀, ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f (ζ, 0)) :
    ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun ζ => iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => f (ζ, τ)) 0 (fun l => Pi.single l 1)) ζ₀ ∧
    ∀ v : StepVariable (finiteCells F),
      fderiv ℝ (fun ζ => iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => f (ζ, τ)) 0
        (fun l => Pi.single l 1)) ζ₀ v =
        derivAlong f ((v, 0) :: parameterList F k) (ζ₀, 0) := by
  have R := h.1 (JointSpace F k) ℝ
  have e : (fun ζ => iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => f (ζ, τ)) 0 (fun l => Pi.single l 1)) =ᶠ[𝓝 ζ₀]
      fun ζ => derivAlong f (parameterList F k) (ζ, 0) := by
    filter_upwards [hf] with ζ hζ
    exact iteratedFDeriv_parameters_eq h f ζ (hζ.of_le (by exact_mod_cast Nat.le_succ k))
  have h0 := hf.self_of_nhds
  have hA : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (derivAlong f (parameterList F k)) (ζ₀, 0) :=
    R.contDiffAt _ _ 1 _ (by rw [parameterList_length, add_comm]; exact h0)
  have hin : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun ζ : StepVariable (finiteCells F) => ((ζ, 0) : JointSpace F k)) ζ₀ :=
    (contDiff_id.prodMk contDiff_const).contDiffAt
  have hc : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun ζ => derivAlong f (parameterList F k) (ζ, 0)) ζ₀ :=
    ContDiffAt.comp (g := derivAlong f (parameterList F k)) (f := fun ζ => ((ζ, 0) : JointSpace F k)) ζ₀ hA hin
  refine ⟨hc.congr_of_eventuallyEq e, fun v => ?_⟩
  rw [e.fderiv_eq]
  have hd : DifferentiableAt ℝ (derivAlong f (parameterList F k)) (ζ₀, 0) := hA.differentiableAt (by simp)
  have := (HasFDerivAt.comp (g := derivAlong f (parameterList F k)) (f := fun ζ => ((ζ, 0) : JointSpace F k))
    ζ₀ hd.hasFDerivAt (hasFDerivAt_prodMk_left ζ₀ 0)).fderiv
  change fderiv ℝ (derivAlong f (parameterList F k) ∘ fun ζ => ((ζ, 0) : JointSpace F k)) ζ₀ v = _
  rw [this]
  simp [derivAlong]
theorem isOpen_bondBall (ρ : ℝ) : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < ρ} := by
  have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < ρ} = ⋂ b, {η | ‖η b‖ < ρ} := by
    ext η
    simp
  rw [this]
  exact isOpen_iInter_of_finite fun b => isOpen_lt (by fun_prop) continuous_const
theorem mul_sqrt_add_one_le {x u : ℝ} (hx : 1 ≤ x) (hu : 0 ≤ u) :
    x * Real.sqrt u + 1 ≤ 2 * Real.sqrt x * (x * u + 1) := by
  set r := Real.sqrt x with hr
  have hr1 : 1 ≤ r := by
    rw [hr, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx
  have hr2 : r * r = x := Real.mul_self_sqrt (by linarith)
  set t := r * Real.sqrt u with ht
  have ht2 : t * t = x * u := by
    have : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu
    calc t * t = (r * r) * (Real.sqrt u * Real.sqrt u) := by rw [ht]; ring
      _ = x * u := by rw [hr2, this]
  have e1 : x * Real.sqrt u = r * t := by
    rw [ht, ← hr2]
    ring
  rw [e1, ← ht2]
  nlinarith [sq_nonneg (t - 1), mul_nonneg (by linarith : (0 : ℝ) ≤ r) (sq_nonneg (t - 1)), mul_self_nonneg t]
end Parameters
section Bounds
variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : BlockFrame}
  {j : ι → ↥(chordBonds (finiteCells F))} {Λ : Finset ι}
  {ρ x lam κ W C : ℝ} {d : ι → ι → ℝ} {Φ : BondField ι → ℝ} {p : ℝ → ℝ}
  {s a ρA : ℝ} {m : ℕ} {V : F.GaugeField F.top}
theorem bondSpan_le_bondSpanWithCell (hD : SupDistCellComparison) {k : ℕ} (Y z : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) :
    bondSpan Y c ≤ bondSpanWithCell Y z c ∧ cellSupDist z Y ≤ bondSpanWithCell Y z c := by
  have e : ∀ y w : F.Cell, siteSupDist y w = cellSupDist y w := fun _ _ => rfl
  unfold bondSpanWithCell
  set c' : Fin (k + 1) → F.Site F.top × Fin 4 := Fin.cons (z, 0) c with hc'
  have hone : ∀ l, cellSupDist Y (c' l).1 ≤ bondSpan Y c' := fun l =>
    (Finset.le_sup (f := fun l => cellSupDist Y (c' l).1) (Finset.mem_univ l)).trans (le_max_left _ _)
  have htwo : ∀ l l', cellSupDist (c' l).1 (c' l').1 ≤ bondSpan Y c' := fun l l' =>
    ((Finset.le_sup (f := fun l' => cellSupDist (c' l).1 (c' l').1) (Finset.mem_univ l')).trans
      (Finset.le_sup (f := fun l => Finset.univ.sup fun l' => cellSupDist (c' l).1 (c' l').1)
        (Finset.mem_univ l))).trans (le_max_right _ _)
  refine ⟨?_, ?_⟩
  · have g1 : ∀ l, siteSupDist Y (c l).1 ≤ bondSpan Y c' := fun l => by
      have := hone l.succ
      simp only [hc', Fin.cons_succ] at this
      exact this
    have g2 : ∀ l l', siteSupDist (c l).1 (c l').1 ≤ bondSpan Y c' := fun l l' => by
      have := htwo l.succ l'.succ
      simp only [hc', Fin.cons_succ] at this
      exact this
    have e2 : bondSpan Y c = max (Finset.univ.sup fun l => siteSupDist Y (c l).1)
        (Finset.univ.sup fun l => Finset.univ.sup fun l' => siteSupDist (c l).1 (c l').1) := rfl
    rw [e2]
    exact max_le (Finset.sup_le fun l _ => g1 l)
      (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => g2 l l')
  · have h1 := (hD.1 F F.top z Y Y).2.1
    rw [e, e] at h1
    rw [h1]
    simpa [hc'] using hone 0
theorem cellSupDist_self_eq_zero (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem exp_le_exp_mul_exp {κ n D w : ℝ} (hκ : 0 < κ) (hn : n ≤ w) (hD : D ≤ w) (h0 : 0 ≤ n) (h1 : 0 ≤ D) :
    Real.exp (-(2 ^ 6 * κ * w)) ≤ Real.exp (-(2 ^ 5 * κ * n)) * Real.exp (-(2 * κ * D)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have a1 : 2 ^ 5 * κ * n ≤ 2 ^ 5 * κ * w := mul_le_mul_of_nonneg_left hn (by positivity)
  have a2 : 2 * κ * D ≤ 2 * κ * w := mul_le_mul_of_nonneg_left hD (by positivity)
  have a3 : 0 ≤ κ * w := mul_nonneg hκ.le (h0.trans hn)
  nlinarith
theorem hasLocalSize_exponentDeriv (hL : DerivAlongRulesHold) (hSz : localSizeOfQuadraticBoundsStatement)
    (hD : SupDistCellComparison) (S : SizeSetting j ρ x lam κ W C d Φ p) {Cb : ℝ} (hC0 : 0 ≤ Cb)
    (hB : InterpolatedExponentBounds s a ρA ρ x κ Cb m V)
    (hSm : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions),
      (∀ b, ‖η b‖ < ρ) → AreUnitVectors X → ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞)
        (rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X) (η, 0))
    (Y : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    (hX : AreUnitVectors X) :
    HasLocalSize ρ (cutoffFactor ρ p) Φ (fun q => 4 * lpMomentConstant lam W W q) x κ
      (Cb * Real.exp (-(2 ^ 5 * κ * bondSpan Y c))) (embeddedCellDist j Y)
      (fun ζ => bondDeriv (fun V' => interpolatedBlockExponent s a ρA x m Y V' (extendByZero j Λ ζ)) V c X) := by
  have hκ := S.rate_pos
  have hx1 := S.one_le_x
  have R := hL.1 (JointSpace F k) ℝ
  set f := rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X with hf
  set T : StepVariable (finiteCells F) → ℝ :=
    fun η => bondDeriv (fun V' => interpolatedBlockExponent s a ρA x m Y V' η) V c X with hT
  have hev : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      ∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f (ζ, 0) := by
    intro η hη
    filter_upwards [(isOpen_bondBall ρ).mem_nhds hη] with ζ hζ
    exact (hSm Y ζ k c X hζ hX).of_le (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  have hmv := fun η hη => contDiffAt_iteratedFDeriv_parameters hL f η (hev η hη)
  have hE : 0 ≤ Cb * Real.exp (-(2 ^ 5 * κ * (bondSpan Y c : ℝ))) := mul_nonneg hC0 (Real.exp_pos _).le
  refine hasLocalSize_comp_extendByZero j Λ hSz S T 0 _ 4 Y hE (by norm_num) (fun η hη => (hmv η hη).1) ?_ ?_
  · intro η hη
    rw [sub_zero]
    have h1 := hB.deriv_top Y η k c X hη hk hX
    refine h1.trans ?_
    have hsq : 0 ≤ localSqNorm κ Y η :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    have hn : 0 ≤ x * localSqNorm κ Y η + 1 := by positivity
    have h2 : Real.exp (-(2 ^ 6 * κ * (bondSpan Y c : ℝ))) ≤ Real.exp (-(2 ^ 5 * κ * (bondSpan Y c : ℝ))) := by
      refine Real.exp_le_exp.2 ?_
      have : (0 : ℝ) ≤ bondSpan Y c := Nat.cast_nonneg _
      nlinarith [mul_nonneg hκ.le this]
    calc _ ≤ Cb * (x * localSqNorm κ Y η + 1) * Real.exp (-(2 ^ 5 * κ * (bondSpan Y c : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 4 * (Cb * Real.exp (-(2 ^ 5 * κ * (bondSpan Y c : ℝ)))) * (x * localSqNorm κ Y η + 1) := by
          nlinarith [mul_nonneg hE hn]
  · intro η b e hη he
    have e1 : fderiv ℝ T η (bondVariation b e) =
        bondDeriv (fun V' => bondPartialDeriv (interpolatedBlockExponent s a ρA x m Y V') b η e) V c X := by
      have h1 := (hmv η hη).2 (bondVariation b e)
      have hlen : ContDiffAt ℝ ((((bondVariation b e, 0) :: parameterList F k :
          List (JointSpace F k)).length : ℕ) : WithTop ℕ∞) f (η, 0) := by
        have h2 := (hev η hη).self_of_nhds
        rw [show ((bondVariation b e, 0) :: parameterList F k : List (JointSpace F k)).length = k + 1 by
          simp [parameterList_length]]
        exact h2
      have h3 := iteratedFDeriv_parameters_fderiv_eq hL f η (bondVariation b e) (hev η hη).self_of_nhds
      have h4 : derivAlong f ((bondVariation b e, 0) :: parameterList F k) (η, 0) =
          derivAlong f (parameterList F k ++ [(bondVariation b e, 0)]) (η, 0) :=
        R.perm _ _ _ _ (List.perm_append_singleton _ _).symm hlen
      exact h1.trans (h4.trans h3.symm)
    rw [e1]
    have h1 := hB.deriv_top_partial Y η b e k c X hη hk hX he
    refine h1.trans ?_
    obtain ⟨w1, w2⟩ := bondSpan_le_bondSpanWithCell hD Y (enclosingCell b.1.1) c
    have h2 := exp_le_exp_mul_exp (n := (bondSpan Y c : ℝ)) (D := (cellSupDist (enclosingCell b.1.1) Y : ℝ))
      (w := (bondSpanWithCell Y (enclosingCell b.1.1) c : ℝ)) hκ (by exact_mod_cast w1) (by exact_mod_cast w2)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hsq : 0 ≤ localSqNorm κ Y η :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    have h3 := mul_sqrt_add_one_le hx1 hsq
    have hn : 0 ≤ x * Real.sqrt (localSqNorm κ Y η) + 1 := by positivity
    set A := Real.exp (-(2 ^ 5 * κ * (bondSpan Y c : ℝ)))
    set B := Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))
    calc _ ≤ Cb * (x * Real.sqrt (localSqNorm κ Y η) + 1) * (A * B) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ Cb * (2 * Real.sqrt x * (x * localSqNorm κ Y η + 1)) * (A * B) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hC0) (by positivity)
      _ ≤ Real.sqrt x * (4 * (Cb * A)) * B * (x * localSqNorm κ Y η + 1) := by
          have : 0 ≤ Cb * Real.sqrt x * (x * localSqNorm κ Y η + 1) * (A * B) := by positivity
          nlinarith
theorem leftTranslate_bondSpread_zero {i : ℕ} {W : F.GaugeField i} {k : ℕ} (c : Fin k → F.Site i × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread c X 0) W = W := by apply _root_.YangMills.Construction.Interpolation.TopVariation.leftTranslate_bondSpread_zero <;> assumption
theorem localSqNorm_nonneg (κ : ℝ) (Y : F.Cell) (η : StepVariable (finiteCells F)) : 0 ≤ localSqNorm κ Y η :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
theorem sq_norm_le_localSqNorm {κ : ℝ} {Y : F.Cell} (η : StepVariable (finiteCells F))
    (b : ↥(chordBonds (finiteCells F))) (hb : enclosingCell b.1.1 = Y) : ‖η b‖ ^ 2 ≤ localSqNorm κ Y η := by
  have h1 := Finset.single_le_sum (f := fun b : ↥(chordBonds (finiteCells F)) =>
    Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) * ‖η b‖ ^ 2)
    (fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) (Finset.mem_univ b)
  calc ‖η b‖ ^ 2 = Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) * ‖η b‖ ^ 2 := by
        rw [hb, cellSupDist_self_eq_zero]
        simp
    _ ≤ localSqNorm κ Y η := h1
theorem abs_cellQuadratic_le (lam x κ : ℝ) (hx : 0 ≤ x) (hlam : 0 ≤ lam) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) :
    |cellQuadratic lam x Y η| ≤ lam / 2 * (x * localSqNorm κ Y η) := by
  have h1 : ∀ b : ↥(chordBonds (finiteCells F)),
      (if enclosingCell b.1.1 = Y then x * lam / 2 * ‖η b‖ ^ 2 else 0) ≤
      lam / 2 * x * (Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) * ‖η b‖ ^ 2) := by
    intro b
    split_ifs with hb
    · simp only [hb, cellSupDist_self_eq_zero]
      simp
      nlinarith [sq_nonneg ‖η b‖]
    · have : 0 ≤ Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) * ‖η b‖ ^ 2 :=
        mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
      positivity
  have h0 : 0 ≤ cellQuadratic lam x Y η := Finset.sum_nonneg fun b _ => by
    split_ifs
    · positivity
    · exact le_rfl
  rw [abs_of_nonneg h0]
  have h2 := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => h1 b
  rw [← Finset.mul_sum] at h2
  calc cellQuadratic lam x Y η ≤ _ := h2
    _ = _ := by unfold localSqNorm; ring
theorem cellQuadratic_deriv (lam x : ℝ) (Y : F.Cell) (η : StepVariable (finiteCells F)) :
    DifferentiableAt ℝ (cellQuadratic lam x Y) η ∧
    ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (cellQuadratic lam x Y) η ∧
    ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
      |fderiv ℝ (cellQuadratic lam x Y) η (bondVariation b e)| ≤
        if enclosingCell b.1.1 = Y then |x * lam| * ‖η b‖ * ‖e‖ else 0 := by
  classical
  have hpr : ∀ b : ↥(chordBonds (finiteCells F)), HasFDerivAt (fun ζ : StepVariable (finiteCells F) => ζ b)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b) η :=
    fun b => (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b).hasFDerivAt
  have hf := fun b => (hpr b).norm_sq
  set Lc : StepVariable (finiteCells F) →L[ℝ] ℝ := ∑ b : ↥(chordBonds (finiteCells F)),
    if enclosingCell b.1.1 = Y then (x * lam / 2) • (2 • (innerSL ℝ (η b)).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b))
    else 0 with hLc
  have hQ : HasFDerivAt (cellQuadratic lam x Y) Lc η := by
    unfold cellQuadratic
    refine HasFDerivAt.fun_sum fun b _ => ?_
    split_ifs with hb
    · exact (hf b).const_mul (x * lam / 2)
    · exact hasFDerivAt_const _ _
  have hC : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (cellQuadratic lam x Y) η := by
    unfold cellQuadratic
    refine ContDiffAt.sum fun b _ => ?_
    split_ifs with hb
    · have h1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun ζ : StepVariable (finiteCells F) => ‖ζ b‖ ^ 2) :=
        (contDiff_norm_sq ℝ).comp (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b).contDiff
      exact contDiffAt_const.mul h1.contDiffAt
    · exact contDiffAt_const
  refine ⟨hQ.differentiableAt, hC, fun b e => ?_⟩
  rw [hQ.fderiv]
  have hsum : Lc (bondVariation b e) = if enclosingCell b.1.1 = Y then x * lam * inner ℝ (η b) e else 0 := by
    simp only [hLc, ContinuousLinearMap.sum_apply]
    rw [Finset.sum_eq_single b]
    · split_ifs with hb
      · simp [bondVariation]
        ring
      · simp
    · intro b' _ hne
      split_ifs with hb'
      · simp [bondVariation, Pi.single_eq_of_ne hne]
      · simp
    · simp
  rw [hsum]
  split_ifs with hb
  · rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
  · simp
theorem hasLocalSize_exponent_sub_quadratic (hL : DerivAlongRulesHold) (hSz : localSizeOfQuadraticBoundsStatement)
    (hD : SupDistCellComparison) (S : SizeSetting j ρ x lam κ W C d Φ p) {Cb : ℝ} (hC0 : lam ≤ Cb)
    (hB : InterpolatedExponentBounds s a ρA ρ x κ Cb m V)
    (hSm : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions),
      (∀ b, ‖η b‖ < ρ) → AreUnitVectors X → ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞)
        (rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X) (η, 0))
    (Y : F.Cell) :
    HasLocalSize ρ (cutoffFactor ρ p) Φ (fun q => 4 * lpMomentConstant lam W W q) x κ Cb (embeddedCellDist j Y)
      (fun ζ => interpolatedBlockExponent s a ρA x m Y V (extendByZero j Λ ζ) -
        cellQuadratic lam x Y (extendByZero j Λ ζ)) := by
  have hκ := S.rate_pos
  have hx1 := S.one_le_x
  have hx0 : 0 ≤ x := by linarith
  have hlam := S.lam_pos
  have hCb : 0 ≤ Cb := by linarith
  set c₀ : Fin 0 → F.Site F.top × Fin 4 := Fin.elim0 with hc₀
  set X₀ : Fin 0 → imaginaryQuaternions := Fin.elim0 with hX₀
  have hU : AreUnitVectors X₀ := fun i => i.elim0
  set f := rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c₀ X₀ with hf
  have hval : ∀ ζ, iteratedFDeriv ℝ 0 (fun τ : Fin 0 → ℝ => f (ζ, τ)) 0 (fun l => Pi.single l 1) =
      interpolatedBlockExponent s a ρA x m Y V ζ := by
    intro ζ
    rw [iteratedFDeriv_zero_apply]
    simp only [hf, rotatedEval, leftTranslate_bondSpread_zero]
  have hev : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      ∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) f (ζ, 0) := by
    intro η hη
    filter_upwards [(isOpen_bondBall ρ).mem_nhds hη] with ζ hζ
    exact (hSm Y ζ 0 c₀ X₀ hζ hU).of_le (by norm_num)
  have hmv := fun η hη => contDiffAt_iteratedFDeriv_parameters hL f η (hev η hη)
  have heq : (fun ζ => iteratedFDeriv ℝ 0 (fun τ : Fin 0 → ℝ => f (ζ, τ)) 0 (fun l => Pi.single l 1)) =
      interpolatedBlockExponent s a ρA x m Y V := funext hval
  simp only [heq] at hmv
  have htop : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      |interpolatedBlockExponent s a ρA x m Y V η| ≤ Cb * (x * localSqNorm κ Y η + 1) := by
    intro η hη
    have h1 := hB.deriv_top Y η 0 c₀ X₀ hη (by omega) hU
    have e1 : bondDeriv (fun V' => interpolatedBlockExponent s a ρA x m Y V' η) V c₀ X₀ =
        interpolatedBlockExponent s a ρA x m Y V η := hval η
    have e2 : bondSpan Y c₀ = 0 := by simp [bondSpan]
    rw [e1, e2] at h1
    simpa using h1
  refine hasLocalSize_comp_extendByZero j Λ hSz S
    (fun ζ => interpolatedBlockExponent s a ρA x m Y V ζ - cellQuadratic lam x Y ζ) 0 Cb 4 Y
    hCb (by norm_num) (fun η hη => ((hmv η hη).1).sub (cellQuadratic_deriv lam x Y η).2.1) ?_ ?_
  · intro η hη
    rw [sub_zero]
    have h1 := htop η hη
    have h2 := abs_cellQuadratic_le lam x κ hx0 hlam.le Y η
    have hsq := localSqNorm_nonneg κ Y η
    have h3 := abs_sub (interpolatedBlockExponent s a ρA x m Y V η) (cellQuadratic lam x Y η)
    have hxs : 0 ≤ x * localSqNorm κ Y η := mul_nonneg hx0 hsq
    nlinarith
  · intro η b e hη he
    have hd1 : DifferentiableAt ℝ (interpolatedBlockExponent s a ρA x m Y V) η :=
      (hmv η hη).1.differentiableAt (by simp)
    obtain ⟨hd2, -, hd3⟩ := cellQuadratic_deriv lam x Y η
    have e0 : fderiv ℝ (fun ζ => interpolatedBlockExponent s a ρA x m Y V ζ - cellQuadratic lam x Y ζ) η
        (bondVariation b e) =
        fderiv ℝ (interpolatedBlockExponent s a ρA x m Y V) η (bondVariation b e) -
          fderiv ℝ (cellQuadratic lam x Y) η (bondVariation b e) := by
      rw [fderiv_fun_sub hd1 hd2]
      rfl
    rw [e0]
    have e1 : fderiv ℝ (interpolatedBlockExponent s a ρA x m Y V) η (bondVariation b e) =
        bondDeriv (fun V' => bondPartialDeriv (interpolatedBlockExponent s a ρA x m Y V') b η e) V c₀ X₀ := by
      unfold bondDeriv
      rw [iteratedFDeriv_zero_apply]
      simp only [leftTranslate_bondSpread_zero]
      rfl
    have h1 := hB.deriv_top_partial Y η b e 0 c₀ X₀ hη (by omega) hU he
    rw [← e1] at h1
    obtain ⟨-, w2⟩ := bondSpan_le_bondSpanWithCell hD Y (enclosingCell b.1.1) c₀
    set B := Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) with hBd
    have hB0 : 0 < B := Real.exp_pos _
    have h2 : Real.exp (-(2 ^ 6 * κ * (bondSpanWithCell Y (enclosingCell b.1.1) c₀ : ℝ))) ≤ B := by
      refine Real.exp_le_exp.2 ?_
      have a1 : (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤ (bondSpanWithCell Y (enclosingCell b.1.1) c₀ : ℝ) := by
        exact_mod_cast w2
      nlinarith
    have hsq := localSqNorm_nonneg κ Y η
    have hr := mul_sqrt_add_one_le hx1 hsq
    set u := x * Real.sqrt (localSqNorm κ Y η) + 1 with hu
    have hu0 : 0 ≤ u := by positivity
    have h3 : |fderiv ℝ (interpolatedBlockExponent s a ρA x m Y V) η (bondVariation b e)| ≤ Cb * u * B :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    have h4 : |fderiv ℝ (cellQuadratic lam x Y) η (bondVariation b e)| ≤ lam * u * B := by
      have h5 := hd3 b e
      rw [he, mul_one] at h5
      refine h5.trans ?_
      split_ifs with hb
      · have hBone : B = 1 := by
          simp [hBd, hb, cellSupDist_self_eq_zero]
        rw [hBone, mul_one, abs_of_nonneg (by positivity)]
        have h6 : ‖η b‖ ≤ Real.sqrt (localSqNorm κ Y η) :=
          Real.le_sqrt_of_sq_le (sq_norm_le_localSqNorm η b hb)
        have : x * lam * ‖η b‖ ≤ lam * (x * Real.sqrt (localSqNorm κ Y η)) := by
          have := mul_le_mul_of_nonneg_left h6 (mul_nonneg hx0 hlam.le)
          linarith
        linarith
      · positivity
    calc _ ≤ |fderiv ℝ (interpolatedBlockExponent s a ρA x m Y V) η (bondVariation b e)| +
          |fderiv ℝ (cellQuadratic lam x Y) η (bondVariation b e)| := abs_sub _ _
      _ ≤ (2 * Cb) * u * B := by nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hC0) hu0) hB0.le]
      _ ≤ (2 * Cb) * (2 * Real.sqrt x * (x * localSqNorm κ Y η + 1)) * B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by positivity)) hB0.le
      _ = _ := by ring
def perturbationsOf {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) : Fin (l + k) → Perturbation F :=
  Fin.addCases (fun i => Perturbation.bulk (b i) (u i)) (fun i => Perturbation.top (c i) (X i))
theorem perturbationsOf_isUnit {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hu : ∀ i, ‖u i‖ = 1) (hX : AreUnitVectors X) :
    ∀ i, (perturbationsOf b u c X i).IsUnit := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [perturbationsOf, Fin.addCases_left, Perturbation.IsUnit]
    exact hu i
  · simp only [perturbationsOf, Fin.addCases_right, Perturbation.IsUnit]
    exact hX i
theorem jointDisplacement_eq_perturbedField {l k : ℕ} (h : LocalFamily) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    jointDisplacement (fun ζ V' => interpolatedExpansion s a ρA m h y ζ V') η V b u c X =
      fun τ => subtractTrivial h F y (perturbedField s a ρA m V η (perturbationsOf b u c X) τ) := by
  classical
  funext τ
  have h1 : perturbedVariable η (perturbationsOf b u c X) τ =
      displacedPoint η b u fun i => τ (Fin.castAdd k i) := by
    unfold perturbedVariable displacedPoint
    congr 1
    rw [Fin.sum_univ_add]
    simp only [perturbationsOf, Fin.addCases_left, Fin.addCases_right, Perturbation.variableDirection, smul_zero,
      Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ => (Pi.single_smul _ _ _).symm
  have h2 : perturbedTop V (perturbationsOf b u c X) τ =
      leftTranslate (ColdStepAtMirrorFrames.bondSpread c X fun i => τ (Fin.natAdd l i)) V := by
    unfold perturbedTop
    congr 1
    funext z i
    simp only [ColdStepAtMirrorFrames.bondSpread]
    rw [Fin.sum_univ_add]
    simp only [perturbationsOf, Fin.addCases_left, Fin.addCases_right, Perturbation.topBond,
      Perturbation.topDirection, smul_zero, ite_self, Finset.sum_const_zero, zero_add]
  simp only [jointDisplacement, interpolatedExpansion, perturbedField, h1, h2]
theorem cellSupDist_le_cellSetDiameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P :=
  (Finset.le_sup (f := fun v => cellSupDist u v) hv).trans
    (Finset.le_sup (f := fun u => P.sup fun v => cellSupDist u v) hu)
theorem bondSpan_le_cellSetDiameter {k : ℕ} {P : Finset F.Cell} {Y : F.Cell} {c : Fin k → F.Site F.top × Fin 4}
    (hY : Y ∈ P) (hc : ∀ l, (c l).1 ∈ P) : bondSpan Y c ≤ cellSetDiameter P := by
  have e2 : bondSpan Y c = max (Finset.univ.sup fun l => siteSupDist Y (c l).1)
      (Finset.univ.sup fun l => Finset.univ.sup fun l' => siteSupDist (c l).1 (c l').1) := rfl
  rw [e2]
  exact max_le (Finset.sup_le fun l _ => cellSupDist_le_cellSetDiameter hY (hc l)) (Finset.sup_le fun l _ =>
    Finset.sup_le fun l' _ => cellSupDist_le_cellSetDiameter (hc l) (hc l'))
set_option maxHeartbeats 1600000 in
theorem hasLocalSize_expansionDeriv (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hRM : rotatedEvalContDiffOfDisplacements) (hSz : localSizeOfQuadraticBoundsStatement)
    (hD : SupDistCellComparison) (S : SizeSetting j ρ x lam κ W C d Φ p) {Cb Cc Ek : ℝ} {e' : ℕ → ℝ}
    (h : LocalFamily) (y : F.Site F.depth) (hCb : 0 ≤ Cb) (hCc : Cb * (W + 1) ≤ Cc) (hEk : 0 ≤ Ek)
    (hRow : ∀ (η : StepVariable (finiteCells F)) (q : ℕ) (w : Fin q → Perturbation F), (∀ b, ‖η b‖ < ρ) →
      (∀ l, (w l).IsUnit) →
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ => subtractTrivial h F y (perturbedField s a ρA m V η w τ)) 0 ∧
      (1 ≤ q → q ≤ 3 →
        |iteratedFDeriv ℝ q (fun τ => subtractTrivial h F y (perturbedField s a ρA m V η w τ)) 0
          fun l => Pi.single l 1| ≤
          Cb * runningMax e' q *
            Real.exp (-(2 ^ 7 * κ * cellSetDiameter (insert (enclosingCell y) (perturbationCells w))))))
    (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 2)
    (hX : AreUnitVectors X) (hE : runningMax e' (1 + k) ≤ Ek) :
    HasLocalSize ρ (cutoffFactor ρ p) Φ (fun q => 4 * lpMomentConstant lam W W q) x κ
      (Cc * Ek * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(2 ^ 4 * κ * bondSpan (enclosingCell y) c)))
      (embeddedCellDist j (enclosingCell y))
      (fun ζ => bondDeriv (interpolatedExpansion s a ρA m h y (extendByZero j Λ ζ)) V c X) := by
  classical
  have hκ := S.rate_pos
  have hx1 := S.one_le_x
  have hx0 : 0 < x := by linarith
  have hW := S.total_nonneg
  set Y : F.Cell := enclosingCell y with hY
  set G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
    fun ζ V' => interpolatedExpansion s a ρA m h y ζ V' with hG
  set f := rotatedEval G V c X with hf
  set T : StepVariable (finiteCells F) → ℝ := fun η => bondDeriv (interpolatedExpansion s a ρA m h y η) V c X with hT
  have hf3 : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) f (η, 0) := by
    intro η hη
    refine hRM F V G η k c X 3 fun l b u hu => ?_
    rw [jointDisplacement_eq_perturbedField h y η b u c X]
    exact (hRow η _ (perturbationsOf b u c X) hη (perturbationsOf_isUnit b u c X hu hX)).1
  have hev : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      ∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f (ζ, 0) := by
    intro η hη
    filter_upwards [(isOpen_bondBall ρ).mem_nhds hη] with ζ hζ
    exact (hf3 ζ hζ).of_le (by exact_mod_cast (show k + 1 ≤ 3 by omega))
  have hmv := fun η hη => contDiffAt_iteratedFDeriv_parameters hL f η (hev η hη)
  set n : ℝ := (bondSpan Y c : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hgrad : ∀ (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
      (∀ b, ‖η b‖ < ρ) → ‖e‖ = 1 → |fderiv ℝ T η (bondVariation b e)| ≤
        Cb * Ek * (Real.exp (-(2 ^ 6 * κ * n)) *
          Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))) := by
    intro η b e hη he
    have e1 := (hmv η hη).2 (bondVariation b e)
    have hu : ∀ i : Fin 1, ‖(![e] : Fin 1 → BondVector) i‖ = 1 := fun i => by simpa using he
    have e2 := (hA F V G η k c X).2 1 ![b] ![e] ((hf3 η hη).of_le (by
      exact_mod_cast (show 1 + k ≤ 3 by omega)))
    have e3 : pointDirections (k := k) ![b] ![e] = [(bondVariation b e, 0)] := by
      simp [pointDirections, List.ofFn_succ, variableDirection, bondVariation]
    rw [e3] at e2
    have e4 : fderiv ℝ T η (bondVariation b e) = jointMixedDeriv G η V ![b] ![e] c X := by
      rw [e2]
      exact e1
    rw [e4]
    have hb := (hRow η _ (perturbationsOf ![b] ![e] c X) hη (perturbationsOf_isUnit _ _ c X hu hX)).2
      (by omega) (by omega)
    have e5 : jointMixedDeriv G η V ![b] ![e] c X = iteratedFDeriv ℝ (1 + k) (fun τ => subtractTrivial h F y
        (perturbedField s a ρA m V η (perturbationsOf ![b] ![e] c X) τ)) 0 fun l => Pi.single l 1 := by
      unfold jointMixedDeriv
      rw [jointDisplacement_eq_perturbedField h y η ![b] ![e] c X]
    rw [e5]
    refine hb.trans ?_
    set P : Finset F.Cell := insert Y (perturbationCells (perturbationsOf ![b] ![e] c X)) with hP
    have mY : Y ∈ P := Finset.mem_insert_self _ _
    have mb : enclosingCell b.1.1 ∈ P := by
      refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨Fin.castAdd k 0, Finset.mem_univ _, ?_⟩)
      simp [perturbationsOf, Perturbation.cell]
    have mc : ∀ l, (c l).1 ∈ P := fun l => by
      refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨Fin.natAdd 1 l, Finset.mem_univ _, ?_⟩)
      simp [perturbationsOf, Perturbation.cell]
    have s1 : n ≤ (cellSetDiameter P : ℝ) := by
      rw [hn]
      exact_mod_cast bondSpan_le_cellSetDiameter mY mc
    have s2 : (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤ (cellSetDiameter P : ℝ) := by
      exact_mod_cast cellSupDist_le_cellSetDiameter mb mY
    have hex : Real.exp (-(2 ^ 7 * κ * (cellSetDiameter P : ℝ))) ≤
        Real.exp (-(2 ^ 6 * κ * n)) * Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have a1 : 2 ^ 6 * κ * n ≤ 2 ^ 6 * κ * (cellSetDiameter P : ℝ) := mul_le_mul_of_nonneg_left s1 (by positivity)
      have a2 := mul_le_mul_of_nonneg_left s2 (by positivity : 0 ≤ 2 ^ 6 * κ)
      nlinarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left hE hCb) hex (Real.exp_pos _).le (by positivity)
  set r := Real.sqrt x with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hx0
  have hrr : r * r = x := Real.mul_self_sqrt hx0.le
  have hpow : x ^ (-(1 / 2 : ℝ)) = r⁻¹ := by
    rw [Real.rpow_neg hx0.le, hr, Real.sqrt_eq_rpow]
  set E4 := Real.exp (-(2 ^ 4 * κ * n)) with hE4
  set E6 := Real.exp (-(2 ^ 6 * κ * n)) with hE6
  have hE40 : 0 < E4 := Real.exp_pos _
  have h64 : E6 ≤ E4 := by
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg hκ.le hn0]
  have hCc0 : 0 ≤ Cc := (mul_nonneg hCb (by linarith)).trans hCc
  have hCbc : Cb ≤ Cc := by nlinarith
  have hh : 0 ≤ Cc * Ek * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(2 ^ 4 * κ * (bondSpan (enclosingCell y) c : ℝ))) := by
    rw [hpow]
    positivity
  refine hasLocalSize_comp_extendByZero j Λ hSz S T (T 0) _ 4 Y hh (by norm_num) (fun η hη => (hmv η hη).1) ?_ ?_
  · intro η hη
    set gb : ↥(chordBonds (finiteCells F)) → ℝ := fun b =>
      Cb * Ek * (E6 * Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))) with hgb
    have hall : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ < ρ) →
        ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        |fderiv ℝ T ζ (bondVariation b e)| ≤ gb b * ‖e‖ := fun ζ hζ b e =>
      abs_le_mul_norm_of_homogeneous (g := fun e => fderiv ℝ T ζ (bondVariation b e))
        (fun c' e' => by simp [bondVariation, Pi.single_smul])
        (fun e' he' => hgrad ζ b e' hζ he') e
    have hball : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ b, ‖(t • η) b‖ < ρ := by
      intro t ht b
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      have := hη b
      nlinarith [norm_nonneg (η b), ht.2, ht.1]
    have hder : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => T (t • η)) (fderiv ℝ T (t • η) η) t := by
      intro t ht
      have h1 : DifferentiableAt ℝ T (t • η) := ((hmv _ (hball t ht)).1).differentiableAt (by simp)
      have h2 : HasDerivAt (fun t : ℝ => t • η) η t := by
        simpa using (hasDerivAt_id t).smul_const η
      exact h1.hasFDerivAt.comp_hasDerivAt t h2
    have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => T (t • η)) t‖ ≤ ∑ b, gb b * ‖η b‖ := by
      intro t ht
      rw [(hder t ht).deriv, Real.norm_eq_abs]
      have e1 : ∑ b, bondVariation b (η b) = η := Finset.univ_sum_single η
      have e2 : fderiv ℝ T (t • η) η = ∑ b, fderiv ℝ T (t • η) (bondVariation b (η b)) := by
        have h3 := map_sum (fderiv ℝ T (t • η)) (fun b => bondVariation b (η b)) Finset.univ
        rw [← h3, e1]
      rw [e2]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => hall _ (hball t ht) b _)
    have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hder t ht).differentiableAt) hbd (Set.left_mem_Icc.2 zero_le_one)
      (Set.right_mem_Icc.2 zero_le_one)
    simp only [one_smul, zero_smul, sub_zero, norm_one, mul_one, Real.norm_eq_abs] at hmvt
    refine hmvt.trans ?_
    set u : ↥(chordBonds (finiteCells F)) → ℝ :=
      fun b => Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) with hu
    have hu0 : ∀ b, 0 ≤ u b := fun b => (Real.exp_pos _).le
    have hsu : ∑ b, u b ≤ W := by
      refine (Finset.sum_le_sum fun b _ => ?_).trans (S.cellSums Y)
      refine Real.exp_le_exp.2 ?_
      have a0 : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1.1) Y := Nat.cast_nonneg _
      nlinarith [mul_nonneg hκ.le a0]
    have hterm : ∀ b, u b * ‖η b‖ ≤ (2 * r)⁻¹ * (x * (u b * ‖η b‖ ^ 2) + u b) := by
      intro b
      have h1 : 2 * r * ‖η b‖ ≤ x * ‖η b‖ ^ 2 + 1 := by
        nlinarith [sq_nonneg (r * ‖η b‖ - 1)]
      have h2 : ‖η b‖ ≤ (2 * r)⁻¹ * (x * ‖η b‖ ^ 2 + 1) := by
        rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
        linarith
      have := mul_le_mul_of_nonneg_left h2 (hu0 b)
      calc _ ≤ _ := this
        _ = _ := by ring
    have hsum : ∑ b, u b * ‖η b‖ ≤ (2 * r)⁻¹ * (x * localSqNorm κ Y η + W) := by
      refine (Finset.sum_le_sum fun b _ => hterm b).trans ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : ∑ b, u b * ‖η b‖ ^ 2 = localSqNorm κ Y η := rfl
      rw [this]
      linarith
    have hsq := localSqNorm_nonneg κ Y η
    have hxs : 0 ≤ x * localSqNorm κ Y η := mul_nonneg hx0.le hsq
    have e2 : ∑ b, gb b * ‖η b‖ = Cb * Ek * E6 * ∑ b, u b * ‖η b‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hgb, hu]
      ring
    rw [e2, hpow]
    have h5 : x * localSqNorm κ Y η + W ≤ (W + 1) * (x * localSqNorm κ Y η + 1) := by nlinarith
    have h6 : ∑ b, u b * ‖η b‖ ≤ (2 * r)⁻¹ * ((W + 1) * (x * localSqNorm κ Y η + 1)) :=
      hsum.trans (mul_le_mul_of_nonneg_left h5 (by positivity))
    have hm : 0 ≤ x * localSqNorm κ Y η + 1 := by linarith
    have e3 : (2 * r)⁻¹ = 2⁻¹ * r⁻¹ := mul_inv _ _
    calc _ ≤ Cb * Ek * E6 * ((2 * r)⁻¹ * ((W + 1) * (x * localSqNorm κ Y η + 1))) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = (Cb * (W + 1)) * (Ek * E6 * (2⁻¹ * r⁻¹ * (x * localSqNorm κ Y η + 1))) := by rw [e3]; ring
      _ ≤ Cc * (Ek * E6 * (2⁻¹ * r⁻¹ * (x * localSqNorm κ Y η + 1))) :=
          mul_le_mul_of_nonneg_right hCc (by positivity)
      _ ≤ Cc * (Ek * E4 * (2⁻¹ * r⁻¹ * (x * localSqNorm κ Y η + 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCc0
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h64 hEk
      _ ≤ 4 * (Cc * Ek * r⁻¹ * E4) * (x * localSqNorm κ Y η + 1) := by
          have : 0 ≤ Cc * Ek * r⁻¹ * E4 * (x * localSqNorm κ Y η + 1) := by positivity
          nlinarith
  · intro η b e hη he
    refine (hgrad η b e hη he).trans ?_
    rw [hpow]
    have hsq := localSqNorm_nonneg κ Y η
    have hm : 1 ≤ x * localSqNorm κ Y η + 1 := by nlinarith
    set D : ℝ := (cellSupDist (enclosingCell b.1.1) Y : ℝ) with hDd
    have hD0 : 0 ≤ D := Nat.cast_nonneg _
    have hd1 : Real.exp (-(2 ^ 6 * κ * D)) ≤ Real.exp (-(2 * κ * D)) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [mul_nonneg hκ.le hD0]
    have e1 : r * (4 * (Cc * Ek * r⁻¹ * E4)) = 4 * (Cc * Ek * E4) := by
      field_simp
    rw [e1]
    calc _ ≤ Cc * Ek * (E4 * Real.exp (-(2 * κ * D))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hCbc hEk) ?_ (by positivity) (by positivity)
          exact mul_le_mul h64 hd1 (Real.exp_pos _).le hE40.le
      _ ≤ 4 * (Cc * Ek * E4) * Real.exp (-(2 * κ * D)) * 1 := by
          have : 0 ≤ Cc * Ek * E4 * Real.exp (-(2 * κ * D)) := by positivity
          nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
end Bounds
section Constants
def ExpansionDerivBound (K : ℕ → ℝ) (r κ : ℝ) (L : ℕ) (C : ℝ) : Prop :=
  ∀ (F : BlockFrame) (n₀ k p m : ℕ) (σ s a ρA : ℝ) (e : ℕ → ℝ) (f : LocalFamily)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) (w : Fin p → Perturbation F) (y : F.Site F.depth),
    F.blockSide = L → IsLargeCubicTorus F → IsCubicTorusAbove L F.depth n₀ F → k ≤ 6 → (∀ j, 0 ≤ e j) →
    HasBoundedDerivatives L F.depth n₀ σ (κ / 2 ^ 10) k e f →
    IsSmallCurvature σ (interpolatedField s a ρA m V η) →
    (∀ x i, ¬ IsAxialTreeBond (x, i) → ‖interpolatedCoords s a ρA m V η x i‖ ≤ 1) →
    (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m d) V) →
    (∀ d ∈ chordBonds (finiteCells F), ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4)
      (X' : Fin k' → imaginaryQuaternions),
      1 ≤ k' → AreUnitVectors X' →
      ‖bondDeriv (interpolatedFrame s a ρA m d) V c' X'‖ ≤
        K k' * Real.exp (-(r * bondListDistance (enclosingCell d.1) c'))) →
    (∀ l, (w l).IsUnit) →
    ContDiffAt ℝ k (fun τ => subtractTrivial f F y (perturbedField s a ρA m V η w τ)) 0 ∧
    (1 ≤ p → p ≤ k →
      |iteratedFDeriv ℝ p (fun τ => subtractTrivial f F y (perturbedField s a ρA m V η w τ)) 0
        fun l => Pi.single l 1| ≤
        C * runningMax e p *
          Real.exp (-(2 ^ 7 * κ * cellSetDiameter (insert (enclosingCell y) (perturbationCells w)))))
open Classical in
def weightTotal (hS : ExpDecaySumBounded) (L : ℕ) (κ : ℝ) : ℝ :=
  if h : 0 < κ then Classical.choose (hS ((centredCube L).card * 4) (2 * κ) (by positivity)) else 0
theorem weightTotal_spec (hS : ExpDecaySumBounded) (L : ℕ) {κ : ℝ} (h : 0 < κ) :
    0 ≤ weightTotal hS L κ ∧ ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
      (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ (centredCube L).card * 4) →
      ∀ z : F.Cell, ∑ b, Real.exp (-(2 * κ * (cellSupDist (y b) z : ℝ))) ≤ weightTotal hS L κ := by
  unfold weightTotal
  rw [dif_pos h]
  exact Classical.choose_spec (hS ((centredCube L).card * 4) (2 * κ) (by positivity))
structure ObservableConstants (hS : ExpDecaySumBounded) (K : StepParameters → ℕ → ℝ) (T : StepParameters) :
    Prop where
  side_large : 2 ^ 40 ≤ T.L
  n₀_large : 64 ≤ T.n₀
  rate_le : 2 ^ 10 * T.κ ≤ T.chainParams.δ₂
  one_le_coupling : 1 ≤ T.coupling
  lam_le : T.chainParams.lam ≤ T.Cs
  rowBound : ∃ Cb : ℝ, 0 ≤ Cb ∧ ExpansionDerivBound (K (rateParameters T)) T.chainParams.κ₂ T.κ T.L Cb ∧
    Cb * (weightTotal hS T.L T.κ + 1) ≤ T.Cs
theorem eventually_observableConstants (hS : ExpDecaySumBounded) (hBA : boundAlongPerturbationsStatement)
    (K : StepParameters → ℕ → ℝ) (hK : ∀ T k, 0 < K T k) :
    EventuallyInParameters (ObservableConstants hS K) := by
  intro a _
  refine ⟨2 ^ 40, fun L hL hL₀ c hc => ?_⟩
  have hcl := hc.classical.1
  have hδ : 0 < c.δ₂ := hcl.2.2.2.1
  refine ⟨0, fun Ct _ => ?_⟩
  refine ⟨c.δ₂ / 2 ^ 10, by positivity, fun κ hκ hκle => ?_⟩
  have hr : 2 ^ 10 * κ ≤ c.δ₂ := by
    have := mul_le_mul_of_nonneg_left hκle (by positivity : (0 : ℝ) ≤ 2 ^ 10)
    linarith
  have h9 : 2 ^ 9 * κ ≤ c.κ₂ := by nlinarith
  refine ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩
  refine ⟨0, fun nss _ => ?_⟩
  refine ⟨1, one_pos, fun σ _ _ p _ => ?_⟩
  obtain ⟨Cb, hCb, hRow⟩ := hBA (K ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩) c.κ₂ κ L
    (fun k => (hK _ k).le) hκ h9 hL hL₀
  refine ⟨max c.lam (Cb * (weightTotal hS L κ + 1)), fun Cs hCs E _ => ?_⟩
  refine ⟨64, fun n₀ hn₀ => ?_⟩
  refine ⟨0, fun CE _ => ?_⟩
  refine ⟨1, fun y₁ hy₁ => ?_⟩
  exact ⟨hL₀, hn₀, hr, hy₁, (le_max_left _ _).trans hCs, Cb, hCb.le, hRow, (le_max_right _ _).trans hCs⟩
theorem card_bonds_in_cell_le {F : BlockFrame} (hB : SiteDecomposition) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) :
    (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
      (centredCube F.blockSide).card * 4 := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.card_cellChordBonds_le <;> assumption
theorem nonempty_chordBonds {F : BlockFrame} (hB : SiteDecomposition) (hC : BlocksCoverLowerLevel)
    (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) : Nonempty ↥(chordBonds (finiteCells F)) := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.nonempty_chordBonds <;> assumption
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem runningMax_le {ε ε₃ : ℝ} (hε : 0 < ε) (h3 : ε ≤ ε₃) (k : ℕ) (hk : k ≤ 2) :
    runningMax (fun i => if i = 3 then ε₃ else ε) (1 + k) ≤ if k = 2 then ε₃ else ε := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · simp [runningMax, hε.le]
  · simp [runningMax, hε.le]
  · simp [runningMax, hε.le, h3]
end Constants
end ObservableSizes
open ObservableSizes in
set_option maxHeartbeats 1600000 in
theorem observableSizesStatement_holds (hKern : interpolationKernelBoundsStatement)
    (hEB : interpolatedExponentBoundsStatement) (hNear : interpolatedFramesControlled)
    (hConv : mixturesOfIntermediateLawsConvex) (hS : ExpDecaySumBounded)
    (hJoin : EventuallyInParametersCombines) (hD : SupDistCellComparison)
    (hBA : boundAlongPerturbationsStatement) (hSz : localSizeOfQuadraticBoundsStatement)
    (hSmooth : interpolatedBlockExponentSmoothStatement) (hL : DerivAlongRulesHold)
    (hA : JointMixedDerivEqDerivAlong) (hRM : rotatedEvalContDiffOfDisplacements)
    (hB : SiteDecomposition) (hC : BlocksCoverLowerLevel) :
    observableSizesStatement := by
  classical
  obtain ⟨K, Dk, hKpos, -, hKT⟩ := hKern
  refine ⟨fun T q => 4 * lpMomentConstant T.chainParams.lam (weightTotal hS T.L T.κ) (weightTotal hS T.L T.κ) q, ?_⟩
  have hP := hJoin.1 _ _ (hJoin.1 _ _ (hJoin.1 _ _ (hJoin.1 _ _ hKT hEB) hNear) hConv)
    (eventually_observableConstants hS hBA K hKpos)
  refine hJoin.2 _ _ ?_ hP
  rintro T hT ⟨⟨⟨⟨hk, he⟩, hn⟩, hcv⟩, hnum⟩ t x hx ι _ _ d n w M hw hM M₀ hM₀
  have htor := hM₀.isCubicTopTorus
  have hcold := hM₀.isSmallCurvature
  obtain ⟨hFL, hFt, n', hside, hn₀⟩ := id htor
  have hn64 : 64 ≤ n' := hnum.n₀_large.trans hn₀
  have hs2 : ∀ i, 2 ≤ M₀.frame.extent i := fun i => by rw [hside i]; omega
  have hsd : ∀ i, 0 < M₀.frame.extent i := fun i => by have := hs2 i; omega
  have hLodd : Odd M₀.frame.blockSide := hFL ▸ hT.odd_L
  have hx1 : 1 ≤ x := hnum.one_le_coupling.trans hx
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hρ' : T.ballRadius = T.σ / 64 := rfl
  have hlam : 0 < T.chainParams.lam := hT.chain_admissible.positivity.2.2.1
  obtain ⟨hW0, hW1⟩ := weightTotal_spec hS T.L hT.κ_pos
  have hcells : ∀ z : M₀.frame.Cell, ∑ b : ↥(chordBonds (finiteCells M₀.frame)),
      Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ weightTotal hS T.L T.κ :=
    hW1 M₀.frame ↥(chordBonds (finiteCells M₀.frame)) (fun b => enclosingCell b.1.1) (fun z => by
      have := card_bonds_in_cell_le hB hLodd hs2 z
      rwa [hFL] at this)
  have hdist : IsPseudoMetricOnBonds d := by
    have hk' := hM₀.preservesCellDist
    refine ⟨fun i => ?_, fun i i' => ?_, fun i i' i'' => ?_⟩
    · rw [hk' i i, cellSupDist_self_eq_zero]
      simp
    · rw [hk' i i', hk' i' i]
      have := (hD.1 M₀.frame M₀.frame.top (enclosingCell (M₀.embed i).1.1) (enclosingCell (M₀.embed i').1.1)
        (enclosingCell (M₀.embed i').1.1)).2.1
      exact_mod_cast this
    · rw [hk' i i'', hk' i i', hk' i' i'']
      have := (hD.1 M₀.frame M₀.frame.top (enclosingCell (M₀.embed i).1.1) (enclosingCell (M₀.embed i').1.1)
        (enclosingCell (M₀.embed i'').1.1)).2.2
      exact_mod_cast this
  have S : SizeSetting M₀.embed T.ballRadius x T.chainParams.lam T.κ (weightTotal hS T.L T.κ) T.Ct d
      (convexCombinationExponent T.chainParams.lam x w M) T.p :=
    ⟨hρ, hx1, hlam, hT.κ_pos, hW0, hT.cutoff, hdist, hcv t x hx ι d n w M hw hM, hM₀.embed_injective,
      hM₀.preservesCellDist, hcells⟩
  have hne := nonempty_chordBonds hB hC hLodd hs2
  have hCs0 : 0 ≤ T.Cs := hlam.le.trans hnum.lam_le
  have hker := fun (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (η : StepVariable (finiteCells M₀.frame))
      (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) =>
    hk x t M₀.frame M₀.topField s η hx htor hcold hs0 hs1 hη
  have hSm := fun (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (Y : M₀.frame.Cell)
      (η : StepVariable (finiteCells M₀.frame)) (k : ℕ)
      (c : Fin k → M₀.frame.Site M₀.frame.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (hη : ∀ b, ‖η b‖ < T.ballRadius) (hX : AreUnitVectors X) =>
    hSmooth M₀.frame s T.a T.chainParams.ρA T.ballRadius x T.κ T.chainParams.κ₂ T.chainParams.δ₂ (frameRadius x)
      (K (rateParameters T)) (Dk (rateParameters T)) M₀.topField Y η k c X hne (hker s hs0 hs1)
      (fun b => (hη b).le) hX
  refine ⟨fun s Y k c X hs0 hs1 hk3 hX => ?_, fun s Y hs0 hs1 => ?_,
    fun s ε h y k c X hs0 hs1 hε hfam hk2 hX => ?_⟩
  · exact hasLocalSize_exponentDeriv hL hSz hD S hCs0 (he t x hx M₀.frame M₀.topField s htor hcold hs0 hs1)
      (hSm s hs0 hs1) Y k c X hk3 hX
  · exact hasLocalSize_exponent_sub_quadratic hL hSz hD S hnum.lam_le
      (he t x hx M₀.frame M₀.topField s htor hcold hs0 hs1) (hSm s hs0 hs1) Y
  · obtain ⟨Cb, hCb, hRow, hCc⟩ := hnum.rowBound
    have hη₃ := hT.η₃_pos
    have hη₁ := hT.η₃_le_one
    have h3 : ε ≤ ε / T.η₃ := by
      rw [le_div_iff₀ hη₃]
      nlinarith
    have hE := runningMax_le hε h3 k hk2
    have he0 : ∀ i, 0 ≤ (fun i => if i = 3 then ε / T.η₃ else ε) i := by
      intro i
      simp only
      split_ifs
      · positivity
      · exact hε.le
    have hfam' : IsNormBoundedLocalFamily T.L M₀.frame.depth T.n₀ T.σ T.decayRate ε (ε / T.η₃) h := by
      rw [hFt]
      exact hfam
    have hHas : HasBoundedDerivatives T.L M₀.frame.depth T.n₀ T.σ (T.κ / 2 ^ 10) 3
        (fun i => if i = 3 then ε / T.η₃ else ε) h :=
      ⟨fun F' hF' y' W hW j' c' X' => by simpa using hfam'.smooth F' hF' y' W hW j' c' X',
        hfam'.gauge_invariant, fun F' hF' y' W j' c' X' hW h1 h3' hX' => hfam'.decay F' hF' y' W j' c' X' hW h1 h3' hX'⟩
    have hcub : IsLargeCubicTorus M₀.frame := ⟨n', hn64, hside⟩
    have hlow : IsCubicTorusAbove T.L M₀.frame.depth T.n₀ M₀.frame := by
      refine ⟨hFL, rfl, n', hside, ?_⟩
      have hLpos : 1 ≤ T.L := hT.odd_L.pos
      calc T.n₀ ≤ n' := hn₀
        _ ≤ n' * T.L := Nat.le_mul_of_pos_right _ hLpos
    obtain ⟨-, hsmall⟩ := (hn t x hx).single M₀.frame M₀.topField s htor hcold hs0 hs1
    have hρA : T.chainParams.ρA ≤ 1 := hT.chain_admissible.classical.1.2.1
    have hσ := hT.σ_pos
    refine hasLocalSize_expansionDeriv (Cb := Cb) (Cc := T.Cs) (e' := fun i => if i = 3 then ε / T.η₃ else ε)
      hL hA hRM hSz hD S h y hCb hCc (by split_ifs <;> positivity) (fun η q w' hη hw' => ?_) k c X hk2 hX hE
    have hηc : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
    have hkr := hker s hs0 hs1 η hηc
    refine hRow M₀.frame T.n₀ 3 q (frameRadius x) T.σ s T.a T.chainParams.ρA _ h M₀.topField η w' y hFL hcub hlow
      (by norm_num) he0 hHas ?_ ?_ hkr.analytic hkr.frame_deriv hw'
    · intro pl hpl
      have := hsmall.small_curvature_nearby η (fun b => by rw [← hρ']; exact hηc b) pl hpl
      linarith
    · intro x' i ht
      have hch : (x', i) ∈ chordBonds (finiteCells M₀.frame) := by
        unfold chordBonds innerBonds
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
        exact ⟨⟨hC M₀.frame hLodd hsd x', hC M₀.frame hLodd hsd _⟩, ht⟩
      have h1 := hsmall.norm_add_le (x', i) hch
      have e1 : stepCoordinates η x' i = toImaginary (η ⟨(x', i), hch⟩) := by
        unfold stepCoordinates
        rw [dif_pos hch]
      have h2 := hη ⟨(x', i), hch⟩
      have h4 : interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) M₀.topField η x' i =
          interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (x', i) M₀.topField + stepCoordinates η x' i := rfl
      rw [h4, e1]
      have h5 := norm_add_le (interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (x', i) M₀.topField)
        (toImaginary (η ⟨(x', i), hch⟩))
      rw [norm_toImaginary] at h5
      linarith
end YangMills.Construction.Interpolation
end
