import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesAcrossTwoVariables
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.PartFromItsBounds
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenAtATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open Set BlockAverages ColdStepAtMirrorFrames IteratedDerivative Interpolation WeightedResponses
namespace ResponseInTheExpansion.RemainderCalculus
section DirectionalForms
variable {F : BlockFrame} {k : ℕ}
abbrev JointSpace (F : BlockFrame) (k : ℕ) : Type := StepVariable (finiteCells F) × (Fin k → ℝ)
abbrev paramList (F : BlockFrame) (k : ℕ) : List (JointSpace F k) := parameterDirections _ _ (parameterBasis k)
theorem paramList_length : (paramList F k).length = k := by simp [parameterDirections, parameterBasis]
theorem iteratedFDeriv_slice_eq_derivAlong (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ)
    (ζ : StepVariable (finiteCells F))
    (hf : ContDiffAt ℝ (k : WithTop ℕ∞) f (ζ, 0)) :
    iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => f (ζ, τ)) 0 (fun l => Pi.single l 1) =
      derivAlong f (paramList F k) (ζ, 0) := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.iteratedFDeriv_parameters_eq <;> assumption
theorem abs_le_norm_mul_of_homogeneous {g : EuclideanSpace ℝ (Fin 3) → ℝ} {B : ℝ}
    (hg : ∀ (c : ℝ) (e : EuclideanSpace ℝ (Fin 3)), g (c • e) = c * g e)
    (h : ∀ e, ‖e‖ = 1 → |g e| ≤ B) (e : EuclideanSpace ℝ (Fin 3)) : |g e| ≤ ‖e‖ * B := by apply _root_.YangMills.Construction.Interpolation.AtTop.abs_le_norm_mul_of_homogeneous <;> assumption
abbrev bondDirection (k : ℕ) (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)) : JointSpace F k :=
  variableDirection (Fin k → ℝ) (Pi.single b e)
theorem bondDirection_smul (b : ↥(chordBonds (finiteCells F))) (c : ℝ) (e : EuclideanSpace ℝ (Fin 3)) :
    (bondDirection k b (c • e) : JointSpace F k) = c • bondDirection k b e := by
  simp [bondDirection, variableDirection, Pi.single_smul]
variable (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
  (η : StepVariable (finiteCells F)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
theorem abs_derivAlong_one_le (h : JointMixedDerivEqDerivAlong) (R : DerivAlongRules (JointSpace F k) ℝ) {B : ℝ}
    (hs : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0))
    (b : ↥(chordBonds (finiteCells F)))
    (hB : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → |jointMixedDeriv (l := 1) G η V ![b] ![u] c X| ≤ B)
    (e : EuclideanSpace ℝ (Fin 3)) :
    |derivAlong (rotatedEval G V c X) (bondDirection k b e :: paramList F k) (η, 0)| ≤ ‖e‖ * B := by
  refine abs_le_norm_mul_of_homogeneous
    (g := fun e => derivAlong (rotatedEval G V c X) (bondDirection k b e :: paramList F k) (η, 0)) ?_ ?_ e
  · intro r e
    have := R.smul_slot (rotatedEval G V c X) (η, 0) [] (paramList F k) r (bondDirection k b e)
      (by simpa [parameterDirections, parameterBasis, add_comm] using hs)
    simpa [bondDirection_smul] using this
  · intro u hu
    have e1 := (h F V G η k c X).2 1 ![b] ![u] (by simpa [add_comm] using hs)
    have := hB u hu
    rw [e1] at this
    simpa [pointDirections] using this
theorem abs_derivAlong_two_le (h : JointMixedDerivEqDerivAlong) (R : DerivAlongRules (JointSpace F k) ℝ) {B : ℝ}
    (hs : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0))
    (b b' : ↥(chordBonds (finiteCells F)))
    (hB : ∀ u u' : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → ‖u'‖ = 1 →
      |jointMixedDeriv (l := 2) G η V ![b', b] ![u', u] c X| ≤ B)
    (e e' : EuclideanSpace ℝ (Fin 3)) :
    |derivAlong (rotatedEval G V c X) (bondDirection k b' e' :: bondDirection k b e :: paramList F k) (η, 0)| ≤
      ‖e‖ * ‖e'‖ * B := by
  have hlen : ∀ (x y : JointSpace F k), ContDiffAt ℝ (((x :: y :: paramList F k).length : ℕ) : WithTop ℕ∞)
      (rotatedEval G V c X) (η, 0) := fun x y => by
    rw [show (x :: y :: paramList F k).length = k + 2 by simp [paramList_length]]; exact hs
  have hlen' : ∀ (x y : JointSpace F k), ContDiffAt ℝ ((([x] ++ y :: paramList F k).length : ℕ) : WithTop ℕ∞)
      (rotatedEval G V c X) (η, 0) := fun x y => by
    rw [show ([x] ++ y :: paramList F k).length = k + 2 by simp [paramList_length]]; exact hs
  have step : ∀ e' : EuclideanSpace ℝ (Fin 3), ‖e'‖ = 1 → ∀ e : EuclideanSpace ℝ (Fin 3),
      |derivAlong (rotatedEval G V c X) (bondDirection k b' e' :: bondDirection k b e :: paramList F k) (η, 0)| ≤
        ‖e‖ * B := by
    intro e' he'
    refine abs_le_norm_mul_of_homogeneous (g := fun e => derivAlong (rotatedEval G V c X)
      (bondDirection k b' e' :: bondDirection k b e :: paramList F k) (η, 0)) ?_ ?_
    · intro r e
      have := R.smul_slot (rotatedEval G V c X) (η, 0) [bondDirection k b' e'] (paramList F k) r
        (bondDirection k b e) (hlen' _ _)
      simpa [bondDirection_smul] using this
    · intro u hu
      have e1 := (h F V G η k c X).2 2 ![b', b] ![e', u] (by simpa [add_comm] using hs)
      have := hB u e' hu he'
      rw [e1] at this
      simpa [pointDirections, List.ofFn_succ] using this
  have := abs_le_norm_mul_of_homogeneous (g := fun e' => derivAlong (rotatedEval G V c X)
      (bondDirection k b' e' :: bondDirection k b e :: paramList F k) (η, 0))
    (B := ‖e‖ * B) (fun r e' => by
      have := R.smul_slot (rotatedEval G V c X) (η, 0) [] (bondDirection k b e :: paramList F k) r
        (bondDirection k b' e') (hlen _ _)
      simpa [bondDirection_smul] using this) (fun u hu => step u hu e) e'
  calc _ ≤ ‖e'‖ * (‖e‖ * B) := this
    _ = ‖e‖ * ‖e'‖ * B := by ring
theorem derivAlong_iteratedFDeriv_slice (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ)
    (ζ : StepVariable (finiteCells F)) (l : List (StepVariable (finiteCells F)))
    (hf : ContDiffAt ℝ ((l.length + k : ℕ) : WithTop ℕ∞) f (ζ, 0)) :
    derivAlong (fun ζ' => iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => f (ζ', τ)) 0 (fun l => Pi.single l 1)) l ζ =
      derivAlong f (l.map (fun w => ((w, 0) : JointSpace F k)) ++ paramList F k) (ζ, 0) := by
  have hk : ContDiffAt ℝ (k : WithTop ℕ∞) f (ζ, 0) :=
    hf.of_le (by exact_mod_cast (by omega : k ≤ l.length + k))
  have hc : Filter.Tendsto (fun ζ' : StepVariable (finiteCells F) => (ζ', (0 : Fin k → ℝ))) (𝓝 ζ) (𝓝 (ζ, 0)) :=
    (by fun_prop : Continuous fun ζ' : StepVariable (finiteCells F) => (ζ', (0 : Fin k → ℝ))).tendsto ζ
  have hev : ∀ᶠ ζ' in 𝓝 ζ, ContDiffAt ℝ (k : WithTop ℕ∞) f (ζ', 0) := hc.eventually (hk.eventually (by simp))
  have e1 : (fun ζ' => iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => f (ζ', τ)) 0 (fun l => Pi.single l 1)) =ᶠ[𝓝 ζ]
      fun ζ' => derivAlong f (paramList F k) (ζ', 0) := by
    filter_upwards [hev] with ζ' h'
    exact iteratedFDeriv_slice_eq_derivAlong h f ζ' h'
  rw [((h.1 _ ℝ).congr _ _ ζ l e1).self_of_nhds]
  have hs : ContDiffAt ℝ (l.length : WithTop ℕ∞) (derivAlong f (paramList F k))
      (((0 : StepVariable (finiteCells F)), (0 : Fin k → ℝ)) +
        ContinuousLinearMap.inl ℝ (StepVariable (finiteCells F)) (Fin k → ℝ) ζ) := by
    have : ((((0 : StepVariable (finiteCells F)), (0 : Fin k → ℝ)) : JointSpace F k) +
        ContinuousLinearMap.inl ℝ (StepVariable (finiteCells F)) (Fin k → ℝ) ζ) = (ζ, 0) := by simp
    rw [this]
    exact (h.1 _ ℝ).contDiffAt _ _ l.length (paramList F k) (by simpa [paramList_length] using hf)
  have e2 := h.2 (JointSpace F k) (StepVariable (finiteCells F)) ℝ (derivAlong f (paramList F k))
    (ContinuousLinearMap.inl ℝ _ _) ((0 : StepVariable (finiteCells F)), (0 : Fin k → ℝ)) ζ l hs
  have e3 : (fun t' : StepVariable (finiteCells F) => derivAlong f (paramList F k)
      (((0 : StepVariable (finiteCells F)), (0 : Fin k → ℝ)) + ContinuousLinearMap.inl ℝ _ _ t')) =
      fun ζ' => derivAlong f (paramList F k) (ζ', 0) := by
    funext t'
    simp
  rw [e3] at e2
  rw [e2, (h.1 _ ℝ).append]
  simp
  rfl
end DirectionalForms
section Dilation
variable {F : BlockFrame} {k : ℕ}
def dilation (S : Finset ↥(chordBonds (finiteCells F))) (G : AboveFrames F) : AboveFrames F :=
  fun η V => ∑ b ∈ S, bondPartialDeriv (fun ζ => G ζ V) b η (η b)
def paramFirstEval (G : AboveFrames F) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ := fun q => G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)
theorem rotatedEval_contDiffAt {n : WithTop ℕ∞} {G : AboveFrames F} {V : F.GaugeField F.top}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {η : StepVariable (finiteCells F)}
    (h : ContDiffAt ℝ n (paramFirstEval G V c X) (0, η)) :
    ContDiffAt ℝ n (rotatedEval G V c X) (η, 0) :=
  ContDiffAt.comp (g := paramFirstEval G V c X) (f := fun p : JointSpace F k => (p.2, p.1)) (η, 0) h
    (contDiff_snd.prodMk contDiff_fst).contDiffAt
theorem fderiv_slice_eq {Φ : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ} {τ : Fin k → ℝ}
    {ζ : StepVariable (finiteCells F)} (hd : DifferentiableAt ℝ Φ (τ, ζ)) (e : StepVariable (finiteCells F)) :
    fderiv ℝ (fun ζ' => Φ (τ, ζ')) ζ e = fderiv ℝ Φ (τ, ζ) (0, e) := by
  have := (HasFDerivAt.comp (g := Φ) (f := fun ζ' => (τ, ζ')) ζ hd.hasFDerivAt
    (hasFDerivAt_prodMk_right τ ζ)).fderiv
  change fderiv ℝ (Φ ∘ fun ζ' => (τ, ζ')) ζ e = _
  rw [this]
  simp
theorem contDiff_bondVariation_pair {n : WithTop ℕ∞} (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (b : ↥(chordBonds (finiteCells F))) :
    ContDiff ℝ n (fun q : P × StepVariable (finiteCells F) =>
      ((0 : P), (bondVariation b (q.2 b) : StepVariable (finiteCells F)))) := by
  have h1 : ContDiff ℝ n (fun q : P × StepVariable (finiteCells F) =>
      (bondVariation b (q.2 b) : StepVariable (finiteCells F))) :=
    (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b).contDiff.comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b).contDiff.comp
        contDiff_snd)
  exact contDiff_const.prodMk h1
theorem dilation_contDiffAt {G : AboveFrames F} {V : F.GaugeField F.top} {S : Finset ↥(chordBonds (finiteCells F))}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {η : StepVariable (finiteCells F)}
    (h : ContDiffAt ℝ 3 (paramFirstEval G V c X) (0, η)) :
    ContDiffAt ℝ 2 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      dilation S G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η) := by
  set Φ := paramFirstEval G V c X with hΦ
  have hev : ∀ᶠ q in 𝓝 ((0 : Fin k → ℝ), η), DifferentiableAt ℝ Φ q :=
    (h.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num)
  have e : (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      dilation S G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) =ᶠ[𝓝 (0, η)] fun q =>
        ∑ b ∈ S, fderiv ℝ Φ q (0, bondVariation b (q.2 b)) := by
    filter_upwards [hev] with q hq
    refine Finset.sum_congr rfl fun b _ => ?_
    exact fderiv_slice_eq (Φ := Φ) (τ := q.1) (ζ := q.2) hq _
  refine ContDiffAt.congr_of_eventuallyEq ?_ e
  have hfd : ContDiffAt ℝ 2 (fderiv ℝ Φ) (0, η) := h.fderiv_right (by norm_num)
  exact ContDiffAt.sum fun b _ => hfd.clm_apply (contDiff_bondVariation_pair (Fin k → ℝ) b).contDiffAt
theorem fderiv_slice_contDiffAt {Φ : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ}
    {ζ e : StepVariable (finiteCells F)} (h : ContDiffAt ℝ 3 Φ (0, ζ)) :
    ContDiffAt ℝ 2 (fun τ : Fin k → ℝ => fderiv ℝ (fun ζ' => Φ (τ, ζ')) ζ e) 0 := by
  have hc : Filter.Tendsto (fun τ : Fin k → ℝ => (τ, ζ)) (𝓝 0) (𝓝 (0, ζ)) :=
    (by fun_prop : Continuous fun τ : Fin k → ℝ => (τ, ζ)).tendsto 0
  have hev : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), DifferentiableAt ℝ Φ (τ, ζ) :=
    hc.eventually ((h.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num))
  have e1 : (fun τ : Fin k → ℝ => fderiv ℝ (fun ζ' => Φ (τ, ζ')) ζ e) =ᶠ[𝓝 0]
      fun τ => fderiv ℝ Φ (τ, ζ) (0, e) := by
    filter_upwards [hev] with τ hτ using fderiv_slice_eq hτ e
  refine ContDiffAt.congr_of_eventuallyEq ?_ e1
  have hfd : ContDiffAt ℝ 2 (fderiv ℝ Φ) (0, ζ) := h.fderiv_right (by norm_num)
  have hl : ContDiffAt ℝ 2 (fun τ : Fin k → ℝ => (τ, ζ)) 0 := (contDiff_id.prodMk contDiff_const).contDiffAt
  exact (ContDiffAt.comp (g := fderiv ℝ Φ) (f := fun τ : Fin k → ℝ => (τ, ζ)) 0 hfd hl).clm_apply contDiffAt_const
theorem bondDeriv_dilation (hTwo : Calculus.IteratedFDerivParamDiff) {G : AboveFrames F} {V : F.GaugeField F.top}
    {S : Finset ↥(chordBonds (finiteCells F))} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    {ζ : StepVariable (finiteCells F)} (hk : k ≤ 2) (h : ContDiffAt ℝ 3 (paramFirstEval G V c X) (0, ζ)) :
    bondDeriv (dilation S G ζ) V c X =
      ∑ b ∈ S, fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) ζ (bondVariation b (ζ b)) := by
  unfold bondDeriv
  have e1 : (fun τ : Fin k → ℝ => dilation S G ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) =
      fun τ => ∑ b ∈ S, (fun b τ => fderiv ℝ (fun ζ' => paramFirstEval G V c X (τ, ζ')) ζ
        (bondVariation b (ζ b))) b τ := rfl
  rw [e1, iteratedFDeriv_finsetSum_apply S k _ 0
    (fun b _ => (fderiv_slice_contDiffAt h).of_le (by exact_mod_cast hk))]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact ((hTwo (Fin k → ℝ) (StepVariable (finiteCells F)) k (paramFirstEval G V c X) ζ (fun l => Pi.single l 1)
    (h.of_le (by exact_mod_cast (by omega : k + 1 ≤ 3)))).2 _).symm
theorem fderiv_bondDeriv_dilation (hTwo : Calculus.IteratedFDerivParamDiff)
    (hSl : SmoothSlices.IteratedFDerivSlices)
    {G : AboveFrames F} {V : F.GaugeField F.top} {S : Finset ↥(chordBonds (finiteCells F))}
    {c : Fin k → F.Site F.top × Fin 4}
    {X : Fin k → imaginaryQuaternions} {η : StepVariable (finiteCells F)} (hk : k ≤ 1)
    (hnear : ∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ 3 (paramFirstEval G V c X) (0, ζ)) (e : StepVariable (finiteCells F)) :
    fderiv ℝ (fun ζ => bondDeriv (dilation S G ζ) V c X) η e =
      ∑ b ∈ S, (fderiv ℝ (fun ζ => fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) ζ (bondVariation b (η b))) η e +
        fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) η (bondVariation b (e b))) := by
  set g : StepVariable (finiteCells F) → ℝ := fun ζ' => bondDeriv (G ζ') V c X with hg
  have h0 := hnear.self_of_nhds
  have hg2 : ContDiffAt ℝ 2 g η := by
    have := hSl.2.1 (Fin k → ℝ) (StepVariable (finiteCells F)) (paramFirstEval G V c X) k 2
      (fun l => Pi.single l 1) η (h0.of_le (by exact_mod_cast (by omega : 2 + k ≤ 3)))
    exact_mod_cast this
  have hL : ContDiffAt ℝ 1 (fderiv ℝ g) η := hg2.fderiv_right (by norm_num)
  have hLd : DifferentiableAt ℝ (fderiv ℝ g) η := hL.differentiableAt (by norm_num)
  have ev : (fun ζ => bondDeriv (dilation S G ζ) V c X) =ᶠ[𝓝 η] fun ζ =>
      ∑ b ∈ S, fderiv ℝ g ζ (bondVariation b (ζ b)) := by
    filter_upwards [hnear] with ζ hζ using bondDeriv_dilation hTwo (by omega) hζ
  rw [ev.fderiv_eq]
  let π : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) →L[ℝ] StepVariable (finiteCells F) :=
    fun b =>
      (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b)
  have hπ : ∀ (b) (ζ : StepVariable (finiteCells F)),
      (bondVariation b (ζ b) : StepVariable (finiteCells F)) = π b ζ := fun b ζ => rfl
  have ht : ∀ b, HasFDerivAt (fun ζ => fderiv ℝ g ζ (π b ζ)) _ η := fun b =>
    hLd.hasFDerivAt.clm_apply (π b).hasFDerivAt
  simp only [hπ]
  rw [(HasFDerivAt.fun_sum fun b _ => ht b).fderiv, _root_.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h2 := (hLd.hasFDerivAt.clm_apply (hasFDerivAt_const (π b η) η)).fderiv
  rw [h2]
  simp
  ring
theorem abs_bondDeriv_dilation_le (hTwo : Calculus.IteratedFDerivParamDiff) {G : AboveFrames F}
    {V : F.GaugeField F.top}
    {S : Finset ↥(chordBonds (finiteCells F))} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    {ζ : StepVariable (finiteCells F)} (hk : k ≤ 2) (h : ContDiffAt ℝ 3 (paramFirstEval G V c X) (0, ζ))
    (a : ↥(chordBonds (finiteCells F)) → ℝ)
    (ha : ∀ b ∈ S, ∀ e : BondVector,
      |fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) ζ (bondVariation b e)| ≤ ‖e‖ * a b) :
    |bondDeriv (dilation S G ζ) V c X| ≤ ∑ b ∈ S, ‖ζ b‖ * a b := by
  rw [bondDeriv_dilation hTwo hk h]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hb => ha b hb _)
theorem bondGradNorm_dilation_le (hTwo : Calculus.IteratedFDerivParamDiff)
    (hSl : SmoothSlices.IteratedFDerivSlices)
    {G : AboveFrames F} {V : F.GaugeField F.top} {S : Finset ↥(chordBonds (finiteCells F))}
    {c : Fin k → F.Site F.top × Fin 4}
    {X : Fin k → imaginaryQuaternions} {η : StepVariable (finiteCells F)} (hk : k ≤ 1)
    (hnear : ∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ 3 (paramFirstEval G V c X) (0, ζ)) (b₀ : ↥(chordBonds (finiteCells F)))
    (a₁ : ℝ) (a₂ : ↥(chordBonds (finiteCells F)) → ℝ) (ha₁ : 0 ≤ a₁) (ha₂ : ∀ b, 0 ≤ a₂ b)
    (h₁ : b₀ ∈ S → ∀ e : BondVector,
      |fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) η (bondVariation b₀ e)| ≤ ‖e‖ * a₁)
    (h₂ : ∀ b ∈ S, ∀ e e' : BondVector,
      |fderiv ℝ (fun ζ => fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) ζ (bondVariation b e)) η
        (bondVariation b₀ e')| ≤ ‖e‖ * ‖e'‖ * a₂ b) :
    bondGradNorm (fun ζ => bondDeriv (dilation S G ζ) V c X) b₀ η ≤ ∑ b ∈ S, ‖η b‖ * a₂ b + a₁ := by
  classical
  have hM : 0 ≤ ∑ b ∈ S, ‖η b‖ * a₂ b + a₁ :=
    add_nonneg (Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (ha₂ b)) ha₁
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun e' => ?_
  show |fderiv ℝ (fun ζ => bondDeriv (dilation S G ζ) V c X) η (bondVariation b₀ e')| ≤ _
  rw [fderiv_bondDeriv_dilation hTwo hSl hk hnear, Finset.sum_add_distrib]
  have hB : ∑ b ∈ S, fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) η
        (bondVariation b ((bondVariation b₀ e' : StepVariable (finiteCells F)) b)) =
      if b₀ ∈ S then fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) η (bondVariation b₀ e') else 0 := by
    have hz : ∀ b ∈ S, fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) η
          (bondVariation b ((bondVariation b₀ e' : StepVariable (finiteCells F)) b)) =
        if b = b₀ then fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) η (bondVariation b₀ e') else 0 := by
      intro b _
      by_cases hb : b = b₀
      · subst hb
        simp [bondVariation]
      · simp [bondVariation, hb]
    rw [Finset.sum_congr rfl hz, Finset.sum_ite_eq' S b₀]
  rw [hB]
  have hA : |∑ b ∈ S, fderiv ℝ (fun ζ => fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) ζ
        (bondVariation b (η b))) η (bondVariation b₀ e')| ≤
      (∑ b ∈ S, ‖η b‖ * a₂ b) * ‖e'‖ := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hb => ?_)
    refine (h₂ b hb _ _).trans (le_of_eq ?_)
    ring
  have hC : |if b₀ ∈ S then fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) η (bondVariation b₀ e') else 0| ≤
      a₁ * ‖e'‖ := by
    split_ifs with hb
    · refine (h₁ hb e').trans (le_of_eq ?_)
      ring
    · simp only [abs_zero]
      positivity
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hA hC
    _ = _ := by ring
end Dilation
section Remainders
variable {F : BlockFrame} {k : ℕ}
theorem abs_fderiv_bondDeriv_le (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    {G : AboveFrames F} {V : F.GaugeField F.top} {c : Fin k → F.Site F.top × Fin 4}
    {X : Fin k → imaginaryQuaternions}
    {ζ : StepVariable (finiteCells F)}
    (hs : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (ζ, 0))
    (b : ↥(chordBonds (finiteCells F))) {B : ℝ}
    (hB : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → |jointMixedDeriv (l := 1) G ζ V ![b] ![u] c X| ≤ B)
    (e : BondVector) :
    |fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) ζ (bondVariation b e)| ≤ ‖e‖ * B := by
  have h1 := derivAlong_iteratedFDeriv_slice hL (rotatedEval G V c X) ζ [bondVariation b e]
    (by simpa [add_comm] using hs)
  have h2 := abs_derivAlong_one_le G V ζ c X hA (hL.1 _ ℝ) hs b hB e
  have e1 : fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) ζ (bondVariation b e) =
      derivAlong (rotatedEval G V c X) (bondDirection k b e :: paramList F k) (ζ, 0) := h1
  rw [e1]
  exact h2
theorem abs_fderiv_fderiv_bondDeriv_le (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    {G : AboveFrames F} {V : F.GaugeField F.top} {c : Fin k → F.Site F.top × Fin 4}
    {X : Fin k → imaginaryQuaternions}
    {ζ : StepVariable (finiteCells F)}
    (hs : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (ζ, 0))
    (b b₀ : ↥(chordBonds (finiteCells F))) {B : ℝ}
    (hB : ∀ u u' : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → ‖u'‖ = 1 →
      |jointMixedDeriv (l := 2) G ζ V ![b₀, b] ![u', u] c X| ≤ B) (e e' : BondVector) :
    |fderiv ℝ (fun ζ' => fderiv ℝ (fun ζ'' => bondDeriv (G ζ'') V c X) ζ' (bondVariation b e)) ζ
      (bondVariation b₀ e')| ≤ ‖e‖ * ‖e'‖ * B := by
  have h1 := derivAlong_iteratedFDeriv_slice hL (rotatedEval G V c X) ζ
    [bondVariation b₀ e', bondVariation b e] (by simpa [add_comm] using hs)
  have h2 := abs_derivAlong_two_le G V ζ c X hA (hL.1 _ ℝ) hs b b₀ hB e e'
  have e1 : fderiv ℝ (fun ζ' => fderiv ℝ (fun ζ'' => bondDeriv (G ζ'') V c X) ζ' (bondVariation b e)) ζ
        (bondVariation b₀ e') =
      derivAlong (rotatedEval G V c X) (bondDirection k b₀ e' :: bondDirection k b e :: paramList F k) (ζ, 0) := h1
  rw [e1]
  exact h2
theorem HasRemainderBounds.mono {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x A A' : ℝ} {Y : F.Cell} {K : AboveFrames F}
    {V : F.GaugeField F.top}
    (hx : 0 ≤ x) (hAA : A ≤ A') (h : HasRemainderBounds T x A Y K V) : HasRemainderBounds T x A' Y K V := by
  refine ⟨h.smooth, fun k c X hk hX η hη => (h.deriv_le k c X hk hX η hη).trans ?_,
    fun k c X hk hX η b₀ hη => (h.gradNorm_le k c X hk hX η b₀ hη).trans ?_⟩
  · have h0 : 0 ≤ Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
        ∑ b : ↥(chordBonds (finiteCells F)),
          Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) * (‖η b‖ + x * ‖η b‖ ^ 3) := by
      positivity
    have := mul_le_mul_of_nonneg_right hAA h0
    simpa [mul_assoc] using this
  · have h0 : 0 ≤ Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
        Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b₀.1.1) Y : ℝ))) *
        (x * ∑ b : ↥(chordBonds (finiteCells F)),
          Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) * ‖η b‖ ^ 2 + 1) := by
      positivity
    have := mul_le_mul_of_nonneg_right hAA h0
    simpa [mul_assoc] using this
theorem HasRemainderBounds.finset_sum (hSl : SmoothSlices.IteratedFDerivSlices) {J : Type} (Js : Finset J)
    {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ}
    {A : J → ℝ} {Y : F.Cell} {K : J → AboveFrames F} {V : F.GaugeField F.top}
    (hρ : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius})
    (h : ∀ j ∈ Js, HasRemainderBounds T x (A j) Y (K j) V) :
    HasRemainderBounds T x (∑ j ∈ Js, A j) Y (fun η V' => ∑ j ∈ Js, K j η V') V := by
  classical
  have hslice : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (j : J), j ∈ Js →
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ContDiffAt ℝ 2 (fun τ : Fin k → ℝ => K j η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0 := fun c X j hj η hη =>
    ContDiffAt.comp (g := fun q : (Fin _ → ℝ) × StepVariable (finiteCells F) =>
        K j q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V))
      (f := fun τ => (τ, η)) 0 ((h j hj).smooth η _ c X hη) (contDiff_id.prodMk contDiff_const).contDiffAt
  have hder : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      bondDeriv (fun V' => ∑ j ∈ Js, K j η V') V c X = ∑ j ∈ Js, bondDeriv (K j η) V c X := by
    intro k c X hk η hη
    unfold bondDeriv
    exact iteratedFDeriv_finsetSum_apply Js k (fun j τ => K j η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0
      (fun j hj => (hslice c X j hj η hη).of_le (by exact_mod_cast hk)) _
  refine ⟨fun η k c X hη => ContDiffAt.sum fun j hj => (h j hj).smooth η k c X hη, fun k c X hk hX η hη => ?_,
    fun k c X hk hX η b₀ hη => ?_⟩
  · rw [hder c X hk η fun b => (hη b).le, Finset.sum_mul, Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j hj => (h j hj).deriv_le k c X hk hX η hη)
  · have hnear : ∀ᶠ ζ in 𝓝 η, ∀ b, ‖ζ b‖ < T.ballRadius := hρ.mem_nhds hη
    have ev : (fun ζ => bondDeriv (fun V' => ∑ j ∈ Js, K j ζ V') V c X) =ᶠ[𝓝 η] fun ζ =>
        ∑ j ∈ Js, bondDeriv (K j ζ) V c X := by
      filter_upwards [hnear] with ζ hζ using hder c X (by omega) ζ fun b => (hζ b).le
    have hd : ∀ j ∈ Js, HasFDerivAt (fun ζ => bondDeriv (K j ζ) V c X)
        (fderiv ℝ (fun ζ => bondDeriv (K j ζ) V c X) η) η := by
      intro j hj
      have := hSl.2.1 (Fin k → ℝ) (StepVariable (finiteCells F))
        (fun q => K j q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) k 1
        (fun l => Pi.single l 1) η (((h j hj).smooth η k c X fun b => (hη b).le).of_le
          (by exact_mod_cast (by omega : 1 + k ≤ 2)))
      exact (ContDiffAt.differentiableAt this (by norm_num)).hasFDerivAt
    unfold bondGradNorm
    rw [ev.fderiv_eq, (HasFDerivAt.fun_sum hd).fderiv]
    have e1 : (∑ j ∈ Js, fderiv ℝ (fun ζ => bondDeriv (K j ζ) V c X) η).comp
          (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b₀) =
        ∑ j ∈ Js, (fderiv ℝ (fun ζ => bondDeriv (K j ζ) V c X) η).comp
          (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b₀) :=
      ContinuousLinearMap.ext fun e => by simp
    rw [e1]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj => (h j hj).gradNorm_le k c X hk hX η b₀ hη
structure HasDilationBounds (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (A : ℝ) (Y : F.Cell) (S : Finset ↥(chordBonds (finiteCells F)))
    (G : AboveFrames F) (V : F.GaugeField F.top) : Prop where
  smooth : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)),
    (∀ b, ‖η b‖ ≤ T.ballRadius) → ContDiffAt ℝ 3 (paramFirstEval G V c X) (0, η)
  fderiv_le : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
    AreUnitVectors X →
    ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) → ∀ b ∈ S, ∀ e : BondVector,
      |fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) η (bondVariation b e)| ≤
        ‖e‖ * (A * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
          Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))))
  fderiv_fderiv_le : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 1 →
    AreUnitVectors X →
    ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) → ∀ b ∈ S,
      ∀ (b₀ : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      |fderiv ℝ (fun ζ => fderiv ℝ (fun ζ' => bondDeriv (G ζ') V c X) ζ (bondVariation b e)) η
        (bondVariation b₀ e')| ≤
        ‖e‖ * ‖e'‖ * (A * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
          Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b₀.1.1) Y : ℝ))) *
          Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))))
theorem HasDilationBounds.hasRemainderBounds (hTwo : Calculus.IteratedFDerivParamDiff)
    (hSl : SmoothSlices.IteratedFDerivSlices)
    {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x A S₀ : ℝ} {Y : F.Cell} {S : Finset ↥(chordBonds (finiteCells F))} {G : AboveFrames F}
    {V : F.GaugeField F.top}
    (hx : 0 ≤ x) (hA : 0 ≤ A) (hκ : 0 ≤ T.κ) (hρ₀ : 0 ≤ T.ballRadius)
    (hρ : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius})
    (hS₀ : ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤ S₀)
    (h : HasDilationBounds T A Y S G V) :
    HasRemainderBounds T x (A * (1 + T.ballRadius * S₀)) Y (dilation S G) V := by
  classical
  set w : ↥(chordBonds (finiteCells F)) → ℝ := fun b =>
    Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) with hw
  have hw0 : ∀ b, 0 ≤ w b := fun b => (Real.exp_pos _).le
  have hS0 : 0 ≤ S₀ := (Finset.sum_nonneg fun b _ => hw0 b).trans hS₀
  have hww : ∀ b, Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤ w b := fun b => by
    refine Real.exp_le_exp.2 ?_
    have : 0 ≤ T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ) := by positivity
    nlinarith
  refine ⟨fun η k c X hη => dilation_contDiffAt (h.smooth k c X η hη), fun k c X hk hX η hη => ?_,
    fun k c X hk hX η b₀ hη => ?_⟩
  · set E := Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have h1 := abs_bondDeriv_dilation_le (S := S) hTwo hk (h.smooth k c X η fun b => (hη b).le)
      (fun b => A * E * Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))))
      (fun b hb e => h.fderiv_le k c X hk hX η hη b hb e)
    refine h1.trans ?_
    have h2 : ∑ b ∈ S, ‖η b‖ * (A * E * Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))) ≤
        A * E * ∑ b, w b * (‖η b‖ + x * ‖η b‖ ^ 3) := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun b _ _ => by positivity).trans ?_
      refine Finset.sum_le_sum fun b _ => ?_
      have h3 : ‖η b‖ * Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤
          w b * (‖η b‖ + x * ‖η b‖ ^ 3) := by
        have h4 : ‖η b‖ ≤ ‖η b‖ + x * ‖η b‖ ^ 3 := by
          have : 0 ≤ x * ‖η b‖ ^ 3 := by positivity
          linarith
        calc _ = Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) * ‖η b‖ := by ring
          _ ≤ w b * ‖η b‖ := mul_le_mul_of_nonneg_right (hww b) (norm_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left h4 (hw0 b)
      calc _ = A * E * (‖η b‖ * Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
    refine h2.trans ?_
    have hsum0 : 0 ≤ ∑ b, w b * (‖η b‖ + x * ‖η b‖ ^ 3) := Finset.sum_nonneg fun b _ => by
      have := hw0 b
      positivity
    have hle : A ≤ A * (1 + T.ballRadius * S₀) := by
      have : 0 ≤ T.ballRadius * S₀ := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hE0) hsum0
  · set E := Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    set e₀ := Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b₀.1.1) Y : ℝ))) with he₀
    have hnear : ∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ 3 (paramFirstEval G V c X) (0, ζ) := by
      filter_upwards [hρ.mem_nhds hη] with ζ hζ using h.smooth k c X ζ fun b => (hζ b).le
    have h1 := bondGradNorm_dilation_le (S := S) hTwo hSl hk hnear b₀ (A * E * e₀) (fun b => A * E * e₀ * w b)
      (by positivity) (fun b => by have := hw0 b; positivity)
      (fun hb e => h.fderiv_le k c X (by omega) hX η hη b₀ hb e)
      (fun b hb e e' => h.fderiv_fderiv_le k c X hk hX η hη b hb b₀ e e')
    refine h1.trans ?_
    have h2 : ∑ b ∈ S, ‖η b‖ * (A * E * e₀ * w b) ≤ A * E * e₀ * (T.ballRadius * S₀) := by
      have h3 : ∑ b ∈ S, ‖η b‖ * w b ≤ T.ballRadius * S₀ := by
        refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          fun b _ _ => mul_nonneg (norm_nonneg _) (hw0 b)).trans ?_
        calc ∑ b, ‖η b‖ * w b ≤ ∑ b, T.ballRadius * w b :=
              Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hη b).le (hw0 b)
          _ = T.ballRadius * ∑ b, w b := by rw [Finset.mul_sum]
          _ ≤ T.ballRadius * S₀ := mul_le_mul_of_nonneg_left hS₀ hρ₀
      calc ∑ b ∈ S, ‖η b‖ * (A * E * e₀ * w b) = A * E * e₀ * ∑ b ∈ S, ‖η b‖ * w b := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun b _ => by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hq : 0 ≤ x * ∑ b, w b * ‖η b‖ ^ 2 :=
      mul_nonneg hx (Finset.sum_nonneg fun b _ => mul_nonneg (hw0 b) (by positivity))
    calc ∑ b ∈ S, ‖η b‖ * (A * E * e₀ * w b) + A * E * e₀ ≤ A * E * e₀ * (T.ballRadius * S₀) + A * E * e₀ := by
          linarith
      _ = A * (1 + T.ballRadius * S₀) * E * e₀ * 1 := by ring
      _ ≤ A * (1 + T.ballRadius * S₀) * E * e₀ * (x * ∑ b, w b * ‖η b‖ ^ 2 + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
end Remainders
section Displacements
variable {F : BlockFrame}
theorem cellSupDist_le_cellSetDiameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
theorem bondSpan_le_cellSetDiameter {k : ℕ} {P : Finset F.Cell} {Y : F.Cell} {c : Fin k → F.Site F.top × Fin 4}
    (hY : Y ∈ P) (hc : ∀ l, (c l).1 ∈ P) : bondSpan Y c ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.bondSpan_le_cellSetDiameter <;> assumption
theorem nonempty_chordBonds (hB : SiteDecomposition) (hC : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) : Nonempty ↥(chordBonds (finiteCells F)) := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.nonempty_chordBonds <;> assumption
def lowOrderSum (D : ℕ → ℕ → ℝ) : ℝ := ∑ l ∈ Finset.range 5, ∑ j ∈ Finset.range 5, D l j
theorem lowOrderSum_nonneg {D : ℕ → ℕ → ℝ} (h : ∀ l j, 0 < D l j) : 0 ≤ lowOrderSum D :=
  Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun j _ => (h l j).le
theorem le_lowOrderSum {D : ℕ → ℕ → ℝ} (h : ∀ l j, 0 < D l j) (l j : ℕ) (hl : l ≤ 4) (hj : j ≤ 4) :
    D l j ≤ lowOrderSum D := by
  have h1 : D l j ≤ ∑ j ∈ Finset.range 5, D l j :=
    Finset.single_le_sum (f := fun j => D l j) (fun j _ => (h l j).le) (Finset.mem_range.2 (by omega))
  have h2 : ∑ j ∈ Finset.range 5, D l j ≤ lowOrderSum D :=
    Finset.single_le_sum (f := fun l => ∑ j ∈ Finset.range 5, D l j)
      (fun l _ => Finset.sum_nonneg fun j _ => (h l j).le) (Finset.mem_range.2 (by omega))
  exact h1.trans h2
theorem jointDisplacement_contDiffAt {l j : ℕ} {n : WithTop ℕ∞} {G : AboveFrames F} {V : F.GaugeField F.top}
    {η : StepVariable (finiteCells F)}
    (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions)
    (h : ContDiffAt ℝ n (rotatedEval G V c X) (η, 0)) :
    ContDiffAt ℝ n (jointDisplacement G η V b u c X) 0 := by
  classical
  let m : (Fin (l + j) → ℝ) → JointSpace F j := fun τ =>
    (displacedPoint η b u fun i => τ (Fin.castAdd j i), fun i => τ (Fin.natAdd l i))
  have hm : ContDiff ℝ n m := by
    refine ContDiff.prodMk ?_ (contDiff_pi.2 fun i => contDiff_apply _ _ _)
    unfold displacedPoint
    refine contDiff_const.add (ContDiff.sum fun i _ => ?_)
    refine contDiff_pi.2 fun b' => ?_
    by_cases hb : b' = b i
    · subst hb
      simp only [Pi.single_eq_same]
      exact (contDiff_apply _ _ _).smul contDiff_const
    · simp only [Pi.single_eq_of_ne hb]
      exact contDiff_const
  have h0 : m 0 = (η, 0) := by
    simp only [m, displacedPoint]
    ext1
    · simp
    · rfl
  exact ContDiffAt.comp (g := rotatedEval G V c X) (f := m) 0 (by rw [h0]; exact h) hm.contDiffAt
theorem jointMixedDeriv_finset_sum {l k : ℕ} {J : Type} (Js : Finset J) (G : J → AboveFrames F)
    {V : F.GaugeField F.top}
    {η : StepVariable (finiteCells F)} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (h : ∀ j ∈ Js, ContDiffAt ℝ ((l + k : ℕ) : WithTop ℕ∞) (jointDisplacement (G j) η V b u c X) 0) :
    jointMixedDeriv (fun ζ V' => ∑ j ∈ Js, G j ζ V') η V b u c X =
      ∑ j ∈ Js, jointMixedDeriv (G j) η V b u c X :=
  iteratedFDeriv_finsetSum_apply Js (l + k) (fun j => jointDisplacement (G j) η V b u c X) 0 h _
end Displacements
end ResponseInTheExpansion.RemainderCalculus
end YangMills.Construction
end
