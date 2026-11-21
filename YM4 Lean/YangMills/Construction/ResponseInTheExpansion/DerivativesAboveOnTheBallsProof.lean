import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.DerivativesAboveOnTheBalls
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativeInTheTopAlongASegmentProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames Estimates Interpolation SmoothSlices Topology
open BlockAverages hiding bondSpread
namespace ResponseInTheExpansion
variable {F : BlockFrame}
namespace MixedDerivativeSteps
def bondFieldEmbedding {k : ℕ} (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)) :
    (Fin (1 + k) → ℝ) →L[ℝ] (Fin k → ℝ) × StepVariable (finiteCells F) :=
  (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (1 + k) => ℝ) (Fin.natAdd 1 i)).prod
    ((ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => EuclideanSpace ℝ (Fin 3)) b).comp
      ((ContinuousLinearMap.toSpanSingleton ℝ u).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (1 + k) => ℝ) (Fin.castAdd k 0))))
theorem bondFieldEmbedding_apply {k : ℕ} (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3))
    (σ : Fin (1 + k) → ℝ) :
    bondFieldEmbedding b u σ = (fun i => σ (Fin.natAdd 1 i), Pi.single b (σ (Fin.castAdd k 0) • u)) := rfl
theorem jointDisplacement_single_eq {k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (ζ : StepVariable (finiteCells F))
    (V : F.GaugeField F.top) (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    jointDisplacement G ζ V ![b] ![u] c X = fun σ =>
      (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread c X q.1) V))
        ((0, ζ) + bondFieldEmbedding b u σ) := by
  funext σ
  unfold jointDisplacement displacedPoint
  rw [bondFieldEmbedding_apply]
  simp
theorem fderiv_fieldDeriv_single (hS : IteratedFDerivSlices) {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hG : JointlyContDiffOnBalls ρ V G) {k : ℕ} (hk : k ≤ 2)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {ζ : StepVariable (finiteCells F)}
    (hζ : ∀ b, ‖ζ b‖ ≤ ρ)
    (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fieldDeriv G V c X) ζ (Pi.single b u) = jointMixedDeriv G ζ V ![b] ![u] c X := by apply _root_.YangMills.Construction.FieldDerivSegment.fderiv_fieldDeriv_single <;> assumption
def twoBondEmbedding (b b' : ↥(chordBonds (finiteCells F))) (u u' : EuclideanSpace ℝ (Fin 3)) :
    (Fin (2 + 0) → ℝ) →L[ℝ] StepVariable (finiteCells F) :=
  (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => EuclideanSpace ℝ (Fin 3)) b).comp
      ((ContinuousLinearMap.toSpanSingleton ℝ u).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 + 0) => ℝ) 0)) +
    (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => EuclideanSpace ℝ (Fin 3)) b').comp
      ((ContinuousLinearMap.toSpanSingleton ℝ u').comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 + 0) => ℝ) 1))
theorem twoBondEmbedding_apply (b b' : ↥(chordBonds (finiteCells F))) (u u' : EuclideanSpace ℝ (Fin 3))
    (σ : Fin (2 + 0) → ℝ) :
    twoBondEmbedding b b' u u' σ = Pi.single b (σ 0 • u) + Pi.single b' (σ 1 • u') := rfl
theorem jointDisplacement_pair_eq (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (ζ : StepVariable (finiteCells F)) (V : F.GaugeField F.top)
    (b b' : ↥(chordBonds (finiteCells F))) (u u' : EuclideanSpace ℝ (Fin 3)) :
    jointDisplacement G ζ V ![b, b'] ![u, u'] (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions) =
      fun z => G (ζ + twoBondEmbedding b b' u u' z) V := by
  classical
  funext z
  simp only [jointDisplacement, displacedPoint, twoBondEmbedding_apply]
  rw [show bondSpread (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)
      (fun i => z (Fin.natAdd 2 i)) =
    bondSpread (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) 0 from by
      funext y i
      simp [bondSpread]]
  rw [leftTranslate_bondSpread_zero]
  simp [Fin.sum_univ_two]
theorem contDiffAt_jointDisplacement_single {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hG : JointlyContDiffOnBalls ρ V G)
    {k : ℕ} (hk : k ≤ 2) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    {ζ : StepVariable (finiteCells F)}
    (hζ : ∀ b, ‖ζ b‖ ≤ ρ) (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)) :
    ContDiffAt ℝ (1 + k : ℕ) (jointDisplacement G ζ V ![b] ![u] c X) 0 := by
  rw [jointDisplacement_single_eq]
  have hJ := hG k c X ζ hζ
  have hJ' : ContDiffAt ℝ (1 + k : ℕ)
      (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread c X q.1) V))
      ((0, ζ) + bondFieldEmbedding b u 0) := by
    rw [map_zero, add_zero]
    exact ContDiffAt.of_le hJ (by exact_mod_cast (by omega : 1 + k ≤ 3))
  have hm : ContDiffAt ℝ (1 + k : ℕ)
      (fun σ : Fin (1 + k) → ℝ => ((0, ζ) : (Fin k → ℝ) × StepVariable (finiteCells F)) + bondFieldEmbedding b u σ) 0 :=
    contDiffAt_const.add (bondFieldEmbedding b u).contDiff.contDiffAt
  exact ContDiffAt.comp (0 : Fin (1 + k) → ℝ) hJ' hm
theorem contDiffAt_jointDisplacement_pair {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (hA : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ ρ) → ContDiffAt ℝ 3 (fun ζ' => G ζ' V) ζ)
    {ζ : StepVariable (finiteCells F)} (hζ : ∀ b, ‖ζ b‖ ≤ ρ) (b b' : ↥(chordBonds (finiteCells F)))
    (u u' : EuclideanSpace ℝ (Fin 3)) :
    ContDiffAt ℝ (2 + 0 : ℕ) (jointDisplacement G ζ V ![b, b'] ![u, u'] (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
      (Fin.elim0 : Fin 0 → imaginaryQuaternions)) 0 := by
  rw [jointDisplacement_pair_eq]
  have hJ' : ContDiffAt ℝ (2 + 0 : ℕ) (fun ζ' => G ζ' V) (ζ + twoBondEmbedding b b' u u' 0) := by
    have e : ζ + twoBondEmbedding b b' u u' 0 = ζ := by simp
    rw [e]
    exact ContDiffAt.of_le (hA ζ hζ) (by norm_num)
  have hm : ContDiffAt ℝ (2 + 0 : ℕ) (fun σ : Fin (2 + 0) → ℝ => ζ + twoBondEmbedding b b' u u' σ) 0 :=
    contDiffAt_const.add (twoBondEmbedding b b' u u').contDiff.contDiffAt
  exact ContDiffAt.comp (0 : Fin (2 + 0) → ℝ) hJ' hm
theorem contDiffAt_fieldSlice {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hG : JointlyContDiffOnBalls ρ V G)
    (ζ : StepVariable (finiteCells F)) (hζ : ∀ b, ‖ζ b‖ ≤ ρ) : ContDiffAt ℝ 3 (fun ζ' => G ζ' V) ζ := by
  have h := hG 0 Fin.elim0 Fin.elim0 ζ hζ
  have hc : ContDiffAt ℝ 3 (fun ζ' : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), ζ')) ζ :=
    contDiffAt_const.prodMk contDiffAt_id
  have := ContDiffAt.comp ζ h hc
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ζ' => ?_)
  simp only [Function.comp]
  rw [leftTranslate_bondSpread_zero]
end MixedDerivativeSteps
open MixedDerivativeSteps in
theorem mixedDerivativesOnBalls (hS : IteratedFDerivSlices) :
    mixedDerivativesOnBallsStatement := by
  classical
  intro F ρ V
  refine ⟨⟨fun α S G k c X ζ b u hG hk hζ => ?_, fun α S G ζ b b' u u' hG hζ => ?_⟩, fun G hG => ?_⟩
  · unfold jointMixedDeriv
    have e : jointDisplacement (fun ζ' V' => ∑ a ∈ S, G a ζ' V') ζ V ![b] ![u] c X =
        fun τ => ∑ a ∈ S, jointDisplacement (G a) ζ V ![b] ![u] c X τ := rfl
    rw [e]
    exact iteratedFDeriv_finsetSum_apply S (1 + k) _ 0
      (fun a ha => contDiffAt_jointDisplacement_single (hG a ha) hk c X hζ b u) _
  · unfold jointMixedDeriv
    have e : jointDisplacement (fun ζ' V' => ∑ a ∈ S, G a ζ' V') ζ V ![b, b'] ![u, u']
        (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) =
        fun τ => ∑ a ∈ S, jointDisplacement (G a) ζ V ![b, b'] ![u, u']
          (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) τ := rfl
    rw [e]
    exact iteratedFDeriv_finsetSum_apply S (2 + 0) _ 0
      (fun a ha => contDiffAt_jointDisplacement_pair (contDiffAt_fieldSlice (hG a ha)) hζ b b' u u') _
  have hval : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k = 0 →
      fieldDeriv G V c X = fun ζ => G ζ V := by
    intro k c X hk
    subst hk
    funext ζ
    simp only [fieldDeriv, bondDeriv, iteratedFDeriv_zero_apply]
    rw [leftTranslate_bondSpread_zero]
  have hpoint : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ ρ) → ContDiffAt ℝ 3 (fun ζ' => G ζ' V) ζ := contDiffAt_fieldSlice hG
  have halong : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (ζ : StepVariable (finiteCells F)), k ≤ 2 →
      (∀ b, ‖ζ b‖ ≤ ρ) → ContDiffAt ℝ 1 (fieldDeriv G V c X) ζ := by
    intro k c X ζ hk hζ
    have h3 := hG k c X ζ hζ
    exact_mod_cast hS.2.1 (Fin k → ℝ) (StepVariable (finiteCells F))
      (fun q => G q.2 (leftTranslate (bondSpread c X q.1) V)) k 1 (fun l => Pi.single l 1) ζ
      (ContDiffAt.of_le h3 (by exact_mod_cast (by omega : 1 + k ≤ 3)))
  have hfirst : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (ζ : StepVariable (finiteCells F))
      (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)), k ≤ 2 → (∀ b, ‖ζ b‖ ≤ ρ) →
      fderiv ℝ (fieldDeriv G V c X) ζ (Pi.single b u) = jointMixedDeriv G ζ V ![b] ![u] c X :=
    fun c X ζ b u hk hζ => fderiv_fieldDeriv_single hS hG hk c X hζ b u
  refine ⟨hval, hpoint, halong, hfirst, ?_, ?_, ?_⟩
  · intro ζ b b' u u' hζ
    have hA := hpoint ζ hζ
    set A : StepVariable (finiteCells F) → ℝ := fun ζ' => G ζ' V with hAdef
    have hA2 : ContDiffAt ℝ (2 : ℕ) A (ζ + twoBondEmbedding b b' u u' 0) := by
      rw [map_zero, add_zero]
      exact ContDiffAt.of_le hA (by norm_num)
    have h1 := hS.1 (StepVariable (finiteCells F)) (Fin (2 + 0) → ℝ) A (twoBondEmbedding b b' u u') ζ 0 2
      (fun i => Pi.single i 1) hA2
    have e1 : jointMixedDeriv G ζ V ![b, b'] ![u, u'] (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions) =
        iteratedFDeriv ℝ 2 (fun z => A (ζ + twoBondEmbedding b b' u u' z)) 0 (fun i => Pi.single i 1) := by
      unfold jointMixedDeriv
      have : jointDisplacement G ζ V ![b, b'] ![u, u'] (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
          (Fin.elim0 : Fin 0 → imaginaryQuaternions) =
          fun z => A (ζ + twoBondEmbedding b b' u u' z) := by
        funext z
        simp only [jointDisplacement, displacedPoint, hAdef, twoBondEmbedding_apply]
        rw [show bondSpread (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)
            (fun i => z (Fin.natAdd 2 i)) =
          bondSpread (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) 0 from by
            funext y i
            simp [bondSpread]]
        rw [leftTranslate_bondSpread_zero]
        simp [Fin.sum_univ_two]
      rw [this]
    rw [e1, h1, map_zero, add_zero, iteratedFDeriv_two_apply]
    simp only [twoBondEmbedding_apply]
    simp
  · intro k c X D ζ ζ' hk hD hζ hζ'
    set g := fieldDeriv G V c X with hg
    set d : StepVariable (finiteCells F) := ζ' - ζ with hd
    have hseg : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ b, ‖(ζ + v • d) b‖ ≤ ρ := fun v hv b => by
      have e : (ζ + v • d) b = (1 - v) • ζ b + v • ζ' b := by
        simp only [hd, Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
        module
      rw [e]
      calc ‖(1 - v) • ζ b + v • ζ' b‖ ≤ ‖(1 - v) • ζ b‖ + ‖v • ζ' b‖ := norm_add_le _ _
        _ = (1 - v) * ‖ζ b‖ + v * ‖ζ' b‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [hv.2]), Real.norm_of_nonneg hv.1]
        _ ≤ (1 - v) * ρ + v * ρ := by
          have h1 := hζ b
          have h2 := hζ' b
          have := hv.1
          have := hv.2
          nlinarith
        _ = ρ := by ring
    have hdiff : ∀ ξ : StepVariable (finiteCells F), (∀ b, ‖ξ b‖ ≤ ρ) → DifferentiableAt ℝ g ξ := fun ξ hξ =>
      (halong c X ξ hk hξ).differentiableAt (by simp)
    have hbound : ∀ ξ : StepVariable (finiteCells F), (∀ b, ‖ξ b‖ ≤ ρ) →
        ‖fderiv ℝ g ξ d‖ ≤ ∑ b, ‖d b‖ * D b := fun ξ hξ => by
      have hsum : d = ∑ b, Pi.single b (d b) := (Finset.univ_sum_single d).symm
      conv_lhs => rw [hsum, map_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      by_cases h0 : d b = 0
      · rw [h0]
        simp
      · have hn : ‖d b‖ ≠ 0 := norm_ne_zero_iff.mpr h0
        set u := ‖d b‖⁻¹ • d b with hu
        have hu1 : ‖u‖ = 1 := by
          rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
        have hdec : d b = ‖d b‖ • u := by
          rw [hu, smul_smul, mul_inv_cancel₀ hn, one_smul]
        have hsingle : (Pi.single b (d b) : StepVariable (finiteCells F)) = ‖d b‖ • Pi.single b u := by
          conv_lhs => rw [hdec]
          funext b'
          by_cases hb : b' = b
          · subst hb
            simp
          · simp [Pi.single_eq_of_ne hb]
        rw [hsingle, map_smul, norm_smul, norm_norm, hfirst c X ξ b u hk hξ, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hD ξ hξ b u hu1) (norm_nonneg _)
    have hder : ∀ v ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun v : ℝ => g (ζ + v • d)) (fderiv ℝ g (ζ + v • d) d) (Set.Icc (0 : ℝ) 1) v :=
      fun v hv => by
      have h1 : HasDerivAt (fun v : ℝ => ζ + v • d) ((1 : ℝ) • d) v :=
        ((hasDerivAt_id v).smul_const d).const_add ζ
      rw [one_smul] at h1
      exact ((hdiff _ (hseg v hv)).hasFDerivAt.comp_hasDerivAt v h1).hasDerivWithinAt
    have := norm_image_sub_le_of_norm_deriv_le_segment_01' hder
      (fun v hv => hbound _ (hseg v ⟨hv.1, hv.2.le⟩))
    have e2 : ζ + (1 : ℝ) • d = ζ' := by simp [hd]
    have e3 : ζ + (0 : ℝ) • d = ζ := by simp
    simp only [e2, e3, Real.norm_eq_abs] at this
    exact this
  · intro k c X ζ b D hk hD hζ hu
    unfold bondGradNorm
    refine ContinuousLinearMap.opNorm_le_bound _ hD fun v => ?_
    by_cases h0 : v = 0
    · subst h0
      simp
    · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      set u := ‖v‖⁻¹ • v with hud
      have hu1 : ‖u‖ = 1 := by
        rw [hud, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have hdec : v = ‖v‖ • u := by
        rw [hud, smul_smul, mul_inv_cancel₀ hn, one_smul]
      rw [hdec, map_smul, norm_smul, norm_norm, mul_comm, ← hdec]
      have e4 : ((fderiv ℝ (fieldDeriv G V c X) ζ).comp
          (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b)) u =
          fderiv ℝ (fieldDeriv G V c X) ζ (Pi.single b u) := rfl
      rw [e4, hfirst c X ζ b u hk hζ, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hu u hu1) (norm_nonneg _)
end ResponseInTheExpansion
end YangMills.Construction
end
