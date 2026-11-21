import YangMills.Construction.SummableBoundsOfTheFlow.DerivativeInTheTopAlongASegment
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import Mathlib
set_option autoImplicit false
noncomputable section
open Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation Estimates SmoothSlices
namespace FieldDerivSegment
variable {F : BlockFrame}
theorem iteratedFDeriv_order_cast {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n m : ℕ} (hnm : n = m)
    (f : E → ℝ) (x : E) (v : Fin n → E) :
    iteratedFDeriv ℝ n f x v = iteratedFDeriv ℝ m f x (fun i => v (Fin.cast hnm.symm i)) := by
  subst hnm
  rfl
def bondLineEmbedding {k : ℕ} (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)) :
    (Fin (1 + k) → ℝ) →L[ℝ] (Fin k → ℝ) × StepVariable (finiteCells F) :=
  (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (1 + k) => ℝ) (Fin.natAdd 1 i)).prod
    ((ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => EuclideanSpace ℝ (Fin 3)) b).comp
      ((ContinuousLinearMap.toSpanSingleton ℝ u).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (1 + k) => ℝ) (Fin.castAdd k 0))))
theorem bondLineEmbedding_apply {k : ℕ} (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3))
    (σ : Fin (1 + k) → ℝ) :
    bondLineEmbedding b u σ = (fun i => σ (Fin.natAdd 1 i), Pi.single b (σ (Fin.castAdd k 0) • u)) := rfl
theorem jointDisplacement_eq_comp {k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (ζ : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (b : ↥(chordBonds (finiteCells F)))
    (u : EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    jointDisplacement G ζ V ![b] ![u] c X = fun σ =>
      (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V))
        ((0, ζ) + bondLineEmbedding b u σ) := by
  funext σ
  unfold jointDisplacement displacedPoint
  rw [bondLineEmbedding_apply]
  simp
theorem fderiv_fieldDeriv_single (hS : IteratedFDerivSlices) {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hG : JointlyContDiffOnBalls ρ V G) {k : ℕ}
    (hk : k ≤ 2) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    {ζ : StepVariable (finiteCells F)} (hζ : ∀ b, ‖ζ b‖ ≤ ρ)
    (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fieldDeriv G V c X) ζ (Pi.single b u) = jointMixedDeriv G ζ V ![b] ![u] c X := by
  set J : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ :=
    fun q => G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V) with hJdef
  have hJ : ContDiffAt ℝ 3 J (0, ζ) := hG k c X ζ hζ
  have hJk : ContDiffAt ℝ (k + 1 : ℕ) J (0, ζ) := ContDiffAt.of_le hJ (by exact_mod_cast (by omega : k + 1 ≤ 3))
  have hJk' : ContDiffAt ℝ (1 + k : ℕ) J ((0, ζ) + bondLineEmbedding b u 0) := by
    rw [map_zero, add_zero]
    exact ContDiffAt.of_le hJ (by exact_mod_cast (by omega : 1 + k ≤ 3))
  have h1 := hS.2.2 (Fin k → ℝ) (StepVariable (finiteCells F)) J k (fun l => Pi.single l 1) ζ (Pi.single b u) hJk
  have h2 := hS.1 ((Fin k → ℝ) × StepVariable (finiteCells F)) (Fin (1 + k) → ℝ) J (bondLineEmbedding b u) (0, ζ) 0
    (1 + k) (fun i => Pi.single i 1) hJk'
  have e1 : jointMixedDeriv G ζ V ![b] ![u] c X =
      iteratedFDeriv ℝ (1 + k) (fun σ => J ((0, ζ) + bondLineEmbedding b u σ)) 0 (fun i => Pi.single i 1) := by
    unfold jointMixedDeriv
    rw [jointDisplacement_eq_comp]
  rw [e1, h2, map_zero, add_zero, iteratedFDeriv_order_cast (Nat.add_comm 1 k)]
  refine h1.trans ?_
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Fin.cons_zero, bondLineEmbedding_apply]
    have e0 : Fin.cast (Nat.add_comm 1 k).symm (0 : Fin (k + 1)) = Fin.castAdd k 0 := Fin.ext rfl
    refine Prod.ext ?_ ?_
    · funext l
      rw [e0]
      have : Fin.natAdd 1 l ≠ Fin.castAdd k 0 := fun h => by
        have := congrArg Fin.val h
        simp at this
      simp [this]
    · rw [e0]
      simp
  · rw [Fin.cons_succ, bondLineEmbedding_apply]
    have e0 : Fin.cast (Nat.add_comm 1 k).symm (Fin.succ i) = Fin.natAdd 1 i := Fin.ext (by simp; omega)
    refine Prod.ext ?_ ?_
    · funext l
      rw [e0]
      by_cases hl : l = i
      · subst hl
        simp
      · have : Fin.natAdd 1 l ≠ Fin.natAdd 1 i := fun h => hl (by
          have := congrArg Fin.val h
          simp at this
          exact Fin.ext this)
        simp [this, hl]
    · rw [e0]
      have : Fin.castAdd k (0 : Fin 1) ≠ Fin.natAdd 1 i := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      simp [this]
end FieldDerivSegment
open FieldDerivSegment in
theorem Estimates.fieldDerivAlongSegment_of_slices (hS : IteratedFDerivSlices) :
    fieldDerivAlongSegmentStatement := by
  classical
  intro F ρ V G k c X D η hG hk hD hη
  set g := fieldDeriv G V c X with hg
  have hdiff : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ ρ) → DifferentiableAt ℝ g ζ := fun ζ hζ => by
    have h3 := hG k c X ζ hζ
    have h := hS.2.1 (Fin k → ℝ) (StepVariable (finiteCells F))
      (fun q => G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) k 1 (fun l => Pi.single l 1) ζ
      (ContDiffAt.of_le h3 (by exact_mod_cast (by omega : 1 + k ≤ 3)))
    exact h.differentiableAt (by simp)
  have hseg : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ b, ‖(v • η) b‖ ≤ ρ := fun v hv b => by
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hv.1]
    calc v * ‖η b‖ ≤ 1 * ‖η b‖ := mul_le_mul_of_nonneg_right hv.2 (norm_nonneg _)
      _ = ‖η b‖ := one_mul _
      _ ≤ ρ := hη b
  have hbound : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ ρ) →
      ‖fderiv ℝ g ζ η‖ ≤ ∑ b, ‖η b‖ * D b := fun ζ hζ => by
    have hsum : η = ∑ b, Pi.single b (η b) := (Finset.univ_sum_single η).symm
    conv_lhs => rw [hsum, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    by_cases h0 : η b = 0
    · rw [h0]
      simp
    · have hn : ‖η b‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      set u := ‖η b‖⁻¹ • η b with hu
      have hu1 : ‖u‖ = 1 := by
        rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have hdec : η b = ‖η b‖ • u := by
        rw [hu, smul_smul, mul_inv_cancel₀ hn, one_smul]
      have hsingle : (Pi.single b (η b) : StepVariable (finiteCells F)) = ‖η b‖ • Pi.single b u := by
        conv_lhs => rw [hdec]
        funext b'
        by_cases hb : b' = b
        · subst hb
          simp
        · simp [Pi.single_eq_of_ne hb]
      rw [hsingle, map_smul, norm_smul, norm_norm, fderiv_fieldDeriv_single hS hG hk c X hζ b u, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hD ζ hζ b u hu1) (norm_nonneg _)
  have hder : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun v : ℝ => g (v • η)) (fderiv ℝ g (v • η) η) (Set.Icc (0 : ℝ) 1) v := fun v hv => by
    have h1 : HasDerivAt (fun v : ℝ => v • η) ((1 : ℝ) • η) v := (hasDerivAt_id v).smul_const η
    rw [one_smul] at h1
    exact ((hdiff _ (hseg v hv)).hasFDerivAt.comp_hasDerivAt v h1).hasDerivWithinAt
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' hder
    (fun v hv => hbound _ (hseg v ⟨hv.1, hv.2.le⟩))
  simpa using this
end YangMills.Construction
end
