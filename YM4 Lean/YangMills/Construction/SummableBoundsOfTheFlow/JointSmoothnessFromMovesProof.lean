import YangMills.Construction.SummableBoundsOfTheFlow.JointSmoothnessFromMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace Estimates
variable {F : BlockFrame}
namespace DisplacementCoordinates
def quaternionI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
def imaginaryUnitI : imaginaryQuaternions := ⟨quaternionI, rfl⟩
theorem norm_imaginaryUnitI : ‖imaginaryUnitI‖ = 1 := by
  change ‖quaternionI‖ = 1
  have h : ‖quaternionI‖ * ‖quaternionI‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    simp [quaternionI]
  have h0 : 0 ≤ ‖quaternionI‖ := norm_nonneg _
  nlinarith
open Classical in
def normalize (X : imaginaryQuaternions) : imaginaryQuaternions :=
  if X = 0 then imaginaryUnitI else ‖X‖⁻¹ • X
theorem norm_normalize (X : imaginaryQuaternions) : ‖normalize X‖ = 1 := by
  unfold normalize
  split_ifs with h
  · exact norm_imaginaryUnitI
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)
theorem norm_smul_normalize (X : imaginaryQuaternions) : ‖X‖ • normalize X = X := by
  unfold normalize
  split_ifs with h
  · simp [h]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]
def normScaling {k : ℕ} (X : Fin k → imaginaryQuaternions) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i => ‖X i‖ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i
theorem bondSpread_normScaling {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) :
    ColdStepAtMirrorFrames.bondSpread c X τ =
      ColdStepAtMirrorFrames.bondSpread c (fun l => normalize (X l)) (normScaling X τ) := by
  funext y i
  unfold ColdStepAtMirrorFrames.bondSpread
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · have : normScaling X τ l = ‖X l‖ * τ l := by simp [normScaling]
    rw [this, mul_comm, mul_smul, norm_smul_normalize]
  · rfl
variable {ι : Type} [Fintype ι]
theorem sum_single_coordinates [DecidableEq ι] (ζ : ι → EuclideanSpace ℝ (Fin 3)) :
    ∑ q : ι × Fin 3, (Pi.single q.1 ((ζ q.1) q.2 • EuclideanSpace.single q.2 (1 : ℝ)) :
      ι → EuclideanSpace ℝ (Fin 3)) = ζ := by
  funext b
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · ext i
    simp [Pi.single_apply, Finset.sum_apply]
  · intro b' _ hb
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [Ne.symm hb]
  · simp
end DisplacementCoordinates
open DisplacementCoordinates in
theorem jointlyContDiffOnBallsOfDisplacements_holds : JointlyContDiffOnBallsOfDisplacements := by
  classical
  intro F ρ V G hG
  set ι := ↥(chordBonds (finiteCells F)) with hι
  have units : ∀ (j : ℕ) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions)
      (η : StepVariable (finiteCells F)),
      (∀ b, ‖η b‖ ≤ ρ) → AreUnitVectors X →
      ContDiffAt ℝ 3 (fun q : (Fin j → ℝ) × StepVariable (finiteCells F) =>
        G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η) := by
    intro j c X η hη hX
    set l := Fintype.card (ι × Fin 3) with hl
    set en : Fin l ≃ ι × Fin 3 := (Fintype.equivFin (ι × Fin 3)).symm with hen
    set b : Fin l → ι := fun i => (en i).1 with hb
    set u : Fin l → EuclideanSpace ℝ (Fin 3) := fun i => EuclideanSpace.single (en i).2 (1 : ℝ) with hu
    have hun : ∀ i, ‖u i‖ = 1 := fun i => by simp [hu]
    have hm := hG η hη l j b u c X hun hX
    set Θ : (Fin j → ℝ) × StepVariable (finiteCells F) →L[ℝ] (Fin (l + j) → ℝ) :=
      ContinuousLinearMap.pi fun i => Fin.addCases (motive := fun _ =>
        (Fin j → ℝ) × StepVariable (finiteCells F) →L[ℝ] ℝ)
        (fun a => (EuclideanSpace.proj (en a).2).comp
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => EuclideanSpace ℝ (Fin 3)) (en a).1).comp
            (ContinuousLinearMap.snd ℝ (Fin j → ℝ) (StepVariable (finiteCells F)))))
        (fun a => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin j => ℝ) a).comp
          (ContinuousLinearMap.fst ℝ (Fin j → ℝ) (StepVariable (finiteCells F)))) i with hΘ
    have hleft : ∀ (q : (Fin j → ℝ) × StepVariable (finiteCells F)) (a : Fin l),
        Θ q (Fin.castAdd j a) = (q.2 (en a).1) (en a).2 := fun q a => by
      simp [hΘ, Fin.addCases_left]
    have hright : ∀ (q : (Fin j → ℝ) × StepVariable (finiteCells F)) (a : Fin j),
        Θ q (Fin.natAdd l a) = q.1 a := fun q a => by
      simp [hΘ, Fin.addCases_right]
    have hpt : ∀ ζ : StepVariable (finiteCells F), ∑ i, (Pi.single (b i) ((ζ (en i).1) (en i).2 • u i) :
        StepVariable (finiteCells F)) = ζ := fun ζ => by
      have := sum_single_coordinates (ι := ι) ζ
      rw [← Equiv.sum_comp en] at this
      exact this
    have hmoved : ∀ q : (Fin j → ℝ) × StepVariable (finiteCells F),
        jointDisplacement G η V b u c X (Θ (q.1, q.2 - η)) =
          G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V) := fun q => by
      unfold jointDisplacement displacedPoint
      simp only [hleft, hright]
      rw [hpt]
      simp
    have hS : ContDiff ℝ 3 (fun q : (Fin j → ℝ) × StepVariable (finiteCells F) => Θ (q.1, q.2 - η)) :=
      Θ.contDiff.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))
    have hz : Θ ((0 : Fin j → ℝ), η - η) = 0 := by
      rw [sub_self]
      exact map_zero Θ
    have := ContDiffAt.comp (g := jointDisplacement G η V b u c X)
      ((0, η) : (Fin j → ℝ) × StepVariable (finiteCells F)) (by
        change ContDiffAt ℝ 3 _ (Θ ((0 : Fin j → ℝ), η - η))
        rw [hz]
        exact hm) hS.contDiffAt
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    exact (hmoved q).symm
  intro k c X η hη
  have h := units k c (fun l => normalize (X l)) η hη fun l => norm_normalize _
  have hL : ContDiff ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => (normScaling X q.1, q.2)) :=
    ((normScaling X).contDiff.comp contDiff_fst).prodMk contDiff_snd
  have := ContDiffAt.comp (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
    G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c (fun l => normalize (X l)) q.1) V))
    ((0, η) : (Fin k → ℝ) × StepVariable (finiteCells F)) (by
      change ContDiffAt ℝ 3 _ (normScaling X 0, η)
      rw [map_zero]
      exact h) hL.contDiffAt
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  simp only [Function.comp]
  rw [bondSpread_normScaling]
end Estimates
end YangMills.Construction
end
