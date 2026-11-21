import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrameProof
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmittedProof
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionsOfAFamilyAboveTheStar
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation FamilyNorms MeasureTheory Topology
namespace BlockMeans
variable {F : BlockFrame}
namespace CentredExpansionContDiff
theorem bondSpread_smul {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (s τ : Fin k → ℝ) :
    ColdStepAtMirrorFrames.bondSpread c (fun l => s l • X l) τ =
      ColdStepAtMirrorFrames.bondSpread c X (fun l => s l * τ l) := by apply _root_.YangMills.SharedProofs.p12456 <;> assumption
theorem exists_unitVectors_smul {k : ℕ} (X : Fin k → imaginaryQuaternions) :
    ∃ Y : Fin k → imaginaryQuaternions, AreUnitVectors Y ∧ X = fun l => ‖X l‖ • Y l := by apply _root_.YangMills.SharedProofs.p4546 <;> assumption
theorem interpolatedExpansion_zero (a ρA : ℝ) (m : ℕ) (f : LocalFamily) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    interpolatedExpansion 0 a ρA m f y η V = centredExpansion true a ρA m f y η V := by
  have h1 : interpolatedCoords 0 a ρA m V η = coordsAboveFrame true a ρA m V η := by
    funext z i
    simp [interpolatedCoords, coordsAboveFrame, interpolatedFrame]
  simp only [interpolatedExpansion, centredExpansion, interpolatedField, fieldAboveFrame, h1]
theorem displacedPoint_basis_sum {l : ℕ} (e : (↥(chordBonds (finiteCells F)) × Fin 3) ≃ Fin l)
    (η d : StepVariable (finiteCells F)) :
    displacedPoint η (fun i => (e.symm i).1) (fun i => EuclideanSpace.single (e.symm i).2 (1 : ℝ))
      (fun i => d (e.symm i).1 (e.symm i).2) = η + d := by apply _root_.YangMills.SharedProofs.p5713 <;> assumption
theorem contDiffAt_centredExpansion_of_displaced {a ρA : ℝ} {m : ℕ} {f : LocalFamily} {y : F.Site F.depth}
    {V : F.GaugeField F.top} {η : StepVariable (finiteCells F)}
    (hsm : ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
      (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
      (X : Fin j → imaginaryQuaternions),
      (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
      ContDiffAt ℝ 3 (jointDisplacement (interpolatedExpansion 0 a ρA m f y) η V b u c X) 0)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      centredExpansion true a ρA m f y q.2
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η) := by
  classical
  obtain ⟨Xu, hXu, hXe⟩ := exists_unitVectors_smul X
  set e := Fintype.equivFin (↥(chordBonds (finiteCells F)) × Fin 3) with he
  set l := Fintype.card (↥(chordBonds (finiteCells F)) × Fin 3) with hl
  set b : Fin l → ↥(chordBonds (finiteCells F)) := fun i => (e.symm i).1 with hb
  set u : Fin l → EuclideanSpace ℝ (Fin 3) := fun i => EuclideanSpace.single (e.symm i).2 (1 : ℝ) with hu
  have hun : ∀ i, ‖u i‖ = 1 := fun i => by simp [hu]
  set Φ : (Fin k → ℝ) × StepVariable (finiteCells F) → Fin (l + k) → ℝ := fun q =>
    Fin.append (fun i => (q.2 - η) (e.symm i).1 (e.symm i).2) (fun i => ‖X i‖ * q.1 i) with hΦ
  have hΦs : ContDiff ℝ 3 Φ := by
    refine contDiff_pi.mpr fun i => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [hΦ, Fin.append_left]
      have h1 : ContDiff ℝ 3 fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => (q.2 - η) (e.symm i).1 :=
        (contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) (e.symm i).1).comp (contDiff_snd.sub contDiff_const)
      exact (EuclideanSpace.proj (e.symm i).2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff.comp h1
    · simp only [hΦ, Fin.append_right]
      have h1 : ContDiff ℝ 3 fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => q.1 i :=
        (contDiff_apply ℝ ℝ i).comp contDiff_fst
      exact contDiff_const.mul h1
  have hΦ0 : Φ (0, η) = 0 := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [hΦ, Fin.append_left]
    · simp [hΦ, Fin.append_right]
  have hG := hsm l k b u c Xu hun hXu
  have hcomp := ContDiffAt.comp (f := Φ) ((0 : Fin k → ℝ), η)
    (by rw [hΦ0]; exact hG : ContDiffAt ℝ 3 _ (Φ (0, η))) hΦs.contDiffAt
  refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  simp only [Function.comp, jointDisplacement, hΦ, Fin.append_left, Fin.append_right]
  have h1 := displacedPoint_basis_sum e η (q.2 - η)
  rw [add_sub_cancel] at h1
  have h2 : ColdStepAtMirrorFrames.bondSpread c Xu (fun i => ‖X i‖ * q.1 i) =
      ColdStepAtMirrorFrames.bondSpread c X q.1 := by
    conv_rhs => rw [hXe]
    exact (bondSpread_smul c Xu _ _).symm
  rw [interpolatedExpansion_zero]
  simp only [hb, hu, h1, h2]
theorem hasBoundedDerivatives_of_family {L t n₀ : ℕ} {σ δ ε ε₃ : ℝ} {f : LocalFamily}
    (hf : IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ f) :
    HasBoundedDerivatives L t n₀ σ δ 3 (fun j => if j = 3 then ε₃ else ε) f := by apply _root_.YangMills.SharedProofs.p1 <;> assumption
theorem contDiffAt_centredExpansion {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {C : ℝ} {Ck : ℕ → ℝ} (hTr : TransportBoundsAt T C Ck)
    {t : ℕ} {x ε ε₃ : ℝ} {f : LocalFamily} (hx : T.coupling ≤ x) (hε : 0 ≤ ε) (hε₃ : 0 ≤ ε₃)
    (hf : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε ε₃ f) {V : F.GaugeField F.top}
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) :
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      centredExpansion true T.a T.chainParams.ρA (frameRadius x) f y q.2
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η) := by
  have h := hTr x t 3 (fun j => if j = 3 then ε₃ else ε) f F V 0 η hx le_rfl (by norm_num)
    (fun j => by
      show 0 ≤ if j = 3 then ε₃ else ε
      split_ifs <;> assumption) (hasBoundedDerivatives_of_family hf) hF hV le_rfl zero_le_one hη
  exact contDiffAt_centredExpansion_of_displaced
    (fun l j b u c X hu hX => by exact_mod_cast h.smooth y l j b u c X hu hX) c X
end CentredExpansionContDiff
open CentredExpansionContDiff in
theorem centredExpansionContDiff (hJ : EventuallyInParametersCombines)
    (hTr : transportBoundsStatement) : centredExpansionContDiffStatement := by
  obtain ⟨-, weaken⟩ := hJ
  obtain ⟨C, Ck, -, -, hTr⟩ := hTr
  refine weaken _ _ (fun T _ h t x ε ε₃ f F V k c X y η hx hε hε₃ hf hF hV hη => ?_) hTr
  exact contDiffAt_centredExpansion h hx hε hε₃ hf hF hV c X y η hη
end BlockMeans
end YangMills.Construction
end
