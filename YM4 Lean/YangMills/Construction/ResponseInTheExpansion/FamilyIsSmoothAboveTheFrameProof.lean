import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrameProof
import YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyIsAnExpansionProof
import YangMills.Construction.ResponseInTheExpansion.FamilyIsSmoothAboveTheFrame
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation Topology
namespace LinearResponse
variable {F : BlockFrame}
namespace RestrictedFamily
open Classical in
private def restrictToFrame (f : LocalFamily) (F : BlockFrame) : LocalFamily :=
  fun F' => if F' = F then f F' else fun _ _ => 0
private theorem restrictToFrame_self (f : LocalFamily) (F : BlockFrame) :
    restrictToFrame f F F = f F := if_pos rfl
private theorem restrictToFrame_of_ne (f : LocalFamily) {F F' : BlockFrame} (hne : F' ≠ F) :
    restrictToFrame f F F' = fun _ _ => 0 := if_neg hne
private theorem torusDecayFactor_nonneg (L : ℕ) (δ x : ℝ) : 0 ≤ torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyRegular.torusDecayWeight_nonneg <;> assumption
private theorem hasBoundedDerivatives_restrictToFrame {L t n₀ : ℕ} {σ δ E E₃ : ℝ} {f : LocalFamily}
    {F : BlockFrame} (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃) (hf : IsRegularOnTorus L t n₀ σ δ E E₃ f F) :
    HasBoundedDerivatives L t n₀ σ δ 3 (fun j => if j = 3 then E₃ else E) (restrictToFrame f F) := by
  refine ⟨fun F' hF' y W hW j c X => ?_, fun F' hF' y W γ hW => ?_,
    fun F' hF' y W j c X hW h1 h3 hX => ?_⟩
  · by_cases hne : F' = F
    · subst hne
      rw [restrictToFrame_self]
      exact_mod_cast hf.smooth hF' y W hW j c X
    · rw [restrictToFrame_of_ne f hne]
      exact contDiffAt_const
  · by_cases hne : F' = F
    · subst hne
      rw [restrictToFrame_self]
      exact hf.gauge_invariant hF' y W γ hW
    · rw [restrictToFrame_of_ne f hne]
  · by_cases hne : F' = F
    · subst hne
      rw [restrictToFrame_self]
      exact hf.decay hF' y W j c X hW h1 h3 hX
    · rw [restrictToFrame_of_ne f hne]
      have h0 : bondDeriv (fun _ : F'.GaugeField F'.depth => (0 : ℝ)) W c X = 0 := by
        simp [bondDeriv]
      have he : 0 ≤ (if j = 3 then E₃ else E) := by split_ifs <;> assumption
      rw [show (fun _ : F'.GaugeField F'.depth => (0 : ℝ)) = (fun _ => 0 : F'.GaugeField F'.depth → ℝ) from rfl]
      simp only [h0, abs_zero]
      exact div_nonneg he (torusDecayFactor_nonneg _ _ _)
private def segmentEnd (star : Bool) : ℝ := if star then 0 else 1
private theorem segmentEnd_nonneg (star : Bool) : 0 ≤ segmentEnd star := by
  cases star <;> simp [segmentEnd]
private theorem segmentEnd_le_one (star : Bool) : segmentEnd star ≤ 1 := by
  cases star <;> simp [segmentEnd]
private theorem interpolatedExpansion_segmentEnd (star : Bool) (a ρA : ℝ) (m : ℕ) (f : LocalFamily)
    (y : F.Site F.depth) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    interpolatedExpansion (segmentEnd star) a ρA m (restrictToFrame f F) y η V = centredExpansion star a ρA m f y η V := by
  have h1 : interpolatedCoords (segmentEnd star) a ρA m V η = coordsAboveFrame star a ρA m V η := by
    funext z i
    cases star <;> simp [interpolatedCoords, coordsAboveFrame, interpolatedFrame, segmentEnd]
  simp only [interpolatedExpansion, centredExpansion, interpolatedField, fieldAboveFrame, h1,
    ColdStepAtMirrorFrames.subtractTrivial, restrictToFrame_self]
private theorem bondSpread_smul {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (s τ : Fin k → ℝ) :
    ColdStepAtMirrorFrames.bondSpread c (fun l => s l • X l) τ =
      ColdStepAtMirrorFrames.bondSpread c X (fun l => s l * τ l) := by apply _root_.YangMills.SharedProofs.p12456 <;> assumption
private theorem exists_unit_scaling {k : ℕ} (X : Fin k → imaginaryQuaternions) :
    ∃ Y : Fin k → imaginaryQuaternions, AreUnitVectors Y ∧ X = fun l => ‖X l‖ • Y l := by apply _root_.YangMills.SharedProofs.p4546 <;> assumption
private theorem displacedPoint_all {l : ℕ} (e : (↥(chordBonds (finiteCells F)) × Fin 3) ≃ Fin l)
    (η d : StepVariable (finiteCells F)) :
    displacedPoint η (fun i => (e.symm i).1) (fun i => EuclideanSpace.single (e.symm i).2 (1 : ℝ))
      (fun i => d (e.symm i).1 (e.symm i).2) = η + d := by apply _root_.YangMills.SharedProofs.p5713 <;> assumption
private theorem contDiffAt_joint_of_displacements
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {V : F.GaugeField F.top}
    {η : StepVariable (finiteCells F)}
    (hsm : ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
      (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions),
      (∀ i, ‖u i‖ = 1) → AreUnitVectors X → ContDiffAt ℝ 3 (jointDisplacement G η V b u c X) 0)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η) := by
  classical
  obtain ⟨Xu, hXu, hXe⟩ := exists_unit_scaling X
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
  have h1 := displacedPoint_all e η (q.2 - η)
  rw [add_sub_cancel] at h1
  have h2 : ColdStepAtMirrorFrames.bondSpread c Xu (fun i => ‖X i‖ * q.1 i) =
      ColdStepAtMirrorFrames.bondSpread c X q.1 := by
    conv_rhs => rw [hXe]
    exact (bondSpread_smul c Xu _ _).symm
  simp only [hb, hu, h1, h2]
abbrev _root_.YangMills.SharedProofs.p27303 := @contDiffAt_joint_of_displacements
private theorem centredExpansionContDiffAt_of_transportBoundsAt {T : StepParameters} {C : ℝ} {Ck : ℕ → ℝ}
    (hD : T.IsOrdered) (hTr : TransportBoundsAt T C Ck) : CentredExpansionContDiffAt T := by
  intro t x f F V star hx hf hF hV y η k c X hη
  have hE : 0 ≤ T.E := zero_le_one.trans hD.one_le_E
  have hE₃ : 0 ≤ T.energyRatio := div_nonneg hE hD.η₃_pos.le
  have h := hTr x t 3 (fun j => if j = 3 then T.energyRatio else T.E) (restrictToFrame f F) F V
    (segmentEnd star) η hx le_rfl
    (by norm_num) (fun j => by
      show 0 ≤ if j = 3 then T.energyRatio else T.E
      split_ifs <;> assumption) (hasBoundedDerivatives_restrictToFrame hE hE₃ hf) hF hV
    (segmentEnd_nonneg star) (segmentEnd_le_one star) hη
  refine contDiffAt_joint_of_displacements (G := centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y)
    (fun l j b u c X hu hX => ?_) c X
  have e : jointDisplacement (centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y) η V b u c X =
      jointDisplacement (interpolatedExpansion (segmentEnd star) T.a T.chainParams.ρA (frameRadius x)
        (restrictToFrame f F) y) η V b u c X := by
    funext τ
    simp only [jointDisplacement, interpolatedExpansion_segmentEnd]
  rw [e]
  exact_mod_cast h.smooth y l j b u c X hu hX
end RestrictedFamily
open RestrictedFamily in
theorem centredExpansionContDiff_of_transport (hJ : EventuallyInParametersCombines)
    (hTr : transportBoundsStatement) : CentredExpansionContDiff := by
  obtain ⟨-, weaken⟩ := hJ
  obtain ⟨C, Ck, -, -, hTr⟩ := hTr
  exact weaken _ _ (fun T hD h => centredExpansionContDiffAt_of_transportBoundsAt hD h) hTr
end LinearResponse
end YangMills.Construction
end
