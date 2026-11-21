import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmittedProof
import YangMills.Construction.SummableBoundsOfTheFlow.FamilyExponentIsSmoothAlongTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.PartsBetweenAreSmoothInTheParametersProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeBetweenComparesOnTwoToriProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames IteratedDerivative Estimates FamilyNorms
namespace Interpolation
variable {F : BlockFrame} {a' : ℝ}
namespace LawExponentSmooth
theorem toImaginary_imaginaryCoords (w : imaginaryQuaternions) : toImaginary (_root_.YangMills.Construction.Interpolation.imaginaryCoords w) = w := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_imaginaryCoords <;> assumption
theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
def imaginaryCoordsCLM : imaginaryQuaternions →L[ℝ] BondVector :=
  LinearMap.toContinuousLinearMap
    { toFun := _root_.YangMills.Construction.Interpolation.imaginaryCoords
      map_add' := fun p q => by
        ext i
        fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords]
      map_smul' := fun r p => by
        ext i
        fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords] }
theorem imaginaryCoordsCLM_apply (w : imaginaryQuaternions) : imaginaryCoordsCLM w = _root_.YangMills.Construction.Interpolation.imaginaryCoords w := rfl
def baseUnit : imaginaryQuaternions := toImaginary (EuclideanSpace.single 0 1)
theorem norm_baseUnit : ‖baseUnit‖ = 1 := by
  unfold baseUnit
  rw [norm_toImaginary]
  simp
open Classical in
def normalize (X : imaginaryQuaternions) : imaginaryQuaternions := if X = 0 then baseUnit else ‖X‖⁻¹ • X
theorem norm_normalize (X : imaginaryQuaternions) : ‖normalize X‖ = 1 := by
  unfold normalize
  split_ifs with h
  · exact norm_baseUnit
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]
theorem norm_smul_normalize (X : imaginaryQuaternions) : ‖X‖ • normalize X = X := by
  unfold normalize
  split_ifs with h
  · simp [h]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]
theorem bondSpread_normalize {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) :
    ColdStepAtMirrorFrames.bondSpread c (fun l => normalize (X l)) (fun l => ‖X l‖ * τ l) =
      ColdStepAtMirrorFrames.bondSpread c X τ := by
  funext y i
  unfold ColdStepAtMirrorFrames.bondSpread
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · show (‖X l‖ * τ l) • normalize (X l) = τ l • X l
    rw [mul_comm, ← smul_smul, norm_smul_normalize]
  · rfl
theorem jointlyContDiffOnBalls_of_kernels (hDA : JointMixedDerivEqDerivAlong) {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hne : Nonempty ↥(chordBonds (finiteCells F)))
    (hk : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) → ∀ (l j : ℕ)
      (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
      (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions), 2 ≤ l → (∀ i, ‖u i‖ = 1) →
      AreUnitVectors X → ContDiffAt ℝ ((l + j : ℕ) : WithTop ℕ∞) (jointDisplacement G η V b u c X) 0) :
    JointlyContDiffOnBalls ρ V G := by
  intro k c X η hη
  have hu : AreUnitVectors fun l => normalize (X l) := fun l => norm_normalize (X l)
  have h3 := (hDA F V G η k c fun l => normalize (X l)).1 hne
    (fun l b u h2 hu' => hk η hη l k b u c _ h2 hu' hu) 3
  have hL : ContDiff ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      ((q.2, fun l => ‖X l‖ * q.1 l) : StepVariable (finiteCells F) × (Fin k → ℝ))) := by
    refine contDiff_snd.prodMk (contDiff_pi.mpr fun l => ?_)
    exact contDiff_const.mul ((contDiff_apply ℝ ℝ l).comp contDiff_fst)
  have h0 : ((fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      ((q.2, fun l => ‖X l‖ * q.1 l) : StepVariable (finiteCells F) × (Fin k → ℝ))) (0, η)) = (η, 0) := by
    simp only [Pi.zero_apply, mul_zero]
    rfl
  have h3' : ContDiffAt ℝ 3 (rotatedEval G V c fun l => normalize (X l))
      ((fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        ((q.2, fun l => ‖X l‖ * q.1 l) : StepVariable (finiteCells F) × (Fin k → ℝ))) (0, η)) := by
    rw [h0]
    exact_mod_cast h3
  have hc := ContDiffAt.comp (0, η) h3' hL.contDiffAt
  refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  show G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V) =
    G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c (fun l => normalize (X l))
      (fun l => ‖X l‖ * q.1 l)) V)
  rw [bondSpread_normalize]
theorem contDiffAt_comp_shift {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    {H : (Fin k → ℝ) × E → ℝ} {D : (Fin k → ℝ) → E} {s₀ : ℝ} {η : E} (hH : ContDiffAt ℝ 3 H (0, η))
    (hD : ContDiffAt ℝ 3 D 0) :
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × E) => H (q.1, q.2.2 + (q.2.1 - s₀) • D q.1)) (0, s₀, η) := by
  have h1 : ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × E) => D q.1) (0, s₀, η) :=
    ContDiffAt.comp (g := D) (0, s₀, η) hD contDiff_fst.contDiffAt
  have h2 : ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × E) => q.2.1 - s₀) (0, s₀, η) :=
    ((contDiff_fst.comp contDiff_snd).sub contDiff_const).contDiffAt
  have h3 : ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × E) =>
      ((q.1, q.2.2 + (q.2.1 - s₀) • D q.1) : (Fin k → ℝ) × E)) (0, s₀, η) :=
    contDiff_fst.contDiffAt.prodMk ((contDiff_snd.comp contDiff_snd).contDiffAt.add (h2.smul h1))
  have h0 : (((0 : Fin k → ℝ), η + (s₀ - s₀) • D 0) : (Fin k → ℝ) × E) = (0, η) := by simp
  have hH' : ContDiffAt ℝ 3 H (((0 : Fin k → ℝ), η + (s₀ - s₀) • D 0) : (Fin k → ℝ) × E) := by
    rw [h0]
    exact hH
  exact ContDiffAt.comp (g := H) (0, s₀, η) hH' h3
theorem contDiffAt_comp_shift_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    {H : (Fin k → ℝ) × E → ℝ} {D : (Fin k → ℝ) → E} {s₀ : ℝ} {η : E} (hH : ContDiffAt ℝ 3 H (0, 0))
    (hD : ContDiffAt ℝ 3 D 0) :
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × E) => H (q.1, (0 : E) + (q.2.1 - s₀) • D q.1)) (0, s₀, η) := by
  have h1 := contDiffAt_comp_shift (s₀ := s₀) hH hD
  have hm : ContDiff ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × E) => ((q.1, q.2.1, (0 : E)) : (Fin k → ℝ) × (ℝ × E))) :=
    contDiff_fst.prodMk ((contDiff_fst.comp contDiff_snd).prodMk contDiff_const)
  exact ContDiffAt.comp (g := fun q : (Fin k → ℝ) × (ℝ × E) => H (q.1, q.2.2 + (q.2.1 - s₀) • D q.1))
    (0, s₀, η) (by simpa using h1) hm.contDiffAt
theorem contDiffAt_exponent_shift {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {α β γ : Type}
    (x g₀ : ℝ) (He : (Fin k → ℝ) × E → ℝ) (Hg : α → (Fin k → ℝ) × E → ℝ) (Hh : β → (Fin k → ℝ) × E → ℝ)
    (Hr : γ → (Fin k → ℝ) × E → ℝ) (S₁ : Finset α) (S₂ : Finset β) (S₃ : Finset γ)
    {D : (Fin k → ℝ) → E} {s₀ : ℝ} {η : E} (h₁ : ContDiffAt ℝ 3 He (0, η)) (h₀ : ContDiffAt ℝ 3 He (0, 0))
    (hg : ∀ a ∈ S₁, ContDiffAt ℝ 3 (Hg a) (0, η)) (hh : ∀ b ∈ S₂, ContDiffAt ℝ 3 (Hh b) (0, η))
    (hr : ∀ y ∈ S₃, ContDiffAt ℝ 3 (Hr y) (0, η)) (hD : ContDiffAt ℝ 3 D 0) :
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × E) =>
      x * (He (q.1, q.2.2 + (q.2.1 - s₀) • D q.1) - He (q.1, 0 + (q.2.1 - s₀) • D q.1)) -
      (∑ a ∈ S₁, (Hg a (q.1, q.2.2 + (q.2.1 - s₀) • D q.1) - g₀)) -
      (∑ b ∈ S₂, Hh b (q.1, q.2.2 + (q.2.1 - s₀) • D q.1)) -
      ∑ y ∈ S₃, Hr y (q.1, q.2.2 + (q.2.1 - s₀) • D q.1)) (0, s₀, η) := by
  have a1 := contDiffAt_comp_shift (s₀ := s₀) h₁ hD
  have a0 := contDiffAt_comp_shift_zero (s₀ := s₀) (η := η) h₀ hD
  have aG : ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × E) =>
      ∑ a ∈ S₁, (Hg a (q.1, q.2.2 + (q.2.1 - s₀) • D q.1) - g₀)) (0, s₀, η) :=
    ContDiffAt.sum fun a ha => (contDiffAt_comp_shift (s₀ := s₀) (hg a ha) hD).sub contDiffAt_const
  have aH : ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × E) =>
      ∑ b ∈ S₂, Hh b (q.1, q.2.2 + (q.2.1 - s₀) • D q.1)) (0, s₀, η) :=
    ContDiffAt.sum fun b hb => contDiffAt_comp_shift (s₀ := s₀) (hh b hb) hD
  have aR : ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × E) =>
      ∑ y ∈ S₃, Hr y (q.1, q.2.2 + (q.2.1 - s₀) • D q.1)) (0, s₀, η) :=
    ContDiffAt.sum fun y hy => contDiffAt_comp_shift (s₀ := s₀) (hr y hy) hD
  exact (((contDiffAt_const (c := x)).mul (a1.sub a0)).sub aG |>.sub aH).sub aR
def gapVector (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) : StepVariable (finiteCells F) :=
  fun b => _root_.YangMills.Construction.Interpolation.imaginaryCoords (frameGap a ρA m b.1 V)
theorem toImaginary_add (p q : BondVector) : toImaginary (p + q) = toImaginary p + toImaginary q := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.toImaginary_add <;> assumption
theorem toImaginary_smul (r : ℝ) (p : BondVector) : toImaginary (r • p) = r • toImaginary p := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.toImaginary_smul <;> assumption
theorem chartedField_congr {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (hw : ∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) : chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
theorem interpolatedCoords_shift (s s₀ a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) {y : F.Site F.depth} {i : Fin 4}
    (hb : (y, i) ∈ chordBonds (finiteCells F)) :
    interpolatedCoords s a ρA m V ζ y i =
      interpolatedCoords s₀ a ρA m V (ζ + (s - s₀) • gapVector a ρA m V) y i := by
  unfold interpolatedCoords stepCoordinates
  rw [dif_pos hb, dif_pos hb]
  simp only [Pi.add_apply, Pi.smul_apply, toImaginary_add, toImaginary_smul, gapVector,
    toImaginary_imaginaryCoords, interpolatedFrame, frameGap]
  module
theorem interpolatedField_shift (hM : ChartEquivariance F a') (s s₀ a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) :
    interpolatedField s a ρA m V ζ = interpolatedField s₀ a ρA m V (ζ + (s - s₀) • gapVector a ρA m V) := by
  unfold interpolatedField
  exact chartedField_congr V fun y i ht =>
    interpolatedCoords_shift s s₀ a ρA m V ζ (hM.mem_chordBonds_of_not_tree _ ht)
theorem familyLawExponent_eq_shift (hM : ChartEquivariance F a') (s s₀ a ρA x : ℝ) (m : ℕ) (φ : LocalFamily)
    (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)) :
    familyLawExponent s a ρA x m φ V ζ =
      x * (interpolatedEnergy s₀ a ρA m (ζ + (s - s₀) • gapVector a ρA m V) V -
        interpolatedEnergy s₀ a ρA m (0 + (s - s₀) • gapVector a ρA m V) V) -
      (∑ c ∈ innerBonds (finiteCells F) F.top,
        (contourHaarGap s₀ a ρA x m c (ζ + (s - s₀) • gapVector a ρA m V) V - haarGap (a * x))) -
      (∑ b : ↥(chordBonds (finiteCells F)),
        interpolatedHaarLogRatio s₀ a ρA m b (ζ + (s - s₀) • gapVector a ρA m V) V) -
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        interpolatedExpansion s₀ a ρA m φ y (ζ + (s - s₀) • gapVector a ρA m V) V := by
  have hE : ∀ ξ : StepVariable (finiteCells F), chartedEnergy a (interpolatedCoords s a ρA m V ξ) V =
      interpolatedEnergy s₀ a ρA m (ξ + (s - s₀) • gapVector a ρA m V) V := fun ξ => by
    unfold interpolatedEnergy chartedEnergy
    rw [chartedField_congr V fun y i ht =>
      interpolatedCoords_shift s s₀ a ρA m V ξ (hM.mem_chordBonds_of_not_tree _ ht)]
  have hG : ∀ c, haarGapExcess a x (interpolatedField s a ρA m V ζ) c =
      contourHaarGap s₀ a ρA x m c (ζ + (s - s₀) • gapVector a ρA m V) V - haarGap (a * x) := fun c => by
    unfold haarGapExcess contourHaarGap
    rw [interpolatedField_shift hM s s₀ a ρA m V ζ]
  have hH : ∀ b : ↥(chordBonds (finiteCells F)), haarLogRatio (interpolatedCoords s a ρA m V ζ b.1.1 b.1.2) =
      interpolatedHaarLogRatio s₀ a ρA m b (ζ + (s - s₀) • gapVector a ρA m V) V := fun b => by
    unfold interpolatedHaarLogRatio
    rw [interpolatedCoords_shift s s₀ a ρA m V ζ b.2]
  have hR : ∀ y, interpolatedExpansion s a ρA m φ y ζ V =
      interpolatedExpansion s₀ a ρA m φ y (ζ + (s - s₀) • gapVector a ρA m V) V := fun y => by
    unfold interpolatedExpansion
    rw [interpolatedField_shift hM s s₀ a ρA m V ζ]
  unfold familyLawExponent interpolatedExponent
  rw [hE ζ, hE 0]
  simp only [hG, hH, hR]
theorem chordBonds_nonempty (hSites : SiteDecomposition) (hCh : chartEquivarianceStatement) (F : BlockFrame)
    (a : ℝ) (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) : Nonempty ↥(chordBonds (finiteCells F)) := by apply _root_.YangMills.Construction.Interpolation.PartsSmooth.chordBonds_nonempty <;> assumption
theorem hasBoundedDerivatives_of_normBounded {L t n₀ : ℕ} {σ δ ε ε₃ : ℝ} {f : LocalFamily}
    (hf : IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ f) :
    HasBoundedDerivatives L t n₀ σ δ 3 (fun j => if j = 3 then ε₃ else ε) f := by apply _root_.YangMills.SharedProofs.p1 <;> assumption
theorem frameGap_eq_sub (a ρA : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    frameGap a ρA m b V = interpolatedFrame 1 a ρA m b V - interpolatedFrame 0 a ρA m b V := by
  simp [frameGap, interpolatedFrame]
set_option maxHeartbeats 1600000 in
theorem familyLawExponentSmoothAt_of (hDA : JointMixedDerivEqDerivAlong)
    (hJm : JointlyContDiffOnBallsOfDisplacements) (hCh : chartEquivarianceStatement)
    (hSites : SiteDecomposition) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hT : T.IsOrdered) (h2 : 2 ≤ T.n₀) {K : ℕ → ℝ}
    {D : ℕ → ℕ → ℝ} (hK : interpolationKernelBoundsAt T K D) {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (hfb : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFrameBoundsAt T Cq Cz Cr t x)
    {C : ℝ} {Ck : ℕ → ℝ} (htr : TransportBoundsAt T C Ck) :
    familyLawExponentSmoothAt T := by
  classical
  intro t x s₀ φ F V k c X η hx h0 h1 hφ hF hV hη
  have hodd : Odd F.blockSide := by
    rw [hF.1]
    exact hT.odd_L
  have hside : ∀ i, 2 ≤ F.extent i := by
    obtain ⟨-, -, n, hs, hn⟩ := hF
    intro i
    rw [hs i]
    omega
  have hM := hCh F T.a hodd hside
  have hne := chordBonds_nonempty hSites hCh F T.a hodd hside
  have hσ := hT.σ_pos
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hE1 : 1 ≤ T.E := hT.one_le_E
  have hη₃ := hT.η₃_pos
  have hE₃ : 0 < T.energyRatio := by
    show 0 < T.E / T.η₃
    have : 0 < T.E := by linarith
    positivity
  have hker := fun (ζ : StepVariable (finiteCells F)) (hζ : ∀ b, ‖ζ b‖ ≤ T.ballRadius) =>
    hK x t F V s₀ ζ hx hF hV h0 h1 hζ
  have jE : JointlyContDiffOnBalls T.ballRadius V
      (interpolatedEnergy s₀ T.a T.chainParams.ρA (frameRadius x)) :=
    jointlyContDiffOnBalls_of_kernels hDA hne fun ζ hζ l j b u c' X' hl hu hX =>
      ((hker ζ hζ).energy l j b u c' X' hl hu hX).1
  have jG : ∀ c₀, JointlyContDiffOnBalls T.ballRadius V
      (contourHaarGap s₀ T.a T.chainParams.ρA x (frameRadius x) c₀) := fun c₀ =>
    jointlyContDiffOnBalls_of_kernels hDA hne fun ζ hζ l j b u c' X' hl hu hX =>
      ((hker ζ hζ).gap c₀ l j b u c' X' (by omega) hu hX).1
  have jH : ∀ b₀, JointlyContDiffOnBalls T.ballRadius V
      (interpolatedHaarLogRatio s₀ T.a T.chainParams.ρA (frameRadius x) b₀) := fun b₀ =>
    jointlyContDiffOnBalls_of_kernels hDA hne fun ζ hζ l j b u c' X' hl hu hX =>
      ((hker ζ hζ).haar b₀ l j b u c' X' (by omega) hu hX).1
  have jR : ∀ y, JointlyContDiffOnBalls T.ballRadius V
      (interpolatedExpansion s₀ T.a T.chainParams.ρA (frameRadius x) φ y) := fun y => by
    refine hJm F T.ballRadius V _ fun ζ hζ l j b u c' X' hu hX => ?_
    have tr := htr x t 3 _ φ F V s₀ ζ hx le_rfl (by norm_num)
      (fun j => by
        split_ifs
        · exact hE₃.le
        · linarith) (hasBoundedDerivatives_of_normBounded hφ) hF hV h0 h1 hζ
    have h3' := tr.smooth y l j b u c' X' hu hX
    exact_mod_cast h3'
  have one0 := (hfb t x hx).one_torus F V 0 hF hV le_rfl zero_le_one
  have one1 := (hfb t x hx).one_torus F V 1 hF hV zero_le_one le_rfl
  have hD : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
      gapVector T.a T.chainParams.ρA (frameRadius x)
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0 := by
    refine contDiffAt_pi.mpr fun b => ?_
    have a1 := one1.small.analytic b.1 b.2 k c X
    have a0 := one0.small.analytic b.1 b.2 k c X
    have e1 : (fun τ : Fin k → ℝ => gapVector T.a T.chainParams.ρA (frameRadius x)
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) b) =
        imaginaryCoordsCLM ∘ ((fun σ : Fin k → ℝ => interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b.1
            (rotatedField (BlockAverages.bondSpread c X σ) V)) -
          (fun σ : Fin k → ℝ => interpolatedFrame 0 T.a T.chainParams.ρA (frameRadius x) b.1
            (rotatedField (BlockAverages.bondSpread c X σ) V))) := by
      funext τ
      simp only [gapVector, Function.comp, imaginaryCoordsCLM_apply, Pi.sub_apply]
      rw [frameGap_eq_sub]
      rfl
    rw [e1]
    exact imaginaryCoordsCLM.contDiff.contDiffAt.comp 0 (a1.sub a0).contDiffAt
  have hz : ∀ b : ↥(chordBonds (finiteCells F)), ‖(0 : StepVariable (finiteCells F)) b‖ ≤ T.ballRadius :=
    fun b => by simpa using hρ.le
  have hall := contDiffAt_exponent_shift x (haarGap (T.a * x))
    (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      interpolatedEnergy s₀ T.a T.chainParams.ρA (frameRadius x) q.2
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V))
    (fun c₀ (q : (Fin k → ℝ) × StepVariable (finiteCells F)) =>
      contourHaarGap s₀ T.a T.chainParams.ρA x (frameRadius x) c₀ q.2
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V))
    (fun b (q : (Fin k → ℝ) × StepVariable (finiteCells F)) =>
      interpolatedHaarLogRatio s₀ T.a T.chainParams.ρA (frameRadius x) b q.2
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V))
    (fun y (q : (Fin k → ℝ) × StepVariable (finiteCells F)) =>
      interpolatedExpansion s₀ T.a T.chainParams.ρA (frameRadius x) φ y q.2
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V))
    (innerBonds (finiteCells F) F.top) Finset.univ (sitesOfCells (finiteCells F) F.depth) (s₀ := s₀)
    (jE k c X η hη) (jE k c X 0 hz) (fun c₀ _ => jG c₀ k c X η hη) (fun b _ => jH b k c X η hη)
    (fun y _ => jR y k c X η hη) hD
  refine hall.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  exact familyLawExponent_eq_shift hM q.2.1 s₀ T.a T.chainParams.ρA x (frameRadius x) φ _ q.2.2
theorem eventually_two_le_n₀ : EventuallyInParameters fun T => 2 ≤ T.n₀ := by apply _root_.YangMills.SharedProofs.p10519 <;> assumption
end LawExponentSmooth
open LawExponentSmooth in
theorem familyLawExponentSmooth_proof (hframes : interpolatedFramesStatement)
    (hTr : transportBoundsStatement) (hK : interpolationKernelBoundsStatement)
    (hDA : JointMixedDerivEqDerivAlong) (hJm : JointlyContDiffOnBallsOfDisplacements)
    (hCh : chartEquivarianceStatement) (hSites : SiteDecomposition)
    (hJ : EventuallyInParametersCombines) : FamilyLawExponentSmooth := by
  obtain ⟨Cq, Cz, Cr, hfb⟩ := hframes
  obtain ⟨C, Ck, -, -, htr⟩ := hTr
  obtain ⟨K, D, -, -, hk⟩ := hK
  have j := hJ.1
  have J := j _ _ eventually_two_le_n₀ (j _ _ hfb (j _ _ htr hk))
  refine hJ.2 _ _ (fun T hT h => ?_) J
  obtain ⟨h2, hf, ht, hk'⟩ := h
  exact familyLawExponentSmoothAt_of hDA hJm hCh hSites T hT h2 hk' hf ht
end Interpolation
end YangMills.Construction
end
