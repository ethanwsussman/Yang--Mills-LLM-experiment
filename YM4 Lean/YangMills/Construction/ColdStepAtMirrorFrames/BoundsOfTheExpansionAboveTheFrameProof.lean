import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAlongMovesFreeOfTheRate
import YangMills.Construction.ColdStepAtMirrorFrames.SecondDerivativeThroughTheChartProof
import YangMills.Construction.SummableBoundsOfTheFlow.DecayOfTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages SummableBounds Interpolation IteratedDerivative Estimates FamilyNorms
namespace ColdStepAtMirrorFrames
section Derivatives
variable {F : BlockFrame} {k : ℕ}
private abbrev JointSpace (F : BlockFrame) (k : ℕ) : Type := StepVariable (finiteCells F) × (Fin k → ℝ)
private abbrev paramList (F : BlockFrame) (k : ℕ) : List (JointSpace F k) := parameterDirections _ _ (parameterBasis k)
private theorem paramList_length : (paramList F k).length = k := by simp [parameterDirections, parameterBasis]
private theorem iteratedFDeriv_param_eq_derivAlong (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ)
    (ζ : StepVariable (finiteCells F)) (hf : ContDiffAt ℝ (k : WithTop ℕ∞) f (ζ, 0)) :
    iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => f (ζ, τ)) 0 (fun l => Pi.single l 1) =
      derivAlong f (paramList F k) (ζ, 0) := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.iteratedFDeriv_parameters_eq <;> assumption
private theorem iteratedFDeriv_slope_eq_derivAlong (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ)
    (ζ w : StepVariable (finiteCells F)) (hf : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f (ζ, 0)) :
    iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => fderiv ℝ (fun ζ' => f (ζ', τ)) ζ w) 0 (fun l => Pi.single l 1) =
      derivAlong f (paramList F k ++ [(w, 0)]) (ζ, 0) := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.iteratedFDeriv_parameters_fderiv_eq <;> assumption
private theorem second_deriv_eq_derivAlong (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ)
    (η u v : StepVariable (finiteCells F)) (hf : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) f (η, 0)) :
    fderiv ℝ (fun ζ => fderiv ℝ (fun ζ' => f (ζ', 0)) ζ u) η v = derivAlong f [(v, 0), (u, 0)] (η, 0) := by
  have hev := hf.eventually (by simp)
  have hc : Filter.Tendsto (fun ζ : StepVariable (finiteCells F) => (ζ, (0 : Fin k → ℝ))) (𝓝 η) (𝓝 (η, 0)) :=
    (by fun_prop : Continuous fun ζ : StepVariable (finiteCells F) => (ζ, (0 : Fin k → ℝ))).tendsto η
  have e1 : (fun ζ => fderiv ℝ (fun ζ' => f (ζ', (0 : Fin k → ℝ))) ζ u) =ᶠ[𝓝 η]
      fun ζ => derivAlong f [(u, 0)] (ζ, 0) := by
    filter_upwards [hc.eventually hev] with ζ hζ
    have hd : DifferentiableAt ℝ f (ζ, 0) := hζ.differentiableAt (by simp)
    have := (HasFDerivAt.comp (g := f) (f := fun ζ' => (ζ', (0 : Fin k → ℝ))) ζ hd.hasFDerivAt
      (hasFDerivAt_prodMk_left ζ 0)).fderiv
    change fderiv ℝ (f ∘ fun ζ' => (ζ', (0 : Fin k → ℝ))) ζ u = _
    rw [this]
    simp [derivAlong]
  have hH : DifferentiableAt ℝ (derivAlong f [((u, 0) : JointSpace F k)]) (η, 0) :=
    ((h.1 _ ℝ).contDiffAt _ _ 1 [((u, 0) : JointSpace F k)] (by simpa using hf)).differentiableAt (by simp)
  rw [e1.fderiv_eq]
  have := (HasFDerivAt.comp (g := derivAlong f [((u, 0) : JointSpace F k)])
    (f := fun ζ' => (ζ', (0 : Fin k → ℝ))) η hH.hasFDerivAt (hasFDerivAt_prodMk_left η 0)).fderiv
  change fderiv ℝ (derivAlong f [((u, 0) : JointSpace F k)] ∘ fun ζ' => (ζ', (0 : Fin k → ℝ))) η v = _
  rw [this]
  simp [derivAlong]
abbrev _root_.YangMills.DeltaSharedProofs.p502347 := @second_deriv_eq_derivAlong
private theorem third_deriv_eq_derivAlong (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ)
    (η u v z : StepVariable (finiteCells F)) (hf : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) f (η, 0)) :
    fderiv ℝ (fun ζ => fderiv ℝ (fun ζ₁ => fderiv ℝ (fun ζ' => f (ζ', 0)) ζ₁ u) ζ v) η z =
      derivAlong f [(z, 0), (v, 0), (u, 0)] (η, 0) := by
  have hev := hf.eventually (by simp)
  have hc : Filter.Tendsto (fun ζ : StepVariable (finiteCells F) => (ζ, (0 : Fin k → ℝ))) (𝓝 η) (𝓝 (η, 0)) :=
    (by fun_prop : Continuous fun ζ : StepVariable (finiteCells F) => (ζ, (0 : Fin k → ℝ))).tendsto η
  have e1 : (fun ζ => fderiv ℝ (fun ζ₁ => fderiv ℝ (fun ζ' => f (ζ', (0 : Fin k → ℝ))) ζ₁ u) ζ v) =ᶠ[𝓝 η]
      fun ζ => derivAlong f [(v, 0), (u, 0)] (ζ, 0) := by
    filter_upwards [hc.eventually hev] with ζ hζ
    exact second_deriv_eq_derivAlong h f ζ u v (hζ.of_le (by exact_mod_cast (by norm_num : 2 ≤ 3)))
  have hH : DifferentiableAt ℝ (derivAlong f [((v, 0) : JointSpace F k), ((u, 0) : JointSpace F k)]) (η, 0) :=
    ((h.1 _ ℝ).contDiffAt _ _ 1 [((v, 0) : JointSpace F k), ((u, 0) : JointSpace F k)] hf).differentiableAt (by simp)
  rw [e1.fderiv_eq]
  have := (HasFDerivAt.comp (g := derivAlong f [((v, 0) : JointSpace F k), ((u, 0) : JointSpace F k)])
    (f := fun ζ' => (ζ', (0 : Fin k → ℝ))) η hH.hasFDerivAt (hasFDerivAt_prodMk_left η 0)).fderiv
  change fderiv ℝ (derivAlong f [((v, 0) : JointSpace F k), ((u, 0) : JointSpace F k)] ∘
    fun ζ' => (ζ', (0 : Fin k → ℝ))) η z = _
  rw [this]
  simp [derivAlong]
end Derivatives
section Perturbations
variable {F : BlockFrame} {s a ρA : ℝ} {m : ℕ} {V : F.GaugeField F.top}
private def combinedPerturbations {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    Fin (l + k) → Perturbation F :=
  Fin.addCases (fun i => Perturbation.bulk (b i) (u i)) (fun i => Perturbation.top (c i) (X i))
private theorem combinedPerturbations_isUnit {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hu : ∀ i, ‖u i‖ = 1) (hX : AreUnitVectors X) :
    ∀ i, (combinedPerturbations b u c X i).IsUnit := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [combinedPerturbations, Fin.addCases_left, Perturbation.IsUnit]
    exact hu i
  · simp only [combinedPerturbations, Fin.addCases_right, Perturbation.IsUnit]
    exact hX i
private theorem jointDisplacement_eq_perturbed {l k : ℕ} (h : LocalFamily) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F))
    (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    jointDisplacement (fun ζ V' => interpolatedExpansion s a ρA m h y ζ V') η V b u c X =
      fun τ => subtractTrivial h F y (perturbedField s a ρA m V η (combinedPerturbations b u c X) τ) := by
  classical
  funext τ
  have h1 : perturbedVariable η (combinedPerturbations b u c X) τ =
      displacedPoint η b u fun i => τ (Fin.castAdd k i) := by
    unfold perturbedVariable displacedPoint
    congr 1
    rw [Fin.sum_univ_add]
    simp only [combinedPerturbations, Fin.addCases_left, Fin.addCases_right, Perturbation.variableDirection,
      smul_zero, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ => (Pi.single_smul _ _ _).symm
  have h2 : perturbedTop V (combinedPerturbations b u c X) τ =
      leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V := by
    unfold perturbedTop
    congr 1
    funext z i
    simp only [bondSpread]
    rw [Fin.sum_univ_add]
    simp only [combinedPerturbations, Fin.addCases_left, Fin.addCases_right, Perturbation.topBond,
      Perturbation.topDirection, smul_zero, ite_self, Finset.sum_const_zero, zero_add]
  simp only [jointDisplacement, interpolatedExpansion, perturbedField, h1, h2]
private theorem bondSpan_le_diameter {k : ℕ} {P : Finset F.Cell} {Y : F.Cell} {c : Fin k → F.Site F.top × Fin 4}
    (hY : Y ∈ P) (hc : ∀ l, (c l).1 ∈ P) : bondSpan Y c ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.bondSpan_le_cellSetDiameter <;> assumption
private theorem bondSpanWithCell_le_diameter {k : ℕ} {P : Finset F.Cell} {Y z : F.Cell}
    {c : Fin k → F.Site F.top × Fin 4}
    (hY : Y ∈ P) (hz : z ∈ P) (hc : ∀ l, (c l).1 ∈ P) : bondSpanWithCell Y z c ≤ cellSetDiameter P := by
  unfold bondSpanWithCell
  refine bondSpan_le_diameter hY fun l => ?_
  refine Fin.cases ?_ (fun i => ?_) l
  · simpa using hz
  · simpa using hc i
abbrev _root_.YangMills.SharedProofs.p114969 := @bondSpanWithCell_le_diameter
private theorem bulk_cell_mem {Y : F.Cell} {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (i : Fin l) :
    enclosingCell (b i).1.1 ∈ insert Y (perturbationCells (combinedPerturbations b u c X)) := by
  refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨Fin.castAdd k i, Finset.mem_univ _, ?_⟩)
  simp [combinedPerturbations, Perturbation.cell]
private theorem top_cell_mem {Y : F.Cell} {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (i : Fin k) :
    (c i).1 ∈ insert Y (perturbationCells (combinedPerturbations b u c X)) := by
  refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨Fin.natAdd l i, Finset.mem_univ _, ?_⟩)
  simp [combinedPerturbations, Perturbation.cell]
private theorem leftTranslate_bondSpread_zero {j : ℕ} {W : F.GaugeField j} {k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    leftTranslate (bondSpread c X 0) W = W := by apply _root_.YangMills.Construction.Interpolation.TopVariation.leftTranslate_bondSpread_zero <;> assumption
private theorem bondSpread_smul {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (s τ : Fin k → ℝ) :
    bondSpread c (fun l => s l • X l) τ = bondSpread c X (fun l => s l * τ l) := by
  funext y i
  simp only [bondSpread, smul_smul, mul_comm]
abbrev _root_.YangMills.SharedProofs.p12456 := @bondSpread_smul
private theorem exists_norm_eq_one : ∃ U : imaginaryQuaternions, ‖U‖ = 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSecondDeriv.exists_norm_eq_one <;> assumption
private theorem eq_norm_smul_unit {k : ℕ} (X : Fin k → imaginaryQuaternions) :
    ∃ Y : Fin k → imaginaryQuaternions, AreUnitVectors Y ∧ X = fun l => ‖X l‖ • Y l := by
  classical
  obtain ⟨U, hU⟩ := exists_norm_eq_one
  refine ⟨fun l => if X l = 0 then U else ‖X l‖⁻¹ • X l, fun l => ?_, ?_⟩
  · by_cases h : X l = 0
    · simpa [h] using hU
    · simp only [h, if_false]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]
  · funext l
    by_cases h : X l = 0
    · simp [h]
    · simp only [h, if_false]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]
abbrev _root_.YangMills.SharedProofs.p4546 := @eq_norm_smul_unit
private theorem displacedPoint_basis {l : ℕ} (e : (↥(chordBonds (finiteCells F)) × Fin 3) ≃ Fin l)
    (η d : StepVariable (finiteCells F)) :
    displacedPoint η (fun i => (e.symm i).1) (fun i => EuclideanSpace.single (e.symm i).2 (1 : ℝ))
      (fun i => d (e.symm i).1 (e.symm i).2) = η + d := by
  classical
  unfold displacedPoint
  congr 1
  have h := Equiv.sum_comp e.symm (fun p : ↥(chordBonds (finiteCells F)) × Fin 3 =>
    (Pi.single p.1 (d p.1 p.2 • EuclideanSpace.single p.2 (1 : ℝ)) : StepVariable (finiteCells F)))
  refine h.trans ?_
  funext β
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single β]
  · simp only [if_true]
    ext i
    simp [Pi.single_apply]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
abbrev _root_.YangMills.SharedProofs.p5713 := @displacedPoint_basis
private theorem interpolatedExpansion_contDiffAt {f : LocalFamily} {y : F.Site F.depth} {η : StepVariable (finiteCells F)}
    (hsm : ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
      (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions),
      (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
      ContDiffAt ℝ 3 (jointDisplacement (fun ζ V' => interpolatedExpansion s a ρA m f y ζ V') η V b u c X) 0)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      interpolatedExpansion s a ρA m f y q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η) := by
  classical
  obtain ⟨Xu, hXu, hXe⟩ := eq_norm_smul_unit X
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
  have h1 := displacedPoint_basis e η (q.2 - η)
  rw [add_sub_cancel] at h1
  have h2 : bondSpread c Xu (fun i => ‖X i‖ * q.1 i) = bondSpread c X q.1 := by
    conv_rhs => rw [hXe]
    exact (bondSpread_smul c Xu _ _).symm
  simp only [hb, hu, h1, h2]
end Perturbations
section Bounds
variable {F : BlockFrame} {s a ρA : ℝ} {m : ℕ} {V : F.GaugeField F.top}
private def orderBounds (E E₃ : ℝ) (j : ℕ) : ℝ := if j = 3 then E₃ else E
private theorem runningMax_orderBounds_nonneg (E E₃ : ℝ) (p : ℕ) :
    0 ≤ runningMax (orderBounds E E₃) p := by
  induction p with
  | zero => exact le_rfl
  | succ p ih => exact ih.trans (le_max_left _ _)
private theorem runningMax_orderBounds_le {E E₃ : ℝ} (hE : 0 ≤ E) (h3 : E ≤ E₃) (p : ℕ) (hp : p ≤ 3) :
    runningMax (orderBounds E E₃) p ≤ if p = 3 then E₃ else E := by
  interval_cases p <;> simp [runningMax, orderBounds, hE, h3]
private def PerturbedExpansionBounds (s a ρA ρ κ C E E₃ : ℝ) (m : ℕ) (f : LocalFamily) (V : F.GaugeField F.top) : Prop :=
  ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)) (q : ℕ) (w : Fin q → Perturbation F),
    (∀ b, ‖η b‖ ≤ ρ) → (∀ l, (w l).IsUnit) →
    ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ => subtractTrivial f F y (perturbedField s a ρA m V η w τ)) 0 ∧
    (1 ≤ q → q ≤ 3 →
      |iteratedFDeriv ℝ q (fun τ => subtractTrivial f F y (perturbedField s a ρA m V η w τ)) 0
          fun l => Pi.single l 1| ≤
        C * runningMax (orderBounds E E₃) q *
          Real.exp (-(2 ^ 7 * κ * cellSetDiameter (insert (enclosingCell y) (perturbationCells w)))))
variable {ρ κ C E E₃ : ℝ} {f : LocalFamily}
private theorem jointMixedDeriv_bound (H : PerturbedExpansionBounds s a ρA ρ κ C E E₃ m f V) {l k : ℕ}
    (y : F.Site F.depth) (η : StepVariable (finiteCells F)) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hη : ∀ b, ‖η b‖ ≤ ρ) (hu : ∀ i, ‖u i‖ = 1) (hX : AreUnitVectors X) (h1 : 1 ≤ l + k) (h3 : l + k ≤ 3) :
    |jointMixedDeriv (fun ζ V' => interpolatedExpansion s a ρA m f y ζ V') η V b u c X| ≤
      C * runningMax (orderBounds E E₃) (l + k) *
        Real.exp (-(2 ^ 7 * κ *
          cellSetDiameter (insert (enclosingCell y) (perturbationCells (combinedPerturbations b u c X))))) := by
  unfold jointMixedDeriv
  rw [jointDisplacement_eq_perturbed]
  exact (H y η _ (combinedPerturbations b u c X) hη (combinedPerturbations_isUnit b u c X hu hX)).2 h1 h3
private theorem rotatedEval_contDiffAt (hRM : rotatedEvalContDiffOfDisplacements)
    (H : PerturbedExpansionBounds s a ρA ρ κ C E E₃ m f V)
    (y : F.Site F.depth) (η : StepVariable (finiteCells F)) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hη : ∀ b, ‖η b‖ ≤ ρ) (hX : AreUnitVectors X) :
    ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞)
      (rotatedEval (fun ζ V' => interpolatedExpansion s a ρA m f y ζ V') V c X) (η, 0) := by
  refine hRM F V _ η k c X 3 fun l b u hu => ?_
  rw [jointDisplacement_eq_perturbed]
  exact (H y η _ (combinedPerturbations b u c X) hη (combinedPerturbations_isUnit b u c X hu hX)).1
private theorem weighted_exp_le {κ' r n D C' e' Ek : ℝ} (hκ : 0 < κ') (hr : r ≤ 2 ^ 7 * κ') (hn0 : 0 ≤ n)
    (hn : n ≤ D) (hC : 0 ≤ C') (he : e' ≤ Ek) (hEk : 0 ≤ Ek) :
    C' * e' * Real.exp (-(2 ^ 7 * κ' * D)) ≤ C' * Ek * Real.exp (-(r * n)) := by
  refine mul_le_mul (mul_le_mul_of_nonneg_left he hC) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    (mul_nonneg hC hEk)
  have h1 : r * n ≤ 2 ^ 7 * κ' * n := mul_le_mul_of_nonneg_right hr hn0
  have h2 : 2 ^ 7 * κ' * n ≤ 2 ^ 7 * κ' * D := mul_le_mul_of_nonneg_left hn (by positivity)
  linarith
private theorem top_deriv_bound (H : PerturbedExpansionBounds s a ρA ρ κ C E E₃ m f V) (hκ : 0 < κ) (hE : 0 ≤ E)
    (h3 : E ≤ E₃) (hC : 0 ≤ C) (y : F.Site F.depth) (η : StepVariable (finiteCells F)) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hη : ∀ b, ‖η b‖ ≤ ρ) (h1 : 1 ≤ k) (hk : k ≤ 3) (hX : AreUnitVectors X) :
    |bondDeriv (interpolatedExpansion s a ρA m f y η) V c X| ≤
      C * (if k = 3 then E₃ else E) * Real.exp (-(2 ^ 6 * κ * bondSpan (enclosingCell y) c)) := by
  set w : Fin k → Perturbation F := fun l => Perturbation.top (c l) (X l) with hw
  have e : (fun τ : Fin k → ℝ => interpolatedExpansion s a ρA m f y η (leftTranslate (bondSpread c X τ) V)) =
      fun τ => subtractTrivial f F y (perturbedField s a ρA m V η w τ) := by
    funext τ
    have h1 : perturbedVariable η w τ = η := by simp [perturbedVariable, hw, Perturbation.variableDirection]
    have h2 : perturbedTop V w τ = leftTranslate (bondSpread c X τ) V := rfl
    simp only [interpolatedExpansion, perturbedField, h1, h2]
  unfold bondDeriv
  rw [e]
  refine ((H y η k w hη fun l => hX l).2 h1 hk).trans ?_
  have hEk : 0 ≤ if k = 3 then E₃ else E := by
    split_ifs
    · exact hE.trans h3
    · exact hE
  refine weighted_exp_le hκ (by nlinarith) (Nat.cast_nonneg _) ?_ hC (runningMax_orderBounds_le hE h3 k hk) hEk
  have hs : bondSpan (enclosingCell y) c ≤ cellSetDiameter (insert (enclosingCell y) (perturbationCells w)) :=
    bondSpan_le_diameter (Finset.mem_insert_self _ _) fun l =>
      Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩)
  exact_mod_cast hs
private theorem slope_deriv_bound (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hRM : rotatedEvalContDiffOfDisplacements) (H : PerturbedExpansionBounds s a ρA ρ κ C E E₃ m f V) (hκ : 0 < κ)
    (hE : 0 ≤ E) (h3 : E ≤ E₃) (hC : 0 ≤ C) (y : F.Site F.depth) (η : StepVariable (finiteCells F))
    (b : ↥(chordBonds (finiteCells F))) (e : BondVector) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (hη : ∀ b, ‖η b‖ ≤ ρ) (hk : k ≤ 2) (hX : AreUnitVectors X) (he : ‖e‖ = 1) :
    |bondDeriv (fun V' => bondPartialDeriv (fun ζ => interpolatedExpansion s a ρA m f y ζ V') b η e) V c X| ≤
      C * (if k = 2 then E₃ else E) *
        Real.exp (-(2 ^ 5 * κ * bondSpanWithCell (enclosingCell y) (enclosingCell b.1.1) c)) := by
  set G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
    fun ζ V' => interpolatedExpansion s a ρA m f y ζ V' with hG
  set fn := rotatedEval G V c X with hfn
  have hs : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) fn (η, 0) := rotatedEval_contDiffAt hRM H y η c X hη hX
  have hs1 : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) fn (η, 0) :=
    hs.of_le (by exact_mod_cast (show k + 1 ≤ 3 by omega))
  have hs2 : ContDiffAt ℝ ((1 + k : ℕ) : WithTop ℕ∞) fn (η, 0) := by
    rw [add_comm]
    exact hs1
  have R := hL.1 (JointSpace F k) ℝ
  have e0 : bondDeriv (fun V' => bondPartialDeriv (fun ζ => G ζ V') b η e) V c X =
      derivAlong fn (paramList F k ++ [(bondVariation b e, 0)]) (η, 0) :=
    iteratedFDeriv_slope_eq_derivAlong hL fn η (bondVariation b e) hs1
  have hlen : (paramList F k ++ [((bondVariation b e, 0) : JointSpace F k)]).length = k + 1 := by
    simp [paramList_length]
  have e1 : derivAlong fn (paramList F k ++ [(bondVariation b e, 0)]) (η, 0) =
      derivAlong fn ((bondVariation b e, 0) :: paramList F k) (η, 0) :=
    R.perm _ _ _ _ List.perm_append_comm (by rw [hlen]; exact hs1)
  have e2 := (hA F V G η k c X).2 1 ![b] ![e] hs2
  have e3 : pointDirections (k := k) ![b] ![e] = [(bondVariation b e, 0)] := by
    simp [pointDirections, List.ofFn_succ, variableDirection, bondVariation]
  rw [e3] at e2
  have e4 : bondDeriv (fun V' => bondPartialDeriv (fun ζ => G ζ V') b η e) V c X =
      jointMixedDeriv G η V ![b] ![e] c X := by
    rw [e0, e1, e2]
    rfl
  rw [e4]
  have hu : ∀ i : Fin 1, ‖(![e] : Fin 1 → BondVector) i‖ = 1 := fun i => by simpa using he
  refine (jointMixedDeriv_bound H y η ![b] ![e] c X hη hu hX (by omega) (by omega)).trans ?_
  have hEk : 0 ≤ if k = 2 then E₃ else E := by
    split_ifs
    · exact hE.trans h3
    · exact hE
  have hle : runningMax (orderBounds E E₃) (1 + k) ≤ if k = 2 then E₃ else E := by
    have h := runningMax_orderBounds_le hE h3 (1 + k) (by omega)
    by_cases hk2 : k = 2
    · subst hk2
      simpa using h
    · have : 1 + k ≠ 3 := by omega
      simpa [this, hk2] using h
  refine weighted_exp_le hκ (by nlinarith) (Nat.cast_nonneg _) ?_ hC hle hEk
  have hsp : bondSpanWithCell (enclosingCell y) (enclosingCell b.1.1) c ≤
      cellSetDiameter (insert (enclosingCell y) (perturbationCells (combinedPerturbations ![b] ![e] c X))) :=
    bondSpanWithCell_le_diameter (Finset.mem_insert_self _ _)
      (by simpa using bulk_cell_mem (Y := enclosingCell y) ![b] ![e] c X 0)
      (fun l => top_cell_mem _ _ c X l)
  exact_mod_cast hsp
private theorem second_deriv_bound (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hRM : rotatedEvalContDiffOfDisplacements) (H : PerturbedExpansionBounds s a ρA ρ κ C E E₃ m f V) (hκ : 0 < κ)
    (hE : 0 ≤ E) (h3 : E ≤ E₃) (hC : 0 ≤ C) (y : F.Site F.depth) (η : StepVariable (finiteCells F))
    (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector)
    (hη : ∀ b, ‖η b‖ ≤ ρ) (he : ‖e‖ = 1) (he' : ‖e'‖ = 1) :
    |secondDerivAlong (fun ζ => interpolatedExpansion s a ρA m f y ζ V) η (bondVariation b e) (bondVariation b' e')| ≤
      C * E * Real.exp (-(2 ^ 5 * κ * chordBondSpan (enclosingCell y) ![b, b'])) := by
  set G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
    fun ζ V' => interpolatedExpansion s a ρA m f y ζ V' with hG
  set c : Fin 0 → F.Site F.top × Fin 4 := Fin.elim0 with hc
  set X : Fin 0 → imaginaryQuaternions := Fin.elim0 with hXd
  have hX : AreUnitVectors X := fun i => i.elim0
  set fn := rotatedEval G V c X with hfn
  have hs : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) fn (η, 0) := rotatedEval_contDiffAt hRM H y η c X hη hX
  have hf : (fun ζ' => fn (ζ', 0)) = fun ζ => interpolatedExpansion s a ρA m f y ζ V := by
    funext ζ'
    simp only [hfn, rotatedEval, hG, leftTranslate_bondSpread_zero]
  have h1 := second_deriv_eq_derivAlong hL fn η (bondVariation b e) (bondVariation b' e')
    (hs.of_le (by exact_mod_cast (show 2 ≤ 3 by omega)))
  rw [hf] at h1
  have e2 := (hA F V G η 0 c X).2 2 ![b', b] ![e', e] (hs.of_le (by exact_mod_cast (show 2 + 0 ≤ 3 by omega)))
  have e3 : pointDirections (k := 0) ![b', b] ![e', e] ++ parameterDirections _ _ (parameterBasis 0) =
      [((bondVariation b' e', 0) : JointSpace F 0), (bondVariation b e, 0)] := by
    simp [pointDirections, List.ofFn_succ, variableDirection, bondVariation, parameterDirections, parameterBasis]
  rw [e3] at e2
  have e4 : secondDerivAlong (fun ζ => interpolatedExpansion s a ρA m f y ζ V) η (bondVariation b e)
      (bondVariation b' e') = jointMixedDeriv G η V ![b', b] ![e', e] c X := by
    rw [e2]
    exact h1
  rw [e4]
  have hu : ∀ i : Fin 2, ‖(![e', e] : Fin 2 → BondVector) i‖ = 1 := fun i => by
    fin_cases i <;> simpa
  refine (jointMixedDeriv_bound H y η ![b', b] ![e', e] c X hη hu hX (by omega) (by omega)).trans ?_
  have hle : runningMax (orderBounds E E₃) (2 + 0) ≤ E := by
    simpa using runningMax_orderBounds_le hE h3 2 (by omega)
  refine weighted_exp_le hκ (by nlinarith) (Nat.cast_nonneg _) ?_ hC hle hE
  have mb : enclosingCell b.1.1 ∈
      insert (enclosingCell y) (perturbationCells (combinedPerturbations ![b', b] ![e', e] c X)) := by
    simpa using bulk_cell_mem (Y := enclosingCell y) ![b', b] ![e', e] c X 1
  have mb' : enclosingCell b'.1.1 ∈
      insert (enclosingCell y) (perturbationCells (combinedPerturbations ![b', b] ![e', e] c X)) := by
    simpa using bulk_cell_mem (Y := enclosingCell y) ![b', b] ![e', e] c X 0
  have hsp : chordBondSpan (enclosingCell y) ![b, b'] ≤
      cellSetDiameter (insert (enclosingCell y) (perturbationCells (combinedPerturbations ![b', b] ![e', e] c X))) := by
    refine bondSpan_le_diameter (Finset.mem_insert_self _ _) fun l => ?_
    fin_cases l
    · simpa using mb
    · simpa using mb'
  exact_mod_cast hsp
private theorem third_deriv_bound (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hRM : rotatedEvalContDiffOfDisplacements) (H : PerturbedExpansionBounds s a ρA ρ κ C E E₃ m f V) (hκ : 0 < κ)
    (hE : 0 ≤ E) (h3 : E ≤ E₃) (hC : 0 ≤ C) (y : F.Site F.depth) (η : StepVariable (finiteCells F))
    (b b' b'' : ↥(chordBonds (finiteCells F))) (e e' e'' : BondVector)
    (hη : ∀ b, ‖η b‖ ≤ ρ) (he : ‖e‖ = 1) (he' : ‖e'‖ = 1) (he'' : ‖e''‖ = 1) :
    |thirdDerivAlong (fun ζ => interpolatedExpansion s a ρA m f y ζ V) η (bondVariation b e) (bondVariation b' e')
        (bondVariation b'' e'')| ≤
      C * E₃ * Real.exp (-(2 ^ 5 * κ * chordBondSpan (enclosingCell y) ![b, b', b''])) := by
  set G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
    fun ζ V' => interpolatedExpansion s a ρA m f y ζ V' with hG
  set c : Fin 0 → F.Site F.top × Fin 4 := Fin.elim0 with hc
  set X : Fin 0 → imaginaryQuaternions := Fin.elim0 with hXd
  have hX : AreUnitVectors X := fun i => i.elim0
  set fn := rotatedEval G V c X with hfn
  have hs : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) fn (η, 0) := rotatedEval_contDiffAt hRM H y η c X hη hX
  have hf : (fun ζ' => fn (ζ', 0)) = fun ζ => interpolatedExpansion s a ρA m f y ζ V := by
    funext ζ'
    simp only [hfn, rotatedEval, hG, leftTranslate_bondSpread_zero]
  have h1 := third_deriv_eq_derivAlong hL fn η (bondVariation b e) (bondVariation b' e') (bondVariation b'' e'') hs
  rw [hf] at h1
  have e2 := (hA F V G η 0 c X).2 3 ![b'', b', b] ![e'', e', e]
    (hs.of_le (by exact_mod_cast (show 3 + 0 ≤ 3 by omega)))
  have e3 : pointDirections (k := 0) ![b'', b', b] ![e'', e', e] ++ parameterDirections _ _ (parameterBasis 0) =
      [((bondVariation b'' e'', 0) : JointSpace F 0), (bondVariation b' e', 0), (bondVariation b e, 0)] := by
    simp [pointDirections, List.ofFn_succ, variableDirection, bondVariation, parameterDirections, parameterBasis]
  rw [e3] at e2
  have e4 : thirdDerivAlong (fun ζ => interpolatedExpansion s a ρA m f y ζ V) η (bondVariation b e)
      (bondVariation b' e') (bondVariation b'' e'') = jointMixedDeriv G η V ![b'', b', b] ![e'', e', e] c X := by
    rw [e2]
    exact h1
  rw [e4]
  have hu : ∀ i : Fin 3, ‖(![e'', e', e] : Fin 3 → BondVector) i‖ = 1 := fun i => by
    fin_cases i <;> simpa
  refine (jointMixedDeriv_bound H y η ![b'', b', b] ![e'', e', e] c X hη hu hX (by omega) (by omega)).trans ?_
  have hle : runningMax (orderBounds E E₃) (3 + 0) ≤ E₃ := by
    simpa using runningMax_orderBounds_le hE h3 3 (by omega)
  refine weighted_exp_le hκ (by nlinarith) (Nat.cast_nonneg _) ?_ hC hle (hE.trans h3)
  have mb : enclosingCell b.1.1 ∈
      insert (enclosingCell y) (perturbationCells (combinedPerturbations ![b'', b', b] ![e'', e', e] c X)) := by
    simpa using bulk_cell_mem (Y := enclosingCell y) ![b'', b', b] ![e'', e', e] c X 2
  have mb' : enclosingCell b'.1.1 ∈
      insert (enclosingCell y) (perturbationCells (combinedPerturbations ![b'', b', b] ![e'', e', e] c X)) := by
    simpa using bulk_cell_mem (Y := enclosingCell y) ![b'', b', b] ![e'', e', e] c X 1
  have mb'' : enclosingCell b''.1.1 ∈
      insert (enclosingCell y) (perturbationCells (combinedPerturbations ![b'', b', b] ![e'', e', e] c X)) := by
    simpa using bulk_cell_mem (Y := enclosingCell y) ![b'', b', b] ![e'', e', e] c X 0
  have hsp : chordBondSpan (enclosingCell y) ![b, b', b''] ≤
      cellSetDiameter (insert (enclosingCell y)
        (perturbationCells (combinedPerturbations ![b'', b', b] ![e'', e', e] c X))) := by
    refine bondSpan_le_diameter (Finset.mem_insert_self _ _) fun l => ?_
    fin_cases l
    · simpa using mb
    · simpa using mb'
    · simpa using mb''
  exact_mod_cast hsp
private theorem centredExpansionBounds_of_perturbed (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hRM : rotatedEvalContDiffOfDisplacements) {star : Bool} {δ : ℝ} {L : ℕ}
    (hEnd : ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)) (V' : F.GaugeField F.top),
      interpolatedExpansion s a ρA m f y η V' = centredExpansion star a ρA m f y η V')
    (H : PerturbedExpansionBounds s a ρA ρ κ C E E₃ m f V) (hκ : 0 < κ) (hE : 0 ≤ E) (h3 : E ≤ E₃) (hC : 0 ≤ C) :
    CentredExpansionBounds star a ρA ρ κ δ E E₃ C L m f V := by
  have hEq : ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)),
      centredExpansion star a ρA m f y η = interpolatedExpansion s a ρA m f y η :=
    fun y η => funext fun V' => (hEnd y η V').symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y η k c X hη
    simp only [hEq]
    exact interpolatedExpansion_contDiffAt (fun l j b u c X hu hX => by
      rw [jointDisplacement_eq_perturbed]
      exact_mod_cast (H y η _ (combinedPerturbations b u c X) hη
        (combinedPerturbations_isUnit b u c X hu hX)).1) c X
  · rintro Y y η k c X rfl hη h1 hk hX
    rw [hEq]
    refine (top_deriv_bound H hκ hE h3 hC y η c X (fun b => (hη b).le) h1 hk hX).trans ?_
    have hEk : 0 ≤ if k = 3 then E₃ else E := by
      split_ifs
      · exact hE.trans h3
      · exact hE
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC hEk)
    have hW : 0 ≤ 1 / torusDecayFactor L δ ((L : ℝ) * bondSpan (enclosingCell y) c / 16) := by
      have hpos : 0 < torusDecayFactor L δ ((L : ℝ) * bondSpan (enclosingCell y) c / 16) := by
        rw [torusDecayFactor]
        exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
      exact (one_div_pos.2 hpos).le
    linarith
  · intro y η b e k c X hη hk hX he
    simp only [hEq]
    exact slope_deriv_bound hL hA hRM H hκ hE h3 hC y η b e c X (fun b => (hη b).le) hk hX he
  · intro y η b b' e e' hη he he'
    simp only [hEq]
    exact second_deriv_bound hL hA hRM H hκ hE h3 hC y η b b' e e' (fun b => (hη b).le) he he'
  · intro y η b b' b'' e e' e'' hη he he' he''
    simp only [hEq]
    exact third_deriv_bound hL hA hRM H hκ hE h3 hC y η b b' b'' e e' e'' (fun b => (hη b).le) he he' he''
end Bounds
section Parameters
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private structure StepConstraints (T : StepParameters) : Prop where
  blockSide_large : 2 ^ 40 ≤ T.L
  n₀_large : 64 ≤ T.n₀
  rate_le : 2 ^ 9 * T.κ ≤ T.chainParams.κ₂
  expansion_bound : ∃ Cb : ℝ, 0 < Cb ∧ Cb ≤ T.Ct ∧
    ExpansionAlongPerturbationsAt (fun k => 16 ^ k * T.chainParams.Kk k) T.chainParams.κ₂ T.L Cb
private theorem eventually_stepConstraints (hB : ExpansionAlongPerturbationsUniformInRate) :
    EventuallyInParameters StepConstraints := by
  intro a _
  refine ⟨2 ^ 40, fun L hL hL₀ c hc => ?_⟩
  have hcl := hc.classical.1
  have hκ₂ : 0 < c.κ₂ := by nlinarith
  have hKk : ∀ k, 0 < c.Kk k := hcl.2.2.2.2.2.2.2
  obtain ⟨Cb, hCb, hRow⟩ := hB (fun k => 16 ^ k * c.Kk k) c.κ₂ L
    (fun k => by have := hKk k; positivity) hκ₂ hL hL₀
  refine ⟨Cb, fun Ct hCt => ?_⟩
  refine ⟨c.κ₂ / 2 ^ 9, by positivity, fun κ hκ hκle => ?_⟩
  have hr : 2 ^ 9 * κ ≤ c.κ₂ := by
    have := mul_le_mul_of_nonneg_left hκle (by positivity : (0 : ℝ) ≤ 2 ^ 9)
    linarith
  refine ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩
  refine ⟨0, fun idx _ => ?_⟩
  refine ⟨1, one_pos, fun σ _ _ p _ => ?_⟩
  refine ⟨0, fun Cs _ E _ => ?_⟩
  refine ⟨64, fun n₀ hn₀ => ?_⟩
  refine ⟨0, fun CE _ => ?_⟩
  refine ⟨0, fun g _ => ?_⟩
  exact ⟨hL₀, hn₀, hr, Cb, hCb, hCt, hRow⟩
end Parameters
theorem centredExpansionsBounded_holds (hB : ExpansionAlongPerturbationsUniformInRate)
    (hDec : interpolatedFrameDecayStatement) (hNear : interpolatedFramesControlled)
    (hEnds : interpolationAtEndpoints) (hL : DerivAlongRulesHold)
    (hA : JointMixedDerivEqDerivAlong) (hRM : rotatedEvalContDiffOfDisplacements)
    (hJoin : EventuallyInParametersCombines) (hC : BlocksCoverLowerLevel) :
    CentredExpansionsBounded := by
  classical
  obtain ⟨Cz, -, hD⟩ := hDec
  have hP := hJoin.1 _ _ (hJoin.1 _ _ hD hNear) (eventually_stepConstraints hB)
  refine hJoin.2 _ _ ?_ hP
  rintro T hT ⟨⟨hd, hn⟩, hnum⟩ t x f F V star hx hf hF hV
  obtain ⟨hFL, hFt, n', hside, hn₀⟩ := id hF
  subst hFt
  have hn64 : 64 ≤ n' := hnum.n₀_large.trans hn₀
  have hsd : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
  have hLodd : Odd F.blockSide := hFL ▸ hT.odd_L
  have hs0 : 0 ≤ segmentEnd star := by
    unfold segmentEnd
    split_ifs <;> norm_num
  have hs1 : segmentEnd star ≤ 1 := by
    unfold segmentEnd
    split_ifs <;> norm_num
  have hEnd : ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)) (V' : F.GaugeField F.top),
      interpolatedExpansion (segmentEnd star) T.a T.chainParams.ρA (frameRadius x) f y η V' =
        centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η V' := fun y η V' =>
    (hEnds F star T.a T.chainParams.ρA 0 0 0 (frameRadius x) V').2.2.2.1 f y η
  obtain ⟨-, hsmall⟩ := (hn F.depth x hx).single F V (segmentEnd star) hF hV hs0 hs1
  have hdk := hd x F.depth F V (segmentEnd star) hx hF hV hs0 hs1
  obtain ⟨Cb, hCb, hCt, hRow⟩ := hnum.expansion_bound
  have hκ := hT.κ_pos
  have hη₃ := hT.η₃_pos
  have hη₁ := hT.η₃_le_one
  have hE1 := hT.one_le_E
  have hσ := hT.σ_pos
  have hE0 : 0 ≤ T.E := by linarith
  have h3 : T.E ≤ T.energyRatio := by
    show T.E ≤ T.E / T.η₃
    rw [le_div_iff₀ hη₃]
    nlinarith
  have he0 : ∀ j, 0 ≤ orderBounds T.E T.energyRatio j := fun j => by
    unfold orderBounds
    split_ifs
    · exact hE0.trans h3
    · exact hE0
  have hHas : HasBoundedDerivatives T.L F.depth T.n₀ T.σ (T.κ / 2 ^ 10) 3 (orderBounds T.E T.energyRatio) f :=
    ⟨fun F' hF' y' W hW j' c' X' => by exact_mod_cast hf.smooth F' hF' y' W hW j' c' X', hf.gauge_invariant,
      fun F' hF' y' W j' c' X' hW h1 h3' hX' => hf.decay F' hF' y' W j' c' X' hW h1 h3' hX'⟩
  have hcub : IsLargeCubicTorus F := ⟨n', hn64, hside⟩
  have hlow : IsCubicTorusAbove T.L F.depth T.n₀ F := by
    refine ⟨hFL, rfl, n', hside, ?_⟩
    have hLpos : 1 ≤ T.L := hT.odd_L.pos
    calc T.n₀ ≤ n' := hn₀
      _ ≤ n' * T.L := Nat.le_mul_of_pos_right _ hLpos
  have hρA : T.chainParams.ρA ≤ 1 := hT.chain_admissible.classical.1.2.1
  have hρ' : T.ballRadius = T.σ / 64 := rfl
  have H : PerturbedExpansionBounds (segmentEnd star) T.a T.chainParams.ρA T.ballRadius T.κ T.Ct T.E T.energyRatio
      (frameRadius x) f V := by
    intro y η q w hη hw
    have hmain := hRow T.κ hκ hnum.rate_le F T.n₀ 3 q (frameRadius x) T.σ (segmentEnd star) T.a T.chainParams.ρA
      (orderBounds T.E T.energyRatio) f V η w y hFL hcub hlow (by norm_num) he0 hHas
      (fun pl hpl => by
        have := hsmall.small_curvature_nearby η (fun b => by rw [← hρ']; exact hη b) pl hpl
        linarith)
      (fun x' i ht => by
        have hch : (x', i) ∈ chordBonds (finiteCells F) := by
          unfold chordBonds innerBonds
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
          exact ⟨⟨hC F hLodd hsd x', hC F hLodd hsd _⟩, ht⟩
        have h1 := hsmall.norm_add_le (x', i) hch
        have e1 : stepCoordinates η x' i = toImaginary (η ⟨(x', i), hch⟩) := by
          unfold stepCoordinates
          rw [dif_pos hch]
        have h2 := hη ⟨(x', i), hch⟩
        have h4 : interpolatedCoords (segmentEnd star) T.a T.chainParams.ρA (frameRadius x) V η x' i =
            interpolatedFrame (segmentEnd star) T.a T.chainParams.ρA (frameRadius x) (x', i) V +
              stepCoordinates η x' i := rfl
        rw [h4, e1]
        have h5 := norm_add_le (interpolatedFrame (segmentEnd star) T.a T.chainParams.ρA (frameRadius x) (x', i) V)
          (toImaginary (η ⟨(x', i), hch⟩))
        rw [norm_toImaginary] at h5
        linarith)
      (fun d hdm => (hdk d hdm).2.1) (fun d hdm k' c' X' h1 hX' => (hdk d hdm).2.2 k' c' X' h1 hX') hw
    refine ⟨by exact_mod_cast hmain.1, fun h1 h3' => (hmain.2 h1 h3').trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCt (runningMax_orderBounds_nonneg T.E T.energyRatio q)) (Real.exp_pos _).le
  exact centredExpansionBounds_of_perturbed hL hA hRM hEnd H hκ hE0 h3 (hCb.le.trans hCt)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
