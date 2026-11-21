import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastFieldProof
import YangMills.Construction.SummableBoundsOfTheFlow.GapObservableHasTheConditionsOfThirdOrder
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAtATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftOfTheChart
import YangMills.Construction.SummableBoundsOfTheFlow.RimBoundsGiveASize
import YangMills.Construction.SummableBoundsOfTheFlow.ThirdOrderWithTwoFamiliesProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion RealInnerProductSpace
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Estimates TorusComparison ConvexObservables
namespace Interpolation
private theorem fderiv_apply_along_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Λ : E → E →L[ℝ] ℝ} {g : E → E} {v : E} (hΛ : DifferentiableAt ℝ Λ v) (hg : DifferentiableAt ℝ g v) :
    DifferentiableAt ℝ (fun u => Λ u (g u)) v ∧
      ‖fderiv ℝ (fun u => Λ u (g u)) v‖ ≤ ‖fderiv ℝ Λ v‖ * ‖g v‖ + ‖Λ v‖ * ‖fderiv ℝ g v‖ := by
  have h := hΛ.hasFDerivAt.clm_apply hg.hasFDerivAt
  refine ⟨h.differentiableAt, ?_⟩
  rw [h.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  refine (norm_add_le _ _).trans ?_
  have a1 : ‖Λ v (fderiv ℝ g v u)‖ ≤ ‖Λ v‖ * (‖fderiv ℝ g v‖ * ‖u‖) :=
    ((Λ v).le_opNorm _).trans (mul_le_mul_of_nonneg_left ((fderiv ℝ g v).le_opNorm u) (norm_nonneg _))
  have a2 : ‖fderiv ℝ Λ v u (g v)‖ ≤ ‖fderiv ℝ Λ v‖ * ‖u‖ * ‖g v‖ :=
    ((fderiv ℝ Λ v u).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((fderiv ℝ Λ v).le_opNorm u) (norm_nonneg _))
  nlinarith
private theorem translated_field_deriv_bound {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {Θ : W → W →L[ℝ] W} (ι₁ : E →L[ℝ] W) (π₁ : W →L[ℝ] E)
    (w A X : W) (v : E) {B : ℝ}
    (hd : DifferentiableAt ℝ Θ (w + ι₁ v)) (hB : ‖iteratedFDeriv ℝ 1 Θ (w + ι₁ v)‖ ≤ B) :
    DifferentiableAt ℝ (fun u => π₁ (A + Θ (w + ι₁ u) X)) v ∧
      ‖fderiv ℝ (fun u => π₁ (A + Θ (w + ι₁ u) X)) v‖ ≤ ‖π₁‖ * B * ‖X‖ * ‖ι₁‖ := by
  rw [norm_iteratedFDeriv_one] at hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have h1 : HasFDerivAt (fun u : E => w + ι₁ u) ι₁ v := ι₁.hasFDerivAt.const_add w
  have h2 : HasFDerivAt (fun u : E => Θ (w + ι₁ u)) ((fderiv ℝ Θ (w + ι₁ v)).comp ι₁) v :=
    hd.hasFDerivAt.comp v h1
  have h3 : HasFDerivAt (fun u : E => Θ (w + ι₁ u) X)
      ((ContinuousLinearMap.apply ℝ W X).comp ((fderiv ℝ Θ (w + ι₁ v)).comp ι₁)) v :=
    (ContinuousLinearMap.apply ℝ W X).hasFDerivAt.comp v h2
  have h4 := (π₁.hasFDerivAt.comp v (h3.const_add A))
  refine ⟨h4.differentiableAt, ?_⟩
  have e : (fun u => π₁ (A + Θ (w + ι₁ u) X)) = π₁ ∘ fun u => A + Θ (w + ι₁ u) X := rfl
  rw [e, h4.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  calc _ ≤ ‖π₁‖ * ‖fderiv ℝ Θ (w + ι₁ v) (ι₁ u) X‖ := π₁.le_opNorm _
    _ ≤ ‖π₁‖ * (‖fderiv ℝ Θ (w + ι₁ v) (ι₁ u)‖ * ‖X‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖π₁‖ * ((B * (‖ι₁‖ * ‖u‖)) * ‖X‖) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) (norm_nonneg _)
        exact ((fderiv ℝ Θ (w + ι₁ v)).le_opNorm _).trans
          (mul_le_mul hB (ι₁.le_opNorm u) (norm_nonneg _) hB0)
    _ = _ := by ring
section BondSums
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem hasFDerivAt_bond_proj (b : ι) (η : BondField ι) :
    HasFDerivAt (fun ζ : BondField ι => ζ b)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b) η :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt
private theorem bondGradNorm_single_bond_le {f : BondVector → ℝ} (b : ι) {η : BondField ι}
    (hf : DifferentiableAt ℝ f (η b)) (b' : ι) :
    bondGradNorm (fun ζ : BondField ι => f (ζ b)) b' η ≤
      if b' = b then ‖fderiv ℝ f (η b)‖ else 0 := by
  have hp : HasFDerivAt (fun ζ : BondField ι => f (ζ b))
      ((fderiv ℝ f (η b)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b)) η :=
    hf.hasFDerivAt.comp η (hasFDerivAt_bond_proj b η)
  unfold bondGradNorm
  rw [hp.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by split_ifs <;> positivity) fun u => ?_
  split_ifs with h
  · subst h
    simpa using (fderiv ℝ f (η b')).le_opNorm u
  · simp [Pi.single_eq_of_ne (Ne.symm h)]
private theorem hasFDerivAt_bond_sum {S : Finset ι} {G : ι → BondVector → ℝ} {η : BondField ι}
    (hG : ∀ b, DifferentiableAt ℝ (G b) (η b)) :
    HasFDerivAt (fun ζ : BondField ι => ∑ b ∈ S, G b (ζ b))
      (∑ b ∈ S, (fderiv ℝ (G b) (η b)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b)) η :=
  HasFDerivAt.fun_sum fun b _ => (hG b).hasFDerivAt.comp η (hasFDerivAt_bond_proj b η)
private theorem fderiv_bond_sum_bondVariation {S : Finset ι} {G : ι → BondVector → ℝ} {η : BondField ι}
    (hG : ∀ b, DifferentiableAt ℝ (G b) (η b)) (b : ι) (u : BondVector) :
    fderiv ℝ (fun ζ : BondField ι => ∑ b ∈ S, G b (ζ b)) η (bondVariation b u) =
      if b ∈ S then fderiv ℝ (G b) (η b) u else 0 := by
  rw [(hasFDerivAt_bond_sum hG).fderiv]
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, bondVariation]
  have : ∀ b' ∈ S, fderiv ℝ (G b') (η b') ((Pi.single b u : BondField ι) b') =
      if b' = b then fderiv ℝ (G b) (η b) u else 0 := by
    intro b' _
    by_cases h : b' = b
    · subst h
      simp
    · simp [h]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' S b]
private theorem bondGradNorm_bond_sum_le {S : Finset ι} {G : ι → BondVector → ℝ} {η : BondField ι}
    (hG : ∀ b, DifferentiableAt ℝ (G b) (η b)) (b : ι) :
    bondGradNorm (fun ζ : BondField ι => ∑ b ∈ S, G b (ζ b)) b η ≤
      if b ∈ S then ‖fderiv ℝ (G b) (η b)‖ else 0 := by
  unfold bondGradNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (by split_ifs <;> positivity) fun u => ?_
  have e : ((fderiv ℝ (fun ζ : BondField ι => ∑ b ∈ S, G b (ζ b)) η).comp
      (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)) u =
      fderiv ℝ (fun ζ : BondField ι => ∑ b ∈ S, G b (ζ b)) η (bondVariation b u) := rfl
  rw [e, fderiv_bond_sum_bondVariation hG]
  split_ifs with h
  · exact (fderiv ℝ (G b) (η b)).le_opNorm u
  · simp
private theorem ballDensity_congr {r : ℝ} {p : ℝ → ℝ} {Φ₁ Φ₂ : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < r) → Φ₁ η = Φ₂ η) :
    ballDensity (cutoffFactor r p) Φ₁ = ballDensity (cutoffFactor r p) Φ₂ := by apply _root_.YangMills.Construction.Interpolation.ExpansionThirdDeriv.ballDensity_congr <;> assumption
private theorem hasLocalSize_congr {r : ℝ} {p : ℝ → ℝ} {Φ f g : BondField ι → ℝ} {Cq : ℕ → ℝ}
    {x κ a : ℝ} {dZ : ι → ℝ} (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < r) → f η = g η)
    (hs : HasLocalSize r (cutoffFactor r p) Φ Cq x κ a dZ f) :
    HasLocalSize r (cutoffFactor r p) Φ Cq x κ a dZ g := by apply _root_.YangMills.Construction.ThirdOrderCovariance.hasLocalSize_congr <;> assumption
end BondSums
private theorem imaginaryCoords_toImaginary (v : BondVector) : _root_.YangMills.Construction.Interpolation.imaginaryCoords (toImaginary v) = v := by apply _root_.YangMills.Construction.FrameInterpolationProof.imaginaryCoords_toImaginary <;> assumption
private theorem inner_toImaginary (v : BondVector) (w : imaginaryQuaternions) :
    ⟪((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]), (w : ℍ[ℝ])⟫ = ⟪v, _root_.YangMills.Construction.Interpolation.imaginaryCoords w⟫ := by apply _root_.YangMills.Construction.FrameInterpolationProof.inner_toImaginary <;> assumption
private def toImaginaryCLM (h : ImaginaryCoordinatesIsometric) : BondVector →L[ℝ] imaginaryQuaternions :=
  LinearMap.mkContinuous
    { toFun := toImaginary
      map_add' := h.1
      map_smul' := h.2.1 } 1 fun v => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact (h.2.2.1 v).le
private theorem toImaginaryCLM_norm_le (h : ImaginaryCoordinatesIsometric) : ‖toImaginaryCLM h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _
private theorem norm_imaginaryCoords (h : ImaginaryCoordinatesIsometric) (w : imaginaryQuaternions) :
    ‖_root_.YangMills.Construction.Interpolation.imaginaryCoords w‖ = ‖w‖ := by
  obtain ⟨v, rfl⟩ := h.2.2.2.1 w
  rw [imaginaryCoords_toImaginary, h.2.2.1]
private def imaginaryCoordsCLM (h : ImaginaryCoordinatesIsometric) : imaginaryQuaternions →L[ℝ] BondVector :=
  LinearMap.mkContinuous
    { toFun := _root_.YangMills.Construction.Interpolation.imaginaryCoords
      map_add' := fun a b => by
        obtain ⟨u, rfl⟩ := h.2.2.2.1 a
        obtain ⟨v, rfl⟩ := h.2.2.2.1 b
        rw [← h.1, imaginaryCoords_toImaginary, imaginaryCoords_toImaginary, imaginaryCoords_toImaginary]
      map_smul' := fun c a => by
        obtain ⟨u, rfl⟩ := h.2.2.2.1 a
        rw [← h.2.1, imaginaryCoords_toImaginary, imaginaryCoords_toImaginary]
        rfl } 1 fun w => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact (norm_imaginaryCoords h w).le
private theorem imaginaryCoordsCLM_norm_le (h : ImaginaryCoordinatesIsometric) : ‖imaginaryCoordsCLM h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _
section TopFields
variable {F : BlockFrame}
private theorem bondDeriv_zero_order {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : F.GaugeField F.top → E) (V : F.GaugeField F.top) (c : Fin 0 → F.Site F.top × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.bondDeriv_zero <;> assumption
private theorem cellSupDist_le_bondSpan_cons {k : ℕ} (Z : F.Cell) (c : F.Site F.top × Fin 4)
    (c' : Fin k → F.Site F.top × Fin 4) :
    cellSupDist Z c.1 ≤ bondSpan Z (Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4) := by apply _root_.YangMills.SharedProofs.p4114 <;> assumption
open Classical in
private theorem topVariationField_facts (hIm : ImaginaryCoordinatesIsometric) (hU : RightTranslationDerivUnique)
    {Θc : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions} {Cc : ℝ} (hCc : 0 ≤ Cc)
    (hΘc : ∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Θc w X))
    (hΘd : ∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Θc w)
    (hΘb : ∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 2 → ‖iteratedFDeriv ℝ j Θc w‖ ≤ Cc)
    {Θ : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions}
    (hΘ : ∀ w X' : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X' (Θ w X'))
    {s a ρA r κ C : ℝ} {m : ℕ} {V : F.GaugeField F.top} (hf : TopVariationRepresentation s a ρA r κ C m V)
    (hκ : 0 < κ) (hC : 0 ≤ C) (b : ↥(chordBonds (finiteCells F))) (c₁ : F.Site F.top × Fin 4)
    {X₁ : imaginaryQuaternions} (hX₁ : ‖X₁‖ = 1) (hw : ‖interpolatedFrame s a ρA m b.1 V‖ + r ≤ 1 / 4) :
    ∃ z : BondVector → BondVector, ∀ v : BondVector, ‖v‖ < r →
      _root_.YangMills.Construction.Interpolation.imaginaryCoords (topVariationField Θ s a ρA m c₁ X₁ b.1 (toImaginary v) V) = z v ∧
      DifferentiableAt ℝ z v ∧
      ‖z v‖ ≤ C * Real.exp (-(2 ^ 6 * κ * bondDistToTopBond b c₁)) ∧
      ‖fderiv ℝ z v‖ ≤ Cc * Real.exp (-(2 ^ 6 * κ * bondDistToTopBond b c₁)) := by
  obtain ⟨Θ', hΘ', -, hdec⟩ := hf.exists_representation
  obtain ⟨w, hwd⟩ : ∃ w, w = interpolatedFrame s a ρA m b.1 V := ⟨_, rfl⟩
  rw [← hwd] at hw
  obtain ⟨A, hA⟩ : ∃ A, A = bondDeriv (interpolatedFrame s a ρA m b.1) V (fun _ : Fin 1 => c₁)
      (fun _ => X₁) := ⟨_, rfl⟩
  have hsm : ∀ v : BondVector, ‖v‖ < r → ‖w + toImaginary v‖ ≤ 1 / 4 := by
    intro v hv
    have := norm_add_le w (toImaginary v)
    rw [hIm.2.2.1] at this
    linarith
  have hpi : ∀ v : BondVector, ‖v‖ < r → ‖w + toImaginary v‖ < Real.pi := fun v hv => by
    have := hsm v hv
    have := Real.pi_gt_three
    linarith
  have e1 : ∀ v : BondVector, ‖v‖ < r → Θ (w + toImaginary v) X₁ = Θc (w + toImaginary v) X₁ :=
    fun v hv => hU _ X₁ _ _ (hpi v hv) (hΘ _ _ (hpi v hv)) (hΘc _ _ (hpi v hv))
  have e2 : ∀ v : BondVector, ‖v‖ < r → Θ' (w + toImaginary v) X₁ = Θc (w + toImaginary v) X₁ :=
    fun v hv => hU _ X₁ _ _ (hpi v hv) (hΘ' _ _ (hpi v hv)) (hΘc _ _ (hpi v hv))
  obtain ⟨ε, hε⟩ : ∃ ε, ε = Real.exp (-(2 ^ 6 * κ * bondDistToTopBond b c₁)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact Real.exp_pos _
  rw [← hε]
  by_cases ind : IsCrossingBond b.1 ∧ (enclosingCell b.1.1, b.1.2) = c₁
  · refine ⟨fun v => imaginaryCoordsCLM hIm (A + Θc (w + toImaginaryCLM hIm v) X₁), fun v hv => ?_⟩
    have hd1 : ε = 1 := by
      have h0 : bondDistToTopBond b c₁ = 0 := by
        have hc : c₁.1 = enclosingCell b.1.1 := (congrArg Prod.fst ind.2).symm
        simp [bondDistToTopBond, hc, cellSupDist]
      rw [hε, h0]
      simp
    have hval : ∀ T' : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions,
        T' (w + toImaginary v) X₁ = Θc (w + toImaginary v) X₁ →
        _root_.YangMills.Construction.Interpolation.imaginaryCoords (topVariationField T' s a ρA m c₁ X₁ b.1 (toImaginary v) V) =
          imaginaryCoordsCLM hIm (A + Θc (w + toImaginaryCLM hIm v) X₁) := by
      intro T' hT'
      unfold topVariationField
      rw [if_pos ind, ← hwd, ← hA, hT']
      rfl
    have hd : DifferentiableAt ℝ Θc (w + toImaginaryCLM hIm v) :=
      (hΘd _ ((hsm v hv).trans (by norm_num))).differentiableAt (by norm_num)
    have hb : ‖iteratedFDeriv ℝ 1 Θc (w + toImaginaryCLM hIm v)‖ ≤ Cc :=
      hΘb (w + toImaginaryCLM hIm v) 1 ((hsm v hv).trans (by norm_num)) (by norm_num)
    obtain ⟨f1, f2⟩ :=
      translated_field_deriv_bound (toImaginaryCLM hIm) (imaginaryCoordsCLM hIm) w A X₁ v hd hb
    refine ⟨hval Θ (e1 v hv), f1, ?_, ?_⟩
    · show ‖imaginaryCoordsCLM hIm (A + Θc (w + toImaginaryCLM hIm v) X₁)‖ ≤ _
      rw [← hval Θ' (e2 v hv), norm_imaginaryCoords hIm]
      have := hdec c₁ X₁ b (toImaginary v) 0 Fin.elim0 Fin.elim0 hX₁ (by rwa [hIm.2.2.1]) (by norm_num)
        (fun l => l.elim0)
      rw [bondDeriv_zero_order (topVariationField Θ' s a ρA m c₁ X₁ b.1 (toImaginary v))] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hC)
      rw [hε]
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      have h1 : (cellSupDist (enclosingCell b.1.1) c₁.1 : ℝ) ≤
          bondSpan (enclosingCell b.1.1) (Fin.cons c₁ Fin.elim0 : Fin 1 → _) := by
        exact_mod_cast cellSupDist_le_bondSpan_cons (enclosingCell b.1.1) c₁ Fin.elim0
      have h2 : (0 : ℝ) ≤
          bondSpan (enclosingCell b.1.1) (Fin.cons c₁ Fin.elim0 : Fin 1 → F.Site F.top × Fin 4) :=
        Nat.cast_nonneg _
      have h3 : bondDistToTopBond b c₁ = (cellSupDist (enclosingCell b.1.1) c₁.1 : ℝ) := rfl
      rw [h3]
      nlinarith
    · rw [hd1, mul_one]
      refine f2.trans ?_
      rw [hX₁, mul_one]
      have b1 := imaginaryCoordsCLM_norm_le hIm
      have b2 := toImaginaryCLM_norm_le hIm
      calc _ ≤ 1 * Cc * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right b1 hCc) b2 (ContinuousLinearMap.opNorm_nonneg _)
              (by positivity)
        _ = Cc := by ring
  · refine ⟨fun _ => _root_.YangMills.Construction.Interpolation.imaginaryCoords A, fun v hv => ?_⟩
    have hval : ∀ T' : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions,
        _root_.YangMills.Construction.Interpolation.imaginaryCoords (topVariationField T' s a ρA m c₁ X₁ b.1 (toImaginary v) V) = _root_.YangMills.Construction.Interpolation.imaginaryCoords A := by
      intro T'
      unfold topVariationField
      rw [if_neg ind, ← hA, add_zero]
    refine ⟨hval Θ, differentiableAt_const _, ?_, ?_⟩
    · rw [← hval Θ', norm_imaginaryCoords hIm]
      have := hdec c₁ X₁ b (toImaginary v) 0 Fin.elim0 Fin.elim0 hX₁ (by rwa [hIm.2.2.1]) (by norm_num)
        (fun l => l.elim0)
      rw [bondDeriv_zero_order (topVariationField Θ' s a ρA m c₁ X₁ b.1 (toImaginary v))] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hC)
      rw [hε]
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      have h1 : (cellSupDist (enclosingCell b.1.1) c₁.1 : ℝ) ≤
          bondSpan (enclosingCell b.1.1) (Fin.cons c₁ Fin.elim0 : Fin 1 → _) := by
        exact_mod_cast cellSupDist_le_bondSpan_cons (enclosingCell b.1.1) c₁ Fin.elim0
      have h2 : (0 : ℝ) ≤
          bondSpan (enclosingCell b.1.1) (Fin.cons c₁ Fin.elim0 : Fin 1 → F.Site F.top × Fin 4) :=
        Nat.cast_nonneg _
      have h3 : bondDistToTopBond b c₁ = (cellSupDist (enclosingCell b.1.1) c₁.1 : ℝ) := rfl
      rw [h3]
      nlinarith
    · rw [fderiv_const_apply, norm_zero]
      positivity
end TopFields
private theorem eventuallyInParameters_strengthen {R Q : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → Prop} (h : EventuallyInParameters R)
    (hQ : ∀ T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters, R T → T.IsOrdered → 1 ≤ T.coupling → 1 ≤ T.Cs →
      T.σ * (|T.Ct| + 1) ≤ 1 / 4 → Q T) :
    EventuallyInParameters Q := by
  intro a ha
  obtain ⟨L₀, h⟩ := h a ha
  refine ⟨L₀, fun L hL hL₀ c hc => ?_⟩
  obtain ⟨Ct₀, h⟩ := h L hL hL₀ c hc
  refine ⟨Ct₀, fun Ct hCt => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h Ct hCt
  refine ⟨κ₀, hκ₀, fun κ hκ hκ' => ?_⟩
  obtain ⟨η₀, hη₀, h⟩ := h κ hκ hκ'
  refine ⟨η₀, hη₀, fun η₃ hη hη1 hηa => ?_⟩
  obtain ⟨N₀, h⟩ := h η₃ hη hη1 hηa
  refine ⟨N₀, fun k hk => ?_⟩
  obtain ⟨σ₀, hσ₀, h⟩ := h k hk
  have hc0 : 0 < 4 * (|Ct| + 1) := by positivity
  refine ⟨min σ₀ (1 / (4 * (|Ct| + 1))), lt_min hσ₀ (by positivity), fun σ hσ hσ' p hp => ?_⟩
  obtain ⟨C₀, h⟩ := h σ hσ (hσ'.trans (min_le_left _ _)) p hp
  refine ⟨max C₀ 1, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₀, h⟩ := h Cs ((le_max_left _ _).trans hCs) E hE
  refine ⟨m₀, fun n₀ hn₀ => ?_⟩
  obtain ⟨C₁, h⟩ := h n₀ hn₀
  refine ⟨C₁, fun CE hCE => ?_⟩
  obtain ⟨y₀, h⟩ := h CE hCE
  refine ⟨max y₀ 1, fun y₁ hy => ?_⟩
  refine hQ _ (h y₁ ((le_max_left _ _).trans hy)) ⟨ha, hL, hc, hκ, hη, hη1, hσ, hp, hE⟩
    ((le_max_right _ _).trans hy) ((le_max_right _ _).trans hCs) ?_
  have h1 := hσ'.trans (min_le_right _ _)
  rw [le_div_iff₀ hc0] at h1
  show σ * (|Ct| + 1) ≤ 1 / 4
  linarith
set_option maxHeartbeats 1600000 in
theorem gapObservableThirdOrder_proof (hF : interpolatedFramesStatement) (hC : rightTranslationChartStatement)
    (hU : RightTranslationDerivUnique) (hB : cellBondsCardStatement)
    (hR : localSizeOfCutoffDerivBoundStatement) (hS : radialDirectionalDerivBoundStatement)
    (hL : normalizedBallLawIsProbabilityStatement) (hIm : ImaginaryCoordinatesIsometric) :
    gapObservableThirdOrderStatement := by
  obtain ⟨Cq₀, Cz₀, Cr₀, hFT⟩ := hF
  obtain ⟨Θc, Cc, hCc, hΘc, hΘd, hΘb⟩ := hC
  refine eventuallyInParameters_strengthen hFT ?_
  intro T hT hdr hy hCs hsm N
  have hσ : 0 < T.σ := hdr.σ_pos
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hcut : IsCutoff T.ballRadius T.p := hdr.cutoff
  have hκ : 0 < T.κ := hdr.κ_pos
  have hCs0 : 0 ≤ T.Cs := by linarith
  obtain ⟨Kr, hKr0, hKr⟩ := hS T.ballRadius T.p hρ hcut
  have hK0 : 0 ≤ Kr * (1 + Cc) := by positivity
  obtain ⟨Cq, hCq, hsz⟩ :=
    hR T.ballRadius T.p (Cr₀ (momentParameters T)) (4 * T.L ^ 4) N (Kr * (1 + Cc)) hρ hK0
  refine ⟨1, Cq, one_pos, hCq, ?_⟩
  intro t x s φ F V Y c X Θ hx hs hs1 hφ hTF hV hX hside hΘ
  have hx1 : 1 ≤ x := hy.trans hx
  have hfr := hT t x hx
  have one := hfr.one_torus F V s hTF hV hs hs1
  obtain ⟨ω, hω⟩ : ∃ ω, ω = Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) := ⟨_, rfl⟩
  have hω0 : 0 < ω := by rw [hω]; exact Real.exp_pos _
  rw [← hω]
  have hCtσ : |T.Ct| * T.σ ≤ 1 / 4 := by nlinarith
  obtain ⟨e, he⟩ : ∃ e : ↥(chordBonds (finiteCells F)) → BondVector,
    e = fun b => _root_.YangMills.Construction.Interpolation.imaginaryCoords (frameGap T.a T.chainParams.ρA (frameRadius x) b.1 V) := ⟨_, rfl⟩
  have hen : ∀ b, ‖e b‖ ≤ ω := by
    intro b
    rw [he]
    show ‖_root_.YangMills.Construction.Interpolation.imaginaryCoords (frameGap T.a T.chainParams.ρA (frameRadius x) b.1 V)‖ ≤ ω
    rw [norm_imaginaryCoords hIm]
    refine (one.near_minimizer.norm_eq_and_le b.1 b.2).2.trans ?_
    show T.Ct * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) * T.σ ≤ ω
    rw [← hω]
    have h1 : T.Ct * T.σ ≤ |T.Ct| * T.σ := mul_le_mul_of_nonneg_right (le_abs_self _) hσ.le
    nlinarith
  have hw : ∀ b : ↥(chordBonds (finiteCells F)),
      ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b.1 V‖ + T.ballRadius ≤ 1 / 4 := by
    intro b
    have h1 := one.small.norm_le b.1 b.2
    have h2 : T.Ct * T.σ ≤ |T.Ct| * T.σ := mul_le_mul_of_nonneg_right (le_abs_self _) hσ.le
    show _ + T.σ / 64 ≤ 1 / 4
    nlinarith
  obtain ⟨M, hM⟩ : ∃ M : Fin 1 → LawOnBondVariables ↥(chordBonds (finiteCells F)),
    M = fun _ => ⟨F, V, id, Finset.univ, familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V⟩ :=
      ⟨_, rfl⟩
  have hmix : convexCombinationExponent T.chainParams.lam x (fun _ => 1) M =
      familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V := by
    funext ζ
    have hp : _root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ ζ = ζ := by
      funext b
      simp [_root_.YangMills.Construction.Interpolation.extendByZero]
    have hl : ∀ l, (M l).exponent T.chainParams.lam x ζ =
        familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V ζ := by
      intro l
      rw [hM]
      show familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V (_root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ ζ) +
        ∑ i ∈ Finset.univ \ Finset.univ, x * T.chainParams.lam / 2 * ‖ζ i‖ ^ 2 = _
      rw [hp, Finset.sdiff_self, Finset.sum_empty, add_zero]
    simp [convexCombinationExponent, hl]
  obtain ⟨hconv, hmom, -⟩ := hfr.laws ↥(chordBonds (finiteCells F))
    (fun b b' => (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ)) 1 (fun _ => 1) M
    ⟨fun _ => zero_le_one, by simp⟩
    (fun l => by
      rw [hM]
      exact ⟨hTF, hV, IsIntermediateLaw.ofFamily s φ hs hs1 hφ, Function.injective_id, fun _ _ => rfl⟩)
  rw [hmix] at hconv hmom
  have hd : AEStronglyMeasurable (ballDensity (cutoffFactor T.ballRadius T.p)
      (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V)) volume := by
    obtain ⟨Ψ, K, hag, hIs, -, -⟩ := hconv
    have h1 : Measurable (ballDensity (cutoffFactor T.ballRadius T.p) Ψ) :=
      (hL _ T.ballRadius T.p Ψ hρ hcut hIs.smooth.continuous).2.2.2.2.1
    rw [← ballDensity_congr hag]
    exact h1.aestronglyMeasurable
  obtain ⟨S, hSd⟩ : ∃ S : Finset ↥(chordBonds (finiteCells F)),
    S = Finset.univ.filter fun b => enclosingCell b.1.1 = Y := ⟨_, rfl⟩
  have hOb : blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y V =
      fun η => ∑ b ∈ S, radialDirectionalDeriv T.p (e b) (η b) := by
    funext η
    unfold blockGapObservable
    rw [hSd, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · unfold radialDirectionalDeriv
      rw [inner_toImaginary, he]
    · rfl
  have hSc : S.card ≤ 4 * T.L ^ 4 := by
    have hL' : Odd F.blockSide := by rw [hTF.1]; exact hdr.odd_L
    have h2 : ∀ i, 2 ≤ F.extent i := fun i => by
      have := hside i
      omega
    have := hB F hL' h2 Y
    rw [hTF.1] at this
    rw [hSd]
    exact this
  have hLpos : 1 ≤ 4 * T.L ^ 4 := by
    have : 0 < T.L := hdr.odd_L.pos
    have : 0 < T.L ^ 4 := by positivity
    omega
  have hGd : ∀ (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ < T.ballRadius) → ∀ b,
      DifferentiableAt ℝ (radialDirectionalDeriv T.p (e b)) (η b) := fun η hη b =>
    (hKr (e b) (η b) (hη b)).1.differentiableAt (by norm_num)
  have hrim0 : ∀ u : ℝ, 0 ≤ cutoffDerivSum T.p u := fun u => by
    unfold cutoffDerivSum
    positivity
  have hKe : ∀ b (R : ℝ), 0 ≤ R → Kr * ‖e b‖ * R ≤ Kr * (1 + Cc) * (T.Cs * ω) * R := by
    intro b R hR
    refine mul_le_mul_of_nonneg_right ?_ hR
    have h1 : ‖e b‖ ≤ (1 + Cc) * (T.Cs * ω) := by
      have h2 : ω ≤ T.Cs * ω := le_mul_of_one_le_left hω0.le hCs
      have h3 : T.Cs * ω ≤ (1 + Cc) * (T.Cs * ω) :=
        le_mul_of_one_le_left (by positivity) (by linarith)
      exact (hen b).trans (h2.trans h3)
    calc Kr * ‖e b‖ ≤ Kr * ((1 + Cc) * (T.Cs * ω)) := mul_le_mul_of_nonneg_left h1 hKr0
      _ = _ := by ring
  refine ⟨fun η hη => ?_, ?_, fun b l => ?_⟩
  · rw [hOb]
    exact ContDiffAt.sum fun b _ => (ContDiffAt.comp η (hKr (e b) (η b) (hη b)).1
      (contDiff_apply ℝ BondVector b).contDiffAt)
  · have hh : 0 ≤ T.Cs * ω := by positivity
    have h1 := hsz _ x T.κ (T.Cs * ω) (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V) S
      (bondDistToCell Y) (fun η => ∑ b ∈ S, radialDirectionalDeriv T.p (e b) (η b)) hx1 hh hSc hd
      hmom.cutoff_deriv_moments
      (fun b hb => by
        have : enclosingCell b.1.1 = Y := by
          rw [hSd] at hb
          exact (Finset.mem_filter.1 hb).2
        simp [bondDistToCell, this, cellSupDist])
      (fun η hη => ((hasFDerivAt_bond_sum (S := S) (hGd η hη)).differentiableAt).differentiableWithinAt)
      (fun η hη => by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun b _ =>
          (hKr (e b) (η b) (hη b)).2.1.trans (hKe b _ (hrim0 _)))
      (fun η hη b => by
        refine (bondGradNorm_bond_sum_le (S := S) (hGd η hη) b).trans ?_
        split_ifs with hb
        · refine (hKr (e b) (η b) (hη b)).2.2.1.trans ((hKe b _ (hrim0 _)).trans ?_)
          exact mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun b => cutoffDerivSum T.p ‖η b‖) (fun b _ => hrim0 _) hb)
            (by positivity)
        · exact le_rfl)
    have eα : 1 * (x ^ N)⁻¹ * (T.Cs * ω) = T.Cs * ω * (x ^ N)⁻¹ := by ring
    rw [eα, hOb]
    exact h1
  · obtain ⟨z, hz⟩ :=
      topVariationField_facts hIm hU hCc hΘc hΘd hΘb hΘ one.variation hκ hCs0 b (c l) (hX l) (hw b)
    obtain ⟨ε, hε⟩ : ∃ ε, ε = Real.exp (-(2 ^ 4 * T.κ * bondDistToCell Y b) -
        2 ^ 6 * T.κ * bondDistToTopBond b (c l)) := ⟨_, rfl⟩
    have hε0 : 0 < ε := by rw [hε]; exact Real.exp_pos _
    have eβ : 1 * (x ^ N)⁻¹ * (T.Cs * ω) *
        Real.exp (-(2 ^ 4 * T.κ * bondDistToCell Y b) - 2 ^ 6 * T.κ * bondDistToTopBond b (c l)) =
        T.Cs * ω * ε * (x ^ N)⁻¹ := by rw [hε]; ring
    rw [eβ]
    have hh : 0 ≤ T.Cs * ω * ε := by positivity
    by_cases hb : b ∈ S
    · have hYb : bondDistToCell Y b = 0 := by
        have : enclosingCell b.1.1 = Y := by
          rw [hSd] at hb
          exact (Finset.mem_filter.1 hb).2
        simp [bondDistToCell, this, cellSupDist]
      have hεe : Real.exp (-(2 ^ 6 * T.κ * bondDistToTopBond b (c l))) = ε := by
        rw [hε, hYb]
        congr 1
        ring
      rw [hεe] at hz
      have hL1 : ∀ v : BondVector, ‖v‖ < T.ballRadius →
          DifferentiableAt ℝ (fderiv ℝ (radialDirectionalDeriv T.p (e b))) v :=
        fun v hv => ((hKr (e b) v hv).1.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
      have hfb : ∀ v : BondVector, ‖v‖ < T.ballRadius →
          DifferentiableAt ℝ (fun u => fderiv ℝ (radialDirectionalDeriv T.p (e b)) u (z u)) v ∧
          |fderiv ℝ (radialDirectionalDeriv T.p (e b)) v (z v)| ≤
            Kr * (1 + Cc) * (T.Cs * ω * ε) * cutoffDerivSum T.p ‖v‖ ∧
          ‖fderiv ℝ (fun u => fderiv ℝ (radialDirectionalDeriv T.p (e b)) u (z u)) v‖ ≤
            Kr * (1 + Cc) * (T.Cs * ω * ε) * cutoffDerivSum T.p ‖v‖ := by
        intro v hv
        obtain ⟨-, hz2, hz3, hz4⟩ := hz v hv
        obtain ⟨-, -, a3, a4⟩ := hKr (e b) v hv
        obtain ⟨d1, d2⟩ := fderiv_apply_along_bound (hL1 v hv) hz2
        refine ⟨d1, ?_, ?_⟩
        all_goals
          obtain ⟨R, hRd⟩ : ∃ R, R = cutoffDerivSum T.p ‖v‖ := ⟨_, rfl⟩
          rw [← hRd] at a3 a4 ⊢
          have hR0 : 0 ≤ R := by rw [hRd]; exact hrim0 _
          obtain ⟨B, hBd⟩ : ∃ B, B = Kr * ω * R := ⟨_, rfl⟩
          have hB0 : 0 ≤ B := by rw [hBd]; positivity
          have hEB : Kr * ‖e b‖ * R ≤ B := by
            rw [hBd]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hen b) hKr0) hR0
          have e0 : Kr * (1 + Cc) * (T.Cs * ω * ε) * R = B * ((1 + Cc) * T.Cs * ε) := by
            rw [hBd]
            ring
          rw [e0]
          have hCε : 0 ≤ T.Cs * ε := by positivity
        · have h1 : |fderiv ℝ (radialDirectionalDeriv T.p (e b)) v (z v)| ≤
              ‖fderiv ℝ (radialDirectionalDeriv T.p (e b)) v‖ * ‖z v‖ := by
            rw [← Real.norm_eq_abs]
            exact (fderiv ℝ (radialDirectionalDeriv T.p (e b)) v).le_opNorm _
          refine h1.trans ?_
          calc _ ≤ B * (T.Cs * ε) := mul_le_mul (a3.trans hEB) hz3 (norm_nonneg _) hB0
            _ ≤ B * ((1 + Cc) * T.Cs * ε) := by
                refine mul_le_mul_of_nonneg_left ?_ hB0
                nlinarith
        · refine d2.trans ?_
          calc _ ≤ B * (T.Cs * ε) + B * (Cc * ε) :=
                add_le_add (mul_le_mul (a4.trans hEB) hz3 (norm_nonneg _) hB0)
                  (mul_le_mul (a3.trans hEB) hz4 (norm_nonneg _) hB0)
            _ ≤ B * ((1 + Cc) * T.Cs * ε) := by
                rw [← mul_add]
                refine mul_le_mul_of_nonneg_left ?_ hB0
                have h1 : Cc * ε ≤ Cc * (T.Cs * ε) := by
                  refine mul_le_mul_of_nonneg_left ?_ hCc
                  exact le_mul_of_one_le_left hε0.le hCs
                nlinarith
      have size' := hsz _ x T.κ (T.Cs * ω * ε) (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V) {b}
        (bondDistToCell Y) (fun η => fderiv ℝ (radialDirectionalDeriv T.p (e b)) (η b) (z (η b))) hx1 hh
        (by simpa using hLpos) hd hmom.cutoff_deriv_moments
        (fun b' hb' => by rw [Finset.mem_singleton.1 hb']; exact hYb)
        (fun η hη => (DifferentiableAt.comp
          (g := fun u => fderiv ℝ (radialDirectionalDeriv T.p (e b)) u (z u)) η
          (hfb (η b) (hη b)).1 (hasFDerivAt_bond_proj b η).differentiableAt).differentiableWithinAt)
        (fun η hη => by
          rw [Finset.sum_singleton]
          exact (hfb (η b) (hη b)).2.1)
        (fun η hη b' => by
          refine le_trans (bondGradNorm_single_bond_le
            (f := fun u => fderiv ℝ (radialDirectionalDeriv T.p (e b)) u (z u)) b
            (hfb (η b) (hη b)).1 b') ?_
          by_cases hbb : b' = b
          · rw [if_pos hbb, if_pos (Finset.mem_singleton.2 hbb), Finset.sum_singleton]
            exact (hfb (η b) (hη b)).2.2
          · rw [if_neg hbb, if_neg (by simpa using hbb)])
      refine hasLocalSize_congr (fun η hη => ?_) size'
      have hs : fderiv ℝ (fun ζ : StepVariable (finiteCells F) =>
          ∑ b ∈ S, radialDirectionalDeriv T.p (e b) (ζ b)) η
          (bondVariation b (z (η b))) =
            if b ∈ S then fderiv ℝ (radialDirectionalDeriv T.p (e b)) (η b) (z (η b)) else 0 :=
        fderiv_bond_sum_bondVariation (hGd η hη) b _
      unfold topFieldPartial bondPartialDeriv
      rw [hOb, (hz (η b) (hη b)).1, hs, if_pos hb]
    · have size' := hsz _ x T.κ (T.Cs * ω * ε) (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V) ∅
        (bondDistToCell Y) (fun _ => 0) hx1 hh (by simp) hd hmom.cutoff_deriv_moments (by simp)
        (differentiableOn_const _) (fun η hη => by simp) (fun η hη b' => by simp [bondGradNorm])
      refine hasLocalSize_congr (fun η hη => ?_) size'
      have hs : ∀ u, fderiv ℝ (fun ζ : StepVariable (finiteCells F) =>
          ∑ b ∈ S, radialDirectionalDeriv T.p (e b) (ζ b)) η
          (bondVariation b u) = if b ∈ S then fderiv ℝ (radialDirectionalDeriv T.p (e b)) (η b) u else 0 :=
        fun u => fderiv_bond_sum_bondVariation (hGd η hη) b _
      unfold topFieldPartial bondPartialDeriv
      rw [hOb, hs, if_neg hb]
end Interpolation
end YangMills.Construction
end
