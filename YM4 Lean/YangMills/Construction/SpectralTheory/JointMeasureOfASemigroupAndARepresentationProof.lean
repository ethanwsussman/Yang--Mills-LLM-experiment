import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystemProof
import YangMills.Construction.HilbertSpace.BasicFacts
import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusTheorem
import YangMills.Construction.SpectralTheory.CoordinateOperatorsOfAProjectionValuedMeasure
import YangMills.Construction.SpectralTheory.JointMeasureOfASemigroupAndARepresentation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped Matrix NNReal InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.SemigroupRepresentation
open YangMills.Construction.BorelSpectral YangMills.Construction.HilbertSpaceBasics YangMills.Construction.SpectralTheorem YangMills.Construction.SelfAdjointFunctions YangMills.Construction.ContractionSemigroups YangMills.Construction.UnitaryGroups YangMills.Construction.BorelCalculus YangMills.Construction.JointSpectral YangMills.Construction.CoordOps
section Calculus
variable {n n' : ℕ} {Y : Set (Fin n → ℝ)} {Y' : Set (Fin n' → ℝ)} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasure Y H}
theorem integralOp_congr_of_isCarriedBy (hu : UnboundedFunctionalCalculus E) {g h : Y → ℂ}
    (hg : Measurable g) (hgb : IsBoundedFn g) (hh : Measurable h) (hhb : IsBoundedFn h)
    (Δ₀ : BorelSubsets Y) (hΔ : E.IsCarriedBy Δ₀) (he : ∀ y ∈ Δ₀.1, g y = h y) :
    E.integralOp g = E.integralOp h := by
  obtain ⟨cg, hcg⟩ := hgb
  obtain ⟨ch, hch⟩ := hhb
  ext ψ
  have hv := (hu.congr g h hg hh Δ₀ hΔ he).2 ψ (by rw [E.integralDom_eq_univ hcg]; trivial)
  rwa [E.integralApply_eq_integralOp hcg, E.integralApply_eq_integralOp hch] at hv
theorem integralOp_pushforward (hi : PushforwardProperties E) (hn' : 1 ≤ n')
    (hY' : MeasurableSet Y') (κ : Y → Y') (hκ : Measurable κ) {g' : Y' → ℂ} (hg : Measurable g')
    {c : ℝ} (hb : ∀ y, ‖g' y‖ ≤ c) :
    (E.pushforward hn' hY' κ hκ).integralOp g' = E.integralOp (g' ∘ κ) := by
  ext ψ
  have hb' : ∀ y, ‖(g' ∘ κ) y‖ ≤ c := fun y => hb _
  have h := (hi.integral_pushforward hn' hY' κ hκ g' hg).2 ψ
    (by rw [E.integralDom_eq_univ hb']; trivial)
  rwa [(E.pushforward hn' hY' κ hκ).integralApply_eq_integralOp hb,
    E.integralApply_eq_integralOp hb'] at h
theorem isSpectralIntegralOf_comp_pushforward (hi : PushforwardProperties E) (hn' : 1 ≤ n')
    (hY' : MeasurableSet Y') (κ : Y → Y') (hκ : Measurable κ) {A : UnboundedOp H} {g' : Y' → ℂ}
    (hg : Measurable g') (h : IsSpectralIntegralOf A (E.pushforward hn' hY' κ hκ) g') :
    IsSpectralIntegralOf A E (g' ∘ κ) := by
  obtain ⟨hd, hv⟩ := hi.integral_pushforward hn' hY' κ hκ g' hg
  refine ⟨fun ψ => ?_, fun ψ => ?_⟩
  · rw [h.1 ψ, hd]
  · rw [h.2 ψ]
    exact hv _ (by rw [← hd]; exact (h.1 _).mp ψ.2)
theorem integralOp_const_one (hc : BoundedFunctionalCalculus E) :
    E.integralOp (fun _ => 1) = 1 := by
  have h := hc.indicator ⟨univ, MeasurableSet.univ⟩
  have h1 : (univ : Set Y).indicator (1 : Y → ℂ) = fun _ => 1 := by
    funext y
    simp
  change E.integralOp ((univ : Set Y).indicator 1) = _ at h
  rw [h1] at h
  exact h.trans E.map_univ
theorem measurable_cexp_I_mul {X : Type*} [MeasurableSpace X] {r : X → ℝ} (hr : Measurable r) :
    Measurable fun x => Complex.exp (Complex.I * ((r x : ℝ) : ℂ)) :=
  Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hr))
theorem norm_cexp_I_mul (r : ℝ) : ‖Complex.exp (Complex.I * ((r : ℝ) : ℂ))‖ = 1 := by apply _root_.YangMills.Construction.ConfigSpace.ModeCost.norm_exp_I_mul_ofReal <;> assumption
theorem isBoundedFn_cexp_I_mul {X : Type*} (r : X → ℝ) :
    IsBoundedFn fun x => Complex.exp (Complex.I * ((r x : ℝ) : ℂ)) :=
  ⟨1, fun x => (norm_cexp_I_mul _).le⟩
theorem cexp_I_mul_mul_eq (s r : ℝ) :
    Complex.exp (Complex.I * s * ((r : ℝ) : ℂ)) = Complex.exp (Complex.I * ((s * r : ℝ) : ℂ)) := by
  congr 1
  push_cast
  ring
end Calculus
section Operators
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev axisUnitaryGroup (U : (Fin n → ℝ) → H →L[ℂ] H) (i : Fin n) : ℝ → H →L[ℂ] H :=
  fun s => U (s • Pi.single i 1)
theorem isContinuousUnitaryGroup_axis {U : (Fin n → ℝ) → H →L[ℂ] H} (hU : IsUnitaryRep U)
    (h0 : TendstoStrongly U (𝓝 0) 1) (i : Fin n) :
    IsContinuousUnitaryGroup (axisUnitaryGroup U i) := by
  refine ⟨⟨fun s => hU.1 _, by simp [axisUnitaryGroup, hU.2.1], fun s s' => ?_⟩, fun ψ => ?_⟩
  · simp only [axisUnitaryGroup]
    rw [hU.2.2, add_smul]
  · have hc : Tendsto (fun s : ℝ => s • (Pi.single i 1 : Fin n → ℝ)) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun s : ℝ => s • (Pi.single i 1 : Fin n → ℝ)) := by fun_prop
      simpa using hcont.tendsto 0
    exact (h0 ψ).comp hc
theorem inner_star_apply_eq (A : H →L[ℂ] H) (φ ψ : H) : ⟪φ, star A ψ⟫_ℂ = ⟪A φ, ψ⟫_ℂ := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
theorem le_of_isGE {A B : H →L[ℂ] H} (h : HilbertSpaceBasics.IsGE A B) : B ≤ A := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff']
  refine ⟨h.2.2.1, fun x => ?_⟩
  have h0 := h.2.2.2 x
  have hs : star (A - B) = A - B := h.2.2.1
  rw [← inner_star_apply_eq, hs]
  exact h0
theorem isSelfAdjoint_realPartOp (C : H →L[ℂ] H) : IsSelfAdjoint (realPartOp C) := by
  change star (realPartOp C) = realPartOp C
  simp only [realPartOp, star_smul, star_add, star_star]
  rw [add_comm]
  simp
theorem isSelfAdjoint_imagPartOp (C : H →L[ℂ] H) : IsSelfAdjoint (imagPartOp C) := by
  change star (imagPartOp C) = imagPartOp C
  have hz : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp only [Complex.star_def, map_div₀, map_mul, map_one, Complex.conj_I, map_ofNat]
    field_simp
  simp only [imagPartOp, star_smul, star_sub, star_star, hz]
  rw [neg_smul, ← smul_neg, neg_sub]
theorem norm_realPartOp_le_one {C : H →L[ℂ] H} (h : ‖C‖ ≤ 1) : ‖realPartOp C‖ ≤ 1 := by
  have h1 : ‖C + star C‖ ≤ 2 := (norm_add_le _ _).trans (by rw [norm_star]; linarith)
  rw [realPartOp, norm_smul]
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]
  linarith
theorem norm_imagPartOp_le_one {C : H →L[ℂ] H} (h : ‖C‖ ≤ 1) : ‖imagPartOp C‖ ≤ 1 := by
  have h1 : ‖C - star C‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_star]; linarith)
  rw [imagPartOp, norm_smul]
  have : ‖(1 / (2 * Complex.I) : ℂ)‖ = 1 / 2 := by simp
  rw [this]
  linarith
theorem realPartOp_add_I_smul_imagPartOp (C : H →L[ℂ] H) :
    realPartOp C + Complex.I • imagPartOp C = C := by
  have hz : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  simp only [realPartOp, imagPartOp, smul_smul, hz]
  module
theorem norm_le_one_of_inner_bound {C : H →L[ℂ] H} (h : ∀ φ ψ, ‖⟪φ, C ψ⟫_ℂ‖ ≤ ‖φ‖ * ‖ψ‖) :
    ‖C‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ψ => by
    rw [one_mul]
    have h1 := h (C ψ) ψ
    have h2 : ‖⟪C ψ, C ψ⟫_ℂ‖ = ‖C ψ‖ * ‖C ψ‖ := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [sq]
    rw [h2] at h1
    rcases (norm_nonneg (C ψ)).eq_or_lt with h0 | h0
    · rw [← h0]
      exact norm_nonneg _
    · exact le_of_mul_le_mul_left h1 h0
def resolventParts (U : (Fin n → ℝ) → H →L[ℂ] H) : Fin (n + n) → H →L[ℂ] H :=
  Fin.append (fun i => realPartOp (resolventOp (axisUnitaryGroup U i)))
    fun i => imagPartOp (resolventOp (axisUnitaryGroup U i))
def generatorFamily (T : ℝ≥0 → H →L[ℂ] H) (U : (Fin n → ℝ) → H →L[ℂ] H) :
    Fin (n + n + 1) → H →L[ℂ] H :=
  Fin.cons (T 1) (resolventParts U)
def boxLower : Fin (n + n + 1) → ℝ := Fin.cons 0 fun _ => -1
def boxUpper : Fin (n + n + 1) → ℝ := fun _ => 1
theorem commute_resolventParts (h₄ : UnitaryGroups.StoneTheoremHolds)
    {U : (Fin n → ℝ) → H →L[ℂ] H} (hG : ∀ i, IsContinuousUnitaryGroup (axisUnitaryGroup U i))
    {B : H →L[ℂ] H} (hB : ∀ a, Commute B (U a)) (j : Fin (n + n)) :
    Commute B (resolventParts U j) := by
  have hC : ∀ i, Commute B (resolventOp (axisUnitaryGroup U i)) ∧
      Commute B (star (resolventOp (axisUnitaryGroup U i))) := fun i => by
    obtain ⟨-, -, -, -, -, -, -, -, hcomm, -⟩ := (h₄ H).1 _ (hG i)
    exact hcomm B fun s => hB _
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [resolventParts, Fin.append_left]
    exact ((hC i).1.add_right (hC i).2).smul_right _
  · rw [resolventParts, Fin.append_right]
    exact ((hC i).1.sub_right (hC i).2).smul_right _
theorem commute_unitaryRep {U : (Fin n → ℝ) → H →L[ℂ] H} (hU : IsUnitaryRep U)
    (a b : Fin n → ℝ) : Commute (U a) (U b) := by
  change U a * U b = U b * U a
  rw [hU.2.2, hU.2.2, add_comm]
theorem commute_generatorFamily (h₄ : UnitaryGroups.StoneTheoremHolds)
    {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H} (h : IsCommutingSemigroupRep T U)
    (i j : Fin (n + n + 1)) : Commute (generatorFamily T U i) (generatorFamily T U j) := by
  have hG := isContinuousUnitaryGroup_axis h.isUnitaryRep h.tendstoStrongly_zero
  have hT : ∀ a, Commute (T 1) (U a) := fun a => (h.commute a 1).symm
  have hP : ∀ (j : Fin (n + n)) a, Commute (resolventParts U j) (U a) := fun j a =>
    (commute_resolventParts h₄ hG (commute_unitaryRep h.isUnitaryRep a) j).symm
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact Commute.refl _
    | succ j => exact commute_resolventParts h₄ hG hT j
  | succ i =>
    induction j using Fin.cases with
    | zero => exact (commute_resolventParts h₄ hG hT i).symm
    | succ j => exact commute_resolventParts h₄ hG (hP i) j
theorem resolventParts_selfAdjoint_norm_le (h₄ : UnitaryGroups.StoneTheoremHolds)
    {U : (Fin n → ℝ) → H →L[ℂ] H} (hG : ∀ i, IsContinuousUnitaryGroup (axisUnitaryGroup U i))
    (j : Fin (n + n)) :
    IsSelfAdjoint (resolventParts U j) ∧ ‖resolventParts U j‖ ≤ 1 := by
  have hC : ∀ i, ‖resolventOp (axisUnitaryGroup U i)‖ ≤ 1 := fun i => by
    obtain ⟨-, -, -, -, hbound, -, hL, -⟩ := (h₄ H).1 _ (hG i)
    refine norm_le_one_of_inner_bound fun φ ψ => ?_
    rw [hL φ ψ]
    exact hbound φ ψ
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [resolventParts, Fin.append_left]
    exact ⟨isSelfAdjoint_realPartOp _, norm_realPartOp_le_one (hC i)⟩
  · rw [resolventParts, Fin.append_right]
    exact ⟨isSelfAdjoint_imagPartOp _, norm_imagPartOp_le_one (hC i)⟩
theorem isCommutingInBox_generatorFamily (h₀ : HilbertSpaceFacts.Facts)
    (h₃ : ContractionSemigroups.ContractionSemigroupTheorem)
    (h₄ : UnitaryGroups.StoneTheoremHolds)
    {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H} (h : IsCommutingSemigroupRep T U) :
    IsCommutingInBox (generatorFamily T U) boxLower boxUpper := by
  have hG := isContinuousUnitaryGroup_axis h.isUnitaryRep h.tendstoStrongly_zero
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hB, -, -, -, -, -⟩ := h₀
  obtain ⟨⟨-, hpos, -⟩, -⟩ := h₃ H T h.isContractionSemigroup
  have hsa₁ : IsSelfAdjoint (T 1) := h.isContractionSemigroup.selfAdjoint 1
  refine ⟨fun i => ?_, commute_generatorFamily h₄ h, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · induction i using Fin.cases with
    | zero => exact hsa₁
    | succ j => exact (resolventParts_selfAdjoint_norm_le h₄ hG j).1
  · induction i using Fin.cases with
    | zero => simp [boxLower, boxUpper]
    | succ j => simp [boxLower, boxUpper]
  · induction i using Fin.cases with
    | zero =>
      refine le_of_isGE ⟨hsa₁, ?_, ?_⟩
      · simp [boxLower]
      · simpa [boxLower, generatorFamily] using (hpos 1).1
    | succ j =>
      have := (hB H _ 1 (resolventParts_selfAdjoint_norm_le h₄ hG j).1
        (resolventParts_selfAdjoint_norm_le h₄ hG j).2).1
      exact le_of_isGE (by simpa [boxLower, generatorFamily] using this)
  · induction i using Fin.cases with
    | zero => exact le_of_isGE (by simpa [boxUpper, generatorFamily] using (hpos 1).2)
    | succ j =>
      have := (hB H _ 1 (resolventParts_selfAdjoint_norm_le h₄ hG j).1
        (resolventParts_selfAdjoint_norm_le h₄ hG j).2).2
      exact le_of_isGE (by simpa [boxUpper, generatorFamily] using this)
end Operators
section Existence
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev generatorBox (n : ℕ) : Set (Fin (n + n + 1) → ℝ) := closedBox boxLower boxUpper
def resolventCoord (i : Fin n) (y : Fin (n + n + 1) → ℝ) : ℂ :=
  ((y (Fin.castAdd n i).succ : ℝ) : ℂ) + Complex.I * ((y (Fin.natAdd n i).succ : ℝ) : ℂ)
theorem measurable_resolventCoord (i : Fin n) : Measurable (resolventCoord (n := n) i) :=
  (Complex.measurable_ofReal.comp (measurable_pi_apply _)).add
    (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_pi_apply _)))
def axisFrequency (i : Fin n) (y : Fin (n + n + 1) → ℝ) : ℝ :=
  (resolventCoord i y).im / (resolventCoord i y).re
theorem measurable_axisFrequency (i : Fin n) : Measurable (axisFrequency (n := n) i) :=
  (Complex.measurable_im.comp (measurable_resolventCoord i)).div
    (Complex.measurable_re.comp (measurable_resolventCoord i))
def energyFrequencyPoint (y : Fin (n + n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (-Real.log (y 0)) fun i => axisFrequency i y
theorem measurable_energyFrequencyPoint : Measurable (energyFrequencyPoint (n := n)) := by
  refine measurable_pi_iff.mpr fun l => ?_
  induction l using Fin.cases with
  | zero => exact (Real.measurable_log.comp (measurable_pi_apply 0)).neg
  | succ i => exact measurable_axisFrequency i
theorem apply_zero_mem_Icc (y : generatorBox n) : y.1 0 ∈ Icc (0 : ℝ) 1 :=
  y.2 0 (mem_univ 0)
theorem abs_apply_le_one (y : generatorBox n) (j : Fin (n + n + 1)) : |y.1 j| ≤ 1 := by
  have hy := y.2 j (mem_univ j)
  have hf : -1 ≤ boxLower (n := n) j := by
    induction j using Fin.cases with
    | zero => simp [boxLower]
    | succ j => simp [boxLower]
  exact abs_le.mpr ⟨hf.trans hy.1, hy.2⟩
def boxToHalfSpace (y : generatorBox n) : nonnegHalfSpace n :=
  ⟨energyFrequencyPoint y.1, by
    change 0 ≤ -Real.log (y.1 0)
    have hy := apply_zero_mem_Icc y
    exact neg_nonneg.mpr (Real.log_nonpos hy.1 hy.2)⟩
theorem measurable_boxToHalfSpace : Measurable (boxToHalfSpace (n := n)) :=
  (measurable_energyFrequencyPoint.comp measurable_subtype_coe).subtype_mk
theorem measurable_coordFn_box (j : Fin (n + n + 1)) :
    Measurable (coordFn (Y := generatorBox n) j) :=
  Complex.measurable_ofReal.comp ((measurable_pi_apply j).comp measurable_subtype_coe)
theorem isBoundedFn_coordFn_box (j : Fin (n + n + 1)) :
    IsBoundedFn (coordFn (Y := generatorBox n) j) :=
  ⟨1, fun y => by
    rw [coordFn, Complex.norm_real, Real.norm_eq_abs]
    exact abs_apply_le_one y j⟩
theorem resolventOp_axis_eq {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H}
    {F : SpectralMeasure (generatorBox n) H} (hc : BoundedFunctionalCalculus F)
    (hRep : IsJointRepresentation F (generatorFamily T U)) (i : Fin n) :
    resolventOp (axisUnitaryGroup U i) = F.integralOp fun y => resolventCoord i y.1 := by
  have h1 := hRep (Fin.castAdd n i).succ
  have h2 := hRep (Fin.natAdd n i).succ
  simp only [generatorFamily, Fin.cons_succ, resolventParts, Fin.append_left,
    Fin.append_right] at h1 h2
  have e : (fun y : generatorBox n => resolventCoord i y.1) =
      coordFn (Fin.castAdd n i).succ + Complex.I • coordFn (Fin.natAdd n i).succ := by
    funext y
    simp [resolventCoord, coordFn]
  rw [e, hc.add _ _ (measurable_coordFn_box _) (isBoundedFn_coordFn_box _)
    ((measurable_coordFn_box _).const_smul _)
    (by
      obtain ⟨c, hc'⟩ := isBoundedFn_coordFn_box (n := n) (Fin.natAdd n i).succ
      exact ⟨‖Complex.I‖ * c, fun y => by
        rw [Pi.smul_apply, norm_smul]
        exact mul_le_mul_of_nonneg_left (hc' y) (norm_nonneg _)⟩),
    hc.smul _ _ (measurable_coordFn_box _) (isBoundedFn_coordFn_box _), ← h1, ← h2]
  exact (realPartOp_add_I_smul_imagPartOp _).symm
theorem axisUnitaryGroup_eq (h₄ : UnitaryGroups.StoneTheoremHolds)
    {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H} (h : IsCommutingSemigroupRep T U)
    {F : SpectralMeasure (generatorBox n) H} (hc : BoundedFunctionalCalculus F)
    (hu : UnboundedFunctionalCalculus F)
    (hRep : IsJointRepresentation F (generatorFamily T U)) (i : Fin n) (s : ℝ) :
    U (s • Pi.single i 1) = F.integralOp fun y =>
      Complex.exp (Complex.I * ((s * axisFrequency i y.1 : ℝ) : ℂ)) := by
  have hG := isContinuousUnitaryGroup_axis h.isUnitaryRep h.tendstoStrongly_zero i
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hb, -⟩ := (h₄ H).1 _ hG
  have hζ : Measurable fun y : generatorBox n => resolventCoord i y.1 :=
    (measurable_resolventCoord i).comp measurable_subtype_coe
  have hbd : ∃ c : ℝ, ∀ y : generatorBox n, ‖resolventCoord i y.1‖ ≤ c := ⟨2, fun y => by
    have h1 := abs_apply_le_one y (Fin.castAdd n i).succ
    have h2 := abs_apply_le_one y (Fin.natAdd n i).succ
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    linarith⟩
  obtain ⟨hcar, hs⟩ := hb _ _ F _ hζ hbd (resolventOp_axis_eq hc hRep i)
  refine (hs s).trans ?_
  have hq : Measurable fun y : generatorBox n => s * axisFrequency i y.1 :=
    ((measurable_axisFrequency i).comp measurable_subtype_coe).const_mul s
  refine integralOp_congr_of_isCarriedBy hu
    (measurable_zeroExtend (circleSupport _ hζ).2 ?_) ⟨1, fun y => ?_⟩ (measurable_cexp_I_mul hq)
    (isBoundedFn_cexp_I_mul _) _ hcar fun y hy => ?_
  · have : Measurable fun y : (circleSupport _ hζ).1 =>
        Complex.exp (Complex.I * ((s * axisFrequency i y.1.1 : ℝ) : ℂ)) :=
      measurable_cexp_I_mul (hq.comp measurable_subtype_coe)
    convert this using 2 with y
    exact cexp_I_mul_mul_eq _ _
  · unfold zeroExtend
    split_ifs with hy
    · beta_reduce
      rw [cexp_I_mul_mul_eq]
      exact (norm_cexp_I_mul _).le
    · simp
  · simp only [zeroExtend, dif_pos hy]
    exact cexp_I_mul_mul_eq _ _
theorem unitaryRep_sum_eq (h₄ : UnitaryGroups.StoneTheoremHolds)
    {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H} (h : IsCommutingSemigroupRep T U)
    {F : SpectralMeasure (generatorBox n) H} (hc : BoundedFunctionalCalculus F)
    (hu : UnboundedFunctionalCalculus F)
    (hRep : IsJointRepresentation F (generatorFamily T U)) (a : Fin n → ℝ)
    (S : Finset (Fin n)) :
    U (∑ i ∈ S, a i • Pi.single i 1) = F.integralOp fun y =>
      Complex.exp (Complex.I * ((∑ i ∈ S, a i * axisFrequency i y.1 : ℝ) : ℂ)) := by
  classical
  have hm : ∀ (S : Finset (Fin n)), Measurable fun y : generatorBox n =>
      ∑ i ∈ S, a i * axisFrequency i y.1 := fun S =>
    Finset.measurable_fun_sum S fun i _ =>
      ((measurable_axisFrequency i).comp measurable_subtype_coe).const_mul (a i)
  have hmi : ∀ i, Measurable fun y : generatorBox n => a i * axisFrequency i y.1 := fun i =>
    ((measurable_axisFrequency i).comp measurable_subtype_coe).const_mul (a i)
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [integralOp_const_one hc]
    exact h.isUnitaryRep.2.1
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, ← h.isUnitaryRep.2.2, axisUnitaryGroup_eq h₄ h hc hu hRep j (a j),
      ih, ← hc.mul _ _ (measurable_cexp_I_mul (hmi j)) (isBoundedFn_cexp_I_mul _)
        (measurable_cexp_I_mul (hm S)) (isBoundedFn_cexp_I_mul _)]
    congr 1
    funext y
    rw [Finset.sum_insert hj, Pi.mul_apply, ← Complex.exp_add]
    congr 1
    push_cast
    ring
theorem sum_smul_single_eq (a : Fin n → ℝ) : ∑ i, a i • (Pi.single i 1 : Fin n → ℝ) = a := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]
theorem norm_cexp_damped_le_one (t : ℝ≥0) (l r : ℝ) (hl : 0 ≤ l) :
    ‖Complex.exp (((-(t : ℝ) * l : ℝ) : ℂ) + Complex.I * ((r : ℝ) : ℂ))‖ ≤ 1 := by
  rw [Complex.exp_add, norm_mul, norm_cexp_I_mul, mul_one, Complex.norm_exp]
  simp only [Complex.ofReal_re, Real.exp_le_one_iff]
  have : 0 ≤ (t : ℝ) * l := mul_nonneg t.2 hl
  linarith
theorem measurable_dotProduct_const (a : Fin n → ℝ) :
    Measurable fun v : Fin n → ℝ => a ⬝ᵥ v := by
  simp only [dotProduct]
  exact Finset.measurable_fun_sum _ fun i _ => (measurable_pi_apply i).const_mul _
def energyMomentumCharacter (t : ℝ≥0) (a : Fin n → ℝ) (y : nonnegHalfSpace n) : ℂ :=
  Complex.exp (((-(t : ℝ) * y.1 0 : ℝ) : ℂ) + Complex.I * ((a ⬝ᵥ spatialCoords y.1 : ℝ) : ℂ))
theorem measurable_energyMomentumCharacter (t : ℝ≥0) (a : Fin n → ℝ) :
    Measurable (energyMomentumCharacter t a) := by
  have h0 : Measurable fun y : nonnegHalfSpace n => y.1 0 :=
    (measurable_pi_apply 0).comp measurable_subtype_coe
  have h1 : Measurable fun y : nonnegHalfSpace n => a ⬝ᵥ spatialCoords y.1 :=
    (measurable_dotProduct_const a).comp (measurable_spatialCoords.comp measurable_subtype_coe)
  exact Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp (h0.const_mul _)).add
      (measurable_const.mul (Complex.measurable_ofReal.comp h1)))
theorem norm_energyMomentumCharacter_le (t : ℝ≥0) (a : Fin n → ℝ) (y : nonnegHalfSpace n) :
    ‖energyMomentumCharacter t a y‖ ≤ 1 :=
  norm_cexp_damped_le_one t _ _ y.2
theorem exists_isJointSpectralMeasure (h₀ : HilbertSpaceFacts.Facts)
    (h₂ : BorelCalculus.BorelCalculusTheorem)
    (h₃ : ContractionSemigroups.ContractionSemigroupTheorem)
    (h₄ : UnitaryGroups.StoneTheoremHolds)
    (h₆ : JointSpectral.JointSpectralTheorem)
    {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H} (h : IsCommutingSemigroupRep T U) :
    ∃ E : SpectralMeasure (nonnegHalfSpace n) H, IsJointSpectralMeasure E T U ∧
      ∀ B : H →L[ℂ] H, Commute B (T 1) → (∀ a, Commute B (U a)) → ∀ Δ, Commute B (E Δ) := by
  have hG := isContinuousUnitaryGroup_axis h.isUnitaryRep h.tendstoStrongly_zero
  have hbox := isCommutingInBox_generatorFamily h₀ h₃ h₄ h
  have hm1 : 1 ≤ n + n + 1 := by omega
  obtain ⟨-, hRep, -, hFc⟩ := (h₆ H (n + n + 1) hm1).1 _ _ _ hbox
  set F := JointSpectral.jointMeasure hm1 (generatorFamily T U) boxLower boxUpper hbox.lt with hF
  obtain ⟨hc, -, -, hu, -, hi, -⟩ := (h₂ H (n + n + 1)).1 _ F
  obtain ⟨-, ⟨hsb, -⟩, -⟩ := h₃ H T h.isContractionSemigroup
  have hx : Measurable fun y : generatorBox n => y.1 0 :=
    (measurable_pi_apply 0).comp measurable_subtype_coe
  obtain ⟨hzero, hTt⟩ := hsb _ _ F _ hx apply_zero_mem_Icc (hRep 0)
  let Δ₀ : BorelSubsets (generatorBox n) :=
    ⟨((fun y : generatorBox n => y.1 0) ⁻¹' {0})ᶜ, (hx (measurableSet_singleton 0)).compl⟩
  have hcar : F.IsCarriedBy Δ₀ := by
    have hs : (⟨Δ₀.1ᶜ, Δ₀.2.compl⟩ : BorelSubsets (generatorBox n)) =
        ⟨(fun y : generatorBox n => y.1 0) ⁻¹' {0}, hx (measurableSet_singleton 0)⟩ :=
      Subtype.ext (compl_compl _)
    exact (congrArg F.toFun hs).trans hzero
  refine ⟨F.pushforward (Nat.succ_le_succ (Nat.zero_le n)) (measurableSet_nonnegHalfSpace n)
    boxToHalfSpace measurable_boxToHalfSpace, fun t a => ?_, fun B hB1 hBU Δ => ?_⟩
  · have hUa := unitaryRep_sum_eq h₄ h hc hu hRep a Finset.univ
    rw [sum_smul_single_eq] at hUa
    have hq : Measurable fun y : generatorBox n => ∑ i, a i * axisFrequency i y.1 :=
      Finset.measurable_fun_sum _ fun i _ =>
        ((measurable_axisFrequency i).comp measurable_subtype_coe).const_mul (a i)
    have hxt : Measurable fun y : generatorBox n => ((y.1 0 ^ (t : ℝ) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (hx.pow_const _)
    have hxb : IsBoundedFn fun y : generatorBox n => ((y.1 0 ^ (t : ℝ) : ℝ) : ℂ) :=
      ⟨1, fun y => by
        have hy := apply_zero_mem_Icc y
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hy.1 _)]
        exact Real.rpow_le_one hy.1 hy.2 t.2⟩
    change T t * U a = _
    refine Eq.trans ?_ (integralOp_pushforward hi _ _ _ _ (measurable_energyMomentumCharacter t a)
      (norm_energyMomentumCharacter_le t a)).symm
    rw [hTt t, hUa, ← hc.mul _ _ hxt hxb (measurable_cexp_I_mul hq) (isBoundedFn_cexp_I_mul _)]
    refine integralOp_congr_of_isCarriedBy hu (hxt.mul (measurable_cexp_I_mul hq)) ?_
      ((measurable_energyMomentumCharacter t a).comp measurable_boxToHalfSpace)
      ⟨1, fun y => norm_energyMomentumCharacter_le t a _⟩ Δ₀ hcar fun y hy => ?_
    · obtain ⟨c, hc'⟩ := hxb
      refine ⟨c, fun y => ?_⟩
      rw [Pi.mul_apply, norm_mul, norm_cexp_I_mul, mul_one]
      exact hc' y
    · have hpos : 0 < y.1 0 := lt_of_le_of_ne (apply_zero_mem_Icc y).1 (Ne.symm hy)
      have e1 : (boxToHalfSpace y).1 0 = -Real.log (y.1 0) := rfl
      have e2 : a ⬝ᵥ spatialCoords (boxToHalfSpace y).1 = ∑ i, a i * axisFrequency i y.1 := rfl
      simp only [Pi.mul_apply, Function.comp_apply, energyMomentumCharacter, e1, e2]
      rw [Real.rpow_def_of_pos hpos, Complex.ofReal_exp, ← Complex.exp_add]
      congr 2
      ring
  · have hall : ∀ j, Commute B (generatorFamily T U j) := fun j => by
      induction j using Fin.cases with
      | zero => exact hB1
      | succ j => exact commute_resolventParts h₄ hG hBU j
    exact hFc F hRep B hall _
end Existence
section Main
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem measurable_fullSpace_apply {m : ℕ} (l : Fin m) : Measurable fun y : FullSpace m => y.1 l :=
  (measurable_pi_apply l).comp measurable_subtype_coe
theorem integralOp_extendToWhole (h₂ : BorelCalculus.BorelCalculusTheorem)
    (E : SpectralMeasure (nonnegHalfSpace n) H) {g : FullSpace (n + 1) → ℂ} (hg : Measurable g)
    {c : ℝ} (hb : ∀ y, ‖g y‖ ≤ c) :
    (extendToWhole E).integralOp g = E.integralOp fun y => g ⟨y.1, mem_univ _⟩ := by
  obtain ⟨-, -, -, -, -, hi, -⟩ := (h₂ H (n + 1)).1 _ E
  exact integralOp_pushforward hi E.one_le_dimension MeasurableSet.univ (inclusion (subset_univ _))
    measurable_subtype_coe.subtype_mk hg hb
theorem integralOp_coordMarginal {m : ℕ} (h₂ : BorelCalculus.BorelCalculusTheorem)
    (W : SpectralMeasure (FullSpace m) H) (i : Fin m) {f : ℝ → ℂ} (hf : Measurable f)
    {c : ℝ} (hb : ∀ x, ‖f x‖ ≤ c) :
    (W.coordMarginal i).integralOp (fun y => f (y.1 0)) = W.integralOp fun y => f (y.1 i) := by
  obtain ⟨-, -, -, -, -, hi, -⟩ := (h₂ H m).1 _ W
  exact integralOp_pushforward hi le_rfl MeasurableSet.univ _ (measurable_coordLine i)
    (hf.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)) fun y => hb _
theorem expI_coordOperator {m : ℕ} (h₂ : BorelCalculus.BorelCalculusTheorem)
    (h₅ : CoordOps.CoordOpsTheorem)
    (W : SpectralMeasure (FullSpace m) H) (i : Fin m) (s : ℝ) :
    expI (coordOperator W i) s =
      W.integralOp fun y => Complex.exp (Complex.I * ((s * y.1 i : ℝ) : ℂ)) := by
  obtain ⟨ha, -⟩ := h₅ H m W
  have hf : Measurable fun x : ℝ => Complex.exp (Complex.I * ((s * x : ℝ) : ℂ)) :=
    measurable_cexp_I_mul (measurable_id.const_mul s)
  have h := integralOp_coordMarginal h₂ W i hf (c := 1) fun x => (norm_cexp_I_mul _).le
  rw [← h, ← (ha i).2.1]
  unfold expI
  congr 1
  funext y
  exact cexp_I_mul_mul_eq _ _
theorem semigroupRep_apply_zero {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H}
    (hT : IsCommutingSemigroupRep T U) : T 0 = 1 ∧ U 0 = 1 :=
  ⟨hT.isContractionSemigroup.semigroup.1, hT.isUnitaryRep.2.1⟩
theorem coordOperator_zero_eq (h₂ : BorelCalculus.BorelCalculusTheorem)
    (h₃ : ContractionSemigroups.ContractionSemigroupTheorem)
    (h₅ : CoordOps.CoordOpsTheorem)
    (h₇ : SpectralTheorem.SpectralTheoremHolds)
    {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H} (hT : IsCommutingSemigroupRep T U)
    {E : SpectralMeasure (nonnegHalfSpace n) H} (hE : IsJointSpectralMeasure E T U) :
    coordOperator (extendToWhole E) 0 = semigroupGenerator T := by
  obtain ⟨ha, -⟩ := h₅ H (n + 1) (extendToWhole E)
  obtain ⟨hsa, hsp, -⟩ := ha 0
  obtain ⟨-, -, -, -, -, -, -, hnn, -⟩ := h₇ H _ hsa
  obtain ⟨-, -, ⟨-, -, -, huniq, -⟩, -⟩ := h₃ H T hT.isContractionSemigroup
  refine huniq _ (hnn.mpr ?_) ?_
  · rw [hsp]
    have hu : (⟨inclusion (subset_univ (nonnegHalfSpace n)) ⁻¹' {y | y.1 0 ∈ negHalfLine.1},
        measurable_subtype_coe.subtype_mk
          (((measurable_pi_apply 0).comp measurable_subtype_coe) negHalfLine.2)⟩ :
          BorelSubsets (nonnegHalfSpace n)) = ⟨∅, MeasurableSet.empty⟩ := by
      refine Subtype.ext (eq_empty_of_forall_notMem fun y hy => ?_)
      have h0 : y.1 0 < 0 := hy
      exact absurd y.2 (not_le.mpr h0)
    exact (congrArg E.toFun hu).trans E.apply_empty
  · have hf : Measurable fun x : ℝ => (Ici (0 : ℝ)).indicator
        (fun x => Complex.exp ((-((1 : ℝ≥0) : ℝ) * x : ℝ) : ℂ)) x :=
      (Complex.measurable_exp.comp
        (Complex.measurable_ofReal.comp (measurable_id.const_mul _))).indicator measurableSet_Ici
    have hb : ∀ x : ℝ, ‖(Ici (0 : ℝ)).indicator
        (fun x => Complex.exp ((-((1 : ℝ≥0) : ℝ) * x : ℝ) : ℂ)) x‖ ≤ 1 := fun x => by
      by_cases hx : x ∈ Ici (0 : ℝ)
      · rw [indicator_of_mem hx, Complex.norm_exp]
        simpa using hx
      · rw [indicator_of_notMem hx]
        simp
    have hgm : Measurable fun y : FullSpace (n + 1) => (Ici (0 : ℝ)).indicator
        (fun x => Complex.exp ((-((1 : ℝ≥0) : ℝ) * x : ℝ) : ℂ)) (y.1 0) :=
      hf.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)
    unfold expNeg
    rw [hsp, integralOp_coordMarginal h₂ _ 0 hf hb,
      integralOp_extendToWhole h₂ E hgm fun y => hb _]
    have h1 := hE 1 0
    rw [(semigroupRep_apply_zero hT).2, mul_one] at h1
    rw [h1]
    congr 1
    funext y
    have hy : y.1 0 ∈ Ici (0 : ℝ) := y.2
    rw [indicator_of_mem hy]
    simp
theorem smul_single_dotProduct (s : ℝ) (i : Fin n) (v : Fin n → ℝ) :
    (s • (Pi.single i 1 : Fin n → ℝ)) ⬝ᵥ v = s * v i := by
  simp [smul_dotProduct]
theorem coordOperator_succ_eq (h₂ : BorelCalculus.BorelCalculusTheorem)
    (h₄ : UnitaryGroups.StoneTheoremHolds)
    (h₅ : CoordOps.CoordOpsTheorem)
    {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H} (hT : IsCommutingSemigroupRep T U)
    {E : SpectralMeasure (nonnegHalfSpace n) H} (hE : IsJointSpectralMeasure E T U) (i : Fin n) :
    coordOperator (extendToWhole E) i.succ = momentumOp U i := by
  obtain ⟨ha, -⟩ := h₅ H (n + 1) (extendToWhole E)
  have hG := isContinuousUnitaryGroup_axis hT.isUnitaryRep hT.tendstoStrongly_zero i
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hex, hgen, -⟩ := (h₄ H).1 _ hG
  refine hex.unique ⟨(ha i.succ).1, fun s => ?_⟩ hgen
  have hgm : Measurable fun y : FullSpace (n + 1) =>
      Complex.exp (Complex.I * ((s * y.1 i.succ : ℝ) : ℂ)) :=
    measurable_cexp_I_mul ((measurable_fullSpace_apply i.succ).const_mul s)
  rw [expI_coordOperator h₂ h₅,
    integralOp_extendToWhole h₂ E hgm (c := 1) fun y => (norm_cexp_I_mul _).le]
  have h1 := hE 0 (s • Pi.single i 1)
  rw [(semigroupRep_apply_zero hT).1, one_mul] at h1
  refine h1.trans ?_
  congr 1
  funext y
  rw [smul_single_dotProduct]
  simp [spatialCoords]
theorem coordOperator_eq (h₂ : BorelCalculus.BorelCalculusTheorem)
    (h₃ : ContractionSemigroups.ContractionSemigroupTheorem)
    (h₄ : UnitaryGroups.StoneTheoremHolds)
    (h₅ : CoordOps.CoordOpsTheorem)
    (h₇ : SpectralTheorem.SpectralTheoremHolds)
    {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H} (hT : IsCommutingSemigroupRep T U)
    {E : SpectralMeasure (nonnegHalfSpace n) H} (hE : IsJointSpectralMeasure E T U)
    (l : Fin (n + 1)) :
    coordOperator (extendToWhole E) l = energyMomentumOps T U l := by
  induction l using Fin.cases with
  | zero => exact coordOperator_zero_eq h₂ h₃ h₅ h₇ hT hE
  | succ i => exact coordOperator_succ_eq h₂ h₄ h₅ hT hE i
theorem extendToWhole_injective {E₁ E₂ : SpectralMeasure (nonnegHalfSpace n) H}
    (h : extendToWhole E₁ = extendToWhole E₂) : E₁ = E₂ := by
  refine SpectralMeasure.ext_apply fun Δ => ?_
  have hm : MeasurableSet (Subtype.val '' Δ.1 : Set (Fin (n + 1) → ℝ)) :=
    (measurableSet_nonnegHalfSpace n).subtype_image Δ.2
  let Δ' : BorelSubsets (FullSpace (n + 1)) :=
    ⟨Subtype.val ⁻¹' (Subtype.val '' Δ.1), measurable_subtype_coe hm⟩
  have e : ∀ E : SpectralMeasure (nonnegHalfSpace n) H, extendToWhole E Δ' = E Δ := fun E =>
    congrArg E.toFun (Subtype.ext (by
      ext y
      constructor
      · rintro ⟨z, hz, he⟩
        have : z = y := Subtype.ext he
        exact this ▸ hz
      · intro hy
        exact ⟨y, hy, rfl⟩))
  rw [← e E₁, ← e E₂, h]
theorem isJointSpectralMeasure_unique (h₂ : BorelCalculus.BorelCalculusTheorem)
    (h₃ : ContractionSemigroups.ContractionSemigroupTheorem)
    (h₄ : UnitaryGroups.StoneTheoremHolds)
    (h₅ : CoordOps.CoordOpsTheorem)
    (h₇ : SpectralTheorem.SpectralTheoremHolds)
    {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H} (hT : IsCommutingSemigroupRep T U)
    {E₁ E₂ : SpectralMeasure (nonnegHalfSpace n) H} (h₁ : IsJointSpectralMeasure E₁ T U)
    (h₂' : IsJointSpectralMeasure E₂ T U) : E₁ = E₂ := by
  obtain ⟨-, -, -, hun, -⟩ := h₅ H (n + 1) (extendToWhole E₁)
  obtain ⟨-, -, hco, -⟩ := h₅ H (n + 1) (extendToWhole E₂)
  refine extendToWhole_injective (hun _ fun l => ?_).symm
  rw [coordOperator_eq h₂ h₃ h₄ h₅ h₇ hT h₁ l, ← coordOperator_eq h₂ h₃ h₄ h₅ h₇ hT h₂' l]
  exact hco l
theorem prod_ofFn_unitaryRep {U : (Fin n → ℝ) → H →L[ℂ] H} (hU : IsUnitaryRep U) {m : ℕ}
    (f : Fin m → Fin n → ℝ) : (List.ofFn fun k => U (f k)).prod = U (∑ k, f k) := by
  induction m with
  | zero => simp [hU.2.1]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ih, hU.2.2, Fin.sum_univ_succ]
theorem unitaryRep_eq_jointExpI (h₄ : UnitaryGroups.StoneTheoremHolds)
    {U : (Fin n → ℝ) → H →L[ℂ] H} (hU : IsUnitaryRep U)
    (h0 : TendstoStrongly U (𝓝 0) 1) (a : Fin n → ℝ) : U a = jointExpI (momentumOp U) a := by
  have hk : ∀ k, expI (momentumOp U k) (a k) = U (a k • Pi.single k 1) := fun k => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgen, -⟩ :=
      (h₄ H).1 _ (isContinuousUnitaryGroup_axis hU h0 k)
    exact (hgen.2 (a k)).symm
  unfold jointExpI
  simp only [hk]
  rw [prod_ofFn_unitaryRep hU, sum_smul_single_eq]
theorem isStronglyCont_of_tendstoStrongly {U : (Fin n → ℝ) → H →L[ℂ] H}
    (hU : IsUnitaryRep U) (h0 : TendstoStrongly U (𝓝 0) 1) : IsStronglyCont U := by
  intro ψ
  refine continuous_iff_continuousAt.mpr fun a₀ => ?_
  have h1 : Tendsto (fun a => a - a₀) (𝓝 a₀) (𝓝 0) := by
    have hcont : Continuous fun a : Fin n → ℝ => a - a₀ := by fun_prop
    simpa using hcont.tendsto a₀
  have h2 : Tendsto (fun a => U (a - a₀) ψ) (𝓝 a₀) (𝓝 ψ) := (h0 ψ).comp h1
  have h3 := ((U a₀).continuous.tendsto ψ).comp h2
  refine h3.congr fun a => ?_
  change U a₀ (U (a - a₀) ψ) = U a ψ
  rw [← ContinuousLinearMap.mul_apply, hU.2.2, add_sub_cancel]
theorem unitaryRep_eq_integralOp {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H}
    (hT : IsCommutingSemigroupRep T U) {E : SpectralMeasure (nonnegHalfSpace n) H}
    (hE : IsJointSpectralMeasure E T U) (a : Fin n → ℝ) :
    U a = E.integralOp fun y =>
      Complex.exp (Complex.I * ((a ⬝ᵥ spatialCoords y.1 : ℝ) : ℂ)) := by
  have h1 := hE 0 a
  rw [(semigroupRep_apply_zero hT).1, one_mul] at h1
  refine h1.trans ?_
  congr 1
  funext y
  simp
theorem measurable_cexp_dotProduct (a : Fin n → ℝ) :
    Measurable fun y : FullSpace (n + 1) =>
      Complex.exp (Complex.I * ((a ⬝ᵥ spatialCoords y.1 : ℝ) : ℂ)) :=
  measurable_cexp_I_mul ((measurable_dotProduct_const a).comp
    (measurable_spatialCoords.comp measurable_subtype_coe))
theorem isUnitaryJointMeasure_extendToWhole (h₂ : BorelCalculus.BorelCalculusTheorem)
    (h₃ : ContractionSemigroups.ContractionSemigroupTheorem)
    (h₅ : CoordOps.CoordOpsTheorem)
    (h₇ : SpectralTheorem.SpectralTheoremHolds)
    {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H} (hT : IsCommutingSemigroupRep T U)
    {E : SpectralMeasure (nonnegHalfSpace n) H} (hE : IsJointSpectralMeasure E T U) :
    IsUnitaryJointMeasure (extendToWhole E) T U := by
  obtain ⟨hc, -⟩ := (h₂ H (n + 1)).1 _ (extendToWhole E)
  intro τ a
  have hy0 : Measurable fun y : FullSpace (n + 1) => τ * y.1 0 :=
    (measurable_fullSpace_apply 0).const_mul τ
  have hUa : U a = (extendToWhole E).integralOp fun y =>
      Complex.exp (Complex.I * ((a ⬝ᵥ spatialCoords y.1 : ℝ) : ℂ)) := by
    rw [integralOp_extendToWhole h₂ E (measurable_cexp_dotProduct a) (c := 1)
      fun y => (norm_cexp_I_mul _).le]
    exact unitaryRep_eq_integralOp hT hE a
  rw [← coordOperator_zero_eq h₂ h₃ h₅ h₇ hT hE, expI_coordOperator h₂ h₅]
  nth_rewrite 1 [hUa]
  rw [← hc.mul _ _ (measurable_cexp_I_mul hy0) (isBoundedFn_cexp_I_mul _)
    (measurable_cexp_dotProduct a) (isBoundedFn_cexp_I_mul _)]
  congr 1
  funext y
  rw [Pi.mul_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem representsGroup_spatialMarginal (h₂ : BorelCalculus.BorelCalculusTheorem) (hn : 1 ≤ n)
    {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H} (hT : IsCommutingSemigroupRep T U)
    {E : SpectralMeasure (nonnegHalfSpace n) H} (hE : IsJointSpectralMeasure E T U) :
    RepresentsGroup (spatialMarginal hn E) U := by
  obtain ⟨-, -, -, -, -, hi, -⟩ := (h₂ H (n + 1)).1 _ E
  intro a
  have hg : Measurable fun p : FullSpace n =>
      Complex.exp (Complex.I * ((a ⬝ᵥ p.1 : ℝ) : ℂ)) :=
    measurable_cexp_I_mul ((measurable_dotProduct_const a).comp measurable_subtype_coe)
  exact (unitaryRep_eq_integralOp hT hE a).trans
    (integralOp_pushforward hi hn MeasurableSet.univ projSpatial measurable_projSpatial hg (c := 1)
      fun y => (norm_cexp_I_mul _).le).symm
theorem representsGroup_unique (h₄ : UnitaryGroups.StoneTheoremHolds)
    {U : (Fin n → ℝ) → H →L[ℂ] H} {E₁ E₂ : SpectralMeasure (FullSpace n) H}
    (h₁ : RepresentsGroup E₁ U) (h₂ : RepresentsGroup E₂ U) : E₁ = E₂ := by
  refine (h₄ H).2 n E₁ E₂ fun s i _ => ?_
  have e := (h₁ (s • Pi.single i 1)).symm.trans (h₂ (s • Pi.single i 1))
  have hf : (fun y : FullSpace n => Complex.exp (Complex.I * s * ((y.1 i : ℝ) : ℂ))) =
      fun p : FullSpace n => Complex.exp (Complex.I *
        (((s • (Pi.single i 1 : Fin n → ℝ)) ⬝ᵥ p.1 : ℝ) : ℂ)) :=
    funext fun y => by rw [smul_single_dotProduct, cexp_I_mul_mul_eq]
  exact (congrArg E₁.integralOp hf).trans (e.trans (congrArg E₂.integralOp hf).symm)
theorem isUnitaryJointMeasure_unique (h₄ : UnitaryGroups.StoneTheoremHolds)
    {T : ℝ≥0 → H →L[ℂ] H} {U : (Fin n → ℝ) → H →L[ℂ] H}
    {E₁ E₂ : SpectralMeasure (FullSpace (n + 1)) H}
    (h₁ : IsUnitaryJointMeasure E₁ T U) (h₂ : IsUnitaryJointMeasure E₂ T U) : E₁ = E₂ := by
  refine (h₄ H).2 (n + 1) E₁ E₂ fun s i _ => ?_
  induction i using Fin.cases with
  | zero =>
    have e := (h₁ s 0).symm.trans (h₂ s 0)
    have hf : (fun y : FullSpace (n + 1) => Complex.exp (Complex.I * s * ((y.1 0 : ℝ) : ℂ))) =
        fun y : FullSpace (n + 1) => Complex.exp (Complex.I *
          ((s * y.1 0 + (0 : Fin n → ℝ) ⬝ᵥ spatialCoords y.1 : ℝ) : ℂ)) :=
      funext fun y => by rw [zero_dotProduct, add_zero, cexp_I_mul_mul_eq]
    exact (congrArg E₁.integralOp hf).trans (e.trans (congrArg E₂.integralOp hf).symm)
  | succ i =>
    have e := (h₁ 0 (s • Pi.single i 1)).symm.trans (h₂ 0 (s • Pi.single i 1))
    have hf : (fun y : FullSpace (n + 1) =>
          Complex.exp (Complex.I * s * ((y.1 i.succ : ℝ) : ℂ))) =
        fun y : FullSpace (n + 1) => Complex.exp (Complex.I *
          ((0 * y.1 0 + (s • (Pi.single i 1 : Fin n → ℝ)) ⬝ᵥ spatialCoords y.1 : ℝ) : ℂ)) :=
      funext fun y => by
        rw [smul_single_dotProduct, zero_mul, zero_add, cexp_I_mul_mul_eq]
        rfl
    exact (congrArg E₁.integralOp hf).trans (e.trans (congrArg E₂.integralOp hf).symm)
theorem isCommutingSemigroupRep_one {U : (Fin n → ℝ) → H →L[ℂ] H} (hU : IsUnitaryRep U)
    (h0 : TendstoStrongly U (𝓝 0) 1) :
    IsCommutingSemigroupRep (fun _ : ℝ≥0 => (1 : H →L[ℂ] H)) U where
  isContractionSemigroup :=
    { semigroup := ⟨rfl, fun _ _ => one_mul 1⟩
      selfAdjoint := fun _ => IsSelfAdjoint.one _
      contraction := fun _ => ContinuousLinearMap.norm_id_le
      tendsto_zero := fun _ => tendsto_const_nhds }
  isUnitaryRep := hU
  tendstoStrongly_zero := h0
  commute := fun a _ => by simp
end Main
theorem jointSpectralTheoremForPair_holds (h₀ : HilbertSpaceFacts.Facts)
    (h₂ : BorelCalculus.BorelCalculusTheorem)
    (h₃ : ContractionSemigroups.ContractionSemigroupTheorem)
    (h₄ : UnitaryGroups.StoneTheoremHolds)
    (h₅ : CoordOps.CoordOpsTheorem)
    (h₆ : JointSpectral.JointSpectralTheorem)
    (h₇ : SpectralTheorem.SpectralTheoremHolds) : JointSpectralTheoremForPair := by
  intro H _ _ _ n hn
  refine ⟨fun T U hT => ?_, fun U hU h0 => ?_⟩
  · obtain ⟨E₀, hE₀, hcomm⟩ := exists_isJointSpectralMeasure h₀ h₂ h₃ h₄ h₆ hT
    have hJ : IsJointSpectralMeasure (jointSpectralMeasure T U) T U :=
      Classical.epsilon_spec (p := fun E => IsJointSpectralMeasure E T U) ⟨E₀, hE₀⟩
    have hJe : jointSpectralMeasure T U = E₀ :=
      isJointSpectralMeasure_unique h₂ h₃ h₄ h₅ h₇ hT hJ hE₀
    have hk := coordOperator_eq h₂ h₃ h₄ h₅ h₇ hT hJ
    have hk0 := coordOperator_zero_eq h₂ h₃ h₅ h₇ hT hJ
    have hks := coordOperator_succ_eq h₂ h₄ h₅ hT hJ
    obtain ⟨ha, hcs, hco, -, -⟩ := h₅ H (n + 1) (extendToWhole (jointSpectralMeasure T U))
    obtain ⟨-, -, -, -, -, hi, -⟩ := (h₂ H (n + 1)).1 _ (jointSpectralMeasure T U)
    have hWm := isUnitaryJointMeasure_extendToWhole h₂ h₃ h₅ h₇ hT hJ
    have hM := representsGroup_spatialMarginal h₂ hn hT hJ
    have hmc : ∀ l : Fin (n + 1), Measurable fun y : FullSpace (n + 1) => ((y.1 l : ℝ) : ℂ) :=
      fun l => Complex.measurable_ofReal.comp ((measurable_pi_apply l).comp measurable_subtype_coe)
    have hint : ∀ (l : Fin (n + 1)) (A : UnboundedOp H), coordOperator
        (extendToWhole (jointSpectralMeasure T U)) l = A →
        IsSpectralIntegralOf A (jointSpectralMeasure T U) fun y => ((y.1 l : ℝ) : ℂ) :=
      fun l A hA => by
      have h1 := hco l
      rw [hA] at h1
      exact isSpectralIntegralOf_comp_pushforward hi (jointSpectralMeasure T U).one_le_dimension
        MeasurableSet.univ (inclusion (subset_univ _)) measurable_subtype_coe.subtype_mk (hmc l) h1
    refine ⟨isStronglyCont_of_tendstoStrongly hT.isUnitaryRep hT.tendstoStrongly_zero,
      ⟨_, hJ, fun E hE => isJointSpectralMeasure_unique h₂ h₃ h₄ h₅ h₇ hT hE hJ⟩, hJ,
      hint 0 _ hk0, fun i => hint i.succ _ (hks i), ?_, fun i => ?_, ?_,
      unitaryRep_eq_jointExpI h₄ hT.isUnitaryRep hT.tendstoStrongly_zero,
      fun B h1 h2 Δ => ?_, hWm, fun E' hE' => isUnitaryJointMeasure_unique h₄ hE' hWm, hM,
      fun E'' hE'' => representsGroup_unique h₄ hE'' hM⟩
    · rw [← hk0]
      exact (ha 0).2.1.symm
    · rw [← hks i]
      exact (ha i.succ).2.1.symm
    · have he : energyMomentumOps T U =
          coordOperator (extendToWhole (jointSpectralMeasure T U)) :=
        funext fun l => (hk l).symm
      rw [he]
      exact hcs
    · rw [hJe]
      exact hcomm B h1 h2 Δ
  · have hT := isCommutingSemigroupRep_one hU h0
    obtain ⟨E₀, hE₀, -⟩ := exists_isJointSpectralMeasure h₀ h₂ h₃ h₄ h₆ hT
    have hM := representsGroup_spatialMarginal h₂ hn hT hE₀
    have hR : RepresentsGroup (groupSpectralMeasure hn U) U :=
      Classical.epsilon_spec (p := fun E => RepresentsGroup E U) ⟨_, hM⟩
    exact ⟨⟨_, hM, fun E h => representsGroup_unique h₄ h hM⟩, hR⟩
end YangMills.Construction.SemigroupRepresentation
