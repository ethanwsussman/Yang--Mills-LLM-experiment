import YangMills.Construction.Towers.FormsOfTheFreeOperatorsInCoefficientsProof
import YangMills.Construction.EuclideanFunctionals.CauchyEstimateAtARealPoint
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.CauchyEstimate
open RealCoordinates Coordinates Coordinates.ComplexCoordinates
  Coordinates.ComplexCoordinates.PowerSeriesHolomorphy
def IsHoloSmooth (U : Set (ComplexCoordinates 4)) (F : ComplexCoordinates 4 → ℂ) : Prop :=
  DifferentiableOn ℂ F U ∧ ContDiffOn ℝ ∞ F U
def cpartial (i : Fin 4) (F : ComplexCoordinates 4 → ℂ) (w : ComplexCoordinates 4) : ℂ :=
  fderiv ℂ F w (stdBasisVector i)
def iteratedCPartial (α : Multiindex) (F : ComplexCoordinates 4 → ℂ) :
    ComplexCoordinates 4 → ℂ :=
  (cpartial 0)^[α 0] ((cpartial 1)^[α 1]
    ((cpartial 2)^[α 2] ((cpartial 3)^[α 3] F)))
theorem exists_clm_of_commute_I (T : ComplexCoordinates 4 →L[ℝ] ℂ)
    (hT : ∀ v, T (Complex.I • v) = Complex.I * T v) :
    ∃ T' : ComplexCoordinates 4 →L[ℂ] ℂ, T'.restrictScalars ℝ = T := by
  refine ⟨⟨{ toFun := T, map_add' := T.map_add, map_smul' := ?_ }, T.continuous⟩, ?_⟩
  · intro c v
    have hv : c • v = c.re • v + c.im • (Complex.I • v) := by
      ext j
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
      conv_lhs => rw [← Complex.re_add_im c]
      ring
    simp only [RingHom.id_apply]
    rw [hv, T.map_add, T.map_smul, T.map_smul, hT]
    simp only [smul_eq_mul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  · ext v
    rfl
theorem hasDerivAt_complexLine {F : ComplexCoordinates 4 → ℂ} {w e : ComplexCoordinates 4} {ζ : ℂ}
    (hw : DifferentiableAt ℂ F (w + ζ • e)) :
    HasDerivAt (fun ζ : ℂ => F (w + ζ • e)) (fderiv ℂ F (w + ζ • e) e) ζ := by
  have hline : HasDerivAt (fun ζ : ℂ => w + ζ • e) e ζ := by
    simpa using ((hasDerivAt_id ζ).smul_const e).const_add w
  exact hw.hasFDerivAt.comp_hasDerivAt ζ hline
theorem fderiv_real_eq_complex {F : ComplexCoordinates 4 → ℂ} {w : ComplexCoordinates 4}
    (hw : DifferentiableAt ℂ F w) (v : ComplexCoordinates 4) :
    fderiv ℝ F w v = fderiv ℂ F w v := by
  have := (hw.hasFDerivAt.restrictScalars ℝ).fderiv
  rw [this]
  rfl
theorem IsHoloSmooth.deriv_coord {U : Set (ComplexCoordinates 4)}
    {F : ComplexCoordinates 4 → ℂ} (hU : IsOpen U) (hF : IsHoloSmooth U F) (i : Fin 4) :
    IsHoloSmooth U (cpartial i F) := by
  set e : ComplexCoordinates 4 := stdBasisVector i with he
  have hdiff : ∀ w ∈ U, DifferentiableAt ℂ F w :=
    fun w hw => hF.1.differentiableAt (hU.mem_nhds hw)
  have hK : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.2.fderiv_of_isOpen hU (by simp)
  have heq : ∀ w ∈ U, cpartial i F w = fderiv ℝ F w e :=
    fun w hw => (fderiv_real_eq_complex (hdiff w hw) e).symm
  refine ⟨?_, ?_⟩
  · intro b hb
    have hbn : U ∈ 𝓝 b := hU.mem_nhds hb
    have hKb : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) b) b :=
      ((hK.contDiffAt hbn).differentiableAt (by simp)).hasFDerivAt
    set B := fderiv ℝ (fderiv ℝ F) b with hB
    have hsymm : ∀ v u, B v u = B u v :=
      ((hF.2.contDiffAt hbn).isSymmSndFDerivAt (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact ENat.LEInfty.out))
    have happ : ∀ u, HasFDerivAt (fun w => fderiv ℝ F w u)
        ((ContinuousLinearMap.apply ℝ ℂ u).comp B) b :=
      fun u => (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp b hKb
    have hI : ∀ v u, B v (Complex.I • u) = Complex.I * B v u := by
      intro v u
      have h1 := happ (Complex.I • u)
      have h2 : HasFDerivAt (fun w => fderiv ℝ F w (Complex.I • u))
          (Complex.I • (ContinuousLinearMap.apply ℝ ℂ u).comp B) b := by
        refine ((happ u).const_smul Complex.I).congr_of_eventuallyEq ?_
        filter_upwards [hbn] with w hw
        change fderiv ℝ F w (Complex.I • u) = Complex.I • fderiv ℝ F w u
        rw [fderiv_real_eq_complex (hdiff w hw), fderiv_real_eq_complex (hdiff w hw), map_smul]
      have := congrArg (fun T : ComplexCoordinates 4 →L[ℝ] ℂ => T v) (h1.unique h2)
      simpa using this
    obtain ⟨T', hT'⟩ := exists_clm_of_commute_I ((ContinuousLinearMap.apply ℝ ℂ e).comp B) (by
      intro v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
      rw [hsymm, hI, hsymm])
    have hder : HasFDerivAt (𝕜 := ℂ) (fun w => fderiv ℝ F w e) T' b :=
      hasFDerivAt_of_restrictScalars ℝ (happ e) hT'
    refine (hder.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hbn] with w hw using heq w hw
  · exact ((hK.clm_apply contDiffOn_const).congr heq)
theorem IsHoloSmooth.iter {U : Set (ComplexCoordinates 4)}
    {F : ComplexCoordinates 4 → ℂ} (hU : IsOpen U) (hF : IsHoloSmooth U F) (i : Fin 4)
    (n : ℕ) : IsHoloSmooth U ((cpartial i)^[n] F) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.deriv_coord hU i
theorem IsHoloSmooth.multi {U : Set (ComplexCoordinates 4)}
    {F : ComplexCoordinates 4 → ℂ} (hU : IsOpen U) (hF : IsHoloSmooth U F)
    (α : Multiindex) : IsHoloSmooth U (iteratedCPartial α F) :=
  (((hF.iter hU 3 _).iter hU 2 _).iter hU 1 _).iter hU 0 _
theorem isHoloSmooth_of_isHolomorphicIn (H : PowerSeriesHolomorphy.Properties)
    {U : Set (ComplexCoordinates 4)} {F : ComplexCoordinates 4 → ℂ} (hU : IsOpen U)
    (hF : IsHolomorphicIn (N' := 1) U (fun w _ => F w)) : IsHoloSmooth U F := by
  obtain ⟨-, hC, hL, -, -⟩ := (H.1 4 U hU).1 1 _ hF
  refine ⟨fun b hb => ?_, contDiffOn_pi.1 hC 0⟩
  obtain ⟨T, hT⟩ := hL b hb
  have hd : HasFDerivAt (𝕜 := ℂ) (fun w (_ : Fin 1) => F w) T b :=
    hasFDerivAt_of_restrictScalars ℝ hT rfl
  exact (differentiableAt_pi.1 hd.differentiableAt 0).differentiableWithinAt
theorem IsHoloSmooth.isHolomorphicIn {U : Set (ComplexCoordinates 4)}
    {F : ComplexCoordinates 4 → ℂ} (hU : IsOpen U) (hF : IsHoloSmooth U F) :
    IsHolomorphicIn (N' := 1) U (fun w _ => F w) := by
  refine ⟨hU, continuousOn_pi.2 fun _ => hF.1.continuousOn, fun a ha j => ?_⟩
  have hcont : ContinuousAt (fun ζ : ℂ => a + ζ • stdBasisVector j) 0 := by fun_prop
  have hmem : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • stdBasisVector j ∈ U :=
    hcont.eventually_mem (by simpa using hU.mem_nhds ha)
  filter_upwards [hmem] with ζ hζ
  exact differentiableAt_pi.2 fun _ =>
    (hasDerivAt_complexLine (hF.1.differentiableAt (hU.mem_nhds hζ))).differentiableAt
theorem iteratedDeriv_complexLine {U : Set (ComplexCoordinates 4)} {F : ComplexCoordinates 4 → ℂ}
    (hU : IsOpen U) (hF : IsHoloSmooth U F) (i : Fin 4) (w : ComplexCoordinates 4) (n : ℕ) :
    ∀ ζ : ℂ, w + ζ • stdBasisVector i ∈ U →
      iteratedDeriv n (fun ζ : ℂ => F (w + ζ • stdBasisVector i)) ζ =
        (cpartial i)^[n] F (w + ζ • stdBasisVector i) := by
  have hWopen : IsOpen {ζ : ℂ | w + ζ • stdBasisVector i ∈ U} :=
    hU.preimage (by fun_prop)
  induction n with
  | zero => intro ζ _; simp
  | succ n ih =>
    intro ζ hζ
    rw [iteratedDeriv_succ, Function.iterate_succ_apply']
    have hev : iteratedDeriv n (fun ζ : ℂ => F (w + ζ • stdBasisVector i)) =ᶠ[𝓝 ζ]
        fun ζ : ℂ => (cpartial i)^[n] F (w + ζ • stdBasisVector i) := by
      filter_upwards [hWopen.mem_nhds hζ] with ζ' hζ' using ih ζ' hζ'
    rw [hev.deriv_eq]
    exact (hasDerivAt_complexLine
      ((hF.iter hU i n).1.differentiableAt (hU.mem_nhds hζ))).deriv
theorem norm_iterate_cpartial_le {U A B : Set (ComplexCoordinates 4)} {F : ComplexCoordinates 4 → ℂ}
    (hU : IsOpen U) (hF : IsHoloSmooth U F) (i : Fin 4) (n : ℕ) {r C : ℝ} (hr : 0 < r)
    (hAU : A ⊆ U) (hBA : ∀ w ∈ B, ∀ ζ : ℂ, ‖ζ‖ ≤ r → w + ζ • stdBasisVector i ∈ A)
    (hC : ∀ w ∈ A, ‖F w‖ ≤ C) :
    ∀ w ∈ B, ‖(cpartial i)^[n] F w‖ ≤ n.factorial * C / r ^ n := by
  intro w hw
  have hball : ∀ ζ ∈ Metric.closedBall (0 : ℂ) r, w + ζ • stdBasisVector i ∈ A := fun ζ hζ =>
    hBA w hw ζ (by simpa using hζ)
  have hdiff : DifferentiableOn ℂ (fun ζ : ℂ => F (w + ζ • stdBasisVector i))
      (Metric.closedBall (0 : ℂ) r) := fun ζ hζ =>
    (hasDerivAt_complexLine (hF.1.differentiableAt
      (hU.mem_nhds (hAU (hball ζ hζ))))).differentiableAt.differentiableWithinAt
  have hest := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) n hr
    (hdiff.diffContOnCl_ball subset_rfl) (C := C)
    (fun ζ hζ => hC _ (hball ζ (Metric.sphere_subset_closedBall hζ)))
  have h0 : w + (0 : ℂ) • stdBasisVector i ∈ U := hAU (hball 0 (by simpa using hr.le))
  rw [iteratedDeriv_complexLine hU hF i w n 0 h0] at hest
  simpa using hest
theorem partialDerivR4_eq_cpartial {U : Set (ComplexCoordinates 4)} {F : ComplexCoordinates 4 → ℂ}
    (hU : IsOpen U) (hF : IsHoloSmooth U F) (i : Fin 4) {g : R4 → ℂ}
    (hgU : ∀ x ∈ complexify ⁻¹' U, g x = F (complexify x)) :
    ∀ x ∈ complexify ⁻¹' U,
      TestFunctions.partialDerivR4 i g x = cpartial i F (complexify x) := by
  intro x hx
  have hline : ∀ t : ℝ, complexify (x + t • Pi.single i (1 : ℝ)) =
      complexify x + t • stdBasisVector i := by
    intro t
    ext j
    by_cases hj : j = i
    · subst hj
      simp [complexify, stdBasisVector]
    · simp [complexify, stdBasisVector, Pi.single_eq_of_ne hj]
  have hcont : ContinuousAt (fun t : ℝ => complexify x + t • stdBasisVector i) 0 := by fun_prop
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, complexify x + t • stdBasisVector i ∈ U :=
    hcont.eventually_mem (by simpa using hU.mem_nhds hx)
  have hlineD : HasDerivAt (fun t : ℝ => complexify x + t • stdBasisVector i)
      (stdBasisVector i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (stdBasisVector i)).const_add (complexify x)
  have hfd : HasFDerivAt F ((fderiv ℂ F (complexify x)).restrictScalars ℝ)
      (complexify x + (0 : ℝ) • stdBasisVector i) := by
    simpa using ((hF.1.differentiableAt (hU.mem_nhds hx)).hasFDerivAt.restrictScalars ℝ)
  have hder := hfd.comp_hasDerivAt (0 : ℝ) hlineD
  unfold TestFunctions.partialDerivR4
  have hev : (fun t : ℝ => g (x + t • Pi.single i (1 : ℝ))) =ᶠ[𝓝 0]
      (F ∘ fun t : ℝ => complexify x + t • stdBasisVector i) := by
    filter_upwards [hmem] with t ht
    rw [← hline] at ht
    rw [hgU _ ht, Function.comp_apply, hline]
  rw [hev.deriv_eq]
  exact hder.deriv
theorem iterate_partialDerivR4_eq {U : Set (ComplexCoordinates 4)} {F : ComplexCoordinates 4 → ℂ}
    (hU : IsOpen U) (hF : IsHoloSmooth U F) (i : Fin 4) (n : ℕ) {g : R4 → ℂ}
    (hgU : ∀ x ∈ complexify ⁻¹' U, g x = F (complexify x)) :
    ∀ x ∈ complexify ⁻¹' U,
      (TestFunctions.partialDerivR4 i)^[n] g x = (cpartial i)^[n] F (complexify x) := by
  induction n with
  | zero => exact hgU
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact partialDerivR4_eq_cpartial hU (hF.iter hU i n) i ih x hx
theorem iteratedPartial_eq {U : Set (ComplexCoordinates 4)} {F : ComplexCoordinates 4 → ℂ}
    (hU : IsOpen U) (hF : IsHoloSmooth U F) (α : Multiindex) :
    ∀ x ∈ complexify ⁻¹' U, iteratedPartial α (realRestriction F) x =
      iteratedCPartial α F (complexify x) :=
  iterate_partialDerivR4_eq hU (((hF.iter hU 3 _).iter hU 2 _).iter hU 1 _) 0 _
    (iterate_partialDerivR4_eq hU ((hF.iter hU 3 _).iter hU 2 _) 1 _
      (iterate_partialDerivR4_eq hU (hF.iter hU 3 _) 2 _
        (iterate_partialDerivR4_eq hU hF 3 _ fun _ _ => rfl)))
def pinnedPolydisk (a : ComplexCoordinates 4) (r : ℝ) (k : ℕ) : Set (ComplexCoordinates 4) :=
  {w | ∀ j : Fin 4, ‖w j - a j‖ ≤ r ∧ (k ≤ (j : ℕ) → w j = a j)}
theorem pinnedPolydisk_shift {a : ComplexCoordinates 4} {r : ℝ} (i : Fin 4) (k : ℕ)
    (hk : (i : ℕ) = k) :
    ∀ w ∈ pinnedPolydisk a r k, ∀ ζ : ℂ, ‖ζ‖ ≤ r →
      w + ζ • stdBasisVector i ∈ pinnedPolydisk a r (k + 1) := by
  intro w hw ζ hζ j
  by_cases hj : j = i
  · subst hj
    have hwa : w j = a j := (hw j).2 hk.ge
    refine ⟨by simpa [stdBasisVector, hwa] using hζ, fun h => by omega⟩
  · have hjw : (w + ζ • stdBasisVector i) j = w j := by
      simp [stdBasisVector, Pi.single_eq_of_ne hj]
    rw [hjw]
    exact ⟨(hw j).1, fun h => (hw j).2 (by omega)⟩
theorem norm_iteratedCPartial_le {U : Set (ComplexCoordinates 4)} {F : ComplexCoordinates 4 → ℂ}
    (hU : IsOpen U) (hF : IsHoloSmooth U F) (a : ComplexCoordinates 4) {r c : ℝ}
    (hr : 0 < r) (hP : closedPolydisk a r ⊆ U) (hc : ∀ w ∈ closedPolydisk a r, ‖F w‖ ≤ c)
    (α : Multiindex) :
    ‖iteratedCPartial α F a‖ ≤ (α.fact : ℝ) * r ^ (-(α.order : ℤ)) * c := by
  have hsub : ∀ k, pinnedPolydisk a r k ⊆ closedPolydisk a r := fun k w hw j => (hw j).1
  have hsubU : ∀ k, pinnedPolydisk a r k ⊆ U := fun k => (hsub k).trans hP
  have b3 := norm_iterate_cpartial_le hU hF 3 (α 3) hr (hsubU 4) (pinnedPolydisk_shift 3 3 rfl)
    (fun w hw => hc w (hsub 4 hw))
  have b2 := norm_iterate_cpartial_le hU (hF.iter hU 3 _) 2 (α 2) hr (hsubU 3)
    (pinnedPolydisk_shift 2 2 rfl) b3
  have b1 := norm_iterate_cpartial_le hU ((hF.iter hU 3 _).iter hU 2 _) 1 (α 1) hr (hsubU 2)
    (pinnedPolydisk_shift 1 1 rfl) b2
  have b0 := norm_iterate_cpartial_le hU (((hF.iter hU 3 _).iter hU 2 _).iter hU 1 _) 0 (α 0) hr
    (hsubU 1) (pinnedPolydisk_shift 0 0 rfl) b1
  have ha : a ∈ pinnedPolydisk a r 0 := fun j => ⟨by simpa using hr.le, fun _ => rfl⟩
  refine (b0 a ha).trans (le_of_eq ?_)
  simp only [Multiindex.fact, Multiindex.order, Fin.prod_univ_four, Fin.sum_univ_four]
  rw [zpow_neg, zpow_natCast, pow_add, pow_add, pow_add]
  push_cast
  field_simp
theorem complexify_rePart {w : ComplexCoordinates 4} (hw : w ∈ realLocus 4) :
    complexify (rePart w) = w := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.toComplexVec_re <;> assumption
theorem cauchyBound_holds (H : PowerSeriesHolomorphy.Properties) : CauchyBound := by
  intro U F hU hF
  have hg : IsHoloSmooth U F := isHoloSmooth_of_isHolomorphicIn H hU hF
  have htc : ContDiff ℝ ∞ (complexify : R4 → ComplexCoordinates 4) :=
    contDiff_pi.2 fun j => Complex.ofRealCLM.contDiff.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) j).contDiff
  refine ⟨⟨hg.2.comp htc.contDiffOn (fun _ hx => hx), fun α => ?_⟩, ?_⟩
  · have hol := (hg.multi hU α).isHolomorphicIn hU
    obtain ⟨-, -, -, -, hra⟩ := (H.1 4 U hU).1 1 _ hol
    refine ⟨hra.1, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := hra.2 a ha
    refine ⟨c, ?_⟩
    have hUa : ∀ᶠ w in 𝓝[realLocus 4] a, w ∈ U :=
      mem_nhdsWithin_of_mem_nhds (hU.mem_nhds ha.1)
    filter_upwards [hc, hUa, self_mem_nhdsWithin] with w hw hwU hwr
    convert hw using 1
    funext _
    have hwx : complexify (rePart w) = w := complexify_rePart hwr
    have hmem : rePart w ∈ complexify ⁻¹' U := by
      change complexify (rePart w) ∈ U
      rw [hwx]
      exact hwU
    change iteratedPartial α (realRestriction F) (rePart w) = _
    rw [iteratedPartial_eq hU hg α _ hmem, hwx]
  · intro x r c hx hr _ hP hb α
    rw [iteratedPartial_eq hU hg α x hx]
    exact norm_iteratedCPartial_le hU hg _ hr hP hb α
end YangMills.Construction.EuclideanFunctionals.CauchyEstimate
