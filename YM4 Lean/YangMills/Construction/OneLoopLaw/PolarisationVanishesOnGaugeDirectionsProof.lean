import YangMills.Construction.OneLoopLaw.FirstDerivativeOfAMemberVanishesProof
import YangMills.Construction.DirichletOperator.DerivativeBoundsOfTheFunctionsOfACubeProof
import YangMills.Construction.OneLoopLaw.GaugeColourMomentaAndDifferencesOfFunctionalsProof
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace YangMills.Construction.OneLoopLaw.GaugeDirectionHessian
open Matrices Matrices.PowerExpCharts Tower PeriodicOperators.Tempered
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem iteratedDeriv_lines_eq_secondFDeriv {G : E → ℝ} (hG : ContDiffAt ℝ 2 G 0)
    (v w : E) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => G (s • v + t • w)) 0) 0 =
      fderiv ℝ (fderiv ℝ G) 0 v w := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_two_param <;> assumption
private theorem secondFDeriv_eq_zero_of_invariant {G : E → ℝ} {T : ℝ × E → E}
    (hG : ContDiffAt ℝ 2 G 0) (hd : fderiv ℝ G 0 = 0) (hT : ContDiffAt ℝ 2 T (0, 0))
    (hT0 : ∀ᶠ Y in 𝓝 (0 : E), T (0, Y) = Y)
    (hinv : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : E)), G (T p) = G p.2)
    {v : E} (hv : HasDerivAt (fun t : ℝ => T (t, 0)) v 0) (w : E) :
    fderiv ℝ (fderiv ℝ G) 0 v w = 0 := by
  have hzero : T (0, 0) = 0 := hT0.self_of_nhds
  have hDG : DifferentiableAt ℝ (fderiv ℝ G) 0 :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDT : DifferentiableAt ℝ (fderiv ℝ T) (0, 0) :=
    (hT.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hGnear : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ G y :=
    (hG.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hTnear : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : E)), DifferentiableAt ℝ T p :=
    (hT.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hTt : Tendsto T (𝓝 ((0 : ℝ), (0 : E))) (𝓝 0) := by
    have h := hT.continuousAt
    rwa [ContinuousAt, hzero] at h
  have hsnd : Tendsto (Prod.snd : ℝ × E → E) (𝓝 ((0 : ℝ), (0 : E))) (𝓝 0) :=
    continuous_snd.tendsto _
  have hfirst : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : E)),
      fderiv ℝ G (T p) (fderiv ℝ T p (0, w)) = fderiv ℝ G p.2 w := by
    filter_upwards [hinv.eventually_nhds, hTnear, hTt.eventually hGnear, hsnd.eventually hGnear]
      with p hp hTp hGp hGs
    have h1 : HasFDerivAt (fun q => G (T q)) ((fderiv ℝ G (T p)).comp (fderiv ℝ T p)) p :=
      hGp.hasFDerivAt.comp p hTp.hasFDerivAt
    have h2 : HasFDerivAt (fun q : ℝ × E => G q.2)
        ((fderiv ℝ G p.2).comp (ContinuousLinearMap.snd ℝ ℝ E)) p :=
      hGs.hasFDerivAt.comp p hasFDerivAt_snd
    have h3 := (h1.congr_of_eventuallyEq (hp.mono fun q hq => hq.symm)).unique h2
    simpa using congrArg (fun A => A (0, w)) h3
  have hline : Tendsto (fun t : ℝ => (t, (0 : E))) (𝓝 0) (𝓝 ((0 : ℝ), (0 : E))) := by
    have h : Continuous fun t : ℝ => (t, (0 : E)) := by fun_prop
    exact h.tendsto 0
  have hW0 : fderiv ℝ T (0, 0) (0, w) = w := by
    have hT1 : HasFDerivAt T (fderiv ℝ T (0, 0)) ((0 : ℝ), (0 : E)) :=
      (hT.differentiableAt (by norm_num)).hasFDerivAt
    have hi : HasFDerivAt (fun Y : E => T (0, Y))
        ((fderiv ℝ T (0, 0)).comp (ContinuousLinearMap.inr ℝ ℝ E)) 0 :=
      HasFDerivAt.comp (0 : E) hT1 (hasFDerivAt_prodMk_right (0 : ℝ) (0 : E))
    have hid : HasFDerivAt (fun Y : E => T (0, Y)) (ContinuousLinearMap.id ℝ E) 0 :=
      (hasFDerivAt_id (0 : E)).congr_of_eventuallyEq hT0
    simpa using congrArg (fun A => A w) (hi.unique hid)
  have hA : HasDerivAt (fun t : ℝ => fderiv ℝ T (t, 0))
      (fderiv ℝ (fderiv ℝ T) (0, 0) (1, 0)) 0 := by
    have hc : HasDerivAt (fun t : ℝ => (t, (0 : E))) ((1 : ℝ), (0 : E)) 0 :=
      (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hDT.hasFDerivAt hc
  have hΦ : HasDerivAt (fun t : ℝ => fderiv ℝ G (T (t, 0))) (fderiv ℝ (fderiv ℝ G) 0 v) 0 := by
    have h0 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) 0) (T (0, 0)) := by
      rw [hzero]
      exact hDG.hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) h0 hv
  have hc := hΦ.clm_apply (hA.clm_apply (hasDerivAt_const (0 : ℝ) ((0 : ℝ), w)))
  have hz : (fun t : ℝ => fderiv ℝ G (T (t, 0)) (fderiv ℝ T (t, 0) (0, w))) =ᶠ[𝓝 0]
      fun _ => (0 : ℝ) := by
    filter_upwards [hline.eventually hfirst] with t ht
    rw [ht, hd]
    rfl
  have h := hc.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hz)
  rw [hW0, hzero, hd] at h
  simpa using h
end Calculus
private theorem two_le_top_order : (2 : WithTop ℕ∞) ≤ ∞ := by apply _root_.YangMills.Construction.PartitionCubes.CubeFunctionDerivBounds.two_le_infty <;> assumption
section Chart
variable {L n : ℕ}
private def expI (X : ComplexMatrix2.LieElement) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • X.toMatrix)
private theorem expI_inv (X : ComplexMatrix2.LieElement) : (expI X)⁻¹ = expI (-X) := by apply _root_.YangMills.DeltaSharedProofs.p501014 <;> assumption
private theorem expI_zero : expI 0 = 1 := by
  have h : (0 : ComplexMatrix2.LieElement).toMatrix = 0 := rfl
  simp only [expI, h, smul_zero, ComplexMatrix2.matExp, NormedSpace.exp_zero]
private def lieInclusion : ComplexMatrix2.LieElement →L[ℝ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := ComplexMatrix2.LieElement.toMatrix, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
private theorem contDiff_expI : ContDiff ℝ 2 expI := by
  have he : ContDiff ℝ 2 (ComplexMatrix2.matExp) := contDiff_iff_contDiffAt.2 fun x =>
    ((NormedSpace.exp_analytic (𝕂 := ℂ) x).contDiffAt).restrict_scalars ℝ
  have hi : ContDiff ℝ 2 fun X : ComplexMatrix2.LieElement => Complex.I • lieInclusion X :=
    lieInclusion.contDiff.const_smul Complex.I
  exact he.comp hi
private theorem hasDerivAt_expI {c : ℝ → ComplexMatrix2.LieElement}
    {c' : ComplexMatrix2.LieElement} (hc : HasDerivAt c c' 0) (h0 : c 0 = 0) :
    HasDerivAt (fun t => expI (c t)) (Complex.I • c'.toMatrix) 0 := by
  have hm : HasDerivAt (fun t => lieInclusion (c t)) (lieInclusion c') 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) lieInclusion.hasFDerivAt hc
  have ha : HasDerivAt (fun t => Complex.I • lieInclusion (c t))
      (Complex.I • lieInclusion c') 0 :=
    hm.const_smul Complex.I
  have he : HasFDerivAt (ComplexMatrix2.matExp) (1 : ComplexMatrix2 →L[ℂ] ComplexMatrix2) 0 :=
    hasFDerivAt_exp_zero
  have he' : HasFDerivAt (ComplexMatrix2.matExp)
      ((1 : ComplexMatrix2 →L[ℂ] ComplexMatrix2).restrictScalars ℝ)
      ((fun t => Complex.I • lieInclusion (c t)) 0) := by
    have hz : (fun t => Complex.I • lieInclusion (c t)) 0 = 0 := by
      simp [h0]
    rw [hz]
    exact he.restrictScalars ℝ
  exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) he' ha
private theorem opposite_pos {b : UnitEdge L n} (hb : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p9846 <;> assumption
private theorem xor_pos (hL : 2 ≤ L) (hn : 0 < n) (b : UnitEdge L n) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
  PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (L := L) (m := n)
    (j := PeriodicLattice.levelDepth 0 0)
    (by omega) (by simp [PeriodicLattice.levelDepth]; omega) b
private theorem extendOddly_mem (hL : 2 ≤ L) (hn : 0 < n) {f : UnitEdge L n → ComplexMatrix2}
    (hf : ∀ b : UnitEdge L n, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly (k := 0) (j := 0) f ∈ edgeFormSpace L n 0 0 := by
  have hrr : ∀ b : UnitEdge L n, b.opposite.opposite = b :=
    fun b => PeriodicLattice.Bond.ext rfl rfl
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [extendOddly, if_pos hb]
    exact hf b hb
  · by_cases h : b.IsPositivelyOriented
    · have hr : ¬b.opposite.IsPositivelyOriented := by
        rcases xor_pos hL hn b with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact h'
        · exact absurd h h'
      simp only [extendOddly, if_pos h, if_neg hr, hrr]
    · simp only [extendOddly, if_neg h, if_pos (opposite_pos h), neg_neg]
private def formOfLieFamily (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement) :
    UnitEdge L n → ComplexMatrix2 :=
  open Classical in
  extendOddly (k := 0) (j := 0) fun b =>
    if h : b.IsPositivelyOriented then (Y ⟨b, h⟩).toMatrix else 0
private theorem formOfLieFamily_mem (hL : 2 ≤ L) (hn : 0 < n)
    (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement) :
    formOfLieFamily Y ∈ edgeFormSpace L n 0 0 := by
  refine extendOddly_mem hL hn fun b hb => ?_
  simp only [dif_pos hb]
  exact (Y ⟨b, hb⟩).2
private theorem formOfLieFamily_apply (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement)
    (s : PositiveUnitEdge L n) : formOfLieFamily Y s.1 = (Y s).toMatrix := by
  simp only [formOfLieFamily, extendOddly, if_pos s.2, dif_pos s.2]
private def expField (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement) :
    UnitEdge L n → ComplexMatrix2 :=
  fieldOfPositiveValues (k := 0) (j := 0) fun s => expI (Y s)
private theorem expField_of_pos (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement)
    {b : UnitEdge L n} (h : b.IsPositivelyOriented) : expField Y b = expI (Y ⟨b, h⟩) := by
  simp only [expField, fieldOfPositiveValues, dif_pos h]
private theorem expField_of_not_pos (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement)
    {b : UnitEdge L n} (h : ¬b.IsPositivelyOriented) :
    expField Y b = expI (-Y ⟨b.opposite, opposite_pos h⟩) := by
  simp only [expField, fieldOfPositiveValues, dif_neg h, dif_pos (opposite_pos h)]
  exact expI_inv _
private theorem expTwist_identity_eq {Z : PositiveUnitEdge L n → ComplexMatrix2.LieElement}
    {A : UnitEdge L n → ComplexMatrix2} (hZ : ∀ s, (Z s).toMatrix = A s.1) :
    PeriodicLattice.expTwist A (identityField L n) = expField Z := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · rw [expField_of_pos _ h]
    simp only [PeriodicLattice.expTwist, if_pos h, identityField, mul_one, expI, hZ ⟨b, h⟩]
  · rw [expField_of_not_pos _ h, ← expI_inv]
    simp only [PeriodicLattice.expTwist, if_neg h, identityField, mul_one, expI,
      hZ ⟨b.opposite, opposite_pos h⟩]
private theorem tendsto_expField (hL : 2 ≤ L) (hn : 0 < n)
    (hmem : ∀ X : ComplexMatrix2.LieElement, expI X ∈ PeriodicLattice.compactGaugeGroup) :
    Tendsto (expField (L := L) (n := n)) (𝓝 0)
      (𝓝[fieldSpace L n 0 0] fun _ => (1 : ComplexMatrix2)) := by
  have hX : ∀ (s : PositiveUnitEdge L n)
      (ε : ComplexMatrix2.LieElement → ComplexMatrix2.LieElement),
      Continuous ε → ε 0 = 0 →
      Tendsto (fun Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement => expI (ε (Y s)))
        (𝓝 0) (𝓝 1) := by
    intro s ε hε h0
    have hc : Continuous fun Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement =>
        expI (ε (Y s)) :=
      contDiff_expI.continuous.comp (hε.comp (continuous_apply s))
    have h := hc.tendsto 0
    simpa only [Pi.zero_apply, h0, expI_zero] using h
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun b => ?_, Eventually.of_forall fun Y => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · simp only [expField_of_pos _ h]
      exact hX _ id continuous_id rfl
    · simp only [expField_of_not_pos _ h]
      exact hX _ (fun X => -X) continuous_neg neg_zero
  · have hrr : ∀ b : UnitEdge L n, b.opposite.opposite = b :=
      fun b => PeriodicLattice.Bond.ext rfl rfl
    refine ⟨fun b _ => ?_, fun b _ => ?_⟩
    · by_cases h : b.IsPositivelyOriented
      · rw [expField_of_pos _ h]
        exact hmem _
      · rw [expField_of_not_pos _ h]
        exact hmem _
    · by_cases h : b.IsPositivelyOriented
      · have hr : ¬b.opposite.IsPositivelyOriented := by
          rcases xor_pos hL hn b with ⟨-, h'⟩ | ⟨-, h'⟩
          · exact h'
          · exact absurd h h'
        have hs : (⟨b.opposite.opposite, opposite_pos hr⟩ : PositiveUnitEdge L n) = ⟨b, h⟩ :=
          Subtype.ext (hrr b)
        rw [expField_of_not_pos _ hr, expField_of_pos _ h, expI_inv, hs]
      · have hs := opposite_pos h
        rw [expField_of_pos _ hs, expField_of_not_pos _ h, expI_inv, neg_neg]
private theorem gaugeTransform_expField (v : Vertex L n 0 0 → ComplexMatrix2)
    (hv : ∀ x, IsUnit (v x).det) (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement) :
    PeriodicLattice.gaugeTransform v (expField Y) =
      fieldOfPositiveValues (k := 0) (j := 0)
        fun s => v s.1.source * expI (Y s) * (v s.1.target)⁻¹ := by
  funext b
  simp only [PeriodicLattice.gaugeTransform]
  by_cases h : b.IsPositivelyOriented
  · rw [expField_of_pos _ h]
    simp only [fieldOfPositiveValues, dif_pos h]
  · rw [expField_of_not_pos _ h, ← expI_inv]
    simp only [fieldOfPositiveValues, dif_neg h, dif_pos (opposite_pos h)]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hv _), mul_assoc]
    rfl
private def gaugedChart (lv : Vertex L n 0 0 → ComplexMatrix2.LieElement)
    (p : ℝ × (PositiveUnitEdge L n → ComplexMatrix2.LieElement)) :
    PositiveUnitEdge L n → ComplexMatrix2 :=
  fun s => expI (p.1 • lv s.1.source) * expI (p.2 s) * expI (-(p.1 • lv s.1.target))
private theorem contDiff_gaugedChart [Fintype (PositiveUnitEdge L n)]
    (lv : Vertex L n 0 0 → ComplexMatrix2.LieElement) : ContDiff ℝ 2 (gaugedChart lv) := by
  refine contDiff_pi.2 fun s => ?_
  have hc := contDiff_expI
  have h1 : ContDiff ℝ 2 fun p : ℝ × (PositiveUnitEdge L n → ComplexMatrix2.LieElement) =>
      expI (p.1 • lv s.1.source) := hc.comp (contDiff_fst.smul contDiff_const)
  have h2 : ContDiff ℝ 2 fun p : ℝ × (PositiveUnitEdge L n → ComplexMatrix2.LieElement) =>
      expI (p.2 s) := hc.comp ((contDiff_apply ℝ _ s).comp contDiff_snd)
  have h3 : ContDiff ℝ 2 fun p : ℝ × (PositiveUnitEdge L n → ComplexMatrix2.LieElement) =>
      expI (-(p.1 • lv s.1.target)) := hc.comp (contDiff_fst.smul contDiff_const).neg
  exact (h1.mul h2).mul h3
end Chart
private theorem hessianAtIdentity_covDiff_eq_zero (hC : ExpChartsStatement)
    (hP : OneLoop.PauliMatrixRelations)
    (hD : MemberFirstDerivativeVanishes) {L n : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (F : FieldFamily L)
    (hf : IsAdmissibleMember (F n))
    (l : Vertex L n 0 0 → ComplexMatrix2) (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    (B' : UnitEdge L n → ComplexMatrix2) (hB' : B' ∈ edgeFormSpace L n 0 0) :
    hessianAtIdentity F n (covDiff (k := 0) (j := 0) (identityField L n) l) B' = 0 := by
  have hL2 : 2 ≤ L := by have := hL.2; omega
  obtain ⟨inst, O, hO, hone, hA⟩ := hf.analytic
  have hne : Nonempty (PositiveUnitEdge L n) :=
    ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, 0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩
  obtain ⟨-, -, -, ⟨β, -⟩, -⟩ := hP
  obtain ⟨hCh, -, -, -, -, -, -, hb⟩ := hC (PositiveUnitEdge L n) (PositiveUnitEdge L n)
  obtain ⟨hR, -⟩ := hb β
  have hser := ((hR O hO).1 _ (hA β)).1
  have hp : (fun _ => (1 : ComplexMatrix2)) ∈ specialUnitaryPower (PositiveUnitEdge L n) := by
    obtain ⟨W, -, rfl⟩ := hO
    exact hone.2
  obtain ⟨-, hval, hsmall⟩ := hCh _ hp
  obtain ⟨N, hN, -, hsm, -⟩ := hser.1 _ hone
  have hchart : ∀ Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement,
      expChartI (fun _ => (1 : ComplexMatrix2)) Y = fun s => expI (Y s) := by
    intro Y
    rw [(hval Y).2.1]
    funext s
    simp [expI]
  have hmem : ∀ X, expI X ∈ PeriodicLattice.compactGaugeGroup := by
    intro X
    obtain ⟨s⟩ := hne
    have h := (hval fun _ => X).2.2 s
    rw [hchart] at h
    exact h
  have hunit : ∀ X, IsUnit (expI X).det := by
    intro X
    have h : (expI X).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.1 (hmem X)).2
    rw [h]
    exact isUnit_one
  let G : (PositiveUnitEdge L n → ComplexMatrix2.LieElement) → ℝ := fun Y => F n (expField Y)
  have hcomp : ((fun w => F n (fieldOfPositiveValues (k := 0) (j := 0) w)) ∘
      expChartI (fun _ => (1 : ComplexMatrix2))) = G := by
    funext Y
    simp only [Function.comp, hchart]
    rfl
  rw [hcomp] at hsm
  have hG : ContDiffAt ℝ 2 G 0 := (hsm.contDiffAt hN).of_le two_le_top_order
  have hGd : DifferentiableAt ℝ G 0 := hG.differentiableAt (by norm_num)
  have hline : ∀ Y, HasDerivAt (fun t : ℝ => G (t • Y)) (fderiv ℝ G 0 Y) 0 := by
    intro Y
    have h := hGd.hasFDerivAt.hasLineDerivAt Y
    simpa [HasLineDerivAt] using h
  have hd : fderiv ℝ G 0 = 0 := by
    refine ContinuousLinearMap.ext fun Y => ?_
    have h := hD L n hL hn (F n) hf (formOfLieFamily Y) (formOfLieFamily_mem hL2 hn Y)
    have hfun : (fun t : ℝ => F n (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ t • formOfLieFamily Y) (identityField L n))) =
        fun t => G (t • Y) := by
      funext t
      have hZ : ∀ s, ((t • Y) s).toMatrix = (algebraMap ℝ ℂ t • formOfLieFamily Y) s.1 := by
        intro s
        rw [Pi.smul_apply, Pi.smul_apply, formOfLieFamily_apply]
        change t • (Y s).toMatrix = _
        ext i j
        simp
      rw [expTwist_identity_eq hZ]
    simp only [leftDeriv, directionalDeriv, hfun] at h
    rw [(hline Y).deriv] at h
    simpa using h
  have hε : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, ⟨O', hO', himg⟩, h1img, -, hdom, hlog, hsub, hleft, -⟩ :=
    hsmall (Real.log (19 / 10)) hε (by rw [Real.exp_log (by norm_num)])
  have hone' : (fun _ => (1 : ComplexMatrix2)) ∈ O' := by
    rw [himg] at h1img
    exact h1img.1
  have hsmallN : ∀ᶠ Y in 𝓝 (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement),
      Y ∈ smallBall (PositiveUnitEdge L n) (Real.log (19 / 10)) := by
    refine Filter.eventually_all.2 fun s => ?_
    have hc : Continuous fun Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement =>
        ‖lieInclusion (Y s)‖ :=
      (lieInclusion.continuous.comp (continuous_apply s)).norm
    have h := hc.tendsto 0
    simp only [Pi.zero_apply, map_zero, norm_zero] at h
    exact h.eventually_lt_const hε
  let ι : (PositiveUnitEdge L n → ComplexMatrix2.LieElement) →ₗ[ℝ]
      (PositiveUnitEdge L n → ComplexMatrix2) :=
    LinearMap.pi fun s =>
      (lieInclusion : ComplexMatrix2.LieElement →ₗ[ℝ] ComplexMatrix2) ∘ₗ LinearMap.proj s
  have hι : LinearMap.ker ι = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun Y Y' h => ?_
    funext s
    exact Subtype.ext (congrFun h s)
  obtain ⟨g, hg⟩ := ι.exists_leftInverse_of_injective hι
  let Q : (PositiveUnitEdge L n → ComplexMatrix2) →L[ℝ]
      (PositiveUnitEdge L n → ComplexMatrix2.LieElement) :=
    LinearMap.toContinuousLinearMap g
  have hQ : ∀ Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement,
      Q (fun s => (Y s).toMatrix) = Y :=
    fun Y => LinearMap.congr_fun hg Y
  let lv : Vertex L n 0 0 → ComplexMatrix2.LieElement :=
    fun x => (⟨l x, hl x⟩ : ComplexMatrix2.hermitianTraceless)
  let Ψ := gaugedChart lv
  let Λ := logChart (fun _ : PositiveUnitEdge L n => (1 : ComplexMatrix2))
  let T : ℝ × (PositiveUnitEdge L n → ComplexMatrix2.LieElement) →
      PositiveUnitEdge L n → ComplexMatrix2.LieElement :=
    fun p => Q (Λ (Ψ p))
  have hΨ0 : Ψ (0, 0) = fun _ => 1 := by
    funext s
    simp [Ψ, gaugedChart, expI_zero]
  have hΨmem : ∀ p, Ψ p ∈ specialUnitaryPower (PositiveUnitEdge L n) := by
    intro p s
    have hm : ∀ X, expI X ∈ ComplexMatrix2.specialUnitary := hmem
    exact mul_mem (mul_mem (hm _) (hm _)) (hm _)
  have hΨc := contDiff_gaugedChart lv
  have h1dom : (fun _ => (1 : ComplexMatrix2)) ∈
      logDomain (fun _ : PositiveUnitEdge L n => (1 : ComplexMatrix2)) :=
    hsub h1img
  have hΛ : ContDiffAt ℝ 2 Λ (Ψ (0, 0)) := by
    rw [hΨ0]
    exact (hlog.contDiffAt (hdom.mem_nhds h1dom)).of_le two_le_top_order
  have hT : ContDiffAt ℝ 2 T (0, 0) :=
    Q.contDiff.contDiffAt.comp _ (hΛ.comp _ hΨc.contDiffAt)
  have hPsi : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement)),
      (fun s => expI (T p s)) = Ψ p := by
    have h1 : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement)),
        Ψ p ∈ O' :=
      hΨc.continuous.continuousAt.eventually_mem (by
        change O' ∈ 𝓝 (Ψ (0, 0))
        rw [hΨ0]
        exact hO'.mem_nhds hone')
    filter_upwards [h1] with p hp
    have h2 : Ψ p ∈ expChartI (fun _ => (1 : ComplexMatrix2)) ''
        smallBall (PositiveUnitEdge L n) (Real.log (19 / 10)) := by
      rw [himg]
      exact ⟨hp, hΨmem p⟩
    obtain ⟨Y₁, hY₁, hE⟩ := h2
    have h3 : T p = Y₁ := by
      change Q (Λ (Ψ p)) = Y₁
      rw [← hE]
      change Q (logChart _ (expChartI _ Y₁)) = Y₁
      rw [hleft Y₁ hY₁]
      exact hQ Y₁
    rw [h3, ← hE, hchart]
  have hT0 : ∀ᶠ Y in 𝓝 (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement), T (0, Y) = Y := by
    filter_upwards [hsmallN] with Y hY
    have h1 : Ψ (0, Y) = expChartI (fun _ => (1 : ComplexMatrix2)) Y := by
      rw [hchart]
      funext s
      simp [Ψ, gaugedChart, expI_zero]
    change Q (Λ (Ψ (0, Y))) = Y
    rw [h1]
    change Q (logChart _ (expChartI _ Y)) = Y
    rw [hleft Y hY]
    exact hQ Y
  let v : ℝ → Vertex L n 0 0 → ComplexMatrix2 := fun t x => expI (t • lv x)
  have hvg : ∀ t, v t ∈ gaugeGroupAt L n 0 0 := fun t x => hmem _
  have hvt : Tendsto v (𝓝 0) (𝓝[gaugeGroupAt L n 0 0] fun _ => (1 : ComplexMatrix2)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun x => ?_, Eventually.of_forall hvg⟩
    have hc : Continuous fun t : ℝ => expI (t • lv x) :=
      contDiff_expI.continuous.comp (continuous_id.smul continuous_const)
    have h := hc.tendsto 0
    simpa only [zero_smul, expI_zero] using h
  have hinv : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement)),
      G (T p) = G p.2 := by
    obtain ⟨W, hW, hU⟩ := hf.locallyGauge
    have hfst : Tendsto (Prod.fst : ℝ × (PositiveUnitEdge L n → ComplexMatrix2.LieElement) → ℝ)
        (𝓝 (0, 0)) (𝓝 0) := continuous_fst.tendsto _
    have hsnd : Tendsto (Prod.snd : ℝ × (PositiveUnitEdge L n → ComplexMatrix2.LieElement) → _)
        (𝓝 (0, 0)) (𝓝 0) := continuous_snd.tendsto _
    filter_upwards [hPsi, (hvt.comp hfst).eventually hW,
      ((tendsto_expField hL2 hn hmem).comp hsnd).eventually hU] with p h1 h2 h3
    have h4 : F n (PeriodicLattice.gaugeTransform (v p.1) (expField p.2)) =
        F n (expField p.2) := h3 (v p.1) (hvg _) h2
    have h5 : expField (T p) = fieldOfPositiveValues (k := 0) (j := 0) (Ψ p) := by
      rw [← h1]
      rfl
    have h6 : Ψ p = fun s => v p.1 s.1.source * expI (p.2 s) * (v p.1 s.1.target)⁻¹ := by
      funext s
      simp only [Ψ, gaugedChart, v, expI_inv]
    change F n (expField (T p)) = F n (expField p.2)
    rw [← h4, gaugeTransform_expField _ (fun x => hunit _), h5, h6]
  have hlineT : Tendsto (fun t : ℝ => (t, (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement)))
      (𝓝 0) (𝓝 ((0 : ℝ), (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement))) :=
    (continuous_id.prodMk continuous_const).tendsto 0
  have hTd : DifferentiableAt ℝ
      (fun t : ℝ => T (t, (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement))) 0 := by
    have h1 : DifferentiableAt ℝ T
        ((0 : ℝ), (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement)) :=
      hT.differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ
        (fun t : ℝ => (t, (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement))) 0 :=
      differentiableAt_id.prodMk (differentiableAt_const _)
    exact DifferentiableAt.comp (g := T)
      (f := fun t : ℝ => (t, (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement))) (0 : ℝ) h1 h2
  have hγ := hTd.hasDerivAt
  have hT00 : T (0, 0) = 0 := hT0.self_of_nhds
  have hAd : ∀ A : ComplexMatrix2, ComplexMatrix2.conjugateBy 1 A = A :=
    fun A => by simp [ComplexMatrix2.conjugateBy]
  have hdl : ∀ s : PositiveUnitEdge L n,
      covDiff (k := 0) (j := 0) (identityField L n) l s.1 = l s.1.target - l s.1.source := by
    intro s
    simp only [covDiff, extendOddly, if_pos s.2, identityField, hAd]
  have hdlmem : ∀ s : PositiveUnitEdge L n,
      covDiff (k := 0) (j := 0) (identityField L n) l s.1 ∈
        ComplexMatrix2.hermitianTraceless := by
    intro s
    rw [hdl]
    exact ComplexMatrix2.hermitianTraceless.sub_mem (hl _) (hl _)
  let Yd : PositiveUnitEdge L n → ComplexMatrix2.LieElement :=
    fun s => (⟨_, hdlmem s⟩ : ComplexMatrix2.hermitianTraceless)
  have hv₀ : deriv (fun t : ℝ => T (t, (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement))) 0 =
      -Yd := by
    funext s
    have hs := (hasDerivAt_pi.1 hγ) s
    have hA' := hasDerivAt_expI hs (congrFun hT00 s)
    have hB : HasDerivAt (fun t : ℝ => t • lv s.1.source) (lv s.1.source) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (lv s.1.source)
    have hB' := hasDerivAt_expI hB (zero_smul ℝ _)
    have hC' := hasDerivAt_expI
      (c := fun t : ℝ => -(t • lv s.1.target)) (c' := -lv s.1.target)
      (by simpa only [id, one_smul] using
        ((hasDerivAt_id (0 : ℝ)).smul_const (lv s.1.target)).fun_neg)
      (by simp)
    have hprod := hB'.mul hC'
    have hev : (fun t : ℝ => expI
        (T (t, (0 : PositiveUnitEdge L n → ComplexMatrix2.LieElement)) s)) =ᶠ[𝓝 0]
        fun t => expI (t • lv s.1.source) * expI (-(t • lv s.1.target)) := by
      filter_upwards [hlineT.eventually hPsi] with t ht
      have h := congrFun ht s
      simpa [Ψ, gaugedChart, expI_zero] using h
    have h := hA'.unique (hprod.congr_of_eventuallyEq hev)
    have e1 : expI (-((0 : ℝ) • lv s.1.target)) = 1 := by simp [expI_zero]
    have e2 : expI ((0 : ℝ) • lv s.1.source) = 1 := by simp [expI_zero]
    simp only [e1, e2, mul_one, one_mul] at h
    have h2 : Complex.I • (deriv (fun t : ℝ => T (t, 0)) 0 s).toMatrix =
        Complex.I • (-(l s.1.target - l s.1.source)) := by
      rw [h]
      change Complex.I • l s.1.source + Complex.I • (-l s.1.target) = _
      rw [← smul_add]
      congr 1
      abel
    have h3 := smul_right_injective ComplexMatrix2 Complex.I_ne_zero h2
    apply Subtype.ext (p := (· ∈ ComplexMatrix2.hermitianTraceless))
    change (deriv (fun t : ℝ => T (t, 0)) 0 s).toMatrix =
      -covDiff (k := 0) (j := 0) (identityField L n) l s.1
    rw [h3, hdl]
  let Y' : PositiveUnitEdge L n → ComplexMatrix2.LieElement :=
    fun s => (⟨B' s.1, hB'.1 s.1 s.2⟩ : ComplexMatrix2.hermitianTraceless)
  have hess := secondFDeriv_eq_zero_of_invariant hG hd hT hT0 hinv hγ Y'
  rw [hv₀] at hess
  have hess' : fderiv ℝ (fderiv ℝ G) 0 Yd Y' = 0 := by
    simpa only [map_neg, neg_apply, neg_eq_zero] using hess
  rw [← iteratedDeriv_lines_eq_secondFDeriv hG Yd Y'] at hess'
  have hfun : ∀ s t : ℝ, F n (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ s • covDiff (k := 0) (j := 0) (identityField L n) l +
        algebraMap ℝ ℂ t • B') (identityField L n)) = G (s • Yd + t • Y') := by
    intro s t
    have hZ : ∀ b, ((s • Yd + t • Y') b).toMatrix =
        (algebraMap ℝ ℂ s • covDiff (k := 0) (j := 0) (identityField L n) l +
          algebraMap ℝ ℂ t • B') b.1 := by
      intro b
      change s • (covDiff (k := 0) (j := 0) (identityField L n) l b.1) + t • B' b.1 = _
      ext i j
      simp
    rw [expTwist_identity_eq hZ]
  simp only [hessianAtIdentity, leftSecondDeriv, mixedDirectionalDeriv, hfun]
  exact hess'
private theorem hermitianPart_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    (2⁻¹ : ℂ) • (X + X.conjTranspose) ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p48895 <;> assumption
private theorem skewPart_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    (2 * Complex.I)⁻¹ • (X - X.conjTranspose) ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p51273 <;> assumption
section Parts
variable {L n : ℕ}
private theorem realComponent_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : realComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p16359 <;> assumption
private theorem imagComponent_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : imagComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p9724 <;> assumption
private theorem realComponent_covDiff (l : Vertex L n 0 0 → ComplexMatrix2) :
    realComponent (covDiff (k := 0) (j := 0) (identityField L n) l) =
      covDiff (k := 0) (j := 0) (identityField L n)
        fun x => (2⁻¹ : ℂ) • (l x + (l x).conjTranspose) := by
  have hAd : ∀ A : ComplexMatrix2, ComplexMatrix2.conjugateBy 1 A = A :=
    fun A => by simp [ComplexMatrix2.conjugateBy]
  funext b
  by_cases h : b.IsPositivelyOriented
  · simp only [realComponent, covDiff, extendOddly, if_pos h, identityField,
      hAd, Matrix.conjTranspose_sub]
    module
  · simp only [realComponent, covDiff, extendOddly, if_neg h, identityField,
      hAd, Matrix.conjTranspose_sub, Matrix.conjTranspose_neg]
    module
private theorem imagComponent_covDiff (l : Vertex L n 0 0 → ComplexMatrix2) :
    imagComponent (covDiff (k := 0) (j := 0) (identityField L n) l) =
      covDiff (k := 0) (j := 0) (identityField L n)
        fun x => (2 * Complex.I)⁻¹ • (l x - (l x).conjTranspose) := by
  have hAd : ∀ A : ComplexMatrix2, ComplexMatrix2.conjugateBy 1 A = A :=
    fun A => by simp [ComplexMatrix2.conjugateBy]
  funext b
  by_cases h : b.IsPositivelyOriented
  · simp only [imagComponent, covDiff, extendOddly, if_pos h,
      identityField, hAd, Matrix.conjTranspose_sub]
    module
  · simp only [imagComponent, covDiff, extendOddly, if_neg h,
      identityField, hAd, Matrix.conjTranspose_sub, Matrix.conjTranspose_neg]
    module
end Parts
theorem hessianKillsGaugeDirections_holds (hC : ExpChartsStatement)
    (hP : OneLoop.PauliMatrixRelations)
    (hD : MemberFirstDerivativeVanishes) : HessianKillsGaugeDirections := by
  intro L n hL hn F hf l hl B' hB'
  have hR := realComponent_mem hB'
  have hS := imagComponent_mem hB'
  have h₁ := fun B hB => hessianAtIdentity_covDiff_eq_zero hC hP hD hL hn F hf
    (fun x => (2⁻¹ : ℂ) • (l x + (l x).conjTranspose)) (fun x => hermitianPart_mem (hl x)) B hB
  have h₂ := fun B hB => hessianAtIdentity_covDiff_eq_zero hC hP hD hL hn F hf
    (fun x => (2 * Complex.I)⁻¹ • (l x - (l x).conjTranspose))
    (fun x => skewPart_mem (hl x)) B hB
  simp only [complexHessian, realComponent_covDiff, imagComponent_covDiff,
    h₁ _ hR, h₁ _ hS, h₂ _ hR, h₂ _ hS]
  simp
end YangMills.Construction.OneLoopLaw.GaugeDirectionHessian
end
