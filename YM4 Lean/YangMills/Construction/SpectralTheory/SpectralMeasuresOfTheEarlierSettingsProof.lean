import YangMills.Construction.SpectralTheory.EverySelfAdjointOperatorIsResolved
import YangMills.Construction.SpectralTheory.MeasuresOnABorelSetOfTheEarlierSettings
import YangMills.Construction.SpectralTheory.SpectralMeasuresOfTheEarlierSettings
import YangMills.Construction.SpectralTheory.UnboundedFunctionalCalculusStatement
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal
noncomputable section
namespace YangMills.Construction.SettingsComparison.SpectralAgreement
open YangMills.Construction.BorelSpectral
open YangMills.Construction.HilbertSpaceBasics (UnboundedOp ofBounded)
open YangMills.Construction.SpectralTheorem
  (IsSpectralIntegralOf IsSpectralMeasureFor RealLineSet spectralIntegralOp coordVar spectralMeasure)
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem eq_of_isSpectralIntegralOf {n : ℕ} {S : Set (Fin n → ℝ)} {P : SpectralMeasure S H}
    {f : S → ℂ} {T T' : UnboundedOp H} (hT : IsSpectralIntegralOf T P f)
    (hT' : IsSpectralIntegralOf T' P f) : T = T' := by
  have hdom : T.domain = T'.domain := by
    ext v
    rw [hT.1, hT'.1]
  refine LinearPMap.ext hdom fun x hx hy => ?_
  rw [hT.2, hT'.2]
theorem isSpectralIntegralOf_spectralIntegralOp
    (hcalc : BorelCalculus.UnboundedFunctionalCalculusHolds)
    {n : ℕ} {S : Set (Fin n → ℝ)} (P : SpectralMeasure S H) {f : S → ℂ}
    (hf : Measurable f) : IsSpectralIntegralOf (spectralIntegralOp P f) P f := by
  obtain ⟨T, -, hdom, hval⟩ := (hcalc H n S P).exists_op f hf
  have hex : ∃ T : UnboundedOp H, IsSpectralIntegralOf T P f :=
    ⟨T, fun v => Set.ext_iff.mp hdom v, hval⟩
  unfold spectralIntegralOp
  exact Classical.epsilon_spec hex
theorem spectralIntegralOp_eq_ofBounded
    (hcalc : BorelCalculus.UnboundedFunctionalCalculusHolds)
    {n : ℕ} {S : Set (Fin n → ℝ)} (P : SpectralMeasure S H) {f : S → ℂ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ s, ‖f s‖ ≤ M) :
    spectralIntegralOp P f = ofBounded (P.integralOp f) := by
  refine eq_of_isSpectralIntegralOf (isSpectralIntegralOf_spectralIntegralOp hcalc P hf)
    ⟨fun v => ?_, fun v => ?_⟩
  · rw [P.integralDom_eq_univ hM]
    exact ⟨fun _ => mem_univ _, fun _ => Submodule.mem_top⟩
  · rw [P.integralApply_eq_integralOp hM]
    rfl
theorem commute_apply {n : ℕ} {S : Set (Fin n → ℝ)} (P : SpectralMeasure S H)
    (A B : BorelSubsets S) : Commute (P A) (P B) := by
  have hAB := P.map_inter A B
  have hBA := P.map_inter B A
  have hswap : (⟨A.1 ∩ B.1, A.2.inter B.2⟩ : BorelSubsets S) = ⟨B.1 ∩ A.1, B.2.inter A.2⟩ :=
    Subtype.ext (inter_comm _ _)
  rw [hswap] at hAB
  exact hAB.symm.trans hBA
theorem measurable_firstCoord : Measurable fun p : RealLineSet => p.1 0 :=
  (measurable_pi_apply 0).comp measurable_subtype_coe
theorem exists_realLineSet_eq (A : BorelSubsets RealLineSet) :
    ∃ D : BorelSubsets ℝ, realLineSet D = A := by
  have hemb : Measurable fun x : ℝ => (⟨fun _ => x, mem_univ _⟩ : RealLineSet) :=
    Measurable.subtype_mk (measurable_pi_iff.mpr fun _ => measurable_id)
  refine ⟨⟨_, hemb A.2⟩, Subtype.ext (Set.ext fun p => ?_)⟩
  have hp : (⟨fun _ => p.1 0, mem_univ _⟩ : RealLineSet) = p :=
    Subtype.ext (funext fun i => by rw [Subsingleton.elim i 0])
  change (⟨fun _ => p.1 0, mem_univ _⟩ : RealLineSet) ∈ A.1 ↔ p ∈ A.1
  rw [hp]
theorem spectralMeasuresAgreeForAllSpaces_holds
    (hdiag : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hborel : BorelSetMeasuresAgreeForAllSpaces)
    (hcalc : BorelCalculus.UnboundedFunctionalCalculusHolds) :
    SpectralMeasuresAgreeForAllSpaces := by
  intro H _ _ _
  obtain ⟨-, -, -, hres, -, hmean⟩ := hdiag.1 H
  have hB := hborel H 1 RealLineSet le_rfl MeasurableSet.univ univ_nonempty
  refine ⟨hres, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT P
    have hm : Measurable (coordVar : RealLineSet → ℂ) :=
      Complex.measurable_ofReal.comp measurable_firstCoord
    obtain ⟨huniq, hspec⟩ := hmean T hT
    exact (hB.viaCoeffs_iff P coordVar hm T).trans
      ⟨fun h => huniq.unique h hspec, fun h => h ▸ hspec⟩
  · intro T hT u hu T'
    have hg : Measurable fun p : RealLineSet => u (p.1 0) := hu.comp measurable_firstCoord
    refine (hB.viaCoeffs_iff _ _ hg T').trans
      ⟨fun h => eq_of_isSpectralIntegralOf h (isSpectralIntegralOf_spectralIntegralOp hcalc _ hg),
        fun h => ?_⟩
    subst h
    exact isSpectralIntegralOf_spectralIntegralOp hcalc _ hg
  · intro T hT C u hu hC
    rfl
  · intro T hT s
    have hm : Measurable fun p : RealLineSet => Complex.exp (Complex.I * s * (p.1 0 : ℝ)) :=
      Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp measurable_firstCoord))
    refine spectralIntegralOp_eq_ofBounded hcalc _ hm (M := 1) fun p => ?_
    have hre : Complex.I * s * (p.1 0 : ℝ) = ((s * p.1 0 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    change ‖Complex.exp (Complex.I * s * (p.1 0 : ℝ))‖ ≤ 1
    rw [hre, Complex.norm_exp_ofReal_mul_I]
  · intro T hT
    rfl
  · intro T hT hn t
    have hfun : (fun x : ℝ => Complex.exp (-((t : ℝ) : ℂ) * (x : ℂ))) =
        fun x : ℝ => Complex.exp ((-(t : ℝ) * x : ℝ) : ℂ) := by
      funext x
      push_cast
      rfl
    unfold ResolvedOps.expComplex SelfAdjointFunctions.expNeg
    rw [hfun]
  · intro T T' hT hT'
    constructor
    · intro h
      refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · exact fun A B => commute_apply _ _ _
      · exact fun A B => h _ _
      · exact fun A B => (h _ _).symm
      · exact fun A B => commute_apply _ _ _
    · intro h A₁ A₂
      obtain ⟨D₁, rfl⟩ := exists_realLineSet_eq A₁
      obtain ⟨D₂, rfl⟩ := exists_realLineSet_eq A₂
      exact h 0 1 D₁ D₂
end YangMills.Construction.SettingsComparison.SpectralAgreement
