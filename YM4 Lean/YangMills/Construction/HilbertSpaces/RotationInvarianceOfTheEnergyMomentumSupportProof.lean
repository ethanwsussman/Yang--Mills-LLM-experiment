import YangMills.Construction.Continuum.StabiliserOfTheTimeVectorIsometriesAndSymbolsProof
import YangMills.Construction.HilbertSpaces.EnergyMomentumMeasureOfACommutingRepresentation
import YangMills.Construction.HilbertSpaces.RotationInvarianceOfTheEnergyMomentumSupport
import YangMills.Construction.SpectralMeasures.CalculusOfBorelFunctionsOnEuclideanSpace
import YangMills.Construction.SpectralMeasures.RulesForTheSpectralMeasure
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.RotationInvariantSupport
open YangMills.Construction.EuclideanBorel
open YangMills.Construction.FormsOperators (IsSelfAdj IsC0Semigroup
  IsStronglyContUnitaryRep Commutes UnitaryMap ofCLM)
open YangMills.Construction.TimeAxisSymbols (spatialPart timeAxisStabilizer)
open YangMills.Construction.SpectralTheory (UnboundedOp)
section Rotation
theorem rotateMomentum_energy (w : timeAxisStabilizer) (y : Space (1 + 3)) :
    rotateMomentum w y energyCoordIndex = y energyCoordIndex := by
  show Fin.append (fun _ : Fin 1 => y energyCoordIndex) (rotateSpatial w (momentumVec y)).ofLp
    (Fin.castAdd 3 0) = _
  exact Fin.append_left _ _ _
theorem momentumVec_rotateMomentum (w : timeAxisStabilizer) (y : Space (1 + 3)) :
    momentumVec (rotateMomentum w y) = rotateSpatial w (momentumVec y) := by
  refine PiLp.ext fun i => ?_
  show Fin.append (fun _ : Fin 1 => y energyCoordIndex) (rotateSpatial w (momentumVec y)).ofLp
    (Fin.natAdd 1 i) = _
  exact Fin.append_right _ _ _
theorem ext_energy_momentum {y y' : Space (1 + 3)}
    (h : y energyCoordIndex = y' energyCoordIndex)
    (h' : momentumVec y = momentumVec y') : y = y' := by
  refine PiLp.ext fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    exact h
  · exact congrArg (fun p : Space 3 => p j) h'
theorem spatialPart_one (a : Fin 3 → ℝ) : spatialPart 1 a = a := by apply _root_.YangMills.Construction.TimeAxisSymbols.StabilizerAction.spatialPart_one <;> assumption
variable (hIso : YangMills.Construction.TimeAxisSymbols.StabilizerAction.Statement)
include hIso
theorem rotateSpatial_inv_apply_self (w : timeAxisStabilizer) (a : Space 3) :
    rotateSpatial w⁻¹ (rotateSpatial w a) = a := by
  obtain ⟨⟨-, -, -, -, -, hg, -⟩, -⟩ := hIso
  refine PiLp.ext fun i => ?_
  have h := hg w⁻¹ w a.ofLp
  rw [inv_mul_cancel, spatialPart_one] at h
  exact (congrFun h i).symm
theorem rotateSpatial_apply_inv_self (w : timeAxisStabilizer) (a : Space 3) :
    rotateSpatial w (rotateSpatial w⁻¹ a) = a := by
  have h := rotateSpatial_inv_apply_self hIso w⁻¹ a
  rwa [inv_inv] at h
theorem continuous_rotateSpatial (w : timeAxisStabilizer) : Continuous (rotateSpatial w) := by
  obtain ⟨⟨-, -, -, hl, -, -, -⟩, -⟩ := hIso
  obtain ⟨-, S, -, hS⟩ := hl w
  have h : rotateSpatial w = fun a : Space 3 => WithLp.toLp 2 (S.mulVec a.ofLp) := by
    funext a
    simp only [rotateSpatial, hS]
  rw [h]
  exact (PiLp.continuous_toLp 2 _).comp
    (Continuous.matrix_mulVec continuous_const (PiLp.continuous_ofLp 2 _))
theorem continuous_rotateMomentum (w : timeAxisStabilizer) :
    Continuous (rotateMomentum w) := by
  have hr := continuous_rotateSpatial hIso w
  have hm : Continuous momentumVec := by
    unfold momentumVec
    fun_prop
  have hp := hr.comp hm
  unfold rotateMomentum appendCoords
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
    fun_prop
  · simp only [Fin.append_right]
    exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp hp)
theorem rotateMomentum_inv_apply_self (w : timeAxisStabilizer) (y : Space (1 + 3)) :
    rotateMomentum w⁻¹ (rotateMomentum w y) = y := by
  refine ext_energy_momentum ?_ ?_
  · rw [rotateMomentum_energy, rotateMomentum_energy]
  · rw [momentumVec_rotateMomentum, momentumVec_rotateMomentum,
      rotateSpatial_inv_apply_self hIso]
theorem rotateMomentum_apply_inv_self (w : timeAxisStabilizer) (y : Space (1 + 3)) :
    rotateMomentum w (rotateMomentum w⁻¹ y) = y := by
  have h := rotateMomentum_inv_apply_self hIso w⁻¹ y
  rwa [inv_inv] at h
theorem inner_rotateSpatial (w : timeAxisStabilizer) (a p : Space 3) :
    inner ℝ a (rotateSpatial w p) = inner ℝ (rotateSpatial w⁻¹ a) p := by
  obtain ⟨⟨-, -, -, -, -, -, hadj⟩, -⟩ := hIso
  have h := hadj w⁻¹ a.ofLp p.ofLp
  rw [inv_inv] at h
  simp only [PiLp.inner_apply, rotateSpatial, RCLike.inner_apply, conj_trivial]
  simp only [dotProduct] at h
  simpa [mul_comm] using h.symm
theorem energyMomentumChar_comp_rotateMomentum (w : timeAxisStabilizer) (τ : ℝ) (a : Space 3) :
    energyMomentumChar τ a ∘ rotateMomentum w = energyMomentumChar τ (rotateSpatial w⁻¹ a) := by
  funext y
  simp only [Function.comp, energyMomentumChar, rotateMomentum_energy,
    momentumVec_rotateMomentum, inner_rotateSpatial hIso]
end Rotation
section Integrals
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem hasSpectralValue_iff {n : ℕ} {E : BorelSubset n → H →L[ℂ] H} {f : Space n → ℂ}
    (hop : RealizesSpectralIntegral E f (spectralOp E f)) (ψ v : H) :
    HasSpectralValue E f ψ v ↔
      ∃ h : ψ ∈ (spectralOp E f).domain, spectralOp E f ⟨ψ, h⟩ = v := by
  constructor
  · rintro ⟨h, rfl⟩
    have hm : ψ ∈ (spectralOp E f).domain := by
      exact show ψ ∈ ((spectralOp E f).domain : Set H) from hop.1 ▸ h
    obtain ⟨_, hv⟩ := hop.2 ⟨ψ, hm⟩
    exact ⟨hm, hv.symm⟩
  · rintro ⟨hm, rfl⟩
    exact hop.2 ⟨ψ, hm⟩
theorem isPVM_unitaryConj (hCalc : FunctionalCalculus.Statement)
    {n : ℕ} [NeZero n] {E : BorelSubset n → H →L[ℂ] H}
    (hE : IsPVM E) (U : UnitaryMap H H) :
    IsPVM (EuclideanBorel.unitaryConj U E) := by
  have hf : Measurable fun _ : Space n => (0 : ℂ) := measurable_const
  obtain ⟨-, -, -, -, -, -, -, -, hc, -, -⟩ := hCalc n n H E hE _ _ hf hf 0
  exact (hc U).1
theorem hasSpectralValue_unitaryConj (hCalc : FunctionalCalculus.Statement)
    {n : ℕ} [NeZero n] {E : BorelSubset n → H →L[ℂ] H}
    (hE : IsPVM E) {f : Space n → ℂ} (hf : Measurable f)
    (U : UnitaryMap H H) {χ v : H} (h : HasSpectralValue E f χ v) :
    HasSpectralValue (EuclideanBorel.unitaryConj U E) f (U χ) (U v) := by
  obtain ⟨hd, -, -, -, -, -, -, -, hc, -, -⟩ := hCalc n n H E hE f f hf hf 0
  obtain ⟨hd', -⟩ := hCalc n n H _ (hc U).1 f f hf hf 0
  rw [hasSpectralValue_iff hd'.isOp, (hc U).2]
  obtain ⟨hm, rfl⟩ := (hasSpectralValue_iff hd.isOp χ v).1 h
  exact ⟨Submodule.mem_map_of_mem hm, FormsOperators.unitaryConjugate_apply U _ ⟨χ, hm⟩⟩
theorem hasSpectralValue_pushforward (hCalc : FunctionalCalculus.Statement)
    {n n' : ℕ} [NeZero n] [NeZero n'] {E : BorelSubset n → H →L[ℂ] H}
    (hE : IsPVM E) {κ : Space n → Space n'} (hκ : Measurable κ)
    {h : Space n' → ℂ} (hh : Measurable h) {ψ v : H} (hv : HasSpectralValue E (h ∘ κ) ψ v) :
    HasSpectralValue (EuclideanBorel.pushforward E κ hκ) h ψ v := by
  have hc : Measurable (h ∘ κ) := hh.comp hκ
  obtain ⟨hd, -, -, -, -, -, -, hi, -, -, -⟩ := hCalc n n' H E hE _ _ hc hc 0
  obtain ⟨hd', -⟩ := hCalc n' n' H _ (hi κ hκ).1 h h hh hh 0
  rw [hasSpectralValue_iff hd'.isOp, (hi κ hκ).2 h hh]
  exact (hasSpectralValue_iff hd.isOp ψ v).1 hv
omit [CompleteSpace H] in
theorem apply_unitary_of_conj_eq {U : UnitaryMap H H} {S : Set H} {u : S → H}
    (hu : PartialMapEq (conjPartialMap U u) u) (χ : S) :
    ∃ h : U χ ∈ S, u ⟨U χ, h⟩ = U (u χ) := by
  obtain ⟨hS, hv⟩ := hu
  have hm : U χ ∈ U '' S := mem_image_of_mem U χ.2
  refine ⟨hS.subset hm, (hv ⟨U χ, hm⟩).trans ?_⟩
  show U (u ⟨U.symm (U χ), _⟩) = U (u χ)
  congr 2
  exact Subtype.ext (U.symm_apply_apply χ)
omit [CompleteSpace H] in
theorem apply_unitary_of_eq_conj {U : UnitaryMap H H} {S : Set H} {u : S → H}
    (hu : PartialMapEq u (conjPartialMap U u)) (χ : S) :
    ∃ h : U χ ∈ S, u ⟨U χ, h⟩ = U (u χ) := by
  obtain ⟨hS, hv⟩ := hu
  have hm : U χ ∈ U '' S := mem_image_of_mem U χ.2
  have hm' : U χ ∈ S := hS.symm.subset hm
  refine ⟨hm', (hv ⟨U χ, hm'⟩).symm.trans ?_⟩
  show U (u ⟨U.symm (U χ), _⟩) = U (u χ)
  congr 2
  exact Subtype.ext (U.symm_apply_apply χ)
theorem unitaryConjugate_eq_self_of_commute {A : UnboundedOp H} {U : UnitaryMap H H}
    (hD : U '' (A.domain : Set H) = A.domain)
    (hv : ∀ χ : A.domain, ∃ h : U χ ∈ A.domain, A ⟨U χ, h⟩ = U (A χ)) :
    FormsOperators.unitaryConjugate U A = A := by
  have hdom : (FormsOperators.unitaryConjugate U A).domain = A.domain := by
    refine SetLike.coe_injective ?_
    exact hD
  refine LinearPMap.ext hdom ?_
  intro x hx hx'
  obtain ⟨χ, hχ, rfl⟩ := hx
  obtain ⟨h, hval⟩ := hv ⟨χ, hχ⟩
  exact (FormsOperators.unitaryConjugate_apply U A ⟨χ, hχ⟩).trans hval.symm
end Integrals
section Generator
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def negLogOnLine : ℝ → ℂ :=
  fun x => if 0 < x then ((-Real.log x : ℝ) : ℂ) else 0
theorem measurable_negLogOnLine : Measurable negLogOnLine :=
  Measurable.ite measurableSet_Ioi (Complex.measurable_ofReal.comp Real.measurable_log.neg)
    measurable_const
theorem liftFromLine_negLogOnLine :
    liftFromLine negLogOnLine = zeroExtend openPosRay negLogOnPosRay := by
  funext y
  by_cases h : 0 < y 0
  · have hy : y ∈ openPosRay.1 := h
    simp only [liftFromLine, negLogOnLine, zeroExtend, if_pos h, dif_pos hy, negLogOnPosRay]
  · have hy : y ∉ openPosRay.1 := h
    simp only [liftFromLine, negLogOnLine, zeroExtend, if_neg h, dif_neg hy]
theorem isSelfAdj_ofCLM_of_isExpNegMul (hCalc : FunctionalCalculus.Statement)
    (hSpec : SelfAdjoint.SpectralTheorem) {A : UnboundedOp H} (hA : IsSelfAdj A)
    {t : ℝ≥0} {T : H →L[ℂ] H} (hT : IsExpNegMul A t T) :
    IsSelfAdj (ofCLM T) := by
  obtain ⟨-, -, -, -, -, -, -, -, hsp, -, -⟩ := hSpec H A hA
  have hf : Measurable (liftFromLine fun x => Complex.exp (-((t : ℝ) : ℂ) * (x : ℂ))) := by
    refine Continuous.measurable ?_
    unfold liftFromLine
    fun_prop
  obtain ⟨hd, -, hadj, -⟩ := hCalc 1 1 H _ hsp.1 _ _ hf hf 0
  have hreal := hadj.2 fun y => by
    simp only [liftFromLine]
    rw [show -(((t : ℝ)) : ℂ) * ((y 0 : ℝ) : ℂ) = ((-(t : ℝ) * y 0 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.exp_ofReal_im _
  have hop := hd.isOp
  have heq : spectralOp (spectralResolution A)
      (liftFromLine fun x => Complex.exp (-((t : ℝ) : ℂ) * (x : ℂ))) = ofCLM T := by
    have hdom : (spectralOp (spectralResolution A)
        (liftFromLine fun x => Complex.exp (-((t : ℝ) : ℂ) * (x : ℂ)))).domain =
        (ofCLM T).domain := by
      refine SetLike.coe_injective ?_
      rw [hop.1, hT.1]
      rfl
    refine LinearPMap.ext hdom ?_
    intro x hx hx'
    obtain ⟨h, hv⟩ := hop.2 ⟨x, hx⟩
    exact hv.symm.trans (hT.2 ⟨x, h⟩)
  rwa [heq] at hreal
theorem unitaryConjugate_eq_self_of_isNegLogOf (hRules : SpectralRules.AllRules)
    {A : UnboundedOp H} {T : H →L[ℂ] H} (hT : IsSelfAdj (ofCLM T))
    (hlog : IsNegLogOf A T) {U : UnitaryMap H H}
    (hU : toCLM U * T = T * toCLM U) :
    FormsOperators.unitaryConjugate U A = A := by
  obtain ⟨-, -, -, hconj, -⟩ := hRules H
  obtain ⟨-, -, -, hlast⟩ := hconj (ofCLM T) hT U
  obtain ⟨-, hmap⟩ := hlast T rfl hU
  have hu := hmap negLogOnLine measurable_negLogOnLine
  have hI : IsSpectralIntegralOp A (spectralResolution (ofCLM T))
      (liftFromLine negLogOnLine) := by
    rw [liftFromLine_negLogOnLine]
    exact hlog.2
  obtain ⟨hd', hv⟩ := hI
  refine unitaryConjugate_eq_self_of_commute ?_ fun χ => ?_
  · rw [hd']
    exact hu.1
  · have hχ : (χ : H) ∈ sqIntegrableDomain (spectralResolution (ofCLM T))
        (liftFromLine negLogOnLine) := hd' ▸ χ.2
    obtain ⟨h, hval⟩ := apply_unitary_of_conj_eq hu ⟨χ, hχ⟩
    have hm : U χ ∈ A.domain := by
      have : U χ ∈ (A.domain : Set H) := hd'.symm ▸ h
      exact this
    refine ⟨hm, (hv ⟨U χ, hm⟩).trans (Eq.trans ?_ ((congrArg U (hv χ)).symm))⟩
    exact hval
end Generator
section Support
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem measurable_energyMomentumChar (τ : ℝ) (a : Space 3) :
    Measurable (energyMomentumChar τ a) := by
  have hm : Continuous momentumVec := by
    unfold momentumVec
    fun_prop
  refine Continuous.measurable ?_
  unfold energyMomentumChar
  fun_prop
theorem isJointSpectralMeasure_pushforward (hCalc : FunctionalCalculus.Statement)
    (hRules : SpectralRules.AllRules)
    (hIso : YangMills.Construction.TimeAxisSymbols.StabilizerAction.Statement)
    {A : UnboundedOp H} (hA : IsSelfAdj A) {W : Space 3 → UnitaryMap H H}
    {U : UnitaryMap H H} {w : timeAxisStabilizer}
    (hcA : FormsOperators.unitaryConjugate U A = A)
    (hUW : ∀ a, toCLM U * toCLM (W a) = toCLM (W (rotateSpatial w a)) * toCLM U)
    {E : BorelSubset (1 + 3) → H →L[ℂ] H} (hE : IsJointSpectralMeasure A W E)
    (hκ : Measurable (rotateMomentum w)) :
    IsJointSpectralMeasure A W
      (EuclideanBorel.pushforward (EuclideanBorel.unitaryConj U E) (rotateMomentum w) hκ) := by
  obtain ⟨hP, hI⟩ := hE
  have hPc := isPVM_unitaryConj hCalc hP U
  have hz : Measurable fun _ : Space (1 + 3) => (0 : ℂ) := measurable_const
  obtain ⟨-, -, -, -, -, -, -, himg, -, -, -⟩ := hCalc (1 + 3) (1 + 3) H _ hPc _ _ hz hz 0
  refine ⟨(himg _ hκ).1, fun τ a => ?_⟩
  obtain ⟨-, -, -, hconj, -⟩ := hRules H
  obtain ⟨-, -, hthird, -⟩ := hconj A hA U
  have hg : Measurable fun x : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ)) := by
    refine Continuous.measurable ?_
    fun_prop
  have hu := hthird _ hg
  rw [hcA] at hu
  have hval : ∀ ψ : H, ∃ v : H,
      HasSpectralValue (EuclideanBorel.pushforward (EuclideanBorel.unitaryConj U E)
        (rotateMomentum w) hκ) (energyMomentumChar τ a) ψ v ∧
      HasSpectralValue (spectralResolution A)
        (liftFromLine fun x => Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ))) (W a ψ) v := by
    intro ψ
    obtain ⟨hd, hv⟩ := hI τ (rotateSpatial w⁻¹ a)
    have hχ : U.symm ψ ∈ sqIntegrableDomain E (energyMomentumChar τ (rotateSpatial w⁻¹ a)) := by
      rw [hd]
      exact mem_univ _
    obtain ⟨h₁, h₂⟩ := hv ⟨U.symm ψ, hχ⟩
    have hHV : HasSpectralValue E (energyMomentumChar τ (rotateSpatial w⁻¹ a)) (U.symm ψ)
        (expIMul A τ ⟨W (rotateSpatial w⁻¹ a) (U.symm ψ), h₁⟩) := ⟨hχ, h₂⟩
    have hc := hasSpectralValue_unitaryConj hCalc hP (measurable_energyMomentumChar τ _) U hHV
    rw [U.apply_symm_apply, ← energyMomentumChar_comp_rotateMomentum hIso] at hc
    refine ⟨_, hasSpectralValue_pushforward hCalc hPc hκ (measurable_energyMomentumChar τ a) hc, ?_⟩
    obtain ⟨h₃, h₄⟩ := apply_unitary_of_eq_conj hu ⟨_, h₁⟩
    have hW : U (W (rotateSpatial w⁻¹ a) (U.symm ψ)) = W a ψ := by
      have h := DFunLike.congr_fun (hUW (rotateSpatial w⁻¹ a)) (U.symm ψ)
      rw [rotateSpatial_apply_inv_self hIso] at h
      refine h.trans ?_
      show W a (U (U.symm ψ)) = W a ψ
      rw [U.apply_symm_apply]
    rw [← hW]
    exact ⟨h₃, h₄⟩
  refine ⟨eq_univ_of_forall fun ψ => ?_, fun ψ => ?_⟩
  · obtain ⟨v, ⟨h, -⟩, -⟩ := hval ψ
    exact h
  · obtain ⟨v, ⟨h, hv⟩, ⟨h', hv'⟩⟩ := hval ψ
    exact ⟨h', hv.trans hv'.symm⟩
omit [CompleteSpace H] in
theorem isNull_preimage_iff {E : BorelSubset (1 + 3) → H →L[ℂ] H} {U : UnitaryMap H H}
    {κ : Space (1 + 3) → Space (1 + 3)} (hκ : Measurable κ)
    (hEq : EuclideanBorel.pushforward (EuclideanBorel.unitaryConj U E) κ hκ = E)
    (Δ : BorelSubset (1 + 3)) :
    IsNull E ⟨κ ⁻¹' Δ.1, hκ Δ.2⟩ ↔ IsNull E Δ := by
  have h : E Δ = (U.toContinuousLinearEquiv : H →L[ℂ] H) * E ⟨κ ⁻¹' Δ.1, hκ Δ.2⟩ *
      (U.symm.toContinuousLinearEquiv : H →L[ℂ] H) := (congrFun hEq Δ).symm
  constructor
  · intro h₀
    have h₀' : E ⟨κ ⁻¹' Δ.1, hκ Δ.2⟩ = 0 := h₀
    show E Δ = 0
    rw [h, h₀']
    simp
  · intro h₀
    have h₀' : E Δ = 0 := h₀
    show E ⟨κ ⁻¹' Δ.1, hκ Δ.2⟩ = 0
    refine ContinuousLinearMap.ext fun ψ => ?_
    have hψ := DFunLike.congr_fun h (U ψ)
    rw [h₀'] at hψ
    have hψ' : (0 : H) = U (E ⟨κ ⁻¹' Δ.1, hκ Δ.2⟩ (U.symm (U ψ))) := hψ
    rw [U.symm_apply_apply] at hψ'
    exact U.injective (by rw [← hψ']; simp)
omit [CompleteSpace H] in
theorem image_pvmSupport_eq {E : BorelSubset (1 + 3) → H →L[ℂ] H} {U : UnitaryMap H H}
    {κ κ' : Space (1 + 3) → Space (1 + 3)} (hκ : Continuous κ) (hκ' : Continuous κ')
    (hl : ∀ y, κ' (κ y) = y) (hr : ∀ y, κ (κ' y) = y)
    (hEq : EuclideanBorel.pushforward (EuclideanBorel.unitaryConj U E) κ hκ.measurable = E)
    (hL : ∃ L, IsMaximalOpenNull E L) :
    κ '' pvmSupport E = pvmSupport E := by
  have hspec : IsMaximalOpenNull E (maxOpenNull E) := Classical.epsilon_spec hL
  obtain ⟨⟨hLo, hLn⟩, hmax⟩ := hspec
  have h₁ : κ ⁻¹' maxOpenNull E ⊆ maxOpenNull E :=
    hmax _ ⟨hLo.preimage hκ,
      (isNull_preimage_iff hκ.measurable hEq ⟨_, hLo.measurableSet⟩).2 hLn⟩
  have h₂ : κ' ⁻¹' maxOpenNull E ⊆ maxOpenNull E := by
    refine hmax _ ⟨hLo.preimage hκ', ?_⟩
    refine (isNull_preimage_iff hκ.measurable hEq ⟨_, (hLo.preimage hκ').measurableSet⟩).1 ?_
    have hs : κ ⁻¹' (κ' ⁻¹' maxOpenNull E) = maxOpenNull E := by
      ext y
      simp only [mem_preimage, hl]
    have he : (⟨κ ⁻¹' (κ' ⁻¹' maxOpenNull E), hκ.measurable
        (hLo.preimage hκ').measurableSet⟩ : BorelSubset (1 + 3)) =
        ⟨maxOpenNull E, hLo.measurableSet⟩ := Subtype.ext hs
    show IsNull E ⟨κ ⁻¹' (κ' ⁻¹' maxOpenNull E), _⟩
    rw [he]
    exact hLn
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ hy
    exact hx (h₁ hy)
  · intro hy
    exact ⟨κ' y, fun h => hy (h₂ h), hr y⟩
end Support
theorem holds (hEM : CommutingJointSpectrum.Statement)
    (hRules : SpectralRules.AllRules)
    (hCalc : FunctionalCalculus.Statement) (hSpec : SelfAdjoint.SpectralTheorem)
    (hIso : YangMills.Construction.TimeAxisSymbols.StabilizerAction.Statement) :
    Statement := by
  intro H _ _ _ B A W U w hB hG hlog hW hWB hUB hUW
  have hT := isSelfAdj_ofCLM_of_isExpNegMul hCalc hSpec hG.1 (hG.2.2 1)
  have hcA := unitaryConjugate_eq_self_of_isNegLogOf hRules hT hlog (hUB 1)
  refine ⟨hcA, ?_⟩
  obtain ⟨hU, hprop⟩ := hEM H B A W hB hG hlog hW hWB
  have hE := hprop.1
  have hκ := continuous_rotateMomentum hIso w
  have hκ' := continuous_rotateMomentum hIso w⁻¹
  have hImg := isJointSpectralMeasure_pushforward hCalc hRules hIso hG.1 hcA hUW hE hκ.measurable
  have hEq := hU.unique hImg hE
  have hz : Measurable fun _ : Space (1 + 3) => (0 : ℂ) := measurable_const
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hother⟩ :=
    hCalc (1 + 3) (1 + 3) H _ hE.1 _ _ hz hz 0
  exact image_pvmSupport_eq hκ hκ' (rotateMomentum_inv_apply_self hIso w)
    (rotateMomentum_apply_inv_self hIso w) hEq hother.1
end YangMills.Construction.PositiveFormReconstruction.RotationInvariantSupport
