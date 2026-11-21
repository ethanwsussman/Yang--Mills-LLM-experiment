import YangMills.Construction.HilbertSpaces.EnergyMomentumMeasureOfACommutingRepresentation
import YangMills.Construction.SpectralMeasures.CalculusOfBorelFunctionsOnEuclideanSpace
import YangMills.Construction.SpectralMeasures.RulesForTheSpectralMeasure
import YangMills.Construction.SpectralMeasures.StronglyContinuousUnitaryRepresentationsOfRealSpace
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
open YangMills.Construction.EuclideanBorel (Space BorelSubset SpectralIntegralIs IsSpectralIntegralOp
  IsPVM IsSpectralMeasureOf StronglyCommute IsNull IsOpenNull
  IsMaximalOpenNull RealizesSpectralIntegral EssBounded IsSpectralResolution PartialMapEq
  appendCoords expChar expMomentumOp zeroExtend borelCalculus
  spectralIntegral jointSpectrum spectralParamCoord maxOpenNull
  liftFromLine liftToLine measurable_liftToLine momentumCoord momentumExpChar
  momentumVec negLogOnPosRay iioSet toLine openPosRay
  pvmSupport spectralMeasureOf diagonalForm spectralResolution
  sqIntegrableDomain)
open YangMills.Construction.FormsOperators (IsSelfAdj IsC0Semigroup
  IsStronglyContUnitaryRep Commutes UnitaryMap ofCLM)
open YangMills.Construction.SpectralTheory (UnboundedOp)
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.CommutingJointSpectrum
theorem toLine_apply_zero (v : Space 1) : toLine (v 0) = v := by
  ext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rfl
theorem toLine_zero : toLine 0 = 0 := rfl
theorem inner_toLine (τ : ℝ) (y : Space 1) : inner ℝ (toLine τ) y = τ * y 0 := by
  simp [PiLp.inner_apply, toLine, mul_comm]
theorem inner_eq_energy_add_momentum (y₀ y : Space (1 + 3)) :
    inner ℝ y₀ y = y₀ energyCoordIndex * y energyCoordIndex +
      inner ℝ (momentumVec y₀) (momentumVec y) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_add, momentumVec, energyCoordIndex]
  simp [mul_comm]
def energyMomentumPoint (τ : ℝ) (a : Space 3) : Space (1 + 3) :=
  appendCoords 1 3 (toLine τ, a)
theorem energyMomentumPoint_energy (τ : ℝ) (a : Space 3) :
    energyMomentumPoint τ a energyCoordIndex = τ := by
  change Fin.append (toLine τ).ofLp a.ofLp (Fin.castAdd 3 0) = τ
  rw [Fin.append_left]
  rfl
theorem momentumVec_energyMomentumPoint (τ : ℝ) (a : Space 3) :
    momentumVec (energyMomentumPoint τ a) = a := by
  ext i
  simp [energyMomentumPoint, appendCoords, momentumVec]
theorem expChar_eq_energyMomentumChar (y₀ : Space (1 + 3)) :
    expChar y₀ = energyMomentumChar (y₀ energyCoordIndex) (momentumVec y₀) := by
  funext y
  simp only [expChar, energyMomentumChar, inner_eq_energy_add_momentum]
theorem liftFromLine_exp_eq_expChar (τ : ℝ) :
    (liftFromLine fun x : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ))) =
      expChar (toLine τ) := by
  funext y
  simp only [liftFromLine, expChar, inner_toLine]
  push_cast
  ring_nf
theorem measurable_expChar {n : ℕ} (v : Space n) :
    Measurable (expChar v) := by
  unfold expChar
  fun_prop
theorem norm_expChar {n : ℕ} (v y : Space n) : ‖expChar v y‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _
section Integrals
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem spectralIntegralOp_unique {n : ℕ} {A A' : UnboundedOp H} {E : BorelSubset n → H →L[ℂ] H}
    {f : Space n → ℂ} (h : IsSpectralIntegralOp A E f) (h' : IsSpectralIntegralOp A' E f) :
    A = A' := by
  obtain ⟨h₁, v₁⟩ := h
  obtain ⟨h₂, v₂⟩ := h'
  refine (YangMills.Construction.FormsOperators.unboundedOp_eq_iff A A').2
    ⟨SetLike.coe_injective (h₁.trans h₂.symm), fun χ => ?_⟩
  exact (v₂ _).trans (v₁ χ).symm
theorem isSpectralIntegralOp_ofCLM {n : ℕ} {E : BorelSubset n → H →L[ℂ] H} {f : Space n → ℂ}
    {T : H →L[ℂ] H} (h : SpectralIntegralIs E f T) : IsSpectralIntegralOp (ofCLM T) E f := by
  refine ⟨?_, fun χ => ?_⟩
  · rw [h.1]
    rfl
  · change T (χ : H) = _
    exact (h.2 ⟨χ, by rw [h.1]; exact mem_univ _⟩).symm
omit [CompleteSpace H] in
theorem isNull_empty {n : ℕ} {E : BorelSubset n → H →L[ℂ] H} (hE : IsPVM E) :
    IsNull E ⟨∅, MeasurableSet.empty⟩ := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  obtain ⟨μ, hμ⟩ := hE.isPositiveMeasure ψ
  have h₀ := (hμ ⟨∅, MeasurableSet.empty⟩).2
  have h₁ : ⟪ψ, E ⟨∅, MeasurableSet.empty⟩ ψ⟫_ℂ = 0 := by
    simpa [diagonalForm] using h₀
  obtain ⟨hsq, hsym⟩ := hE.isOrthoProjection ⟨∅, MeasurableSet.empty⟩
  have h₂ : ⟪E ⟨∅, MeasurableSet.empty⟩ ψ, E ⟨∅, MeasurableSet.empty⟩ ψ⟫_ℂ = 0 := by
    rw [← hsym ψ]
    change ⟪ψ, (E ⟨∅, MeasurableSet.empty⟩ * E ⟨∅, MeasurableSet.empty⟩) ψ⟫_ℂ = 0
    rw [hsq, h₁]
  simpa using inner_self_eq_zero.mp h₂
omit [CompleteSpace H] in
theorem essBounded_of_norm_eq_one {n : ℕ} {E : BorelSubset n → H →L[ℂ] H}
    (hE : IsPVM E) {f : Space n → ℂ} (hf : ∀ y, ‖f y‖ = 1) :
    EssBounded E f :=
  ⟨1, ⟨∅, MeasurableSet.empty⟩, isNull_empty hE, fun y _ => (hf y).le⟩
omit [CompleteSpace H] in
theorem spectralIntegralIs_of_partialMapEq {n m : ℕ} {E₁ : BorelSubset n → H →L[ℂ] H}
    {E₂ : BorelSubset m → H →L[ℂ] H} {f₁ : Space n → ℂ} {f₂ : Space m → ℂ} {T : H → H}
    (h : PartialMapEq (spectralIntegral E₁ f₁) (spectralIntegral E₂ f₂))
    (hT : SpectralIntegralIs E₂ f₂ T) : SpectralIntegralIs E₁ f₁ T := by
  obtain ⟨hd, hv⟩ := h
  exact ⟨hd.trans hT.1, fun ψ => (hv ψ).symm.trans (hT.2 _)⟩
omit [CompleteSpace H] in
theorem spectralIntegralIs_of_partialMapEq' {n m : ℕ} {E₁ : BorelSubset n → H →L[ℂ] H}
    {E₂ : BorelSubset m → H →L[ℂ] H} {f₁ : Space n → ℂ} {f₂ : Space m → ℂ} {T : H → H}
    (h : PartialMapEq (spectralIntegral E₁ f₁) (spectralIntegral E₂ f₂))
    (hT : SpectralIntegralIs E₁ f₁ T) : SpectralIntegralIs E₂ f₂ T := by
  obtain ⟨hd, hv⟩ := h
  exact ⟨hd.symm.trans hT.1, fun ψ => (hv ⟨ψ, by rw [hd]; exact ψ.2⟩).trans (hT.2 _)⟩
theorem spectralIntegralIs_of_isSpectralIntegralOp {n m : ℕ} {E : BorelSubset n → H →L[ℂ] H}
    {E' : BorelSubset m → H →L[ℂ] H} {f : Space n → ℂ} {f' : Space m → ℂ} {P : UnboundedOp H}
    {T : H → H} (h : RealizesSpectralIntegral E f P) (h' : RealizesSpectralIntegral E' f' P)
    (hT : SpectralIntegralIs E f T) : SpectralIntegralIs E' f' T := by
  refine ⟨h'.1.symm.trans (h.1.trans hT.1), fun ψ => ?_⟩
  have hψ : (ψ : H) ∈ P.domain := by
    change (ψ : H) ∈ (P.domain : Set H)
    rw [h'.1]
    exact ψ.2
  obtain ⟨_, ha⟩ := h'.2 ⟨ψ, hψ⟩
  obtain ⟨_, hb⟩ := h.2 ⟨ψ, hψ⟩
  exact ha.trans (hb.symm.trans (hT.2 _))
end Integrals
section Commutation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def negLogPosPart (y : Space 1) : ℝ := if 0 < y 0 then -Real.log (y 0) else 0
theorem measurable_negLogPosPart : Measurable negLogPosPart := by
  unfold negLogPosPart
  refine Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) ?_ measurable_const
  exact (Real.measurable_log.comp (by fun_prop)).neg
theorem zeroExtend_negLogOnPosRay : zeroExtend openPosRay negLogOnPosRay =
    fun y => ((negLogPosPart y : ℝ) : ℂ) := by
  funext y
  by_cases h : 0 < y 0
  · have hm : y ∈ openPosRay.1 := h
    simp [zeroExtend, negLogOnPosRay, negLogPosPart, hm, h]
  · have hm : y ∉ openPosRay.1 := h
    simp [zeroExtend, negLogPosPart, hm, h]
theorem commutes_spectralResolution (hRules : YangMills.Construction.EuclideanBorel.SpectralRules.AllRules)
    (hSpec : YangMills.Construction.EuclideanBorel.SelfAdjoint.SpectralTheorem) {B : ℝ≥0 → H →L[ℂ] H}
    {A : UnboundedOp H} {T : H →L[ℂ] H} (hgen : IsSemigroupGenerator B A) (hlog : IsNegLogOf A (B 1))
    (hc : T * B 1 = B 1 * T) (Δ : BorelSubset 1) : Commutes T (spectralResolution A Δ) := by
  obtain ⟨hsa, -, hexp⟩ := hgen
  obtain ⟨-, -, -, -, -, -, -, -, hA, -, -⟩ := hSpec H A hsa
  have hfm : Measurable fun y : Space 1 => Real.exp (-(y 0)) := by fun_prop
  obtain ⟨A₁, hA₁, hsa₁, -, -⟩ := (hRules H).2.1 1 le_rfl _ hA.1 _ hfm
  have hfun : (liftFromLine fun x : ℝ => Complex.exp (-(((1 : ℝ≥0) : ℝ) : ℂ) * (x : ℂ))) =
      fun y : Space 1 => ((Real.exp (-(y 0)) : ℝ) : ℂ) := by
    funext y
    simp [liftFromLine]
  have hB₁ : SpectralIntegralIs (spectralResolution A)
      (fun y : Space 1 => ((Real.exp (-(y 0)) : ℝ) : ℂ)) (B 1) := by
    rw [← hfun]
    exact ⟨(hexp 1).1, (hexp 1).2⟩
  have hbd : IsSelfAdj (ofCLM (B 1)) := by
    rw [← spectralIntegralOp_unique hA₁ (isSpectralIntegralOp_ofCLM hB₁)]
    exact hsa₁
  obtain ⟨-, -, -, -, -, -, -, -, hE₁, -, hcomm₁⟩ := hSpec H _ hbd
  obtain ⟨A₂, hA₂, -, himg, -⟩ :=
    (hRules H).2.1 1 le_rfl _ hE₁.1 _ measurable_negLogPosPart
  have hl := hlog.2
  rw [zeroExtend_negLogOnPosRay] at hl
  have hAeq : A₂ = A := spectralIntegralOp_unique hA₂ hl
  rw [hAeq] at himg
  rw [himg]
  exact hcomm₁ (B 1) rfl T hc _
theorem exists_timeTranslation
    (hUnit : YangMills.Construction.EuclideanBorel.UnitaryRep.SpectralCorrespondence)
    (hCalc : YangMills.Construction.EuclideanBorel.FunctionalCalculus.Statement)
    (hSpec : YangMills.Construction.EuclideanBorel.SelfAdjoint.SpectralTheorem)
    {A : UnboundedOp H} (hsa : IsSelfAdj A) {W : Space 3 → UnitaryMap H H}
    (hW : ∀ a Δ, Commutes (toCLM (W a)) (spectralResolution A Δ)) :
    ∃ V₁ : Space 1 → UnitaryMap H H, IsStronglyContUnitaryRep V₁ ∧
      (∀ τ : ℝ, SpectralIntegralIs (spectralResolution A)
        (liftFromLine fun x : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ)))
        (V₁ (toLine τ))) ∧
      IsSpectralMeasureOf V₁ (spectralResolution A) ∧
      ∀ v a, V₁ v * W a = W a * V₁ v := by
  obtain ⟨-, -, -, -, -, -, -, -, hA, -, -⟩ := hSpec H A hsa
  obtain ⟨V₁, hV₁, hv⟩ := (hUnit H 1 le_rfl).1 _ hA.1
  refine ⟨V₁, hV₁, fun τ => ?_, ⟨hA.1, hv⟩, fun v a => ?_⟩
  · rw [liftFromLine_exp_eq_expChar]
    exact hv _
  · have hf := measurable_expChar v
    obtain ⟨-, -, -, -, -, -, -, -, -, hcom, -⟩ :=
      hCalc 1 1 H (spectralResolution A) hA.1 _ _ hf hf 0
    obtain ⟨B', hB', hcomm⟩ := hcom (toCLM (W a)) (hW a)
      (essBounded_of_norm_eq_one hA.1 (norm_expChar v))
    have hval : ∀ ψ, B' ψ = V₁ v ψ := fun ψ => by
      have h₁ : ψ ∈ sqIntegrableDomain (spectralResolution A) (expChar v) := by
        rw [(hv v).1]
        exact mem_univ _
      exact (hB'.2 ⟨ψ, h₁⟩).symm.trans ((hv v).2 ⟨ψ, h₁⟩)
    refine LinearIsometryEquiv.ext fun ψ => ?_
    change V₁ v (W a ψ) = W a (V₁ v ψ)
    have h₂ := congrArg (fun S : H →L[ℂ] H => S ψ) hcomm
    change W a (B' ψ) = B' (W a ψ) at h₂
    rw [hval, hval] at h₂
    exact h₂.symm
end Commutation
section Joint
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def energyMomentumRep (V₁ : Space 1 → UnitaryMap H H)
    (W : Space 3 → UnitaryMap H H) : Space (1 + 3) → UnitaryMap H H :=
  fun y => V₁ (toLine (y energyCoordIndex)) * W (momentumVec y)
omit [CompleteSpace H] in
theorem isStronglyContUnitaryRep_energyMomentumRep {V₁ : Space 1 → UnitaryMap H H}
    {W : Space 3 → UnitaryMap H H} (hV₁ : IsStronglyContUnitaryRep V₁)
    (hW : IsStronglyContUnitaryRep W) (hc : ∀ v a, V₁ v * W a = W a * V₁ v) :
    IsStronglyContUnitaryRep (energyMomentumRep V₁ W) := by
  refine ⟨?_, fun y y' => ?_, fun ψ => ?_⟩
  · have h₁ : toLine ((0 : Space (1 + 3)) energyCoordIndex) = 0 := rfl
    have h₂ : momentumVec (0 : Space (1 + 3)) = 0 := rfl
    simp only [energyMomentumRep, h₁, h₂, hV₁.map_zero, hW.map_zero, mul_one]
  · have h₁ : toLine ((y + y') energyCoordIndex) =
        toLine (y energyCoordIndex) + toLine (y' energyCoordIndex) := rfl
    have h₂ : momentumVec (y + y') = momentumVec y + momentumVec y' := rfl
    simp only [energyMomentumRep, h₁, h₂, ← hV₁.map_add, ← hW.map_add]
    rw [mul_assoc, mul_assoc, ← mul_assoc (W _) (V₁ _), ← hc, mul_assoc]
  · have hp : Continuous momentumVec := by
      unfold momentumVec
      fun_prop
    have he : Continuous fun y : Space (1 + 3) => toLine (y energyCoordIndex) := by
      unfold toLine
      exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => by fun_prop)
    rw [continuous_iff_continuousAt]
    intro y₀
    have h₁ : Tendsto (fun y => W (momentumVec y) ψ) (𝓝 y₀) (𝓝 (W (momentumVec y₀) ψ)) :=
      ((hW.continuous_apply ψ).comp hp).tendsto y₀
    have h₂ : Tendsto (fun y : Space (1 + 3) => V₁ (toLine (y energyCoordIndex))
        (W (momentumVec y₀) ψ)) (𝓝 y₀)
        (𝓝 (V₁ (toLine (y₀ energyCoordIndex)) (W (momentumVec y₀) ψ))) :=
      ((hV₁.continuous_apply _).comp he).tendsto y₀
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have h₃ := (tendsto_iff_norm_sub_tendsto_zero.1 h₁).add
      (tendsto_iff_norm_sub_tendsto_zero.1 h₂)
    rw [add_zero] at h₃
    refine squeeze_zero (fun _ => norm_nonneg _) (fun y => ?_) h₃
    change ‖V₁ (toLine (y energyCoordIndex)) (W (momentumVec y) ψ) -
      V₁ (toLine (y₀ energyCoordIndex)) (W (momentumVec y₀) ψ)‖ ≤ _
    have h₄ : V₁ (toLine (y energyCoordIndex)) (W (momentumVec y) ψ) -
        V₁ (toLine (y₀ energyCoordIndex)) (W (momentumVec y₀) ψ) =
        V₁ (toLine (y energyCoordIndex)) (W (momentumVec y) ψ - W (momentumVec y₀) ψ) +
        (V₁ (toLine (y energyCoordIndex)) (W (momentumVec y₀) ψ) -
          V₁ (toLine (y₀ energyCoordIndex)) (W (momentumVec y₀) ψ)) := by
      rw [map_sub]
      abel
    rw [h₄]
    refine (norm_add_le _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
theorem isJointSpectralMeasure_iff {A : UnboundedOp H} {V₁ : Space 1 → UnitaryMap H H}
    {W : Space 3 → UnitaryMap H H}
    (hosc : ∀ τ : ℝ, SpectralIntegralIs (spectralResolution A)
      (liftFromLine fun x : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ)))
      (V₁ (toLine τ))) (E : BorelSubset (1 + 3) → H →L[ℂ] H) :
    IsJointSpectralMeasure A W E ↔ IsSpectralMeasureOf (energyMomentumRep V₁ W) E := by
  constructor
  · rintro ⟨hP, h⟩
    refine ⟨hP, fun y => ?_⟩
    rw [expChar_eq_energyMomentumChar]
    obtain ⟨hd, hv⟩ := h (y energyCoordIndex) (momentumVec y)
    refine ⟨hd, fun ψ => ?_⟩
    obtain ⟨h₁, h₂⟩ := hv ψ
    exact h₂.trans ((hosc _).2 ⟨_, h₁⟩)
  · rintro ⟨hP, h⟩
    refine ⟨hP, fun τ a => ?_⟩
    have h₀ := h (energyMomentumPoint τ a)
    rw [expChar_eq_energyMomentumChar, energyMomentumPoint_energy,
      momentumVec_energyMomentumPoint] at h₀
    have hj : ∀ φ, energyMomentumRep V₁ W (energyMomentumPoint τ a) φ =
        V₁ (toLine τ) (W a φ) := fun φ => by
      simp only [energyMomentumRep, energyMomentumPoint_energy, momentumVec_energyMomentumPoint]
      rfl
    refine ⟨h₀.1, fun ψ => ?_⟩
    have hm : W a ψ.1 ∈ sqIntegrableDomain (spectralResolution A)
        (liftFromLine fun x : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ))) := by
      rw [(hosc τ).1]
      exact mem_univ _
    exact ⟨hm, (h₀.2 ψ).trans ((hj _).trans ((hosc τ).2 ⟨_, hm⟩).symm)⟩
end Joint
section Properties
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem energyMomentumChar_time (τ : ℝ) :
    (fun y : Space (1 + 3) =>
      Complex.exp (Complex.I * (τ : ℂ) * ((y energyCoordIndex : ℝ) : ℂ))) =
      energyMomentumChar τ 0 := by
  funext y
  simp only [energyMomentumChar, inner_zero_left, add_zero]
  push_cast
  ring_nf
theorem energyMomentumChar_space (a : Space 3) :
    momentumExpChar a = energyMomentumChar 0 a := by
  funext y
  simp [momentumExpChar, energyMomentumChar]
theorem satisfiesConditions
    (hUnit : YangMills.Construction.EuclideanBorel.UnitaryRep.SpectralCorrespondence)
    (hRules : YangMills.Construction.EuclideanBorel.SpectralRules.AllRules)
    (hCalc : YangMills.Construction.EuclideanBorel.FunctionalCalculus.Statement)
    (hSpec : YangMills.Construction.EuclideanBorel.SelfAdjoint.SpectralTheorem)
    {B : ℝ≥0 → H →L[ℂ] H} {A : UnboundedOp H} {W : Space 3 → UnitaryMap H H}
    {V₁ : Space 1 → UnitaryMap H H}
    (hgen : IsSemigroupGenerator B A) (hWrep : IsStronglyContUnitaryRep W)
    (hV₁ : IsStronglyContUnitaryRep V₁)
    (hEA : IsSpectralMeasureOf V₁ (spectralResolution A))
    (hosc : ∀ τ : ℝ, SpectralIntegralIs (spectralResolution A)
      (liftFromLine fun x : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ)))
      (V₁ (toLine τ)))
    {E : BorelSubset (1 + 3) → H →L[ℂ] H} (hE : IsJointSpectralMeasure A W E) :
    SatisfiesConditions B A W E := by
  have : NeZero (1 + 3) := ⟨by norm_num⟩
  have hpm := hE.1
  have hI : ∀ (τ : ℝ) (a : Space 3), SpectralIntegralIs E (energyMomentumChar τ a)
      (fun ψ => V₁ (toLine τ) (W a ψ)) := fun τ a => by
    refine ⟨(hE.2 τ a).1, fun ψ => ?_⟩
    obtain ⟨h₁, h₂⟩ := (hE.2 τ a).2 ψ
    exact h₂.trans ((hosc τ).2 ⟨_, h₁⟩)
  have hIe : ∀ τ : ℝ, SpectralIntegralIs E (fun y : Space (1 + 3) =>
      Complex.exp (Complex.I * (τ : ℂ) * ((y energyCoordIndex : ℝ) : ℂ))) (V₁ (toLine τ)) :=
    fun τ => by
      rw [energyMomentumChar_time]
      have h₀ := hI τ 0
      rw [hWrep.map_zero] at h₀
      exact h₀
  have hIm : ∀ a, SpectralIntegralIs E (momentumExpChar a) (W a) := fun a => by
    rw [energyMomentumChar_space]
    have h₀ := hI 0 a
    rw [toLine_zero, hV₁.map_zero] at h₀
    exact h₀
  have hme : Measurable fun y : Space (1 + 3) => y energyCoordIndex := by fun_prop
  obtain ⟨A', hA', hsa', hspec', hfun'⟩ := (hRules H).2.1 (1 + 3) (by norm_num) E hpm _ hme
  obtain ⟨-, -, -, -, -, -, -, -, hS', -, -⟩ := hSpec H A' hsa'
  obtain ⟨-, -, -, -, -, -, -, -, hS, -, -⟩ := hSpec H A hgen.1
  have hV₁' : IsSpectralMeasureOf V₁ (spectralResolution A') := by
    refine ⟨hS'.1, fun v => ?_⟩
    have hm : Measurable fun x : ℝ => Complex.exp (Complex.I * ((v 0 : ℝ) : ℂ) * (x : ℂ)) := by
      fun_prop
    have hl : expChar v =
        liftFromLine fun x : ℝ => Complex.exp (Complex.I * ((v 0 : ℝ) : ℂ) * (x : ℂ)) := by
      rw [liftFromLine_exp_eq_expChar, toLine_apply_zero]
    rw [hl]
    have h₀ := hIe (v 0)
    rw [toLine_apply_zero] at h₀
    exact spectralIntegralIs_of_partialMapEq (hfun' _ hm) h₀
  have hEq : spectralResolution A' = spectralResolution A :=
    ((hUnit H 1 le_rfl).2 V₁ hV₁).1.unique hV₁' hEA
  have hline := hS'.2
  rw [hEq] at hline
  have hAA : A' = A := spectralIntegralOp_unique hline hS.2
  rw [hAA] at hA' hspec' hfun'
  have hisop : ∀ {n : ℕ} [NeZero n] (F : BorelSubset n → H →L[ℂ] H), IsPVM F →
      ∀ (f : Space n → ℂ), Measurable f →
        RealizesSpectralIntegral F f (YangMills.Construction.EuclideanBorel.spectralOp F f) :=
    fun {n} _ F hF f hf => (hCalc n n H F hF f f hf hf 0).1.isOp
  obtain ⟨-, -, -, -, -, -, -, himg, -, -, hother⟩ :=
    hCalc (1 + 3) 3 H E hpm _ _ (measurable_const (a := (0 : ℂ)))
      (measurable_const (a := (0 : ℂ))) 0
  have hmargPVM : IsPVM (momentumMarginal E) :=
    (himg momentumVec measurable_momentumVec |>.1)
  have hmarg : IsSpectralMeasureOf W (momentumMarginal E) := by
    refine ⟨hmargPVM, fun a => ?_⟩
    have hf := measurable_expChar a
    have hop := (himg momentumVec measurable_momentumVec).2 _ hf
    have h₁ := hisop _ hmargPVM _ hf
    have h₂ := hisop _ hpm _ (hf.comp measurable_momentumVec)
    change RealizesSpectralIntegral (momentumMarginal E) _
      (YangMills.Construction.EuclideanBorel.spectralOp (momentumMarginal E) _) at h₁
    have hop' : YangMills.Construction.EuclideanBorel.spectralOp (momentumMarginal E)
        (expChar a) = YangMills.Construction.EuclideanBorel.spectralOp E
        (expChar a ∘ momentumVec) := hop
    rw [hop'] at h₁
    exact spectralIntegralIs_of_isSpectralIntegralOp h₂ h₁ (hIm a)
  obtain ⟨huniq, hWspec, -⟩ := (hUnit H 3 (by norm_num)).2 W hWrep
  obtain ⟨P, hPi, hPs, -, hPc⟩ := (hRules H).2.2.1 (1 + 3) (by norm_num) E hpm
  have hmom : ∀ i, momentumOp E i = P (momentumCoordIndex i) := fun i =>
    spectralIntegralOp_unique (Classical.epsilon_spec
      (p := fun Q => IsSpectralIntegralOp Q E (momentumCoord i))
      ⟨_, hPi (momentumCoordIndex i)⟩) (hPi _)
  have hP0 : P energyCoordIndex = A := spectralIntegralOp_unique (hPi energyCoordIndex) hA'
  have hPeq : (![A, momentumOp E 0, momentumOp E 1, momentumOp E 2] :
      Fin 4 → UnboundedOp H) = P := by
    funext i
    fin_cases i
    · exact hP0.symm
    · exact hmom 0
    · exact hmom 1
    · exact hmom 2
  have hsupp : pvmSupport E ⊆ {y | 0 ≤ y energyCoordIndex} := by
    intro y hy
    by_contra hneg
    have hL : IsMaximalOpenNull E (maxOpenNull E) :=
      Classical.epsilon_spec hother.1
    have hO : IsOpenNull E {y | y energyCoordIndex < 0} := by
      refine ⟨isOpen_lt (by fun_prop) continuous_const, ?_⟩
      have h₁ := ((hRules H).1.1 A hgen.1 0).2 (fun χ => by simpa using hgen.2.1 χ)
      rw [hspec'] at h₁
      exact h₁
    have hlt : y energyCoordIndex < 0 := not_le.1 hneg
    exact hy (hL.2 _ hO hlt)
  unfold SatisfiesConditions
  refine ⟨hE, hA', fun t => ?_, hmarg, huniq.unique hmarg hWspec, fun i => ⟨?_, ?_⟩,
    fun a => ⟨(hIm a).1, fun ψ => (hIm a).2 ψ⟩,
    Eq.mpr (congrArg (fun Q : Fin 4 → UnboundedOp H => StronglyCommute Q) hPeq) hPc, rfl, hsupp⟩
  · have hm : Measurable fun x : ℝ => Complex.exp (-((t : ℝ) : ℂ) * (x : ℂ)) := by fun_prop
    exact spectralIntegralIs_of_partialMapEq' (hfun' _ hm) ⟨(hgen.2.2 t).1, (hgen.2.2 t).2⟩
  · rw [hmom]
    exact hPi _
  · rw [hmom]
    exact hPs _
end Properties
theorem statement_holds
    (hUnit : YangMills.Construction.EuclideanBorel.UnitaryRep.SpectralCorrespondence)
    (hRules : YangMills.Construction.EuclideanBorel.SpectralRules.AllRules)
    (hCalc : YangMills.Construction.EuclideanBorel.FunctionalCalculus.Statement)
    (hSpec : YangMills.Construction.EuclideanBorel.SelfAdjoint.SpectralTheorem) : Statement := by
  intro H _ _ _ B A W _ hgen hlog hWrep hc
  have hcW : ∀ a Δ, Commutes (toCLM (W a)) (spectralResolution A Δ) :=
    fun a Δ => commutes_spectralResolution hRules hSpec hgen hlog (hc a 1) Δ
  obtain ⟨V₁, hV₁, hosc, hEA, hcomm⟩ :=
    exists_timeTranslation hUnit hCalc hSpec hgen.1 hcW
  have hrep := isStronglyContUnitaryRep_energyMomentumRep hV₁ hWrep hcomm
  have hiff := isJointSpectralMeasure_iff (W := W) hosc
  obtain ⟨⟨E₀, hE₀, hU⟩, -, -⟩ := (hUnit H (1 + 3) (by norm_num)).2 _ hrep
  have hE₁ : IsJointSpectralMeasure A W E₀ := (hiff E₀).2 hE₀
  refine ⟨⟨E₀, hE₁, fun E' h' => hU E' ((hiff E').1 h')⟩, ?_⟩
  have hE : IsJointSpectralMeasure A W (jointSpectralMeasure A W) :=
    Classical.epsilon_spec ⟨E₀, hE₁⟩
  exact satisfiesConditions hUnit hRules hCalc hSpec hgen hWrep hV₁ hEA hosc hE
end YangMills.Construction.PositiveFormReconstruction.CommutingJointSpectrum
