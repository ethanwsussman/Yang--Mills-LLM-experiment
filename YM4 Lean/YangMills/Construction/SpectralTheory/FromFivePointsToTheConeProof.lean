import YangMills.Construction.HilbertSpaces.JointSpectralMeasureOfACommutingPairProof
import YangMills.Construction.ReflectionPositiveLimits.FromFivePointInequalitiesToTheConeProof
import YangMills.Construction.EnergyMomentum.ArcoshCurveChordProof
import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusTheorem
import YangMills.Construction.SpectralTheory.FromFivePointsToTheCone
import YangMills.Construction.SpectralTheory.UnboundedBorelCalculusFromTruncations
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.FivePointCone
open BorelSpectral HilbertSpaceBasics SpectralTheorem SelfAdjointFunctions BorelCalculus
theorem norm_one_sub_exp_I_mul_sq (x : ℝ) :
    ‖1 - Complex.exp (Complex.I * (x : ℂ))‖ ^ 2 = 2 - 2 * Real.cos x := by apply _root_.YangMills.Construction.EnergyMomentum.ArcoshCurve.norm_one_sub_exp_I_mul_sq <;> assumption
theorem exp_mul_sinh_sin_form (a x : ℝ) :
    Real.exp a * ((1 - Real.exp (-a)) ^ 2 - Real.exp (-a) * (2 - 2 * Real.cos x)) =
        4 * Real.sinh (a / 2) ^ 2 - 4 * Real.sin (x / 2) ^ 2 ∧
      4 * Real.sinh (a / 2) ^ 2 - 4 * Real.sin (x / 2) ^ 2 =
        2 * (Real.cosh a + Real.cos x - 2) := by
  have hcosh : Real.cosh a = 1 + 2 * Real.sinh (a / 2) ^ 2 := by
    have h := Real.cosh_two_mul (a / 2)
    rw [mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at h
    rw [h, Real.cosh_sq]
    ring
  have hcos : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    have h := Real.cos_two_mul (x / 2)
    rw [mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at h
    rw [h]
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  have hright : 4 * Real.sinh (a / 2) ^ 2 - 4 * Real.sin (x / 2) ^ 2 =
      2 * (Real.cosh a + Real.cos x - 2) := by
    rw [hcosh, hcos]
    ring
  refine ⟨?_, hright⟩
  rw [hright]
  have hexp : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
  have hch : 2 * Real.cosh a = Real.exp a + Real.exp (-a) := by rw [Real.cosh_eq]; ring
  linear_combination (Real.exp (-a) - 4 + 2 * Real.cos x) * hexp - hch
theorem abs_le_of_sin_le_sinh_seq (a x : ℝ) (s : ℕ → ℝ) (hs : ∀ k, 0 < s k)
    (hlim : Tendsto s atTop (𝓝 0))
    (h : ∀ k, |Real.sin (s k * x / 2)| ≤ Real.sinh (s k * a / 2)) : |x| ≤ a := by
  have hsin : HasDerivAt (fun r : ℝ => Real.sin (r * x / 2)) (x / 2) 0 := by
    simpa using (((hasDerivAt_id' (0 : ℝ)).mul_const x).div_const 2).sin
  have hsinh : HasDerivAt (fun r : ℝ => Real.sinh (r * a / 2)) (a / 2) 0 := by
    simpa using (((hasDerivAt_id' (0 : ℝ)).mul_const a).div_const 2).sinh
  have hs' : Tendsto s atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun k => (hs k).ne'⟩
  have lim₁ := hsin.tendsto_slope_zero.comp hs'
  have lim₂ := hsinh.tendsto_slope_zero.comp hs'
  have hle := le_of_tendsto_of_tendsto' lim₁.abs lim₂ (fun k => by
    have hk : 0 < (s k)⁻¹ := inv_pos.mpr (hs k)
    simp only [Function.comp, zero_add, zero_mul, zero_div, Real.sin_zero, Real.sinh_zero, sub_zero,
      smul_eq_mul, abs_mul, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_left (h k) hk.le)
  rw [abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)] at hle
  linarith
def IsBddBorel {X : Type*} [MeasurableSpace X] (f : X → ℂ) : Prop :=
  Measurable f ∧ IsBoundedFn f
section Functions
variable {X : Type*} [MeasurableSpace X] {f g : X → ℂ}
theorem IsBddBorel.add (hf : IsBddBorel f) (hg : IsBddBorel g) : IsBddBorel (f + g) := by apply _root_.YangMills.Construction.ReflectionPositivity.FivePointCone.isBoundedMeasurable_add_fn <;> assumption
theorem IsBddBorel.smul (hf : IsBddBorel f) (z : ℂ) : IsBddBorel (z • f) := by
  obtain ⟨c, hc⟩ := hf.2
  refine ⟨hf.1.const_smul z, ‖z‖ * c, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hc x) (norm_nonneg z)
theorem IsBddBorel.mul (hf : IsBddBorel f) (hg : IsBddBorel g) : IsBddBorel (f * g) := by apply _root_.YangMills.Construction.SpectralCalculus.JointSpectralProof.isBoundedMeasurable_mul <;> assumption
theorem IsBddBorel.sub (hf : IsBddBorel f) (hg : IsBddBorel g) : IsBddBorel (f - g) := by
  have e : f - g = f + (-1 : ℂ) • g := by simp [sub_eq_add_neg]
  rw [e]
  exact hf.add (hg.smul _)
theorem isBddBorel_one : IsBddBorel (1 : X → ℂ) :=
  ⟨measurable_one, 1, fun x => by simp⟩
end Functions
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
def expDecay (lam : Y → ℝ) (t : ℝ) : Y → ℂ := fun y => Complex.exp ((-(t * lam y) : ℝ) : ℂ)
def expPhase (q : Y → ℝ) (s : ℝ) : Y → ℂ := fun y => Complex.exp (Complex.I * s * (q y : ℝ))
theorem expDecay_apply (lam : Y → ℝ) (t : ℝ) (y : Y) :
    expDecay lam t y = ((Real.exp (-(t * lam y)) : ℝ) : ℂ) :=
  (Complex.ofReal_exp _).symm
theorem expDecay_two_mul (lam : Y → ℝ) (t : ℝ) (y : Y) :
    expDecay lam (2 * t) y = ((Real.exp (-(t * lam y)) : ℝ) : ℂ) ^ 2 := by
  rw [expDecay_apply, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring
theorem isBddBorel_expDecay {lam : Y → ℝ} (hlam : Measurable lam) (hpos : ∀ y, 0 ≤ lam y) {t : ℝ}
    (ht : 0 ≤ t) : IsBddBorel (expDecay lam t) := by
  refine ⟨?_, 1, fun y => ?_⟩
  · unfold expDecay
    fun_prop
  · rw [expDecay_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.exp_le_one_iff]
    have := mul_nonneg ht (hpos y)
    linarith
theorem I_mul_mul_eq (q : Y → ℝ) (s : ℝ) (y : Y) :
    Complex.I * (s : ℂ) * (q y : ℝ) = ((s * q y : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring
theorem norm_expPhase (q : Y → ℝ) (s : ℝ) (y : Y) : ‖expPhase q s y‖ = 1 := by
  unfold expPhase
  rw [I_mul_mul_eq, Complex.norm_exp_ofReal_mul_I]
theorem isBddBorel_expPhase {q : Y → ℝ} (hq : Measurable q) (s : ℝ) :
    IsBddBorel (expPhase q s) := by
  refine ⟨?_, 1, fun y => (norm_expPhase q s y).le⟩
  unfold expPhase
  fun_prop
theorem expPhase_add_neg (q : Y → ℝ) (t : ℝ) (y : Y) :
    expPhase q t y + expPhase q (-t) y = ((2 * Real.cos (t * q y) : ℝ) : ℂ) := by
  have h := Complex.two_cos ((t * q y : ℝ) : ℂ)
  unfold expPhase
  rw [I_mul_mul_eq, I_mul_mul_eq]
  have e : ((-t * q y : ℝ) : ℂ) = -((t * q y : ℝ) : ℂ) := by push_cast; ring
  rw [e, ← h]
  push_cast
  rfl
theorem conjFn_expPhase (q : Y → ℝ) (t : ℝ) :
    conjFn (expPhase q t) = expPhase q (-t) := by
  funext y
  simp only [conjFn, expPhase]
  rw [← Complex.exp_conj, I_mul_mul_eq, I_mul_mul_eq]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring
theorem fivePointFn_eq (lam q : Y → ℝ) (t : ℝ) (y : Y) :
    fivePointFn lam q t y = (1 - Real.exp (-(t * lam y))) ^ 2 -
      Real.exp (-(t * lam y)) * (2 - 2 * Real.cos (t * q y)) := by
  unfold fivePointFn
  have e : Complex.I * (t : ℂ) * (q y : ℝ) = Complex.I * ((t * q y : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e, norm_one_sub_exp_I_mul_sq]
section Algebra
variable {E : SpectralMeasure Y H} {f g h : Y → ℂ}
theorem integralOp_add (C : BoundedFunctionalCalculus E) (hg : IsBddBorel g) (hh : IsBddBorel h) :
    E.integralOp (g + h) = E.integralOp g + E.integralOp h :=
  C.add g h hg.1 hg.2 hh.1 hh.2
theorem integralOp_smul (C : BoundedFunctionalCalculus E) (z : ℂ) (hg : IsBddBorel g) :
    E.integralOp (z • g) = z • E.integralOp g :=
  C.smul z g hg.1 hg.2
theorem integralOp_mul (C : BoundedFunctionalCalculus E) (hg : IsBddBorel g) (hh : IsBddBorel h) :
    E.integralOp (g * h) = E.integralOp g * E.integralOp h :=
  C.mul g h hg.1 hg.2 hh.1 hh.2
theorem integralOp_sub (C : BoundedFunctionalCalculus E) (hg : IsBddBorel g) (hh : IsBddBorel h) :
    E.integralOp (g - h) = E.integralOp g - E.integralOp h := by
  have e : g - h = g + (-1 : ℂ) • h := by simp [sub_eq_add_neg]
  rw [e, integralOp_add C hg (hh.smul _), integralOp_smul C _ hh]
  simp [sub_eq_add_neg]
theorem integralOp_one (C : BoundedFunctionalCalculus E) : E.integralOp (1 : Y → ℂ) = 1 := by apply _root_.YangMills.Construction.BorelCalculus.Unbounded.integralOp_one <;> assumption
theorem integralOp_five_terms (C : BoundedFunctionalCalculus E) {a a₂ u v : Y → ℂ}
    (ha : IsBddBorel a) (ha₂ : IsBddBorel a₂) (hu : IsBddBorel u) (hv : IsBddBorel v) :
    E.integralOp (1 - (4 : ℂ) • a + a₂ + a * u + a * v) =
      1 - (4 : ℂ) • E.integralOp a + E.integralOp a₂ +
        E.integralOp a * E.integralOp u + E.integralOp a * E.integralOp v := by
  have h₁ : IsBddBorel (1 : Y → ℂ) := isBddBorel_one
  have h₄ := ha.smul 4
  rw [integralOp_add C (((h₁.sub h₄).add ha₂).add (ha.mul hu)) (ha.mul hv),
    integralOp_add C ((h₁.sub h₄).add ha₂) (ha.mul hu), integralOp_add C (h₁.sub h₄) ha₂,
    integralOp_sub C h₁ h₄, integralOp_one C, integralOp_smul C _ ha, integralOp_mul C ha hu,
    integralOp_mul C ha hv]
end Algebra
section Parts
variable {E : SpectralMeasure Y H} {lam q : Y → ℝ}
theorem five_terms_apply (lam q : Y → ℝ) (t : ℝ) (y : Y) :
    (1 - (4 : ℂ) • expDecay lam t + expDecay lam (2 * t) + expDecay lam t * expPhase q t +
      expDecay lam t * expPhase q (-t)) y = ((fivePointFn lam q t y : ℝ) : ℂ) := by
  have hcos := expPhase_add_neg q t y
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.one_apply, smul_eq_mul]
  rw [expDecay_two_mul, expDecay_apply, fivePointFn_eq]
  push_cast at hcos ⊢
  linear_combination (Complex.exp (-(t * lam y : ℂ))) * hcos
theorem fivePointOp_eq_and_selfAdjoint (C : BoundedFunctionalCalculus E) (hlam : Measurable lam)
    (hq : Measurable q) (hpos : ∀ y, 0 ≤ lam y) {t : ℝ} (ht : 0 < t) :
    fivePointOp E lam q t = defectSq E lam t - phaseDefectOp E lam q t ∧
      fivePointOp E lam q t =
        E.integralOp (fun y => ((fivePointFn lam q t y : ℝ) : ℂ)) ∧
      IsSelfAdjoint (defectSq E lam t) ∧ IsSelfAdjoint (phaseDefectOp E lam q t) ∧
      IsSelfAdjoint (fivePointOp E lam q t) ∧
      IsBddBorel (fun y => ((fivePointFn lam q t y : ℝ) : ℂ)) := by
  have ha := isBddBorel_expDecay hlam hpos ht.le
  have ha₂ := isBddBorel_expDecay hlam hpos (mul_nonneg zero_le_two ht.le : 0 ≤ 2 * t)
  have hu := isBddBorel_expPhase hq t
  have hv := isBddBorel_expPhase hq (-t)
  have h₁ : IsBddBorel (1 : Y → ℂ) := isBddBorel_one
  have h₂ := (h₁.smul 2)
  have hsq := (h₁.sub ha).mul (h₁.sub ha)
  have hdef := ha.mul ((h₂.sub hu).sub hv)
  have hfive := ((((h₁.sub (ha.smul 4)).add ha₂).add (ha.mul hu)).add (ha.mul hv))
  have hstar : star (E.integralOp (expPhase q t)) = E.integralOp (expPhase q (-t)) := by
    rw [← C.star_eq _ hu.1 hu.2, conjFn_expPhase]
  have eSq : defectSq E lam t =
      E.integralOp ((1 - expDecay lam t) * (1 - expDecay lam t)) := by
    rw [integralOp_mul C (h₁.sub ha) (h₁.sub ha), integralOp_sub C h₁ ha, integralOp_one C]
    exact sq _
  have eDef : phaseDefectOp E lam q t = E.integralOp
      (expDecay lam t * ((2 : ℂ) • 1 - expPhase q t - expPhase q (-t))) := by
    rw [integralOp_mul C ha ((h₂.sub hu).sub hv), integralOp_sub C (h₂.sub hu) hv,
      integralOp_sub C h₂ hu, integralOp_smul C _ h₁, integralOp_one C, ← hstar]
    rfl
  have eFive : fivePointOp E lam q t = E.integralOp
      (1 - (4 : ℂ) • expDecay lam t + expDecay lam (2 * t) + expDecay lam t * expPhase q t +
        expDecay lam t * expPhase q (-t)) := by
    rw [integralOp_five_terms C ha ha₂ hu hv]
    rfl
  have fFive : (1 - (4 : ℂ) • expDecay lam t + expDecay lam (2 * t) + expDecay lam t * expPhase q t +
      expDecay lam t * expPhase q (-t)) = fun y => ((fivePointFn lam q t y : ℝ) : ℂ) :=
    funext (five_terms_apply lam q t)
  have fSq : ∀ y, ((1 - expDecay lam t) * (1 - expDecay lam t)) y =
      (((1 - Real.exp (-(t * lam y))) ^ 2 : ℝ) : ℂ) := fun y => by
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, expDecay_apply]
    push_cast
    ring
  have fDef : ∀ y, (expDecay lam t * ((2 : ℂ) • 1 - expPhase q t - expPhase q (-t))) y =
      ((Real.exp (-(t * lam y)) * (2 - 2 * Real.cos (t * q y)) : ℝ) : ℂ) := fun y => by
    have hcos := expPhase_add_neg q t y
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, expDecay_apply]
    push_cast at hcos ⊢
    linear_combination (-(Complex.exp (-(t * lam y : ℂ)))) * hcos
  have fSplit : (1 - (4 : ℂ) • expDecay lam t + expDecay lam (2 * t) + expDecay lam t * expPhase q t +
      expDecay lam t * expPhase q (-t)) = (1 - expDecay lam t) * (1 - expDecay lam t) -
        expDecay lam t * ((2 : ℂ) • 1 - expPhase q t - expPhase q (-t)) := by
    funext y
    rw [five_terms_apply, Pi.sub_apply, fSq, fDef, fivePointFn_eq]
    push_cast
    ring
  have hFn : IsBddBorel fun y => ((fivePointFn lam q t y : ℝ) : ℂ) := fFive ▸ hfive
  refine ⟨?_, ?_, ?_, ?_, ?_, hFn⟩
  · rw [eFive, fSplit, integralOp_sub C hsq hdef, eSq, eDef]
  · rw [eFive, fFive]
  · rw [eSq]
    exact C.isSelfAdjoint _ hsq.1 hsq.2 fun y => by rw [fSq]; exact Complex.ofReal_im _
  · rw [eDef]
    exact C.isSelfAdjoint _ hdef.1 hdef.2 fun y => by rw [fDef]; exact Complex.ofReal_im _
  · rw [eFive, fFive]
    exact C.isSelfAdjoint _ hFn.1 hFn.2 fun y => Complex.ofReal_im _
omit [CompleteSpace H] in
theorem inner_nonneg_of_isNonnegOnDense {A : H →L[ℂ] H} (hA : IsNonnegOnDense A) (ψ : H) :
    0 ≤ ⟪ψ, A ψ⟫_ℂ := by
  obtain ⟨D, hD, hnn⟩ := hA
  have hcl : IsClosed {ψ : H | 0 ≤ ⟪ψ, A ψ⟫_ℂ} :=
    isClosed_le continuous_const (continuous_id.inner A.continuous)
  exact hcl.closure_subset_iff.mpr hnn (hD ψ)
theorem defectSq_ge_and_carried (C : BoundedFunctionalCalculus E) (K : KernelAndPositivity E)
    (hlam : Measurable lam) (hq : Measurable q) (hpos : ∀ y, 0 ≤ lam y) {t : ℝ} (ht : 0 < t)
    (hA : IsNonnegOnDense (fivePointOp E lam q t)) :
    IsGE (defectSq E lam t) (phaseDefectOp E lam q t) ∧
      E.IsCarriedBy (sinhGeSinSet hlam hq t) := by
  obtain ⟨eSplit, eFive, sSq, sDef, -, hb⟩ := fivePointOp_eq_and_selfAdjoint C hlam hq hpos ht
  have hall := inner_nonneg_of_isNonnegOnDense hA
  refine ⟨⟨sSq, sDef, sSq.sub sDef, fun ψ => ?_⟩, ?_⟩
  · rw [← eSplit]
    exact hall ψ
  · obtain ⟨c, hc⟩ := hb.2
    have hneg := (K.nonneg_iff _ hb.1 fun y => Complex.ofReal_im _).mp fun ψ _ => by
      rw [E.integralApply_eq_integralOp hc, ← eFive]
      exact hall ψ
    refine C.apply_subset _ _ hneg fun y hy => ?_
    have hlt : Real.sinh (t * lam y / 2) < |Real.sin (t * q y / 2)| := not_le.mp hy
    have hsh : 0 ≤ Real.sinh (t * lam y / 2) :=
      Real.sinh_nonneg_iff.mpr (by have := mul_nonneg ht.le (hpos y); linarith)
    have hform := (exp_mul_sinh_sin_form (t * lam y) (t * q y)).1
    rw [← fivePointFn_eq] at hform
    have hsq : Real.sinh (t * lam y / 2) ^ 2 < Real.sin (t * q y / 2) ^ 2 := by
      rw [← sq_abs (Real.sin _)]
      exact pow_lt_pow_left₀ hlt hsh two_ne_zero
    show (((fivePointFn lam q t y : ℝ) : ℂ)).re < 0
    rw [Complex.ofReal_re]
    by_contra hge
    have := mul_nonneg (Real.exp_pos (t * lam y)).le (not_lt.mp hge)
    linarith
theorem apply_ltAbsSet_eq_zero (C : BoundedFunctionalCalculus E) (K : KernelAndPositivity E)
    (hlam : Measurable lam) (hq : Measurable q) (hpos : ∀ y, 0 ≤ lam y) (t : ℕ → ℝ)
    (ht : ∀ k, 0 < t k) (hlim : Tendsto t atTop (𝓝 0))
    (hA : ∀ k, IsNonnegOnDense (fivePointOp E lam q (t k))) :
    E (ltAbsSet hlam hq) = 0 := by
  have hk : ∀ k, E ⟨(sinhGeSinSet hlam hq (t k)).1ᶜ, (sinhGeSinSet hlam hq (t k)).2.compl⟩ = 0 :=
    fun k => (defectSq_ge_and_carried C K hlam hq hpos (ht k) (hA k)).2
  refine C.apply_subset _ _ (C.apply_iUnion ℕ _ hk) fun y hy => ?_
  by_contra hn
  have hall : ∀ k, |Real.sin (t k * q y / 2)| ≤ Real.sinh (t k * lam y / 2) := fun k => by
    by_contra hk'
    exact hn (mem_iUnion.mpr ⟨k, hk'⟩)
  exact absurd (abs_le_of_sin_le_sinh_seq (lam y) (q y) t ht hlim hall) (not_le.mpr hy)
theorem isSpectralIntegralOf_spectralIntegralOp (U : UnboundedFunctionalCalculus E) {g : Y → ℂ}
    (hg : Measurable g) : IsSpectralIntegralOf (spectralIntegralOp E g) E g := by
  obtain ⟨A, -, hd, hv⟩ := U.exists_op g hg
  exact Classical.epsilon_spec (p := fun A => IsSpectralIntegralOf A E g)
    ⟨A, fun ψ => by rw [← hd]; rfl, hv⟩
theorem spectralIntegralOp_eq_of_integralsAgree {m : ℕ} {Z : Set (Fin m → ℝ)}
    {F : SpectralMeasure Z H} {g : Y → ℂ} {g' : Z → ℂ}
    (h : IntegralsAgree E g F g') : spectralIntegralOp E g = spectralIntegralOp F g' := by
  have e : (fun A => IsSpectralIntegralOf A E g) = fun A => IsSpectralIntegralOf A F g' := by
    funext A
    apply propext
    constructor
    · rintro ⟨hd, hv⟩
      refine ⟨fun ψ => by rw [hd, h.1], fun ψ => ?_⟩
      rw [hv ψ]
      exact h.2 _ ((hd _).1 ψ.2)
    · rintro ⟨hd, hv⟩
      refine ⟨fun ψ => by rw [hd, h.1], fun ψ => ?_⟩
      have hm : (ψ : H) ∈ E.integralDom g := by
        rw [h.1]
        exact (hd _).1 ψ.2
      rw [hv ψ]
      exact (h.2 _ hm).symm
  unfold spectralIntegralOp
  rw [e]
theorem integrable_of_mem_integralDom {g : Y → ℂ} (hg : Measurable g) {ψ : H}
    (hψ : ψ ∈ E.integralDom g) : Integrable g (E.diagMeasure ψ) := by
  have hm : MemLp g 2 (E.diagMeasure ψ) := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    have hψ' : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure ψ < ∞ := hψ
    simpa using hψ'
  exact hm.integrable one_le_two
theorem cone_of_null_ltAbsSet (C : BoundedFunctionalCalculus E) (U : UnboundedFunctionalCalculus E)
    (K : KernelAndPositivity E)
    (hS : ∀ A : UnboundedOp H, IsSelfAdjointOp A →
      ∀ g : Y → ℝ, Measurable g → IsSpectralIntegralOf A E (fun y => ((g y : ℝ) : ℂ)) →
        ∀ f : ℝ → ℂ, Measurable f →
          IntegralsAgree (spectralMeasure A) (fun y => f (y.1 0)) E (fun y => f (g y)))
    (hlam : Measurable lam) (hq : Measurable q) (hpos : ∀ y, 0 ≤ lam y)
    (hE : E (ltAbsSet hlam hq) = 0) :
    absOp (momentumOp E q) = spectralIntegralOp E (fun y => ((|q y| : ℝ) : ℂ)) ∧
      (energyOp E lam).domain ≤ (momentumOp E q).domain ∧
      (momentumOp E q).domain = (absOp (momentumOp E q)).domain ∧
      (∀ ψ : (energyOp E lam).domain, ∃ h : (ψ : H) ∈ (absOp (momentumOp E q)).domain,
        ⟪(ψ : H), absOp (momentumOp E q) ⟨ψ, h⟩⟫_ℂ ≤ ⟪(ψ : H), energyOp E lam ψ⟫_ℂ) ∧
      ∀ ψ : (energyOp E lam).domain, energyOp E lam ψ = 0 → ∀ s : ℝ, phaseOp E q s ψ = ψ := by
  have hlc : Measurable fun y => ((lam y : ℝ) : ℂ) := Complex.measurable_ofReal.comp hlam
  have hqc : Measurable fun y => ((q y : ℝ) : ℂ) := Complex.measurable_ofReal.comp hq
  have hac : Measurable fun y => ((|q y| : ℝ) : ℂ) := Complex.measurable_ofReal.comp hq.abs
  have iEn : IsSpectralIntegralOf (energyOp E lam) E _ := isSpectralIntegralOf_spectralIntegralOp U hlc
  have iMo : IsSpectralIntegralOf (momentumOp E q) E _ := isSpectralIntegralOf_spectralIntegralOp U hqc
  have iAb := isSpectralIntegralOf_spectralIntegralOp U hac
  have sMo : IsSelfAdjointOp (momentumOp E q) :=
    U.isSelfAdjoint _ hqc (fun y => Complex.ofReal_im _) _ ⟨Set.ext iMo.1, iMo.2⟩
  have habs : absOp (momentumOp E q) = spectralIntegralOp E (fun y => ((|q y| : ℝ) : ℂ)) :=
    spectralIntegralOp_eq_of_integralsAgree (hS _ sMo q hq iMo (fun x => ((|x| : ℝ) : ℂ))
      (Complex.measurable_ofReal.comp measurable_id.abs))
  have iM : IsSpectralIntegralOf (absOp (momentumOp E q)) E (fun y => ((|q y| : ℝ) : ℂ)) := by
    rw [habs]
    exact iAb
  have hcarried : E.IsCarriedBy ⟨(ltAbsSet hlam hq).1ᶜ, (ltAbsSet hlam hq).2.compl⟩ :=
    C.apply_subset _ _ hE fun y hy => by simpa using hy
  have hle : ∀ y ∈ (ltAbsSet hlam hq).1ᶜ, |q y| ≤ lam y := fun y hy => not_lt.mp hy
  have hdom : ∀ ψ, ψ ∈ E.integralDom (fun y => ((q y : ℝ) : ℂ)) ↔
      ψ ∈ E.integralDom (fun y => ((|q y| : ℝ) : ℂ)) := fun ψ => by
    simp only [SpectralMeasure.integralDom, mem_ofPred_eq, ← ofReal_norm,
      Complex.norm_real, Real.norm_eq_abs, abs_abs]
  have hsub : ∀ ψ, ψ ∈ (energyOp E lam).domain → ψ ∈ (momentumOp E q).domain := fun ψ hψ => by
    rw [iMo.1]
    refine U.dom_subset _ _ hqc hlc _ hcarried (fun y hy => ?_) ((iEn.1 ψ).1 hψ)
    simpa [abs_of_nonneg (hpos y)] using hle y hy
  have hsame : ∀ ψ, ψ ∈ (momentumOp E q).domain ↔ ψ ∈ (absOp (momentumOp E q)).domain :=
    fun ψ => by rw [iMo.1, iM.1, hdom]
  refine ⟨habs, fun ψ hψ => hsub ψ hψ, ?_, ?_, ?_⟩
  · ext ψ
    exact hsame ψ
  · intro ψ
    have hψP := hsub ψ ψ.2
    have hψM : (ψ : H) ∈ (absOp (momentumOp E q)).domain := (hsame ψ).1 hψP
    refine ⟨hψM, ?_⟩
    have dEn : (ψ : H) ∈ E.integralDom (fun y => ((lam y : ℝ) : ℂ)) := (iEn.1 ψ).1 ψ.2
    have dAb : (ψ : H) ∈ E.integralDom (fun y => ((|q y| : ℝ) : ℂ)) := (iM.1 ψ).1 hψM
    have hμ : E.diagMeasure (ψ : H) (ltAbsSet hlam hq).1 = 0 := by
      rw [E.diagMeasure_apply, hE]
      simp
    have hae : ∀ᵐ y ∂E.diagMeasure (ψ : H), |q y| ≤ lam y :=
      ae_iff.mpr (measure_mono_null (fun y hy => not_le.mp hy) hμ)
    have ilam : Integrable lam (E.diagMeasure (ψ : H)) :=
      (integrable_of_mem_integralDom hlc dEn).norm.congr (ae_of_all _ fun y => by
        simp [abs_of_nonneg (hpos y)])
    have iabs : Integrable (fun y => |q y|) (E.diagMeasure (ψ : H)) :=
      (integrable_of_mem_integralDom hac dAb).norm.congr (ae_of_all _ fun y => by simp)
    rw [iM.2 ⟨ψ, hψM⟩, iEn.2 ψ, U.inner_eq _ hac _ dAb, U.inner_eq _ hlc _ dEn,
      integral_complex_ofReal, integral_complex_ofReal]
    exact Complex.real_le_real.mpr (integral_mono_ae iabs ilam hae)
  · intro ψ hψ s
    have dEn : (ψ : H) ∈ E.integralDom (fun y => ((lam y : ℝ) : ℂ)) := (iEn.1 ψ).1 ψ.2
    have hker : (ψ : H) ∈ Set.range (E (zeroLocus hlc)) := by
      rw [← K.kernel_eq _ hlc]
      exact ⟨dEn, by rw [← iEn.2 ψ, hψ]⟩
    have hμ₀ := C.diagMeasure_compl (zeroLocus hlc) ψ hker
    have hμ : E.diagMeasure (ψ : H) (ltAbsSet hlam hq).1 = 0 := by
      rw [E.diagMeasure_apply, hE]
      simp
    have hae₁ : ∀ᵐ y ∂E.diagMeasure (ψ : H), |q y| ≤ lam y :=
      ae_iff.mpr (measure_mono_null (fun y hy => not_le.mp hy) hμ)
    have hsubz : {y | ¬ lam y = 0} ⊆ (zeroLocus hlc).1ᶜ := fun y hy hz => hy (by
      have hz' : ((lam y : ℝ) : ℂ) = 0 := hz
      exact_mod_cast hz')
    have hae₂ : ∀ᵐ y ∂E.diagMeasure (ψ : H), lam y = 0 :=
      ae_iff.mpr (measure_mono_null hsubz hμ₀)
    have hb := (isBddBorel_expPhase hq s).sub (isBddBorel_one : IsBddBorel (1 : Y → ℂ))
    have hn := C.norm_sq _ hb.1 hb.2 ψ
    rw [integralOp_sub C (isBddBorel_expPhase hq s) isBddBorel_one, integralOp_one C,
      integral_eq_zero_of_ae (by
        filter_upwards [hae₁, hae₂] with y h₁ h₂
        have hqy : q y = 0 := by
          rw [h₂] at h₁
          exact abs_nonpos_iff.mp h₁
        simp [expPhase, hqy])] at hn
    have h₀ : (E.integralOp (expPhase q s) - 1) (ψ : H) = 0 := by
      simpa using hn
    have h₁ : E.integralOp (expPhase q s) (ψ : H) - (ψ : H) = 0 := by
      simpa using h₀
    exact sub_eq_zero.mp h₁
end Parts
theorem fivePointConeTheorem_holds (hC : BorelCalculusTheorem) (hS : SpectralTheoremHolds) :
    FivePointConeTheorem := by
  intro H _ _ _ n Y E lam q hlam hq hpos
  obtain ⟨C, -, -, U, K, -, -⟩ := (hC H n).1 Y E
  refine ⟨fun t ht => ?_, fun t ht hA => defectSq_ge_and_carried C K hlam hq hpos ht hA,
    fun t ht hlim hA => apply_ltAbsSet_eq_zero C K hlam hq hpos t ht hlim hA, fun hE => ?_⟩
  · obtain ⟨h₁, h₂, h₃, h₄, h₅, -⟩ := fivePointOp_eq_and_selfAdjoint C hlam hq hpos ht
    refine ⟨h₁, h₂, h₃, h₄, h₅, fun y => ?_⟩
    rw [fivePointFn_eq]
    exact exp_mul_sinh_sin_form (t * lam y) (t * q y)
  · refine cone_of_null_ltAbsSet C U K (fun A sA g hg hA f hf => ?_) hlam hq hpos hE
    exact ((hS H A sA).2.2.2.2.2.2.1 n Y E g hg hA).2 f hf
end YangMills.Construction.FivePointCone
