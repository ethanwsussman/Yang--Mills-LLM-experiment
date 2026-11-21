import YangMills.Construction.PeriodicOperators.AdditivityAndIntegralOfTheLogarithmicNumber
import YangMills.Construction.PeriodicOperators.AlgebraOfQuadruples
import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.AssociativityAndNormOfProductsOfJets
import YangMills.Construction.PeriodicOperators.DerivativeOfTheLogarithmicNumberAlongAFamily
import YangMills.Construction.PeriodicOperators.InverseOfAnInvertibleJet
import YangMills.Construction.PeriodicOperators.JetsOfPeriodicOperatorsAndConstantParts
import YangMills.Construction.PeriodicOperators.NormsAndTracesOfMatricesOnTheClasses
import YangMills.Construction.PeriodicOperators.ProductsOfJets
import YangMills.Construction.PeriodicOperators.StripsAndFiniteNormsOfJets
import YangMills.Construction.PeriodicOperators.SumsAndMultiplesOfJets
import YangMills.Construction.Towers.FactsOfTheMatricesOfAPeriodicFunctionProof
import Mathlib
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace LogNumberDerivAlongFamily
open JetQuad
variable {P : PeriodicData}
private structure Ingredients (δ : ℝ) (q : Fin 4 → ℂ) (P : PeriodicData) : Prop where
  add_isJet : ∀ T S : JetQuad P P, IsJet δ q T → IsJet δ q S → IsJet δ q (add T S)
  smul_isJet : ∀ (z : ℂ) (T : JetQuad P P), IsJet δ q T → IsJet δ q (smul z T)
  mul_isJet : ∀ T S : JetQuad P P, IsJet δ q T → IsJet δ q S → IsJet δ q (mul q T S)
  one_isJet : IsJet δ q (one P)
  zeroPartInv_isJet : ∀ T : JetQuad P P, IsInvertibleJet δ q T → IsJet δ q (zeroPartInv T)
  jetNorm_lt_top : ∀ T : JetQuad P P, IsJet δ q T → jetNorm δ q T < ∞
  jetNorm_mul_le : ∀ T S : JetQuad P P, IsJet δ q T → IsJet δ q S →
    jetNorm δ q (mul q T S) ≤ jetNorm δ q T * jetNorm δ q S
  jetNorm_add_le : ∀ T S : JetQuad P P, IsJet δ q T → IsJet δ q S →
    jetNorm δ q (add T S) ≤ jetNorm δ q T + jetNorm δ q S
  traceNumber_add : ∀ T S : JetQuad P P, IsJet δ q T → IsJet δ q S →
    traceNumber (add T S) = traceNumber T + traceNumber S
  traceNumber_smul : ∀ (z : ℂ) (T : JetQuad P P), IsJet δ q T →
    traceNumber (smul z T) = z * traceNumber T
  real_mem_imStrip : ∀ κ ∈ realDualPoints, κ ∈ imStrip (2 * δ)
  addShift_mem_imStrip : ∀ κ ∈ stripAddShift δ q, κ + q ∈ imStrip (2 * δ)
  subShift_mem_imStrip : ∀ κ ∈ stripSubShift δ q, κ - q ∈ imStrip (2 * δ)
  quotHomNorm_comp_le : ∀ M N : QuotHom P P,
    quotHomNorm (M.comp N) ≤ quotHomNorm M * quotHomNorm N
  quotHomNorm_smul_le : ∀ (z : ℂ) (M : QuotHom P P),
    quotHomNorm (z • M) ≤ ENNReal.ofReal ‖z‖ * quotHomNorm M
  quotHomNorm_zero : quotHomNorm (0 : QuotHom P P) = 0
  trace_le_quotHomNorm : ∃ C : ℝ, 0 ≤ C ∧ ∀ M : QuotHom P P,
    ‖LinearMap.trace ℂ (P.UnitQuot → ℂ) M‖ ≤ C * (quotHomNorm M).toReal
  mulBilinear : QuadAlgebra.MulBilinearUnital q P P P
  mul_assoc_jet : ∀ T S R : JetQuad P P, IsJet δ q T → IsJet δ q S → IsJet δ q R →
    EqAsJet δ q (mul q (mul q T S) R) (mul q T (mul q S R))
  mul_congr_left : ∀ T T' S : JetQuad P P, IsJet δ q T → IsJet δ q T' → IsJet δ q S →
    EqAsJet δ q T T' → EqAsJet δ q (mul q T S) (mul q T' S)
  invJet_spec : ∀ T : JetQuad P P, IsInvertibleJet δ q T → IsJet δ q (invJet q T) ∧
    EqAsJet δ q (mul q (invJet q T) T) (one P) ∧ EqAsJet δ q (mul q T (invJet q T)) (one P)
  logNumber_mul : ∀ T S : JetQuad P P, IsInvertibleJet δ q T → IsInvertibleJet δ q S →
    IsInvertibleJet δ q (mul q T S) ∧
      logNumber q (mul q T S) = logNumber q T + logNumber q S
  logNumber_congr : ∀ T T' : JetQuad P P, IsJet δ q T' → EqAsJet δ q T T' →
    IsInvertibleJet δ q T → logNumber q T = logNumber q T'
section ComponentBounds
variable {δ : ℝ} {q : Fin 4 → ℂ}
private theorem f00_le_jetNorm (T : JetQuad P P) {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip (2 * δ)) :
    quotHomNorm (T.f00 κ) ≤ jetNorm δ q T := by
  unfold jetNorm
  refine le_trans ?_ (le_add_right (le_add_right (le_add_right le_rfl)))
  exact le_iSup₂ (f := fun κ (_ : κ ∈ imStrip (2 * δ)) => quotHomNorm (T.f00 κ)) κ hκ
private theorem f11_le_jetNorm (T : JetQuad P P) {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) :
    quotHomNorm (T.f11 κ) ≤ jetNorm δ q T := by
  unfold jetNorm
  refine le_trans ?_ (le_add_left le_rfl)
  exact le_iSup₂ (f := fun κ (_ : κ ∈ realDualPoints) => quotHomNorm (T.f11 κ)) κ hκ
private theorem f10_le_jetNorm (T : JetQuad P P) {κ : Fin 4 → ℂ} (hκ : κ ∈ stripAddShift δ q) :
    quotHomNorm (T.f10 κ) ≤ jetNorm δ q T := by
  unfold jetNorm
  refine le_trans ?_ (le_add_right (le_add_right (le_add_left le_rfl)))
  exact le_iSup₂ (f := fun κ (_ : κ ∈ stripAddShift δ q) => quotHomNorm (T.f10 κ)) κ hκ
private theorem f01_le_jetNorm (T : JetQuad P P) {κ : Fin 4 → ℂ} (hκ : κ ∈ stripSubShift δ q) :
    quotHomNorm (T.f01 κ) ≤ jetNorm δ q T := by
  unfold jetNorm
  refine le_trans ?_ (le_add_right (le_add_left le_rfl))
  exact le_iSup₂ (f := fun κ (_ : κ ∈ stripSubShift δ q) => quotHomNorm (T.f01 κ)) κ hκ
end ComponentBounds
private theorem normalize_f00 (q : Fin 4 → ℂ) (R : JetQuad P P) (κ : Fin 4 → ℂ) :
    (normalize q R).f00 κ =
      (quotHomInverse (R.f00 κ)).comp (R.f00 κ) + (-1 : ℂ) • LinearMap.id := by
  simp [JetQuad.normalize, add, smul, mul, zeroPartInv, one]
private theorem normalize_f10 (q : Fin 4 → ℂ) (R : JetQuad P P) (κ : Fin 4 → ℂ) :
    (normalize q R).f10 κ = (quotHomInverse (R.f00 (κ + q))).comp (R.f10 κ) := by
  simp [JetQuad.normalize, add, smul, mul, zeroPartInv, one]
private theorem normalize_f01 (q : Fin 4 → ℂ) (R : JetQuad P P) (κ : Fin 4 → ℂ) :
    (normalize q R).f01 κ = (quotHomInverse (R.f00 (κ - q))).comp (R.f01 κ) := by
  simp [JetQuad.normalize, add, smul, mul, zeroPartInv, one]
private theorem normalize_f11 (q : Fin 4 → ℂ) (R : JetQuad P P) (κ : Fin 4 → ℂ) :
    (normalize q R).f11 κ = (quotHomInverse (R.f00 κ)).comp (R.f11 κ) := by
  simp [JetQuad.normalize, add, smul, mul, zeroPartInv, one]
private theorem quotHomInverse_eq_of_comp {M N : QuotHom P P} (h₁ : M.comp N = LinearMap.id)
    (h₂ : N.comp M = LinearMap.id) : quotHomInverse M = N := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.quotHomInverse_eq_of_comp <;> assumption
private theorem quotHomInverse_comp_self {M : QuotHom P P}
    (h : IsUnit (M : Module.End ℂ (P.UnitQuot → ℂ))) :
    (quotHomInverse M).comp M = LinearMap.id :=
  Ring.inverse_mul_cancel _ h
private theorem comp_quotHomInverse_self {M : QuotHom P P}
    (h : IsUnit (M : Module.End ℂ (P.UnitQuot → ℂ))) :
    M.comp (quotHomInverse M) = LinearMap.id :=
  Ring.mul_inverse_cancel _ h
private theorem quotHomInverse_comp_of_inverses {a a' c ci : QuotHom P P}
    (h₁ : a.comp a' = LinearMap.id) (h₂ : a'.comp a = LinearMap.id)
    (h₃ : c.comp ci = LinearMap.id) (h₄ : ci.comp c = LinearMap.id) :
    quotHomInverse (a'.comp c) = ci.comp a := by
  apply quotHomInverse_eq_of_comp
  · refine LinearMap.ext fun x => ?_
    have e₃ := LinearMap.congr_fun h₃ (a x)
    have e₂ := LinearMap.congr_fun h₂ x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at e₃ e₂ ⊢
    rw [e₃, e₂]
  · refine LinearMap.ext fun x => ?_
    have e₁ := LinearMap.congr_fun h₁ (c x)
    have e₄ := LinearMap.congr_fun h₄ x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at e₁ e₄ ⊢
    rw [e₁, e₄]
private theorem add_neg_smul_add (Q X : JetQuad P P) : add (add Q (smul (-1) X)) X = Q := by
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;> simp only [add, smul, Pi.add_apply, Pi.smul_apply] <;>
    module
private theorem smul_smul_inv (X : JetQuad P P) {s : ℝ} (hs : s ≠ 0) :
    smul (s : ℂ) (smul ((s⁻¹ : ℝ) : ℂ) X) = X := by
  have hc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
    simp [smul, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hc]
section Bounds
variable {δ : ℝ} {q : Fin 4 → ℂ}
private theorem invJet_isInvertibleJet (F : Ingredients δ q P) {T : JetQuad P P}
    (hT : IsInvertibleJet δ q T) : IsInvertibleJet δ q (invJet q T) ∧
      ∀ κ ∈ imStrip (2 * δ), (T.f00 κ).comp ((invJet q T).f00 κ) = LinearMap.id ∧
        ((invJet q T).f00 κ).comp (T.f00 κ) = LinearMap.id := by
  obtain ⟨hj, h₁, h₂⟩ := F.invJet_spec T hT
  have hpair : ∀ κ ∈ imStrip (2 * δ), (T.f00 κ).comp ((invJet q T).f00 κ) = LinearMap.id ∧
      ((invJet q T).f00 κ).comp (T.f00 κ) = LinearMap.id :=
    fun κ hκ => ⟨h₂.1 hκ, h₁.1 hκ⟩
  refine ⟨⟨hj, fun κ hκ => ?_, ?_⟩, hpair⟩
  · let u : (Module.End ℂ (P.UnitQuot → ℂ))ˣ :=
      ⟨(invJet q T).f00 κ, T.f00 κ, (hpair κ hκ).2, (hpair κ hκ).1⟩
    exact u.isUnit
  · refine lt_of_le_of_lt (iSup₂_le fun κ hκ => ?_) (F.jetNorm_lt_top T hT.isJet)
    rw [quotHomInverse_eq_of_comp (hpair κ hκ).2 (hpair κ hκ).1]
    exact f00_le_jetNorm T hκ
private theorem traceNumber_le_of_f11 (F : Ingredients δ q P) : ∃ c : ℝ, 0 ≤ c ∧
    ∀ (X : JetQuad P P) (b : ℝ), 0 ≤ b →
      (∀ κ ∈ realDualPoints, quotHomNorm (X.f11 κ) ≤ ENNReal.ofReal b) →
        ‖traceNumber X‖ ≤ c * b := by
  obtain ⟨C, hC0, hC⟩ := F.trace_le_quotHomNorm
  set s : Set (Fin 4 → ℝ) := Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi) with hs
  refine ⟨‖(((((2 * Real.pi) ^ 4)⁻¹ : ℝ)) : ℂ)‖ * (C * volume.real s), by positivity,
    fun X b hb h => ?_⟩
  have hint : ‖∫ κ in s, LinearMap.trace ℂ (P.UnitQuot → ℂ) (X.f11 (toComplexVec κ))‖ ≤
      (C * b) * volume.real s := by
    refine norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top fun κ _ => ?_
    refine (hC _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    exact ENNReal.toReal_le_of_le_ofReal hb (h _ fun μ => Complex.ofReal_im (κ μ))
  unfold traceNumber torusAverage
  rw [norm_mul]
  calc _ ≤ ‖(((((2 * Real.pi) ^ 4)⁻¹ : ℝ)) : ℂ)‖ * ((C * b) * volume.real s) := by
        gcongr
    _ = _ := by ring
private theorem quotHomNorm_comp_smul_le (F : Ingredients δ q P) {M N : QuotHom P P} (z : ℂ)
    {b w : ℝ} (hb : 0 ≤ b) (hM : quotHomNorm M ≤ ENNReal.ofReal b)
    (hN : quotHomNorm N ≤ ENNReal.ofReal w) :
    quotHomNorm (M.comp (z • N)) ≤ ENNReal.ofReal (‖z‖ * b * w) := by
  calc quotHomNorm (M.comp (z • N)) ≤ quotHomNorm M * quotHomNorm (z • N) :=
        F.quotHomNorm_comp_le _ _
    _ ≤ ENNReal.ofReal b * (ENNReal.ofReal ‖z‖ * ENNReal.ofReal w) := by
        gcongr
        exact (F.quotHomNorm_smul_le z N).trans (by gcongr)
    _ = ENNReal.ofReal (‖z‖ * b * w) := by
        rw [← ENNReal.ofReal_mul (norm_nonneg z), ← ENNReal.ofReal_mul hb]
        congr 1
        ring
private theorem norm_logNumber_sub_le (F : Ingredients δ q P) {c : ℝ} (_hc0 : 0 ≤ c)
    (hc : ∀ (X : JetQuad P P) (b : ℝ), 0 ≤ b →
      (∀ κ ∈ realDualPoints, quotHomNorm (X.f11 κ) ≤ ENNReal.ofReal b) →
        ‖traceNumber X‖ ≤ c * b)
    {R W : JetQuad P P} (hR : IsInvertibleJet δ q R) (hW : IsJet δ q W) (z : ℂ) {b w : ℝ}
    (hb : 0 ≤ b) (hw : 0 ≤ w) (hWn : jetNorm δ q W ≤ ENNReal.ofReal w)
    (hinv : ∀ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (R.f00 κ)) ≤ ENNReal.ofReal b)
    (h00 : ∀ κ ∈ imStrip (2 * δ), R.f00 κ = LinearMap.id + z • W.f00 κ)
    (h10 : ∀ κ ∈ stripAddShift δ q, R.f10 κ = z • W.f10 κ)
    (h01 : ∀ κ ∈ stripSubShift δ q, R.f01 κ = z • W.f01 κ)
    (h11 : ∀ κ ∈ realDualPoints, R.f11 κ = z • W.f11 κ) :
    ‖logNumber q R - z * traceNumber W‖ ≤
      c * (‖z‖ ^ 2 * (b * w * w)) + 1 / 2 * (c * (3 * (‖z‖ * b * w)) ^ 2) := by
  have hRj := hR.isJet
  have hK := F.zeroPartInv_isJet R hR
  have hN : IsJet δ q (normalize q R) :=
    F.add_isJet _ _ (F.mul_isJet _ _ hK hRj) (F.smul_isJet _ _ F.one_isJet)
  have hN2 := F.mul_isJet _ _ hN hN
  have hx : 0 ≤ ‖z‖ * b * w := by positivity
  have hNn : jetNorm δ q (normalize q R) ≤ ENNReal.ofReal (3 * (‖z‖ * b * w)) := by
    have e00 : (⨆ κ ∈ imStrip (2 * δ), quotHomNorm ((normalize q R).f00 κ)) ≤ 0 := by
      refine iSup₂_le fun κ hκ => ?_
      rw [normalize_f00, quotHomInverse_comp_self (hR.isUnit_f00 κ hκ)]
      have : (LinearMap.id + (-1 : ℂ) • LinearMap.id : QuotHom P P) = 0 := by
        refine LinearMap.ext fun x => ?_
        simp
      rw [this, F.quotHomNorm_zero]
    have e10 : (⨆ κ ∈ stripAddShift δ q, quotHomNorm ((normalize q R).f10 κ)) ≤
        ENNReal.ofReal (‖z‖ * b * w) := by
      refine iSup₂_le fun κ hκ => ?_
      rw [normalize_f10, h10 κ hκ]
      exact quotHomNorm_comp_smul_le F z hb (hinv _ (F.addShift_mem_imStrip κ hκ))
        ((f10_le_jetNorm W hκ).trans hWn)
    have e01 : (⨆ κ ∈ stripSubShift δ q, quotHomNorm ((normalize q R).f01 κ)) ≤
        ENNReal.ofReal (‖z‖ * b * w) := by
      refine iSup₂_le fun κ hκ => ?_
      rw [normalize_f01, h01 κ hκ]
      exact quotHomNorm_comp_smul_le F z hb (hinv _ (F.subShift_mem_imStrip κ hκ))
        ((f01_le_jetNorm W hκ).trans hWn)
    have e11 : (⨆ κ ∈ realDualPoints, quotHomNorm ((normalize q R).f11 κ)) ≤
        ENNReal.ofReal (‖z‖ * b * w) := by
      refine iSup₂_le fun κ hκ => ?_
      rw [normalize_f11, h11 κ hκ]
      exact quotHomNorm_comp_smul_le F z hb (hinv _ (F.real_mem_imStrip κ hκ))
        ((f11_le_jetNorm W hκ).trans hWn)
    unfold jetNorm
    calc _ ≤ 0 + ENNReal.ofReal (‖z‖ * b * w) + ENNReal.ofReal (‖z‖ * b * w) +
          ENNReal.ofReal (‖z‖ * b * w) := by gcongr
      _ = ENNReal.ofReal (3 * (‖z‖ * b * w)) := by
        rw [zero_add, ← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add (by positivity) hx]
        congr 1
        ring
  have ht2 : ‖traceNumber (mul q (normalize q R) (normalize q R))‖ ≤
      c * (3 * (‖z‖ * b * w)) ^ 2 := by
    refine hc _ _ (by positivity) fun κ hκ => ?_
    refine (f11_le_jetNorm (δ := δ) (q := q) _ hκ).trans
      ((F.jetNorm_mul_le _ _ hN hN).trans ?_)
    calc _ ≤ ENNReal.ofReal (3 * (‖z‖ * b * w)) * ENNReal.ofReal (3 * (‖z‖ * b * w)) := by
          gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have ht1 : ‖traceNumber (add (normalize q R) (smul (-z) W))‖ ≤
      c * (‖z‖ ^ 2 * (b * w * w)) := by
    refine hc _ _ (by positivity) fun κ hκ => ?_
    have hs := F.real_mem_imStrip κ hκ
    have hid : (quotHomInverse (R.f00 κ)).comp (LinearMap.id + z • W.f00 κ) = LinearMap.id := by
      rw [← h00 κ hs]
      exact quotHomInverse_comp_self (hR.isUnit_f00 κ hs)
    have e : (quotHomInverse (R.f00 κ)).comp (W.f11 κ) + z •
        (quotHomInverse (R.f00 κ)).comp ((W.f00 κ).comp (W.f11 κ)) = W.f11 κ := by
      refine LinearMap.ext fun x => ?_
      have := LinearMap.congr_fun hid (W.f11 κ x)
      simpa [LinearMap.comp_apply, map_add, map_smul] using this
    have hform : (add (normalize q R) (smul (-z) W)).f11 κ =
        (-(z * z)) • (quotHomInverse (R.f00 κ)).comp ((W.f00 κ).comp (W.f11 κ)) := by
      show (normalize q R).f11 κ + (-z) • W.f11 κ = _
      rw [normalize_f11, h11 κ hκ, LinearMap.comp_smul]
      calc z • (quotHomInverse (R.f00 κ)).comp (W.f11 κ) + (-z) • W.f11 κ
          = z • (quotHomInverse (R.f00 κ)).comp (W.f11 κ) +
            (-z) • ((quotHomInverse (R.f00 κ)).comp (W.f11 κ) + z •
              (quotHomInverse (R.f00 κ)).comp ((W.f00 κ).comp (W.f11 κ))) := by rw [e]
        _ = _ := by module
    rw [hform]
    have hW0 : quotHomNorm (W.f00 κ) ≤ ENNReal.ofReal w := (f00_le_jetNorm W hs).trans hWn
    have hW1 : quotHomNorm (W.f11 κ) ≤ ENNReal.ofReal w := (f11_le_jetNorm W hκ).trans hWn
    calc _ ≤ ENNReal.ofReal ‖-(z * z)‖ * quotHomNorm
          ((quotHomInverse (R.f00 κ)).comp ((W.f00 κ).comp (W.f11 κ))) :=
          F.quotHomNorm_smul_le _ _
      _ ≤ ENNReal.ofReal ‖-(z * z)‖ *
          (ENNReal.ofReal b * (ENNReal.ofReal w * ENNReal.ofReal w)) := by
          gcongr
          exact (F.quotHomNorm_comp_le _ _).trans (mul_le_mul' (hinv κ hs)
            ((F.quotHomNorm_comp_le _ _).trans (mul_le_mul' hW0 hW1)))
      _ = ENNReal.ofReal (‖z‖ ^ 2 * (b * w * w)) := by
          rw [← ENNReal.ofReal_mul hw, ← ENNReal.ofReal_mul hb,
            ← ENNReal.ofReal_mul (norm_nonneg _)]
          congr 1
          rw [norm_neg, norm_mul]
          ring
  have hsplit : logNumber q R - z * traceNumber W =
      traceNumber (add (normalize q R) (smul (-z) W)) +
        (-(1 / 2) : ℂ) * traceNumber (mul q (normalize q R) (normalize q R)) := by
    rw [F.traceNumber_add _ _ hN (F.smul_isJet _ _ hW), F.traceNumber_smul _ _ hW]
    unfold logNumber logSeries
    rw [F.traceNumber_add _ _ hN (F.smul_isJet _ _ hN2), F.traceNumber_smul _ _ hN2]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ht1 ?_)
  rw [norm_mul]
  have : ‖(-(1 / 2) : ℂ)‖ = 1 / 2 := by simp
  rw [this]
  gcongr
private def diffQuotBound (c b a e m r : ℝ) : ℝ :=
  |r| * (c * (b * (a * e + m) * (a * e + m)) + 1 / 2 * (c * (3 * (b * (a * e + m))) ^ 2)) +
    c * (a * e)
private theorem norm_diffQuot_sub_le (F : Ingredients δ q P) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ (X : JetQuad P P) (b : ℝ), 0 ≤ b →
      (∀ κ ∈ realDualPoints, quotHomNorm (X.f11 κ) ≤ ENNReal.ofReal b) →
        ‖traceNumber X‖ ≤ c * b)
    {T₀ T' Td Q D : JetQuad P P} (h₀ : IsInvertibleJet δ q T₀) (h' : IsInvertibleJet δ q T')
    (hTd : IsJet δ q Td) {r : ℝ} (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hinv : ∀ κ ∈ imStrip (2 * δ),
      quotHomNorm (quotHomInverse (T'.f00 κ)) * jetNorm δ q T₀ ≤ ENNReal.ofReal b)
    (hQ : Q = smul ((r⁻¹ : ℝ) : ℂ) (add T' (smul (-1) T₀)))
    (hD : D = add Q (smul (-1) Td)) :
    ‖((r⁻¹ : ℝ) : ℂ) * (logNumber q T' - logNumber q T₀) -
        traceNumber (mul q (invJet q T₀) Td)‖ ≤
      diffQuotBound c b (jetNorm δ q (invJet q T₀)).toReal (jetNorm δ q D).toReal
        (jetNorm δ q (mul q (invJet q T₀) Td)).toReal r := by
  obtain ⟨hTi, hTiT, hTTi⟩ := F.invJet_spec T₀ h₀
  have hT₀ := h₀.isJet
  have hT' := h'.isJet
  have hQj : IsJet δ q Q := by
    rw [hQ]
    exact F.smul_isJet _ _ (F.add_isJet _ _ hT' (F.smul_isJet _ _ hT₀))
  have hDj : IsJet δ q D := by
    rw [hD]
    exact F.add_isJet _ _ hQj (F.smul_isJet _ _ hTd)
  have hMj := F.mul_isJet _ _ hTi hTd
  have hEj := F.mul_isJet _ _ hTi hDj
  have hWj := F.mul_isJet _ _ hTi hQj
  have hQD : add D Td = Q := by
    rw [hD]
    exact add_neg_smul_add Q Td
  have hWE : mul q (invJet q T₀) Q =
      add (mul q (invJet q T₀) D) (mul q (invJet q T₀) Td) := by
    rw [← hQD]
    exact F.mulBilinear.2.1 _ _ _
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
  have hsQ : smul (r : ℂ) Q = add T' (smul (-1) T₀) := by
    rw [hQ]
    exact smul_smul_inv _ hr
  have key : smul (r : ℂ) (mul q (invJet q T₀) Q) =
      add (mul q (invJet q T₀) T') (smul (-1) (mul q (invJet q T₀) T₀)) := by
    rw [← F.mulBilinear.2.2.2.1, hsQ, F.mulBilinear.2.1, F.mulBilinear.2.2.2.1]
  have hinvT := invJet_isInvertibleJet F h₀
  have hRinv := (F.logNumber_mul _ _ hinvT.1 h').1
  have h00 : ∀ κ ∈ imStrip (2 * δ), (mul q (invJet q T₀) T').f00 κ =
      LinearMap.id + (r : ℂ) • (mul q (invJet q T₀) Q).f00 κ := by
    intro κ hκ
    have e := congrFun (congrArg JetQuad.f00 key) κ
    have e1 : (mul q (invJet q T₀) T₀).f00 κ = LinearMap.id := hTiT.1 hκ
    simp only [smul, add, Pi.add_apply, Pi.smul_apply] at e
    rw [e, e1]
    module
  have h10 : ∀ κ ∈ stripAddShift δ q, (mul q (invJet q T₀) T').f10 κ =
      (r : ℂ) • (mul q (invJet q T₀) Q).f10 κ := by
    intro κ hκ
    have e := congrFun (congrArg JetQuad.f10 key) κ
    have e1 : (mul q (invJet q T₀) T₀).f10 κ = 0 := hTiT.2.1 hκ
    simp only [smul, add, Pi.add_apply, Pi.smul_apply] at e
    rw [e, e1]
    module
  have h01 : ∀ κ ∈ stripSubShift δ q, (mul q (invJet q T₀) T').f01 κ =
      (r : ℂ) • (mul q (invJet q T₀) Q).f01 κ := by
    intro κ hκ
    have e := congrFun (congrArg JetQuad.f01 key) κ
    have e1 : (mul q (invJet q T₀) T₀).f01 κ = 0 := hTiT.2.2.1 hκ
    simp only [smul, add, Pi.add_apply, Pi.smul_apply] at e
    rw [e, e1]
    module
  have h11 : ∀ κ ∈ realDualPoints, (mul q (invJet q T₀) T').f11 κ =
      (r : ℂ) • (mul q (invJet q T₀) Q).f11 κ := by
    intro κ hκ
    have e := congrFun (congrArg JetQuad.f11 key) κ
    have e1 : (mul q (invJet q T₀) T₀).f11 κ = 0 := hTiT.2.2.2 hκ
    simp only [smul, add, Pi.add_apply, Pi.smul_apply] at e
    rw [e, e1]
    module
  have hbinv : ∀ κ ∈ imStrip (2 * δ),
      quotHomNorm (quotHomInverse ((mul q (invJet q T₀) T').f00 κ)) ≤ ENNReal.ofReal b := by
    intro κ hκ
    have e : quotHomInverse ((mul q (invJet q T₀) T').f00 κ) =
        (quotHomInverse (T'.f00 κ)).comp (T₀.f00 κ) :=
      quotHomInverse_comp_of_inverses (hinvT.2 κ hκ).1 (hinvT.2 κ hκ).2
        (comp_quotHomInverse_self (h'.isUnit_f00 κ hκ))
        (quotHomInverse_comp_self (h'.isUnit_f00 κ hκ))
    rw [e]
    exact (F.quotHomNorm_comp_le _ _).trans
      ((mul_le_mul' le_rfl (f00_le_jetNorm T₀ hκ)).trans (hinv κ hκ))
  have ha := (F.jetNorm_lt_top _ hTi).ne
  have he := (F.jetNorm_lt_top _ hDj).ne
  have hm := (F.jetNorm_lt_top _ hMj).ne
  set a := (jetNorm δ q (invJet q T₀)).toReal with ha'
  set e := (jetNorm δ q D).toReal with he'
  set m := (jetNorm δ q (mul q (invJet q T₀) Td)).toReal with hm'
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hEn : jetNorm δ q (mul q (invJet q T₀) D) ≤ ENNReal.ofReal (a * e) := by
    rw [ENNReal.ofReal_mul ha0, ha', he', ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal he]
    exact F.jetNorm_mul_le _ _ hTi hDj
  have hWn : jetNorm δ q (mul q (invJet q T₀) Q) ≤ ENNReal.ofReal (a * e + m) := by
    rw [hWE, ENNReal.ofReal_add (by positivity) hm0, hm', ENNReal.ofReal_toReal hm]
    exact (F.jetNorm_add_le _ _ hEj hMj).trans (by gcongr)
  have hw0 : 0 ≤ a * e + m := by positivity
  have hcore :=
    norm_logNumber_sub_le F hc0 hc hRinv hWj (r : ℂ) hb hw0 hWn hbinv h00 h10 h01 h11
  have htE : ‖traceNumber (mul q (invJet q T₀) D)‖ ≤ c * (a * e) :=
    hc _ _ (by positivity) fun κ hκ => (f11_le_jetNorm _ hκ).trans hEn
  have htW : traceNumber (mul q (invJet q T₀) Q) =
      traceNumber (mul q (invJet q T₀) D) + traceNumber (mul q (invJet q T₀) Td) := by
    rw [hWE]
    exact F.traceNumber_add _ _ hEj hMj
  have hell : logNumber q T' =
      logNumber q T₀ + logNumber q (mul q (invJet q T₀) T') := by
    obtain ⟨hinv2, hadd⟩ := F.logNumber_mul _ _ h₀ hRinv
    rw [← hadd]
    symm
    refine F.logNumber_congr _ _ hT' ?_ hinv2
    have e₁ := F.mul_assoc_jet _ _ _ hT₀ hTi hT'
    have e₂ := F.mul_congr_left _ _ T' (F.mul_isJet _ _ hT₀ hTi) F.one_isJet hT' hTTi
    have e₃ : mul q (one P) T' = T' := (F.mulBilinear.2.2.2.2 T').1
    rw [e₃] at e₂
    exact ⟨e₁.1.symm.trans e₂.1, e₁.2.1.symm.trans e₂.2.1, e₁.2.2.1.symm.trans e₂.2.2.1,
      e₁.2.2.2.symm.trans e₂.2.2.2⟩
  have hirc : ((r⁻¹ : ℝ) : ℂ) * (r : ℂ) = 1 := by
    rw [Complex.ofReal_inv]
    exact inv_mul_cancel₀ hrc
  have hrew : ((r⁻¹ : ℝ) : ℂ) * (logNumber q T' - logNumber q T₀) -
        traceNumber (mul q (invJet q T₀) Td) =
      ((r⁻¹ : ℝ) : ℂ) * (logNumber q (mul q (invJet q T₀) T') -
          (r : ℂ) * traceNumber (mul q (invJet q T₀) Q)) +
        traceNumber (mul q (invJet q T₀) D) := by
    rw [hell, htW]
    linear_combination (traceNumber (mul q (invJet q T₀) D) +
      traceNumber (mul q (invJet q T₀) Td)) * hirc
  rw [hrew]
  refine (norm_add_le _ _).trans ?_
  unfold diffQuotBound
  refine add_le_add ?_ htE
  rw [norm_mul]
  have hnr : ‖(r : ℂ)‖ = |r| := Complex.norm_real r
  have hni : ‖((r⁻¹ : ℝ) : ℂ)‖ = |r|⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_inv]
  rw [hni]
  rw [hnr] at hcore
  calc _ ≤ |r|⁻¹ * (c * (|r| ^ 2 * (b * (a * e + m) * (a * e + m))) +
        1 / 2 * (c * (3 * (|r| * b * (a * e + m))) ^ 2)) := by gcongr
    _ = _ := by
      field_simp
end Bounds
private theorem diffQuotBound_tendsto (c b a m : ℝ) {L : Filter ℝ} {e : ℝ → ℝ}
    (he : Tendsto e L (𝓝 0)) (hid : Tendsto (fun r : ℝ => r) L (𝓝 0)) :
    Tendsto (fun r => diffQuotBound c b a (e r) m r) L (𝓝 0) := by
  have hcont : Continuous fun x : ℝ × ℝ => diffQuotBound c b a x.1 m x.2 := by
    unfold diffQuotBound
    fun_prop
  have := (hcont.tendsto (0, 0)).comp (he.prodMk_nhds hid)
  simpa [diffQuotBound, Function.comp_def] using this
end LogNumberDerivAlongFamily
open LogNumberDerivAlongFamily JetQuad in
theorem LogNumberDerivAlongFamily.holds
    (hAlg : QuadAlgebra.Claim)
    (hMat : QuotMatrixNorms.Claim)
    (hInv : JetInverse.Claim)
    (hLog : JetLogNumber.Claim)
    (hProd : JetProductsAssocAndNormLe)
    (hArg : JetArgumentsAndEqualJets)
    (hFin : StripJetNorms.Claim)
    (hSum : JetAddSMul.Claim)
    (hPr : JetProducts.Claim)
    (hCst : ZeroPartJets.Claim) :
    LogNumberDerivAlongFamily.Claim := by
  intro δ q hδ hq P hP A _ _ T Tdot hinv hjet hfam hC t ht
  obtain ⟨C, hCf, hC⟩ := hC
  have hNJ := hAlg.2 δ q hδ hq P P hP hP
  have hM := hMat P P P hP hP hP
  have hArgs := hArg.1 δ q hδ hq
  have hS := hFin P P hP hP δ q hδ hq
  have hSm := hSum P P hP hP δ q hδ hq
  have hCs := hCst P P hP hP δ q hδ hq
  have hEq := hArg.2.1 δ q P P hP hP
  have F : Ingredients δ q P :=
    { add_isJet := hSm.2.1
      smul_isJet := hSm.2.2.2
      mul_isJet := (hPr P P P hP hP hP δ q hδ hq).2
      one_isJet := hCs.2.1
      zeroPartInv_isJet := fun T hT => (hCs.2.2 T hT).2.1
      jetNorm_lt_top := fun T hT => by
        obtain ⟨a, b, c, d⟩ := hS.2 T hT
        unfold jetNorm
        exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨a, b⟩, c⟩, d⟩
      jetNorm_mul_le := fun T S hT hS' => by
        obtain ⟨_, h⟩ := hProd δ q hδ hq P P P P hP hP hP hP T S S hT hS' hS'
        exact h
      jetNorm_add_le := hNJ.1
      traceNumber_add := hNJ.2.2.2.1
      traceNumber_smul := hNJ.2.2.2.2
      real_mem_imStrip := fun κ hκ => (hArgs.1.mem_real κ hκ).1.1.1
      addShift_mem_imStrip := fun κ hκ => (hArgs.1.mem_addShift κ hκ).2.1
      subShift_mem_imStrip := fun κ hκ => (hArgs.1.mem_subShift κ hκ).2.1
      quotHomNorm_comp_le := hM.2.1
      quotHomNorm_smul_le := hM.1.2.2.1
      quotHomNorm_zero := hM.1.2.2.2.1
      trace_le_quotHomNorm := hM.2.2.2
      mulBilinear := hAlg.1 q P P P
      mul_assoc_jet := fun T S R hT hS' hR =>
        (hProd δ q hδ hq P P P P hP hP hP hP T S R hT hS' hR).1
      mul_congr_left := fun T T' S hT hT' hS' e =>
        (hEq T T' hT hT' e).2.2.2.2 P hP S S hS' hS'
          ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
      invJet_spec := fun T hT => by
        obtain ⟨a, b, c, _⟩ := hInv δ q hδ hq P hP T hT
        exact ⟨a, b, c⟩
      logNumber_mul := (hLog δ q hδ hq P hP).1
      logNumber_congr := fun T T' hT' e hT =>
        ((hArg.2.2 δ q P hP T T' hT.isJet hT' e).2 hT).2.2.2 }
  obtain ⟨c, hc0, hc⟩ := traceNumber_le_of_f11 F
  have hT₀ := hinv t ht
  have hbfin : C * jetNorm δ q (T t) ≠ ∞ :=
    ENNReal.mul_ne_top hCf.ne (F.jetNorm_lt_top _ hT₀.isJet).ne
  have hq' : ∀ r : ℝ, r ∈ {r : ℝ | r ≠ 0 ∧ t + r ∈ A} →
      ‖((r⁻¹ : ℝ) : ℂ) * (logNumber q (T (t + r)) - logNumber q (T t)) -
          traceNumber (mul q (invJet q (T t)) (Tdot t))‖ ≤
        diffQuotBound c (C * jetNorm δ q (T t)).toReal (jetNorm δ q (invJet q (T t))).toReal
          (jetNorm δ q (add (smul ((r⁻¹ : ℝ) : ℂ) (add (T (t + r)) (smul (-1) (T t))))
            (smul (-1) (Tdot t)))).toReal
          (jetNorm δ q (mul q (invJet q (T t)) (Tdot t))).toReal r := by
    intro r hr
    refine norm_diffQuot_sub_le F hc0 hc hT₀ (hinv _ hr.2) (hjet t ht) hr.1
      ENNReal.toReal_nonneg (fun κ hκ => ?_) rfl rfl
    rw [ENNReal.ofReal_toReal hbfin]
    refine mul_le_mul' (le_trans ?_ (hC _ hr.2)) le_rfl
    exact le_iSup₂ (f := fun κ (_ : κ ∈ imStrip (2 * δ)) =>
      quotHomNorm (quotHomInverse ((T (t + r)).f00 κ))) κ hκ
  have he := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hfam t ht).1
  rw [ENNReal.toReal_zero] at he
  have hbound := diffQuotBound_tendsto c (C * jetNorm δ q (T t)).toReal
    (jetNorm δ q (invJet q (T t))).toReal
    (jetNorm δ q (mul q (invJet q (T t)) (Tdot t))).toReal he
    (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hmain : Tendsto (fun r : ℝ => ((r⁻¹ : ℝ) : ℂ) *
        (logNumber q (T (t + r)) - logNumber q (T t)))
      (𝓝[{r : ℝ | r ≠ 0 ∧ t + r ∈ A}] 0)
      (𝓝 (traceNumber (mul q (invJet q (T t)) (Tdot t)))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hq' r hr
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hmap : Tendsto (fun s : ℝ => s - t) (𝓝[A \ {t}] t)
      (𝓝[{r : ℝ | r ≠ 0 ∧ t + r ∈ A}] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 (t - t)) :=
        (continuous_id.sub continuous_const).tendsto t
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact ⟨sub_ne_zero.2 hs.2, by simpa using hs.1⟩
  refine (hmain.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s _
  simp [slope, Complex.real_smul]
end YangMills.Construction.PeriodicOperators
end
