import YangMills.Construction.Gaussian.KernelGaussianIntegral
import YangMills.Construction.Towers.GaussianNumberThroughTwoSaddleDeterminants
import YangMills.Construction.Towers.TheSaddleDeterminant
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.GaussianConstraint.TwoSaddleProof
open LinearMap (ker range adjoint)
section AbsoluteDeterminant
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma absDet_eq_abs_det (hM : AbsDetIndependentOfBases) (f : V →ₗ[ℝ] V)
    (hf : Function.Bijective f) :
    absDet f = |LinearMap.det f| := by
  rw [← hM V V f hf (Fin (Module.finrank ℝ V)) (stdOrthonormalBasis ℝ V) (stdOrthonormalBasis ℝ V),
    absDetInBases, LinearMap.det_toMatrix]
lemma endo_bijective_of_det_ne_zero (f : V →ₗ[ℝ] V) (hf : LinearMap.det f ≠ 0) :
    Function.Bijective f :=
  (Module.End.isUnit_iff f).1
    ((LinearMap.isUnit_iff_isUnit_det f).2 (isUnit_iff_ne_zero.2 hf))
end AbsoluteDeterminant
section Setup
variable {A C G Gc : Type} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup Gc] [InnerProductSpace ℝ Gc] [FiniteDimensional ℝ Gc]
lemma gauge_apply_mem_ker {D : G →ₗ[ℝ] A} {Dc : Gc →ₗ[ℝ] C} {Q : A →ₗ[ℝ] C} {r : G →ₗ[ℝ] Gc}
    (hQD : Q ∘ₗ D = Dc ∘ₗ r) (κ : ker r) : D κ ∈ ker Q := by
  have h : Q (D κ) = Dc (r κ) := LinearMap.congr_fun hQD κ
  have hκ : r κ = 0 := κ.2
  rw [LinearMap.mem_ker, h, hκ, map_zero]
lemma exists_decomp_ker {D : G →ₗ[ℝ] A} {Dc : Gc →ₗ[ℝ] C} {Q : A →ₗ[ℝ] C} {r : G →ₗ[ℝ] Gc}
    (hQD : Q ∘ₗ D = Dc ∘ₗ r) (Lf : ker Q →ₗ[ℝ] ker r) (v : ker r →ₗ[ℝ] ker r)
    (hv : ∀ (κ : ker r) (h : D κ ∈ ker Q), v κ = Lf ⟨D κ, h⟩) (hvb : Function.Bijective v)
    (B : ker Q) :
    ∃ (κ : ker r) (B₀ : ker Q), B = B₀ + ⟨D κ, gauge_apply_mem_ker hQD κ⟩ ∧ Lf B₀ = 0 := by
  obtain ⟨κ, hκ⟩ := hvb.2 (Lf B)
  refine ⟨κ, B - ⟨D κ, gauge_apply_mem_ker hQD κ⟩, by abel, ?_⟩
  rw [map_sub, ← hv κ (gauge_apply_mem_ker hQD κ), hκ, sub_self]
lemma form_nonneg_and_eq_zero_iff {D : G →ₗ[ℝ] A} {Dc : Gc →ₗ[ℝ] C} {Q : A →ₗ[ℝ] C}
    {r : G →ₗ[ℝ] Gc}
    (hQD : Q ∘ₗ D = Dc ∘ₗ r) (H T : QuadraticForm ℝ (ker Q)) (Lf : ker Q →ₗ[ℝ] ker r)
    (v : ker r →ₗ[ℝ] ker r)
    (hinv : ∀ (B : ker Q) (κ : ker r) (h : D κ ∈ ker Q), H (B + ⟨D κ, h⟩) = H B)
    (hT : ∀ B : ker Q, T B = H B + ‖Lf B‖ ^ 2) (hTpos : T.PosDef)
    (hv : ∀ (κ : ker r) (h : D κ ∈ ker Q), v κ = Lf ⟨D κ, h⟩) (hvb : Function.Bijective v)
    (B : ker Q) : 0 ≤ H B ∧ (H B = 0 ↔ ∃ κ : ker r, (B : A) = D κ) := by
  obtain ⟨κ, B₀, rfl, h0⟩ := exists_decomp_ker hQD Lf v hv hvb B
  have hB₀ : T B₀ = H B₀ := by rw [hT, h0]; simp
  refine ⟨by rw [hinv, ← hB₀]; exact hTpos.nonneg B₀, ?_, ?_⟩
  · intro hz
    rw [hinv, ← hB₀] at hz
    have hzero : B₀ = 0 := by
      by_contra hne
      exact (hTpos B₀ hne).ne' hz
    exact ⟨κ, by simp [hzero]⟩
  · rintro ⟨κ', hκ'⟩
    have hB : B₀ + ⟨D κ, gauge_apply_mem_ker hQD κ⟩ = 0 + ⟨D κ', gauge_apply_mem_ker hQD κ'⟩ :=
      Subtype.ext (by simpa using hκ')
    rw [hB, hinv, map_zero]
def projOffGauge (D : G →ₗ[ℝ] A) (Q : A →ₗ[ℝ] C) (r : G →ₗ[ℝ] Gc) (g : C →ₗ[ℝ] Gc) :
    A →ₗ[ℝ] A :=
  LinearMap.id - D ∘ₗ adjoint r ∘ₗ g ∘ₗ Q
lemma projOffGauge_apply (D : G →ₗ[ℝ] A) (Q : A →ₗ[ℝ] C) (r : G →ₗ[ℝ] Gc) (g : C →ₗ[ℝ] Gc)
    (x : A) :
    projOffGauge D Q r g x = x - D (adjoint r (g (Q x))) := rfl
lemma projOffGauge_mem {D : G →ₗ[ℝ] A} {Dc : Gc →ₗ[ℝ] C} {Q : A →ₗ[ℝ] C} {r : G →ₗ[ℝ] Gc}
    {g : C →ₗ[ℝ] Gc} (hg : g ∘ₗ Dc = LinearMap.id) (hQD : Q ∘ₗ D = Dc ∘ₗ r)
    (hrr : r ∘ₗ adjoint r = LinearMap.id) (x : constraintPreimage Q Dc) :
    projOffGauge D Q r g x ∈ ker Q := by
  obtain ⟨y, hy⟩ : Q (x : A) ∈ range Dc := x.2
  have h1 : g (Q x) = y := by rw [← hy]; exact LinearMap.congr_fun hg y
  have h2 : Q (D (adjoint r y)) = Dc (r (adjoint r y)) := LinearMap.congr_fun hQD _
  have h3 : r (adjoint r y) = y := LinearMap.congr_fun hrr y
  rw [LinearMap.mem_ker, projOffGauge_apply, h1, map_sub, h2, h3, hy, sub_self]
def toKerConstraint {D : G →ₗ[ℝ] A} {Dc : Gc →ₗ[ℝ] C} {Q : A →ₗ[ℝ] C} {r : G →ₗ[ℝ] Gc}
    {g : C →ₗ[ℝ] Gc} (hg : g ∘ₗ Dc = LinearMap.id) (hQD : Q ∘ₗ D = Dc ∘ₗ r)
    (hrr : r ∘ₗ adjoint r = LinearMap.id) : constraintPreimage Q Dc →ₗ[ℝ] ker Q :=
  LinearMap.codRestrict _ (projOffGauge D Q r g ∘ₗ Submodule.subtype _)
    (projOffGauge_mem hg hQD hrr)
lemma toKerConstraint_coe {D : G →ₗ[ℝ] A} {Dc : Gc →ₗ[ℝ] C} {Q : A →ₗ[ℝ] C} {r : G →ₗ[ℝ] Gc}
    {g : C →ₗ[ℝ] Gc} (hg : g ∘ₗ Dc = LinearMap.id) (hQD : Q ∘ₗ D = Dc ∘ₗ r)
    (hrr : r ∘ₗ adjoint r = LinearMap.id) (x : constraintPreimage Q Dc) :
    (toKerConstraint hg hQD hrr x : A) = (x : A) - D (adjoint r (g (Q x))) := rfl
lemma toKerConstraint_eq_zero_iff {D : G →ₗ[ℝ] A} {Dc : Gc →ₗ[ℝ] C} {Q : A →ₗ[ℝ] C}
    {r : G →ₗ[ℝ] Gc}
    {g : C →ₗ[ℝ] Gc} (hg : g ∘ₗ Dc = LinearMap.id) (hQD : Q ∘ₗ D = Dc ∘ₗ r)
    (hrr : r ∘ₗ adjoint r = LinearMap.id) (H : QuadraticForm ℝ (ker Q))
    (hnull : ∀ B : ker Q, H B = 0 ↔ ∃ κ : ker r, (B : A) = D κ)
    (x : constraintPreimage Q Dc) :
    H (toKerConstraint hg hQD hrr x) = 0 ↔ (x : A) ∈ range D := by
  rw [hnull]
  constructor
  · rintro ⟨κ, hκ⟩
    rw [toKerConstraint_coe, sub_eq_iff_eq_add] at hκ
    exact ⟨κ + adjoint r (g (Q x)), by rw [map_add]; exact hκ.symm⟩
  · rintro ⟨l, hl⟩
    have hrl : g (Q (D l)) = r l := by
      have h1 : Q (D l) = Dc (r l) := LinearMap.congr_fun hQD l
      rw [h1]
      exact LinearMap.congr_fun hg (r l)
    have hk : l - adjoint r (r l) ∈ ker r := by
      have h3 : r (adjoint r (r l)) = r l := LinearMap.congr_fun hrr (r l)
      rw [LinearMap.mem_ker, map_sub, h3, sub_self]
    refine ⟨⟨_, hk⟩, ?_⟩
    rw [toKerConstraint_coe, ← hl, hrl]
    simp
lemma gaugeFixedForm_apply {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {E K : Submodule ℝ A} (H : QuadraticForm ℝ E) (hK : K ≤ E) (L : K →ₗ[ℝ] W) (x : K) :
    gaugeFixedForm H hK L x = H (Submodule.inclusion hK x) + ‖L x‖ ^ 2 := by
  simp [gaugeFixedForm]
lemma constrainedGaussianNumber_eq_of_base (hM : AbsDetIndependentOfBases) (D : G →ₗ[ℝ] A)
    (Dc : Gc →ₗ[ℝ] C)
    (Q Q₀ : A →ₗ[ℝ] C) (r r₀ : G →ₗ[ℝ] Gc) (e₁ : Q₀ = Q) (e₂ : r₀ = r)
    (hrr : r ∘ₗ adjoint r = LinearMap.id) (Hh : QuadraticForm ℝ (constraintPreimage Q Dc))
    (T : QuadraticForm ℝ (ker Q)) (Lf : ker Q →ₗ[ℝ] ker r) (v : ker r →ₗ[ℝ] ker r)
    (hT : ∀ (B : ker Q) (hB : (B : A) ∈ constraintPreimage Q Dc),
      T B = Hh ⟨B, hB⟩ + ‖Lf B‖ ^ 2)
    (hv : ∀ (κ : ker r) (h : D κ ∈ ker Q), v κ = Lf ⟨D κ, h⟩) (hvb : Function.Bijective v)
    (hdet : |LinearMap.det v| = 1) (c : ℝ)
    (h : ∃ (hD : Q₀ ∘ₗ D = Dc ∘ₗ r₀) (hE : ker Q₀ ≤ constraintPreimage Q Dc),
      ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
        (L' : ker Q₀ →ₗ[ℝ] W),
        Module.finrank ℝ W = Module.finrank ℝ (ker r₀) →
        Function.Bijective (L' ∘ₗ gaugeRestrictKer D Dc _ _ hD) →
        (gaugeFixedForm Hh hE L').PosDef ∧
          gaugeFixedNumber Q₀ r₀ (gaugeFixedForm Hh hE L')
            (L' ∘ₗ gaugeRestrictKer D Dc _ _ hD) = c) :
    constrainedGaussianNumber Q T = c := by
  subst e₁ e₂
  obtain ⟨hD, hE, hall⟩ := h
  have hw : Lf ∘ₗ gaugeRestrictKer D Dc _ _ hD = v := by
    ext1 κ
    exact (hv κ _).symm
  have hform : gaugeFixedForm Hh hE Lf = T := by
    ext B
    rw [hT B (hE B.2), gaugeFixedForm_apply]
    rfl
  obtain ⟨-, hval⟩ := hall (ker r₀) Lf rfl (by rw [hw]; exact hvb)
  rw [hw, hform, gaugeFixedNumber, absDet_eq_abs_det hM v hvb, hdet, hrr, LinearMap.det_id,
    Real.one_rpow, mul_one, mul_one] at hval
  exact hval
def gaugeComplement (r' : G →ₗ[ℝ] Gc) (a : ℝ) : G →ₗ[ℝ] G :=
  LinearMap.id - a⁻¹ • (adjoint r' ∘ₗ r')
lemma gaugeComplement_apply (r' : G →ₗ[ℝ] Gc) (a : ℝ) (y : G) :
    gaugeComplement r' a y = y - a⁻¹ • adjoint r' (r' y) := rfl
lemma gaugeComplement_mem {r' : G →ₗ[ℝ] Gc} {a : ℝ} (ha : 0 < a)
    (hr' : r' ∘ₗ adjoint r' = a • LinearMap.id) (y : G) : gaugeComplement r' a y ∈ ker r' := by
  have h : r' (adjoint r' (r' y)) = a • r' y := LinearMap.congr_fun hr' (r' y)
  rw [LinearMap.mem_ker, gaugeComplement_apply, map_sub, map_smul, h, smul_smul,
    inv_mul_cancel₀ ha.ne', one_smul, sub_self]
def complementGaugeFixing (D : G →ₗ[ℝ] A) (Q' : A →ₗ[ℝ] C) {r' : G →ₗ[ℝ] Gc} {a : ℝ}
    (ha : 0 < a) (hr' : r' ∘ₗ adjoint r' = a • LinearMap.id) : ker Q' →ₗ[ℝ] ker r' :=
  LinearMap.codRestrict _ (gaugeComplement r' a ∘ₗ adjoint D ∘ₗ Submodule.subtype _)
    (fun _ => gaugeComplement_mem ha hr' _)
lemma inner_compression_eq {D : G →ₗ[ℝ] A} {r' : G →ₗ[ℝ] Gc} {a : ℝ}
    (w : ker r' →ₗ[ℝ] ker r')
    (hw : ∀ κ : ker r', (w κ : G) = gaugeComplement r' a (adjoint D (D κ))) (κ κ' : ker r') :
    inner ℝ (w κ) κ' = inner ℝ (D κ) (D κ') := by
  have hκ' : r' κ' = 0 := κ'.2
  rw [Submodule.coe_inner, hw, gaugeComplement_apply, inner_sub_left, real_inner_smul_left,
    LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hκ', inner_zero_right, mul_zero,
    sub_zero]
lemma compression_bijective {D : G →ₗ[ℝ] A} {r' : G →ₗ[ℝ] Gc} (hD : Function.Injective D)
    (w : ker r' →ₗ[ℝ] ker r')
    (hw : ∀ κ κ' : ker r', inner ℝ (w κ) κ' = inner ℝ (D κ) (D κ')) :
    Function.Bijective w := by
  have hinj : Function.Injective w := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro κ hκ
    have h := hw κ κ
    rw [hκ, inner_zero_left] at h
    have h0 : D κ = 0 := inner_self_eq_zero.1 h.symm
    exact Subtype.ext (hD (by simpa using h0))
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
def gaugeNormSq (D : G →ₗ[ℝ] A) (r' : G →ₗ[ℝ] Gc) : QuadraticForm ℝ (ker r') :=
  (LinearMap.BilinMap.toQuadraticMap (innerₗ A)).comp (D ∘ₗ Submodule.subtype _)
lemma gaugeNormSq_apply (D : G →ₗ[ℝ] A) (r' : G →ₗ[ℝ] Gc) (κ : ker r') :
    gaugeNormSq D r' κ = inner ℝ (D κ) (D κ) := by
  simp [gaugeNormSq]
lemma associated_gaugeNormSq (D : G →ₗ[ℝ] A) (r' : G →ₗ[ℝ] Gc) (x y : ker r') :
    QuadraticMap.associated (gaugeNormSq D r') x y = inner ℝ (D x) (D y) := by
  rw [gaugeNormSq, QuadraticMap.associated_comp, LinearMap.compl₁₂_apply,
    QuadraticMap.associated_toQuadraticMap]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, innerₗ_apply_apply,
    real_inner_comm (D x) (D y)]
  simp
  ring
lemma gaugeNormSq_posDef {D : G →ₗ[ℝ] A} (hD : Function.Injective D) (r' : G →ₗ[ℝ] Gc) :
    (gaugeNormSq D r').PosDef := by
  intro κ hκ
  rw [gaugeNormSq_apply]
  refine real_inner_self_pos.2 ?_
  intro h0
  exact hκ (Subtype.ext (hD (by simpa using h0)))
lemma formMatrixInBasis_gaugeNormSq {D : G →ₗ[ℝ] A} {r' : G →ₗ[ℝ] Gc}
    (w : ker r' →ₗ[ℝ] ker r')
    (hw : ∀ κ κ' : ker r', inner ℝ (w κ) κ' = inner ℝ (D κ) (D κ'))
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ (ker r')) :
    Gaussian.KernelIntegral.formMatrixInBasis r' (gaugeNormSq D r') b =
      LinearMap.toMatrix b.toBasis b.toBasis w := by
  ext i j
  simp only [Gaussian.KernelIntegral.formMatrixInBasis,
    LinearMap.BilinForm.toMatrix_apply, LinearMap.toMatrix_apply, associated_gaugeNormSq,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  rw [← real_inner_comm (b i) (w (b j)), hw]
  exact real_inner_comm _ _
end Setup
lemma constrainedGaussianNumber_pos (hB : Gaussian.KernelIntegral.GaussianIntegralOnKernel)
    {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) (hM : Function.Surjective M) (T : QuadraticForm ℝ (ker M)) (hT : T.PosDef) :
    0 < constrainedGaussianNumber M T := by
  obtain ⟨hdet, d, -, -, -, hpos, -⟩ := hB E F M hM T hT
  exact mul_pos (Real.rpow_pos_of_pos hdet _) hpos
lemma ne_zero_of_pos_of_eq_mul_rpow {I p x : ℝ} (hI : 0 < I)
    (h : I = p * |x| ^ (-(1 / 2) : ℝ)) :
    x ≠ 0 := by
  rintro rfl
  rw [abs_zero, Real.zero_rpow (by norm_num), mul_zero] at h
  exact hI.ne' h
lemma twoSaddle_final_identity {c I₁ e f S₁ S₂ d a : ℝ} {m : ℕ} (ha : 0 < a) (hf : f ≠ 0)
    (hS₂ : 0 < S₂)
    (hd : 0 < d) (h1 : I₁ = e * S₁ ^ (-(1 / 2) : ℝ))
    (h2 : I₁ * d * (a ^ m) ^ (1 / 2 : ℝ) = c)
    (h3 : f * S₂ ^ (-(1 / 2) : ℝ) = (a ^ m) ^ (-(1 / 2) : ℝ) * (f * d ^ (-(1 / 2) : ℝ))) :
    c = e * a ^ (-(m : ℝ) / 2) * S₁ ^ (-(1 / 2) : ℝ) * S₂ := by
  have ham : 0 < a ^ m := pow_pos ha m
  have h4 : S₂ ^ (-(1 / 2) : ℝ) = (a ^ m * d) ^ (-(1 / 2) : ℝ) := by
    rw [Real.mul_rpow ham.le hd.le]
    apply mul_left_cancel₀ hf
    rw [h3]
    ring
  have h5 : S₂ = a ^ m * d := by
    have h6 : (S₂ ^ (-(1 / 2) : ℝ)) ^ (-2 : ℝ) = ((a ^ m * d) ^ (-(1 / 2) : ℝ)) ^ (-2 : ℝ) := by
      rw [h4]
    rw [← Real.rpow_mul hS₂.le, ← Real.rpow_mul (mul_pos ham hd).le] at h6
    norm_num at h6
    exact h6
  set x : ℝ := a ^ ((m : ℝ) / 2) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos ha _
  have hxx : a ^ m = x * x := by
    rw [hx, ← Real.rpow_add ha, add_halves, Real.rpow_natCast]
  have hsq : (a ^ m) ^ (1 / 2 : ℝ) = x := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    ring
  have hneg : a ^ (-(m : ℝ) / 2) = x⁻¹ := by
    rw [hx, ← Real.rpow_neg ha.le]
    congr 1
    ring
  rw [hneg, ← h2, hsq, h1, h5, hxx]
  field_simp
theorem gaussianNumberViaTwoSaddleDeterminants_holds (hGC : GaugeFixingIndependence)
    (hS : SaddleDeterminantIdentity)
    (hB : Gaussian.KernelIntegral.GaussianIntegralOnKernel) :
    GaussianNumberViaTwoSaddleDeterminants := by
  intro A C G Gc _ _ _ _ _ _ _ _ _ _ _ _ D Dc Q r n a H T Lf v X hDi hDci hQs hrs hQD hrr ha hr'
    hinv hT hTpos hv hdet hXs hXf
  obtain ⟨hM, hG⟩ := hGC
  have hdne : LinearMap.det v ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hdet
    exact zero_ne_one hdet
  have hvb := endo_bijective_of_det_ne_zero v hdne
  have hform := form_nonneg_and_eq_zero_iff hQD H T Lf v hinv hT hTpos hv hvb
  obtain ⟨g, hg⟩ := Dc.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hDci)
  let pE := toKerConstraint (D := D) hg hQD hrr
  have hHE₁ : ∀ x, 0 ≤ (H.comp pE) x := fun x => (hform _).1
  have hHE₂ : ∀ x, (H.comp pE) x = 0 ↔ (x : A) ∈ range D :=
    fun x => toKerConstraint_eq_zero_iff hg hQD hrr H (fun B => (hform B).2) x
  obtain ⟨c, hc⟩ := hG A C G Gc D Dc Q r hDi hDci hQs hrs hQD (H.comp pE) hHE₁ hHE₂
  have e₁ : shiftedConstraint Q Dc 0 = Q := by simp [shiftedConstraint]
  have e₂ : shiftedGaugeMap r 0 D = r := by simp [shiftedGaugeMap]
  have hTform : ∀ (B : ker Q) (hB' : (B : A) ∈ constraintPreimage Q Dc),
      T B = (H.comp pE) ⟨B, hB'⟩ + ‖Lf B‖ ^ 2 := by
    intro B hB'
    have hBz : Q (B : A) = 0 := B.2
    have hp : pE ⟨B, hB'⟩ = B := Subtype.ext (by
      change (B : A) - D (adjoint r (g (Q (B : A)))) = B
      simp [hBz])
    rw [QuadraticMap.comp_apply, hp, hT]
  have hbase : constrainedGaussianNumber Q T = c :=
    constrainedGaussianNumber_eq_of_base hM D Dc Q _ r _ e₁ e₂ hrr (H.comp pE) T Lf v hTform hv
      hvb hdet c (hc 0 (by rw [e₂]; exact hrs)).2.2
  have hr's : Function.Surjective (shiftedGaugeMap r n D) := by
    intro y
    refine ⟨adjoint (shiftedGaugeMap r n D) (a⁻¹ • y), ?_⟩
    have h : shiftedGaugeMap r n D (adjoint (shiftedGaugeMap r n D) (a⁻¹ • y)) =
        a • (a⁻¹ • y) :=
      LinearMap.congr_fun hr' _
    rw [h, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  obtain ⟨hQ's, -, hD', hE', hall⟩ := hc n hr's
  let L' := complementGaugeFixing D (shiftedConstraint Q Dc n) ha hr'
  let w := L' ∘ₗ gaugeRestrictKer D Dc _ _ hD'
  have hwc : ∀ κ : ker (shiftedGaugeMap r n D),
      (w κ : G) = gaugeComplement (shiftedGaugeMap r n D) a (adjoint D (D κ)) := fun κ => rfl
  have hwi := inner_compression_eq w hwc
  have hwb := compression_bijective hDi w hwi
  obtain ⟨hTpos', hval⟩ := hall (ker (shiftedGaugeMap r n D)) L' rfl hwb
  let T' := gaugeFixedForm (H.comp pE) hE' L'
  have hXT : ∀ B : ker (shiftedConstraint Q Dc n), inner ℝ (B : A) (X B) = T' B := by
    intro B
    have hBz : Q (B : A) + Dc (n B) = 0 := B.2
    have hgq : g (Q (B : A)) = - n B := by
      have h2 : Q (B : A) = Dc (- n B) := by
        rw [map_neg]
        exact eq_neg_of_add_eq_zero_left hBz
      rw [h2]
      exact LinearMap.congr_fun hg _
    have hcoe : (pE ⟨B, hE' B.2⟩ : A) = (B : A) + D (adjoint r (n B)) := by
      change (B : A) - D (adjoint r (g (Q (B : A)))) = _
      rw [hgq, map_neg, map_neg, sub_neg_eq_add]
    have hmem : (B : A) + D (adjoint r (n B)) ∈ ker Q := hcoe ▸ (pE ⟨B, hE' B.2⟩).2
    have hp : pE ⟨B, hE' B.2⟩ = ⟨_, hmem⟩ := Subtype.ext hcoe
    have hL : ‖L' B‖ = ‖adjoint D (B : A) - a⁻¹ • adjoint (shiftedGaugeMap r n D)
        (shiftedGaugeMap r n D (adjoint D (B : A)))‖ := by
      rw [Submodule.coe_norm]
      rfl
    rw [hXf B B.2 hmem, gaugeFixedForm_apply, hL, QuadraticMap.comp_apply]
    change _ = H (pE ⟨B, hE' B.2⟩) + _
    rw [hp]
  have hS1 := (hS A C _ T' hQ's hTpos' X hXs hXT).1
  have hT₂ := gaugeNormSq_posDef hDi (shiftedGaugeMap r n D)
  have hX₂s : (adjoint D ∘ₗ D).IsSymmetric := by
    intro x y
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
  have hX₂T : ∀ κ : ker (shiftedGaugeMap r n D), inner ℝ (κ : G) ((adjoint D ∘ₗ D) κ) =
      gaugeNormSq D (shiftedGaugeMap r n D) κ := by
    intro κ
    rw [gaugeNormSq_apply, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  have hS2 := (hS G Gc _ _ hr's hT₂ _ hX₂s hX₂T).1
  have det1 := ne_zero_of_pos_of_eq_mul_rpow
    (constrainedGaussianNumber_pos hB _ hQ's T' hTpos') hS1
  have det2 := ne_zero_of_pos_of_eq_mul_rpow (constrainedGaussianNumber_pos hB _ hr's _ hT₂) hS2
  refine ⟨det1, det2, ?_⟩
  obtain ⟨-, d, hdpos, hdall, -, -, hival⟩ := hB G Gc _ hr's _ hT₂
  have hdetw : absDet w = d := by
    have h := hdall (Fin _) (stdOrthonormalBasis ℝ (ker (shiftedGaugeMap r n D)))
    rw [formMatrixInBasis_gaugeNormSq w hwi, LinearMap.det_toMatrix] at h
    rw [absDet_eq_abs_det hM w hwb, h, abs_of_pos hdpos]
  have hdetr : LinearMap.det (shiftedGaugeMap r n D ∘ₗ adjoint (shiftedGaugeMap r n D)) =
      a ^ Module.finrank ℝ Gc := by
    rw [hr', LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hrank : (Module.finrank ℝ (ker (shiftedGaugeMap r n D)) : ℝ) =
      (Module.finrank ℝ G : ℝ) - (Module.finrank ℝ Gc : ℝ) := by
    have h := LinearMap.finrank_range_add_finrank_ker (shiftedGaugeMap r n D)
    rw [LinearMap.range_eq_top.2 hr's, finrank_top] at h
    rw [← h]
    push_cast
    ring
  have hgi : kernelGaussianIntegral (shiftedGaugeMap r n D)
      (gaugeNormSq D (shiftedGaugeMap r n D)) =
      (2 * Real.pi) ^ ((Module.finrank ℝ (ker (shiftedGaugeMap r n D)) : ℝ) / 2) *
        d ^ (-(1 / 2) : ℝ) := hival
  have h2 : constrainedGaussianNumber (shiftedConstraint Q Dc n) T' * d *
      (a ^ Module.finrank ℝ Gc) ^ (1 / 2 : ℝ) = c := by
    rw [← hdetr, ← hdetw]
    exact hval
  have hf : (2 * Real.pi) ^ (((Module.finrank ℝ G : ℝ) - (Module.finrank ℝ Gc : ℝ)) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity) _).ne'
  have h3 : (2 * Real.pi) ^ (((Module.finrank ℝ G : ℝ) - (Module.finrank ℝ Gc : ℝ)) / 2) *
      |LinearMap.det (saddlePointOperator (adjoint D ∘ₗ D) (shiftedGaugeMap r n D))| ^
        (-(1 / 2) : ℝ) =
      (a ^ Module.finrank ℝ Gc) ^ (-(1 / 2) : ℝ) *
        ((2 * Real.pi) ^ (((Module.finrank ℝ G : ℝ) - (Module.finrank ℝ Gc : ℝ)) / 2) *
          d ^ (-(1 / 2) : ℝ)) := by
    rw [← hS2, constrainedGaussianNumber, hdetr, hgi, hrank]
  rw [hbase]
  exact twoSaddle_final_identity ha hf (abs_pos.2 det2) hdpos hS1 h2 h3
end YangMills.Construction.GaussianConstraint.TwoSaddleProof
end
