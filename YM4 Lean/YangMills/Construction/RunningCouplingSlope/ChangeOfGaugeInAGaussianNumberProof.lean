import YangMills.Construction.RunningCouplingSlope.ChangeOfGaugeInAGaussianNumber
import YangMills.Construction.Towers.TheSaddleDeterminant
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Module MeasureTheory
noncomputable section
namespace YangMills.Construction.LinearConstraint.GaugeChangeProof
section Determinants
variable {V W U : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
theorem det_id_add_comp_comm (A : W →ₗ[ℝ] V) (B : V →ₗ[ℝ] W) :
    LinearMap.det (LinearMap.id + A ∘ₗ B) = LinearMap.det (LinearMap.id + B ∘ₗ A) := by
  classical
  let bV := Module.finBasis ℝ V
  let bW := Module.finBasis ℝ W
  rw [← LinearMap.det_toMatrix bV, ← LinearMap.det_toMatrix bW, map_add, map_add,
    LinearMap.toMatrix_id, LinearMap.toMatrix_id, LinearMap.toMatrix_comp bV bW bV,
    LinearMap.toMatrix_comp bW bV bW]
  exact Matrix.det_one_add_mul_comm _ _
theorem det_adjoint_eq (f : V →ₗ[ℝ] V) : LinearMap.det (LinearMap.adjoint f) = LinearMap.det f := by
  classical
  let b := stdOrthonormalBasis ℝ V
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis]
  have h : LinearMap.toMatrix b.toBasis b.toBasis (LinearMap.adjoint f) =
      (LinearMap.toMatrix b.toBasis b.toBasis f).transpose := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Matrix.transpose_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    rw [LinearMap.adjoint_inner_right, real_inner_comm]
  rw [h, Matrix.det_transpose]
theorem nonempty_linearIsometryEquiv_of_finrank_eq (h : finrank ℝ V = finrank ℝ W) :
    Nonempty (V ≃ₗᵢ[ℝ] W) :=
  ⟨(stdOrthonormalBasis ℝ V).equiv ((stdOrthonormalBasis ℝ W).reindex (finCongr h.symm))
    (Equiv.refl _)⟩
theorem absDetOfMap_eq_abs_det_comp (e : W ≃ₗᵢ[ℝ] V) (A : V →ₗ[ℝ] W) :
    absDetOfMap A = |LinearMap.det (e.toLinearEquiv.toLinearMap ∘ₗ A)| := by
  have h : LinearMap.adjoint A ∘ₗ A =
      LinearMap.adjoint (e.toLinearEquiv.toLinearMap ∘ₗ A) ∘ₗ
        (e.toLinearEquiv.toLinearMap ∘ₗ A) := by
    refine LinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    simp
  rw [absDetOfMap, h, LinearMap.det_comp, det_adjoint_eq, ← sq, Real.sqrt_sq_eq_abs]
theorem absDetOfMap_comp (A : V →ₗ[ℝ] W) (B : U →ₗ[ℝ] V) (hUV : finrank ℝ U = finrank ℝ V)
    (hVW : finrank ℝ V = finrank ℝ W) :
    absDetOfMap (A ∘ₗ B) = absDetOfMap A * absDetOfMap B := by
  obtain ⟨e₁⟩ := nonempty_linearIsometryEquiv_of_finrank_eq hUV.symm
  obtain ⟨e₂⟩ := nonempty_linearIsometryEquiv_of_finrank_eq hVW.symm
  rw [absDetOfMap_eq_abs_det_comp (e₂.trans e₁) (A ∘ₗ B), absDetOfMap_eq_abs_det_comp e₂ A,
    absDetOfMap_eq_abs_det_comp e₁ B, ← abs_mul]
  congr 1
  have h : ((e₂.trans e₁).toLinearEquiv.toLinearMap ∘ₗ A ∘ₗ B) =
      (e₁.toLinearEquiv.toLinearMap ∘ₗ (e₂.toLinearEquiv.toLinearMap ∘ₗ A) ∘ₗ
        e₁.toLinearEquiv.symm.toLinearMap) ∘ₗ (e₁.toLinearEquiv.toLinearMap ∘ₗ B) := by
    ext x
    simp
  rw [h, LinearMap.det_comp]
  congr 1
  exact LinearMap.det_conj _ e₁.toLinearEquiv
theorem absDetOfMap_id : absDetOfMap (LinearMap.id : V →ₗ[ℝ] V) = 1 := by
  simp [absDetOfMap]
theorem endo_bijective_of_det_ne_zero (f : V →ₗ[ℝ] V) (h : LinearMap.det f ≠ 0) :
    Function.Bijective f := (Module.End.isUnit_iff f).mp ((LinearMap.isUnit_iff_isUnit_det f).mpr (isUnit_iff_ne_zero.mpr h))
theorem det_ne_zero_of_endo_bijective (f : V →ₗ[ℝ] V) (h : Function.Bijective f) :
    LinearMap.det f ≠ 0 :=
  ((LinearEquiv.ofBijective f h).isUnit_det').ne_zero
end Determinants
section Substitution
variable {K P Y Y' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] [FiniteDimensional ℝ Y']
theorem normSqForm_apply (l : K →ₗ[ℝ] Y) (ξ : K) : normSqForm l ξ = ‖l ξ‖ ^ 2 := by
  simp [normSqForm, LinearMap.BilinMap.toQuadraticMap_apply, real_inner_self_eq_norm_sq]
theorem quadraticForm_add_of_null (T : QuadraticForm ℝ K) (hT : ∀ ξ, 0 ≤ T ξ) (ξ ν : K)
    (hν : T ν = 0) : T (ξ + ν) = T ξ := by
  have hp : QuadraticMap.polar T ξ ν = 0 := by
    by_contra hne
    set p := QuadraticMap.polar T ξ ν with hpdef
    have key : ∀ t : ℝ, 0 ≤ T ξ + t * p := by
      intro t
      have h := hT (ξ + t • ν)
      have e1 : T (ξ + t • ν) = T ξ + T (t • ν) + QuadraticMap.polar T ξ (t • ν) := by
        simp [QuadraticMap.polar]
      have e2 : QuadraticMap.polar T ξ (t • ν) = t * p := by
        rw [QuadraticMap.polar_smul_right]; simp [hpdef]
      have e3 : T (t • ν) = 0 := by
        rw [QuadraticMap.map_smul]; simp [hν]
      linarith
    have h := key (-(T ξ + 1) / p)
    have : -(T ξ + 1) / p * p = -(T ξ + 1) := by field_simp
    linarith
  have e1 : T (ξ + ν) = T ξ + T ν + QuadraticMap.polar T ξ ν := by
    simp [QuadraticMap.polar]
  rw [e1, hp, hν]; ring
theorem integral_comp_linearMap_of_det_ne_zero [MeasurableSpace K] [BorelSpace K]
    (φ : K →ₗ[ℝ] K) (hφ : LinearMap.det φ ≠ 0) (f : K → ℝ) :
    ∫ x, f (φ x) = |(LinearMap.det φ)⁻¹| * ∫ x, f x := by
  have hb := endo_bijective_of_det_ne_zero φ hφ
  let e : K ≃L[ℝ] K := (LinearEquiv.ofBijective φ hb).toContinuousLinearEquiv
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure K) hφ
  have he : MeasurableEmbedding φ := e.toHomeomorph.measurableEmbedding
  rw [← he.integral_map, hmap, integral_smul_measure]
  simp [ENNReal.toReal_ofReal (abs_nonneg _)]
theorem gaussian_mul_absDet_slice_indep [MeasurableSpace K] [BorelSpace K] (T : QuadraticForm ℝ K)
    (hT : ∀ ξ, 0 ≤ T ξ) (b : P →ₗ[ℝ] K) (hnull : ∀ p, T (b p) = 0)
    (l : K →ₗ[ℝ] Y) (l' : K →ₗ[ℝ] Y')
    (hl : Function.Bijective (l ∘ₗ b)) (hl' : Function.Bijective (l' ∘ₗ b)) :
    (∫ ξ, Real.exp (-(1 / 2) * (T + normSqForm l) ξ)) * absDetOfMap (l ∘ₗ b) =
      (∫ ξ, Real.exp (-(1 / 2) * (T + normSqForm l') ξ)) * absDetOfMap (l' ∘ₗ b) := by
  let Bl := LinearEquiv.ofBijective (l ∘ₗ b) hl
  let Bl' := LinearEquiv.ofBijective (l' ∘ₗ b) hl'
  have hPY : finrank ℝ P = finrank ℝ Y := Bl.finrank_eq
  have hPY' : finrank ℝ P = finrank ℝ Y' := Bl'.finrank_eq
  obtain ⟨e⟩ := nonempty_linearIsometryEquiv_of_finrank_eq (hPY.symm.trans hPY')
  obtain ⟨e₀⟩ := nonempty_linearIsometryEquiv_of_finrank_eq hPY'.symm
  let el : K →ₗ[ℝ] Y' := e.toLinearEquiv.toLinearMap ∘ₗ l
  let w : K →ₗ[ℝ] P := Bl'.symm.toLinearMap ∘ₗ (el - l')
  let φ : K →ₗ[ℝ] K := LinearMap.id + b ∘ₗ w
  let M : P →ₗ[ℝ] P := LinearMap.id + w ∘ₗ b
  have hl'b : ∀ p, l' (b p) = Bl' p := fun p => rfl
  have hφl : ∀ ξ, l' (φ ξ) = e (l ξ) := by
    intro ξ
    have : l' (b (w ξ)) = el ξ - l' ξ := by
      rw [hl'b]; simp [w]
    simp [φ, this, el]
  have hM : (l' ∘ₗ b) ∘ₗ M = el ∘ₗ b := by
    refine LinearMap.ext fun p => ?_
    have : l' (b (w (b p))) = el (b p) - l' (b p) := by
      rw [hl'b]; simp [w]
    simp [M, this]
  have hdet : LinearMap.det φ = LinearMap.det M := det_id_add_comp_comm b w
  have hvf : absDetOfMap (l ∘ₗ b) = |LinearMap.det M| * absDetOfMap (l' ∘ₗ b) := by
    rw [absDetOfMap_eq_abs_det_comp (e.trans e₀) (l ∘ₗ b), absDetOfMap_eq_abs_det_comp e₀ (l' ∘ₗ b),
      ← abs_mul, mul_comm, ← LinearMap.det_comp]
    congr 2
    refine LinearMap.ext fun p => ?_
    have := LinearMap.congr_fun hM p
    simp only [LinearMap.comp_apply] at this ⊢
    rw [this]
    simp [el]
  have hMinj : Function.Injective M := by
    have hb : Function.Injective ((l' ∘ₗ b) ∘ₗ M) := by
      rw [hM]
      intro p q hpq
      apply hl.1
      simpa [el] using hpq
    exact Function.Injective.of_comp (f := l' ∘ₗ b) (show Function.Injective ((l' ∘ₗ b) ∘ M) from hb)
  have hMdet : LinearMap.det M ≠ 0 :=
    det_ne_zero_of_endo_bijective M ⟨hMinj, LinearMap.injective_iff_surjective.mp hMinj⟩
  have hf : ∀ ξ, (T + normSqForm l) ξ = (T + normSqForm l') (φ ξ) := by
    intro ξ
    have h1 : T (φ ξ) = T ξ := quadraticForm_add_of_null T hT ξ (b (w ξ)) (hnull _)
    simp only [add_apply, normSqForm_apply, hφl, h1]
    simp
  have hint : (∫ ξ, Real.exp (-(1 / 2) * (T + normSqForm l) ξ)) =
      |(LinearMap.det M)⁻¹| * ∫ ξ, Real.exp (-(1 / 2) * (T + normSqForm l') ξ) := by
    rw [← hdet, ← integral_comp_linearMap_of_det_ne_zero φ (hdet ▸ hMdet)
      (fun ξ => Real.exp (-(1 / 2) * (T + normSqForm l') ξ))]
    simp only [hf]
  rw [hint, hvf, abs_inv]
  have : |LinearMap.det M| ≠ 0 := abs_ne_zero.mpr hMdet
  field_simp
theorem exists_isSymmetric_extension_of_form (N : Submodule ℝ K) (S : QuadraticForm ℝ N) :
    ∃ X : K →ₗ[ℝ] K, X.IsSymmetric ∧ ∀ B : N, inner ℝ (B : K) (X B) = S B := by
  classical
  let β := QuadraticMap.associated (R := ℝ) S
  let b := stdOrthonormalBasis ℝ N
  let Y : N →ₗ[ℝ] N := ∑ i, (β.flip (b i)).smulRight (b i)
  have hY : ∀ x y : N, inner ℝ (Y x) y = β x y := by
    intro x y
    have hy : y = ∑ i, (inner ℝ (b i) y) • b i := (b.sum_repr' y).symm
    conv_rhs => rw [hy]
    simp only [Y, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply, map_sum,
      map_smul, sum_inner, inner_smul_left, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  let ι := N.subtype
  have hι : ∀ x y : N, inner ℝ (ι x) (ι y) = inner ℝ x y := fun x y => rfl
  have hιι : ∀ x : N, LinearMap.adjoint ι (ι x) = x := by
    intro x
    refine ext_inner_right ℝ fun y => ?_
    rw [LinearMap.adjoint_inner_left, hι]
  refine ⟨ι ∘ₗ Y ∘ₗ LinearMap.adjoint ι, ?_, ?_⟩
  · intro x y
    simp only [LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right ι (Y _) y, ← LinearMap.adjoint_inner_left ι (Y _) x, hY,
      real_inner_comm, hY]
    exact QuadraticMap.associated_isSymm ℝ S _ _
  · intro B
    simp only [LinearMap.comp_apply]
    have : LinearMap.adjoint ι (B : K) = B := hιι B
    rw [this]
    change inner ℝ (ι B) (ι (Y B)) = S B
    rw [hι, real_inner_comm, hY]
    exact QuadraticMap.associated_eq_self_apply ℝ S B
end Substitution
section Saddle
variable {A C : Type} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
theorem det_saddlePointOperator_conj (X τ : A →ₗ[ℝ] A) (Q : A →ₗ[ℝ] C) :
    LinearMap.det (GaussianConstraint.saddlePointOperator (LinearMap.adjoint τ ∘ₗ X ∘ₗ τ) (Q ∘ₗ τ)) =
      LinearMap.det τ ^ 2 * LinearMap.det (GaussianConstraint.saddlePointOperator X Q) := by
  have h : GaussianConstraint.saddlePointOperator (LinearMap.adjoint τ ∘ₗ X ∘ₗ τ) (Q ∘ₗ τ) =
      ((LinearMap.adjoint τ).prodMap (LinearMap.id : C →ₗ[ℝ] C)) ∘ₗ
        GaussianConstraint.saddlePointOperator X Q ∘ₗ
        (τ.prodMap (LinearMap.id : C →ₗ[ℝ] C)) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨e, f⟩ := x
    simp [GaussianConstraint.saddlePointOperator, LinearMap.adjoint_comp]
  rw [h, LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_prodMap, LinearMap.det_prodMap,
    det_adjoint_eq, LinearMap.det_id]
  ring
theorem constrainedGaussianNumber_precomp (hs : GaussianConstraint.SaddleDeterminantIdentity)
    (Q Q' : A →ₗ[ℝ] C) (τ : A →ₗ[ℝ] A) (hτ : Function.Bijective τ) (h : Q ∘ₗ τ = Q')
    (hQ : Function.Surjective Q) (S : QuadraticForm ℝ (LinearMap.ker Q)) (hS : S.PosDef) :
    GaussianConstraint.constrainedGaussianNumber Q S =
      |LinearMap.det τ| * GaussianConstraint.constrainedGaussianNumber Q' (S.comp (kerMapOfCompEq τ h)) := by
  subst h
  obtain ⟨X, hXs, hX⟩ := exists_isSymmetric_extension_of_form (LinearMap.ker Q) S
  have hQ' : Function.Surjective (Q ∘ₗ τ) := by
    rw [LinearMap.coe_comp]; exact hQ.comp hτ.2
  have hX's : (LinearMap.adjoint τ ∘ₗ X ∘ₗ τ).IsSymmetric := by
    intro x y
    simp only [LinearMap.comp_apply]
    rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, hXs]
  have hinj : Function.Injective (kerMapOfCompEq (Q := Q) τ rfl) := by
    intro x y hxy
    apply Subtype.ext
    apply hτ.1
    exact congrArg Subtype.val hxy
  have hS' : (S.comp (kerMapOfCompEq (Q := Q) τ rfl)).PosDef := by
    intro x hx
    exact hS _ (fun h0 => hx (hinj (by rw [h0, map_zero])))
  have hX' : ∀ B : LinearMap.ker (Q ∘ₗ τ), inner ℝ (B : A) ((LinearMap.adjoint τ ∘ₗ X ∘ₗ τ) B) =
      (S.comp (kerMapOfCompEq (Q := Q) τ rfl)) B := by
    intro B
    simp only [LinearMap.comp_apply]
    rw [LinearMap.adjoint_inner_right]
    exact hX (kerMapOfCompEq (Q := Q) τ rfl B)
  have e1 := (hs A C Q S hQ hS X hXs hX).1
  have e2 := (hs A C (Q ∘ₗ τ) _ hQ' hS' _ hX's hX').1
  have ht : LinearMap.det τ ≠ 0 := det_ne_zero_of_endo_bijective τ hτ
  rw [e1, e2, det_saddlePointOperator_conj, abs_mul, abs_of_nonneg (sq_nonneg (LinearMap.det τ)),
    Real.mul_rpow (sq_nonneg _) (abs_nonneg _)]
  have h2 : (LinearMap.det τ ^ 2) ^ (-(1 / 2) : ℝ) = |LinearMap.det τ|⁻¹ := by
    rw [Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  have hfin : Module.finrank ℝ A = Module.finrank ℝ A := rfl
  rw [h2]
  have : |LinearMap.det τ| ≠ 0 := abs_ne_zero.mpr ht
  field_simp
end Saddle
section Slices
variable {G Gc : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup Gc] [InnerProductSpace ℝ Gc] [FiniteDimensional ℝ Gc]
theorem ker_subtype_comp_adjoint (r : G →ₗ[ℝ] Gc) (hrr : r ∘ₗ LinearMap.adjoint r = LinearMap.id) :
    (LinearMap.ker r).subtype ∘ₗ LinearMap.adjoint (LinearMap.ker r).subtype =
      LinearMap.id - LinearMap.adjoint r ∘ₗ r := by
  have hrR : ∀ x, r (LinearMap.adjoint r x) = x := fun x => LinearMap.congr_fun hrr x
  refine LinearMap.ext fun x => ?_
  have hz : x - LinearMap.adjoint r (r x) ∈ LinearMap.ker r := by
    simp [LinearMap.mem_ker, hrR]
  have : LinearMap.adjoint (LinearMap.ker r).subtype x = ⟨_, hz⟩ := by
    refine ext_inner_right ℝ fun y => ?_
    rw [LinearMap.adjoint_inner_left]
    have hy : r (y : G) = 0 := y.2
    change inner ℝ x (y : G) = inner ℝ (x - LinearMap.adjoint r (r x)) (y : G)
    rw [inner_sub_left, LinearMap.adjoint_inner_left, hy]
    simp
  simp [this]
theorem exists_slice_projection_area (r aa : G →ₗ[ℝ] Gc)
    (hrr : r ∘ₗ LinearMap.adjoint r = LinearMap.id)
    (hc : Function.Bijective (aa ∘ₗ LinearMap.adjoint r)) :
    ∃ p : LinearMap.ker aa →ₗ[ℝ] LinearMap.ker r,
      (∀ x : LinearMap.ker aa, (p x : G) = x - LinearMap.adjoint r (r x)) ∧
      Function.Bijective p ∧
      absDetOfMap p * LinearMap.det (aa ∘ₗ LinearMap.adjoint aa) ^ (1 / 2 : ℝ) =
        |LinearMap.det (aa ∘ₗ LinearMap.adjoint r)| := by
  let R := LinearMap.adjoint r
  have hrR : ∀ x, r (R x) = x := fun x => LinearMap.congr_fun hrr x
  let c := LinearEquiv.ofBijective (aa ∘ₗ R) hc
  let ci : Gc →ₗ[ℝ] Gc := c.symm.toLinearMap
  have hcc : ∀ x, aa (R (ci x)) = x := fun x => c.apply_symm_apply x
  have hcc' : ∀ x, ci (aa (R x)) = x := fun x => c.symm_apply_apply x
  let p : LinearMap.ker aa →ₗ[ℝ] LinearMap.ker r :=
    LinearMap.codRestrict (LinearMap.ker r) ((LinearMap.id - R ∘ₗ r) ∘ₗ (LinearMap.ker aa).subtype)
      (fun x => by simp [LinearMap.mem_ker, hrR])
  let q : LinearMap.ker r →ₗ[ℝ] LinearMap.ker aa :=
    LinearMap.codRestrict (LinearMap.ker aa)
      ((LinearMap.id - R ∘ₗ ci ∘ₗ aa) ∘ₗ (LinearMap.ker r).subtype)
      (fun x => by simp [LinearMap.mem_ker, hcc])
  have hpv : ∀ x : LinearMap.ker aa, (p x : G) = x - R (r x) := fun x => rfl
  have hqv : ∀ x : LinearMap.ker r, (q x : G) = x - R (ci (aa x)) := fun x => rfl
  have hpq : p ∘ₗ q = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hx : r (x : G) = 0 := x.2
    simp [hpv, hqv, hx, hrR]
  have hqp : q ∘ₗ p = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hx : aa (x : G) = 0 := x.2
    simp [hpv, hqv, hx, hcc']
  let ι := (LinearMap.ker r).subtype
  let Y : LinearMap.ker r →ₗ[ℝ] Gc := ci ∘ₗ aa ∘ₗ ι
  have hRk : ∀ (z : Gc) (w : LinearMap.ker r), inner ℝ (R z) (w : G) = 0 := by
    intro z w
    have hw : r (w : G) = 0 := w.2
    rw [LinearMap.adjoint_inner_left, hw, inner_zero_right]
  have hRk' : ∀ (z : Gc) (w : LinearMap.ker r), inner ℝ (w : G) (R z) = 0 := by
    intro z w
    rw [real_inner_comm, hRk]
  have hRR : ∀ z z' : Gc, inner ℝ (R z) (R z') = inner ℝ z z' := by
    intro z z'
    rw [LinearMap.adjoint_inner_left, hrR]
  have hq : LinearMap.adjoint q ∘ₗ q = LinearMap.id + LinearMap.adjoint Y ∘ₗ Y := by
    refine LinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply, inner_add_left,
      LinearMap.adjoint_inner_left]
    change inner ℝ (q x : G) (q y : G) = inner ℝ (x : G) (y : G) + inner ℝ (Y x) (Y y)
    rw [hqv, hqv]
    change inner ℝ ((x : G) - R (Y x)) ((y : G) - R (Y y)) = _
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hRk, hRk', hRR]
    ring
  have hE : ci ∘ₗ aa ∘ₗ R = LinearMap.id := LinearMap.ext hcc'
  have hr' : ∀ z, r (LinearMap.adjoint aa (LinearMap.adjoint ci z)) = z := by
    have h := congrArg LinearMap.adjoint hE
    simp only [LinearMap.adjoint_comp, LinearMap.adjoint_id, R, LinearMap.adjoint_adjoint] at h
    exact fun z => LinearMap.congr_fun h z
  have hY : LinearMap.id + Y ∘ₗ LinearMap.adjoint Y =
      ci ∘ₗ (aa ∘ₗ LinearMap.adjoint aa) ∘ₗ LinearMap.adjoint ci := by
    have h1 : Y ∘ₗ LinearMap.adjoint Y =
        ci ∘ₗ aa ∘ₗ (ι ∘ₗ LinearMap.adjoint ι) ∘ₗ LinearMap.adjoint aa ∘ₗ LinearMap.adjoint ci := by
      simp only [Y, LinearMap.adjoint_comp, LinearMap.comp_assoc]
    rw [h1, ker_subtype_comp_adjoint r hrr]
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      map_sub, hr']
    have := hcc' z
    change z + (ci (aa (LinearMap.adjoint aa (LinearMap.adjoint ci z))) - ci (aa (R z))) = _
    rw [this]
    abel
  have hdet : LinearMap.det (LinearMap.adjoint q ∘ₗ q) =
      LinearMap.det ci ^ 2 * LinearMap.det (aa ∘ₗ LinearMap.adjoint aa) := by
    rw [hq, det_id_add_comp_comm (LinearMap.adjoint Y) Y, hY, LinearMap.det_comp,
      LinearMap.det_comp, det_adjoint_eq]
    ring
  have hvq : absDetOfMap q =
      |LinearMap.det ci| * Real.sqrt (LinearMap.det (aa ∘ₗ LinearMap.adjoint aa)) := by
    rw [absDetOfMap, hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hpb : Function.Bijective p :=
    ⟨Function.LeftInverse.injective (g := q) (fun x => LinearMap.congr_fun hqp x),
      Function.RightInverse.surjective (g := q) (fun x => LinearMap.congr_fun hpq x)⟩
  have hfr : finrank ℝ (LinearMap.ker aa) = finrank ℝ (LinearMap.ker r) :=
    (LinearEquiv.ofBijective p hpb).finrank_eq
  have h1 : absDetOfMap p * absDetOfMap q = 1 := by
    rw [← absDetOfMap_comp p q hfr.symm hfr, hpq, absDetOfMap_id]
  have hci : LinearMap.det ci * LinearMap.det (aa ∘ₗ LinearMap.adjoint r) = 1 := by
    have : ci ∘ₗ aa ∘ₗ R = LinearMap.id := hE
    rw [← LinearMap.det_comp]
    change LinearMap.det (ci ∘ₗ aa ∘ₗ R) = 1
    rw [this, LinearMap.det_id]
  have hci' : |LinearMap.det ci| * |LinearMap.det (aa ∘ₗ LinearMap.adjoint r)| = 1 := by
    rw [← abs_mul, hci, abs_one]
  refine ⟨p, hpv, hpb, ?_⟩
  rw [← Real.sqrt_eq_rpow]
  rw [hvq] at h1
  calc absDetOfMap p * Real.sqrt (LinearMap.det (aa ∘ₗ LinearMap.adjoint aa))
      = (absDetOfMap p * (|LinearMap.det ci| *
          Real.sqrt (LinearMap.det (aa ∘ₗ LinearMap.adjoint aa)))) *
          |LinearMap.det (aa ∘ₗ LinearMap.adjoint r)| := by
        have : absDetOfMap p * Real.sqrt (LinearMap.det (aa ∘ₗ LinearMap.adjoint aa)) =
            absDetOfMap p * Real.sqrt (LinearMap.det (aa ∘ₗ LinearMap.adjoint aa)) *
              (|LinearMap.det ci| * |LinearMap.det (aa ∘ₗ LinearMap.adjoint r)|) := by
          rw [hci', mul_one]
        rw [this]; ring
    _ = |LinearMap.det (aa ∘ₗ LinearMap.adjoint r)| := by rw [h1, one_mul]
end Slices
section Gaussian
variable {A C P Y Y' : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] [FiniteDimensional ℝ Y']
theorem kernelGaussianIntegral_slice_indep (Q : A →ₗ[ℝ] C) (T : QuadraticForm ℝ (LinearMap.ker Q))
    (hT : ∀ ξ, 0 ≤ T ξ) (b : P →ₗ[ℝ] LinearMap.ker Q) (hnull : ∀ p, T (b p) = 0)
    (l : LinearMap.ker Q →ₗ[ℝ] Y) (l' : LinearMap.ker Q →ₗ[ℝ] Y')
    (hl : Function.Bijective (l ∘ₗ b)) (hl' : Function.Bijective (l' ∘ₗ b)) :
    GaussianConstraint.kernelGaussianIntegral Q (T + normSqForm l) * absDetOfMap (l ∘ₗ b) =
      GaussianConstraint.kernelGaussianIntegral Q (T + normSqForm l') * absDetOfMap (l' ∘ₗ b) := by
  unfold GaussianConstraint.kernelGaussianIntegral
  letI : MeasurableSpace (LinearMap.ker Q) := borel _
  haveI : BorelSpace (LinearMap.ker Q) := ⟨rfl⟩
  exact gaussian_mul_absDet_slice_indep T hT b hnull l l' hl hl'
end Gaussian
theorem gaugeChange_of_explicit_data (hs : GaussianConstraint.SaddleDeterminantIdentity)
    {G A Gc C Y Y' : Type}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup Gc] [InnerProductSpace ℝ Gc] [FiniteDimensional ℝ Gc]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] [FiniteDimensional ℝ Y']
    (D : G →ₗ[ℝ] A) (Dc : Gc →ₗ[ℝ] C) (Q Q' : A →ₗ[ℝ] C) (r aa : G →ₗ[ℝ] Gc) (n : A →ₗ[ℝ] Gc)
    (τ : A →ₗ[ℝ] A) (T : QuadraticForm ℝ (LinearMap.ker Q))
    (haa : ∀ x, aa x = r x + n (D x)) (hτv : ∀ x, τ x = x + D (LinearMap.adjoint r (n x)))
    (hQ'v : ∀ x, Q' x = Q x + Dc (n x))
    (hQ : Function.Surjective Q)
    (hrr : r ∘ₗ LinearMap.adjoint r = LinearMap.id)
    (hQDv : ∀ x, Q (D x) = Dc (r x))
    (hc : Function.Bijective (aa ∘ₗ LinearMap.adjoint r))
    (hT0 : ∀ ξ, 0 ≤ T ξ)
    (hTnull : ∀ ξ : LinearMap.ker Q, T ξ = 0 ↔ (ξ : A) ∈ (LinearMap.ker r).map D)
    (hbij : Function.Bijective τ)
    (hdet : LinearMap.det τ = LinearMap.det (aa ∘ₗ LinearMap.adjoint r))
    (hQτ : Q ∘ₗ τ = Q')
    (l : A →ₗ[ℝ] Y) (l' : A →ₗ[ℝ] Y')
    (hl : Function.Bijective (l ∘ₗ D ∘ₗ (LinearMap.ker r).subtype))
    (hl' : Function.Bijective (l' ∘ₗ D ∘ₗ (LinearMap.ker aa).subtype)) :
    GaussianConstraint.constrainedGaussianNumber Q (T + (normSqForm l).comp (LinearMap.ker Q).subtype) *
        absDetOfMap (l ∘ₗ D ∘ₗ (LinearMap.ker r).subtype) =
      LinearMap.det (aa ∘ₗ LinearMap.adjoint aa) ^ (1 / 2 : ℝ) *
        GaussianConstraint.constrainedGaussianNumber Q'
          (T.comp (kerMapOfCompEq _ hQτ) + (normSqForm l').comp (LinearMap.ker Q').subtype) *
        absDetOfMap (l' ∘ₗ D ∘ₗ (LinearMap.ker aa).subtype) := by
  obtain ⟨p, hpv, hpb, hparea⟩ := exists_slice_projection_area r aa hrr hc
  let τ' := kerMapOfCompEq τ hQτ
  have hτ'v : ∀ ξ : LinearMap.ker Q', (τ' ξ : A) = τ ξ := fun ξ => rfl
  have hT1 : (T + (normSqForm l).comp (LinearMap.ker Q).subtype).PosDef := by
    intro ξ hξ
    have h0 := hT0 ξ
    have hval : (T + (normSqForm l).comp (LinearMap.ker Q).subtype) ξ = T ξ + ‖l ξ‖ ^ 2 := by
      simp [normSqForm_apply]
    rw [hval]
    by_contra hle
    have hTz : T ξ = 0 := by nlinarith [sq_nonneg ‖l (ξ : A)‖]
    have hlz : ‖l (ξ : A)‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖l (ξ : A)‖]
    obtain ⟨κ, hκ, hκξ⟩ := (Submodule.mem_map).mp ((hTnull ξ).mp hTz)
    have hlκ : (l ∘ₗ D ∘ₗ (LinearMap.ker r).subtype) ⟨κ, hκ⟩ = 0 := by
      have : l (ξ : A) = 0 := by simpa using hlz
      simpa [hκξ] using this
    have hκ0 : (⟨κ, hκ⟩ : LinearMap.ker r) = 0 := hl.1 (by rw [hlκ, map_zero])
    apply hξ
    apply Subtype.ext
    have : κ = 0 := congrArg Subtype.val hκ0
    simp [← hκξ, this]
  have e1 := constrainedGaussianNumber_precomp hs Q Q' τ hbij hQτ hQ _ hT1
  have hb0 : ∀ x : LinearMap.ker aa, (D ∘ₗ (LinearMap.ker aa).subtype) x ∈ LinearMap.ker Q' := by
    intro x
    have hx : aa (x : G) = 0 := x.2
    rw [haa] at hx
    have h2 : Dc (r (x : G)) + Dc (n (D x)) = 0 := by rw [← map_add, hx, map_zero]
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, hQ'v, hQDv]
    exact h2
  let b0 : LinearMap.ker aa →ₗ[ℝ] LinearMap.ker Q' :=
    LinearMap.codRestrict (LinearMap.ker Q') (D ∘ₗ (LinearMap.ker aa).subtype) hb0
  have hτD : ∀ x : LinearMap.ker aa, τ (D x) = D (p x) := by
    intro x
    have hx : aa (x : G) = 0 := x.2
    rw [haa] at hx
    have hn : n (D x) = - r (x : G) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hx
    rw [hpv, hτv, hn]
    simp [sub_eq_add_neg]
  have hnull : ∀ x, (T.comp τ') (b0 x) = 0 := by
    intro x
    refine (hTnull (τ' (b0 x))).mpr ?_
    rw [hτ'v]
    change τ (D x) ∈ _
    rw [hτD]
    exact Submodule.mem_map_of_mem (p x).2
  have hT0' : ∀ ξ, 0 ≤ (T.comp τ') ξ := fun ξ => hT0 _
  have hcomp : ((l ∘ₗ τ) ∘ₗ (LinearMap.ker Q').subtype) ∘ₗ b0 =
      (l ∘ₗ D ∘ₗ (LinearMap.ker r).subtype) ∘ₗ p := by
    refine LinearMap.ext fun x => ?_
    change l (τ (D x)) = l (D (p x))
    rw [hτD]
  have hcomp' : (l' ∘ₗ (LinearMap.ker Q').subtype) ∘ₗ b0 =
      l' ∘ₗ D ∘ₗ (LinearMap.ker aa).subtype := rfl
  have hlb : Function.Bijective (((l ∘ₗ τ) ∘ₗ (LinearMap.ker Q').subtype) ∘ₗ b0) := by
    rw [hcomp, LinearMap.coe_comp]
    exact hl.comp hpb
  have hl'b : Function.Bijective ((l' ∘ₗ (LinearMap.ker Q').subtype) ∘ₗ b0) := hl'
  have e2 := kernelGaussianIntegral_slice_indep Q' (T.comp τ') hT0' b0 hnull _ _ hlb hl'b
  have hf1 : (T + (normSqForm l).comp (LinearMap.ker Q).subtype).comp (kerMapOfCompEq τ hQτ) =
      T.comp τ' + normSqForm ((l ∘ₗ τ) ∘ₗ (LinearMap.ker Q').subtype) := by
    ext ξ
    simp [normSqForm_apply, τ', kerMapOfCompEq]
  have hf2 : T.comp (kerMapOfCompEq τ hQτ) + (normSqForm l').comp (LinearMap.ker Q').subtype =
      T.comp τ' + normSqForm (l' ∘ₗ (LinearMap.ker Q').subtype) := by
    ext ξ
    simp [normSqForm_apply, τ']
  have hfr₁ : finrank ℝ (LinearMap.ker aa) = finrank ℝ (LinearMap.ker r) :=
    (LinearEquiv.ofBijective p hpb).finrank_eq
  have hfr₂ : finrank ℝ (LinearMap.ker r) = finrank ℝ Y :=
    (LinearEquiv.ofBijective _ hl).finrank_eq
  rw [hcomp, hcomp', absDetOfMap_comp _ p hfr₁ hfr₂] at e2
  have habs : |LinearMap.det τ| = absDetOfMap p *
      LinearMap.det (aa ∘ₗ LinearMap.adjoint aa) ^ (1 / 2 : ℝ) := by rw [hdet, hparea]
  rw [e1, hf1, hf2, habs, GaussianConstraint.constrainedGaussianNumber,
    GaussianConstraint.constrainedGaussianNumber]
  linear_combination
    (LinearMap.det (aa ∘ₗ LinearMap.adjoint aa) ^ (1 / 2 : ℝ) *
      LinearMap.det (Q' ∘ₗ LinearMap.adjoint Q') ^ (-(1 / 2) : ℝ)) * e2
theorem gaugeChangeGaussianIdentity (hs : GaussianConstraint.SaddleDeterminantIdentity) :
    GaugeChangeGaussianIdentity := by
  intro G A Gc C _ _ _ _ _ _ _ _ _ _ _ _ D Dc Q r n T hQ hrr hQD hc hDinj hT0 hTnull
  have hrR : ∀ x, r (LinearMap.adjoint r x) = x := fun x => LinearMap.congr_fun hrr x
  have hQDv : ∀ x, Q (D x) = Dc (r x) := fun x => LinearMap.congr_fun hQD x
  have hdet : LinearMap.det (LinearMap.id + D ∘ₗ LinearMap.adjoint r ∘ₗ n : A →ₗ[ℝ] A) =
      LinearMap.det ((r + n ∘ₗ D) ∘ₗ LinearMap.adjoint r) := by
    have h1 : (r + n ∘ₗ D) ∘ₗ LinearMap.adjoint r =
        LinearMap.id + n ∘ₗ (D ∘ₗ LinearMap.adjoint r) := by
      refine LinearMap.ext fun x => ?_
      simp [hrR]
    rw [h1]
    exact det_id_add_comp_comm (D ∘ₗ LinearMap.adjoint r) n
  have hbij : Function.Bijective (LinearMap.id + D ∘ₗ LinearMap.adjoint r ∘ₗ n : A →ₗ[ℝ] A) :=
    endo_bijective_of_det_ne_zero _ (hdet ▸ det_ne_zero_of_endo_bijective _ hc)
  have hQτ : Q ∘ₗ (LinearMap.id + D ∘ₗ LinearMap.adjoint r ∘ₗ n) = Q + Dc ∘ₗ n := by
    refine LinearMap.ext fun x => ?_
    simp [hQDv, hrR]
  refine ⟨hbij, hdet, hQτ, ?_⟩
  intro Y Y' _ _ _ _ _ _ l l' hl hl'
  exact gaugeChange_of_explicit_data hs D Dc Q (Q + Dc ∘ₗ n) r (r + n ∘ₗ D) n _ T (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) hQ hrr hQDv hc hT0 hTnull hbij hdet hQτ l l' hl hl'
end YangMills.Construction.LinearConstraint.GaugeChangeProof
end
