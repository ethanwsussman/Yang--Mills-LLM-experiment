import YangMills.Construction.HilbertSpaces.PolynomialsOfACommutingPairAreBoundedByTheirSuprema
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert WeakDual
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.ContractionUnitary.PolynomialBound
section Algebra
variable {B D : Type} [Ring B] [StarRing B] [Algebra ℂ B] [Ring D] [StarRing D] [Algebra ℂ D]
def zpowStar (v : B) (y : ℤ) : B := if 0 ≤ y then v ^ y.toNat else star v ^ (-y).toNat
def evalPolyIn (c : Coeffs) (a v : B) : B :=
  c.sum fun i z => z • (a ^ i.1 * zpowStar v i.2)
theorem map_zpowStar (f : B →⋆ₐ[ℂ] D) (v : B) (y : ℤ) : f (zpowStar v y) = zpowStar (f v) y := by
  unfold zpowStar
  split_ifs <;> simp [map_pow, map_star]
theorem map_evalPolyIn (f : B →⋆ₐ[ℂ] D) (c : Coeffs) (a v : B) :
    f (evalPolyIn c a v) = evalPolyIn c (f a) (f v) := by
  unfold evalPolyIn Finsupp.sum
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_mul, map_pow, map_zpowStar]
end Algebra
section Characters
variable {B : Type} [CommCStarAlgebra B] {a v : B}
theorem conj_mul_self_char (φ : characterSpace ℂ B) (hv : star v * v = 1) :
    conj (φ v) * φ v = 1 := by
  have e₁ := congrArg φ hv
  rwa [map_mul, map_star, map_one] at e₁
theorem char_zpowStar (φ : characterSpace ℂ B) (hv : star v * v = 1) (y : ℤ) :
    φ (zpowStar v y) = φ v ^ y := by
  have e₁ := conj_mul_self_char φ hv
  have e₂ : φ (star v) = (φ v)⁻¹ := by
    rw [map_star]
    exact eq_inv_of_mul_eq_one_left e₁
  unfold zpowStar
  split_ifs with hy
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hy
    simp [map_pow]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, y = -n := ⟨(-y).toNat, by omega⟩
    rw [map_pow, e₂, zpow_neg, zpow_natCast, inv_pow]
    simp
theorem char_evalPolyIn (φ : characterSpace ℂ B) (hv : star v * v = 1) (c : Coeffs) :
    φ (evalPolyIn c a v) = c.sum fun i z => z * φ a ^ i.1 * φ v ^ i.2 := by
  unfold evalPolyIn Finsupp.sum
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_mul, map_pow, char_zpowStar φ hv, smul_eq_mul]
  exact (mul_assoc _ _ _).symm
theorem exists_point_char_eq (hv : star v * v = 1) (c : Coeffs) (φ : characterSpace ℂ B)
    (e₀ : (φ a).im = 0) (e₁ : 0 ≤ (φ a).re) (e₂ : (φ a).re ≤ 1) :
    ∃ p : intervalCircle, φ (evalPolyIn c a v) = evalPoly c p := by
  have e₃ : ‖φ v‖ = 1 := by
    have e₄ := conj_mul_self_char φ hv
    rw [Complex.conj_mul'] at e₄
    have e₅ : ‖φ v‖ ^ 2 = 1 := by exact_mod_cast e₄
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp e₅
  have e₆ : (((φ a).re : ℝ) : ℂ) = φ a := Complex.ext (by simp) (by simp [e₀])
  refine ⟨⟨((φ a).re, φ v), ⟨e₁, e₂⟩, e₃⟩, ?_⟩
  rw [char_evalPolyIn φ hv]
  simp only [evalPoly, e₆]
theorem exists_eq_star_mul_self_of_char_nonneg (x : B) (hx : ∀ φ : characterSpace ℂ B, 0 ≤ φ x) :
    ∃ g : B, x = star g * g := by
  let f : C(characterSpace ℂ B, ℂ) := gelfandTransform ℂ B x
  let r : C(characterSpace ℂ B, ℂ) :=
    ⟨fun φ => ((Real.sqrt (f φ).re : ℝ) : ℂ),
      Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (Complex.continuous_re.comp f.continuous))⟩
  obtain ⟨g, hg⟩ := (gelfandTransform_bijective B).2 r
  refine ⟨g, (gelfandTransform_bijective B).1 ?_⟩
  rw [map_mul, gelfandTransform_map_star, hg]
  ext φ
  have e₁ := Complex.le_def.mp (hx φ)
  have e₂ : f φ = φ x := rfl
  have e₃ : (star r * r) φ = conj (r φ) * r φ := rfl
  have e₄ : r φ = ((Real.sqrt (φ x).re : ℝ) : ℂ) := by
    change ((Real.sqrt (f φ).re : ℝ) : ℂ) = _
    rw [e₂]
  have e₅ : gelfandTransform ℂ B x φ = φ x := rfl
  rw [e₃, e₅, e₄, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by simpa using e₁.1)]
  exact Complex.ext (by simp) (by simpa using e₁.2.symm)
theorem norm_le_of_forall_char (x : B) {C : ℝ} (hC : 0 ≤ C)
    (hx : ∀ φ : characterSpace ℂ B, ‖φ x‖ ≤ C) : ‖x‖ ≤ C := by
  rw [← (gelfandTransform_isometry B).norm_map_of_map_zero (map_zero _) x]
  exact (ContinuousMap.norm_le _ hC).mpr hx
end Characters
section Pair
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A V : BddOp H}
theorem star_mul_self_of_isUnitaryMap (hU : IsUnitaryMap (V : H →ₗ[ℂ] H)) :
    star V * V = 1 := by
  let W : H →ₗᵢ[ℂ] H := ⟨(V : H →ₗ[ℂ] H), hU.isometric⟩
  ext ψ
  refine ext_inner_left ℂ fun φ => ?_
  have e₁ : ⟪φ, (star V * V) ψ⟫_ℂ = ⟪V φ, V ψ⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_right V φ (V ψ)
  rw [e₁]
  exact W.inner_map_map φ ψ
theorem opInv_eq_star (hU : IsUnitaryMap (V : H →ₗ[ℂ] H)) :
    opInv V = star V := by
  obtain ⟨e₁, _⟩ := isTwoSidedInverse_opInv hU
  calc opInv V = (star V * V) * opInv V := by
        rw [star_mul_self_of_isUnitaryMap hU, one_mul]
    _ = star V := by rw [mul_assoc, e₁, mul_one]
theorem self_mul_star_of_isUnitaryMap (hU : IsUnitaryMap (V : H →ₗ[ℂ] H)) :
    V * star V = 1 := by
  rw [← opInv_eq_star hU]
  exact (isTwoSidedInverse_opInv hU).1
theorem evalPolyOp_eq_evalPolyIn (hU : IsUnitaryMap (V : H →ₗ[ℂ] H))
    (c : Coeffs) (A : BddOp H) :
    evalPolyOp c A V = evalPolyIn c A V := by
  unfold evalPolyOp evalPolyIn zpowOp zpowStar
  rw [opInv_eq_star hU]
theorem nonneg_of_inner_self_nonneg {T : BddOp H} (hT : IsSymmetricOp T)
    (hpos : ∀ ψ, 0 ≤ ⟪ψ, T ψ⟫_ℂ) : 0 ≤ T := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
  refine ⟨(isSymmetricOp_iff T).mp hT, fun ψ => ?_⟩
  have e₁ := (Complex.le_def.mp (hpos ψ)).1
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← hT ψ ψ]
  simpa using e₁
theorem IsCommutingPair.nonneg_left (hp : IsCommutingPair A V) : 0 ≤ A := by
  refine nonneg_of_inner_self_nonneg hp.symm fun ψ => ?_
  have e₁ := hp.nonneg.le ψ
  simpa using e₁
theorem IsCommutingPair.one_sub_nonneg (hp : IsCommutingPair A V) : 0 ≤ 1 - A := by
  have e₁ : IsSymmetricOp (1 - A) := by
    intro φ ψ
    have e₂ := hp.symm φ ψ
    simp [e₂]
  refine nonneg_of_inner_self_nonneg e₁ fun ψ => ?_
  have e₂ := hp.le_one.le ψ
  have e₃ : ⟪ψ, (1 - A) ψ⟫_ℂ = ⟪ψ, ψ⟫_ℂ - ⟪ψ, A ψ⟫_ℂ := by simp
  rw [e₃]
  exact sub_nonneg.mpr e₂
theorem inner_star_mul_self_nonneg (G : BddOp H) (ψ : H) :
    0 ≤ ⟪ψ, (star G * G) ψ⟫_ℂ := by
  have e₁ : ⟪ψ, (star G * G) ψ⟫_ℂ = ⟪G ψ, G ψ⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_right G ψ (G ψ)
  rw [e₁, inner_self_eq_norm_sq_to_K]
  have e₂ : (0 : ℝ) ≤ ‖G ψ‖ ^ 2 := sq_nonneg _
  convert Complex.zero_le_real.mpr e₂ using 1
  simp
def pairAlgebra (A V : BddOp H) : StarSubalgebra ℂ (BddOp H) :=
  (StarAlgebra.adjoin ℂ ({A, V} : Set (BddOp H))).topologicalClosure
instance isClosed_pairAlgebra (A V : BddOp H) :
    IsClosed (pairAlgebra A V : Set (BddOp H)) :=
  StarSubalgebra.isClosed_topologicalClosure _
theorem left_mem_pairAlgebra : A ∈ pairAlgebra A V :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (by simp))
theorem right_mem_pairAlgebra : V ∈ pairAlgebra A V :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (by simp))
theorem pairAlgebra_mul_comm (hp : IsCommutingPair A V) (x y : pairAlgebra A V) :
    x * y = y * x := by
  have hA : star A = A := ((isSymmetricOp_iff A).mp hp.symm).star_eq
  have e₁ := star_mul_self_of_isUnitaryMap hp.unitary
  have e₂ := self_mul_star_of_isUnitaryMap hp.unitary
  have hc : A * star V = star V * A := by
    calc A * star V = (star V * V) * A * star V := by rw [e₁, one_mul]
      _ = star V * (V * A) * star V := by simp only [mul_assoc]
      _ = star V * (A * V) * star V := by rw [hp.comm]
      _ = star V * A * (V * star V) := by simp only [mul_assoc]
      _ = star V * A := by rw [e₂, mul_one]
  have hs := StarAlgebra.isMulCommutative_adjoin ℂ (s := ({A, V} : Set (BddOp H)))
    (by
      rintro _ (rfl | rfl) _ (rfl | rfl)
      · rfl
      · exact hp.comm
      · exact hp.comm.symm
      · rfl)
    (by
      rintro _ (rfl | rfl) _ (rfl | rfl)
      · rw [hA]
      · exact hc
      · rw [hA]
        exact hp.comm.symm
      · rw [e₁, e₂])
  let _ := (StarAlgebra.adjoin ℂ ({A, V} : Set (BddOp H))).commRingTopologicalClosure
    hs.is_comm.comm
  exact mul_comm (G := (StarAlgebra.adjoin ℂ
    ({A, V} : Set (BddOp H))).topologicalClosure) x y
@[reducible] def pairAlgebraCommCStar (hp : IsCommutingPair A V) :
    CommCStarAlgebra (pairAlgebra A V) :=
  { StarSubalgebra.cstarAlgebra (pairAlgebra A V) with
    mul_comm := pairAlgebra_mul_comm hp }
theorem char_of_nonneg (hp : IsCommutingPair A V) (x : pairAlgebra A V)
    (hx : 0 ≤ (x : BddOp H)) :
    letI := pairAlgebraCommCStar hp
    ∀ φ : characterSpace ℂ (pairAlgebra A V), (φ x).im = 0 ∧ 0 ≤ (φ x).re := by
  let _ := pairAlgebraCommCStar hp
  intro φ
  have e₁ : φ x ∈ spectrum ℂ (x : BddOp H) := by
    rw [← StarSubalgebra.spectrum_eq (pairAlgebra A V)]
    exact WeakDual.CharacterSpace.apply_mem_spectrum φ x
  have e₂ : IsSelfAdjoint (x : BddOp H) := IsSelfAdjoint.of_nonneg hx
  have e₃ : φ x = ((φ x).re : ℂ) := e₂.mem_spectrum_eq_re e₁
  have e₄ : (algebraMap ℝ ℂ (φ x).re) ∈ spectrum ℂ (x : BddOp H) := by
    change (((φ x).re : ℝ) : ℂ) ∈ _
    rw [← e₃]
    exact e₁
  have e₅ : (φ x).re ∈ spectrum ℝ (x : BddOp H) :=
    (spectrum.algebraMap_mem_iff ℂ).mp e₄
  refine ⟨?_, spectrum_nonneg_of_nonneg hx e₅⟩
  rw [e₃]
  simp
theorem exists_mem_pairAlgebra (hp : IsCommutingPair A V) (c : Coeffs) :
    ∃ x : pairAlgebra A V, (x : BddOp H) = evalPolyOp c A V ∧
      letI := pairAlgebraCommCStar hp
      ∀ φ : characterSpace ℂ (pairAlgebra A V),
        ∃ p : intervalCircle, φ x = evalPoly c p := by
  let _ := pairAlgebraCommCStar hp
  let a : pairAlgebra A V := ⟨A, left_mem_pairAlgebra⟩
  let v : pairAlgebra A V := ⟨V, right_mem_pairAlgebra⟩
  have hv : star v * v = 1 := Subtype.ext (star_mul_self_of_isUnitaryMap hp.unitary)
  refine ⟨evalPolyIn c a v, ?_, fun φ => ?_⟩
  · rw [evalPolyOp_eq_evalPolyIn hp.unitary]
    exact map_evalPolyIn (pairAlgebra A V).subtype c a v
  · have e₁ := char_of_nonneg hp a (IsCommutingPair.nonneg_left hp) φ
    have e₂ := char_of_nonneg hp (1 - a) (IsCommutingPair.one_sub_nonneg hp) φ
    have e₃ : φ (1 - a) = 1 - φ a := by rw [map_sub, map_one]
    rw [e₃] at e₂
    refine exists_point_char_eq hv c φ e₁.1 e₁.2 ?_
    simpa using e₂.2
end Pair
theorem statement_holds : statement := by
  intro H _ _ _ A V hp c ψ
  obtain ⟨x, hx, hφ⟩ := exists_mem_pairAlgebra hp c
  let _ := pairAlgebraCommCStar hp
  have hsup : ‖x‖ ≤ ⨆ p : intervalCircle, ‖evalPoly c p‖ := by
    refine norm_le_of_forall_char x (Real.iSup_nonneg fun p => norm_nonneg _) fun φ => ?_
    obtain ⟨p, hpφ⟩ := hφ φ
    rw [hpφ]
    exact le_ciSup (bddAbove_range_norm_evalPoly c) p
  rw [← hx]
  constructor
  · have e₁ : ‖(x : BddOp H)‖ = ‖x‖ := rfl
    calc ‖⟪ψ, (x : BddOp H) ψ⟫_ℂ‖ ≤ ‖ψ‖ * ‖(x : BddOp H) ψ‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖ψ‖ * (‖x‖ * ‖ψ‖) := by
          rw [← e₁]
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖ψ‖ * ((⨆ p : intervalCircle, ‖evalPoly c p‖) * ‖ψ‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsup (norm_nonneg _))
            (norm_nonneg _)
      _ = (⨆ p : intervalCircle, ‖evalPoly c p‖) * ‖ψ‖ ^ 2 := by ring
  · intro hpos
    obtain ⟨g, hg⟩ := exists_eq_star_mul_self_of_char_nonneg x fun φ => by
      obtain ⟨p, hpφ⟩ := hφ φ
      rw [hpφ]
      exact hpos p
    have e₁ : (x : BddOp H) = star (g : BddOp H) * g := by
      rw [hg]
      rfl
    rw [e₁]
    exact inner_star_mul_self_nonneg _ ψ
end YangMills.Construction.ContractionUnitary.PolynomialBound
end
