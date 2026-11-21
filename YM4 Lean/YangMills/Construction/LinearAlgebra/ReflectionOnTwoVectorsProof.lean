import YangMills.Construction.InfiniteLattice.BoxRepresentsTheTorusAndItsThinBoundaryLayerProof
import YangMills.Construction.LinearAlgebra.InnerProductMinorsReflectionDeterminantProof
import YangMills.Construction.LinearAlgebra.ReflectionOnTwoVectors
import Mathlib
set_option autoImplicit false
open Matrix Polynomial YangMills.Construction.TorusMetric YangMills.Construction.Exterior
noncomputable section
namespace YangMills.Construction.PeriodicLattice.HouseholderBivectorProof
theorem dotProduct_self_of_euclidNormVec_eq_one {u : Fin 4 → ℝ} (hu : euclidNormVec u = 1) :
    u ⬝ᵥ u = 1 := by apply _root_.YangMills.DeltaSharedProofs.p3944 <;> assumption
theorem wedgeProd_entry_eq (a b : Fin 4 → ℝ) (μ ν : Fin 4) :
    (wedgeProd a b).1 μ ν = a μ * b ν - b μ * a ν := by
  change (vecMulVec a b - vecMulVec b a) μ ν = _
  simp only [Matrix.sub_apply, vecMulVec_apply]
theorem wedgeProd_swap_eq_neg (a b : Fin 4 → ℝ) : wedgeProd b a = -wedgeProd a b := by apply _root_.YangMills.SharedProofs.p1483 <;> assumption
theorem wedgeProd_self_eq_zero (a : Fin 4 → ℝ) : wedgeProd a a = 0 := by
  apply Bivector.ext
  ext μ ν
  rw [wedgeProd_entry_eq]
  simp
theorem inner_wedgeProd_eq_dotProduct_mulVec (η : Bivector) (a b : Fin 4 → ℝ) :
    inner ℝ η (wedgeProd a b) = a ⬝ᵥ (η.1 *ᵥ b) := by
  have d0 : η.1 0 0 = 0 := by linarith [η.apply_swap 0 0]
  have d1 : η.1 1 1 = 0 := by linarith [η.apply_swap 1 1]
  have d2 : η.1 2 2 = 0 := by linarith [η.apply_swap 2 2]
  have d3 : η.1 3 3 = 0 := by linarith [η.apply_swap 3 3]
  rw [inner_eq_bivInner, bivInner_eq_sum_six]
  simp only [wedgeProd_entry_eq, dotProduct, mulVec, Fin.sum_univ_four, η.apply_swap 0 1,
    η.apply_swap 0 2, η.apply_swap 0 3, η.apply_swap 1 2, η.apply_swap 1 3,
    η.apply_swap 2 3, d0, d1, d2, d3]
  ring
theorem wedgeProd_mulVec_eq (a b x : Fin 4 → ℝ) :
    (wedgeProd a b).1 *ᵥ x = (b ⬝ᵥ x) • a - (a ⬝ᵥ x) • b := by
  ext μ
  simp only [mulVec, dotProduct, wedgeProd_entry_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_four]
  ring
theorem householder_mulVec_eq (u x : Fin 4 → ℝ) :
    householder u *ᵥ x = x - (2 * (u ⬝ᵥ x)) • u := by apply _root_.YangMills.SharedProofs.p79454 <;> assumption
theorem wedgeRangeProj_eq_wedgeProd {u : Fin 4 → ℝ} (hu : u ⬝ᵥ u = 1) (ω : Bivector) :
    wedgeRangeProj u ω = wedgeProd (ω.1 *ᵥ u) u := by
  have hanti : ∀ (η : Bivector) (a b : Fin 4 → ℝ),
      a ⬝ᵥ (η.1 *ᵥ b) = -(b ⬝ᵥ (η.1 *ᵥ a)) := by
    intro η a b
    rw [← inner_wedgeProd_eq_dotProduct_mulVec, ← inner_wedgeProd_eq_dotProduct_mulVec,
      wedgeProd_swap_eq_neg a b, inner_neg_right, neg_neg]
  have hzero : u ⬝ᵥ (ω.1 *ᵥ u) = 0 := by
    have := hanti ω u u
    linarith
  change (wedgeRange u).starProjection ω = _
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · refine LinearMap.mem_range.2 ⟨-(ω.1 *ᵥ u), ?_⟩
    rw [map_neg, wedgeProd_swap_eq_neg (ω.1 *ᵥ u) u, neg_neg]
  · intro w hw
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hw
    rw [inner_sub_left, inner_wedgeProd_eq_dotProduct_mulVec,
      inner_wedgeProd_eq_dotProduct_mulVec, wedgeProd_mulVec_eq,
      dotProduct_sub, dotProduct_smul, dotProduct_smul, hzero, hu, dotProduct_comm (ω.1 *ᵥ u) x,
      hanti ω x u]
    simp only [smul_eq_mul]
    ring
theorem charpoly_householder_eq {u : Fin 4 → ℝ} (hs : u ⬝ᵥ u = 1) :
    (householder u).charpoly = (X + 1) * (X - 1) ^ 3 := by
  have hform : householder u = vecMulVec ((-2 : ℝ) • u) u - scalar (Fin 4) (-1 : ℝ) := by
    ext i j
    have h1 : (scalar (Fin 4) (-1 : ℝ)) i j = -(1 : Matrix (Fin 4) (Fin 4) ℝ) i j := by
      by_cases h : i = j <;>
        simp [Matrix.scalar_apply, Matrix.one_apply, h]
    rw [Matrix.sub_apply, h1, householder, Matrix.sub_apply, Matrix.smul_apply]
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hdot : ((-2 : ℝ) • u) ⬝ᵥ u = -2 := by
    rw [smul_dotProduct, hs]
    simp
  rw [hform, charpoly_sub_scalar, charpoly_vecMulVec, hdot, Fintype.card_fin]
  simp only [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.smul_eq_C_mul, Polynomial.mul_comp, Polynomial.C_comp]
  have hc : (C (-1 : ℝ) : Polynomial ℝ) = -1 := by simp
  have hc2 : (C (-2 : ℝ) : Polynomial ℝ) = -2 := by simp only [map_neg, map_ofNat]
  rw [hc, hc2, show (4 - 1 : ℕ) = 3 from rfl]
  ring
theorem single_dotProduct_single_eq_kroneckerReal (μ ρ : Fin 4) :
    (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ⬝ᵥ Pi.single ρ 1 = kroneckerReal μ ρ := by
  fin_cases μ <;> fin_cases ρ <;> simp [kroneckerReal, dotProduct, Fin.sum_univ_four]
theorem single_dotProduct_eq_apply (ρ : Fin 4) (u : Fin 4 → ℝ) :
    (Pi.single ρ (1 : ℝ) : Fin 4 → ℝ) ⬝ᵥ u = u ρ := by apply _root_.YangMills.Construction.InfiniteLattice.BoxQuotient.coordVec_dotProduct <;> assumption
theorem householderOnBivectorsFacts_of (hext : ExteriorSquareTraceHodgeFacts)
    (hfacts : BivectorInnerMinorsReflectionDet) : HouseholderOnBivectorsFacts := by
  obtain ⟨-, -, -, -, hplaneE, hgram, hwedgeE, hminors, hspan, hcomp, hone, -, horth, hsym, htrace,
    -, -, -, -, hstarInv, -, -, -, -, -, -, -, -, -, hstarT⟩ := hext
  obtain ⟨-, -, -, hrefl, -⟩ := hfacts
  intro u hu
  have hs := dotProduct_self_of_euclidNormVec_eq_one hu
  obtain ⟨hIsym, hIorth, hIu, hIv, hdim⟩ := hrefl u hu
  have hII : householder u * householder u = 1 := by
    have h := (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).1 hIorth
    have h' : (householder u)ᵀ * householder u = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using h
    rwa [hIsym] at h'
  have hchar := charpoly_householder_eq hs
  have hroots : ((householder u).charpoly.map (algebraMap ℝ ℂ)).roots = {-1, 1, 1, 1} := by
    have hprod : (householder u).charpoly.map (algebraMap ℝ ℂ) =
        (Multiset.map (fun a : ℂ => X - C a) {-1, 1, 1, 1}).prod := by
      rw [hchar]
      simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_one]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton, Polynomial.C_neg, Polynomial.C_1,
        sub_neg_eq_add]
      ring
    rw [hprod, roots_multiset_prod_X_sub_C]
  have hdet : (householder u).det = -1 := by
    rw [det_eq_sign_charpoly_coeff, hchar, Polynomial.coeff_zero_eq_eval_zero]
    norm_num
  have hneg : householder (-u) = householder u := by
    ext i j
    simp [householder, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply]
  have hortho : (wedgeRange u).IsOrtho (orthogonalBivectors u) := by
    rw [Submodule.isOrtho_iff_inner_eq]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.1 hx
    induction hy using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨v, w, hv, hw, rfl⟩ := h
      rw [hgram, hv, hw]
      ring
    | zero => simp
    | add _ _ _ _ h1 h2 => rw [inner_add_right, h1, h2, add_zero]
    | smul c _ _ h => rw [inner_smul_right, h, mul_zero]
  have hcompl : IsCompl (wedgeRange u) (orthogonalBivectors u) := by
    refine ⟨hortho.disjoint, codisjoint_iff.2 (top_le_iff.1 ?_)⟩
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨a, b, rfl⟩
    have hperp : ∀ x : Fin 4 → ℝ, u ⬝ᵥ (x - (u ⬝ᵥ x) • u) = 0 := by
      intro x
      rw [dotProduct_sub, dotProduct_smul, hs]
      simp
    refine Submodule.mem_sup.2 ⟨wedgeProd u ((u ⬝ᵥ a) • b - (u ⬝ᵥ b) • a), ⟨_, rfl⟩,
      wedgeProd (a - (u ⬝ᵥ a) • u) (b - (u ⬝ᵥ b) • u),
      Submodule.subset_span ⟨_, _, hperp a, hperp b, rfl⟩, ?_⟩
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, wedgeProd_self_eq_zero]
    rw [wedgeProd_swap_eq_neg a u]
    module
  have hE : exteriorSq (householder u) = LinearMap.id - (2 : ℝ) • wedgeRangeProj u := by
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨a, b, rfl⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hwedgeE, householder_mulVec_eq, householder_mulVec_eq, wedgeRangeProj_eq_wedgeProd hs,
      wedgeProd_mulVec_eq]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, wedgeProd_self_eq_zero]
    rw [dotProduct_comm b u, dotProduct_comm a u, wedgeProd_swap_eq_neg u b]
    module
  have hPhalf : ∀ ω, wedgeRangeProj u ω =
      (1 / 2 : ℝ) • (ω - exteriorSq (householder u) ω) := by
    intro ω
    rw [hE]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    module
  have hinv : ∀ ω, hodge (hodge ω) = ω := fun ω => LinearMap.congr_fun hstarInv ω
  have hpt : ∀ ω, hodge (exteriorSq (householder u) ω) =
      -exteriorSq (householder u) (hodge ω) := by
    intro ω
    have h := LinearMap.congr_fun (hstarT _ hIorth) ω
    rw [hdet] at h
    simpa using h
  have hEpt : ∀ ω, hodge (exteriorSq (householder u) (hodge ω)) =
      -exteriorSq (householder u) ω := by
    intro ω
    rw [hpt, hinv]
  have hPstar : wedgeRangeProj u + hodge ∘ₗ wedgeRangeProj u ∘ₗ hodge = LinearMap.id := by
    refine LinearMap.ext fun ω => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    rw [hPhalf ω, hPhalf (hodge ω), map_smul, map_sub, hinv, hEpt]
    module
  have hEstar : hodge ∘ₗ exteriorSq (householder u) ∘ₗ hodge =
      -exteriorSq (householder u) := by
    refine LinearMap.ext fun ω => ?_
    simp only [LinearMap.comp_apply, LinearMap.neg_apply]
    exact hEpt ω
  have hinvol : exteriorSq (householder u) ∘ₗ exteriorSq (householder u) = LinearMap.id := by
    rw [← hcomp, hII, hone]
  have htr0 : bivectorTrace (exteriorSq (householder u)) = 0 := by
    have htr : (householder u).trace = 2 := by
      rw [householder, Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul, trace_vecMulVec, hs]
      simp
      norm_num
    rw [(htrace _).1, htr, pow_two (householder u), hII, Matrix.trace_one, Fintype.card_fin]
    norm_num
  have hent : ∀ μ ρ : Fin 4, householder u μ ρ = kroneckerReal μ ρ - 2 * u μ * u ρ := by
    intro μ ρ
    simp only [householder, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      vecMulVec_apply, kroneckerReal, smul_eq_mul]
    ring
  have hclosed : ∀ μ ν ρ σ : Fin 4,
      householder u μ ρ * householder u ν σ - householder u μ σ * householder u ν ρ =
        kroneckerReal μ ρ * kroneckerReal ν σ - kroneckerReal μ σ * kroneckerReal ν ρ -
          2 * householderMinorBracket u μ ν ρ σ := by
    intro μ ν ρ σ
    simp only [hent, householderMinorBracket]
    ring
  have hPentry : ∀ μ ν ρ σ : Fin 4,
      endEntry (wedgeRangeProj u) μ ν ρ σ = householderMinorBracket u μ ν ρ σ := by
    intro μ ν ρ σ
    have h1 := hminors (householder u) μ ν ρ σ
    have h2 := hclosed μ ν ρ σ
    have h3 := hgram (Pi.single μ 1) (Pi.single ν 1) (Pi.single ρ 1) (Pi.single σ 1)
    simp only [single_dotProduct_single_eq_kroneckerReal] at h3
    unfold endEntry at h1 ⊢
    rw [hPhalf, inner_smul_right, inner_sub_right, h1, h2, h3]
    ring
  have hPsingle : ∀ ρ σ : Fin 4,
      wedgeRangeProj u (wedgeProd (Pi.single ρ 1) (Pi.single σ 1)) =
        wedgeProd u (u ρ • Pi.single σ 1 - u σ • Pi.single ρ 1) := by
    intro ρ σ
    rw [wedgeRangeProj_eq_wedgeProd hs, wedgeProd_mulVec_eq, single_dotProduct_eq_apply,
      single_dotProduct_eq_apply]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
    rw [wedgeProd_swap_eq_neg u (Pi.single ρ 1), wedgeProd_swap_eq_neg u (Pi.single σ 1)]
    module
  have hunit : ∀ P : AxisPlane, ‖axisBivector P‖ = 1 := orthonormal_axisBivector.1
  have hnormE : ∀ x, ‖exteriorSq (householder u) x‖ = ‖x‖ := by
    intro x
    have h1 := hsym _ hIsym x (exteriorSq (householder u) x)
    rw [show exteriorSq (householder u) (exteriorSq (householder u) x) = x from
      LinearMap.congr_fun hinvol x, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
    exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1).symm
  have hbd : ∀ P Q : AxisPlane,
      |bivectorMatrixEntry (exteriorSq (householder u)) P Q| ≤ 1 ∧
        |bivectorMatrixEntry (wedgeRangeProj u) P Q| ≤ 1 := by
    intro P Q
    constructor
    · unfold bivectorMatrixEntry
      calc _ ≤ ‖axisBivector P‖ * ‖exteriorSq (householder u) (axisBivector Q)‖ :=
            abs_real_inner_le_norm _ _
        _ = 1 := by rw [hnormE, hunit, hunit, one_mul]
    · unfold bivectorMatrixEntry
      calc _ ≤ ‖axisBivector P‖ * ‖wedgeRangeProj u (axisBivector Q)‖ :=
            abs_real_inner_le_norm _ _
        _ = ‖wedgeRangeProj u (axisBivector Q)‖ := by rw [hunit, one_mul]
        _ ≤ ‖axisBivector Q‖ := (wedgeRange u).norm_starProjection_apply_le _
        _ = 1 := hunit Q
  have hdisj : ∀ P Q : AxisPlane, P.IsDisjoint Q →
      bivectorMatrixEntry (exteriorSq (householder u)) P Q = 0 ∧
        bivectorMatrixEntry (wedgeRangeProj u) P Q = 0 := by
    rintro P Q ⟨h1, h2, h3, h4⟩
    have hB : householderMinorBracket u P.lower P.upper Q.lower Q.upper = 0 := by
      simp [householderMinorBracket, kroneckerReal, h1, h2, h3, h4]
    constructor
    · rw [← hplaneE, hminors, hclosed, hB]
      simp [kroneckerReal, h1, h2, h3, h4]
    · rw [← hplaneE, hPentry, hB]
  exact ⟨⟨hIsym, hII, hIorth, hIu, hIv, hroots, hdet, hneg⟩, ⟨hdim, hcompl, hortho⟩,
    ⟨hE, hPstar, hEstar⟩, ⟨hsym _ hIsym, horth _ hIorth, hinvol, htr0⟩,
    ⟨hent, hminors _, hclosed, hPentry, hPsingle, hbd, hdisj⟩⟩
end YangMills.Construction.PeriodicLattice.HouseholderBivectorProof
end
