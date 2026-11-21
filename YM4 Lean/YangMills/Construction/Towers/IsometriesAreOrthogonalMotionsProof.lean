import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.SourcesAndGluing.LatticeIsometriesAndTheirAction
import YangMills.Construction.Torus.CollinearQuadruplesProof
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import YangMills.Construction.InfiniteLattice.DilationToSpacingOneProof
import YangMills.Construction.InfiniteLattice.GroupOfLatticeIsometriesProof
import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairsProof
import YangMills.Construction.PeriodicOperators.SymbolOfAProductProof
import Mathlib
set_option autoImplicit false
open Matrix
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.OrthogonalMotions
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec torusProj torusEuclidNorm Torus4)
theorem euclidNormVec_sq (v : AmbientSpace) : euclidNormVec v ^ 2 = v ⬝ᵥ v := by apply _root_.YangMills.Construction.NormalFamilies.normSq_eq_dotProduct <;> assumption
theorem euclidNormVec_nonneg (v : AmbientSpace) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_eq_norm (v : AmbientSpace) :
    euclidNormVec v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolComp.euclidNormVec_eq_norm <;> assumption
theorem euclidNormVec_sub_le (a b : AmbientSpace) :
    euclidNormVec (a - b) ≤ euclidNormVec a + euclidNormVec b := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.euclidNormVec_sub_le <;> assumption
theorem euclidNormVec_add_le (a b : AmbientSpace) :
    euclidNormVec (a + b) ≤ euclidNormVec a + euclidNormVec b := by apply _root_.YangMills.SharedProofs.p2091 <;> assumption
theorem euclidNormVec_smul (c : ℝ) (v : AmbientSpace) :
    euclidNormVec (c • v) = |c| * euclidNormVec v := by apply _root_.YangMills.Construction.UnitSpacing.euclidNormVec_smul <;> assumption
theorem euclidNormVec_zero : euclidNormVec (0 : AmbientSpace) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
theorem euclidNormVec_basis (μ : Fin 4) : euclidNormVec (Pi.single μ 1 : AmbientSpace) = 1 := by
  have hsq : euclidNormVec (Pi.single μ 1 : AmbientSpace) ^ 2 = 1 := by
    rw [euclidNormVec_sq]
    simp
  nlinarith [euclidNormVec_nonneg (Pi.single μ 1 : AmbientSpace)]
theorem eq_zero_of_euclidNormVec_eq_zero {v : AmbientSpace} (hv : euclidNormVec v = 0) :
    v = 0 := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetryGroup.eq_zero_of_euclidNormVec_eq_zero <;> assumption
theorem abs_apply_le_euclidNormVec (v : AmbientSpace) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
theorem orth_transpose_mul_self {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : Qᵀ * Q = 1 := by apply _root_.YangMills.Construction.ConfigSpace.orth_transpose_mul_self <;> assumption
theorem orth_mul_transpose_self {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : Q * Qᵀ = 1 := by
  have hm := (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 hQ
  simpa [star_eq_conjTranspose] using hm
theorem mem_orthogonalGroup_of_transpose_mul {Q : Matrix (Fin 4) (Fin 4) ℝ} (hQ : Qᵀ * Q = 1) :
    Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  refine (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).2 ?_
  simpa [star_eq_conjTranspose] using hQ
theorem orth_transpose_mem {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : Qᵀ ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  apply mem_orthogonalGroup_of_transpose_mul
  simpa using orth_mul_transpose_self hQ
theorem euclidNormVec_orth_mulVec {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (u : AmbientSpace) :
    euclidNormVec (Q *ᵥ u) = euclidNormVec u := by apply _root_.YangMills.Construction.ConfigSpace.euclidNormVec_orth_mulVec <;> assumption
theorem orth_transpose_mulVec_mulVec {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (u : AmbientSpace) : Qᵀ *ᵥ (Q *ᵥ u) = u := by
  rw [mulVec_mulVec, orth_transpose_mul_self hQ, one_mulVec]
theorem orth_mulVec_transpose_mulVec {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (u : AmbientSpace) : Q *ᵥ (Qᵀ *ᵥ u) = u := by
  rw [mulVec_mulVec, orth_mul_transpose_self hQ, one_mulVec]
theorem matrix_eq_of_eq_on_ball {Q Q' : Matrix (Fin 4) (Fin 4) ℝ} {r : ℝ} (hr : 0 < r)
    (hQ : ∀ u : AmbientSpace, euclidNormVec u < r → Q' *ᵥ u = Q *ᵥ u) : Q' = Q := by
  ext i μ
  have hu : euclidNormVec ((r / 2) • (Pi.single μ 1 : AmbientSpace)) < r := by
    rw [euclidNormVec_smul, euclidNormVec_basis, abs_of_pos (by positivity)]
    linarith
  have e1 := congrFun (hQ _ hu) i
  rw [mulVec_smul, mulVec_smul] at e1
  have e2 : (r / 2) * (Q' *ᵥ (Pi.single μ 1 : AmbientSpace)) i =
      (r / 2) * (Q *ᵥ (Pi.single μ 1 : AmbientSpace)) i := by
    simpa using e1
  have e3 := mul_left_cancel₀ (by positivity : r / 2 ≠ 0) e2
  simpa using e3
theorem mem_openBall_iff {ϱ : ℝ≥0∞} {x : AmbientSpace} :
    x ∈ openBall ϱ ↔ ENNReal.ofReal (euclidNormVec x) < ϱ :=
  Iff.rfl
theorem sub_dotProduct_sub_self (a b : AmbientSpace) :
    (a - b) ⬝ᵥ (a - b) = a ⬝ᵥ a - 2 * (a ⬝ᵥ b) + b ⬝ᵥ b := by
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm b a]
  ring
theorem ballIsometry_linear : BallIsometryFixingOriginIsLinear := by
  intro ϱ hϱ g g0 hg
  obtain ⟨t, ht0, htϱ⟩ : ∃ t : ℝ, 0 < t ∧ ENNReal.ofReal t < ϱ := by
    obtain ⟨r, hr0, hrϱ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hϱ
    exact ⟨r, by exact_mod_cast hr0, by simpa using hrϱ⟩
  have h0 : (0 : AmbientSpace) ∈ openBall ϱ := by
    rw [mem_openBall_iff, euclidNormVec_zero]
    simpa using hϱ
  have hnorm : ∀ x ∈ openBall ϱ, euclidNormVec (g x) = euclidNormVec x := by
    intro x hx
    have hx0 := hg x hx 0 h0
    simpa [g0] using hx0
  have hdot : ∀ x ∈ openBall ϱ, ∀ x' ∈ openBall ϱ, g x ⬝ᵥ g x' = x ⬝ᵥ x' := by
    intro x hx x' hx'
    have e1 := congrArg (· ^ 2) (hg x hx x' hx')
    have e2 := congrArg (· ^ 2) (hnorm x hx)
    have e3 := congrArg (· ^ 2) (hnorm x' hx')
    simp only [euclidNormVec_sq, sub_dotProduct_sub_self] at e1 e2 e3
    linarith
  let e : Fin 4 → AmbientSpace := fun μ => t • Pi.single μ 1
  have he : ∀ μ, e μ ∈ openBall ϱ := by
    intro μ
    rw [mem_openBall_iff]
    simp only [e]
    rw [euclidNormVec_smul, euclidNormVec_basis, abs_of_pos ht0, mul_one]
    exact htϱ
  have hee : ∀ μ (x : AmbientSpace), e μ ⬝ᵥ x = t * x μ := by
    intro μ x
    simp [e, smul_dotProduct]
  let Q : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i μ => t⁻¹ * g (e μ) i
  have hQg : ∀ x ∈ openBall ϱ, Qᵀ *ᵥ g x = x := by
    intro x hx
    funext μ
    have e1 : (Qᵀ *ᵥ g x) μ = t⁻¹ * (g (e μ) ⬝ᵥ g x) := by
      simp [Q, mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [e1, hdot _ (he μ) _ hx, hee]
    field_simp
  have hQQ : Qᵀ * Q = 1 := by
    ext μ ν
    have e1 : (Qᵀ * Q) μ ν = (Qᵀ *ᵥ (fun i => Q i ν)) μ := by
      simp [Matrix.mul_apply, mulVec, dotProduct]
    have e2 : (fun i => Q i ν) = t⁻¹ • g (e ν) := by
      funext i
      simp [Q]
    rw [e1, e2, mulVec_smul, Pi.smul_apply, hQg _ (he ν)]
    simp only [e, Pi.smul_apply, smul_eq_mul, Matrix.one_apply, Pi.single_apply]
    by_cases hμν : μ = ν
    · subst hμν
      simp
      field_simp
    · simp [hμν]
  have hQ := mem_orthogonalGroup_of_transpose_mul hQQ
  refine ⟨Q, hQ, fun x hx => ?_⟩
  have hx' := orth_mulVec_transpose_mulVec hQ (g x)
  rw [hQg x hx] at hx'
  exact hx'.symm
theorem isometryOfSpace_affine : IsometryOfSpaceIsAffine := by
  intro f hf
  obtain ⟨Q, hQ, hg⟩ := ballIsometry_linear ⊤ (by simp) (fun x => f x - f 0) (by simp)
    (fun x _ x' _ => by simpa using hf x x')
  refine ⟨Q, hQ, f 0, fun x => ?_⟩
  have e1 := hg x (by rw [mem_openBall_iff]; exact ENNReal.ofReal_lt_top)
  rw [← e1]
  simp
theorem integerAffine_isometry : IntegerAffineIsIsometry := by
  intro Q hQ _ v x y
  have hxy : (Q *ᵥ x + v) - (Q *ᵥ y + v) = Q *ᵥ (x - y) := by
    rw [mulVec_sub]
    abel
  simp only [hxy]
  exact euclidNormVec_orth_mulVec hQ _
section Projection
variable {S : ℝ}
theorem torusProj_add (a b : AmbientSpace) :
    torusProj S (a + b) = torusProj S a + torusProj S b := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_add' <;> assumption
theorem torusProj_sub (a b : AmbientSpace) :
    torusProj S (a - b) = torusProj S a - torusProj S b := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_sub' <;> assumption
theorem torusProj_zero : torusProj S (0 : AmbientSpace) = 0 := rfl
theorem torusProj_surjective : Function.Surjective (torusProj S) := by apply _root_.YangMills.Construction.TestFunctions.torusProj_surjective <;> assumption
def intVec (n : Fin 4 → ℤ) : AmbientSpace := fun μ => (n μ : ℝ)
theorem torusProj_eq_zero_iff {u : AmbientSpace} :
    torusProj S u = 0 ↔ ∃ n : Fin 4 → ℤ, u = S • intVec n := by
  constructor
  · intro hu
    have e1 : ∀ μ, ∃ n : ℤ, n • S = u μ := fun μ =>
      AddCircle.coe_eq_zero_iff S |>.1 (congrFun hu μ)
    choose n hn using e1
    refine ⟨n, funext fun μ => ?_⟩
    simp [intVec, ← hn, mul_comm]
  · rintro ⟨n, rfl⟩
    funext μ
    refine (AddCircle.coe_eq_zero_iff S).2 ⟨n μ, ?_⟩
    simp [intVec, mul_comm]
def coordNormLength (x : Torus4 S) : ℝ := Real.sqrt (∑ μ, ‖x μ‖ ^ 2)
theorem isLeast_euclidNormVec_fiber (x : Torus4 S) :
    IsLeast (euclidNormVec '' (torusProj S ⁻¹' {x})) (coordNormLength x) := by
  choose b hb hb' using fun μ => TorusMetric.exists_coe_eq_abs_eq_norm (x μ)
  constructor
  · refine ⟨b, funext hb, ?_⟩
    simp only [euclidNormVec, coordNormLength, ← hb', sq_abs]
  · rintro _ ⟨v, hv, rfl⟩
    have hv' : torusProj S v = x := hv
    subst hv'
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
    have e1 : ‖torusProj S v μ‖ ≤ |v μ| := TorusMetric.addCircle_norm_coe_le_abs _
    calc ‖torusProj S v μ‖ ^ 2 ≤ |v μ| ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e1 2
      _ = v μ ^ 2 := sq_abs _
theorem torusEuclidNorm_eq_coordNormLength (x : Torus4 S) :
    torusEuclidNorm x = coordNormLength x := by apply _root_.YangMills.Construction.AmbientPoints.torusEuclidNorm_eq_sqrt <;> assumption
theorem exists_lift_euclidNormVec_eq (x : Torus4 S) :
    ∃ v : AmbientSpace, torusProj S v = x ∧ euclidNormVec v = torusEuclidNorm x := by apply _root_.YangMills.Construction.AmbientPoints.exists_torusProj_eq_euclidNormVec_eq <;> assumption
theorem torusEuclidNorm_torusProj_le (v : AmbientSpace) :
    torusEuclidNorm (torusProj S v) ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
theorem torusEuclidNorm_torusProj_of_lt (hS : 0 < S) {u : AmbientSpace}
    (hu : euclidNormVec u < S / 2) : torusEuclidNorm (torusProj S u) = euclidNormVec u := by
  rw [torusEuclidNorm_eq_coordNormLength, coordNormLength, euclidNormVec]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e1 : ‖torusProj S u μ‖ = |u μ| := by
    refine (AddCircle.norm_coe_eq_abs_iff S hS.ne').2 ?_
    rw [abs_of_pos hS]
    exact (abs_apply_le_euclidNormVec u μ).trans hu.le
  rw [e1, sq_abs]
theorem eq_of_torusProj_eq_of_lt (hS : 0 < S) {x x' : AmbientSpace}
    (hc : torusProj S x = torusProj S x') (hd : euclidNormVec (x - x') < S / 2) : x = x' := by
  have e1 := torusEuclidNorm_torusProj_of_lt hS hd
  have e2 : torusProj S (x - x') = 0 := by rw [torusProj_sub, hc, sub_self]
  have e3 : torusEuclidNorm (0 : Torus4 S) = 0 := by
    have hz := torusEuclidNorm_torusProj_of_lt (S := S) hS (u := 0)
      (by rw [euclidNormVec_zero]; positivity)
    rwa [euclidNormVec_zero, torusProj_zero] at hz
  rw [e2, e3] at e1
  exact sub_eq_zero.1 (eq_zero_of_euclidNormVec_eq_zero e1.symm)
theorem liftNorms_eq_image (a b : AmbientSpace) :
    liftNorms S a b = euclidNormVec '' (torusProj S ⁻¹' {torusProj S a - torusProj S b}) := by
  ext r
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨a - b + S • intVec n, ?_, rfl⟩
    have hn : torusProj S (S • intVec n) = 0 := torusProj_eq_zero_iff.2 ⟨n, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [torusProj_add, hn, add_zero, torusProj_sub]
  · rintro ⟨v, hv, rfl⟩
    have hv' : torusProj S v = torusProj S a - torusProj S b := hv
    have e0 : torusProj S (v - (a - b)) = 0 := by
      rw [torusProj_sub, torusProj_sub, hv', sub_self]
    obtain ⟨n, hn⟩ := torusProj_eq_zero_iff.1 e0
    refine ⟨n, ?_⟩
    have e2 : a - b + S • (fun μ => (n μ : ℝ)) = v := by
      change a - b + S • intVec n = v
      rw [← hn]
      abel
    simp only [e2]
theorem minLiftNorm_eq (a b : AmbientSpace) :
    minLiftNorm S a b = torusEuclidNorm (torusProj S a - torusProj S b) := by
  rw [minLiftNorm, liftNorms_eq_image]
  rfl
theorem isLeast_liftNorms (a b : AmbientSpace) :
    IsLeast (liftNorms S a b) (minLiftNorm S a b) := by
  have hl := isLeast_euclidNormVec_fiber (torusProj S a - torusProj S b)
  rw [minLiftNorm, liftNorms_eq_image, hl.csInf_eq]
  exact hl
end Projection
section IntegerMatrices
variable {S : ℝ}
theorem isIntegerMatrix_transpose {Q : Matrix (Fin 4) (Fin 4) ℝ} (hQ : IsIntegerMatrix Q) :
    IsIntegerMatrix Qᵀ := fun μ ν => hQ ν μ
theorem exists_mulVec_intVec {Q : Matrix (Fin 4) (Fin 4) ℝ} (hQ : IsIntegerMatrix Q)
    (n : Fin 4 → ℤ) : ∃ m : Fin 4 → ℤ, Q *ᵥ intVec n = intVec m := by
  choose z hz using hQ
  refine ⟨fun μ => ∑ ν, z μ ν * n ν, funext fun μ => ?_⟩
  simp [intVec, mulVec, dotProduct, hz]
theorem torusProj_mulVec_eq_zero {Q : Matrix (Fin 4) (Fin 4) ℝ} (hQ : IsIntegerMatrix Q)
    {u : AmbientSpace} (hu : torusProj S u = 0) : torusProj S (Q *ᵥ u) = 0 := by
  obtain ⟨n, rfl⟩ := torusProj_eq_zero_iff.1 hu
  obtain ⟨m, hm⟩ := exists_mulVec_intVec hQ n
  exact torusProj_eq_zero_iff.2 ⟨m, by rw [mulVec_smul, hm]⟩
theorem torusProj_mulVec_congr {Q : Matrix (Fin 4) (Fin 4) ℝ} (hQ : IsIntegerMatrix Q)
    {a b : AmbientSpace} (hab : torusProj S a = torusProj S b) :
    torusProj S (Q *ᵥ a) = torusProj S (Q *ᵥ b) := by
  have e1 : torusProj S (a - b) = 0 := by rw [torusProj_sub, hab, sub_self]
  have e2 := torusProj_mulVec_eq_zero hQ e1
  rw [mulVec_sub, torusProj_sub] at e2
  exact sub_eq_zero.1 e2
theorem torusEuclidNorm_mulVec_le {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (hZ : IsIntegerMatrix Q) (u : AmbientSpace) :
    torusEuclidNorm (torusProj S (Q *ᵥ u)) ≤ torusEuclidNorm (torusProj S u) := by
  obtain ⟨u', hu', hl⟩ := exists_lift_euclidNormVec_eq (torusProj S u)
  rw [← hl, ← euclidNormVec_orth_mulVec hQ u', ← torusProj_mulVec_congr hZ hu']
  exact torusEuclidNorm_torusProj_le _
theorem torusEuclidNorm_mulVec {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (hZ : IsIntegerMatrix Q) (u : AmbientSpace) :
    torusEuclidNorm (torusProj S (Q *ᵥ u)) = torusEuclidNorm (torusProj S u) := by
  refine le_antisymm (torusEuclidNorm_mulVec_le hQ hZ u) ?_
  have e1 := torusEuclidNorm_mulVec_le (S := S) (orth_transpose_mem hQ)
    (isIntegerMatrix_transpose hZ) (Q *ᵥ u)
  rwa [orth_transpose_mulVec_mulVec hQ] at e1
theorem exists_induced_isometry {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (hZ : IsIntegerMatrix Q) (v : AmbientSpace) :
    ∃ f : Torus4 S → Torus4 S,
      (∀ x : AmbientSpace, f (torusProj S x) = torusProj S (Q *ᵥ x + v)) ∧
      ∀ a b, torusEuclidNorm (f a - f b) = torusEuclidNorm (a - b) := by
  let f : Torus4 S → Torus4 S := fun x =>
    torusProj S (Q *ᵥ (Function.surjInv (torusProj_surjective (S := S)) x) + v)
  have hf : ∀ x : AmbientSpace, f (torusProj S x) = torusProj S (Q *ᵥ x + v) := by
    intro x
    simp only [f, torusProj_add]
    rw [torusProj_mulVec_congr hZ
      (Function.surjInv_eq (torusProj_surjective (S := S)) (torusProj S x))]
  refine ⟨f, hf, fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := torusProj_surjective a
  obtain ⟨b, rfl⟩ := torusProj_surjective b
  rw [hf, hf, ← torusProj_sub, ← torusProj_sub]
  have e1 : (Q *ᵥ a + v) - (Q *ᵥ b + v) = Q *ᵥ (a - b) := by
    rw [mulVec_sub]
    abel
  rw [e1, torusEuclidNorm_mulVec hQ hZ]
end IntegerMatrices
section TorusLift
variable {S : ℝ} {f : Torus4 S → Torus4 S}
def LocalAffineForm (f : Torus4 S → Torus4 S) (Q : Matrix (Fin 4) (Fin 4) ℝ)
    (a b : AmbientSpace) : Prop :=
  ∀ x : AmbientSpace, euclidNormVec x < S / 4 → f (torusProj S (a + x)) = torusProj S (b + Q *ᵥ x)
theorem exists_localAffineForm (hS : 0 < S)
    (hf : ∀ a b, torusEuclidNorm (f a - f b) = torusEuclidNorm (a - b)) (a b : AmbientSpace)
    (hb : torusProj S b = f (torusProj S a)) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ, LocalAffineForm f Q a b := by
  have hex : ∀ x : AmbientSpace, euclidNormVec x < S / 4 →
      ∃ k, euclidNormVec k < S / 4 ∧ torusProj S k = f (torusProj S (a + x)) - torusProj S b := by
    intro x hx
    obtain ⟨k, hk, hk'⟩ := exists_lift_euclidNormVec_eq (f (torusProj S (a + x)) - torusProj S b)
    refine ⟨k, ?_, hk⟩
    rw [hk', hb, hf, torusProj_add, add_sub_cancel_left,
      torusEuclidNorm_torusProj_of_lt hS (by linarith)]
    exact hx
  classical
  let G : AmbientSpace → AmbientSpace := fun x =>
    if hx : euclidNormVec x < S / 4 then (hex x hx).choose else 0
  have hG : ∀ x, euclidNormVec x < S / 4 →
      euclidNormVec (G x) < S / 4 ∧ torusProj S (G x) = f (torusProj S (a + x)) - torusProj S b := by
    intro x hx
    simp only [G, dif_pos hx]
    exact (hex x hx).choose_spec
  have hz : euclidNormVec (0 : AmbientSpace) < S / 4 := by rw [euclidNormVec_zero]; positivity
  have G0 : G 0 = 0 := by
    obtain ⟨g1, g2⟩ := hG 0 hz
    refine eq_of_torusProj_eq_of_lt hS ?_ (by rw [sub_zero]; linarith)
    rw [g2, add_zero, hb, sub_self, torusProj_zero]
  have hmem : ∀ x, x ∈ openBall (ENNReal.ofReal (S / 4)) ↔ euclidNormVec x < S / 4 := by
    intro x
    rw [mem_openBall_iff]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity)
  have hiso : ∀ x ∈ openBall (ENNReal.ofReal (S / 4)), ∀ x' ∈ openBall (ENNReal.ofReal (S / 4)),
      euclidNormVec (G x - G x') = euclidNormVec (x - x') := by
    intro x hx x' hx'
    have hx1 := (hmem x).1 hx
    have hx2 := (hmem x').1 hx'
    obtain ⟨a1, a2⟩ := hG x hx1
    obtain ⟨b1, b2⟩ := hG x' hx2
    have l1 : euclidNormVec (G x - G x') < S / 2 := by
      have := euclidNormVec_sub_le (G x) (G x')
      linarith
    have l2 : euclidNormVec (x - x') < S / 2 := by
      have := euclidNormVec_sub_le x x'
      linarith
    rw [← torusEuclidNorm_torusProj_of_lt hS l1, ← torusEuclidNorm_torusProj_of_lt hS l2,
      torusProj_sub, a2, b2, sub_sub_sub_cancel_right, hf, ← torusProj_sub,
      add_sub_add_left_eq_sub, torusProj_sub]
  obtain ⟨Q, hQ, hQG⟩ := ballIsometry_linear (ENNReal.ofReal (S / 4))
    (by simpa using (by positivity : 0 < S / 4)) G G0 hiso
  refine ⟨Q, hQ, fun x hx => ?_⟩
  have e1 := (hG x hx).2
  rw [hQG x ((hmem x).2 hx)] at e1
  have e2 : torusProj S (b + Q *ᵥ x) = f (torusProj S (a + x)) := by
    rw [torusProj_add, e1, add_sub_cancel]
  exact e2.symm
theorem LocalAffineForm.translate (hS : 0 < S)
    (hf : ∀ a b, torusEuclidNorm (f a - f b) = torusEuclidNorm (a - b))
    {Q : Matrix (Fin 4) (Fin 4) ℝ} (hQ : Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ)
    {a b y : AmbientSpace} (hloc : LocalAffineForm f Q a b) (hy : euclidNormVec y < S / 4) :
    LocalAffineForm f Q (a + y) (b + Q *ᵥ y) := by
  have hb : torusProj S (b + Q *ᵥ y) = f (torusProj S (a + y)) := (hloc y hy).symm
  obtain ⟨Q', hQ', hloc'⟩ := exists_localAffineForm hS hf (a + y) _ hb
  have hpos : 0 < S / 4 - euclidNormVec y := by linarith
  have heq : Q' = Q := by
    refine matrix_eq_of_eq_on_ball hpos fun w hw => ?_
    have hy0 := euclidNormVec_nonneg y
    have hyw : euclidNormVec (y + w) < S / 4 := by
      have := euclidNormVec_add_le y w
      linarith
    have e1 := hloc' w (by linarith)
    have e2 := hloc (y + w) hyw
    rw [← add_assoc] at e2
    rw [e1, mulVec_add, ← add_assoc, torusProj_add (b + Q *ᵥ y) (Q' *ᵥ w),
      torusProj_add (b + Q *ᵥ y) (Q *ᵥ w)] at e2
    have e3 := add_left_cancel e2
    refine eq_of_torusProj_eq_of_lt hS e3 ?_
    have := euclidNormVec_sub_le (Q' *ᵥ w) (Q *ᵥ w)
    rw [euclidNormVec_orth_mulVec hQ', euclidNormVec_orth_mulVec hQ] at this
    linarith
  rw [heq] at hloc'
  exact hloc'
theorem LocalAffineForm.iterate (hS : 0 < S)
    (hf : ∀ a b, torusEuclidNorm (f a - f b) = torusEuclidNorm (a - b))
    {Q : Matrix (Fin 4) (Fin 4) ℝ} (hQ : Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ)
    {v y : AmbientSpace} (hloc : LocalAffineForm f Q 0 v) (hy : euclidNormVec y < S / 4) (i : ℕ) :
    LocalAffineForm f Q ((i : ℝ) • y) (v + Q *ᵥ ((i : ℝ) • y)) := by
  induction i with
  | zero => simpa using hloc
  | succ i ih =>
    have e1 := ih.translate hS hf hQ hy
    have e2 : ((i + 1 : ℕ) : ℝ) • y = (i : ℝ) • y + y := by
      rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    rw [e2, mulVec_add, ← add_assoc]
    exact e1
theorem exists_globalAffineForm (hS : 0 < S)
    (hf : ∀ a b, torusEuclidNorm (f a - f b) = torusEuclidNorm (a - b)) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∃ v : AmbientSpace, ∀ x : AmbientSpace,
      f (torusProj S x) = torusProj S (Q *ᵥ x + v) := by
  obtain ⟨v, hv⟩ := torusProj_surjective (f (torusProj S 0))
  obtain ⟨Q, hQ, hloc⟩ := exists_localAffineForm hS hf 0 v hv
  refine ⟨Q, hQ, v, fun x => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (euclidNormVec x / (S / 4))
  have hM : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hy : euclidNormVec ((((N + 1 : ℕ) : ℝ))⁻¹ • x) < S / 4 := by
    rw [euclidNormVec_smul, abs_of_pos (inv_pos.2 hM), inv_mul_lt_iff₀ hM]
    have e1 : euclidNormVec x < N * (S / 4) := (div_lt_iff₀ (by positivity)).1 hN
    push_cast
    nlinarith
  have e2 := LocalAffineForm.iterate hS hf hQ hloc hy (N + 1) 0
    (by rw [euclidNormVec_zero]; positivity)
  rw [smul_smul, mul_inv_cancel₀ hM.ne', one_smul, add_zero, mulVec_zero, add_zero] at e2
  rw [e2, add_comm]
theorem isIntegerMatrix_of_globalAffineForm (hS : 0 < S) {Q : Matrix (Fin 4) (Fin 4) ℝ}
    {v : AmbientSpace} (hg : ∀ x : AmbientSpace, f (torusProj S x) = torusProj S (Q *ᵥ x + v)) :
    IsIntegerMatrix Q := by
  intro μ ν
  have e1 : torusProj S (S • (Pi.single ν 1 : AmbientSpace)) = 0 :=
    torusProj_eq_zero_iff.2 ⟨Pi.single ν 1, by
      congr 1
      funext κ
      by_cases hκ : κ = ν
      · subst hκ; simp [intVec]
      · simp [intVec, Pi.single_eq_of_ne hκ]⟩
  have e2 := hg (S • (Pi.single ν 1 : AmbientSpace))
  have e3 := hg 0
  rw [e1] at e2
  rw [torusProj_zero, mulVec_zero, zero_add] at e3
  rw [e3, torusProj_add] at e2
  have e4 : torusProj S (Q *ᵥ (S • (Pi.single ν 1 : AmbientSpace))) = 0 :=
    add_right_cancel (e2.symm.trans (zero_add _).symm)
  obtain ⟨n, hn⟩ := torusProj_eq_zero_iff.1 e4
  refine ⟨n μ, ?_⟩
  have e5 := congrFun hn μ
  rw [mulVec_smul] at e5
  have e6 : S * Q μ ν = S * (n μ : ℝ) := by
    simpa [intVec] using e5
  exact mul_left_cancel₀ hS.ne' e6
theorem image_latticeSubgroup {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (hZ : IsIntegerMatrix Q) :
    (fun x : AmbientSpace => Q *ᵥ x) '' (InfiniteLattice.latticeSubgroup S : Set AmbientSpace) =
      InfiniteLattice.latticeSubgroup S := by
  have key : ∀ {A : Matrix (Fin 4) (Fin 4) ℝ}, IsIntegerMatrix A → ∀ x : AmbientSpace,
      x ∈ InfiniteLattice.latticeSubgroup S → A *ᵥ x ∈ InfiniteLattice.latticeSubgroup S := by
    rintro A hA x ⟨n, hn⟩
    obtain ⟨m, hm⟩ := exists_mulVec_intVec hA n
    have hx : x = S • intVec n := by
      funext μ
      simp [hn, intVec, mul_comm]
    refine ⟨m, fun μ => ?_⟩
    rw [hx, mulVec_smul, hm]
    simp [intVec, mul_comm]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact key hZ x hx
  · intro hy
    exact ⟨Qᵀ *ᵥ y, key (isIntegerMatrix_transpose hZ) y hy, orth_mulVec_transpose_mulVec hQ y⟩
end TorusLift
theorem torusSide_pos {L n : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    0 < PeriodicLattice.torusSide L n := by
  have hL0 : 0 < L := by have := hL.2; omega
  unfold PeriodicLattice.torusSide
  positivity
theorem classification_holds : Classification := by
  refine ⟨ballIsometry_linear, isometryOfSpace_affine, integerAffine_isometry,
    fun L n hL _ => ?_⟩
  have hS := torusSide_pos (n := n) hL
  refine ⟨isLeast_liftNorms, ?_, ?_, ?_⟩
  · intro a b a' b' ha hb
    rw [minLiftNorm_eq, minLiftNorm_eq, ha, hb]
  · intro f hf
    obtain ⟨Q, hQ, v, hg⟩ := exists_globalAffineForm hS hf
    exact ⟨Q, hQ, image_latticeSubgroup hQ (isIntegerMatrix_of_globalAffineForm hS hg), v, hg⟩
  · intro Q hQ hZ v
    exact exists_induced_isometry hQ hZ v
end YangMills.Construction.Tower.OrthogonalMotions
end
