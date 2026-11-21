import YangMills.Construction.Lattice.OneScaleGreenOperatorOnCornerCubesProof
import YangMills.Construction.Lattice.UnitMeshOperatorBounds
import YangMills.Construction.Torus.CoercivityAndWeightedBoundsOfAnAdmissiblePairProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.DirichletLaplacian.UnitMesh
open YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.ScaledFun Finset
variable {d N : ℕ} {hN : 0 < N}
theorem taxicab_symm (u v : Torus d N) : taxicabDist u v = taxicabDist v u := by apply _root_.YangMills.SharedProofs.p1021 <;> assumption
theorem taxicab_triangle (u v w : Torus d N) :
    taxicabDist u w ≤ taxicabDist u v + taxicabDist v w := by apply _root_.YangMills.Construction.PeriodicLattice.CenteredCubeDecay.taxicabDist_triangle <;> assumption
theorem addCircle_norm_coe_le_abs (t : ℝ) (hN : 0 < N) : ‖(t : AddCircle (N : ℝ))‖ ≤ |t| := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [AddCircle.norm_eq]
  have h := round_le ((N : ℝ)⁻¹ * t) 0
  have e1 : t - (round ((N : ℝ)⁻¹ * t) : ℝ) * N =
      N * ((N : ℝ)⁻¹ * t - round ((N : ℝ)⁻¹ * t)) := by
    field_simp
  have e2 : |t| = N * |(N : ℝ)⁻¹ * t - ((0 : ℤ) : ℝ)| := by
    rw [Int.cast_zero, sub_zero, abs_mul, abs_inv, abs_of_pos hp]
    field_simp
  rw [e1, abs_mul, abs_of_pos hp, e2]
  exact mul_le_mul_of_nonneg_left h hp.le
theorem exists_int_coord (x : GridPoint d (Mesh.one hN)) (μ : Fin d) :
    ∃ n : ℤ, (x : Torus d N) μ = ((n : ℝ) : AddCircle (N : ℝ)) := by
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (x.2 μ (Set.mem_univ μ))
  refine ⟨n, ?_⟩
  rw [← hn]
  change n • (((1 : ℝ)) : AddCircle (N : ℝ)) = _
  rw [← AddCircle.coe_zsmul]
  simp
section Entries
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
theorem scaledFun_sum_apply {ι : Type} (t : Finset ι) (g : ι → ScaledFun d (Mesh.one hN) X)
    (x : X) : (∑ i ∈ t, g i) x = ∑ i ∈ t, g i x := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih => rw [sum_insert ha, sum_insert ha, add_apply, ih]
open Classical in
def basisVec (p : X) : ScaledFun d (Mesh.one hN) X := ofMap fun c => if c = p then 1 else 0
omit [Fintype X] in
theorem basisVec_apply (p c : X) :
    (basisVec p : ScaledFun d (Mesh.one hN) X) c = open Classical in if c = p then 1 else 0 :=
  rfl
def matrixEntry (T : ScaledFun d (Mesh.one hN) X →ₗ[ℝ] ScaledFun d (Mesh.one hN) Y) (q : Y)
    (p : X) : ℝ := T (basisVec p) q
theorem eq_sum_basisVec (f : ScaledFun d (Mesh.one hN) X) :
    f = ∑ p, f p • (basisVec p : ScaledFun d (Mesh.one hN) X) := by
  classical
  refine ScaledFun.ext fun x => ?_
  rw [scaledFun_sum_apply]
  simp only [basisVec_apply, smul_apply, mul_ite, mul_one, mul_zero]
  exact ((sum_eq_single x (fun b _ hb => if_neg hb.symm) (by simp)).trans (if_pos rfl)).symm
theorem apply_eq_sum_matrixEntry
    (T : ScaledFun d (Mesh.one hN) X →ₗ[ℝ] ScaledFun d (Mesh.one hN) Y)
    (f : ScaledFun d (Mesh.one hN) X) (q : Y) : T f q = ∑ p, matrixEntry T q p * f p := by
  conv_lhs => rw [eq_sum_basisVec f]
  rw [map_sum, scaledFun_sum_apply]
  refine sum_congr rfl fun p _ => ?_
  rw [map_smul, smul_apply, matrixEntry, mul_comm]
theorem inner_eq_sum_mul (f g : ScaledFun d (Mesh.one hN) X) :
    inner ℝ f g = ∑ x, f x * g x := by
  rw [ScaledFun.inner_eq]
  change ∑ x, (1 : ℝ) ^ d * f x * g x = _
  simp
theorem inner_basisVec_left (p : X) (g : ScaledFun d (Mesh.one hN) X) :
    inner ℝ (basisVec p : ScaledFun d (Mesh.one hN) X) g = g p := by
  classical
  rw [inner_eq_sum_mul]
  simp only [basisVec_apply, ite_mul, one_mul, zero_mul]
  exact (sum_eq_single p (fun b _ hb => if_neg hb) (by simp)).trans (if_pos rfl)
theorem norm_sq_eq_sum_sq (f : ScaledFun d (Mesh.one hN) X) : ‖f‖ ^ 2 = ∑ x, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum_mul]
  exact sum_congr rfl fun x _ => by ring
theorem matrixEntry_adjoint (T : ScaledFun d (Mesh.one hN) X →ₗ[ℝ] ScaledFun d (Mesh.one hN) Y)
    (q : X) (p : Y) : matrixEntry (LinearMap.adjoint T) q p = matrixEntry T p q := by
  calc matrixEntry (LinearMap.adjoint T) q p
      = inner ℝ (basisVec q) (LinearMap.adjoint T (basisVec p)) :=
        (inner_basisVec_left q _).symm
    _ = inner ℝ (T (basisVec q)) (basisVec p) := LinearMap.adjoint_inner_right _ _ _
    _ = inner ℝ (basisVec p) (T (basisVec q)) := real_inner_comm _ _
    _ = matrixEntry T p q := inner_basisVec_left p _
theorem matrixEntry_comp (T₁ : ScaledFun d (Mesh.one hN) Y →ₗ[ℝ] ScaledFun d (Mesh.one hN) Z)
    (T₂ : ScaledFun d (Mesh.one hN) X →ₗ[ℝ] ScaledFun d (Mesh.one hN) Y) (q : Z) (p : X) :
    matrixEntry (T₁ ∘ₗ T₂) q p = ∑ w, matrixEntry T₁ q w * matrixEntry T₂ w p :=
  apply_eq_sum_matrixEntry T₁ (T₂ (basisVec p)) q
structure FiniteRange (pX : X → GridPoint d (Mesh.one hN)) (pY : Y → GridPoint d (Mesh.one hN))
    (T : ScaledFun d (Mesh.one hN) X →ₗ[ℝ] ScaledFun d (Mesh.one hN) Y) (mr mc r : ℝ) :
    Prop where
  row_nonneg : 0 ≤ mr
  col_nonneg : 0 ≤ mc
  far_zero : ∀ q p, r < taxicabDist (pY q : Torus d N) (pX p) → matrixEntry T q p = 0
  row_le : ∀ q, ∑ p, |matrixEntry T q p| ≤ mr
  col_le : ∀ p, ∑ q, |matrixEntry T q p| ≤ mc
variable {pX : X → GridPoint d (Mesh.one hN)} {pY : Y → GridPoint d (Mesh.one hN)}
  {pZ : Z → GridPoint d (Mesh.one hN)}
theorem FiniteRange.adjoint
    {T : ScaledFun d (Mesh.one hN) X →ₗ[ℝ] ScaledFun d (Mesh.one hN) Y}
    {mr mc r : ℝ} (h : FiniteRange pX pY T mr mc r) :
    FiniteRange pY pX (LinearMap.adjoint T) mc mr r where
  row_nonneg := h.col_nonneg
  col_nonneg := h.row_nonneg
  far_zero q p hf := by
    rw [matrixEntry_adjoint]
    exact h.far_zero p q (by rwa [taxicab_symm])
  row_le q := by simpa only [matrixEntry_adjoint] using h.col_le q
  col_le p := by simpa only [matrixEntry_adjoint] using h.row_le p
theorem FiniteRange.comp
    {T₁ : ScaledFun d (Mesh.one hN) Y →ₗ[ℝ] ScaledFun d (Mesh.one hN) Z}
    {T₂ : ScaledFun d (Mesh.one hN) X →ₗ[ℝ] ScaledFun d (Mesh.one hN) Y} {a b r a' b' r' : ℝ}
    (h₁ : FiniteRange pY pZ T₁ a b r) (h₂ : FiniteRange pX pY T₂ a' b' r') :
    FiniteRange pX pZ (T₁ ∘ₗ T₂) (a * a') (b * b') (r + r') where
  row_nonneg := mul_nonneg h₁.row_nonneg h₂.row_nonneg
  col_nonneg := mul_nonneg h₁.col_nonneg h₂.col_nonneg
  far_zero q p hf := by
    rw [matrixEntry_comp]
    refine sum_eq_zero fun w _ => ?_
    by_cases hw : r < taxicabDist (pZ q : Torus d N) (pY w)
    · rw [h₁.far_zero q w hw, zero_mul]
    · have h3 := taxicab_triangle (pZ q : Torus d N) (pY w) (pX p)
      rw [h₂.far_zero w p (by linarith), mul_zero]
  row_le q := by
    calc ∑ p, |matrixEntry (T₁ ∘ₗ T₂) q p|
        ≤ ∑ p, ∑ w, |matrixEntry T₁ q w| * |matrixEntry T₂ w p| := by
          refine sum_le_sum fun p _ => ?_
          rw [matrixEntry_comp]
          refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact sum_congr rfl fun w _ => abs_mul _ _
      _ = ∑ w, |matrixEntry T₁ q w| * ∑ p, |matrixEntry T₂ w p| := by
          rw [sum_comm]
          exact sum_congr rfl fun w _ => (mul_sum _ _ _).symm
      _ ≤ ∑ w, |matrixEntry T₁ q w| * a' :=
          sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h₂.row_le w) (abs_nonneg _)
      _ = (∑ w, |matrixEntry T₁ q w|) * a' := (sum_mul _ _ _).symm
      _ ≤ a * a' := mul_le_mul_of_nonneg_right (h₁.row_le q) h₂.row_nonneg
  col_le p := by
    calc ∑ q, |matrixEntry (T₁ ∘ₗ T₂) q p|
        ≤ ∑ q, ∑ w, |matrixEntry T₁ q w| * |matrixEntry T₂ w p| := by
          refine sum_le_sum fun q _ => ?_
          rw [matrixEntry_comp]
          refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact sum_congr rfl fun w _ => abs_mul _ _
      _ = ∑ w, (∑ q, |matrixEntry T₁ q w|) * |matrixEntry T₂ w p| := by
          rw [sum_comm]
          exact sum_congr rfl fun w _ => (sum_mul _ _ _).symm
      _ ≤ ∑ w, b * |matrixEntry T₂ w p| :=
          sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (h₁.col_le w) (abs_nonneg _)
      _ = b * ∑ w, |matrixEntry T₂ w p| := (mul_sum _ _ _).symm
      _ ≤ b * b' := mul_le_mul_of_nonneg_left (h₂.col_le p) h₁.col_nonneg
theorem matrixEntry_add (T₁ T₂ : ScaledFun d (Mesh.one hN) X →ₗ[ℝ] ScaledFun d (Mesh.one hN) Y)
    (q : Y) (p : X) : matrixEntry (T₁ + T₂) q p = matrixEntry T₁ q p + matrixEntry T₂ q p := rfl
theorem FiniteRange.add
    {T₁ T₂ : ScaledFun d (Mesh.one hN) X →ₗ[ℝ] ScaledFun d (Mesh.one hN) Y}
    {a b a' b' r : ℝ} (h₁ : FiniteRange pX pY T₁ a b r) (h₂ : FiniteRange pX pY T₂ a' b' r) :
    FiniteRange pX pY (T₁ + T₂) (a + a') (b + b') r where
  row_nonneg := add_nonneg h₁.row_nonneg h₂.row_nonneg
  col_nonneg := add_nonneg h₁.col_nonneg h₂.col_nonneg
  far_zero q p hf := by
    rw [matrixEntry_add, h₁.far_zero q p hf, h₂.far_zero q p hf, add_zero]
  row_le q := by
    calc ∑ p, |matrixEntry (T₁ + T₂) q p|
          ≤ ∑ p, (|matrixEntry T₁ q p| + |matrixEntry T₂ q p|) :=
          sum_le_sum fun p _ => abs_add_le _ _
      _ ≤ a + a' := by
          rw [sum_add_distrib]
          exact add_le_add (h₁.row_le q) (h₂.row_le q)
  col_le p := by
    calc ∑ q, |matrixEntry (T₁ + T₂) q p|
          ≤ ∑ q, (|matrixEntry T₁ q p| + |matrixEntry T₂ q p|) :=
          sum_le_sum fun q _ => abs_add_le _ _
      _ ≤ b + b' := by
          rw [sum_add_distrib]
          exact add_le_add (h₁.col_le p) (h₂.col_le p)
end Entries
section Operators
end Operators
section PointBounds
variable {X Y : Type} [Fintype X] [Fintype Y]
end PointBounds
section Norms
variable {κ : Type} [Fintype κ]
theorem abs_apply_le_normAt (f : MultiField d (Mesh.one hN) κ) (i : κ)
    (x : GridPoint d (Mesh.one hN)) : |f (i, x)| ≤ MultiField.normAt f x :=
  le_ciSup (f := fun i => |f (i, x)|) (Set.finite_range _).bddAbove i
theorem zero_le_normAt (f : MultiField d (Mesh.one hN) κ) (x : GridPoint d (Mesh.one hN)) :
    0 ≤ MultiField.normAt f x :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem abs_apply_le_maxNorm (f : MultiField d (Mesh.one hN) κ) (i : κ)
    (x : GridPoint d (Mesh.one hN)) : |f (i, x)| ≤ MultiField.maxNorm f :=
  (abs_apply_le_normAt f i x).trans
    (le_ciSup (f := fun x => MultiField.normAt f x) (Set.finite_range _).bddAbove x)
theorem zero_le_maxNorm (f : MultiField d (Mesh.one hN) κ) : 0 ≤ MultiField.maxNorm f :=
  Real.iSup_nonneg fun x => zero_le_normAt f x
theorem abs_siteFun_le_maxNorm (ζ : SiteFun d (Mesh.one hN)) (x : GridPoint d (Mesh.one hN)) :
    |ζ x| ≤ SiteFun.maxNorm ζ :=
  le_ciSup (f := fun x => |ζ x|) (Set.finite_range _).bddAbove x
theorem zero_le_siteFun_maxNorm (ζ : SiteFun d (Mesh.one hN)) :
    0 ≤ SiteFun.maxNorm ζ :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem abs_mulLeft_le {u : Torus d N} {ζ : SiteFun d (Mesh.one hN)}
    (hζ : SiteFun.SupportedIn ζ (closedMaxBall (Mesh.one hN) u))
    {F : MultiField d (Mesh.one hN) κ} {B : ℝ}
    (hF : ∀ x ∈ closedMaxBall (Mesh.one hN) u, ∀ i, |F (i, x)| ≤ B) (hB : 0 ≤ B)
    (i : κ) (x : GridPoint d (Mesh.one hN)) :
    |MultiField.mulLeft ζ F (i, x)| ≤ SiteFun.maxNorm ζ * B := by
  change |ζ x * F (i, x)| ≤ _
  by_cases hx : x ∈ closedMaxBall (Mesh.one hN) u
  · rw [abs_mul]
    exact mul_le_mul (abs_siteFun_le_maxNorm ζ x) (hF x hx i) (abs_nonneg _)
      (zero_le_siteFun_maxNorm ζ)
  · rw [hζ x hx, zero_mul, abs_zero]
    exact mul_nonneg (zero_le_siteFun_maxNorm ζ) hB
end Norms
section Inequalities
def pointwiseConst (d : ℕ) (θbar : ℝ) : ℝ :=
  4 * d * ((d : ℝ) ^ 3 * 3 ^ d * (4 * (Real.exp (|θbar| * (2 * d + 4)))))
theorem scale_bound {A c S : ℝ} (h : A ≤ c) (hS : 0 ≤ S) : A * S ≤ c * S :=
  mul_le_mul_of_nonneg_right h hS
end Inequalities
section Dirichlet
theorem FiniteRange.mono {X Y : Type} [Fintype X] [Fintype Y]
    {pX : X → GridPoint d (Mesh.one hN)} {pY : Y → GridPoint d (Mesh.one hN)}
    {T : ScaledFun d (Mesh.one hN) X →ₗ[ℝ] ScaledFun d (Mesh.one hN) Y}
    {mr mc r mr' mc' r' : ℝ} (h : FiniteRange pX pY T mr mc r) (h₁ : mr ≤ mr') (h₂ : mc ≤ mc')
    (h₃ : r ≤ r') : FiniteRange pX pY T mr' mc' r' where
  row_nonneg := h.row_nonneg.trans h₁
  col_nonneg := h.col_nonneg.trans h₂
  far_zero q p hf := h.far_zero q p (lt_of_le_of_lt h₃ hf)
  row_le q := (h.row_le q).trans h₁
  col_le p := (h.col_le p).trans h₂
variable (𝔟 : Set (Link d (Mesh.one hN))) (𝔭 : Set (Plaquette d (Mesh.one hN)))
  (𝔰 : Set (GridPoint d (Mesh.one hN)))
end Dirichlet
section Chi
variable {X : Type} [Fintype X]
end Chi
section Form
variable (𝔟 : Set (Link d (Mesh.one hN))) (𝔭 : Set (Plaquette d (Mesh.one hN)))
  (𝔰 : Set (GridPoint d (Mesh.one hN)))
end Form
section Energy
variable {X : Type} [Fintype X]
theorem abs_exp_sub_one_le_of_abs_le {t x : ℝ} (ht : |t| ≤ x) :
    |Real.exp t - 1| ≤ Real.exp x - 1 := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.abs_exp_sub_one_le_of_abs_le <;> assumption
end Energy
section Green
end Green
end YangMills.Construction.DirichletLaplacian.UnitMesh
