import YangMills.Construction.Blocking.DimensionAndFactorLowerBounds
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
abbrev Torus (d N : ℕ) : Type := Fin d → AddCircle (N : ℝ)
variable {d N : ℕ}
def taxicabDist (u u' : Torus d N) : ℝ := ∑ μ, ‖u μ - u' μ‖
def maxDist (u u' : Torus d N) : ℝ := ‖u - u'‖
def diagonalOne : Torus d N := fun _ => ((1 : ℝ) : AddCircle (N : ℝ))
def axisMultiple (μ : Fin d) (c : ℝ) : Torus d N := Pi.single μ (c : AddCircle (N : ℝ))
def halfOpenCube (u : Torus d N) (r : ℝ) : Set (Torus d N) :=
  {v | ∃ w : Fin d → ℝ, (∀ μ, 0 ≤ w μ ∧ w μ < r) ∧ v = u + fun μ => (w μ : AddCircle (N : ℝ))}
structure Mesh (N : ℕ) where
  h : ℝ
  h_pos : 0 < h
  count : ℕ
  count_pos : 0 < count
  period_eq : (N : ℝ) = count * h
def Mesh.one (hN : 0 < N) : Mesh N where
  h := 1
  h_pos := one_pos
  count := N
  count_pos := hN
  period_eq := by simp
variable (d) in
def gridSubgroup (s : Mesh N) : AddSubgroup (Torus d N) :=
  AddSubgroup.pi Set.univ fun _ => AddSubgroup.zmultiples ((s.h : ℝ) : AddCircle (N : ℝ))
variable (d) in
abbrev GridPoint (s : Mesh N) : Type := ↥(gridSubgroup d s)
theorem isOfFinAddOrder_mesh (s : Mesh N) :
    IsOfFinAddOrder ((s.h : ℝ) : AddCircle (N : ℝ)) := by
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨s.count, s.count_pos, ?_⟩
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul, ← s.period_eq, AddCircle.coe_period]
instance (s : Mesh N) : Finite (GridPoint d s) := by
  have : Finite (AddSubgroup.zmultiples ((s.h : ℝ) : AddCircle (N : ℝ))) :=
    finite_zmultiples.mpr (isOfFinAddOrder_mesh s)
  let f : GridPoint d s → Fin d → AddSubgroup.zmultiples ((s.h : ℝ) : AddCircle (N : ℝ)) :=
    fun x μ => ⟨x.1 μ, x.2 μ (Set.mem_univ μ)⟩
  refine Finite.of_injective f fun x y hxy => Subtype.ext (funext fun μ => ?_)
  exact congrArg Subtype.val (congrFun hxy μ)
instance (s : Mesh N) : Fintype (GridPoint d s) := Fintype.ofFinite _
def Mesh.basisStep (s : Mesh N) (μ : Fin d) : GridPoint d s :=
  ⟨axisMultiple μ s.h, fun ν _ => by
    by_cases hν : ν = μ
    · subst hν
      simp [axisMultiple, AddSubgroup.mem_zmultiples]
    · simp [axisMultiple, Pi.single_eq_of_ne hν, zero_mem]⟩
theorem sublattice_le_of_mul {s s' : Mesh N} (k : ℕ) (hk : s'.h = k * s.h) :
    gridSubgroup d s' ≤ gridSubgroup d s := by
  intro x hx μ hμ
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hx μ hμ)
  have hc : ((s'.h : ℝ) : AddCircle (N : ℝ)) = k • ((s.h : ℝ) : AddCircle (N : ℝ)) := by
    rw [hk, ← nsmul_eq_mul, AddCircle.coe_nsmul]
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨n * k, ?_⟩
  rw [← hn, hc, mul_smul, natCast_zsmul]
def ScaledFun (_d : ℕ) (_s : Mesh N) (X : Type) : Type := X → ℝ
namespace ScaledFun
variable {s : Mesh N} {X : Type}
instance : AddCommGroup (ScaledFun d s X) := inferInstanceAs (AddCommGroup (X → ℝ))
instance : Module ℝ (ScaledFun d s X) := inferInstanceAs (Module ℝ (X → ℝ))
def ofMap (f : X → ℝ) : ScaledFun d s X := f
@[simp] theorem ofMap_apply (f : X → ℝ) (x : X) : (ofMap f : ScaledFun d s X) x = f x := rfl
@[simp] theorem add_apply (f g : ScaledFun d s X) (x : X) : (f + g) x = f x + g x := rfl
@[simp] theorem smul_apply (c : ℝ) (f : ScaledFun d s X) (x : X) : (c • f) x = c * f x := rfl
theorem ext {f g : ScaledFun d s X} (h : ∀ x, f x = g x) : f = g := funext h
variable [Fintype X]
@[instance_reducible]
def innerProductCore : InnerProductSpace.Core ℝ (ScaledFun d s X) where
  inner f g := ∑ x, s.h ^ d * f x * g x
  conj_inner_symm f g := by
    simp only [conj_trivial]
    exact sum_congr rfl fun x _ => by ring
  re_inner_nonneg f := by
    simp only [RCLike.re_to_real]
    refine sum_nonneg fun x _ => ?_
    have := pow_pos s.h_pos d
    rw [mul_assoc]
    exact mul_nonneg this.le (mul_self_nonneg _)
  add_left f g k := by
    simp only [add_apply, mul_add, add_mul, sum_add_distrib]
  smul_left f g c := by
    simp only [smul_apply, conj_trivial, mul_sum]
    exact sum_congr rfl fun x _ => by ring
  definite f h := by
    have hw := pow_pos s.h_pos d
    have hz := (sum_eq_zero_iff_of_nonneg fun x _ => by
      rw [mul_assoc]; exact mul_nonneg hw.le (mul_self_nonneg (f x))).mp h
    refine ext fun x => ?_
    have hx := hz x (mem_univ x)
    rw [mul_assoc] at hx
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hw.ne')
instance : NormedAddCommGroup (ScaledFun d s X) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (ScaledFun d s X) _ _ _ innerProductCore
instance : InnerProductSpace ℝ (ScaledFun d s X) := InnerProductSpace.ofCore innerProductCore.toCore
instance : FiniteDimensional ℝ (ScaledFun d s X) := inferInstanceAs (FiniteDimensional ℝ (X → ℝ))
theorem inner_eq (f g : ScaledFun d s X) : inner ℝ f g = ∑ x, s.h ^ d * f x * g x := rfl
end ScaledFun
open ScaledFun
variable (d) in
abbrev SiteFun (s : Mesh N) : Type := ScaledFun d s (GridPoint d s)
variable (d) in
abbrev MultiField (s : Mesh N) (ι : Type) : Type := ScaledFun d s (ι × GridPoint d s)
variable (d) in
abbrev Link (s : Mesh N) : Type := Fin d × GridPoint d s
variable (d) in
abbrev OneForm (s : Mesh N) : Type := MultiField d s (Fin d)
variable (d) in
abbrev OrderedAxisPair : Type := {p : Fin d × Fin d // p.1 < p.2}
variable (d) in
abbrev TwoForm (s : Mesh N) : Type := MultiField d s (OrderedAxisPair d)
section Spaces
variable {s : Mesh N} {ι : Type}
def MultiField.comp (f : MultiField d s ι) (i : ι) : SiteFun d s := ofMap fun x => f (i, x)
theorem MultiField.inner_eq [Fintype ι] (f g : MultiField d s ι) :
    inner ℝ f g = ∑ i, ∑ x, s.h ^ d * f (i, x) * g (i, x) :=
  Fintype.sum_prod_type _
def MultiField.normAt [Fintype ι] (f : MultiField d s ι) (x : GridPoint d s) : ℝ := ⨆ i, |f (i, x)|
def MultiField.maxNorm [Fintype ι] (f : MultiField d s ι) : ℝ := ⨆ x, f.normAt x
def SiteFun.maxNorm (f : SiteFun d s) : ℝ := ⨆ x, |f x|
def Link.source (b : Link d s) : GridPoint d s := b.2
def Link.target (b : Link d s) : GridPoint d s := b.2 + s.basisStep b.1
def OneForm.pathSum (A : OneForm d s) (Γ : List (Link d s)) : ℝ := (Γ.map A).sum
open Classical in
def deltaLink (b : Link d s) : OneForm d s := ofMap fun c => if c = b then 1 else 0
end Spaces
section Operators
variable (s : Mesh N) (ι : Type)
def forwardDiff (μ : Fin d) : SiteFun d s →ₗ[ℝ] SiteFun d s where
  toFun f := ofMap fun x => s.h⁻¹ * (f (x + s.basisStep μ) - f x)
  map_add' f g := ScaledFun.ext fun x => by
    simp only [ofMap_apply, add_apply]; ring
  map_smul' c f := ScaledFun.ext fun x => by
    simp only [ofMap_apply, smul_apply, RingHom.id_apply]; ring
def discreteGrad : SiteFun d s →ₗ[ℝ] OneForm d s where
  toFun f := ofMap fun b => forwardDiff s b.1 f b.2
  map_add' f g := ScaledFun.ext fun b => by simp only [ofMap_apply, map_add, add_apply]
  map_smul' c f := ScaledFun.ext fun b => by
    simp only [ofMap_apply, map_smul, smul_apply, RingHom.id_apply]
def discreteCurl : OneForm d s →ₗ[ℝ] TwoForm d s where
  toFun A := ofMap fun q =>
    forwardDiff s q.1.1.1 (A.comp q.1.1.2) q.2 -
      forwardDiff s q.1.1.2 (A.comp q.1.1.1) q.2
  map_add' A B := ScaledFun.ext fun q => by
    have h (i : Fin d) : (A + B).comp i = A.comp i + B.comp i := rfl
    simp only [ofMap_apply, h, map_add, add_apply]; ring
  map_smul' c A := ScaledFun.ext fun q => by
    have h (i : Fin d) : (c • A).comp i = c • A.comp i := rfl
    simp only [ofMap_apply, h, map_smul, smul_apply, RingHom.id_apply]; ring
def fieldGrad : MultiField d s ι →ₗ[ℝ] MultiField d s (Fin d × ι) where
  toFun f := ofMap fun q => forwardDiff s q.1.1 (f.comp q.1.2) q.2
  map_add' f g := ScaledFun.ext fun q => by
    have h (i : ι) : (f + g).comp i = f.comp i + g.comp i := rfl
    simp only [ofMap_apply, h, map_add, add_apply]
  map_smul' c f := ScaledFun.ext fun q => by
    have h (i : ι) : (c • f).comp i = c • f.comp i := rfl
    simp only [ofMap_apply, h, map_smul, smul_apply, RingHom.id_apply]
def discreteLaplacian : SiteFun d s →ₗ[ℝ] SiteFun d s :=
  ∑ μ, LinearMap.adjoint (forwardDiff s μ) ∘ₗ forwardDiff s μ
def fieldLaplacian : MultiField d s ι →ₗ[ℝ] MultiField d s ι where
  toFun f := ofMap fun q => discreteLaplacian s (f.comp q.1) q.2
  map_add' f g := ScaledFun.ext fun q => by
    have h (i : ι) : (f + g).comp i = f.comp i + g.comp i := rfl
    simp only [ofMap_apply, h, map_add, add_apply]
  map_smul' c f := ScaledFun.ext fun q => by
    have h (i : ι) : (c • f).comp i = c • f.comp i := rfl
    simp only [ofMap_apply, h, map_smul, smul_apply, RingHom.id_apply]
end Operators
def fineScale (L j : ℕ) : ℝ := ((L : ℝ) ^ j)⁻¹
structure Scales (d L j N : ℕ) : Prop where
  bounds : Blocking.DimensionAndFactorLowerBounds d L
  even_multiple : ∃ k : ℕ, 0 < k ∧ N = 2 * k * L
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
include S
theorem factor_pos : 0 < L := by
  have := S.bounds.two_le_factor
  omega
theorem period_pos : 0 < N := by
  obtain ⟨k, hk, rfl⟩ := S.even_multiple
  have := S.factor_pos
  positivity
def fineMesh : Mesh N where
  h := fineScale L j
  h_pos := inv_pos.mpr (pow_pos (by exact_mod_cast S.factor_pos) j)
  count := N * L ^ j
  count_pos := Nat.mul_pos S.period_pos (pow_pos S.factor_pos j)
  period_eq := by
    have : ((L : ℝ) ^ j) ≠ 0 := pow_ne_zero j (by exact_mod_cast S.factor_pos.ne')
    rw [fineScale]
    push_cast
    field_simp
def unitMesh : Mesh N := Mesh.one S.period_pos
def coarseMesh : Mesh N where
  h := L
  h_pos := by exact_mod_cast S.factor_pos
  count := N / L
  count_pos := Nat.div_pos (by
    obtain ⟨k, hk, rfl⟩ := S.even_multiple
    exact Nat.le_mul_of_pos_left L (by omega)) S.factor_pos
  period_eq := by
    obtain ⟨k, _, hN⟩ := S.even_multiple
    have : L ∣ N := ⟨2 * k, by rw [hN]; ring⟩
    exact_mod_cast (Nat.div_mul_cancel this).symm
theorem unitMesh_le_fineMesh : gridSubgroup d S.unitMesh ≤ gridSubgroup d S.fineMesh := by
  refine sublattice_le_of_mul (L ^ j) ?_
  have : ((L : ℝ) ^ j) ≠ 0 := pow_ne_zero j (by exact_mod_cast S.factor_pos.ne')
  change (1 : ℝ) = ((L ^ j : ℕ) : ℝ) * fineScale L j
  rw [fineScale]
  push_cast
  field_simp
theorem coarseMesh_le_unitMesh : gridSubgroup d S.coarseMesh ≤ gridSubgroup d S.unitMesh :=
  sublattice_le_of_mul L (by change (L : ℝ) = L * 1; ring)
def unitToFine : GridPoint d S.unitMesh →+ GridPoint d S.fineMesh :=
  AddSubgroup.inclusion S.unitMesh_le_fineMesh
def coarseToUnit : GridPoint d S.coarseMesh →+ GridPoint d S.unitMesh :=
  AddSubgroup.inclusion S.coarseMesh_le_unitMesh
end Scales
open Classical in
def sitesInCube (s : Mesh N) (u : Torus d N) (r : ℝ) : Finset (GridPoint d s) :=
  univ.filter fun x => (x : Torus d N) ∈ halfOpenCube u r
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
def fineCell (y : GridPoint d S.unitMesh) : Finset (GridPoint d S.fineMesh) :=
  sitesInCube S.fineMesh y 1
def coarseCell (y' : GridPoint d S.coarseMesh) : Finset (GridPoint d S.unitMesh) :=
  sitesInCube S.unitMesh y' L
def fineSiteAverage : SiteFun d S.fineMesh →ₗ[ℝ] SiteFun d S.unitMesh where
  toFun f := ofMap fun y => ∑ x ∈ S.fineCell y, fineScale L j ^ d * f x
  map_add' f g := ScaledFun.ext fun y => by
    simp only [ofMap_apply, add_apply, mul_add, sum_add_distrib]
  map_smul' c f := ScaledFun.ext fun y => by
    simp only [ofMap_apply, smul_apply, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun x _ => by ring
def fineFormAverage : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.unitMesh where
  toFun A := ofMap fun b => ∑ x ∈ S.fineCell b.2, fineScale L j ^ d *
    ∑ t ∈ range (L ^ j), fineScale L j * A (b.1, x + t • S.fineMesh.basisStep b.1)
  map_add' A B := ScaledFun.ext fun b => by
    simp only [ofMap_apply, add_apply, mul_add, sum_add_distrib]
  map_smul' c A := ScaledFun.ext fun b => by
    simp only [ofMap_apply, smul_apply, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun x _ => sum_congr rfl fun t _ => by ring
def coarseSiteAverage : SiteFun d S.unitMesh →ₗ[ℝ] SiteFun d S.coarseMesh where
  toFun g := ofMap fun y' => ∑ y ∈ S.coarseCell y', ((L : ℝ) ^ d)⁻¹ * g y
  map_add' f g := ScaledFun.ext fun y => by
    simp only [ofMap_apply, add_apply, mul_add, sum_add_distrib]
  map_smul' c f := ScaledFun.ext fun y => by
    simp only [ofMap_apply, smul_apply, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun x _ => by ring
def coarseFormAverage : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.coarseMesh where
  toFun B := ofMap fun c => ∑ y ∈ S.coarseCell c.2, ((L : ℝ) ^ d)⁻¹ *
    ∑ t ∈ range L, (L : ℝ)⁻¹ * B (c.1, y + t • S.unitMesh.basisStep c.1)
  map_add' A B := ScaledFun.ext fun b => by
    simp only [ofMap_apply, add_apply, mul_add, sum_add_distrib]
  map_smul' c A := ScaledFun.ext fun b => by
    simp only [ofMap_apply, smul_apply, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun x _ => sum_congr rfl fun t _ => by ring
end Scales
def staircasePath {s : Mesh N} (a : GridPoint d s) (σ : Fin d → ℕ) : List (Link d s) :=
  (List.finRange d).reverse.flatMap fun μ =>
    (List.range (σ μ)).map fun t =>
      (μ, a + (∑ ν ∈ Ioi μ, σ ν • s.basisStep ν) + t • s.basisStep μ)
def firstDifferingAxis {s : Mesh N} (y' y : GridPoint d s) (h : y ≠ y') : Fin d :=
  open Classical in
  (univ.filter fun μ => (y : Torus d N) μ ≠ (y' : Torus d N) μ).min' <| by
    by_contra hne
    refine h (Subtype.ext (funext fun μ => ?_))
    by_contra hμ
    exact hne ⟨μ, by simpa using hμ⟩
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
def cellOffset (y' : GridPoint d S.coarseMesh) (y : GridPoint d S.unitMesh) : Fin d → ℕ :=
  Classical.epsilon fun σ : Fin d → ℕ =>
    (∀ μ, σ μ < L) ∧ y = S.coarseToUnit y' + ∑ μ, σ μ • S.unitMesh.basisStep μ
def treePath (y' : GridPoint d S.coarseMesh) (y : GridPoint d S.unitMesh) :
    List (Link d S.unitMesh) :=
  staircasePath (S.coarseToUnit y') (S.cellOffset y' y)
open Classical in
def treeLinks (y' : GridPoint d S.coarseMesh) : Finset (Link d S.unitMesh) :=
  (S.coarseCell y').biUnion fun y => (S.treePath y' y).toFinset
end Scales
end YangMills.Construction.PeriodicLattice
