module

public import NoContact.Density
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace NoContact

/-- A real-valued smooth potential with compact support in `U`. -/
structure Potential (U : Set X) where
  /-- The real-valued potential `u`. -/
  toFun : X → ℝ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  support_subset : tsupport toFun ⊆ U

instance {U : Set X} : CoeFun (Potential U) (fun _ => X → ℝ) := ⟨Potential.toFun⟩

/-- Coordinate expression for the real gradient, embedded in `ℂ³`. -/
def gradient (u : X → ℝ) (x : X) : E :=
  WithLp.toLp 2 (fun j => ((fderiv ℝ u x) (EuclideanSpace.single j 1) : ℂ))

/-- A smooth potential has a continuous complex-embedded gradient. -/
theorem gradient_continuous {u : X → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (gradient u) := by
  have hd := hu.continuous_fderiv (by simp)
  unfold gradient
  fun_prop

/-- Differentiation does not enlarge topological support. -/
theorem gradient_tsupport_subset (u : X → ℝ) : tsupport (gradient u) ⊆ tsupport u := by
  apply closure_minimal ?_ isClosed_closure
  intro x hx
  by_contra hxu
  have hd : fderiv ℝ u x = 0 := by
    by_contra h
    exact hxu (support_fderiv_subset ℝ h)
  apply hx
  ext j
  simp [gradient, hd]

/-- The gradient of a compactly supported potential has compact support. -/
theorem gradient_hasCompactSupport {u : X → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (gradient u) :=
  hu.of_isClosed_subset (isClosed_tsupport _) (gradient_tsupport_subset u)

/-- A smooth compactly supported potential has an `L²` gradient. -/
theorem Potential.gradient_memLp {U : Set X} (u : Potential U) :
    MemLp (gradient u) 2 (volume : Measure X) :=
  (gradient_continuous u.smooth).memLp_of_hasCompactSupport
    (gradient_hasCompactSupport u.compact)

/-- The gradient `∇u` of a potential, as an element of `L²(ℝ³; ℂ³)`. -/
def Potential.gradientLp {U : Set X} (u : Potential U) : L2 :=
  u.gradient_memLp.toLp (gradient u)

/-- The `L²` gradient agrees almost everywhere with the pointwise derivative formula. -/
theorem Potential.gradientLp_ae {U : Set X} (u : Potential U) :
    u.gradientLp =ᵐ[volume] gradient u := MemLp.coeFn_toLp _

/-- The gradient is zero almost everywhere outside `U`. -/
theorem Potential.gradientLp_supported {U : Set X} (u : Potential U) :
    Supported U u.gradientLp := by
  filter_upwards [u.gradientLp_ae] with x hx
  intro hxU
  rw [hx]
  by_contra hn
  exact hxU (u.support_subset (gradient_tsupport_subset u (subset_tsupport _ hn)))

/-- The gradient as an element of `L²(U; ℂ³)`. -/
def Potential.gradientL2U {U : Set X} (u : Potential U) : L2U U :=
  ⟨u.gradientLp, u.gradientLp_supported⟩

/-- Regard a potential supported in `V` as one supported in a larger set `U`. -/
def Potential.mono {U V : Set X} (u : Potential V) (hVU : V ⊆ U) : Potential U :=
  ⟨u, u.smooth, u.compact, u.support_subset.trans hVU⟩

/-- Enlarging the support set preserves the ambient `L²` gradient. -/
@[simp] theorem Potential.gradientLp_mono {U V : Set X} (u : Potential V) (hVU : V ⊆ U) :
    (u.mono hVU).gradientLp = u.gradientLp := rfl

/-- A smooth compactly supported cutoff equal to one near a compact set. -/
theorem exists_cutoff {U K : Set X} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ χ : Potential U, ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by
  obtain ⟨B, hBo, hKB, hBc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨W, hWo, hKW, hWU⟩ := hK.exists_isOpen_closure_subset
    ((hBo.inter hU).mem_nhdsSet.mpr (subset_inter hKB hKU))
  have hWc : IsCompact (closure W) :=
    hBc.of_isClosed_subset isClosed_closure (hWU.trans (inter_subset_left.trans subset_closure))
  obtain ⟨V, hVo, hKV, hVW⟩ := hK.exists_isOpen_closure_subset (hWo.mem_nhdsSet.mpr hKW)
  obtain ⟨χ, hχsmooth, _, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hWo isClosed_closure hVW
  have hχts : tsupport χ = closure W := by rw [tsupport, hχsupp]
  refine ⟨⟨χ, hχsmooth, ?_, ?_⟩, V, hVo, hKV, ?_⟩
  · change IsCompact (tsupport χ)
    rwa [hχts]
  · rw [hχts]
    exact hWU.trans inter_subset_right
  · intro x hx
    exact (hχone x).mp (subset_closure hx)

/-- A potential whose gradient is exactly the `j`th coordinate vector on `K`.
It is constructed as `u_j(x) = x_j χ(x)`. -/
theorem exists_coordinate_potential {U K : Set X} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (j : Fin 3) :
    ∃ u : Potential U, ∀ x ∈ K, gradient u x = EuclideanSpace.single j (1 : ℂ) := by
  obtain ⟨χ, V, hVo, hKV, hχone⟩ := exists_cutoff hU hK hKU
  let coord : X →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j
  let u : Potential U :=
    { toFun := fun x => χ x * coord x
      smooth := χ.smooth.mul coord.contDiff
      compact := χ.compact.mul_right
      support_subset := tsupport_mul_subset_left.trans χ.support_subset }
  refine ⟨u, ?_⟩
  intro x hx
  have heq : (u : X → ℝ) =ᶠ[𝓝 x] coord := by
    filter_upwards [hVo.mem_nhds (hKV hx)] with y hy
    change χ y * coord y = coord y
    rw [hχone y hy, one_mul]
  have hd : fderiv ℝ u x = coord := heq.fderiv_eq.trans coord.fderiv
  ext k
  by_cases h : j = k <;>
    simp [gradient, hd, coord, PiLp.proj_apply, PiLp.single_apply, h, eq_comm]

/-- A gradient constant on `K` cuts to the corresponding compact indicator. -/
theorem cut_gradient_eq_compactIndicator {U K : Set X} (hK : IsCompact K)
    (u : Potential U) (c : E) (hgrad : ∀ x ∈ K, gradient u x = c) :
    cut K hK.measurableSet u.gradientLp = compactIndicator K hK c := by
  apply Lp.ext
  filter_upwards [cut_ae K hK.measurableSet u.gradientLp, u.gradientLp_ae,
    compactIndicator_ae K hK c] with x h₁ h₂ h₃
  by_cases hx : x ∈ K
  · simp_all [hgrad x hx]
  · simp_all

end NoContact
