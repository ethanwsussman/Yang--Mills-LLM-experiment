import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Continuum.TuplesOfDisjointSupports
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesAndFunctionals
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace SeparatedTuplesR4
open DisjointTuples TorusMetric
theorem norm_le_euclidNormVec (v : Fin 4 → ℝ) : ‖v‖ ≤ euclidNormVec v := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun μ => ?_
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt
    (Finset.single_le_sum (f := fun ν => v ν ^ 2) (fun ν _ => sq_nonneg _) (Finset.mem_univ μ))
theorem euclidNormVec_le_two_mul_norm (v : Fin 4 → ℝ) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
section Distance
variable {d : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ}
theorem closureWrt_euclid_eq_closure (hd : ∀ x y, d x y = euclidNormVec (x - y))
    (Z : Set (Fin 4 → ℝ)) : MetricNotions.closureWrt d Z = closure Z := by
  ext x
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨y, hy, hxy⟩ := h ε hε
    refine ⟨y, hy, ?_⟩
    rw [dist_eq_norm]
    exact (norm_le_euclidNormVec _).trans_lt (by rwa [hd] at hxy)
  · intro h r hr
    obtain ⟨y, hy, hxy⟩ := h (r / 2) (half_pos hr)
    refine ⟨y, hy, ?_⟩
    rw [dist_eq_norm] at hxy
    rw [hd]
    linarith [euclidNormVec_le_two_mul_norm (x - y)]
theorem isOpenWrt_euclid_iff (hd : ∀ x y, d x y = euclidNormVec (x - y))
    (U : Set (Fin 4 → ℝ)) : MetricNotions.IsOpenWrt d U ↔ IsOpen U := by
  rw [Metric.isOpen_iff]
  constructor
  · intro h x hx
    obtain ⟨r, hr, hU⟩ := h x hx
    refine ⟨r / 2, half_pos hr, fun y hy => hU y ?_⟩
    rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hy
    rw [hd]
    linarith [euclidNormVec_le_two_mul_norm (x - y)]
  · intro h x hx
    obtain ⟨ε, hε, hU⟩ := h x hx
    refine ⟨ε, hε, fun y hy => hU ?_⟩
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    rw [hd] at hy
    exact (norm_le_euclidNormVec _).trans_lt hy
theorem isCompactWrt_euclid_iff (hd : ∀ x y, d x y = euclidNormVec (x - y))
    (Z : Set (Fin 4 → ℝ)) : MetricNotions.IsCompactWrt d Z ↔ IsCompact Z := by
  constructor
  · intro h
    refine isCompact_of_finite_subcover fun {ι} U hU hZ => ?_
    obtain ⟨𝒱, h𝒱, hfin, hcov⟩ := h (range U)
      (by rintro _ ⟨i, rfl⟩; exact (isOpenWrt_euclid_iff hd _).2 (hU i))
      (by rwa [sUnion_range])
    classical
    have hpick : ∀ V : 𝒱, ∃ i, U i = V.1 := fun V => h𝒱 V.2
    choose g hg using hpick
    have : Finite 𝒱 := hfin
    have := Fintype.ofFinite 𝒱
    refine ⟨Finset.univ.image g, fun x hx => ?_⟩
    obtain ⟨V, hV, hxV⟩ := hcov hx
    refine mem_iUnion₂.2 ⟨g ⟨V, hV⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    rw [hg]
    exact hxV
  · intro h 𝒰 hopen hcov
    obtain ⟨𝒱, h𝒱, hfin, hsub⟩ := h.elim_finite_subcover_image (c := id)
      (fun U hU => (isOpenWrt_euclid_iff hd U).1 (hopen U hU)) (by simpa [sUnion_eq_biUnion] using hcov)
    exact ⟨𝒱, h𝒱, hfin, by simpa [sUnion_eq_biUnion] using hsub⟩
end Distance
theorem setDistR4_pos_of_disjoint {A B : Set (Fin 4 → ℝ)} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : 0 < TestFunctions.setDistR4 A B := by
  obtain ⟨δ, hδ, hdisj⟩ := h.exists_thickenings hA hB
  refine (ENNReal.ofReal_pos.2 hδ).trans_le (le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  by_contra hlt
  rw [not_le] at hlt
  have hab : dist b a < δ := by
    rw [dist_comm, dist_eq_norm]
    exact (norm_le_euclidNormVec _).trans_lt hlt
  exact Set.disjoint_left.1 hdisj (Metric.mem_thickening_iff.2 ⟨a, ha, hab⟩)
    (Metric.self_subset_thickening hδ B hb)
theorem isDisjointTuple_iff_mem_separatedAll (D : ReflectionPositivity.AxisMirror.MirrorData)
    (X : List RealFun) :
    IsDisjointTuple X ↔
      X ∈ ReflectionPositivity.AxisMirror.Ambient.separatedAll D
        ReflectionPositivity.AxisMirror.Ambient.euclidean := by
  have hd : ∀ x y : Fin 4 → ℝ,
      ReflectionPositivity.AxisMirror.Ambient.metric D
        ReflectionPositivity.AxisMirror.Ambient.euclidean x y = euclidNormVec (x - y) :=
    fun _ _ => rfl
  have hs : ∀ f : RealFun,
      (ReflectionPositivity.AxisMirror.Ambient.closedSupport D
        ReflectionPositivity.AxisMirror.Ambient.euclidean f : Set (Fin 4 → ℝ)) = tsupport f :=
    fun f => closureWrt_euclid_eq_closure hd _
  have hc : ∀ f : RealFun,
      f ∈ ReflectionPositivity.AxisMirror.Ambient.compactC1 D ℝ
          ReflectionPositivity.AxisMirror.Ambient.euclidean ↔
        SchwingerFunctions.IsC1c f := by
    intro f
    refine and_congr Iff.rfl ?_
    rw [hs f]
    exact isCompactWrt_euclid_iff hd _
  constructor
  · rintro ⟨h₁, h₂⟩
    refine mem_iUnion.2 ⟨X.length, rfl, fun f hf => (hc f).2 (h₁ f hf), ?_⟩
    refine h₂.imp fun {f g} h => ?_
    rw [hs f, hs g]
    exact h
  · intro h
    obtain ⟨n, -, h₁, h₂⟩ := mem_iUnion.1 h
    refine ⟨fun f hf => (hc f).1 (h₁ f hf), h₂.imp fun {f g} h => ?_⟩
    rw [hs f, hs g] at h
    exact h
end SeparatedTuplesR4
end YangMills.Construction
