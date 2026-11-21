import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.RefinedLattices
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set Filter InfiniteLattice
open scoped Topology ComplexConjugate InnerProductSpace ENNReal
namespace LatticePhases
structure Setup where
  L : ℕ
  admissible : Conventions.IsAdmissibleBlockingFactor L
  K : ℕ+
  β : ℝ
  β_pos : 0 < β
section Links
variable {a : ℝ}
theorem forwardFrom_mem_positiveLinks (x : LatticePoint a) (μ : Fin 4) :
    Link.forwardFrom x μ ∈ positiveLinks a :=
  ⟨μ, add_sub_cancel_left x (axisStep a μ)⟩
theorem infinite_positiveLinks (ha : 0 < a) : Infinite (positiveLinks a) := by
  refine Infinite.of_injective
    (fun n : ℕ => (⟨Link.forwardFrom ((n : ℤ) • axisStep a 0) 0,
      forwardFrom_mem_positiveLinks _ _⟩ : positiveLinks a)) ?_
  intro n n' h
  have ht : ((n : ℤ) • axisStep a 0 : LatticePoint a) = (n' : ℤ) • axisStep a 0 :=
    congrArg Link.initial (congrArg Subtype.val h)
  have hc := congrFun (congrArg Subtype.val ht) 0
  simp [axisStep] at hc
  rcases hc with hc | hc
  · exact hc
  · exact absurd hc ha.ne'
end Links
namespace Setup
variable (D : Setup)
def mesh : ℝ := refinedSpacing D.L (D.K : ℕ)
theorem mesh_eq : D.mesh = (D.L : ℝ) ^ (-((D.K : ℕ) : ℤ)) := rfl
theorem mesh_pos : 0 < D.mesh := by
  have hL : (0 : ℝ) < D.L := by
    have := D.admissible.2
    exact_mod_cast (by omega : 0 < D.L)
  rw [mesh_eq]
  exact zpow_pos hL _
def linkEnum : ℕ+ ≃ positiveLinks D.mesh :=
  haveI := infinite_positiveLinks D.mesh_pos
  Classical.choice nonempty_equiv_of_countable
def fieldDist (U U' : GaugeField D.mesh) : ℝ :=
  ∑' k : ℕ+, (2 : ℝ)⁻¹ ^ (k : ℕ) *
    Matrices.ComplexMatrix2.operatorNorm
      ((U (D.linkEnum k).1 : Matrices.ComplexMatrix2) - (U' (D.linkEnum k).1 : Matrices.ComplexMatrix2))
end Setup
section Truncation
variable {a : ℝ}
theorem opposite_mem_linksWithin_iff (S : Set AmbientSpace) (b : Link a) :
    b.opposite ∈ linksWithin S ↔ b ∈ linksWithin S :=
  and_comm
open Classical in
def truncate (S : Set AmbientSpace) (U : GaugeField a) : GaugeField a :=
  ⟨fun b => if b ∈ linksWithin S then U b else 1, fun b => by
    by_cases h : b ∈ linksWithin S
    · simp only [if_pos h, if_pos ((opposite_mem_linksWithin_iff S b).mpr h)]
      exact U.2 b
    · simp only [if_neg h, if_neg (fun h' => h ((opposite_mem_linksWithin_iff S b).mp h')),
        inv_one]⟩
end Truncation
section Measures
variable {X : Type*}
def uniformSup (F : X → ℂ) : ℝ := ⨆ x, ‖F x‖
def ProbMeasure (X : Type*) [MeasurableSpace X] : Type _ := ProbabilityMeasure X
namespace ProbMeasure
variable [MeasurableSpace X]
def toMeasure (ρ : ProbMeasure X) : Measure X := ProbabilityMeasure.toMeasure ρ
instance isProbabilityMeasure_toMeasure (ρ : ProbMeasure X) : IsProbabilityMeasure ρ.toMeasure :=
  ρ.2
def eval (ρ : ProbMeasure X) (F : X → ℂ) : ℂ := ∫ x, F x ∂ρ.toMeasure
instance instWeakTopology [TopologicalSpace X] : TopologicalSpace (ProbMeasure X) :=
  ⨅ F : C(X, ℂ), TopologicalSpace.induced (fun ρ : ProbMeasure X => ρ.eval F) inferInstance
theorem tendsto_iff_eval [TopologicalSpace X] {ι : Type*} {l : Filter ι}
    (ρs : ι → ProbMeasure X) (ρ : ProbMeasure X) :
    Tendsto ρs l (𝓝 ρ) ↔
      ∀ F : C(X, ℂ), Tendsto (fun i => (ρs i).eval F) l (𝓝 (ρ.eval F)) := by
  simp only [nhds_iInf, tendsto_iInf, nhds_induced, tendsto_comap_iff]
  rfl
abbrev Lp1 (ρ : ProbMeasure X) : Type _ := Lp ℂ 1 ρ.toMeasure
abbrev Lp2 (ρ : ProbMeasure X) : Type _ := Lp ℂ 2 ρ.toMeasure
def l2Norm (ρ : ProbMeasure X) (Y : ρ.Lp2) : ℝ := (∫ x, ‖Y x‖ ^ 2 ∂ρ.toMeasure) ^ (1 / 2 : ℝ)
theorem norm_Lp2_eq_l2Norm (ρ : ProbMeasure X) (Y : ρ.Lp2) : ‖Y‖ = ρ.l2Norm Y := by
  have h : ‖Y‖ ^ 2 = ∫ x, ‖Y x‖ ^ 2 ∂ρ.toMeasure := by
    have hi : ‖Y‖ ^ 2 = RCLike.re ⟪Y, Y⟫_ℂ := norm_sq_eq_re_inner Y
    rw [hi, L2.inner_def]
    have : ∀ x, ⟪(Y : X → ℂ) x, (Y : X → ℂ) x⟫_ℂ = ((‖Y x‖ ^ 2 : ℝ) : ℂ) := fun x => by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    simp only [this]
    rw [integral_complex_ofReal]
    simp
  rw [l2Norm, ← h, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
def HoldsAS (ρ : ProbMeasure X) (P : X → Prop) : Prop :=
  ∃ N : Set X, MeasurableSet N ∧ ρ.toMeasure N = 0 ∧ ∀ x, x ∉ N → P x
theorem holdsAS_iff (ρ : ProbMeasure X) (P : X → Prop) :
    ρ.HoldsAS P ↔ ∀ᵐ x ∂ρ.toMeasure, P x := by
  constructor
  · rintro ⟨N, -, hN, h⟩
    exact measure_mono_null (fun x hx => by_contra fun hn => hx (h x hn)) hN
  · intro h
    obtain ⟨N, hs, hm, hN⟩ := exists_measurable_superset_of_null h
    exact ⟨N, hm, hN, fun x hx => by_contra fun hn => hx (hs hn)⟩
end ProbMeasure
end Measures
end LatticePhases
end YangMills.Construction
end
