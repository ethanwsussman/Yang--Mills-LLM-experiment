import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanSpectral
abbrev BorelSubsets (X : Type*) [MeasurableSpace X] : Type _ := Subtype (MeasurableSet : Set X → Prop)
def IsEuclideanBorel (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∃ (n : ℕ) (e : Y → EuclideanSpace ℝ (Fin n)), IsEmbedding e ∧ MeasurableSet (range e)
section Measures
variable {Y : Type*} [MeasurableSpace Y]
def MeasureIsCarriedBy (μ : Measure Y) (S : BorelSubsets Y) : Prop :=
  μ S.1ᶜ = 0
def MemSqIntegrable (μ : Measure Y) (g : Y → ℂ) : Prop :=
  Measurable g ∧ ∫⁻ y, ‖g y‖ₑ ^ 2 ∂μ < ∞
def TendstoSqMean (μ : Measure Y) (f : ℕ → Y → ℂ) (g : Y → ℂ) : Prop :=
  Tendsto (fun n => ∫⁻ y, ‖f n y - g y‖ₑ ^ 2 ∂μ) atTop (𝓝 0)
end Measures
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def IsAdjointPair (T T' : H →L[ℂ] H) : Prop :=
  ∀ x y : H, ⟪x, T y⟫_ℂ = ⟪T' x, y⟫_ℂ
def IsSelfAdjointOp (T : H →L[ℂ] H) : Prop :=
  IsAdjointPair T T
def OpGe (T T' : H →L[ℂ] H) : Prop :=
  ∀ x : H, (⟪x, T' x⟫_ℂ).re ≤ (⟪x, T x⟫_ℂ).re
def scalarOp (c : ℝ) : H →L[ℂ] H :=
  (c : ℂ) • 1
def IsContractionOp (T : H →L[ℂ] H) : Prop :=
  ‖T‖ ≤ 1
structure IsUnitaryOp (T : H →L[ℂ] H) : Prop where
  bijective : Function.Bijective T
  norm_map : ∀ x : H, ‖T x‖ = ‖x‖
structure IsOrthProjection (T : H →L[ℂ] H) : Prop where
  selfAdjoint : IsSelfAdjointOp T
  idempotent : T * T = T
def fixedSet (T : H →L[ℂ] H) : Set H :=
  {x | T x = x}
def TendstoStrongly {ι : Type*} (l : Filter ι) (T : ι → H →L[ℂ] H) (T₀ : H →L[ℂ] H) : Prop :=
  ∀ x : H, Tendsto (fun i => T i x) l (𝓝 (T₀ x))
def IsStrongContinuous {X : Type*} [TopologicalSpace X] (T : X → H →L[ℂ] H) : Prop :=
  ∀ x : H, Continuous fun t => T t x
def opKernel (T : H →L[ℂ] H) : Set H :=
  {x | T x = 0}
def pmapKernel (A : H →ₗ.[ℂ] H) : Set H :=
  {x | ∃ h : x ∈ A.domain, A ⟨x, h⟩ = 0}
structure IsSelfAdjointPartial (A : H →ₗ.[ℂ] H) : Prop where
  dense : Dense (A.domain : Set H)
  symmetric : ∀ x y : A.domain, ⟪(x : H), A y⟫_ℂ = ⟪A x, (y : H)⟫_ℂ
  maximal : ∀ x x' : H, (∀ y : A.domain, ⟪x, A y⟫_ℂ = ⟪x', (y : H)⟫_ℂ) → x ∈ A.domain
def IsNonnegPartial (A : H →ₗ.[ℂ] H) : Prop :=
  ∀ x : A.domain, 0 ≤ (⟪(x : H), A x⟫_ℂ).re
end Operators
structure SpectralMeasure (Y H : Type*) [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  borelSubset : IsEuclideanBorel Y
  toFun : BorelSubsets Y → H →L[ℂ] H
  selfAdjoint : ∀ B, IsSelfAdjointOp (toFun B)
  map_univ : toFun ⟨univ, MeasurableSet.univ⟩ = 1
  map_inter : ∀ B B' : BorelSubsets Y, toFun B * toFun B' = toFun ⟨B.1 ∩ B'.1, B.2.inter B'.2⟩
  countablyAdditive : ∀ (x : H) (B : ℕ → BorelSubsets Y),
    (Pairwise fun k l => Disjoint (B k).1 (B l).1) →
      HasSum (fun k => ⟪x, toFun (B k) x⟫_ℂ)
        ⟪x, toFun ⟨⋃ k, (B k).1, MeasurableSet.iUnion fun k => (B k).2⟩ x⟫_ℂ
namespace SpectralMeasure
variable {Y H : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
instance : CoeFun (SpectralMeasure Y H) fun _ => BorelSubsets Y → H →L[ℂ] H := ⟨toFun⟩

def diagMass (E : SpectralMeasure Y H) (x : H) (B : BorelSubsets Y) : ℂ :=
  ⟪x, E B x⟫_ℂ
theorem diagMass_eq_norm_sq (E : SpectralMeasure Y H) (x : H) (B : BorelSubsets Y) :
    E.diagMass x B = ((‖E B x‖ ^ 2 : ℝ) : ℂ) := by
  have hidem : E B (E B x) = E B x := by
    have h := E.map_inter B B
    have hself : (⟨B.1 ∩ B.1, B.2.inter B.2⟩ : BorelSubsets Y) = B := Subtype.ext (inter_self _)
    rw [hself] at h
    exact congrArg (fun T : H →L[ℂ] H => T x) h
  have hinner : ⟪x, E B x⟫_ℂ = ⟪E B x, E B x⟫_ℂ := by
    have h := E.selfAdjoint B x (E B x)
    rwa [hidem] at h
  rw [diagMass, hinner, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem diagMass_empty (E : SpectralMeasure Y H) (x : H) :
    E.diagMass x ⟨∅, MeasurableSet.empty⟩ = 0 := by
  have h := E.countablyAdditive x (fun _ => ⟨∅, MeasurableSet.empty⟩)
    (fun _ _ _ => disjoint_bot_left)
  exact tendsto_nhds_unique tendsto_const_nhds h.summable.tendsto_atTop_zero
def diagMeasure (E : SpectralMeasure Y H) (x : H) : Measure Y :=
  Measure.ofMeasurable (fun s hs => ENNReal.ofReal (E.diagMass x ⟨s, hs⟩).re)
    (by simp only [diagMass_empty, Complex.zero_re, ENNReal.ofReal_zero])
    (by
      intro f hf hd
      have h := E.countablyAdditive x (fun k => ⟨f k, hf k⟩) hd
      have h' : HasSum (fun k => ((‖E ⟨f k, hf k⟩ x‖ ^ 2 : ℝ) : ℂ))
          ((‖E ⟨⋃ k, f k, MeasurableSet.iUnion hf⟩ x‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [← diagMass_eq_norm_sq, diagMass] using h
      have hr := Complex.hasSum_ofReal.mp h'
      simp only [diagMass_eq_norm_sq, Complex.ofReal_re]
      rw [← hr.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hr.summable])
def IsCarriedBy (E : SpectralMeasure Y H) (S : BorelSubsets Y) : Prop :=
  E ⟨S.1ᶜ, S.2.compl⟩ = 0
def supp (E : SpectralMeasure Y H) : Set Y :=
  {y | ∀ (U : Set Y) (hU : IsOpen U), y ∈ U → E ⟨U, hU.measurableSet⟩ ≠ 0}
theorem isClosed_supp (E : SpectralMeasure Y H) : IsClosed E.supp := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  simp only [supp, mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not] at hy
  obtain ⟨U, hU, hyU, h⟩ := hy
  refine ⟨U, fun z hz hs => hs U hU hz h, hU, hyU⟩
end SpectralMeasure
end YangMills.Construction.EuclideanSpectral
