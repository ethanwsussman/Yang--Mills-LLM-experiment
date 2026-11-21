import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction
namespace SpectralTheory
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
structure IsOrthProj (P : H →ₗ[ℂ] H) : Prop where
  idem : P ∘ₗ P = P
  symm : ∀ x y : H, ⟪x, P y⟫_ℂ = ⟪P x, y⟫_ℂ
abbrev UnboundedOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Type _ :=
  H →ₗ.[ℂ] H
def IsSelfAdjointOp (A : UnboundedOp H) : Prop :=
  Dense (A.domain : Set H) ∧
    ∀ x z : H, (∀ y : A.domain, ⟪x, A y⟫_ℂ = ⟪z, (y : H)⟫_ℂ) ↔
      ∃ h : x ∈ A.domain, A ⟨x, h⟩ = z
end
abbrev BorelSubset (n : ℕ) : Type := {S : Set (Fin n → ℝ) // MeasurableSet S}
structure SpectralMeasure (n : ℕ) [NeZero n] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  toFun : BorelSubset n → H →ₗ[ℂ] H
  isOrthProj : ∀ S, IsOrthProj (toFun S)
  map_univ : toFun ⟨univ, MeasurableSet.univ⟩ = LinearMap.id
  map_inter : ∀ S T : BorelSubset n,
    toFun ⟨S.1 ∩ T.1, S.2.inter T.2⟩ = toFun S ∘ₗ toFun T
  tendsto_sum : ∀ S : ℕ → BorelSubset n, (Pairwise fun j k => Disjoint (S j).1 (S k).1) →
    ∀ x : H, Tendsto (fun N => ∑ j ∈ Finset.range N, toFun (S j) x) atTop
      (𝓝 (toFun ⟨⋃ j, (S j).1, MeasurableSet.iUnion fun j => (S j).2⟩ x))
namespace SpectralMeasure
variable {n m : ℕ} [NeZero n] [NeZero m] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]
instance : CoeFun (SpectralMeasure n H) fun _ => BorelSubset n → H →ₗ[ℂ] H := ⟨toFun⟩
def diag (E : SpectralMeasure n H) (x : H) (S : BorelSubset n) : ℂ := ⟪x, E S x⟫_ℂ
theorem diag_eq_norm_sq (E : SpectralMeasure n H) (x : H) (S : BorelSubset n) :
    E.diag x S = ((‖E S x‖ ^ 2 : ℝ) : ℂ) := by
  have hP := E.isOrthProj S
  have hi : E S (E S x) = E S x := LinearMap.congr_fun hP.idem x
  calc E.diag x S = ⟪x, E S (E S x)⟫_ℂ := by rw [hi]; rfl
    _ = ⟪E S x, E S x⟫_ℂ := hP.symm _ _
    _ = ((‖E S x‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
theorem map_empty (E : SpectralMeasure n H) : E ⟨∅, MeasurableSet.empty⟩ = 0 := by
  refine LinearMap.ext fun x => ?_
  have hd : Pairwise fun j k : ℕ =>
      Disjoint ((fun _ => ⟨∅, MeasurableSet.empty⟩ : ℕ → BorelSubset n) j).1
        ((fun _ => ⟨∅, MeasurableSet.empty⟩ : ℕ → BorelSubset n) k).1 :=
    fun _ _ _ => disjoint_bot_left
  have ht := E.tendsto_sum (fun _ => ⟨∅, MeasurableSet.empty⟩) hd x
  have hz := ((tendsto_add_atTop_iff_nat 1).mpr ht).sub ht
  rw [sub_self] at hz
  have hc : (fun N : ℕ => ∑ j ∈ Finset.range (N + 1), E.toFun ⟨∅, MeasurableSet.empty⟩ x -
      ∑ j ∈ Finset.range N, E.toFun ⟨∅, MeasurableSet.empty⟩ x) =
      fun _ => E.toFun ⟨∅, MeasurableSet.empty⟩ x := by
    funext N
    rw [Finset.sum_range_succ]
    abel
  have hz' : Tendsto (fun _ : ℕ => E.toFun ⟨∅, MeasurableSet.empty⟩ x) atTop (𝓝 0) := by
    rw [← hc]
    exact hz
  exact tendsto_nhds_unique tendsto_const_nhds hz'
def diagMeasure (E : SpectralMeasure n H) (x : H) : Measure (Fin n → ℝ) :=
  Measure.ofMeasurable (fun S hS => ENNReal.ofReal (‖E ⟨S, hS⟩ x‖ ^ 2))
    (by
      rw [E.map_empty]
      simp)
    (by
      intro f hf hd
      have ht := E.tendsto_sum (fun j => ⟨f j, hf j⟩) hd x
      have hc : Continuous fun v : H => (⟪x, v⟫_ℂ).re := by fun_prop
      have h₁ := (hc.tendsto _).comp ht
      have hre : ∀ S : BorelSubset n, (⟪x, E S x⟫_ℂ).re = ‖E S x‖ ^ 2 := fun S => by
        have h := congrArg Complex.re (E.diag_eq_norm_sq x S)
        rw [Complex.ofReal_re] at h
        exact h
      have h₂ : Tendsto (fun N => ∑ j ∈ Finset.range N, ‖E ⟨f j, hf j⟩ x‖ ^ 2) atTop
          (𝓝 (‖E ⟨⋃ j, f j, MeasurableSet.iUnion hf⟩ x‖ ^ 2)) := by
        rw [← hre]
        refine h₁.congr fun N => ?_
        simp only [Function.comp_apply, inner_sum, Complex.re_sum]
        exact Finset.sum_congr rfl fun j _ => hre _
      have hs := (hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity) _).2 h₂
      rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs.summable])
theorem diagMeasure_apply (E : SpectralMeasure n H) (x : H) (S : BorelSubset n) :
    E.diagMeasure x S.1 = ENNReal.ofReal (‖E S x‖ ^ 2) :=
  Measure.ofMeasurable_apply S.1 S.2
instance (E : SpectralMeasure n H) (x : H) : IsFiniteMeasure (E.diagMeasure x) :=
  ⟨by
    rw [E.diagMeasure_apply x ⟨univ, MeasurableSet.univ⟩]
    exact ENNReal.ofReal_lt_top⟩
theorem diag_eq_diagMeasure_real (E : SpectralMeasure n H) (x : H) (S : BorelSubset n) :
    E.diag x S = (((E.diagMeasure x).real S.1 : ℝ) : ℂ) := by
  rw [E.diag_eq_norm_sq, Measure.real, E.diagMeasure_apply,
    ENNReal.toReal_ofReal (by positivity)]
def integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (E : SpectralMeasure n H) (x : H) (g : (Fin n → ℝ) → F) : F :=
  ∫ y, g y ∂(E.diagMeasure x)
def lintegral (E : SpectralMeasure n H) (x : H)
    (g : (Fin n → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ y, g y ∂(E.diagMeasure x)
def IsNull (E : SpectralMeasure n H) (S : BorelSubset n) : Prop := E S = 0
def pushforward (E : SpectralMeasure n H) (Φ : (Fin n → ℝ) → Fin m → ℝ) (hΦ : Measurable Φ)
    (S : BorelSubset m) : H →ₗ[ℂ] H :=
  E ⟨Φ ⁻¹' S.1, hΦ S.2⟩
end SpectralMeasure
end SpectralTheory
end YangMills.Construction
