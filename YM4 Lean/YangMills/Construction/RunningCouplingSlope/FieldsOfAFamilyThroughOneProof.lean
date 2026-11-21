import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreIsSmoothProof
import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOne
import YangMills.Construction.RunningCouplingSlope.FieldsOfAFamilyThroughOne
import YangMills.Construction.RunningCouplingSlope.PlainAverageIsAnalytic
import YangMills.Construction.RunningCouplingSlope.PlainAverageOfARealField
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace LevelFieldsAlongFamily
open Tower
variable {L n k : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private theorem analyticAt_inv_of_eq_one {f : E → Matrices.ComplexMatrix2}
    (hf : AnalyticAt ℝ f p₀) (hu : f p₀ = 1) :
    AnalyticAt ℝ (fun y => (f y)⁻¹) p₀ := by
  have e : (fun y => (f y)⁻¹) = Ring.inverse ∘ f := by
    funext y
    simp [Matrix.nonsing_inv_eq_ringInverse]
  rw [e]
  refine AnalyticAt.comp ?_ hf
  rw [hu]
  simpa using analyticAt_inverse (𝕜 := ℝ) (1 : Matrices.ComplexMatrix2ˣ)
private theorem inv_mem_compact {g : Matrices.ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem inv_inv_of_mem_compact {g : Matrices.ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
private theorem levelField_of_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
private theorem levelField_of_not_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : ¬b.IsPositivelyOriented) :
    levelField X (j + 1) b = (levelField X (j + 1) b.opposite)⁻¹ := by apply _root_.YangMills.SharedProofs.p5483 <;> assumption
private theorem radius_mean_at_unit (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    meanRadius (fun _ : Edge L n k j => (1 : Matrices.ComplexMatrix2)) c = 1 ∧
      normalizedMean (fun _ : Edge L n k j => (1 : Matrices.ComplexMatrix2)) c = 1 := by
  have h := hD L hL n k j hn hj 0 (Submodule.zero_mem _) c hc
  exact ⟨h.2.1, h.2.2.1⟩
private theorem analyticAt_radius_mean (hA : NormalizedMeanAnalytic)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j < k) {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented)
    {V : E → Edge L n k j → Matrices.ComplexMatrix2}
    (hV : ∀ b, AnalyticAt ℝ (fun p => V p b) p₀)
    (h₁ : V p₀ = fun _ => 1) :
    AnalyticAt ℝ (fun p => meanRadius (V p) c) p₀ ∧
      AnalyticAt ℝ (fun p => normalizedMean (V p) c) p₀ := by
  have hL2 : 0 < L := by
    have := hL.2
    omega
  have : NeZero L := ⟨by omega⟩
  have hfin : Finite (Edge L n k j) := PeriodicLattice.instFiniteBond _
  let _ := Fintype.ofFinite (Edge L n k j)
  obtain ⟨ρ, hρ, H⟩ := hA L hL
  have hone : (fun _ : Edge L n k j => (1 : Matrices.ComplexMatrix2)) ∈
      fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
    refine ⟨fun b _ => ?_, fun b _ => ?_⟩
    · show Matrix.det (1 : Matrices.ComplexMatrix2) = 1
      simp
    · simp
  obtain ⟨a₁, a₂⟩ := H n k j hn hj _ hone (fun b => by simpa using hρ) c hc
  have hVa : AnalyticAt ℝ V p₀ := analyticAt_pi_iff.2 hV
  rw [← h₁] at a₁ a₂
  exact ⟨AnalyticAt.comp (g := fun V' : Edge L n k j → Matrices.ComplexMatrix2 => meanRadius V' c)
      (a₁.restrictScalars (𝕜 := ℝ)) hVa,
    AnalyticAt.comp (g := fun V' : Edge L n k j → Matrices.ComplexMatrix2 => normalizedMean V' c)
      (a₂.restrictScalars (𝕜 := ℝ)) hVa⟩
private theorem levels_analytic_unit (hA : NormalizedMeanAnalytic)
    (hD : NormalizedMeanAtOne) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {X : E → ChainPoint L n k} (hX : IsAnalyticFamilyThroughUnit X p₀) :
    ∀ j, j ≤ k → (∀ b : Edge L n k j, AnalyticAt ℝ (fun p => levelField (X p) j b) p₀) ∧
      levelField (X p₀) j = fun _ => 1 := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨hX.analyticAt_fine, ?_⟩
    rw [hX.eq_unit]
    rfl
  | succ j ih =>
    intro hj'
    have hj : j < k := hj'
    obtain ⟨ha, hv⟩ := ih hj.le
    have pos : ∀ (b : Edge L n k (j + 1)) (hb : b.IsPositivelyOriented),
        AnalyticAt ℝ (fun p => levelField (X p) (j + 1) b) p₀ ∧
          levelField (X p₀) (j + 1) b = 1 := by
      intro b hb
      have hn₁ : (X p₀).noise ⟨j, hj⟩ ⟨b, hb⟩ = 1 := by
        rw [hX.eq_unit]
        rfl
      constructor
      · simp only [levelField_of_pos _ hj hb]
        exact (hX.analyticAt_noise _ _).mul (analyticAt_radius_mean hA hL hn hj hb ha hv).2
      · rw [levelField_of_pos _ hj hb, hn₁, hv, (radius_mean_at_unit hD hL hn hj hb).2, one_mul]
    have all : ∀ b : Edge L n k (j + 1),
        AnalyticAt ℝ (fun p => levelField (X p) (j + 1) b) p₀ ∧
          levelField (X p₀) (j + 1) b = 1 := by
      intro b
      by_cases hb : b.IsPositivelyOriented
      · exact pos b hb
      · obtain ⟨a, v⟩ := pos b.opposite (PeriodicLattice.Bond.opposite_isPositivelyOriented hb)
        constructor
        · simp only [levelField_of_not_pos _ hj hb]
          exact analyticAt_inv_of_eq_one a v
        · rw [levelField_of_not_pos _ hj hb, v]
          simp
    exact ⟨fun b => (all b).1, funext fun b => (all b).2⟩
private theorem isCompactValued_of_near (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {ρ : ℝ}
    (H : ∀ j, j < k → ∀ V ∈ fieldSpace L n k j,
      (∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < ρ) →
      ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup)
    {X : ChainPoint L n k} (h₀ : X.fine ∈ fieldSpace L n k 0)
    (hn' : ∀ i c, X.noise i c ∈ PeriodicLattice.compactGaugeGroup)
    (hs : ∀ j ∈ Finset.range (k + 1), ∀ b : Edge L n k j,
      Matrices.ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ) :
    IsCompactValued X := by
  refine ⟨hn', fun j => ?_⟩
  induction j with
  | zero => exact fun _ => h₀
  | succ j ih =>
    intro hj'
    have hj : j < k := hj'
    have hc := ih hj.le
    have hL2 : 2 ≤ L := by
      have := hL.2
      omega
    have hx : ∀ b : Edge L n k (j + 1),
        Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun b =>
      PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
        (by simp only [PeriodicLattice.levelDepth]; omega) b
    have pos : ∀ (b : Edge L n k (j + 1)), b.IsPositivelyOriented →
        levelField X (j + 1) b ∈ PeriodicLattice.compactGaugeGroup := fun b hb => by
      rw [levelField_of_pos X hj hb]
      exact Submonoid.mul_mem _ (hn' _ _)
        (H j hj _ hc (hs j (Finset.mem_range.2 (by omega))) b hb)
    refine ⟨fun b _ => ?_, fun b _ => ?_⟩
    · by_cases hb : b.IsPositivelyOriented
      · exact pos b hb
      · rw [levelField_of_not_pos X hj hb]
        exact inv_mem_compact (pos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb))
    · by_cases hb : b.IsPositivelyOriented
      · have hr : ¬b.opposite.IsPositivelyOriented := by
          rcases hx b with ⟨_, h₂⟩ | h₂
          · exact h₂
          · exact absurd hb h₂.2
        exact levelField_of_not_pos X hj hr
      · rw [levelField_of_not_pos X hj hb,
          inv_inv_of_mem_compact (pos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb))]
end LevelFieldsAlongFamily
open Tower LevelFieldsAlongFamily in
theorem LevelFieldsAnalyticAlongFamily.holds (hA : NormalizedMeanAnalytic)
    (hD : NormalizedMeanAtOne)
    (hR : NormalizedMeanOfCompactField) : LevelFieldsAnalyticAlongFamily := by
  intro L hL k n hk hn E _ _ X p₀ hX
  have lv := levels_analytic_unit hA hD hL hn hX
  refine ⟨fun j hj b => ⟨(lv j hj).1 b, congrFun (lv j hj).2 b⟩, fun i c => ?_, ?_⟩
  · obtain ⟨ha, hv⟩ := lv i i.2.le
    constructor
    · exact (analyticAt_radius_mean hA hL hn i.2 c.2 ha hv).1
    · rw [hv]
      exact (radius_mean_at_unit hD hL hn i.2 c.2).1
  · obtain ⟨ρ, hρ, H⟩ := hR L hL
    have hfin : ∀ j, Finite (Edge L n k j) := fun j => by
      have : NeZero L := ⟨by have := hL.2; omega⟩
      exact PeriodicLattice.instFiniteBond _
    have near : ∀ j ∈ Finset.range (k + 1), ∀ᶠ p in 𝓝 p₀, ∀ b : Edge L n k j,
        Matrices.ComplexMatrix2.operatorNorm (levelField (X p) j b - 1) < ρ := by
      intro j hj
      have := hfin j
      obtain ⟨ha, hv⟩ := lv j (by have := Finset.mem_range.1 hj; omega)
      refine eventually_all.2 fun b => ?_
      have h₁ := (ha b).continuousAt.eventually (Metric.ball_mem_nhds _ hρ)
      filter_upwards [h₁] with p hp
      have h₂ := Metric.mem_ball.1 hp
      rw [dist_eq_norm, hv] at h₂
      exact h₂
    filter_upwards [(eventually_all_finset _).2 near, hX.eventually_compact] with p h₁ h₂
    exact isCompactValued_of_near hL hn (fun j hj V hV hs c hc => (H n k j hn hj V hV hs c hc).2.2)
      h₂.1 h₂.2 h₁
end YangMills.Construction.RunningCouplingSlope
end
