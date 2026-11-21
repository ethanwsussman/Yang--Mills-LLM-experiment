import YangMills.Construction.ReflectionPositivity.FactsOfTheCoveringMapProof
import YangMills.Construction.ReflectionPositivity.MirrorAndItsOpenSidesPartTheSpace
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenCopiesAtEveryDatumProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.PartitionProof
private theorem period_pos (D : MirrorData) : 0 < D.side := by apply _root_.YangMills.SharedProofs.p8577 <;> assumption
private theorem eq_of_halfOpen_of_sub_mul {ℓ a b : ℝ} (hℓ : 0 < ℓ) (n : ℤ) (ha₁ : -(ℓ / 2) < a)
    (ha₂ : a ≤ ℓ / 2) (hb₁ : -(ℓ / 2) < b) (hb₂ : b ≤ ℓ / 2) (h : a = b + ℓ * n) : a = b := by
  have hn : n = 0 := by
    have u : ℓ * (n : ℝ) < ℓ * 1 := by linarith
    have v : ℓ * (-1 : ℝ) < ℓ * (n : ℝ) := by linarith
    have u' : (n : ℝ) < 1 := lt_of_mul_lt_mul_left u hℓ.le
    have v' : (-1 : ℝ) < n := lt_of_mul_lt_mul_left v hℓ.le
    have w₁ : n < 1 := by exact_mod_cast u'
    have w₂ : -1 < n := by exact_mod_cast v'
    omega
  subst hn
  simpa using h
private theorem exists_centered_rep {ℓ : ℝ} (hℓ : 0 < ℓ) (c α : ℝ) :
    ∃ (ρ : ℝ) (n : ℤ), -(ℓ / 2) < ρ ∧ ρ ≤ ℓ / 2 ∧ α = c + ρ + ℓ * n := by
  obtain ⟨k, ⟨hk₁, hk₂⟩, -⟩ := existsUnique_sub_zsmul_mem_Ioc hℓ (α - c) (-(ℓ / 2))
  refine ⟨α - c - k • ℓ, k, hk₁, by linarith, ?_⟩
  rw [zsmul_eq_mul]
  ring
private def wallLevels (ℓ c : ℝ) : Set ℝ := {t | t = c ∨ t = c + ℓ / 2}
private def upperLevels (ℓ c : ℝ) : Set ℝ := {t | 0 < t - c ∧ t - c < ℓ / 2}
private def lowerLevels (ℓ c : ℝ) : Set ℝ := {t | 0 < -(t - c) ∧ -(t - c) < ℓ / 2}
private theorem abs_coord_le_norm (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem norm_sub_update (y : Fin 4 → ℝ) (μ : Fin 4) (t : ℝ) :
    TorusMetric.euclidNormVec (y - Function.update y μ t) = |y μ - t| := by apply _root_.YangMills.SharedProofs.p26106 <;> assumption
private theorem closureWrt_of_partition {X : Type*} (d : X → X → ℝ) (M P N : Set X)
    (hcov : ∀ x, (x ∈ M ∨ x ∈ P) ∨ x ∈ N) (hPN : Disjoint P N)
    (hN : MetricNotions.IsOpenWrt d N) (hself : ∀ x r, 0 < r → d x x < r)
    (hnear : ∀ x ∈ M, ∀ r : ℝ, 0 < r → ∃ y ∈ P, d x y < r) :
    MetricNotions.closureWrt d P = P ∪ M := by
  ext x
  constructor
  · intro hx
    by_contra hnot
    have hxN : x ∈ N := by
      rcases hcov x with (h | h) | h
      · exact absurd (Or.inr h) hnot
      · exact absurd (Or.inl h) hnot
      · exact h
    obtain ⟨r, hr, H⟩ := hN x hxN
    obtain ⟨y, hy, hd⟩ := hx r hr
    exact disjoint_left.1 hPN hy (H y hd)
  · rintro (hxP | hxM) r hr
    · exact ⟨x, hxP, hself x r hr⟩
    · exact hnear x hxM r hr
private theorem isClosedWrt_of_partition {X : Type*} (d : X → X → ℝ) (M P N : Set X)
    (hcov : ∀ x, (x ∈ M ∨ x ∈ P) ∨ x ∈ N) (hMP : Disjoint M P) (hMN : Disjoint M N)
    (hP : MetricNotions.IsOpenWrt d P) (hN : MetricNotions.IsOpenWrt d N) :
    MetricNotions.IsClosedWrt d M := by
  intro x hx
  rcases hcov x with (h | h) | h
  · exact absurd h hx
  · obtain ⟨r, hr, H⟩ := hP x h
    exact ⟨r, hr, fun y hy hyM => disjoint_left.1 hMP hyM (H y hy)⟩
  · obtain ⟨r, hr, H⟩ := hN x h
    exact ⟨r, hr, fun y hy hyM => disjoint_left.1 hMN hyM (H y hy)⟩
section Torus
variable {D : MirrorData}
private theorem slabImage_congr (hH : D.ProjectionSlabs) (μ : Fin 4) {A B : Set ℝ}
    (hAB : ∀ a ∈ A, ∃ n : ℤ, a + D.side * n ∈ B) (hBA : ∀ b ∈ B, ∃ n : ℤ, b + D.side * n ∈ A) :
    D.slabImage μ A = D.slabImage μ B := by
  refine (hH μ A B).2.2.1 ?_
  ext t
  constructor
  · rintro ⟨α, hα, n, rfl⟩
    obtain ⟨k, hk⟩ := hAB α hα
    refine ⟨α + D.side * k, hk, n - k, ?_⟩
    push_cast
    ring
  · rintro ⟨α, hα, n, rfl⟩
    obtain ⟨k, hk⟩ := hBA α hα
    refine ⟨α + D.side * k, hk, n - k, ?_⟩
    push_cast
    ring
private theorem slabImage_union (μ : Fin 4) (A B : Set ℝ) :
    D.slabImage μ A ∪ D.slabImage μ B = D.slabImage μ (A ∪ B) := by
  unfold MirrorData.slabImage
  rw [← image_union]
  rfl
private theorem disjoint_slabImage (hH : D.ProjectionSlabs) (μ : Fin 4) (c : ℝ) {A B : Set ℝ}
    (hA : ∀ t ∈ A, -(D.side / 2) < t - c ∧ t - c ≤ D.side / 2)
    (hB : ∀ t ∈ B, -(D.side / 2) < t - c ∧ t - c ≤ D.side / 2)
    (hAB : ∀ t ∈ A, t ∉ B) : Disjoint (D.slabImage μ A) (D.slabImage μ B) := by
  refine (hH μ A B).2.1.2 ?_
  refine eq_empty_iff_forall_notMem.2 ?_
  rintro t ⟨⟨α, hα, n, rfl⟩, ht⟩
  have e := eq_of_halfOpen_of_sub_mul (period_pos D) n (hB _ ht).1 (hB _ ht).2 (hA _ hα).1
    (hA _ hα).2 (by ring)
  have e' : α + D.side * n = α := by linarith
  rw [e'] at ht
  exact hAB α hα ht
private theorem wallLevels_range (ℓ c : ℝ) (hℓ : 0 < ℓ) :
    ∀ t ∈ wallLevels ℓ c, -(ℓ / 2) < t - c ∧ t - c ≤ ℓ / 2 := by
  rintro t (rfl | rfl)
  · constructor <;> linarith
  · constructor <;> linarith
private theorem upperLevels_range (ℓ c : ℝ) :
    ∀ t ∈ upperLevels ℓ c, -(ℓ / 2) < t - c ∧ t - c ≤ ℓ / 2 := by
  rintro t ⟨h₁, h₂⟩
  constructor <;> linarith
private theorem lowerLevels_range (ℓ c : ℝ) :
    ∀ t ∈ lowerLevels ℓ c, -(ℓ / 2) < t - c ∧ t - c ≤ ℓ / 2 := by
  rintro t ⟨h₁, h₂⟩
  constructor <;> linarith
private theorem torus_trichotomy (hS : D.ProjectionAdditive) (hH : D.ProjectionSlabs) (μ : Fin 4)
    (c : ℝ) (x : D.Torus) :
    (x ∈ D.slabImage μ (wallLevels D.side c) ∨
      x ∈ D.slabImage μ (upperLevels D.side c)) ∨
      x ∈ D.slabImage μ (lowerLevels D.side c) := by
  obtain ⟨y, rfl⟩ := hS.1 x
  obtain ⟨ρ, n, h₁, h₂, e⟩ := exists_centered_rep (period_pos D) c (y μ)
  have mem : ∀ A : Set ℝ, y μ ∈ D.periodize A → D.projection y ∈ D.slabImage μ A :=
    fun A hA => ((hH μ A A).1 y).2 hA
  rcases lt_trichotomy ρ 0 with hρ | hρ | hρ
  · refine Or.inr (mem _ ⟨c + ρ, ?_, n, e⟩)
    show _ ∧ _
    constructor <;> linarith
  · refine Or.inl (Or.inl (mem _ ⟨c, Or.inl rfl, n, ?_⟩))
    rw [e, hρ, add_zero]
  · rcases lt_or_eq_of_le h₂ with h | h
    · refine Or.inl (Or.inr (mem _ ⟨c + ρ, ?_, n, e⟩))
      show _ ∧ _
      constructor <;> linarith
    · refine Or.inl (Or.inl (mem _ ⟨c + D.side / 2, Or.inr rfl, n, ?_⟩))
      rw [e, h]
private theorem isOpenWrt_slabImage (hD : D.ProjectionMetric) (μ : Fin 4) (A : Set ℝ)
    (hA : ∀ t ∈ A, ∃ r : ℝ, 0 < r ∧ ∀ t', |t - t'| < r → t' ∈ A) :
    MetricNotions.IsOpenWrt (Ambient.metric D Ambient.torus) (D.slabImage μ A) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨r, hr, H⟩ := hA _ hy
  refine ⟨r, hr, fun (x' : D.Torus) hx' => ?_⟩
  obtain ⟨y', rfl, hy'⟩ := hD.2.2.1 y x'
  have hlt : TorusMetric.euclidNormVec (y - y') < r := by
    rw [hy']
    exact hx'
  exact ⟨y', H _ (lt_of_le_of_lt (abs_coord_le_norm (y - y') μ) hlt), rfl⟩
private theorem upperLevels_open (ℓ c : ℝ) :
    ∀ t ∈ upperLevels ℓ c, ∃ r : ℝ, 0 < r ∧ ∀ t', |t - t'| < r → t' ∈ upperLevels ℓ c := by
  rintro t ⟨h₁, h₂⟩
  refine ⟨min (t - c) (ℓ / 2 - (t - c)), lt_min h₁ (by linarith), fun t' ht' => ?_⟩
  obtain ⟨a, b⟩ := abs_lt.1 (lt_of_lt_of_le ht' (min_le_left _ _))
  obtain ⟨a', b'⟩ := abs_lt.1 (lt_of_lt_of_le ht' (min_le_right _ _))
  show _ ∧ _
  constructor <;> linarith
private theorem lowerLevels_open (ℓ c : ℝ) :
    ∀ t ∈ lowerLevels ℓ c, ∃ r : ℝ, 0 < r ∧ ∀ t', |t - t'| < r → t' ∈ lowerLevels ℓ c := by
  rintro t ⟨h₁, h₂⟩
  refine ⟨min (-(t - c)) (ℓ / 2 - -(t - c)), lt_min h₁ (by linarith), fun t' ht' => ?_⟩
  obtain ⟨a, b⟩ := abs_lt.1 (lt_of_lt_of_le ht' (min_le_left _ _))
  obtain ⟨a', b'⟩ := abs_lt.1 (lt_of_lt_of_le ht' (min_le_right _ _))
  show _ ∧ _
  constructor <;> linarith
private theorem torus_metric_self (hS : D.ProjectionAdditive) (hD : D.ProjectionMetric)
    (x : D.Torus) (r : ℝ) (hr : 0 < r) : Ambient.metric D Ambient.torus x x < r := by
  obtain ⟨y, rfl⟩ := hS.1 x
  have h := hD.2.1 y y
  have h0 : TorusMetric.euclidNormVec (y - y) = 0 := by simp [TorusMetric.euclidNormVec]
  rw [h0] at h
  exact lt_of_le_of_lt h hr
private theorem metric_update_lt (hD : D.ProjectionMetric) (y : Fin 4 → ℝ) (μ : Fin 4) (t r : ℝ)
    (h : |y μ - t| < r) :
    Ambient.metric D Ambient.torus (D.projection y) (D.projection (Function.update y μ t)) < r := by
  have h₁ := hD.2.1 y (Function.update y μ t)
  rw [norm_sub_update] at h₁
  exact lt_of_le_of_lt h₁ h
private theorem projection_update_sub_half (y : Fin 4 → ℝ) (μ : Fin 4) (c : ℝ)
    (hy : y μ = c + D.side / 2) :
    D.projection (Function.update y μ (c - D.side / 2)) = D.projection y := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    show (((Function.update y ν (c - D.side / 2)) ν : ℝ) :
      AddCircle (PeriodicLattice.torusSide D.L D.m)) =
      ((y ν : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m))
    rw [Function.update_self, hy]
    have e : c + D.side / 2 = (c - D.side / 2) + PeriodicLattice.torusSide D.L D.m := by
      show _ = _ + D.side
      ring
    rw [e, AddCircle.coe_add_period]
  · show (((Function.update y μ (c - D.side / 2)) ν : ℝ) :
      AddCircle (PeriodicLattice.torusSide D.L D.m)) =
      ((y ν : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m))
    rw [Function.update_of_ne hν]
private theorem projection_update_mem (y : Fin 4 → ℝ) (μ : Fin 4) {t : ℝ} {A : Set ℝ}
    (ht : t ∈ A) : D.projection (Function.update y μ t) ∈ D.slabImage μ A := by
  refine ⟨Function.update y μ t, ?_, rfl⟩
  show Function.update y μ t μ ∈ A
  rw [Function.update_self]
  exact ht
private theorem exists_pos_lt_both {ℓ r : ℝ} (hℓ : 0 < ℓ) (hr : 0 < r) :
    ∃ τ : ℝ, 0 < τ ∧ τ < r ∧ τ < ℓ / 2 := by
  refine ⟨min (r / 2) (ℓ / 4), lt_min (by linarith) (by linarith), ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
private theorem wall_approx_upper (hD : D.ProjectionMetric) (μ : Fin 4) (c : ℝ) :
    ∀ x ∈ D.slabImage μ (wallLevels D.side c), ∀ r : ℝ, 0 < r →
      ∃ y ∈ D.slabImage μ (upperLevels D.side c), Ambient.metric D Ambient.torus x y < r := by
  rintro _ ⟨y, hy, rfl⟩ r hr
  obtain ⟨τ, h₀, h₁, h₂⟩ := exists_pos_lt_both (period_pos D) hr
  rcases (hy : y μ = c ∨ y μ = c + D.side / 2) with hy | hy
  · refine ⟨_, projection_update_mem y μ (t := c + τ) ?_, metric_update_lt hD y μ _ r ?_⟩
    · show _ ∧ _
      constructor <;> linarith
    · rw [hy, abs_lt]
      constructor <;> linarith
  · refine ⟨_, projection_update_mem y μ (t := c + D.side / 2 - τ) ?_,
      metric_update_lt hD y μ _ r ?_⟩
    · show _ ∧ _
      constructor <;> linarith
    · rw [hy, abs_lt]
      constructor <;> linarith
private theorem wall_approx_lower (hD : D.ProjectionMetric) (μ : Fin 4) (c : ℝ) :
    ∀ x ∈ D.slabImage μ (wallLevels D.side c), ∀ r : ℝ, 0 < r →
      ∃ y ∈ D.slabImage μ (lowerLevels D.side c), Ambient.metric D Ambient.torus x y < r := by
  rintro _ ⟨y, hy, rfl⟩ r hr
  obtain ⟨τ, h₀, h₁, h₂⟩ := exists_pos_lt_both (period_pos D) hr
  rcases (hy : y μ = c ∨ y μ = c + D.side / 2) with hy | hy
  · refine ⟨_, projection_update_mem y μ (t := c - τ) ?_, metric_update_lt hD y μ _ r ?_⟩
    · show _ ∧ _
      constructor <;> linarith
    · rw [hy, abs_lt]
      constructor <;> linarith
  · rw [← projection_update_sub_half y μ c hy]
    refine ⟨_, projection_update_mem (Function.update y μ (c - D.side / 2)) μ
      (t := c - D.side / 2 + τ) ?_, metric_update_lt hD _ μ _ r ?_⟩
    · show _ ∧ _
      constructor <;> linarith
    · rw [Function.update_self, abs_lt]
      constructor <;> linarith
private theorem upper_union_wall (hH : D.ProjectionSlabs) (μ : Fin 4) (c : ℝ) :
    D.slabImage μ (upperLevels D.side c) ∪ D.slabImage μ (wallLevels D.side c) =
      D.slabImage μ {t | 0 ≤ t - c ∧ t - c ≤ D.side / 2} := by
  have hℓ := period_pos D
  rw [slabImage_union]
  refine slabImage_congr hH μ ?_ ?_
  · rintro a ha
    refine ⟨0, ?_⟩
    rw [Int.cast_zero, mul_zero, add_zero]
    rcases ha with ⟨h₁, h₂⟩ | rfl | rfl
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith
  · rintro b ⟨h₁, h₂⟩
    refine ⟨0, ?_⟩
    rw [Int.cast_zero, mul_zero, add_zero]
    rcases eq_or_lt_of_le h₁ with h | h
    · exact Or.inr (Or.inl (by linarith))
    · rcases eq_or_lt_of_le h₂ with h' | h'
      · exact Or.inr (Or.inr (by linarith))
      · exact Or.inl ⟨h, h'⟩
private theorem lower_union_wall (hH : D.ProjectionSlabs) (μ : Fin 4) (c : ℝ) :
    D.slabImage μ (lowerLevels D.side c) ∪ D.slabImage μ (wallLevels D.side c) =
      D.slabImage μ {t | 0 ≤ -(t - c) ∧ -(t - c) ≤ D.side / 2} := by
  have hℓ := period_pos D
  rw [slabImage_union]
  refine slabImage_congr hH μ ?_ ?_
  · rintro a ha
    rcases ha with ⟨h₁, h₂⟩ | rfl | rfl
    · refine ⟨0, ?_⟩
      rw [Int.cast_zero, mul_zero, add_zero]
      constructor <;> linarith
    · refine ⟨0, ?_⟩
      rw [Int.cast_zero, mul_zero, add_zero]
      constructor <;> linarith
    · refine ⟨-1, ?_⟩
      show _ ∧ _
      push_cast
      constructor <;> linarith
  · rintro b ⟨h₁, h₂⟩
    rcases eq_or_lt_of_le h₁ with h | h
    · refine ⟨0, ?_⟩
      rw [Int.cast_zero, mul_zero, add_zero]
      exact Or.inr (Or.inl (by linarith))
    · rcases eq_or_lt_of_le h₂ with h' | h'
      · refine ⟨1, ?_⟩
        refine Or.inr (Or.inr ?_)
        push_cast
        linarith
      · refine ⟨0, ?_⟩
        rw [Int.cast_zero, mul_zero, add_zero]
        exact Or.inl ⟨h, h'⟩
private theorem wall_shift_half (hH : D.ProjectionSlabs) (μ : Fin 4) (c : ℝ) :
    D.slabImage μ (wallLevels D.side (c + D.side / 2)) =
      D.slabImage μ (wallLevels D.side c) := by
  refine slabImage_congr hH μ ?_ ?_
  · rintro a (rfl | rfl)
    · refine ⟨0, Or.inr ?_⟩
      rw [Int.cast_zero, mul_zero, add_zero]
    · refine ⟨-1, Or.inl ?_⟩
      push_cast
      ring
  · rintro b (rfl | rfl)
    · refine ⟨1, Or.inr ?_⟩
      push_cast
      ring
    · refine ⟨0, Or.inl ?_⟩
      rw [Int.cast_zero, mul_zero, add_zero]
private theorem upper_shift_half (hH : D.ProjectionSlabs) (μ : Fin 4) (c : ℝ) :
    D.slabImage μ (upperLevels D.side (c + D.side / 2)) =
      D.slabImage μ (lowerLevels D.side c) := by
  refine slabImage_congr hH μ ?_ ?_
  · rintro a ⟨h₁, h₂⟩
    refine ⟨-1, ?_⟩
    show _ ∧ _
    push_cast
    constructor <;> linarith
  · rintro b ⟨h₁, h₂⟩
    refine ⟨1, ?_⟩
    show _ ∧ _
    push_cast
    constructor <;> linarith
private theorem lower_shift_half (hH : D.ProjectionSlabs) (μ : Fin 4) (c : ℝ) :
    D.slabImage μ (lowerLevels D.side (c + D.side / 2)) =
      D.slabImage μ (upperLevels D.side c) := by
  refine slabImage_congr hH μ ?_ ?_
  · rintro a ⟨h₁, h₂⟩
    refine ⟨0, ?_⟩
    rw [Int.cast_zero, mul_zero, add_zero]
    show _ ∧ _
    constructor <;> linarith
  · rintro b ⟨h₁, h₂⟩
    refine ⟨0, ?_⟩
    rw [Int.cast_zero, mul_zero, add_zero]
    show _ ∧ _
    constructor <;> linarith
private theorem descended_reflect_shift_half (μ : Fin 4) (c : ℝ) :
    D.descended (euclidReflect μ (c + D.side / 2)) = D.descended (euclidReflect μ c) := by
  have hcomp : D.projection ∘ euclidReflect μ (c + D.side / 2) =
      D.projection ∘ euclidReflect μ c := by
    funext y ν
    by_cases hν : ν = μ
    · subst hν
      show ((euclidReflect ν (c + D.side / 2) y ν : ℝ) :
        AddCircle (PeriodicLattice.torusSide D.L D.m)) =
        ((euclidReflect ν c y ν : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m))
      have e : euclidReflect ν (c + D.side / 2) y ν =
          euclidReflect ν c y ν + PeriodicLattice.torusSide D.L D.m := by
        show _ = _ + D.side
        simp only [euclidReflect, PeriodicLattice.coordVec, Pi.sub_apply, Pi.smul_apply,
          Pi.single_eq_same, smul_eq_mul]
        ring
      rw [e, AddCircle.coe_add_period]
    · show ((euclidReflect μ (c + D.side / 2) y ν : ℝ) :
        AddCircle (PeriodicLattice.torusSide D.L D.m)) =
        ((euclidReflect μ c y ν : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m))
      have e : ∀ c' : ℝ, euclidReflect μ c' y ν = y ν := by
        intro c'
        simp [euclidReflect, PeriodicLattice.coordVec, hν]
      rw [e, e]
  have hI : D.Induces (euclidReflect μ (c + D.side / 2)) = D.Induces (euclidReflect μ c) := by
    funext s
    simp only [MirrorData.Induces, hcomp]
  show Classical.epsilon (D.Induces _) = Classical.epsilon (D.Induces _)
  rw [hI]
end Torus
section FourSpace
variable (D : MirrorData)
private theorem isOpenWrt_coordSet (μ : Fin 4) (P : ℝ → Prop)
    (hP : ∀ t, P t → ∃ r : ℝ, 0 < r ∧ ∀ t', |t - t'| < r → P t') :
    MetricNotions.IsOpenWrt (Ambient.metric D Ambient.euclidean) (coordSet μ P) := by
  intro (x : Fin 4 → ℝ) hx
  obtain ⟨r, hr, H⟩ := hP _ hx
  refine ⟨r, hr, fun (y : Fin 4 → ℝ) hy => H _ ?_⟩
  exact lt_of_le_of_lt (abs_coord_le_norm (x - y) μ) hy
private theorem euclid_metric_self (x : Fin 4 → ℝ) (r : ℝ) (hr : 0 < r) :
    Ambient.metric D Ambient.euclidean x x < r := by
  have h0 : TorusMetric.euclidNormVec (x - x) = 0 := by simp [TorusMetric.euclidNormVec]
  show TorusMetric.euclidNormVec (x - x) < r
  rw [h0]
  exact hr
private theorem euclid_metric_update_lt (x : Fin 4 → ℝ) (μ : Fin 4) (t r : ℝ)
    (h : |x μ - t| < r) :
    Ambient.metric D Ambient.euclidean x (Function.update x μ t) < r := by
  show TorusMetric.euclidNormVec (x - Function.update x μ t) < r
  rw [norm_sub_update]
  exact h
end FourSpace
theorem carrierAndSidesPartition_of_projectionFacts (h : ProjectionFacts) :
    CarrierAndSidesPartition := by
  intro D S
  obtain ⟨hS, hD, hH, -, -, -⟩ := h D
  have hℓ := period_pos D
  obtain ⟨μ, c⟩ := S
  have cov := torus_trichotomy hS hH μ c
  have dMP : Disjoint (D.slabImage μ (wallLevels D.side c))
      (D.slabImage μ (upperLevels D.side c)) := by
    refine disjoint_slabImage hH μ c (wallLevels_range _ _ hℓ) (upperLevels_range _ _) ?_
    rintro t (rfl | rfl) ⟨h₁, h₂⟩ <;> linarith
  have dMN : Disjoint (D.slabImage μ (wallLevels D.side c))
      (D.slabImage μ (lowerLevels D.side c)) := by
    refine disjoint_slabImage hH μ c (wallLevels_range _ _ hℓ) (lowerLevels_range _ _) ?_
    rintro t (rfl | rfl) ⟨h₁, h₂⟩ <;> linarith
  have dPN : Disjoint (D.slabImage μ (upperLevels D.side c))
      (D.slabImage μ (lowerLevels D.side c)) := by
    refine disjoint_slabImage hH μ c (upperLevels_range _ _) (lowerLevels_range _ _) ?_
    rintro t ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    linarith
  have oP := isOpenWrt_slabImage hD μ _ (upperLevels_open D.side c)
  have oN := isOpenWrt_slabImage hD μ _ (lowerLevels_open D.side c)
  have self0 := torus_metric_self hS hD
  have cP := closureWrt_of_partition _ _ _ _ cov dPN oN self0 (wall_approx_upper hD μ c)
  have cN := closureWrt_of_partition _ _ _ _
    (fun x => (cov x).elim (fun a => a.elim (fun b => Or.inl (Or.inl b))
      (fun b => Or.inr b)) (fun a => Or.inl (Or.inr a))) dPN.symm oP self0
      (wall_approx_lower hD μ c)
  have clM := isClosedWrt_of_partition _ _ _ _ cov dMP dMN oP oN
  have cov4 : ∀ x : Fin 4 → ℝ, (x ∈ coordSet μ (fun t => t = c) ∨
      x ∈ coordSet μ (fun t => t > c)) ∨ x ∈ coordSet μ (fun t => t < c) := by
    intro x
    rcases lt_trichotomy (x μ) c with h' | h' | h'
    · exact Or.inr h'
    · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr h')
  have dMP4 : Disjoint (coordSet μ (fun t => t = c)) (coordSet μ (fun t => t > c)) :=
    disjoint_left.2 fun x (h₁ : x μ = c) (h₂ : x μ > c) => by linarith
  have dMN4 : Disjoint (coordSet μ (fun t => t = c)) (coordSet μ (fun t => t < c)) :=
    disjoint_left.2 fun x (h₁ : x μ = c) (h₂ : x μ < c) => by linarith
  have dPN4 : Disjoint (coordSet μ (fun t => t > c)) (coordSet μ (fun t => t < c)) :=
    disjoint_left.2 fun x (h₁ : x μ > c) (h₂ : x μ < c) => by linarith
  have oP4 : MetricNotions.IsOpenWrt (Ambient.metric D Ambient.euclidean)
      (coordSet μ (fun t => t > c)) := by
    refine isOpenWrt_coordSet D μ _ fun t (ht : t > c) => ⟨t - c, by linarith, fun t' h' => ?_⟩
    obtain ⟨a, b⟩ := abs_lt.1 h'
    show t' > c
    linarith
  have oN4 : MetricNotions.IsOpenWrt (Ambient.metric D Ambient.euclidean)
      (coordSet μ (fun t => t < c)) := by
    refine isOpenWrt_coordSet D μ _ fun t (ht : t < c) => ⟨c - t, by linarith, fun t' h' => ?_⟩
    obtain ⟨a, b⟩ := abs_lt.1 h'
    show t' < c
    linarith
  have near4P : ∀ x ∈ coordSet μ (fun t => t = c), ∀ r : ℝ, 0 < r →
      ∃ y ∈ coordSet μ (fun t => t > c), Ambient.metric D Ambient.euclidean x y < r := by
    intro x (hx : x μ = c) r hr
    refine ⟨Function.update x μ (c + r / 2), ?_, euclid_metric_update_lt D x μ _ r ?_⟩
    · show Function.update x μ (c + r / 2) μ > c
      rw [Function.update_self]
      linarith
    · rw [hx, abs_lt]
      constructor <;> linarith
  have near4N : ∀ x ∈ coordSet μ (fun t => t = c), ∀ r : ℝ, 0 < r →
      ∃ y ∈ coordSet μ (fun t => t < c), Ambient.metric D Ambient.euclidean x y < r := by
    intro x (hx : x μ = c) r hr
    refine ⟨Function.update x μ (c - r / 2), ?_, euclid_metric_update_lt D x μ _ r ?_⟩
    · show Function.update x μ (c - r / 2) μ < c
      rw [Function.update_self]
      linarith
    · rw [hx, abs_lt]
      constructor <;> linarith
  have self4 := euclid_metric_self D
  have cP4 := closureWrt_of_partition _ _ _ _ cov4 dPN4 oN4 self4 near4P
  have cN4 := closureWrt_of_partition _ _ _ _
    (fun x => (cov4 x).elim (fun a => a.elim (fun b => Or.inl (Or.inl b))
      (fun b => Or.inr b)) (fun a => Or.inl (Or.inr a))) dPN4.symm oP4 self4 near4N
  have clM4 := isClosedWrt_of_partition _ _ _ _ cov4 dMP4 dMN4 oP4 oN4
  refine And.intro (fun E => ?_) (And.intro ?_ (And.intro ?_ ?_))
  · cases E
    · exact And.intro
        (And.intro (eq_univ_of_forall cov) (And.intro dMP (And.intro dMN dPN)))
        (And.intro oP (And.intro oN (And.intro clM (And.intro cP cN))))
    · exact And.intro
        (And.intro (eq_univ_of_forall cov4) (And.intro dMP4 (And.intro dMN4 dPN4)))
        (And.intro oP4 (And.intro oN4 (And.intro clM4 (And.intro cP4 cN4))))
  · exact And.intro (cP.trans (upper_union_wall hH μ c))
      (cN.trans (lower_union_wall hH μ c))
  · refine And.intro (cP4.trans ?_) (cN4.trans ?_)
    · ext x
      show (x μ > c ∨ x μ = c) ↔ x μ - c ≥ 0
      constructor
      · rintro (h' | h') <;> linarith
      · intro h'
        rcases eq_or_lt_of_le h' with h'' | h''
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)
    · ext x
      show (x μ < c ∨ x μ = c) ↔ -(x μ - c) ≥ 0
      constructor
      · rintro (h' | h') <;> linarith
      · intro h'
        rcases eq_or_lt_of_le h' with h'' | h''
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)
  · exact And.intro (wall_shift_half hH μ c) (And.intro (descended_reflect_shift_half μ c)
      (And.intro (upper_shift_half hH μ c) (lower_shift_half hH μ c)))
end YangMills.Construction.ReflectionPositivity.AxisMirror.PartitionProof
