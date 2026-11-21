import YangMills.Construction.ReflectionPositivity.FactsOfTheCoveringMapProof
import YangMills.Construction.ReflectionPositivity.ReflectionAtACoordinateMirror
import Mathlib
set_option autoImplicit false
open Set Function YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.ReflectionProof
private theorem euclidReflect_apply_axis (μ : Fin 4) (c : ℝ) (y : Fin 4 → ℝ) :
    euclidReflect μ c y μ = 2 * c - y μ := by
  simp [euclidReflect, PeriodicLattice.coordVec]
  ring
private theorem euclidReflect_apply_of_ne {μ ν : Fin 4} (hne : ν ≠ μ) (c : ℝ) (y : Fin 4 → ℝ) :
    euclidReflect μ c y ν = y ν := by
  simp [euclidReflect, PeriodicLattice.coordVec, hne]
private theorem euclidReflect_involutive (μ : Fin 4) (c : ℝ) (y : Fin 4 → ℝ) :
    euclidReflect μ c (euclidReflect μ c y) = y := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    rw [euclidReflect_apply_axis, euclidReflect_apply_axis]
    ring
  · rw [euclidReflect_apply_of_ne hν, euclidReflect_apply_of_ne hν]
private theorem euclidReflect_eq_self_iff (μ : Fin 4) (c : ℝ) (y : Fin 4 → ℝ) :
    euclidReflect μ c y = y ↔ y μ = c := by
  constructor
  · intro hfix
    have := congrFun hfix μ
    rw [euclidReflect_apply_axis] at this
    linarith
  · intro hy
    funext ν
    by_cases hν : ν = μ
    · subst hν
      rw [euclidReflect_apply_axis, hy]
      ring
    · rw [euclidReflect_apply_of_ne hν]
private theorem euclidReflect_image_coordSet (μ : Fin 4) (c : ℝ) (P : ℝ → Prop) :
    euclidReflect μ c '' coordSet μ P = coordSet μ fun t => P (2 * c - t) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change P (2 * c - euclidReflect μ c y μ)
    rw [euclidReflect_apply_axis]
    have : 2 * c - (2 * c - y μ) = y μ := by ring
    rw [this]
    exact hy
  · intro hz
    refine ⟨euclidReflect μ c z, ?_, euclidReflect_involutive μ c z⟩
    change P (euclidReflect μ c z μ)
    rw [euclidReflect_apply_axis]
    exact hz
private theorem intCombination_apply (α : ℝ) (w : Fin 4 → ℤ) (μ : Fin 4) :
    intCombination α w μ = α * w μ := by
  simp [intCombination, PeriodicLattice.coordVec, Finset.sum_apply, Pi.single_apply]
private theorem side_pos (D : MirrorData) : 0 < D.side := by apply _root_.YangMills.SharedProofs.p8577 <;> assumption
section
variable (D : MirrorData) (μ : Fin 4) (c : ℝ)
private theorem induces_descended (hd : D.ProjectionDescends (axisSignFlip μ)
    ((2 * c) • PeriodicLattice.coordVec μ)) :
    D.Induces (euclidReflect μ c) (D.descended (euclidReflect μ c)) := by
  rw [euclidReflect_eq_frameAffine]
  exact hd.2.2.2.2.2.1
private theorem descended_projection
    (hind : D.Induces (euclidReflect μ c) (D.descended (euclidReflect μ c)))
    (y : Fin 4 → ℝ) :
    D.descended (euclidReflect μ c) (D.projection y) =
      D.projection (euclidReflect μ c y) :=
  congrFun hind y
private theorem descended_involutive (hadd : D.ProjectionAdditive)
    (hind : D.Induces (euclidReflect μ c) (D.descended (euclidReflect μ c)))
    (x : D.Torus) :
    D.descended (euclidReflect μ c) (D.descended (euclidReflect μ c) x) = x := by
  obtain ⟨y, rfl⟩ := hadd.1 x
  rw [descended_projection D μ c hind, descended_projection D μ c hind, euclidReflect_involutive]
private theorem residueClass_eq_fiber (hadd : D.ProjectionAdditive) (y : Fin 4 → ℝ) :
    D.residueClass y = {y' | D.projection y' = D.projection y} := by
  ext y'
  exact (hadd.2.2.1 y' y).symm
private theorem euclidReflect_image_residueClass (hadd : D.ProjectionAdditive)
    (hind : D.Induces (euclidReflect μ c) (D.descended (euclidReflect μ c)))
    (y : Fin 4 → ℝ) :
    euclidReflect μ c '' D.residueClass y = D.residueClass (euclidReflect μ c y) := by
  rw [residueClass_eq_fiber D hadd, residueClass_eq_fiber D hadd]
  ext z
  constructor
  · rintro ⟨y', hy', rfl⟩
    change D.projection (euclidReflect μ c y') = D.projection (euclidReflect μ c y)
    rw [← descended_projection D μ c hind, ← descended_projection D μ c hind, show D.projection y' =
      D.projection y from hy']
  · intro hz
    refine ⟨euclidReflect μ c z, ?_, euclidReflect_involutive μ c z⟩
    change D.projection (euclidReflect μ c z) = D.projection y
    rw [← descended_projection D μ c hind, show D.projection z =
      D.projection (euclidReflect μ c y) from hz, descended_projection D μ c hind,
      euclidReflect_involutive]
private theorem isInvolutiveIsometry_of (hadd : D.ProjectionAdditive)
    (hd : D.ProjectionDescends (axisSignFlip μ)
      ((2 * c) • PeriodicLattice.coordVec μ)) :
    D.IsInvolutiveIsometry μ c := by
  have hind := induces_descended D μ c hd
  have hinv : ∀ x, D.descended (euclidReflect μ c) (D.descended (euclidReflect μ c) x) = x :=
    descended_involutive D μ c hadd hind
  refine ⟨?_, funext (euclidReflect_involutive μ c), fun y =>
    ⟨_, euclidReflect_image_residueClass D μ c hadd hind y⟩, ?_, funext hinv,
    ⟨euclidReflect_involutive μ c, euclidReflect_involutive μ c⟩, hinv, hinv⟩
  · intro x y
    have h := hd.2.2.1 x y
    rw [← euclidReflect_eq_frameAffine] at h
    exact h
  · intro x y
    have h := hd.2.2.2.2.2.2.2.1 x y
    rw [← euclidReflect_eq_frameAffine] at h
    exact h
private theorem carrier_eq_slabImage :
    CoordMirror.carrier D ⟨μ, c⟩ .torus = D.slabImage μ {c, c + D.side / 2} := by
  have h : (coordSet μ (fun t => t = c) ∪ coordSet μ fun t => t = c + D.side / 2) =
      coordSet μ fun t => t ∈ ({c, c + D.side / 2} : Set ℝ) := by
    ext y
    exact Iff.rfl
  exact congrArg (fun Z => D.projection '' Z) h
private theorem euclidReflect_sub_mem (y : Fin 4 → ℝ) (k : ℤ) (h : D.side * k = 2 * c - 2 * y μ) :
    euclidReflect μ c y - y ∈ intLattice D.side := by
  refine ⟨Pi.single μ k, funext fun ν => ?_⟩
  rw [intCombination_apply, Pi.sub_apply]
  by_cases hν : ν = μ
  · subst hν
    rw [euclidReflect_apply_axis, Pi.single_eq_same]
    linarith
  · rw [euclidReflect_apply_of_ne hν, Pi.single_eq_of_ne hν]
    simp
private theorem levelSets_disjoint (hslab : D.ProjectionSlabs) :
    Disjoint (Ambient.levelSet D μ c .torus) (Ambient.levelSet D μ (c + D.side / 2) .torus) := by
  have hpos := side_pos D
  have hdisj := (hslab μ {c} {c + D.side / 2}).2.1
  refine (show Disjoint (D.slabImage μ {c}) (D.slabImage μ {c + D.side / 2}) from hdisj.2 ?_)
  ext t
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
  rintro ⟨⟨α, hα, k, hk⟩, ht⟩
  rw [mem_singleton_iff] at hα ht
  subst hα
  subst ht
  have h1 : D.side * (2 * (k : ℝ) - 1) = 0 := by linarith
  have h2 : 2 * (k : ℝ) - 1 = 0 := (mul_eq_zero.1 h1).resolve_left hpos.ne'
  have h3 : 2 * k - 1 = 0 := by exact_mod_cast h2
  omega
private theorem fixedSetOfReflect_of (hadd : D.ProjectionAdditive) (hslab : D.ProjectionSlabs)
    (hind : D.Induces (euclidReflect μ c) (D.descended (euclidReflect μ c))) :
    D.FixedSetOfReflect μ c := by
  refine ⟨?_, rfl, ?_, image_union _ _ _, levelSets_disjoint D μ c hslab⟩
  · ext y
    exact euclidReflect_eq_self_iff μ c y
  · ext x
    obtain ⟨y, rfl⟩ := hadd.1 x
    have hm : D.projection y ∈ CoordMirror.carrier D ⟨μ, c⟩ .torus ↔
        y μ ∈ D.periodize {c, c + D.side / 2} := by
      rw [carrier_eq_slabImage]
      exact (hslab μ _ ∅).1 y
    refine Iff.trans ?_ hm.symm
    change D.descended (euclidReflect μ c) (D.projection y) = D.projection y ↔ _
    rw [descended_projection D μ c hind, hadd.2.2.1]
    constructor
    · rintro ⟨n, hn⟩
      have hμ := congrFun hn μ
      rw [intCombination_apply, Pi.sub_apply, euclidReflect_apply_axis] at hμ
      obtain ⟨j, hj | hj⟩ := Int.even_or_odd' (n μ)
      · refine ⟨c, Or.inl rfl, -j, ?_⟩
        rw [hj] at hμ
        push_cast at hμ ⊢
        linarith
      · refine ⟨c + D.side / 2, Or.inr rfl, -j - 1, ?_⟩
        rw [hj] at hμ
        push_cast at hμ ⊢
        linarith
    · rintro ⟨α, hα, k, hk⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hα
      rcases hα with hα | hα
      · refine euclidReflect_sub_mem D μ c y (-2 * k) ?_
        rw [hk, hα]
        push_cast
        ring
      · refine euclidReflect_sub_mem D μ c y (-1 - 2 * k) ?_
        rw [hk, hα]
        push_cast
        ring
private theorem coordSet_congr {P Q : ℝ → Prop} (h : ∀ t, P t ↔ Q t) :
    coordSet μ P = coordSet μ Q := by
  ext y
  exact h (y μ)
private theorem reflectSwapsSides_of (hd : D.ProjectionDescends (axisSignFlip μ)
    ((2 * c) • PeriodicLattice.coordVec μ)) :
    D.ReflectSwapsSides μ c := by
  have himg : ∀ Z : Set (Fin 4 → ℝ), D.descended (euclidReflect μ c) '' (D.projection '' Z) =
      D.projection '' (euclidReflect μ c '' Z) := by
    intro Z
    have h := hd.2.2.2.2.2.2.2.2.1 Z
    rw [← euclidReflect_eq_frameAffine μ c] at h
    exact h
  have key : ∀ P : ℝ → Prop, D.descended (euclidReflect μ c) ''
      (D.projection '' coordSet μ P) =
        D.projection '' coordSet μ fun t => P (2 * c - t) := by
    intro P
    rw [himg, euclidReflect_image_coordSet]
  intro E
  cases E with
  | torus =>
    constructor
    · change D.descended (euclidReflect μ c) ''
          (D.projection '' coordSet μ fun t => 0 < t - c ∧ t - c < D.side / 2) =
        D.projection '' coordSet μ fun t => 0 < -(t - c) ∧ -(t - c) < D.side / 2
      refine (key _).trans (congrArg (fun Z => D.projection '' Z)
        (coordSet_congr μ fun t => ?_))
      have h : 2 * c - t - c = -(t - c) := by ring
      simp only [h]
    · change D.descended (euclidReflect μ c) ''
          (D.projection '' coordSet μ fun t => 0 < -(t - c) ∧ -(t - c) < D.side / 2) =
        D.projection '' coordSet μ fun t => 0 < t - c ∧ t - c < D.side / 2
      refine (key _).trans (congrArg (fun Z => D.projection '' Z)
        (coordSet_congr μ fun t => ?_))
      have h : -(2 * c - t - c) = t - c := by ring
      simp only [h]
  | euclidean =>
    constructor
    · change euclidReflect μ c '' coordSet μ (fun t => t > c) =
        coordSet μ fun t => t < c
      rw [euclidReflect_image_coordSet]
      refine coordSet_congr μ fun t => ?_
      constructor <;> intro h <;> linarith
    · change euclidReflect μ c '' coordSet μ (fun t => t < c) =
        coordSet μ fun t => t > c
      rw [euclidReflect_image_coordSet]
      refine coordSet_congr μ fun t => ?_
      constructor <;> intro h <;> linarith
end
theorem reflectionProperties_of_projectionFacts (h : ProjectionFacts) : ReflectionProperties := by
  intro D μ c
  obtain ⟨hadd, -, hslab, -, -, hdesc⟩ := h D
  have hR := hdesc (axisSignFlip μ) ((2 * c) • PeriodicLattice.coordVec μ)
  exact ⟨isInvolutiveIsometry_of D μ c hadd hR, fixedSetOfReflect_of D μ c hadd hslab (induces_descended D μ c hR),
    reflectSwapsSides_of D μ c hR⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror.ReflectionProof
