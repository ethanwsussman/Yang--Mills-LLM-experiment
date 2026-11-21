import YangMills.Construction.Geometry.ExpandingTori
import YangMills.Construction.Geometry.Periodization
import YangMills.Construction.ReflectionPositivity.ReflectionsMirrorsAndSlabsAtOneCutoff
import YangMills.Construction.SourcesAndGluing.BallTransportAndInducedIsometries
import YangMills.Construction.Torus.BumpsAndShapeNumbers
import YangMills.Construction.TorusOrFourSpace.CompactnessAndLiftsOfClosedBallsAndOriginBallsProof
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefinedProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric TestFunctions TorusPeriodization
open scoped ENNReal
namespace BallPeriodization
variable (D : PeriodicSpace.Params)
theorem side_mem_torusSides : D.side ∈ PeriodicLattice.torusSides D.L := ⟨D.m, D.m.pos, rfl⟩
theorem side_pos : 0 < D.side := by apply _root_.YangMills.SharedProofs.p25685 <;> assumption
def radiusOffset : ℝ := 1
def periodizationMargin : ExpandingTori.PeriodizationMargin D.L where
  value := radiusOffset
  pos := by norm_num [radiusOffset]
  lt_half := by
    have h : (13 : ℝ) ≤ D.L := by exact_mod_cast D.isAdmissible.2
    norm_num [radiusOffset]
    linarith
abbrev ballRadius : ℝ := (periodizationMargin D).radius D.side
theorem ballRadius_eq :
    ballRadius D = D.side / 4 - radiusOffset ∧
      ballRadius D = (1 / 2) * (D.L : ℝ) ^ (D.m : ℕ) - radiusOffset ∧
      0 ≤ radiusOffset ∧ radiusOffset < 13 / 2 := by
  have h : ballRadius D = D.side / 4 - radiusOffset := rfl
  refine ⟨h, ?_, ?_, ?_⟩
  · have hs : D.side = 2 * (D.L : ℝ) ^ (D.m : ℕ) := rfl
    rw [h, hs]
    ring
  · norm_num [radiusOffset]
  · norm_num [radiusOffset]
section Periodize
variable {𝕜 : Type*} [RCLike 𝕜]
def IsPeriodizableInBall (ρ : ℝ) (f : (Fin 4 → ℝ) → 𝕜) : Prop :=
  0 < ρ ∧ ρ ≤ ballRadius D ∧
    SourcesAndGluing.HasCompactSupportIn f (SourcesAndGluing.ballR4 ρ)
variable {D} {ρ : ℝ} {f : (Fin 4 → ℝ) → 𝕜}
theorem IsPeriodizableInBall.two_mul_le (h : IsPeriodizableInBall D ρ f) :
    2 * ρ ≤ D.side / 2 := by
  have h₁ : ballRadius D = D.side / 4 - 1 := rfl
  have h₂ := h.2.1
  linarith
theorem IsPeriodizableInBall.support_subset (h : IsPeriodizableInBall D ρ f) :
    Function.support f ⊆ SourcesAndGluing.ballR4 ρ :=
  subset_closure.trans h.2.2.2
theorem IsPeriodizableInBall.isPeriodizable (h : IsPeriodizableInBall D ρ f) :
    IsPeriodizable D.side (SourcesAndGluing.ballR4 ρ) f := by
  refine ⟨fun x hx y hy => ?_, h.support_subset⟩
  have hx' : euclidNormVec x < ρ := hx
  have hy' : euclidNormVec y < ρ := hy
  have hneg : euclidNormVec (-y) = euclidNormVec y := by simp [euclidNormVec]
  have htri := Periodization.euclidNormVec_triangle x (-y)
  rw [← sub_eq_add_neg, hneg] at htri
  have := h.two_mul_le
  linarith
theorem IsPeriodizableInBall.periodize_torusProj_of_mem (h : IsPeriodizableInBall D ρ f)
    {x : Fin 4 → ℝ} (hx : x ∈ SourcesAndGluing.ballR4 ρ) :
    periodize D.side f (torusProj D.side x) = f x := by
  rw [periodize_torusProj, periodicSum, tsum_eq_single 0]
  · have h0 : latticeTranslate D.side 0 = 0 := by
      funext μ
      simp [latticeTranslate]
    rw [h0, add_zero]
  · intro k hk
    by_contra hne
    have hd := h.isPeriodizable.1 _ (h.support_subset hne) _ hx
    rw [add_sub_cancel_left] at hd
    have hpos := side_pos D
    obtain ⟨μ, hμ⟩ := Function.ne_iff.mp hk
    have h1 : (1 : ℝ) ≤ |(k μ : ℝ)| := by
      have hμ' : k μ ≠ 0 := hμ
      exact_mod_cast Int.one_le_abs hμ'
    have h2 := abs_apply_le_euclidNormVec (latticeTranslate D.side k) μ
    simp only [latticeTranslate, abs_mul, abs_of_pos hpos] at h2
    nlinarith
theorem IsPeriodizableInBall.periodize_eq_zero (h : IsPeriodizableInBall D ρ f)
    {u : D.Torus} (hu : u ∉ torusProj D.side '' SourcesAndGluing.ballR4 ρ) :
    periodize D.side f u = 0 := by
  obtain ⟨x, rfl⟩ := torusProj_surjective D.side u
  have hz : ∀ k, f (x + latticeTranslate D.side k) = 0 := by
    intro k
    by_contra hne
    exact hu ⟨_, h.support_subset hne, torusProj_add_latticeTranslate D.side x k⟩
  rw [periodize_torusProj, periodicSum]
  simp [hz]
end Periodize
abbrev axisMirrorData (K : ℕ+) : ReflectionPositivity.AxisMirror.MirrorData where
  L := D.L
  isAdmissible := D.isAdmissible
  K := K
  m := D.m
  β := 1
  β_pos := one_pos
section ClassC1
variable {𝕜 : Type*} [RCLike 𝕜]
def IsC1Torus (u : D.Torus → 𝕜) : Prop :=
  ReflectionPositivity.AxisMirror.Ambient.IsC1 (axisMirrorData D 1) .torus u
theorem isC1Torus_iff (u : D.Torus → 𝕜) :
    IsC1Torus D u ↔ IsC1R4 (u ∘ torusProj D.side) := Iff.rfl
def gradTorus (u : D.Torus → 𝕜) (x : D.Torus) : Fin 4 → 𝕜 :=
  ReflectionPositivity.AxisMirror.Ambient.grad (axisMirrorData D 1) .torus u x
def partialDerivTorus (μ : Fin 4) (u : D.Torus → 𝕜) (x : D.Torus) : 𝕜 := gradTorus D u x μ
theorem partialDerivTorus_comp_torusProj (μ : Fin 4) (u : D.Torus → 𝕜) :
    partialDerivTorus D μ u ∘ torusProj D.side = partialDerivR4 μ (u ∘ torusProj D.side) := by
  funext y
  have hlift : torusProj D.side ((axisMirrorData D 1).liftChoice (torusProj D.side y)) =
      torusProj D.side y :=
    Classical.epsilon_spec (p := fun z => (axisMirrorData D 1).projection z = torusProj D.side y)
      ⟨y, rfl⟩
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq hlift
  have hper : ∀ t : ℝ, (u ∘ torusProj D.side)
      ((axisMirrorData D 1).liftChoice (torusProj D.side y) + t • Pi.single μ (1 : ℝ)) =
        (u ∘ torusProj D.side) (y + t • Pi.single μ (1 : ℝ)) := by
    intro t
    rw [hk, add_right_comm]
    simp only [Function.comp_apply, torusProj_add_latticeTranslate]
  change partialDerivR4 μ (u ∘ torusProj D.side)
      ((axisMirrorData D 1).liftChoice (torusProj D.side y)) =
    partialDerivR4 μ (u ∘ torusProj D.side) y
  simp only [partialDerivR4, hper]
end ClassC1
theorem euclidReflect_involutive (μ : Fin 4) (c : ℝ) :
    Function.Involutive (ReflectionPositivity.AxisMirror.euclidReflect μ c) := by
  intro x
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [ReflectionPositivity.AxisMirror.euclidReflect, PeriodicLattice.coordVec]
    ring
  · simp [ReflectionPositivity.AxisMirror.euclidReflect, PeriodicLattice.coordVec, h]
def hyperplaneReflection (μ : Fin 4) (c : ℝ) : euclideanMotions :=
  ⟨(euclidReflect_involutive μ c).toPerm, 1, fun ν => if ν = μ then -1 else 1,
    (2 * c) • PeriodicLattice.coordVec μ, fun x => by
      funext ν
      by_cases h : ν = μ
      · subst h
        simp [ReflectionPositivity.AxisMirror.euclidReflect, PeriodicLattice.coordVec,
          PeriodicLattice.CutoffTorus.signedPermEuclidean]
        ring
      · simp [ReflectionPositivity.AxisMirror.euclidReflect, PeriodicLattice.coordVec,
          PeriodicLattice.CutoffTorus.signedPermEuclidean, h]⟩
theorem hyperplaneReflection_apply (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    (hyperplaneReflection μ c : Equiv.Perm (Fin 4 → ℝ)) x =
      x - (2 * (x μ - c)) • PeriodicLattice.coordVec μ := rfl
theorem reflectVec_eq_hyperplaneReflection (E : ReflectionPositivity.CutoffMirrors.MirrorData)
    (c : ℝ) (x : Fin 4 → ℝ) :
    E.reflectVec c x = (hyperplaneReflection E.dir c : Equiv.Perm (Fin 4 → ℝ)) x :=
  E.reflectVec_eq_sub c x
def torusMap (s : euclideanMotions) : Equiv.Perm D.Torus := torusMotion D.side s
theorem torusMap_comp_torusProj (s : euclideanMotions) :
    torusMap D s ∘ torusProj D.side = torusProj D.side ∘ (s : Equiv.Perm (Fin 4 → ℝ)) :=
  funext fun x => torusMotion_torusProj D.side s x
def tupleComp {E : Type*} {q : ℕ} (X : Fin q → (Fin 4 → ℝ) → E) (s : euclideanMotions) :
    Fin q → (Fin 4 → ℝ) → E :=
  fun i => X i ∘ (s : Equiv.Perm (Fin 4 → ℝ))
section Distances
variable (E : PeriodicSpace.Kind)
def ptInfDist (u v : E.Pt D) : ℝ≥0∞ := PeriodicSpace.Kind.setInfDist D E {u} {v}
theorem ptInfDist_eq (u v : E.Pt D) :
    ptInfDist D E u v = ENNReal.ofReal (PeriodicSpace.Kind.quotDist D E u v) := by
  simp [ptInfDist, PeriodicSpace.Kind.setInfDist]
theorem quotDist_euclidean (x y : Fin 4 → ℝ) :
    PeriodicSpace.Kind.quotDist D .euclidean x y = euclidNormVec (x - y) := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_euclidean <;> assumption
theorem quotDist_torus (u v : D.Torus) :
    PeriodicSpace.Kind.quotDist D .torus u v = torusEuclidNorm (u - v) := by
  have hs : {r | ∃ x y, PeriodicSpace.Kind.IsLift D .torus u x ∧
      PeriodicSpace.Kind.IsLift D .torus v y ∧
      ∃ k ∈ PeriodicSpace.Kind.periodGroup D .torus, r = euclidNormVec (x - y - k)} =
      euclidNormVec '' (torusProj D.side ⁻¹' {u - v}) := by
    ext r
    constructor
    · rintro ⟨x, y, hx, hy, k, hk, rfl⟩
      refine ⟨x - y - k, ?_, rfl⟩
      obtain ⟨n, hn⟩ := hk
      have hx' : torusProj D.side x = u := hx
      have hy' : torusProj D.side y = v := hy
      have hk0 : torusProj D.side k = 0 := by
        funext μ
        change ((k μ : ℝ) : AddCircle D.side) = 0
        rw [hn μ, AddCircle.coe_eq_zero_iff]
        exact ⟨n μ, by simp⟩
      have hsub : torusProj D.side (x - y - k) =
          torusProj D.side x - torusProj D.side y - torusProj D.side k := by
        funext μ
        simp [torusProj]
      change torusProj D.side (x - y - k) = u - v
      rw [hsub, hx', hy', hk0, sub_zero]
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨y, rfl⟩ := torusProj_surjective D.side v
      refine ⟨w + y, y, ?_, rfl, 0, zero_mem _, by simp⟩
      have hadd : torusProj D.side (w + y) = torusProj D.side w + torusProj D.side y := by
        funext μ
        simp [torusProj]
      have hw' : torusProj D.side w = u - torusProj D.side y := hw
      change torusProj D.side (w + y) = u
      rw [hadd, hw', sub_add_cancel]
  exact congrArg sInf hs
end Distances
end BallPeriodization
end YangMills.Construction
end
