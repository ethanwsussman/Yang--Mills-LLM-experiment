import YangMills.Construction.SourcesAndGluing.StandingDataAndSigns
import YangMills.Construction.Torus.LiftsAndInducedMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
open Set TorusMetric TestFunctions TorusPeriodization
def ballR4 (ρ : ℝ) : Set (Fin 4 → ℝ) := {x | euclidNorm x < ρ}
abbrev closedBallAt (x : Fin 4 → ℝ) (R : ℝ) : Set (Fin 4 → ℝ) := closedBallR4 x R
section CompactSupport
variable {𝕜 : Type*} [RCLike 𝕜]
def HasCompactSupportIn (f : (Fin 4 → ℝ) → 𝕜) (O : Set (Fin 4 → ℝ)) : Prop :=
  IsCompact (GluingSetup.suppR4 f) ∧ GluingSetup.suppR4 f ⊆ O
end CompactSupport
theorem range_euclidNorm_sub_latticeTranslate (ℓ : ℝ) (x y : Fin 4 → ℝ) :
    (range fun k : Fin 4 → ℤ => euclidNorm (x - y - latticeTranslate ℓ k)) =
      euclidNormVec '' (torusProj ℓ ⁻¹' {torusProj ℓ x - torusProj ℓ y}) := by
  have hxy : torusProj ℓ x - torusProj ℓ y = torusProj ℓ (x - y) := by
    funext μ
    simp [torusProj]
  rw [hxy]
  ext r
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨x - y - latticeTranslate ℓ k, ?_, rfl⟩
    have h := torusProj_add_latticeTranslate ℓ (x - y - latticeTranslate ℓ k) k
    rw [sub_add_cancel] at h
    exact h.symm
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hk⟩ :=
      exists_latticeTranslate_of_torusProj_eq (show torusProj ℓ w = torusProj ℓ (x - y) from hw)
    refine ⟨-k, ?_⟩
    have hneg : latticeTranslate ℓ (-k) = -latticeTranslate ℓ k := by
      funext μ
      simp [latticeTranslate]
    simp only [hk, hneg, sub_neg_eq_add, euclidNorm]
theorem sInf_euclidNorm_sub_latticeTranslate (ℓ : ℝ) (x y : Fin 4 → ℝ) :
    sInf (range fun k : Fin 4 → ℤ => euclidNorm (x - y - latticeTranslate ℓ k)) =
      torusEuclidNorm (torusProj ℓ x - torusProj ℓ y) := by
  rw [range_euclidNorm_sub_latticeTranslate]
  rfl
theorem sInf_euclidNorm_liftPoint_sub (ℓ : ℝ) (u v : Torus4 ℓ) :
    sInf (range fun k : Fin 4 → ℤ =>
      euclidNorm (liftPoint u - liftPoint v - latticeTranslate ℓ k)) = torusEuclidNorm (u - v) := by
  have h := sInf_euclidNorm_sub_latticeTranslate ℓ (liftPoint u) (liftPoint v)
  rwa [torusProj_liftPoint, torusProj_liftPoint] at h
namespace GluingSetup
variable (D : GluingSetup)
abbrev torusSideAt (m' : ℕ+) : ℝ := (D.withCutoffAndSide D.K m').side
abbrev torusAt (m' : ℕ+) : Type := (D.withCutoffAndSide D.K m').Torus
def projAt (m' : ℕ+) : (Fin 4 → ℝ) →+ D.torusAt m' := (D.withCutoffAndSide D.K m').proj
def torusDist (m' : ℕ+) (u v : D.torusAt m') : ℝ :=
  sInf (range fun k : Fin 4 → ℤ =>
    euclidNorm (liftPoint (ℓ := D.torusSideAt m') u - liftPoint (ℓ := D.torusSideAt m') v -
      latticeTranslate (D.torusSideAt m') k))
theorem torusDist_eq_torusEuclidNorm (m' : ℕ+) (u v : D.torusAt m') :
    D.torusDist m' u v = torusEuclidNorm (S := D.torusSideAt m') (u - v) :=
  sInf_euclidNorm_liftPoint_sub (D.torusSideAt m') u v
def inducedMotion (m' : ℕ+) (s : euclideanMotions) : Equiv.Perm (D.torusAt m') :=
  torusMotion (D.torusSideAt m') s
theorem inducedMotion_descends (m' : ℕ+) (s : euclideanMotions) :
    TorusLifts.Descends (D.torusSideAt m') (D.torusSideAt m') (s : Equiv.Perm (Fin 4 → ℝ))
      (D.inducedMotion m' s) :=
  funext fun x => torusMotion_torusProj (D.torusSideAt m') s x
section Periodization
variable {𝕜 : Type*} [RCLike 𝕜]
def IsBallPeriodization (m' : ℕ+) (ρ : ℝ) (f : (Fin 4 → ℝ) → 𝕜)
    (g : D.torusAt m' → 𝕜) : Prop :=
  (∀ x ∈ ballR4 ρ, g (D.projAt m' x) = f x) ∧
    ∀ u, u ∉ D.projAt m' '' ballR4 ρ → g u = 0
open Classical in
def ballPeriodize (m' : ℕ+) (ρ : ℝ) (f : (Fin 4 → ℝ) → 𝕜) : D.torusAt m' → 𝕜 := fun u =>
  if h : ∃ x ∈ ballR4 ρ, D.projAt m' x = u then f h.choose else 0
theorem isBallPeriodization_ballPeriodize {m' : ℕ+} {ρ : ℝ} (f : (Fin 4 → ℝ) → 𝕜)
    (hinj : InjOn (D.projAt m') (ballR4 ρ)) :
    D.IsBallPeriodization m' ρ f (D.ballPeriodize m' ρ f) := by
  refine ⟨fun x hx => ?_, fun u hu => ?_⟩
  · have h : ∃ y ∈ ballR4 ρ, D.projAt m' y = D.projAt m' x := ⟨x, hx, rfl⟩
    rw [ballPeriodize, dif_pos h, hinj h.choose_spec.1 hx h.choose_spec.2]
  · exact dif_neg fun ⟨x, hx, hxu⟩ => hu ⟨x, hx, hxu⟩
def ballPeriodizeTuple {n : ℕ} (m' : ℕ+) (ρ : ℝ) (f : Fin n → (Fin 4 → ℝ) → 𝕜) :
    Fin n → D.torusAt m' → 𝕜 :=
  fun i => D.ballPeriodize m' ρ (f i)
end Periodization
end GluingSetup
theorem mem_euclideanMotions_iff (s : Equiv.Perm (Fin 4 → ℝ)) :
    s ∈ euclideanMotions ↔
      ∃ S ∈ TorusLifts.hyperoctahedralGroupEuclidean, ∃ v : Fin 4 → ℝ, ∀ x, s x = S x + v := by
  constructor
  · rintro ⟨π, σ, v, h⟩
    exact ⟨TorusLifts.signedCoordinateEquiv π σ, ⟨π, σ, rfl⟩, v, h⟩
  · rintro ⟨_, ⟨π, σ, rfl⟩, v, h⟩
    exact ⟨π, σ, v, h⟩
end YangMills.Construction.SourcesAndGluing
end
