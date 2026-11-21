import YangMills.Construction.Continuum.SymbolsOfFourSpaceWithATimeAxis
import YangMills.Construction.SourcesAndGluing.BallTransportAndInducedIsometries
import YangMills.Construction.Torus.CoordinateReflectionsMirrorsAndSlabs
import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusMetric TorusPeriodization TorusTransport
namespace GrowingTori
theorem mem_euclideanMotions_iff_mem_affineHyperoctahedral (s : Equiv.Perm (Fin 4 → ℝ)) :
    s ∈ euclideanMotions ↔ ⇑s ∈ affineHyperoctahedral := by
  rw [SourcesAndGluing.mem_euclideanMotions_iff]
  constructor
  · rintro ⟨S, hS, v, h⟩
    exact ⟨⟨S, hS⟩, v, funext h⟩
  · rintro ⟨w, v, h⟩
    exact ⟨w.1, w.2, v, fun x => congrFun h x⟩
theorem hyperoctahedral_le_euclideanMotions : hyperoctahedral ≤ euclideanMotions := by
  intro w hw
  rw [SourcesAndGluing.mem_euclideanMotions_iff]
  exact ⟨w, hw, 0, fun x => (add_zero _).symm⟩
def euclideanTranslation (v : Fin 4 → ℝ) : euclideanMotions :=
  ⟨translationEquiv v, (SourcesAndGluing.mem_euclideanMotions_iff _).2
    ⟨1, one_mem _, v, fun _ => rfl⟩⟩
section Families
variable {ι Z : Type*}
def shiftFamily (a : Fin 4 → ℝ) (X : ι → (Fin 4 → ℝ) → Z) : ι → (Fin 4 → ℝ) → Z :=
  familyComp X (translationEquiv (-a))
theorem shiftFamily_apply (a : Fin 4 → ℝ) (X : ι → (Fin 4 → ℝ) → Z) (i : ι) (y : Fin 4 → ℝ) :
    shiftFamily a X i y = X i (y - a) := by
  simp [shiftFamily, familyComp, sub_eq_add_neg]
def hyperoctahedralActFamily (w : hyperoctahedral) (X : ι → (Fin 4 → ℝ) → Z) :
    ι → (Fin 4 → ℝ) → Z :=
  familyComp X (w⁻¹ : hyperoctahedral).1
variable (σ : Conventions.StandingParameters)
theorem isDistIsometry_toPerm {f : (Fin 4 → ℝ) → Fin 4 → ℝ} (hf : IsEuclideanMotion f) :
    AmbientPoints.IsDistIsometry (s := σ) (E := .euclidean) hf.toPerm :=
  fun x y => hf.isDistancePreserving x y
end Families
def diagMap (f : (Fin 4 → ℝ) → Fin 4 → ℝ) {n : ℕ} (y : Fin n → Fin 4 → ℝ) :
    Fin n → Fin 4 → ℝ :=
  fun i => f (y i)
def periodicMotion (L : ℕ) (m : ℕ+) (g : euclideanMotions) :
    Equiv.Perm (PeriodicLattice.FourTorus L m) :=
  torusMotion (PeriodicLattice.torusSide L m) g
theorem periodicMotion_comp_torusProj (L : ℕ) (m : ℕ+) (g : euclideanMotions) :
    periodicMotion L m g ∘ torusProj (PeriodicLattice.torusSide L m) =
      torusProj (PeriodicLattice.torusSide L m) ∘ (g : Equiv.Perm (Fin 4 → ℝ)) :=
  funext fun x => torusMotion_torusProj _ g x
theorem eq_periodicMotion {L : ℕ} {m : ℕ+} {g : euclideanMotions}
    {Φ : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m}
    (h : Φ ∘ torusProj (PeriodicLattice.torusSide L m) =
      torusProj (PeriodicLattice.torusSide L m) ∘ (g : Equiv.Perm (Fin 4 → ℝ))) :
    Φ = periodicMotion L m g := by
  funext u
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  exact (congrFun h x).trans (congrFun (periodicMotion_comp_torusProj L m g) x).symm
theorem hyperplaneReflect_eq_sub (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneReflect μ c x = x - (2 * (x μ - c)) • basisVec μ := by
  simp only [hyperplaneReflect]
  rw [sub_eq_add_neg x, ← neg_smul]
  congr 2
  ring
def torusReflection (L : ℕ) (m : ℕ+) (μ : Fin 4) (c : ℝ) :
    Equiv.Perm (PeriodicLattice.FourTorus L m) :=
  periodicMotion L m (AxisReflection.coordReflectMotion μ c)
open TimeAxisSymbols
def spatialAct (w : timeAxisStabilizer) (a : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => w.1.1 (spaceTimePoint a 0) i.castSucc
end GrowingTori
end YangMills.Construction
end
