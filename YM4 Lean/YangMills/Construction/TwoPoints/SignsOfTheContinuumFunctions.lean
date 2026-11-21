import YangMills.Construction.Continuum.TimeAxisAndTheReflectionOfTime
import YangMills.Construction.Lattice.LevelCoordinates
import YangMills.Construction.Torus.LiftsAndInducedMaps
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
def euclidDot {n : ℕ} (x x' : Fin n → ℝ) : ℝ := ∑ μ, x μ * x' μ
def euclidNorm {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ μ, x μ ^ 2)
theorem euclidNorm_eq_euclidNormVec (x : AmbientSpace) :
    euclidNorm x = YangMills.Construction.TorusMetric.euclidNormVec x := rfl
def hermitianNorm (z : Fin 4 → ℂ) : ℝ := Real.sqrt (∑ μ, ‖z μ‖ ^ 2)
def conjFun {X : Type*} (f : X → ℂ) : X → ℂ := fun x => (starRingEnd ℂ) (f x)
def IsRealNonneg (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re
section Functions
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
def compactlySupportedIn (k : WithTop ℕ∞) (O : Set X) : Submodule ℂ (X → ℂ) where
  carrier := {f | ContDiff ℝ k f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O}
  add_mem' := by
    rintro f g ⟨hf, hfK, hfO⟩ ⟨hg, hgK, hgO⟩
    have hsupp : tsupport (f + g) ⊆ tsupport f ∪ tsupport g := by
      simp only [tsupport]
      rw [← closure_union]
      exact closure_mono (Function.support_add f g)
    exact ⟨hf.add hg, (hfK.union hgK).of_isClosed_subset (isClosed_tsupport _) hsupp,
      hsupp.trans (union_subset hfO hgO)⟩
  zero_mem' := by
    have hsupp : tsupport (0 : X → ℂ) = ∅ := by simp [tsupport]
    exact ⟨contDiff_const, by simp [hsupp], by simp [hsupp]⟩
  smul_mem' := by
    rintro c f ⟨hf, hfK, hfO⟩
    have hsupp : tsupport (c • f) ⊆ tsupport f :=
      closure_mono (Function.support_const_smul_subset c f)
    exact ⟨contDiff_const.smul hf, hfK.of_isClosed_subset (isClosed_tsupport _) hsupp,
      hsupp.trans hfO⟩
abbrev ccIn (O : Set X) : Submodule ℂ (X → ℂ) := compactlySupportedIn 0 O
abbrev cc1In (O : Set X) : Submodule ℂ (X → ℂ) := compactlySupportedIn 1 O
abbrev ccInfIn (O : Set X) : Submodule ℂ (X → ℂ) := compactlySupportedIn ∞ O
theorem mem_ccIn_iff (O : Set X) (f : X → ℂ) :
    f ∈ ccIn O ↔ Continuous f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O := by
  change ContDiff ℝ 0 f ∧ _ ↔ _
  rw [contDiff_zero]
def realValuedPart (V : Submodule ℂ (X → ℂ)) : Submodule ℝ (X → ℂ) where
  carrier := {f | f ∈ V ∧ ∀ x, (f x).im = 0}
  add_mem' := by
    rintro f g ⟨hf, hfre⟩ ⟨hg, hgre⟩
    exact ⟨V.add_mem hf hg, fun x => by simp [hfre x, hgre x]⟩
  zero_mem' := ⟨V.zero_mem, fun _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨hf, hfre⟩
    refine ⟨?_, fun x => by simp [hfre x]⟩
    have hcast : c • f = (c : ℂ) • f := by
      funext x
      simp
    rw [hcast]
    exact V.smul_mem _ hf
end Functions
section Integrals
def integralWrt {X : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℂ) : ℂ := ∫ x, F x ∂μ
variable {X E : Type*} [MeasureSpace X] [NormedAddCommGroup E]
def lebesgueIntegral (F : X → ℂ) : ℂ := integralWrt volume F
def l1NormENN (k : X → E) : ℝ≥0∞ := ∫⁻ x, ‖k x‖ₑ
def l1Norm (k : X → E) : ℝ := (l1NormENN k).toReal
end Integrals
abbrev hyperoctahedralPerms : Subgroup (Equiv.Perm AmbientSpace) :=
  YangMills.Construction.TorusLifts.hyperoctahedralGroupEuclidean
def IsSignedPerm (w : AmbientSpace →ₗ[ℝ] AmbientSpace) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ),
    ∀ μ, w (coordVec μ) = (((ε μ : ℤˣ) : ℤ) : ℝ) • coordVec (σ μ)
def signedPermLinear (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) :
    AmbientSpace →ₗ[ℝ] AmbientSpace where
  toFun := YangMills.Construction.TorusLifts.signedCoordinateEquiv π s
  map_add' x y := by
    funext μ
    simp [YangMills.Construction.TorusLifts.signedCoordinateEquiv,
      YangMills.Construction.PeriodicLattice.CutoffTorus.signedPermEuclidean, mul_add]
  map_smul' c x := by
    funext μ
    simp [YangMills.Construction.TorusLifts.signedCoordinateEquiv,
      YangMills.Construction.PeriodicLattice.CutoffTorus.signedPermEuclidean]
    ring
theorem signedPermLinear_coordVec (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) (μ : Fin 4) :
    signedPermLinear π s (coordVec μ) =
      (((s (π.symm μ) : ℤˣ) : ℤ) : ℝ) • coordVec (π.symm μ) := by
  funext ν
  by_cases hν : ν = π.symm μ
  · subst hν
    simp [signedPermLinear, YangMills.Construction.TorusLifts.signedCoordinateEquiv,
      YangMills.Construction.PeriodicLattice.CutoffTorus.signedPermEuclidean, coordVec]
  · have hν' : π ν ≠ μ := fun e => hν (by simp [← e])
    simp [signedPermLinear, YangMills.Construction.TorusLifts.signedCoordinateEquiv,
      YangMills.Construction.PeriodicLattice.CutoffTorus.signedPermEuclidean, coordVec, hν, hν']
theorem exists_isSignedPerm {w : Equiv.Perm AmbientSpace} (hw : w ∈ hyperoctahedralPerms) :
    ∃ l : AmbientSpace →ₗ[ℝ] AmbientSpace, ⇑l = ⇑w ∧ IsSignedPerm l := by
  obtain ⟨π, s, rfl⟩ := hw
  exact ⟨signedPermLinear π s, rfl, π⁻¹, fun μ => s (π.symm μ),
    signedPermLinear_coordVec π s⟩
theorem exists_mem_hyperoctahedralPerms {l : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hl : IsSignedPerm l) : ∃ w ∈ hyperoctahedralPerms, ⇑w = ⇑l := by
  obtain ⟨σ, ε, h⟩ := hl
  refine ⟨YangMills.Construction.TorusLifts.signedCoordinateEquiv σ⁻¹ fun ν => ε (σ.symm ν),
    ⟨_, _, rfl⟩, ?_⟩
  have hlin : signedPermLinear σ⁻¹ (fun ν => ε (σ.symm ν)) = l := by
    refine (Pi.basisFun ℝ (Fin 4)).ext fun μ => ?_
    have hbasis : Pi.basisFun ℝ (Fin 4) μ = coordVec μ := by
      simp [coordVec]
    rw [hbasis, h μ, signedPermLinear_coordVec]
    change (((ε (σ.symm (σ μ)) : ℤˣ) : ℤ) : ℝ) • coordVec (σ μ) = _
    rw [Equiv.symm_apply_apply]
  rw [← hlin]
  rfl
theorem hyperoctahedral_map_add {w : Equiv.Perm AmbientSpace} (hw : w ∈ hyperoctahedralPerms)
    (x y : AmbientSpace) : w (x + y) = w x + w y := by
  obtain ⟨l, hl, -⟩ := exists_isSignedPerm hw
  simp only [← hl, map_add]
def euclideanMotions : Subgroup (Equiv.Perm AmbientSpace) where
  carrier := {r | ∃ w ∈ hyperoctahedralPerms, ∃ v : AmbientSpace, ∀ x, r x = w x + v}
  mul_mem' := by
    rintro r r' ⟨w, hw, v, h⟩ ⟨w', hw', v', h'⟩
    refine ⟨w * w', hyperoctahedralPerms.mul_mem hw hw', w v' + v, fun x => ?_⟩
    simp only [Equiv.Perm.mul_apply, h, h', hyperoctahedral_map_add hw, add_assoc]
  one_mem' := ⟨1, hyperoctahedralPerms.one_mem, 0, fun x => by simp⟩
  inv_mem' := by
    rintro r ⟨w, hw, v, h⟩
    refine ⟨w⁻¹, hyperoctahedralPerms.inv_mem hw, -(w⁻¹ v), fun x => ?_⟩
    have hinv : ∀ y, w (w⁻¹ y) = y := fun y => w.apply_symm_apply y
    rw [Equiv.Perm.inv_eq_iff_eq, h, hyperoctahedral_map_add hw]
    have hneg : w (-(w⁻¹ v)) = -v := by
      have hsum := hyperoctahedral_map_add hw (w⁻¹ v) (-(w⁻¹ v))
      have hzero : w 0 = 0 := by
        obtain ⟨l, hl, -⟩ := exists_isSignedPerm hw
        simp only [← hl, map_zero]
      rw [add_neg_cancel, hzero, hinv] at hsum
      exact (neg_eq_of_add_eq_zero_right hsum.symm).symm
    rw [hneg, hinv]
    abel
section Actions
variable {E : Type*}
def translateFun (v : AmbientSpace) (f : AmbientSpace → E) : AmbientSpace → E :=
  fun x => f (x - v)
def actOn (r : Equiv.Perm AmbientSpace) (f : AmbientSpace → E) : AmbientSpace → E := f ∘ ⇑r⁻¹
def timeReflected (f : AmbientSpace → E) : AmbientSpace → E :=
  f ∘ YangMills.Construction.TimeAxis.timeReflection
end Actions
structure FixedScale where
  scale : ℝ
  scale_pos : 0 < scale
def FixedScale.sharpNorm (S : FixedScale) (f : AmbientSpace → ℂ) : ℝ :=
  YangMills.Construction.TestFunctions.sharpNormR4 S.scale f
def grad (f : AmbientSpace → ℂ) (x : AmbientSpace) : Fin 4 → ℂ :=
  fun μ => YangMills.Construction.TestFunctions.partialDerivR4 μ f x
def gradNorm (f : AmbientSpace → ℂ) (x : AmbientSpace) : ℝ := hermitianNorm (grad f x)
def gradSupENN (f : AmbientSpace → ℂ) : ℝ≥0∞ := ⨆ x, ENNReal.ofReal (gradNorm f x)
def gradSup (f : AmbientSpace → ℂ) : ℝ := (gradSupENN f).toReal
section Balls
variable {n : ℕ}
def euclidOpenBall (x : Fin n → ℝ) (ϱ : ℝ) : Set (Fin n → ℝ) := {y | euclidNorm (y - x) < ϱ}
def euclidClosedBall (x : Fin n → ℝ) (ϱ : ℝ) : Set (Fin n → ℝ) := {y | euclidNorm (y - x) ≤ ϱ}
def SeparatedBy (d : ℝ) (Y Y' : Set (Fin n → ℝ)) : Prop :=
  ∀ y ∈ Y, ∀ y' ∈ Y', d ≤ euclidNorm (y - y')
end Balls
section SetsOfPoints
variable {X : Type*}
def minkowskiSum [Add X] (Y Y' : Set X) : Set X := {z | ∃ y ∈ Y, ∃ y' ∈ Y', z = y + y'}
end SetsOfPoints
end YangMills.Construction.TwoPoints
end
