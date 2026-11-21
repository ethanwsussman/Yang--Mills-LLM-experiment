import YangMills.Construction.EnergyMomentum.ContractionSemigroupUnitaryGroup
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.LevelCoordinates
import YangMills.Construction.ReflectionPositivity.SeparatedTuples
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
def timeAxis : Fin 4 := Fin.last 3
def spaceAxis (i : Fin 3) : Fin 4 := i.castSucc
def embedSpatial (q : EnergyMomentum.Momentum3) : Space :=
  Fin.snoc (α := fun _ => ℝ) (fun i => q i) 0
def spatialPart (y : Space) : EnergyMomentum.Momentum3 :=
  WithLp.toLp 2 fun i => y (spaceAxis i)
theorem embedSpatial_spaceAxis (q : EnergyMomentum.Momentum3) (i : Fin 3) :
    embedSpatial q (spaceAxis i) = q i := by
  simp [embedSpatial, spaceAxis]
theorem embedSpatial_timeAxis (q : EnergyMomentum.Momentum3) :
    embedSpatial q timeAxis = 0 :=
  Fin.snoc_last (α := fun _ => ℝ) _ _
def maxNorm (x : Space) : ℝ := Finset.univ.sup' Finset.univ_nonempty fun μ => |x μ|
def euclidInner (x x' : Space) : ℝ := ∑ μ, x μ * x' μ
def maxNormInfDist (x : Space) (S : Set Space) : ℝ :=
  sInf ((fun x' => maxNorm (x - x')) '' S)
theorem maxNorm_eq_norm (x : Space) : maxNorm x = ‖x‖ := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun μ _ => by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x μ
  · refine (pi_norm_le_iff_of_nonneg ?_).2 fun μ => ?_
    · exact (abs_nonneg (x 0)).trans
        (Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ (0 : Fin 4)))
    · rw [Real.norm_eq_abs]
      exact Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ μ)
def axisReflection (μ : Fin 4) : Equiv.Perm Space where
  toFun x := x - (2 * x μ) • PeriodicLattice.coordVec μ
  invFun x := x - (2 * x μ) • PeriodicLattice.coordVec μ
  left_inv x := by
    funext ν
    by_cases h : ν = μ
    · subst h
      simp [PeriodicLattice.coordVec]
      ring
    · simp [PeriodicLattice.coordVec, h]
  right_inv x := by
    funext ν
    by_cases h : ν = μ
    · subst h
      simp [PeriodicLattice.coordVec]
      ring
    · simp [PeriodicLattice.coordVec, h]
def reflectTime : Equiv.Perm Space := axisReflection timeAxis
def upperHalfSpace : Set Space := {x | 0 < x timeAxis}
theorem intUnit_cast_mul_self (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp
def permuteAndSign (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) : Equiv.Perm Space where
  toFun x μ := (s μ : ℤ) • x (π μ)
  invFun x ν := (s (π.symm ν) : ℤ) • x (π.symm ν)
  left_inv x := by
    funext ν
    simp only [zsmul_eq_mul, Equiv.apply_symm_apply]
    rw [← mul_assoc, intUnit_cast_mul_self, one_mul]
  right_inv x := by
    funext μ
    simp only [zsmul_eq_mul, Equiv.symm_apply_apply]
    rw [← mul_assoc, intUnit_cast_mul_self, one_mul]
def hyperoctahedral : Subgroup (Equiv.Perm Space) where
  carrier := {σ | ∃ π s, σ = permuteAndSign π s}
  mul_mem' := by
    rintro _ _ ⟨π, s, rfl⟩ ⟨π', s', rfl⟩
    refine ⟨π' * π, fun μ => s μ * s' (π μ), ?_⟩
    ext x μ
    simp [permuteAndSign]
    ring
  one_mem' := ⟨1, fun _ => 1, by ext x μ; simp [permuteAndSign]⟩
  inv_mem' := by
    rintro _ ⟨π, s, rfl⟩
    refine ⟨π⁻¹, fun ν => s (π.symm ν), ?_⟩
    ext x ν
    rfl
def flipSigns (s : Fin 4 → ℤˣ) : Equiv.Perm Space := permuteAndSign 1 s
theorem flipSigns_apply (s : Fin 4 → ℤˣ) (x : Space) (μ : Fin 4) :
    flipSigns s x μ = ((s μ : ℤ) : ℝ) * x μ := by
  simp [flipSigns, permuteAndSign]
theorem flipSigns_mul (s s' : Fin 4 → ℤˣ) : flipSigns s * flipSigns s' = flipSigns (s * s') := by
  ext x μ
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, flipSigns_apply, Pi.mul_apply,
    Units.val_mul]
  push_cast
  ring
theorem flipSigns_one : flipSigns 1 = 1 := by
  ext x μ
  simp [flipSigns_apply]
theorem flipSigns_inv (s : Fin 4 → ℤˣ) : (flipSigns s)⁻¹ = flipSigns s⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, flipSigns_mul, mul_inv_cancel, flipSigns_one]
theorem axisReflection_eq_flipSigns (μ : Fin 4) :
    axisReflection μ = flipSigns (Pi.mulSingle μ (-1)) := by
  ext x ν
  rw [flipSigns_apply]
  change (x - (2 * x μ) • PeriodicLattice.coordVec μ) ν = _
  by_cases h : ν = μ
  · subst h
    simp [PeriodicLattice.coordVec]
    ring
  · simp [PeriodicLattice.coordVec, h]
def reflectionGroup : Subgroup (Equiv.Perm Space) :=
  Subgroup.closure (range axisReflection)
theorem mem_reflectionGroup_iff (σ : Equiv.Perm Space) :
    σ ∈ reflectionGroup ↔ ∃ s, σ = flipSigns s := by
  constructor
  · intro h
    induction h using Subgroup.closure_induction with
    | mem σ h =>
      obtain ⟨μ, rfl⟩ := h
      exact ⟨_, axisReflection_eq_flipSigns μ⟩
    | one => exact ⟨1, flipSigns_one.symm⟩
    | mul _ _ _ _ h h' =>
      obtain ⟨s, rfl⟩ := h
      obtain ⟨s', rfl⟩ := h'
      exact ⟨s * s', flipSigns_mul s s'⟩
    | inv _ _ h =>
      obtain ⟨s, rfl⟩ := h
      exact ⟨s⁻¹, flipSigns_inv s⟩
  · rintro ⟨s, rfl⟩
    have single : ∀ (μ : Fin 4) (u : ℤˣ), flipSigns (Pi.mulSingle μ u) ∈ reflectionGroup := by
      intro μ u
      rcases Int.units_eq_one_or u with rfl | rfl
      · rw [Pi.mulSingle_one, flipSigns_one]
        exact one_mem _
      · rw [← axisReflection_eq_flipSigns]
        exact Subgroup.subset_closure (mem_range_self μ)
    have split : s = Pi.mulSingle 0 (s 0) * Pi.mulSingle 1 (s 1) * Pi.mulSingle 2 (s 2) *
        Pi.mulSingle 3 (s 3) := by
      funext ν
      fin_cases ν <;> simp
    rw [split, ← flipSigns_mul, ← flipSigns_mul, ← flipSigns_mul]
    exact mul_mem (mul_mem (mul_mem (single _ _) (single _ _)) (single _ _)) (single _ _)
theorem flipSigns_injective : Function.Injective flipSigns := by
  intro s s' h
  funext μ
  have := congrFun (congrArg (fun σ : Equiv.Perm Space => σ 1) h) μ
  simp only [flipSigns_apply, Pi.one_apply, mul_one] at this
  exact Units.ext (by exact_mod_cast this)
theorem card_reflectionGroup : Nat.card reflectionGroup = 16 := by
  have e : (Fin 4 → ℤˣ) ≃ reflectionGroup :=
    Equiv.ofBijective (fun s => ⟨flipSigns s, (mem_reflectionGroup_iff _).2 ⟨s, rfl⟩⟩)
      ⟨fun s s' h => flipSigns_injective (congrArg Subtype.val h), by
        rintro ⟨σ, h⟩
        obtain ⟨s, rfl⟩ := (mem_reflectionGroup_iff σ).1 h
        exact ⟨s, rfl⟩⟩
  rw [← Nat.card_congr e]
  simp [Nat.card_eq_fintype_card]
def centredCube (r : ℝ) : Set Space := {x | maxNorm x < r}
theorem centredCube_eq_ball (r : ℝ) : centredCube r = Metric.ball 0 r := by
  ext x
  simp [centredCube, maxNorm_eq_norm]
def scaledLattice (L K : ℕ) : AddSubgroup Space :=
  InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L (K : ℤ))
abbrev GaugeFieldsAt (a : ℝ) : Type := InfiniteLattice.GaugeField a
abbrev GaugeFieldsAtLevel (L K : ℕ) : Type :=
  GaugeFieldsAt (PeriodicLattice.meshSize L (K : ℤ))
end YangMills.Construction.ReflectionPositivity
