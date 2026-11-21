import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open Set
open scoped Pointwise
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def LatticeSymmetry.linkSetImage (g : LatticeSymmetry a) (S : Set (Link a)) : Set (Link a) :=
  g.linkMap '' S
def Link.shiftBy (l : Link a) (v : LatticePoint a) : Link a := (shift v).linkMap l
def shiftedLinks (S : Set (Link a)) (v : LatticePoint a) : Set (Link a) := (shift v).linkSetImage S
def signedUnitVectors : Set AmbientSpace :=
  {x | ∃ μ : Fin 4, x = Pi.single μ 1 ∨ x = -Pi.single μ 1}
def hyperoctahedralLinearGroup : Subgroup (AmbientSpace ≃ₗ[ℝ] AmbientSpace) where
  carrier := {w | w '' signedUnitVectors = signedUnitVectors}
  mul_mem' := by
    intro w w' hw hw'
    change (fun x => w (w' x)) '' signedUnitVectors = signedUnitVectors
    rw [← image_image (fun x => w x) (fun x => w' x), hw', hw]
  one_mem' := by
    change (fun x => x) '' signedUnitVectors = signedUnitVectors
    simp
  inv_mem' := by
    intro w hw
    change w.symm '' signedUnitVectors = signedUnitVectors
    conv_lhs => rw [← (show w '' signedUnitVectors = signedUnitVectors from hw)]
    rw [image_image]
    simp
theorem exists_mem_hyperoctahedralLinearGroup (f : AmbientSpace →ₗ[ℝ] AmbientSpace)
    (hf : BijOn f signedUnitVectors signedUnitVectors) :
    ∃ w ∈ hyperoctahedralLinearGroup, ⇑w = ⇑f := by
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    intro x _
    have hx : x = ∑ ν, x ν • (Pi.single ν 1 : AmbientSpace) := by
      funext μ
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx]
    refine Submodule.sum_mem _ fun ν _ => Submodule.smul_mem _ _ ?_
    obtain ⟨y, -, hy⟩ :=
      hf.surjOn (show (Pi.single ν 1 : AmbientSpace) ∈ signedUnitVectors from ⟨ν, Or.inl rfl⟩)
    exact ⟨y, hy⟩
  have hinj : Function.Injective f := LinearMap.injective_iff_surjective.mpr hsurj
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_, rfl⟩
  exact hf.image_eq
theorem mem_hyperoctahedralLinearGroup_iff (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) :
    w ∈ hyperoctahedralLinearGroup ↔ ∃ (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ),
      ∀ x μ, w x μ = ((s μ : ℤ) : ℝ) * x (π μ) := by
  constructor
  · intro hw
    have hw' : w '' signedUnitVectors = signedUnitVectors := hw
    have hmem : ∀ ν, ∃ (κ : Fin 4) (t : ℤˣ),
        w (Pi.single ν 1) = ((t : ℤ) : ℝ) • (Pi.single κ 1 : AmbientSpace) := by
      intro ν
      have hin : w (Pi.single ν 1) ∈ signedUnitVectors := by
        rw [← hw']
        exact mem_image_of_mem w ⟨ν, Or.inl rfl⟩
      obtain ⟨κ, h | h⟩ := hin
      · exact ⟨κ, 1, by simp [h]⟩
      · exact ⟨κ, -1, by simp [h]⟩
    choose σ ε hσ using hmem
    have hsq : ∀ ν, ((ε ν : ℤ) : ℝ) * ((ε ν : ℤ) : ℝ) = 1 := fun ν => by
      rcases Int.units_eq_one_or (ε ν) with h | h <;> simp [h]
    have hone : ∀ ν,
        w (((ε ν : ℤ) : ℝ) • (Pi.single ν 1 : AmbientSpace)) = Pi.single (σ ν) 1 := by
      intro ν
      rw [map_smul, hσ, smul_smul, hsq, one_smul]
    have hinj : Function.Injective σ := by
      intro ν ν' h
      have h2 := w.injective ((hone ν).trans (by rw [h]; exact (hone ν').symm))
      by_contra hne
      have h3 := congrFun h2 ν
      have h4 := hsq ν
      simp [Pi.single_eq_of_ne hne] at h3
    let σe : Equiv.Perm (Fin 4) := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
    have hσe : ∀ μ, σ (σe.symm μ) = μ := fun μ => σe.apply_symm_apply μ
    refine ⟨σe.symm, fun μ => ε (σe.symm μ), fun x μ => ?_⟩
    have hx : x = ∑ ν, x ν • (Pi.single ν 1 : AmbientSpace) := by
      funext κ
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single (σe.symm μ)]
    · simp only [map_smul, hσ, Pi.smul_apply, smul_eq_mul, hσe, Pi.single_eq_same]
      ring
    · intro ν _ hν
      have hne : μ ≠ σ ν := fun h => hν (by rw [h]; exact (σe.symm_apply_apply ν).symm)
      simp [map_smul, hσ, Pi.single_eq_of_ne hne]
    · simp
  · rintro ⟨π, s, h⟩
    have hsign : ∀ μ, ((s μ : ℤ) : ℝ) = 1 ∨ ((s μ : ℤ) : ℝ) = -1 := fun μ => by
      rcases Int.units_eq_one_or (s μ) with h | h <;> simp [h]
    have hsingle : ∀ κ,
        w (Pi.single (π κ) 1) = ((s κ : ℤ) : ℝ) • (Pi.single κ 1 : AmbientSpace) := by
      intro κ
      funext μ
      rw [h]
      by_cases hμ : μ = κ
      · subst hμ
        simp
      · have hne : π μ ≠ π κ := fun e => hμ (π.injective e)
        simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hμ]
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨x, ⟨ν, rfl | rfl⟩, rfl⟩
      · obtain ⟨κ, rfl⟩ := π.surjective ν
        rcases hsign κ with h1 | h1
        · exact ⟨κ, Or.inl (by rw [hsingle, h1, one_smul])⟩
        · exact ⟨κ, Or.inr (by rw [hsingle, h1, neg_one_smul])⟩
      · obtain ⟨κ, rfl⟩ := π.surjective ν
        rcases hsign κ with h1 | h1
        · exact ⟨κ, Or.inr (by rw [map_neg, hsingle, h1, one_smul])⟩
        · exact ⟨κ, Or.inl (by rw [map_neg, hsingle, h1, neg_one_smul, neg_neg])⟩
    · rintro x ⟨κ, rfl | rfl⟩
      · rcases hsign κ with h1 | h1
        · exact ⟨_, ⟨π κ, Or.inl rfl⟩, by rw [hsingle, h1, one_smul]⟩
        · exact ⟨_, ⟨π κ, Or.inr rfl⟩, by rw [map_neg, hsingle, h1, neg_one_smul, neg_neg]⟩
      · rcases hsign κ with h1 | h1
        · exact ⟨_, ⟨π κ, Or.inr rfl⟩, by rw [map_neg, hsingle, h1, one_smul]⟩
        · exact ⟨_, ⟨π κ, Or.inl rfl⟩, by rw [hsingle, h1, neg_one_smul]⟩
def latticeMotion (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) (v : LatticePoint a)
    (x : AmbientSpace) : AmbientSpace := w x + v
theorem latticeMotion_eq_comp (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) (v : LatticePoint a) :
    latticeMotion w v = (shift v).toFun ∘ w := rfl
def affineHyperoctahedralMaps (a : ℝ) : Set (AmbientSpace → AmbientSpace) :=
  {f | ∃ w ∈ hyperoctahedralLinearGroup, ∃ v : LatticePoint a, f = latticeMotion w v}
def IsLinearPart (a : ℝ) (f : AmbientSpace → AmbientSpace)
    (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) : Prop :=
  w ∈ hyperoctahedralLinearGroup ∧ ∃ v : LatticePoint a, f = latticeMotion w v
def signFlip (ε : Fin 4 → ℤˣ) : AmbientSpace ≃ₗ[ℝ] AmbientSpace where
  toFun x μ := ((ε μ : ℤ) : ℝ) * x μ
  invFun x μ := ((ε μ : ℤ) : ℝ) * x μ
  map_add' x y := by
    funext μ
    simp [mul_add]
  map_smul' t x := by
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv x := by
    funext μ
    rcases Int.units_eq_one_or (ε μ) with h | h <;> simp [h]
  right_inv x := by
    funext μ
    rcases Int.units_eq_one_or (ε μ) with h | h <;> simp [h]
def signFlipGroup : Subgroup (AmbientSpace ≃ₗ[ℝ] AmbientSpace) where
  carrier := range signFlip
  mul_mem' := by
    rintro _ _ ⟨ε, rfl⟩ ⟨ε', rfl⟩
    refine ⟨ε * ε', LinearEquiv.ext fun x => ?_⟩
    funext μ
    change ((((ε * ε') μ : ℤˣ) : ℤ) : ℝ) * x μ = ((ε μ : ℤ) : ℝ) * (((ε' μ : ℤ) : ℝ) * x μ)
    simp [mul_assoc]
  one_mem' := ⟨1, LinearEquiv.ext fun x => by
    funext μ
    change (((1 : Fin 4 → ℤˣ) μ : ℤ) : ℝ) * x μ = x μ
    simp⟩
  inv_mem' := by
    rintro _ ⟨ε, rfl⟩
    exact ⟨ε, LinearEquiv.ext fun x => rfl⟩
theorem signFlipGroup_le_hyperoctahedralLinearGroup :
    signFlipGroup ≤ hyperoctahedralLinearGroup := by
  rintro _ ⟨ε, rfl⟩
  exact (mem_hyperoctahedralLinearGroup_iff _).mpr ⟨1, ε, fun x μ => rfl⟩
theorem signFlip_injective : Function.Injective signFlip := by
  intro ε ε' h
  funext μ
  have h1 := congrFun (congrArg (fun w : AmbientSpace ≃ₗ[ℝ] AmbientSpace => w fun _ => (1 : ℝ)) h) μ
  have h2 : ((ε μ : ℤ) : ℝ) = ((ε' μ : ℤ) : ℝ) := by simpa [signFlip] using h1
  exact Units.ext (by exact_mod_cast h2)
def scaledCube (a : ℝ) (q : ℕ) : Set AmbientSpace := a • Set.pi univ fun _ => Icc (-(q : ℝ)) q
theorem mem_centeredCube (ha : 0 < a) (q : ℕ) (x : AmbientSpace) :
    x ∈ scaledCube a q ↔ ∀ μ, -((q : ℝ) * a) ≤ x μ ∧ x μ ≤ (q : ℝ) * a := by
  constructor
  · rintro ⟨y, hy, rfl⟩ μ
    obtain ⟨h1, h2⟩ := hy μ (mem_univ μ)
    simp only [Pi.smul_apply, smul_eq_mul]
    constructor <;> nlinarith
  · intro h
    refine ⟨a⁻¹ • x, fun μ _ => ?_, by simp [smul_smul, ha.ne']⟩
    obtain ⟨h1, h2⟩ := h μ
    have hi : 0 < a⁻¹ := inv_pos.mpr ha
    have hm : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
    simp only [Pi.smul_apply, smul_eq_mul]
    constructor <;> nlinarith
end InfiniteLattice
end YangMills.Construction
end
