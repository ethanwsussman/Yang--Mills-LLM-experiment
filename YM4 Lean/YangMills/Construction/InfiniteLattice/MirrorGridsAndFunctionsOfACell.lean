import YangMills.Construction.Lattice.GridCellsAndFaceReflections
import YangMills.Construction.InfiniteLattice.CutoffLattice
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
open YangMills.Construction.CutoffLattice (spacingAt FieldsAt)
namespace YangMills.Construction.InfiniteLattice
def ReflectionGrid.IsAdmissibleSide (L K : ℕ) (l : ℝ) : Prop :=
  (∃ q : ℤ, l = (L : ℝ) ^ q) ∧ spacingAt L K ≤ l / (L : ℝ) ^ 2
theorem ReflectionGrid.IsAdmissibleSide.pow_mul {L K : ℕ}
    (hL : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L) {l : ℝ}
    (h : ReflectionGrid.IsAdmissibleSide L K l) (n : ℕ) :
    ReflectionGrid.IsAdmissibleSide L K ((L : ℝ) ^ n * l) := by
  obtain ⟨⟨q, rfl⟩, hl⟩ := h
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := hL.2; omega : 1 ≤ L)
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  refine ⟨⟨(n : ℤ) + q, ?_⟩, ?_⟩
  · rw [zpow_add₀ hL0, zpow_natCast]
  · have hnn : 0 ≤ (L : ℝ) ^ q / (L : ℝ) ^ 2 :=
      (YangMills.Construction.CutoffLattice.spacingAt_pos hL K).le.trans hl
    calc spacingAt L K ≤ (L : ℝ) ^ q / (L : ℝ) ^ 2 := hl
      _ ≤ (L : ℝ) ^ n * ((L : ℝ) ^ q / (L : ℝ) ^ 2) :=
        le_mul_of_one_le_left hnn (one_le_pow₀ hL1)
      _ = (L : ℝ) ^ n * (L : ℝ) ^ q / (L : ℝ) ^ 2 := by ring
structure ReflectionGrid (L K : ℕ) where
  edge : ℝ
  edge_admissible : ReflectionGrid.IsAdmissibleSide L K edge
  shift : AmbientSpace
  shift_mem : ∀ μ, ∃ i : ℤ, shift μ = spacingAt L K * ((i : ℝ) + 1 / 2)
namespace ReflectionGrid
variable {L K : ℕ} (G : ReflectionGrid L K)
def basisVec (μ : Fin 4) : AmbientSpace := Pi.single μ 1
def cornerAt (k : Fin 4 → ℤ) : AmbientSpace := G.shift + G.edge • fun μ => (k μ : ℝ)
def tile (k : Fin 4 → ℤ) : Set AmbientSpace := cube (G.cornerAt k) G.edge
def tiling : Set (Set AmbientSpace) := range G.tile
def tileInterior (k : Fin 4 → ℤ) : Set AmbientSpace :=
  {x | ∀ μ, G.cornerAt k μ < x μ ∧ x μ < G.cornerAt k μ + G.edge}
def tileCenter (k : Fin 4 → ℤ) : AmbientSpace :=
  G.cornerAt k + (G.edge / 2) • ∑ μ, basisVec μ
def wall (μ : Fin 4) (k : ℤ) : Set AmbientSpace := {x | x μ = G.shift μ + k * G.edge}
def IsWall (S : Set AmbientSpace) : Prop := ∃ (μ : Fin 4) (k : ℤ), S = G.wall μ k
def wallReflect (μ : Fin 4) (k : ℤ) (x : AmbientSpace) : AmbientSpace :=
  x - (2 * (x μ - G.shift μ - k * G.edge)) • basisVec μ
theorem wallReflect_eq_hyperplaneReflect (μ : Fin 4) (k : ℤ) :
    G.wallReflect μ k =
      hyperplaneReflect (basisVec μ)
        (G.shift μ + k * G.edge) := by
  have hdot : ∀ x : AmbientSpace, dotProduct (basisVec μ) x = x μ := fun x => by
    simp [basisVec, dotProduct, Pi.single_apply]
  have hone : dotProduct (basisVec μ) (basisVec μ) = 1 := by
    rw [hdot]
    simp [basisVec]
  funext x
  simp only [wallReflect, hyperplaneReflect, hone, hdot, div_one]
  congr 2
  ring
def signFlip (μ : Fin 4) : Fin 4 → ℝ := Function.update 1 μ (-1)
theorem signFlip_mul_self (μ i : Fin 4) : signFlip μ i * signFlip μ i = 1 := by apply _root_.YangMills.Construction.CellGrid.flipDiag_mul_self <;> assumption
def axisFlip (μ : Fin 4) : AmbientSpace ≃ₗ[ℝ] AmbientSpace :=
  LinearEquiv.ofInvolutive (Matrix.toLin' (Matrix.diagonal (signFlip μ))) fun x => by
    funext i
    simp only [Matrix.toLin'_apply, Matrix.mulVec_diagonal, ← mul_assoc, signFlip_mul_self,
      one_mul]
theorem axisFlip_apply (μ : Fin 4) (x : AmbientSpace) (i : Fin 4) :
    axisFlip μ x i = signFlip μ i * x i := by
  show Matrix.toLin' (Matrix.diagonal (signFlip μ)) x i = _
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
def wallReflectEquiv (μ : Fin 4) (k : ℤ) : AmbientSpace ≃ᵃ[ℝ] AmbientSpace :=
  AffineEquiv.mk' (G.wallReflect μ k) (axisFlip μ) 0 fun x => by
    funext i
    by_cases h : i = μ
    · subst h
      simp [wallReflect, axisFlip_apply, signFlip,
        basisVec]
      ring
    · simp [wallReflect, axisFlip_apply, signFlip,
        basisVec, Function.update_of_ne h, Pi.single_eq_of_ne h]
theorem coe_wallReflectEquiv (μ : Fin 4) (k : ℤ) :
    ⇑(G.wallReflectEquiv μ k) = G.wallReflect μ k := rfl
def reflectionGroup : Subgroup (AmbientSpace ≃ᵃ[ℝ] AmbientSpace) :=
  Subgroup.closure (range fun p : Fin 4 × ℤ => G.wallReflectEquiv p.1 p.2)
theorem euclidNormVec_sub_of_mem_reflectionGroup {g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace}
    (hg : g ∈ G.reflectionGroup) (x y : AmbientSpace) :
    YangMills.Construction.TorusMetric.euclidNormVec (g x - g y) =
      YangMills.Construction.TorusMetric.euclidNormVec (x - y) := by
  induction hg using Subgroup.closure_induction generalizing x y with
  | mem g hg =>
    obtain ⟨⟨μ, k⟩, rfl⟩ := hg
    simp only [coe_wallReflectEquiv, wallReflect_eq_hyperplaneReflect]
    refine euclidNormVec_hyperplaneReflect_sub ?_ _ x y
    simp [basisVec, dotProduct, Pi.single_apply]
  | one => rfl
  | mul g h _ _ hg hh =>
    exact (hg (h x) (h y)).trans (hh x y)
  | inv g _ hg =>
    have h := hg (g⁻¹ x) (g⁻¹ y)
    have hx : ∀ z : AmbientSpace, g (g⁻¹ z) = z := fun z => g.apply_symm_apply z
    rw [hx, hx] at h
    exact h.symm
def orientation (g : G.reflectionGroup) : ℝ :=
  LinearMap.det ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).linear : AmbientSpace →ₗ[ℝ] AmbientSpace)
theorem orientation_eq_one_or_neg_one (g : G.reflectionGroup) :
    G.orientation g = 1 ∨ G.orientation g = -1 := by
  let φ : (AmbientSpace ≃ᵃ[ℝ] AmbientSpace) →* ℝˣ := LinearEquiv.det.comp AffineEquiv.linearHom
  have hφ : ∀ h : AmbientSpace ≃ᵃ[ℝ] AmbientSpace,
      ((φ h : ℝˣ) : ℝ) = LinearMap.det (h.linear : AmbientSpace →ₗ[ℝ] AmbientSpace) := fun h =>
    LinearEquiv.coe_det _
  have hsq : ∀ h ∈ G.reflectionGroup, φ h ^ 2 = 1 := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem h hh =>
      obtain ⟨⟨μ, k⟩, rfl⟩ := hh
      ext
      have hdet : LinearMap.det
          ((G.wallReflectEquiv μ k).linear : AmbientSpace →ₗ[ℝ] AmbientSpace) = -1 := by
        have hl : ((G.wallReflectEquiv μ k).linear : AmbientSpace →ₗ[ℝ] AmbientSpace) =
            Matrix.toLin' (Matrix.diagonal (signFlip μ)) := rfl
        rw [hl, LinearMap.det_toLin', Matrix.det_diagonal]
        fin_cases μ <;> simp [signFlip, Function.update]
      simp only [Units.val_pow_eq_pow_val, hφ, hdet, Units.val_one]
      norm_num
    | one => simp
    | mul g h _ _ hg hh => rw [map_mul, mul_pow, hg, hh, one_mul]
    | inv g _ hg => rw [map_inv, inv_pow, hg, inv_one]
  have h1 : G.orientation g ^ 2 = 1 := by
    have := congrArg (fun u : ℝˣ => (u : ℝ)) (hsq g g.2)
    simpa [hφ, orientation] using this
  exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h1)
def IsTileObservable (k : Fin 4 → ℤ) (A : FieldsAt L K → ℂ) : Prop :=
  IsBoundedObservable A ∧ IsRegionMeasurable (G.tileInterior k) A
def tileAlgebra (k : Fin 4 → ℤ) : StarSubalgebra ℂ (FieldsAt L K → ℂ) where
  carrier := {A | G.IsTileObservable k A}
  mul_mem' := by
    rintro A B ⟨⟨hA, C, hC⟩, hA'⟩ ⟨⟨hB, D, hD⟩, hB'⟩
    refine ⟨⟨hA.mul hB, C * D, fun U => ?_⟩, Measurable.mul hA' hB'⟩
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hC U) (hD U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
  add_mem' := by
    rintro A B ⟨⟨hA, C, hC⟩, hA'⟩ ⟨⟨hB, D, hD⟩, hB'⟩
    refine ⟨⟨hA.add hB, C + D, fun U => ?_⟩, Measurable.add hA' hB'⟩
    exact (norm_add_le _ _).trans (add_le_add (hC U) (hD U))
  algebraMap_mem' z :=
    ⟨⟨measurable_const, ‖z‖, fun _ => le_rfl⟩, measurable_const⟩
  star_mem' := by
    rintro A ⟨⟨hA, C, hC⟩, hA'⟩
    refine ⟨⟨continuous_star.measurable.comp hA, C, fun U => ?_⟩,
      continuous_star.measurable.comp hA'⟩
    simpa using hC U
theorem mem_tileAlgebra {k : Fin 4 → ℤ} {A : FieldsAt L K → ℂ} :
    A ∈ G.tileAlgebra k ↔ G.IsTileObservable k A := Iff.rfl
end ReflectionGrid
end YangMills.Construction.InfiniteLattice
