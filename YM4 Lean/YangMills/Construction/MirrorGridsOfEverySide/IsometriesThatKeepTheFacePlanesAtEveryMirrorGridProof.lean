import YangMills.Construction.ChessboardTori.MirrorPeriodicWeightsAsCellFunctionsProof
import YangMills.Construction.ChessboardTori.PeriodicRealizationOnARectangularTorusProof
import YangMills.Construction.MirrorGridsOfEverySide.CellsOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsOfTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.IsometriesThatKeepTheFacePlanesAtEveryMirrorGrid
import YangMills.Construction.ReflectionPositivity.CovarianceOfTheCurvatureDensity
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open InfiniteLattice (AmbientSpace)
open ChessboardTori (ReflectionGrid orientationSign)
noncomputable section
namespace MirrorGridsAllSides.WallPreserving
def signedPermEquiv (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℝ) (hε : ∀ μ, ε μ * ε μ = 1) :
    AmbientSpace ≃ₗ[ℝ] AmbientSpace where
  toFun x μ := ε μ * x (σ μ)
  map_add' x y := by
    funext μ
    simp [mul_add]
  map_smul' c x := by
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  invFun y ν := ε (σ⁻¹ ν) * y (σ⁻¹ ν)
  left_inv x := by
    funext ν
    simp [← mul_assoc, hε]
  right_inv y := by
    funext μ
    simp [← mul_assoc, hε]
def IsSignedIsometry (ρ : Equiv.Perm AmbientSpace) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℝ) (hε : ∀ μ, ε μ * ε μ = 1) (v : AmbientSpace),
    ∀ x, ρ x = signedPermEquiv σ ε hε x + v
theorem inv_apply_of_eq_signedPermEquiv {σ : Equiv.Perm (Fin 4)} {ε : Fin 4 → ℝ}
    {hε : ∀ μ, ε μ * ε μ = 1} {v : AmbientSpace}
    {ρ : Equiv.Perm AmbientSpace} (h : ∀ x, ρ x = signedPermEquiv σ ε hε x + v) (y : AmbientSpace) :
    ρ⁻¹ y = (signedPermEquiv σ ε hε).symm (y - v) := by
  apply ρ.injective
  rw [show ρ (ρ⁻¹ y) = y by simp, h]
  simp
theorem IsSignedIsometry.inv {ρ : Equiv.Perm AmbientSpace} (h : IsSignedIsometry ρ) :
    IsSignedIsometry ρ⁻¹ := by
  obtain ⟨σ, ε, hε, v, hρ⟩ := h
  refine ⟨σ⁻¹, fun μ => ε (σ⁻¹ μ), fun μ => hε _, -(signedPermEquiv σ ε hε).symm v, fun y => ?_⟩
  rw [inv_apply_of_eq_signedPermEquiv hρ, map_sub, sub_eq_add_neg]
  rfl
def IsSignedIsometry.toHomeomorph {ρ : Equiv.Perm AmbientSpace} (h : IsSignedIsometry ρ) :
    AmbientSpace ≃ₜ AmbientSpace where
  toEquiv := ρ
  continuous_toFun := by
    obtain ⟨σ, ε, hε, v, hρ⟩ := h
    have hc : Continuous fun x => signedPermEquiv σ ε hε x + v :=
      (signedPermEquiv σ ε hε).toLinearMap.continuous_of_finiteDimensional.add continuous_const
    exact hc.congr fun x => (hρ x).symm
  continuous_invFun := by
    obtain ⟨σ, ε, hε, v, hρ⟩ := h.inv
    have hc : Continuous fun x => signedPermEquiv σ ε hε x + v :=
      (signedPermEquiv σ ε hε).toLinearMap.continuous_of_finiteDimensional.add continuous_const
    exact hc.congr fun x => (hρ x).symm
theorem IsSignedIsometry.coe_toHomeomorph {ρ : Equiv.Perm AmbientSpace} (h : IsSignedIsometry ρ) :
    ⇑h.toHomeomorph = ρ := rfl
theorem IsSignedIsometry.convex_image {ρ : Equiv.Perm AmbientSpace} (h : IsSignedIsometry ρ)
    {I : Set AmbientSpace} (hI : Convex ℝ I) : Convex ℝ (ρ '' I) := by
  obtain ⟨σ, ε, hε, v, hρ⟩ := h
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ s t hs ht hst
  refine ⟨s • a + t • b, hI ha hb hs ht hst, ?_⟩
  obtain rfl : t = 1 - s := by linarith
  simp only [hρ, map_add, map_smul]
  module
theorem linearComponent_eq {r : AmbientSpace → AmbientSpace} {R : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (h : ChessboardTori.HasLinearComponent r R) : ChessboardTori.linearComponent r = R := by apply _root_.YangMills.Construction.ChessboardTori.BoxTorusQuotient.linearComponent_eq <;> assumption
theorem orientationSign_eq_of_det_eq {r r' : AmbientSpace → AmbientSpace}
    {R R' : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (h : ChessboardTori.HasLinearComponent r R) (h' : ChessboardTori.HasLinearComponent r' R')
    (hd : LinearMap.det R = LinearMap.det R') : orientationSign r = orientationSign r' := by
  simp only [orientationSign, linearComponent_eq h, linearComponent_eq h', hd]
theorem orientationSign_conj {ρ h : Equiv.Perm AmbientSpace} (hρ : IsSignedIsometry ρ)
    {A : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hA : ChessboardTori.HasLinearComponent h A) : orientationSign ⇑(ρ * h * ρ⁻¹) = orientationSign h := by
  obtain ⟨σ, ε, hε, v, hv⟩ := hρ
  obtain ⟨w, hw⟩ := hA
  set e := signedPermEquiv σ ε hε with he
  have hlin : ChessboardTori.HasLinearComponent ⇑(ρ * h * ρ⁻¹)
      ((e : AmbientSpace →ₗ[ℝ] AmbientSpace) ∘ₗ A ∘ₗ (e.symm : AmbientSpace →ₗ[ℝ] AmbientSpace)) := by
    refine ⟨e (w - A (e.symm v)) + v, fun y => ?_⟩
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [inv_apply_of_eq_signedPermEquiv hv, hv, hw, map_sub, map_sub, map_add, map_sub, map_sub]
    abel
  exact orientationSign_eq_of_det_eq hlin ⟨w, hw⟩ (LinearMap.det_conj A e)
section Cells
variable {D : GridSetup} (g : ReflectionGrid D)
theorem cellSide_pos : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
theorem cell_eq_pi (k : Fin 4 → ℤ) : g.cell k = Set.pi univ fun μ =>
    Icc (g.origin μ + g.cellSide * k μ) (g.origin μ + g.cellSide * k μ + g.cellSide) := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionPeriodicWeightsAsCellFunctions.cell_eq_pi <;> assumption
theorem interior_cell (k : Fin 4 → ℤ) : interior (g.cell k) = Set.pi univ fun μ =>
    Ioo (g.origin μ + g.cellSide * k μ) (g.origin μ + g.cellSide * k μ + g.cellSide) := by
  rw [cell_eq_pi, interior_pi_set finite_univ]
  simp only [interior_Icc]
theorem convex_cell (k : Fin 4 → ℤ) : Convex ℝ (g.cell k) := by
  rw [cell_eq_pi]
  exact convex_pi fun _ _ => convex_Icc _ _
theorem isClosed_cell (k : Fin 4 → ℤ) : IsClosed (g.cell k) := by
  rw [cell_eq_pi]
  exact isClosed_set_pi fun _ _ => isClosed_Icc
theorem interior_cell_nonempty (k : Fin 4 → ℤ) : (interior (g.cell k)).Nonempty := by
  rw [interior_cell]
  refine ⟨fun μ => g.origin μ + g.cellSide * k μ + g.cellSide / 2, fun μ _ => ?_⟩
  have := cellSide_pos g
  constructor <;> simp only <;> linarith
theorem closure_interior_cell (k : Fin 4 → ℤ) : closure (interior (g.cell k)) = g.cell k := by
  rw [(convex_cell g k).closure_interior_eq_closure_of_nonempty_interior
    (interior_cell_nonempty g k), (isClosed_cell g k).closure_eq]
theorem disjoint_interior_cell_walls (k : Fin 4 → ℤ) : Disjoint (interior (g.cell k)) g.walls := by
  rw [Set.disjoint_left, interior_cell]
  intro x hx hxP
  simp only [ReflectionGrid.walls, mem_iUnion] at hxP
  obtain ⟨μ, j, hj⟩ := hxP
  have hj' : x μ = g.origin μ + j * g.cellSide := hj
  obtain ⟨h₁, h₂⟩ := hx μ (mem_univ _)
  have hs := cellSide_pos g
  rw [hj'] at h₁ h₂
  have h₃ : (k μ : ℝ) < j := by
    by_contra hc
    have : (j : ℝ) * g.cellSide ≤ k μ * g.cellSide := mul_le_mul_of_nonneg_right (not_lt.mp hc) hs.le
    linarith
  have h₄ : (j : ℝ) < k μ + 1 := by
    by_contra hc
    have : ((k μ : ℝ) + 1) * g.cellSide ≤ j * g.cellSide :=
      mul_le_mul_of_nonneg_right (not_lt.mp hc) hs.le
    linarith
  have h₅ : k μ < j := by exact_mod_cast h₃
  have h₆ : j < k μ + 1 := by exact_mod_cast h₄
  omega
variable {g}
theorem inv_image_walls {ρ : Equiv.Perm AmbientSpace} (hP : ρ '' g.walls = g.walls) :
    ⇑(ρ⁻¹ : Equiv.Perm AmbientSpace) '' g.walls = g.walls := by
  conv_lhs => rw [← hP]
  rw [← image_comp]
  simp
theorem exists_image_interior_subset_interior {ρ : Equiv.Perm AmbientSpace} (hρ : IsSignedIsometry ρ)
    (hP : ρ '' g.walls = g.walls) (hd : g.DistToWalls) (k : Fin 4 → ℤ) :
    ∃ S' ∈ g.cellSet, ρ '' interior (g.cell k) ⊆ interior S' := by
  refine hd.2.2.2 _ (hρ.convex_image (convex_cell g k).interior) ?_
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ hy
  rw [← hP] at hy
  obtain ⟨z, hz, hzx⟩ := hy
  obtain rfl := ρ.injective hzx
  exact Set.disjoint_left.mp (disjoint_interior_cell_walls g k) hx hz
theorem image_cell_mem {ρ : Equiv.Perm AmbientSpace} (hρ : IsSignedIsometry ρ)
    (hP : ρ '' g.walls = g.walls) (hd : g.DistToWalls) {S : Set AmbientSpace}
    (hS : S ∈ g.cellSet) : ρ '' S ∈ g.cellSet ∧ ρ '' interior S = interior (ρ '' S) := by
  obtain ⟨k, rfl⟩ := hS
  obtain ⟨_, ⟨k', rfl⟩, h₁⟩ := exists_image_interior_subset_interior hρ hP hd k
  obtain ⟨_, ⟨k'', rfl⟩, h₂⟩ := exists_image_interior_subset_interior hρ.inv (inv_image_walls hP) hd k'
  have hback : interior (g.cell k) ⊆ interior (g.cell k'') := fun x hx =>
    h₂ ⟨ρ x, h₁ ⟨x, hx, rfl⟩, show ρ⁻¹ (ρ x) = x by simp⟩
  obtain ⟨x₀, hx₀⟩ := interior_cell_nonempty g k
  have hx₀P : x₀ ∉ g.walls := fun h =>
    Set.disjoint_left.mp (disjoint_interior_cell_walls g k) hx₀ h
  have heq : g.cell k'' = g.cell k :=
    (hd.2.1 x₀ hx₀P).unique ⟨⟨k'', rfl⟩, hback hx₀⟩ ⟨⟨k, rfl⟩, hx₀⟩
  rw [heq] at h₂
  have hint : ρ '' interior (g.cell k) = interior (g.cell k') := by
    refine Subset.antisymm h₁ fun y hy => ?_
    exact ⟨ρ⁻¹ y, h₂ ⟨y, hy, rfl⟩, show ρ (ρ⁻¹ y) = y by simp⟩
  have hcell : ρ '' g.cell k = g.cell k' := by
    have hcl := hρ.toHomeomorph.image_closure (interior (g.cell k))
    rw [closure_interior_cell, hρ.coe_toHomeomorph, hint, closure_interior_cell] at hcl
    exact hcl
  rw [hcell]
  exact ⟨⟨k', rfl⟩, hint⟩
end Cells
section Reflections
variable {D : GridSetup} {g : ReflectionGrid D}
theorem conj_reflectPerm_mem {ρ : Equiv.Perm AmbientSpace} (hρ : IsSignedIsometry ρ)
    (hP : ρ '' g.walls = g.walls) (ν : Fin 4) (k : ℤ) :
    ρ * g.reflectPerm ν k * ρ⁻¹ ∈ g.reflectionGroup := by
  obtain ⟨σ, ε, hε, v, hv⟩ := hρ
  have hco : ∀ (x : AmbientSpace) (μ : Fin 4), ρ x μ = ε μ * x (σ μ) + v μ := fun x μ => by
    rw [hv]
    rfl
  obtain ⟨lam, hσ⟩ : ∃ lam, σ lam = ν := σ.surjective ν
  have hs := cellSide_pos g
  obtain ⟨k', hk'⟩ : ∃ k' : ℤ,
      ε lam * (g.origin ν + k * g.cellSide) + v lam = g.origin lam + k' * g.cellSide := by
    let y : AmbientSpace := fun μ =>
      if μ = lam then ε lam * (g.origin ν + k * g.cellSide) + v lam else g.origin μ + g.cellSide / 2
    have hyl : y lam = ε lam * (g.origin ν + k * g.cellSide) + v lam := by simp [y]
    have hx : (ρ⁻¹ y) ν = g.origin ν + k * g.cellSide := by
      have h1 := hco (ρ⁻¹ y) lam
      rw [show ρ (ρ⁻¹ y) = y by simp, hyl, hσ] at h1
      have h2 : ε lam * (ρ⁻¹ y) ν = ε lam * (g.origin ν + k * g.cellSide) := by linarith
      have h3 := congrArg (fun z => ε lam * z) h2
      simpa [← mul_assoc, hε] using h3
    have hyP : y ∈ g.walls := by
      rw [← hP]
      refine ⟨ρ⁻¹ y, ?_, by simp⟩
      simp only [ReflectionGrid.walls, mem_iUnion]
      exact ⟨ν, k, hx⟩
    simp only [ReflectionGrid.walls, mem_iUnion] at hyP
    obtain ⟨μ, j, hj⟩ := hyP
    have hj' : y μ = g.origin μ + j * g.cellSide := hj
    by_cases hμ : μ = lam
    · subst hμ
      exact ⟨j, by rw [← hyl, hj']⟩
    · exfalso
      have h0 : y μ = g.origin μ + g.cellSide / 2 := by simp [y, hμ]
      rw [h0] at hj'
      have h1 : g.cellSide * (2 * (j : ℝ) - 1) = 0 := by linarith
      have h2 : (2 * (j : ℝ) - 1) = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hs.ne'
        · exact h
      have h3 : 2 * j - 1 = 0 := by exact_mod_cast h2
      omega
  have hconj : ρ * g.reflectPerm ν k * ρ⁻¹ = g.reflectPerm lam k' := by
    refine Equiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := ρ.surjective y
    funext μ
    have hxx : ρ⁻¹ (ρ x) = x := by simp
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hxx]
    show ρ (g.reflect ν k x) μ = g.reflect lam k' (ρ x) μ
    rw [hco]
    by_cases hμ : μ = lam
    · subst hμ
      simp only [ReflectionGrid.reflect, Pi.sub_apply, Pi.smul_apply, ChessboardTori.coordVec,
        Pi.single_eq_same, smul_eq_mul, mul_one, hσ]
      rw [hco x μ, hσ]
      linear_combination 2 * hk'
    · have hσμ : σ μ ≠ ν := fun h => hμ (σ.injective (h.trans hσ.symm))
      simp [ReflectionGrid.reflect, ChessboardTori.coordVec, Pi.single_eq_of_ne hμ,
        Pi.single_eq_of_ne hσμ, hco]
  rw [hconj]
  exact Subgroup.subset_closure ⟨(lam, k'), rfl⟩
theorem conj_mem_reflectionGroup {ρ h : Equiv.Perm AmbientSpace} (hρ : IsSignedIsometry ρ)
    (hP : ρ '' g.walls = g.walls) (hh : h ∈ g.reflectionGroup) :
    ρ * h * ρ⁻¹ ∈ g.reflectionGroup := by
  induction hh using Subgroup.closure_induction with
  | mem h hh =>
    obtain ⟨⟨ν, k⟩, rfl⟩ := hh
    exact conj_reflectPerm_mem hρ hP ν k
  | one => simp
  | mul a b _ _ ha hb =>
    have e : ρ * (a * b) * ρ⁻¹ = (ρ * a * ρ⁻¹) * (ρ * b * ρ⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : ρ * a⁻¹ * ρ⁻¹ = (ρ * a * ρ⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha
end Reflections
section Lifts
variable {D : GridSetup} {g : ReflectionGrid D}
structure TorusLift (g : ReflectionGrid D) (s t : D.Torus → D.Torus) (ρ : Equiv.Perm AmbientSpace) :
    Prop where
  isSigned : IsSignedIsometry ρ
  commutes : ∀ x, s (D.proj x) = D.proj (ρ x)
  left_inv : ∀ y, t (s y) = y
  right_inv : ∀ y, s (t y) = y
  image_walls : ρ '' g.walls = g.walls
variable {s t : D.Torus → D.Torus} {ρ : Equiv.Perm AmbientSpace}
theorem TorusLift.symm (h : TorusLift g s t ρ) : TorusLift g t s ρ⁻¹ where
  isSigned := h.isSigned.inv
  commutes x := by
    have h1 := h.commutes (ρ⁻¹ x)
    rw [show ρ (ρ⁻¹ x) = x by simp] at h1
    rw [← h1, h.left_inv]
  left_inv := h.right_inv
  right_inv := h.left_inv
  image_walls := inv_image_walls h.image_walls
theorem TorusLift.image_proj_image (h : TorusLift g s t ρ) (S : Set AmbientSpace) :
    s '' (D.proj '' S) = D.proj '' (ρ '' S) := by
  rw [← image_comp, ← image_comp]
  exact image_congr fun x _ => h.commutes x
theorem TorusLift.image_mem_torusCellSet (h : TorusLift g s t ρ) (hd : g.DistToWalls)
    {C : Set D.Torus} (hC : C ∈ g.torusCellSet) : s '' C ∈ g.torusCellSet := by
  obtain ⟨S, hS, rfl⟩ := hC
  show s '' (D.proj '' S) ∈ g.torusCellSet
  rw [h.image_proj_image]
  exact ⟨ρ '' S, (image_cell_mem h.isSigned h.image_walls hd hS).1, rfl⟩
theorem TorusLift.bijOn_torusCellSet (h : TorusLift g s t ρ) (hd : g.DistToWalls) :
    BijOn (fun C => s '' C) g.torusCellSet g.torusCellSet := by
  have hback : ∀ C : Set D.Torus, t '' (s '' C) = C := fun C => by
    rw [← image_comp]
    simp [h.left_inv]
  have hfwd : ∀ C : Set D.Torus, s '' (t '' C) = C := fun C => by
    rw [← image_comp]
    simp [h.right_inv]
  refine ⟨fun C hC => h.image_mem_torusCellSet hd hC, fun C _ C' _ e => ?_,
    fun C hC => ⟨t '' C, h.symm.image_mem_torusCellSet hd hC, hfwd C⟩⟩
  rw [← hback C, ← hback C']
  exact congrArg (fun Z => t '' Z) e
theorem TorusLift.proj_comp_conj (h : TorusLift g s t ρ) {r : Equiv.Perm AmbientSpace}
    {u : D.Torus → D.Torus} (hru : D.proj ∘ r = u ∘ D.proj) :
    D.proj ∘ ⇑(ρ * r * ρ⁻¹) = (s ∘ u ∘ t) ∘ D.proj := by
  funext x
  have h1 := h.symm.commutes x
  have h2 := congrFun hru (ρ⁻¹ x)
  simp only [Function.comp_apply, Equiv.Perm.coe_mul] at h2 ⊢
  rw [h1, ← h2, h.commutes]
theorem TorusLift.conj_mem_inducedTorusMaps (h : TorusLift g s t ρ) {u : D.Torus → D.Torus}
    (hu : u ∈ g.inducedTorusMaps) : s ∘ u ∘ t ∈ g.inducedTorusMaps := by
  obtain ⟨r, hr, hru⟩ := hu
  exact ⟨ρ * r * ρ⁻¹, conj_mem_reflectionGroup h.isSigned h.image_walls hr, h.proj_comp_conj hru⟩
theorem TorusLift.bijOn_conj (h : TorusLift g s t ρ) :
    BijOn (fun u => s ∘ u ∘ t) g.inducedTorusMaps g.inducedTorusMaps := by
  refine ⟨fun u hu => h.conj_mem_inducedTorusMaps hu, fun u _ u' _ e => ?_,
    fun u hu => ⟨t ∘ u ∘ s, h.symm.conj_mem_inducedTorusMaps hu, ?_⟩⟩
  · funext y
    have h1 := congrFun e (s y)
    simp only [Function.comp_apply, h.left_inv] at h1
    rw [← h.left_inv (u y), h1, h.left_inv]
  · funext y
    simp [Function.comp_apply, h.right_inv]
theorem TorusLift.torusSign_conj (h : TorusLift g s t ρ) (hG : ReflectionGroupActsOnCells g)
    (hT : TorusGroupActsOnCells g) {u : D.Torus → D.Torus} (hu : u ∈ g.inducedTorusMaps) :
    g.torusSign (s ∘ u ∘ t) = g.torusSign u := by
  obtain ⟨r, hr, hru⟩ := id hu
  have h₁ := hT.2.2.2.1 u hu ⟨r, hr⟩ hru
  have h₂ := hT.2.2.2.1 _ (h.conj_mem_inducedTorusMaps hu)
    ⟨ρ * r * ρ⁻¹, conj_mem_reflectionGroup h.isSigned h.image_walls hr⟩ (h.proj_comp_conj hru)
  obtain ⟨-, ⟨ε, -, hlin⟩, -⟩ := hG.1 r hr
  rw [← h₁, ← h₂]
  exact orientationSign_conj h.isSigned hlin
theorem TorusLift.invFun_eq (h : TorusLift g s t ρ) : Function.invFun s = t := by
  have hinj : Function.Injective s := fun a b e => by rw [← h.left_inv a, e, h.left_inv]
  funext y
  have h1 := Function.leftInverse_invFun hinj (t y)
  rwa [h.right_inv] at h1
theorem TorusLift.image_torusCellInterior (h : TorusLift g s t ρ) (hd : g.DistToWalls)
    (hc : TorusCellStructure g) {C : Set D.Torus} (hC : C ∈ g.torusCellSet) :
    s '' g.torusCellInterior C = g.torusCellInterior (s '' C) := by
  have hopen : ∀ k, g.torusCellInterior (D.proj '' g.cell k) =
      D.proj '' interior (g.cell k) := fun k => (hc.2.2.2.2 k k rfl).2.1
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hC
  obtain ⟨⟨k', hk'⟩, hint⟩ :=
    image_cell_mem h.isSigned h.image_walls hd (⟨k, rfl⟩ : g.cell k ∈ g.cellSet)
  show s '' g.torusCellInterior (D.proj '' g.cell k) =
    g.torusCellInterior (s '' (D.proj '' g.cell k))
  rw [hopen k, h.image_proj_image, h.image_proj_image, hint, ← hk', hopen k']
end Lifts
section Observables
open PeriodicLattice (TorusLatticeSymmetry)
variable {D : GridSetup} {g : ReflectionGrid D}
def MapsLinksToLinks (s : D.TorusSymmetry) : Prop :=
  ∀ b : D.PeriodicLink, ∃ b', TorusLatticeSymmetry.IsBondImage s b b'
theorem isBondImage_bondMap {s : D.TorusSymmetry} (hs : MapsLinksToLinks s) (b : D.PeriodicLink) :
    TorusLatticeSymmetry.IsBondImage s b (TorusLatticeSymmetry.bondMap s b) := by
  have e : TorusLatticeSymmetry.bondMap s b = (hs b).choose := dif_pos (hs b)
  rw [e]
  exact (hs b).choose_spec
theorem source_bondMap {s : D.TorusSymmetry} (hs : MapsLinksToLinks s) (b : D.PeriodicLink) :
    ((TorusLatticeSymmetry.bondMap s b).source : D.Torus) = s.toFun b.source :=
  congrArg (fun p : D.TorusPoint × D.TorusPoint => (p.1 : D.Torus)) (isBondImage_bondMap hs b)
theorem target_bondMap {s : D.TorusSymmetry} (hs : MapsLinksToLinks s) (b : D.PeriodicLink) :
    ((TorusLatticeSymmetry.bondMap s b).target : D.Torus) = s.toFun b.target :=
  congrArg (fun p : D.TorusPoint × D.TorusPoint => (p.2 : D.Torus)) (isBondImage_bondMap hs b)
theorem bondMap_bondMap {s t : D.TorusSymmetry} (hs : MapsLinksToLinks s) (ht : MapsLinksToLinks t)
    (h : ∀ y, s.toFun (t.toFun y) = y) (b : D.PeriodicLink) :
    TorusLatticeSymmetry.bondMap s (TorusLatticeSymmetry.bondMap t b) = b := by
  refine PeriodicLattice.Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact (source_bondMap hs _).trans ((congrArg s.toFun (source_bondMap ht b)).trans (h _))
  · exact (target_bondMap hs _).trans ((congrArg s.toFun (target_bondMap ht b)).trans (h _))
theorem bondMap_mem_torusCellLinks {s : D.TorusSymmetry} {t : D.Torus → D.Torus}
    {ρ : Equiv.Perm AmbientSpace}
    (h : TorusLift g s.toFun t ρ) (hs : MapsLinksToLinks s) (hd : g.DistToWalls)
    (hc : TorusCellStructure g) {C : Set D.Torus} (hC : C ∈ g.torusCellSet) {b : D.PeriodicLink}
    (hb : b ∈ g.torusCellLinks C) :
    TorusLatticeSymmetry.bondMap s b ∈ g.torusCellLinks (s.toFun '' C) := by
  have himg := h.image_torusCellInterior hd hc hC
  refine ⟨?_, ?_⟩
  · rw [← himg, source_bondMap hs b]
    exact mem_image_of_mem _ hb.1
  · rw [← himg, target_bondMap hs b]
    exact mem_image_of_mem _ hb.2
theorem precompose_mem_torusCellObservables (s : D.TorusSymmetry)
    (hU : ∀ U ∈ D.torusFields, GridSetup.TorusSymmetry.pullback s U ∈ D.torusFields)
    {C C' : Set D.Torus}
    (hCC : ∀ b ∈ g.torusCellLinks C,
      TorusLatticeSymmetry.bondMap s b ∈ g.torusCellLinks C')
    {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hF : F ∈ g.torusCellObservables C) :
    GridSetup.TorusSymmetry.precompose s F ∈ g.torusCellObservables C' := by
  obtain ⟨f, hf, ⟨c, hc⟩, hFU⟩ := hF
  refine ⟨f ∘ fun u b => u ⟨TorusLatticeSymmetry.bondMap s b.1, hCC b.1 b.2⟩,
    hf.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _), ⟨c, fun u => hc _⟩,
    fun U => ?_⟩
  exact hFU ⟨_, hU U.1 U.2⟩
theorem precompose_image_torusCellObservables {s t : D.TorusSymmetry} {ρ : Equiv.Perm AmbientSpace}
    (h : TorusLift g s.toFun t.toFun ρ) (hbs : MapsLinksToLinks s) (hbt : MapsLinksToLinks t)
    (hUs : ∀ U ∈ D.torusFields, GridSetup.TorusSymmetry.pullback s U ∈ D.torusFields)
    (hUt : ∀ U ∈ D.torusFields, GridSetup.TorusSymmetry.pullback t U ∈ D.torusFields)
    (hd : g.DistToWalls) (hc : TorusCellStructure g) {C : Set D.Torus}
    (hC : C ∈ g.torusCellSet) :
    GridSetup.TorusSymmetry.precompose s '' g.torusCellObservables C =
      g.torusCellObservables (s.toFun '' C) := by
  refine Subset.antisymm ?_ fun F' hF' => ?_
  · rintro _ ⟨F, hF, rfl⟩
    exact precompose_mem_torusCellObservables s hUs
      (fun b hb => bondMap_mem_torusCellLinks h hbs hd hc hC hb) hF
  · have hC' := h.image_mem_torusCellSet hd hC
    have hback : t.toFun '' (s.toFun '' C) = C := by
      rw [← image_comp]
      simp [h.left_inv]
    refine ⟨GridSetup.TorusSymmetry.precompose t F', ?_, ?_⟩
    · have h1 := precompose_mem_torusCellObservables (g := g) t hUt (C := s.toFun '' C)
        (C' := t.toFun '' (s.toFun '' C))
        (fun b hb => bondMap_mem_torusCellLinks h.symm hbt hd hc hC' hb) hF'
      rwa [hback] at h1
    · funext U
      show F' (GridSetup.TorusSymmetry.pullback t (GridSetup.TorusSymmetry.pullback s U)) = F' U
      congr 1
      funext b
      show U (TorusLatticeSymmetry.bondMap s (TorusLatticeSymmetry.bondMap t b)) = U b
      rw [bondMap_bondMap hbs hbt h.right_inv]
end Observables
section Walls
variable {D : GridSetup} {g : ReflectionGrid D}
theorem mem_walls_of_mem_wall {μ : Fin 4} {k : ℤ} {x : AmbientSpace} (h : x ∈ g.wall μ k) :
    x ∈ g.walls :=
  mem_iUnion.2 ⟨μ, mem_iUnion.2 ⟨k, h⟩⟩
theorem mem_walls_of_proj_eq (hn : ∃ n : ℤ, PeriodicLattice.torusSide D.L D.m = n * g.cellSide)
    {x y : AmbientSpace} (hxy : D.proj x = D.proj y) (hy : y ∈ g.walls) : x ∈ g.walls := by
  obtain ⟨n, hn⟩ := hn
  obtain ⟨j, rfl⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hxy
  simp only [ReflectionGrid.walls, mem_iUnion] at hy
  obtain ⟨μ, k, hk⟩ := hy
  have hk' : y μ = g.origin μ + k * g.cellSide := hk
  refine mem_walls_of_mem_wall (μ := μ) (k := k + n * j μ) ?_
  show (y + TestFunctions.latticeTranslate _ j) μ = g.origin μ + ((k + n * j μ : ℤ) : ℝ) * g.cellSide
  simp only [Pi.add_apply, TestFunctions.latticeTranslate, hk', hn]
  push_cast
  ring
theorem image_walls_of_torusWalls (hn : ∃ n : ℤ, PeriodicLattice.torusSide D.L D.m = n * g.cellSide)
    {s t : D.Torus → D.Torus} {ρ : Equiv.Perm AmbientSpace}
    (hcov : ∀ x, s (D.proj x) = D.proj (ρ x)) (hleft : ∀ y, t (s y) = y)
    (hkeep : (fun P => s '' P) '' g.torusWallFamily = g.torusWallFamily) :
    ρ '' g.walls = g.walls := by
  have hinj : Function.Injective s := fun a b e => by rw [← hleft a, e, hleft]
  have hiff : ∀ x, ρ x ∈ g.walls ↔ x ∈ g.walls := by
    intro x
    constructor
    · intro hx
      simp only [ReflectionGrid.walls, mem_iUnion] at hx
      obtain ⟨μ, k, hk⟩ := hx
      have h1 : D.proj (ρ x) ∈ g.torusWall μ k := ⟨_, hk, rfl⟩
      have h2 : g.torusWall μ k ∈ (fun P => s '' P) '' g.torusWallFamily := by
        rw [hkeep]
        exact ⟨(μ, k), rfl⟩
      obtain ⟨_, ⟨⟨μ', k'⟩, rfl⟩, h3⟩ := h2
      have h3' : s '' g.torusWall μ' k' = g.torusWall μ k := h3
      rw [← h3'] at h1
      obtain ⟨_, ⟨y, hy, rfl⟩, hz⟩ := h1
      have h4 : D.proj x = D.proj y := hinj (by rw [hz, hcov x])
      exact mem_walls_of_proj_eq hn h4 (mem_walls_of_mem_wall hy)
    · intro hx
      simp only [ReflectionGrid.walls, mem_iUnion] at hx
      obtain ⟨μ, k, hk⟩ := hx
      have h2 : s '' g.torusWall μ k ∈ g.torusWallFamily := by
        rw [← hkeep]
        exact ⟨_, ⟨(μ, k), rfl⟩, rfl⟩
      obtain ⟨⟨μ', k'⟩, h3⟩ := h2
      have h3' : g.torusWall μ' k' = s '' g.torusWall μ k := h3
      have h1 : D.proj (ρ x) ∈ s '' g.torusWall μ k :=
        ⟨D.proj x, ⟨x, hk, rfl⟩, hcov x⟩
      rw [← h3'] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      exact mem_walls_of_proj_eq hn hyx.symm (mem_walls_of_mem_wall hy)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hiff x).2 hx
  · intro hy
    exact ⟨ρ⁻¹ y, (hiff _).1 (by simpa using hy), by simp⟩
theorem exists_torusLift
    (h₁ : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    (hn : ∃ n : ℤ, PeriodicLattice.torusSide D.L D.m = n * g.cellSide) (s : D.TorusSymmetry)
    (hkeep : (fun P => s.toFun '' P) '' g.torusWallFamily = g.torusWallFamily) :
    ∃ (t : D.TorusSymmetry) (ρ : Equiv.Perm AmbientSpace), TorusLift g s.toFun t.toFun ρ := by
  obtain ⟨⟨R, v, -, hRv⟩, -, t, ⟨ht₁, ht₂⟩, -⟩ := (h₁ (D.mirrors 0)).2 s
  have hε : ∀ μ, ((R.2 μ : ℤ) : ℝ) * ((R.2 μ : ℤ) : ℝ) = 1 := fun μ => by
    rcases Int.units_eq_one_or (R.2 μ) with h | h <;> simp [h]
  let e := signedPermEquiv R.1 (fun μ => ((R.2 μ : ℤ) : ℝ)) hε
  let ρ : Equiv.Perm AmbientSpace :=
    ⟨fun x => e x + v, fun y => e.symm (y - v), fun x => by simp, fun y => by simp⟩
  have hcov : ∀ x, s.toFun (D.proj x) = D.proj (ρ x) := fun x => hRv x
  exact ⟨t, ρ, ⟨R.1, _, hε, v, fun _ => rfl⟩, hcov, ht₁, ht₂,
    image_walls_of_torusWalls hn hcov ht₁ hkeep⟩
theorem pullback_mem_torusFields
    (h₁ : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    (s : D.TorusSymmetry) {U : D.PeriodicLink → Matrices.ComplexMatrix2} (hU : U ∈ D.torusFields) :
    GridSetup.TorusSymmetry.pullback s U ∈ D.torusFields := by
  obtain ⟨-, -, t, -, -, hconf, -⟩ := (h₁ (D.mirrors 0)).2 s
  exact (hconf.1 U hU).1
theorem exists_image_wall {r : Equiv.Perm AmbientSpace} (hr : g.IsProductOfCoordMaps r)
    (μ : Fin 4) (k : ℤ) : ∃ k' : ℤ, r '' g.wall μ k = g.wall μ k' := by
  rcases hr μ with ⟨t, ht⟩ | ⟨j, hj⟩
  · refine ⟨k + 2 * t, Subset.antisymm ?_ fun y hy => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have h1 := ht x
      have hx' : x μ = g.origin μ + k * g.cellSide := hx
      show r x μ = g.origin μ + ((k + 2 * t : ℤ) : ℝ) * g.cellSide
      simp only [ReflectionGrid.coordShift] at h1
      rw [hx'] at h1
      push_cast
      linarith
    · refine ⟨r⁻¹ y, ?_, by simp⟩
      have h1 := ht (r⁻¹ y)
      rw [show r (r⁻¹ y) = y by simp] at h1
      have hy' : y μ = g.origin μ + ((k + 2 * t : ℤ) : ℝ) * g.cellSide := hy
      show (r⁻¹ y) μ = g.origin μ + k * g.cellSide
      simp only [ReflectionGrid.coordShift] at h1
      push_cast at hy'
      linarith
  · refine ⟨2 * j - k, Subset.antisymm ?_ fun y hy => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have h1 := hj x
      have hx' : x μ = g.origin μ + k * g.cellSide := hx
      show r x μ = g.origin μ + ((2 * j - k : ℤ) : ℝ) * g.cellSide
      simp only [ReflectionGrid.coordReflect] at h1
      rw [hx'] at h1
      push_cast
      linarith
    · refine ⟨r⁻¹ y, ?_, by simp⟩
      have h1 := hj (r⁻¹ y)
      rw [show r (r⁻¹ y) = y by simp] at h1
      have hy' : y μ = g.origin μ + ((2 * j - k : ℤ) : ℝ) * g.cellSide := hy
      show (r⁻¹ y) μ = g.origin μ + k * g.cellSide
      simp only [ReflectionGrid.coordReflect] at h1
      push_cast at hy'
      linarith
theorem image_torusWalls_of_mem (hf : g.ReflectionGroupCoordForm) {r : Equiv.Perm AmbientSpace}
    (hr : r ∈ g.reflectionGroup) {s : D.Torus → D.Torus} (hs : D.proj ∘ r = s ∘ D.proj) :
    (fun P => s '' P) '' g.torusWallFamily = g.torusWallFamily := by
  have hmove : ∀ (S : Set AmbientSpace), s '' (D.proj '' S) = D.proj '' (r '' S) := fun S => by
    rw [← image_comp, ← image_comp]
    exact image_congr fun x _ => (congrFun hs x).symm
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨_, ⟨⟨μ, k⟩, rfl⟩, rfl⟩
    obtain ⟨k', hk'⟩ := exists_image_wall (hf.1 r hr) μ k
    refine ⟨(μ, k'), ?_⟩
    show D.proj '' g.wall μ k' = s '' (D.proj '' g.wall μ k)
    rw [hmove, hk']
  · rintro _ ⟨⟨μ, k'⟩, rfl⟩
    obtain ⟨k, hk⟩ := exists_image_wall (hf.1 r⁻¹ (inv_mem hr)) μ k'
    have h1 : r '' g.wall μ k = g.wall μ k' := by
      rw [← hk, ← image_comp]
      simp
    refine ⟨g.torusWall μ k, ⟨(μ, k), rfl⟩, ?_⟩
    show s '' (D.proj '' g.wall μ k) = D.proj '' g.wall μ k'
    rw [hmove, h1]
end Walls
theorem allGridsWallPreservingSymmetries_holds
    (h₁ : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    (h₂ : ChessboardTori.GridBasicProperties.Statement)
    (h₃ : AllGridsReflectionGroupActsOnCells)
    (h₄ : AllGridsTorusGroupActsOnCells)
    (h₅ : AllGridsTorusCellStructure)
    (h₆ : PeriodicLattice.SymmetriesPreserveBondsAndPlaquettes) :
    AllGridsWallPreservingSymmetries := by
  intro D g hg hl
  have hE := h₂ D g
  have hd : g.DistToWalls := hE.2.2.2.2.2.1
  have hf : g.ReflectionGroupCoordForm := hE.2.2.2.1
  have hG := h₃ D g hg
  have hT := h₄ D g hg hl
  have hc := h₅ D g hg hl
  have hn : ∃ n : ℤ, PeriodicLattice.torusSide D.L D.m = n * g.cellSide := by
    obtain ⟨n, -, hn⟩ := hc.1
    refine ⟨n, ?_⟩
    rw [← hn, ReflectionGrid.cellsAcross, div_mul_cancel₀ _ (cellSide_pos g).ne']
  have hbonds : ∀ s : D.TorusSymmetry, MapsLinksToLinks s := fun s =>
    ((h₆ D.toStandingParameters).1 s).1
  refine ⟨fun s hkeep => ?_, fun r' hr' => ?_⟩
  · obtain ⟨t, ρ, h⟩ := exists_torusLift h₁ hn s hkeep
    have hinv := h.invFun_eq
    refine ⟨h.bijOn_torusCellSet hd, fun C hC => ?_, ?_, fun u hu => ?_⟩
    · exact precompose_image_torusCellObservables h (hbonds s) (hbonds t)
        (fun U hU => pullback_mem_torusFields h₁ s hU)
        (fun U hU => pullback_mem_torusFields h₁ t hU) hd hc hC
    · rw [hinv]
      exact h.bijOn_conj
    · rw [hinv]
      exact h.torusSign_conj hG hT hu
  · obtain ⟨r, hr, hrr⟩ := id hr'
    obtain ⟨s, hs⟩ := hT.1 r hr
    have hsr : s.toFun = r' := GridSetup.Descends.unique hs hrr.symm
    refine ⟨s, hsr, ?_⟩
    rw [hsr]
    exact image_torusWalls_of_mem hf hr hrr
end MirrorGridsAllSides.WallPreserving
end
end YangMills.Construction
