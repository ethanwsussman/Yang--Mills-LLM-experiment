import YangMills.Construction.Dirichlet.CubeBumpBoundsProof
import YangMills.Construction.Lattice.GroupAndCellsOfAGridDatum
import YangMills.Construction.Lattice.MapsInducedOnTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GroupAndCells
open Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (meshSize)
open YangMills.Construction.TorusDescent (signAffineGroup signAffine descend IsSignMatrix)
section
variable {L : ℕ} {κ : ℤ}
def HasReflectionForm (d : CellGrid L κ) (g : AmbientSpace → AmbientSpace) (r m : Fin 4 → ℤ) :
    Prop :=
  (∀ μ, r μ = 1 ∨ r μ = -1) ∧
    ∀ x μ, g x μ = d.centre μ + (r μ : ℝ) * (x μ - d.centre μ) + 2 * (m μ : ℝ) * d.cellLength
variable {d : CellGrid L κ}
theorem HasReflectionForm.comp {g h : AmbientSpace → AmbientSpace} {r m r' m' : Fin 4 → ℤ}
    (hg : HasReflectionForm d g r m) (hh : HasReflectionForm d h r' m') :
    HasReflectionForm d (g ∘ h) (r * r') (fun μ => r μ * m' μ + m μ) := by
  refine ⟨fun μ => ?_, fun x μ => ?_⟩
  · rcases hg.1 μ with e | e <;> rcases hh.1 μ with e' | e' <;> simp [e, e']
  · simp only [Function.comp, hg.2, hh.2, Pi.mul_apply]
    push_cast
    ring
variable (d)
theorem hasReflectionForm_faceReflect (μ : Fin 4) (a : ℤ) :
    HasReflectionForm d (d.faceReflect μ a) (Function.update 1 μ (-1)) (Pi.single μ a) := by
  refine ⟨fun ν => ?_, fun x ν => ?_⟩
  · by_cases h : ν = μ
    · subst h
      simp
    · simp [Function.update_of_ne h]
  · by_cases h : ν = μ
    · subst h
      simp [CellGrid.faceReflect, BoxTorus.basisVector]
      ring
    · simp [CellGrid.faceReflect, BoxTorus.basisVector, Function.update_of_ne h,
        Pi.single_eq_of_ne h]
theorem exists_hasReflectionForm {g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace}
    (hg : g ∈ d.reflectionGroup) : ∃ r m, HasReflectionForm d g r m := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨⟨μ, a⟩, rfl⟩ := hg
    exact ⟨_, _, hasReflectionForm_faceReflect d μ a⟩
  | one => exact ⟨1, 0, fun _ => Or.inl rfl, fun x μ => by simp⟩
  | mul g h _ _ hg hh =>
    obtain ⟨r, m, hg⟩ := hg
    obtain ⟨r', m', hh⟩ := hh
    exact ⟨_, _, hg.comp hh⟩
  | inv g _ hg =>
    obtain ⟨r, m, hr, hf⟩ := hg
    refine ⟨r, fun μ => -(r μ * m μ), hr, fun x μ => ?_⟩
    have h := hf (g⁻¹ x) μ
    have hx : g (g⁻¹ x) = x := g.apply_symm_apply x
    rw [hx] at h
    have hrr : (r μ : ℝ) * r μ = 1 := by rcases hr μ with e | e <;> simp [e]
    push_cast
    linear_combination (-(r μ : ℝ)) * h - ((g⁻¹ x) μ - d.centre μ) * hrr
theorem exists_mem_hasReflectionForm_single (μ : Fin 4) (ε n : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ g ∈ d.reflectionGroup, HasReflectionForm d g (Function.update 1 μ ε) (Pi.single μ n) := by
  have hmem : ∀ a : ℤ, d.faceReflectEquiv μ a ∈ d.reflectionGroup := fun a =>
    Subgroup.subset_closure ⟨(μ, a), rfl⟩
  rcases hε with rfl | rfl
  · refine ⟨d.faceReflectEquiv μ n * d.faceReflectEquiv μ 0, mul_mem (hmem n) (hmem 0), ?_⟩
    have h := (hasReflectionForm_faceReflect d μ n).comp (hasReflectionForm_faceReflect d μ 0)
    have e₁ : (Function.update (1 : Fin 4 → ℤ) μ (-1)) * (Function.update (1 : Fin 4 → ℤ) μ (-1)) =
        Function.update (1 : Fin 4 → ℤ) μ 1 := by
      funext ν
      by_cases hν : ν = μ
      · subst hν
        simp
      · simp [Function.update_of_ne hν]
    have e₂ : (fun ν => (Function.update (1 : Fin 4 → ℤ) μ (-1)) ν * (Pi.single μ 0 : Fin 4 → ℤ) ν +
        (Pi.single μ n : Fin 4 → ℤ) ν) = Pi.single μ n := by
      funext ν
      simp
    rw [e₁, e₂] at h
    exact h
  · exact ⟨d.faceReflectEquiv μ n, hmem n, hasReflectionForm_faceReflect d μ n⟩
theorem exists_mem_hasReflectionForm (r m : Fin 4 → ℤ) (hr : ∀ μ, r μ = 1 ∨ r μ = -1) :
    ∃ g ∈ d.reflectionGroup, HasReflectionForm d g r m := by
  obtain ⟨g₀, m₀, f₀⟩ := exists_mem_hasReflectionForm_single d 0 (r 0) (m 0) (hr 0)
  obtain ⟨g₁, m₁, f₁⟩ := exists_mem_hasReflectionForm_single d 1 (r 1) (m 1) (hr 1)
  obtain ⟨g₂, m₂, f₂⟩ := exists_mem_hasReflectionForm_single d 2 (r 2) (m 2) (hr 2)
  obtain ⟨g₃, m₃, f₃⟩ := exists_mem_hasReflectionForm_single d 3 (r 3) (m 3) (hr 3)
  refine ⟨g₀ * g₁ * g₂ * g₃, mul_mem (mul_mem (mul_mem m₀ m₁) m₂) m₃, ?_⟩
  have h := ((f₀.comp f₁).comp f₂).comp f₃
  refine ⟨hr, fun x μ => ?_⟩
  have h' := h.2 x μ
  have hc : (⇑(g₀ * g₁ * g₂ * g₃) : AmbientSpace → AmbientSpace) = ((g₀ ∘ g₁) ∘ g₂) ∘ g₃ := rfl
  rw [hc, h']
  fin_cases μ <;> simp [Function.update]
def lowerCorner (k : Fin 4 → ℤ) (μ : Fin 4) : ℝ := d.centre μ + d.cellLength * (k μ : ℝ)
theorem cellCube_eq_pi (k : Fin 4 → ℤ) :
    d.cellCube k =
      Set.pi univ fun μ => Icc (lowerCorner d k μ) (lowerCorner d k μ + d.cellLength) := by
  ext x
  simp only [CellGrid.cellCube, mem_image, mem_pi, mem_univ, forall_true_left, mem_Icc,
    lowerCorner]
  constructor
  · rintro ⟨y, hy, rfl⟩ μ
    have := hy μ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> linarith [this.1, this.2]
  · intro h
    refine ⟨x - (d.centre + d.cellLength • fun μ => (k μ : ℝ)), fun μ => ?_, by simp⟩
    have := h μ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    constructor <;> linarith [this.1, this.2]
theorem mem_cellCube_iff {k : Fin 4 → ℤ} {x : AmbientSpace} :
    x ∈ d.cellCube k ↔
      ∀ μ, lowerCorner d k μ ≤ x μ ∧ x μ ≤ lowerCorner d k μ + d.cellLength := by
  rw [cellCube_eq_pi]
  simp only [mem_pi, mem_univ, forall_true_left, mem_Icc]
def imageIndex (r m k : Fin 4 → ℤ) (μ : Fin 4) : ℤ :=
  if r μ = 1 then k μ + 2 * m μ else 2 * m μ - 1 - k μ
theorem image_cellCube {g : AmbientSpace → AmbientSpace} (hb : Function.Bijective g)
    {r m : Fin 4 → ℤ} (hf : HasReflectionForm d g r m) (k : Fin 4 → ℤ) :
    g '' d.cellCube k = d.cellCube (imageIndex r m k) := by
  ext y
  obtain ⟨x, rfl⟩ := hb.2 y
  rw [hb.1.mem_set_image, mem_cellCube_iff, mem_cellCube_iff]
  refine forall_congr' fun μ => ?_
  rw [hf.2]
  simp only [lowerCorner, imageIndex]
  rcases hf.1 μ with e | e
  · simp only [e, if_true]
    push_cast
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  · have : ¬ ((-1 : ℤ) = 1) := by norm_num
    simp only [e, this, if_false]
    push_cast
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
theorem cellCube_injective : Function.Injective d.cellCube := by
  have key : ∀ k k' : Fin 4 → ℤ, d.cellCube k = d.cellCube k' → ∀ μ, k' μ ≤ k μ := by
    intro k k' h μ
    have hm : lowerCorner d k ∈ d.cellCube k := by
      rw [mem_cellCube_iff]
      exact fun ν => ⟨le_rfl, by linarith [d.cellLength_pos]⟩
    rw [h, mem_cellCube_iff] at hm
    have h₁ := (hm μ).1
    simp only [lowerCorner] at h₁
    have h₂ : (k' μ : ℝ) ≤ k μ := le_of_mul_le_mul_left (by linarith) d.cellLength_pos
    exact_mod_cast h₂
  intro k k' h
  exact funext fun μ => le_antisymm (key k' k h.symm μ) (key k k' h μ)
theorem reflectionForm_unique {r m r' m' k : Fin 4 → ℤ} (hr : ∀ μ, r μ = 1 ∨ r μ = -1)
    (hr' : ∀ μ, r' μ = 1 ∨ r' μ = -1) (h : imageIndex r m k = imageIndex r' m' k) :
    r = r' ∧ m = m' := by
  have key : ∀ μ, r μ = r' μ ∧ m μ = m' μ := by
    intro μ
    have hμ := congrFun h μ
    simp only [imageIndex] at hμ
    rcases hr μ with e | e <;> rcases hr' μ with e' | e' <;> simp only [e, e'] at hμ ⊢ <;>
      norm_num at hμ ⊢ <;> omega
  exact ⟨funext fun μ => (key μ).1, funext fun μ => (key μ).2⟩
theorem eq_of_hasReflectionForm {g g' : AmbientSpace ≃ᵃ[ℝ] AmbientSpace} {r m : Fin 4 → ℤ}
    (hf : HasReflectionForm d g r m) (hf' : HasReflectionForm d g' r m) : g = g' :=
  AffineEquiv.ext fun x => funext fun μ => by rw [hf.2, hf'.2]
theorem linearSign_eq_prod (g : d.reflectionGroup) {r m : Fin 4 → ℤ}
    (hf : HasReflectionForm d (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) r m) :
    d.linearSign g = ∏ μ, (r μ : ℝ) := by
  have hl : ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).linear : AmbientSpace →ₗ[ℝ] AmbientSpace) =
      Matrix.toLin' (Matrix.diagonal fun μ => (r μ : ℝ)) := by
    apply LinearMap.ext
    intro v
    funext μ
    rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
    have h₁ := congrFun ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).map_vadd (0 : AmbientSpace) v) μ
    simp only [vadd_eq_add, add_zero, Pi.add_apply] at h₁
    rw [hf.2, hf.2] at h₁
    have h₂ : ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).linear : AmbientSpace →ₗ[ℝ] AmbientSpace) v μ =
        (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).linear v μ := rfl
    rw [h₂]
    simp only [Pi.zero_apply] at h₁
    linarith
  rw [CellGrid.linearSign, hl, LinearMap.det_toLin', Matrix.det_diagonal]
theorem exists_cellLength_eq_mul : ∃ t : ℤ, d.cellLength = (t : ℝ) * meshSize L κ := by
  have hL : (L : ℝ) ≠ 0 := by
    have := d.admissible.2
    exact_mod_cast (by omega : L ≠ 0)
  have ha : meshSize L κ ≠ 0 := zpow_ne_zero _ hL
  obtain ⟨z, hz⟩ := d.cellLength_div_meshSize
  exact ⟨z, by rw [← hz]; field_simp⟩
theorem map_mem_latticeSubgroup {g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace} (hg : g ∈ d.reflectionGroup)
    {x : AmbientSpace} (hx : x ∈ InfiniteLattice.latticeSubgroup (meshSize L κ)) :
    g x ∈ InfiniteLattice.latticeSubgroup (meshSize L κ) := by
  obtain ⟨r, m, hr, hf⟩ := exists_hasReflectionForm d hg
  obtain ⟨n, hn⟩ := hx
  obtain ⟨t, ht⟩ := exists_cellLength_eq_mul d
  choose z hz using d.centre_mem
  refine ⟨fun μ => if r μ = 1 then n μ + 2 * m μ * t else 2 * z μ + 1 - n μ + 2 * m μ * t,
    fun μ => ?_⟩
  rw [hf, hn, ht]
  rcases hr μ with e | e
  · simp only [e, if_true]
    push_cast
    ring
  · have : ¬ ((-1 : ℤ) = 1) := by norm_num
    simp only [e, this, if_false, hz]
    push_cast
    ring
theorem prod_eq_neg_one_zpow_sum (k k' : Fin 4 → ℤ) {r m : Fin 4 → ℤ}
    (hr : ∀ μ, r μ = 1 ∨ r μ = -1) (h : imageIndex r m k = k') :
    ∏ μ, (r μ : ℝ) = (-1 : ℝ) ^ ∑ μ, (k' μ - k μ) := by
  have key : ∀ μ, (r μ : ℝ) = (-1 : ℝ) ^ (k' μ - k μ) := by
    intro μ
    have hμ := congrFun h μ
    simp only [imageIndex] at hμ
    rcases hr μ with e | e
    · simp only [e, if_true] at hμ
      have : Even (k' μ - k μ) := ⟨m μ, by omega⟩
      rw [this.neg_one_zpow, e]
      simp
    · have hne : ¬ ((-1 : ℤ) = 1) := by norm_num
      simp only [e, hne, if_false] at hμ
      have : Odd (k' μ - k μ) := ⟨m μ - k μ - 1, by omega⟩
      rw [this.neg_one_zpow, e]
      simp
  have h0 : (-1 : ℝ) ≠ 0 := by norm_num
  simp only [Fin.prod_univ_four, Fin.sum_univ_four, key, zpow_add₀ h0]
theorem reflectionGroupActsOnCubes_holds : ReflectionGroupActsOnCubes d := by
  refine ⟨fun g hg => ⟨?_, ?_⟩, fun k k' => ?_, fun v => ?_⟩
  · refine Subset.antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact map_mem_latticeSubgroup d hg hx
    · exact ⟨g⁻¹ y, map_mem_latticeSubgroup d (inv_mem hg) hy, g.apply_symm_apply y⟩
  · rintro S ⟨k, rfl⟩
    obtain ⟨r, m, hf⟩ := exists_hasReflectionForm d hg
    exact ⟨_, (image_cellCube d g.bijective hf k).symm⟩
  · have hex : ∃ g : d.reflectionGroup, d.MapsCubeTo g k k' := by
      let r : Fin 4 → ℤ := fun μ => if Even (k' μ - k μ) then 1 else -1
      let m : Fin 4 → ℤ := fun μ =>
        if Even (k' μ - k μ) then (k' μ - k μ) / 2 else (k μ + k' μ + 1) / 2
      have hr : ∀ μ, r μ = 1 ∨ r μ = -1 := fun μ => by
        by_cases h : Even (k' μ - k μ) <;> simp [r, h]
      obtain ⟨g, hg, hf⟩ := exists_mem_hasReflectionForm d r m hr
      refine ⟨⟨g, hg⟩, ?_⟩
      show (g : AmbientSpace → AmbientSpace) '' d.cellCube k = d.cellCube k'
      rw [image_cellCube d g.bijective hf k]
      congr 1
      funext μ
      by_cases h : Even (k' μ - k μ)
      · have h' := Int.even_iff.mp h
        simp only [imageIndex, r, m, h, if_true]
        omega
      · have h' := Int.not_even_iff.mp h
        have hne : ¬ ((-1 : ℤ) = 1) := by norm_num
        simp only [imageIndex, r, m, h, if_false, hne]
        omega
    have huniq : ∀ g g' : d.reflectionGroup, d.MapsCubeTo g k k' → d.MapsCubeTo g' k k' →
        g = g' := by
      intro g g' hc hc'
      obtain ⟨r, m, hf⟩ := exists_hasReflectionForm d g.2
      obtain ⟨r', m', hf'⟩ := exists_hasReflectionForm d g'.2
      have e₁ : imageIndex r m k = k' :=
        cellCube_injective d
          ((image_cellCube d (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).bijective hf k).symm.trans hc)
      have e₂ : imageIndex r' m' k = k' :=
        cellCube_injective d
          ((image_cellCube d (g' : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).bijective hf' k).symm.trans hc')
      obtain ⟨rfl, rfl⟩ := reflectionForm_unique hf.1 hf'.1 (e₁.trans e₂.symm)
      exact Subtype.ext (eq_of_hasReflectionForm d hf hf')
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨g, hg⟩ := hex
      exact ⟨g, hg, fun g' hg' => huniq g' g hg' hg⟩
    · exact @Classical.epsilon_spec _ _ hex
    · intro g hc
      obtain ⟨r, m, hf⟩ := exists_hasReflectionForm d g.2
      have e₁ : imageIndex r m k = k' :=
        cellCube_injective d
          ((image_cellCube d (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).bijective hf k).symm.trans hc)
      rw [linearSign_eq_prod d g hf, prod_eq_neg_one_zpow_sum k k' hf.1 e₁]
  · obtain ⟨g, hg, hf⟩ := exists_mem_hasReflectionForm d 1 v fun _ => Or.inl rfl
    refine ⟨g, hg, fun x => ?_⟩
    funext μ
    rw [hf.2]
    simp
    ring
end
section
variable {L : ℕ} {κ : ℤ}
theorem addCircle_coe_eq_coe_iff {p x y : ℝ} :
    (x : AddCircle p) = y ↔ ∃ j : ℤ, x - y = j * p := by apply _root_.YangMills.Construction.Dirichlet.CubeBump.addCircle_coe_eq_iff <;> assumption
variable (d : CellGrid L κ)
theorem projection_eq_iff {x y : AmbientSpace} :
    BoxTorus.projection d.sideLengths x = BoxTorus.projection d.sideLengths y ↔
      ∀ μ, ∃ j : ℤ, x μ - y μ = j * d.sideLengths μ := by
  constructor
  · intro h μ
    exact addCircle_coe_eq_coe_iff.mp (congrFun h μ)
  · intro h
    funext μ
    exact addCircle_coe_eq_coe_iff.mpr (h μ)
theorem sideLengths_pos (μ : Fin 4) : 0 < d.sideLengths μ :=
  mul_pos (by exact_mod_cast d.counts_pos μ) d.cellLength_pos
theorem two_le_counts (μ : Fin 4) : 2 ≤ d.counts μ := by
  obtain ⟨h, hh⟩ := d.counts_even μ
  have := d.counts_pos μ
  omega
theorem eq_signAffine_of_hasReflectionForm {g : AmbientSpace → AmbientSpace} {r m : Fin 4 → ℤ}
    (hf : HasReflectionForm d g r m) :
    g = signAffine (Matrix.diagonal fun μ => (r μ : ℝ))
      (fun μ => d.centre μ - (r μ : ℝ) * d.centre μ + 2 * (m μ : ℝ) * d.cellLength) := by
  funext x μ
  rw [hf.2]
  simp only [signAffine, Pi.add_apply, Matrix.mulVec_diagonal]
  ring
theorem isSignMatrix_of_hasReflectionForm {g : AmbientSpace → AmbientSpace} {r m : Fin 4 → ℤ}
    (hf : HasReflectionForm d g r m) : IsSignMatrix (Matrix.diagonal fun μ => (r μ : ℝ)) :=
  ⟨fun μ => (r μ : ℝ), fun μ => by rcases hf.1 μ with e | e <;> simp [e], rfl⟩
theorem mem_signAffineGroup_of_hasReflectionForm {g : AmbientSpace → AmbientSpace}
    {r m : Fin 4 → ℤ} (hf : HasReflectionForm d g r m) : g ∈ signAffineGroup :=
  ⟨_, _, isSignMatrix_of_hasReflectionForm d hf, eq_signAffine_of_hasReflectionForm d hf⟩
variable {d} in
theorem isInducedMap_unique {gbar gbar' : d.Space → d.Space} {g : AmbientSpace → AmbientSpace}
    (h : d.IsInducedMap gbar g) (h' : d.IsInducedMap gbar' g) : gbar = gbar' := by
  funext p
  obtain ⟨w, rfl⟩ := BoxTorus.projection_surjective d.sideLengths p
  exact (congrFun h w).trans (congrFun h' w).symm
variable {d} in
theorem isInducedMap_comp {gbar hbar : d.Space → d.Space} {g h : AmbientSpace → AmbientSpace}
    (hg : d.IsInducedMap gbar g) (hh : d.IsInducedMap hbar h) :
    d.IsInducedMap (gbar ∘ hbar) (g ∘ h) := by
  funext w
  show gbar (hbar (BoxTorus.projection d.sideLengths w)) =
    BoxTorus.projection d.sideLengths (g (h w))
  rw [show hbar (BoxTorus.projection d.sideLengths w) = BoxTorus.projection d.sideLengths (h w)
    from congrFun hh w]
  exact congrFun hg _
variable {d} in
theorem isInducedMap_image {gbar : d.Space → d.Space} {g : AmbientSpace → AmbientSpace}
    (h : d.IsInducedMap gbar g) (S : Set AmbientSpace) :
    gbar '' BoxTorus.image d.sideLengths S = BoxTorus.image d.sideLengths (g '' S) := by
  rw [BoxTorus.image, BoxTorus.image, ← image_comp, ← image_comp]
  exact congrArg (· '' S) h
theorem exists_isInducedMap (hI : TorusDescent.DescentProperties d)
    {g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace} (hg : g ∈ d.reflectionGroup) :
    ∃ gbar : d.Space → d.Space, d.IsInducedMap gbar g := by
  obtain ⟨r, m, hf⟩ := exists_hasReflectionForm d hg
  exact ⟨_, hI.2.1 _ (mem_signAffineGroup_of_hasReflectionForm d hf)⟩
theorem inducedGroupMaps_properties (hI : TorusDescent.DescentProperties d)
    (hImg : TorusDescent.DescentImageRules d) {gbar : d.Space → d.Space}
    (hb : gbar ∈ d.inducedGroupMaps) :
    BoxTorus.IsDistPreserving gbar ∧ IsHomeomorph gbar ∧
      gbar '' (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) =
        (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) := by
  obtain ⟨g, hg, hi⟩ := hb
  obtain ⟨r, m, hf⟩ := exists_hasReflectionForm d hg
  have hmem := mem_signAffineGroup_of_hasReflectionForm d hf
  have e : gbar = descend d g := isInducedMap_unique hi (hI.2.1 _ hmem)
  refine ⟨e ▸ (hI.2.2.2.2 _ hmem).1, e ▸ (hI.2.2.2.2 _ hmem).2, ?_⟩
  have hs := ((reflectionGroupActsOnCubes_holds d).1 g hg).1
  have ea := eq_signAffine_of_hasReflectionForm d hf
  have h₃ := (hImg (Matrix.diagonal fun μ => (r μ : ℝ))
    (fun μ => d.centre μ - (r μ : ℝ) * d.centre μ + 2 * (m μ : ℝ) * d.cellLength)
    (isSignMatrix_of_hasReflectionForm d hf)).2.2
  rw [← ea] at h₃
  rw [e]
  exact h₃ hs
theorem inducedMapsFormGroup_holds (hI : TorusDescent.DescentProperties d)
    (hImg : TorusDescent.DescentImageRules d) : InducedMapsFormGroup d := by
  refine ⟨fun g hg => ?_, fun gbar hb => ?_, ⟨1, one_mem _, rfl⟩, ?_, ?_⟩
  · obtain ⟨gbar, hi⟩ := exists_isInducedMap d hI hg
    have hp := inducedGroupMaps_properties d hI hImg ⟨g, hg, hi⟩
    exact ⟨gbar, hi, hp.1, hp.2.2⟩
  · have hp := inducedGroupMaps_properties d hI hImg hb
    rw [CellGrid.symmetryOfMap, dif_pos ⟨hp.1, hp.2.2⟩]
  · rintro gbar ⟨g, hg, hi⟩ hbar ⟨h, hh, hj⟩
    exact ⟨g * h, mul_mem hg hh, isInducedMap_comp (g := ⇑g) (h := ⇑h) hi hj⟩
  · rintro gbar ⟨g, hg, hi⟩
    obtain ⟨hbar, hj⟩ := exists_isInducedMap d hI (inv_mem hg)
    refine ⟨hbar, ⟨g⁻¹, inv_mem hg, hj⟩, ?_, ?_⟩
    · have h₁ : d.IsInducedMap (gbar ∘ hbar) (⇑(g * g⁻¹)) :=
        isInducedMap_comp (g := ⇑g) (h := ⇑g⁻¹) hi hj
      rw [mul_inv_cancel] at h₁
      exact isInducedMap_unique h₁ rfl
    · have h₁ : d.IsInducedMap (hbar ∘ gbar) (⇑(g⁻¹ * g)) :=
        isInducedMap_comp (g := ⇑g⁻¹) (h := ⇑g) hj hi
      rw [inv_mul_cancel] at h₁
      exact isInducedMap_unique h₁ rfl
theorem spaceCell_subset_of_indexClass_eq {k k' : Fin 4 → ℤ} (h : d.indexClass k = d.indexClass k') :
    d.spaceCell k ⊆ d.spaceCell k' := by
  have hv : ∀ μ, ∃ v : ℤ, k' μ - k μ = (d.counts μ : ℤ) * v := fun μ =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun h μ)
  choose v hv using hv
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨w + fun μ => (v μ : ℝ) * d.sideLengths μ, ?_, ?_⟩
  · rw [mem_cellCube_iff] at hw ⊢
    intro μ
    have hc : (k' μ : ℝ) = k μ + (d.counts μ : ℝ) * v μ := by
      have := hv μ
      have e : k' μ = k μ + (d.counts μ : ℤ) * v μ := by omega
      rw [e]
      push_cast
      ring
    have hμ := hw μ
    simp only [lowerCorner, Pi.add_apply, CellGrid.sideLengths, hc] at hμ ⊢
    constructor <;> nlinarith [hμ.1, hμ.2]
  · exact (projection_eq_iff d).mpr fun μ => ⟨v μ, by simp⟩
theorem indexClass_eq_of_spaceCell_eq {k k' : Fin 4 → ℤ} (h : d.spaceCell k = d.spaceCell k') :
    d.indexClass k = d.indexClass k' := by
  have hl := d.cellLength_pos
  have hm : (fun μ => lowerCorner d k μ + d.cellLength / 2) ∈ d.cellCube k := by
    rw [mem_cellCube_iff]
    exact fun μ => ⟨by linarith, by linarith⟩
  have hp : BoxTorus.projection d.sideLengths (fun μ => lowerCorner d k μ + d.cellLength / 2) ∈
      d.spaceCell k' := by
    rw [← h]
    exact ⟨_, hm, rfl⟩
  obtain ⟨w, hw, e⟩ := hp
  rw [mem_cellCube_iff] at hw
  funext μ
  obtain ⟨j, hj⟩ := (projection_eq_iff d).mp e μ
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ⟨j, ?_⟩
  have hμ := hw μ
  have hq : (((k μ + (d.counts μ : ℤ) * j - k' μ : ℤ) : ℝ)) * d.cellLength ≤ d.cellLength / 2 ∧
      -(d.cellLength / 2) ≤ (((k μ + (d.counts μ : ℤ) * j - k' μ : ℤ) : ℝ)) * d.cellLength := by
    simp only [lowerCorner, CellGrid.sideLengths] at hμ hj
    push_cast
    constructor <;> nlinarith [hμ.1, hμ.2]
  have h₁ : ((k μ + (d.counts μ : ℤ) * j - k' μ : ℤ) : ℝ) < 1 :=
    lt_of_mul_lt_mul_right (by linarith [hq.1]) hl.le
  have h₂ : (-1 : ℝ) < ((k μ + (d.counts μ : ℤ) * j - k' μ : ℤ) : ℝ) :=
    lt_of_mul_lt_mul_right (by linarith [hq.2]) hl.le
  have h₃ : k μ + (d.counts μ : ℤ) * j - k' μ < 1 := by exact_mod_cast h₁
  have h₄ : -1 < k μ + (d.counts μ : ℤ) * j - k' μ := by exact_mod_cast h₂
  omega
theorem spaceCell_eq_iff {k k' : Fin 4 → ℤ} :
    d.spaceCell k = d.spaceCell k' ↔ d.indexClass k = d.indexClass k' :=
  ⟨indexClass_eq_of_spaceCell_eq d, fun h =>
    Subset.antisymm (spaceCell_subset_of_indexClass_eq d h)
      (spaceCell_subset_of_indexClass_eq d h.symm)⟩
theorem indexClass_cast (k : d.CellIndex) : d.indexClass (fun μ => ((k μ).cast : ℤ)) = k := by
  funext μ
  have : NeZero (d.counts μ) := ⟨(d.counts_pos μ).ne'⟩
  exact ZMod.intCast_zmod_cast (k μ)
theorem cellAt_indexClass (k : Fin 4 → ℤ) : d.cellAt (d.indexClass k) = d.spaceCell k :=
  (spaceCell_eq_iff d).mpr (indexClass_cast d _)
theorem cellAt_eq_of_indexClass {k : d.CellIndex} {k' : Fin 4 → ℤ} (h : d.indexClass k' = k) :
    d.cellAt k = d.spaceCell k' := by
  rw [← h, cellAt_indexClass]
theorem cellAt_injective : Function.Injective d.cellAt := by
  intro k k' h
  have := indexClass_eq_of_spaceCell_eq d h
  rwa [indexClass_cast, indexClass_cast] at this
theorem spaceCells_eq_range : d.spaceCells = range d.cellAt := by
  ext c
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨d.indexClass k, cellAt_indexClass d k⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, rfl⟩
theorem spaceCellsIndexed_holds : SpaceCellsIndexed d := by
  refine ⟨fun k k' => spaceCell_eq_iff d, fun k => (cellAt_indexClass d k).symm,
    spaceCells_eq_range d, ?_⟩
  rw [spaceCells_eq_range, ← image_univ, ncard_image_of_injective _ (cellAt_injective d),
    Set.ncard_univ, Nat.card_pi]
  simp [CellGrid.numCells, Nat.card_zmod]
theorem eq_of_mapsCell {gbar gbar' : d.Space → d.Space} (hb : gbar ∈ d.inducedGroupMaps)
    (hb' : gbar' ∈ d.inducedGroupMaps) {k k' : Fin 4 → ℤ}
    (h : gbar '' d.spaceCell k = d.spaceCell k') (h' : gbar' '' d.spaceCell k = d.spaceCell k') :
    gbar = gbar' := by
  obtain ⟨g, hg, hi⟩ := hb
  obtain ⟨g', hg', hi'⟩ := hb'
  obtain ⟨r, m, hf⟩ := exists_hasReflectionForm d hg
  obtain ⟨r', m', hf'⟩ := exists_hasReflectionForm d hg'
  have e₁ : d.spaceCell (imageIndex r m k) = d.spaceCell k' := by
    rw [← h]
    simp only [CellGrid.spaceCell]
    rw [isInducedMap_image hi, image_cellCube d g.bijective hf]
  have e₂ : d.spaceCell (imageIndex r' m' k) = d.spaceCell k' := by
    rw [← h']
    simp only [CellGrid.spaceCell]
    rw [isInducedMap_image hi', image_cellCube d g'.bijective hf']
  have hc := indexClass_eq_of_spaceCell_eq d (e₁.trans e₂.symm)
  have hv : ∀ μ, ∃ v : ℤ, imageIndex r' m' k μ - imageIndex r m k μ = (d.counts μ : ℤ) * v :=
    fun μ => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun hc μ)
  choose v hv using hv
  choose t ht using d.counts_even
  have hidx : imageIndex r (fun μ => m μ + (t μ : ℤ) * v μ) k = imageIndex r' m' k := by
    funext μ
    have h₁ := hv μ
    have h₂ : (d.counts μ : ℤ) * v μ = 2 * ((t μ : ℤ) * v μ) := by
      rw [ht μ]
      push_cast
      ring
    have h₃ : imageIndex r (fun μ => m μ + (t μ : ℤ) * v μ) k μ =
        imageIndex r m k μ + 2 * ((t μ : ℤ) * v μ) := by
      simp only [imageIndex]
      split_ifs <;> omega
    omega
  obtain ⟨rfl, hm⟩ := reflectionForm_unique hf.1 hf'.1 hidx
  have hpi : ∀ x, BoxTorus.projection d.sideLengths (g x) =
      BoxTorus.projection d.sideLengths (g' x) := fun x =>
    (projection_eq_iff d).mpr fun μ => ⟨-v μ, by
      rw [hf.2, hf'.2, ← hm]
      simp only [CellGrid.sideLengths, ht μ]
      push_cast
      ring⟩
  refine isInducedMap_unique hi ?_
  funext w
  exact (congrFun hi' w).trans (hpi w).symm
theorem simplyTransitiveOnCells_holds (hI : TorusDescent.DescentProperties d) :
    SimplyTransitiveOnCells d := by
  have hg := reflectionGroupActsOnCubes_holds d
  refine ⟨?_, ?_⟩
  · rintro gbar ⟨g, hg, hi⟩ _ ⟨k, rfl⟩
    obtain ⟨r, m, hf⟩ := exists_hasReflectionForm d hg
    refine ⟨imageIndex r m k, ?_⟩
    rw [CellGrid.spaceCell, CellGrid.spaceCell, isInducedMap_image hi,
      image_cellCube d g.bijective hf]
  · rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩
    obtain ⟨⟨g, hc, -⟩, -, -⟩ := hg.2.1 k k'
    obtain ⟨gbar, hi⟩ := exists_isInducedMap d hI g.2
    have hex : d.MapsCellTo gbar (d.spaceCell k) (d.spaceCell k') := by
      refine ⟨⟨g, g.2, hi⟩, ?_⟩
      rw [CellGrid.spaceCell, isInducedMap_image hi, hc]
      rfl
    refine ⟨⟨gbar, hex, fun gbar' h' => eq_of_mapsCell d h'.1 hex.1 h'.2 hex.2⟩, ?_⟩
    exact @Classical.epsilon_spec _
      (fun gb => d.MapsCellTo gb (d.spaceCell k) (d.spaceCell k')) ⟨gbar, hex⟩
theorem reflectionSigns_unique {g g' : AmbientSpace → AmbientSpace} {r m r' m' : Fin 4 → ℤ}
    (hf : HasReflectionForm d g r m) (hf' : HasReflectionForm d g' r' m')
    (h : ∀ x, BoxTorus.projection d.sideLengths (g x) = BoxTorus.projection d.sideLengths (g' x)) :
    r = r' := by
  funext μ
  obtain ⟨j₀, hj₀⟩ := (projection_eq_iff d).mp (h d.centre) μ
  obtain ⟨j₁, hj₁⟩ := (projection_eq_iff d).mp (h fun ν => d.centre ν + d.sideLengths ν / 4) μ
  rw [hf.2, hf'.2] at hj₀ hj₁
  have hs := (sideLengths_pos d μ).ne'
  by_contra hne
  have key : ((2 * (j₁ - j₀) : ℤ) : ℝ) = 1 ∨ ((2 * (j₁ - j₀) : ℤ) : ℝ) = -1 := by
    rcases hf.1 μ with e | e <;> rcases hf'.1 μ with e' | e' <;> simp only [e, e'] at hj₀ hj₁ hne
    · exact (hne trivial).elim
    · left
      push_cast at hj₀ hj₁ ⊢
      apply mul_right_cancel₀ hs
      linarith
    · right
      push_cast at hj₀ hj₁ ⊢
      apply mul_right_cancel₀ hs
      linarith
    · exact (hne trivial).elim
  rcases key with k | k
  · have : 2 * (j₁ - j₀) = 1 := by exact_mod_cast k
    omega
  · have : 2 * (j₁ - j₀) = -1 := by exact_mod_cast k
    omega
theorem linearSign_eq_of_isInducedMap {g g' : d.reflectionGroup} {gbar : d.Space → d.Space}
    (h : d.IsInducedMap gbar g) (h' : d.IsInducedMap gbar g') :
    d.linearSign g = d.linearSign g' := by
  obtain ⟨r, m, hf⟩ := exists_hasReflectionForm d g.2
  obtain ⟨r', m', hf'⟩ := exists_hasReflectionForm d g'.2
  have e : r = r' := reflectionSigns_unique d hf hf' fun x =>
    (congrFun h x).symm.trans (congrFun h' x)
  rw [linearSign_eq_prod d g hf, linearSign_eq_prod d g' hf', e]
theorem inducedSign_eq {g : d.reflectionGroup} {gbar : d.Space → d.Space}
    (h : d.IsInducedMap gbar g) : d.inducedSign gbar = d.linearSign g := by
  have hex : ∃ s, d.IsInducedSign gbar s := ⟨d.linearSign g, g, h, rfl⟩
  obtain ⟨g', hi', e⟩ := Classical.epsilon_spec hex
  exact e.symm.trans (linearSign_eq_of_isInducedMap d hi' h)
theorem linearSign_mul (g h : d.reflectionGroup) :
    d.linearSign (g * h) = d.linearSign g * d.linearSign h := by
  obtain ⟨r, m, hf⟩ := exists_hasReflectionForm d g.2
  obtain ⟨r', m', hf'⟩ := exists_hasReflectionForm d h.2
  have hc : HasReflectionForm d ((g * h : d.reflectionGroup) : AmbientSpace ≃ᵃ[ℝ] AmbientSpace)
    _ _ := hf.comp hf'
  rw [linearSign_eq_prod d _ hc, linearSign_eq_prod d g hf, linearSign_eq_prod d h hf',
    ← Finset.prod_mul_distrib]
  simp
theorem signDescends_holds : SignDescends d := by
  refine ⟨fun g g' gbar h h' => linearSign_eq_of_isInducedMap d h h',
    fun g gbar h => inducedSign_eq d h, ?_, ?_⟩
  · rintro gbar ⟨g, hg, hi⟩
    rw [inducedSign_eq d (g := ⟨g, hg⟩) hi]
    exact d.linearSign_eq_one_or_neg_one _
  · rintro gbar ⟨g, hg, hi⟩ hbar ⟨h, hh, hj⟩
    have hc : d.IsInducedMap (gbar ∘ hbar)
        ((⟨g, hg⟩ * ⟨h, hh⟩ : d.reflectionGroup) : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) :=
      isInducedMap_comp (g := ⇑g) (h := ⇑h) hi hj
    rw [inducedSign_eq d hc, inducedSign_eq d (g := ⟨g, hg⟩) hi, inducedSign_eq d (g := ⟨h, hh⟩) hj,
      linearSign_mul]
end
section
variable {L : ℕ} {κ : ℤ} (d : CellGrid L κ)
theorem faceReflect_eq_coordReflection (μ : Fin 4) (a : ℤ) :
    d.faceReflect μ a = TorusDescent.coordReflection μ (d.faceLevel μ a) := by
  funext x
  have e : x μ - d.centre μ - a * d.cellLength = x μ - d.faceLevel μ a := by
    simp only [CellGrid.faceLevel]
    ring
  simp only [CellGrid.faceReflect, TorusDescent.coordReflection, e]
theorem exists_faceLevel_eq (μ : Fin 4) (a : ℤ) :
    ∃ z : ℤ, d.faceLevel μ a = meshSize L κ * ((z : ℝ) + 1 / 2) := by
  obtain ⟨t, ht⟩ := exists_cellLength_eq_mul d
  obtain ⟨z, hz⟩ := d.centre_mem μ
  refine ⟨z + a * t, ?_⟩
  simp only [CellGrid.faceLevel, hz, ht]
  push_cast
  ring
theorem exists_faceLevel_add_half_eq (μ : Fin 4) (a : ℤ) :
    ∃ z : ℤ, d.faceLevel μ a + 1 / 2 * d.sideLengths μ = meshSize L κ * ((z : ℝ) + 1 / 2) := by
  obtain ⟨t, ht⟩ := exists_cellLength_eq_mul d
  obtain ⟨z, hz⟩ := exists_faceLevel_eq d μ a
  obtain ⟨h, hh⟩ := d.counts_even μ
  refine ⟨z + h * t, ?_⟩
  rw [hz]
  simp only [CellGrid.sideLengths, hh, ht]
  push_cast
  ring
theorem faceReflectionFixedSet_holds (hI : TorusDescent.DescentProperties d) (μ : Fin 4) (a : ℤ)
    (hmem : TorusDescent.coordReflection μ (d.faceLevel μ a) ∈ signAffineGroup)
    (hInv : TorusDescent.ReflectionInvolutive d μ (d.faceLevel μ a))
    (hComp : TorusDescent.HalvesAreComponents d μ (d.faceLevel μ a))
    {θ : d.Space → d.Space} (hθ : d.IsInducedMap θ (d.faceReflect μ a)) :
    FaceReflectionFixedSet d μ a θ := by
  have e : θ = descend d (TorusDescent.coordReflection μ (d.faceLevel μ a)) := by
    rw [faceReflect_eq_coordReflection] at hθ
    exact isInducedMap_unique hθ (hI.2.1 _ hmem)
  subst e
  obtain ⟨z₁, hz₁⟩ := exists_faceLevel_eq d μ a
  obtain ⟨z₂, hz₂⟩ := exists_faceLevel_add_half_eq d μ a
  exact ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩, hInv.2, ⟨_, ⟨μ, _, ⟨z₁, hz₁⟩, rfl⟩, rfl⟩,
    ⟨_, ⟨μ, _, ⟨z₂, hz₂⟩, rfl⟩, rfl⟩, hComp.1, hComp.2.1, hComp.2.2.2.2.1, hComp.2.2.2.2.2⟩
theorem interior_cellCube (k : Fin 4 → ℤ) :
    interior (d.cellCube k) =
      Set.pi univ fun μ => Ioo (lowerCorner d k μ) (lowerCorner d k μ + d.cellLength) := by
  rw [cellCube_eq_pi, interior_pi_set finite_univ]
  simp only [interior_Icc]
theorem mem_interior_cellCube_iff {k : Fin 4 → ℤ} {x : AmbientSpace} :
    x ∈ interior (d.cellCube k) ↔
      ∀ μ, lowerCorner d k μ < x μ ∧ x μ < lowerCorner d k μ + d.cellLength := by
  rw [interior_cellCube]
  simp only [mem_pi, mem_univ, forall_true_left, mem_Ioo]
theorem not_multiple_mem_Icc {j : ℤ} {n : ℕ} (hn : 2 ≤ n) {l t : ℝ} (hl : 0 < l) (ht : 0 < t)
    (htl : t < l) : ¬ (t ≤ (j : ℝ) * ((n : ℝ) * l) ∧ (j : ℝ) * ((n : ℝ) * l) ≤ l + t) := by
  rintro ⟨h₁, h₂⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rcases le_or_gt j 0 with hj | hj
  · have hj' : (j : ℝ) ≤ 0 := by exact_mod_cast hj
    have := mul_nonpos_of_nonpos_of_nonneg hj' (mul_nonneg (by linarith : (0 : ℝ) ≤ n) hl.le)
    linarith
  · have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hnl : 2 * l ≤ (n : ℝ) * l := mul_le_mul_of_nonneg_right hn' hl.le
    have : (n : ℝ) * l ≤ (j : ℝ) * ((n : ℝ) * l) :=
      le_mul_of_one_le_left (by linarith) hj'
    linarith
theorem interior_spaceCell (hQ : TorusDescent.ProjectionContinuousOpen d) (k : Fin 4 → ℤ) :
    interior (d.spaceCell k) = BoxTorus.image d.sideLengths (interior (d.cellCube k)) := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨y, hy, rfl⟩ := interior_subset hp
    refine ⟨y, ?_, rfl⟩
    rw [mem_interior_cellCube_iff]
    rw [mem_cellCube_iff] at hy
    by_contra hn
    push Not at hn
    obtain ⟨ν, hν⟩ := hn
    have hl := d.cellLength_pos
    let f : ℝ → AmbientSpace := fun t => y + t • BoxTorus.basisVector ν
    have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
    have hO : IsOpen (f ⁻¹' (BoxTorus.projection d.sideLengths ⁻¹' interior (d.spaceCell k))) :=
      (isOpen_interior.preimage hQ.1).preimage hf
    have h0 : (0 : ℝ) ∈ f ⁻¹' (BoxTorus.projection d.sideLengths ⁻¹' interior (d.spaceCell k)) := by
      have e : f 0 = y := by simp [f]
      rw [mem_preimage, e]
      exact hp
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO 0 h0
    have hmem : ∀ s : ℝ, |s| < ε → ∃ j : ℤ,
        lowerCorner d k ν ≤ y ν + s + (j : ℝ) * d.sideLengths ν ∧
        y ν + s + (j : ℝ) * d.sideLengths ν ≤ lowerCorner d k ν + d.cellLength := by
      intro s hs
      have h₁ : s ∈ f ⁻¹' (BoxTorus.projection d.sideLengths ⁻¹' interior (d.spaceCell k)) :=
        hball (by simpa [Real.dist_eq] using hs)
      obtain ⟨w, hw, e⟩ := interior_subset (mem_preimage.mp (mem_preimage.mp h₁))
      obtain ⟨j, hj⟩ := (projection_eq_iff d).mp e ν
      rw [mem_cellCube_iff] at hw
      have hfs : f s ν = y ν + s := by simp [f, BoxTorus.basisVector]
      rw [hfs] at hj
      refine ⟨j, ?_⟩
      have e' : y ν + s + (j : ℝ) * d.sideLengths ν = w ν := by linarith
      rw [e']
      exact hw ν
    have ht0 : 0 < min (ε / 2) (d.cellLength / 2) := lt_min (by linarith) (by linarith)
    have htε : min (ε / 2) (d.cellLength / 2) < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htl : min (ε / 2) (d.cellLength / 2) < d.cellLength :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith)
    generalize min (ε / 2) (d.cellLength / 2) = t at ht0 htε htl
    have hside : d.sideLengths ν = (d.counts ν : ℝ) * d.cellLength := rfl
    by_cases hc : lowerCorner d k ν < y ν
    · have hy₂ : y ν = lowerCorner d k ν + d.cellLength := le_antisymm (hy ν).2 (hν hc)
      obtain ⟨j, h₁, h₂⟩ := hmem t (by rwa [abs_of_pos ht0])
      refine not_multiple_mem_Icc (j := -j) (two_le_counts d ν) hl ht0 htl ⟨?_, ?_⟩
      all_goals
        rw [hside] at h₁ h₂
        push_cast
        linarith
    · have hy₂ : y ν = lowerCorner d k ν := le_antisymm (not_lt.mp hc) (hy ν).1
      obtain ⟨j, h₁, h₂⟩ := hmem (-t) (by rwa [abs_neg, abs_of_pos ht0])
      refine not_multiple_mem_Icc (j := j) (two_le_counts d ν) hl ht0 htl ⟨?_, ?_⟩
      all_goals
        rw [hside] at h₁ h₂
        linarith
  · exact interior_maximal (image_mono interior_subset) (hQ.2 _ isOpen_interior)
theorem indexClass_update (k : d.CellIndex) (μ : Fin 4) (z : ℤ)
    (hz : (z : ZMod (d.counts μ)) = k μ) :
    d.indexClass (Function.update (fun ν => ((k ν).cast : ℤ)) μ z) = k := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simpa [CellGrid.indexClass] using hz
  · simp [CellGrid.indexClass, Function.update_of_ne h]
theorem indexClass_imageIndex_faceReflect (μ : Fin 4) (a : ℤ) (k : d.CellIndex) :
    d.indexClass (imageIndex (Function.update (1 : Fin 4 → ℤ) μ (-1)) (Pi.single μ a)
      (fun ν => ((k ν).cast : ℤ))) = d.reflectIndex μ (a : ZMod (d.counts μ)) k := by
  funext ν
  have hk := congrFun (indexClass_cast d k) ν
  simp only [CellGrid.indexClass] at hk
  by_cases h : ν = μ
  · subst h
    have hne : ¬ ((-1 : ℤ) = 1) := by norm_num
    simp only [CellGrid.indexClass, imageIndex, Function.update_self, hne, if_false,
      CellGrid.reflectIndex, Pi.single_eq_same]
    push_cast
    rfl
  · simp only [CellGrid.indexClass, imageIndex, Function.update_of_ne h, Pi.one_apply, if_true,
      CellGrid.reflectIndex, Pi.single_eq_of_ne h]
    simp
theorem faceReflectionCells_holds (hQ : TorusDescent.ProjectionContinuousOpen d)
    (μ : Fin 4) (a : ℤ) {θ : d.Space → d.Space} (hθ : d.IsInducedMap θ (d.faceReflect μ a)) :
    FaceReflectionCells d μ a θ := by
  have hl := d.cellLength_pos
  obtain ⟨t, ht⟩ := d.counts_even μ
  have hnr : (d.counts μ : ℝ) = (t : ℝ) + t := by rw [ht]; push_cast; ring
  have hside : d.sideLengths μ = (d.counts μ : ℝ) * d.cellLength := rfl
  have hpos : 0 < d.counts μ := d.counts_pos μ
  refine ⟨fun k => ?_, interior_spaceCell d hQ, fun k => ?_, fun k => ⟨?_, ?_⟩⟩
  · have hr := hasReflectionForm_faceReflect d μ a
    have hb : Function.Bijective (d.faceReflect μ a) := (d.faceReflectEquiv μ a).bijective
    rw [cellAt_eq_of_indexClass d (indexClass_imageIndex_faceReflect d μ a k)]
    show θ '' BoxTorus.image d.sideLengths (d.cellCube _) =
      BoxTorus.image d.sideLengths (d.cellCube _)
    rw [isInducedMap_image hθ, image_cellCube d hb hr]
  · rw [cellAt_indexClass, interior_spaceCell d hQ]
  · rintro ⟨j, hj, hk⟩ p hp
    have hc := indexClass_update d k μ ((a : ℤ) + (j : ℤ)) (by rw [hk]; push_cast; rfl)
    rw [cellAt_eq_of_indexClass d hc, interior_spaceCell d hQ] at hp
    obtain ⟨w, hw, rfl⟩ := hp
    have hμ := (mem_interior_cellCube_iff d).mp hw μ
    simp only [lowerCorner, Function.update_self] at hμ
    push_cast at hμ
    have hjt : (j : ℝ) + 1 ≤ t := by
      have : j + 1 ≤ t := by omega
      exact_mod_cast this
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    refine ⟨w, ⟨?_, ?_⟩, rfl⟩
    · simp only [CellGrid.faceLevel]
      nlinarith [hμ.1, mul_nonneg hl.le hj0]
    · simp only [CellGrid.faceLevel]
      rw [hside, hnr]
      nlinarith [hμ.2, mul_le_mul_of_nonneg_left hjt hl.le]
  · intro hn p hp
    have : NeZero (d.counts μ) := ⟨hpos.ne'⟩
    have hj : (((k μ - (a : ZMod (d.counts μ))).val : ℕ) : ZMod (d.counts μ)) =
        k μ - (a : ZMod (d.counts μ)) := ZMod.natCast_zmod_val _
    have hjlt := ZMod.val_lt (k μ - (a : ZMod (d.counts μ)))
    generalize (k μ - (a : ZMod (d.counts μ))).val = j at hj hjlt
    have hge : t ≤ j := by
      by_contra hlt
      refine hn ⟨j, by omega, ?_⟩
      rw [hj]
      ring
    have hc := indexClass_update d k μ ((a : ℤ) + (j : ℤ) - (d.counts μ : ℤ)) (by
      push_cast
      rw [hj]
      simp)
    rw [cellAt_eq_of_indexClass d hc, interior_spaceCell d hQ] at hp
    obtain ⟨w, hw, rfl⟩ := hp
    have hμ := (mem_interior_cellCube_iff d).mp hw μ
    simp only [lowerCorner, Function.update_self] at hμ
    push_cast at hμ
    have h₁ : (t : ℝ) ≤ j := by exact_mod_cast hge
    have h₂ : (j : ℝ) + 1 ≤ d.counts μ := by
      have : j + 1 ≤ d.counts μ := hjlt
      exact_mod_cast this
    refine ⟨w, ⟨?_, ?_⟩, rfl⟩
    · simp only [CellGrid.faceLevel]
      rw [hside]
      rw [hnr] at hμ ⊢
      nlinarith [hμ.1, mul_le_mul_of_nonneg_left h₁ hl.le]
    · simp only [CellGrid.faceLevel]
      nlinarith [hμ.2, mul_le_mul_of_nonneg_left h₂ hl.le]
end
section
variable {L : ℕ} {κ : ℤ} {d : CellGrid L κ}
theorem edgeImage_compose (hL : GridLattice.EdgesByDistance d)
    (g h : d.GridSymmetry) (b : d.DirectedEdge) :
    (g.compose h).edgeImage b = g.edgeImage (h.edgeImage b) := by
  obtain ⟨e₁, e₂⟩ := (g.compose h).edgeImage_endpoints hL b
  obtain ⟨e₃, e₄⟩ := g.edgeImage_endpoints hL (h.edgeImage b)
  obtain ⟨e₅, e₆⟩ := h.edgeImage_endpoints hL b
  refine BoxTorus.DirectedEdge.ext ?_ ?_
  · rw [e₁, e₃, e₅]
    rfl
  · rw [e₂, e₄, e₆]
    rfl
theorem pullback_comp (hL : GridLattice.EdgesByDistance d)
    (hC : GridLattice.GaugeConfigsAsEdgeMaps d) (g h : d.GridSymmetry) :
    h.pullback ∘ g.pullback = (g.compose h).pullback := by
  funext U b
  show BoxTorus.edgeVariable (g.pullback U) (h.edgeImage b.1) =
    BoxTorus.edgeVariable U ((g.compose h).edgeImage b.1)
  rw [g.edgeVariable_pullback hC, edgeImage_compose hL]
theorem pullback_of_toFun_eq_id (hL : GridLattice.EdgesByDistance d)
    (k : d.GridSymmetry) (hk : k.toFun = id) (U : d.GaugeConfig) :
    k.pullback U = U := by
  funext b
  have hb : k.edgeImage b.1 = b.1 := by
    obtain ⟨e₁, e₂⟩ := k.edgeImage_endpoints hL b.1
    refine BoxTorus.DirectedEdge.ext ?_ ?_
    · rw [e₁]
      exact Subtype.ext (congrFun hk _)
    · rw [e₂]
      exact Subtype.ext (congrFun hk _)
  show BoxTorus.edgeVariable U (k.edgeImage b.1) = U b
  rw [hb, BoxTorus.edgeVariable, dif_pos b.2]
theorem actOnObservables_mem_localAlgebra (hL : GridLattice.EdgesByDistance d)
    (g : d.GridSymmetry) (O O' : TopologicalSpace.Opens d.Space)
    (hO : ∀ x ∈ O, g.toFun x ∈ O') {F : d.GaugeConfig → ℂ}
    (hF : F ∈ d.localAlgebra O) : g.actOnObservables F ∈ d.localAlgebra O' := by
  classical
  obtain ⟨f, hf, hb, hFf⟩ := hF
  have hE : ∀ b : ↥(BoxTorus.forwardPart (d.edgesWithin O)),
      (g.edgeImage b.1.1).source.1 ∈ O' ∧ (g.edgeImage b.1.1).target.1 ∈ O' := by
    rintro ⟨b, hb⟩
    obtain ⟨e₁, e₂⟩ := g.edgeImage_endpoints hL b.1
    have hends : (b.1.source : d.Space) ∈ O ∧ (b.1.target : d.Space) ∈ O := by
      rcases hb with hb | hb
      · exact hb
      · exact ⟨hb.2, hb.1⟩
    show ((g.edgeImage b.1).source : d.Space) ∈ O' ∧ ((g.edgeImage b.1).target : d.Space) ∈ O'
    rw [e₁, e₂]
    exact ⟨hO _ hends.1, hO _ hends.2⟩
  let Φ : (↥(BoxTorus.forwardPart (d.edgesWithin O')) →
        Conventions.StandingParameters.gaugeGroup) →
      ↥(BoxTorus.forwardPart (d.edgesWithin O)) → Conventions.StandingParameters.gaugeGroup :=
    fun u b =>
      if h : (g.edgeImage b.1.1).IsForward then
        u ⟨⟨g.edgeImage b.1.1, h⟩, Or.inl (hE b)⟩
      else
        (u ⟨⟨(g.edgeImage b.1.1).flip, BoxTorus.DirectedEdge.flip_isForward h⟩,
          Or.inr (hE b)⟩)⁻¹
  have hΦ : Measurable Φ := by
    refine measurable_pi_iff.mpr fun b => ?_
    by_cases h : (g.edgeImage b.1.1).IsForward
    · simp only [Φ, dif_pos h]
      exact measurable_pi_apply _
    · simp only [Φ, dif_neg h]
      exact continuous_inv.measurable.comp (measurable_pi_apply _)
  refine ⟨f ∘ Φ, hf.comp hΦ, ?_, fun U => ?_⟩
  · obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun u => hC _⟩
  · show F (g.pullback U) = f (Φ fun b => U b.1)
    rw [hFf]
    congr 1
theorem observableAction_holds (hL : GridLattice.EdgesByDistance d)
    (hC : GridLattice.GaugeConfigsAsEdgeMaps d)
    (hinv : ∀ gbar ∈ d.inducedGroupMaps, ∃ hbar ∈ d.inducedGroupMaps,
      gbar ∘ hbar = id ∧ hbar ∘ gbar = id)
    (hiso : ∀ gbar ∈ d.inducedGroupMaps, BoxTorus.IsDistPreserving gbar ∧
      gbar '' (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) =
        (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) ∧ IsOpenMap gbar) :
    ObservableAction d := by
  refine ⟨fun g h => ⟨pullback_comp hL hC g h, fun X F => ?_⟩, fun g => ⟨?_, ?_, ?_⟩,
    fun g hg c c' hc => ?_⟩
  · show F ∘ (h.pullback ∘ g.pullback) = F ∘ (g.compose h).pullback
    rw [pullback_comp hL hC]
  · intro α β F F'
    rfl
  · intro F F'
    rfl
  · intro F
    rfl
  · obtain ⟨hbar, hh, e₁, e₂⟩ := hinv _ hg
    obtain ⟨i₁, i₂, i₃⟩ := hiso _ hh
    let h : d.GridSymmetry := ⟨hbar, i₁, i₂⟩
    have hgo : IsOpenMap g.toFun := (hiso _ hg).2.2
    have hcc : hbar '' c'.1 = c.1 := by
      rw [hc, ← image_comp, e₂, image_id]
    refine Subset.antisymm ?_ fun F' hF' => ?_
    · rintro _ ⟨F, hF, rfl⟩
      refine actOnObservables_mem_localAlgebra hL g _ _ (fun x hx => ?_) hF
      have := hgo.image_interior_subset c.1 ⟨x, hx, rfl⟩
      rw [← hc] at this
      exact this
    · refine ⟨h.actOnObservables F', actOnObservables_mem_localAlgebra hL h _ _
        (fun x hx => ?_) hF', ?_⟩
      · have := i₃.image_interior_subset c'.1 ⟨x, hx, rfl⟩
        rw [hcc] at this
        exact this
      · have hk : (g.compose h).toFun = id := e₁
        show (F' ∘ h.pullback) ∘ g.pullback = F'
        rw [Function.comp_assoc, pullback_comp hL hC]
        funext U
        show F' ((g.compose h).pullback U) = F' U
        rw [pullback_of_toFun_eq_id hL _ hk]
end
theorem allHold (hM : TorusDescent.DescentTheorem) (hL : GridLattice.Properties) : AllHold := by
  intro L κ d
  obtain ⟨hQ, -, hI, hImg, hR⟩ := hM L κ d
  obtain ⟨-, -, hC, hD, -⟩ := hL L κ d
  have hG := inducedMapsFormGroup_holds d hI hImg
  refine ⟨reflectionGroupActsOnCubes_holds d, hG, spaceCellsIndexed_holds d,
    simplyTransitiveOnCells_holds d hI, signDescends_holds d,
    fun μ a θ hθ => ⟨?_, faceReflectionCells_holds d hQ μ a hθ⟩, ?_⟩
  · obtain ⟨hmem, -, hInv, hComp, -⟩ := hR μ (d.faceLevel μ a)
    exact faceReflectionFixedSet_holds d hI μ a hmem hInv hComp hθ
  · refine observableAction_holds hD hC (fun gbar hb => ?_) fun gbar hb => ?_
    · obtain ⟨hbar, hh, e₁, e₂⟩ := hG.2.2.2.2 gbar hb
      exact ⟨hbar, hh, e₁, e₂⟩
    · have hp := inducedGroupMaps_properties d hI hImg hb
      exact ⟨hp.1, hp.2.2, hp.2.1.isOpenMap⟩
end YangMills.Construction.GroupAndCells
end
