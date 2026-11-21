import YangMills.Construction.InfiniteLattice.IsometriesOfALatticePlaquettesAndGenerators
import YangMills.Construction.InfiniteLattice.MovesOfBondsSupportsAndPlaquettes
import YangMills.Construction.ReflectionPositivity.UnitNormalReflectionAndLatticeMirrors
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open Mirrors (axialHyperplane)
open PeriodicLattice (coordVec)
namespace SymmetriesFacesAndGenerators
theorem permuteCoords_apply (σ : Equiv.Perm (Fin 4)) (x : AmbientSpace) (ν : Fin 4) :
    permuteCoords σ x ν = x (σ.symm ν) := rfl
theorem permuteCoords_mem_hyperoctahedral (σ : Equiv.Perm (Fin 4)) :
    permuteCoords σ ∈ hyperoctahedralLinearGroup :=
  (mem_hyperoctahedralLinearGroup_iff _).mpr ⟨σ.symm, 1, fun x μ => by
    simp [permuteCoords_apply]⟩
theorem signedPermutationGroup_eq : signedPermutationGroup = hyperoctahedralLinearGroup := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun w hw => ?_
  · rintro _ (⟨σ, rfl⟩ | h)
    · exact permuteCoords_mem_hyperoctahedral σ
    · exact signFlipGroup_le_hyperoctahedralLinearGroup h
  · obtain ⟨π, s, h⟩ := (mem_hyperoctahedralLinearGroup_iff w).mp hw
    have hw' : w = signFlip s * permuteCoords π.symm :=
      LinearEquiv.ext fun x => funext fun μ => h x μ
    rw [hw']
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Or.inr ⟨s, rfl⟩))
      (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
theorem exists_mem_signedPermutationGroup_iff_bijOn (f : AmbientSpace →ₗ[ℝ] AmbientSpace) :
    (∃ w ∈ signedPermutationGroup, ⇑w = ⇑f) ↔ BijOn f signedUnitVectors signedUnitVectors := by
  rw [signedPermutationGroup_eq]
  constructor
  · rintro ⟨w, hw, hwf⟩
    have hw' : w '' signedUnitVectors = signedUnitVectors := hw
    have h : BijOn w signedUnitVectors (w '' signedUnitVectors) := w.injective.injOn.bijOn_image
    rw [hw', hwf] at h
    exact h
  · exact exists_mem_hyperoctahedralLinearGroup f
def linearEquivToPerm : (AmbientSpace ≃ₗ[ℝ] AmbientSpace) →* Equiv.Perm AmbientSpace where
  toFun w := w.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl
theorem linearEquivToPerm_apply (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) (x : AmbientSpace) :
    linearEquivToPerm w x = w x := rfl
def diagonalHyperplane (μ lam : Fin 4) (h : μ < lam) : Mirrors.ReflectingHyperplane :=
  ⟨coordVec μ - coordVec lam, Or.inr ⟨μ, lam, h, Or.inr rfl⟩, 0⟩
theorem axialHyperplane_isLatticeSymmetric
    (hF : Mirrors.UnitNormalAndLattice.Statement)
    {a : ℝ} (ha : 0 < a) (μ : Fin 4) : (axialHyperplane μ 0).IsLatticeSymmetric a :=
  ⟨ha, ((hF (axialHyperplane μ 0) a ha).2.1 μ rfl).mpr ⟨0, by simp [axialHyperplane]⟩⟩
theorem diagonalHyperplane_isLatticeSymmetric
    (hF : Mirrors.UnitNormalAndLattice.Statement)
    {a : ℝ} (ha : 0 < a) {μ lam : Fin 4} (h : μ < lam) :
    (diagonalHyperplane μ lam h).IsLatticeSymmetric a :=
  ⟨ha, ((hF (diagonalHyperplane μ lam h) a ha).2.2.1 μ lam h (Or.inr rfl)).1.mpr
    ⟨0, by simp [diagonalHyperplane]⟩⟩
theorem reflect_axialHyperplane (μ : Fin 4) (x : AmbientSpace) (κ : Fin 4) :
    (axialHyperplane μ 0).reflect x κ = if κ = μ then -x κ else x κ := by
  by_cases hκ : κ = μ
  · subst hκ
    simp [Mirrors.ReflectingHyperplane.reflect, axialHyperplane, coordVec, single_dotProduct]
    ring
  · simp [Mirrors.ReflectingHyperplane.reflect, axialHyperplane, coordVec, single_dotProduct, hκ]
theorem reflect_diagonalHyperplane {μ lam : Fin 4} (h : μ < lam) (x : AmbientSpace) :
    (diagonalHyperplane μ lam h).reflect x = fun κ => x (Equiv.swap μ lam κ) := by
  have hne : μ ≠ lam := h.ne
  have hdot : ∀ y : AmbientSpace, (coordVec μ - coordVec lam) ⬝ᵥ y = y μ - y lam := by
    intro y
    simp [coordVec, sub_dotProduct, single_dotProduct]
  have hnn : (coordVec μ - coordVec lam : AmbientSpace) ⬝ᵥ
      (coordVec μ - coordVec lam) = 2 := by
    rw [hdot]
    simp [coordVec, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
    norm_num
  have hform : (diagonalHyperplane μ lam h).reflect x =
      x - (x μ - x lam) • (coordVec μ - coordVec lam) := by
    change x - (2 * ((coordVec μ - coordVec lam) ⬝ᵥ x - 0) /
      ((coordVec μ - coordVec lam) ⬝ᵥ
        (coordVec μ - coordVec lam))) •
      (coordVec μ - coordVec lam) = _
    rw [hnn, hdot, sub_zero, mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)]
  rw [hform]
  funext κ
  by_cases h1 : κ = μ
  · subst h1
    simp [coordVec, Pi.single_eq_of_ne hne]
  · by_cases h2 : κ = lam
    · subst h2
      simp [coordVec, Pi.single_eq_of_ne hne.symm]
    · simp [coordVec, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2,
        Equiv.swap_apply_of_ne_of_ne h1 h2]
theorem permuteCoords_one : permuteCoords 1 = 1 :=
  LinearEquiv.ext fun _ => rfl
theorem permuteCoords_mul (σ τ : Equiv.Perm (Fin 4)) :
    permuteCoords (σ * τ) = permuteCoords σ * permuteCoords τ :=
  LinearEquiv.ext fun _ => rfl
theorem mem_closure_of_reflect {a : ℝ} (M : Mirrors.ReflectingHyperplane)
    (hM : M.IsLatticeSymmetric a)
    (g : Equiv.Perm AmbientSpace) (hg : ⇑g = M.reflect) :
    g ∈ Subgroup.closure (shiftsAndMirrorReflections a) :=
  Subgroup.subset_closure (Or.inr ⟨M, hM, hg⟩)
theorem linearEquivToPerm_permuteCoords_mem
    (hF : Mirrors.UnitNormalAndLattice.Statement)
    {a : ℝ} (ha : 0 < a) (σ : Equiv.Perm (Fin 4)) :
    linearEquivToPerm (permuteCoords σ) ∈ Subgroup.closure (shiftsAndMirrorReflections a) := by
  have hswap : ∀ μ lam : Fin 4, μ < lam →
      linearEquivToPerm (permuteCoords (Equiv.swap μ lam)) ∈
        Subgroup.closure (shiftsAndMirrorReflections a) := by
    intro μ lam h
    refine mem_closure_of_reflect _ (diagonalHyperplane_isLatticeSymmetric hF ha h) _ ?_
    funext x
    rw [reflect_diagonalHyperplane]
    funext κ
    rw [linearEquivToPerm_apply, permuteCoords_apply, Equiv.symm_swap]
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    rw [permuteCoords_one, map_one]
    exact Subgroup.one_mem _
  | swap_mul f x y hxy hf =>
    rw [permuteCoords_mul, map_mul]
    refine Subgroup.mul_mem _ ?_ hf
    rcases lt_or_gt_of_ne hxy with h | h
    · exact hswap x y h
    · rw [Equiv.swap_comm]
      exact hswap y x h
def signFlipHom : (Fin 4 → ℤˣ) →* Equiv.Perm AmbientSpace where
  toFun ε := linearEquivToPerm (signFlip ε)
  map_one' := by
    refine Equiv.ext fun x => funext fun μ => ?_
    change (((1 : Fin 4 → ℤˣ) μ : ℤ) : ℝ) * x μ = x μ
    simp
  map_mul' ε η := by
    refine Equiv.ext fun x => funext fun μ => ?_
    change ((((ε * η) μ : ℤˣ) : ℤ) : ℝ) * x μ = ((ε μ : ℤ) : ℝ) * (((η μ : ℤ) : ℝ) * x μ)
    simp [mul_assoc]
theorem linearEquivToPerm_signFlip_mem
    (hF : Mirrors.UnitNormalAndLattice.Statement)
    {a : ℝ} (ha : 0 < a) (ε : Fin 4 → ℤˣ) :
    linearEquivToPerm (signFlip ε) ∈ Subgroup.closure (shiftsAndMirrorReflections a) := by
  have hsingle : ∀ μ, signFlipHom (Pi.mulSingle μ (ε μ)) ∈
      Subgroup.closure (shiftsAndMirrorReflections a) := by
    intro μ
    rcases Int.units_eq_one_or (ε μ) with h | h
    · rw [h, Pi.mulSingle_one, map_one]
      exact Subgroup.one_mem _
    · rw [h]
      refine mem_closure_of_reflect _ (axialHyperplane_isLatticeSymmetric hF ha μ) _ ?_
      funext x κ
      rw [reflect_axialHyperplane]
      change (((Pi.mulSingle μ (-1 : ℤˣ) : Fin 4 → ℤˣ) κ : ℤ) : ℝ) * x κ = _
      by_cases hκ : κ = μ
      · subst hκ
        simp
      · simp [hκ]
  change signFlipHom ε ∈ _
  rw [← Finset.univ_prod_mulSingle ε, Fin.prod_univ_four, map_mul, map_mul, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsingle 0) (hsingle 1))
    (hsingle 2)) (hsingle 3)
theorem linearEquivToPerm_mem_of_mem_hyperoctahedral
    (hF : Mirrors.UnitNormalAndLattice.Statement)
    {a : ℝ} (ha : 0 < a) {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hyperoctahedralLinearGroup) :
    linearEquivToPerm w ∈ Subgroup.closure (shiftsAndMirrorReflections a) := by
  rw [← signedPermutationGroup_eq] at hw
  have hle : signedPermutationGroup ≤
      (Subgroup.closure (shiftsAndMirrorReflections a)).comap linearEquivToPerm := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (⟨σ, rfl⟩ | ⟨ε, rfl⟩)
    · exact linearEquivToPerm_permuteCoords_mem hF ha σ
    · exact linearEquivToPerm_signFlip_mem hF ha ε
  exact hle hw
def reflectSymmetry (hF : Mirrors.UnitNormalAndLattice.Statement)
    {a : ℝ} (ha : 0 < a) (M : Mirrors.ReflectingHyperplane) (hM : M.IsLatticeSymmetric a) :
    LatticeSymmetry a where
  toFun := M.reflect
  preservesDist x y := by
    have hnorm : ∀ z : AmbientSpace, ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 4))‖ =
        TorusMetric.euclidNormVec z := fun z => by
      simp [EuclideanSpace.norm_eq, TorusMetric.euclidNormVec]
    have h := (hF M a ha).2.2.2.1.2.2.1.dist_eq (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    rw [dist_eq_norm, dist_eq_norm] at h
    simp only [Mirrors.ReflectingHyperplane.reflectL2] at h
    rw [← WithLp.toLp_sub, ← WithLp.toLp_sub, hnorm, hnorm] at h
    exact h
  image_eq := hM.2
end SymmetriesFacesAndGenerators
open SymmetriesFacesAndGenerators in
theorem SymmetriesFacesAndGenerators.claim_of_transport
    (hMoves : GibbsAtFixedSpacing.SymmetriesTransportLinksSupportsAndPlaquettes)
    (hMirrors : Mirrors.UnitNormalAndLattice.Statement) :
    SymmetriesFacesAndGenerators.Claim := by
  intro a ha
  obtain ⟨⟨hEq, G, hG⟩, -, hPlaq⟩ := hMoves a ha
  refine ⟨exists_mem_signedPermutationGroup_iff_bijOn, signedPermutationGroup_eq, fun s => ?_,
    fun r p => ?_, fun r => ?_, fun g hg => ?_⟩
  · rw [← hEq]
    rfl
  · obtain ⟨h1, -, -, h4, h5, -⟩ := hPlaq r
    exact ⟨(h1 p).1, (h1 p).2, h5 p, h4 p⟩
  · have hr : r.toFun ∈ affineHyperoctahedralMaps a := by
      rw [← hEq]
      exact ⟨r, rfl⟩
    obtain ⟨w, hw, v, hv⟩ := hr
    refine ⟨Equiv.addRight (v : AmbientSpace) * linearEquivToPerm w, Subgroup.mul_mem _ ?_
      (linearEquivToPerm_mem_of_mem_hyperoctahedral hMirrors ha hw), ?_⟩
    · exact Subgroup.subset_closure (Or.inl ⟨v, rfl⟩)
    · rw [hv]
      rfl
  · have hle : Subgroup.closure (shiftsAndMirrorReflections a) ≤ G := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro g (⟨v, hv⟩ | ⟨M, hM, hgM⟩)
      · obtain ⟨g', hg', he⟩ := (hG _).mp ⟨shift v, rfl⟩
        have : g' = g := Equiv.coe_fn_injective (he.trans hv.symm)
        exact this ▸ hg'
      · obtain ⟨g', hg', he⟩ := (hG _).mp ⟨reflectSymmetry hMirrors ha M hM, rfl⟩
        have : g' = g := Equiv.coe_fn_injective (he.trans hgM.symm)
        exact this ▸ hg'
    exact (hG _).mpr ⟨g, hle hg, rfl⟩
end YangMills.Construction.InfiniteLattice
