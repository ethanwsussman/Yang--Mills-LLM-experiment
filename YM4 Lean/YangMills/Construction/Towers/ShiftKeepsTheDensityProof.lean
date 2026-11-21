import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.Towers.ShiftKeepsTheDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.TranslationProof
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.PeriodicOperators
section Permutation
variable {J : Type}
theorem memℓp_comp_perm (e : J ≃ J) (f : lp (fun _ : J => ℂ) 2) :
    Memℓp (fun i => f (e i)) 2 := by
  have h := (memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp f)
  exact (memℓp_gen_iff (p := 2) (by norm_num)).2 (e.summable_iff.2 h)
theorem norm_sq_eq_tsum_sq (f : lp (fun _ : J => ℂ) 2) : ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
  simpa using h
def permL2 (e : J ≃ J) : lp (fun _ : J => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : J => ℂ) 2 where
  toFun f := ⟨fun i => f (e.symm i), memℓp_comp_perm e.symm f⟩
  invFun f := ⟨fun i => f (e i), memℓp_comp_perm e f⟩
  map_add' f g := by
    ext i
    rfl
  map_smul' c f := by
    ext i
    simp
  left_inv f := by
    ext i
    simp
  right_inv f := by
    ext i
    simp
  norm_map' f := by
    have h : ‖(⟨fun i => f (e.symm i), memℓp_comp_perm e.symm f⟩ :
        lp (fun _ : J => ℂ) 2)‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [norm_sq_eq_tsum_sq, norm_sq_eq_tsum_sq]
      exact e.symm.tsum_eq fun i => ‖f i‖ ^ 2
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
theorem permL2_apply (e : J ≃ J) (f : lp (fun _ : J => ℂ) 2) (i : J) :
    permL2 e f i = f (e.symm i) := rfl
theorem permL2_symm_apply (e : J ≃ J) (f : lp (fun _ : J => ℂ) 2) (i : J) :
    (permL2 e).symm f i = f (e i) := rfl
theorem lpShift_eq_permL2 (e : J ≃ J) : lpShift e = permL2 e := by
  funext f
  have hex : ∃ g : lp (fun _ : J => ℂ) 2, ∀ ι, g (e ι) = f ι :=
    ⟨permL2 e f, fun ι => by simp [permL2_apply]⟩
  have hs := Classical.epsilon_spec hex
  ext i
  have h1 := hs (e.symm i)
  rw [Equiv.apply_symm_apply] at h1
  exact h1.trans (permL2_apply e f i).symm
open Classical in
theorem permL2_symm_basisVec (e : J ≃ J) (ι : J) :
    (permL2 e).symm (basisVec (e ι)) = basisVec ι := by
  ext j
  rw [permL2_symm_apply]
  simp only [basisVec, lp.single_apply, Pi.single_apply, e.injective.eq_iff]
end Permutation
variable {L : ℕ}
theorem preservesTraceDensity_of_perm {σ : Type} (pos : Fin 3 × σ → InfiniteLattice.AmbientSpace)
    (e : Fin 3 × σ ≃ Fin 3 × σ) (v : Fin 4 → ℤ)
    (hpos : ∀ (ι : Fin 3 × σ) (x : FullSpace.Vertex L 0 0),
      pos (e ι) = (vertexAdd v x : InfiniteLattice.AmbientSpace) ↔
        pos ι = (x : InfiniteLattice.AmbientSpace)) :
    PreservesTraceDensity (L := L) pos (lpShift e) v := by
  rw [lpShift_eq_permL2]
  have hinv : Function.invFun (permL2 e) = (permL2 e).symm := by
    funext f
    apply (permL2 e).injective
    rw [Function.invFun_eq ((permL2 e).surjective f)]
    simp
  refine ⟨⟨⟨map_add (permL2 e), map_smul (permL2 e)⟩, (permL2 e).bijective,
    (permL2 e).norm_map⟩, fun S => ?_⟩
  rw [hinv]
  let B : L2Field σ →L[ℂ] L2Field σ :=
    ((permL2 e).toContinuousLinearEquiv : _ →L[ℂ] _).comp
      (S.comp ((permL2 e).symm.toContinuousLinearEquiv : _ →L[ℂ] _))
  have hB : ∀ ψ, B ψ = permL2 e (S ((permL2 e).symm ψ)) := fun ψ => rfl
  refine ⟨⟨B, hB⟩, fun x => ?_⟩
  have hop : toBddOp (fun f => permL2 e (S ((permL2 e).symm f))) = B := by
    have hex : ∃ B' : L2Field σ →L[ℂ] L2Field σ,
        ∀ ψ, B' ψ = permL2 e (S ((permL2 e).symm ψ)) := ⟨B, hB⟩
    have hs := Classical.epsilon_spec hex
    ext1 ψ
    rw [hB]
    exact hs ψ
  rw [hop]
  unfold traceAt
  have himg : {ι | pos ι = (vertexAdd v x : InfiniteLattice.AmbientSpace)} =
      e '' {ι | pos ι = (x : InfiniteLattice.AmbientSpace)} := by
    ext ι
    constructor
    · intro h
      refine ⟨e.symm ι, ?_, e.apply_symm_apply ι⟩
      refine (hpos (e.symm ι) x).1 ?_
      rw [e.apply_symm_apply]
      exact h
    · rintro ⟨ι', h, rfl⟩
      exact (hpos ι' x).2 h
  rw [himg, finsum_mem_image e.injective.injOn]
  refine finsum_mem_congr rfl fun ι _ => ?_
  change permL2 e (S ((permL2 e).symm (basisVec (e ι)))) (e ι) = S (basisVec ι) ι
  rw [permL2_symm_basisVec, permL2_apply, e.symm_apply_apply]
def translatePerm {I : PeriodicData} (hI : IsPeriodic I) (v : Fin 4 → ℤ) : I.Carrier ≃ I.Carrier where
  toFun := I.translate v
  invFun := I.translate (-v)
  left_inv ι := by
    rw [← hI.translate_add, add_neg_cancel, hI.translate_zero]
  right_inv ι := by
    rw [← hI.translate_add, neg_add_cancel, hI.translate_zero]
theorem vertexAdd_coe (hs : IsPeriodic (colourVertices L 0 0)) (v : Fin 4 → ℤ)
    (x : FullSpace.Vertex L 0 0) :
    (vertexAdd v x : InfiniteLattice.AmbientSpace) = (x : InfiniteLattice.AmbientSpace) + castVec v :=
  hs.pos_translate v ((0 : Fin 3), x)
theorem eq_iff_of_add_right_eq {a b c d w : InfiniteLattice.AmbientSpace} (h₁ : a = b + w)
    (h₂ : c = d + w) : a = c ↔ b = d := by
  rw [h₁, h₂]
  exact add_left_inj w
theorem translationPreservesTrace_holds (h : TowerIndexSets.Claim) : TranslationPreservesTrace := by
  intro L hL v
  obtain ⟨hs, hb, -⟩ := h L hL 0 0 le_rfl
  exact ⟨preservesTraceDensity_of_perm (L := L) (vertexPos L)
      (translatePerm hs v : VertexIndex L ≃ VertexIndex L) v fun ι x =>
        eq_iff_of_add_right_eq (hs.pos_translate v ι) (vertexAdd_coe hs v x),
    preservesTraceDensity_of_perm (L := L) (edgePos L)
      (translatePerm hb v : EdgeIndex L ≃ EdgeIndex L) v fun ι x =>
        eq_iff_of_add_right_eq (hb.pos_translate v ι) (vertexAdd_coe hs v x)⟩
end YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.TranslationProof
end
