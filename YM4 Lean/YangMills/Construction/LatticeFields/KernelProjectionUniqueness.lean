import YangMills.Construction.LatticeFields.DirichletBlockOpsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.KernelProjectionUnique
variable {d : ℕ}
theorem exists_sub_orthogonal_of_posDef {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) (hsymm : ∀ u v, B u v = B v u)
    (hpos : ∀ u, B u u = 0 → u = 0) (W : Submodule ℝ V) (f : V) :
    ∃ g ∈ W, ∀ h ∈ W, B (f - g) h = 0 := by
  have hrefl : B.IsRefl := fun u v h => by rw [hsymm]; exact h
  have hnd : (B.restrict W).Nondegenerate := by
    constructor
    · intro u hu
      exact Subtype.ext (hpos _ (hu u))
    · intro u hu
      exact Subtype.ext (hpos _ (hu u))
  have hc := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd
  have hf : f ∈ W ⊔ B.orthogonal W := by
    rw [hc.sup_eq_top]
    trivial
  obtain ⟨g, hg, k, hk, rfl⟩ := Submodule.mem_sup.mp hf
  refine ⟨g, hg, fun h hh => ?_⟩
  have hk' : g + k - g = k := by abel
  rw [hk', hsymm]
  exact LinearMap.BilinForm.mem_orthogonal_iff.mp hk h hh
theorem finite_latticeSite_torus (N : ℕ) [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
section Inner
variable {N : ℕ} {κ : LatticeShape d} {I : Type}
theorem fieldInner_eq_sum [Fintype (LatticeSite N κ)] [Fintype I] (F G : LatticeField N κ I) :
    fieldInner F G = ∑ p : LatticeSite N κ × I, latticeSpacing N ^ d * F p.1 p.2 * G p.1 p.2 :=
  tsum_fintype _
theorem fieldInner_comm [Fintype (LatticeSite N κ)] [Fintype I] (F G : LatticeField N κ I) :
    fieldInner F G = fieldInner G F := by apply _root_.YangMills.Construction.LatticeFields.WeightConjGreen.fieldInner_comm_aux <;> assumption
theorem fieldInner_add_left [Fintype (LatticeSite N κ)] [Fintype I] (F F' G : LatticeField N κ I) :
    fieldInner (F + F') G = fieldInner F G + fieldInner F' G := by
  simp only [fieldInner_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by simp only [Pi.add_apply]; ring
theorem fieldInner_smul_left [Fintype (LatticeSite N κ)] [Fintype I] (c : ℝ)
    (F G : LatticeField N κ I) :
    fieldInner (c • F) G = c * fieldInner F G := by apply _root_.YangMills.Construction.LatticeFields.DirichletBlockOpsProof.fieldInner_smul_left <;> assumption
theorem eq_zero_of_fieldInner_self [NeZero N] [Fintype (LatticeSite N κ)] [Fintype I]
    (F : LatticeField N κ I) (h : fieldInner F F = 0) : F = 0 := by apply _root_.YangMills.Construction.LatticeFields.DirichletBlockOpsProof.eq_zero_of_fieldInner_self_eq_zero <;> assumption
end Inner
section Linear
variable {N : ℕ} {κ : LatticeShape d}
theorem tensorLaplacian_add (F G : ScalarField N κ) :
    tensorLaplacian (F + G) = tensorLaplacian F + tensorLaplacian G := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.tensorLaplacian_add <;> assumption
theorem tensorLaplacian_smul (c : ℝ) (F : ScalarField N κ) :
    tensorLaplacian (c • F) = c • tensorLaplacian F := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.tensorLaplacian_smul <;> assumption
theorem siteBlockAvg_add [Finite (LatticeSite N κ)] (f g : ScalarField N κ) :
    siteBlockAvg (f + g) = siteBlockAvg f + siteBlockAvg g := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.siteBlockAvg_add <;> assumption
theorem siteBlockAvg_smul [Finite (LatticeSite N κ)] (c : ℝ) (f : ScalarField N κ) :
    siteBlockAvg (c • f) = c • siteBlockAvg f := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.siteBlockAvg_smul <;> assumption
end Linear
theorem claim_holds : Claim := by
  intro d N _ ℓ hℓ f
  have := finite_latticeSite_torus N ℓ hℓ
  let _ : Fintype (LatticeSite N (LatticeShape.torus ℓ hℓ)) := Fintype.ofFinite _
  let W : Submodule ℝ (ScalarField N (LatticeShape.torus ℓ hℓ)) :=
    { carrier := laplacianImageKer N ℓ hℓ
      add_mem' := by
        rintro _ _ ⟨l, hl, rfl⟩ ⟨l', hl', rfl⟩
        refine ⟨l + l', ?_, tensorLaplacian_add l l'⟩
        change siteBlockAvg (l + l') = 0
        rw [siteBlockAvg_add, show siteBlockAvg l = 0 from hl,
          show siteBlockAvg l' = 0 from hl', add_zero]
      zero_mem' := ⟨0, by
        change siteBlockAvg 0 = 0
        simpa using siteBlockAvg_smul (0 : ℝ) (0 : ScalarField N (LatticeShape.torus ℓ hℓ)), by
        simpa using tensorLaplacian_smul (0 : ℝ) (0 : ScalarField N (LatticeShape.torus ℓ hℓ))⟩
      smul_mem' := by
        rintro c _ ⟨l, hl, rfl⟩
        refine ⟨c • l, ?_, tensorLaplacian_smul c l⟩
        change siteBlockAvg (c • l) = 0
        rw [siteBlockAvg_smul, show siteBlockAvg l = 0 from hl, smul_zero] }
  let B : LinearMap.BilinForm ℝ (ScalarField N (LatticeShape.torus ℓ hℓ)) :=
    LinearMap.mk₂ ℝ fieldInner fieldInner_add_left
      (fun c F G => by rw [fieldInner_smul_left]; rfl)
      (fun F G G' => by
        rw [fieldInner_comm, fieldInner_add_left, fieldInner_comm G, fieldInner_comm G'])
      (fun c F G => by
        rw [fieldInner_comm, fieldInner_smul_left, fieldInner_comm]; rfl)
  have hB : ∀ u v, B u v = fieldInner u v := fun _ _ => rfl
  have hex : ∃ g, IsOrthProj (laplacianImageKer N ℓ hℓ) f g := by
    obtain ⟨g, hg, h⟩ := exists_sub_orthogonal_of_posDef B (fun u v => fieldInner_comm u v)
      (fun u hu => eq_zero_of_fieldInner_self u hu) W f
    exact ⟨g, hg, h⟩
  have hspec : IsOrthProj (laplacianImageKer N ℓ hℓ) f (kerLaplacianProj f) :=
    Classical.epsilon_spec hex
  refine ⟨hspec, fun g hg => ?_⟩
  have hu : g - kerLaplacianProj f ∈ W := W.sub_mem hg.1 hspec.1
  have h1 : B (f - g) (g - kerLaplacianProj f) = 0 := hg.2 _ hu
  have h2 : B (f - kerLaplacianProj f) (g - kerLaplacianProj f) = 0 := hspec.2 _ hu
  have e : g - kerLaplacianProj f = (f - kerLaplacianProj f) - (f - g) := by abel
  have h3 : B (g - kerLaplacianProj f) (g - kerLaplacianProj f) = 0 := by
    have h4 : B ((f - kerLaplacianProj f) - (f - g)) (g - kerLaplacianProj f) = 0 := by
      rw [LinearMap.map_sub₂, h1, h2, sub_zero]
    rwa [← e] at h4
  exact sub_eq_zero.mp (eq_zero_of_fieldInner_self _ ((hB _ _).symm.trans h3))
end YangMills.Construction.LatticeFields.KernelProjectionUnique
