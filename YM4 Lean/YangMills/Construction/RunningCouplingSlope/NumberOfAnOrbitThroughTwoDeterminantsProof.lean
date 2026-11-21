import YangMills.Construction.RunningCouplingSlope.ChangeOfGaugeInAGaussianNumber
import YangMills.Construction.RunningCouplingSlope.NumberOfAnOrbitThroughTwoDeterminants
import YangMills.Construction.Towers.TheSaddleDeterminantProof
import Mathlib
set_option autoImplicit false
open Matrix Module
noncomputable section
namespace YangMills.Construction.LinearConstraint.BorderedDeterminant
section Blocks
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
private theorem abs_det_saddleMatrix (X : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (M : Matrix κ (ι ⊕ κ) ℝ)
    (hM : ∀ f i, M f (Sum.inl i) = 0) (hN : IsUnit M.toCols₂.det) :
    |(fromBlocks X Mᵀ M 0).det| = |X.toBlocks₁₁.det| * M.toCols₂.det ^ 2 := by apply _root_.YangMills.Construction.GaussianConstraint.SaddleDeterminant.abs_det_saddleMatrix <;> assumption
end Blocks
section Spaces
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
private theorem exists_orthonormalBasis_sum_adapted {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (K : Submodule ℝ E) (bK : OrthonormalBasis ι ℝ K)
    (bP : OrthonormalBasis κ ℝ Kᗮ) :
    ∃ v : OrthonormalBasis (ι ⊕ κ) ℝ E,
      (∀ i, v (Sum.inl i) = bK i) ∧ ∀ j, v (Sum.inr j) = bP j := by apply _root_.YangMills.Construction.GaussianConstraint.SaddleDeterminant.exists_orthonormalBasis_sum_orthogonal <;> assumption
private theorem det_saddlePointOperator_eq {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (v : OrthonormalBasis α ℝ E) (w : OrthonormalBasis β ℝ F) (X : E →ₗ[ℝ] E)
    (M : E →ₗ[ℝ] F) :
    LinearMap.det (GaussianConstraint.saddlePointOperator X M) =
      (fromBlocks (LinearMap.toMatrix v.toBasis v.toBasis X)
        (LinearMap.toMatrix v.toBasis w.toBasis M)ᵀ
        (LinearMap.toMatrix v.toBasis w.toBasis M) 0).det := by apply _root_.YangMills.Construction.GaussianConstraint.SaddleDeterminant.det_saddlePointOperator_eq_det_fromBlocks <;> assumption
private theorem surjective_of_comp_adjoint_eq_smul (M : E →ₗ[ℝ] F) {b : ℝ} (hb : 0 < b)
    (hMM : M ∘ₗ LinearMap.adjoint M = b • LinearMap.id) : Function.Surjective M := fun f =>
  ⟨b⁻¹ • LinearMap.adjoint M f, by
    have h := LinearMap.congr_fun hMM f
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
    rw [map_smul, h, smul_smul, inv_mul_cancel₀ hb.ne', one_smul]⟩
private theorem apply_adjoint_of_comp_eq_smul (M : E →ₗ[ℝ] F) {b : ℝ}
    (hMM : M ∘ₗ LinearMap.adjoint M = b • LinearMap.id) (f : F) :
    M (LinearMap.adjoint M f) = b • f := by
  have h := LinearMap.congr_fun hMM f
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] using h
private theorem abs_det_saddlePointOperator_of_scaled (M : E →ₗ[ℝ] F) {b : ℝ} (hb : 0 < b)
    (hMM : M ∘ₗ LinearMap.adjoint M = b • LinearMap.id) (Y : E →ₗ[ℝ] E)
    (c : LinearMap.ker M →ₗ[ℝ] LinearMap.ker M)
    (hc : ∀ x y : LinearMap.ker M, inner ℝ (x : E) (Y y) = inner ℝ x (c y)) :
    |LinearMap.det (GaussianConstraint.saddlePointOperator Y M)| = |LinearMap.det c| * b ^ finrank ℝ F := by
  have hM := surjective_of_comp_adjoint_eq_smul M hb hMM
  have hrank : finrank ℝ (LinearMap.ker M) + finrank ℝ F = finrank ℝ E := by
    have := LinearMap.finrank_range_add_finrank_ker M
    rw [LinearMap.range_eq_top.2 hM, finrank_top] at this
    omega
  have hperp : finrank ℝ (LinearMap.ker M)ᗮ = finrank ℝ F := by
    have := (LinearMap.ker M).finrank_add_finrank_orthogonal
    omega
  let bK := stdOrthonormalBasis ℝ (LinearMap.ker M)
  let bP := (stdOrthonormalBasis ℝ (LinearMap.ker M)ᗮ).reindex (finCongr hperp)
  let w := stdOrthonormalBasis ℝ F
  obtain ⟨v, hvK, hvP⟩ := exists_orthonormalBasis_sum_adapted _ bK bP
  set Xm := LinearMap.toMatrix v.toBasis v.toBasis Y with hXm
  set Mm := LinearMap.toMatrix v.toBasis w.toBasis M with hMmdef
  have hz : ∀ f i, Mm f (Sum.inl i) = 0 := by
    intro f i
    have hk : M (bK i : E) = 0 := (bK i).2
    simp [hMmdef, LinearMap.toMatrix_apply, hvK, hk]
  have hsplit : Mm = fromCols 0 Mm.toCols₂ := by
    ext f i
    rcases i with i | i
    · simp [hz]
    · simp [toCols₂]
  have hMM' : Mm * Mmᵀ = Mm.toCols₂ * Mm.toCols₂ᵀ := by
    conv_lhs => rw [hsplit]
    rw [transpose_fromCols, fromCols_mul_fromRows]
    simp
  have hdetMM : LinearMap.det (M ∘ₗ LinearMap.adjoint M) = Mm.toCols₂.det ^ 2 := by
    have hadj : LinearMap.toMatrix w.toBasis v.toBasis (LinearMap.adjoint M) = Mmᵀ := by
      rw [LinearMap.toMatrix_adjoint, conjTranspose_eq_transpose_of_trivial]
    rw [← LinearMap.det_toMatrix w.toBasis,
      LinearMap.toMatrix_comp w.toBasis v.toBasis w.toBasis, hadj, hMM', det_mul, det_transpose, sq]
  have hdb : Mm.toCols₂.det ^ 2 = b ^ finrank ℝ F := by
    rw [← hdetMM, hMM, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hA : Xm.toBlocks₁₁ = LinearMap.toMatrix bK.toBasis bK.toBasis c := by
    ext i j
    have h1 := hc (bK i) (bK j)
    simp only [toBlocks₁₁, hXm, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, of_apply, hvK]
    exact h1
  have hN : IsUnit Mm.toCols₂.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0] at hdb
    have : 0 < b ^ finrank ℝ F := by positivity
    simp at hdb
    exact this.ne (by simpa using hdb.symm ▸ rfl)
  rw [det_saddlePointOperator_eq v w, abs_det_saddleMatrix Xm Mm hz hN, hA, LinearMap.det_toMatrix, hdb]
end Spaces
section Turning
variable {G Gc : Type} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup Gc] [InnerProductSpace ℝ Gc] [FiniteDimensional ℝ Gc]
private theorem det_adjoint_eq {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (f : V →ₗ[ℝ] V) :
    LinearMap.det (LinearMap.adjoint f) = LinearMap.det f := by
  classical
  let b := stdOrthonormalBasis ℝ V
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis]
  have h : LinearMap.toMatrix b.toBasis b.toBasis (LinearMap.adjoint f) =
      (LinearMap.toMatrix b.toBasis b.toBasis f).transpose := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Matrix.transpose_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    rw [LinearMap.adjoint_inner_right, real_inner_comm]
  rw [h, Matrix.det_transpose]
private theorem absDetOfMap_eq_abs_det_comp {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (e : W ≃ₗᵢ[ℝ] V) (A : V →ₗ[ℝ] W) :
    absDetOfMap A = |LinearMap.det (e.toLinearEquiv.toLinearMap ∘ₗ A)| := by
  have h : LinearMap.adjoint A ∘ₗ A =
      LinearMap.adjoint (e.toLinearEquiv.toLinearMap ∘ₗ A) ∘ₗ
        (e.toLinearEquiv.toLinearMap ∘ₗ A) := by
    refine LinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    exact (e.inner_map_map _ _).symm
  rw [absDetOfMap, h, LinearMap.det_comp, det_adjoint_eq, ← sq, Real.sqrt_sq_eq_abs]
private theorem exists_isometry_comp_eq (aa r₂ : G →ₗ[ℝ] Gc) {b : ℝ} (hb : 0 < b)
    (h₁ : aa ∘ₗ LinearMap.adjoint aa = b • LinearMap.id)
    (h₂ : r₂ ∘ₗ LinearMap.adjoint r₂ = b • LinearMap.id) :
    ∃ R : G ≃ₗᵢ[ℝ] G, ∀ x, r₂ (R x) = aa x := by
  have e₁ := apply_adjoint_of_comp_eq_smul aa h₁
  have e₂ := apply_adjoint_of_comp_eq_smul r₂ h₂
  have hb' : b ≠ 0 := hb.ne'
  set S : Submodule ℝ G := LinearMap.range (LinearMap.adjoint aa) with hS
  set f : G →ₗ[ℝ] G := b⁻¹ • (LinearMap.adjoint r₂ ∘ₗ aa) with hf
  have hnorm : ∀ s : S, ‖f s‖ = ‖(s : G)‖ := by
    rintro ⟨s, g, rfl⟩
    have h3 : f (LinearMap.adjoint aa g) = LinearMap.adjoint r₂ g := by
      simp only [hf, LinearMap.smul_apply, LinearMap.comp_apply, e₁, map_smul, smul_smul,
        inv_mul_cancel₀ hb', one_smul]
    have ha : ‖LinearMap.adjoint aa g‖ ^ 2 = b * ‖g‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, LinearMap.adjoint_inner_left, e₁, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
    have hr : ‖LinearMap.adjoint r₂ g‖ ^ 2 = b * ‖g‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, LinearMap.adjoint_inner_left, e₂, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
    show ‖f (LinearMap.adjoint aa g)‖ = ‖LinearMap.adjoint aa g‖
    rw [h3]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hr.trans ha.symm)
  let Li : S →ₗᵢ[ℝ] G := ⟨f ∘ₗ S.subtype, hnorm⟩
  let R0 : G →ₗᵢ[ℝ] G := Li.extend
  have hR0 : ∀ s : S, R0 s = f s := fun s => LinearIsometry.extend_apply Li s
  have hker : ∀ κ, aa κ = 0 → r₂ (R0 κ) = 0 := by
    intro κ hκ
    refine ext_inner_right ℝ fun g => ?_
    have h3 : LinearMap.adjoint r₂ g = R0 (LinearMap.adjoint aa g) := by
      have h4 := hR0 ⟨LinearMap.adjoint aa g, g, rfl⟩
      simp only at h4
      rw [h4]
      simp only [hf, LinearMap.smul_apply, LinearMap.comp_apply, e₁, map_smul, smul_smul,
        inv_mul_cancel₀ hb', one_smul]
    rw [← LinearMap.adjoint_inner_right, h3, R0.inner_map_map, LinearMap.adjoint_inner_right, hκ]
  have hall : ∀ x, r₂ (R0 x) = aa x := by
    intro x
    set s : G := LinearMap.adjoint aa (b⁻¹ • aa x) with hs
    have haa : aa s = aa x := by
      rw [hs, e₁, smul_smul, mul_inv_cancel₀ hb', one_smul]
    have hsS : s ∈ S := ⟨_, rfl⟩
    have hx : x = s + (x - s) := by abel
    have hk : r₂ (R0 (x - s)) = 0 := hker _ (by rw [map_sub, haa, sub_self])
    have hs1 : r₂ (R0 s) = aa s := by
      have h4 := hR0 ⟨s, hsS⟩
      simp only at h4
      rw [h4]
      simp only [hf, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, e₂, smul_smul,
        inv_mul_cancel₀ hb', one_smul]
    calc r₂ (R0 x) = r₂ (R0 (s + (x - s))) := by rw [← hx]
      _ = aa x := by rw [map_add, map_add, hs1, hk, add_zero, haa]
  exact ⟨R0.toLinearIsometryEquiv rfl, fun x => by
    simpa using hall x⟩
private theorem abs_det_borderedBlockOperator_eq (m : G →ₗ[ℝ] G) (aa r₂ : G →ₗ[ℝ] Gc) {b : ℝ} (hb : 0 < b)
    (h₁ : aa ∘ₗ LinearMap.adjoint aa = b • LinearMap.id)
    (h₂ : r₂ ∘ₗ LinearMap.adjoint r₂ = b • LinearMap.id)
    (l' : LinearMap.ker aa →ₗ[ℝ] LinearMap.ker r₂)
    (hl : ∀ κ : LinearMap.ker aa, (l' κ : G) =
      m κ - b⁻¹ • LinearMap.adjoint r₂ (r₂ (m κ))) :
    |LinearMap.det (borderedBlockOperator m (LinearMap.adjoint r₂) aa)| =
      b ^ finrank ℝ Gc * absDetOfMap l' := by
  obtain ⟨R, hR⟩ := exists_isometry_comp_eq aa r₂ hb h₁ h₂
  set Rl : G →ₗ[ℝ] G := R.toLinearEquiv.toLinearMap with hRl
  have hRa : ∀ x y, inner ℝ (LinearMap.adjoint Rl x) y = inner ℝ x (R y) := fun x y => by
    rw [LinearMap.adjoint_inner_left]
    rfl
  have hRRa : ∀ x, R (LinearMap.adjoint Rl x) = x := fun x => by
    refine ext_inner_right ℝ fun y => ?_
    have h3 := hRa x (R.symm y)
    rw [← R.inner_map_map] at h3
    simpa using h3
  have hRaR : ∀ x, LinearMap.adjoint Rl (R x) = x := fun x =>
    R.injective (hRRa (R x))
  have hT : ∀ g, R (LinearMap.adjoint aa g) = LinearMap.adjoint r₂ g := fun g => by
    refine ext_inner_right ℝ fun y => ?_
    have h3 : inner ℝ (R (LinearMap.adjoint aa g)) y =
        inner ℝ (LinearMap.adjoint aa g) (R.symm y) := by
      conv_lhs => rw [← R.apply_symm_apply y]
      exact R.inner_map_map _ _
    rw [h3, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, ← hR, R.apply_symm_apply]
  set Y : G →ₗ[ℝ] G := LinearMap.adjoint Rl ∘ₗ m with hY
  have hfac : borderedBlockOperator m (LinearMap.adjoint r₂) aa =
      (Rl.prodMap LinearMap.id) ∘ₗ GaussianConstraint.saddlePointOperator Y aa := by
    refine LinearMap.ext fun x => ?_
    rcases x with ⟨x, g⟩
    refine Prod.ext ?_ rfl
    show m x + LinearMap.adjoint r₂ g = R (LinearMap.adjoint Rl (m x) + LinearMap.adjoint aa g)
    rw [map_add, hRRa, hT]
  have hdetR : |LinearMap.det Rl| = 1 := by
    have h3 : LinearMap.adjoint Rl ∘ₗ Rl = LinearMap.id := LinearMap.ext hRaR
    have h4 := congrArg LinearMap.det h3
    rw [LinearMap.det_comp, det_adjoint_eq, LinearMap.det_id, ← sq] at h4
    rw [← sq_eq_sq₀ (abs_nonneg _) zero_le_one, sq_abs, h4, one_pow]
  have hmem : ∀ x : LinearMap.ker aa, Rl x ∈ LinearMap.ker r₂ := fun x => by
    have h3 : r₂ (R x) = aa x := hR x
    exact LinearMap.mem_ker.mpr (h3.trans (LinearMap.mem_ker.mp x.2))
  let e₀ : LinearMap.ker aa →ₗᵢ[ℝ] LinearMap.ker r₂ :=
    ⟨(Rl ∘ₗ (LinearMap.ker aa).subtype).codRestrict _ hmem, fun x => R.norm_map x⟩
  have he₀ : Function.Surjective e₀ := fun y => by
    have h3 : aa (R.symm y) = 0 := by
      rw [← hR, R.apply_symm_apply]
      exact y.2
    exact ⟨⟨R.symm y, h3⟩, Subtype.ext (R.apply_symm_apply _)⟩
  let e : LinearMap.ker aa ≃ₗᵢ[ℝ] LinearMap.ker r₂ := LinearIsometryEquiv.ofSurjective e₀ he₀
  have hcoe : ∀ x : LinearMap.ker aa, ((e x : LinearMap.ker r₂) : G) = R x := fun x => rfl
  set c : LinearMap.ker aa →ₗ[ℝ] LinearMap.ker aa := e.symm.toLinearEquiv.toLinearMap ∘ₗ l' with hc
  have hcc : ∀ x y : LinearMap.ker aa, inner ℝ (x : G) (Y y) = inner ℝ x (c y) := by
    intro x y
    have h3 : inner ℝ x (c y) = inner ℝ (e x) (l' y) := by
      have := e.inner_map_map x (c y)
      rw [← this]
      simp [hc]
    rw [h3, Submodule.coe_inner, hcoe, hl, inner_sub_right, real_inner_smul_right,
      LinearMap.adjoint_inner_right, hR, LinearMap.mem_ker.mp x.2]
    simp [hY, LinearMap.adjoint_inner_right]
    rfl
  have hs := abs_det_saddlePointOperator_of_scaled aa hb h₁ Y c hcc
  rw [hfac, LinearMap.det_comp, LinearMap.det_prodMap, LinearMap.det_id, mul_one, abs_mul, hdetR,
    one_mul, hs, absDetOfMap_eq_abs_det_comp e.symm l', mul_comm]
end Turning
private theorem normSqForm_apply {K Y : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [FiniteDimensional ℝ K] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [FiniteDimensional ℝ Y] (l : K →ₗ[ℝ] Y) (ξ : K) : normSqForm l ξ = ‖l ξ‖ ^ 2 := by
  simp [normSqForm, LinearMap.BilinMap.toQuadraticMap_apply, real_inner_self_eq_norm_sq]
theorem gaussianNumberViaBorderedDeterminant_holds (hC : GaugeChangeGaussianIdentity)
    (hS : GaussianConstraint.SaddleDeterminantIdentity) :
    GaussianNumberViaBorderedDeterminant := by
  intro G A Gc C Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D Dc Q r r₂ n p b T X l hQ hrr hQD hb h₁ h₁r h₂
    hDinj hT0 hTnull hghost hXs hXf hl
  set aa : G →ₗ[ℝ] Gc := r + n ∘ₗ D with haa
  have e₁ := apply_adjoint_of_comp_eq_smul aa h₁
  have e₂ := apply_adjoint_of_comp_eq_smul r₂ h₂
  have e₃ : ∀ g, aa (LinearMap.adjoint r g) = b • g := fun g => by
    simpa using LinearMap.congr_fun h₁r g
  have e₄ : ∀ g, r (LinearMap.adjoint r g) = g := fun g => LinearMap.congr_fun hrr g
  have hb' : b ≠ 0 := hb.ne'
  have hbij : Function.Bijective (aa ∘ₗ LinearMap.adjoint r) := by
    rw [h₁r]
    refine ⟨fun x y hxy => ?_, fun y => ⟨b⁻¹ • y, ?_⟩⟩
    · have h3 : b • x = b • y := hxy
      exact smul_right_injective _ hb' h3
    · simp [smul_smul, inv_mul_cancel₀ hb', mul_inv_cancel₀ hb']
  obtain ⟨hτb, -, h, key⟩ := hC G A Gc C D Dc Q r n T hQ hrr hQD hbij hDinj hT0 hTnull
  set τ : A →ₗ[ℝ] A := LinearMap.id + D ∘ₗ LinearMap.adjoint r ∘ₗ n with hτ
  have hτa : ∀ ξ, τ ξ = ξ + D (LinearMap.adjoint r (n ξ)) := fun ξ => rfl
  set q : G →ₗ[ℝ] G := LinearMap.id - b⁻¹ • (LinearMap.adjoint r₂ ∘ₗ r₂) with hq
  have hqa : ∀ x, q x = x - b⁻¹ • LinearMap.adjoint r₂ (r₂ x) := fun x => rfl
  have hq0 : ∀ x, r₂ (q x) = 0 := fun x => by
    rw [hqa, map_sub, map_smul, e₂, smul_smul, inv_mul_cancel₀ hb', one_smul, sub_self]
  let l' : A →ₗ[ℝ] LinearMap.ker r₂ := (q ∘ₗ p).codRestrict _ fun ξ => hq0 _
  have hl'a : ∀ ξ, ((l' ξ : LinearMap.ker r₂) : G) = p ξ - b⁻¹ • LinearMap.adjoint r₂ (r₂ (p ξ)) :=
    fun ξ => rfl
  let A₀ : LinearMap.ker aa →ₗ[ℝ] LinearMap.ker r₂ := l' ∘ₗ D ∘ₗ (LinearMap.ker aa).subtype
  have hA₀a : ∀ κ : LinearMap.ker aa, ((A₀ κ : LinearMap.ker r₂) : G) =
      (p ∘ₗ D) κ - b⁻¹ • LinearMap.adjoint r₂ (r₂ ((p ∘ₗ D) κ)) := fun κ => hl'a _
  have hBd : Function.Injective (borderedBlockOperator (p ∘ₗ D) (LinearMap.adjoint r₂) aa) :=
    ((Module.End.isUnit_iff _).mp
      ((LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hghost))).1
  have hinj : Function.Injective A₀ := by
    refine (injective_iff_map_eq_zero A₀).mpr fun κ hκ => ?_
    have h3 := hA₀a κ
    rw [hκ] at h3
    have h4 : borderedBlockOperator (p ∘ₗ D) (LinearMap.adjoint r₂) aa
        ((κ : G), -(b⁻¹ • r₂ ((p ∘ₗ D) κ))) = 0 := by
      refine Prod.ext ?_ (LinearMap.mem_ker.mp κ.2)
      show (p ∘ₗ D) κ + LinearMap.adjoint r₂ (-(b⁻¹ • r₂ ((p ∘ₗ D) κ))) = 0
      rw [map_neg, map_smul, ← sub_eq_add_neg]
      simpa using h3.symm
    have h5 := hBd (h4.trans (map_zero _).symm)
    exact Subtype.ext (congrArg Prod.fst h5)
  have hr₁ : Function.Surjective aa := surjective_of_comp_adjoint_eq_smul aa hb h₁
  have hr₂ : Function.Surjective r₂ := surjective_of_comp_adjoint_eq_smul r₂ hb h₂
  have hrank : finrank ℝ (LinearMap.ker aa) = finrank ℝ (LinearMap.ker r₂) := by
    have h3 := LinearMap.finrank_range_add_finrank_ker aa
    have h4 := LinearMap.finrank_range_add_finrank_ker r₂
    rw [LinearMap.range_eq_top.2 hr₁, finrank_top] at h3
    rw [LinearMap.range_eq_top.2 hr₂, finrank_top] at h4
    omega
  have hA₀ : Function.Bijective A₀ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj⟩
  have K := key Y (LinearMap.ker r₂) l l' hl hA₀
  set Q' : A →ₗ[ℝ] C := Q + Dc ∘ₗ n with hQ'
  have hQτ : ∀ ξ, Q (τ ξ) = Q' ξ := fun ξ => LinearMap.congr_fun h ξ
  have hQ's : Function.Surjective Q' := fun f => by
    obtain ⟨x, hx⟩ := hQ f
    obtain ⟨y, hy⟩ := hτb.2 x
    exact ⟨y, by rw [← hQτ, hy, hx]⟩
  set T' : QuadraticForm ℝ (LinearMap.ker Q') :=
    T.comp (kerMapOfCompEq τ h) +
      (normSqForm l').comp (LinearMap.ker Q').subtype with hT'
  have hT'a : ∀ B : LinearMap.ker Q', T' B =
      T (kerMapOfCompEq τ h B) + ‖l' B‖ ^ 2 := fun B => by
    simp [hT', normSqForm_apply]
  have hpos : T'.PosDef := by
    intro x hx
    by_contra hnot
    have h0 := hT0 (kerMapOfCompEq τ h x)
    have h1 : 0 ≤ ‖l' x‖ ^ 2 := by positivity
    have h2 : T' x ≤ 0 := not_lt.mp hnot
    rw [hT'a] at h2
    have hTz : T (kerMapOfCompEq τ h x) = 0 := by linarith
    have hlz : ‖l' x‖ ^ 2 = 0 := by linarith
    have hlz' : l' x = 0 := by simpa using hlz
    obtain ⟨κ, hκ, hDκ⟩ := (hTnull _).mp hTz
    set lam : G := κ - b⁻¹ • LinearMap.adjoint r (aa κ) with hlam
    have haal : aa lam = 0 := by
      rw [hlam, map_sub, map_smul, e₃, smul_smul, inv_mul_cancel₀ hb', one_smul, sub_self]
    have hrl : r lam = -(b⁻¹ • aa κ) := by
      rw [hlam, map_sub, map_smul, e₄, LinearMap.mem_ker.mp hκ, zero_sub]
    have hnl : n (D lam) = b⁻¹ • aa κ := by
      have h3 : r lam + n (D lam) = 0 := haal
      rw [hrl] at h3
      exact (neg_add_eq_zero.mp h3).symm
    have hτD : τ (D lam) = D κ := by
      rw [hτa, hnl, hlam, map_sub, map_smul, map_smul, map_smul]
      abel
    have hxD : (x : A) = D lam := by
      apply hτb.1
      rw [hτD, hDκ]
      rfl
    have hz : A₀ ⟨lam, haal⟩ = 0 := by
      exact show l' (D lam) = 0 from by rw [← hxD]; exact hlz'
    have h3 : (⟨lam, haal⟩ : LinearMap.ker aa) = 0 := hinj (hz.trans (map_zero _).symm)
    have h4 : lam = 0 := congrArg Subtype.val h3
    exact hx (Subtype.ext (by rw [hxD, h4, map_zero]; rfl))
  have hform : ∀ B : LinearMap.ker Q', inner ℝ (B : A) (X B) = T' B := by
    intro B
    have hm : (B : A) + D (LinearMap.adjoint r (n B)) ∈ LinearMap.ker Q := by
      rw [LinearMap.mem_ker]
      exact (hQτ B).trans (LinearMap.mem_ker.mp B.2)
    rw [hXf B (LinearMap.mem_ker.mp B.2) hm, hT'a]
    have e₅ : (⟨_, hm⟩ : LinearMap.ker Q) = kerMapOfCompEq τ h B := Subtype.ext rfl
    rw [e₅, ← hl'a, Submodule.coe_norm]
  have hI := (hS A C Q' T' hQ's hpos X hXs hform).1
  have hSne : LinearMap.det (GaussianConstraint.saddlePointOperator X Q') ≠ 0 := by
    have hinjS : Function.Injective (GaussianConstraint.saddlePointOperator X Q') := by
      refine (injective_iff_map_eq_zero _).mpr ?_
      rintro ⟨ξ, f⟩ hz
      have h3 : X ξ + LinearMap.adjoint Q' f = 0 := congrArg Prod.fst hz
      have h4 : Q' ξ = 0 := congrArg Prod.snd hz
      have h5 : inner ℝ ξ (X ξ) = 0 := by
        have h6 : X ξ = -LinearMap.adjoint Q' f := eq_neg_of_add_eq_zero_left h3
        rw [h6, inner_neg_right, LinearMap.adjoint_inner_right, h4]
        simp
      have h7 := hform ⟨ξ, h4⟩
      have h8 : T' ⟨ξ, h4⟩ = 0 := by rw [← h7]; exact h5
      have h9 : (⟨ξ, h4⟩ : LinearMap.ker Q') = 0 := by
        by_contra hne
        have := hpos _ hne
        rw [h8] at this
        exact lt_irrefl _ this
      have hξ : ξ = 0 := congrArg Subtype.val h9
      have h10 : LinearMap.adjoint Q' f = 0 := by simpa [hξ] using h3
      have hf : f = 0 := by
        obtain ⟨y, hy⟩ := hQ's f
        have h11 : inner ℝ f f = 0 := by
          have h12 := LinearMap.adjoint_inner_left Q' y f
          rw [h10, inner_zero_left, hy] at h12
          exact h12.symm
        exact inner_self_eq_zero.mp h11
      rw [hξ, hf]
      rfl
    exact (LinearEquiv.ofInjectiveEndo _ hinjS).isUnit_det'.ne_zero
  refine ⟨hSne, ?_⟩
  have hdetaa : LinearMap.det (aa ∘ₗ LinearMap.adjoint aa) = b ^ finrank ℝ Gc := by
    rw [h₁, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hvol : absDetOfMap (l' ∘ₗ D ∘ₗ (LinearMap.ker aa).subtype) =
      (b ^ finrank ℝ Gc)⁻¹ *
        |LinearMap.det (borderedBlockOperator (p ∘ₗ D) (LinearMap.adjoint r₂) aa)| := by
    have h3 := abs_det_borderedBlockOperator_eq (p ∘ₗ D) aa r₂ hb h₁ h₂ A₀ hA₀a
    rw [h3, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have K' : GaussianConstraint.constrainedGaussianNumber Q
      (T + (normSqForm l).comp (LinearMap.ker Q).subtype) *
      absDetOfMap (l ∘ₗ D ∘ₗ (LinearMap.ker r).subtype) =
      LinearMap.det (aa ∘ₗ LinearMap.adjoint aa) ^ (1 / 2 : ℝ) *
        GaussianConstraint.constrainedGaussianNumber Q' T' *
        absDetOfMap (l' ∘ₗ D ∘ₗ (LinearMap.ker aa).subtype) := K
  rw [K', hdetaa, hI, hvol]
  ring
end YangMills.Construction.LinearConstraint.BorderedDeterminant
end
