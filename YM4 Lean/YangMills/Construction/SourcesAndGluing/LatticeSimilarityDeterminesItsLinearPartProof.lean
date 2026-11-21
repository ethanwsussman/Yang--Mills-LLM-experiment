import YangMills.Construction.SourcesAndGluing.LatticeSimilarityDeterminesItsLinearPartForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.ScaledMotionRotation
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusLifts
theorem hyperoctahedral_apply_zero {S : Equiv.Perm AmbientSpace}
    (hS : S ∈ hyperoctahedralGroupEuclidean) : S 0 = 0 := by
  obtain ⟨π, s, rfl⟩ := hS
  funext μ
  have hμ : (signedCoordinateEquiv π s) (0 : AmbientSpace) μ =
      ((s μ : ℤ) : ℝ) * (0 : AmbientSpace) (π μ) := rfl
  rw [hμ]
  simp
theorem hyperoctahedral_apply_smul {S : Equiv.Perm AmbientSpace}
    (hS : S ∈ hyperoctahedralGroupEuclidean) (t : ℝ) (x : AmbientSpace) (μ : Fin 4) :
    S (t • x) μ = t * S x μ := by
  obtain ⟨π, s, rfl⟩ := hS
  have h₁ : (signedCoordinateEquiv π s) (t • x) μ = ((s μ : ℤ) : ℝ) * (t • x) (π μ) := rfl
  have h₂ : (signedCoordinateEquiv π s) x μ = ((s μ : ℤ) : ℝ) * x (π μ) := rfl
  rw [h₁, h₂, Pi.smul_apply, smul_eq_mul]
  ring
theorem abs_hyperoctahedral_apply_one {S : Equiv.Perm AmbientSpace}
    (hS : S ∈ hyperoctahedralGroupEuclidean) (μ : Fin 4) :
    |S (fun _ => 1) μ| = 1 := by
  obtain ⟨π, s, rfl⟩ := hS
  have h : (signedCoordinateEquiv π s) (fun _ => 1) μ = ((s μ : ℤ) : ℝ) * (1 : ℝ) := rfl
  rw [h]
  rcases Int.units_eq_one_or (s μ) with h | h <;> simp [h]
theorem L_zpow_pos (D : GluingSetup) (b : ℤ) : 0 < (D.L : ℝ) ^ b :=
  zpow_pos (by exact_mod_cast ScaleExponent.L_pos (D := D)) b
theorem rotation_eq_of_onSpace_eq {D : GluingSetup} {e e' : ScaleExponent D}
    (Φ : ScaledLatticeMotion e) (Φ' : ScaledLatticeMotion e') (h : Φ'.onSpace = Φ.onSpace) :
    Φ'.rotation = Φ.rotation := by
  have hc := L_zpow_pos D e.shift
  have hc' := L_zpow_pos D e'.shift
  have hx : ∀ x, (D.L : ℝ) ^ e'.shift • Φ'.rotation x + Φ'.offset =
      (D.L : ℝ) ^ e.shift • Φ.rotation x + Φ.offset := fun x => congrFun h x
  have hw : Φ'.offset = Φ.offset := by
    have h₀ := hx 0
    rw [hyperoctahedral_apply_zero Φ.rotation_mem, hyperoctahedral_apply_zero Φ'.rotation_mem,
      smul_zero, smul_zero, zero_add, zero_add] at h₀
    exact h₀
  have hone : (D.L : ℝ) ^ e'.shift * Φ'.rotation (fun _ => 1) 0 =
      (D.L : ℝ) ^ e.shift * Φ.rotation (fun _ => 1) 0 := by
    have h₁ := hx fun _ => 1
    rw [hw] at h₁
    exact congrFun (add_right_cancel h₁) 0
  have hscale : (D.L : ℝ) ^ e'.shift = (D.L : ℝ) ^ e.shift := by
    have h₁ := congrArg abs hone
    rwa [abs_mul, abs_mul, abs_hyperoctahedral_apply_one Φ'.rotation_mem,
      abs_hyperoctahedral_apply_one Φ.rotation_mem, mul_one, mul_one, abs_of_pos hc',
      abs_of_pos hc] at h₁
  refine Equiv.ext fun x => ?_
  have h₁ := hx x
  rw [hw, hscale] at h₁
  exact smul_right_injective AmbientSpace hc.ne' (add_right_cancel h₁)
theorem rotation_eq_of_onTorus_eq {D : GluingSetup} {e : ScaleExponent D}
    (Φ Φ' : ScaledLatticeMotion e) (h : Φ'.onTorus = Φ.onTorus) :
    Φ'.rotation = Φ.rotation := by
  have hc := L_zpow_pos D e.shift
  have hside : PeriodicLattice.torusSide D.L (e.target.m : ℕ) ≠ 0 := by
    have hL : (0 : ℝ) < D.L := by exact_mod_cast ScaleExponent.L_pos (D := D)
    have : 0 < PeriodicLattice.torusSide D.L (e.target.m : ℕ) := by
      simp only [PeriodicLattice.torusSide]
      positivity
    exact this.ne'
  generalize hℓ : PeriodicLattice.torusSide D.L (e.target.m : ℕ) = ℓ at hside
  have hk : ∀ x, ∃ k, Φ'.onSpace x = Φ.onSpace x + TestFunctions.latticeTranslate ℓ k :=
    fun x => TestFunctions.exists_latticeTranslate_of_torusProj_eq (by
      rw [← hℓ, ← Φ'.onTorus_torusProj, ← Φ.onTorus_torusProj, h])
  obtain ⟨k₀, h₀⟩ := hk 0
  have hz : ∀ (x : AmbientSpace) (μ : Fin 4), ∃ n : ℤ,
      (D.L : ℝ) ^ e.shift * (Φ'.rotation x μ - Φ.rotation x μ) = ℓ * (n : ℝ) := by
    intro x μ
    obtain ⟨k, hk'⟩ := hk x
    refine ⟨k μ - k₀ μ, ?_⟩
    have h₁ : (D.L : ℝ) ^ e.shift * Φ'.rotation x μ + Φ'.offset μ =
        (D.L : ℝ) ^ e.shift * Φ.rotation x μ + Φ.offset μ + ℓ * (k μ : ℝ) := congrFun hk' μ
    have h₂ : (D.L : ℝ) ^ e.shift * Φ'.rotation 0 μ + Φ'.offset μ =
        (D.L : ℝ) ^ e.shift * Φ.rotation 0 μ + Φ.offset μ + ℓ * (k₀ μ : ℝ) := congrFun h₀ μ
    rw [hyperoctahedral_apply_zero Φ.rotation_mem, hyperoctahedral_apply_zero Φ'.rotation_mem] at h₂
    simp only [Pi.zero_apply, mul_zero, zero_add] at h₂
    push_cast
    linear_combination h₁ - h₂
  refine Equiv.ext fun x => funext fun μ => ?_
  by_contra hne
  have hf : (D.L : ℝ) ^ e.shift * (Φ'.rotation x μ - Φ.rotation x μ) ≠ 0 :=
    mul_ne_zero hc.ne' (sub_ne_zero.2 hne)
  generalize hfdef : (D.L : ℝ) ^ e.shift * (Φ'.rotation x μ - Φ.rotation x μ) = f at hf
  obtain ⟨n, hn⟩ := hz ((ℓ / (2 * f)) • x) μ
  rw [hyperoctahedral_apply_smul Φ'.rotation_mem, hyperoctahedral_apply_smul Φ.rotation_mem] at hn
  have hhalf : ℓ / 2 = ℓ * (n : ℝ) := by
    rw [← hn]
    have : (D.L : ℝ) ^ e.shift * (ℓ / (2 * f) * Φ'.rotation x μ - ℓ / (2 * f) * Φ.rotation x μ) =
        ℓ / (2 * f) * f := by
      rw [← hfdef]
      ring
    rw [this]
    field_simp
  have hn2 : (2 : ℝ) * (n : ℝ) = 1 := by
    have h₁ : ℓ * (2 * (n : ℝ) - 1) = 0 := by linear_combination (-2 : ℝ) * hhalf
    have h₂ := (mul_eq_zero.1 h₁).resolve_left hside
    linarith
  have hn3 : 2 * n = 1 := by exact_mod_cast hn2
  omega
theorem holds : ScaledMotionRotationClaim := fun _ _ Φ =>
  ⟨fun _ Φ' h => rotation_eq_of_onSpace_eq Φ Φ' h,
    fun Φ' h => rotation_eq_of_onTorus_eq Φ Φ' h⟩
end YangMills.Construction.SourcesAndGluing.ScaledMotionRotation
end
