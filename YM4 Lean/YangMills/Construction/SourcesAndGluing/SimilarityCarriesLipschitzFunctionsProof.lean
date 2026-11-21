import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfTori
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesLipschitzFunctions
import Mathlib
set_option autoImplicit false
open scoped Pointwise
noncomputable section
namespace YangMills.Construction
open TestFunctions
namespace SourcesAndGluing.LipschitzRescaling
section General
variable {X Y E : Type*}
theorem dist_invFun_of_scaling [Nonempty X] {T : X → Y} (hT : Function.Bijective T)
    {dX : X → X → ℝ} {dY : Y → Y → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hscale : ∀ x y, dY (T x) (T y) = c * dX x y) (x y : Y) :
    dX (Function.invFun T x) (Function.invFun T y) = c⁻¹ * dY x y := by
  obtain ⟨p, rfl⟩ := hT.surjective x
  obtain ⟨q, rfl⟩ := hT.surjective y
  rw [Function.leftInverse_invFun hT.injective p, Function.leftInverse_invFun hT.injective q,
    hscale, inv_mul_cancel_left₀ hc]
theorem uniformNorm_comp_surjective [Norm E] {φ : Y → X} (hφ : Function.Surjective φ)
    (f : X → E) : uniformNorm (f ∘ φ) = uniformNorm f :=
  hφ.iSup_comp fun x => ‖f x‖
theorem bestLipschitzConstant_comp_surjective [NormedAddCommGroup E] {φ : Y → X}
    (hφ : Function.Surjective φ) {dX : X → X → ℝ} {dY : Y → Y → ℝ} {c : ℝ} (hc : 0 < c)
    (hscale : ∀ x y, dX (φ x) (φ y) = c * dY x y) (f : X → E) :
    bestLipschitzConstant dY (f ∘ φ) = c * bestLipschitzConstant dX f := by
  have hset : {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖(f ∘ φ) x - (f ∘ φ) y‖ ≤ C * dY x y} =
      c • {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * dX x y} := by
    ext C
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨hC, hbound⟩
      refine ⟨c⁻¹ * C, ⟨by positivity, fun x y => ?_⟩, by
        rw [smul_eq_mul, mul_inv_cancel_left₀ hc.ne']⟩
      obtain ⟨p, rfl⟩ := hφ x
      obtain ⟨q, rfl⟩ := hφ y
      have hpq := hbound p q
      rw [hscale, mul_comm c⁻¹ C, mul_assoc, inv_mul_cancel_left₀ hc.ne']
      exact hpq
    · rintro ⟨C', ⟨hC', hbound⟩, rfl⟩
      refine ⟨by rw [smul_eq_mul]; positivity, fun x y => ?_⟩
      have hxy := hbound (φ x) (φ y)
      rw [hscale] at hxy
      calc ‖(f ∘ φ) x - (f ∘ φ) y‖ ≤ C' * (c * dY x y) := hxy
        _ = c • C' * dY x y := by rw [smul_eq_mul]; ring
  rw [bestLipschitzConstant, hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul,
    bestLipschitzConstant]
theorem bestLipschitzConstant_nonneg [NormedAddCommGroup E] (d : X → X → ℝ) (f : X → E) :
    0 ≤ bestLipschitzConstant d f :=
  Real.sInf_nonneg fun _ hC => hC.1
end General
variable {D : GluingSetup} (Ψ : LatticeRescaling D)
theorem L_zpow_neg_exp_le_one : (D.L : ℝ) ^ (-Ψ.exp) ≤ 1 := by
  have hL : (1 : ℝ) ≤ D.L := by
    exact_mod_cast ScaleExponent.L_pos (D := D)
  rw [zpow_neg]
  exact inv_le_one_of_one_le₀ (one_le_zpow₀ hL Ψ.exp_nonneg)
theorem target_M_eq : Ψ.scaleExponent.target.M = D.M := rfl
theorem max_rescaled_le {s l : ℝ} (hl : 0 ≤ l) :
    max s (40 * D.M * ((D.L : ℝ) ^ (-Ψ.exp) * l)) ≤ max s (40 * D.M * l) := by
  refine max_le_max le_rfl (mul_le_mul_of_nonneg_left ?_ ?_)
  · exact mul_le_of_le_one_left hl (L_zpow_neg_exp_le_one Ψ)
  · have := D.one_le_M
    positivity
theorem euclidDistTorus_inverseOnTorus
    (hT : Ψ.toMotion.IsDilatingBijectionOfTori) (x y : Ψ.scaleExponent.target.Torus) :
    euclidDistTorus (Ψ.inverseOnTorus x) (Ψ.inverseOnTorus y) =
      (D.L : ℝ) ^ (-Ψ.exp) * euclidDistTorus x y := by
  rw [zpow_neg]
  exact dist_invFun_of_scaling (T := Ψ.toTorus) hT.1
    (zpow_pos (by exact_mod_cast ScaleExponent.L_pos (D := D)) Ψ.exp).ne' hT.2.1 x y
theorem euclidDistR4_inverseOnSpace (hS : Ψ.toMotion.IsDilatingBijectionOfSpace)
    (hbij : Function.Bijective Ψ.toSpace) (x y : Fin 4 → ℝ) :
    euclidDistR4 (Ψ.inverseOnSpace x) (Ψ.inverseOnSpace y) =
      (D.L : ℝ) ^ (-Ψ.exp) * euclidDistR4 x y := by
  rw [zpow_neg]
  refine dist_invFun_of_scaling (T := Ψ.toSpace) hbij
    (zpow_pos (by exact_mod_cast ScaleExponent.L_pos (D := D)) Ψ.exp).ne' (fun p q => ?_) x y
  have hpq := hS.2.1 p q
  rw [Ψ.toMotion_onSpace] at hpq
  exact hpq
theorem mapsLipschitzOnTorus (hT : Ψ.toMotion.IsDilatingBijectionOfTori) :
    Ψ.MapsLipschitzOnTorus := by
  intro 𝕜 _ f _
  have hsurj : Function.Surjective Ψ.inverseOnTorus := Function.invFun_surjective hT.1.1
  have hsup : uniformNorm (f ∘ Ψ.inverseOnTorus) = uniformNorm f :=
    uniformNorm_comp_surjective hsurj f
  have hlip : lipConstTorus (f ∘ Ψ.inverseOnTorus) = (D.L : ℝ) ^ (-Ψ.exp) * lipConstTorus f :=
    bestLipschitzConstant_comp_surjective hsurj (zpow_pos (by
      exact_mod_cast ScaleExponent.L_pos (D := D)) _)
      (euclidDistTorus_inverseOnTorus Ψ hT) f
  refine ⟨hsup, hlip, ?_⟩
  change max (uniformNorm (f ∘ Ψ.inverseOnTorus))
      (40 * Ψ.scaleExponent.target.M * lipConstTorus (f ∘ Ψ.inverseOnTorus)) ≤
    max (uniformNorm f) (40 * D.M * lipConstTorus f)
  rw [hsup, hlip, target_M_eq]
  exact max_rescaled_le Ψ (bestLipschitzConstant_nonneg _ _)
theorem mapsLipschitzOnSpace (hS : Ψ.toMotion.IsDilatingBijectionOfSpace) :
    Ψ.MapsLipschitzOnSpace := by
  intro 𝕜 _ f _ _
  have hbij : Function.Bijective Ψ.toSpace := by
    have h := hS.1
    rwa [Ψ.toMotion_onSpace] at h
  have hsurj : Function.Surjective Ψ.inverseOnSpace := Function.invFun_surjective hbij.1
  have hsup : uniformNorm (f ∘ Ψ.inverseOnSpace) = uniformNorm f :=
    uniformNorm_comp_surjective hsurj f
  have hlip : lipConstR4 (f ∘ Ψ.inverseOnSpace) = (D.L : ℝ) ^ (-Ψ.exp) * lipConstR4 f :=
    bestLipschitzConstant_comp_surjective hsurj (zpow_pos (by
      exact_mod_cast ScaleExponent.L_pos (D := D)) _)
      (euclidDistR4_inverseOnSpace Ψ hS hbij) f
  change max (uniformNorm (f ∘ Ψ.inverseOnSpace))
      (40 * Ψ.scaleExponent.target.M * lipConstR4 (f ∘ Ψ.inverseOnSpace)) ≤
    max (uniformNorm f) (40 * D.M * lipConstR4 f)
  rw [hsup, hlip, target_M_eq]
  exact max_rescaled_le Ψ (bestLipschitzConstant_nonneg _ _)
theorem rescalingLipschitzClaim_holds (hS : ScaledMotionDilationOfSpaceClaim)
    (hT : TorusDilationOfScaledMotions.Statement) : RescalingLipschitzClaim := fun D Ψ =>
  ⟨mapsLipschitzOnTorus Ψ (hT D Ψ.scaleExponent Ψ.toMotion),
    mapsLipschitzOnSpace Ψ (hS D Ψ.scaleExponent Ψ.toMotion)⟩
end SourcesAndGluing.LipschitzRescaling
end YangMills.Construction
end
