import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.ColdChainAtEveryLevel.FormsInAPatch
import YangMills.Construction.ColdChainAtEveryLevel.GeneratorNearItsBlockMean
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.NearBlockMean
open YangMills.Construction.GaugeMotions YangMills.Construction.PatchForms YangMills.Construction.LatticePaths YangMills.Construction.LatticeFractionalIntegration
variable {F : BlockFrame} {j : ℕ}
theorem normSubOne_mul_le (a b : UnitQuaternion) : normSubOne (a * b) ≤ normSubOne a + normSubOne b := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.normSubOne_mul_le <;> assumption
theorem normSubOne_conj (a b : UnitQuaternion) : normSubOne (a * b * a⁻¹) = normSubOne b := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem normSubOne_inv (a : UnitQuaternion) : normSubOne a⁻¹ = normSubOne a := norm_coe_inv_sub_one a
def cubePermMean {E : Type} [AddCommMonoid E] [Module ℝ E] (L : ℕ) (g : Lattice4 → Equiv.Perm (Fin 4) → E) : E :=
  (1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), g h π
theorem card_perm_fin_four : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = 24 := by apply _root_.YangMills.Construction.ReferenceBounds.card_perm_fin_four <;> assumption
theorem cubePermMean_const (hodd : Odd F.blockSide) (q : ℍ[ℝ]) : cubePermMean F.blockSide (fun _ _ => q) = q := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  unfold cubePermMean
  simp only [Finset.sum_const, card_perm_fin_four, card_centredCube hodd]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  have : 1 / (24 * (F.blockSide : ℝ) ^ 4) * ((F.blockSide ^ 4 : ℕ) : ℝ) * ((24 : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp
  rw [this, one_smul]
theorem cubePermMean_of_offset (hodd : Odd F.blockSide) (g : Lattice4 → ℍ[ℝ]) :
    cubePermMean F.blockSide (fun h _ => g h) = (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide, g h := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  unfold cubePermMean
  simp only [Finset.sum_const, card_perm_fin_four]
  simp only [← Nat.cast_smul_eq_nsmul ℝ]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  push_cast
  field_simp
theorem cubePermMean_real_of_offset (hodd : Odd F.blockSide) (g : Lattice4 → ℝ) :
    (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), g h =
      (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, g h := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  simp only [Finset.sum_const, card_perm_fin_four, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc]
  congr 1
  push_cast
  field_simp
theorem cubePermMean_sub (L : ℕ) (g g' : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) :
    cubePermMean L (fun h π => g h π - g' h π) = cubePermMean L g - cubePermMean L g' := by
  unfold cubePermMean
  simp only [Finset.sum_sub_distrib, smul_sub]
theorem norm_cubePermMean_le (hodd : Odd F.blockSide) {g : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]}
    {b : Lattice4 → ℝ} (h : ∀ x ∈ centredCube F.blockSide, ∀ π, ‖g x π‖ ≤ b x) :
    ‖cubePermMean F.blockSide g‖ ≤ (1 / (F.blockSide : ℝ) ^ 4) * ∑ x ∈ centredCube F.blockSide, b x := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  rw [← cubePermMean_real_of_offset hodd]
  unfold cubePermMean
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => h x hx π)
theorem mul_cubePermMean (q : ℍ[ℝ]) (L : ℕ) (g : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) :
    q * cubePermMean L g = cubePermMean L (fun h π => q * g h π) := by
  unfold cubePermMean
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum]
theorem adjointAction_cubePermMean (a : UnitQuaternion) (L : ℕ) (g : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) :
    adjointAction a (cubePermMean L g) = cubePermMean L (fun h π => adjointAction a (g h π)) := by
  unfold cubePermMean
  rw [adjointAction_apply_smul, adjointAction_apply_sum]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [adjointAction_apply_sum]
theorem pureComponent_cubePermMean (L : ℕ) (g : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) :
    pureComponent (cubePermMean L g) = cubePermMean L (fun h π => pureComponent (g h π)) := by
  unfold cubePermMean
  rw [pureComponent_smul, pureComponent_sum]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [pureComponent_sum]
theorem polarUnit_coe_mul_left (g : UnitQuaternion) {C : ℍ[ℝ]} (hC : C ≠ 0) :
    polarUnit ((g : ℍ[ℝ]) * C) = g * polarUnit C := by apply _root_.YangMills.Construction.BlockAverages.PinnedGaugeVariation.polarUnit_coe_mul <;> assumption
set_option maxHeartbeats 2000000 in
theorem generatorNearBlockMean : generatorNearBlockMeanStatement := by
  intro F j Γ X R κ f fr y t E hodd ht0 ht hE0 hc hκ hR hf
  have hLpos : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  set d := refineSite y with hd
  let x : Lattice4 → F.Site j := fun h => d + siteOfCoords j h
  let Rl : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion := fun h π => pathHolonomy R d (axisPath h π)
  let e : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion := fun h π =>
    pathHolonomy X d (axisPath h π) * (Γ (x h))⁻¹ * (Rl h π)⁻¹
  let c : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion := fun h π =>
    pathHolonomy (gaugeTransform Γ X) d (axisPath h π) * (Rl h π)⁻¹
  have hce : ∀ h π, c h π = Γ d * e h π := by
    intro h π
    show pathHolonomy (gaugeTransform Γ X) d (axisPath h π) * _ = _
    rw [pathHolonomy_gaugeTransform_of_base, (axisPath_spec h π).2]
    simp only [e, x, mul_assoc]
  set C := gaugedPathAverage Γ X R y with hC
  set A := relativePathAverage (gaugeTransform Γ X) R y with hA
  have hAc : A = cubePermMean F.blockSide (fun h π => ((c h π : UnitQuaternion) : ℍ[ℝ])) := rfl
  have hAC : A = (Γ d : ℍ[ℝ]) * C := relativePathAverage_gaugeTransform Γ X R y
  have hA1 : ‖A - 1‖ ≤ t := by
    have e1 : A - 1 = cubePermMean F.blockSide (fun h π => ((c h π : UnitQuaternion) : ℍ[ℝ]) - 1) := by
      rw [cubePermMean_sub, cubePermMean_const hodd, ← hAc]
    rw [e1]
    have h1 := norm_cubePermMean_le hodd (g := fun h π => ((c h π : UnitQuaternion) : ℍ[ℝ]) - 1)
      (b := fun _ => t) (fun h hh π => hc h hh π)
    refine le_trans h1 (le_of_eq ?_)
    rw [Finset.sum_const, card_centredCube hodd, nsmul_eq_mul]
    push_cast
    field_simp
  have hnA : ‖A‖ = ‖C‖ := by rw [hAC, norm_mul, norm_coe_unitQuaternion, one_mul]
  set r := ‖C‖ with hr
  have hr1 : 1 - t ≤ r := by
    have h1 := norm_sub_norm_le (1 : ℍ[ℝ]) A
    rw [norm_one, hnA, norm_sub_rev] at h1
    linarith
  have hr2 : r ≤ 1 + t := by
    have h1 := norm_add_le (A - 1) 1
    rw [sub_add_cancel, norm_one, hnA] at h1
    linarith
  have hr0 : 7 / 8 ≤ r := by linarith
  have hC0 : C ≠ 0 := fun h0 => by
    rw [hr, h0, norm_zero] at hr0
    norm_num at hr0
  have hA0 : A ≠ 0 := fun h0 => by
    rw [hAC] at h0
    exact hC0 ((mul_eq_zero.1 h0).resolve_left (fun h1 => by
      have := norm_coe_unitQuaternion (Γ d)
      rw [h1, norm_zero] at this
      norm_num at this))
  have hre : 0 ≤ A.re := by
    have h1 : |(A - 1).re| ≤ ‖A - 1‖ := by
      have h2 : (A - 1).re ^ 2 ≤ ‖A - 1‖ ^ 2 := by
        have e2 : ‖A - 1‖ ^ 2 = Quaternion.normSq (A - 1) := by
          rw [Quaternion.normSq_eq_norm_mul_self]
          ring
        rw [e2, Quaternion.normSq_def']
        nlinarith [sq_nonneg (A - 1).imI, sq_nonneg (A - 1).imJ, sq_nonneg (A - 1).imK]
      exact abs_le_of_sq_le_sq h2 (norm_nonneg _)
    have h3 := (abs_le.1 (h1.trans hA1)).1
    simp only [Quaternion.re_sub, Quaternion.re_one] at h3
    linarith
  set u0 := polarUnit C with hu0
  set uA := polarUnit A with huA
  have huu : uA = Γ d * u0 := by rw [huA, hAC, polarUnit_coe_mul_left _ hC0]
  have huA1 : normSubOne uA ≤ 3 * t := by
    have h1 := norm_polarUnit_sub_one_le hre hA0
    have h2 : ‖pureComponent A‖ ≤ t := by
      have e2 : pureComponent A = pureComponent (A - 1) := by
        rw [pureComponent_sub, pureComponent_one, sub_zero]
      rw [e2]
      exact (norm_pureComponent_le _).trans hA1
    have h3 : 2 * ‖pureComponent A‖ / ‖A‖ ≤ 3 * t := by
      rw [hnA, div_le_iff₀ (by linarith)]
      nlinarith
    exact h1.trans h3
  let b : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion := fun h π => u0⁻¹ * e h π
  have hb : ∀ h ∈ centredCube F.blockSide, ∀ π, normSubOne (b h π) ≤ 4 * t := by
    intro h hh π
    have e1 : b h π = uA⁻¹ * c h π := by
      show u0⁻¹ * e h π = _
      rw [huu, hce]
      group
    rw [e1]
    refine (normSubOne_mul_le _ _).trans ?_
    rw [normSubOne_inv]
    have := hc h hh π
    have h2 : normSubOne (c h π) ≤ t := this
    linarith
  let w : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π => adjointAction (Rl h π) (f (x h))
  have hwre : ∀ h ∈ centredCube F.blockSide, ∀ π, pureComponent (w h π) = w h π := by
    intro h hh π
    show pureComponent (adjointAction (Rl h π) (f (x h))) = _
    rw [pureComponent_adjointAction, pureComponent_of_re_eq_zero (hf h hh)]
  have hwn : ∀ h π, ‖w h π‖ = ‖f (x h)‖ := fun h π => norm_adjointAction _ _
  have hGm : pathAveragedGenerator Γ X R f y =
      cubePermMean F.blockSide (fun h π => ((e h π : UnitQuaternion) : ℍ[ℝ]) * w h π) := by
    unfold pathAveragedGenerator cubePermMean
    congr 1
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_
    have hinv : (((Rl h π)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((Rl h π : UnitQuaternion) : ℍ[ℝ]) = 1 := by
      rw [← Submonoid.coe_mul, inv_mul_cancel]
      rfl
    show _ = ((pathHolonomy X d (axisPath h π) * (Γ (x h))⁻¹ * (Rl h π)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
      (((Rl h π : UnitQuaternion) : ℍ[ℝ]) * f (x h) * (((Rl h π)⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    have e2 : ((pathHolonomy X d (axisPath h π) * (Γ (x h))⁻¹ * (Rl h π)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
        ((pathHolonomy X d (axisPath h π) * (Γ (x h))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          (((Rl h π)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := rfl
    rw [e2]
    calc _ = ((pathHolonomy X d (axisPath h π) * (Γ (x h))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          ((((Rl h π)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((Rl h π : UnitQuaternion) : ℍ[ℝ])) * f (x h) *
            (((Rl h π)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
          rw [hinv, mul_one]
      _ = _ := by simp only [mul_assoc]
  let ρ : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    pureComponent ((((b h π : UnitQuaternion) : ℍ[ℝ]) - 1) * w h π)
  have hρ : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ρ h π‖ ≤ 4 * t * ‖f (x h)‖ := by
    intro h hh π
    refine (norm_pureComponent_le _).trans ?_
    rw [norm_mul, hwn]
    exact mul_le_mul_of_nonneg_right (hb h hh π) (norm_nonneg _)
  set P := pureComponent (((u0⁻¹ : UnitQuaternion) : ℍ[ℝ]) * pathAveragedGenerator Γ X R f y) with hP
  have hPv : P = cubePermMean F.blockSide (fun h π => w h π + ρ h π) := by
    rw [hP, hGm, mul_cubePermMean, pureComponent_cubePermMean]
    unfold cubePermMean
    congr 1
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
    have e1 : ((u0⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (((e h π : UnitQuaternion) : ℍ[ℝ]) * w h π) =
        w h π + (((b h π : UnitQuaternion) : ℍ[ℝ]) - 1) * w h π := by
      show _ = w h π + ((((u0⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((e h π : UnitQuaternion) : ℍ[ℝ])) - 1) * w h π
      noncomm_ring
    show pureComponent (((u0⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (((e h π : UnitQuaternion) : ℍ[ℝ]) * w h π)) =
      w h π + ρ h π
    rw [e1, pureComponent_add, hwre h hh π]
  set ψ := (fr d)⁻¹ with hψ
  let g : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion := fun h π => ψ * κ * Rl h π * fr (x h)
  let ξt : Lattice4 → ℍ[ℝ] := fun h => adjointAction (fr (x h))⁻¹ (f (x h))
  have hξn : ∀ h, ‖ξt h‖ = ‖f (x h)‖ := fun h => norm_adjointAction _ _
  have hgw : ∀ h π, adjointAction (ψ * κ) (w h π) = adjointAction (g h π) (ξt h) := by
    intro h π
    show adjointAction (ψ * κ) (adjointAction (Rl h π) (f (x h))) =
      adjointAction (ψ * κ * Rl h π * fr (x h)) (adjointAction (fr (x h))⁻¹ (f (x h)))
    rw [adjointAction_mul_apply (ψ * κ * Rl h π), adjointAction_apply_inv_apply, adjointAction_mul_apply (ψ * κ)]
  have hg : ∀ h ∈ centredCube F.blockSide, ∀ π, normSubOne (g h π) ≤ 2 * E := by
    intro h hh π
    have e1 : g h π = (ψ * κ * ψ⁻¹) * (ψ * Rl h π * fr (x h)) := by
      show ψ * κ * Rl h π * fr (x h) = _
      group
    rw [e1]
    refine (normSubOne_mul_le _ _).trans ?_
    rw [normSubOne_conj]
    have h1 := hR h hh π
    have h2 : normSubOne (ψ * Rl h π * fr (x h)) ≤ E := h1
    have h3 : normSubOne κ ≤ E := hκ
    linarith
  set M := (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, ‖f (x h)‖ with hM
  have hcoef : ∀ a : ℝ, (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, a * ‖f (x h)‖ = a * M := by
    intro a
    rw [hM, ← Finset.mul_sum]
    ring
  set Q := adjointAction (ψ * κ) P with hQ
  have hQv : Q = cubePermMean F.blockSide
      (fun h π => adjointAction (g h π) (ξt h) + adjointAction (ψ * κ) (ρ h π)) := by
    rw [hQ, hPv, adjointAction_cubePermMean]
    unfold cubePermMean
    congr 1
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_
    show adjointAction (ψ * κ) (w h π + ρ h π) = _
    rw [adjointAction_apply_add, hgw]
  have hQn : ‖Q‖ ≤ 3 / 2 * M := by
    rw [hQv]
    have h1 := norm_cubePermMean_le hodd
      (g := fun h π => adjointAction (g h π) (ξt h) + adjointAction (ψ * κ) (ρ h π))
      (b := fun h => 3 / 2 * ‖f (x h)‖) (fun h hh π => by
        refine (norm_add_le _ _).trans ?_
        rw [norm_adjointAction, hξn, norm_adjointAction]
        have := hρ h hh π
        have h3 : 0 ≤ ‖f (x h)‖ := norm_nonneg _
        nlinarith)
    rwa [hcoef] at h1
  set mξ := (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide, ξt h with hmξ
  have hmξv : mξ = cubePermMean F.blockSide (fun h _ => ξt h) := (cubePermMean_of_offset hodd ξt).symm
  have hD : ‖Q - mξ‖ ≤ (4 * E + 4 * t) * M := by
    rw [hQv, hmξv, ← cubePermMean_sub]
    have h1 := norm_cubePermMean_le hodd
      (g := fun h π => adjointAction (g h π) (ξt h) + adjointAction (ψ * κ) (ρ h π) - ξt h)
      (b := fun h => (4 * E + 4 * t) * ‖f (x h)‖) (fun h hh π => by
        have e1 : adjointAction (g h π) (ξt h) + adjointAction (ψ * κ) (ρ h π) - ξt h =
            (adjointAction (g h π) (ξt h) - ξt h) + adjointAction (ψ * κ) (ρ h π) := by abel
        rw [e1]
        refine (norm_add_le _ _).trans ?_
        rw [norm_adjointAction]
        have h2 := norm_adjointAction_apply_sub_le (g h π) (ξt h)
        rw [hξn] at h2
        have h3 : ‖((g h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * E := hg h hh π
        have h4 := hρ h hh π
        have h5 : 0 ≤ ‖f (x h)‖ := norm_nonneg _
        nlinarith)
    rwa [hcoef] at h1
  have hgen : adjointAction ψ (coarseGenerator Γ X R κ f y) = (1 / r) • Q := by
    unfold coarseGenerator
    rw [adjointAction_apply_smul, hQ, adjointAction_mul_apply]
  have hr' : 0 < r := by linarith
  have hfin : adjointAction ψ (coarseGenerator Γ X R κ f y) - mξ = (1 / r - 1) • Q + (Q - mξ) := by
    rw [hgen, sub_smul, one_smul]
    abel
  show ‖adjointAction ψ (coarseGenerator Γ X R κ f y) - mξ‖ ≤ _
  rw [hfin]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h1 : |1 / r - 1| ≤ 8 / 7 * t := by
    have e1 : 1 / r - 1 = (1 - r) / r := by field_simp
    rw [e1, abs_div, abs_of_pos hr', div_le_iff₀ hr']
    have h2 : |1 - r| ≤ t := by
      rw [abs_le]
      constructor <;> linarith
    nlinarith
  have h2 : |1 / r - 1| * ‖Q‖ ≤ (8 / 7 * t) * (3 / 2 * M) :=
    mul_le_mul h1 hQn (norm_nonneg _) (by positivity)
  have h3 : 0 ≤ t * M := by positivity
  have h4 : 0 ≤ E * M := by positivity
  nlinarith
end YangMills.Construction.BlockAverages.NearBlockMean
end
