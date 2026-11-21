import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuplesProof
import YangMills.Construction.Continuum.FiniteSeminormsOfRapidlyDecreasingFunctions
import YangMills.Construction.Continuum.SupremaOfASmoothFunctionAndTheVectorSpaceOfSchwartzFunctions
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace Seminorms
variable {n : ℕ}
theorem setOf_order_le_finite (q : ℕ) : {α : MultiIndex n | α.order ≤ q}.Finite := by apply _root_.YangMills.Construction.ConfigSpace.TensorSupport.finite_setOf_order_le <;> assumption
theorem decaySeminorm_lt_top (k q : ℕ) {φ : Config n → ℂ} (h : φ ∈ schwartzSet n) :
    decaySeminorm k q φ < ⊤ := by
  have hs : (setOf_order_le_finite (n := n) q).toFinset.sup
      (fun α => multiIndexDecaySup k α φ) < ⊤ :=
    (Finset.sup_lt_iff bot_lt_top).2 fun α _ => h.2 k α
  refine lt_of_le_of_lt (iSup₂_le fun α hα => ?_) hs
  exact Finset.le_sup (f := fun α => multiIndexDecaySup k α φ)
    ((setOf_order_le_finite q).mem_toFinset.2 hα)
theorem one_add_euclidNorm_pow_nonneg (k : ℕ) (x : Config n) : 0 ≤ (1 + euclidNorm x) ^ k := by
  have h : 0 ≤ euclidNorm x := Real.sqrt_nonneg _
  positivity
theorem one_add_euclidNorm_sq_rpow_nonneg (p : ℕ) (x : Config n) :
    0 ≤ (1 + euclidNorm x ^ 2) ^ ((p : ℝ) / 2) := by
  positivity
section Terms
variable (hsup : SchwartzSupremaStatement) (hn : 1 ≤ n)
include hsup hn
theorem iteratedPartial_smul (α : MultiIndex n) (c : ℂ) {φ : Config n → ℂ}
    (h : ContDiff ℝ ∞ φ) : iteratedPartial α (c • φ) = c • iteratedPartial α φ := by
  simpa only [zero_smul, add_zero] using (hsup n hn).2.1 φ φ h h c 0 0 0 le_rfl |>.2.2 α
theorem iteratedPartial_add (α : MultiIndex n) {φ ψ : Config n → ℂ}
    (h : ContDiff ℝ ∞ φ) (h' : ContDiff ℝ ∞ ψ) :
    iteratedPartial α (φ + ψ) = iteratedPartial α φ + iteratedPartial α ψ := by
  simpa only [one_smul] using (hsup n hn).2.1 φ ψ h h' 1 1 0 0 le_rfl |>.2.2 α
theorem ofReal_weighted_smul (w : ℝ) (α : MultiIndex n) (c : ℂ) {φ : Config n → ℂ}
    (h : ContDiff ℝ ∞ φ) (x : Config n) :
    ENNReal.ofReal (w * ‖iteratedPartial α (c • φ) x‖) =
      ENNReal.ofReal ‖c‖ * ENNReal.ofReal (w * ‖iteratedPartial α φ x‖) := by
  rw [iteratedPartial_smul hsup hn α c h, Pi.smul_apply, norm_smul,
    ← ENNReal.ofReal_mul (norm_nonneg c)]
  congr 1
  ring
theorem ofReal_weighted_add_le {w : ℝ} (hw : 0 ≤ w) (α : MultiIndex n) {φ ψ : Config n → ℂ}
    (h : ContDiff ℝ ∞ φ) (h' : ContDiff ℝ ∞ ψ) (x : Config n) :
    ENNReal.ofReal (w * ‖iteratedPartial α (φ + ψ) x‖) ≤
      ENNReal.ofReal (w * ‖iteratedPartial α φ x‖) +
        ENNReal.ofReal (w * ‖iteratedPartial α ψ x‖) := by
  rw [iteratedPartial_add hsup hn α h h', Pi.add_apply,
    ← ENNReal.ofReal_add (mul_nonneg hw (norm_nonneg _)) (mul_nonneg hw (norm_nonneg _)), ← mul_add]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (norm_add_le _ _) hw)
theorem decaySeminorm_smul (k q : ℕ) (c : ℂ) {φ : Config n → ℂ} (h : ContDiff ℝ ∞ φ) :
    decaySeminorm k q (c • φ) = ENNReal.ofReal ‖c‖ * decaySeminorm k q φ := by
  unfold decaySeminorm
  simp only [ENNReal.mul_iSup]
  exact iSup_congr fun α => iSup_congr fun _ => iSup_congr fun x =>
    ofReal_weighted_smul hsup hn _ α c h x
theorem schwartzSeminorm_smul (p : ℕ) (c : ℂ) {φ : Config n → ℂ} (h : ContDiff ℝ ∞ φ) :
    schwartzSeminorm p (c • φ) = ENNReal.ofReal ‖c‖ * schwartzSeminorm p φ := by
  unfold schwartzSeminorm
  simp only [ENNReal.mul_iSup]
  exact iSup_congr fun x => iSup_congr fun α => iSup_congr fun _ =>
    ofReal_weighted_smul hsup hn _ α c h x
theorem decaySeminorm_add_le (k q : ℕ) {φ ψ : Config n → ℂ} (h : ContDiff ℝ ∞ φ)
    (h' : ContDiff ℝ ∞ ψ) :
    decaySeminorm k q (φ + ψ) ≤ decaySeminorm k q φ + decaySeminorm k q ψ := by
  have hup : ∀ (χ : Config n → ℂ) (α : MultiIndex n), α.order ≤ q → ∀ x,
      ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖iteratedPartial α χ x‖) ≤
        decaySeminorm k q χ :=
    fun χ α hα x => le_iSup_of_le α (le_iSup_of_le hα (le_iSup_of_le x le_rfl))
  refine iSup₂_le fun α hα => iSup_le fun x => ?_
  exact (ofReal_weighted_add_le hsup hn (one_add_euclidNorm_pow_nonneg k x) α h h' x).trans
    (add_le_add (hup φ α hα x) (hup ψ α hα x))
theorem schwartzSeminorm_add_le (p : ℕ) {φ ψ : Config n → ℂ} (h : ContDiff ℝ ∞ φ)
    (h' : ContDiff ℝ ∞ ψ) :
    schwartzSeminorm p (φ + ψ) ≤ schwartzSeminorm p φ + schwartzSeminorm p ψ := by
  have hup : ∀ (χ : Config n → ℂ) (x : Config n) (α : MultiIndex n), α.order ≤ p →
      ENNReal.ofReal ((1 + euclidNorm x ^ 2) ^ ((p : ℝ) / 2) * ‖iteratedPartial α χ x‖) ≤
        schwartzSeminorm p χ :=
    fun χ x α hα => le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le hα le_rfl))
  refine iSup_le fun x => iSup₂_le fun α hα => ?_
  exact (ofReal_weighted_add_le hsup hn (one_add_euclidNorm_sq_rpow_nonneg p x) α h h' x).trans
    (add_le_add (hup φ x α hα) (hup ψ x α hα))
end Terms
end Seminorms
open Seminorms in
theorem schwartzSeminormsFinite_holds (hsup : SchwartzSupremaStatement) :
    SchwartzSeminormsFinite := by
  intro n hn k q p
  have hle : ∀ φ ∈ schwartzSet n, schwartzSeminorm p φ ≤ decaySeminorm p p φ :=
    fun φ h => ((hsup n hn).2.2.2.1 φ h.1 p p).1
  refine ⟨fun φ h => ⟨decaySeminorm_lt_top k q h, hle φ h⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact fun φ h => decaySeminorm_lt_top k q h
  · exact fun c φ h => decaySeminorm_smul hsup hn k q c h.1
  · exact fun φ h ψ h' => decaySeminorm_add_le hsup hn k q h.1 h'.1
  · exact fun φ h => lt_of_le_of_lt (hle φ h) (decaySeminorm_lt_top p p h)
  · exact fun c φ h => schwartzSeminorm_smul hsup hn p c h.1
  · exact fun φ h ψ h' => schwartzSeminorm_add_le hsup hn p h.1 h'.1
end YangMills.Construction.ConfigSpace
end
