import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongTheFieldsOfTheTopProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Interpolation BondIntegration Cumulants
  ConvexObservables TorusComparison Estimates CellCounting FamilyNorms SummableBounds
namespace ThirdOrderCovariance
section BallLaws
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ}
theorem ballDensity_eq_zero_of_not_mem {Φ : BondField ι → ℝ} {η : BondField ι} (hη : ¬ (∀ b, ‖η b‖ < ρ)) :
    ballDensity (cutoffFactor ρ p) Φ η = 0 := by apply _root_.YangMills.SharedProofs.p11780 <;> assumption
theorem ballDensity_congr {Φ₁ Φ₂ : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Φ₁ η = Φ₂ η) :
    ballDensity (cutoffFactor ρ p) Φ₁ = ballDensity (cutoffFactor ρ p) Φ₂ := by apply _root_.YangMills.Construction.Interpolation.ExpansionThirdDeriv.ballDensity_congr <;> assumption
theorem ballExpectation_eq_of_ballDensity_eq {Φ₁ Φ₂ : BondField ι → ℝ}
    (h : ballDensity (cutoffFactor ρ p) Φ₁ = ballDensity (cutoffFactor ρ p) Φ₂) (f : BondField ι → ℝ) :
    ballExpectation (cutoffFactor ρ p) Φ₁ f = ballExpectation (cutoffFactor ρ p) Φ₂ f := by apply _root_.YangMills.SharedProofs.p53358 <;> assumption
theorem ballCovariance_eq_of_ballDensity_eq {Φ₁ Φ₂ : BondField ι → ℝ}
    (h : ballDensity (cutoffFactor ρ p) Φ₁ = ballDensity (cutoffFactor ρ p) Φ₂) (f g : BondField ι → ℝ) :
    ballCovariance (cutoffFactor ρ p) Φ₁ f g = ballCovariance (cutoffFactor ρ p) Φ₂ f g := by
  unfold ballCovariance
  simp only [ballExpectation_eq_of_ballDensity_eq h]
theorem hasLocalSize_of_ballDensity_eq {Φ₁ Φ₂ H : BondField ι → ℝ} {Cq : ℕ → ℝ} {x κ a : ℝ} {dZ : ι → ℝ}
    (h : ballDensity (cutoffFactor ρ p) Φ₁ = ballDensity (cutoffFactor ρ p) Φ₂)
    (hs : HasLocalSize ρ (cutoffFactor ρ p) Φ₁ Cq x κ a dZ H) :
    HasLocalSize ρ (cutoffFactor ρ p) Φ₂ Cq x κ a dZ H := by apply _root_.YangMills.Construction.Interpolation.ExpansionThirdDeriv.hasLocalSize_of_ballDensity_eq <;> assumption
theorem isOpen_bondBalls : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.SharedProofs.p5886 <;> assumption
theorem momentBound_congr {Φ f g : BondField ι → ℝ} {q : ℕ} {B : ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → f η = g η)
    (hm : MomentBound (cutoffFactor ρ p) Φ f q B) : MomentBound (cutoffFactor ρ p) Φ g q B := by
  have e : (fun η => |g η| ^ q * ballDensity (cutoffFactor ρ p) Φ η) =
      fun η => |f η| ^ q * ballDensity (cutoffFactor ρ p) Φ η := by
    funext η
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · rw [h η hη]
    · rw [ballDensity_eq_zero_of_not_mem hη]
      simp
  refine ⟨?_, ?_⟩
  · rw [e]
    exact hm.1
  · have h2 := hm.2
    unfold ballExpectation at h2 ⊢
    have e2 : (fun η => (fun η => |g η| ^ q) η * ballDensity (cutoffFactor ρ p) Φ η) =
        fun η => (fun η => |f η| ^ q) η * ballDensity (cutoffFactor ρ p) Φ η := e
    rw [e2]
    exact h2
theorem hasLocalSize_congr {Φ f g : BondField ι → ℝ} {Cq : ℕ → ℝ} {x κ a : ℝ} {dZ : ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → f η = g η)
    (hs : HasLocalSize ρ (cutoffFactor ρ p) Φ Cq x κ a dZ f) :
    HasLocalSize ρ (cutoffFactor ρ p) Φ Cq x κ a dZ g := by
  obtain ⟨h1, H₀, h2⟩ := hs
  have ev : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → f =ᶠ[nhds η] g := fun η hη => by
    filter_upwards [(isOpen_bondBalls (ι := ι) (ρ := ρ)).mem_nhds hη] with ζ hζ
    exact h ζ hζ
  refine ⟨fun η hη => (h1 η hη).congr_of_eventuallyEq (ev η hη).symm, H₀, fun q hq => ⟨?_, fun b => ?_⟩⟩
  · exact momentBound_congr (f := fun η => f η - H₀) (g := fun η => g η - H₀)
      (fun η hη => by rw [h η hη]) (h2 q hq).1
  · refine momentBound_congr (f := bondGradNorm f b) (g := bondGradNorm g b) (fun η hη => ?_) ((h2 q hq).2 b)
    unfold bondGradNorm
    rw [(ev η hη).fderiv_eq]
theorem ballCovariance_of_average {α : Type} [Fintype α] {Ψ A D : BondField ι → ℝ} {f : α → BondField ι → ℝ}
    (hD : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → D η = (1 / 6) * ∑ π, f π η)
    (i1 : ∀ π, Integrable fun η => f π η * ballDensity (cutoffFactor ρ p) Ψ η)
    (i2 : ∀ π, Integrable fun η => A η * f π η * ballDensity (cutoffFactor ρ p) Ψ η) :
    ballCovariance (cutoffFactor ρ p) Ψ A D = (1 / 6) * ∑ π, ballCovariance (cutoffFactor ρ p) Ψ A (f π) := by
  set W := ballDensity (cutoffFactor ρ p) Ψ with hW
  have e1 : ballExpectation (cutoffFactor ρ p) Ψ D =
      (1 / 6) * ∑ π, ballExpectation (cutoffFactor ρ p) Ψ (f π) := by
    unfold ballExpectation
    rw [← hW]
    have e : (fun η => D η * W η) = fun η => (1 / 6) * ∑ π, f π η * W η := by
      funext η
      by_cases hη : ∀ b, ‖η b‖ < ρ
      · rw [hD η hη, mul_assoc, Finset.sum_mul]
      · have : W η = 0 := ballDensity_eq_zero_of_not_mem hη
        simp [this]
    rw [e, integral_const_mul, integral_finset_sum _ fun π _ => i1 π, mul_div_assoc, Finset.sum_div]
  have e2 : ballExpectation (cutoffFactor ρ p) Ψ (fun η => A η * D η) =
      (1 / 6) * ∑ π, ballExpectation (cutoffFactor ρ p) Ψ (fun η => A η * f π η) := by
    unfold ballExpectation
    rw [← hW]
    have e : (fun η => A η * D η * W η) = fun η => (1 / 6) * ∑ π, A η * f π η * W η := by
      funext η
      by_cases hη : ∀ b, ‖η b‖ < ρ
      · rw [hD η hη]
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun π _ => by ring
      · have : W η = 0 := ballDensity_eq_zero_of_not_mem hη
        simp [this]
    rw [e, integral_const_mul, integral_finset_sum _ fun π _ => i2 π, mul_div_assoc, Finset.sum_div]
  unfold ballCovariance
  rw [e1, e2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
theorem contDiffOn_fieldDerivative {A : BondField ι → ℝ} {z : BondVector → BondVector} (b : ι)
    (hz : ContDiff ℝ 1 z) (hA : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ContDiffAt ℝ 2 A η) :
    ContDiffOn ℝ 1 (fieldDerivative b z A) {η | ∀ b, ‖η b‖ < ρ} := by
  have h2 : ContDiffOn ℝ 2 A {η : BondField ι | ∀ b, ‖η b‖ < ρ} := fun η hη =>
    (hA η hη).contDiffWithinAt
  have h3 : ContDiffOn ℝ 1 (fderiv ℝ A) {η : BondField ι | ∀ b, ‖η b‖ < ρ} :=
    h2.fderiv_of_isOpen isOpen_bondBalls (by norm_num)
  have h4 : ContDiff ℝ 1 fun η : BondField ι => bondVariation b (z (η b)) := by
    have e : (fun η : BondField ι => bondVariation b (z (η b))) =
        fun η => ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b (z (η b)) := by
      funext η
      rfl
    rw [e]
    exact (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b).contDiff.comp
      (hz.comp (contDiff_apply ℝ BondVector b))
  exact h3.clm_apply h4.contDiffOn
end BallLaws
section CellDistances
variable {F : BlockFrame}
theorem cellSupDist_comm (a b : F.Cell) : cellSupDist a b = cellSupDist b a := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_triangle (a b c : F.Cell) : cellSupDist a c ≤ cellSupDist a b + cellSupDist b c := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem cellSupDist_self (a : F.Cell) : cellSupDist a a = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellSupDist_le_cellsDiameter {M : ℕ} (Z : Fin M → F.Cell) (i j : Fin M) :
    cellSupDist (Z i) (Z j) ≤ cellsDiameter Z := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.cellSupDist_le_cellsDiameter <;> assumption
theorem bondSpan_le_of_perm {Y : F.Cell} {c : Fin 3 → F.Site F.top × Fin 4} (π : Equiv.Perm (Fin 3)) {N : ℕ}
    (h0 : cellSupDist Y (c (π 0)).1 ≤ N) (h1 : cellSupDist Y (c (π 1)).1 ≤ N)
    (h2 : cellSupDist Y (c (π 2)).1 ≤ N)
    (h01 : cellSupDist (c (π 0)).1 (c (π 1)).1 ≤ N) (h02 : cellSupDist (c (π 0)).1 (c (π 2)).1 ≤ N)
    (h12 : cellSupDist (c (π 1)).1 (c (π 2)).1 ≤ N) : bondSpan Y c ≤ N := by
  unfold bondSpan
  have hY : ∀ l, siteSupDist Y (c l).1 ≤ N := by
    intro l
    obtain ⟨k, rfl⟩ := π.surjective l
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by
      revert k
      decide
    rcases hk with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  have hc : ∀ l l', siteSupDist (c l).1 (c l').1 ≤ N := by
    intro l l'
    obtain ⟨k, rfl⟩ := π.surjective l
    obtain ⟨k', rfl⟩ := π.surjective l'
    have s1 : siteSupDist (c (π 0)).1 (c (π 1)).1 ≤ N := h01
    have s2 : siteSupDist (c (π 0)).1 (c (π 2)).1 ≤ N := h02
    have s3 : siteSupDist (c (π 1)).1 (c (π 2)).1 ≤ N := h12
    have t : ∀ a b : F.Cell, siteSupDist a b = siteSupDist b a := cellSupDist_comm
    have z : ∀ a : F.Cell, siteSupDist a a = 0 := cellSupDist_self
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by
      revert k
      decide
    have hk' : k' = 0 ∨ k' = 1 ∨ k' = 2 := by
      revert k'
      decide
    rcases hk with rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl <;>
      first
        | (rw [z]; exact Nat.zero_le _)
        | exact s1
        | exact s2
        | exact s3
        | (rw [t]; exact s1)
        | (rw [t]; exact s2)
        | (rw [t]; exact s3)
  exact max_le (Finset.sup_le fun l _ => hY l)
    (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => hc l l')
theorem siteSupDist_le_bondSpan {k : ℕ} (Z : F.Cell) (c : Fin k → F.Site F.top × Fin 4) (l l' : Fin k) :
    siteSupDist Z (c l).1 ≤ bondSpan Z c ∧ siteSupDist (c l).1 (c l').1 ≤ bondSpan Z c := by
  unfold bondSpan
  refine ⟨?_, ?_⟩
  · exact le_max_of_le_left
      (Finset.le_sup (f := fun l : Fin k => siteSupDist Z (c l).1) (Finset.mem_univ l))
  · refine le_max_of_le_right ?_
    exact (Finset.le_sup (f := fun l' : Fin k => siteSupDist (c l).1 (c l').1) (Finset.mem_univ l')).trans
      (Finset.le_sup (f := fun l : Fin k => Finset.univ.sup fun l' : Fin k => siteSupDist (c l).1 (c l').1)
        (Finset.mem_univ l))
theorem cellSupDist_le_bondSpan_pair {Z : F.Cell} {a b : F.Site F.top × Fin 4} :
    cellSupDist Z a.1 ≤ bondSpan Z ![a, b] ∧ cellSupDist Z b.1 ≤ bondSpan Z ![a, b] ∧
      cellSupDist a.1 b.1 ≤ bondSpan Z ![a, b] := by
  have h0 := siteSupDist_le_bondSpan Z ![a, b] 0 1
  have h1 := siteSupDist_le_bondSpan Z ![a, b] 1 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact ⟨h0.1, h1.1, h0.2⟩
theorem cellSupDist_le_bondSpan_three {Z : F.Cell} {c : Fin 3 → F.Site F.top × Fin 4} (l l' : Fin 3) :
    cellSupDist Z (c l).1 ≤ bondSpan Z c ∧ cellSupDist (c l).1 (c l').1 ≤ bondSpan Z c :=
  siteSupDist_le_bondSpan Z c l l'
theorem bondSpan_le_triangle {Y Z B : F.Cell} {c : Fin 3 → F.Site F.top × Fin 4} (π : Equiv.Perm (Fin 3)) :
    bondSpan Y c ≤ cellsDiameter ![Y, Z, B] + bondSpan Z ![c (π 1), c (π 2)] + cellSupDist B (c (π 0)).1 ∧
    bondSpan Y c ≤ cellsDiameter ![Y, Z] + bondSpan Z ![c (π 1), c (π 2)] + cellSupDist Y B +
      cellSupDist B (c (π 0)).1 ∧
    bondSpan Y c ≤ cellsDiameter ![Y, Z] + bondSpan Z c := by
  obtain ⟨a1, a2, a3⟩ := cellSupDist_le_bondSpan_pair (Z := Z) (a := c (π 1)) (b := c (π 2))
  have dYZ : cellSupDist Y Z ≤ cellsDiameter ![Y, Z, B] := cellSupDist_le_cellsDiameter ![Y, Z, B] 0 1
  have dYB : cellSupDist Y B ≤ cellsDiameter ![Y, Z, B] := cellSupDist_le_cellsDiameter ![Y, Z, B] 0 2
  have dZB : cellSupDist B Z ≤ cellsDiameter ![Y, Z, B] := cellSupDist_le_cellsDiameter ![Y, Z, B] 2 1
  have eYZ : cellSupDist Y Z ≤ cellsDiameter ![Y, Z] := cellSupDist_le_cellsDiameter ![Y, Z] 0 1
  have tr := fun a b c' => cellSupDist_triangle (F := F) a b c'
  have sy := fun a b => cellSupDist_comm (F := F) a b
  refine ⟨?_, ?_, ?_⟩
  · refine bondSpan_le_of_perm π ?_ ?_ ?_ ?_ ?_ ?_
    · have := tr Y B (c (π 0)).1
      omega
    · have := tr Y Z (c (π 1)).1
      omega
    · have := tr Y Z (c (π 2)).1
      omega
    · have h1 := tr (c (π 0)).1 B (c (π 1)).1
      have h2 := tr B Z (c (π 1)).1
      have h3 := sy (c (π 0)).1 B
      omega
    · have h1 := tr (c (π 0)).1 B (c (π 2)).1
      have h2 := tr B Z (c (π 2)).1
      have h3 := sy (c (π 0)).1 B
      omega
    · omega
  · refine bondSpan_le_of_perm π ?_ ?_ ?_ ?_ ?_ ?_
    · have := tr Y B (c (π 0)).1
      omega
    · have := tr Y Z (c (π 1)).1
      omega
    · have := tr Y Z (c (π 2)).1
      omega
    · have h1 := tr (c (π 0)).1 Y (c (π 1)).1
      have h2 := tr (c (π 0)).1 B Y
      have h3 := tr Y Z (c (π 1)).1
      have h4 := sy (c (π 0)).1 B
      have h5 := sy B Y
      omega
    · have h1 := tr (c (π 0)).1 Y (c (π 2)).1
      have h2 := tr (c (π 0)).1 B Y
      have h3 := tr Y Z (c (π 2)).1
      have h4 := sy (c (π 0)).1 B
      have h5 := sy B Y
      omega
    · omega
  · have b0 := (cellSupDist_le_bondSpan_three (Z := Z) (c := c) (π 0) (π 1))
    have b1 := (cellSupDist_le_bondSpan_three (Z := Z) (c := c) (π 1) (π 2))
    have b2 := (cellSupDist_le_bondSpan_three (Z := Z) (c := c) (π 2) (π 0))
    have b3 := (cellSupDist_le_bondSpan_three (Z := Z) (c := c) (π 0) (π 2))
    refine bondSpan_le_of_perm π ?_ ?_ ?_ ?_ ?_ ?_
    · have := tr Y Z (c (π 0)).1
      omega
    · have := tr Y Z (c (π 1)).1
      omega
    · have := tr Y Z (c (π 2)).1
      omega
    · have := b0.2
      omega
    · have := b3.2
      omega
    · have := b1.2
      omega
end CellDistances
theorem exp_mul_three_le {a b c d e f : ℝ} (h : a + b + c ≤ d + e + f) :
    Real.exp a * Real.exp b * Real.exp c ≤ Real.exp d * (Real.exp e * Real.exp f) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith
theorem exp_mul_two_le {a b e f : ℝ} (h : a + b ≤ e + f) :
    Real.exp a * Real.exp b ≤ Real.exp e * Real.exp f := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  exact h
theorem siteTerm_le {Tn cA cH c α β E₃ xi sx S₂ Q Sw e2 e3 Ee e56 : ℝ} (hTn : 0 ≤ Tn) (hcA : 0 ≤ cA)
    (hcH : 0 ≤ cH) (hc : 0 ≤ c) (hα : 0 < α) (hβ : 0 ≤ β) (hE₃ : 0 ≤ E₃) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hxs : xi * sx = 1) (hS₂ : 0 ≤ S₂) (he56 : 0 ≤ e56) (hSw : 0 ≤ Sw) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3)
    (hEe : 0 ≤ Ee)
    (tA : e2 * Q ≤ S₂ * e56) (tB : e2 * Sw * Ee ≤ S₂ * e56) (tC : e3 * Ee ≤ e56) :
    Tn * cA * cH * (cH * α * (c * E₃ * xi * e2) * (c * sx) * Q +
        α * (c * E₃ * xi * e2) * (β / α * Sw) * Ee + α * (c * E₃ * xi * e3) * Ee) ≤
      Tn * cA * cH * E₃ * (cH * c ^ 2 * S₂ + c * S₂ + c) * (α + xi * β) * e56 := by
  have a1 : cH * α * (c * E₃ * xi * e2) * (c * sx) * Q ≤ cH * α * c ^ 2 * E₃ * (S₂ * e56) := by
    have e : cH * α * (c * E₃ * xi * e2) * (c * sx) * Q = cH * α * c ^ 2 * E₃ * (xi * sx) * (e2 * Q) := by
      ring
    rw [e, hxs, mul_one]
    exact mul_le_mul_of_nonneg_left tA (by positivity)
  have a2 : α * (c * E₃ * xi * e2) * (β / α * Sw) * Ee ≤ xi * β * c * E₃ * (S₂ * e56) := by
    have e : α * (c * E₃ * xi * e2) * (β / α * Sw) * Ee = xi * β * c * E₃ * (e2 * Sw * Ee) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left tB (by positivity)
  have a3 : α * (c * E₃ * xi * e3) * Ee ≤ α * c * E₃ * e56 := by
    have e : α * (c * E₃ * xi * e3) * Ee = α * c * E₃ * (xi * (e3 * Ee)) := by ring
    rw [e]
    have h1 : 0 ≤ e3 * Ee := by positivity
    exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left h1 hxi1).trans tC) (by positivity)
  have hsum := add_le_add (add_le_add a1 a2) a3
  have hcoef : 0 ≤ Tn * cA * cH := by positivity
  refine (mul_le_mul_of_nonneg_left hsum hcoef).trans ?_
  have hE : 0 ≤ Tn * cA * cH * E₃ * e56 := by positivity
  have hA : cH * α * c ^ 2 * S₂ + xi * β * c * S₂ + α * c ≤
      (cH * c ^ 2 * S₂ + c * S₂ + c) * (α + xi * β) := by
    have p1 : 0 ≤ cH * c ^ 2 * S₂ * (xi * β) := by positivity
    have p2 : 0 ≤ c * S₂ * α := by positivity
    have p3 : 0 ≤ c * (xi * β) := by positivity
    nlinarith
  have := mul_le_mul_of_nonneg_left hA hE
  nlinarith
section WeightedSums
variable {F : BlockFrame}
theorem weightedSums_le {Y Z : F.Cell} {c₃ : Fin 3 → F.Site F.top × Fin 4} (π : Equiv.Perm (Fin 3))
    {κ S₂ : ℝ} (hκ : 0 < κ)
    (hS₂ : ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(κ / 64 * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤ S₂) :
    Real.exp (-(2 ^ 4 * κ * (bondSpan Z ![c₃ (π 1), c₃ (π 2)] : ℝ))) *
        (∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * κ * bondDistToTopBond b (c₃ (π 0)))) *
          Real.exp (-(κ / 8 * cellsDiameter ![Y, Z, enclosingCell b.1.1]))) ≤
      S₂ * (Real.exp (-(κ / 2 ^ 5 * (bondSpan Y c₃ : ℝ))) *
        Real.exp (-(κ / 64 * (cellSupDist Z Y : ℝ)))) ∧
    Real.exp (-(2 ^ 4 * κ * (bondSpan Z ![c₃ (π 1), c₃ (π 2)] : ℝ))) *
        (∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 4 * κ * bondDistToCell Y b) -
          2 ^ 6 * κ * bondDistToTopBond b (c₃ (π 0)))) *
        Real.exp (-(κ / 8 * cellsDiameter ![Y, Z])) ≤
      S₂ * (Real.exp (-(κ / 2 ^ 5 * (bondSpan Y c₃ : ℝ))) *
        Real.exp (-(κ / 64 * (cellSupDist Z Y : ℝ)))) ∧
    Real.exp (-(2 ^ 4 * κ * (bondSpan Z c₃ : ℝ))) * Real.exp (-(κ / 8 * cellsDiameter ![Y, Z])) ≤
      Real.exp (-(κ / 2 ^ 5 * (bondSpan Y c₃ : ℝ))) * Real.exp (-(κ / 64 * (cellSupDist Z Y : ℝ))) := by
  have hκ0 := hκ.le
  set Dn : ℝ := (bondSpan Y c₃ : ℝ) with hDn
  set σ₂ : ℝ := (bondSpan Z ![c₃ (π 1), c₃ (π 2)] : ℝ) with hσ₂
  set σ₃ : ℝ := (bondSpan Z c₃ : ℝ) with hσ₃
  have hσ₂0 : 0 ≤ σ₂ := Nat.cast_nonneg _
  have hσ₃0 : 0 ≤ σ₃ := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.mul_sum]
    refine (Finset.sum_le_sum (g := fun b : ↥(chordBonds (finiteCells F)) =>
      Real.exp (-(κ / 64 * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) *
        (Real.exp (-(κ / 2 ^ 5 * Dn)) * Real.exp (-(κ / 64 * (cellSupDist Z Y : ℝ))))) fun b _ => ?_).trans ?_
    · set B := enclosingCell b.1.1 with hB
      have g0 := (bondSpan_le_triangle (Y := Y) (Z := Z) (B := B) (c := c₃) π).1
      have g1 : Dn ≤ (cellsDiameter ![Y, Z, B] : ℝ) + σ₂ + bondDistToTopBond b (c₃ (π 0)) := by
        have : ((bondSpan Y c₃ : ℕ) : ℝ) ≤ ((cellsDiameter ![Y, Z, B] +
            bondSpan Z ![c₃ (π 1), c₃ (π 2)] + cellSupDist B (c₃ (π 0)).1 : ℕ) : ℝ) := by
          exact_mod_cast g0
        push_cast at this
        exact this
      have g2 : (cellSupDist Z Y : ℝ) ≤ (cellsDiameter ![Y, Z, B] : ℝ) := by
        exact_mod_cast cellSupDist_le_cellsDiameter ![Y, Z, B] 1 0
      have g3 : (cellSupDist B Y : ℝ) ≤ (cellsDiameter ![Y, Z, B] : ℝ) := by
        exact_mod_cast cellSupDist_le_cellsDiameter ![Y, Z, B] 2 0
      have g4 : 0 ≤ bondDistToTopBond b (c₃ (π 0)) := by
        unfold bondDistToTopBond
        exact Nat.cast_nonneg _
      have k1 := mul_le_mul_of_nonneg_left g1 hκ0
      have k2 := mul_le_mul_of_nonneg_left g2 hκ0
      have k3 := mul_le_mul_of_nonneg_left g3 hκ0
      have k4 := mul_nonneg hκ0 hσ₂0
      have k5 := mul_nonneg hκ0 g4
      have key := exp_mul_three_le (a := -(2 ^ 4 * κ * σ₂))
        (b := -(2 ^ 6 * κ * bondDistToTopBond b (c₃ (π 0))))
        (c := -(κ / 8 * (cellsDiameter ![Y, Z, B] : ℝ))) (d := -(κ / 64 * (cellSupDist B Y : ℝ)))
        (e := -(κ / 2 ^ 5 * Dn)) (f := -(κ / 64 * (cellSupDist Z Y : ℝ))) (by nlinarith)
      calc _ = Real.exp (-(2 ^ 4 * κ * σ₂)) * Real.exp (-(2 ^ 6 * κ * bondDistToTopBond b (c₃ (π 0)))) *
            Real.exp (-(κ / 8 * (cellsDiameter ![Y, Z, B] : ℝ))) := by ring
        _ ≤ _ := key
    · rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hS₂ (by positivity)
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine (Finset.sum_le_sum (g := fun b : ↥(chordBonds (finiteCells F)) =>
      Real.exp (-(κ / 64 * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) *
        (Real.exp (-(κ / 2 ^ 5 * Dn)) * Real.exp (-(κ / 64 * (cellSupDist Z Y : ℝ))))) fun b _ => ?_).trans ?_
    · set B := enclosingCell b.1.1 with hB
      have g0 := (bondSpan_le_triangle (Y := Y) (Z := Z) (B := B) (c := c₃) π).2.1
      have g1 : Dn ≤ (cellsDiameter ![Y, Z] : ℝ) + σ₂ + (cellSupDist Y B : ℝ) +
          bondDistToTopBond b (c₃ (π 0)) := by
        have : ((bondSpan Y c₃ : ℕ) : ℝ) ≤ ((cellsDiameter ![Y, Z] +
            bondSpan Z ![c₃ (π 1), c₃ (π 2)] + cellSupDist Y B + cellSupDist B (c₃ (π 0)).1 : ℕ) : ℝ) := by
          exact_mod_cast g0
        push_cast at this
        exact this
      have g2 : (cellSupDist Z Y : ℝ) ≤ (cellsDiameter ![Y, Z] : ℝ) := by
        exact_mod_cast cellSupDist_le_cellsDiameter ![Y, Z] 1 0
      have g3 : (cellSupDist Y B : ℝ) = (cellSupDist B Y : ℝ) := by
        exact_mod_cast cellSupDist_comm Y B
      have g4 : 0 ≤ bondDistToTopBond b (c₃ (π 0)) := by
        unfold bondDistToTopBond
        exact Nat.cast_nonneg _
      have g5 : (0 : ℝ) ≤ (cellSupDist B Y : ℝ) := Nat.cast_nonneg _
      have hbY : bondDistToCell Y b = (cellSupDist B Y : ℝ) := rfl
      rw [g3] at g1
      have k1 := mul_le_mul_of_nonneg_left g1 hκ0
      have k2 := mul_le_mul_of_nonneg_left g2 hκ0
      have k4 := mul_nonneg hκ0 hσ₂0
      have k5 := mul_nonneg hκ0 g4
      have k6 := mul_nonneg hκ0 g5
      exact exp_mul_three_le (a := -(2 ^ 4 * κ * σ₂))
        (b := -(2 ^ 4 * κ * bondDistToCell Y b) - 2 ^ 6 * κ * bondDistToTopBond b (c₃ (π 0)))
        (c := -(κ / 8 * (cellsDiameter ![Y, Z] : ℝ))) (d := -(κ / 64 * (cellSupDist B Y : ℝ)))
        (e := -(κ / 2 ^ 5 * Dn)) (f := -(κ / 64 * (cellSupDist Z Y : ℝ))) (by rw [hbY]; nlinarith)
    · rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hS₂ (by positivity)
  · have g0 := (bondSpan_le_triangle (Y := Y) (Z := Z) (B := Z) (c := c₃) π).2.2
    have g1 : Dn ≤ (cellsDiameter ![Y, Z] : ℝ) + σ₃ := by
      have : ((bondSpan Y c₃ : ℕ) : ℝ) ≤ ((cellsDiameter ![Y, Z] + bondSpan Z c₃ : ℕ) : ℝ) := by
        exact_mod_cast g0
      push_cast at this
      exact this
    have g2 : (cellSupDist Z Y : ℝ) ≤ (cellsDiameter ![Y, Z] : ℝ) := by
      exact_mod_cast cellSupDist_le_cellsDiameter ![Y, Z] 1 0
    have k1 := mul_le_mul_of_nonneg_left g1 hκ0
    have k2 := mul_le_mul_of_nonneg_left g2 hκ0
    have k4 := mul_nonneg hκ0 hσ₃0
    exact exp_mul_two_le (by nlinarith)
end WeightedSums
def FieldCovarianceBound (N : ℕ) (κ lam Tn : ℝ) : Prop :=
  0 ≤ Tn ∧
      ∀ (F : BlockFrame) (ι : Type) [Fintype ι] [DecidableEq ι] (y : ι → F.Cell) (ρ x : ℝ)
        (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ),
        0 < ρ → 0 < x → IsCutoff ρ p →
        (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ N) →
        IsUniformlyConvexDecaying ρ (x * lam / 4) κ (fun b b' => (cellSupDist (y b) (y b') : ℝ)) Ψ K →
        (∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
        ∀ (A H R : BondField ι → ℝ) (z : ι → BondVector → BondVector) (Y Z : F.Cell)
          (CA CH CS : ℕ → ℝ) (α h h' s : ℝ) (w u : ι → ℝ),
          (∀ q, 0 ≤ CA q) → (∀ q, 0 ≤ CH q) → (∀ q, 0 ≤ CS q) → 0 ≤ α → 0 ≤ h → 0 ≤ h' → 0 ≤ s →
          (∀ b, 0 ≤ w b) → (∀ b, 0 ≤ u b) →
          ContDiffOn ℝ 1 A {η | ∀ b, ‖η b‖ < ρ} → ContDiffOn ℝ 1 H {η | ∀ b, ‖η b‖ < ρ} →
          ContDiffOn ℝ 1 R {η | ∀ b, ‖η b‖ < ρ} →
          (∀ b, ContDiffOn ℝ 1 (fieldDerivative b (z b) A) {η | ∀ b, ‖η b‖ < ρ}) →
          (∀ b, ContDiffOn ℝ 1 (fieldScore p Ψ b (z b)) {η | ∀ b, ‖η b‖ < ρ}) →
          HasLocalSize ρ (cutoffFactor ρ p) Ψ CA x κ α (fun b => (cellSupDist (y b) Y : ℝ)) A →
          (∀ b, HasLocalSize ρ (cutoffFactor ρ p) Ψ CA x κ (α * w b)
            (fun b' => (cellSupDist (y b') Y : ℝ)) (fieldDerivative b (z b) A)) →
          HasLocalSize ρ (cutoffFactor ρ p) Ψ CH x κ h (fun b => (cellSupDist (y b) Z : ℝ)) H →
          HasLocalSize ρ (cutoffFactor ρ p) Ψ CH x κ h' (fun b => (cellSupDist (y b) Z : ℝ)) R →
          (∀ b, HasLocalSize ρ (cutoffFactor ρ p) Ψ CS x κ (s * u b)
            (fun b' => (cellSupDist (y b') (y b) : ℝ)) (fieldScore p Ψ b (z b))) →
          (∀ b, IsBoundedC1BondField (z b)) →
          Integrable (fun η => ((∑ b, fieldDerivative b (z b) H η) + R η) *
            ballDensity (cutoffFactor ρ p) Ψ η) ∧
          Integrable (fun η => A η * ((∑ b, fieldDerivative b (z b) H η) + R η) *
            ballDensity (cutoffFactor ρ p) Ψ η) ∧
          |ballCovariance (cutoffFactor ρ p) Ψ A (fun η => (∑ b, fieldDerivative b (z b) H η) + R η)| ≤
            Tn * sizeConstantSum CA 3 * sizeConstantSum CH 3 *
              (sizeConstantSum CS 3 * α * h * s *
                  (∑ b, u b * Real.exp (-(κ / 8 * cellsDiameter ![Y, Z, y b]))) +
                α * h * (∑ b, w b) * Real.exp (-(κ / 8 * cellsDiameter ![Y, Z])) +
                α * h' * Real.exp (-(κ / 8 * cellsDiameter ![Y, Z])))
set_option maxHeartbeats 2000000 in
theorem thirdOrder_sum_le {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {Cc Cq : ℕ → ℝ} {Tn S₂ S₁ : ℝ} (hCnt : cellBondsCardStatement)
    (hSi : SitesPerCellLePow) (hA : FieldCovarianceBound (4 * T.L ^ 4) T.κ T.chainParams.lam Tn)
    (hP : expansionThirdDerivDecompAt T Cc) (hc : 0 ≤ T.Cs) (hy : 1 ≤ T.coupling) (hodd : Odd T.L) (hE : 1 ≤ T.E)
    (hη : 0 < T.η₃) (hκ : 0 < T.κ) (hσ : 0 < T.σ) (hch : T.chainParams.Admissible T.a T.L)
    (hcut : IsCutoff (T.σ / 64) T.p) (hCc0 : ∀ q, 0 ≤ Cc q) (hCq : ∀ q, 0 ≤ Cq q) (hW20 : 0 ≤ S₂)
    (hW10 : 0 ≤ S₁)
    (hW2 : ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
      (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ 4 * T.L ^ 4) →
      ∀ z : F.Cell, ∑ b, Real.exp (-(T.κ / 64 * (cellSupDist (y b) z : ℝ))) ≤ S₂)
    (hW1 : ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
      (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ T.L ^ 4) →
      ∀ z : F.Cell, ∑ b, Real.exp (-(T.κ / 64 * (cellSupDist (y b) z : ℝ))) ≤ S₁)
    {t : ℕ} {x s α β : ℝ} {φ h₀ : LocalFamily} {F : BlockFrame} {V : F.GaugeField F.top} {Y : F.Cell}
    {c₃ : Fin 3 → F.Site F.top × Fin 4} {X : Fin 3 → imaginaryQuaternions}
    {Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions}
    {A : StepVariable (finiteCells F) → ℝ}
    (hx : T.coupling ≤ x) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hα : 0 < α) (hβ : 0 ≤ β)
    (hφ : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ)
    (hh₀ : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio h₀)
    (hTF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hX : AreUnitVectors X)
    (hTh : ∀ w X' : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X' (Th w X'))
    (hcl : ThirdOrderHypotheses Th s T.a T.chainParams.ρA T.ballRadius x T.κ α β (frameRadius x) T.p Cq V Y c₃ X
      (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V) A) :
    ∑ y' ∈ sitesOfCells (finiteCells F) F.depth,
      |ballCovariance (cutoffFactor T.ballRadius T.p)
          (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V) A
        (fun η => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y' η) V c₃ X)| ≤
      (Tn * sizeConstantSum Cc 3 * (sizeConstantSum Cc 3 * T.Cs ^ 2 * S₂ + T.Cs * S₂ + T.Cs) * S₁) *
        (1 + ∑ q ∈ Finset.range 7, Cq q) * T.energyRatio * (α + x ^ (-(1 / 2 : ℝ)) * β) *
        Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₃)) := by
  obtain ⟨hTn0, hTO'⟩ := hA
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hcut' : IsCutoff T.ballRadius T.p := hcut
  have hlam : 0 < T.chainParams.lam := hch.positivity.2.2.1
  have hx1 : 1 ≤ x := hy.trans hx
  have hx0 : 0 < x := by linarith
  obtain ⟨Ψ, K, z, Hs, Rs, hside, ag, hK, hsl, hfield, hrow⟩ :=
    hP t x s φ h₀ F V c₃ X Th hx hs hs1 hφ hh₀ hTF hV hX hTh
  have hd : ballDensity (cutoffFactor T.ballRadius T.p)
      (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V) =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ := (ballDensity_congr ag).symm
  have hL : Odd F.blockSide := by rw [hTF.1]; exact hodd
  have pos3 : ∀ C₀ : ℕ → ℝ, (∀ q, 0 ≤ C₀ q) → 0 ≤ sizeConstantSum C₀ 3 := by
    intro C₀ h₀
    have : 0 ≤ ∑ q ∈ Finset.range (2 * 3 + 1), C₀ q := Finset.sum_nonneg fun q _ => h₀ q
    unfold sizeConstantSum
    linarith
  obtain ⟨cH, hcHd⟩ : ∃ cH, cH = sizeConstantSum Cc 3 := ⟨_, rfl⟩
  obtain ⟨cA, hcAd⟩ : ∃ cA, cA = sizeConstantSum Cq 3 := ⟨_, rfl⟩
  have hcH0 : 0 ≤ cH := by rw [hcHd]; exact pos3 Cc hCc0
  have hcA0 : 0 ≤ cA := by rw [hcAd]; exact pos3 Cq hCq
  have hcount : ∀ z₀ : F.Cell,
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) =>
        enclosingCell b.1.1 = z₀).card ≤ 4 * T.L ^ 4 := by
    intro z₀
    have h0 := hCnt F hL hside z₀
    have e : F.blockSide = T.L := hTF.1
    calc _ ≤ 4 * F.blockSide ^ 4 := h0
      _ = 4 * T.L ^ 4 := by rw [e]
  have hS₂b : ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(T.κ / 64 * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤ S₂ :=
    hW2 F (↥(chordBonds (finiteCells F))) (fun b => enclosingCell b.1.1) hcount Y
  have hE₃0 : 0 ≤ T.energyRatio := by
    show 0 ≤ T.E / T.η₃
    have : 0 ≤ T.E := by linarith
    positivity
  have hxi0 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
  have hxi1 : x ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hxis : x ^ (-(1 / 2 : ℝ)) * Real.sqrt x = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    norm_num
  have hc0 : 0 ≤ T.Cs := hc
  obtain ⟨e₅, he₅⟩ : ∃ e₅, e₅ = Real.exp (-(T.κ / 2 ^ 5 * (bondSpan Y c₃ : ℝ))) := ⟨_, rfl⟩
  have he₅0 : 0 < e₅ := by rw [he₅]; exact Real.exp_pos _
  obtain ⟨Kc, hKc⟩ : ∃ Kc, Kc = Tn * cA * cH * T.energyRatio * (cH * T.Cs ^ 2 * S₂ + T.Cs * S₂ + T.Cs) *
    (α + x ^ (-(1 / 2 : ℝ)) * β) := ⟨_, rfl⟩
  have per : ∀ y ∈ sitesOfCells (finiteCells F) F.depth,
      |ballCovariance (cutoffFactor T.ballRadius T.p)
          (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V) A
        (fun η => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y η) V c₃ X)| ≤
      Kc * (e₅ * Real.exp (-(T.κ / 64 * (cellSupDist (enclosingCell y) Y : ℝ)))) := by
    intro y _
    obtain ⟨hDy, hsz⟩ := hrow y
    have bound : ∀ π : Equiv.Perm (Fin 3), Integrable (fun η =>
          ((∑ b, fieldDerivative b (z π b) (Hs y π) η) + Rs y π η) *
            ballDensity (cutoffFactor T.ballRadius T.p) Ψ η) ∧
        Integrable (fun η => A η * ((∑ b, fieldDerivative b (z π b) (Hs y π) η) + Rs y π η) *
          ballDensity (cutoffFactor T.ballRadius T.p) Ψ η) ∧
        |ballCovariance (cutoffFactor T.ballRadius T.p) Ψ A
            (fun η => (∑ b, fieldDerivative b (z π b) (Hs y π) η) + Rs y π η)| ≤
          Kc * (e₅ * Real.exp (-(T.κ / 64 * (cellSupDist (enclosingCell y) Y : ℝ)))) := by
      intro π
      obtain ⟨dH, dR, sH, sR⟩ := hsz π
      have dA : ContDiffOn ℝ 1 A {η | ∀ b, ‖η b‖ < T.ballRadius} := fun η hη =>
        ((hcl.smooth η hη).of_le (by norm_num)).contDiffWithinAt
      have sAb : ∀ b, HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) Ψ Cq x T.κ
          (α * (β / α * Real.exp (-(2 ^ 4 * T.κ * bondDistToCell Y b) -
            2 ^ 6 * T.κ * bondDistToTopBond b (c₃ (π 0)))))
          (fun b' => (cellSupDist (enclosingCell b'.1.1) Y : ℝ)) (fieldDerivative b (z π b) A) := by
        intro b
        have eβ : α * (β / α * Real.exp (-(2 ^ 4 * T.κ * bondDistToCell Y b) -
            2 ^ 6 * T.κ * bondDistToTopBond b (c₃ (π 0)))) =
            β * Real.exp (-(2 ^ 4 * T.κ * bondDistToCell Y b) -
              2 ^ 6 * T.κ * bondDistToTopBond b (c₃ (π 0))) := by
          field_simp
        rw [eβ]
        refine hasLocalSize_congr (fun η hη => ?_)
          (hasLocalSize_of_ballDensity_eq hd (hcl.hasLocalSize_topFieldPartial b (π 0)))
        unfold fieldDerivative topFieldPartial
        rw [(hfield π b).2.1 (η b) (hη b)]
      obtain ⟨r1, r2, r3⟩ := hTO' F (↥(chordBonds (finiteCells F))) (fun b => enclosingCell b.1.1)
        T.ballRadius x T.p Ψ K hρ hx0 hcut' hcount hK hsl A
        (Hs y π) (Rs y π) (z π) Y (enclosingCell y) Cq Cc Cc α
        (T.Cs * T.energyRatio * x ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(2 ^ 4 * T.κ * (bondSpan (enclosingCell y) ![c₃ (π 1), c₃ (π 2)] : ℝ))))
        (T.Cs * T.energyRatio * x ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(2 ^ 4 * T.κ * (bondSpan (enclosingCell y) c₃ : ℝ))))
        (T.Cs * Real.sqrt x)
        (fun b => β / α * Real.exp (-(2 ^ 4 * T.κ * bondDistToCell Y b) -
          2 ^ 6 * T.κ * bondDistToTopBond b (c₃ (π 0))))
        (fun b => Real.exp (-(2 ^ 6 * T.κ * bondDistToTopBond b (c₃ (π 0))))) hCq hCc0 hCc0 hα.le
        (by positivity) (by positivity) (by positivity) (fun b => by positivity)
        (fun b => (Real.exp_pos _).le) dA dH dR
        (fun b => contDiffOn_fieldDerivative b (hfield π b).1.contDiff hcl.smooth)
        (fun b => (hfield π b).2.2.1)
        (hasLocalSize_of_ballDensity_eq hd hcl.hasLocalSize) sAb sH sR (fun b => (hfield π b).2.2.2)
        (fun b => (hfield π b).1)
      refine ⟨r1, r2, r3.trans ?_⟩
      obtain ⟨tA, tB, tC⟩ := weightedSums_le (Y := Y) (Z := enclosingCell y) (c₃ := c₃) π hκ hS₂b
      rw [← he₅] at tA tB tC
      have := siteTerm_le hTn0 hcA0 hcH0 hc0 hα hβ hE₃0 hxi0 hxi1 hxis hW20
        (mul_nonneg he₅0.le (Real.exp_pos _).le)
        (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le) (Real.exp_pos _).le (Real.exp_pos _).le
        (Real.exp_pos _).le tA tB tC
      rw [← hcAd, ← hcHd, ← Finset.mul_sum]
      rw [hKc]
      exact this
    have hcov := ballCovariance_of_average (ρ := T.ballRadius) (p := T.p) (Ψ := Ψ) (A := A)
      (f := fun π η => (∑ b, fieldDerivative b (z π b) (Hs y π) η) + Rs y π η) hDy
      (fun π => (bound π).1) (fun π => (bound π).2.1)
    rw [ballCovariance_eq_of_ballDensity_eq hd, hcov, abs_mul]
    have h1 : |∑ π : Equiv.Perm (Fin 3), ballCovariance (cutoffFactor T.ballRadius T.p) Ψ A
        (fun η => (∑ b, fieldDerivative b (z π b) (Hs y π) η) + Rs y π η)| ≤
        6 * (Kc * (e₅ * Real.exp (-(T.κ / 64 * (cellSupDist (enclosingCell y) Y : ℝ))))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ _ fun π _ => (bound π).2.2).trans (le_of_eq ?_)
      simp [Finset.card_univ, Fintype.card_perm, Nat.factorial]
    have h2 : |(1 / 6 : ℝ)| = 1 / 6 := abs_of_pos (by norm_num)
    rw [h2]
    calc 1 / 6 * _ ≤ 1 / 6 * (6 * (Kc * (e₅ * Real.exp (-(T.κ / 64 *
          (cellSupDist (enclosingCell y) Y : ℝ)))))) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = _ := by ring
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    have : 0 ≤ α + x ^ (-(1 / 2 : ℝ)) * β := by positivity
    positivity
  have hsum : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      Real.exp (-(T.κ / 64 * (cellSupDist (enclosingCell y) Y : ℝ))) ≤ S₁ := by
    rw [← Finset.sum_coe_sort]
    refine hW1 F (↥(sitesOfCells (finiteCells F) F.depth))
      (fun y : ↥(sitesOfCells (finiteCells F) F.depth) => enclosingCell y.1) (fun z₀ => ?_) Y
    have h0 := hSi F (finiteCells F) hL hside z₀
    have e : F.blockSide = T.L := hTF.1
    calc _ ≤ F.blockSide ^ 4 := h0
      _ = T.L ^ 4 := by rw [e]
  refine (Finset.sum_le_sum per).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum he₅0.le) hKc0).trans ?_
  have ecA : (1 + ∑ q ∈ Finset.range 7, Cq q) = cA := by rw [hcAd]; rfl
  rw [ecA, ← he₅, ← hcHd]
  rw [hKc]
  exact le_of_eq (by ring)
theorem thirdOrderCovarianceBound_of (hJ : joinAtLoweredSmallnessConstantStatement)
    (hRow : expansionThirdDerivDecompStatement) (hTO : CovarianceWithFieldDerivativeDecay)
    (hW : _root_.YangMills.Construction.CellCounting.ExpDecaySumBounded) (hCnt : cellBondsCardStatement)
    (hSi : SitesPerCellLePow) : thirdOrderCovarianceBound := by
  obtain ⟨Cz, hCz, hExpansionT⟩ := hRow
  have hW' : ∀ (N : ℕ) (κ : ℝ), ∃ W : ℝ, 0 < κ → 0 ≤ W ∧
      ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
        (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ N) →
        ∀ z : F.Cell, ∑ b, Real.exp (-(κ * (cellSupDist (y b) z : ℝ))) ≤ W := by
    intro N κ
    by_cases h : 0 < κ
    · obtain ⟨W, h1, h2⟩ := hW N κ h
      exact ⟨W, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Wf hWf using hW'
  have hTO2 : ∀ (N : ℕ) (κ lam : ℝ), 0 < κ → 0 < lam → ∃ Tn : ℝ, FieldCovarianceBound N κ lam Tn := hTO
  choose! Tf hTf using hTO2
  refine hJ (fun T => expansionThirdDerivDecompAt T (Cz { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 }))
    (fun T => expansionThirdDerivDecompAt T (Cz { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 }))
    (fun T => ∀ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) → thirdOrderCovarianceBoundAt T Cq)
    (fun U c => Tf (4 * U.L ^ 4) U.κ U.chainParams.lam * sizeConstantSum (Cz U) 3 *
      (sizeConstantSum (Cz U) 3 * c ^ 2 * Wf (4 * U.L ^ 4) (U.κ / 64) +
        c * Wf (4 * U.L ^ 4) (U.κ / 64) + c) * Wf (U.L ^ 4) (U.κ / 64)) hExpansionT hExpansionT ?_
  intro T c hc hodd hn hy hE hη hη1 hκ hσ hch hcut hGle hP _ Cq hCq t x s α β φ h₀ F V Y c₃ X Th A hx hs hs1
    hα hβ hφ hh₀ hTF hV hX hTh hcl
  have hlam : 0 < T.chainParams.lam := hch.positivity.2.2.1
  have hκ64 : 0 < T.κ / 64 := by positivity
  have b := thirdOrder_sum_le (T := { T with Cs := c })
    (Cc := Cz { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 }) (Cq := Cq)
    (Tn := Tf (4 * T.L ^ 4) T.κ T.chainParams.lam) (S₂ := Wf (4 * T.L ^ 4) (T.κ / 64))
    (S₁ := Wf (T.L ^ 4) (T.κ / 64)) hCnt hSi (hTf _ _ _ hκ hlam) hP (by show 0 ≤ c; linarith) hy hodd hE
    hη hκ hσ hch hcut (fun q => hCz _ q) hCq (hWf _ _ hκ64).1 (hWf _ _ hκ64).1 (hWf _ _ hκ64).2
    (hWf _ _ hκ64).2 hx hs hs1 hα hβ hφ hh₀ hTF hV hX hTh hcl
  refine b.trans ?_
  have hq : 0 ≤ 1 + ∑ q ∈ Finset.range 7, Cq q := by
    have : 0 ≤ ∑ q ∈ Finset.range 7, Cq q := Finset.sum_nonneg fun q _ => hCq q
    linarith
  have hE₃ : 0 ≤ T.energyRatio := by
    show 0 ≤ T.E / T.η₃
    have : 0 ≤ T.E := by linarith
    positivity
  have hx1 : 1 ≤ x := hy.trans hx
  have hr : 0 ≤ (α + x ^ (-(1 / 2 : ℝ)) * β) := by positivity
  have he := (Real.exp_pos (-(T.κ / 2 ^ 5 * (bondSpan Y c₃ : ℝ)))).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hGle hq) hE₃) hr) he
end ThirdOrderCovariance
end YangMills.Construction
end
