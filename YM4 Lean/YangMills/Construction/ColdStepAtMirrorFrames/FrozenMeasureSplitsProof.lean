import YangMills.Construction.ColdStepAtMirrorFrames.CalculusOfLocalTerms
import YangMills.Construction.ColdStepAtMirrorFrames.FrozenMeasureSplits
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace FrozenPotentialFactorization
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
theorem pushforwardField_apply_of_injective (f : κ → ι) (hf : Function.Injective f) (ξ : BondField κ) (k : κ) :
    pushforwardField f ξ (f k) = ξ k := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.pushforwardField_apply_image <;> assumption
theorem pushforwardField_apply_of_forall_ne (f : κ → ι) (ξ : BondField κ) (b : ι) (hb : ∀ k, f k ≠ b) :
    pushforwardField f ξ b = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.pushforwardField_apply_of_not_mem_range <;> assumption
theorem integral_eq_mul_of_factor_subtype (Λ : Finset ι)
    (N : BondField {b // b ∈ Λ} → ℝ)
    (C : BondField {b // b ∉ Λ} → ℝ) (φ : BondField ι → ℝ)
    (hφ : ∀ η, φ η = N (fun x => η x) * C (fun x => η x)) :
    ∫ η, φ η = (∫ ξ, N ξ) * ∫ ζ, C ζ := by
  have hp := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => BondVector) (fun b => b ∈ Λ)
  rw [show (Subtype.fintype fun b => b ∈ Λ) = Finset.Subtype.fintype Λ from Subsingleton.elim _ _] at hp
  have hcomp := hp.integral_comp' (g := fun z : BondField {b // b ∈ Λ} × BondField {b // b ∉ Λ} =>
    N z.1 * C z.2)
  have hrw : ∀ η : BondField ι, φ η = (fun z : BondField {b // b ∈ Λ} × BondField {b // b ∉ Λ} =>
      N z.1 * C z.2) (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => BondVector) (fun b => b ∈ Λ) η) :=
    fun η => hφ η
  simp only [hrw]
  rw [hcomp, Measure.volume_eq_prod]
  exact integral_prod_mul (μ := volume) (ν := volume) N C
theorem integral_comp_equiv (S : Type) [Fintype S] [DecidableEq S] (e : κ ≃ S) (N : BondField S → ℝ) :
    ∫ ξ : BondField κ, N (fun s => ξ (e.symm s)) = ∫ ξ, N ξ := by
  have hp := volume_measurePreserving_piCongrLeft (fun _ : S => BondVector) e
  have hcomp := hp.integral_comp' (g := N)
  rw [← hcomp]
  congr 1
  funext ξ
  congr 1
  funext s
  obtain ⟨k, rfl⟩ := e.surjective s
  simp [MeasurableEquiv.piCongrLeft]
end FrozenPotentialFactorization
open FrozenPotentialFactorization in
theorem frozenPotentialExpectationFactorizes_of_cutoff (hm : CutoffExpectationIsPositiveForm) :
    FrozenPotentialExpectationFactorizes := by
  intro ι κ _ _ _ _ Λ e ρ μ p Ψ H hρ hp hΨ hμ
  set f : κ → ι := fun k => (e k).1 with hf
  have hf_inj : Function.Injective f := fun a b h => e.injective (Subtype.ext h)
  set f₀ : {b // b ∈ Λ} → ι := fun s => s.1 with hf₀
  have hf₀_inj : Function.Injective f₀ := Subtype.val_injective
  set r := cutoffFactor ρ p with hr
  set Cf : BondField {b // b ∉ Λ} → ℝ := fun ζ =>
    radialWeightProd r ζ * Real.exp (-(∑ c, μ / 2 * ‖ζ c‖ ^ 2)) with hCf
  have hC : (∫ ζ, Cf ζ) ≠ 0 := by
    have hcont : Continuous (fun ζ : BondField {b // b ∉ Λ} => ∑ c, μ / 2 * ‖ζ c‖ ^ 2) :=
      continuous_finsetSum _ fun c _ => continuous_const.mul ((continuous_apply c).norm.pow 2)
    have F := hm {b // b ∉ Λ} ρ p _ hρ hp hcont
    have hone := F.map_one
    intro h0
    unfold ballExpectation at hone
    have hzero : ∫ ζ, ballDensity r (fun ζ : BondField {b // b ∉ Λ} => ∑ c, μ / 2 * ‖ζ c‖ ^ 2) ζ = 0 := by
      simpa [ballDensity, hCf] using h0
    rw [← hr, hzero] at hone
    simp at hone
  have hrestrict : ∀ η : BondField ι, restrictToBonds Λ η = pushforwardField f₀ (fun x => η x) := by
    intro η
    funext b
    by_cases hb : b ∈ Λ
    · have := pushforwardField_apply_of_injective f₀ hf₀_inj (fun x => η x) ⟨b, hb⟩
      simp only [hf₀] at this ⊢
      rw [this]
      simp [restrictToBonds, hb]
    · rw [pushforwardField_apply_of_forall_ne f₀ _ b (fun k h => hb (h ▸ k.2))]
      simp [restrictToBonds, hb]
  have hprod : ∀ η : BondField ι, radialWeightProd r η =
      radialWeightProd r (fun x : {b // b ∈ Λ} => η x) * radialWeightProd r (fun x : {b // b ∉ Λ} => η x) := by
    intro η
    unfold radialWeightProd
    convert (Fintype.prod_subtype_mul_prod_subtype (fun b => b ∈ Λ) (fun b => r ‖η b‖)).symm using 3
    ext x
    simp
  have hsq : ∀ η : BondField ι, halfSqNormOn μ Λᶜ η = ∑ c : {b // b ∉ Λ}, μ / 2 * ‖η c‖ ^ 2 := by
    intro η
    unfold halfSqNormOn
    exact Finset.sum_subtype _ (fun b => by simp) _
  have hsplit : ∀ G : BondField ι → ℝ,
      ∫ η, G (restrictToBonds Λ η) * ballDensity r (frozenPotential Λ μ Ψ) η =
        (∫ ξ : BondField κ, G (pushforwardField f ξ) * ballDensity r (fun ξ => Ψ (pushforwardField f ξ)) ξ) *
          ∫ ζ, Cf ζ := by
    intro G
    set N : BondField {b // b ∈ Λ} → ℝ := fun ξ =>
      G (pushforwardField f₀ ξ) * (radialWeightProd r ξ * Real.exp (-Ψ (pushforwardField f₀ ξ))) with hN
    have hint := integral_eq_mul_of_factor_subtype Λ N Cf
      (fun η => G (restrictToBonds Λ η) * ballDensity r (frozenPotential Λ μ Ψ) η) (fun η => by
        simp only [hN, hCf, ballDensity, frozenPotential, ← hrestrict, hprod η, hsq η, neg_add, Real.exp_add]
        ring)
    rw [hint]
    congr 1
    rw [← integral_comp_equiv _ e N]
    congr 1
    funext ξ
    have hpush : pushforwardField f₀ (fun s => ξ (e.symm s)) = pushforwardField f ξ := by
      funext b
      by_cases hb : b ∈ Λ
      · obtain ⟨k, hk⟩ := e.surjective ⟨b, hb⟩
        have hbk : b = f k := by simp [hf, hk]
        have h₂ := pushforwardField_apply_of_injective f₀ hf₀_inj (fun s => ξ (e.symm s)) ⟨b, hb⟩
        have h₃ := pushforwardField_apply_of_injective f hf_inj ξ k
        simp only [hf₀] at h₂
        have h₄ : e.symm ⟨b, hb⟩ = k := by
          rw [← hk]
          simp
        have h₅ : pushforwardField f ξ b = ξ k := by
          rw [hbk]
          exact h₃
        rw [h₂, h₄, h₅]
      · rw [pushforwardField_apply_of_forall_ne f₀ _ b (fun k h => hb (h ▸ k.2)),
          pushforwardField_apply_of_forall_ne f _ b (fun k h => hb (h ▸ (e k).2))]
    have hweight : radialWeightProd r (fun s => ξ (e.symm s)) = radialWeightProd r ξ := by
      unfold radialWeightProd
      exact (Fintype.prod_equiv e _ _ (fun k => by simp)).symm
    simp only [hN, hpush, hweight, ballDensity]
  unfold ballExpectation
  have hG := hsplit H
  have hOne := hsplit (fun _ => 1)
  simp only [one_mul] at hOne
  rw [hG, hOne]
  exact mul_div_mul_right _ _ hC
end YangMills.Construction.ColdStepAtMirrorFrames
end
