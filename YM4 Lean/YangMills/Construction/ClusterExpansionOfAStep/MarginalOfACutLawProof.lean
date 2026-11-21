import YangMills.Construction.ClusterExpansionOfAStep.MarginalOfACutLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ClusterExpansionOfAStep.BallLaws
namespace RestrictedMarginal
set_option linter.unusedSectionVars false
variable {ι ι₀ : Type} [Fintype ι] [DecidableEq ι] [Fintype ι₀] [DecidableEq ι₀] {ρ c : ℝ}
  {Ψ : BondField ι → ℝ} {p : ℝ → ℝ} {j : ι₀ → ι}
def InSupport (X : Finset ι) (b : ι) : Prop := b ∈ X
instance instDecidablePredInSupport (X : Finset ι) : DecidablePred (InSupport X) :=
  fun b => inferInstanceAs (Decidable (b ∈ X))
def complementWeight (ρ c : ℝ) (p : ℝ → ℝ) (X : Finset ι) (ζ : BondField {b // ¬ InSupport X b}) : ℝ :=
  radialWeightProd (cutoffFactor ρ p) ζ * Real.exp (-(c / 2 * ∑ x, ‖ζ x‖ ^ 2))
theorem integral_complementWeight_pos (hρ : 0 < ρ) (hp : IsCutoff ρ p) (X : Finset ι) :
    0 < ∫ ζ, complementWeight ρ c p X ζ := by
  have := isFiniteMeasure_radialLaw (ι := {b // ¬ InSupport X b}) hρ hp
  have := radialLaw_neZero (ι := {b // ¬ InSupport X b}) hρ hp
  have hc : Continuous fun ζ : BondField {b // ¬ InSupport X b} => c / 2 * ∑ x, ‖ζ x‖ ^ 2 := by fun_prop
  obtain ⟨M, hM⟩ := exists_abs_le_on_ballProduct (ι := {b // ¬ InSupport X b}) hρ hc
  have hi : Integrable (fun ζ : BondField {b // ¬ InSupport X b} => Real.exp (-(c / 2 * ∑ x, ‖ζ x‖ ^ 2)))
      (radialLaw _ ρ p) := by
    refine Integrable.of_bound (hc.neg.rexp.aestronglyMeasurable) (Real.exp M) ?_
    filter_upwards [ae_mem_ballProduct] with ζ hζ
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := hM ζ hζ
    have h2 := neg_abs_le (c / 2 * ∑ x, ‖ζ x‖ ^ 2)
    linarith
  have h := integral_exp_pos hi
  rw [integral_radialLaw hp] at h
  refine h.trans_eq (integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_))
  simp only [complementWeight]
  ring
theorem integral_mul_ballDensity_restrictedPotential (hj : Function.Injective j) (hp : IsCutoff ρ p)
    (H : BondField ι₀ → ℝ) :
    ∫ η, H (fun a => η (j a)) * ballDensity (cutoffFactor ρ p) (restrictedPotential c (Finset.univ.image j) Ψ) η =
      (∫ ξ, H ξ * ballDensity (cutoffFactor ρ p) (fun ξ => Ψ (extendByZero j ξ)) ξ) *
        ∫ ζ, complementWeight ρ c p (Finset.univ.image j) ζ := by
  set X := Finset.univ.image j with hX
  have memX : ∀ a, j a ∈ X := fun a => Finset.mem_image_of_mem j (Finset.mem_univ a)
  let g : ι₀ ≃ {b // InSupport X b} :=
    Equiv.ofBijective (fun a => ⟨j a, memX a⟩) ⟨fun a a' h => hj (Subtype.ext_iff.mp h), by
      rintro ⟨b, hb⟩
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
      exact ⟨a, rfl⟩⟩
  let Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => BondVector) (InSupport X)
  have hΦ : MeasurePreserving Φ volume volume := volume_preserving_piEquivPiSubtypeProd _ _
  have hsym : ∀ (z : BondField {b // InSupport X b} × BondField {b // ¬ InSupport X b}) (b : ι),
      Φ.symm z b = if h : InSupport X b then z.1 ⟨b, h⟩ else z.2 ⟨b, h⟩ := fun _ _ => rfl
  let A₀ : BondField ι₀ → ℝ :=
    fun ξ => H ξ * ballDensity (cutoffFactor ρ p) (fun ξ => Ψ (extendByZero j ξ)) ξ
  have point : ∀ z : BondField {b // InSupport X b} × BondField {b // ¬ InSupport X b},
      H (fun a => Φ.symm z (j a)) * ballDensity (cutoffFactor ρ p) (restrictedPotential c X Ψ) (Φ.symm z) =
        A₀ (fun a => z.1 (g a)) * complementWeight ρ c p X z.2 := by
    intro z
    have e1 : (fun a => Φ.symm z (j a)) = fun a => z.1 (g a) := by
      funext a
      rw [hsym, dif_pos (show InSupport X (j a) from memX a)]
      rfl
    have e2 : restrictToSet X (Φ.symm z) = extendByZero j fun a => z.1 (g a) := by
      funext b
      unfold restrictToSet
      by_cases hb : b ∈ X
      · rw [if_pos hb, hsym, dif_pos (show InSupport X b from hb)]
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
        rw [extendByZero_apply_image hj]
        rfl
      · rw [if_neg hb, extendByZero_apply_of_not_mem_range]
        exact fun a e => hb (e ▸ memX a)
    have e3 : radialWeightProd (cutoffFactor ρ p) (Φ.symm z) =
        radialWeightProd (cutoffFactor ρ p) (fun a => z.1 (g a)) * radialWeightProd (cutoffFactor ρ p) z.2 := by
      unfold radialWeightProd
      rw [← Fintype.prod_subtype_mul_prod_subtype (InSupport X)]
      congr 1
      · rw [← Equiv.prod_comp g]
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [hsym, dif_pos (g a).2]
      · refine Finset.prod_congr rfl fun x _ => ?_
        rw [hsym, dif_neg x.2]
    have e4 : ∑ b ∈ Finset.univ \ X, ‖Φ.symm z b‖ ^ 2 = ∑ x, ‖z.2 x‖ ^ 2 := by
      rw [Finset.sum_subtype (Finset.univ \ X) (p := fun b => ¬ InSupport X b) (by simp [InSupport])]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hsym, dif_neg x.2]
    simp only [A₀, complementWeight, ballDensity, restrictedPotential, e1, e2, e3, e4]
    rw [neg_add, Real.exp_add]
    ring
  have h1 := hΦ.symm.integral_comp'
    (fun η => H (fun a => η (j a)) * ballDensity (cutoffFactor ρ p) (restrictedPotential c X Ψ) η)
  rw [← h1]
  simp only [point]
  rw [Measure.volume_eq_prod]
  erw [integral_prod_mul (fun ξ₁ : BondField {b // InSupport X b} => A₀ fun a => ξ₁ (g a))
    (complementWeight ρ c p X)]
  congr 1
  have hΞ := volume_measurePreserving_piCongrLeft (fun _ : {b // InSupport X b} => BondVector) g
  rw [← hΞ.integral_comp' (fun ξ₁ : BondField {b // InSupport X b} => A₀ fun a => ξ₁ (g a))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [A₀]
  congr 1
  all_goals
    congr 1
    funext a
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
theorem marginalOfRestrictedLaw_holds : MarginalOfRestrictedLaw := by
  intro ι ι₀ _ _ _ _ ρ c Ψ p j F hρ hp hj
  unfold ballExpectation
  have h1 := integral_mul_ballDensity_restrictedPotential (c := c) (Ψ := Ψ) hj hp F
  have h2 := integral_mul_ballDensity_restrictedPotential (c := c) (Ψ := Ψ) hj hp fun _ => 1
  simp only [one_mul] at h2
  rw [h1, h2]
  exact mul_div_mul_right _ _ (integral_complementWeight_pos hρ hp _).ne'
end RestrictedMarginal
end YangMills.Construction.ClusterExpansionOfAStep
end
