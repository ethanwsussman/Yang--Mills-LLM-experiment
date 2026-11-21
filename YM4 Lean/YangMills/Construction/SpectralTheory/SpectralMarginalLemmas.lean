import YangMills.Construction.SpectralTheory.MarginalsOfSpectralMeasure
import YangMills.Construction.SpectralTheory.SpectralPushforwardLemmas
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.SpectralMarginal
open BorelSpectral BorelCalculus
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def finiteInter {X : Type} [MeasurableSpace X] : List (BorelSubsets X) → BorelSubsets X
  | [] => ⟨univ, MeasurableSet.univ⟩
  | s :: l => ⟨s.1 ∩ (finiteInter l).1, s.2.inter (finiteInter l).2⟩
theorem mem_finiteInter {X : Type} [MeasurableSpace X] (l : List (BorelSubsets X)) (y : X) :
    y ∈ (finiteInter l).1 ↔ ∀ s ∈ l, y ∈ s.1 := by
  induction l with
  | nil => simp [finiteInter]
  | cons s l ih => simp [finiteInter, ih]
theorem prod_map_toFun_eq (E : SpectralMeasure (univ : Set (Fin n → ℝ)) H)
    (l : List (BorelSubsets (univ : Set (Fin n → ℝ)))) :
    (l.map E.toFun).prod = E (finiteInter l) := by
  induction l with
  | nil => exact E.map_univ.symm
  | cons s l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    exact (E.map_inter s (finiteInter l)).symm
theorem apply_boxProduct_eq_prod (E : SpectralMeasure (univ : Set (Fin n → ℝ)) H)
    (Δ : Fin n → BorelSubsets ℝ) :
    E (boxProduct Δ) = (List.ofFn fun i => E.coordMarginal i (realLineSet (Δ i))).prod := by
  let s : Fin n → BorelSubsets (univ : Set (Fin n → ℝ)) := fun i =>
    ⟨{y | y.1 i ∈ (Δ i).1}, ((measurable_pi_apply i).comp measurable_subtype_coe) (Δ i).2⟩
  have hl : (List.ofFn fun i => E.coordMarginal i (realLineSet (Δ i))) =
      (List.ofFn s).map E.toFun := by
    rw [List.map_ofFn]
    rfl
  have hs : boxProduct Δ = finiteInter (List.ofFn s) := by
    refine Subtype.ext (Set.ext fun y => ?_)
    rw [mem_finiteInter]
    simp [boxProduct, List.mem_ofFn, s]
  rw [hl, prod_map_toFun_eq, hs]
theorem commute_apply (E : SpectralMeasure (univ : Set (Fin n → ℝ)) H)
    (Δ Δ' : BorelSubsets (univ : Set (Fin n → ℝ))) : Commute (E Δ) (E Δ') := by
  have h : (⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩ : BorelSubsets (univ : Set (Fin n → ℝ))) =
      ⟨Δ'.1 ∩ Δ.1, Δ'.2.inter Δ.2⟩ := Subtype.ext (inter_comm _ _)
  change E Δ * E Δ' = E Δ' * E Δ
  rw [← E.map_inter, ← E.map_inter, h]
theorem diagMeasure_eq_of_boxProduct (E E' : SpectralMeasure (univ : Set (Fin n → ℝ)) H)
    (h : ∀ Δ : Fin n → BorelSubsets ℝ, E (boxProduct Δ) = E' (boxProduct Δ)) (ψ : H) :
    E.diagMeasure ψ = E'.diagMeasure ψ := by
  have hv : Measurable (Subtype.val : ↥(univ : Set (Fin n → ℝ)) → Fin n → ℝ) :=
    measurable_subtype_coe
  have hmap : (E.diagMeasure ψ).map Subtype.val = (E'.diagMeasure ψ).map Subtype.val := by
    refine ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      have hp : MeasurableSet (pi univ t) := MeasurableSet.univ_pi fun i => ht i (mem_univ i)
      let Δ : Fin n → BorelSubsets ℝ := fun i => ⟨t i, ht i (mem_univ i)⟩
      have hs : Subtype.val ⁻¹' pi univ t = (boxProduct Δ).1 := by
        ext y
        simp [boxProduct, Δ, Set.mem_pi]
      rw [Measure.map_apply hv hp, Measure.map_apply hv hp, hs, E.diagMeasure_apply,
        E'.diagMeasure_apply, h]
    · rw [Measure.map_apply hv MeasurableSet.univ, Measure.map_apply hv MeasurableSet.univ,
        preimage_univ, E.diagMeasure_univ, E'.diagMeasure_univ]
  refine Measure.ext fun Δ hΔ => ?_
  have hi : MeasurableSet (Subtype.val '' Δ : Set (Fin n → ℝ)) :=
    MeasurableSet.univ.subtype_image hΔ
  have hpre : (Subtype.val : ↥(univ : Set (Fin n → ℝ)) → Fin n → ℝ) ⁻¹' (Subtype.val '' Δ) = Δ :=
    preimage_image_eq _ Subtype.val_injective
  have := congrArg (fun μ => μ (Subtype.val '' Δ)) hmap
  simpa only [Measure.map_apply hv hi, hpre] using this
omit [CompleteSpace H] in
theorem ext_of_inner_self {T S : H →L[ℂ] H} (h : ∀ ψ, ⟪ψ, T ψ⟫_ℂ = ⟪ψ, S ψ⟫_ℂ) : T = S := by apply _root_.YangMills.Construction.SpectralPushforward.ext_of_inner_self <;> assumption
theorem marginalsHold_proof : MarginalsHold := by
  intro H _ _ _ n E
  refine ⟨apply_boxProduct_eq_prod E, fun i j Δ Δ' => commute_apply E _ _, fun E' hm => ?_⟩
  have hprod : ∀ Δ : Fin n → BorelSubsets ℝ, E' (boxProduct Δ) = E (boxProduct Δ) := by
    intro Δ
    rw [apply_boxProduct_eq_prod E, apply_boxProduct_eq_prod E']
    simp only [hm]
  refine SpectralMeasure.ext_apply fun Δ => ext_of_inner_self fun ψ => ?_
  rw [E'.inner_apply_self_eq_diagMeasure, E.inner_apply_self_eq_diagMeasure,
    diagMeasure_eq_of_boxProduct E' E hprod ψ]
end YangMills.Construction.SpectralMarginal
