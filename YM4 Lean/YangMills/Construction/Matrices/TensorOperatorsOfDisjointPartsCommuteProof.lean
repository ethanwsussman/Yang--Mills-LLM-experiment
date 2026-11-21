import YangMills.Construction.Matrices.OperatorsAreDeterminedByMatrixElementsForm
import YangMills.Construction.Matrices.ProjectionsCommuteWithTwoSidedTranslationsProof
import YangMills.Construction.Matrices.TensorOperatorOnProductsAndItsMatrixElements
import YangMills.Construction.Matrices.TensorOperatorsOfDisjointPartsCommute
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SpinHarmonics.DisjointParts
open Matrices.ComplexMatrix2 SeveralVariables
theorem measurePreserving_comp_injective {ι κ : Type} [Countable ι] [Countable κ] (e : ι → κ)
    (he : Function.Injective e) :
    MeasurePreserving (fun (u : κ → specialUnitary) (i : ι) => u (e i)) (haarPi κ) (haarPi ι) := by
  classical
  have hm : Measurable fun (u : κ → specialUnitary) (i : ι) => u (e i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (e i)
  refine ⟨hm, ?_⟩
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  let t' : κ → Set specialUnitary := Function.extend e t fun _ => Set.univ
  have ht' : ∀ i, t' (e i) = t i := fun i => he.extend_apply _ _ i
  have hpre : (fun (u : κ → specialUnitary) (i : ι) => u (e i)) ⁻¹' Set.pi (s : Set ι) t =
      Set.pi ((s.map ⟨e, he⟩ : Finset κ) : Set κ) t' := by
    ext u
    simp [Set.mem_pi, ht']
  have hmeas : ∀ k ∈ s.map ⟨e, he⟩, MeasurableSet (t' k) := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hk
    change MeasurableSet (t' (e i))
    rw [ht']
    exact ht i
  rw [hpre]
  unfold haarPi
  rw [Measure.infinitePi_pi _ hmeas, Finset.prod_map]
  exact Finset.prod_congr rfl fun i _ => by
    change haarProb (t' (e i)) = haarProb (t i)
    rw [ht']
section Classes
variable {J : Type} [Finite J]
theorem toHaarL2_congr {f g : (J → specialUnitary) → ℂ} (h : f =ᵐ[haarPi J] g) :
    toHaarL2 f = toHaarL2 g := by
  unfold toHaarL2
  by_cases hf : MemLp f 2 (haarPi J)
  · have hg : MemLp g 2 (haarPi J) := (memLp_congr_ae h).1 hf
    rw [dif_pos hf, dif_pos hg]
    exact (MemLp.toLp_eq_toLp_iff hf hg).2 h
  · have hg : ¬ MemLp g 2 (haarPi J) := fun hg => hf ((memLp_congr_ae h).2 hg)
    rw [dif_neg hf, dif_neg hg]
theorem coe_toHaarL2 {f : (J → specialUnitary) → ℂ} (hf : MemLp f 2 (haarPi J)) :
    (toHaarL2 f : (J → specialUnitary) → ℂ) =ᵐ[haarPi J] f := by apply _root_.YangMills.Construction.SpinHarmonics.BiTranslation.toHaarL2_ae_eq <;> assumption
theorem memLp_two_continuous (g : C(J → specialUnitary, ℂ)) : MemLp g 2 (haarPi J) :=
  MemLp.of_bound g.continuous.aestronglyMeasurable ‖g‖ (ae_of_all _ fun x => g.norm_coe_le_norm x)
theorem peterWeylVec_eq_toHaarL2 (α : PeterWeylIndex J) :
    peterWeylVec α = toHaarL2 (peterWeylFn α) := by
  have hg := memLp_two_continuous (peterWeylFn α)
  unfold toHaarL2
  rw [dif_pos hg]
  exact Lp.ext ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (haarPi J)
    (peterWeylFn α)).trans hg.coeFn_toLp.symm)
theorem tensorFn_ae_congr (B : Set J) {f f' : (↥B → specialUnitary) → ℂ}
    {h h' : (↥Bᶜ → specialUnitary) → ℂ}
    (hf : f =ᵐ[haarPi ↥B] f') (hh : h =ᵐ[haarPi ↥Bᶜ] h') :
    tensorFn B f h =ᵐ[haarPi J] tensorFn B f' h' := by
  have h₁ := (measurePreserving_comp_injective (Subtype.val : ↥B → J)
    Subtype.val_injective).quasiMeasurePreserving.ae_eq_comp hf
  have h₂ := (measurePreserving_comp_injective (Subtype.val : ↥Bᶜ → J)
    Subtype.val_injective).quasiMeasurePreserving.ae_eq_comp hh
  filter_upwards [h₁, h₂] with u e₁ e₂
  have e₁' : f (restrictTo B u) = f' (restrictTo B u) := e₁
  have e₂' : h (restrictTo Bᶜ u) = h' (restrictTo Bᶜ u) := e₂
  simp only [tensorFn, e₁', e₂']
theorem tensorOne_toHaarL2_tensorFn (B : Set J)
    {X : HaarL2 ↥B →L[ℂ] HaarL2 ↥B} (hX : TensorOneOnProducts B X)
    {f : (↥B → specialUnitary) → ℂ} {h : (↥Bᶜ → specialUnitary) → ℂ} (hf : MemLp f 2 (haarPi ↥B))
    (hh : MemLp h 2 (haarPi ↥Bᶜ)) :
    tensorOne B X (toHaarL2 (tensorFn B f h)) =
      toHaarL2 (tensorFn B (X (toHaarL2 f)) h) := by
  have e := (hX.1 (toHaarL2 f) (toHaarL2 h)).2
  rw [toHaarL2_congr (tensorFn_ae_congr B (coe_toHaarL2 hf) (coe_toHaarL2 hh)),
    toHaarL2_congr (tensorFn_ae_congr B (Filter.EventuallyEq.refl _ _)
      (coe_toHaarL2 hh))] at e
  exact e
def subfamily {S T : Set J} (h : S ⊆ T) (z : ↥T → specialUnitary) : ↥S → specialUnitary :=
  fun s => z ⟨s, h s.2⟩
theorem measurePreserving_subfamily {S T : Set J} (h : S ⊆ T) :
    MeasurePreserving (subfamily h) (haarPi ↥T) (haarPi ↥S) :=
  measurePreserving_comp_injective (fun s : ↥S => (⟨s, h s.2⟩ : ↥T)) fun _ _ hab =>
    Subtype.ext (congrArg (fun t : ↥T => (t : J)) hab)
theorem memLp_mul_subfamily {S R T : Set J} (hS : S ⊆ T) (hR : R ⊆ T)
    {g : (↥S → specialUnitary) → ℂ}
    (hg : MemLp g 2 (haarPi ↥S)) (r : C(↥R → specialUnitary, ℂ)) :
    MemLp (fun z : ↥T → specialUnitary => g (subfamily hS z) * r (subfamily hR z)) 2
      (haarPi ↥T) := by
  have h₁ : MemLp (fun z : ↥T → specialUnitary => g (subfamily hS z)) 2 (haarPi ↥T) :=
    hg.comp_measurePreserving (measurePreserving_subfamily hS)
  have h₂ : AEStronglyMeasurable (fun z : ↥T → specialUnitary => r (subfamily hR z))
      (haarPi ↥T) :=
    r.continuous.aestronglyMeasurable.comp_measurePreserving (measurePreserving_subfamily hR)
  refine MemLp.of_le_mul (c := ‖r‖) h₁ (h₁.aestronglyMeasurable.mul h₂) (ae_of_all _ fun z => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (r.norm_coe_le_norm _) (norm_nonneg _)
end Classes
section Disjoint
variable {J : Type} [Finite J] {B B' : Set J}
def threeFactorFn (B B' : Set J) (f : (↥B → specialUnitary) → ℂ)
    (g : (↥B' → specialUnitary) → ℂ)
    (r : (↥(B ∪ B')ᶜ → specialUnitary) → ℂ) (u : J → specialUnitary) : ℂ :=
  f (restrictTo B u) * g (restrictTo B' u) * r (restrictTo (B ∪ B')ᶜ u)
omit [Finite J] in
theorem compl_union_subset_compl_left : (B ∪ B')ᶜ ⊆ Bᶜ :=
  Set.compl_subset_compl.2 Set.subset_union_left
omit [Finite J] in
theorem compl_union_subset_compl_right : (B ∪ B')ᶜ ⊆ B'ᶜ :=
  Set.compl_subset_compl.2 Set.subset_union_right
omit [Finite J] in
theorem threeFactorFn_eq_tensorFn_left (hsub : B' ⊆ Bᶜ) (f : (↥B → specialUnitary) → ℂ)
    (g : (↥B' → specialUnitary) → ℂ) (r : (↥(B ∪ B')ᶜ → specialUnitary) → ℂ) :
    threeFactorFn B B' f g r = tensorFn B f
      (fun z => g (subfamily hsub z) * r (subfamily compl_union_subset_compl_left z)) := by
  funext u
  exact mul_assoc _ _ _
omit [Finite J] in
theorem threeFactorFn_eq_tensorFn_right (hsub : B ⊆ B'ᶜ) (f : (↥B → specialUnitary) → ℂ)
    (g : (↥B' → specialUnitary) → ℂ) (r : (↥(B ∪ B')ᶜ → specialUnitary) → ℂ) :
    threeFactorFn B B' f g r = tensorFn B' g
      (fun z => f (subfamily hsub z) * r (subfamily compl_union_subset_compl_right z)) := by
  funext u
  change f (restrictTo B u) * g (restrictTo B' u) * r (restrictTo (B ∪ B')ᶜ u) =
    g (restrictTo B' u) * (f (restrictTo B u) * r (restrictTo (B ∪ B')ᶜ u))
  ring
theorem peterWeylFn_eq_threeFactorFn (hsub : B' ⊆ Bᶜ) (α : PeterWeylIndex J) :
    (peterWeylFn α : (J → specialUnitary) → ℂ) =
      threeFactorFn B B' (peterWeylFn fun b : ↥B => α b)
        (peterWeylFn fun b : ↥B' => α b)
        (peterWeylFn fun b : ↥(B ∪ B')ᶜ => α b) := by
  funext u
  change (∏ᶠ b, normalizedCoeff (α b) (u b)) =
    (∏ᶠ b : ↥B, normalizedCoeff (α b) (u b)) * (∏ᶠ b : ↥B', normalizedCoeff (α b) (u b)) *
      ∏ᶠ b : ↥(B ∪ B')ᶜ, normalizedCoeff (α b) (u b)
  have hd : Disjoint B B' := Set.disjoint_left.2 fun b hb hb' => hsub hb' hb
  rw [finprod_set_coe_eq_finprod_mem (f := fun b => normalizedCoeff (α b) (u b)) B,
    finprod_set_coe_eq_finprod_mem (f := fun b => normalizedCoeff (α b) (u b)) B',
    finprod_set_coe_eq_finprod_mem (f := fun b => normalizedCoeff (α b) (u b)) (B ∪ B')ᶜ,
    ← finprod_mem_union hd (Set.toFinite _) (Set.toFinite _),
    ← finprod_mem_union disjoint_compl_right (Set.toFinite _) (Set.toFinite _),
    Set.union_compl_self, finprod_mem_univ]
end Disjoint
theorem tensorOne_disjoint_commute (hDetermined : AllOpsDeterminedByEntries)
    (hProducts : TensorOneOnProductsForAll) : TensorOneDisjointCommuteForAll := by
  intro J _ _ B hB hBu X B' hB' hsub X'
  have hBu' : B' ≠ Set.univ := by
    intro h
    obtain ⟨b, hb⟩ := hB
    exact hsub (h ▸ Set.mem_univ b) hb
  have hX := hProducts J B hB hBu X
  have hX' := hProducts J B' hB' hBu' X'
  have hsub' : B ⊆ B'ᶜ := fun b hb hb' => hsub hb' hb
  have left : ∀ {f : (↥B → specialUnitary) → ℂ} {g : (↥B' → specialUnitary) → ℂ}
      (r : C(↥(B ∪ B')ᶜ → specialUnitary, ℂ)),
      MemLp f 2 (haarPi ↥B) → MemLp g 2 (haarPi ↥B') →
      tensorOne B X (toHaarL2 (threeFactorFn B B' f g r)) =
        toHaarL2 (threeFactorFn B B' (X (toHaarL2 f)) g r) := by
    intro f g r hf hg
    rw [threeFactorFn_eq_tensorFn_left hsub, threeFactorFn_eq_tensorFn_left hsub]
    exact tensorOne_toHaarL2_tensorFn B hX hf
      (memLp_mul_subfamily hsub compl_union_subset_compl_left hg r)
  have right : ∀ {f : (↥B → specialUnitary) → ℂ} {g : (↥B' → specialUnitary) → ℂ}
      (r : C(↥(B ∪ B')ᶜ → specialUnitary, ℂ)),
      MemLp f 2 (haarPi ↥B) → MemLp g 2 (haarPi ↥B') →
      tensorOne B' X' (toHaarL2 (threeFactorFn B B' f g r)) =
        toHaarL2 (threeFactorFn B B' f (X' (toHaarL2 g)) r) := by
    intro f g r hf hg
    rw [threeFactorFn_eq_tensorFn_right hsub', threeFactorFn_eq_tensorFn_right hsub']
    exact tensorOne_toHaarL2_tensorFn B' hX' hg
      (memLp_mul_subfamily hsub' compl_union_subset_compl_right hf r)
  refine hDetermined J _ _ fun α α' => ?_
  have key : tensorOne B X (tensorOne B' X' (peterWeylVec α')) =
      tensorOne B' X' (tensorOne B X (peterWeylVec α')) := by
    have hf := memLp_two_continuous (peterWeylFn fun b : ↥B => α' b)
    have hg := memLp_two_continuous (peterWeylFn fun b : ↥B' => α' b)
    rw [peterWeylVec_eq_toHaarL2, peterWeylFn_eq_threeFactorFn hsub α', right _ hf hg,
      left _ hf (Lp.memLp _), left _ hf hg, right _ (Lp.memLp _) hg]
  change inner ℂ (peterWeylVec α) (tensorOne B X (tensorOne B' X'
      (peterWeylVec α'))) = inner ℂ (peterWeylVec α) (tensorOne B' X'
      (tensorOne B X (peterWeylVec α')))
  rw [key]
end YangMills.Construction.SpinHarmonics.DisjointParts
end
