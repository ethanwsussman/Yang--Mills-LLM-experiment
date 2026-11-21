import YangMills.Construction.InfiniteLattice.TraceOnTheGroupAndOneBondWeightProof
import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfG
import YangMills.Construction.TransferOperators.ObjectsOfTheStepBetweenSymmetricStacks
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.TransferOperators.KernelSymmetryAndGaugeInvariance
section EntryPolynomials
variable {J : Type}
theorem isEntryPolynomial_const (c : ℂ) :
    IsEntryPolynomial fun _ : J → ComplexMatrix2.specialUnitary => c :=
  ⟨MvPolynomial.C c, fun u => by simp⟩
theorem isEntryPolynomial_add {F H : (J → ComplexMatrix2.specialUnitary) → ℂ}
    (hF : IsEntryPolynomial F) (hH : IsEntryPolynomial H) :
    IsEntryPolynomial fun u => F u + H u := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hH
  exact ⟨p + q, fun u => by
    change F u + H u = _
    rw [hp, hq, map_add]⟩
theorem isEntryPolynomial_mul {F H : (J → ComplexMatrix2.specialUnitary) → ℂ}
    (hF : IsEntryPolynomial F) (hH : IsEntryPolynomial H) :
    IsEntryPolynomial fun u => F u * H u := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hH
  exact ⟨p * q, fun u => by
    change F u * H u = _
    rw [hp, hq, map_mul]⟩
theorem isEntryPolynomial_finsetSum {A : Type} (s : Finset A)
    (F : A → (J → ComplexMatrix2.specialUnitary) → ℂ)
    (hF : ∀ a ∈ s, IsEntryPolynomial (F a)) : IsEntryPolynomial fun u => ∑ a ∈ s, F a u := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isEntryPolynomial_const (J := J) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact isEntryPolynomial_add (hF a (Finset.mem_insert_self a s))
      (ih fun a' h => hF a' (Finset.mem_insert_of_mem h))
def EntrywisePolynomial (M : (J → ComplexMatrix2.specialUnitary) → ComplexMatrix2) : Prop :=
  ∀ i j, IsEntryPolynomial fun u => M u i j
theorem entrywisePolynomial_coord (b : J) :
    EntrywisePolynomial fun u : J → ComplexMatrix2.specialUnitary =>
      ((u b : ComplexMatrix2.specialUnitary) : ComplexMatrix2) :=
  fun i j => ⟨MvPolynomial.X (Sum.inl (b, i, j)), fun u => by simp [entryEval]⟩
theorem entrywisePolynomial_inv (b : J) :
    EntrywisePolynomial fun u : J → ComplexMatrix2.specialUnitary =>
      (((u b)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by
  intro i j
  refine ⟨MvPolynomial.X (Sum.inr (b, j, i)), fun u => ?_⟩
  change (((u b)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j = _
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  simp [entryEval, Matrix.star_apply]
theorem EntrywisePolynomial.mul {M N : (J → ComplexMatrix2.specialUnitary) → ComplexMatrix2}
    (hM : EntrywisePolynomial M) (hN : EntrywisePolynomial N) :
    EntrywisePolynomial fun u => M u * N u := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact isEntryPolynomial_add (isEntryPolynomial_mul (hM i 0) (hN 0 j))
    (isEntryPolynomial_mul (hM i 1) (hN 1 j))
end EntryPolynomials
section Holonomy
variable {μ : Fin 4}
theorem coe_mul_specialUnitary (a b : ComplexMatrix2.specialUnitary) :
    ((a * b : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      (a : ComplexMatrix2) * (b : ComplexMatrix2) := rfl
theorem isEntryPolynomial_trace_holonomy (p : SlicePlaquette μ) {S : Set (SliceLink μ)}
    (hS : p.links ⊆ S) :
    IsEntryPolynomial fun w : S → ComplexMatrix2.specialUnitary =>
      ComplexMatrix2.fullTrace ((plaquetteHolonomy p hS w : ComplexMatrix2.specialUnitary) :
        ComplexMatrix2) := by
  have h : EntrywisePolynomial fun w : S → ComplexMatrix2.specialUnitary =>
      ((plaquetteHolonomy p hS w : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by
    simp only [plaquetteHolonomy, coe_mul_specialUnitary]
    exact (((entrywisePolynomial_coord _).mul (entrywisePolynomial_coord _)).mul
      (entrywisePolynomial_inv _)).mul (entrywisePolynomial_inv _)
  simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  exact isEntryPolynomial_add (h 0 0) (h 1 1)
theorem plaquetteHolonomy_gaugeAct {v : Set (SliceSite μ)} (p : SlicePlaquette μ)
    {S : Set (SliceLink μ)} (hS : p.links ⊆ S) (hv : S ⊆ linksWithin v) (hb : p.origin ∈ v)
    (g : v → ComplexMatrix2.specialUnitary) (u : S → ComplexMatrix2.specialUnitary) :
    plaquetteHolonomy p hS (gaugeAct hv g u) =
      g ⟨p.origin, hb⟩ * plaquetteHolonomy p hS u * (g ⟨p.origin, hb⟩)⁻¹ := by
  classical
  let G : SliceSite μ → ComplexMatrix2.specialUnitary := fun y => if h : y ∈ v then g ⟨y, h⟩ else 1
  have hG : ∀ (y : SliceSite μ) (h : y ∈ v), g ⟨y, h⟩ = G y := fun y h => by
    simp only [G, dif_pos h]
  have e₁ : p.bottomLink.source = p.origin := rfl
  have e₂ : p.bottomLink.target = p.rightLink.source := rfl
  have e₃ : p.rightLink.target = p.topLink.target :=
    Subtype.ext (add_right_comm _ _ _)
  have e₄ : p.topLink.source = p.leftLink.target := rfl
  have e₅ : p.leftLink.source = p.origin := rfl
  simp only [plaquetteHolonomy, gaugeAct, hG]
  rw [e₁, e₂, e₃, e₄, e₅]
  group
theorem fullTrace_conj (a w : ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.fullTrace ((a * w * a⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      ComplexMatrix2.fullTrace (w : ComplexMatrix2) := by apply _root_.YangMills.Construction.InfiniteLattice.SUTwoTrace.fullTrace_conj <;> assumption
end Holonomy
section SliceEnergy
variable {μ : Fin 4} (B : Block μ)
theorem touchingPlaquettes_finite : B.touchingPlaquettes.Finite := by apply _root_.YangMills.Construction.TransferOperators.Block.touchingPlaquettes_finite <;> assumption
theorem gluedConfiguration_restrict (w : B.thickened → ComplexMatrix2.specialUnitary) :
    B.gluedConfiguration (fun b => w ⟨b.1, B.subset_thickened b.2⟩) (fun b => w ⟨b.1, b.2.1⟩) = w := by
  funext b
  simp only [Block.gluedConfiguration]
  split_ifs <;> rfl
theorem gluedConfiguration_gaugeAct (g : B.thickenedBlock.vertices → ComplexMatrix2.specialUnitary)
    (u : B.links → ComplexMatrix2.specialUnitary)
    (η : ↥(B.thickened \ (B.links : Set (SliceLink μ))) → ComplexMatrix2.specialUnitary) :
    B.gluedConfiguration (gaugeAct B.links_subset_linksWithin_thickenedBlock g u)
        (gaugeAct B.collar_subset_linksWithin_thickenedBlock g η) =
      gaugeAct B.thickened_subset_linksWithin g (B.gluedConfiguration u η) := by
  funext b
  by_cases h : b.1 ∈ B.links
  · simp only [Block.gluedConfiguration, gaugeAct, dif_pos h]
  · simp only [Block.gluedConfiguration, gaugeAct, dif_neg h]
theorem sliceEnergyOnThickened_eq_sum (β : ℝ) [Fintype B.touchingPlaquettes]
    (w : B.thickened → ComplexMatrix2.specialUnitary) :
    B.sliceEnergyOnThickened β w = (β : ℂ) * ∑ p : B.touchingPlaquettes, (1 - (1 / 2 : ℂ) *
      ComplexMatrix2.fullTrace ((plaquetteHolonomy p.1 (B.links_subset_thickened p) w :
        ComplexMatrix2.specialUnitary) : ComplexMatrix2)) := by
  rw [Block.sliceEnergyOnThickened, Block.sliceEnergy,
    gluedConfiguration_restrict B, finsum_eq_sum_of_fintype]
theorem isEntryPolynomial_sliceEnergyOnThickened (β : ℝ) :
    IsEntryPolynomial (B.sliceEnergyOnThickened β) := by
  let _ : Fintype B.touchingPlaquettes := (touchingPlaquettes_finite B).fintype
  have h : B.sliceEnergyOnThickened β = fun w => (β : ℂ) * ∑ p : B.touchingPlaquettes,
      (1 - (1 / 2 : ℂ) * ComplexMatrix2.fullTrace ((plaquetteHolonomy p.1
        (B.links_subset_thickened p) w : ComplexMatrix2.specialUnitary) : ComplexMatrix2)) :=
    funext (sliceEnergyOnThickened_eq_sum B β)
  rw [h]
  refine isEntryPolynomial_mul (isEntryPolynomial_const _)
    (isEntryPolynomial_finsetSum _ _ fun p _ => ?_)
  have hn : IsEntryPolynomial fun w : B.thickened → ComplexMatrix2.specialUnitary =>
      (-(1 / 2 : ℂ)) * ComplexMatrix2.fullTrace ((plaquetteHolonomy p.1
        (B.links_subset_thickened p) w : ComplexMatrix2.specialUnitary) : ComplexMatrix2) :=
    isEntryPolynomial_mul (isEntryPolynomial_const _) (isEntryPolynomial_trace_holonomy p.1 _)
  have := isEntryPolynomial_add (isEntryPolynomial_const (J := B.thickened) 1) hn
  simpa only [sub_eq_add_neg, neg_mul] using this
theorem sliceEnergyOnThickened_im (β : ℝ)
    (htr : ∀ w : ComplexMatrix2.specialUnitary, (ComplexMatrix2.fullTrace (w : ComplexMatrix2)).im = 0)
    (w : B.thickened → ComplexMatrix2.specialUnitary) : (B.sliceEnergyOnThickened β w).im = 0 := by
  let _ : Fintype B.touchingPlaquettes := (touchingPlaquettes_finite B).fintype
  rw [sliceEnergyOnThickened_eq_sum B β, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.im_sum]
  have h : ∀ p : B.touchingPlaquettes, ((1 - (1 / 2 : ℂ) *
      ComplexMatrix2.fullTrace ((plaquetteHolonomy p.1 (B.links_subset_thickened p) w :
        ComplexMatrix2.specialUnitary) : ComplexMatrix2))).im = 0 := by
    intro p
    have ht := htr (plaquetteHolonomy p.1 (B.links_subset_thickened p) w)
    generalize ComplexMatrix2.fullTrace ((plaquetteHolonomy p.1 (B.links_subset_thickened p) w :
      ComplexMatrix2.specialUnitary) : ComplexMatrix2) = t at ht
    have h₁ : t = (t.re : ℂ) := Complex.ext (by simp) (by simp [ht])
    rw [h₁]
    have h₂ : (1 - (1 / 2 : ℂ) * (t.re : ℂ)) = ((1 - 1 / 2 * t.re : ℝ) : ℂ) := by push_cast; ring
    rw [h₂, Complex.ofReal_im]
  rw [Finset.sum_eq_zero fun p _ => h p, mul_zero]
theorem sliceEnergy_gaugeAct (β : ℝ) (u : B.links → ComplexMatrix2.specialUnitary)
    (η : ↥(B.thickened \ (B.links : Set (SliceLink μ))) → ComplexMatrix2.specialUnitary)
    (g : B.thickenedBlock.vertices → ComplexMatrix2.specialUnitary) :
    B.sliceEnergy β (gaugeAct B.links_subset_linksWithin_thickenedBlock g u)
        (gaugeAct B.collar_subset_linksWithin_thickenedBlock g η) =
      B.sliceEnergy β u η := by
  rw [Block.sliceEnergy, Block.sliceEnergy,
    gluedConfiguration_gaugeAct B]
  refine congrArg _ (finsum_congr fun p => ?_)
  have hmem : p.1.bottomLink ∈ p.1.links := by simp [SlicePlaquette.links]
  have hb : p.1.origin ∈ B.thickenedBlock.vertices :=
    (B.thickened_subset_linksWithin (B.links_subset_thickened p hmem)).1
  rw [plaquetteHolonomy_gaugeAct p.1 (B.links_subset_thickened p) B.thickened_subset_linksWithin hb,
    fullTrace_conj]
end SliceEnergy
section ProductKernel
variable {β : ℝ}
theorem linkProductKernel_eq_ofReal
    (hreal : ∀ w : ComplexMatrix2.specialUnitary, (singleBondWeight β w).im = 0) {B : Type}
    [Fintype B] (u u' : B → ComplexMatrix2.specialUnitary) :
    linkProductKernel β u u' = ((∏ b, (singleBondWeight β (u b * (u' b)⁻¹)).re : ℝ) : ℂ) := by
  rw [linkProductKernel, finprod_eq_prod_of_fintype, Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun b _ => Complex.ext (by simp) (by simp [hreal])
theorem linkProductKernel_comm
    (hinv : ∀ w : ComplexMatrix2.specialUnitary, singleBondWeight β w⁻¹ = singleBondWeight β w)
    {B : Type} (u u' : B → ComplexMatrix2.specialUnitary) :
    linkProductKernel β u u' = linkProductKernel β u' u := by
  refine finprod_congr fun b => ?_
  rw [← hinv, mul_inv_rev, inv_inv]
theorem linkProductKernel_bounds
    (hreal : ∀ w : ComplexMatrix2.specialUnitary, (singleBondWeight β w).im = 0)
    (hbound : ∀ w : ComplexMatrix2.specialUnitary, Real.exp (-2 * β) ≤ (singleBondWeight β w).re ∧
      (singleBondWeight β w).re ≤ 1) {B : Type} [Finite B] (u u' : B → ComplexMatrix2.specialUnitary) :
    (linkProductKernel β u u').im = 0 ∧
      Real.exp (-2 * β * (Nat.card B : ℝ)) ≤ (linkProductKernel β u u').re ∧
      (linkProductKernel β u u').re ≤ 1 := by
  let _ : Fintype B := Fintype.ofFinite B
  rw [linkProductKernel_eq_ofReal hreal, Complex.ofReal_im, Complex.ofReal_re]
  have hpos : ∀ b, 0 ≤ (singleBondWeight β (u b * (u' b)⁻¹)).re := fun b =>
    (Real.exp_pos _).le.trans (hbound _).1
  refine ⟨rfl, ?_, Finset.prod_le_one (fun b _ => hpos b) fun b _ => (hbound _).2⟩
  have hconst : Real.exp (-2 * β * (Nat.card B : ℝ)) = ∏ _b : B, Real.exp (-2 * β) := by
    rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card, mul_comm, Real.exp_nat_mul]
  rw [hconst]
  exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun b _ => (hbound _).1
theorem linkProductKernel_smooth (h : FieldCalculus.AllRules) (hβ : 0 < β) (B : Type) [Finite B]
    [Nonempty B] :
    (fun w : B ⊕ B → ComplexMatrix2.specialUnitary =>
      linkProductKernel β (fun b => w (Sum.inl b)) fun b => w (Sum.inr b)) ∈ smoothSet := by
  obtain ⟨-, -, hJ⟩ := h
  obtain ⟨-, halg, -, -, -, hpw, -⟩ := hJ (B ⊕ B)
  obtain ⟨⟨A, hA⟩, -⟩ := halg ⊤
  have hA' : (A : Set ((B ⊕ B → ComplexMatrix2.specialUnitary) → ℂ)) = smoothSet := hA
  let _ : Fintype B := Fintype.ofFinite B
  have hprod : (fun w : B ⊕ B → ComplexMatrix2.specialUnitary =>
      linkProductKernel β (fun b => w (Sum.inl b)) fun b => w (Sum.inr b)) =
      ∏ b : B, fun w : B ⊕ B → ComplexMatrix2.specialUnitary =>
        singleBondWeight β (w (Sum.inl b) * (w (Sum.inr b))⁻¹) := by
    funext w
    rw [linkProductKernel, finprod_eq_prod_of_fintype, Finset.prod_apply]
  rw [hprod, ← hA']
  exact prod_mem fun b _ => by
    have hb := (hpw.2 β hβ (Sum.inl b) (Sum.inr b) Sum.inl_ne_inr).1
    rw [← hA'] at hb
    exact hb
theorem linkProductKernel_gaugeAct
    (hclass : ∀ g w : ComplexMatrix2.specialUnitary,
      singleBondWeight β (g * w * g⁻¹) = singleBondWeight β w) {μ : Fin 4}
    {v : Set (SliceSite μ)} {S : Set (SliceLink μ)} (hv : S ⊆ linksWithin v)
    (g : v → ComplexMatrix2.specialUnitary) (u u' : S → ComplexMatrix2.specialUnitary) :
    linkProductKernel β (gaugeAct hv g u) (gaugeAct hv g u') = linkProductKernel β u u' := by
  refine finprod_congr fun b => ?_
  rw [← hclass (g ⟨b.1.source, (hv b.2).1⟩) (u b * (u' b)⁻¹)]
  simp only [gaugeAct]
  congr 1
  group
end ProductKernel
theorem statement_holds (h₁ : FieldCalculus.AllRules) (h₂ : TraceAndSingleBondWeight) :
    Statement := by
  intro β hβ
  obtain ⟨hfacts, hweight⟩ := h₂
  obtain ⟨⟨hreal, -, hclass, hinv⟩, hbound, -⟩ := hweight β hβ
  have htr : ∀ w : ComplexMatrix2.specialUnitary,
      (ComplexMatrix2.fullTrace (w : ComplexMatrix2)).im = 0 := fun w =>
    (hfacts.2 w).2.2.2.2.2.1
  refine ⟨fun B _ _ => ⟨fun u u' => ?_, linkProductKernel_smooth h₁ hβ B⟩, ?_, ?_, ?_⟩
  · exact ⟨linkProductKernel_comm hinv u u', linkProductKernel_bounds hreal hbound u u'⟩
  · intro μ B g u u'
    exact linkProductKernel_gaugeAct hclass _ g u u'
  · intro μ p u g
    exact plaquetteHolonomy_gaugeAct p Subset.rfl _ p.origin_mem_cornerSites g u
  · intro μ B
    exact ⟨⟨isEntryPolynomial_sliceEnergyOnThickened B β, sliceEnergyOnThickened_im B β htr⟩,
      fun u η g => sliceEnergy_gaugeAct B β u η g⟩
end YangMills.Construction.TransferOperators.KernelSymmetryAndGaugeInvariance
end
