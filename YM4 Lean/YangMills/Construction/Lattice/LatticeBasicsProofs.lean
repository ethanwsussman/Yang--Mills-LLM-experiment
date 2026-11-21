import YangMills.Construction.Lattice.SiteCoordinatesProof
import YangMills.Construction.Lattice.CountingSitesBondsPlaquettes
import YangMills.Construction.Lattice.LatticeBasicsAndSummationByParts
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice.LatticeBasics
open Matrices
variable {L m : ℕ} {j : ℤ}
theorem meshSize_pos (hL : 0 < L) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p16883 <;> assumption
theorem two_le_sitesPerAxis (hL : 0 < L) : 2 ≤ gridSideLength L m j := by
  have : 0 < L ^ ((m : ℤ) + j).toNat := Nat.pow_pos hL
  simp only [gridSideLength]
  omega
theorem intMul_meshSize_coe_eq_zero_iff (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (n : ℤ) :
    (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 ↔
      (gridSideLength L m j : ℤ) ∣ n := by apply _root_.YangMills.DeltaSharedProofs.p501788 <;> assumption
theorem shiftedPoint_apply (x : Site L m j) (n : Fin 4 → ℤ) (μ : Fin 4) :
    shiftedPoint x n μ =
      (x : FourTorus L m) μ + (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
  classical
  simp [shiftedPoint, pointOnAxis, Finset.sum_apply, Pi.single_apply]
def siteOfIntCoords (n : Fin 4 → ℤ) : Site L m j :=
  ⟨fun μ => (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)), ⟨n, fun _ => rfl⟩⟩
theorem shiftedPoint_eq_add (x : Site L m j) (n : Fin 4 → ℤ) :
    shiftedPoint x n = ((x + siteOfIntCoords n : Site L m j) : FourTorus L m) := by
  funext μ
  rw [shiftedPoint_apply]
  rfl
theorem natCard_site (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    Nat.card (Site L m j) = gridSideLength L m j ^ 4 := by apply _root_.YangMills.Construction.PeriodicLattice.Counting.card_site_eq <;> assumption
theorem site_finite (hL : 0 < L) (hj : -(m : ℤ) ≤ j) : Finite (Site L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.Counting.site_finite <;> assumption
theorem siteFacts_hold (hL : 0 < L) (hj : -(m : ℤ) ≤ j) : SiteFacts L m j := by
  refine ⟨fun x n => ⟨?_, ?_⟩, natCard_site hL hj, two_le_sitesPerAxis hL, fun n =>
    ⟨fun x => x + siteOfIntCoords n, (Equiv.addRight _).bijective,
      fun x => (shiftedPoint_eq_add x n).symm⟩⟩
  · rw [shiftedPoint_eq_add]
    exact (x + siteOfIntCoords n).2
  · constructor
    · intro hx
      have hall : ∀ μ, (gridSideLength L m j : ℤ) ∣ n μ := fun μ => by
        rw [← intMul_meshSize_coe_eq_zero_iff hL hj]
        have := congrFun hx μ
        rw [shiftedPoint_apply] at this
        simpa using this
      choose k hk using hall
      exact ⟨k, funext fun μ => by simp [hk μ]⟩
    · rintro ⟨k, rfl⟩
      funext μ
      rw [shiftedPoint_apply]
      have hzero : ((((((gridSideLength L m j : ℤ) • k) μ : ℤ) : ℝ) * meshSize L j : ℝ) :
          AddCircle (torusSide L m)) = 0 :=
        (intMul_meshSize_coe_eq_zero_iff hL hj _).2 ⟨k μ, by simp⟩
      rw [hzero, add_zero]
theorem unitStep_apply (μ ν : Fin 4) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) ν =
      if ν = μ then ((meshSize L j : ℝ) : AddCircle (torusSide L m)) else 0 := by
  by_cases hνμ : ν = μ
  · subst hνμ
    simp [unitStep, pointOnAxis]
  · simp [unitStep, pointOnAxis, hνμ]
theorem unitStep_injective (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    Function.Injective (unitStep L m j) := by
  intro μ ν hμν
  by_contra hne
  have hval := congrFun (congrArg Subtype.val hμν) μ
  have hval' : ((unitStep L m j μ : Site L m j) : FourTorus L m) μ =
      ((unitStep L m j ν : Site L m j) : FourTorus L m) μ := hval
  rw [unitStep_apply, unitStep_apply, if_pos rfl, if_neg hne] at hval'
  have hone : ((((1 : ℤ) : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
    simpa using hval'
  have hdvd := (intMul_meshSize_coe_eq_zero_iff hL hj 1).1 hone
  have hle := Int.le_of_dvd one_pos hdvd
  have htwo := two_le_sitesPerAxis (m := m) (j := j) hL
  omega
theorem bondFacts_hold (hL : 0 < L) (hj : -(m : ℤ) ≤ j) : BondFacts L m j := by
  refine ⟨fun μ x => ⟨μ, by simp [Bond.forwardFrom]⟩, ?_, ?_, ?_, fun b => Bond.ext rfl rfl⟩
  · rintro b ⟨μ, hμ⟩
    refine ⟨(μ, b.source), Bond.ext rfl (by simp [Bond.forwardFrom, ← hμ]), ?_⟩
    rintro ⟨ν, x⟩ hb
    have hsrc : x = b.source := congrArg Bond.source hb
    have htgt : x + unitStep L m j ν = b.target := congrArg Bond.target hb
    have hstep : unitStep L m j ν = unitStep L m j μ := by
      rw [← hμ, ← htgt, hsrc]
      abel
    exact Prod.ext (unitStep_injective hL hj hstep) hsrc
  · intro b
    obtain ⟨μ, hb | hb⟩ := b.isNeighbour
    · exact Or.inl ⟨μ, hb⟩
    · refine Or.inr ⟨μ, ?_⟩
      show b.source - b.target = _
      rw [← neg_sub, hb, neg_neg]
  · intro b
    constructor
    · rintro ⟨⟨μ, hfwd⟩, ⟨ν, hbwd⟩⟩
      have hbwd' : b.source - b.target = unitStep L m j ν := hbwd
      exact ⟨μ, ν, by rw [← hfwd]; abel, by rw [← hbwd']; abel⟩
    · rintro ⟨μ, ν, hfwd, hbwd⟩
      refine ⟨⟨μ, sub_eq_iff_eq_add'.mpr hfwd⟩, ⟨ν, ?_⟩⟩
      show b.source - b.target = _
      exact sub_eq_iff_eq_add'.mpr hbwd
theorem fullTrace_cyclic (X A Y B : ComplexMatrix2) :
    ComplexMatrix2.fullTrace (X * (A * Y * B)) = ComplexMatrix2.fullTrace (B * X * A * Y) := by
  simp only [ComplexMatrix2.fullTrace]
  rw [show X * (A * Y * B) = (X * A * Y) * B by simp only [mul_assoc], Matrix.trace_mul_comm]
  simp only [mul_assoc]
theorem fullTrace_pairing_nondegenerate (X : ComplexMatrix2)
    (h : ∀ Y : ComplexMatrix2, ComplexMatrix2.fullTrace (X * Y) = 0) : X = 0 := by
  have e00 := h !![1, 0; 0, 0]
  have e10 := h !![0, 1; 0, 0]
  have e01 := h !![0, 0; 1, 0]
  have e11 := h !![0, 0; 0, 1]
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10 e01 e11
  ext i k
  fin_cases i <;> fin_cases k <;> simp [e00, e10, e01, e11]
theorem fullTrace_pairing_nondegenerate_traceless (X : ComplexMatrix2)
    (hX : X ∈ ComplexMatrix2.traceless)
    (h : ∀ Y ∈ ComplexMatrix2.traceless, ComplexMatrix2.fullTrace (X * Y) = 0) : X = 0 := by
  have hX' : ComplexMatrix2.fullTrace X = 0 := hX
  have hdiag := h !![1, 0; 0, -1]
    (by show ComplexMatrix2.fullTrace _ = 0; simp [Matrix.trace_fin_two])
  have e10 := h !![0, 1; 0, 0] (by show ComplexMatrix2.fullTrace _ = 0; simp [Matrix.trace_fin_two])
  have e01 := h !![0, 0; 1, 0] (by show ComplexMatrix2.fullTrace _ = 0; simp [Matrix.trace_fin_two])
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at hX' hdiag e10 e01
  have e00 : X 0 0 = 0 := by linear_combination (hX' + hdiag) / 2
  have e11 : X 1 1 = 0 := by linear_combination (hX' - hdiag) / 2
  ext i k
  fin_cases i <;> fin_cases k <;> simp [e00, e10, e01, e11]
theorem traceFacts_hold : TraceFacts := by
  refine ⟨fun T hT => ?_, fullTrace_pairing_nondegenerate,
    fullTrace_pairing_nondegenerate_traceless⟩
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT
  have hinv : (T⁻¹)⁻¹ = T := Matrix.nonsing_inv_nonsing_inv T hdet
  have hleft : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hdet
  have hright : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hdet
  have hconj : ∀ X : ComplexMatrix2,
      ComplexMatrix2.fullTrace (T * X * T⁻¹) = ComplexMatrix2.fullTrace X := fun X => by
    simp only [ComplexMatrix2.fullTrace]
    rw [Matrix.trace_mul_comm, ← mul_assoc, hleft, one_mul]
  have hconj' : ∀ X : ComplexMatrix2,
      ComplexMatrix2.fullTrace (T⁻¹ * X * T) = ComplexMatrix2.fullTrace X := fun X => by
    simp only [ComplexMatrix2.fullTrace]
    rw [Matrix.trace_mul_comm, ← mul_assoc, hright, one_mul]
  have hinvConj : ∀ X : ComplexMatrix2, ComplexMatrix2.conjugateBy T⁻¹ X = T⁻¹ * X * T :=
    fun X => by simp only [ComplexMatrix2.conjugateBy, hinv]
  have hlin : ∀ S : ComplexMatrix2, IsLinearMap ℂ (ComplexMatrix2.conjugateBy S) := fun S =>
    ⟨fun X Y => by simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul],
      fun c X => by simp only [ComplexMatrix2.conjugateBy, mul_smul_comm, smul_mul_assoc]⟩
  refine ⟨hconj, ?_, hinvConj, ?_, ?_, hlin _, hlin _, ?_⟩
  · intro X Y
    rw [hinvConj]
    simp only [ComplexMatrix2.conjugateBy]
    rw [fullTrace_cyclic]
  · intro X
    rw [hinvConj]
    simp only [ComplexMatrix2.conjugateBy]
    calc T⁻¹ * (T * X * T⁻¹) * T = (T⁻¹ * T) * X * (T⁻¹ * T) := by simp only [mul_assoc]
      _ = X := by rw [hleft, one_mul, mul_one]
  · intro X
    rw [hinvConj]
    simp only [ComplexMatrix2.conjugateBy]
    calc T * (T⁻¹ * X * T) * T⁻¹ = (T * T⁻¹) * X * (T * T⁻¹) := by simp only [mul_assoc]
      _ = X := by rw [hright, one_mul, mul_one]
  · intro X hX
    have hX' : ComplexMatrix2.fullTrace X = 0 := hX
    refine ⟨?_, ?_⟩
    · show ComplexMatrix2.fullTrace (ComplexMatrix2.conjugateBy T X) = 0
      simp only [ComplexMatrix2.conjugateBy]
      rw [hconj, hX']
    · show ComplexMatrix2.fullTrace (ComplexMatrix2.conjugateBy T⁻¹ X) = 0
      rw [hinvConj, hconj', hX']
theorem families_nondegenerate : TraceFormNondegenerateOnFamilies := by
  intro V hV I _ f hf h
  classical
  funext ι
  have hkey : ∀ Y ∈ V, ComplexMatrix2.fullTrace (f ι * Y) = 0 := fun Y hY => by
    have hsingle := h (Pi.single ι Y) (fun κ => by
      by_cases hκ : κ = ι
      · subst hκ
        simpa using hY
      · rw [Pi.single_eq_of_ne hκ]
        exact V.zero_mem)
    rw [Finset.sum_eq_single ι (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp),
      Pi.single_eq_same] at hsingle
    exact hsingle
  show f ι = 0
  rcases hV with rfl | rfl
  · exact fullTrace_pairing_nondegenerate_traceless _ (hf ι) hkey
  · exact fullTrace_pairing_nondegenerate _ (fun Y => hkey Y trivial)
theorem sum_trace_covDeriv_eq [Fintype (Site L m j)] (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (f g : Site L m j → ComplexMatrix2) (ν : Fin 4) :
    ∑ x : Site L m j, ComplexMatrix2.fullTrace (f x * covDeriv ξ U ν g x) =
      ∑ x : Site L m j, ComplexMatrix2.fullTrace (covDerivTranspose ξ U ν f x * g x) := by
  have hfwd : ∀ x : Site L m j, ComplexMatrix2.fullTrace (f x * covDeriv ξ U ν g x) =
      ((ξ⁻¹ : ℝ) : ℂ) * ComplexMatrix2.fullTrace (f x *
          ComplexMatrix2.conjugateBy (U (Bond.forwardFrom x ν)) (g (x + unitStep L m j ν))) -
        ((ξ⁻¹ : ℝ) : ℂ) * ComplexMatrix2.fullTrace (f x * g x) := fun x => by
    simp only [covDeriv, ComplexMatrix2.fullTrace, mul_smul_comm, mul_sub, Matrix.trace_smul,
      Matrix.trace_sub, smul_eq_mul]
  have hbwd : ∀ x : Site L m j, ComplexMatrix2.fullTrace (covDerivTranspose ξ U ν f x * g x) =
      ((ξ⁻¹ : ℝ) : ℂ) * ComplexMatrix2.fullTrace
          ((U (Bond.forwardFrom (x - unitStep L m j ν) ν))⁻¹ *
            f (x - unitStep L m j ν) * U (Bond.forwardFrom (x - unitStep L m j ν) ν) * g x) -
        ((ξ⁻¹ : ℝ) : ℂ) * ComplexMatrix2.fullTrace (f x * g x) := fun x => by
    simp only [covDerivTranspose, ComplexMatrix2.fullTrace, smul_mul_assoc, sub_mul,
      Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul, mul_sub]
  simp only [hfwd, hbwd, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 2
  rw [← Equiv.sum_comp (Equiv.addRight (unitStep L m j ν)) (fun x : Site L m j =>
    ComplexMatrix2.fullTrace ((U (Bond.forwardFrom (x - unitStep L m j ν) ν))⁻¹ *
      f (x - unitStep L m j ν) * U (Bond.forwardFrom (x - unitStep L m j ν) ν) * g x))]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, ComplexMatrix2.conjugateBy]
  exact fullTrace_cyclic _ _ _ _
theorem summationByParts_holds [Finite (Site L m j)] (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) :
    SummationByParts ξ U := by
  let := Fintype.ofFinite (Site L m j)
  intro f g ν
  simp only [finsum_eq_sum_of_fintype]
  exact sum_trace_covDeriv_eq ξ U f g ν
theorem plaquetteFamilyComponent_swap (F : PlaquetteFamily L m j) {μ ν : Fin 4} (h : μ ≠ ν)
    (x : Site L m j) :
    plaquetteFamilyComponent F ν μ x = -plaquetteFamilyComponent F μ ν x := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · simp [plaquetteFamilyComponent, plaquetteFormOf, hlt, not_lt_of_gt hlt]
  · simp [plaquetteFamilyComponent, plaquetteFormOf, hgt, not_lt_of_gt hgt]
theorem plaquetteFamilyComponent_add (F G : PlaquetteFamily L m j) (μ ν : Fin 4)
    (x : Site L m j) :
    plaquetteFamilyComponent (F + G) μ ν x =
      plaquetteFamilyComponent F μ ν x + plaquetteFamilyComponent G μ ν x := by
  simp only [plaquetteFamilyComponent, plaquetteFormOf]
  split_ifs
  · rfl
  · simp only [Pi.add_apply, neg_add]
  · simp
theorem plaquetteFamilyComponent_smul (c : ℂ) (F : PlaquetteFamily L m j) (μ ν : Fin 4)
    (x : Site L m j) :
    plaquetteFamilyComponent (c • F) μ ν x = c • plaquetteFamilyComponent F μ ν x := by
  simp only [plaquetteFamilyComponent, plaquetteFormOf]
  split_ifs
  · rfl
  · simp only [Pi.smul_apply, smul_neg]
  · simp
theorem plaquetteFamilyExteriorDerivTranspose_eq {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField complexGaugeGroup Set.univ U) (F : PlaquetteFamily L m j) (μ : Fin 4)
    (x : Site L m j) :
    plaquetteFamilyExteriorDerivTranspose ξ U F μ x =
      ((ξ⁻¹ : ℝ) : ℂ) • ∑ ν ∈ Finset.univ.erase μ,
        (plaquetteFamilyComponent F μ ν x -
          ComplexMatrix2.conjugateBy (U (Bond.forwardFrom (x - unitStep L m j ν) ν))⁻¹
            (plaquetteFamilyComponent F μ ν (x - unitStep L m j ν))) := by
  rw [Finset.smul_sum]
  simp only [plaquetteFamilyExteriorDerivTranspose]
  refine Finset.sum_congr rfl fun ν hν => ?_
  have hne : μ ≠ ν := (Finset.ne_of_mem_erase hν).symm
  simp only [covDerivTranspose]
  rw [plaquetteFamilyComponent_swap F hne x,
    plaquetteFamilyComponent_swap F hne (x - unitStep L m j ν)]
  congr 1
  have hdet : (U (Bond.forwardFrom (x - unitStep L m j ν) ν)).det = 1 :=
    hU.1 _ (Set.mem_univ _)
  have hinv := Matrix.nonsing_inv_nonsing_inv (U (Bond.forwardFrom (x - unitStep L m j ν) ν))
    (by rw [hdet]; exact isUnit_one)
  simp only [ComplexMatrix2.conjugateBy, hinv, mul_neg, neg_mul]
  abel
theorem plaquetteFamilyExteriorDerivTranspose_isLinearMap (ξ : ℝ)
    (U : Bond L m j → ComplexMatrix2) :
    IsLinearMap ℂ (plaquetteFamilyExteriorDerivTranspose (L := L) (m := m) (j := j) ξ U) := by
  constructor
  · intro F G
    funext μ x
    simp only [plaquetteFamilyExteriorDerivTranspose, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [covDerivTranspose, plaquetteFamilyComponent_add]
    rw [← smul_add]
    congr 1
    simp only [mul_add, add_mul]
    abel
  · intro c F
    funext μ x
    simp only [plaquetteFamilyExteriorDerivTranspose, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [covDerivTranspose, plaquetteFamilyComponent_smul]
    rw [smul_comm]
    congr 1
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
theorem sum_Ioi_symm_eq_sum_erase (G : Fin 4 → Fin 4 → ℂ) :
    ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ, (G μ ν + G ν μ) =
      ∑ μ : Fin 4, ∑ ν ∈ Finset.univ.erase μ, G ν μ := by
  have i0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
  have i1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
  have i2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
  have i3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide
  have r0 : Finset.univ.erase (0 : Fin 4) = {1, 2, 3} := by decide
  have r1 : Finset.univ.erase (1 : Fin 4) = {0, 2, 3} := by decide
  have r2 : Finset.univ.erase (2 : Fin 4) = {0, 1, 3} := by decide
  have r3 : Finset.univ.erase (3 : Fin 4) = {0, 1, 2} := by decide
  rw [Fin.sum_univ_four, Fin.sum_univ_four, i0, i1, i2, i3, r0, r1, r2, r3]
  simp
  ring
theorem plaquetteFamilyInner_exteriorDeriv [Fintype (Site L m j)] (ξ : ℝ)
    (U : Bond L m j → ComplexMatrix2) (F : PlaquetteFamily L m j) (A : AxisSiteFamily L m j) :
    plaquetteFamilyInner ξ F (plaquetteFamilyExteriorDeriv ξ U A) =
      axisFamilyInner ξ (plaquetteFamilyExteriorDerivTranspose ξ U F) A := by
  simp only [plaquetteFamilyInner, plaquetteFormInner, axisFamilyInner, finsum_eq_sum_of_fintype]
  congr 1
  let G : Fin 4 → Fin 4 → ℂ := fun ν μ => ∑ x : Site L m j,
    ComplexMatrix2.fullTrace (plaquetteFamilyComponent F ν μ x * covDeriv ξ U ν (A μ) x)
  have hterm : ∀ (x : Site L m j) (μ ν : Fin 4), ν ∈ Finset.Ioi μ →
      ComplexMatrix2.halfTrace (plaquetteFamilyComponent F μ ν x *
          plaquetteFamilyComponent (plaquetteFamilyExteriorDeriv ξ U A) μ ν x) =
        (1 / 2 : ℂ) * (ComplexMatrix2.fullTrace (plaquetteFamilyComponent F μ ν x *
            covDeriv ξ U μ (A ν) x) +
          ComplexMatrix2.fullTrace (plaquetteFamilyComponent F ν μ x *
            covDeriv ξ U ν (A μ) x)) := by
    intro x μ ν hν
    have hlt : μ < ν := Finset.mem_Ioi.mp hν
    have hcurl : plaquetteFamilyComponent (plaquetteFamilyExteriorDeriv ξ U A) μ ν x =
        covDeriv ξ U μ (A ν) x - covDeriv ξ U ν (A μ) x := by
      simp [plaquetteFamilyComponent, plaquetteFormOf, hlt, plaquetteFamilyExteriorDeriv]
    rw [hcurl, plaquetteFamilyComponent_swap F hlt.ne x]
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, mul_sub, neg_mul,
      Matrix.trace_sub, Matrix.trace_neg]
    ring
  have hleft : ∑ x : Site L m j, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
      ComplexMatrix2.halfTrace (plaquetteFamilyComponent F μ ν x *
        plaquetteFamilyComponent (plaquetteFamilyExteriorDeriv ξ U A) μ ν x) =
      (1 / 2 : ℂ) * ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ, (G μ ν + G ν μ) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν hν => ?_
    rw [Finset.sum_congr rfl fun x _ => hterm x μ ν hν, ← Finset.mul_sum,
      Finset.sum_add_distrib]
  have hright : ∑ x : Site L m j, ∑ μ : Fin 4,
      ComplexMatrix2.halfTrace (plaquetteFamilyExteriorDerivTranspose ξ U F μ x * A μ x) =
      (1 / 2 : ℂ) * ∑ μ : Fin 4, ∑ ν ∈ Finset.univ.erase μ, G ν μ := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    simp only [plaquetteFamilyExteriorDerivTranspose, Finset.sum_mul, ComplexMatrix2.fullTrace,
      Matrix.trace_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    exact (sum_trace_covDeriv_eq ξ U (plaquetteFamilyComponent F ν μ) (A μ) ν).symm
  rw [hleft, hright, sum_Ioi_symm_eq_sum_erase]
theorem conclusion_holds : Conclusion := by
  intro L m j ξ U hL _ hj _ hU
  obtain ⟨_, hbig⟩ := hL
  have hLpos : 0 < L := by omega
  have := site_finite hLpos hj
  let := Fintype.ofFinite (Site L m j)
  refine ⟨siteFacts_hold hLpos hj, bondFacts_hold hLpos hj, traceFacts_hold,
    families_nondegenerate, summationByParts_holds ξ U,
    plaquetteFamilyExteriorDerivTranspose_eq hU,
    plaquetteFamilyExteriorDerivTranspose_isLinearMap ξ U, fun F A => ?_⟩
  exact plaquetteFamilyInner_exteriorDeriv ξ U F A
end YangMills.Construction.PeriodicLattice.LatticeBasics
