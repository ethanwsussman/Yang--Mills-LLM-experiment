import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.LatticeBasicsAndSummationByParts
import YangMills.Construction.Lattice.StandardPartitionCubeGeometry
import YangMills.Construction.Lattice.TransposesOfTheCovariantDerivativesOnALattice
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace CovariantAdjoints
open Matrices
open LatticeBasics
variable {L m : ℕ} {j : ℤ}
private theorem one_lt_cast_of_thirteen_le (hL : 13 ≤ L) : (1 : ℝ) < L := by apply _root_.YangMills.SharedProofs.p15248 <;> assumption
private theorem meshSize_pos (hL : 13 ≤ L) : 0 < meshSize L j :=
  zpow_pos (by linarith [one_lt_cast_of_thirteen_le hL]) _
private theorem torusSide_pos (hL : 13 ≤ L) : 0 < torusSide L m := by apply _root_.YangMills.SharedProofs.p14627 <;> assumption
private theorem two_mul_meshSize_lt_torusSide (hL : 13 ≤ L) (hj : -(m : ℤ) < j) :
    2 * meshSize L j < torusSide L m := by apply _root_.YangMills.SharedProofs.p8012 <;> assumption
private theorem addCircle_coe_ne_zero_of_pos_of_lt {ℓ t : ℝ} (hp : 0 < ℓ) (h₀ : 0 < t)
    (h₁ : t < ℓ) : (t : AddCircle ℓ) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff ℓ).1 h
  rw [zsmul_eq_mul] at hn
  rcases le_or_gt n 0 with h' | h'
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast h'
    nlinarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h'
    nlinarith
abbrev _root_.YangMills.SharedProofs.p5311 := @addCircle_coe_ne_zero_of_pos_of_lt
private theorem unitStep_ne_neg_unitStep (hL : 13 ≤ L) (hj : -(m : ℤ) < j) (μ ν : Fin 4) :
    unitStep L m j μ ≠ -unitStep L m j ν := by apply _root_.YangMills.SharedProofs.p70 <;> assumption
private structure BondStructure (L m : ℕ) (j : ℤ) : Prop where
  isPos : ∀ (x : Site L m j) (μ : Fin 4), (Bond.forwardFrom x μ).IsPositivelyOriented
  fwd_inj : ∀ {x y : Site L m j} {μ ν : Fin 4},
    Bond.forwardFrom y ν = Bond.forwardFrom x μ → y = x ∧ ν = μ
  not_both : ∀ {b : Bond L m j}, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented
  pos_or_opp : ∀ b : Bond L m j, b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented
  exists_fwd : ∀ {b : Bond L m j}, b.IsPositivelyOriented → ∃ x μ, b = Bond.forwardFrom x μ
  axis_fwd : ∀ (x : Site L m j) (μ : Fin 4), (Bond.forwardFrom x μ).axis = μ
  step_ne_zero : ∀ μ : Fin 4, unitStep L m j μ ≠ 0
  finite_sites : Finite (Site L m j)
private theorem bondStructure_of (hL : 13 ≤ L) (hj : -(m : ℤ) < j)
    (hS : LatticeBasics.SiteFacts L m j)
    (hB : LatticeBasics.BondFacts L m j) : BondStructure L m j := by
  obtain ⟨hpos, huniq, heither, hboth, -⟩ := hB
  have hinj : ∀ {x y : Site L m j} {μ ν : Fin 4},
      Bond.forwardFrom y ν = Bond.forwardFrom x μ → y = x ∧ ν = μ := by
    intro x y μ ν h
    obtain ⟨p, -, hp⟩ := huniq (Bond.forwardFrom x μ) (hpos μ x)
    have h₁ := hp (ν, y) h
    have h₂ := hp (μ, x) rfl
    have h₃ := h₁.trans h₂.symm
    exact ⟨congrArg Prod.snd h₃, congrArg Prod.fst h₃⟩
  have hstep : ∀ {μ ν : Fin 4}, unitStep L m j μ = unitStep L m j ν → μ = ν := by
    intro μ ν h
    refine (hinj (x := 0) (y := 0) (μ := ν) (ν := μ) ?_).2
    exact Bond.ext rfl (by simp [Bond.forwardFrom, h])
  refine ⟨fun x μ => hpos μ x, hinj, ?_, heither, ?_, ?_, ?_, ?_⟩
  · intro b hb hr
    obtain ⟨μ, ν, h₁, h₂⟩ := (hboth b).1 ⟨hb, hr⟩
    refine unitStep_ne_neg_unitStep hL hj μ ν ?_
    have h₃ : b.source + unitStep L m j μ + unitStep L m j ν = b.source := by rw [← h₁, ← h₂]
    have h₄ : unitStep L m j μ + unitStep L m j ν = 0 := by
      have : b.source + (unitStep L m j μ + unitStep L m j ν) = b.source + 0 := by
        rw [add_zero, ← add_assoc, h₃]
      exact add_left_cancel this
    exact eq_neg_of_add_eq_zero_left h₄
  · intro b hb
    obtain ⟨p, hp, -⟩ := huniq b hb
    exact ⟨p.2, p.1, hp.symm⟩
  · intro x μ
    have hspec := (Bond.forwardFrom x μ).isNeighbour.choose_spec
    have hd : (Bond.forwardFrom x μ).target - (Bond.forwardFrom x μ).source = unitStep L m j μ := by
      simp [Bond.forwardFrom]
    rcases hspec with h' | h'
    · exact hstep (h'.symm.trans hd)
    · exact absurd (hd.symm.trans h') (unitStep_ne_neg_unitStep hL hj _ _)
  · intro μ h
    exact unitStep_ne_neg_unitStep hL hj μ μ (by rw [h]; simp)
  · have hc := hS.2.1
    have hpos' : 0 < gridSideLength L m j ^ 4 := by
      have := hS.2.2.1
      positivity
    exact (Nat.finite_of_card_ne_zero (by rw [hc]; exact hpos'.ne'))
private theorem bondFormOfPositive_pos (a : Bond L m j → ComplexMatrix2) {b : Bond L m j}
    (hb : b.IsPositivelyOriented) : bondFormOfPositive a b = a b := by
  simp [bondFormOfPositive, hb]
private theorem bondFormOfPositive_not_pos (a : Bond L m j → ComplexMatrix2) {b : Bond L m j}
    (hb : ¬ b.IsPositivelyOriented) : bondFormOfPositive a b = -a b.opposite := by
  simp [bondFormOfPositive, hb]
private theorem opposite_opposite (b : Bond L m j) : b.opposite.opposite = b := rfl
private theorem bondFormOfPositive_opposite (hF : BondStructure L m j)
    (a : Bond L m j → ComplexMatrix2) (b : Bond L m j) :
    bondFormOfPositive a b.opposite = -bondFormOfPositive a b := by
  by_cases hb : b.IsPositivelyOriented
  · rw [bondFormOfPositive_not_pos a (hF.not_both hb), opposite_opposite,
      bondFormOfPositive_pos a hb]
  · have hr : b.opposite.IsPositivelyOriented := (hF.pos_or_opp b).resolve_left hb
    rw [bondFormOfPositive_pos a hr, bondFormOfPositive_not_pos a hb, neg_neg]
private theorem isBondForm_bondFormOfPositive (hF : BondStructure L m j) {𝔥 : Set ComplexMatrix2}
    {a : Bond L m j → ComplexMatrix2} (h : ∀ b : Bond L m j, b.IsPositivelyOriented → a b ∈ 𝔥) :
    IsBondForm 𝔥 (bondFormOfPositive a) :=
  ⟨fun b hb => by rw [bondFormOfPositive_pos a hb]; exact h b hb, bondFormOfPositive_opposite hF a⟩
private theorem bondForm_ext (hF : BondStructure L m j) {𝔥 𝔥' : Set ComplexMatrix2}
    {A B : Bond L m j → ComplexMatrix2} (hA : IsBondForm 𝔥 A) (hB : IsBondForm 𝔥' B)
    (h : ∀ μ x, bondFormComponent A μ x = bondFormComponent B μ x) : A = B := by
  funext b
  rcases hF.pos_or_opp b with hb | hb
  · obtain ⟨x, μ, rfl⟩ := hF.exists_fwd hb
    exact h μ x
  · obtain ⟨x, μ, hx⟩ := hF.exists_fwd hb
    have h₁ := hA.2 b.opposite
    have h₂ := hB.2 b.opposite
    rw [opposite_opposite] at h₁ h₂
    rw [h₁, h₂, hx]
    exact congrArg Neg.neg (h μ x)
private theorem conj_sub (V A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (A - B) =
      ComplexMatrix2.conjugateBy V A - ComplexMatrix2.conjugateBy V B := by
  simp [ComplexMatrix2.conjugateBy, Matrix.mul_sub, Matrix.sub_mul]
private theorem conj_neg (V A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (-A) = -ComplexMatrix2.conjugateBy V A := by
  simp [ComplexMatrix2.conjugateBy]
private theorem conj_zero (V : ComplexMatrix2) : ComplexMatrix2.conjugateBy V 0 = 0 := by
  simp [ComplexMatrix2.conjugateBy]
private theorem conj_smul (V A : ComplexMatrix2) (c : ℂ) :
    ComplexMatrix2.conjugateBy V (c • A) = c • ComplexMatrix2.conjugateBy V A := by
  simp [ComplexMatrix2.conjugateBy]
private theorem conj_sum {ι : Type*} (V : ComplexMatrix2) (s : Finset ι) (f : ι → ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (∑ i ∈ s, f i) = ∑ i ∈ s, ComplexMatrix2.conjugateBy V (f i) := by
  simp [ComplexMatrix2.conjugateBy, Finset.mul_sum, Finset.sum_mul]
private theorem conj_inv_conj {W : ComplexMatrix2} (hW : IsUnit W.det) (Z : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy W⁻¹ (ComplexMatrix2.conjugateBy W Z) = Z := by apply _root_.YangMills.SharedProofs.p32697 <;> assumption
private theorem covDerivTranspose_eq_adjointComponent {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U b).det) (ν : Fin 4) (f : Site L m j → ComplexMatrix2) (x : Site L m j) :
    covDerivTranspose ξ U ν f x = covDerivAdjointComponent ξ U ν f x := by
  unfold covDerivTranspose covDerivAdjointComponent ComplexMatrix2.conjugateBy
  rw [Matrix.nonsing_inv_nonsing_inv _ (hU _)]
private theorem covDerivTranspose_add (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) (ν : Fin 4)
    (f g : Site L m j → ComplexMatrix2) (x : Site L m j) :
    covDerivTranspose ξ U ν (f + g) x =
      covDerivTranspose ξ U ν f x + covDerivTranspose ξ U ν g x := by
  unfold covDerivTranspose
  simp only [Pi.add_apply, Matrix.mul_add, Matrix.add_mul, smul_add, smul_sub, add_sub_add_comm]
private theorem covDerivTranspose_smul (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) (ν : Fin 4)
    (c : ℂ) (f : Site L m j → ComplexMatrix2) (x : Site L m j) :
    covDerivTranspose ξ U ν (c • f) x = c • covDerivTranspose ξ U ν f x := by
  unfold covDerivTranspose
  simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
  rw [smul_comm]
private structure ConjStable (𝒱 : Set ComplexMatrix2) (U : Bond L m j → ComplexMatrix2) : Prop where
  zero_mem : (0 : ComplexMatrix2) ∈ 𝒱
  add_mem : ∀ {a b : ComplexMatrix2}, a ∈ 𝒱 → b ∈ 𝒱 → a + b ∈ 𝒱
  neg_mem : ∀ {a : ComplexMatrix2}, a ∈ 𝒱 → -a ∈ 𝒱
  real_smul_mem : ∀ (r : ℝ) {a : ComplexMatrix2}, a ∈ 𝒱 → ((r : ℝ) : ℂ) • a ∈ 𝒱
  conj_mem : ∀ (b : Bond L m j) {a : ComplexMatrix2}, a ∈ 𝒱 → ComplexMatrix2.conjugateBy (U b) a ∈ 𝒱
  conj_inv_mem : ∀ (b : Bond L m j) {a : ComplexMatrix2}, a ∈ 𝒱 →
    ComplexMatrix2.conjugateBy (U b)⁻¹ a ∈ 𝒱
section
variable {𝒱 : Set ComplexMatrix2} {U : Bond L m j → ComplexMatrix2}
private theorem ConjStable.sub_mem (hS : ConjStable 𝒱 U) {a b : ComplexMatrix2} (ha : a ∈ 𝒱)
    (hb : b ∈ 𝒱) : a - b ∈ 𝒱 := by
  rw [sub_eq_add_neg]
  exact hS.add_mem ha (hS.neg_mem hb)
private theorem ConjStable.sum_mem (hS : ConjStable 𝒱 U) {ι : Type*} (s : Finset ι)
    {f : ι → ComplexMatrix2} (h : ∀ i ∈ s, f i ∈ 𝒱) : ∑ i ∈ s, f i ∈ 𝒱 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hS.zero_mem
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hS.add_mem (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
private theorem covDeriv_mem (hS : ConjStable 𝒱 U) {f : Site L m j → ComplexMatrix2}
    (hf : ∀ y, f y ∈ 𝒱) (ξ : ℝ) (ν : Fin 4) (x : Site L m j) : covDeriv ξ U ν f x ∈ 𝒱 :=
  hS.real_smul_mem _ (hS.sub_mem (hS.conj_mem _ (hf _)) (hf _))
private theorem covDerivTranspose_mem (hS : ConjStable 𝒱 U) (hU : ∀ b, IsUnit (U b).det)
    {f : Site L m j → ComplexMatrix2} (hf : ∀ y, f y ∈ 𝒱) (ξ : ℝ)
    (ν : Fin 4) (x : Site L m j) : covDerivTranspose ξ U ν f x ∈ 𝒱 := by
  rw [covDerivTranspose_eq_adjointComponent hU]
  exact hS.real_smul_mem _ (hS.sub_mem (hS.conj_inv_mem _ (hf _)) (hf _))
private theorem bondFormComponent_mem {A : Bond L m j → ComplexMatrix2} (hF : BondStructure L m j)
    (hA : IsBondForm 𝒱 A) (μ : Fin 4) (x : Site L m j) : bondFormComponent A μ x ∈ 𝒱 :=
  hA.1 _ (hF.isPos x μ)
private theorem plaquetteForm_mem (hS : ConjStable 𝒱 U)
    {F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hF : IsPlaquetteForm 𝒱 F) {ν μ : Fin 4} (h : ν ≠ μ) (y : Site L m j) : F ν μ y ∈ 𝒱 := by
  rcases lt_or_gt_of_ne h with h' | h'
  · exact hF.1 _ _ _ h'
  · rw [hF.2 μ ν y]
    exact hS.neg_mem (hF.1 _ _ _ h')
private theorem covExteriorDeriv_isPlaquetteForm (hS : ConjStable 𝒱 U) (hF : BondStructure L m j)
    {A : Bond L m j → ComplexMatrix2} (hA : IsBondForm 𝒱 A) (ξ : ℝ) :
    IsPlaquetteForm 𝒱 (covExteriorDeriv ξ U A) := by
  refine ⟨fun μ ν x _ => hS.sub_mem ?_ ?_, fun μ ν x => ?_⟩
  · exact covDeriv_mem hS (bondFormComponent_mem hF hA ν) ξ μ x
  · exact covDeriv_mem hS (bondFormComponent_mem hF hA μ) ξ ν x
  · simp [covExteriorDeriv]
end
private theorem zeroExtendSiteField_univ (f : Site L m j → ComplexMatrix2) :
    zeroExtendSiteField (univ : Set (FourTorus L m)) f = f := by apply _root_.YangMills.SharedProofs.p23088 <;> assumption
private theorem zeroExtendBondForm_univ (A : Bond L m j → ComplexMatrix2) :
    zeroExtendBondForm (univ : Set (FourTorus L m)) A = A := by apply _root_.YangMills.SharedProofs.p57978 <;> assumption
private theorem bondFormComponent_covGradient (hF : BondStructure L m j) (ξ : ℝ)
    (U : Bond L m j → ComplexMatrix2) (f : Site L m j → ComplexMatrix2) (μ : Fin 4)
    (x : Site L m j) :
    bondFormComponent (covGradient univ ξ U f) μ x = covDeriv ξ U μ f x := by
  unfold covGradient
  rw [zeroExtendBondForm_univ, zeroExtendSiteField_univ]
  unfold bondFormComponent
  rw [bondFormOfPositive_pos _ (hF.isPos x μ), hF.axis_fwd]
  rfl
private theorem covGradient_isBondForm {𝒱 : Set ComplexMatrix2} {U : Bond L m j → ComplexMatrix2}
    (hS : ConjStable 𝒱 U) (hF : BondStructure L m j) {f : Site L m j → ComplexMatrix2}
    (hf : IsSiteField 𝒱 f) (ξ : ℝ) : IsBondForm 𝒱 (covGradient univ ξ U f) := by
  unfold covGradient
  rw [zeroExtendBondForm_univ, zeroExtendSiteField_univ]
  exact isBondForm_bondFormOfPositive hF fun b _ => covDeriv_mem hS hf ξ _ _
private theorem plaquetteFormOf_antisymm (f : Plaquette L m j → ComplexMatrix2) (μ ν : Fin 4)
    (x : Site L m j) : plaquetteFormOf f ν μ x = -plaquetteFormOf f μ ν x := by apply _root_.YangMills.SharedProofs.p51177 <;> assumption
private theorem antisymm_diag_eq_zero {F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hF : ∀ μ ν x, F ν μ x = -F μ ν x) (μ : Fin 4) (x : Site L m j) : F μ μ x = 0 := by
  ext i k
  have h₁ := congrFun (congrFun (hF μ μ x) i) k
  exact self_eq_neg.1 (by simpa using h₁)
private theorem plaquetteFormOf_family {F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hF : ∀ μ ν x, F ν μ x = -F μ ν x) : plaquetteFormOf (plaquetteFamilyOfComponents F) = F := by
  funext μ ν x
  unfold plaquetteFormOf plaquetteFamilyOfComponents
  rcases lt_trichotomy μ ν with h | h | h
  · simp [h]
  · subst h
    simp [antisymm_diag_eq_zero hF]
  · simp [h, not_lt_of_gt h, hF ν μ x]
section
variable [Fintype (Site L m j)]
open Classical in
private def bondIndicator (x : Site L m j) (μ : Fin 4) (Y : ComplexMatrix2) :
    Bond L m j → ComplexMatrix2 :=
  bondFormOfPositive fun b => if b = Bond.forwardFrom x μ then Y else 0
private theorem bondFormInner_bondIndicator (hF : BondStructure L m j) (ξ : ℝ)
    (C : Bond L m j → ComplexMatrix2) (x : Site L m j) (μ : Fin 4) (Y : ComplexMatrix2) :
    bondFormInner ξ C (bondIndicator x μ Y) =
      ((ξ ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace (C (Bond.forwardFrom x μ) * Y) := by
  classical
  have hv : ∀ y ν, bondFormComponent (bondIndicator x μ Y) ν y =
      if Bond.forwardFrom y ν = Bond.forwardFrom x μ then Y else 0 := by
    intro y ν
    unfold bondFormComponent bondIndicator
    rw [bondFormOfPositive_pos _ (hF.isPos y ν)]
  rw [bondFormInner, finsum_eq_sum_of_fintype]
  congr 1
  rw [Finset.sum_eq_single x, Finset.sum_eq_single μ]
  · rw [hv, if_pos rfl]
    rfl
  · intro ν _ hν
    rw [hv, if_neg fun h => hν (hF.fwd_inj h).2]
    simp
  · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [hv, if_neg fun h => hy (hF.fwd_inj h).1]
    simp
  · simp
open Classical in
private def plaquetteIndicator (p : Plaquette L m j) (Y : ComplexMatrix2) :
    Fin 4 → Fin 4 → Site L m j → ComplexMatrix2 :=
  plaquetteFormOf fun q => if q = p then Y else 0
private theorem plaquetteFormInner_plaquetteIndicator (ξ : ℝ)
    (C : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) (p : Plaquette L m j) (Y : ComplexMatrix2) :
    plaquetteFormInner ξ C (plaquetteIndicator p Y) =
      ((ξ ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace (C p.firstAxis p.secondAxis p.origin * Y) := by
  classical
  have hv : ∀ (y : Site L m j) (μ ν : Fin 4) (h : μ < ν), plaquetteIndicator p Y μ ν y =
      if (⟨y, μ, ν, h⟩ : Plaquette L m j) = p then Y else 0 := by
    intro y μ ν h
    simp [plaquetteIndicator, plaquetteFormOf, h]
  rw [plaquetteFormInner, finsum_eq_sum_of_fintype]
  congr 1
  rw [Finset.sum_eq_single p.origin, Finset.sum_eq_single p.firstAxis,
    Finset.sum_eq_single p.secondAxis]
  · rw [hv _ _ _ p.firstAxis_lt_secondAxis, if_pos rfl]
  · intro ν hν hne
    rw [hv _ _ _ (Finset.mem_Ioi.1 hν), if_neg fun h => hne (by rw [← h])]
    simp
  · intro h
    exact absurd (Finset.mem_Ioi.2 p.firstAxis_lt_secondAxis) h
  · intro μ _ hne
    refine Finset.sum_eq_zero fun ν hν => ?_
    rw [hv _ _ _ (Finset.mem_Ioi.1 hν), if_neg fun h => hne (by rw [← h])]
    simp
  · simp
  · intro y _ hne
    refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν hν => ?_
    rw [hv _ _ _ (Finset.mem_Ioi.1 hν), if_neg fun h => hne (by rw [← h])]
    simp
  · simp
open Classical in
private theorem siteInner_indicator (ξ : ℝ) (C : Site L m j → ComplexMatrix2) (x : Site L m j)
    (Y : ComplexMatrix2) :
    siteInner ξ C (fun y => if y = x then Y else 0) =
      ((ξ ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace (C x * Y) := by
  rw [siteInner, finsum_eq_sum_of_fintype]
  congr 1
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp
private theorem trace_eq_of_scaled_halfTrace_eq {ξ : ℝ} (hξ : ξ ≠ 0) {P Q : ComplexMatrix2}
    (h : ((ξ ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace P =
      ((ξ ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace Q) :
    Matrix.trace P = Matrix.trace Q := by apply _root_.YangMills.SharedProofs.p25377 <;> assumption
private def TraceFormNondegenerate (𝒱 : Set ComplexMatrix2) : Prop :=
  ∀ Z ∈ 𝒱, (∀ Y ∈ 𝒱, Matrix.trace (Z * Y) = 0) → Z = 0
variable {𝒱 : Set ComplexMatrix2} {U : Bond L m j → ComplexMatrix2}
private theorem bondForm_eq_of_inner (hF : BondStructure L m j) (hS : ConjStable 𝒱 U)
    (hnd : TraceFormNondegenerate 𝒱) {ξ : ℝ} (hξ : ξ ≠ 0) {B B' : Bond L m j → ComplexMatrix2}
    (hB : IsBondForm 𝒱 B) (hB' : IsBondForm 𝒱 B')
    (h : ∀ A, IsBondForm 𝒱 A → bondFormInner ξ B A = bondFormInner ξ B' A) : B = B' := by
  classical
  refine bondForm_ext hF hB hB' fun μ x => ?_
  have hZ := hS.sub_mem (bondFormComponent_mem hF hB μ x) (bondFormComponent_mem hF hB' μ x)
  refine sub_eq_zero.1 (hnd _ hZ fun Y hY => ?_)
  have hA : IsBondForm 𝒱 (bondIndicator x μ Y) := by
    refine isBondForm_bondFormOfPositive hF fun b _ => ?_
    split_ifs
    · exact hY
    · exact hS.zero_mem
  have h₁ := h _ hA
  rw [bondFormInner_bondIndicator hF, bondFormInner_bondIndicator hF] at h₁
  rw [Matrix.sub_mul, Matrix.trace_sub]
  exact sub_eq_zero.2 (trace_eq_of_scaled_halfTrace_eq hξ h₁)
private theorem siteField_eq_of_inner (hS : ConjStable 𝒱 U) (hnd : TraceFormNondegenerate 𝒱)
    {ξ : ℝ} (hξ : ξ ≠ 0) {B B' : Site L m j → ComplexMatrix2} (hB : IsSiteField 𝒱 B)
    (hB' : IsSiteField 𝒱 B')
    (h : ∀ f, IsSiteField 𝒱 f → siteInner ξ B f = siteInner ξ B' f) : B = B' := by
  classical
  funext x
  refine sub_eq_zero.1 (hnd _ (hS.sub_mem (hB x) (hB' x)) fun Y hY => ?_)
  have h₁ := h (fun y => if y = x then Y else 0) fun y => by
    show (if y = x then Y else 0) ∈ 𝒱
    split_ifs
    · exact hY
    · exact hS.zero_mem
  rw [siteInner_indicator, siteInner_indicator] at h₁
  rw [Matrix.sub_mul, Matrix.trace_sub]
  exact sub_eq_zero.2 (trace_eq_of_scaled_halfTrace_eq hξ h₁)
private theorem plaquetteForm_eq_zero_of_inner (hS : ConjStable 𝒱 U) (hnd : TraceFormNondegenerate 𝒱)
    {ξ : ℝ} (hξ : ξ ≠ 0) {F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hF : IsPlaquetteForm 𝒱 F)
    (h : ∀ H, IsPlaquetteForm 𝒱 H → plaquetteFormInner ξ F H = 0) : F = 0 := by
  classical
  have hup : ∀ μ ν x, μ < ν → F μ ν x = 0 := by
    intro μ ν x hμν
    refine hnd _ (hF.1 _ _ _ hμν) fun Y hY => ?_
    have hH : IsPlaquetteForm 𝒱 (plaquetteIndicator (⟨x, μ, ν, hμν⟩ : Plaquette L m j) Y) := by
      refine ⟨fun μ' ν' x' h' => ?_, plaquetteFormOf_antisymm _⟩
      simp only [plaquetteIndicator, plaquetteFormOf, h', dite_true]
      split_ifs
      · exact hY
      · exact hS.zero_mem
    have h₁ := h _ hH
    rw [plaquetteFormInner_plaquetteIndicator] at h₁
    have h₂ : ((ξ ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace (F μ ν x * Y) =
        ((ξ ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace 0 := by
      rw [h₁]
      simp
    simpa using trace_eq_of_scaled_halfTrace_eq hξ h₂
  funext μ ν x
  rcases lt_trichotomy μ ν with h' | h' | h'
  · exact hup _ _ _ h'
  · subst h'
    exact antisymm_diag_eq_zero hF.2 _ _
  · rw [hF.2 ν μ x, hup _ _ _ h', neg_zero]
    rfl
end
private def adjointBondForm (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  bondFormOfPositive fun b => transposedCurlComponent ξ U X b.axis b.source
private theorem bondFormComponent_adjointBondForm (hF : BondStructure L m j) (ξ : ℝ)
    (U : Bond L m j → ComplexMatrix2) (X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) (μ : Fin 4)
    (x : Site L m j) :
    bondFormComponent (adjointBondForm ξ U X) μ x = transposedCurlComponent ξ U X μ x := by
  unfold bondFormComponent adjointBondForm
  rw [bondFormOfPositive_pos _ (hF.isPos x μ), hF.axis_fwd]
  rfl
private theorem transposedCurlComponent_add (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (X X' : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) (μ : Fin 4) (x : Site L m j) :
    transposedCurlComponent ξ U (X + X') μ x =
      transposedCurlComponent ξ U X μ x + transposedCurlComponent ξ U X' μ x := by
  unfold transposedCurlComponent
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ν _ => covDerivTranspose_add ξ U ν (X ν μ) (X' ν μ) x
private theorem transposedCurlComponent_smul (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) (c : ℂ)
    (X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) (μ : Fin 4) (x : Site L m j) :
    transposedCurlComponent ξ U (c • X) μ x = c • transposedCurlComponent ξ U X μ x := by
  unfold transposedCurlComponent
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun ν _ => covDerivTranspose_smul ξ U ν c (X ν μ) x
private theorem adjointBondForm_add (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (X X' : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) :
    adjointBondForm ξ U (X + X') = adjointBondForm ξ U X + adjointBondForm ξ U X' := by
  funext b
  simp only [adjointBondForm, Pi.add_apply]
  by_cases hb : b.IsPositivelyOriented
  · rw [bondFormOfPositive_pos _ hb, bondFormOfPositive_pos _ hb, bondFormOfPositive_pos _ hb]
    exact transposedCurlComponent_add ξ U X X' _ _
  · rw [bondFormOfPositive_not_pos _ hb, bondFormOfPositive_not_pos _ hb,
      bondFormOfPositive_not_pos _ hb, transposedCurlComponent_add, neg_add]
private theorem adjointBondForm_smul (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) (c : ℂ)
    (X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) :
    adjointBondForm ξ U (c • X) = c • adjointBondForm ξ U X := by
  funext b
  simp only [adjointBondForm, Pi.smul_apply]
  by_cases hb : b.IsPositivelyOriented
  · rw [bondFormOfPositive_pos _ hb, bondFormOfPositive_pos _ hb]
    exact transposedCurlComponent_smul ξ U c X _ _
  · rw [bondFormOfPositive_not_pos _ hb, bondFormOfPositive_not_pos _ hb,
      transposedCurlComponent_smul, smul_neg]
private theorem familyTranspose_eq_transposedCurlComponent {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
    {X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2} (hX : ∀ μ ν x, X ν μ x = -X μ ν x)
    (μ : Fin 4) (x : Site L m j) :
    plaquetteFamilyExteriorDerivTranspose ξ U (plaquetteFamilyOfComponents X) μ x =
      transposedCurlComponent ξ U X μ x := by
  simp only [plaquetteFamilyExteriorDerivTranspose, transposedCurlComponent,
    plaquetteFamilyComponent, plaquetteFormOf_family hX]
private theorem transposedCurlComponent_eq_transportedDifferenceSum {ξ : ℝ}
    {U : Bond L m j → ComplexMatrix2} (hT : PlaquetteTransposeFacts ξ U)
    {X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2} (hX : ∀ μ ν x, X ν μ x = -X μ ν x)
    (μ : Fin 4) (x : Site L m j) :
    transposedCurlComponent ξ U X μ x = TransposeFormulas.transportedDifferenceSum ξ U X μ x := by
  rw [← familyTranspose_eq_transposedCurlComponent hX, hT.1]
  simp only [TransposeFormulas.transportedDifferenceSum, plaquetteFamilyComponent,
    plaquetteFormOf_family hX]
private theorem bondFormInner_adjointBondForm (hF : BondStructure L m j) {ξ : ℝ}
    {U : Bond L m j → ComplexMatrix2} (hT : PlaquetteTransposeFacts ξ U)
    {X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hX : ∀ μ ν x, X ν μ x = -X μ ν x) (A : Bond L m j → ComplexMatrix2) :
    bondFormInner ξ (adjointBondForm ξ U X) A = plaquetteFormInner ξ X (covExteriorDeriv ξ U A) := by
  rw [plaquetteFormInner_eq_plaquetteFamilyInner, bondFormInner_eq_axisFamilyInner]
  have h₁ : plaquetteFamilyOfComponents (covExteriorDeriv ξ U A) =
      plaquetteFamilyExteriorDeriv ξ U (bondFormComponent A) := by
    funext p
    rfl
  have h₂ : bondFormComponent (adjointBondForm ξ U X) =
      plaquetteFamilyExteriorDerivTranspose ξ U (plaquetteFamilyOfComponents X) := by
    funext μ x
    rw [bondFormComponent_adjointBondForm hF, familyTranspose_eq_transposedCurlComponent hX]
  rw [h₁, h₂]
  exact (hT.2.2 _ _).symm
section
variable {𝒱 : Set ComplexMatrix2} {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
private theorem adjointBondForm_isBondForm (hF : BondStructure L m j) (hS : ConjStable 𝒱 U)
    (hU : ∀ b, IsUnit (U b).det) {X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hX : IsPlaquetteForm 𝒱 X) : IsBondForm 𝒱 (adjointBondForm ξ U X) :=
  isBondForm_bondFormOfPositive hF fun _ _ => hS.sum_mem _ fun _ hν =>
    covDerivTranspose_mem hS hU (plaquetteForm_mem hS hX (Finset.ne_of_mem_erase hν)) ξ _ _
variable [Fintype (Site L m j)]
private theorem epsilon_adjoint_eq (hF : BondStructure L m j) (hS : ConjStable 𝒱 U)
    (hU : ∀ b, IsUnit (U b).det) (hnd : TraceFormNondegenerate 𝒱) (hξ : ξ ≠ 0)
    (hT : PlaquetteTransposeFacts ξ U) {X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hX : IsPlaquetteForm 𝒱 X) :
    (Classical.epsilon fun B => IsBondForm 𝒱 B ∧ ∀ A, IsBondForm 𝒱 A →
      bondFormInner ξ B A = plaquetteFormInner ξ X (covExteriorDeriv ξ U A)) =
      adjointBondForm ξ U X := by
  have hmem := adjointBondForm_isBondForm (ξ := ξ) hF hS hU hX
  have hs := Classical.epsilon_spec (p := fun B => IsBondForm 𝒱 B ∧ ∀ A, IsBondForm 𝒱 A →
      bondFormInner ξ B A = plaquetteFormInner ξ X (covExteriorDeriv ξ U A))
    ⟨adjointBondForm ξ U X, hmem, fun A _ => bondFormInner_adjointBondForm hF hT hX.2 A⟩
  exact bondForm_eq_of_inner hF hS hnd hξ hs.1 hmem fun A hA =>
    (hs.2 A hA).trans (bondFormInner_adjointBondForm hF hT hX.2 A).symm
private theorem isExteriorDerivAdjoint_of (hF : BondStructure L m j) (hS : ConjStable 𝒱 U)
    (hU : ∀ b, IsUnit (U b).det) (hnd : TraceFormNondegenerate 𝒱) (hξ : ξ ≠ 0)
    (hT : PlaquetteTransposeFacts ξ U) (hc : ∀ (c : ℂ) {a : ComplexMatrix2}, a ∈ 𝒱 → c • a ∈ 𝒱)
    {T : (Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) → Bond L m j → ComplexMatrix2}
    (hTeq : ∀ X, IsPlaquetteForm 𝒱 X → T X = adjointBondForm ξ U X) :
    IsExteriorDerivAdjoint ξ U 𝒱 T := by
  refine ⟨fun A hA => covExteriorDeriv_isPlaquetteForm hS hF hA ξ, fun X hX => ?_,
    fun X X' hX hX' => ?_, fun c X hX => ?_⟩
  · have hmem := adjointBondForm_isBondForm (ξ := ξ) hF hS hU hX
    have hpair := fun A => bondFormInner_adjointBondForm hF hT hX.2 A
    rw [hTeq X hX]
    refine ⟨⟨_, ⟨hmem, fun A _ => hpair A⟩, fun B hB => ?_⟩, hmem, fun A _ => hpair A,
      fun μ x => ⟨bondFormComponent_adjointBondForm hF ξ U X μ x,
        transposedCurlComponent_eq_transportedDifferenceSum hT hX.2 μ x⟩⟩
    exact bondForm_eq_of_inner hF hS hnd hξ hB.1 hmem fun A hA => (hB.2 A hA).trans (hpair A).symm
  · have hsum : IsPlaquetteForm 𝒱 (X + X') := by
      refine ⟨fun μ ν x h => hS.add_mem (hX.1 μ ν x h) (hX'.1 μ ν x h), fun μ ν x => ?_⟩
      simp only [Pi.add_apply]
      rw [hX.2, hX'.2, neg_add]
    rw [hTeq _ hsum, hTeq _ hX, hTeq _ hX', adjointBondForm_add]
  · have hsmul : IsPlaquetteForm 𝒱 (c • X) := by
      refine ⟨fun μ ν x h => hc c (hX.1 μ ν x h), fun μ ν x => ?_⟩
      simp only [Pi.smul_apply]
      rw [hX.2, smul_neg]
    rw [hTeq _ hsmul, hTeq _ hX, adjointBondForm_smul]
private theorem bondFormInner_covGradient (hF : BondStructure L m j) (hP : SummationByParts ξ U)
    (A : Bond L m j → ComplexMatrix2) (f : Site L m j → ComplexMatrix2) :
    bondFormInner ξ A (covGradient univ ξ U f) = siteInner ξ (transposeDivergence ξ U A) f := by
  have hs : ∀ (g h : Site L m j → ComplexMatrix2) (ν : Fin 4),
      ∑ x, ComplexMatrix2.halfTrace (g x * covDeriv ξ U ν h x) =
        ∑ x, ComplexMatrix2.halfTrace (covDerivTranspose ξ U ν g x * h x) := by
    intro g h ν
    have h₁ := hP g h ν
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at h₁
    simp only [ComplexMatrix2.halfTrace, ← Finset.mul_sum, h₁]
  rw [bondFormInner, siteInner, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  congr 1
  have e₁ : ∀ x, ComplexMatrix2.halfTrace (transposeDivergence ξ U A x * f x) =
      ∑ μ, ComplexMatrix2.halfTrace (covDerivTranspose ξ U μ (bondFormComponent A μ) x * f x) := by
    intro x
    simp only [transposeDivergence, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
      Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]
  simp only [e₁, bondFormComponent_covGradient hF]
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun μ _ => hs (bondFormComponent A μ) f μ) ?_
  rw [Finset.sum_comm]
omit [Fintype (Site L m j)] in
private theorem transposeDivergence_mem (hF : BondStructure L m j) (hS : ConjStable 𝒱 U)
    (hU : ∀ b, IsUnit (U b).det) {A : Bond L m j → ComplexMatrix2} (hA : IsBondForm 𝒱 A) :
    IsSiteField 𝒱 (transposeDivergence ξ U A) := fun x =>
  hS.sum_mem _ fun μ _ => covDerivTranspose_mem hS hU (bondFormComponent_mem hF hA μ) ξ μ x
private theorem gradientAdjointFacts_of (hF : BondStructure L m j) (hS : ConjStable 𝒱 U)
    (hU : ∀ b, IsUnit (U b).det) (hnd : TraceFormNondegenerate 𝒱) (hξ : ξ ≠ 0)
    (hP : SummationByParts ξ U) : GradientAdjointFacts ξ U 𝒱 := by
  refine ⟨fun lam hlam => ⟨covGradient_isBondForm hS hF hlam ξ, ?_⟩, fun A hA =>
    ⟨transposeDivergence_mem hF hS hU hA, fun lam _ => bondFormInner_covGradient hF hP A lam,
      fun τ hτ h => ?_⟩⟩
  · funext μ x
    exact bondFormComponent_covGradient hF ξ U lam μ x
  · exact siteField_eq_of_inner hS hnd hξ hτ (transposeDivergence_mem hF hS hU hA) fun lam hlam =>
      (h lam hlam).trans (bondFormInner_covGradient hF hP A lam)
end
private theorem isUnit_of_isUnit_det {T : ComplexMatrix2} (h : IsUnit T.det) : IsUnit T :=
  (Matrix.isUnit_iff_isUnit_det T).2 h
private theorem conjStable_complexLieAlgebra (hTr : TraceFacts) {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U b).det) : ConjStable complexLieAlgebra U where
  zero_mem := ComplexMatrix2.traceless.zero_mem
  add_mem := fun ha hb => ComplexMatrix2.traceless.add_mem ha hb
  neg_mem := fun ha => ComplexMatrix2.traceless.neg_mem ha
  real_smul_mem := fun _ _ ha => ComplexMatrix2.traceless.smul_mem _ ha
  conj_mem := fun b a ha => ((hTr.1 _ (isUnit_of_isUnit_det (hU b))).2.2.2.2.2.2.2 a ha).1
  conj_inv_mem := fun b a ha => ((hTr.1 _ (isUnit_of_isUnit_det (hU b))).2.2.2.2.2.2.2 a ha).2
private theorem conjStable_univ (U : Bond L m j → ComplexMatrix2) : ConjStable univ U where
  zero_mem := mem_univ _
  add_mem := fun _ _ => mem_univ _
  neg_mem := fun _ => mem_univ _
  real_smul_mem := fun _ _ _ => mem_univ _
  conj_mem := fun _ _ _ => mem_univ _
  conj_inv_mem := fun _ _ _ => mem_univ _
private theorem traceFormNondegenerate_complexLieAlgebra (hTr : TraceFacts) :
    TraceFormNondegenerate complexLieAlgebra :=
  hTr.2.2
private theorem traceFormNondegenerate_univ (hTr : TraceFacts) : TraceFormNondegenerate univ :=
  fun Z _ h => hTr.2.1 Z fun Y => h Y (mem_univ _)
section
variable [Fintype (Site L m j)] {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
private theorem covExteriorDerivAdjoint_eq (hTr : TraceFacts) (hF : BondStructure L m j)
    (hU : ∀ b, IsUnit (U b).det) (hξ : ξ ≠ 0) (hT : PlaquetteTransposeFacts ξ U)
    {X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2} (hX : IsPlaquetteForm complexLieAlgebra X) :
    covExteriorDerivAdjoint ξ U X = adjointBondForm ξ U X :=
  epsilon_adjoint_eq hF (conjStable_complexLieAlgebra hTr hU) hU
    (traceFormNondegenerate_complexLieAlgebra hTr) hξ hT hX
private theorem matrixCovExteriorDerivTranspose_eq (hTr : TraceFacts) (hF : BondStructure L m j)
    (hU : ∀ b, IsUnit (U b).det) (hξ : ξ ≠ 0) (hT : PlaquetteTransposeFacts ξ U)
    {X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2} (hX : IsPlaquetteForm univ X) :
    matrixCovExteriorDerivTranspose ξ U X = adjointBondForm ξ U X :=
  epsilon_adjoint_eq hF (conjStable_univ U) hU (traceFormNondegenerate_univ hTr) hξ hT hX
omit [Fintype (Site L m j)] in
private theorem isPlaquetteForm_univ_of_complex {X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hX : IsPlaquetteForm complexLieAlgebra X) : IsPlaquetteForm univ X :=
  ⟨fun _ _ _ _ => mem_univ _, hX.2⟩
private theorem derivativeAdjoints_of (hTr : TraceFacts) (hF : BondStructure L m j)
    (hU : ∀ b, IsUnit (U b).det) (hξ : ξ ≠ 0) (hT : PlaquetteTransposeFacts ξ U)
    (hP : SummationByParts ξ U) : DerivativeAdjoints ξ U := by
  refine ⟨isExteriorDerivAdjoint_of hF (conjStable_complexLieAlgebra hTr hU) hU
      (traceFormNondegenerate_complexLieAlgebra hTr) hξ hT
      (fun c _ ha => ComplexMatrix2.traceless.smul_mem c ha)
      fun X hX => covExteriorDerivAdjoint_eq hTr hF hU hξ hT hX,
    gradientAdjointFacts_of hF (conjStable_complexLieAlgebra hTr hU) hU
      (traceFormNondegenerate_complexLieAlgebra hTr) hξ hP,
    isExteriorDerivAdjoint_of hF (conjStable_univ U) hU (traceFormNondegenerate_univ hTr)
      hξ hT (fun _ _ _ => mem_univ _) fun X hX => matrixCovExteriorDerivTranspose_eq hTr hF hU hξ hT hX,
    gradientAdjointFacts_of hF (conjStable_univ U) hU (traceFormNondegenerate_univ hTr) hξ hP,
    fun F hF' => ?_⟩
  rw [covExteriorDerivAdjoint_eq hTr hF hU hξ hT hF',
    matrixCovExteriorDerivTranspose_eq hTr hF hU hξ hT (isPlaquetteForm_univ_of_complex hF')]
end
private theorem plaquetteFormOf_isPlaquetteForm (f : Plaquette L m j → ComplexMatrix2) :
    IsPlaquetteForm univ (plaquetteFormOf f) :=
  ⟨fun _ _ _ _ => mem_univ _, plaquetteFormOf_antisymm f⟩
private theorem plaquetteFormOf_conjugateAtOrigin (u : Site L m j → ComplexMatrix2)
    (X : Plaquette L m j → ComplexMatrix2) (ν μ : Fin 4) (y : Site L m j) :
    plaquetteFormOf (TransposeFormulas.conjugateAtOrigin u X) ν μ y =
      ComplexMatrix2.conjugateBy (u y) (plaquetteFormOf X ν μ y) := by
  unfold plaquetteFormOf TransposeFormulas.conjugateAtOrigin
  split_ifs <;> simp [conj_neg, conj_zero]
private theorem conj_gaugeTransformed {a W c : ComplexMatrix2} (ha : IsUnit a.det)
    (hW : IsUnit W.det) (hc : IsUnit c.det) (Z : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (a * W * c⁻¹)⁻¹ (ComplexMatrix2.conjugateBy a Z) =
      ComplexMatrix2.conjugateBy c (ComplexMatrix2.conjugateBy W⁻¹ Z) := by apply _root_.YangMills.SharedProofs.p76369 <;> assumption
private theorem covDerivTranspose_gaugeTransform {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
    {u : Site L m j → ComplexMatrix2} (hU : ∀ b, IsUnit (U b).det) (hu : ∀ x, IsUnit (u x).det)
    (hV : ∀ b, IsUnit (gaugeTransform u U b).det) (ν : Fin 4) (f : Site L m j → ComplexMatrix2)
    (x : Site L m j) :
    covDerivTranspose ξ (gaugeTransform u U) ν (fun y => ComplexMatrix2.conjugateBy (u y) (f y)) x =
      ComplexMatrix2.conjugateBy (u x) (covDerivTranspose ξ U ν f x) := by
  rw [covDerivTranspose_eq_adjointComponent hV, covDerivTranspose_eq_adjointComponent hU]
  unfold covDerivAdjointComponent
  rw [conj_smul, conj_sub]
  congr 2
  show ComplexMatrix2.conjugateBy (u (x - unitStep L m j ν) *
      U (Bond.forwardFrom (x - unitStep L m j ν) ν) *
      (u (x - unitStep L m j ν + unitStep L m j ν))⁻¹)⁻¹
      (ComplexMatrix2.conjugateBy (u (x - unitStep L m j ν)) (f (x - unitStep L m j ν))) = _
  rw [sub_add_cancel]
  exact conj_gaugeTransformed (hu _) (hU _) (hu _) _
private theorem transposedCurlComponent_gaugeTransform {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
    {u : Site L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U b).det) (hu : ∀ x, IsUnit (u x).det)
    (hV : ∀ b, IsUnit (gaugeTransform u U b).det) (X : Plaquette L m j → ComplexMatrix2)
    (μ : Fin 4) (x : Site L m j) :
    transposedCurlComponent ξ (gaugeTransform u U)
        (plaquetteFormOf (TransposeFormulas.conjugateAtOrigin u X)) μ x =
      ComplexMatrix2.conjugateBy (u x) (transposedCurlComponent ξ U (plaquetteFormOf X) μ x) := by
  unfold transposedCurlComponent
  rw [conj_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have h : plaquetteFormOf (TransposeFormulas.conjugateAtOrigin u X) ν μ =
      fun y => ComplexMatrix2.conjugateBy (u y) (plaquetteFormOf X ν μ y) :=
    funext (plaquetteFormOf_conjugateAtOrigin u X ν μ)
  rw [h]
  exact covDerivTranspose_gaugeTransform hU hu hV ν _ x
private theorem det_pathHolonomy {U : Bond L m j → ComplexMatrix2} (hU : ∀ b, (U b).det = 1)
    (Γ : List (Bond L m j)) : (pathHolonomy U Γ).det = 1 := by
  unfold pathHolonomy
  induction Γ with
  | nil => simp
  | cons b Γ ih => simp [Matrix.det_mul, hU b, ih]
abbrev _root_.YangMills.SharedProofs.p29622 := @det_pathHolonomy
private theorem trace_inv_of_det_one {P : ComplexMatrix2} (h : P.det = 1) :
    Matrix.trace P⁻¹ = Matrix.trace P := by apply _root_.YangMills.DeltaSharedProofs.p7762 <;> assumption
private theorem curvatureAt_mem (ξ : ℝ) {U : Bond L m j → ComplexMatrix2} (hU : ∀ b, (U b).det = 1)
    (p : Plaquette L m j) : curvatureAt ξ U p ∈ complexLieAlgebra := by
  refine ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.smul_mem _ ?_)
  show Matrix.trace _ = 0
  have h₁ : (plaquetteHolonomy U p).det = 1 := det_pathHolonomy hU _
  rw [Matrix.trace_sub, trace_inv_of_det_one h₁, sub_self]
private theorem curvature_isPlaquetteForm (ξ : ℝ) {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, (U b).det = 1) : IsPlaquetteForm complexLieAlgebra (curvature ξ U) := by
  refine ⟨fun μ ν x h => ?_, plaquetteFormOf_antisymm _⟩
  unfold curvature plaquetteFormOf
  rw [dif_pos h]
  exact curvatureAt_mem ξ hU _
private theorem curvatureAt_conj (ξ : ℝ) {U V : Bond L m j → ComplexMatrix2} {a : ComplexMatrix2}
    (ha : IsUnit a.det) {p : Plaquette L m j}
    (hp : plaquetteHolonomy V p = a * plaquetteHolonomy U p * a⁻¹) :
    curvatureAt ξ V p = ComplexMatrix2.conjugateBy a (curvatureAt ξ U p) := by apply _root_.YangMills.SharedProofs.p91411 <;> assumption
private theorem isUnit_det_of_det_eq_one {T : ComplexMatrix2} (h : T.det = 1) : IsUnit T.det := by
  rw [h]
  exact isUnit_one
abbrev _root_.YangMills.SharedProofs.p11557 := @isUnit_det_of_det_eq_one
private theorem gaugeCovariant_of [Fintype (Site L m j)]
    (hG : GaugeCovarianceOfHolonomy)
    (hTr : TraceFacts) (hF : BondStructure L m j) (hOdd : Odd L) (hL : 13 ≤ L) (hm : 0 < m)
    (hj : -(m : ℤ) < j) {ξ : ℝ} (hξ : ξ ≠ 0) {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField complexGaugeGroup univ U)
    (hTF : ∀ V : Bond L m j → ComplexMatrix2, IsGaugeField complexGaugeGroup univ V →
      PlaquetteTransposeFacts ξ V)
    {u : Site L m j → ComplexMatrix2} (hu : IsGaugeMap complexGaugeGroup u) :
    TransposeFormulas.GaugeCovariant ξ U u := by
  obtain ⟨⟨hV, -, -⟩, -, hplaq⟩ := hG L m hOdd hL hm j hj.le univ U u u
    (fun _ _ => mem_univ _) hU hu hu
  have hdetU : ∀ b, (U b).det = 1 := fun b => hU.1 b (mem_univ b)
  have hdetV : ∀ b, (gaugeTransform u U b).det = 1 := fun b => hV.1 b (mem_univ b)
  have hUd : ∀ b, IsUnit (U b).det := fun b => isUnit_det_of_det_eq_one (hdetU b)
  have hVd : ∀ b, IsUnit (gaugeTransform u U b).det := fun b => isUnit_det_of_det_eq_one (hdetV b)
  have hud : ∀ x, IsUnit (u x).det := fun x => isUnit_det_of_det_eq_one (hu x)
  have hTU := hTF U hU
  have hTV := hTF _ hV
  intro b hb
  obtain ⟨x, μ, rfl⟩ := hF.exists_fwd hb
  have clause : ∀ X : Plaquette L m j → ComplexMatrix2,
      matrixCovExteriorDerivTranspose ξ (gaugeTransform u U)
          (plaquetteFormOf (TransposeFormulas.conjugateAtOrigin u X)) (Bond.forwardFrom x μ) =
        ComplexMatrix2.conjugateBy (u x) (matrixCovExteriorDerivTranspose ξ U (plaquetteFormOf X)
          (Bond.forwardFrom x μ)) := by
    intro X
    rw [matrixCovExteriorDerivTranspose_eq hTr hF hVd hξ hTV (plaquetteFormOf_isPlaquetteForm _),
      matrixCovExteriorDerivTranspose_eq hTr hF hUd hξ hTU (plaquetteFormOf_isPlaquetteForm _)]
    show bondFormComponent (adjointBondForm ξ (gaugeTransform u U)
        (plaquetteFormOf (TransposeFormulas.conjugateAtOrigin u X))) μ x =
      ComplexMatrix2.conjugateBy (u x)
        (bondFormComponent (adjointBondForm ξ U (plaquetteFormOf X)) μ x)
    rw [bondFormComponent_adjointBondForm hF, bondFormComponent_adjointBondForm hF]
    exact transposedCurlComponent_gaugeTransform hUd hud hVd X μ x
  have hfield : curvature ξ (gaugeTransform u U) =
      plaquetteFormOf (TransposeFormulas.conjugateAtOrigin u (curvatureAt ξ U)) :=
    congrArg plaquetteFormOf (funext fun p =>
      curvatureAt_conj ξ (hud _) (hplaq p fun _ _ => mem_univ _))
  have hplaquettes : plaquetteFormOf (plaquetteHolonomy (gaugeTransform u U)) =
      plaquetteFormOf (TransposeFormulas.conjugateAtOrigin u (plaquetteHolonomy U)) :=
    congrArg plaquetteFormOf (funext fun p => hplaq p fun _ _ => mem_univ _)
  refine ⟨clause, ?_, ?_⟩
  · unfold yangMillsCurrent
    rw [covExteriorDerivAdjoint_eq hTr hF hVd hξ hTV (curvature_isPlaquetteForm ξ hdetV),
      covExteriorDerivAdjoint_eq hTr hF hUd hξ hTU (curvature_isPlaquetteForm ξ hdetU)]
    show bondFormComponent (adjointBondForm ξ (gaugeTransform u U)
        (curvature ξ (gaugeTransform u U))) μ x =
      ComplexMatrix2.conjugateBy (u x) (bondFormComponent (adjointBondForm ξ U (curvature ξ U)) μ x)
    rw [bondFormComponent_adjointBondForm hF, bondFormComponent_adjointBondForm hF, hfield]
    exact transposedCurlComponent_gaugeTransform hUd hud hVd _ μ x
  · rw [hplaquettes]
    exact clause _
private theorem covDerivTranspose_eq_neg_conj {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U b).det) (μ : Fin 4) (f : Site L m j → ComplexMatrix2) (x : Site L m j) :
    covDerivTranspose ξ U μ f x =
      -ComplexMatrix2.conjugateBy (U (Bond.forwardFrom (x - unitStep L m j μ) μ))⁻¹
        (covDeriv ξ U μ f (x - unitStep L m j μ)) := by
  rw [covDerivTranspose_eq_adjointComponent hU]
  unfold covDerivAdjointComponent covDeriv
  rw [conj_smul, conj_sub, conj_inv_conj (hU _), sub_add_cancel, ← smul_neg, neg_sub]
private theorem finite_bond [Finite (Site L m j)] : Finite (Bond L m j) := by apply _root_.YangMills.SharedProofs.p19159 <;> assumption
private theorem adjointIdentityAndBounds_of (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    (hF : BondStructure L m j) {ξ : ℝ} (hξ : 0 < ξ) {U : Bond L m j → ComplexMatrix2}
    (hUd : ∀ b, IsUnit (U b).det) : AdjointIdentityAndBounds ξ U := by
  intro A _
  refine ⟨fun μ x => covDerivTranspose_eq_neg_conj hUd μ _ x, fun hU => ?_⟩
  have hfs : Finite (Site L m j) := hF.finite_sites
  have hfb : Finite (Bond L m j) := finite_bond
  have hnorm : ∀ {V : ComplexMatrix2}, V ∈ compactGaugeGroup → ∀ Z : ComplexMatrix2,
      ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy V Z) =
        ComplexMatrix2.operatorNorm Z := fun hV Z =>
    hN.2.1 Z _ (Matrix.specialUnitaryGroup_le_unitaryGroup hV)
  have hinv : ∀ b : Bond L m j, (U b)⁻¹ ∈ compactGaugeGroup := fun b => by
    rw [← hU.2 b (mem_univ b)]
    exact hU.1 _ (mem_univ _)
  have hbdd : ∀ y : Site L m j, BddAbove (range fun p : Fin 4 × Fin 4 =>
      ComplexMatrix2.operatorNorm (covDeriv ξ U p.1 (bondFormComponent A p.2) y)) :=
    fun _ => (Set.finite_range _).bddAbove
  have hbdd' : BddAbove (range fun y : Site L m j => covDerivNorm ξ U A y) :=
    (Set.finite_range _).bddAbove
  have hterm : ∀ (x : Site L m j) (μ : Fin 4),
      ComplexMatrix2.operatorNorm (covDerivTranspose ξ U μ (bondFormComponent A μ) x) =
        ComplexMatrix2.operatorNorm
          (covDeriv ξ U μ (bondFormComponent A μ) (x - unitStep L m j μ)) := by
    intro x μ
    rw [covDerivTranspose_eq_neg_conj hUd]
    show ‖-ComplexMatrix2.conjugateBy _ _‖ = _
    rw [norm_neg]
    exact hnorm (hinv _) _
  have hat : ∀ x, ComplexMatrix2.operatorNorm (transposeDivergence ξ U A x) ≤
      ∑ μ : Fin 4, ComplexMatrix2.operatorNorm
        (covDeriv ξ U μ (bondFormComponent A μ) (x - unitStep L m j μ)) := by
    intro x
    unfold transposeDivergence
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun μ _ => hterm x μ
  refine ⟨hat, ?_, ?_⟩
  · unfold supOfOperatorNorms
    refine ciSup_le fun x => (hat x).trans ?_
    calc ∑ μ : Fin 4, ComplexMatrix2.operatorNorm
          (covDeriv ξ U μ (bondFormComponent A μ) (x - unitStep L m j μ))
        ≤ ∑ _μ : Fin 4, ⨆ y, covDerivNorm ξ U A y := by
          refine Finset.sum_le_sum fun μ _ => ?_
          refine le_trans ?_ (le_ciSup hbdd' (x - unitStep L m j μ))
          exact le_ciSup (hbdd (x - unitStep L m j μ)) (μ, μ)
      _ = 4 * ⨆ y, covDerivNorm ξ U A y := by simp
  · have hsup : ∀ (y : Site L m j) (ν : Fin 4), ‖A (Bond.forwardFrom y ν)‖ ≤
        supOfOperatorNorms fun b : PositivelyOrientedBond L m j => A b.1 := fun y ν =>
      le_ciSup (f := fun b : PositivelyOrientedBond L m j => ComplexMatrix2.operatorNorm (A b.1))
        (Set.finite_range _).bddAbove ⟨_, hF.isPos y ν⟩
    rw [← le_div_iff₀' hξ]
    refine ciSup_le fun x => ciSup_le fun p => ?_
    unfold covDeriv bondFormComponent
    show ‖((ξ⁻¹ : ℝ) : ℂ) • _‖ ≤ _
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hξ).le, div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hξ).le
    refine (norm_sub_le _ _).trans ?_
    have h₃ := hnorm (hU.1 (Bond.forwardFrom x p.1) (mem_univ _))
      (A (Bond.forwardFrom (x + unitStep L m j p.1) p.2))
    have h₄ : ‖ComplexMatrix2.conjugateBy (U (Bond.forwardFrom x p.1))
        (A (Bond.forwardFrom (x + unitStep L m j p.1) p.2))‖ =
        ‖A (Bond.forwardFrom (x + unitStep L m j p.1) p.2)‖ := h₃
    rw [h₄]
    linarith [hsup (x + unitStep L m j p.1) p.2, hsup x p.2]
private theorem eq_of_min_eq_of_max_eq : ∀ μ ν ν' : Fin 4, ν ≠ μ → ν' ≠ μ → min μ ν = min μ ν' →
    max μ ν = max μ ν' → ν = ν' := by
  decide
private theorem forwardFrom_eq_iff (hF : BondStructure L m j) (x y : Site L m j) (μ ν : Fin 4) :
    Bond.forwardFrom x μ = Bond.forwardFrom y ν ↔ y = x ∧ ν = μ := by
  constructor
  · intro h
    exact hF.fwd_inj h.symm
  · rintro ⟨rfl, rfl⟩
    rfl
private theorem forwardFrom_mem_boundaryBonds_iff (hF : BondStructure L m j) (x : Site L m j)
    (μ : Fin 4) (p : Plaquette L m j) :
    Bond.forwardFrom x μ ∈ boundaryBonds p ↔
      (p.origin = x ∧ p.firstAxis = μ) ∨
        (p.origin + unitStep L m j p.firstAxis = x ∧ p.secondAxis = μ) ∨
        (p.origin + unitStep L m j p.secondAxis = x ∧ p.firstAxis = μ) ∨
        (p.origin = x ∧ p.secondAxis = μ) := by
  simp only [boundaryBonds, mem_insert_iff, mem_singleton_iff, forwardFrom_eq_iff hF]
private theorem boundaryBonds_positive (hF : BondStructure L m j) (p : Plaquette L m j) :
    ∀ b ∈ boundaryBonds p, b.IsPositivelyOriented := by
  intro b hb
  simp only [boundaryBonds, mem_insert_iff, mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact hF.isPos _ _
private theorem forward_backward_plaquette_injective (hF : BondStructure L m j) (x : Site L m j)
    (μ : Fin 4) :
    Function.Injective (Sum.elim (forwardPlaquette x μ) (backwardPlaquette x μ)) := by
  have hstep : ∀ ν : Fin 4, x - unitStep L m j ν ≠ x := fun ν h =>
    hF.step_ne_zero ν (by simpa using h)
  rintro (ν | ν) (ν' | ν') h
  · have h' : forwardPlaquette x μ ν = forwardPlaquette x μ ν' := h
    exact congrArg Sum.inl (Subtype.ext (eq_of_min_eq_of_max_eq μ ν ν' ν.2 ν'.2
      (congrArg Plaquette.firstAxis h') (congrArg Plaquette.secondAxis h')))
  · have h' : forwardPlaquette x μ ν = backwardPlaquette x μ ν' := h
    exact absurd (congrArg Plaquette.origin h').symm (hstep _)
  · have h' : backwardPlaquette x μ ν = forwardPlaquette x μ ν' := h
    exact absurd (congrArg Plaquette.origin h') (hstep _)
  · have h' : backwardPlaquette x μ ν = backwardPlaquette x μ ν' := h
    exact congrArg Sum.inr (Subtype.ext (eq_of_min_eq_of_max_eq μ ν ν' ν.2 ν'.2
      (congrArg Plaquette.firstAxis h') (congrArg Plaquette.secondAxis h')))
private theorem forwardFrom_mem_iff_mem_cofacePlaquettes (hF : BondStructure L m j) (x : Site L m j)
    (μ : Fin 4) (p : Plaquette L m j) :
    Bond.forwardFrom x μ ∈ boundaryBonds p ↔ p ∈ cofacePlaquettes x μ := by
  rw [forwardFrom_mem_boundaryBonds_iff hF]
  constructor
  · obtain ⟨y, ρ, σ, h⟩ := p
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · dsimp only at h₁ h₂
      subst h₁ h₂
      exact Or.inl ⟨⟨σ, h.ne'⟩, Plaquette.ext rfl (min_eq_left h.le) (max_eq_right h.le)⟩
    · dsimp only at h₁ h₂
      subst h₁ h₂
      exact Or.inr ⟨⟨ρ, h.ne⟩, Plaquette.ext (add_sub_cancel_right _ _) (min_eq_right h.le)
        (max_eq_left h.le)⟩
    · dsimp only at h₁ h₂
      subst h₁ h₂
      exact Or.inr ⟨⟨σ, h.ne'⟩, Plaquette.ext (add_sub_cancel_right _ _) (min_eq_left h.le)
        (max_eq_right h.le)⟩
    · dsimp only at h₁ h₂
      subst h₁ h₂
      exact Or.inl ⟨⟨ρ, h.ne⟩, Plaquette.ext rfl (min_eq_right h.le) (max_eq_left h.le)⟩
  · rintro (⟨⟨ν, hν⟩, rfl⟩ | ⟨⟨ν, hν⟩, rfl⟩)
    · rcases lt_or_gt_of_ne hν.symm with h | h
      · exact Or.inl ⟨rfl, min_eq_left h.le⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, max_eq_left h.le⟩))
    · rcases lt_or_gt_of_ne hν.symm with h | h
      · refine Or.inr (Or.inr (Or.inl ⟨?_, min_eq_left h.le⟩))
        show x - unitStep L m j ν + unitStep L m j (max μ ν) = x
        rw [max_eq_right h.le, sub_add_cancel]
      · refine Or.inr (Or.inl ⟨?_, max_eq_left h.le⟩)
        show x - unitStep L m j ν + unitStep L m j (min μ ν) = x
        rw [min_eq_right h.le, sub_add_cancel]
private theorem opposite_not_mem_boundaryBonds (hF : BondStructure L m j) (x : Site L m j)
    (μ : Fin 4) (p : Plaquette L m j) : (Bond.forwardFrom x μ).opposite ∉ boundaryBonds p := fun h =>
  hF.not_both (hF.isPos x μ) (boundaryBonds_positive hF p _ h)
private theorem backward_bond_mem_boundaryBonds (hF : BondStructure L m j) (x : Site L m j)
    (μ : Fin 4) (ν : {ν : Fin 4 // ν ≠ μ}) :
    Bond.forwardFrom (x - unitStep L m j ν) ν ∈ boundaryBonds (backwardPlaquette x μ ν) := by
  rw [forwardFrom_mem_boundaryBonds_iff hF]
  rcases lt_or_gt_of_ne ν.2.symm with h | h
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, max_eq_right h.le⟩))
  · exact Or.inl ⟨rfl, min_eq_right h.le⟩
private theorem plaquetteFormOf_eq_axisOrderSign (X : Plaquette L m j → ComplexMatrix2)
    {μ ν : Fin 4} (h : μ ≠ ν) (y : Site L m j) :
    plaquetteFormOf X μ ν y = axisOrderSign μ ν • X (plaquetteSpanned y h) := by
  unfold plaquetteFormOf axisOrderSign
  rcases lt_or_gt_of_ne h with h' | h'
  · have hp : plaquetteSpanned y h = ⟨y, μ, ν, h'⟩ :=
      Plaquette.ext rfl (min_eq_left h'.le) (max_eq_right h'.le)
    rw [dif_pos h', if_pos h', hp, one_smul]
  · have hp : plaquetteSpanned y h = ⟨y, ν, μ, h'⟩ :=
      Plaquette.ext rfl (min_eq_right h'.le) (max_eq_left h'.le)
    rw [dif_neg (not_lt_of_gt h'), dif_pos h', if_neg (not_lt_of_gt h'), hp, neg_one_smul]
section
variable [Fintype (Site L m j)] {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
private theorem adjoint_value_formula (hTr : TraceFacts) (hF : BondStructure L m j)
    (hU : ∀ b, IsUnit (U b).det) (hξ : ξ ≠ 0) (hT : PlaquetteTransposeFacts ξ U)
    (X : MatrixPlaquetteForm L m j) (μ : Fin 4) (x : Site L m j) :
    matrixCovExteriorDerivTranspose ξ U (plaquetteFamilyComponent X) (Bond.forwardFrom x μ) =
      ∑ ν : {ν : Fin 4 // ν ≠ μ}, axisOrderSign μ ν • ((ξ⁻¹ : ℝ) : ℂ) •
        (X (forwardPlaquette x μ ν) -
          ComplexMatrix2.conjugateBy (U (Bond.forwardFrom (x - unitStep L m j ν) ν))⁻¹
            (X (backwardPlaquette x μ ν))) := by
  have h₁ : matrixCovExteriorDerivTranspose ξ U (plaquetteFamilyComponent X) =
      adjointBondForm ξ U (plaquetteFamilyComponent X) :=
    matrixCovExteriorDerivTranspose_eq hTr hF hU hξ hT (plaquetteFormOf_isPlaquetteForm X)
  rw [h₁]
  show bondFormComponent (adjointBondForm ξ U (plaquetteFamilyComponent X)) μ x = _
  rw [bondFormComponent_adjointBondForm hF,
    transposedCurlComponent_eq_transportedDifferenceSum hT (plaquetteFormOf_antisymm X)]
  unfold TransposeFormulas.transportedDifferenceSum
  rw [Finset.smul_sum, Finset.sum_subtype (Finset.univ.erase μ) (p := fun ν => ν ≠ μ) (by simp)]
  refine Finset.sum_congr rfl fun ν _ => ?_
  show ((ξ⁻¹ : ℝ) : ℂ) • (plaquetteFormOf X μ ν x -
    ComplexMatrix2.conjugateBy _ (plaquetteFormOf X μ ν _)) = _
  rw [plaquetteFormOf_eq_axisOrderSign X ν.2.symm, plaquetteFormOf_eq_axisOrderSign X ν.2.symm,
    conj_smul, ← smul_sub, smul_comm]
  rfl
omit [Fintype (Site L m j)] in
private theorem plaquetteHolonomy_congr {U' : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField complexGaugeGroup univ U) (hU' : IsGaugeField complexGaugeGroup univ U')
    {p : Plaquette L m j} (h : ∀ b ∈ boundaryBonds p, U' b = U b) :
    plaquetteHolonomy U' p = plaquetteHolonomy U p := by
  have hb : ∀ b ∈ p.boundaryBonds, U' b = U b := by
    intro b hb
    simp only [Plaquette.boundaryBonds, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact h _ (by simp [boundaryBonds])
    · exact h _ (by simp [boundaryBonds])
    · rw [hU'.2 _ (mem_univ _), hU.2 _ (mem_univ _), h _ (by simp [boundaryBonds])]
    · rw [hU'.2 _ (mem_univ _), hU.2 _ (mem_univ _), h _ (by simp [boundaryBonds])]
  unfold plaquetteHolonomy pathHolonomy
  rw [List.map_congr_left hb]
private theorem yangMillsCurrent_eq_matrix (hTr : TraceFacts) (hF : BondStructure L m j)
    (hU : IsGaugeField complexGaugeGroup univ U) (hξ : ξ ≠ 0) (hT : PlaquetteTransposeFacts ξ U) :
    yangMillsCurrent ξ U =
      matrixCovExteriorDerivTranspose ξ U (plaquetteFamilyComponent (curvatureAt ξ U)) := by
  have hdet : ∀ b, (U b).det = 1 := fun b => hU.1 b (mem_univ b)
  have hUd : ∀ b, IsUnit (U b).det := fun b => isUnit_det_of_det_eq_one (hdet b)
  have hX := curvature_isPlaquetteForm ξ hdet
  unfold yangMillsCurrent
  rw [covExteriorDerivAdjoint_eq hTr hF hUd hξ hT hX]
  exact (matrixCovExteriorDerivTranspose_eq hTr hF hUd hξ hT
    (isPlaquetteForm_univ_of_complex hX)).symm
private theorem adjointValueAtBond_of (hTr : TraceFacts) (hF : BondStructure L m j)
    (hU : IsGaugeField complexGaugeGroup univ U) (hξ : ξ ≠ 0)
    (hTF : ∀ V : Bond L m j → ComplexMatrix2, IsGaugeField complexGaugeGroup univ V →
      PlaquetteTransposeFacts ξ V) :
    AdjointValueAtBond ξ U := by
  have hUd : ∀ b, IsUnit (U b).det := fun b => isUnit_det_of_det_eq_one (hU.1 b (mem_univ b))
  intro μ x
  refine ⟨forward_backward_plaquette_injective hF x μ,
    forwardFrom_mem_iff_mem_cofacePlaquettes hF x μ, opposite_not_mem_boundaryBonds hF x μ,
    backward_bond_mem_boundaryBonds hF x μ,
    fun X => adjoint_value_formula hTr hF hUd hξ (hTF U hU) X μ x, fun U' hU' hsame => ?_⟩
  have hU'd : ∀ b, IsUnit (U' b).det := fun b => isUnit_det_of_det_eq_one (hU'.1 b (mem_univ b))
  have hread : ∀ X X' : MatrixPlaquetteForm L m j, (∀ p ∈ cofacePlaquettes x μ, X' p = X p) →
      matrixCovExteriorDerivTranspose ξ U' (plaquetteFamilyComponent X') (Bond.forwardFrom x μ) =
        matrixCovExteriorDerivTranspose ξ U (plaquetteFamilyComponent X) (Bond.forwardFrom x μ) := by
    intro X X' hX
    rw [adjoint_value_formula hTr hF hU'd hξ (hTF U' hU') X' μ x,
      adjoint_value_formula hTr hF hUd hξ (hTF U hU) X μ x]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have hbehind : backwardPlaquette x μ ν ∈ cofacePlaquettes x μ := Or.inr ⟨ν, rfl⟩
    rw [hX _ (Or.inl ⟨ν, rfl⟩), hX _ hbehind,
      hsame _ hbehind _ (backward_bond_mem_boundaryBonds hF x μ ν)]
  have hvar : ∀ p ∈ cofacePlaquettes x μ, plaquetteHolonomy U' p = plaquetteHolonomy U p :=
    fun p hp => plaquetteHolonomy_congr hU hU' (hsame p hp)
  refine ⟨hread, ?_, hread _ _ hvar⟩
  rw [yangMillsCurrent_eq_matrix hTr hF hU hξ (hTF U hU),
    yangMillsCurrent_eq_matrix hTr hF hU' hξ (hTF U' hU')]
  refine hread _ _ fun p hp => ?_
  unfold curvatureAt
  rw [hvar p hp]
end
private theorem gaugeFieldsExtendByOne_holds : GaugeFieldsExtendByOne L m j := by
  intro ℬ U' hcl hU'
  classical
  have hout : ∀ b : Bond L m j, b ∉ ℬ → b.opposite ∉ ℬ := fun b hb hr => hb (hcl _ hr)
  have hgen : ∀ 𝒢 : Set ComplexMatrix2, (1 : ComplexMatrix2) ∈ 𝒢 → IsGaugeField 𝒢 ℬ U' →
      IsGaugeField 𝒢 univ (extendByOne ℬ U') := by
    intro 𝒢 h₁ hC
    refine ⟨fun b _ => ?_, fun b _ => ?_⟩
    · unfold extendByOne
      split_ifs with h
      · exact hC.1 b h
      · exact h₁
    · by_cases h : b ∈ ℬ
      · simp [extendByOne, h, hcl b h, hC.2 b h]
      · simp [extendByOne, h, hout b h]
  refine ⟨hgen _ (by simp [complexGaugeGroup, ComplexMatrix2.unitDeterminant]) hU',
    fun b hb => by simp [extendByOne, hb], fun hR => hgen _ ?_ hR⟩
  exact Submonoid.one_mem _
private theorem hermitianTraceless_eq_conjTranspose {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) : Y = Y.conjTranspose := hY.1
private theorem hermitianTraceless_trace {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) : Matrix.trace Y = 0 := hY.2
private theorem inv_eq_conjTranspose_of_mem {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V⁻¹ = V.conjTranspose := by
  have h := (Matrix.mem_specialUnitaryGroup_iff.1 hV).1
  exact Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.1 h)
private theorem conj_mem_hermitianTraceless {V Y : ComplexMatrix2} (hV : V ∈ compactGaugeGroup)
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy V Y ∈ ComplexMatrix2.hermitianTraceless := by
  have hd : IsUnit V.det :=
    isUnit_det_of_det_eq_one (Matrix.mem_specialUnitaryGroup_iff.1 hV).2
  refine ⟨?_, ?_⟩
  · unfold ComplexMatrix2.conjugateBy
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, ← hermitianTraceless_eq_conjTranspose hY,
      inv_eq_conjTranspose_of_mem hV, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  · show Matrix.trace (V * Y * V⁻¹) = 0
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
    exact hermitianTraceless_trace hY
abbrev _root_.YangMills.SharedProofs.p2904 := @conj_mem_hermitianTraceless
private theorem conjStable_compactLieAlgebra {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup univ U) : ConjStable compactLieAlgebra U where
  zero_mem := ComplexMatrix2.hermitianTraceless.zero_mem
  add_mem := fun ha hb => ComplexMatrix2.hermitianTraceless.add_mem ha hb
  neg_mem := fun ha => ComplexMatrix2.hermitianTraceless.neg_mem ha
  real_smul_mem := fun r a ha => by
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_smul, ← hermitianTraceless_eq_conjTranspose ha]
      simp
    · show Matrix.trace _ = 0
      rw [Matrix.trace_smul, hermitianTraceless_trace ha, smul_zero]
  conj_mem := fun b _ ha => conj_mem_hermitianTraceless (hU.1 b (mem_univ b)) ha
  conj_inv_mem := fun b _ ha => by
    rw [← hU.2 b (mem_univ b)]
    exact conj_mem_hermitianTraceless (hU.1 _ (mem_univ _)) ha
private theorem real_smul_eq_ofReal_smul (c : ℝ) (Y : ComplexMatrix2) :
    c • Y = ((c : ℝ) : ℂ) • Y := by
  ext i k
  simp [Complex.real_smul]
abbrev _root_.YangMills.SharedProofs.p9878 := @real_smul_eq_ofReal_smul
private theorem im_trace_mul_eq_zero {Y Y' : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) (hY' : Y' ∈ ComplexMatrix2.hermitianTraceless) :
    (Matrix.trace (Y * Y')).im = 0 := by
  have h : (starRingEnd ℂ) (Matrix.trace (Y * Y')) = Matrix.trace (Y * Y') := by
    have h₁ := Matrix.trace_conjTranspose (Y * Y')
    rw [Matrix.conjTranspose_mul, ← hermitianTraceless_eq_conjTranspose hY,
      ← hermitianTraceless_eq_conjTranspose hY', Matrix.trace_mul_comm] at h₁
    exact h₁.symm
  exact Complex.conj_eq_iff_im.1 h
private theorem re_halfTrace (P : ComplexMatrix2) :
    (ComplexMatrix2.halfTrace P).re = (Matrix.trace P).re / 2 := by
  have h : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by norm_num
  rw [ComplexMatrix2.halfTrace, h, Complex.re_ofReal_mul]
  ring
private theorem im_halfTrace (P : ComplexMatrix2) :
    (ComplexMatrix2.halfTrace P).im = (Matrix.trace P).im / 2 := by
  have h : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by norm_num
  rw [ComplexMatrix2.halfTrace, h, Complex.im_ofReal_mul]
  ring
private theorem re_trace_mul_self {Y : ComplexMatrix2} (hY : Y = Y.conjTranspose) :
    (Matrix.trace (Y * Y)).re = ∑ i, ∑ k, Complex.normSq (Y i k) := by
  have h : ∀ i k, Y k i = (starRingEnd ℂ) (Y i k) := fun i k => by
    have h₁ := congrFun (congrFun hY k) i
    rw [Matrix.conjTranspose_apply] at h₁
    exact h₁
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [h i k, Complex.mul_conj, Complex.ofReal_re]
private theorem re_halfTrace_mul_self_nonneg {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (ComplexMatrix2.halfTrace (Y * Y)).re := by
  rw [re_halfTrace, re_trace_mul_self (hermitianTraceless_eq_conjTranspose hY)]
  have : 0 ≤ ∑ i, ∑ k, Complex.normSq (Y i k) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
  linarith
abbrev _root_.YangMills.DeltaSharedProofs.p2944 := @re_halfTrace_mul_self_nonneg
abbrev _root_.YangMills.SharedProofs.p2980 := @re_halfTrace_mul_self_nonneg
private theorem re_halfTrace_mul_self_pos {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) (hne : Y ≠ 0) :
    0 < (ComplexMatrix2.halfTrace (Y * Y)).re := by
  obtain ⟨i, k, hik⟩ : ∃ i k, Y i k ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by ext i k; exact h i k)
  rw [re_halfTrace, re_trace_mul_self (hermitianTraceless_eq_conjTranspose hY)]
  have : 0 < ∑ i, ∑ k, Complex.normSq (Y i k) := by
    refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun k _ => Complex.normSq_nonneg _)
        ⟨k, Finset.mem_univ _, Complex.normSq_pos.2 hik⟩⟩
  linarith
private structure IsSemiInner {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E)
    (P : E → E → ℂ) : Prop where
  im_eq_zero : ∀ a ∈ S, ∀ b ∈ S, (P a b).im = 0
  comm : ∀ a ∈ S, ∀ b ∈ S, P a b = P b a
  add_left : ∀ a ∈ S, ∀ a' ∈ S, ∀ b ∈ S, ∀ c d : ℝ,
    P (c • a + d • a') b = (c : ℂ) * P a b + (d : ℂ) * P a' b
  add_right : ∀ a ∈ S, ∀ b ∈ S, ∀ b' ∈ S, ∀ c d : ℝ,
    P a (c • b + d • b') = (c : ℂ) * P a b + (d : ℂ) * P a b'
  re_self_nonneg : ∀ a ∈ S, 0 ≤ (P a a).re
section
variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
private theorem IsSemiInner.finsetSum {ι : Type*} (s : Finset ι) {Q : ι → E → E → ℂ}
    (h : ∀ i ∈ s, IsSemiInner S (Q i)) : IsSemiInner S fun a b => ∑ i ∈ s, Q i a b where
  im_eq_zero a ha b hb := by
    rw [Complex.im_sum]
    exact Finset.sum_eq_zero fun i hi => (h i hi).im_eq_zero a ha b hb
  comm a ha b hb := Finset.sum_congr rfl fun i hi => (h i hi).comm a ha b hb
  add_left a ha a' ha' b hb c d := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => (h i hi).add_left a ha a' ha' b hb c d
  add_right a ha b hb b' hb' c d := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => (h i hi).add_right a ha b hb b' hb' c d
  re_self_nonneg a ha := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun i hi => (h i hi).re_self_nonneg a ha
private theorem IsSemiInner.ofReal_mul {P : E → E → ℂ} (h : IsSemiInner S P) {c : ℝ}
    (hc : 0 ≤ c) : IsSemiInner S fun a b => (c : ℂ) * P a b where
  im_eq_zero a ha b hb := by rw [Complex.im_ofReal_mul, h.im_eq_zero a ha b hb, mul_zero]
  comm a ha b hb := by rw [h.comm a ha b hb]
  add_left a ha a' ha' b hb c' d := by
    rw [h.add_left a ha a' ha' b hb]
    ring
  add_right a ha b hb b' hb' c' d := by
    rw [h.add_right a ha b hb b' hb']
    ring
  re_self_nonneg a ha := by
    rw [Complex.re_ofReal_mul]
    exact mul_nonneg hc (h.re_self_nonneg a ha)
private theorem IsSemiInner.halfTrace_mul (φ : E → ComplexMatrix2)
    (hφ : ∀ a ∈ S, φ a ∈ ComplexMatrix2.hermitianTraceless)
    (hlin : ∀ (a a' : E) (c d : ℝ),
      φ (c • a + d • a') = ((c : ℝ) : ℂ) • φ a + ((d : ℝ) : ℂ) • φ a') :
    IsSemiInner S fun a b => ComplexMatrix2.halfTrace (φ a * φ b) where
  im_eq_zero a ha b hb := by
    rw [im_halfTrace, im_trace_mul_eq_zero (hφ a ha) (hφ b hb), zero_div]
  comm a _ b _ := by
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
    rw [Matrix.trace_mul_comm]
  add_left a _ a' _ b _ c d := by
    rw [hlin]
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.add_mul, Matrix.smul_mul,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    ring
  add_right a _ b _ b' _ c d := by
    rw [hlin]
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.mul_add, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    ring
  re_self_nonneg a ha := re_halfTrace_mul_self_nonneg (hφ a ha)
private theorem IsSemiInner.toInnerProduct {P : E → E → ℂ} (h : IsSemiInner S P)
    (hpos : ∀ a ∈ S, a ≠ 0 → 0 < (P a a).re) : IsRealInnerProductOnSet S P :=
  ⟨h.im_eq_zero, h.comm, h.add_left, h.add_right, hpos⟩
end
section
variable [Fintype (Site L m j)] {ξ : ℝ}
private theorem siteInner_isRealInnerProduct (hξ : 0 < ξ) :
    IsRealInnerProductOnSet {f : Site L m j → ComplexMatrix2 | IsSiteField compactLieAlgebra f}
      (siteInner ξ) := by
  have hP : siteInner ξ = fun f g : Site L m j → ComplexMatrix2 =>
      (((ξ ^ 4 : ℝ)) : ℂ) * ∑ x, ComplexMatrix2.halfTrace (f x * g x) := by
    funext f g
    rw [siteInner, finsum_eq_sum_of_fintype]
  have hb : ∀ x : Site L m j,
      IsSemiInner {f : Site L m j → ComplexMatrix2 | IsSiteField compactLieAlgebra f}
        fun f g => ComplexMatrix2.halfTrace (f x * g x) := fun x =>
    IsSemiInner.halfTrace_mul (E := Site L m j → ComplexMatrix2)
      (fun f : Site L m j → ComplexMatrix2 => f x) (fun f hf => hf x) fun a a' c d => by
        simp only [Pi.add_apply, Pi.smul_apply, real_smul_eq_ofReal_smul]
  rw [hP]
  refine ((IsSemiInner.finsetSum Finset.univ fun x _ => hb x).ofReal_mul
    (by positivity)).toInnerProduct fun f hf hne => ?_
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  rw [Complex.re_ofReal_mul]
  refine mul_pos (by positivity) ?_
  rw [Complex.re_sum]
  exact Finset.sum_pos' (fun y _ => (hb y).re_self_nonneg f hf)
    ⟨x, Finset.mem_univ _, re_halfTrace_mul_self_pos (hf x) hx⟩
private theorem bondFormInner_isRealInnerProduct (hF : BondStructure L m j) (hξ : 0 < ξ) :
    IsRealInnerProductOnSet {A : Bond L m j → ComplexMatrix2 | IsBondForm compactLieAlgebra A}
      (bondFormInner ξ) := by
  have hP : bondFormInner ξ = fun A B : Bond L m j → ComplexMatrix2 =>
      (((ξ ^ 4 : ℝ)) : ℂ) * ∑ x, ∑ μ, ComplexMatrix2.halfTrace
        (bondFormComponent A μ x * bondFormComponent B μ x) := by
    funext A B
    rw [bondFormInner, finsum_eq_sum_of_fintype]
  have hb : ∀ (x : Site L m j) (μ : Fin 4),
      IsSemiInner {A : Bond L m j → ComplexMatrix2 | IsBondForm compactLieAlgebra A}
        fun A B => ComplexMatrix2.halfTrace (bondFormComponent A μ x * bondFormComponent B μ x) :=
    fun x μ => IsSemiInner.halfTrace_mul (fun A => bondFormComponent A μ x)
      (fun A hA => bondFormComponent_mem hF hA μ x) fun a a' c d => by
        simp only [bondFormComponent, Pi.add_apply, Pi.smul_apply, real_smul_eq_ofReal_smul]
  have hb' := fun x : Site L m j => IsSemiInner.finsetSum Finset.univ fun μ _ => hb x μ
  rw [hP]
  refine ((IsSemiInner.finsetSum Finset.univ fun x _ => hb' x).ofReal_mul
    (by positivity)).toInnerProduct fun A hA hne => ?_
  obtain ⟨μ, x, hx⟩ : ∃ μ x, bondFormComponent A μ x ≠ 0 := by
    by_contra h
    push Not at h
    refine hne (bondForm_ext hF (𝔥' := univ) hA ⟨fun _ _ => mem_univ _, fun _ => ?_⟩ ?_)
    · simp
    · intro μ x
      exact h μ x
  rw [Complex.re_ofReal_mul]
  refine mul_pos (by positivity) ?_
  rw [Complex.re_sum]
  refine Finset.sum_pos' (fun y _ => (hb' y).re_self_nonneg A hA) ⟨x, Finset.mem_univ _, ?_⟩
  rw [Complex.re_sum]
  exact Finset.sum_pos' (fun ν _ => (hb x ν).re_self_nonneg A hA)
    ⟨μ, Finset.mem_univ _, re_halfTrace_mul_self_pos (bondFormComponent_mem hF hA μ x) hx⟩
private theorem plaquetteFormInner_isRealInnerProduct (hξ : 0 < ξ) :
    IsRealInnerProductOnSet
      {F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2 | IsPlaquetteForm compactLieAlgebra F}
      (plaquetteFormInner ξ) := by
  have hP : plaquetteFormInner ξ = fun F H : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2 =>
      (((ξ ^ 4 : ℝ)) : ℂ) * ∑ x, ∑ μ, ∑ ν ∈ Finset.Ioi μ, ComplexMatrix2.halfTrace
        (F μ ν x * H μ ν x) := by
    funext F H
    rw [plaquetteFormInner, finsum_eq_sum_of_fintype]
  have hb : ∀ (x : Site L m j) (μ ν : Fin 4), μ < ν →
      IsSemiInner
        {F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2 | IsPlaquetteForm compactLieAlgebra F}
        fun F H => ComplexMatrix2.halfTrace (F μ ν x * H μ ν x) :=
    fun x μ ν h => IsSemiInner.halfTrace_mul (E := Fin 4 → Fin 4 → Site L m j → ComplexMatrix2)
      (fun F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2 => F μ ν x)
      (fun F hF => hF.1 μ ν x h) fun a a' c d => by
        simp only [Pi.add_apply, Pi.smul_apply, real_smul_eq_ofReal_smul]
  have hb₁ := fun (x : Site L m j) (μ : Fin 4) =>
    IsSemiInner.finsetSum (Finset.Ioi μ) fun ν hν => hb x μ ν (Finset.mem_Ioi.1 hν)
  have hb₂ := fun x : Site L m j => IsSemiInner.finsetSum Finset.univ fun μ _ => hb₁ x μ
  rw [hP]
  refine ((IsSemiInner.finsetSum Finset.univ fun x _ => hb₂ x).ofReal_mul
    (by positivity)).toInnerProduct fun F hF hne => ?_
  obtain ⟨μ, ν, x, hμν, hx⟩ : ∃ μ ν x, μ < ν ∧ F μ ν x ≠ 0 := by
    by_contra h
    push Not at h
    refine hne ?_
    funext μ ν x
    rcases lt_trichotomy μ ν with h' | h' | h'
    · exact h _ _ _ h'
    · subst h'
      exact antisymm_diag_eq_zero hF.2 _ _
    · rw [hF.2 ν μ x, h _ _ _ h', neg_zero]
      rfl
  rw [Complex.re_ofReal_mul]
  refine mul_pos (by positivity) ?_
  rw [Complex.re_sum]
  refine Finset.sum_pos' (fun y _ => (hb₂ y).re_self_nonneg F hF) ⟨x, Finset.mem_univ _, ?_⟩
  rw [Complex.re_sum]
  refine Finset.sum_pos' (fun ρ _ => (hb₁ x ρ).re_self_nonneg F hF) ⟨μ, Finset.mem_univ _, ?_⟩
  rw [Complex.re_sum]
  exact Finset.sum_pos' (fun ρ hρ => (hb x μ ρ (Finset.mem_Ioi.1 hρ)).re_self_nonneg F hF)
    ⟨ν, Finset.mem_Ioi.2 hμν, re_halfTrace_mul_self_pos (hF.1 μ ν x hμν) hx⟩
omit [Fintype (Site L m j)] in
private theorem isPlaquetteForm_complex_of_compact
    {F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hF : IsPlaquetteForm compactLieAlgebra F) : IsPlaquetteForm complexLieAlgebra F :=
  ⟨fun μ ν x h => hermitianTraceless_trace (hF.1 μ ν x h), hF.2⟩
private theorem compactRealForms_of (hTr : TraceFacts) (hF : BondStructure L m j)
    {U : Bond L m j → ComplexMatrix2} (hU : IsGaugeField compactGaugeGroup univ U) (hξ : 0 < ξ)
    (hT : PlaquetteTransposeFacts ξ U) (hP : SummationByParts ξ U) : CompactRealForms ξ U := by
  have hS := conjStable_compactLieAlgebra hU
  have hUd : ∀ b, IsUnit (U b).det := fun b =>
    isUnit_det_of_det_eq_one (Matrix.mem_specialUnitaryGroup_iff.1 (hU.1 b (mem_univ b))).2
  refine ⟨fun lam h => covGradient_isBondForm hS hF h ξ,
    fun A hA => ⟨covExteriorDeriv_isPlaquetteForm hS hF hA ξ, transposeDivergence_mem hF hS hUd hA⟩,
    fun F hF' => ?_, siteInner_isRealInnerProduct hξ, bondFormInner_isRealInnerProduct hF hξ,
    plaquetteFormInner_isRealInnerProduct hξ, fun F A hF' _ => ?_,
    fun A lam _ _ => (bondFormInner_covGradient hF hP A lam).symm⟩
  · rw [covExteriorDerivAdjoint_eq hTr hF hUd hξ.ne' hT (isPlaquetteForm_complex_of_compact hF')]
    exact adjointBondForm_isBondForm hF hS hUd hF'
  · rw [covExteriorDerivAdjoint_eq hTr hF hUd hξ.ne' hT (isPlaquetteForm_complex_of_compact hF')]
    exact bondFormInner_adjointBondForm hF hT hF'.2 A
end
private theorem familiesAreFormComponents_of (hF : BondStructure L m j) (𝒱 : Set ComplexMatrix2) :
    FamiliesAreFormComponents L m j 𝒱 := by
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · have hcomp : ∀ μ x, bondFormComponent
        (bondFormOfPositive fun b : Bond L m j => f b.axis b.source) μ x = f μ x := by
      intro μ x
      unfold bondFormComponent
      rw [bondFormOfPositive_pos _ (hF.isPos x μ), hF.axis_fwd]
      rfl
    have hone : IsBondForm 𝒱 (bondFormOfPositive fun b : Bond L m j => f b.axis b.source) :=
      isBondForm_bondFormOfPositive hF fun b _ => hf _ _
    refine ⟨_, ⟨hone, funext fun μ => funext fun x => hcomp μ x⟩, fun A hA => ?_⟩
    refine bondForm_ext hF hA.1 hone fun μ x => ?_
    rw [hcomp, hA.2]
  · have hfam : plaquetteFamilyOfComponents (plaquetteFormOf f) = f := by
      funext p
      simp [plaquetteFamilyOfComponents, plaquetteFormOf, p.firstAxis_lt_secondAxis]
    refine ⟨plaquetteFormOf f, ⟨⟨fun μ ν x h => ?_, plaquetteFormOf_antisymm f⟩, hfam⟩,
      fun F hF' => ?_⟩
    · simp only [plaquetteFormOf, h, dite_true]
      exact hf _
    · rw [← hF'.2]
      exact (plaquetteFormOf_family hF'.1.2).symm
private theorem innerProductsNondegenerate_of [Fintype (Site L m j)] (hF : BondStructure L m j)
    {𝒱 : Set ComplexMatrix2} {U : Bond L m j → ComplexMatrix2} (hS : ConjStable 𝒱 U)
    (hnd : TraceFormNondegenerate 𝒱) {ξ : ℝ} (hξ : ξ ≠ 0) :
    InnerProductsNondegenerate L m j ξ 𝒱 := by
  refine ⟨fun f hf h => ?_, fun A hA h => ?_,
    fun F hF' h => plaquetteForm_eq_zero_of_inner hS hnd hξ hF' h⟩
  · refine siteField_eq_of_inner hS hnd hξ hf (fun _ => hS.zero_mem) fun g hg => ?_
    rw [h g hg]
    simp [siteInner, ComplexMatrix2.halfTrace]
  · refine bondForm_eq_of_inner hF hS hnd hξ hA ⟨fun _ _ => hS.zero_mem, fun _ => by simp⟩
      fun B hB => ?_
    rw [h B hB]
    simp [bondFormInner, bondFormComponent, ComplexMatrix2.halfTrace]
private theorem addCircle_eq_of_mutual_shifts {ℓ a s t : ℝ} (hℓ : 0 < ℓ) (ha : 2 * a < ℓ)
    {x y : AddCircle ℓ} (hs : s ∈ Icc 0 a) (ht : t ∈ Icc 0 a) (h₁ : x = y + (s : AddCircle ℓ))
    (h₂ : y = x + (t : AddCircle ℓ)) : x = y := by
  have hz : (((s + t : ℝ)) : AddCircle ℓ) = 0 := by
    have h₃ : y = y + ((s + t : ℝ) : AddCircle ℓ) := by
      rw [AddCircle.coe_add, ← add_assoc, ← h₁]
      exact h₂
    exact left_eq_add.1 h₃
  have hs0 : s = 0 := by
    by_contra hne
    have hpos : 0 < s + t := by
      have := lt_of_le_of_ne hs.1 (Ne.symm hne)
      linarith [ht.1]
    exact addCircle_coe_ne_zero_of_pos_of_lt hℓ hpos (by linarith [hs.2, ht.2]) hz
  rw [h₁, hs0]
  simp
private theorem origin_mem_face (p : Plaquette L m j) (hL : 13 ≤ L) :
    ((p.origin : Site L m j) : FourTorus L m) ∈ p.face :=
  ⟨0, ⟨le_rfl, (meshSize_pos hL).le⟩, 0, ⟨le_rfl, (meshSize_pos hL).le⟩, by simp [pointOnAxis]⟩
private theorem firstCorner_mem_face (p : Plaquette L m j) (hL : 13 ≤ L) :
    ((p.origin : Site L m j) : FourTorus L m) + pointOnAxis L m p.firstAxis (meshSize L j) ∈
      p.face :=
  ⟨meshSize L j, ⟨(meshSize_pos hL).le, le_rfl⟩, 0, ⟨le_rfl, (meshSize_pos hL).le⟩,
    by simp [pointOnAxis]⟩
private theorem secondCorner_mem_face (p : Plaquette L m j) (hL : 13 ≤ L) :
    ((p.origin : Site L m j) : FourTorus L m) + pointOnAxis L m p.secondAxis (meshSize L j) ∈
      p.face :=
  ⟨0, ⟨le_rfl, (meshSize_pos hL).le⟩, meshSize L j, ⟨(meshSize_pos hL).le, le_rfl⟩,
    by simp [pointOnAxis]⟩
private theorem face_apply_of_ne {p : Plaquette L m j} {q : FourTorus L m} (hq : q ∈ p.face)
    {κ : Fin 4} (h₁ : κ ≠ p.firstAxis) (h₂ : κ ≠ p.secondAxis) :
    q κ = ((p.origin : Site L m j) : FourTorus L m) κ := by
  obtain ⟨s, -, t, -, rfl⟩ := hq
  simp [pointOnAxis, Pi.single_eq_of_ne h₁, Pi.single_eq_of_ne h₂]
private theorem eq_firstAxis_or_secondAxis {p p' : Plaquette L m j} (hL : 13 ≤ L)
    (hj : -(m : ℤ) < j) (h : p.face ⊆ p'.face) {κ : Fin 4}
    (hq : ((p.origin : Site L m j) : FourTorus L m) + pointOnAxis L m κ (meshSize L j) ∈ p.face) :
    κ = p'.firstAxis ∨ κ = p'.secondAxis := by
  by_contra hκ
  push Not at hκ
  have h₁ := face_apply_of_ne (h hq) hκ.1 hκ.2
  have h₂ := face_apply_of_ne (h (origin_mem_face p hL)) hκ.1 hκ.2
  have h₃ : ((meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
    have h₄ := h₁.trans h₂.symm
    simpa [pointOnAxis] using h₄
  exact addCircle_coe_ne_zero_of_pos_of_lt (torusSide_pos hL) (meshSize_pos hL)
    (by linarith [two_mul_meshSize_lt_torusSide (m := m) hL hj, meshSize_pos (j := j) hL]) h₃
private theorem apply_shift_firstAxis (b : FourTorus L m) {f s : Fin 4} (h : f ≠ s) (t₁ t₂ : ℝ) :
    (b + pointOnAxis L m f t₁ + pointOnAxis L m s t₂) f = b f + (t₁ : AddCircle (torusSide L m)) := by
  simp [pointOnAxis, Pi.single_eq_of_ne h]
private theorem apply_shift_secondAxis (b : FourTorus L m) {f s : Fin 4} (h : f ≠ s) (t₁ t₂ : ℝ) :
    (b + pointOnAxis L m f t₁ + pointOnAxis L m s t₂) s = b s + (t₂ : AddCircle (torusSide L m)) := by
  simp [pointOnAxis, Pi.single_eq_of_ne h.symm]
private theorem face_injective (hL : 13 ≤ L) (hj : -(m : ℤ) < j) :
    Function.Injective (Plaquette.face : Plaquette L m j → Set (FourTorus L m)) := by
  intro p p' h
  have hsub : p.face ⊆ p'.face := h.le
  have hf := eq_firstAxis_or_secondAxis hL hj hsub (firstCorner_mem_face p hL)
  have hs := eq_firstAxis_or_secondAxis hL hj hsub (secondCorner_mem_face p hL)
  have hlt := p.firstAxis_lt_secondAxis
  have hlt' := p'.firstAxis_lt_secondAxis
  have hfirst : p.firstAxis = p'.firstAxis := by
    rcases hf with hf | hf
    · exact hf
    · rcases hs with hs | hs
      · rw [hf, hs] at hlt
        exact absurd hlt (lt_asymm hlt')
      · rw [hf, hs] at hlt
        exact absurd hlt (lt_irrefl _)
  have hsecond : p.secondAxis = p'.secondAxis := by
    rcases hs with hs | hs
    · rw [hfirst, hs] at hlt
      exact absurd hlt (lt_irrefl _)
    · exact hs
  obtain ⟨s₁, hs₁, t₁, ht₁, hq₁⟩ := hsub (origin_mem_face p hL)
  obtain ⟨s₂, hs₂, t₂, ht₂, hq₂⟩ := h.ge (origin_mem_face p' hL)
  have hne := hlt.ne
  have hne' := hlt'.ne
  have hℓ := torusSide_pos (m := m) hL
  have h2a := two_mul_meshSize_lt_torusSide (m := m) hL hj
  have hbase : p.origin = p'.origin := by
    refine Subtype.ext (funext fun κ => ?_)
    by_cases k₁ : κ = p.firstAxis
    · subst k₁
      have e₁ : ((p.origin : Site L m j) : FourTorus L m) p.firstAxis =
          ((p'.origin : Site L m j) : FourTorus L m) p.firstAxis +
            (s₁ : AddCircle (torusSide L m)) := by
        have h₁ := congrFun hq₁ p.firstAxis
        rw [hfirst] at h₁ ⊢
        rwa [apply_shift_firstAxis _ hne'] at h₁
      have e₂ : ((p'.origin : Site L m j) : FourTorus L m) p.firstAxis =
          ((p.origin : Site L m j) : FourTorus L m) p.firstAxis +
            (s₂ : AddCircle (torusSide L m)) := by
        have h₁ := congrFun hq₂ p.firstAxis
        rwa [apply_shift_firstAxis _ hne] at h₁
      exact addCircle_eq_of_mutual_shifts hℓ h2a hs₁ hs₂ e₁ e₂
    · by_cases k₂ : κ = p.secondAxis
      · subst k₂
        have e₁ : ((p.origin : Site L m j) : FourTorus L m) p.secondAxis =
            ((p'.origin : Site L m j) : FourTorus L m) p.secondAxis +
              (t₁ : AddCircle (torusSide L m)) := by
          have h₁ := congrFun hq₁ p.secondAxis
          rw [hsecond] at h₁ ⊢
          rwa [apply_shift_secondAxis _ hne'] at h₁
        have e₂ : ((p'.origin : Site L m j) : FourTorus L m) p.secondAxis =
            ((p.origin : Site L m j) : FourTorus L m) p.secondAxis +
              (t₂ : AddCircle (torusSide L m)) := by
          have h₁ := congrFun hq₂ p.secondAxis
          rwa [apply_shift_secondAxis _ hne] at h₁
        exact addCircle_eq_of_mutual_shifts hℓ h2a ht₁ ht₂ e₁ e₂
      · have k₁' : κ ≠ p'.firstAxis := by rwa [← hfirst]
        have k₂' : κ ≠ p'.secondAxis := by rwa [← hsecond]
        exact (face_apply_of_ne (hsub (origin_mem_face p hL)) k₁' k₂')
  exact Plaquette.ext hbase hfirst hsecond
private theorem two_mul_le_gridSideLength (hj : -(m : ℤ) < j) : 2 * L ≤ gridSideLength L m j := by
  unfold gridSideLength
  have h : ((m : ℤ) + j).toNat ≠ 0 := by omega
  exact Nat.mul_le_mul_left 2 (Nat.le_self_pow h L)
private theorem bondPlaquetteFormFacts_of [Fintype (Site L m j)] (hTr : TraceFacts)
    (hF : BondStructure L m j) (hL : 13 ≤ L) (hj : -(m : ℤ) < j) {ξ : ℝ} (hξ : ξ ≠ 0) :
    BondPlaquetteFormFacts L m j ξ := by
  have hone : ∀ b : Bond L m j,
      IsUnit ((trivialGaugeField : Bond L m j → ComplexMatrix2) b).det :=
    fun b => by simp [trivialGaugeField]
  refine ⟨two_mul_le_gridSideLength hj, by omega, fun b => ?_, face_injective hL hj, ?_⟩
  · rcases hF.pos_or_opp b with hb | hb
    · exact Or.inl ⟨hb, hF.not_both hb⟩
    · exact Or.inr ⟨hb, fun h => hF.not_both hb h⟩
  · rintro 𝒱 (rfl | rfl)
    · exact ⟨familiesAreFormComponents_of hF _,
        innerProductsNondegenerate_of hF (conjStable_complexLieAlgebra hTr hone)
          (traceFormNondegenerate_complexLieAlgebra hTr) hξ⟩
    · exact ⟨familiesAreFormComponents_of hF _, innerProductsNondegenerate_of hF
        (conjStable_univ trivialGaugeField) (traceFormNondegenerate_univ hTr) hξ⟩
private theorem covDerivAdjointComponent_neg (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) (ν : Fin 4)
    (f : Site L m j → ComplexMatrix2) (x : Site L m j) :
    covDerivAdjointComponent ξ U ν (-f) x = -covDerivAdjointComponent ξ U ν f x := by
  unfold covDerivAdjointComponent
  simp only [Pi.neg_apply, conj_neg]
  rw [← smul_neg]
  congr 1
  abel
private theorem plaquetteFormDivergenceSum_eq {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U b).det) {X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hX : ∀ μ ν x, X ν μ x = -X μ ν x) (μ : Fin 4) (x : Site L m j) :
    plaquetteFormDivergenceSum ξ U X μ x = transposedCurlComponent ξ U X μ x := by
  have hsplit : Finset.univ.erase μ = Finset.Iio μ ∪ Finset.Ioi μ := by
    ext ν
    simp [lt_or_lt_iff_ne]
  have hdisj : Disjoint (Finset.Iio μ) (Finset.Ioi μ) := by
    rw [Finset.disjoint_left]
    intro ν h₁ h₂
    exact lt_asymm (Finset.mem_Iio.1 h₁) (Finset.mem_Ioi.1 h₂)
  unfold plaquetteFormDivergenceSum transposedCurlComponent
  simp only [covDerivTranspose_eq_adjointComponent hU]
  rw [hsplit, Finset.sum_union hdisj, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  have h : X ν μ = -X μ ν := funext fun y => hX μ ν y
  rw [h, covDerivAdjointComponent_neg]
private theorem finestLatticeOperators_of [Fintype (Site L m j)] (hTr : TraceFacts)
    (hF : BondStructure L m j) {η : ℝ} (hη : η ≠ 0) {U₀ : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U₀ b).det) (hT : PlaquetteTransposeFacts η U₀)
    (hP : SummationByParts η U₀) : FinestLatticeOperators η U₀ := by
  have hS := conjStable_complexLieAlgebra hTr hU
  have hnd := traceFormNondegenerate_complexLieAlgebra hTr
  refine ⟨fun ν f x => covDerivTranspose_eq_adjointComponent hU ν f x, fun X hX μ x => ?_,
    fun X hX μ x => ?_, fun A hA => ?_⟩
  · rw [covExteriorDerivAdjoint_eq hTr hF hU hη hT hX, bondFormComponent_adjointBondForm hF,
      plaquetteFormDivergenceSum_eq hU hX.2]
  · rw [matrixCovExteriorDerivTranspose_eq hTr hF hU hη hT hX, bondFormComponent_adjointBondForm hF,
      plaquetteFormDivergenceSum_eq hU hX.2]
  · have hdiv : bondFormDivergenceSum η U₀ A = transposeDivergence η U₀ A := by
      funext x
      unfold bondFormDivergenceSum transposeDivergence
      simp only [covDerivTranspose_eq_adjointComponent hU]
    obtain ⟨hmem, hpair, huniq⟩ := (gradientAdjointFacts_of hF hS hU hnd hη hP).2 A hA
    rw [hdiv]
    have hs := Classical.epsilon_spec (p := fun B : Site L m j → ComplexMatrix2 =>
        IsSiteField complexLieAlgebra B ∧ zeroExtendSiteField univ B = B ∧
        ∀ f, IsSiteField complexLieAlgebra f →
          siteInner η B (zeroExtendSiteField univ f) =
            bondFormInner η (zeroExtendBondForm univ A) (covGradient univ η U₀ f))
      ⟨transposeDivergence η U₀ A, hmem, zeroExtendSiteField_univ _, fun f hf => by
        rw [zeroExtendSiteField_univ, zeroExtendBondForm_univ]
        exact (hpair f hf).symm⟩
    refine ⟨huniq _ hs.1 fun f hf => ?_, fun τ => ⟨fun h => huniq τ h.1 h.2, ?_⟩⟩
    · calc siteInner η (covDivergence univ η U₀ A) f
          = siteInner η (covDivergence univ η U₀ A) (zeroExtendSiteField univ f) := by
            rw [zeroExtendSiteField_univ f]
        _ = bondFormInner η (zeroExtendBondForm univ A) (covGradient univ η U₀ f) := hs.2.2 f hf
        _ = bondFormInner η A (covGradient univ η U₀ f) := by rw [zeroExtendBondForm_univ A]
    · rintro rfl
      exact ⟨hmem, fun lam hlam => (hpair lam hlam).symm⟩
theorem covariantAdjointsStatement_holds (hP : LatticeBasics.Conclusion)
    (hG : GaugeCovarianceOfHolonomy)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    (hC : StandardPartitionCubeGeometry) : CovariantAdjointsStatement := by
  intro L m K k hOdd hL hm hK hk
  have hstand : Conventions.IsAdmissibleBlockingFactor L := ⟨hOdd, hL⟩
  have hLpos : (0 : ℝ) < L := by linarith [one_lt_cast_of_thirteen_le hL]
  have hidentity : ∀ j : ℤ, IsGaugeField complexGaugeGroup univ
      (trivialGaugeField : Bond L m j → ComplexMatrix2) := fun j =>
    ⟨fun _ _ => by simp [trivialGaugeField, complexGaugeGroup, ComplexMatrix2.unitDeterminant],
      fun _ _ => by simp [trivialGaugeField]⟩
  have hdepth : -(m : ℤ) < levelDepth K 0 := by
    simp only [levelDepth]
    omega
  refine ⟨fun j hj ξ hξe => ?_, hdepth, ?_, ?_, fun U₀ hU₀ => ?_⟩
  · have hξ : 0 < ξ := by
      rw [hξe]
      exact mul_pos (zpow_pos hLpos _) (meshSize_pos hL)
    obtain ⟨hSites, hBonds, hTr, -, -, -⟩ :=
      hP L m j ξ trivialGaugeField hstand hm hj.le hξ (hidentity j)
    have hF := bondStructure_of hL hj hSites hBonds
    have hfin : Finite (Site L m j) := hF.finite_sites
    have : Fintype (Site L m j) := Fintype.ofFinite _
    have hTF : ∀ V : Bond L m j → ComplexMatrix2, IsGaugeField complexGaugeGroup univ V →
        PlaquetteTransposeFacts ξ V := fun V hV => (hP L m j ξ V hstand hm hj.le hξ hV).2.2.2.2.2
    have hSB : ∀ V : Bond L m j → ComplexMatrix2, IsGaugeField complexGaugeGroup univ V →
        SummationByParts ξ V := fun V hV => (hP L m j ξ V hstand hm hj.le hξ hV).2.2.2.2.1
    refine ⟨bondPlaquetteFormFacts_of hTr hF hL hj hξ.ne', gaugeFieldsExtendByOne_holds,
      fun U hU => ?_⟩
    have hUd : ∀ b, IsUnit (U b).det := fun b => isUnit_det_of_det_eq_one (hU.1 b (mem_univ b))
    refine ⟨derivativeAdjoints_of hTr hF hUd hξ.ne' (hTF U hU) (hSB U hU), fun u hu => ⟨?_, ?_⟩,
      adjointIdentityAndBounds_of hN hF hξ hUd, adjointValueAtBond_of hTr hF hU hξ.ne' hTF,
      fun hR => compactRealForms_of hTr hF hR hξ (hTF U hU) (hSB U hU)⟩
    · exact gaugeCovariant_of hG hTr hF hOdd hL hm hj hξ.ne' hU hTF hu
    · intro hR huR
      exact (hG L m hOdd hL hm j hj.le univ U u u (fun _ _ => mem_univ _) hU hu hu).1.2.1 hR huR
  · have hL0 : (L : ℝ) ≠ 0 := hLpos.ne'
    unfold toLevelUnits meshSize finestMeshInLevelUnits
    rw [← zpow_add₀ hL0]
    congr 1
    simp only [levelDepth]
    omega
  · exact ⟨standardCubePartition L m (levelDepth K 0), subset_rfl,
      ((hC L m hOdd hL hm _ hdepth.le).2.1.2.2.2.2.1).symm⟩
  · have hη : 0 < finestMeshInLevelUnits L k := zpow_pos hLpos _
    obtain ⟨hSites, hBonds, hTr, -, hSB, hTF⟩ :=
      hP L m (levelDepth K 0) (finestMeshInLevelUnits L k) U₀ hstand hm hdepth.le hη hU₀
    have hF := bondStructure_of hL hdepth hSites hBonds
    have hfin : Finite (Site L m (levelDepth K 0)) := hF.finite_sites
    have : Fintype (Site L m (levelDepth K 0)) := Fintype.ofFinite _
    exact finestLatticeOperators_of hTr hF hη.ne'
      (fun b => isUnit_det_of_det_eq_one (hU₀.1 b (mem_univ b))) hTF hSB
end CovariantAdjoints
end PeriodicLattice
end YangMills.Construction
