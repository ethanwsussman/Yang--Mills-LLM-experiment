import YangMills.Construction.Lattice.ComplexAverageOnHolomorphicFamiliesProof
import YangMills.Construction.Lattice.ConstraintMapFormedNearZero
import YangMills.Construction.Lattice.CountingSitesBondsPlaquettes
import YangMills.Construction.Lattice.IteratedAveragesAtComplexConfigurations
import YangMills.Construction.Towers.RealAnalyticMapsOfConfigurationsAreDifferentiableProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
namespace ConstraintMapDefinedNearZero
theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
theorem finite_bond {L m : ℕ} {j : ℤ} (hL : 0 < L) (hj : -(m : ℤ) ≤ j) : Finite (Bond L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.Counting.bond_finite <;> assumption
open ComplexIteratedAverages
theorem opposite_isPositivelyOriented_of_not {L m : ℕ} {j : ℤ} {e : Bond L m j}
    (h : ¬ e.IsPositivelyOriented) : e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.Bond.opposite_isPositivelyOriented <;> assumption
def positivePoint {L m K k : ℕ} (S : Set (BondAtLevel L m K k)) (V : BondAtLevel L m K k → ComplexMatrix2) :
    PositiveBondOf S ⊕ Empty → ComplexMatrix2 :=
  Sum.elim (fun e => V e.1) fun z => z.elim
def positiveChart {L m K k : ℕ} (S : Set (BondAtLevel L m K k)) (A : BondAtLevel L m K k → ComplexMatrix2) :
    PositiveBondOf S ⊕ Empty → ComplexMatrix2 :=
  Sum.elim (fun e => Complex.I • A e.1) fun z => z.elim
theorem fieldOfPoint_positivePoint {L m K k : ℕ} {S : Set (BondAtLevel L m K k)}
    (hS : IsReversalClosed S) {V : BondAtLevel L m K k → ComplexMatrix2}
    (hV : IsGaugeField complexGaugeGroup S V) {e : BondAtLevel L m K k} (he : e ∈ S) :
    fieldOfPoint S (positivePoint S V) e = V e := by apply _root_.YangMills.Construction.PeriodicLattice.HolomorphicFamilies.fieldOfPoint_positivePoint <;> assumption
theorem fieldOfPoint_expChartAt {L m K k : ℕ} {S : Set (BondAtLevel L m K k)}
    (hS : IsReversalClosed S) (V A : BondAtLevel L m K k → ComplexMatrix2)
    {e : BondAtLevel L m K k} (he : e ∈ S) :
    fieldOfPoint S (GroupLieProduct.expChartAt (positivePoint S V) (positiveChart S A)) e =
      expTwist A V e := by
  classical
  by_cases hpos : e.IsPositivelyOriented
  · simp only [fieldOfPoint, extendFromPositive, expTwist]
    rw [dif_pos ⟨he, hpos⟩, if_pos hpos]
    rfl
  · have hopp : e.opposite ∈ S ∧ e.opposite.IsPositivelyOriented :=
      ⟨hS e he, opposite_isPositivelyOriented_of_not hpos⟩
    simp only [fieldOfPoint, extendFromPositive, expTwist]
    rw [dif_neg (fun h => hpos h.2), dif_pos hopp, if_neg hpos]
    rfl
end ConstraintMapDefinedNearZero
open ConstraintMapDefinedNearZero ComplexIteratedAverages in
theorem ConstraintMapDefinedNearZero.statement_holds
    (hIter : ComplexIteratedAverages.ComplexIteratedAveragesHolomorphic)
    (hLocal : ComplexAverageIsLocal) :
    ConstraintMapDefinedNearZero.Statement := by
  classical
  intro L m K k hL hm hk V Γ c hcΓ hc hV
  have hLpos : 0 < L := by have := hL.2; omega
  have hfin : Finite (BondAtLevel L m K k) := finite_bond hLpos (by simp only [levelDepth]; omega)
  let S : Set (BondAtLevel L m K k) := bondsInDoubleBlock c
  have hS : IsReversalClosed S := fun _ he => ⟨he.2, he.1⟩
  let _ : Fintype (PositiveBondOf S) := Fintype.ofFinite _
  obtain ⟨hHol, -, hAgree⟩ := (hIter L m K hL hm k hk S hS inferInstance).1 1 hk c
  have hloc := hLocal L m K k hL.1 hL.2 hm hk c hc
  have horient : c.positivelyOriented = c := by simp [Bond.positivelyOriented, hc]
  have hpoint : ∀ r ∈ productDomain S 1 c, ∀ W : BondAtLevel L m K k → ComplexMatrix2,
      (∀ e ∈ S, fieldOfPoint S r e = W e) →
        W ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
          iteratedValue S 1 c r = complexBlockAverage W c := by
    intro r hr W hW
    have hmemDom : fieldOfPoint S r ∈ {U | IsComplexGaugeField S U ∧
        ComplexPartialDefinedAt (K := K) k ⟨S, U⟩ 1 c} := hAgree.domain_eq ▸ hr.2
    have hone : _ ∈ (complexAveragingDomainNearOne c.positivelyOriented :
        Set (BondAtLevel L m K k → ComplexMatrix2)) := hmemDom.2.2
    rw [horient] at hone
    refine ⟨(hloc.mem_domain_iff _ _ ?_).1 hone, ?_⟩
    · intro e he
      exact (if_pos he).trans (hW e he)
    refine (hAgree.value_eq _ hr.2).trans ?_
    show complexBlockAverage _ c = complexBlockAverage W c
    simp only [complexBlockAverage, if_pos hc]
    refine hloc.average_eq _ _ fun e he => ?_
    exact (if_pos he).trans (hW e he)
  have hVfield : IsGaugeField complexGaugeGroup S V := hV.1.1
  have hsame₀ : ∀ e ∈ S, fieldOfPoint S (positivePoint S V) e = V e :=
    fun e he => fieldOfPoint_positivePoint hS hVfield he
  have hmem₀ : positivePoint S V ∈ productDomain S 1 c := by
    refine ⟨?_, ?_⟩
    · rintro (e | z)
      · exact hVfield.1 e.1 e.2.1
      · exact z.elim
    · rw [hAgree.domain_eq]
      refine ⟨⟨fun e he => by rw [hsame₀ e he]; exact hVfield.1 e he, fun e he => by
        rw [hsame₀ e he, hsame₀ _ (hS e he)]; exact hVfield.2 e he⟩, fun e he => he, ?_⟩
      show _ ∈ (complexAveragingDomainNearOne c.positivelyOriented :
        Set (BondAtLevel L m K k → ComplexMatrix2))
      rw [horient]
      refine (hloc.mem_domain_iff _ _ fun e he => ?_).2 hV
      exact (if_pos he).trans (hsame₀ e he)
  let basis : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  obtain ⟨O, hO0, hOdom, hOhol⟩ := (hHol.holomorphic basis).2.2.2 _ hmem₀
  obtain ⟨ρ, hρ, hball⟩ := hOhol.1.2 0 hO0
  let inclusion : PositiveBondOf S → SupportBond (levelDepth K k) Γ :=
    fun e => ⟨e.1, ⟨mem_biUnion hcΓ e.2.1, e.2.2⟩⟩
  have hextend : ∀ (B : SupportBond (levelDepth K k) Γ → ComplexMatrix2) (e : PositiveBondOf S),
      extendForm B e.1 = B (inclusion e) := by
    intro B e
    simp only [extendForm]
    rw [dif_pos (inclusion e).2]
  have hsmall : ∀ᶠ B in 𝓝 (0 : SupportBond (levelDepth K k) Γ → ComplexMatrix2),
      ∀ e : PositiveBondOf S, ‖B (inclusion e)‖ < ρ / 2 := by
    rw [eventually_all]
    intro e
    have hcont : Continuous fun B : SupportBond (levelDepth K k) Γ → ComplexMatrix2 =>
        ‖B (inclusion e)‖ :=
      continuous_norm.comp (continuous_apply _)
    exact hcont.continuousAt.eventually_lt continuousAt_const (by simpa using half_pos hρ)
  filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with B hB hBmem
  have hBtr : ∀ i, B i ∈ ComplexMatrix2.traceless := fun i => (Submodule.mem_pi.1 hBmem) i (mem_univ i)
  have hchart : positiveChart S (extendForm B) ∈ O := by
    apply hball
    · rintro (e | z)
      · show Complex.I • extendForm B e.1 ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2)
        rw [hextend]
        exact ComplexMatrix2.traceless.smul_mem _ (hBtr _)
      · exact z.elim
    · rw [sub_zero]
      refine lt_of_le_of_lt (Real.iSup_le ?_ (half_pos hρ).le) (half_lt_self hρ)
      rintro (e | z)
      · show ‖Complex.I • extendForm B e.1‖ ≤ ρ / 2
        rw [hextend, norm_smul, Complex.norm_I, one_mul]
        exact (hB e).le
      · exact z.elim
  obtain ⟨hq, hlog⟩ := hOdom _ hchart
  obtain ⟨hW, hval⟩ := hpoint _ hq (expTwist (extendForm B) V)
    fun e he => fieldOfPoint_expChartAt hS V _ he
  obtain ⟨-, hval₀⟩ := hpoint _ hmem₀ V hsame₀
  refine ⟨hW, ?_⟩
  rw [← hval, ← hval₀]
  exact hlog
end PeriodicLattice
end YangMills.Construction
end
