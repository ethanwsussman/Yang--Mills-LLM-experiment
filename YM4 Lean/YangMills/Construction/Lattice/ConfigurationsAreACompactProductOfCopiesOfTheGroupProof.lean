import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.ConfigurationsAreACompactProductOfCopiesOfTheGroup
import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.SiteAndPlaquetteCounts
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction
namespace PeriodicLattice
namespace GaugeFieldsCompactProduct
open Matrices
variable {L m : ℕ} {k : ℤ}
theorem unitStep_ne_zero (hL : 0 < L)
    (hs : torusSide L m / meshSize L k = ((2 * L ^ ((m : ℤ) + k).toNat : ℕ) : ℝ)) (μ : Fin 4) :
    unitStep L m k μ ≠ 0 := by
  intro h
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hmesh : meshSize L k ≠ 0 := zpow_ne_zero _ hL'
  have h1 : (unitStep L m k μ : FourTorus L m) μ = 0 := by rw [h]; rfl
  have h2 : ((meshSize L k : ℝ) : AddCircle (torusSide L m)) = 0 := by
    simpa [unitStep, pointOnAxis] using h1
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (torusSide L m)).1 h2
  rw [zsmul_eq_mul] at hn
  have hside : torusSide L m = ((2 * L ^ ((m : ℤ) + k).toNat : ℕ) : ℝ) * meshSize L k := by
    rw [← hs]
    field_simp
  rw [hside, ← mul_assoc] at hn
  have h3 : (n : ℝ) * ((2 * L ^ ((m : ℤ) + k).toNat : ℕ) : ℝ) = 1 :=
    mul_right_cancel₀ hmesh (by rw [hn, one_mul])
  have h4 : n * ((2 * L ^ ((m : ℤ) + k).toNat : ℕ) : ℤ) = 1 := by exact_mod_cast h3
  push_cast at h4
  have h5 : 2 * (n * (L : ℤ) ^ ((m : ℤ) + k).toNat) = 1 := by rw [← h4]; ring
  omega
theorem opposite_opposite (b : Bond L m k) : b.opposite.opposite = b := Bond.ext rfl rfl
theorem opposite_ne (hstep : ∀ μ, unitStep L m k μ ≠ 0) (b : Bond L m k) : b.opposite ≠ b := by
  intro h
  have h' : b.target = b.source := congrArg Bond.source h
  obtain ⟨μ, e | e⟩ := b.isNeighbour
  · exact hstep μ (by rw [← e, h', sub_self])
  · exact hstep μ (neg_eq_zero.1 (by rw [← e, h', sub_self]))
theorem positive_or_opposite (b : Bond L m k) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem exists_orientationChoice (hstep : ∀ μ, unitStep L m k μ ≠ 0) :
    ∃ S : Set (Bond L m k), IsOrientationChoice S := by
  obtain ⟨f, hf⟩ := exists_injective_nat (Bond L m k)
  refine ⟨{b | b.IsPositivelyOriented ∧ (b.opposite.IsPositivelyOriented → f b < f b.opposite)},
    fun b hb => hb.1, fun b => ?_⟩
  have hne : f b ≠ f b.opposite := fun h => opposite_ne hstep b (hf h).symm
  by_cases hp : b.IsPositivelyOriented <;> by_cases hr : b.opposite.IsPositivelyOriented
  · rcases lt_or_gt_of_ne hne with h | h
    · refine Or.inl ⟨⟨hp, fun _ => h⟩, fun hm => ?_⟩
      have := hm.2 (by rwa [opposite_opposite])
      rw [opposite_opposite] at this
      omega
    · refine Or.inr ⟨⟨hr, fun _ => by rwa [opposite_opposite]⟩, fun hm => ?_⟩
      have := hm.2 hr
      omega
  · exact Or.inl ⟨⟨hp, fun h => absurd h hr⟩, fun hm => hr hm.1⟩
  · exact Or.inr ⟨⟨hr, fun h => absurd (by rwa [opposite_opposite] at h) hp⟩, fun hm => hp hm.1⟩
  · exact absurd (positive_or_opposite b) (by tauto)
theorem coe_inv (g : ComplexMatrix2.specialUnitary) :
    ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = (g : ComplexMatrix2)⁻¹ := by apply _root_.YangMills.Construction.InfiniteLattice.specialUnitary_coe_inv <;> assumption
noncomputable def extendByOne (S : Set (Bond L m k)) (v : S → ComplexMatrix2.specialUnitary)
    (b : Bond L m k) : ComplexMatrix2.specialUnitary :=
  open Classical in if h : b ∈ S then v ⟨b, h⟩ else 1
noncomputable def valueAt (S : Set (Bond L m k)) (v : S → ComplexMatrix2.specialUnitary)
    (b : Bond L m k) : ComplexMatrix2.specialUnitary :=
  open Classical in if b ∈ S then extendByOne S v b else (extendByOne S v b.opposite)⁻¹
theorem continuous_extendByOne (S : Set (Bond L m k)) (b : Bond L m k) :
    Continuous fun v : S → ComplexMatrix2.specialUnitary => extendByOne S v b := by
  classical
  by_cases h : b ∈ S
  · simp only [extendByOne, dif_pos h]
    exact continuous_apply _
  · simp only [extendByOne, dif_neg h]
    exact continuous_const
theorem continuous_valueAt (S : Set (Bond L m k)) (b : Bond L m k) :
    Continuous fun v : S → ComplexMatrix2.specialUnitary => valueAt S v b := by
  classical
  by_cases h : b ∈ S
  · simp only [valueAt, if_pos h]
    exact continuous_extendByOne S b
  · simp only [valueAt, if_neg h]
    exact (continuous_extendByOne S b.opposite).inv
theorem valueAt_opposite {S : Set (Bond L m k)} (hS : IsOrientationChoice S)
    (v : S → ComplexMatrix2.specialUnitary) (b : Bond L m k) :
    valueAt S v b.opposite = (valueAt S v b)⁻¹ := by
  classical
  rcases hS.2 b with ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    simp only [valueAt, if_pos h, if_neg h', opposite_opposite, inv_inv]
noncomputable def gaugeFieldOf {S : Set (Bond L m k)} (hS : IsOrientationChoice S)
    (v : S → ComplexMatrix2.specialUnitary) : compactGaugeFields L m k :=
  ⟨fun b => (valueAt S v b : ComplexMatrix2), fun b _ => (valueAt S v b).2, fun b _ => by
    show (valueAt S v b.opposite : ComplexMatrix2) = (valueAt S v b : ComplexMatrix2)⁻¹
    rw [valueAt_opposite hS, coe_inv]⟩
def restrictValues (S : Set (Bond L m k)) (U : compactGaugeFields L m k) :
    S → ComplexMatrix2.specialUnitary :=
  fun b => ⟨U.1 b.1, U.2.1 b.1 (mem_univ _)⟩
noncomputable def restrictHomeomorph {S : Set (Bond L m k)}
    (hS : IsOrientationChoice S) :
    compactGaugeFields L m k ≃ₜ (S → ComplexMatrix2.specialUnitary) where
  toFun := restrictValues S
  invFun := gaugeFieldOf hS
  left_inv U := by
    classical
    refine Subtype.ext (funext fun b => ?_)
    show (valueAt S (restrictValues S U) b : ComplexMatrix2) = U.1 b
    by_cases h : b ∈ S
    · simp [valueAt, extendByOne, h, restrictValues]
    · have hr : b.opposite ∈ S := by
        rcases hS.2 b with ⟨h₁, _⟩ | ⟨h₁, _⟩
        · exact absurd h₁ h
        · exact h₁
      have hU : U.1 b.opposite = (U.1 b)⁻¹ := U.2.2 b (mem_univ _)
      have e : (⟨U.1 b.opposite, U.2.1 _ (mem_univ _)⟩ : ComplexMatrix2.specialUnitary) =
          (⟨U.1 b, U.2.1 _ (mem_univ _)⟩ : ComplexMatrix2.specialUnitary)⁻¹ :=
        Subtype.ext (by rw [coe_inv]; exact hU)
      have e' : valueAt S (restrictValues S U) b = ⟨U.1 b, U.2.1 _ (mem_univ _)⟩ := by
        rw [valueAt, if_neg h, extendByOne, dif_pos hr]
        show (⟨U.1 b.opposite, U.2.1 _ (mem_univ _)⟩ : ComplexMatrix2.specialUnitary)⁻¹ = _
        rw [e, inv_inv]
      rw [e']
  right_inv v := by
    classical
    funext b
    refine Subtype.ext ?_
    show (valueAt S v b.1 : ComplexMatrix2) = v b
    simp [valueAt, extendByOne, b.2]
  continuous_toFun := continuous_pi fun b =>
    ((continuous_apply b.1).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := Continuous.subtype_mk
    (continuous_pi fun b => continuous_subtype_val.comp (continuous_valueAt S b)) _
theorem holds (hc : SiteAndPlaquetteCounts) : Statement := by
  intro L m k hL hk
  obtain ⟨hs, -, hsites, -⟩ := hc L m k hL hk
  have hstep : ∀ μ, unitStep L m k μ ≠ 0 := unitStep_ne_zero hL hs
  have hpos : 0 < (2 * L ^ ((m : ℤ) + k).toNat) ^ 4 := by positivity
  have hfs : Finite (Site L m k) := Nat.finite_of_card_ne_zero (by rw [hsites]; exact hpos.ne')
  have hfb : Finite (Bond L m k) := by
    have h : Function.Injective (fun b : Bond L m k => (b.source, b.target)) := fun b b' e =>
      Bond.ext (congrArg Prod.fst e) (congrArg Prod.snd e)
    exact Finite.of_injective _ h
  have hmet : TopologicalSpace.MetrizableSpace ComplexMatrix2 :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Fin 2 → Fin 2 → ℂ))
  have hc2 : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hc3 : SecondCountableTopology ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨S, hS⟩ := exists_orientationChoice hstep
  let e := restrictHomeomorph hS
  have hcomp : CompactSpace (compactGaugeFields L m k) := e.symm.compactSpace
  have hfb' : Fintype (Bond L m k) := Fintype.ofFinite _
  have hborel : BorelSpace (compactGaugeFields L m k) := inferInstance
  refine ⟨hfb, isCompact_iff_compactSpace.2 hcomp, inferInstance, hborel, S, hS, e,
    fun _ _ => rfl, e.continuous.measurable, e.symm.continuous.measurable⟩
end GaugeFieldsCompactProduct
end PeriodicLattice
end YangMills.Construction
