import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Lattice.PropertiesOfTheTwoSchemes
import YangMills.Construction.Matrices.UnitaryLogConjugation
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import YangMills.Construction.Towers.ValuesOfTheAveragesNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.SmoothingNearTrivialProof
open Matrices PeriodicLattice Averaging
variable {L m : ℕ} {j : ℤ}
theorem inv_mem_compactGaugeGroup {X : ComplexMatrix2} (hX : X ∈ compactGaugeGroup) :
    X⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem continuous_plaquetteHolonomy (p : PeriodicLattice.Plaquette L m j) :
    Continuous fun U : PeriodicLattice.Bond L m j → ComplexMatrix2 => plaquetteHolonomy U p := by
  unfold plaquetteHolonomy pathHolonomy
  exact continuous_list_prod _ fun b _ => continuous_apply b
theorem plaquetteHolonomy_one (p : PeriodicLattice.Plaquette L m j) :
    plaquetteHolonomy (fun _ : PeriodicLattice.Bond L m j => (1 : ComplexMatrix2)) p = 1 := by
  simp [plaquetteHolonomy, pathHolonomy]
theorem expTwist_mem_compactGaugeFields
    (hlog : ComplexMatrix2.UnitaryLogConjugationProperties) (hL : 1 < L)
    (hj : -(m : ℤ) < j) {B V : PeriodicLattice.Bond L m j → ComplexMatrix2}
    (hB : IsBondForm compactLieAlgebra B) (hV : V ∈ compactGaugeFields L m j) :
    expTwist B V ∈ compactGaugeFields L m j := by
  have hpos : ∀ b : PeriodicLattice.Bond L m j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • B b) * V b ∈ compactGaugeGroup :=
    fun b hb => mul_mem ((hlog.1 _ (hB.1 b hb)).2.2) (hV.1 b (mem_univ b))
  have hon : ∀ {b : PeriodicLattice.Bond L m j}, b.IsPositivelyOriented →
      expTwist B V b = ComplexMatrix2.matExp (Complex.I • B b) * V b :=
    fun h => by unfold expTwist; rw [if_pos h]
  have hoff : ∀ {b : PeriodicLattice.Bond L m j}, ¬b.IsPositivelyOriented →
      expTwist B V b = (ComplexMatrix2.matExp (Complex.I • B b.opposite) * V b.opposite)⁻¹ :=
    fun h => by unfold expTwist; rw [if_neg h]
  have hopp : ∀ b : PeriodicLattice.Bond L m j, b.opposite.opposite = b :=
    fun b => PeriodicLattice.Bond.ext rfl rfl
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hp : b.IsPositivelyOriented
    · rw [hon hp]
      exact hpos b hp
    · rw [hoff hp]
      exact inv_mem_compactGaugeGroup (hpos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hp))
  · by_cases hp : b.IsPositivelyOriented
    · rw [hoff (PeriodicLattice.Bond.opposite_not_isPositivelyOriented hL hj hp), hon hp, hopp]
    · have hq := PeriodicLattice.Bond.opposite_isPositivelyOriented hp
      have hu : IsUnit (ComplexMatrix2.matExp (Complex.I • B b.opposite) * V b.opposite).det := by
        rw [(Matrix.mem_specialUnitaryGroup_iff.mp (hpos _ hq)).2]
        exact isUnit_one
      rw [hon hq, hoff hp, Matrix.nonsing_inv_nonsing_inv _ hu]
theorem smoothingNearTrivialField
    (hS : PeriodicLattice.AveragingSchemeProperties)
    (hlog : ComplexMatrix2.UnitaryLogConjugationProperties)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hC : BondSetFields.ProductStructureHolds) :
    SmoothingNearTrivialField := by
  intro L n k hL hn hk
  have hL1 : 1 < L := by have := hL.2; omega
  have hω : 0 < smoothingRadius L := (isSmoothingRadius_smoothingRadius hL.1 hL.2).1
  have hplaq : ∀ i, i ≤ k → Finite (PeriodicLattice.Plaquette L n (levelDepth k i)) := fun i hi => by
    have := (hA L hL n i k hn hi).2.1
    exact this.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨fun i hi => ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨c₀, -⟩ := ((hC L hL k (i + 1) hi).1 n hn).2.2.1
    have hsub : commonSmoothingDomain L n k i ⊆ fieldSpace L n k i :=
      fun V hV => (mem_iInter.mp hV c₀).1
    refine ⟨hsub, ?_⟩
    have hall := ((hC L hL k i hi.le).1 n hn).2
    have hfin : Finite (Edge L n k (i + 1)) :=
      Set.finite_univ_iff.mp ((hC L hL k (i + 1) hi).1 n hn).2.1
    have := hplaq i hi.le
    let P : Set (Edge L n k i → ComplexMatrix2) :=
      ⋂ c : Edge L n k (i + 1), ⋂ p : PeriodicLattice.Plaquette L n (levelDepth k i),
        {U | p ∈ (doubleBlockPlaquettes c : Set (PeriodicLattice.Plaquette L n (levelDepth k i))) →
          ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) < smoothingRadius L}
    have hP : IsOpen P := by
      refine isOpen_iInter_of_finite fun c => isOpen_iInter_of_finite fun p => ?_
      by_cases hp : p ∈ (doubleBlockPlaquettes c : Set (PeriodicLattice.Plaquette L n (levelDepth k i)))
      · simp only [hp, forall_true_left]
        exact isOpen_lt ((continuous_plaquetteHolonomy p).sub continuous_const).norm continuous_const
      · simp [hp]
    have hD : commonSmoothingDomain L n k i = P ∩ fieldSpace L n k i := by
      ext U
      constructor
      · intro hU
        exact ⟨mem_iInter.mpr fun c => mem_iInter.mpr fun p hp => (mem_iInter.mp hU c).2 p hp,
          hsub hU⟩
      · rintro ⟨hU, hc⟩
        exact mem_iInter.mpr fun c => ⟨hc, fun p hp => mem_iInter.mp (mem_iInter.mp hU c) p hp⟩
    exact (hall.2.2.2.2.2.2.2.1 _ hsub).mp ⟨P, hP, hD⟩
  · refine mem_iInter.mpr fun c => ⟨⟨fun b _ => one_mem _, fun b _ => by simp⟩, fun p _ => ?_⟩
    show ComplexMatrix2.operatorNorm (plaquetteHolonomy (fun _ => (1 : ComplexMatrix2)) p - 1) <
      smoothingRadius L
    rw [plaquetteHolonomy_one, sub_self]
    simpa using hω
  · intro V hV c hc
    have hVc := mem_iInter.mp hV c
    have hfield : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) V :=
      ⟨fun b _ => hVc.1.1 b (mem_univ b), fun b _ => hVc.1.2 b (mem_univ b)⟩
    have hcurv : doubleBlockCurvature V c < smoothingRadius L := by
      unfold doubleBlockCurvature
      have := hplaq i hi.le
      rcases isEmpty_or_nonempty
        ↥(doubleBlockPlaquettes c : Set (PeriodicLattice.Plaquette L n (levelDepth k i))) with he | he
      · rw [Real.iSup_of_isEmpty]
        exact hω
      · obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite
          (f := fun p : ↥(doubleBlockPlaquettes c :
              Set (PeriodicLattice.Plaquette L n (levelDepth k i))) =>
            ComplexMatrix2.operatorNorm (plaquetteHolonomy V p.1 - 1))
        rw [← hp]
        exact hVc.2 p.1 p.2
    have hsch := (hS L hL n k i hn hi .centred).2.1 c hc
    have hmean := hsch.2.2.2.2.1 V hfield hcurv
    have hval := hsch.2.2.2.1 V hmean.mem_domain hfield
    refine ⟨hfield, hcurv, hmean.unique_mean,
      fun y hy x hx => hmean.contour_eq y hy x hx ▸ hval.contour_mem y hy x hx, ?_⟩
    show blockAverage (smoothingRadius L) V c ∈ compactGaugeGroup
    rw [← hmean.average_eq]
    exact hval.average_mem
  · intro r hr B hB V hV
    have hj : -(n : ℤ) < levelDepth k r := by
      show -(n : ℤ) < (k : ℤ) - (r : ℤ)
      omega
    exact expTwist_mem_compactGaugeFields hlog hL1 hj hB hV
end YangMills.Construction.Tower.SmoothingNearTrivialProof
end
