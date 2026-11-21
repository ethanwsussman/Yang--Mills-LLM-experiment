import YangMills.Construction.InfiniteLattice.FactsFromTopologyMeasureAndFunctionTheoryProof
import YangMills.Construction.Lattice.SiteCoordinates
import YangMills.Construction.Matrices.FiniteProductOfSpecialUnitary
import Mathlib
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
private theorem eq_of_isMulLeftInvariant_of_prob {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant] : μ = ν := by
  have : ν.IsHaarMeasure :=
    isHaarMeasure_of_isCompact_nonempty_interior ν Set.univ isCompact_univ
      (by simp) (by simp) (by simp)
  have h := isMulLeftInvariant_eq_smul μ ν
  have hc : (haarScalarFactor μ ν : ENNReal) = 1 := by
    have h1 := congrArg (fun ρ : Measure H => ρ Set.univ) h
    simpa using h1.symm
  have hc' : haarScalarFactor μ ν = 1 := by exact_mod_cast hc
  rw [hc', one_smul] at h
  exact h
private theorem secondCountable_specialUnitary : SecondCountableTopology specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
private theorem metrizable_specialUnitary : TopologicalSpace.MetrizableSpace specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.AmbientFacts.Proofs.metrizableSpace_specialUnitary <;> assumption
private theorem haarProb_isMulLeftInvariant : haarProb.IsMulLeftInvariant := by
  unfold haarProb
  infer_instance
private theorem haarProb_isMulRightInvariant : haarProb.IsMulRightInvariant := by
  have := secondCountable_specialUnitary
  have := haarProb_isMulLeftInvariant
  refine ⟨fun g => ?_⟩
  have : IsProbabilityMeasure (Measure.map (· * g) haarProb) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  have : (Measure.map (· * g) haarProb).IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    rw [Measure.map_map (measurable_const_mul h) (measurable_mul_const g)]
    have hcomm : (fun x : specialUnitary => h * x) ∘ (fun x => x * g) =
        (fun x => x * g) ∘ (fun x => h * x) := by
      funext x
      simp [mul_assoc]
    rw [hcomm, ← Measure.map_map (measurable_mul_const g) (measurable_const_mul h),
      map_mul_left_eq_self]
  exact eq_of_isMulLeftInvariant_of_prob _ _
private theorem finite_site_of_depth_ge (hl : PeriodicLattice.CoordinateDescription)
    {L m : ℕ} (hodd : Odd L) (h13 : 13 ≤ L) (hm : 0 < m) {j : ℤ} (hj : -(m : ℤ) ≤ j) :
    Finite (PeriodicLattice.Site L m j) := by
  obtain ⟨-, hpos, -, hcoord, hcong, -⟩ := (hl L m hodd h13 hm).1 j hj
  generalize 2 * PeriodicLattice.halfPeriod L m j = N at hpos hcong
  have : NeZero N := ⟨hpos.ne'⟩
  have hN : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hpos
  refine Finite.of_surjective
    (fun n : Fin 4 → Fin N =>
      PeriodicLattice.offsetSite (0 : PeriodicLattice.Site L m j)
        (fun μ => ((n μ : ℕ) : ℤ))) ?_
  intro x
  obtain ⟨n, rfl⟩ := hcoord 0 x
  refine ⟨fun μ => ⟨(n μ % (N : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 := Int.emod_lt_of_pos (n μ) hN
    have h2 := Int.emod_nonneg (n μ) hN.ne'
    omega
  · rw [hcong]
    intro μ
    have h2 := Int.emod_nonneg (n μ) hN.ne'
    show (((n μ % (N : ℤ)).toNat : ℕ) : ℤ) ≡ n μ [ZMOD (N : ℤ)]
    rw [Int.toNat_of_nonneg h2]
    exact Int.mod_modEq _ _
theorem finiteProductGroupStatement_holds (hl : PeriodicLattice.CoordinateDescription) :
    FiniteProductGroupStatement := by
  have := secondCountable_specialUnitary
  have := metrizable_specialUnitary
  have := haarProb_isMulLeftInvariant
  have := haarProb_isMulRightInvariant
  refine ⟨fun S _ => ?_, fun S _ => ?_, fun s A => ?_⟩
  · obtain ⟨_⟩ := nonempty_fintype S
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · obtain ⟨_⟩ := nonempty_fintype S
    have hpi : haarPi S = Measure.pi fun _ : S => haarProb := by
      unfold haarPi
      exact Measure.infinitePi_eq_pi _
    have : BorelSpace (S → specialUnitary) := Pi.borelSpace
    have : (haarPi S).IsMulLeftInvariant := by
      rw [hpi]
      infer_instance
    have : (haarPi S).IsMulRightInvariant := by
      rw [hpi]
      infer_instance
    have : IsProbabilityMeasure (haarPi S) := by
      rw [hpi]
      infer_instance
    refine ⟨BorelSpace.measurable_eq.symm, ⟨haarPi S, ⟨inferInstance, inferInstance⟩, ?_⟩,
      inferInstance, inferInstance, inferInstance⟩
    rintro μ ⟨hμ, hμ'⟩
    exact eq_of_isMulLeftInvariant_of_prob _ _
  · have hj : -((s.m : ℕ) : ℤ) ≤ PeriodicLattice.levelDepth (s.K : ℕ) 0 := by
      have h1 : 0 < (s.m : ℕ) := s.m.pos
      have h2 : 0 < (s.K : ℕ) := s.K.pos
      simp only [PeriodicLattice.levelDepth]
      omega
    have := finite_site_of_depth_ge hl s.isAdmissible.1 s.isAdmissible.2 s.m.pos hj
    exact Set.toFinite A
end YangMills.Construction.Matrices.ComplexMatrix2
