import YangMills.Construction.Averaging.ArgumentsOfTheBlockAverageLieInTheirDomains
import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Lattice.CovarianceOfComplexContourVariablesProof
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.Averaging.BlockArguments
open YangMills.Construction.PeriodicLattice YangMills.Construction.Matrices
theorem pathHolonomy_mem_complexGaugeGroup {L m : ℕ} {j : ℤ} {V : Bond L m j → ComplexMatrix2}
    (Γ : List (Bond L m j)) (h : ∀ b ∈ Γ, V b ∈ complexGaugeGroup) :
    pathHolonomy V Γ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.pathHolonomy_mem_complexGaugeGroup <;> assumption
theorem familyDiameter_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι)
    (V : ι → ComplexMatrix2) :
    ComplexMatrix2.familyDiameter (V ∘ e) = ComplexMatrix2.familyDiameter V := by
  unfold ComplexMatrix2.familyDiameter
  exact (e.prodCongr e).iSup_comp
    (g := fun p : ι × ι => ComplexMatrix2.operatorNorm (V p.1 * (V p.2)⁻¹ - 1))
theorem isLogMean_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι)
    (V : ι → ComplexMatrix2) (W : ComplexMatrix2) :
    ComplexMatrix2.IsLogMean complexGaugeGroup (V ∘ e) W ↔
      ComplexMatrix2.IsLogMean complexGaugeGroup V W := by
  unfold ComplexMatrix2.IsLogMean
  refine and_congr_right fun _ => and_congr ?_ ?_
  · exact (e.surjective.forall
      (p := fun i => ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) < 1)).symm
  · have hsum := e.sum_comp fun i => ComplexMatrix2.logSeries (V i * W⁻¹)
    simp only [Function.comp]
    rw [hsum]
theorem isFamilyLogMean_of_small {ι : Type*} [Fintype ι] [Nonempty ι]
    (hM : ∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n) (V : ι → ComplexMatrix2)
    (hG : ∀ i, V i ∈ complexGaugeGroup)
    (hd : ComplexMatrix2.familyDiameter V < centreOfMassDiameter) :
    IsFamilyLogMean V := by
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hsmall : V ∘ e ∈ smallComplexFamilies (Fintype.card ι) :=
    ⟨fun i => hG _, by rw [familyDiameter_comp_equiv]; exact hd⟩
  obtain ⟨W₀, hW₀, huniq⟩ := (hM _ hn).existsUnique _ hsmall
  have near : ∀ W, IsNearComplexLogMean (V ∘ e) W ↔
      (ComplexMatrix2.IsLogMean complexGaugeGroup V W ∧
        ∃ i, ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ complexMeanTolerance) := by
    intro W
    unfold IsNearComplexLogMean
    refine and_congr (isLogMean_comp_equiv e V W) ?_
    exact (e.surjective.exists
      (p := fun i => ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ complexMeanTolerance)).symm
  have hspec : ComplexMatrix2.IsLogMean complexGaugeGroup V (complexLogMean V) ∧
      ∃ i, ComplexMatrix2.operatorNorm (V i * (complexLogMean V)⁻¹ - 1) ≤ complexMeanTolerance :=
    Classical.epsilon_spec (p := fun W => ComplexMatrix2.IsLogMean complexGaugeGroup V W ∧
      ∃ i, ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ complexMeanTolerance)
      ⟨W₀, (near W₀).1 hW₀⟩
  refine ⟨hG, hspec.1, hspec.2, fun W hW hWi => ?_⟩
  rw [huniq W ((near W).2 ⟨hW, hWi⟩), huniq _ ((near _).2 hspec)]
theorem holds_of_radii (hR : ExplicitRadii.Holds)
    (hD : DoubleBlockStructure.Statement) : Holds := by
  intro s k hk c
  have hL : 0 < s.L := by
    have := s.isAdmissible.2
    omega
  have hm : 0 < (s.m : ℕ) := s.m.pos
  have hS := hR.2.2.1 s
  have hM := hR.1.2.2.2.2.2
  obtain ⟨-, hCont, hCross, -⟩ := hD s.L s.m s.K k s.isAdmissible hm hk c
  have hFinite := SeparatedSequences.BaseParameters.site_finite hL (s.m : ℕ) (levelDepth (s.K : ℕ) k)
  have hIndex : ∀ (y : SiteAtLevel s.L s.m s.K (k + 1)) (x : SiteAtLevel s.L s.m s.K k),
      Nonempty (AxisOrdering y x) := fun y x => ⟨(offsetAxes y x).equivFin.symm⟩
  refine ⟨fun y _ => Set.toFinite _, fun x hx => (hCross.1 x hx).1, fun y _ x => hIndex y x,
    ?_, ?_, fun ω hω hc => hS.regular ω hω k hk c hc, fun ω hω hc => hS.complexDomain ω hω k hk c hc⟩
  · intro U hU y hy x hx
    have hy' : y = c.source ∨ y = c.target := hy
    have := hIndex y x
    refine isFamilyLogMean_of_small hM _ (fun σ => pathHolonomy_mem_complexGaugeGroup _ fun b hb =>
      hU.1.1 b ((hCont y hy' x hx _ ⟨σ, rfl⟩).2 b hb)) ?_
    rcases hy' with rfl | rfl
    · exact hU.2.1 x hx
    · exact hU.2.2 x hx
  · intro ω hω U hU
    have hdiam := hS.contoursSmall ω hω k hk c U hU
    refine ⟨⟨fun b _ => (Matrix.mem_specialUnitaryGroup_iff.mp (hU.1.1 b (mem_univ b))).2,
      fun b _ => hU.1.2 b (mem_univ b)⟩, fun x hx => hdiam _ (Or.inl rfl) x hx,
      fun x hx => hdiam _ (Or.inr rfl) x hx⟩
end YangMills.Construction.Averaging.BlockArguments
