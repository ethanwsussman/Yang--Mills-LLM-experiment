import YangMills.Construction.InfiniteLattice.ConfigurationsOfTheTorusLatticeAtPositiveLinks
import YangMills.Construction.InfiniteLattice.PullBackOfAConfigurationByAnInducedIsometryProof
import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import YangMills.Construction.LawInAState.GridDataAtEveryExponentProofForm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction.CutoffLinks.PositiveLinksProof
variable {L m : ℕ} {j : ℤ}
theorem opposite_opposite (b : Bond L m j) : b.opposite.opposite = b := Bond.ext rfl rfl
theorem finite_sites_bonds_plaquettes (hquot : QuotientLattices.TorusAndSpaceLatticeProperties)
    {L m K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 1 ≤ m) :
    Finite (Site L m (K : ℤ)) ∧ Finite (Bond L m (K : ℤ)) ∧ Finite (Plaquette L m (K : ℤ)) := by
  have h := (hquot L hL m 0 K hm (Nat.zero_le K)).2.1
  unfold QuotientLattices.IsQuotientLattice at h
  have e : QuotientLattices.refinementIndex K 0 = (K : ℤ) := by
    simp [QuotientLattices.refinementIndex]
  rw [e] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsite, hbond, hface⟩ := h
  exact ⟨hsite, hbond, hface⟩
theorem exists_opposite_iff (l : Bond L m j) :
    (∃ l' ∈ forwardBonds L m j, l = l'.opposite) ↔ l.opposite.IsPositivelyOriented := by
  constructor
  · rintro ⟨l', hl', rfl⟩
    rw [opposite_opposite]
    exact mem_positiveBonds_iff.1 hl'
  · intro h
    exact ⟨l.opposite, mem_positiveBonds_iff.2 h, (opposite_opposite l).symm⟩
theorem bijective_restrict {ι : Type} {X : Type}
    (P : ι → Prop) (S : Set ι) (hS : ∀ b, b ∈ S ↔ P b)
    (v : X → {b // P b} → Matrices.ComplexMatrix2.specialUnitary)
    (hv : Function.Bijective v) :
    Function.Bijective (fun (U : X) (l : S) => v U ⟨l.1, (hS l.1).1 l.2⟩) := by
  constructor
  · intro U U' h
    refine hv.1 (funext fun b => ?_)
    exact congrFun h ⟨b.1, (hS b.1).2 b.2⟩
  · intro Y
    obtain ⟨U, hU⟩ := hv.2 fun b => Y ⟨b.1, (hS b.1).2 b.2⟩
    exact ⟨U, funext fun l => congrFun hU ⟨l.1, (hS l.1).1 l.2⟩⟩
theorem plaquetteEnergy_eq_re (U : Bond L m j → Matrices.ComplexMatrix2) (p : Plaquette L m j) :
    plaquetteCost U p = (plaquetteEnergy U p).re := by
  simp [plaquetteCost, plaquetteEnergy]
theorem plaquetteEnergy_mem_Icc
    (h : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m j)
    (U : CompactGaugeField L m j) (p : Plaquette L m j) :
    plaquetteCost U.1 p ∈ Icc (0 : ℝ) 2 := by
  obtain ⟨t, ht, e⟩ := (h p).2 U
  rw [plaquetteEnergy_eq_re, ← e]
  simpa using ht
theorem plaquetteEnergy_congr (p : Plaquette L m j) (U U' : CompactGaugeField L m j)
    (h : ∀ l : Bond L m j, l ∈ InfiniteLattice.WilsonOperator.periodicEdgeList p →
      U.linkValue l = U'.linkValue l) :
    plaquetteCost U.1 p = plaquetteCost U'.1 p := by
  have hv : ∀ l ∈ InfiniteLattice.WilsonOperator.periodicEdgeList p, U.1 l = U'.1 l :=
    fun l hl => congrArg Subtype.val (h l hl)
  simp only [InfiniteLattice.WilsonOperator.periodicEdgeList, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hv
  obtain ⟨e₁, e₂, e₃, e₄⟩ := hv
  have hr : ∀ b : Bond L m j, U.1 b.opposite = (U.1 b)⁻¹ := fun b => U.2.2 b (mem_univ b)
  have hr' : ∀ b : Bond L m j, U'.1 b.opposite = (U'.1 b)⁻¹ := fun b => U'.2.2 b (mem_univ b)
  simp only [plaquetteCost, plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hr, hr', e₁, e₂, e₃, e₄]
theorem gaugeFieldOfPositive_restrict
    (hx : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (U : CompactGaugeField L m j) :
    gaugeFieldOfPositive (restrictToPositiveBonds U) = U.1 := by apply _root_.YangMills.Construction.InducedPullback.gaugeFieldOfPositive_restrict <;> assumption
theorem measurable_gaugeFieldOfPositive :
    Measurable (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) →
        Bond L m j → Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
theorem measurable_boltzmannWeight [Finite (Plaquette L m j)] (β : ℝ) :
    Measurable (boltzmannWeight β : (Bond L m j → Matrices.ComplexMatrix2) → ℝ) := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.boltzmannWeight_measurable <;> assumption
theorem wilsonAction_bounded [Finite (Plaquette L m j)]
    (h : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m j) :
    ∃ C : ℝ, ∀ U : CompactGaugeField L m j, 0 ≤ wilsonAction U.1 ∧ wilsonAction U.1 ≤ C := by
  have := Fintype.ofFinite (Plaquette L m j)
  refine ⟨∑ _p : Plaquette L m j, 2, fun U => ?_⟩
  unfold wilsonAction
  rw [finsum_eq_sum_of_fintype]
  exact ⟨Finset.sum_nonneg fun p _ => (plaquetteEnergy_mem_Icc h U p).1,
    Finset.sum_le_sum fun p _ => (plaquetteEnergy_mem_Icc h U p).2⟩
theorem partitionFunction_mem_Ioc {L m K : ℕ} [Finite (Plaquette L m (K : ℤ))]
    (hact : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m (K : ℤ))
    (hx : ∀ b : Bond L m (K : ℤ), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hs : Function.Surjective
      (restrictToPositiveBonds : CompactGaugeField L m (K : ℤ) → _))
    {β : ℝ} (hβ : 0 < β) :
    0 < partitionFunction L m K β ∧ partitionFunction L m K β ≤ 1 := by
  obtain ⟨C, hC⟩ := wilsonAction_bounded hact
  have : IsProbabilityMeasure (gaugeFieldHaar L m (K : ℤ)) := by
    unfold gaugeFieldHaar Matrices.ComplexMatrix2.haarPi
    infer_instance
  have hg := measurable_gaugeFieldOfPositive (L := L) (m := m) (j := (K : ℤ))
  have hf := measurable_boltzmannWeight (L := L) (m := m) (j := (K : ℤ)) β
  have e : partitionFunction L m K β =
      ∫ v, boltzmannWeight β (gaugeFieldOfPositive v) ∂gaugeFieldHaar L m (K : ℤ) := by
    unfold partitionFunction productHaarMeasure
    exact integral_map hg.aemeasurable hf.aestronglyMeasurable
  have hb : ∀ v : PositivelyOrientedBond L m (K : ℤ) → Matrices.ComplexMatrix2.specialUnitary,
      Real.exp (-β * C) ≤ boltzmannWeight β (gaugeFieldOfPositive v) ∧
        boltzmannWeight β (gaugeFieldOfPositive v) ≤ 1 := by
    intro v
    obtain ⟨U, rfl⟩ := hs v
    rw [gaugeFieldOfPositive_restrict hx U]
    obtain ⟨h₀, h₁⟩ := hC U
    unfold boltzmannWeight
    exact ⟨Real.exp_le_exp.2 (by nlinarith), Real.exp_le_one_iff.2 (by nlinarith)⟩
  have hint : Integrable (fun v => boltzmannWeight β (gaugeFieldOfPositive v))
      (gaugeFieldHaar L m (K : ℤ)) := by
    refine Integrable.of_bound (hf.comp hg).aestronglyMeasurable 1 (ae_of_all _ fun v => ?_)
    have h₀ : 0 ≤ boltzmannWeight β (gaugeFieldOfPositive v) :=
      (Real.exp_pos _).le.trans (hb v).1
    rw [Real.norm_of_nonneg h₀]
    exact (hb v).2
  rw [e]
  constructor
  · calc (0 : ℝ) < Real.exp (-β * C) := Real.exp_pos _
      _ = ∫ _v, Real.exp (-β * C) ∂gaugeFieldHaar L m (K : ℤ) := by simp
      _ ≤ _ := integral_mono (integrable_const _) hint fun v => (hb v).1
  · calc _ ≤ ∫ _v, (1 : ℝ) ∂gaugeFieldHaar L m (K : ℤ) :=
          integral_mono hint (integrable_const _) fun v => (hb v).2
      _ = 1 := by simp
theorem periodicFieldsAtPositiveLinks (hquot : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hor : PeriodicLattice.BondOrientationDichotomy)
    (hprod : GaugeFieldProduct.Statement) : CutoffLinks.PeriodicFieldsAtPositiveLinks := by
  intro d
  have hL := d.isAdmissible
  have hm : 0 < (d.m : ℕ) := d.m.pos
  have hK : 0 < (d.K : ℕ) := d.K.pos
  obtain ⟨hS, hB, hP⟩ := finite_sites_bonds_plaquettes hquot (K := (d.K : ℕ)) hL hm
  obtain ⟨-, -, ⟨hbij, -⟩, hact⟩ :=
    hprod.1 d.L d.m ((d.K : ℕ) : ℤ) hL hm (by omega)
  have hx : ∀ b : Bond d.L d.m ((d.K : ℕ) : ℤ),
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    hor d.L d.m hL hm _ (by omega)
  refine ⟨⟨hS, hB, hP, fun l => ?_, ?_⟩, fun P => ⟨?_, fun U => ?_, fun U U' h => ?_⟩,
    partitionFunction_mem_Ioc hact hx hbij.2 d.coupling_pos⟩
  · have h := hx l
    rw [← mem_positiveBonds_iff (b := l), ← exists_opposite_iff l] at h
    exact h
  · exact bijective_restrict Bond.IsPositivelyOriented d.positiveLinkSet
      (fun _ => mem_positiveBonds_iff) restrictToPositiveBonds hbij
  · exact (Complex.continuous_re.comp (hact P).1).congr
      fun U => (plaquetteEnergy_eq_re U.1 P).symm
  · exact plaquetteEnergy_mem_Icc hact U P
  · exact plaquetteEnergy_congr P U U' h
end YangMills.Construction.CutoffLinks.PositiveLinksProof
