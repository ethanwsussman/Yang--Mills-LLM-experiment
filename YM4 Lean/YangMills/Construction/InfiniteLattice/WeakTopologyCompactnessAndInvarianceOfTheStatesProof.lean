import YangMills.Construction.InfiniteLattice.PeriodsFoldCompactnessAndLimitsOfToriProof
import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservables
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.InvarianceOfStatesUnderIsometriesOfACutoffLatticeProof
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndSpaceOfMeasures
import YangMills.Construction.InfiniteLattice.WeakTopologyCompactnessAndInvarianceOfTheStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Filter GibbsAtFixedSpacing
open scoped Topology
namespace InfiniteLattice.WeakCompactness
variable {a : ℝ}
def toBorelProb (μ : ProbabilityMeasure (GaugeField a)) : BorelProb a := ⟨μ.1, μ.2⟩
theorem toBorelProb_surjective : Function.Surjective (toBorelProb (a := a)) :=
  fun ν => ⟨⟨ν.1, ν.2⟩, rfl⟩
theorem probabilityMeasuresWeakTopology_eq_induced :
    probabilityMeasuresWeakTopology a =
      TopologicalSpace.induced toBorelProb BorelProb.instTopologicalSpace := by
  rw [BorelProb.instTopologicalSpace, induced_iInf]
  apply le_antisymm
  · refine le_iInf fun F => ?_
    rw [induced_compose]
    exact iInf_le_of_le ⟨F.1, F.2⟩ le_rfl
  · refine le_iInf fun F => ?_
    refine iInf_le_of_le ⟨F, F.continuous⟩ ?_
    rw [induced_compose]
    exact le_rfl
theorem continuous_stateEval (F : GaugeField a → ℂ) (hF : Continuous F) :
    @Continuous _ _ (probabilityMeasuresWeakTopology a) _
      (fun μ : ProbabilityMeasure (GaugeField a) =>
        stateEval (μ : Measure (GaugeField a)) F) := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsFoldAndCompactness.continuous_integral_weakTopology <;> assumption
theorem compactSpace_and_firstCountable [CompactSpace (BorelProb a)]
    [TopologicalSpace.MetrizableSpace (BorelProb a)] :
    @CompactSpace _ (probabilityMeasuresWeakTopology a) ∧
      @FirstCountableTopology _ (probabilityMeasuresWeakTopology a) := by
  let _ := probabilityMeasuresWeakTopology a
  have hInd : Topology.IsInducing (toBorelProb (a := a)) :=
    ⟨probabilityMeasuresWeakTopology_eq_induced⟩
  refine ⟨⟨?_⟩, hInd.firstCountableTopology⟩
  rw [hInd.isCompact_iff, Set.image_univ, toBorelProb_surjective.range_eq]
  exact isCompact_univ
theorem weakBasicNhd_isWeakOpen (ν : Measure (GaugeField a)) (N : Set (Measure (GaugeField a)))
    (hν : IsLatticeState ν) (hN : IsWeakBasicNhd ν N) : IsWeakOpen N ∧ ν ∈ N := by
  obtain ⟨k, F, ε, -, hF, hε, rfl⟩ := hN
  refine ⟨⟨fun ρ hρ => hρ.1, ?_⟩, hν, fun l => by simpa using hε⟩
  have hPts : asProbabilityMeasures (weakBasicNhd ν F ε) =
      ⋂ l, {μ : ProbabilityMeasure (GaugeField a) |
        ‖stateEval (μ : Measure (GaugeField a)) (F l) - stateEval ν (F l)‖ < ε} := by
    ext μ
    rw [Set.mem_iInter]
    exact ⟨fun h => h.2, fun h => ⟨μ.2, h⟩⟩
  rw [hPts]
  let _ := probabilityMeasuresWeakTopology a
  exact isOpen_iInter_of_finite fun l =>
    isOpen_lt ((continuous_stateEval (F l) (hF l)).sub continuous_const).norm continuous_const
theorem exists_weakBasicNhd_subset (ν : ProbabilityMeasure (GaugeField a))
    (N : Set (ProbabilityMeasure (GaugeField a)))
    (hN : N ∈ @nhds _ (probabilityMeasuresWeakTopology a) ν) :
    ∃ B : Set (Measure (GaugeField a)),
      IsWeakBasicNhd (ν : Measure (GaugeField a)) B ∧ asProbabilityMeasures B ⊆ N := by
  have hN' : N ∈ ⨅ F : C(GaugeField a, ℂ),
      comap (fun μ : ProbabilityMeasure (GaugeField a) =>
        ∫ U, F U ∂(μ : Measure (GaugeField a)))
        (𝓝 (∫ U, F U ∂(ν : Measure (GaugeField a)))) := by
    simpa only [probabilityMeasuresWeakTopology, nhds_iInf, nhds_induced] using hN
  obtain ⟨I, hI, V, hV, rfl⟩ := Filter.mem_iInf.1 hN'
  have hFin : Finite I := hI.to_subtype
  have hRad : ∀ i : I, ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ProbabilityMeasure (GaugeField a),
      ‖stateEval (μ : Measure (GaugeField a)) i.1 -
        stateEval (ν : Measure (GaugeField a)) i.1‖ < δ → μ ∈ V i := by
    intro i
    obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.1 (hV i)
    obtain ⟨δ, hδ, hBall⟩ := Metric.mem_nhds_iff.1 hW
    refine ⟨δ, hδ, fun μ hμ => hWV (hBall ?_)⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact hμ
  choose δ hδPos hδ using hRad
  let r : Option I → ℝ := fun o => o.elim 1 δ
  have hr : ∀ o, 0 < r o := by
    rintro (_ | i)
    · exact one_pos
    · exact hδPos i
  obtain ⟨o₀, ho₀⟩ := Finite.exists_min r
  let G : Option I → GaugeField a → ℂ := fun o => o.elim 0 (fun i => ⇑i.1)
  have hG : ∀ o, Continuous (G o) := by
    rintro (_ | i)
    · exact continuous_const
    · exact i.1.continuous
  let e := Finite.equivFin (Option I)
  refine ⟨weakBasicNhd (ν : Measure (GaugeField a)) (fun l => G (e.symm l)) (r o₀),
    ⟨Nat.card (Option I), _, _, Nat.card_pos, fun l => hG _, hr o₀, rfl⟩, ?_⟩
  intro μ hμ
  refine Set.mem_iInter.2 fun i => hδ i μ ?_
  have hl := hμ.2 (e (some i))
  simp only [Equiv.symm_apply_apply] at hl
  exact hl.trans_le (ho₀ (some i))
def shiftedSeq (ν : ℕ → Measure (GaugeField a)) (hν : ∀ i, 1 ≤ i → IsLatticeState (ν i))
    (i : ℕ) : ProbabilityMeasure (GaugeField a) :=
  ⟨ν (i + 1), hν (i + 1) (Nat.le_add_left 1 i)⟩
theorem isWeakClusterPoint_iff_mapClusterPt (ν : ℕ → Measure (GaugeField a))
    (hν : ∀ i, 1 ≤ i → IsLatticeState (ν i)) (μ : ProbabilityMeasure (GaugeField a)) :
    IsWeakClusterPoint ν (μ : Measure (GaugeField a)) ↔
      @MapClusterPt _ (probabilityMeasuresWeakTopology a) _ μ atTop (shiftedSeq ν hν) := by
  let _ := probabilityMeasuresWeakTopology a
  rw [mapClusterPt_iff_frequently]
  constructor
  · intro hl s hs
    obtain ⟨B, ⟨k, F, ε, -, hF, hε, rfl⟩, hB⟩ := exists_weakBasicNhd_subset μ s hs
    rw [frequently_atTop]
    intro i₀
    obtain ⟨i, hi, hF'⟩ := hl (Set.range F) (Set.finite_range F)
      (by rintro _ ⟨l, rfl⟩; exact hF l) (ε / 2) (half_pos hε) (i₀ + 1) (Nat.le_add_left 1 i₀)
    have hSucc : i - 1 + 1 = i := by omega
    refine ⟨i - 1, by omega, hB ⟨(shiftedSeq ν hν (i - 1)).2, fun l => ?_⟩⟩
    have hlt := (hF' (F l) ⟨l, rfl⟩).trans_lt (half_lt_self hε)
    change ‖stateEval (ν (i - 1 + 1)) (F l) - _‖ < ε
    rw [hSucc]
    exact hlt
  · intro hc 𝒞 h𝒞 hCont ε hε i₀ _
    have hNhd : (⋂ F ∈ 𝒞, {ρ : ProbabilityMeasure (GaugeField a) |
        ‖stateEval (ρ : Measure (GaugeField a)) F -
          stateEval (μ : Measure (GaugeField a)) F‖ < ε}) ∈ 𝓝 μ := by
      refine (Filter.biInter_mem h𝒞).2 fun F hF => ?_
      refine (isOpen_lt ((continuous_stateEval F (hCont F hF)).sub continuous_const).norm
        continuous_const).mem_nhds ?_
      simpa using hε
    obtain ⟨i, hi, hMem⟩ := frequently_atTop.1 (hc _ hNhd) i₀
    refine ⟨i + 1, by omega, fun F hF => ?_⟩
    exact (Set.mem_iInter₂.1 hMem F hF).le
theorem isWeakClusterPoint_of_subseq (ν : ℕ → Measure (GaugeField a))
    (ν₀ : Measure (GaugeField a)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hConv : StatesTendstoWeakly (ν ∘ φ) ν₀) : IsWeakClusterPoint ν ν₀ := by
  intro 𝒞 h𝒞 hCont ε hε i₀ _
  have hEv : ∀ᶠ k in atTop, ∀ F ∈ 𝒞,
      ‖stateEval ((ν ∘ φ) k) F - stateEval ν₀ F‖ ≤ ε := by
    refine (Filter.eventually_all_finite h𝒞).2 fun F hF => ?_
    filter_upwards [Metric.tendsto_nhds.1 (hConv F (hCont F hF)) ε hε] with k hk
    rw [dist_eq_norm] at hk
    exact hk.le
  obtain ⟨k, hk, hk'⟩ := (hEv.and (eventually_ge_atTop i₀)).exists
  exact ⟨φ k, hk'.trans (hφ.id_le k), hk⟩
theorem exists_subseq_of_isWeakClusterPoint
    [@FirstCountableTopology _ (probabilityMeasuresWeakTopology a)]
    (ν : ℕ → Measure (GaugeField a)) (hν : ∀ i, 1 ≤ i → IsLatticeState (ν i))
    (μ : ProbabilityMeasure (GaugeField a))
    (hl : IsWeakClusterPoint ν (μ : Measure (GaugeField a))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StatesTendstoWeakly (ν ∘ φ) (μ : Measure (GaugeField a)) := by
  let _ := probabilityMeasuresWeakTopology a
  obtain ⟨ψ, hψ, ht⟩ := MapClusterPt.tendsto_subseq
    ((isWeakClusterPoint_iff_mapClusterPt ν hν μ).1 hl)
  refine ⟨fun k => ψ k + 1, fun i j h => Nat.add_lt_add_right (hψ h) 1, fun F hF => ?_⟩
  exact ((continuous_stateEval F hF).tendsto μ).comp ht
theorem isBoundedObservable_of_continuous [CompactSpace (GaugeField a)]
    {F : GaugeField a → ℂ} (hF : Continuous F) : IsBoundedObservable F := by apply _root_.YangMills.Construction.CutoffLatticeStates.MotionInvariance.isBoundedObservable_of_continuous <;> assumption
def idSymmetry (a : ℝ) : LatticeSymmetry a where
  toFun := id
  preservesDist _ _ := rfl
  image_eq := Set.image_id _
theorem isSymmetricUnder_idSymmetry (ν : Measure (GaugeField a)) :
    IsSymmetricUnder ν (idSymmetry a) := by
  intro A _
  have h : ∀ U : GaugeField a, (idSymmetry a).pullbackField U = U :=
    fun U => Subtype.ext (funext fun b => rfl)
  simp only [LatticeSymmetry.actOn, h]
theorem exists_subgroup_of_symmetries (hInv : LatticeSymmetryInverses a)
    (hComp : SymmetricUnderCompAndMultiples a)
    (ν : Measure (GaugeField a)) (hν : IsLatticeState ν) :
    ∃ G : Subgroup (Equiv.Perm AmbientSpace), ∀ f : AmbientSpace → AmbientSpace,
      (∃ r : LatticeSymmetry a, r.toFun = f ∧ IsSymmetricUnder ν r) ↔ ∃ g ∈ G, ⇑g = f := by
  let G : Subgroup (Equiv.Perm AmbientSpace) :=
    { carrier := {g | ∃ r : LatticeSymmetry a, r.toFun = ⇑g ∧ IsSymmetricUnder ν r}
      mul_mem' := by
        rintro g g' ⟨r, hr, hi⟩ ⟨r', hr', hi'⟩
        refine ⟨r.comp r', ?_, (hComp ν hν).1 r r' hi hi'⟩
        change r.toFun ∘ r'.toFun = _
        rw [hr, hr']
        rfl
      one_mem' := ⟨idSymmetry a, rfl, isSymmetricUnder_idSymmetry ν⟩
      inv_mem' := by
        rintro g ⟨r, hr, hi⟩
        obtain ⟨-, ⟨t, ht⟩, hAll⟩ := hInv r
        refine ⟨t, ?_, (hAll t ht).2 ν hν hi⟩
        funext x
        apply g.injective
        have h := ht.2 x
        rw [hr] at h
        rw [h]
        simp }
  refine ⟨G, fun f => ⟨?_, ?_⟩⟩
  · rintro ⟨r, rfl, hi⟩
    exact ⟨Equiv.ofBijective _ (hInv r).1, ⟨r, rfl, hi⟩, rfl⟩
  · rintro ⟨g, ⟨r, hr, hi⟩, rfl⟩
    exact ⟨r, hr, hi⟩
theorem weakCompactnessAndSymmetryOfStates_holds
    (hm : FieldsAtSpacing.CompactFieldsAndMeasures)
    (he : ElementaryLatticeFacts)
    (hAct : SymmetryActionOnObservables) :
    WeakCompactnessAndSymmetryOfStates := by
  intro a ha
  obtain ⟨⟨-, -, -, -, hcV, -, -, -⟩, -, ⟨hcP, hmP⟩, -⟩ := hm a ha
  obtain ⟨-, -, -, hLoc, -, -, -, hIso, -⟩ := he a 1 ha one_pos
  obtain ⟨-, -, -, -, -, -, -, -, -, hInv, hComp⟩ := hAct ⟨a, ha⟩
  obtain ⟨hCompact, hFirst⟩ := compactSpace_and_firstCountable (a := a)
  have hDet := hLoc.2.2.2.2.2.1
  refine ⟨fun ν ν' hν hν' h => hDet ν ν' hν hν' h, weakBasicNhd_isWeakOpen,
    exists_weakBasicNhd_subset, ?_, ?_, ⟨fun ρ hρ => hρ, ?_⟩, ?_,
    exists_subgroup_of_symmetries hInv hComp⟩
  · intro ν ν₀ hν hν₀
    refine ⟨exists_subseq_of_isWeakClusterPoint ν hν ⟨ν₀, hν₀⟩, ?_⟩
    rintro ⟨φ, hφ, hConv⟩
    exact isWeakClusterPoint_of_subseq ν ν₀ φ hφ hConv
  · intro ν hν
    let _ := probabilityMeasuresWeakTopology a
    obtain ⟨x, hx⟩ := exists_clusterPt_of_compactSpace (map (shiftedSeq ν hν) atTop)
    exact ⟨(x : Measure (GaugeField a)), x.2,
      (isWeakClusterPoint_iff_mapClusterPt ν hν x).2 hx⟩
  · have hPts : asProbabilityMeasures {ρ : Measure (GaugeField a) | IsLatticeState ρ} =
        Set.univ :=
      Set.eq_univ_of_forall fun μ => μ.2
    rw [hPts]
    exact @isCompact_univ _ (probabilityMeasuresWeakTopology a) hCompact
  · intro ν r hν
    have hInvar := ((hIso r r).2.2.2.2.2.2 ν hν).2.2
    constructor
    · intro h F hF
      exact h F (isBoundedObservable_of_continuous hF)
    · intro h
      exact hInvar.2 fun F hF => h F hF.2.2
end InfiniteLattice.WeakCompactness
end YangMills.Construction
end
