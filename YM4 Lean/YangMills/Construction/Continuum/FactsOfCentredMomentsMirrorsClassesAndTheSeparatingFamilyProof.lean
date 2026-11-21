import YangMills.Construction.Lattice.ConnectedFunctionsAtArbitraryArguments
import YangMills.Construction.Continuum.FactsOfCentredMomentsMirrorsClassesAndTheSeparatingFamily
import YangMills.Construction.Continuum.FactsOfTheSeparatingFamily
import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.InfiniteLattice.CentredIdentityInAState
import YangMills.Construction.Lattice.ConnectedFunctionsAndTheCentredIdentityAtArbitraryFunctions
import YangMills.Construction.PassageToTheLimit.WhatPassesToTheLimitProof
import YangMills.Construction.ReflectionPositivity.HyperplanesOfATorusMirrorAreOfOneKind
import YangMills.Construction.ReflectionPositivity.WhatAMirrorOfEachKindContains
import YangMills.Construction.Torus.CentredFunctionalOfAFamilyOfConnectedFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
open AmbientPoints
open TorusFunctionals (sharpNormAt)
namespace ContinuumSetting
section Multilinear
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
theorem isTupleMultilinear_of_additive_smul (P : (Pt s E → ℝ) → Prop)
    (hP : ∀ g, IsC1Fn g → IsCompact (tsupport g) → P g)
    (Ψ : (Fin n → Pt s E → ℝ) → ℝ)
    (hadd : ∀ f : Fin n → Pt s E → ℝ, (∀ k, P (f k)) → ∀ (i : Fin n) (g g' : Pt s E → ℝ),
      P g → P g' →
        Ψ (Function.update f i (g + g')) = Ψ (Function.update f i g) + Ψ (Function.update f i g'))
    (hsmul : ∀ f : Fin n → Pt s E → ℝ, (∀ k, P (f k)) → ∀ (i : Fin n) (c : ℝ)
      (g : Pt s E → ℝ), P g → Ψ (Function.update f i (c • g)) = c * Ψ (Function.update f i g)) :
    IsTupleMultilinear (fun f : separatedTuples s E n => Ψ f.1) := by
  intro A hA
  have hmem : ∀ (i : Fin n) (g : c1Submodule (A i)), P (g : Pt s E → ℝ) :=
    fun i g => hP _ g.2.1 g.2.2.1
  have hcoe : ∀ (m : (i : Fin n) → c1Submodule (A i)) (i : Fin n)
      (x : c1Submodule (A i)),
      (fun j => ((Function.update m i x j : c1Submodule (A j)) : Pt s E → ℝ)) =
        Function.update (fun j => (m j : Pt s E → ℝ)) i (x : Pt s E → ℝ) := by
    intro m i x
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Function.update_of_ne h]
  refine ⟨{ toFun := fun g => Ψ fun i => (g i : Pt s E → ℝ)
            map_update_add' := ?_
            map_update_smul' := ?_ }, fun g => rfl⟩
  · intro inst m i x y
    obtain rfl : inst = fun a b => instDecidableEqFin n a b := Subsingleton.elim _ _
    simp only [hcoe]
    exact hadd _ (fun k => hmem k (m k)) i _ _ (hmem i x) (hmem i y)
  · intro inst m i c x
    obtain rfl : inst = fun a b => instDecidableEqFin n a b := Subsingleton.elim _ _
    simp only [hcoe]
    exact hsmul _ (fun k => hmem k (m k)) i c _ (hmem i x)
theorem centred_ofReal_eq_sum (S : AmbientPoints.ConnectedFamily s E)
    (C : (n : ℕ) → (Fin n → Pt s E → ℝ) → ℂ)
    (hS : ∀ (n : ℕ) (hn : 2 ≤ n) (f : separatedTuples s E n),
      ((S.fn n hn f : ℝ) : ℂ) = C n f.1)
    (X : allSeparatedTuples s E) :
    ((S.centred X : ℝ) : ℂ) =
      ∑ π ∈ SetPartition.singletonFree X.1.1, ∏ J ∈ π.parts,
        C J.card (restrictTuple X.1.2 J) := by
  unfold AmbientPoints.ConnectedFamily.centred
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun π hπ => ?_
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun J hJ => ?_
  have h2 := two_le_card_of_mem_singletonFree hπ hJ
  unfold AmbientPoints.ConnectedFamily.blockFactor
  rw [dif_pos h2]
  exact hS _ h2 _
end Multilinear
section Torus
variable (D : ConnectedFunctions.CouplingData)
theorem smearedObservable_ofReal {L m : ℕ} {j : ℤ} (g : PeriodicLattice.FourTorus L m → ℝ)
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    PeriodicLattice.smearedObservable (fun x => (g x : ℂ)) U =
      ((PeriodicLattice.smearedObservable g U : ℝ) : ℂ) := by
  unfold PeriodicLattice.smearedObservable
  have h := AddMonoidHom.map_finsum_of_injective Complex.ofRealHom.toAddMonoidHom
    Complex.ofReal_injective
    (fun p : PeriodicLattice.Plaquette L m j =>
      PeriodicLattice.plaquetteCost U p • g p.barycenter)
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Complex.ofRealHom_eq_coe] at h
  rw [h]
  refine finsum_congr fun p => ?_
  simp
theorem centredProductExpectation_ofReal {q : ℕ} (f : Fin q → D.Torus → ℝ) :
    ((TorusFunctionals.Periodic.centredProductExpectation D f : ℝ) : ℂ) =
      D.centredMomentFn (D.ofRealTuple f) := by
  have hexp : ∀ g : D.Torus → ℝ,
      D.expect (D.obs (D.ofRealFun g)) =
        ((PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
          (fun V => PeriodicLattice.smearedObservable g V) : ℝ) : ℂ) := by
    intro g
    unfold ConnectedFunctions.CouplingData.expect PeriodicLattice.gibbsExpectation
    rw [← integral_complex_ofReal]
    exact congrArg _ (funext fun U => smearedObservable_ofReal g U)
  unfold TorusFunctionals.Periodic.centredProductExpectation
    ConnectedFunctions.CouplingData.centredMomentFn
    ConnectedFunctions.CouplingData.expect PeriodicLattice.gibbsExpectation
  rw [← integral_complex_ofReal]
  refine congrArg _ (funext fun U => ?_)
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  unfold ConnectedFunctions.CouplingData.centred
  have h1 := hexp (f l)
  unfold TorusFunctionals.Periodic.centredObs
  rw [Complex.ofReal_sub]
  refine congrArg₂ (· - ·) (smearedObservable_ofReal (f l) U).symm ?_
  exact h1.symm
theorem connected_ofRealTuple {n : ℕ} (f : Fin n → D.Torus → ℝ) :
    D.connected (D.ofRealTuple f) = D.cumulantReal f := by apply _root_.YangMills.Construction.ConnectedFunctions.CouplingData.connected_ofReal <;> assumption
variable (hA : ConnectedFunctions.CentredIdentityAtAllFunctions)
include hA
theorem torusMomentPartitionExpansion (X : FunctionTuple D.toStandingParameters .torus) :
    TorusMomentPartitionExpansion D X := by
  unfold TorusMomentPartitionExpansion
  have h := (hA D).2.2.1 X.1 (D.ofRealTuple X.2) fun _ => Set.mem_univ _
  refine (centredProductExpectation_ofReal D X.2).trans (h.trans ?_)
  unfold ConnectedFunctions.CouplingData.centredFunctionalFn
  refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => ?_
  exact connected_ofRealTuple D (restrictTuple X.2 J)
theorem cumulantReal_im (n : ℕ) (hn : 2 ≤ n) (f : Fin n → D.Torus → ℝ) :
    (D.cumulantReal f).im = 0 := by
  have h := ((hA D).2.1 n hn).1.1.1 f fun _ => Set.mem_univ _
  rwa [connected_ofRealTuple] at h
theorem cumulantReal_update_add (n : ℕ) (hn : 2 ≤ n) (f : Fin n → D.Torus → ℝ) (i : Fin n)
    (g g' : D.Torus → ℝ) :
    D.cumulantReal (Function.update f i (g + g')) =
      D.cumulantReal (Function.update f i g) +
        D.cumulantReal (Function.update f i g') := by
  have h := ((hA D).2.1 n hn).1.1.2.2.1 f (fun _ => Set.mem_univ _) i g g'
    (Set.mem_univ _) (Set.mem_univ _)
  rwa [connected_ofRealTuple, connected_ofRealTuple, connected_ofRealTuple] at h
theorem cumulantReal_update_smul (n : ℕ) (hn : 2 ≤ n) (f : Fin n → D.Torus → ℝ) (i : Fin n)
    (c : ℝ) (g : D.Torus → ℝ) :
    D.cumulantReal (Function.update f i (c • g)) =
      (c : ℂ) * D.cumulantReal (Function.update f i g) := by
  have h := ((hA D).2.1 n hn).1.1.2.2.2 f (fun _ => Set.mem_univ _) i g c (Set.mem_univ _)
  rwa [connected_ofRealTuple, connected_ofRealTuple] at h
omit hA in
def torusCumulantFamily (hA : ConnectedFunctions.CentredIdentityAtAllFunctions) :
    AmbientPoints.ConnectedFamily D.toStandingParameters .torus where
  fn _ _ f := (D.cumulantReal f.1).re
  fn_multilinear n hn :=
    isTupleMultilinear_of_additive_smul (s := D.toStandingParameters) (E := .torus)
      (fun _ => True) (fun _ _ _ => trivial) (fun f => (D.cumulantReal f).re)
      (fun f _ i g g' _ _ =>
        (congrArg Complex.re (cumulantReal_update_add D hA n hn f i g g')).trans
          (Complex.add_re _ _))
      (fun f _ i c g _ =>
        (congrArg Complex.re (cumulantReal_update_smul D hA n hn f i c g)).trans
          (Complex.re_ofReal_mul _ _))
theorem isTorusCumulantFamily_torusCumulantFamily :
    IsTorusCumulantFamily D (torusCumulantFamily D hA) := by
  intro n hn f
  exact Complex.ext rfl (by simpa using (cumulantReal_im D hA n hn f.1).symm)
theorem torusMomentFacts : TorusMomentFacts D := by
  refine ⟨fun X _ _ => torusMomentPartitionExpansion D hA X, torusCumulantFamily D hA,
    isTorusCumulantFamily_torusCumulantFamily D hA, fun X => ?_⟩
  have h1 := torusMomentPartitionExpansion D hA X.1
  have h2 := centred_ofReal_eq_sum (torusCumulantFamily D hA)
    (fun n f => D.cumulantReal f) (isTorusCumulantFamily_torusCumulantFamily D hA) X
  exact Complex.ofReal_injective (h1.trans h2.symm)
end Torus
theorem centredProduct_tupleAppend {s : Conventions.StandingParameters} {a : ℝ}
    (ν : InfiniteLattice.GaugeFieldProbability a) (X Y : FunctionTuple s .euclidean)
    (U : InfiniteLattice.GaugeField a) :
    CentredRepresentative.centredProduct ν (tupleAppend X Y) U =
      CentredRepresentative.centredProduct ν X U *
        CentredRepresentative.centredProduct ν Y U := by
  unfold CentredRepresentative.centredProduct
  change ∏ i : Fin (X.1 + Y.1), _ = _
  rw [Fin.prod_univ_add]
  simp only [tupleAppend, Fin.append_left, Fin.append_right]
section Hyperplanes
variable (hK : ReflectionPositivity.AxisMirror.LevelContents)
  (hO : ReflectionPositivity.AxisMirror.MirrorLevelKinds.Statement)
include hK in
theorem torusHyperplaneAvoidsSites_of_mem (s : Conventions.StandingParameters) (μ : Fin 4) (c : ℝ)
    (hc : c ∈ ReflectionPositivity.AxisMirror.linkLevels
      (PeriodicLattice.meshSize s.L (s.K : ℕ))) :
    TorusHyperplaneAvoidsSites s μ c := by
  intro x
  exact ((hK ⟨s, 1, one_pos⟩ .torus μ c).2 hc).1 x
include hK hO in
theorem torusHyperplaneAvoidsSites_pair (s : Conventions.StandingParameters) (μ : Fin 4) (c : ℝ)
    (hc : c ∈ ReflectionPositivity.AxisMirror.linkLevels
      (PeriodicLattice.meshSize s.L (s.K : ℕ))) :
    TorusHyperplaneAvoidsSites s μ c ∧
      TorusHyperplaneAvoidsSites s μ (c + s.side / 2) :=
  ⟨torusHyperplaneAvoidsSites_of_mem hK s μ c hc, torusHyperplaneAvoidsSites_of_mem hK s μ _
    (((hO ⟨s, 1, one_pos⟩).2.1 c).2.1 hc)⟩
end Hyperplanes
section Entries
variable {s : Conventions.StandingParameters}
theorem mem_compactTestFunctions_of_continuous {f : (Fin 4 → ℝ) → ℝ} (hc : Continuous f)
    (hcs : HasCompactSupport f) : f ∈ InfiniteLattice.compactTestFunctions :=
  ⟨hc.measurable, hc.bounded_above_of_compact_support hcs, hcs⟩
theorem mem_compactTestFunctions_of_isC1Fn {f : Pt s .euclidean → ℝ} (h : IsC1Fn f)
    (hK : IsCompact (tsupport f)) : f ∈ InfiniteLattice.compactTestFunctions :=
  mem_compactTestFunctions_of_continuous (f := f)
    (ContDiff.continuous ((isC1Fn_euclidean_iff f).1 h))
    ((R4TupleForms.isCompact_tsupport_pt_iff_hasCompactSupport (s := s) f).1 hK)
theorem euclidNormVec_le_two_mul_pi_norm (z : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec z ≤ 2 * ‖z‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
theorem continuous_of_lipschitz_euclidNormVec {f : (Fin 4 → ℝ) → ℝ}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * TorusMetric.euclidNormVec (x - y)) :
    Continuous f := by
  obtain ⟨C, hC, hf⟩ := h
  refine (LipschitzWith.of_dist_le_mul (K := (C * 2).toNNReal) fun x y => ?_).continuous
  rw [Real.dist_eq, ← Real.norm_eq_abs, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  calc ‖f x - f y‖ ≤ C * TorusMetric.euclidNormVec (x - y) := hf x y
    _ ≤ C * (2 * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (euclidNormVec_le_two_mul_pi_norm _) hC
    _ = _ := by ring
theorem entry_mem_compactTestFunctions {X : FunctionTuple s .euclidean}
    (hX : X ∈ separatedTuplesSmoothOrLip s .euclidean) (i : Fin X.1) :
    X.2 i ∈ InfiniteLattice.compactTestFunctions := by
  rcases hX with hX | hX
  · exact mem_compactTestFunctions_of_isC1Fn (hX.1 i).1 (hX.1 i).2
  · exact mem_compactTestFunctions_of_continuous (f := X.2 i)
      (continuous_of_lipschitz_euclidNormVec (hX.1 i).1)
      ((R4TupleForms.isCompact_tsupport_pt_iff_hasCompactSupport (s := s) (X.2 i)).1 (hX.1 i).2)
theorem prod_orderEmbOfFin_eq_prod {q : ℕ} (J : Finset (Fin q)) (F : Fin q → ℝ) :
    ∏ i : Fin J.card, F (J.orderEmbOfFin rfl i) = ∏ l ∈ J, F l := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.LimitPassage.prod_comp_orderEmbOfFin <;> assumption
end Entries
section InAState
variable {s : Conventions.StandingParameters} (ν : LatticeState s)
theorem centredMoment_ofReal (X : FunctionTuple s .euclidean) :
    ((CentredRepresentative.centredMoment ν X : ℝ) : ℂ) =
      InfiniteLattice.centeredMoment ν.1 X.2 := by
  unfold CentredRepresentative.centredMoment
    CentredRepresentative.pairedCentredProduct
    CentredRepresentative.centredProduct InfiniteLattice.centeredMoment
    Probability.complexExpectation
  rw [← integral_complex_ofReal]
  refine congrArg _ (funext fun U => ?_)
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Complex.ofReal_sub, integral_complex_ofReal]
variable (hS : InfiniteLattice.CenteredIdentity.Statement)
include hS in
theorem stateMomentPartitionExpansion {X : FunctionTuple s .euclidean}
    (hX : ∀ i, X.2 i ∈ InfiniteLattice.compactTestFunctions) :
    StateMomentPartitionExpansion ν X := by
  refine (centredMoment_ofReal ν X).trans (((hS s ν.1 ν.2).2.2 X.1 X.2 hX).trans ?_)
  unfold InfiniteLattice.ursellPartitionSum
  have hset : SetPartition.nonSingletonPartitions X.1 = SetPartition.singletonFree X.1 := by
    rw [SetPartition.singletonFree_eq_nonSingletonPartitions]
  rw [hset]
  rfl
include hS in
theorem stateCumulantMobiusExpansion (hC : Cumulants.CumulantMomentRelations)
    {X : FunctionTuple s .euclidean}
    (hX : ∀ i, X.2 i ∈ InfiniteLattice.compactTestFunctions) (h2 : 2 ≤ X.1) :
    StateCumulantMobiusExpansion ν X := by
  have hp : IsProbabilityMeasure ν.1 := ν.2
  obtain ⟨x, hxdef⟩ : ∃ x : Fin X.1 → InfiniteLattice.GaugeField _ → ℝ,
      x = fun i U => InfiniteLattice.smearedEnergy (X.2 i) U := ⟨_, rfl⟩
  have hx : ∀ i, Probability.IsBoundedRealRV (x i) := fun i => by
    rw [hxdef]
    exact ((hS s ν.1 ν.2).1.1 _ (hX i)).2
  obtain ⟨c, hcdef⟩ : ∃ c : Fin X.1 → ℝ, c = fun i => -∫ V, x i V ∂ν.1 := ⟨_, rfl⟩
  have hy : ∀ i, Probability.IsBoundedRealRV (Cumulants.shiftTuple x c i) := by
    intro i
    obtain ⟨C, hC'⟩ := (hx i).bounded
    refine ⟨(hx i).measurable.add_const _, C + |c i|, fun ω => ?_⟩
    exact (abs_add_le _ _).trans (add_le_add_left (hC' ω) _)
  have hall := hC _ ν.1 X.1 _ hy
  have hshift := hall.2.2.2.1 X.1 x c h2 hx
  have hcum := hall.2.2.2.2.2.2 (by omega)
  unfold StateCumulantMobiusExpansion InfiniteLattice.ursellFunction
  rw [← hxdef]
  refine hshift.symm.trans (hcum.trans (Finset.sum_congr rfl fun π _ => ?_))
  refine congrArg _ (Finset.prod_congr rfl fun J hJ => ?_)
  have hne : J ≠ ∅ := (π.nonempty_of_mem_parts hJ).ne_empty
  unfold Cumulants.finsetMoment
  rw [if_neg hne]
  unfold Probability.complexExpectation CentredRepresentative.centredMoment
    CentredRepresentative.pairedCentredProduct
    CentredRepresentative.centredProduct
  rw [integral_complex_ofReal]
  refine congrArg _ (congrArg _ (funext fun U => ?_))
  rw [← prod_orderEmbOfFin_eq_prod J]
  refine Finset.prod_congr rfl fun i _ => ?_
  subst hxdef hcdef
  exact (sub_eq_add_neg _ _).symm
include hS in
theorem ursellFunction_im (n : ℕ) (hn : 2 ≤ n) (f : Fin n → InfiniteLattice.AmbientSpace → ℝ)
    (hf : ∀ k, f k ∈ InfiniteLattice.compactTestFunctions) :
    (InfiniteLattice.ursellFunction ν.1 n f).im = 0 :=
  ((hS s ν.1 ν.2).2.1 n hn f hf).1
theorem update_mem_compactTestFunctions {n : ℕ} {f : Fin n → InfiniteLattice.AmbientSpace → ℝ}
    (hf : ∀ k, f k ∈ InfiniteLattice.compactTestFunctions) (i : Fin n)
    {g : InfiniteLattice.AmbientSpace → ℝ} (hg : g ∈ InfiniteLattice.compactTestFunctions)
    (k : Fin n) :
    Function.update f i g k ∈ InfiniteLattice.compactTestFunctions := by
  by_cases h : k = i
  · subst h
    simpa using hg
  · simpa [Function.update_of_ne h] using hf k
include hS in
theorem ursellFunction_update_add (n : ℕ) (hn : 2 ≤ n)
    (f : Fin n → InfiniteLattice.AmbientSpace → ℝ)
    (hf : ∀ k, f k ∈ InfiniteLattice.compactTestFunctions) (i : Fin n)
    (g g' : InfiniteLattice.AmbientSpace → ℝ) (hg : g ∈ InfiniteLattice.compactTestFunctions)
    (hg' : g' ∈ InfiniteLattice.compactTestFunctions) :
    InfiniteLattice.ursellFunction ν.1 n (Function.update f i (g + g')) =
      InfiniteLattice.ursellFunction ν.1 n (Function.update f i g) +
        InfiniteLattice.ursellFunction ν.1 n (Function.update f i g') := by
  have h := ((hS s ν.1 ν.2).2.1 n hn (Function.update f i g)
    (update_mem_compactTestFunctions hf i hg)).2.2.1 i g' hg'
  simpa only [Function.update_self, Function.update_idem] using h
include hS in
theorem ursellFunction_update_smul (n : ℕ) (hn : 2 ≤ n)
    (f : Fin n → InfiniteLattice.AmbientSpace → ℝ)
    (hf : ∀ k, f k ∈ InfiniteLattice.compactTestFunctions) (i : Fin n) (c : ℝ)
    (g : InfiniteLattice.AmbientSpace → ℝ) (hg : g ∈ InfiniteLattice.compactTestFunctions) :
    InfiniteLattice.ursellFunction ν.1 n (Function.update f i (c • g)) =
      (c : ℂ) * InfiniteLattice.ursellFunction ν.1 n (Function.update f i g) := by
  have h := ((hS s ν.1 ν.2).2.1 n hn (Function.update f i g)
    (update_mem_compactTestFunctions hf i hg)).2.2.2 i c
  simpa only [Function.update_self, Function.update_idem] using h
def stateCumulantFamily (hS : InfiniteLattice.CenteredIdentity.Statement) :
    AmbientPoints.ConnectedFamily s .euclidean where
  fn n _ f := (InfiniteLattice.ursellFunction ν.1 n f.1).re
  fn_multilinear n hn :=
    isTupleMultilinear_of_additive_smul (s := s) (E := .euclidean)
      (fun g => g ∈ InfiniteLattice.compactTestFunctions)
      (fun _ h1 h2 => mem_compactTestFunctions_of_isC1Fn h1 h2)
      (fun f => (InfiniteLattice.ursellFunction ν.1 n f).re)
      (fun f hf i g g' hg hg' =>
        (congrArg Complex.re (ursellFunction_update_add ν hS n hn f hf i g g' hg hg')).trans
          (Complex.add_re _ _))
      (fun f hf i c g hg =>
        (congrArg Complex.re (ursellFunction_update_smul ν hS n hn f hf i c g hg)).trans
          (Complex.re_ofReal_mul _ _))
theorem separated_component_mem_compactTestFunctions {n : ℕ} (f : separatedTuples s .euclidean n)
    (i : Fin n) : f.1 i ∈ InfiniteLattice.compactTestFunctions :=
  mem_compactTestFunctions_of_isC1Fn (f.2.1 i).1 (f.2.1 i).2
include hS in
theorem isStateCumulantFamily_stateCumulantFamily :
    IsStateCumulantFamily ν (stateCumulantFamily ν hS) := by
  intro n hn f
  exact Complex.ext rfl
    (by simpa using
      (ursellFunction_im ν hS n hn f.1 (separated_component_mem_compactTestFunctions f)).symm)
include hS in
theorem separatedCentredMoment_eq_centred (X : allSeparatedTuples s .euclidean) :
    separatedCentredMoment ν X = (stateCumulantFamily ν hS).centred X := by
  have h1 := stateMomentPartitionExpansion ν hS (X := X.1)
    (entry_mem_compactTestFunctions (Or.inl X.2))
  have h2 := centred_ofReal_eq_sum (stateCumulantFamily ν hS)
    (fun n f => InfiniteLattice.ursellFunction ν.1 n f)
    (isStateCumulantFamily_stateCumulantFamily ν hS) X
  exact Complex.ofReal_injective (h1.trans h2.symm)
include hS in
theorem stateMomentFacts (hC : Cumulants.CumulantMomentRelations)
    (hF : CentredOfConnectedFamilyProperties) : StateMomentFacts ν := by
  have hσ : separatedCentredMoment ν = (stateCumulantFamily ν hS).centred :=
    funext (separatedCentredMoment_eq_centred ν hS)
  have hall := hF s .euclidean (stateCumulantFamily ν hS)
  refine ⟨fun X hX _ => stateMomentPartitionExpansion ν hS (entry_mem_compactTestFunctions hX),
    ?_,
    fun X hX h2 => stateCumulantMobiusExpansion ν hS hC (entry_mem_compactTestFunctions hX) h2,
    ⟨stateCumulantFamily ν hS, isStateCumulantFamily_stateCumulantFamily ν hS,
      separatedCentredMoment_eq_centred ν hS⟩, ?_, ?_⟩
  · intro X hX h1
    have h := stateMomentPartitionExpansion ν hS (entry_mem_compactTestFunctions hX)
    refine Complex.ofReal_eq_zero.1 (h.trans (Finset.sum_eq_zero fun π hπ => ?_))
    exfalso
    obtain ⟨J, hJ, -⟩ := π.exists_mem (a := ⟨0, by omega⟩) (by simp)
    have h2 := two_le_card_of_mem_singletonFree hπ hJ
    have h3 : J.card ≤ X.1 := by simpa using Finset.card_le_univ J
    omega
  · rw [hσ]
    exact hall.2.2.2.1
  · intro n hn f
    rw [hσ, hall.2.2.2.2.2.2.1 n hn f]
    exact isStateCumulantFamily_stateCumulantFamily ν hS n hn f
end InAState
section Classes
variable {s : Conventions.StandingParameters}
theorem exists_pos_lower_bound_le_one {ι : Type*} [Fintype ι] (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ i, d ≤ δ i := by
  classical
  have key : ∀ t : Finset ι, ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ i ∈ t, d ≤ δ i := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, one_pos, le_rfl, by simp⟩
    | insert a t _ ih =>
      obtain ⟨d, h0, h1, h⟩ := ih
      refine ⟨min d (δ a), lt_min h0 (hδ a), (min_le_left _ _).trans h1, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h i hi)
  obtain ⟨d, h0, h1, h⟩ := key Finset.univ
  exact ⟨d, h0, h1, fun i => h i (Finset.mem_univ i)⟩
theorem exists_pos_le_pointDist {A B : Set (Pt s .euclidean)} (hA : IsCompact A)
    (hB : IsCompact B) (hAB : Disjoint A B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ A, ∀ b ∈ B, δ ≤ pointDist s .euclidean a b := by
  obtain ⟨δ, hδ, hdis⟩ := hAB.exists_thickenings hA hB.isClosed
  refine ⟨δ, hδ, fun a ha b hb => ?_⟩
  by_contra hlt
  have hab : dist a b < δ := not_le.1 hlt
  have h1 : b ∈ Metric.thickening δ A :=
    Metric.mem_thickening_iff.2 ⟨a, ha, by rwa [dist_comm]⟩
  exact Set.disjoint_left.1 hdis h1 (Metric.self_subset_thickening hδ B hb)
theorem pi_norm_le_euclidNormVec (z : Fin 4 → ℝ) : ‖z‖ ≤ TorusMetric.euclidNormVec z := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem natCast_mem_adicRationalsPositive {L : ℕ} (hL : L ≠ 0) (N : ℕ) :
    (N : ℝ) ∈ PeriodicLattice.adicRationalsPositive L := by
  refine (PeriodicLattice.mem_adicGridPointsPositive_iff L _).2 ⟨1, (N : ℤ) * L, ?_⟩
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  simp only [PeriodicLattice.meshSize, PNat.one_coe, Nat.cast_one, Int.cast_mul,
    Int.cast_natCast, zpow_neg, zpow_one]
  field_simp
theorem exists_mem_classOf (X : FunctionTuple s .euclidean)
    (hX : X ∈ allSeparatedTuples s .euclidean) :
    ∃ ϖ ∈ PeriodicLattice.adicRationalsPositive s.L, ∃ d R : ℝ,
      0 < d ∧ d ≤ ϖ ∧ 0 < R ∧ X ∈ SeparatedClasses.classOf s ϖ d R := by
  have hK : IsCompact (⋃ i, tsupport (X.2 i)) := isCompact_iUnion fun i => (hX.1 i).2
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall ((0 : Fin 4 → ℝ) : Pt s .euclidean)
  have hρ : ∀ i, ∀ x ∈ tsupport (X.2 i), pointDist s .euclidean x (0 : Fin 4 → ℝ) ≤ max r 1 :=
    fun i x hx =>
      (Metric.mem_closedBall.1 (hr (Set.mem_iUnion.2 ⟨i, hx⟩))).trans (le_max_left _ _)
  have hdelta : ∀ p : Fin X.1 × Fin X.1, ∃ δ : ℝ, 0 < δ ∧ (p.1 ≠ p.2 →
      ∀ a ∈ tsupport (X.2 p.1), ∀ b ∈ tsupport (X.2 p.2), δ ≤ pointDist s .euclidean a b) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun h => absurd hp h⟩
    · obtain ⟨δ, h0, h⟩ := exists_pos_le_pointDist (hX.1 p.1).2 (hX.1 p.2).2 (hX.2 hp)
      exact ⟨δ, h0, fun _ => h⟩
  choose δ hδ0 hδ using hdelta
  obtain ⟨d, hd0, hd1, hd⟩ := exists_pos_lower_bound_le_one δ hδ0
  obtain ⟨N, hN⟩ := exists_nat_ge (max r 1 + 1)
  have hρ1 : (1 : ℝ) ≤ max r 1 := le_max_right _ _
  refine ⟨N, natCast_mem_adicRationalsPositive (by have := s.isAdmissible.2; omega) N, d,
    max r 1, hd0, by linarith, by linarith, hX, fun i => ?_, fun i => ?_, fun i k hik => ?_⟩
  · refine ⟨_, ⟨by linarith, (0 : Fin 4 → ℝ), rfl⟩, fun x hx => hρ i x hx⟩
  · intro x hx
    have key : ∀ y : Fin 4 → ℝ, TorusMetric.euclidNormVec (y - 0) ≤ max r 1 →
        y ∈ ReflectionPositivity.centredCube ((N : ℝ) - d / 2) := fun y hy => by
      rw [ReflectionPositivity.centredCube_eq_ball, mem_ball_zero_iff]
      rw [sub_zero] at hy
      have h2 := pi_norm_le_euclidNormVec y
      linarith
    exact key x (hρ i x hx)
  · unfold setDist
    refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal ?_
    exact (hd (i, k)).trans (hδ (i, k) hik a ha b hb)
end Classes
section Family
variable (s : Conventions.StandingParameters)
theorem isOpen_pt_iff (Z : Set (Fin 4 → ℝ)) :
    @IsOpen (Pt s .euclidean) _ Z ↔ IsOpen Z := by
  have hcl : ∀ W : Set (Fin 4 → ℝ), @IsClosed (Pt s .euclidean) _ W ↔ IsClosed W := fun W => by
    have h := R4TupleForms.closure_pt_euclidean (s := s) W
    exact ⟨fun hW => closure_eq_iff_isClosed.1
        (h.symm.trans ((@closure_eq_iff_isClosed (Pt s .euclidean) _ W).2 hW)),
      fun hW => (@closure_eq_iff_isClosed (Pt s .euclidean) _ W).1
        (h.trans (closure_eq_iff_isClosed.2 hW))⟩
  exact (@isClosed_compl_iff (Pt s .euclidean) _ Z).symm.trans
    ((hcl Zᶜ).trans isClosed_compl_iff)
abbrev unitCouplingData : ReflectionPositivity.AxisMirror.MirrorData := ⟨s, 1, one_pos⟩
variable {s}
theorem closedSupport_eq_tsupport (f : Pt s .euclidean → ℝ) :
    (Ambient.closedSupport (unitCouplingData s) .euclidean f : Set (Fin 4 → ℝ)) =
      @tsupport (Pt s .euclidean) ℝ _ _ f :=
  (R4TupleForms.closedSupport_euclidean_eq (unitCouplingData s) f).trans
    (R4TupleForms.tsupport_pt_euclidean (s := s) f).symm
theorem separatingTuplesFacts (hF : SeparatingFamily.SeparatingTuplesFacts) (M : ℕ)
    (hM : LatticeLimits.IsBlockScale s M) : SeparatingTuplesFacts s M := by
  obtain ⟨-, -, -, ⟨hcount, hmotion, hconcat⟩, happ⟩ := hF (unitCouplingData s)
  refine ⟨hcount, fun X hX w => ?_, fun X hX v hv => ?_, fun X Y hX hY hd => ?_,
    fun X hX hk O hO hsub => ?_⟩
  · have h := hmotion ⟨w.1.toEquiv, w.1, w.2, 0, SeparatingFamily.zero_mem_adicLatticeVectors _,
      fun x => by simp⟩ _ hX
    refine (congrArg (fun l => l ∈ SeparatingFamily.separatingTuples s.L) ?_).mpr h
    refine Eq.trans ?_ List.map_ofFn.symm
    rfl
  · have h := hmotion ⟨Equiv.addRight v, 1, one_mem _, v, hv, fun x => by simp⟩ _ hX
    refine (congrArg (fun l => l ∈ SeparatingFamily.separatingTuples s.L) ?_).mpr h
    refine Eq.trans ?_ List.map_ofFn.symm
    refine congrArg List.ofFn (funext fun i => ?_)
    exact translateFn_eq_transportFn v (X.2 i)
  · have hlist : List.ofFn (tupleAppend X Y).2 =
        Ambient.append (D := unitCouplingData s) (E := .euclidean)
          (List.ofFn X.2) (List.ofFn Y.2) :=
      List.ofFn_fin_append X.2 Y.2
    have hp : List.Pairwise (fun f g =>
        Disjoint (Ambient.closedSupport (unitCouplingData s) .euclidean f)
          (Ambient.closedSupport (unitCouplingData s) .euclidean g))
        (List.ofFn (tupleAppend X Y).2) := by
      refine List.pairwise_ofFn.2 fun i j hij => ?_
      have h : Disjoint (tsupport ((tupleAppend X Y).2 i)) (tsupport ((tupleAppend X Y).2 j)) :=
        hd hij.ne
      rwa [← closedSupport_eq_tsupport, ← closedSupport_eq_tsupport] at h
    refine (congrArg (fun l => l ∈ SeparatingFamily.separatingTuples s.L) hlist).mpr
      (hconcat _ hX _ hY ?_)
    exact (congrArg (List.Pairwise _) hlist).mp hp
  · have hsep : List.ofFn X.2 ∈ Ambient.separatedN (unitCouplingData s) .euclidean X.1 := by
      have h1 := (R4TupleForms.isDisjointlySupported_iff_mem_separatedAll (unitCouplingData s) _).1
        ((R4TupleForms.mem_separatedTuples_iff_ofFn (s := s) X.2).1 hX)
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h1
      exact ⟨List.length_ofFn, hn.2⟩
    obtain ⟨φ, h1, h2, h3⟩ := happ (M : ℝ) (by exact_mod_cast hM.one_le) X.1 hk X.2 hsep O
      (fun i => (isOpen_pt_iff s _).1 (hO i))
      (fun i => (closedSupport_eq_tsupport (X.2 i)).trans_subset (hsub i))
    exact ⟨φ, hO, hsub, h1,
      fun l i => (closedSupport_eq_tsupport (φ l i)).symm.trans_subset (h2 l i), h3⟩
end Family
theorem settingFacts_of
    (hA : ConnectedFunctions.CentredIdentityAtAllFunctions)
    (hS : InfiniteLattice.CenteredIdentity.Statement)
    (hC : Cumulants.CumulantMomentRelations)
    (hFam : CentredOfConnectedFamilyProperties)
    (hK : ReflectionPositivity.AxisMirror.LevelContents)
    (hO : ReflectionPositivity.AxisMirror.MirrorLevelKinds.Statement)
    (hF : SeparatingFamily.SeparatingTuplesFacts) : SettingFacts :=
  ⟨fun D => torusMomentFacts D hA, fun _ ν => stateMomentFacts ν hS hC hFam,
    fun s μ c hc => torusHyperplaneAvoidsSites_pair hK hO s μ c hc,
    fun _ ν X _ Y _ _ U => centredProduct_tupleAppend ν X Y U,
    fun _ X hX => exists_mem_classOf X hX,
    fun _ M hM => separatingTuplesFacts hF M hM⟩
end ContinuumSetting
end YangMills.Construction
