import Formulation.WilsonDefinitions
import YangMills.Construction.Continuum.TermsBoundValuesOnTuplesAndApproximationForTheFormOnAdmissibleSequencesProof
import YangMills.Construction.Continuum.LinearCombinationsAndTensorsLieInTheFlatSpacesProof
import YangMills.Construction.Continuum.TheThreeOpenSetsAndTheThreeSpacesProof
import YangMills.Construction.Continuum.SupremaOfASmoothFunctionAndTheVectorSpaceOfSchwartzFunctionsProof
import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuplesProof
import YangMills.Construction.Continuum.FunctionsVanishingOnAnOpenSetProof
import YangMills.Construction.Continuum.OperationsKeepTheSpacesProof
import YangMills.Construction.Continuum.OperationsOnTestFunctionsProof
import YangMills.Construction.Continuum.FirstFactsOnTheTestSpacesProof
import YangMills.Construction.SystemsWithFiveBounds.TheoremOverASystemWithFiveBounds

noncomputable section
open scoped ContDiff ENNReal ComplexConjugate
namespace YangMills.WilsonOS
open Construction
open ConfigSpace (FlatSequence)

private theorem flatSpaceClosure : ConfigSpace.FlatSpaceClosure :=
  ConfigSpace.flatSpaceClosure_of_openLoci_of_compactSupport
    (ConfigSpace.openLociAndFlatSubspaces_of_schwartzSuprema ConfigSpace.schwartzSupremaStatement_holds)
    (ConfigSpace.TensorSupport.compactSupportTensorFacts_of_vanishing ConfigSpace.vanishingOnOpenProperties_holds)

private theorem seminorm_eq {n : ℕ} (k : ℕ) (f : Test n) :
    seminorm k f = ConfigSpace.schwartzSeminorm k f := by
  unfold seminorm ConfigSpace.schwartzSeminorm ConfigSpace.euclidNorm
  congr 1
  funext x
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rfl

private theorem flatOutside_iff {n : ℕ} {U : Set (Config n)} (hU : IsOpen U) {f : Test n} :
    FlatOutside U f ↔ ConfigSpace.IsSchwartz f ∧ ConfigSpace.FlatOff f U := by
  simp only [FlatOutside, seminorm_eq, ConfigSpace.IsSchwartz, ConfigSpace.FlatOff, ConfigSpace.FlatAt]
  exact ⟨fun ⟨hs, hdec, h⟩ => ⟨⟨hs, hdec⟩, hs, hU, fun x hx => ⟨hs, h x hx⟩⟩,
    fun ⟨⟨hs, hdec⟩, _, _, h⟩ => ⟨hs, hdec, fun x hx => (h x hx).2⟩⟩

private theorem flat_iff {n : ℕ} {f : Test n} :
    Flat f ↔ f ∈ ConfigSpace.schwartzFlatOffDiagonal n :=
  flatOutside_iff ConfigSpace.isOpen_distinctArgs

/-- Evaluation of a project distribution on its flat Schwartz domain. -/
def ofFlatSequence (T : FlatSequence) : Family :=
  fun _ f => T.evalAt (ConfigSpace.ofConfigFn f)

private theorem at_flat (T : FlatSequence) {n : ℕ} {f : Test (n+1)}
    (h : f ∈ ConfigSpace.schwartzFlatOffDiagonal (n+1)) :
    ofFlatSequence T (n+1) f = T.atSucc n ⟨f,h⟩ :=
  T.evalAt_of_mem (n:=n+1) h

private theorem at_zero (T : FlatSequence) (hT : ∀ c : ConfigSpace.flatOffDiagonalAt 0, T 0 c = c.1)
    (f : Test 0) : ofFlatSequence T 0 f = f Fin.elim0 :=
  (T.evalAt_of_mem (n:=0) (f:=ConfigSpace.ofConfigFn f) (Set.mem_univ _)).trans (hT _)

private theorem reflectedProduct_eval (T : FlatSequence) {p q : ℕ} (f : Test p) (g : Test q) :
    T.evalAt (ConfigSpace.tensorAt (ConfigSpace.flipConjAt (ConfigSpace.ofConfigFn f)) (ConfigSpace.ofConfigFn g)) =
      ofFlatSequence T (p+q) (reflectedProduct f g) := by
  have eq {n : ℕ} (u : Test n) : ConfigSpace.toConfigFn (ConfigSpace.ofConfigFn u) = u := by
    cases n with
    | zero => funext x; exact congrArg u (Subsingleton.elim _ _)
    | succ n => rfl
  rw [AdmissibleForm.tensorAt_flipConjAt_eq, eq, eq]
  rfl

private def posSeq (Φ : Sequence) (h : Admissible Φ) : ConfigSpace.PosTimeSeq := fun n =>
  ⟨ConfigSpace.ofConfigFn (Φ n), by
    cases n with
    | zero => exact Set.mem_univ _
    | succ m => exact (flatOutside_iff ConfigSpace.isOpen_posTimeSet).mp (h.1 m)⟩

private theorem posSeq_finite (Φ : Sequence) (h : Admissible Φ) :
    ConfigSpace.PosTimeSeq.IsFinitelySupported (posSeq Φ h) := h.2.subset (by
  intro n hn hzero
  apply hn
  change ConfigSpace.ofConfigFn (Φ n) = ConfigSpace.zeroOfDegree n
  rw [hzero]
  cases n <;> rfl)

private theorem pairing_eq (T : FlatSequence) (Φ Ψ : Sequence) :
    T.reflectionPairing (fun n => ConfigSpace.ofConfigFn (Φ n)) (fun n => ConfigSpace.ofConfigFn (Ψ n)) =
      pairing (ofFlatSequence T) Φ Ψ :=
  finsum_congr fun _ => reflectedProduct_eval T _ _

theorem axioms_of_schwinger {σ : SeparatedTuples.TupleFunctional} {T : FlatSequence}
    {D : SystemsWithFiveBounds.LimitConstants} (hD : D.Valid)
    (hT : SystemsWithFiveBounds.HasSchwingerSequence σ T)
    (hg : SystemsWithFiveBounds.SatisfiesGrowth T D.schwartzOrder D.schwartzPrefactor D.schwartzBase D.schwartzExp)
    (heu : ConfigSpace.IsEuclidInvariant T) (hos : ConfigSpace.IsOSPositive T)
    (hperm : ConfigSpace.IsPermSymmetric T) (hr : ConfigSpace.IsReflectionReal T) :
    EuclideanAxioms (ofFlatSequence T) := by
  classical
  have lin : ConfigSpace.IsLinearFunctionalSeq T := ⟨hT.2.1, fun n => (hT.2.2 n).1.1⟩
  have ops := ConfigSpace.operationsPreserveSchwartzSpaces_of_suprema ConfigSpace.schwartzSupremaStatement_holds
  refine ⟨at_zero T hT.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n f g a b hf hg
    let F : ConfigSpace.schwartzFlatOffDiagonal (n+1) := ⟨f, flat_iff.mp hf⟩
    let G : ConfigSpace.schwartzFlatOffDiagonal (n+1) := ⟨g, flat_iff.mp hg⟩
    obtain ⟨X, hX⟩ := (flatSpaceClosure (n+1) (Nat.succ_pos n)).1 a b F G
    have hb : a • f + b • g ∈ ConfigSpace.schwartzFlatOffDiagonal (n+1) := hX ▸ X.2
    rw [at_flat T hb, at_flat T F.2, at_flat T G.2]
    exact lin.2 n a b F G _ rfl
  · refine ⟨_, _, _, _, hD.schwartzOrder_pos, hD.schwartzPrefactor_pos, hD.schwartzBase_pos, hD.schwartzExp_pos, ?_⟩
    intro n f hf
    rw [at_flat T (flat_iff.mp hf), seminorm_eq]
    exact hg n ⟨f, flat_iff.mp hf⟩
  · intro n f hf R hR v
    let F : ConfigSpace.schwartzFlatOffDiagonal (n+1) := ⟨f, flat_iff.mp hf⟩
    let r : ConfigSpace.EuclidMotion := ⟨fun u => R.mulVec u + v, R, hR, v, fun _ => rfl⟩
    have e : ConfigSpace.motionAct r f = fun x => f fun i => R⁻¹.mulVec (x i-v) := by
      funext x
      exact congrArg f (funext fun i => ConfigSpace.EuclidMotion.invMap_eq r hR (v:=v) (fun _ => rfl) _)
    rw [← e, at_flat T (((ops _ (Nat.succ_pos n)).1 F.1 F.2 r 1).1), at_flat T F.2]
    exact heu n F r _
  · intro n f hf π
    let F : ConfigSpace.schwartzFlatOffDiagonal (n+1) := ⟨f, flat_iff.mp hf⟩
    change ofFlatSequence T (n+1) (ConfigSpace.permAct π F.1) = ofFlatSequence T (n+1) F.1
    rw [at_flat T (((ops _ (Nat.succ_pos n)).1 F.1 F.2 ConfigSpace.timeFlipMotion π).2), at_flat T F.2]
    exact hperm n F π _
  · intro n f hf
    let F : ConfigSpace.schwartzFlatOffDiagonal (n+1) := ⟨f, flat_iff.mp hf⟩
    change ofFlatSequence T (n+1) (ConfigSpace.flipConj F.1) = conj (ofFlatSequence T (n+1) F.1)
    rw [at_flat T (ConfigSpace.DomainsAndFiniteSums.flipConj_mem
      (TestFunctionOps.operationsStatement_holds TestSpaces.Elementary.basicProperties) F.2), at_flat T F.2]
    exact hr n F _
  · intro Φ h
    rw [← pairing_eq]
    exact hos (posSeq Φ h) (posSeq_finite Φ h)

private theorem shift_eq (w : Point) {n : ℕ} (f : Test n) :
    ConfigSpace.shiftActAt w (ConfigSpace.ofConfigFn f) = ConfigSpace.ofConfigFn (translate w f) := by
  cases n with
  | zero => exact congrArg f (Subsingleton.elim _ _)
  | succ k => exact funext (ConfigSpace.shiftAct_apply w f)

private theorem reflect_eq {n : ℕ} (f : Test n) :
    ConfigSpace.flipConjAt (ConfigSpace.ofConfigFn f) = ConfigSpace.ofConfigFn (reflectConj f) := by
  cases n with
  | zero => exact congrArg (fun c : ℂ => conj c) (congrArg f (Subsingleton.elim _ _))
  | succ k => rfl

theorem os_of_component {σ : SeparatedTuples.TupleFunctional} {T : FlatSequence}
    {D : SystemsWithFiveBounds.LimitConstants} (hD : D.Valid)
    (hT : SystemsWithFiveBounds.HasSchwingerSequence σ T) (ho : SystemsWithFiveBounds.OSAxioms D T) :
    Axioms (ofFlatSequence T) := by
  refine ⟨axioms_of_schwinger hD hT ho.growth ho.euclidInv ho.osPositive ho.permSymm ho.reality, ?_⟩
  intro Φ Ψ hΦ hΨ v hv hv'
  have hc := ho.cluster (posSeq Φ hΦ) (posSeq Ψ hΨ) (posSeq_finite Φ hΦ) (posSeq_finite Ψ hΨ) v hv hv'
  simpa only [posSeq, shift_eq, reflect_eq, pairing_eq, ofFlatSequence] using hc

theorem tensor_value {σ : SeparatedTuples.TupleFunctional} {T : FlatSequence}
    (hT : SystemsWithFiveBounds.HasSchwingerSequence σ T)
    {n : ℕ} (X : TestSpaces.SepTupleOfCard n) (hX : ∀ i, ContDiff ℝ ∞ (X.1 i)) :
    ofFlatSequence T n (tensor X.1) = (LimitTheorem.evalOnMap σ ⟨n,X⟩ : ℂ) := by
  cases n with
  | zero =>
    have e : (⟨0,X⟩ : TestSpaces.SepTuple) = TestSpaces.sepTupleNil := by
      congr 1
      exact Subtype.ext (Subsingleton.elim _ _)
    rw [at_zero T hT.2.1, e, LimitTheorem.evalOnMap, TupleLists.toList_sepTupleNil, σ.map_nil]
    simp [tensor]
  | succ n =>
    let Y : ConfigSpace.SepFamilyOfLength (n+1) := ⟨X.1, fun i => ConfigSpace.mem_realC1CompactIn_iff.2
      ⟨isOpen_univ, (X.2.1 i).1, (X.2.1 i).2.1, Set.subset_univ _⟩, X.2.2⟩
    have hY : ConfigSpace.AllSmoothCompact Y.1 := fun i => ConfigSpace.mem_realSmoothCompactIn_iff.2
      ⟨isOpen_univ, hX i, (X.2.1 i).2.1, Set.subset_univ _⟩
    have hf := (flatSpaceClosure (n+1) (Nat.succ_pos n)).2 Y hY
    change ofFlatSequence T (n+1) (ConfigSpace.tensorRealFamily Y.1) = _
    rw [at_flat T hf]
    exact (hT.2.2 n).2 Y hY hf

theorem tensor_evaluation {S : LimitTheorem.CumulantFamily} {T : FlatSequence}
    (hT : SystemsWithFiveBounds.HasSchwingerSequence (LimitTheorem.centredOf S) T)
    {n : ℕ} (X : TestSpaces.SepTupleOfCard n) (hX : ∀ i, ContDiff ℝ ∞ (X.1 i)) :
    ofFlatSequence T n (tensor X.1) = (TestSpaces.centredOfCumulants S ⟨n,X⟩ : ℂ) := by
  rw [tensor_value hT X hX]
  change (TestSpaces.centredOfCumulants S (TupleLists.ofList (TupleLists.toList ⟨n,X⟩)) : ℂ) = _
  rw [TupleLists.ofList_toList]

theorem connected_value {σ : SeparatedTuples.TupleFunctional} {T : FlatSequence}
    (hT : SystemsWithFiveBounds.HasSchwingerSequence σ T)
    {n : ℕ} (X : TestSpaces.SepTupleOfCard n) (hX : ∀ i, ContDiff ℝ ∞ (X.1 i)) :
    Wilson.connected (ofFlatSequence T) X.1 = LimitTheorem.connectedFn σ X := by
  unfold Wilson.connected LimitTheorem.connectedFn TestSpaces.cumulant
  refine Finset.sum_congr (by
    ext P
    simp only [ClusterExpansion.SymGraph.partitions, ClusterExpansion.SymGraph.IsPartition,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨h₁,h₂,h₃⟩ <;> refine ⟨h₁,h₂,?_⟩ <;>
      simpa only [Finset.ext_iff, Finset.mem_biUnion] using h₃) fun P _ => congrArg _ (Finset.prod_congr rfl fun B _ => ?_)
  exact congrArg Complex.re (tensor_value hT (TestSpaces.sepRestrict X B) (fun i => hX _))

open MeasureTheory in
theorem decomposition_of_components {σ : SeparatedTuples.TupleFunctional} {T : FlatSequence}
    (hT : SystemsWithFiveBounds.HasSchwingerSequence σ T)
    {A : SeparatedTuples.DecompositionData} (ha : A.IsCanonical σ)
    {D : SystemsWithFiveBounds.LimitConstants} (hd : D.Valid)
    (hos : ∀ ξ, ∃ U, SystemsWithFiveBounds.HasSchwingerSequence (A.comp ξ) U ∧ SystemsWithFiveBounds.OSAxioms D U)
    (hng : ∀ᵐ ξ ∂A.law, ∃ X : TestSpaces.SepTupleOfCard 4,
      (∀ i, ContDiff ℝ ∞ (X.1 i)) ∧ LimitTheorem.connectedFn (A.comp ξ) X ≠ 0) :
    Wilson.HasOSDecomposition (ofFlatSequence T) := by
  classical
  choose U hu hfull using hos
  let := ha.compact
  let := ha.isProb
  refine ⟨A.space, inferInstance, A.law, fun ξ => ofFlatSequence (U ξ), ha.isProb,
    fun ξ => os_of_component hd (hu ξ) (hfull ξ), ?_, ?_⟩
  · intro n f hf
    let X : TestSpaces.SepTupleOfCard n :=
      ⟨f, fun i => ⟨(hf.1 i).1.of_le (by norm_num), (hf.1 i).2, Set.subset_univ _⟩, hf.2⟩
    let Y := TupleLists.toList ⟨n,X⟩
    have ev ξ : ofFlatSequence (U ξ) n (tensor f) = (A.comp ξ Y : ℂ) :=
      tensor_value (hu ξ) X (fun i => (hf.1 i).1)
    simp only [ev]
    refine ⟨(Complex.continuous_ofReal.comp (ha.continuous_comp Y)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _), ?_⟩
    rw [integral_complex_ofReal, tensor_value hT X (fun i => (hf.1 i).1)]
    have hi : ∫ ξ, A.comp ξ Y ∂A.law = σ Y := by
      simpa [SeparatedTuples.iteratedLimitAtInfinity, SeparatedTuples.iterLimitValue,
        SeparatedTuples.shiftedJuxt] using ha.integral_comp_prod Y []
    rw [hi]
    rfl
  · filter_upwards [hng] with ξ h
    obtain ⟨X,hs,hc⟩ := h
    exact ⟨X.1, ⟨fun i => ⟨hs i,(X.2.1 i).2.1⟩,X.2.2⟩, (connected_value (hu ξ) X hs) ▸ hc⟩

end YangMills.WilsonOS
end
