import YangMills.Construction.Lattice.OrthonormalCoordinatesOfFunctionsOnBonds
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.Towers.TheMassiveJets
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctionalAreLocal
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheScaledPictureAndTheirJets
import YangMills.Construction.Towers.TheTwoOperatorsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.Locality
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.ConstantOpFun (addSmulKernel)
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs (IsRealOnRealFields)
open YangMills.Construction.Tower.TwoOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets
theorem symbolHom_eq_smul_id {I : PeriodicData} (hI : IsPeriodic I)
    {T : I.Carrier → I.Carrier → ℂ} {κ : Fin 4 → ℂ} {c : ℂ}
    (h : quotSymbol I I T κ = c • quotOne I) :
    symbolHom I I T κ = c • (LinearMap.id : QuotHom I I) := by
  classical
  have := hI.finite_quot
  have e : symbolHom I I T κ = linearMapOfEntries (quotSymbol I I T κ) := rfl
  rw [e, h]
  refine LinearMap.ext fun f => ?_
  rw [linearMapOfEntries_eq_applyKernel]
  funext c'
  have : applyKernel (c • quotOne I) f c' =
      (c • quotOne I) c' c' * f c' := by
    refine tsum_eq_single c' fun b hb => ?_
    simp [quotOne, Ne.symm hb]
  rw [this]
  simp [quotOne]
theorem ofKernel_idKernel {I : PeriodicData} (hI : IsPeriodic I)
    (h : ∀ κ : Fin 4 → ℂ, quotSymbol I I (idKernel I) κ = quotOne I) :
    JetQuad.ofKernel I I (idKernel I) = JetQuad.one I := by
  have e : symbolHom I I (idKernel I) = fun _ => LinearMap.id := by
    funext κ
    have := symbolHom_eq_smul_id hI (c := 1) (κ := κ) (by rw [h κ, one_smul])
    rwa [one_smul] at this
  show (⟨symbolHom I I (idKernel I), 0, 0, 0⟩ : JetQuad I I) = ⟨fun _ => LinearMap.id, 0, 0, 0⟩
  rw [e]
theorem addSmulKernel_idKernel
    (hW : PeriodicOperators.ConstantOpFun.Claim)
    (hD : PeriodicOperators.CovariantFiniteRange.Claim) {F I : PeriodicData}
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    {S : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} (hS : IsLocalOpFun F I I S) (c : ℂ)
    {δ : ℝ} {p : Fin 4 → ℂ} (hδ : 0 < δ) (hp : p ∈ imStrip δ) (εPlus εMinus : F.UnitQuot → ℂ) :
    IsLocalOpFun F I I (addSmulKernel S c (idKernel I)) ∧
      JetQuad.EqAsJet δ p (jetAlong F I I (addSmulKernel S c (idKernel I)) p εPlus εMinus)
        ((jetAlong F I I S p εPlus εMinus).add (JetQuad.smul c (JetQuad.one I))) := by
  obtain ⟨-, hper, hfin, hsym⟩ := hD.1 I hI
  have key := (hW F I I hF hI hI (idKernel I) hper hfin δ p hδ hp εPlus εMinus).2 S c hS
  rwa [ofKernel_idKernel hI hsym] at key
theorem isUnit_smul_id {I : PeriodicData} {c : ℂ} (hc : c ≠ 0) :
    IsUnit (c • (LinearMap.id : QuotHom I I) : Module.End ℂ (I.UnitQuot → ℂ)) := by
  refine ⟨⟨c • (1 : Module.End ℂ (I.UnitQuot → ℂ)), c⁻¹ • 1, ?_, ?_⟩, rfl⟩
  · rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_mul, one_smul]
  · rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_mul, one_smul]
theorem toComplexVec_mem_imStrip (κ : InfiniteLattice.AmbientSpace) {r : ℝ} (hr : 0 ≤ r) :
    toComplexVec κ ∈ imStrip r := fun μ => by
  simpa [toComplexVec] using hr
theorem latticeSymbol_add_ne_zero (κ : InfiniteLattice.AmbientSpace) {z : ℝ} (hz : 0 < z) :
    Massive.latticeSymbol (toComplexVec κ) + (z : ℂ) ≠ 0 := by
  have e : Massive.latticeSymbol (toComplexVec κ) + (z : ℂ) =
      ((∑ μ, (2 - 2 * Real.cos (κ μ)) + z : ℝ) : ℂ) := by
    simp [Massive.latticeSymbol, Massive.axisSymbol, toComplexVec]
  rw [e]
  have hs : 0 ≤ ∑ μ, (2 - 2 * Real.cos (κ μ)) :=
    Finset.sum_nonneg fun μ _ => by linarith [Real.cos_le_one (κ μ)]
  have hp : (0 : ℝ) < ∑ μ, (2 - 2 * Real.cos (κ μ)) + z := by linarith
  exact_mod_cast hp.ne'
def positiveValues {L : ℕ} (c : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ) :
    FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2 :=
  open Classical in fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
theorem ofCoeffs_eq_extendOddly {L : ℕ} (c : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c = FullSpace.extendOddly (positiveValues c) := rfl
theorem expField_zero (L : ℕ) :
    FullSpace.expField (L := L) 0 = fun _ => 1 := by
  classical
  have hX : (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs
      (0 : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ) =
        (0 : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) := by
    rw [ofCoeffs_eq_extendOddly]
    funext b
    simp [FullSpace.extendOddly, positiveValues, ofPauliCoeffs]
  show FullSpace.expTwist ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs
    (0 : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ)) (fun _ => 1) = fun _ => 1
  rw [hX]
  funext b
  unfold FullSpace.expTwist
  split_ifs <;> simp [Matrices.ComplexMatrix2.matExp]
theorem mem_realCoeffs (L : ℕ) {ζ : (colourEdges L 0 0).Carrier → ℂ} (h : ∀ κ, (ζ κ).im = 0) :
    ζ ∈ realCoeffs L := by
  classical
  have ha : 0 < meshAt L 0 0 := by simp [meshAt]
  have hnot : ∀ {c : InfiniteLattice.Link (meshAt L 0 0)}, c.IsPositivelyOriented →
      ¬ c.opposite.IsPositivelyOriented := fun {c} hc h' =>
    InfiniteLattice.opposite_notMem_positiveLinks ha
      (InfiniteLattice.mem_positiveLinks_iff.2 hc)
      (InfiniteLattice.mem_positiveLinks_iff.2 h')
  have hrev : ∀ {c : InfiniteLattice.Link (meshAt L 0 0)}, ¬ c.IsPositivelyOriented →
      c.opposite.IsPositivelyOriented := fun {c} hc => by
    rcases InfiniteLattice.mem_positiveLinks_or_opposite_mem c with h' | h'
    · exact absurd (InfiniteLattice.mem_positiveLinks_iff.1 h') hc
    · exact InfiniteLattice.mem_positiveLinks_iff.1 h'
  have hpos : ∀ {c : InfiniteLattice.Link (meshAt L 0 0)}, c.IsPositivelyOriented →
      FullSpace.extendOddly (positiveValues (L := L) ζ) c = positiveValues ζ c :=
    fun hc => if_pos hc
  have hneg : ∀ {c : InfiniteLattice.Link (meshAt L 0 0)}, ¬ c.IsPositivelyOriented →
      FullSpace.extendOddly (positiveValues (L := L) ζ) c = -positiveValues ζ c.opposite :=
    fun hc => if_neg hc
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · have e : (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs ζ b = ofPauliCoeffs ζ ⟨b, hb⟩ :=
      (congrFun (ofCoeffs_eq_extendOddly (L := L) ζ) b).trans ((hpos hb).trans (dif_pos hb))
    rw [e]
    refine Submodule.sum_mem _ fun a _ => ?_
    have e' : ζ (a, ⟨b, hb⟩) = (((ζ (a, ⟨b, hb⟩)).re : ℝ) : ℂ) :=
      Complex.ext rfl (by simpa using h (a, ⟨b, hb⟩))
    rw [e']
    have hs : (((ζ (a, ⟨b, hb⟩)).re : ℝ) : ℂ) • Matrices.ComplexMatrix2.pauliFamily a =
        (ζ (a, ⟨b, hb⟩)).re • Matrices.ComplexMatrix2.pauliFamily a := by
      ext i j
      simp
    rw [hs]
    exact Matrices.ComplexMatrix2.hermitianTraceless.smul_mem _
      (BondFunctions.Coordinates.pauliFamily_mem_hermitianTraceless a)
  · refine (congrFun (ofCoeffs_eq_extendOddly (L := L) ζ) b.opposite).trans
      (Eq.trans ?_ (congrArg Neg.neg (congrFun (ofCoeffs_eq_extendOddly (L := L) ζ) b).symm))
    by_cases hb : b.IsPositivelyOriented
    · rw [hneg (hnot hb), hpos hb]
      rfl
    · rw [hpos (hrev hb), hneg hb, neg_neg]
theorem addSmulKernel_isReal (L : ℕ) {I : PeriodicData} (z : ℝ)
    {S : ((colourEdges L 0 0).Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
    (h : ∀ ζ ∈ realCoeffs L, ∀ ι' ι, (S ζ ι' ι).im = 0) :
    IsRealOnRealFields (colourEdges L 0 0) I
      (addSmulKernel S (z : ℂ) (idKernel I)) := by
  classical
  intro ζ hζ _ ι' ι
  have e := h ζ (mem_realCoeffs L hζ) ι' ι
  by_cases hι : ι' = ι
  · subst hι
    simp [addSmulKernel, idKernel, e]
  · simp [addSmulKernel, idKernel, hι, e]
theorem isUnit_symbolHom_coeffZero
    (hW : PeriodicOperators.ConstantOpFun.Claim)
    (hD : PeriodicOperators.CovariantFiniteRange.Claim) {F I : PeriodicData}
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    {S : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} (hS : IsLocalOpFun F I I S)
    (hψ : ∀ κ : Fin 4 → ℂ, quotSymbol I I (coeffZero F I I S) κ =
      Massive.latticeSymbol κ • quotOne I)
    {z : ℝ} (hz : 0 < z) (κ : InfiniteLattice.AmbientSpace) :
    IsUnit (symbolHom I I (coeffZero F I I (addSmulKernel S (z : ℂ) (idKernel I)))
      (toComplexVec κ) : Module.End ℂ (I.UnitQuot → ℂ)) := by
  have key := (addSmulKernel_idKernel hW hD hF hI hS (z : ℂ) (δ := 1) (p := 0) one_pos
    (fun μ => by simp) 0 0).2.1 (toComplexVec_mem_imStrip κ (r := 2 * 1) (by norm_num))
  have e : symbolHom I I (coeffZero F I I (addSmulKernel S (z : ℂ) (idKernel I)))
      (toComplexVec κ) =
        (Massive.latticeSymbol (toComplexVec κ) + (z : ℂ)) •
          (LinearMap.id : QuotHom I I) := by
    refine key.trans ?_
    show symbolHom I I (coeffZero F I I S) (toComplexVec κ) +
      (z : ℂ) • LinearMap.id = _
    rw [symbolHom_eq_smul_id hI (hψ _), add_smul]
  rw [e]
  exact isUnit_smul_id (latticeSymbol_add_ne_zero κ hz)
theorem baseLevelLocal (hU : TwoOperators.AtTrivialField)
    (hW : PeriodicOperators.ConstantOpFun.Claim)
    (hD : PeriodicOperators.CovariantFiniteRange.Claim) (hT : PeriodicOperators.TowerIndexSets.Claim)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {z : ℝ} (hz : 0 < z) :
    BaseLevelLocal L z := by
  obtain ⟨hOne, -, hMaps⟩ := hU L hL
  obtain ⟨hSites, hBonds, -⟩ := hT L hL 0 0 le_rfl
  have hS := hMaps.laplacian_local
  have hB := hMaps.massive_local
  have hzero := expField_zero L
  refine ⟨(addSmulKernel_idKernel hW hD hBonds hSites hS.is_local (z : ℂ) (δ := 1) (p := 0) one_pos
      (fun μ => by simp) 0 0).1,
    (addSmulKernel_idKernel hW hD hBonds hBonds hB.is_local (z : ℂ) (δ := 1) (p := 0) one_pos
      (fun μ => by simp) 0 0).1,
    addSmulKernel_isReal L z hS.real, addSmulKernel_isReal L z hB.real, fun κ => ?_, fun κ => ?_⟩
  · refine isUnit_symbolHom_coeffZero hW hD hBonds hSites hS.is_local (fun q => ?_) hz κ
    have e : coeffZero (colourEdges L 0 0) (colourVertices L 0 0) (colourVertices L 0 0)
        FullSpace.gaugeLaplacianAt = FullSpace.gaugeLaplacianKernel (L := L) fun _ => 1 := by
      show FullSpace.gaugeLaplacianKernel (FullSpace.expField 0) = _
      rw [hzero]
    rw [e]
    exact hOne.laplacian_symbol.matrix q
  · refine isUnit_symbolHom_coeffZero hW hD hBonds hBonds hB.is_local (fun q => ?_) hz κ
    have e : coeffZero (colourEdges L 0 0) (colourEdges L 0 0) (colourEdges L 0 0)
        FullSpace.massiveHessianAt = FullSpace.massiveHessianKernel (L := L) fun _ => 1 := by
      show FullSpace.massiveHessianKernel (FullSpace.expField 0) = _
      rw [hzero]
    rw [e]
    exact hOne.massive_symbol.matrix q
theorem massWidth_pos (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) {z : ℝ}
    (hz : 0 < z) : 0 < massWidth z := by
  obtain ⟨-, -, δ₀, hδ₀, -, -, hpos, -⟩ := hN
  have hdom : FreeStrip.halfSupRate.Dom := Part.dom_iff_mem.2 ⟨δ₀, hδ₀⟩
  have e : stripHalfWidth = δ₀ := Part.mem_unique (stripHalfWidth_mem hdom) hδ₀
  refine lt_min (e ▸ hpos.1) ?_
  have := Real.sqrt_pos.2 hz
  positivity
theorem isUnit_f00_of_eqAsJet {I : PeriodicData} {δ : ℝ} {T T' : JetQuad I I}
    {κ : InfiniteLattice.AmbientSpace} (hδ : 0 < δ) {p : Fin 4 → ℂ} (hJ : JetQuad.EqAsJet δ p T T')
    (hU : IsUnit (T'.f00 (toComplexVec κ) : Module.End ℂ (I.UnitQuot → ℂ))) :
    IsUnit (T.f00 (toComplexVec κ) : Module.End ℂ (I.UnitQuot → ℂ)) := by
  rw [hJ.1 (toComplexVec_mem_imStrip κ (by positivity))]
  exact hU
theorem levelLocal
    (hW : PeriodicOperators.ConstantOpFun.Claim)
    (hD : PeriodicOperators.CovariantFiniteRange.Claim) (hT : PeriodicOperators.TowerIndexSets.Claim)
    (hO : FullSpace.ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hM : MassJets.MassJetsClaim) (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {z : ℝ} (hz : 0 < z) :
    LevelLocal L k z := by
  obtain ⟨hSites, hBonds, -⟩ := hT L hL k 0 (Nat.zero_le k)
  have hop := ((hO.1 L hL k hk).1)
  have hS := hop.Delta_local.1
  have hB := hop.K_local.1
  have hδ := massWidth_pos hN hz
  have hjets := ((hM L hL k hk).1 z hz).2
  have h0 : (0 : Fin 4 → ℂ) ∈ momentumPolydisc (massWidth z) := fun μ => by
    simpa using hδ.le
  have h0s : (0 : Fin 4 → ℂ) ∈ imStrip (massWidth z) := fun μ => by
    simpa using hδ.le
  have hat := hjets 0 h0 0 0
  refine ⟨(addSmulKernel_idKernel hW hD hBonds hSites hS (z : ℂ) hδ h0s 0 0).1,
    (addSmulKernel_idKernel hW hD hBonds hBonds hB (z : ℂ) hδ h0s 0 0).1, fun κ => ?_, fun κ => ?_,
    fun p hp μPlus μMinus => ?_⟩
  · exact isUnit_f00_of_eqAsJet hδ
      (addSmulKernel_idKernel hW hD hBonds hSites hS (z : ℂ) hδ h0s
        (scaledResponseField L k 0 0) (scaledResponseField L k (-0) 0)).2
      (hat.1.1.isUnit_f00 _ (toComplexVec_mem_imStrip κ (by linarith)))
  · exact isUnit_f00_of_eqAsJet hδ
      (addSmulKernel_idKernel hW hD hBonds hBonds hB (z : ℂ) hδ h0s
        (scaledResponseField L k 0 0) (scaledResponseField L k (-0) 0)).2
      (hat.2.1.isUnit_f00 _ (toComplexVec_mem_imStrip κ (by linarith)))
  · have hps : toComplexVec p ∈ imStrip (massWidth z) := toComplexVec_mem_imStrip p hδ.le
    exact ⟨(addSmulKernel_idKernel hW hD hBonds hSites hS (z : ℂ) hδ hps _ _).2,
      (addSmulKernel_idKernel hW hD hBonds hBonds hB (z : ℂ) hδ hps _ _).2⟩
theorem opFunsLocal (hU : TwoOperators.AtTrivialField)
    (hW : PeriodicOperators.ConstantOpFun.Claim)
    (hD : PeriodicOperators.CovariantFiniteRange.Claim) (hT : PeriodicOperators.TowerIndexSets.Claim)
    (hO : FullSpace.ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hM : MassJets.MassJetsClaim) (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    OpFunsLocal := fun _ hL _ hz =>
  ⟨baseLevelLocal hU hW hD hT hL hz, fun _ hk => levelLocal hW hD hT hO hM hN hL hk hz⟩
end YangMills.Construction.Tower.MassiveOpFunctions.Locality
end
