import YangMills.Construction.ColdChainAtEveryLevel.PointsOfAPatchForm
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.ComparedDerivativesInCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.CriticalValueIsTheLeastAction
import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.FactsOfTheLogarithm
import YangMills.Construction.ColdChainAtEveryLevel.MeansOfAPotential
import YangMills.Construction.ColdChainAtEveryLevel.MixedDerivativesOfARestriction
import YangMills.Construction.ColdChainAtEveryLevel.RotationDerivativeOfARestriction
import YangMills.Construction.ColdChainAtEveryLevel.ShareOfAMinimalChainIsItsEvaluation
import YangMills.Construction.ColdChainAtEveryLevel.SharesOfAgreeingPairs
import YangMills.Construction.ColdChainAtEveryLevel.SharesUnderAGauge
import YangMills.Construction.ColdChainAtEveryLevel.SharesUnderAnIsometry
import YangMills.Construction.ColdChainAtEveryLevel.SizeNearACellOfASplit
import YangMills.Construction.ColdChainAtEveryLevel.SumOfTheFramedShares
import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbersProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.BlockAverages
namespace AnalyticCellShares
variable {F : BlockFrame} {S : Finset F.Cell}
section Calculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
theorem iteratedFDeriv_succ_eq_fderiv_perm (m : ℕ) {f : (Fin (m + 1) → ℝ) → E} (hf : AnalyticAt ℝ f 0)
    (σ : Equiv.Perm (Fin (m + 1))) :
    iteratedFDeriv ℝ (m + 1) f 0 (fun l => Pi.single l 1) =
      iteratedFDeriv ℝ m (fun ζ => fderiv ℝ f ζ (Pi.single (σ (Fin.last m)) 1)) 0
        (fun l => Pi.single (σ l.castSucc) 1) := by
  have hc : ContDiffAt ℝ ⊤ f 0 := hf.contDiffAt
  have h1 := hc.iteratedFDeriv_comp_perm (fun l => (Pi.single l (1 : ℝ) : Fin (m + 1) → ℝ)) σ
  rw [← h1, iteratedFDeriv_succ_apply_right]
  have hd : AnalyticAt ℝ (fderiv ℝ f) 0 := hf.fderiv
  have hcd : ContDiffAt ℝ m (fderiv ℝ f) 0 := hd.contDiffAt.of_le (by exact_mod_cast le_top)
  have h2 := (ContinuousLinearMap.apply ℝ E (Pi.single (σ (Fin.last m)) (1 : ℝ) : Fin (m + 1) → ℝ)).iteratedFDeriv_comp_left
    hcd (i := m) le_rfl
  have e : (fun ζ => fderiv ℝ f ζ (Pi.single (σ (Fin.last m)) 1)) =
      (ContinuousLinearMap.apply ℝ E (Pi.single (σ (Fin.last m)) (1 : ℝ) : Fin (m + 1) → ℝ)) ∘ fderiv ℝ f := by
    funext ζ
    rfl
  rw [e, h2]
  rfl
theorem fderiv_comp_critical_eq {W Z : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z]
    {H : W × Z → ℝ} {q : Z → W} {z₀ : Z} (hH : DifferentiableAt ℝ H (q z₀, z₀)) (hq : DifferentiableAt ℝ q z₀)
    (hc : ∀ y : W, HasDerivAt (fun τ : ℝ => H (q z₀ + τ • y, z₀)) 0 0) (w : Z) :
    fderiv ℝ (fun z => H (q z, z)) z₀ w = deriv (fun τ : ℝ => H (q z₀, z₀ + τ • w)) 0 := by
  have hD := hH.hasFDerivAt
  set D := fderiv ℝ H (q z₀, z₀) with hDdef
  have hp : HasFDerivAt (fun z => (q z, z)) ((fderiv ℝ q z₀).prod (ContinuousLinearMap.id ℝ Z)) z₀ :=
    hq.hasFDerivAt.prodMk (hasFDerivAt_id z₀)
  have comp : HasFDerivAt (fun z => H (q z, z)) (D.comp ((fderiv ℝ q z₀).prod (ContinuousLinearMap.id ℝ Z))) z₀ :=
    HasFDerivAt.comp z₀ (g := H) (f := fun z => (q z, z)) hD hp
  have line : ∀ (u : W × Z), HasDerivAt (fun τ : ℝ => H ((q z₀, z₀) + τ • u)) (D u) 0 := by
    intro u
    have h1 : HasDerivAt (fun τ : ℝ => (q z₀, z₀) + τ • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add (q z₀, z₀)
    have h2 : HasFDerivAt H D ((q z₀, z₀) + (0 : ℝ) • u) := by simpa using hD
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have z1 : ∀ y : W, D (y, 0) = 0 := by
    intro y
    have h := line (y, 0)
    have e : (fun τ : ℝ => H ((q z₀, z₀) + τ • (y, (0 : Z)))) = fun τ : ℝ => H (q z₀ + τ • y, z₀) := by
      funext τ
      simp
    rw [e] at h
    exact h.unique (hc y)
  have z2 : deriv (fun τ : ℝ => H (q z₀, z₀ + τ • w)) 0 = D (0, w) := by
    have h := line (0, w)
    have e : (fun τ : ℝ => H ((q z₀, z₀) + τ • ((0 : W), w))) = fun τ : ℝ => H (q z₀, z₀ + τ • w) := by
      funext τ
      simp
    rw [e] at h
    exact h.deriv
  rw [comp.fderiv, z2]
  have : ((fderiv ℝ q z₀ w, w) : W × Z) = (fderiv ℝ q z₀ w, 0) + (0, w) := by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]
  rw [this, map_add, z1, zero_add]
end Calculus
section Small
theorem bondSpread_norm_le {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (ζ : Fin k → ℝ) {σ : ℝ} (hσ : ∀ l, |ζ l| ≤ σ) (y : F.Site F.top) (i : Fin 4) :
    ‖bondSpread c X ζ y i‖ ≤ k * σ := by
  unfold bondSpread
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ l ∈ (Finset.univ : Finset (Fin k)),
      ‖(if c l = (y, i) then ζ l • X l else 0 : imaginaryQuaternions)‖ ≤ σ := by
    intro l _
    split_ifs
    · rw [norm_smul, hX l, mul_one]
      exact hσ l
    · simpa using (abs_nonneg _).trans (hσ l)
  refine (Finset.sum_le_card_nsmul _ _ σ h).trans (le_of_eq ?_)
  simp
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem rotatedField_zero (V : F.GaugeField F.top) :
    rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V = V := by
  funext y i
  simp [rotatedField, expUnit_zero]
theorem bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondSpread c X (0 : Fin k → ℝ) = fun _ _ => 0 := by
  funext y i
  simp [bondSpread]
theorem isBondAnalyticAt_of_unit {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : F.GaugeField F.top → E}
    {V : F.GaugeField F.top}
    (h : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
      AreUnitVectors X → AnalyticAt ℝ (fun σ : Fin k → ℝ => G (rotatedField (bondSpread c X σ) V)) 0) :
    IsBondAnalyticAt G V := by
  classical
  intro k c X
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : (fun σ : Fin 0 → ℝ => G (rotatedField (bondSpread c X σ) V)) =
        fun _ => G (rotatedField (bondSpread c X 0) V) := by
      funext σ
      rw [Subsingleton.elim σ 0]
    rw [this]
    exact analyticAt_const
  · have hu : ∃ u : imaginaryQuaternions, ‖u‖ = 1 := by
      let qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
      have hq0 : qi ∈ imaginaryQuaternions := rfl
      have hn : ‖qi‖ * ‖qi‖ = 1 := by
        rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
        simp [qi]
      have h1 : ‖qi‖ = 1 := (mul_self_eq_one_iff.1 hn).resolve_right (by linarith [norm_nonneg qi])
      exact ⟨⟨qi, hq0⟩, h1⟩
    obtain ⟨u, hu⟩ := hu
    let Xh : Fin k → imaginaryQuaternions := fun l => if X l = 0 then u else ‖X l‖⁻¹ • X l
    have hXh : AreUnitVectors Xh := by
      intro l
      by_cases h0 : X l = 0
      · simp [Xh, h0, hu]
      · simp only [Xh, if_neg h0, norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)
    have hX : ∀ l, X l = ‖X l‖ • Xh l := by
      intro l
      by_cases h0 : X l = 0
      · simp [h0]
      · simp only [Xh, if_neg h0, smul_smul]
        rw [mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]
    let P : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
      ContinuousLinearMap.pi fun l => ‖X l‖ • ContinuousLinearMap.proj l
    have hs : ∀ σ, bondSpread c X σ = bondSpread c Xh (P σ) := by
      intro σ
      funext y i
      simp only [bondSpread]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs
      · have : P σ l = ‖X l‖ * σ l := by simp [P]
        rw [this, mul_comm, mul_smul, ← hX l]
      · rfl
    have h1 := h k c Xh hk hXh
    have h2 : AnalyticAt ℝ (fun σ : Fin k → ℝ => G (rotatedField (bondSpread c Xh σ) V)) (P 0) := by
      rw [map_zero]
      exact h1
    have h3 := h2.comp (P.analyticAt 0)
    refine h3.congr (Filter.Eventually.of_forall fun σ => ?_)
    simp only [Function.comp]
    rw [hs]
end Small
section Coordinates
abbrev BondVec (S : Finset F.Cell) : Type :=
  (↥(innerBonds S 0) → imaginaryQuaternions) × ((j : Fin F.depth) → ↥(innerBonds S (j.1 + 1)) → imaginaryQuaternions)
def toBondVec (S : Finset F.Cell) (U : ChainChart F) : BondVec S :=
  (fun b => U.fine b.1.1 b.1.2, fun j b => U.coarse j.1 b.1.1 b.1.2)
open Classical in
def chartOfBondVec (x : BondVec S) : ChainChart F :=
  ⟨fun y i => if h : (y, i) ∈ innerBonds S 0 then x.1 ⟨(y, i), h⟩ else 0,
    fun j y i => if h' : j < F.depth then
      if h : (y, i) ∈ innerBonds S (j + 1) then x.2 ⟨j, h'⟩ ⟨(y, i), h⟩ else 0 else 0⟩
theorem chartOfBondVec_fine (x : BondVec S) {b : F.Site 0 × Fin 4} (hb : b ∈ innerBonds S 0) :
    (chartOfBondVec x).fine b.1 b.2 = x.1 ⟨b, hb⟩ := by
  simp [chartOfBondVec, hb]
theorem chartOfBondVec_coarse (x : BondVec S) {j : ℕ} (hj : j < F.depth) {b : F.Site (j + 1) × Fin 4}
    (hb : b ∈ innerBonds S (j + 1)) :
    (chartOfBondVec x).coarse j b.1 b.2 = x.2 ⟨j, hj⟩ ⟨b, hb⟩ := by
  simp [chartOfBondVec, hb, hj]
theorem lt_depth_of_succ_lt_top {j : ℕ} (hj : j + 1 < F.top) : j < F.depth := by
  simp only [BlockFrame.top] at hj
  omega
theorem chartShift_sum_agree {ι : Type} [Fintype ι] (U : ChainChart F) (b : ι → BondVec S) (t : ι → ℝ) :
    ChartEqOnBonds S (chartMove U (chartOfBondVec (∑ l, t l • b l)) 1)
      (chartShiftAlong U (fun l => chartOfBondVec (b l)) t) := by
  refine ⟨fun c hc => ?_, fun j hj c hc => ?_⟩
  · simp only [chartMove, chartShiftAlong, one_smul, chartOfBondVec_fine _ hc, Prod.fst_sum, Prod.smul_fst,
      Finset.sum_apply, Pi.smul_apply]
  · have hj' := lt_depth_of_succ_lt_top hj
    simp only [chartMove, chartShiftAlong, one_smul, chartOfBondVec_coarse _ hj' hc, Prod.snd_sum, Prod.smul_snd,
      Finset.sum_apply, Pi.smul_apply]
theorem topVariationAlong_bondSpread {k : ℕ} {ι : Type} [Fintype ι] (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (η : ι → Fin k → ℝ) (t : ι → ℝ) :
    topVariationAlong (fun β => bondSpread c X (η β)) t = bondSpread c X (∑ β, t β • η β) := by
  funext y i
  simp only [topVariationAlong, bondSpread, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul]
  · simp
theorem analyticAt_chart_and_spread {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : F.FieldChain}
    {z : F.Cell} {B : Finset (F.Site F.top × Fin 4)} {Ck : ℕ → ℝ} {U : ChainChart F}
    {Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E} (hΦ : IsLocalRepresentation S R z B Ck U Φ)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    AnalyticAt ℝ (fun p : BondVec S × (Fin k → ℝ) =>
      Φ (chartMove U (chartOfBondVec p.1) 1) (bondSpread c X p.2)) 0 := by
  haveI : FiniteDimensional ℝ imaginaryQuaternions := inferInstance
  let bs := Module.finBasis ℝ (BondVec S × (Fin k → ℝ))
  set d := Module.finrank ℝ (BondVec S × (Fin k → ℝ)) with hd
  let A : Fin d → ChainChart F := fun β => chartOfBondVec (bs β).1
  let e : Fin d → F.Site F.top → Fin 4 → imaginaryQuaternions := fun β => bondSpread c X (bs β).2
  have hΨ : AnalyticAt ℝ (fun t : Fin d → ℝ => Φ (chartShiftAlong U A t) (topVariationAlong e t)) 0 := hΦ.analyticAt A e
  let Lb : (BondVec S × (Fin k → ℝ)) →L[ℝ] (Fin d → ℝ) := (bs.equivFunL : _ ≃L[ℝ] _).toContinuousLinearMap
  have hrec : ∀ p, ∑ β, Lb p β • bs β = p := fun p => bs.sum_equivFun p
  have key : ∀ p : BondVec S × (Fin k → ℝ), Φ (chartMove U (chartOfBondVec p.1) 1) (bondSpread c X p.2) =
      Φ (chartShiftAlong U A (Lb p)) (topVariationAlong e (Lb p)) := by
    intro p
    have h1 : ∑ β, Lb p β • (bs β).1 = p.1 := by
      have := congrArg Prod.fst (hrec p)
      simpa [Prod.fst_sum] using this
    have h2 : ∑ β, Lb p β • (bs β).2 = p.2 := by
      have := congrArg Prod.snd (hrec p)
      simpa [Prod.snd_sum] using this
    have h3 := chartShift_sum_agree (S := S) U (fun β => (bs β).1) (Lb p)
    rw [h1] at h3
    have h4 := topVariationAlong_bondSpread c X (fun β => (bs β).2) (Lb p)
    rw [h2] at h4
    rw [hΦ.congr_of_agree _ _ _ h3, ← h4]
  have h0 : AnalyticAt ℝ (fun t : Fin d → ℝ => Φ (chartShiftAlong U A t) (topVariationAlong e t)) (Lb 0) := by
    rw [map_zero]
    exact hΨ
  have h1 := h0.comp (Lb.analyticAt 0)
  exact h1.congr (Filter.Eventually.of_forall fun p => (key p).symm)
end Coordinates
section Tops
theorem enclosingCell_top (y : F.Cell) : enclosingCell y = y := by apply _root_.YangMills.Construction.PotentialMeans.enclosingCell_self <;> assumption
open ChartCoordinates PatchLocality
theorem cellSupDist_le_one_of_mem_topBonds {Y : F.Cell} {b : F.Site F.top × Fin 4}
    (hb : b ∈ topBondsMeetingCell S Y) : cellSupDist Y b.1 ≤ 1 := by
  classical
  rcases (Finset.mem_filter.1 hb).2 with h | h
  · rw [h, cellSupDist_self]
    exact Nat.zero_le _
  · rw [← h]
    refine Finset.sup_le fun i _ => ?_
    have e' : (b.1 + unitStep F.top b.2 : F.Site F.top) i - b.1 i =
        ((LatticeFractionalIntegration.basisVector b.2 i : ℤ) : ZMod (F.period F.top i)) := by
      simp [unitStep_eq, siteOfCoords]
    show (((((b.1 + unitStep F.top b.2 : F.Site F.top) i) - b.1 i).valMinAbs).natAbs) ≤ 1
    rw [e']
    refine (PatchPoints.natAbs_valMinAbs_intCast_le _ _).trans ?_
    by_cases hi : i = b.2
    · subst hi
      simp [LatticeFractionalIntegration.basisVector]
    · simp [LatticeFractionalIntegration.basisVector, Pi.single_eq_of_ne hi]
theorem localCellShare_congr_spread {a : ℝ} {R : F.FieldChain} {V : F.GaugeField F.top} {Y : F.Cell}
    {U : ChainChart F} {v v' : F.Site F.top → Fin 4 → imaginaryQuaternions}
    (h : ∀ b ∈ topBondsMeetingCell S Y, v b.1 b.2 = v' b.1 b.2) :
    localCellShare a S R V Y U v = localCellShare a S R V Y U v' := by
  classical
  unfold localCellShare gaugedCellShare
  have h0 : 0 < F.top := Nat.succ_pos _
  rw [chartChain_of_lt R U (rotatedField v V) h0, chartChain_of_lt R U (rotatedField v' V) h0]
  refine congrArg₂ (· + ·) rfl (congrArg (a * ·) (Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr rfl fun c hc => ?_))
  have hjn : j < F.top := Finset.mem_range.1 hj
  rw [chartChain_of_lt R U (rotatedField v V) hjn, chartChain_of_lt R U (rotatedField v' V) hjn]
  by_cases htop : j + 1 < F.top
  · rw [chartChain_of_lt R U (rotatedField v V) htop, chartChain_of_lt R U (rotatedField v' V) htop]
  · obtain rfl : j = F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    rw [chartChain_top R U (rotatedField v V), chartChain_top R U (rotatedField v' V)]
    by_cases hb : c ∈ topBondsMeetingCell S Y
    · have e := h c hb
      unfold gaugedBlockFit
      simp only [rotatedField]
      rw [e]
    · have w0 : (if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
          (if enclosingCell (c.1 + unitStep (F.depth + 1) c.2) = Y then (1 / 2 : ℝ) else 0) = 0 := by
        rw [if_neg, if_neg]
        · simp
        · intro e
          exact hb (Finset.mem_filter.2 ⟨hc, Or.inr (by rwa [enclosingCell_top] at e)⟩)
        · intro e
          exact hb (Finset.mem_filter.2 ⟨hc, Or.inl (by rwa [enclosingCell_top] at e)⟩)
      rw [w0, zero_mul, zero_mul]
theorem unitQuaternion_re_le_one (g : UnitQuaternion) : (g : ℍ[ℝ]).re ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.re_coe_le_one <;> assumption
theorem cellShare_nonneg {a : ℝ} (ha : 0 ≤ a) (hV : minimalChainExistenceStatement) (Y : F.Cell)
    (X : F.FieldChain) : 0 ≤ cellShare a S Y X := by
  classical
  unfold cellShare
  refine add_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg ?_ ?_) (mul_nonneg ha ?_)
  · exact Finset.sum_nonneg fun x _ => by split_ifs <;> norm_num
  · linarith [unitQuaternion_re_le_one (plaquetteHolonomy (X 0) p)]
  · refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => mul_nonneg ?_ ?_
    · split_ifs <;> norm_num
    · exact (hV F a S ha).1 j _ _ c
theorem cellShare_of_not_mem (hodd : Odd F.blockSide) {a : ℝ} {Y : F.Cell} (hY : Y ∉ S) (X : F.FieldChain) :
    cellShare a S Y X = 0 := by
  classical
  unfold cellShare
  have e1 : ∀ p ∈ innerPlaquettes S 0,
      (∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0) = 0 := by
    intro p hp
    refine Finset.sum_eq_zero fun x hx => if_neg fun e => hY ?_
    rw [← e]
    exact LocalPartition.enclosingCell_mem hodd ((Finset.mem_filter.1 hp).2.2 hx)
  have e2 : ∀ j, ∀ c ∈ innerBonds S (j + 1), ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
      (if enclosingCell (c.1 + unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) = 0 := by
    intro j c hc
    have hb := innerBonds_ends hc
    rw [if_neg, if_neg]
    · simp
    · intro e
      exact hY (e ▸ LocalPartition.enclosingCell_mem hodd hb.2)
    · intro e
      exact hY (e ▸ LocalPartition.enclosingCell_mem hodd hb.1)
  rw [Finset.sum_eq_zero fun p hp => by rw [e1 p hp, zero_mul],
    Finset.sum_eq_zero (s := Finset.range F.top) fun j _ =>
      Finset.sum_eq_zero fun c hc => by rw [e2 j c hc, zero_mul]]
  simp
theorem minimalCellShare_of_not_mem (hodd : Odd F.blockSide) {a : ℝ} {Y : F.Cell} (hY : Y ∉ S)
    (V : F.GaugeField F.top) : minimalCellShare a S Y V = 0 := by
  classical
  unfold minimalCellShare
  split_ifs
  · exact cellShare_of_not_mem hodd hY _
  · rfl
def ReadsRotatedTops (a θ del Ca CL σ₀ : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) : Prop :=
  ∀ (s' : ℝ) (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (U' : ChainChart F), 0 < s' → s' ≤ σ₀ →
    IsCold S F.top s' V → (∀ y i, ‖v y i‖ ≤ s') →
    IsCriticalChainOverTop a θ del Ca CL s' S V (rotatedField v V) U' →
    (∀ X, IsMinimalChain a S (rotatedField v V) X → ∀ Y, cellShare a S Y X =
      localCellShare a S (referenceFieldChain S V) V Y U' v) ∧
    minimalAction a S F.top (rotatedField v V) = chartAction a S (referenceFieldChain S V) U' (rotatedField v V)
variable {a θ del Ca rL r' CL σ₀ s : ℝ} {Dk : ℕ → ℝ} {V : F.GaugeField F.top} {U : ChainChart F} {k : ℕ}
  {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {T : (Fin k → ℝ) → ChainChart F}
theorem eventually_isCriticalChainOverTop (hk : 1 ≤ k)
    (hT : IsRotatedChain a θ del Ca rL r' CL s Dk S V c X U T) (hX : AreUnitVectors X)
    (hr : 0 < r') (hs : 0 < s) (hsσ : s < σ₀) (hcold : IsCold S F.top s V) :
    ∀ᶠ ζ in 𝓝 (0 : Fin k → ℝ), ∃ s' : ℝ, 0 < s' ∧ s' ≤ σ₀ ∧ IsCold S F.top s' V ∧
      (∀ y i, ‖bondSpread c X ζ y i‖ ≤ s') ∧
      IsCriticalChainOverTop a θ del Ca CL s' S V (rotatedField (bondSpread c X ζ) V) (T ζ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hσ' : 0 < min (r' / k / 2) ((σ₀ - s) / k) :=
    lt_min (by positivity) (div_pos (by linarith) hk0)
  set σ' := min (r' / k / 2) ((σ₀ - s) / k) with hdef
  filter_upwards [Metric.ball_mem_nhds (0 : Fin k → ℝ) hσ'] with ζ hζ
  have hl : ∀ l, |ζ l| ≤ σ' := by
    intro l
    have h1 := norm_le_pi_norm ζ l
    have h2 : ‖ζ‖ < σ' := by simpa using hζ
    rw [Real.norm_eq_abs] at h1
    linarith
  have h1 : σ' ≤ (σ₀ - s) / k := min_le_right _ _
  have h2 : (k : ℝ) * σ' ≤ σ₀ - s := by
    rw [le_div_iff₀ hk0] at h1
    linarith
  have h3 : σ' < r' / k := by
    have : σ' ≤ r' / k / 2 := min_le_left _ _
    linarith
  have h5 : 0 ≤ (k : ℝ) * σ' := by positivity
  refine ⟨s + k * σ', by positivity, by linarith, fun p hp => (hcold p hp).trans_le (by linarith), fun y i => ?_,
    hT.critical ζ σ' hl h3⟩
  exact (bondSpread_norm_le c X hX ζ hl y i).trans (by linarith)
theorem minimalCellShare_eventuallyEq (hR : ReadsRotatedTops a θ del Ca CL σ₀ S V)
    (hLV : ∀ V' : F.GaugeField F.top, ∃ X, IsMinimalChain a S V' X)
    (hev : ∀ᶠ ζ in 𝓝 (0 : Fin k → ℝ), ∃ s' : ℝ, 0 < s' ∧ s' ≤ σ₀ ∧ IsCold S F.top s' V ∧
      (∀ y i, ‖bondSpread c X ζ y i‖ ≤ s') ∧
      IsCriticalChainOverTop a θ del Ca CL s' S V (rotatedField (bondSpread c X ζ) V) (T ζ)) (Y : F.Cell) :
    (fun ζ => minimalCellShare a S Y (rotatedField (bondSpread c X ζ) V)) =ᶠ[𝓝 0]
      fun ζ => localCellShare a S (referenceFieldChain S V) V Y (T ζ) (bondSpread c X ζ) := by
  classical
  filter_upwards [hev] with ζ hζ
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := hζ
  have hex := hLV (rotatedField (bondSpread c X ζ) V)
  unfold minimalCellShare
  rw [dif_pos hex]
  exact (hR s' _ _ h1 h2 h3 h4 h5).1 _ hex.choose_spec Y
theorem chartAction_eq_sum (hSum : gaugedCellShareSumStatement) (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (a : ℝ)
    (R : F.FieldChain) (U' : ChainChart F) (V : F.GaugeField F.top)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    chartAction a S R U' (rotatedField v V) = ∑ Y ∈ S, localCellShare a S R V Y U' v :=
  hSum F a S _ _ hamb hodd
theorem minimalAction_eventuallyEq (hSum : gaugedCellShareSumStatement) (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide)
    (hR : ReadsRotatedTops a θ del Ca CL σ₀ S V)
    (hev : ∀ᶠ ζ in 𝓝 (0 : Fin k → ℝ), ∃ s' : ℝ, 0 < s' ∧ s' ≤ σ₀ ∧ IsCold S F.top s' V ∧
      (∀ y i, ‖bondSpread c X ζ y i‖ ≤ s') ∧
      IsCriticalChainOverTop a θ del Ca CL s' S V (rotatedField (bondSpread c X ζ) V) (T ζ)) :
    (fun ζ => minimalAction a S F.top (rotatedField (bondSpread c X ζ) V)) =ᶠ[𝓝 0]
      fun ζ => ∑ Y ∈ S, localCellShare a S (referenceFieldChain S V) V Y (T ζ) (bondSpread c X ζ) := by
  filter_upwards [hev] with ζ hζ
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := hζ
  rw [(hR s' _ _ h1 h2 h3 h4 h5).2, chartAction_eq_sum hSum hamb hodd]
end Tops
section Bounds
open ChartCoordinates PatchLocality
theorem localDirectionSize_nonneg (R : F.FieldChain) (B : Finset (F.Site F.top × Fin 4)) (z : F.Cell)
    (A : ChainChart F) (e : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    0 ≤ localDirectionSize S R B z A e := by
  unfold localDirectionSize topVariationNorm localNorm
  exact add_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
theorem isLocalFunctional_mono {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : F.FieldChain} {z : F.Cell}
    {B : Finset (F.Site F.top × Fin 4)} {Ck Ck' : ℕ → ℝ} {U : ChainChart F}
    {Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E} (h : IsLocalRepresentation S R z B Ck U Φ)
    (hC : ∀ m, Ck m ≤ Ck' m) : IsLocalRepresentation S R z B Ck' U Φ :=
  ⟨h.congr_of_agree, fun A e => h.analyticAt A e, fun m A e => (h.iteratedDeriv_le m A e).trans
    (mul_le_mul_of_nonneg_right (hC m)
      (Finset.prod_nonneg fun l _ => localDirectionSize_nonneg R B z (A l) (e l)))⟩
theorem mixedDerivConstant_nonneg {Cs Dk : ℕ → ℝ} {M : ℝ} (hC : ∀ m, 0 ≤ Cs m) (hD : ∀ m, 0 ≤ Dk m)
    (hM : 0 ≤ M) (m : ℕ) : 0 ≤ mixedDerivConstant Cs Dk M m :=
  Finset.sum_nonneg fun c _ => mul_nonneg (hC _) (Finset.prod_nonneg fun i _ => add_nonneg (hD _) hM)
theorem bondSpread_single {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (l : Fin k) (b : F.Site F.top × Fin 4) :
    bondSpread c X (Pi.single l 1) b.1 b.2 = if c l = b then X l else 0 := by
  simp only [bondSpread]
  rw [Finset.sum_eq_single l]
  · simp
  · intro l' _ hl'
    simp [Pi.single_eq_of_ne hl']
  · intro h
    exact absurd (Finset.mem_univ l) h
theorem topVariationNorm_single_le {k : ℕ} (B : Finset (F.Site F.top × Fin 4)) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (l : Fin k) :
    topVariationNorm B (bondSpread c X (Pi.single l 1)) ≤ 1 := by
  classical
  have e : ∀ b : F.Site F.top × Fin 4,
      ‖bondSpread c X (Pi.single l 1) b.1 b.2‖ = if c l = b then 1 else 0 := by
    intro b
    rw [bondSpread_single]
    split_ifs
    · exact hX l
    · simp
  unfold topVariationNorm
  simp only [e]
  rw [Finset.sum_ite_eq]
  split_ifs <;> norm_num
theorem bondSpread_add_smul {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (ζ w : Fin k → ℝ) (τ : ℝ) :
    bondSpread c X (ζ + τ • w) = fun y i => bondSpread c X ζ y i + τ • bondSpread c X w y i := by
  funext y i
  simp only [bondSpread, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simp [add_smul, mul_smul]
  · simp
theorem analyticAt_sum_critical {W Z ι : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {P : Finset ι} {HY : ι → W × Z → ℝ} {q : Z → W} (hHY : ∀ Y, AnalyticAt ℝ (HY Y) 0) (hq : AnalyticAt ℝ q 0)
    (hq0 : q 0 = 0)
    (hc : ∀ᶠ ζ in 𝓝 (0 : Z), ∀ y : W, HasDerivAt (fun τ : ℝ => ∑ Y ∈ P, HY Y (q ζ + τ • y, ζ)) 0 0) :
    AnalyticAt ℝ (fun ζ => ∑ Y ∈ P, HY Y (q ζ, ζ)) 0 ∧
      ∀ w : Z, ∀ᶠ ζ in 𝓝 (0 : Z), fderiv ℝ (fun ζ => ∑ Y ∈ P, HY Y (q ζ, ζ)) ζ w =
        ∑ Y ∈ P, deriv (fun τ : ℝ => HY Y (q ζ, ζ + τ • w)) 0 := by
  classical
  have hpt : AnalyticAt ℝ (fun ζ => (q ζ, ζ)) 0 := hq.prod analyticAt_id
  have hp0 : (q 0, (0 : Z)) = (0 : W × Z) := by
    rw [hq0]
    rfl
  have hcont : Filter.Tendsto (fun ζ => (q ζ, ζ)) (𝓝 0) (𝓝 0) := by
    have h1 := hpt.continuousAt.tendsto
    simp only [hp0] at h1
    exact h1
  have hH : AnalyticAt ℝ (fun p : W × Z => ∑ Y ∈ P, HY Y p) 0 := Finset.analyticAt_fun_sum _ fun Y _ => hHY Y
  refine ⟨?_, fun w => ?_⟩
  · have h1 : AnalyticAt ℝ (fun p : W × Z => ∑ Y ∈ P, HY Y p) ((fun ζ => (q ζ, ζ)) 0) := by
      show AnalyticAt ℝ _ (q 0, (0 : Z))
      rw [hp0]
      exact hH
    exact AnalyticAt.comp (g := fun p : W × Z => ∑ Y ∈ P, HY Y p) (f := fun ζ => (q ζ, ζ)) h1 hpt
  · have e1 : ∀ᶠ ζ in 𝓝 (0 : Z), ∀ Y ∈ P, AnalyticAt ℝ (HY Y) (q ζ, ζ) :=
      (Filter.eventually_all_finset P).2 fun Y _ => hcont.eventually (hHY Y).eventually_analyticAt
    have e2 : ∀ᶠ ζ in 𝓝 (0 : Z), AnalyticAt ℝ q ζ := hq.eventually_analyticAt
    filter_upwards [e1, e2, hc] with ζ h1 h2 h3
    have hHd : DifferentiableAt ℝ (fun p : W × Z => ∑ Y ∈ P, HY Y p) (q ζ, ζ) :=
      DifferentiableAt.fun_sum fun Y hY => (h1 Y hY).differentiableAt
    have env := fderiv_comp_critical_eq (H := fun p : W × Z => ∑ Y ∈ P, HY Y p) (q := q) hHd
      h2.differentiableAt h3 w
    rw [env]
    have l1 : HasDerivAt (fun τ : ℝ => ((q ζ, ζ + τ • w) : W × Z)) (0, w) 0 := by
      have := (hasDerivAt_const (0 : ℝ) (q ζ)).prodMk (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add ζ)
      simpa using this
    have hd : ∀ Y ∈ P, DifferentiableAt ℝ (fun τ : ℝ => HY Y (q ζ, ζ + τ • w)) 0 := by
      intro Y hY
      have h4 : DifferentiableAt ℝ (HY Y) ((fun τ : ℝ => ((q ζ, ζ + τ • w) : W × Z)) 0) := by
        simpa using (h1 Y hY).differentiableAt
      exact h4.comp (0 : ℝ) l1.differentiableAt
    exact deriv_fun_sum hd
structure PairData (a θ del Ca rL r' CL σ₀ s : ℝ) (Dk Cs : ℕ → ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (U : ChainChart F) : Prop where
  s_pos : 0 < s
  s_lt : s < σ₀
  radius_pos : 0 < r'
  decay_nonneg : 0 ≤ del
  cold : IsCold S F.top s V
  chainBound_nonneg : ∀ m, 0 ≤ Dk m
  evaluationBound_nonneg : ∀ m, 0 ≤ Cs m
  reads : ReadsRotatedTops a θ del Ca CL σ₀ S V
  exists_minimal : ∀ V' : F.GaugeField F.top, ∃ X, IsMinimalChain a S V' X
  local_evaluation : ∀ Y, IsLocalRepresentation S (referenceFieldChain S V) Y (topBondsMeetingCell S Y) Cs U
    (localCellShare a S (referenceFieldChain S V) V Y)
variable {a θ del Ca rL r' CL σ₀ s : ℝ} {Dk Cs : ℕ → ℝ} {V : F.GaugeField F.top} {U : ChainChart F} {k : ℕ}
  {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {T : (Fin k → ℝ) → ChainChart F}
theorem minimalCellShare_family (P : PairData a θ del Ca rL r' CL σ₀ s Dk Cs S V U)
    (hMix : localMixedDerivStatement)
    (hk : 1 ≤ k) (hT : IsRotatedChain a θ del Ca rL r' CL s Dk S V c X U T) (hX : AreUnitVectors X) (Y : F.Cell)
    {Cq : ℕ → ℝ} (hCq : ∀ m, 0 ≤ Cq m)
    (hloc : IsLocalRepresentation S (referenceFieldChain S V) Y (topBondsMeetingCell S Y) Cq U
      (localCellShare a S (referenceFieldChain S V) V Y)) :
    AnalyticAt ℝ (fun ζ => minimalCellShare a S Y (rotatedField (bondSpread c X ζ) V)) 0 ∧
      ∀ (m : ℕ) (e : Fin m ↪ Fin k), 1 ≤ m →
        ‖iteratedFDeriv ℝ m (fun ζ => minimalCellShare a S Y (rotatedField (bondSpread c X ζ) V)) 0
          (fun l => Pi.single (e l) 1)‖ ≤
          mixedDerivConstant Cq Dk (Real.exp (del * ((1 : ℕ) : ℝ))) m *
            Real.exp (-del * bondListDistance Y (c ∘ e)) := by
  have hev := eventually_isCriticalChainOverTop hk hT hX P.radius_pos P.s_pos P.s_lt P.cold
  have hE := minimalCellShare_eventuallyEq P.reads P.exists_minimal hev Y
  have M := hMix F ℝ S (referenceFieldChain S V) Y (topBondsMeetingCell S Y) Cq Dk U
    (localCellShare a S (referenceFieldChain S V) V Y) del 1 k c X T P.decay_nonneg hCq P.chainBound_nonneg hloc hX
    (fun b hb => cellSupDist_le_one_of_mem_topBonds hb) hT.eq_at_zero hT.analyticAt_fine hT.analyticAt_coarse
    (fun m e hm => hT.decay m e Y hm)
  refine ⟨M.1.congr hE.symm, fun m e hm => ?_⟩
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hE m).self_of_nhds]
  exact M.2.2 m e hm
set_option maxHeartbeats 1000000 in
theorem minimalAction_family (P : PairData a θ del Ca rL r' CL σ₀ s Dk Cs S V U)
    (hSum : gaugedCellShareSumStatement)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hk : 1 ≤ k)
    (hT : IsRotatedChain a θ del Ca rL r' CL s Dk S V c X U T)
    (hX : AreUnitVectors X) :
    ∃ g : (Fin k → ℝ) → ℝ, (fun ζ => minimalAction a S F.top (rotatedField (bondSpread c X ζ) V)) =ᶠ[𝓝 0] g ∧
      AnalyticAt ℝ g 0 ∧
      ∀ w : Fin k → ℝ, ∀ᶠ ζ in 𝓝 (0 : Fin k → ℝ), fderiv ℝ g ζ w =
        ∑ Y ∈ S, derivAlongRotation (localCellShare a S (referenceFieldChain S V) V Y) (bondSpread c X w) (T ζ)
          (bondSpread c X ζ) := by
  classical
  have hfd : FiniteDimensional ℝ imaginaryQuaternions := inferInstance
  have hcs : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
  have hL := P.local_evaluation
  have hvec : AnalyticAt ℝ (fun ζ => toBondVec S (T ζ)) 0 := by
    refine AnalyticAt.prod ?_ ?_
    · rw [analyticAt_pi_iff]
      exact fun b => hT.analyticAt_fine b.1 b.2
    · rw [analyticAt_pi_iff]
      intro j
      rw [analyticAt_pi_iff]
      exact fun b => hT.analyticAt_coarse j.1 (by simp only [BlockFrame.top]; omega) b.1 b.2
  obtain ⟨q, hqdef⟩ : ∃ q : (Fin k → ℝ) → BondVec S, q = fun ζ => toBondVec S (T ζ) - toBondVec S U := ⟨_, rfl⟩
  have hq : AnalyticAt ℝ q 0 := by
    rw [hqdef]
    exact hvec.sub analyticAt_const
  have hq0 : q 0 = 0 := by
    have e : toBondVec S (T 0) = toBondVec S U := by
      refine Prod.ext (funext fun b => hT.eq_at_zero.1 b.1 b.2) (funext fun j => funext fun b => ?_)
      exact hT.eq_at_zero.2 j.1 (by simp only [BlockFrame.top]; omega) b.1 b.2
    rw [hqdef]
    simp only [e, sub_self]
  have hsame : ∀ ζ (y : BondVec S) (τ : ℝ), ChartEqOnBonds S (chartMove U (chartOfBondVec (q ζ + τ • y)) 1)
      (chartMove (T ζ) (chartOfBondVec y) τ) := by
    intro ζ y τ
    refine ⟨fun b hb => ?_, fun j hj c' hc' => ?_⟩
    · simp only [chartMove, one_smul, chartOfBondVec_fine _ hb]
      simp [hqdef, toBondVec]
      abel
    · simp only [chartMove, one_smul, chartOfBondVec_coarse _ (lt_depth_of_succ_lt_top hj) hc']
      simp [hqdef, toBondVec]
      abel
  have hsame0 : ∀ ζ, ChartEqOnBonds S (chartMove U (chartOfBondVec (q ζ)) 1) (T ζ) := by
    intro ζ
    refine ⟨fun b hb => ?_, fun j hj c' hc' => ?_⟩
    · simp only [chartMove, one_smul, chartOfBondVec_fine _ hb]
      simp [hqdef, toBondVec]
    · simp only [chartMove, one_smul, chartOfBondVec_coarse _ (lt_depth_of_succ_lt_top hj) hc']
      simp [hqdef, toBondVec]
  have hform : ∀ Y ζ v, localCellShare a S (referenceFieldChain S V) V Y (chartMove U (chartOfBondVec (q ζ)) 1) v =
      localCellShare a S (referenceFieldChain S V) V Y (T ζ) v :=
    fun Y ζ v => (hL Y).congr_of_agree _ _ _ (hsame0 ζ)
  obtain ⟨HY, hHYdef⟩ : ∃ HY : F.Cell → BondVec S × (Fin k → ℝ) → ℝ, HY = fun Y p =>
      localCellShare a S (referenceFieldChain S V) V Y (chartMove U (chartOfBondVec p.1) 1)
        (bondSpread c X p.2) := ⟨_, rfl⟩
  have hHY : ∀ Y, AnalyticAt ℝ (HY Y) 0 := by
    intro Y
    rw [hHYdef]
    exact analyticAt_chart_and_spread (hL Y) c X
  have hev := eventually_isCriticalChainOverTop hk hT hX P.radius_pos P.s_pos P.s_lt P.cold
  have hc : ∀ᶠ ζ in 𝓝 (0 : Fin k → ℝ), ∀ y : BondVec S,
      HasDerivAt (fun τ : ℝ => ∑ Y ∈ S, HY Y (q ζ + τ • y, ζ)) 0 0 := by
    filter_upwards [hev] with ζ h3 y
    obtain ⟨s', -, -, -, -, hcc⟩ := h3
    have crit := hcc.critical (chartOfBondVec y)
    have e : (fun τ : ℝ => ∑ Y ∈ S, HY Y (q ζ + τ • y, ζ)) = fun τ : ℝ =>
        chartAction a S (referenceFieldChain S V) (chartMove (T ζ) (chartOfBondVec y) τ)
          (rotatedField (bondSpread c X ζ) V) := by
      funext τ
      rw [chartAction_eq_sum hSum hamb hodd, hHYdef]
      exact Finset.sum_congr rfl fun Y _ => (hL Y).congr_of_agree _ _ _ (hsame ζ y τ)
    rw [e]
    exact crit
  obtain ⟨hga, hgd⟩ := analyticAt_sum_critical (P := S) hHY hq hq0 hc
  have hg : ∀ ζ, ∑ Y ∈ S, HY Y (q ζ, ζ) =
      ∑ Y ∈ S, localCellShare a S (referenceFieldChain S V) V Y (T ζ) (bondSpread c X ζ) := by
    intro ζ
    rw [hHYdef]
    exact Finset.sum_congr rfl fun Y _ => hform Y ζ _
  refine ⟨fun ζ => ∑ Y ∈ S, HY Y (q ζ, ζ), ?_, hga, fun w => ?_⟩
  · filter_upwards [minimalAction_eventuallyEq hSum hamb hodd P.reads hev] with ζ hζ
    rw [hζ]
    exact (hg ζ).symm
  · filter_upwards [hgd w] with ζ hζ
    rw [hζ]
    refine Finset.sum_congr rfl fun Y _ => ?_
    unfold derivAlongRotation
    have e4 : (fun τ : ℝ => HY Y (q ζ, ζ + τ • w)) = fun τ : ℝ =>
        localCellShare a S (referenceFieldChain S V) V Y (T ζ)
          (fun y i => bondSpread c X ζ y i + τ • bondSpread c X w y i) := by
      funext τ
      rw [hHYdef]
      show localCellShare a S (referenceFieldChain S V) V Y (chartMove U (chartOfBondVec (q ζ)) 1)
        (bondSpread c X (ζ + τ • w)) = _
      rw [hform, bondSpread_add_smul]
    rw [e4]
theorem derivAlongRotation_eq_zero {R : F.FieldChain} {Y : F.Cell} {e : F.Site F.top → Fin 4 → imaginaryQuaternions}
    (h : ∀ b ∈ topBondsMeetingCell S Y, e b.1 b.2 = 0) (U' : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    derivAlongRotation (localCellShare a S R V Y) e U' v = 0 := by
  unfold derivAlongRotation
  have e1 : (fun τ : ℝ => localCellShare a S R V Y U' (fun y i => v y i + τ • e y i)) =
      fun _ => localCellShare a S R V Y U' v := by
    funext τ
    exact localCellShare_congr_spread fun b hb => by simp [h b hb]
  rw [e1]
  exact deriv_const _ _
set_option maxHeartbeats 1000000 in
theorem minimalAction_iteratedFDeriv_le (P : PairData a θ del Ca rL r' CL σ₀ s Dk Cs S V U)
    (hMix : localMixedDerivStatement)
    (hTD : localEvaluation_derivAlongRotationStatement) (hSum : gaugedCellShareSumStatement)
    (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) {m : ℕ} (hm : 1 ≤ m) {c : Fin (m + 1) → F.Site F.top × Fin 4}
    {X : Fin (m + 1) → imaginaryQuaternions}
    {T : (Fin (m + 1) → ℝ) → ChainChart F} (hT : IsRotatedChain a θ del Ca rL r' CL s Dk S V c X U T)
    (hX : AreUnitVectors X) :
    ‖iteratedFDeriv ℝ (m + 1) (fun ζ => minimalAction a S F.top (rotatedField (bondSpread c X ζ) V)) 0
      (fun l => Pi.single l 1)‖ ≤
      2 * (mixedDerivConstant (fun n => Cs (n + 1)) Dk (Real.exp (del * ((1 : ℕ) : ℝ))) m * Real.exp del) *
        Real.exp (-del * bondListDiameter c) := by
  classical
  obtain ⟨g, hfg, hga, hgd⟩ := minimalAction_family P hSum hamb hodd (by omega) hT hX
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hfg (m + 1)).self_of_nhds]
  obtain ⟨l₁, -, h1⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun l : Fin (m + 1) => Finset.univ.sup fun l' : Fin (m + 1) => cellSupDist (c l).1 (c l').1)
  obtain ⟨l₂, -, h2⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun l' : Fin (m + 1) => cellSupDist (c l₁).1 (c l').1)
  have hdiam : bondListDiameter c = cellSupDist (c l₁).1 (c l₂).1 := by
    unfold bondListDiameter
    rw [h1]
    exact h2
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (m + 1)), σ (Fin.last m) = l₁ :=
    ⟨Equiv.swap (Fin.last m) l₁, Equiv.swap_apply_left _ _⟩
  rw [iteratedFDeriv_succ_eq_fderiv_perm m hga σ, hσ]
  let emb : Fin m ↪ Fin (m + 1) :=
    ⟨fun l => σ l.castSucc, fun x y h => Fin.castSucc_injective _ (σ.injective h)⟩
  obtain ⟨e, hedef⟩ : ∃ e, e = bondSpread c X (Pi.single l₁ 1) := ⟨_, rfl⟩
  have hez : ∀ Y, c l₁ ∉ topBondsMeetingCell S Y → ∀ b ∈ topBondsMeetingCell S Y, e b.1 b.2 = 0 := by
    intro Y hY b hb
    rw [hedef, bondSpread_single, if_neg]
    intro h
    exact hY (h ▸ hb)
  obtain ⟨Pc, hPc⟩ : ∃ Pc : Finset F.Cell, Pc = S.filter fun Y => c l₁ ∈ topBondsMeetingCell S Y := ⟨_, rfl⟩
  have hE : (fun ζ => fderiv ℝ g ζ (Pi.single l₁ 1)) =ᶠ[𝓝 0] fun ζ => ∑ Y ∈ Pc,
      derivAlongRotation (localCellShare a S (referenceFieldChain S V) V Y) e (T ζ) (bondSpread c X ζ) := by
    filter_upwards [hgd (Pi.single l₁ 1)] with ζ hζ
    rw [hζ, hPc, ← hedef]
    refine (Finset.sum_filter_of_ne fun Y _ hne => ?_).symm
    by_contra hcon
    exact hne (derivAlongRotation_eq_zero (hez Y hcon) _ _)
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hE m).self_of_nhds]
  have M : ∀ Y, AnalyticAt ℝ (fun ζ => derivAlongRotation (localCellShare a S (referenceFieldChain S V) V Y) e (T ζ)
        (bondSpread c X ζ)) 0 ∧
      ‖iteratedFDeriv ℝ m (fun ζ => derivAlongRotation (localCellShare a S (referenceFieldChain S V) V Y) e (T ζ)
        (bondSpread c X ζ)) 0 (fun l => Pi.single (emb l) 1)‖ ≤
        mixedDerivConstant (fun n => Cs (n + 1)) Dk (Real.exp (del * ((1 : ℕ) : ℝ))) m *
          Real.exp (-del * bondListDistance Y (c ∘ emb)) := by
    intro Y
    have hloc := isLocalFunctional_mono (Ck' := fun n => Cs (n + 1))
      (hTD F ℝ S (referenceFieldChain S V) Y (topBondsMeetingCell S Y) Cs U _ e (P.local_evaluation Y))
      (fun n => mul_le_of_le_one_right (P.evaluationBound_nonneg _) (by
        rw [hedef]
        exact topVariationNorm_single_le _ c X hX l₁))
    have M0 := hMix F ℝ S (referenceFieldChain S V) Y (topBondsMeetingCell S Y) (fun n => Cs (n + 1)) Dk U _ del 1
      (m + 1) c X T
      P.decay_nonneg (fun n => P.evaluationBound_nonneg _) P.chainBound_nonneg hloc hX
      (fun b hb => cellSupDist_le_one_of_mem_topBonds hb) hT.eq_at_zero hT.analyticAt_fine
      hT.analyticAt_coarse (fun m' e' hm' => hT.decay m' e' Y hm')
    exact ⟨M0.1, M0.2.2 m emb hm⟩
  have hsum := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := m) (u := Pc) (x := (0 : Fin (m + 1) → ℝ))
    (f := fun Y ζ => derivAlongRotation (localCellShare a S (referenceFieldChain S V) V Y) e (T ζ) (bondSpread c X ζ))
    (fun Y _ => (M Y).1.contDiffAt.of_le (by exact_mod_cast le_top))
  have hsum' : (iteratedFDeriv ℝ m (fun ζ => ∑ Y ∈ Pc,
      derivAlongRotation (localCellShare a S (referenceFieldChain S V) V Y) e (T ζ) (bondSpread c X ζ)) 0)
        (fun l => Pi.single (σ l.castSucc) 1) = ∑ Y ∈ Pc, (iteratedFDeriv ℝ m (fun ζ =>
          derivAlongRotation (localCellShare a S (referenceFieldChain S V) V Y) e (T ζ) (bondSpread c X ζ)) 0)
            (fun l => Pi.single (emb l) 1) := by
    rw [hsum]
    simp only [ContinuousMultilinearMap.sum_apply]
    rfl
  rw [hsum']
  set rc := mixedDerivConstant (fun n => Cs (n + 1)) Dk (Real.exp (del * ((1 : ℕ) : ℝ))) m with hrc
  have hrc0 : 0 ≤ rc :=
    mixedDerivConstant_nonneg (fun n => P.evaluationBound_nonneg _) P.chainBound_nonneg (Real.exp_pos _).le m
  have hd0 := P.decay_nonneg
  have hterm : ∀ Y ∈ Pc, ‖(iteratedFDeriv ℝ m (fun ζ =>
      derivAlongRotation (localCellShare a S (referenceFieldChain S V) V Y) e (T ζ) (bondSpread c X ζ)) 0)
        (fun l => Pi.single (emb l) 1)‖ ≤ rc * Real.exp del * Real.exp (-del * bondListDiameter c) := by
    intro Y hY
    have hYb : c l₁ ∈ topBondsMeetingCell S Y := by
      rw [hPc] at hY
      exact (Finset.mem_filter.1 hY).2
    have hnear := cellSupDist_le_one_of_mem_topBonds hYb
    have hdist : (bondListDiameter c : ℝ) ≤ bondListDistance Y (c ∘ emb) + 1 := by
      rcases eq_or_ne l₂ l₁ with e2 | e2
      · rw [hdiam, e2, cellSupDist_self]
        simp only [Nat.cast_zero]
        positivity
      · have hne : σ.symm l₂ ≠ Fin.last m := by
          intro h
          apply e2
          have := congrArg σ h
          rw [Equiv.apply_symm_apply, hσ] at this
          exact this
        obtain ⟨l, hl⟩ := Fin.exists_castSucc_eq.2 hne
        have hle : cellSupDist Y (c l₂).1 ≤ bondListDistance Y (c ∘ emb) := by
          have e3 : emb l = l₂ := by
            show σ l.castSucc = l₂
            rw [hl, Equiv.apply_symm_apply]
          have h5 : cellSupDist Y ((c ∘ emb) l).1 ≤ bondListDistance Y (c ∘ emb) :=
            Finset.le_sup (f := fun l => cellSupDist Y ((c ∘ emb) l).1) (Finset.mem_univ l)
          have e4 : (c ∘ emb) l = c l₂ := by
            simp [e3]
          rw [e4] at h5
          exact h5
        have h3 := cellSupDist_triangle (c l₁).1 Y (c l₂).1
        rw [PatchLocality.cellSupDist_comm (c l₁).1 Y] at h3
        rw [hdiam]
        have h4 : cellSupDist (c l₁).1 (c l₂).1 ≤ bondListDistance Y (c ∘ emb) + 1 := by omega
        exact_mod_cast h4
    refine (M Y).2.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hrc0
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_)
  have hcard : Pc.card ≤ 2 := by
    have hsub : Pc ⊆ {(c l₁).1, (c l₁).1 + unitStep F.top (c l₁).2} := by
      intro Y hY
      rw [hPc] at hY
      have := (Finset.mem_filter.1 (Finset.mem_filter.1 hY).2).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases this with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hB : 0 ≤ rc * Real.exp del * Real.exp (-del * bondListDiameter c) := by positivity
  rw [nsmul_eq_mul]
  have hc2 : (Pc.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  nlinarith [mul_le_mul_of_nonneg_right hc2 hB]
theorem cellShare_base (P : PairData a θ del Ca rL r' CL σ₀ s Dk Cs S V U)
    (hbase : IsCriticalChainOverTop a θ del Ca CL s S V V U) (Y : F.Cell) :
    (∀ X, IsMinimalChain a S V X → cellShare a S Y X =
      localCellShare a S (referenceFieldChain S V) V Y U fun _ _ => 0) ∧
    minimalCellShare a S Y V = localCellShare a S (referenceFieldChain S V) V Y U fun _ _ => 0 := by
  classical
  have hz : ∀ (y : F.Site F.top) (i : Fin 4),
      ‖(fun _ _ => (0 : imaginaryQuaternions) : F.Site F.top → Fin 4 → imaginaryQuaternions) y i‖ ≤ s :=
    fun _ _ => by simpa using P.s_pos.le
  have hb : IsCriticalChainOverTop a θ del Ca CL s S V (rotatedField (fun _ _ => 0) V) U := by
    rw [rotatedField_zero]
    exact hbase
  have h := (P.reads s _ U P.s_pos P.s_lt.le P.cold hz hb).1
  rw [rotatedField_zero] at h
  refine ⟨fun X hX => h X hX Y, ?_⟩
  have hex := P.exists_minimal V
  unfold minimalCellShare
  rw [dif_pos hex]
  exact h _ hex.choose_spec Y
structure ConstantsDominate (del Cn : ℝ) (Dk Cs N : ℕ → ℝ) : Prop where
  action_le : ∀ m,
    2 * (mixedDerivConstant (fun n => Cs (n + 1)) Dk (Real.exp (del * ((1 : ℕ) : ℝ))) m * Real.exp del) ≤ N (m + 1)
  share_le : ∀ m, mixedDerivConstant Cs Dk (Real.exp (del * ((1 : ℕ) : ℝ))) m ≤ N m
  value_le : Cs 0 * (1 + Cn) ^ 2 ≤ N 0
  first_le : (1 + Cn) * mixedDerivConstant Cs Dk (Real.exp (del * ((1 : ℕ) : ℝ))) 1 ≤ N 1
  pos : ∀ k, 0 < N k
theorem orderedFinpartition_one_length (cP : OrderedFinpartition 1) : cP.length = 1 :=
  le_antisymm cP.length_le (cP.length_pos one_pos)
theorem mixedDerivConstant_scale_first {Cs Dk : ℕ → ℝ} {M w : ℝ} :
    mixedDerivConstant (fun n => if n = 1 then w * Cs 1 else Cs n) Dk M 1 = w * mixedDerivConstant Cs Dk M 1 := by
  unfold mixedDerivConstant
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun cP _ => ?_
  have hl := orderedFinpartition_one_length cP
  have e : Cs cP.length = Cs 1 := by rw [hl]
  show (if cP.length = 1 then w * Cs 1 else Cs cP.length) * _ = _
  rw [if_pos hl, e, mul_assoc]
theorem exp_neg_mul_le_of_le {δ del : ℝ} (hδ : δ ≤ del) (n : ℕ) : Real.exp (-del * n) ≤ Real.exp (-δ * n) := by
  refine Real.exp_le_exp.2 ?_
  have : (0 : ℝ) ≤ n := by positivity
  nlinarith
set_option maxHeartbeats 1000000 in
theorem hasRegularCellShares_of_pair {N : ℕ → ℝ} {Cn δ : ℝ} (P : PairData a θ del Ca rL r' CL σ₀ s Dk Cs S V U)
    (hMix : localMixedDerivStatement) (hTD : localEvaluation_derivAlongRotationStatement)
    (hSum : gaugedCellShareSumStatement) (hLV : minimalChainExistenceStatement)
    (hGauge : gaugeInvarianceOfShareStatement) (hIso : symmetryInvarianceOfShareStatement)
    (ha : 0 < a) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hδ : δ ≤ del)
    (hN : ConstantsDominate del Cn Dk Cs N) (hbase : IsCriticalChainOverTop a θ del Ca CL s S V V U)
    (hturn : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
      AreUnitVectors X →
      ∃ T : (Fin k → ℝ) → ChainChart F, IsRotatedChain a θ del Ca rL r' CL s Dk S V c X U T)
    (hnear : ∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ Cn * s)
    (hval : ∀ Y, |localCellShare a S (referenceFieldChain S V) V Y U fun _ _ => 0| ≤
      Cs 0 * (s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y) ^ 2)
    (hfirst : ∀ (Y : F.Cell) (n : ℕ) (A : Fin n → ChainChart F)
      (e : Fin n → F.Site F.top → Fin 4 → imaginaryQuaternions), n = 1 →
      ‖localIteratedDeriv (localCellShare a S (referenceFieldChain S V) V Y) U A e‖ ≤
        Cs 1 * (s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y) *
          ∏ l, localDirectionSize S (referenceFieldChain S V) (topBondsMeetingCell S Y) Y (A l) (e l)) :
    HasRegularCellShares a δ s N S V := by
  classical
  have hs := P.s_pos
  have hone : ∀ X, IsMinimalChain a S V X → ∀ Y, cellShare a S Y X = minimalCellShare a S Y V := by
    intro X hX Y
    rw [(cellShare_base P hbase Y).1 X hX, (cellShare_base P hbase Y).2]
  refine ⟨?_, ?_, hone, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine isBondAnalyticAt_of_unit fun k c X hk hX => ?_
    obtain ⟨T, hT⟩ := hturn k c X hk hX
    obtain ⟨g, hfg, hga, -⟩ := minimalAction_family P hSum hamb hodd hk hT hX
    exact hga.congr hfg.symm
  · intro Y
    refine isBondAnalyticAt_of_unit fun k c X hk hX => ?_
    obtain ⟨T, hT⟩ := hturn k c X hk hX
    exact (minimalCellShare_family P hMix hk hT hX Y P.evaluationBound_nonneg (P.local_evaluation Y)).1
  · exact fun Y γ => hGauge F a S V γ ha.le hodd hone Y
  · intro g S' V' hg hS hC Y
    exact hIso F a S S' V V' g ha.le hodd hg hS hC hone Y
  · intro k c X hk hX
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    obtain ⟨T, hT⟩ := hturn (m + 1) c X (by omega) hX
    have h1 := minimalAction_iteratedFDeriv_le P hMix hTD hSum hamb hodd (by omega : 1 ≤ m) hT hX
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    exact mul_le_mul (hN.action_le m) (exp_neg_mul_le_of_le hδ _) (Real.exp_pos _).le (hN.pos _).le
  · intro Y k c X hk hX
    obtain ⟨T, hT⟩ := hturn k c X hk hX
    have h1 := (minimalCellShare_family P hMix hk hT hX Y P.evaluationBound_nonneg (P.local_evaluation Y)).2 k
      (Function.Embedding.refl _) hk
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    exact mul_le_mul (hN.share_le k) (exp_neg_mul_le_of_le hδ _) (Real.exp_pos _).le (hN.pos _).le
  · intro Y
    by_cases hY : Y ∈ S
    · have hw : s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y ≤ (1 + Cn) * s := by
        have := hnear Y hY
        linarith
      have hw0 : 0 ≤ s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y :=
        add_nonneg hs.le (Real.sqrt_nonneg _)
      constructor
      · have hex := P.exists_minimal V
        unfold minimalCellShare
        rw [dif_pos hex]
        exact cellShare_nonneg ha.le hLV Y _
      · rw [(cellShare_base P hbase Y).2]
        refine (le_abs_self _).trans ((hval Y).trans ?_)
        have h2 : (s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y) ^ 2 ≤ ((1 + Cn) * s) ^ 2 :=
          pow_le_pow_left₀ hw0 hw 2
        have h3 := mul_le_mul_of_nonneg_left h2 (P.evaluationBound_nonneg 0)
        have h4 := mul_le_mul_of_nonneg_right hN.value_le (sq_nonneg s)
        nlinarith
    · rw [minimalCellShare_of_not_mem hodd hY]
      exact ⟨le_rfl, mul_nonneg (hN.pos 0).le (sq_nonneg s)⟩
  · intro Y c X hX
    by_cases hY : Y ∈ S
    · obtain ⟨T, hT⟩ := hturn 1 c X le_rfl hX
      have hw0 : 0 ≤ s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y :=
        add_nonneg hs.le (Real.sqrt_nonneg _)
      have hw : s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y ≤ (1 + Cn) * s := by
        have := hnear Y hY
        linarith
      obtain ⟨w, hwdef⟩ : ∃ w, w = s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y := ⟨_, rfl⟩
      rw [← hwdef] at hw0 hw
      have hCq : ∀ n, 0 ≤ (fun n => if n = 1 then w * Cs 1 else Cs n) n := by
        intro n
        show 0 ≤ if n = 1 then w * Cs 1 else Cs n
        split_ifs
        · exact mul_nonneg hw0 (P.evaluationBound_nonneg 1)
        · exact P.evaluationBound_nonneg n
      have hl := P.local_evaluation Y
      have hloc : IsLocalRepresentation S (referenceFieldChain S V) Y (topBondsMeetingCell S Y)
          (fun n => if n = 1 then w * Cs 1 else Cs n) U (localCellShare a S (referenceFieldChain S V) V Y) := by
        refine ⟨hl.congr_of_agree, fun A e => hl.analyticAt A e, fun n A e => ?_⟩
        by_cases h1 : n = 1
        · simp only [if_pos h1]
          have := hfirst Y n A e h1
          rw [← hwdef] at this
          rw [mul_comm w]
          exact this
        · simp only [if_neg h1]
          exact hl.iteratedDeriv_le n A e
      have h1 := (minimalCellShare_family P hMix le_rfl hT hX Y hCq hloc).2 1 (Function.Embedding.refl _) le_rfl
      rw [mixedDerivConstant_scale_first] at h1
      rw [Real.norm_eq_abs] at h1
      refine h1.trans ?_
      have h2 : w * mixedDerivConstant Cs Dk (Real.exp (del * ((1 : ℕ) : ℝ))) 1 ≤ N 1 * s := by
        have h3 : 0 ≤ mixedDerivConstant Cs Dk (Real.exp (del * ((1 : ℕ) : ℝ))) 1 :=
          mixedDerivConstant_nonneg P.evaluationBound_nonneg P.chainBound_nonneg (Real.exp_pos _).le 1
        have h4 := mul_le_mul_of_nonneg_right hw h3
        have h5 := mul_le_mul_of_nonneg_right hN.first_le hs.le
        nlinarith
      exact mul_le_mul h2 (exp_neg_mul_le_of_le hδ _) (Real.exp_pos _).le
        (mul_nonneg (hN.pos 1).le hs.le)
    · have e0 : (fun σ : Fin 1 → ℝ => minimalCellShare a S Y (rotatedField (bondSpread c X σ) V)) = fun _ => 0 := by
        funext σ
        exact minimalCellShare_of_not_mem hodd hY _
      have e1 : mixedBondDerivative (minimalCellShare a S Y) V c X = 0 := by
        unfold mixedBondDerivative
        rw [e0]
        simp
      rw [e1, abs_zero]
      have := hN.pos 1
      positivity
end Bounds
theorem ConstantsDominate.mono {del Cn : ℝ} {Dk Cs N N' : ℕ → ℝ} (h : ConstantsDominate del Cn Dk Cs N)
    (hle : ∀ k, N k ≤ N' k) : ConstantsDominate del Cn Dk Cs N' :=
  ⟨fun m => (h.action_le m).trans (hle _), fun m => (h.share_le m).trans (hle _), h.value_le.trans (hle _),
    h.first_le.trans (hle _), fun k => (h.pos k).trans_le (hle k)⟩
section Box
open PatchLocality
variable {F' : BlockFrame} {S' : Finset F'.Cell} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell}
  {Y' : F'.Cell} {r : ℕ}
theorem period_top (F : BlockFrame) (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem valMinAbs_of_withinRadius (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i) (i : Fin 4) {A : ℤ}
    (hA : |A| ≤ (r : ℤ) + 1) :
    ((A : ZMod (F.period F.top i))).valMinAbs = A := by
  apply valMinAbs_intCast_of_small
  rw [period_top]
  rcases hs i with h | h
  · exact Or.inl h
  · right
    have : ((2 * r + 2 : ℕ) : ℤ) < (F.extent i : ℤ) := by exact_mod_cast h
    push_cast at this
    linarith
theorem le_abs_valMinAbs {n : ℕ} {A q : ℤ} (hq : q ≤ |A|) (hn : n = 0 ∨ q + |A| ≤ (n : ℤ)) :
    q ≤ |((A : ZMod n)).valMinAbs| := by
  rcases hn with h0 | hn
  · subst h0
    rw [valMinAbs_intCast_of_small (Or.inl rfl)]
    exact hq
  · have hc : (((A : ZMod n)).valMinAbs : ZMod n) = (A : ZMod n) := ZMod.coe_valMinAbs _
    obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hc
    set w := ((A : ZMod n)).valMinAbs with hw
    by_cases t0 : t = 0
    · have : w = A := by
        rw [t0, mul_zero] at ht
        omega
      rw [this]
      exact hq
    · have h1 : (n : ℤ) ≤ |A - w| := by
        rw [ht, abs_mul, Nat.abs_cast]
        have : 1 ≤ |t| := Int.one_le_abs t0
        nlinarith [Int.natCast_nonneg n]
      have h2 := abs_sub A w
      linarith
theorem le_cellSupDist_of_not_bondWithinRadius (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    {h p : LatticeFractionalIntegration.Lattice4} {r' q : ℕ}
    (hh : ∀ i, |h i| + r' ≤ (r : ℤ)) (hp : WithinRadius r p) (hq : 2 * q ≤ r') {i₀ : Fin 4}
    (hnot : ¬ BondWithinRadius q (p - h, i₀)) :
    q ≤ cellSupDist (Y + siteOfCoords F.top h) (Y + siteOfCoords F.top p) + 1 := by
  have hex : ∃ j, (q : ℤ) ≤ |(p - h) j| + 1 := by
    by_contra hc
    push Not at hc
    apply hnot
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have := hc j
      simp only
      omega
    · have h1 := hc j
      have h2 := abs_add_le ((p - h) j) ((Pi.single i₀ 1 : LatticeFractionalIntegration.Lattice4) j)
      have h3 : |(Pi.single i₀ 1 : LatticeFractionalIntegration.Lattice4) j| ≤ 1 := by
        by_cases e : j = i₀
        · subst e
          simp
        · simp [Pi.single_eq_of_ne e]
      simp only [Pi.add_apply] at h2 ⊢
      omega
  obtain ⟨j, hj⟩ := hex
  set A : ℤ := (p - h) j with hA
  have e : (Y + siteOfCoords F.top h : F.Cell) j - (Y + siteOfCoords F.top p : F.Cell) j =
      ((-A : ℤ) : ZMod (F.period F.top j)) := by
    simp [siteOfCoords, hA]
  have h1 : (((Y + siteOfCoords F.top h : F.Cell) j - (Y + siteOfCoords F.top p : F.Cell) j).valMinAbs).natAbs ≤
      cellSupDist (Y + siteOfCoords F.top h) (Y + siteOfCoords F.top p) :=
    Finset.le_sup (f := fun j =>
      (((Y + siteOfCoords F.top h : F.Cell) j - (Y + siteOfCoords F.top p : F.Cell) j).valMinAbs).natAbs)
      (Finset.mem_univ j)
  rw [e] at h1
  have hAb : |A| ≤ 2 * (r : ℤ) - r' := by
    have a1 := abs_sub (p j) (h j)
    simp only [hA, Pi.sub_apply]
    linarith [hh j, hp j]
  have h2 : (q : ℤ) - 1 ≤ |((-A : ℤ) : ZMod (F.period F.top j)).valMinAbs| := by
    refine le_abs_valMinAbs (by rw [abs_neg]; omega) ?_
    rw [period_top]
    rcases hs j with h0 | h0
    · exact Or.inl h0
    · right
      have : ((2 * r + 2 : ℕ) : ℤ) < (F.extent j : ℤ) := by exact_mod_cast h0
      push_cast at this
      rw [abs_neg]
      omega
  rw [Int.abs_eq_natAbs] at h2
  have h3 : ((((-A : ℤ) : ZMod (F.period F.top j)).valMinAbs).natAbs : ℤ) ≤
      (cellSupDist (Y + siteOfCoords F.top h) (Y + siteOfCoords F.top p) : ℤ) := by exact_mod_cast h1
  have : (q : ℤ) ≤ (cellSupDist (Y + siteOfCoords F.top h) (Y + siteOfCoords F.top p) : ℤ) + 1 := by omega
  exact_mod_cast this
theorem half_radius_le_cellSupDist (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    {p : LatticeFractionalIntegration.Lattice4} (hp : WithinRadius r p) {i₀ : Fin 4}
    (hnot : ¬ BondWithinRadius (r / 2) (p, i₀)) : r / 2 ≤ cellSupDist Y (Y + siteOfCoords F.top p) + 1 := by
  have h := le_cellSupDist_of_not_bondWithinRadius (Y := Y) hs (h := 0) (p := p) (r' := r) (q := r / 2)
    (fun i => by simp) hp (by omega) (i₀ := i₀) (by simpa using hnot)
  simpa [siteOfCoords_zero] using h
theorem half_radius_le_bondListDistance (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i) {k : ℕ}
    {h : Fin k → (Fin 4 → ℤ) × Fin 4}
    (hb : ∀ l, BondWithinRadius r (h l)) {l : Fin k} (hnot : ¬ BondWithinRadius (r / 2) (h l)) :
    r / 2 ≤ bondListDistance Y (offsetBonds Y h) + 1 := by
  have h1 := half_radius_le_cellSupDist (Y := Y) hs (hb l).1 (i₀ := (h l).2) hnot
  have h2 : cellSupDist Y (offsetBonds Y h l).1 ≤ bondListDistance Y (offsetBonds Y h) :=
    Finset.le_sup (f := fun l => cellSupDist Y (offsetBonds Y h l).1) (Finset.mem_univ l)
  have h3 : (offsetBonds Y h l).1 = Y + siteOfCoords F.top (h l).1 := rfl
  rw [h3] at h2
  omega
theorem abs_valMinAbs_offset_le_one {b : F.Cell} (hb : cellSupDist Y b ≤ 1) (i : Fin 4) :
    |((b - Y) i).valMinAbs| ≤ 1 := by
  have h1 : (((Y i - b i).valMinAbs).natAbs) ≤ cellSupDist Y b :=
    Finset.le_sup (f := fun i => ((Y i - b i).valMinAbs).natAbs) (Finset.mem_univ i)
  have e : (b - Y) i = -(Y i - b i) := by simp
  rw [e, Int.abs_eq_natAbs, ZMod.natAbs_valMinAbs_neg]
  exact_mod_cast h1.trans hb
theorem eq_add_siteOfCoords_offset (b : F.Cell) : b = Y + siteOfCoords F.top fun i => ((b - Y) i).valMinAbs := by apply _root_.YangMills.Construction.PatchPoints.eq_add_siteOfCoords_cellDisplacement <;> assumption
theorem offset_eq_iff_cellAtSameOffset (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    (hs' : ∀ i, F'.extent i = 0 ∨ 2 * r + 2 < F'.extent i) {p : LatticeFractionalIntegration.Lattice4}
    (hp : WithinRadius r p) {b : F.Cell} (hb : cellSupDist Y b ≤ 1)
    (hr : 1 ≤ r) : Y + siteOfCoords F.top p = b ↔ Y' + siteOfCoords F'.top p = cellAtSameOffset Y Y' b := by
  have ho := abs_valMinAbs_offset_le_one hb
  have e0 := eq_add_siteOfCoords_offset (Y := Y) b
  set o : LatticeFractionalIntegration.Lattice4 := fun i => ((b - Y) i).valMinAbs with hodef
  have hor : ∀ i, |o i| ≤ (r : ℤ) + 1 := fun i => by
    have := ho i
    have h1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
    linarith
  have hpr : ∀ i, |p i| ≤ (r : ℤ) + 1 := fun i => by
    have := hp i
    linarith
  have key : ∀ {G : BlockFrame} (_ : ∀ i, G.extent i = 0 ∨ 2 * r + 2 < G.extent i) (Z : G.Cell),
      Z + siteOfCoords G.top p = Z + siteOfCoords G.top o ↔ p = o := by
    intro G hG Z
    constructor
    · intro h
      have h2 := add_left_cancel h
      funext i
      have h3 := congrFun h2 i
      have h4 := congrArg ZMod.valMinAbs h3
      simp only [siteOfCoords] at h4
      rwa [valMinAbs_of_withinRadius hG i (hpr i), valMinAbs_of_withinRadius hG i (hor i)] at h4
    · rintro rfl
      rfl
  constructor
  · intro h
    have h1 : Y + siteOfCoords F.top p = Y + siteOfCoords F.top o := by
      rw [h]
      exact e0
    rw [(key hs Y).1 h1]
    rfl
  · intro h
    have h1 : Y' + siteOfCoords F'.top p = Y' + siteOfCoords F'.top o := h
    rw [(key hs' Y').1 h1]
    exact e0.symm
end Box
section Compare
open ChartCoordinates
theorem mixedBondDerivative_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : F.GaugeField F.top → E)
    (V : F.GaugeField F.top) (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    mixedBondDerivative G V c X = G V := by
  unfold mixedBondDerivative
  rw [iteratedFDeriv_zero_apply, bondSpread_zero, rotatedField_zero]
theorem mixedBondDerivative_of_not_mem (hodd : Odd F.blockSide) {a : ℝ} {Y : F.Cell} (hY : Y ∉ S)
    (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    mixedBondDerivative (minimalCellShare a S Y) V c X = 0 := by
  have e0 : (fun σ : Fin k → ℝ => minimalCellShare a S Y (rotatedField (bondSpread c X σ) V)) = fun _ => 0 := by
    funext σ
    exact minimalCellShare_of_not_mem hodd hY _
  unfold mixedBondDerivative
  rw [e0]
  simp
theorem derivativeScale_nonneg {s : ℝ} (hs : 0 ≤ s) (k : ℕ) : 0 ≤ derivativeScale s k := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.derivativeScale_nonneg <;> assumption
theorem abs_mixedBondDerivative_le {a δ s : ℝ} {N : ℕ → ℝ} {V : F.GaugeField F.top}
    (H : HasRegularCellShares a δ s N S V) (hs : 0 < s)
    (Y : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) :
    |mixedBondDerivative (minimalCellShare a S Y) V c X| ≤
      derivativeScale s k * N k * Real.exp (-δ * bondListDistance Y c) := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9⟩ := H
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have e : bondListDistance Y c = 0 := by
      unfold bondListDistance
      simp
    rw [mixedBondDerivative_zero, e, abs_of_nonneg (h8 Y).1]
    simp only [derivativeScale, if_true, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    rw [mul_comm]
    exact (h8 Y).2
  · by_cases h1 : k = 1
    · subst h1
      have := h9 Y c X hX
      simp only [derivativeScale, one_ne_zero, if_false, if_true]
      rw [mul_comm s]
      exact this
    · have := h7 Y k c X hk hX
      have e : derivativeScale s k = 1 := by
        simp [derivativeScale, h1, hk.ne']
      rw [e, one_mul]
      exact this
theorem topVariationNorm_partSpread_le {k p : ℕ} (B : Finset (F.Site F.top × Fin 4)) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) {M : ℝ} (hM : 1 ≤ M) (hp : 1 ≤ p)
    (f : Fin p ↪ Fin k) :
    topVariationNorm B (partSpread c X f) ≤ M := by
  classical
  unfold partSpread
  by_cases h1 : p = 1
  · subst h1
    have e : iteratedFDeriv ℝ 1 (fun ζ : Fin k → ℝ => ζ) 0 (fun l => Pi.single (f l) 1) = Pi.single (f 0) 1 := by
      rw [iteratedFDeriv_one_apply]
      have : fderiv ℝ (fun ζ : Fin k → ℝ => ζ) 0 = ContinuousLinearMap.id ℝ _ := fderiv_fun_id
      rw [this]
      rfl
    rw [e]
    exact (topVariationNorm_single_le B c X hX (f 0)).trans hM
  · have h2 : 2 ≤ p := by omega
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have e : fderiv ℝ (fun ζ : Fin k → ℝ => ζ) = fun _ => ContinuousLinearMap.id ℝ _ := by
      funext y
      exact fderiv_fun_id
    have hq : q ≠ 0 := by omega
    have e0 : iteratedFDeriv ℝ (q + 1) (fun ζ : Fin k → ℝ => ζ) 0 = 0 := by
      rw [iteratedFDeriv_succ_eq_comp_right, e]
      simp [Function.comp_def, iteratedFDeriv_const_of_ne hq]
    rw [e0]
    simp only [ContinuousMultilinearMap.zero_apply]
    rw [bondSpread_zero]
    simp only [topVariationNorm, norm_zero, Finset.sum_const_zero]
    linarith
theorem localIteratedDeriv_congr {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    {Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E} {U : ChainChart F}
    (hΦ : ∀ U' U'' v, ChartEqOnBonds S U' U'' → Φ U' v = Φ U'' v) {A A' : Fin m → ChainChart F}
    (e : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions) (h : ∀ l, ChartEqOnBonds S (A l) (A' l)) :
    localIteratedDeriv Φ U A e = localIteratedDeriv Φ U A' e := by
  unfold localIteratedDeriv
  congr 2
  funext t
  refine hΦ _ _ _ ⟨fun b hb => ?_, fun j hj c hc => ?_⟩
  · simp only [chartShiftAlong]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [(h l).1 b hb]
  · simp only [chartShiftAlong]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [(h l).2 j hj c hc]
theorem norm_sub_first_deriv_le {F' : BlockFrame} {S' : Finset F'.Cell} {R : F.FieldChain} {R' : F'.FieldChain}
    {Y : F.Cell} {Y' : F'.Cell}
    {B : Finset (F.Site F.top × Fin 4)} {B' : Finset (F'.Site F'.top × Fin 4)} {Ck Ck' Dk : ℕ → ℝ}
    {C₁ w G E₀ del : ℝ}
    {U : ChainChart F} {U' : ChainChart F'}
    {Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → ℝ}
    {Φ' : ChainChart F' → (F'.Site F'.top → Fin 4 → imaginaryQuaternions) → ℝ}
    {c : Fin 1 → F.Site F.top × Fin 4} {c' : Fin 1 → F'.Site F'.top × Fin 4} {X : Fin 1 → imaginaryQuaternions}
    {T : (Fin 1 → ℝ) → ChainChart F} {T' : (Fin 1 → ℝ) → ChainChart F'}
    (hMix : localMixedDerivStatement) (hdel : 0 ≤ del) (hCk : ∀ m, 0 ≤ Ck m) (hCk' : ∀ m, 0 ≤ Ck' m)
    (hDk : ∀ m, 0 ≤ Dk m) (hC₁ : 0 ≤ C₁) (hw : 0 ≤ w) (hG : 0 ≤ G) (hE₀ : 0 ≤ E₀)
    (hΦ : IsLocalRepresentation S R Y B Ck U Φ) (hΦ' : IsLocalRepresentation S' R' Y' B' Ck' U' Φ')
    (hfirst : ∀ (n : ℕ) (A : Fin n → ChainChart F) (A' : Fin n → ChainChart F')
      (e : Fin n → F.Site F.top → Fin 4 → imaginaryQuaternions)
      (e' : Fin n → F'.Site F'.top → Fin 4 → imaginaryQuaternions), n = 1 →
      (∀ l, ∀ b ∈ B, e l b.1 b.2 = e' l (cellAtSameOffset Y Y' b.1) b.2) →
      ‖localIteratedDeriv Φ U A e - localIteratedDeriv Φ' U' A' e'‖ ≤
        C₁ * (offsetChartGapNorm S R Y Y Y' U U' * ∏ l, localDirectionSize S R B Y (A l) (e l) +
          w * ∑ l, offsetChartGapNorm S R Y Y Y' (A l) (A' l)))
    (hX : AreUnitVectors X) (hB : ∀ b ∈ B, cellSupDist Y b.1 ≤ 1) (hB' : ∀ b ∈ B', cellSupDist Y' b.1 ≤ 1)
    (h0 : ChartEqOnBonds S (T 0) U) (h0' : ChartEqOnBonds S' (T' 0) U')
    (hu : ∀ b ∈ innerBonds S 0, AnalyticAt ℝ (fun ζ => (T ζ).fine b.1 b.2) 0)
    (hmu : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1), AnalyticAt ℝ (fun ζ => (T ζ).coarse j b.1 b.2) 0)
    (hu' : ∀ b ∈ innerBonds S' 0, AnalyticAt ℝ (fun ζ => (T' ζ).fine b.1 b.2) 0)
    (hmu' : ∀ j, j + 1 < F'.top → ∀ b ∈ innerBonds S' (j + 1),
      AnalyticAt ℝ (fun ζ => (T' ζ).coarse j b.1 b.2) 0)
    (hdec : ∀ (m : ℕ) (e : Fin m ↪ Fin 1), 1 ≤ m →
      localNorm S R (mixedDerivativeChart T e) (oneSiteWeights F) Y ≤
        Dk m * Real.exp (-del * bondListDistance Y (c ∘ e)))
    (hdec' : ∀ (m : ℕ) (e : Fin m ↪ Fin 1), 1 ≤ m →
      localNorm S' R' (mixedDerivativeChart T' e) (oneSiteWeights F') Y' ≤
        Dk m * Real.exp (-del * bondListDistance Y' (c' ∘ e)))
    (hgU : offsetChartGapNorm S R Y Y Y' U U' ≤ G)
    (hgA : ∀ (m : ℕ) (e : Fin m ↪ Fin 1), 1 ≤ m →
      offsetChartGapNorm S R Y Y Y' (mixedDerivativeChart T e) (mixedDerivativeChart T' e) ≤ Dk m * E₀)
    (hturn : ∀ l, ∀ b ∈ B, c l = b ↔ c' l = (cellAtSameOffset Y Y' b.1, b.2)) :
    ‖iteratedFDeriv ℝ 1 (fun ζ : Fin 1 → ℝ => Φ (T ζ) (bondSpread c X ζ)) 0 (fun l => Pi.single l 1) -
        iteratedFDeriv ℝ 1 (fun ζ : Fin 1 → ℝ => Φ' (T' ζ) (bondSpread c' X ζ)) 0 (fun l => Pi.single l 1)‖ ≤
      ∑ cP : OrderedFinpartition 1, C₁ * (G * ∏ i, (Dk (cP.partSize i) + Real.exp (del * ((1 : ℕ) : ℝ))) +
        w * ∑ l, Dk (cP.partSize l) * E₀) := by
  classical
  obtain ⟨-, hexp, -⟩ := hMix F ℝ S R Y B Ck Dk U Φ del 1 1 c X T hdel hCk hDk hΦ hX hB h0 hu hmu hdec
  obtain ⟨-, hexp', -⟩ :=
    hMix F' ℝ S' R' Y' B' Ck' Dk U' Φ' del 1 1 c' X T' hdel hCk' hDk hΦ' hX hB' h0' hu' hmu' hdec'
  obtain ⟨A, hA, hE⟩ := hexp 1 (Function.Embedding.refl _) le_rfl
  obtain ⟨A', hA', hE'⟩ := hexp' 1 (Function.Embedding.refl _) le_rfl
  have hE1 : iteratedFDeriv ℝ 1 (fun ζ : Fin 1 → ℝ => Φ (T ζ) (bondSpread c X ζ)) 0
      (fun l => Pi.single l 1) = _ := hE
  have hE2 : iteratedFDeriv ℝ 1 (fun ζ : Fin 1 → ℝ => Φ' (T' ζ) (bondSpread c' X ζ)) 0
      (fun l => Pi.single l 1) = _ := hE'
  rw [hE1, hE2, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun cP _ => ?_)
  rw [localIteratedDeriv_congr hΦ.congr_of_agree _ (hA cP), localIteratedDeriv_congr hΦ'.congr_of_agree _ (hA' cP)]
  set M : ℝ := Real.exp (del * ((1 : ℕ) : ℝ)) with hMdef
  have hM1 : 1 ≤ M := Real.one_le_exp (by positivity)
  have hte : ∀ l, ∀ b ∈ B, partSpread c X (partEmbedding (Function.Embedding.refl _) cP l) b.1 b.2 =
      partSpread c' X (partEmbedding (Function.Embedding.refl _) cP l) (cellAtSameOffset Y Y' b.1) b.2 := by
    intro l b hb
    simp only [partSpread, bondSpread]
    refine Finset.sum_congr rfl fun l' _ => ?_
    have h1 := hturn l' b hb
    have h2 : c l' = (b.1, b.2) ↔ c' l' = (cellAtSameOffset Y Y' b.1, b.2) := h1
    by_cases h3 : c l' = (b.1, b.2)
    · rw [if_pos h3, if_pos (h2.1 h3)]
    · rw [if_neg h3, if_neg (fun h4 => h3 (h2.2 h4))]
  refine (hfirst _ _ _ _ _ (orderedFinpartition_one_length cP) hte).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hC₁
  have hslot : ∀ i, localDirectionSize S R B Y
      (mixedDerivativeChart T (partEmbedding (Function.Embedding.refl _) cP i))
      (partSpread c X (partEmbedding (Function.Embedding.refl _) cP i)) ≤ Dk (cP.partSize i) + M := by
    intro i
    have hp : 1 ≤ cP.partSize i := cP.partSize_pos i
    have h1 := hdec _ (partEmbedding (Function.Embedding.refl _) cP i) hp
    have h2 : Real.exp (-del * bondListDistance Y (c ∘ partEmbedding (Function.Embedding.refl _) cP i)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by
        have : (0 : ℝ) ≤ bondListDistance Y (c ∘ partEmbedding (Function.Embedding.refl _) cP i) := by
          positivity
        nlinarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (hDk (cP.partSize i))
    unfold localDirectionSize
    exact add_le_add (by linarith) (topVariationNorm_partSpread_le B c X hX hM1 hp _)
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ hw)
  · exact mul_le_mul hgU
      (Finset.prod_le_prod (fun i _ => localDirectionSize_nonneg _ _ _ _ _) fun i _ => hslot i)
      (Finset.prod_nonneg fun i _ => localDirectionSize_nonneg _ _ _ _ _) hG
  · exact Finset.sum_le_sum fun l _ => hgA _ _ (cP.partSize_pos l)
end Compare
end AnalyticCellShares
open AnalyticCellShares PatchLocality in
set_option maxHeartbeats 4000000 in
theorem analyticCellSharesStatement_of_parts (hCrit : rotatedCriticalChainsStatement)
    (hMix : localMixedDerivStatement) (hCmp : comparedMixedDerivStatement)
    (hTD : localEvaluation_derivAlongRotationStatement) (hSum : gaugedCellShareSumStatement)
    (hNear : splitChartNearCellStatement) (hLV : minimalChainExistenceStatement)
    (hGauge : gaugeInvarianceOfShareStatement) (hIso : symmetryInvarianceOfShareStatement)
    (hLoc : shareLocalityStatement) (hRead : minimalChainShareEqAverageStatement)
    (hVal : criticalValueEqMinimalActionStatement) (hAg : agreeingPairsShareComparisonStatement) :
    analyticCellSharesStatement := by
  classical
  intro a ha
  obtain ⟨θ, del, Ca, hθ, hθ8, hd, hd8, hCa, L₁, hC⟩ := hCrit a ha
  obtain ⟨L₂, hR⟩ := hRead a θ del Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₃, hV⟩ := hVal a θ del Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₄, hL⟩ := hLoc a ha
  obtain ⟨L₅, hA⟩ := hAg a ha
  refine ⟨del / 4, by positivity, fun δ hδ hδ4 => ⟨max L₁ (max L₂ (max L₃ (max L₄ L₅))), fun L hLo hge => ?_⟩⟩
  have g1 : L₁ ≤ L := le_of_max_le_left hge
  have g2 : L₂ ≤ L := le_of_max_le_left (le_of_max_le_right hge)
  have g3 : L₃ ≤ L := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hge))
  have g4 : L₄ ≤ L := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hge)))
  have g5 : L₅ ≤ L := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hge)))
  obtain ⟨rL, r', sL, CL, Ck, hrL, hr'0, hr'rL, hsL, hCL, hCk, hcrit, hcomp⟩ := hC L hLo g1
  obtain ⟨σ₁, hσ₁, hr1⟩ := hR L hLo g2 CL hCL
  obtain ⟨σ₂, hσ₂, hv⟩ := hV L hLo g3 CL hCL
  obtain ⟨c₁, Cs, hc₁, hCs, hloc⟩ := hL L hLo g4
  obtain ⟨c₂, r₀, Cm, hc₂, hCm, hagr⟩ := hA L hLo g5
  have hCk0 : ∀ m, 0 ≤ Ck m := fun m => (hCk m).le
  set M : ℝ := Real.exp (del * ((1 : ℕ) : ℝ)) with hM
  have hM0 : 0 ≤ M := (Real.exp_pos _).le
  obtain ⟨Cn, hCnv⟩ : ∃ Cn : ℝ, Cn = 2 * Ca + 2 * CL := ⟨_, rfl⟩
  have hCn : 0 < Cn := by
    rw [hCnv]
    positivity
  obtain ⟨cN, hcNv⟩ : ∃ cN : ℝ, cN = min c₁ c₂ := ⟨_, rfl⟩
  have hcN : 0 < cN := by
    rw [hcNv]
    exact lt_min hc₁ hc₂
  obtain ⟨σ₀, hσ₀v⟩ : ∃ σ₀ : ℝ, σ₀ = min σ₁ σ₂ := ⟨_, rfl⟩
  have hσ₀ : 0 < σ₀ := by
    rw [hσ₀v]
    exact lt_min hσ₁ hσ₂
  obtain ⟨σ, hσv⟩ : ∃ σ : ℝ, σ = min (min sL (σ₀ / 2)) (min 1 (min cN (cN / Cn))) := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by
    rw [hσv]
    exact lt_min (lt_min hsL (by positivity)) (lt_min one_pos (lt_min hcN (by positivity)))
  have hRc0 : ∀ k, 0 ≤ mixedDerivConstant Cs Ck M k := mixedDerivConstant_nonneg hCs hCk0 hM0
  have hRa0 : ∀ k, 0 ≤ mixedDerivConstant (fun n => Cs (n + 1)) Ck M k :=
    mixedDerivConstant_nonneg (fun n => hCs _) hCk0 hM0
  have hT0 : 0 ≤ Cs 0 * (1 + Cn) ^ 2 := mul_nonneg (hCs 0) (sq_nonneg _)
  have hT1 : 0 ≤ (1 + Cn) * mixedDerivConstant Cs Ck M 1 := mul_nonneg (by linarith) (hRc0 1)
  have hed : 0 ≤ Real.exp del := (Real.exp_pos _).le
  obtain ⟨N₁, hN₁v⟩ : ∃ N₁ : ℕ → ℝ, N₁ = fun k => 1 + mixedDerivConstant Cs Ck M k +
      2 * (mixedDerivConstant (fun n => Cs (n + 1)) Ck M (k - 1) * Real.exp del) + Cs 0 * (1 + Cn) ^ 2 +
      (1 + Cn) * mixedDerivConstant Cs Ck M 1 := ⟨_, rfl⟩
  have hN₁pos : ∀ k, 0 < N₁ k := by
    intro k
    rw [hN₁v]
    have h1 := hRc0 k
    have h2 := mul_nonneg (hRa0 (k - 1)) hed
    show 0 < 1 + mixedDerivConstant Cs Ck M k +
      2 * (mixedDerivConstant (fun n => Cs (n + 1)) Ck M (k - 1) * Real.exp del) + Cs 0 * (1 + Cn) ^ 2 +
      (1 + Cn) * mixedDerivConstant Cs Ck M 1
    linarith
  have hN₁fit : ConstantsDominate del Cn Ck Cs N₁ := by
    refine ⟨fun m => ?_, fun m => ?_, ?_, ?_, hN₁pos⟩
    · rw [hN₁v]
      have h1 := hRc0 (m + 1)
      simp only [Nat.add_sub_cancel]
      linarith
    · rw [hN₁v]
      have h2 := mul_nonneg (hRa0 (m - 1)) hed
      simp only []
      linarith
    · rw [hN₁v]
      have h1 := hRc0 0
      have h2 := mul_nonneg (hRa0 (0 - 1)) hed
      simp only []
      linarith
    · rw [hN₁v]
      have h1 := hRc0 1
      have h2 := mul_nonneg (hRa0 (1 - 1)) hed
      simp only []
      linarith
  obtain ⟨r₁, hr₁v⟩ : ∃ r₁ : ℕ, r₁ = max r₀ 108 := ⟨_, rfl⟩
  obtain ⟨E, hEv⟩ : ∃ E : ℝ, E = Real.exp (del * ((r₁ : ℝ) + 3)) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by
    rw [hEv]
    exact Real.one_le_exp (by positivity)
  obtain ⟨W, hWv⟩ : ∃ W : ℝ, W = 1 + 2 * Cn := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWv]
    positivity
  obtain ⟨Dc, hDcv⟩ : ∃ Dc : ℕ → ℝ, Dc = fun k => comparisonConstant Cm Ck M
      (CL + ∑ m ∈ Finset.range (k + 1), Ck m) k * (CL + ∑ m ∈ Finset.range (k + 1), Ck m) := ⟨_, rfl⟩
  have hDc0 : ∀ k, 0 ≤ Dc k := by
    intro k
    rw [hDcv]
    have hG0 : 0 ≤ CL + ∑ m ∈ Finset.range (k + 1), Ck m :=
      add_nonneg hCL.le (Finset.sum_nonneg fun m _ => hCk0 m)
    refine mul_nonneg (Finset.sum_nonneg fun c _ => mul_nonneg (hCm _) ?_) hG0
    exact add_nonneg (Finset.prod_nonneg fun i _ => add_nonneg (hCk0 _) hM0)
      (Finset.sum_nonneg fun l _ => Finset.prod_nonneg fun i _ => add_nonneg (add_nonneg (hCk0 _) hM0) hG0)
  obtain ⟨Cf, hCfv⟩ : ∃ Cf : ℝ, Cf = ∑ cP : OrderedFinpartition 1, Cm 1 *
      (CL * ∏ i, (Ck (cP.partSize i) + M) + W * ∑ l, Ck (cP.partSize l)) := ⟨_, rfl⟩
  have hCf0 : 0 ≤ Cf := by
    rw [hCfv]
    refine Finset.sum_nonneg fun cP _ => mul_nonneg (hCm 1) (add_nonneg (mul_nonneg hCL.le ?_)
      (mul_nonneg hW0 (Finset.sum_nonneg fun l _ => hCk0 _)))
    exact Finset.prod_nonneg fun i _ => add_nonneg (hCk0 _) hM0
  have hK0 : 0 ≤ Cm 0 * W * CL := mul_nonneg (mul_nonneg (hCm 0) hW0) hCL.le
  obtain ⟨N, hNv⟩ : ∃ N : ℕ → ℝ, N = fun k => N₁ k + 2 * (N₁ k * E) + Dc k + Cf + Cm 0 * W * CL := ⟨_, rfl⟩
  have hNge : ∀ k, N₁ k + 2 * (N₁ k * E) ≤ N k := by
    intro k
    rw [hNv]
    have := hDc0 k
    simp only []
    linarith
  have hNle : ∀ k, N₁ k ≤ N k := by
    intro k
    have h1 := hNge k
    have h2 : 0 ≤ N₁ k * E := mul_nonneg (hN₁pos k).le (by linarith)
    linarith
  have hNfit : ConstantsDominate del Cn Ck Cs N := hN₁fit.mono hNle
  have hNpos : ∀ k, 0 < N k := hNfit.pos
  have pair : ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ σ → IsCold S F.top s V →
      ∃ U : ChainChart F, IsSliceCriticalPoint a θ del Ca rL CL s S V U ∧
        PairData a θ del Ca rL r' CL σ₀ s Ck Cs S V U ∧ IsCriticalChainOverTop a θ del Ca CL s S V V U ∧
        (∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ Cn * s) ∧
        (∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ cN) ∧
        (∀ Y, |localCellShare a S (referenceFieldChain S V) V Y U fun _ _ => 0| ≤
          Cs 0 * (s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y) ^ 2) ∧
        (∀ (Y : F.Cell) (n : ℕ) (A : Fin n → ChainChart F)
          (e : Fin n → F.Site F.top → Fin 4 → imaginaryQuaternions), n = 1 →
          ‖localIteratedDeriv (localCellShare a S (referenceFieldChain S V) V Y) U A e‖ ≤
            Cs 1 * (s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y) *
              ∏ l, localDirectionSize S (referenceFieldChain S V) (topBondsMeetingCell S Y) Y (A l) (e l)) ∧
        ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
          AreUnitVectors X →
          ∃ T : (Fin k → ℝ) → ChainChart F, IsRotatedChain a θ del Ca rL r' CL s Ck S V c X U T := by
    intro F m S hFL hamb hm hreg s V hs hsσ hcold
    rw [hσv] at hsσ
    have s1 : s ≤ sL := hsσ.trans ((min_le_left _ _).trans (min_le_left _ _))
    have s2 : s ≤ σ₀ / 2 := hsσ.trans ((min_le_left _ _).trans (min_le_right _ _))
    have s3 : s ≤ 1 := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have s4 : s ≤ cN := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have s5 : s ≤ cN / Cn := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    obtain ⟨U, hU, hB, hfam⟩ := hcrit F m S hFL hamb hm hreg s V hs s1 hcold
    have hn : ∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ Cn * s := by
      intro z hz
      obtain ⟨Ul, Ur, hsame, hbd⟩ := hU.split
      obtain ⟨x1, x2⟩ := hbd 0 z 0 (Or.inr rfl)
      have h1 := hNear F S (referenceFieldChain S V) U Ul Ur del (Ca * s) (CL * s ^ 2) z hz hd.le hd8 hsame x1 x2
      have h2 : CL * s ^ 2 ≤ CL * s := by
        refine mul_le_mul_of_nonneg_left ?_ hCL.le
        nlinarith
      rw [hCnv]
      nlinarith
    have hn2 : ∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ cN := by
      intro z hz
      refine (hn z hz).trans ?_
      rw [le_div_iff₀ hCn] at s5
      linarith
    have hc1 : cN ≤ c₁ := by
      rw [hcNv]
      exact min_le_left _ _
    have hl := hloc F m S hFL hamb hm hreg s V hs (s4.trans hc1) hcold U (fun z hz => (hn2 z hz).trans hc1)
    have hreads : ReadsRotatedTops a θ del Ca CL σ₀ S V := fun s' v U' h1 h2 h3 h4 h5 =>
      ⟨fun X hX Y => hr1 F m S hFL hamb hm hreg s' V v h1
          (h2.trans (by rw [hσ₀v]; exact min_le_left _ _)) h3 h4 U' h5 X hX Y,
        (hv F m S hFL hamb hm hreg s' V v h1 (h2.trans (by rw [hσ₀v]; exact min_le_right _ _)) h3 h4 U' h5).1⟩
    have hmin : ∀ V' : F.GaugeField F.top, ∃ X, IsMinimalChain a S V' X := fun V' => by
      obtain ⟨X, hX, -⟩ := (hLV F a S ha.le).2.2.2 V'
      exact ⟨X, hX⟩
    refine ⟨U, hU, ⟨hs, by linarith, hr'0, hd.le, hcold, hCk0, hCs, hreads, hmin, fun Y => (hl Y).1⟩,
      ⟨hU.critical, hU.split, hB.quartic, hB.curvature_and_misfits, hB.misfits_on_cells⟩, hn, hn2,
      fun Y => (hl Y).2.1, fun Y => (hl Y).2.2, hfam⟩
  refine ⟨σ, N, hσ0, hNpos, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsσ hcold
  have hodd : Odd F.blockSide := hFL ▸ hLo
  obtain ⟨U, hU, P, hbase, hn, hn2, hval, hfirst, hturn⟩ := pair F m S hFL hamb hm hreg s V hs hsσ hcold
  have hδ1 : δ ≤ del := by linarith
  have hδ2 : 2 * δ ≤ del := by linarith
  refine ⟨hasRegularCellShares_of_pair P hMix hTD hSum hLV hGauge hIso ha hamb hodd hδ1 hNfit hbase hturn hn hval
    hfirst, ?_⟩
  intro F' S' V' Y Y' r hF'L ht hamb' hreg' hcold' hag
  have hodd' : Odd F'.blockSide := hF'L ▸ hLo
  obtain ⟨U', hU', P', hbase', hn', hn2', hval', hfirst', hturn'⟩ :=
    pair F' m S' hF'L hamb' hm hreg' s V' hs hsσ hcold'
  have H := hasRegularCellShares_of_pair P hMix hTD hSum hLV hGauge hIso ha hamb hodd hδ2 hN₁fit hbase hturn hn
    hval hfirst
  have H' := hasRegularCellShares_of_pair P' hMix hTD hSum hLV hGauge hIso ha hamb' hodd' hδ2 hN₁fit hbase' hturn'
    hn' hval' hfirst'
  intro k h X hh hX
  have hs1 := hag.1
  have hs2 := hag.2.1
  have hfac := derivativeScale_nonneg hs.le k
  have hσs : s ≤ 1 := by
    rw [hσv] at hsσ
    exact hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hexp := Real.exp_pos (-δ * (r : ℝ))
  by_cases hYS : Y ∈ S
  swap
  · have hY' : Y' ∉ S' := by
      intro h'
      apply hYS
      have := (hag.2.2.1 0 (fun i => by simp)).2
      rw [siteOfCoords_zero, siteOfCoords_zero, add_zero, add_zero] at this
      exact this h'
    rw [mixedBondDerivative_of_not_mem hodd hYS, mixedBondDerivative_of_not_mem hodd' hY', sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hfac (hNpos k).le) hexp.le
  have hYS' : Y' ∈ S' := by
    have := (hag.2.2.1 0 (fun i => by simp)).1
    rw [siteOfCoords_zero, siteOfCoords_zero, add_zero, add_zero] at this
    exact this hYS
  have far : ∀ d₀ : ℕ, d₀ ≤ bondListDistance Y (offsetBonds Y h) → d₀ ≤ bondListDistance Y' (offsetBonds Y' h) →
      Real.exp (-(2 * δ) * d₀) ≤ E * Real.exp (-δ * r) →
      |mixedBondDerivative (minimalCellShare a S Y) V (offsetBonds Y h) X -
        mixedBondDerivative (minimalCellShare a S' Y') V' (offsetBonds Y' h) X| ≤
        derivativeScale s k * N k * Real.exp (-δ * r) := by
    intro d₀ h1 h2 h3
    have b1 := abs_mixedBondDerivative_le H hs Y (offsetBonds Y h) X hX
    have b2 := abs_mixedBondDerivative_le H' hs Y' (offsetBonds Y' h) X hX
    have mono : ∀ d : ℕ, d₀ ≤ d → Real.exp (-(2 * δ) * d) ≤ Real.exp (-(2 * δ) * d₀) := by
      intro d hd'
      refine Real.exp_le_exp.2 ?_
      have : (d₀ : ℝ) ≤ d := by exact_mod_cast hd'
      nlinarith
    have hfN : 0 ≤ derivativeScale s k * N₁ k := mul_nonneg hfac (hN₁pos k).le
    have c1 := b1.trans (mul_le_mul_of_nonneg_left ((mono _ h1).trans h3) hfN)
    have c2 := b2.trans (mul_le_mul_of_nonneg_left ((mono _ h2).trans h3) hfN)
    have c3 := abs_sub (mixedBondDerivative (minimalCellShare a S Y) V (offsetBonds Y h) X)
      (mixedBondDerivative (minimalCellShare a S' Y') V' (offsetBonds Y' h) X)
    refine c3.trans ((add_le_add c1 c2).trans ?_)
    have c4 : 2 * (N₁ k * E) ≤ N k := by
      have := hNge k
      have := hN₁pos k
      linarith
    have c5 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left c4 hfac) hexp.le
    nlinarith
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hd0 : 0 ≤ del := hd.le
  have hr1pos : (0 : ℝ) ≤ r₁ := by positivity
  by_cases hr : r < r₁
  · refine far 0 (Nat.zero_le _) (Nat.zero_le _) ?_
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero]
    rw [hEv, ← Real.exp_add]
    refine Real.one_le_exp ?_
    have h1 : (r : ℝ) ≤ r₁ := by exact_mod_cast hr.le
    nlinarith
  have hr' : r₁ ≤ r := not_lt.1 hr
  have h108 : 108 ≤ r := (le_max_right _ _).trans (hr₁v ▸ hr')
  have hr0' : r₀ ≤ r := (le_max_left _ _).trans (hr₁v ▸ hr')
  by_cases hbox : ∀ l, BondWithinRadius (r / 2) (h l)
  swap
  · obtain ⟨l, hl⟩ := not_forall.1 hbox
    have d1 := half_radius_le_bondListDistance (Y := Y) hs1 hh hl
    have d2 := half_radius_le_bondListDistance (Y := Y') hs2 hh hl
    refine far (r / 2 - 1) (by omega) (by omega) ?_
    rw [hEv, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have e1 : ((r / 2 - 1 : ℕ) : ℝ) ≥ ((r : ℝ) - 3) / 2 := by
      have a1 : r ≤ 2 * (r / 2 - 1) + 3 := by omega
      have a2 : (r : ℝ) ≤ 2 * ((r / 2 - 1 : ℕ) : ℝ) + 3 := by exact_mod_cast a1
      linarith
    nlinarith
  have hrad : (-del * (r : ℝ) / 4) ≤ -δ * r := by nlinarith
  obtain ⟨E₀, hE₀v⟩ : ∃ E₀ : ℝ, E₀ = Real.exp (-del * r / 4) := ⟨_, rfl⟩
  have hE₀0 : 0 ≤ E₀ := by
    rw [hE₀v]
    exact (Real.exp_pos _).le
  have hE₀le : E₀ ≤ Real.exp (-δ * r) := by
    rw [hE₀v]
    exact Real.exp_le_exp.2 hrad
  have sσ1 : s ≤ sL := by
    rw [hσv] at hsσ
    exact hsσ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hcN2 : cN ≤ c₂ := by
    rw [hcNv]
    exact min_le_right _ _
  have sc2 : s ≤ c₂ := by
    rw [hσv] at hsσ
    exact (hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).trans hcN2
  obtain ⟨hg1, hg2⟩ := hcomp F F' m S S' hFL hF'L ht hamb hamb' hm hreg hreg' s V V' Y Y' r hs sσ1 hcold hcold' h108
    hag U U' hU hU'
  have gU : offsetChartGapNorm S (referenceFieldChain S V) Y Y Y' U U' ≤ CL * s * E₀ := by
    rw [hE₀v]
    exact hg1 Y (by rw [cellSupDist_self]; omega)
  obtain ⟨hAC, hvalc, hfc⟩ := hagr F F' m S S' hFL hF'L ht hamb hamb' hm hreg hreg' s V V' Y Y' r hs sc2 hcold
    hcold' hr0' hag U U' (fun z hz => (hn2 z hz).trans hcN2) (fun z hz => (hn2' z hz).trans hcN2)
  have hw0 : 0 ≤ s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y +
      localNorm S' (referenceFieldChain S' V') U' (oneSiteWeights F') Y' :=
    add_nonneg (add_nonneg hs.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hwle : s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y +
      localNorm S' (referenceFieldChain S' V') U' (oneSiteWeights F') Y' ≤ W * s := by
    have h1 := hn Y hYS
    have h2 := hn' Y' hYS'
    rw [hWv]
    nlinarith
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [mixedBondDerivative_zero, mixedBondDerivative_zero, (cellShare_base P hbase Y).2,
      (cellShare_base P' hbase' Y').2]
    refine hvalc.trans ?_
    have e0 : derivativeScale s 0 = s ^ 2 := by simp [derivativeScale]
    rw [e0]
    have hgap : 0 ≤ offsetChartGapNorm S (referenceFieldChain S V) Y Y Y' U U' := Real.sqrt_nonneg _
    have h1 : Cm 0 * (s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y +
        localNorm S' (referenceFieldChain S' V') U' (oneSiteWeights F') Y') *
          offsetChartGapNorm S (referenceFieldChain S V) Y Y Y' U U' ≤
        Cm 0 * (W * s) * (CL * s * E₀) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hwle (hCm 0)) gU hgap (mul_nonneg (hCm 0) (mul_nonneg hW0 hs.le))
    have h2 : Cm 0 * W * CL ≤ N 0 := by
      rw [hNv]
      have := hN₁pos 0
      have := hDc0 0
      have : 0 ≤ N₁ 0 * E := mul_nonneg (hN₁pos 0).le (by linarith)
      simp only []
      linarith
    have h3 : Cm 0 * (W * s) * (CL * s * E₀) = s ^ 2 * (Cm 0 * W * CL) * E₀ := by ring
    rw [h3] at h1
    refine h1.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (sq_nonneg s)) hE₀le hE₀0
      (mul_nonneg (sq_nonneg s) (hNpos 0).le)
  obtain ⟨T, hT⟩ := hturn k (offsetBonds Y h) X hk hX
  obtain ⟨T', hT'⟩ := hturn' k (offsetBonds Y' h) X hk hX
  have hev := eventually_isCriticalChainOverTop hk hT hX P.radius_pos P.s_pos P.s_lt P.cold
  have hev' := eventually_isCriticalChainOverTop hk hT' hX P'.radius_pos P'.s_pos P'.s_lt P'.cold
  have hE := minimalCellShare_eventuallyEq P.reads P.exists_minimal hev Y
  have hE' := minimalCellShare_eventuallyEq P'.reads P'.exists_minimal hev' Y'
  have m1 : mixedBondDerivative (minimalCellShare a S Y) V (offsetBonds Y h) X =
      iteratedFDeriv ℝ k (fun ζ => localCellShare a S (referenceFieldChain S V) V Y (T ζ)
        (bondSpread (offsetBonds Y h) X ζ)) 0 (fun l => Pi.single l 1) := by
    unfold mixedBondDerivative
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hE k).self_of_nhds]
  have m2 : mixedBondDerivative (minimalCellShare a S' Y') V' (offsetBonds Y' h) X =
      iteratedFDeriv ℝ k (fun ζ => localCellShare a S' (referenceFieldChain S' V') V' Y' (T' ζ)
        (bondSpread (offsetBonds Y' h) X ζ)) 0 (fun l => Pi.single l 1) := by
    unfold mixedBondDerivative
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hE' k).self_of_nhds]
  have hturnI : ∀ l, ∀ b ∈ topBondsMeetingCell S Y,
      offsetBonds Y h l = b ↔ offsetBonds Y' h l = (cellAtSameOffset Y Y' b.1, b.2) := by
    intro l b hb
    have hiff := offset_eq_iff_cellAtSameOffset (Y := Y) (Y' := Y') hs1 hs2 (hh l).1
      (cellSupDist_le_one_of_mem_topBonds hb) (by omega)
    simp only [offsetBonds, Prod.ext_iff]
    rw [hiff]
  have hgapA : ∀ (m' : ℕ) (e : Fin m' ↪ Fin k), 1 ≤ m' →
      offsetChartGapNorm S (referenceFieldChain S V) Y Y Y' (mixedDerivativeChart T e) (mixedDerivativeChart T' e) ≤
        Ck m' * E₀ := by
    intro m' e hm'
    rw [hE₀v]
    exact hg2 k h X hk hbox hX T T' hT hT' m' e Y hm' (by rw [cellSupDist_self]; omega)
  rw [m1, m2, ← Real.norm_eq_abs]
  by_cases hk1 : k = 1
  · subst hk1
    have hc := norm_sub_first_deriv_le (w := s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y +
        localNorm S' (referenceFieldChain S' V') U' (oneSiteWeights F') Y') (G := CL * s * E₀) (E₀ := E₀)
      (del := del) (C₁ := Cm 1) hMix hd0 hCs hCs hCk0 (hCm 1) hw0 (by positivity) hE₀0 (P.local_evaluation Y)
      (P'.local_evaluation Y')
      (fun n A A' e e' hn1 ht' => hfc n A A' e e' hn1 ht') hX (fun b hb => cellSupDist_le_one_of_mem_topBonds hb)
      (fun b hb => cellSupDist_le_one_of_mem_topBonds hb) hT.eq_at_zero hT'.eq_at_zero hT.analyticAt_fine
      hT.analyticAt_coarse hT'.analyticAt_fine
      hT'.analyticAt_coarse (fun m' e hm' => hT.decay m' e Y hm') (fun m' e hm' => hT'.decay m' e Y' hm') gU hgapA
      hturnI
    refine hc.trans ?_
    have e1 : derivativeScale s 1 = s := by simp [derivativeScale]
    rw [e1]
    have h1 : Cf ≤ N 1 := by
      rw [hNv]
      have := hDc0 1
      have : 0 ≤ N₁ 1 * E := mul_nonneg (hN₁pos 1).le (by linarith)
      have := hN₁pos 1
      simp only []
      linarith
    have h2 : (∑ cP : OrderedFinpartition 1, Cm 1 * (CL * s * E₀ * ∏ i, (Ck (cP.partSize i) + M) +
        (s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y +
          localNorm S' (referenceFieldChain S' V') U' (oneSiteWeights F') Y') * ∑ l, Ck (cP.partSize l) * E₀)) ≤
        Cf * (s * E₀) := by
      rw [hCfv, Finset.sum_mul]
      refine Finset.sum_le_sum fun cP _ => ?_
      have e2 : ∑ l, Ck (cP.partSize l) * E₀ = (∑ l, Ck (cP.partSize l)) * E₀ := by
        rw [Finset.sum_mul]
      have hS0 : 0 ≤ ∑ l, Ck (cP.partSize l) := Finset.sum_nonneg fun l _ => hCk0 _
      rw [e2, mul_assoc (Cm 1)]
      refine mul_le_mul_of_nonneg_left ?_ (hCm 1)
      have h3 := mul_le_mul_of_nonneg_right hwle (mul_nonneg hS0 hE₀0)
      nlinarith
    refine h2.trans ?_
    have h4 : 0 ≤ s * E₀ := mul_nonneg hs.le hE₀0
    calc Cf * (s * E₀) ≤ N 1 * (s * E₀) := mul_le_mul_of_nonneg_right h1 h4
      _ = s * N 1 * E₀ := by ring
      _ ≤ s * N 1 * Real.exp (-δ * r) :=
        mul_le_mul_of_nonneg_left hE₀le (mul_nonneg hs.le (hNpos 1).le)
  · have hk2 : k ≠ 0 := by omega
    have e1 : derivativeScale s k = 1 := by
      simp [derivativeScale, hk1, hk2]
    rw [e1, one_mul]
    obtain ⟨Gs, hGs⟩ : ∃ Gs : ℝ, Gs = CL + ∑ m' ∈ Finset.range (k + 1), Ck m' := ⟨_, rfl⟩
    have hGs0 : 0 ≤ Gs := by
      rw [hGs]
      exact add_nonneg hCL.le (Finset.sum_nonneg fun m' _ => hCk0 m')
    have hE₀1 : E₀ ≤ 1 := by
      rw [hE₀v]
      exact Real.exp_le_one_iff.2 (by nlinarith)
    have hc := hCmp F F' ℝ S S' (referenceFieldChain S V) (referenceFieldChain S' V') Y Y'
      (topBondsMeetingCell S Y) (topBondsMeetingCell S' Y')
      Cs Cs Cm Ck U U' _ _ del (Gs * E₀) Gs 1 k (offsetBonds Y h) (offsetBonds Y' h) X T T' hd0
      (mul_nonneg hGs0 hE₀0)
      (by nlinarith) hCs hCs hCm hCk0 (P.local_evaluation Y) (P'.local_evaluation Y') hAC hX
      (fun b hb => cellSupDist_le_one_of_mem_topBonds hb)
      (fun b hb => cellSupDist_le_one_of_mem_topBonds hb) hT.eq_at_zero hT'.eq_at_zero hT.analyticAt_fine
      hT.analyticAt_coarse hT'.analyticAt_fine
      hT'.analyticAt_coarse (fun m' e hm' => hT.decay m' e Y hm') (fun m' e hm' => hT'.decay m' e Y' hm')
      (gU.trans (by
        have h1 : CL * s ≤ Gs := by
          rw [hGs]
          have : 0 ≤ ∑ m' ∈ Finset.range (k + 1), Ck m' := Finset.sum_nonneg fun m' _ => hCk0 m'
          nlinarith
        exact mul_le_mul_of_nonneg_right h1 hE₀0))
      (fun m' e hm' => (hgapA m' e hm').trans (by
        have h1 : m' ≤ k := by
          have := Fintype.card_le_of_embedding e
          simpa using this
        have h2 : Ck m' ≤ ∑ m'' ∈ Finset.range (k + 1), Ck m'' :=
          Finset.single_le_sum (f := Ck) (fun m'' _ => hCk0 m'') (Finset.mem_range.2 (by omega))
        have h3 : Ck m' ≤ Gs := by
          rw [hGs]
          linarith
        exact mul_le_mul_of_nonneg_right h3 hE₀0))
      hturnI k (Function.Embedding.refl _) hk
    refine hc.trans ?_
    have h1 : comparisonConstant Cm Ck M Gs k * Gs ≤ N k := by
      have e2 : Dc k = comparisonConstant Cm Ck M Gs k * Gs := by
        rw [hDcv, hGs]
      rw [← e2, hNv]
      have : 0 ≤ N₁ k * E := mul_nonneg (hN₁pos k).le (by linarith)
      have := hN₁pos k
      simp only []
      linarith
    rw [← mul_assoc]
    exact mul_le_mul h1 hE₀le hE₀0 (hNpos k).le
end YangMills.Construction.BlockAverages
end
