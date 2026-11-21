import YangMills.Construction.PeriodicOperators.RealLogarithmOfTheDeterminantOfLinearMapsProof
import YangMills.Construction.Towers.PeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.TheMassiveFamilyIsTemperedProof
import YangMills.Construction.Towers.TheTorusMatricesOfTheMassiveOperatorFunctions
import YangMills.Construction.Towers.TheTwoOperatorsAtOneOnATorusProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.LogarithmsNearIdentity
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (seriesLog)
open YangMills.Construction.Tower.Massive (shiftedDetOn)
open YangMills.Construction.PeriodicOperators.Tempered (EventuallyForSides)
open YangMills.Construction.LocalKernels.Periodisation (ProjCellsClassified)
theorem seriesLog_ofReal {x : ℝ} (h : ‖(x : ℂ) - 1‖ < 1) :
    seriesLog (x : ℂ) = (Real.log x : ℂ) := by apply _root_.YangMills.Construction.PeriodicOperators.RealLogDet.seriesLog_ofReal <;> assumption
theorem pauliCoeff_norm_le (hE : ComplexMatrix2.NormExpLogBasics) (a : Fin 3) (X : ComplexMatrix2) :
    ‖pauliCoeff a X‖ ≤ ComplexMatrix2.operatorNorm X := by
  have hent : ∀ i j : Fin 2, ‖X i j‖ ≤ ComplexMatrix2.operatorNorm X := hE.1.2.2.2.2.1 X
  by_cases hX : X ∈ ComplexMatrix2.traceless
  · unfold pauliCoeff
    rw [dif_pos hX]
    fin_cases a
    · show ‖(X 0 1 + X 1 0) / 2‖ ≤ _
      rw [norm_div]
      have := norm_add_le (X 0 1) (X 1 0)
      have h1 := hent 0 1
      have h2 := hent 1 0
      simp only [Complex.norm_ofNat]
      linarith
    · show ‖(X 1 0 - X 0 1) / (2 * Complex.I)‖ ≤ _
      rw [norm_div]
      have := norm_sub_le (X 1 0) (X 0 1)
      have h1 := hent 0 1
      have h2 := hent 1 0
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
      linarith
    · exact hent 0 0
  · unfold pauliCoeff
    rw [dif_neg hX, norm_zero]
    exact norm_nonneg _
theorem pauliCoeff_im_eq_zero {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff a X).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
variable {L n : ℕ}
theorem remainderQuotField_mk (hC : ProjCellsClassified L n 0 0) (B : Edge L n 0 0 → ComplexMatrix2)
    (κ : (colourEdges L 0 0).Carrier) :
    remainderQuotField B ((colourEdges L 0 0).mkQuot (2 * L ^ n) κ) =
      remainderCoeffs B κ := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.remainderQuotField_mkQuot <;> assumption
theorem remainderQuotField_zero (hC : ProjCellsClassified L n 0 0) :
    remainderQuotField (0 : Edge L n 0 0 → ComplexMatrix2) = 0 := by
  funext c
  obtain ⟨κ, rfl⟩ := Quot.exists_rep c
  refine (remainderQuotField_mk hC 0 κ).trans ?_
  exact pauliCoeff_zero _
theorem expTwist_apply {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n 0 0)
    (b : Edge L n 0 0) :
    PeriodicLattice.expTwist B (PeriodicOperators.Tempered.identityField L n) b =
      ComplexMatrix2.matExp (Complex.I • B b) := by
  have hB' : PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra B := hB
  unfold PeriodicLattice.expTwist
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb]
    simp [PeriodicOperators.Tempered.identityField]
  · rw [if_neg hb]
    simp only [PeriodicOperators.Tempered.identityField, mul_one]
    rw [hB'.2 b, smul_neg]
    have e := Matrix.exp_neg (-(Complex.I • B b))
    rw [neg_neg] at e
    exact e.symm
theorem edgeForm_apply_mem {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n 0 0)
    (b : Edge L n 0 0) : B b ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.IdentityOperatorsTorus.edgeForm_apply_mem <;> assumption
theorem expTwist_mem_fieldsIn {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n 0 0) :
    PeriodicLattice.expTwist B (PeriodicOperators.Tempered.identityField L n) ∈
      fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup := by
  have hB' : PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra B := hB
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · rw [expTwist_apply hB]
    obtain ⟨hh, ht⟩ := edgeForm_apply_mem hB b
    refine SpinHarmonics.matExp_mem_of_skewAdjoint ?_ ?_
    · rw [star_smul, Matrix.star_eq_conjTranspose, ← hh]
      simp
    · simp only [ComplexMatrix2.fullTrace] at ht ⊢
      rw [Matrix.trace_smul, ht, smul_zero]
  · rw [expTwist_apply hB, expTwist_apply hB, hB'.2 b, smul_neg]
    exact Matrix.exp_neg _
theorem exists_radius_of_eventuallyNearIdentity {P : (Edge L n 0 0 → ComplexMatrix2) → Prop}
    (hP : EventuallyNearIdentity (fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup) P) :
    ∃ r : ℝ, 0 < r ∧ ∀ B ∈ edgeFormSpace L n 0 0, (∀ b, ComplexMatrix2.operatorNorm (B b) < r) →
      P (PeriodicLattice.expTwist B (PeriodicOperators.Tempered.identityField L n)) := by
  have hev := hP
  unfold EventuallyNearIdentity at hev
  rw [eventually_nhdsWithin_iff, nhds_pi, Filter.eventually_iff, Filter.mem_pi] at hev
  obtain ⟨I, hI, t, ht, hsub⟩ := hev
  have hS : (⋂ i ∈ I, t i) ∈ 𝓝 (1 : ComplexMatrix2) := (Filter.biInter_mem hI).2 fun i _ => ht i
  have hg : ContinuousAt (fun X : ComplexMatrix2 => ComplexMatrix2.matExp (Complex.I • X)) 0 := by
    have h₁ : ContinuousAt (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2)
        (Complex.I • (0 : ComplexMatrix2)) :=
      (NormedSpace.exp_analytic (𝕂 := ℂ) _).continuousAt
    exact ContinuousAt.comp (f := fun X : ComplexMatrix2 => Complex.I • X) h₁
      (continuous_const_smul Complex.I).continuousAt
  have hpre := hg.preimage_mem_nhds (t := ⋂ i ∈ I, t i) (by simpa using hS)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hpre
  refine ⟨r, hr, fun B hB hsmall => ?_⟩
  refine hsub (fun b hb => ?_) (expTwist_mem_fieldsIn hB)
  rw [expTwist_apply hB]
  have h := hball (mem_ball_zero_iff.2 (hsmall b))
  exact mem_iInter₂.1 h b hb
theorem logs_of_positive_dets {F I : PeriodicData} {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
    {s : ℕ} {ζ : F.QuotMod s → ℂ} {d d₀ : ℝ} (hu : IsUnit (quotOperator F I T s 0))
    (h₀ : LinearMap.det (quotOperator F I T s 0) = (d₀ : ℂ))
    (h₁ : LinearMap.det (quotOperator F I T s ζ) = (d : ℂ)) (hd : 0 < d) (hd₀ : 0 < d₀)
    (hw : ‖normalizedDet F I T s ζ - 1‖ < 1) (hre : ∀ c, (ζ c).im = 0) :
    logNormalizedDet F I T s ζ = ((Real.log d - Real.log d₀ : ℝ) : ℂ) ∧
      realLogAbsDetDiff F I T s (fun c => (ζ c).re) = Real.log d - Real.log d₀ := by
  have hq : normalizedDet F I T s ζ = ((d / d₀ : ℝ) : ℂ) := by
    unfold normalizedDet
    obtain ⟨u, hu'⟩ := hu
    rw [← hu'] at h₀
    rw [← hu', Ring.inverse_unit, map_mul, h₁]
    have e : LinearMap.det ((u⁻¹ : (Module.End ℂ (I.QuotMod s → ℂ))ˣ) :
        Module.End ℂ (I.QuotMod s → ℂ)) * (d₀ : ℂ) = 1 := by
      rw [← h₀, ← map_mul, Units.inv_mul, map_one]
    have hne : (d₀ : ℂ) ≠ 0 := by exact_mod_cast hd₀.ne'
    have e' : LinearMap.det ((u⁻¹ : (Module.End ℂ (I.QuotMod s → ℂ))ˣ) :
        Module.End ℂ (I.QuotMod s → ℂ)) = (d₀ : ℂ)⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [e']
    push_cast
    field_simp
  refine ⟨?_, ?_⟩
  · unfold logNormalizedDet
    rw [hq] at hw ⊢
    rw [seriesLog_ofReal hw, Real.log_div hd.ne' hd₀.ne']
  · unfold realLogAbsDetDiff
    have e : (fun c => (((ζ c).re : ℝ) : ℂ)) = ζ :=
      funext fun c => Complex.ext (by simp) (by simp [hre c])
    simp only [e]
    rw [h₁, h₀, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hd.le,
      Real.norm_of_nonneg hd₀.le]
theorem logarithmsNearIdentity (hE : ComplexMatrix2.NormExpLogBasics)
    (hT3 : YangMills.Construction.PeriodicOperators.TowerIndexSets.Claim)
    (hJ1 : YangMills.Construction.PeriodicOperators.Quotients.QuotientTransposeNorm)
    (hY2 : YangMills.Construction.LocalKernels.Periodisation.PeriodisationHolds)
    (hLog : YangMills.Construction.PeriodicOperators.LogDetSecondDerivs.Claim)
    (hPos : YangMills.Construction.Tower.HessianDeterminants.HessianSymmAndDetsPositive)
    (hLoc : YangMills.Construction.Tower.MassiveOpFunctions.Locality.OpFunsLocal)
    (hDet : YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.DetIdentities) :
    YangMills.Construction.Tower.MassiveOpFunctions.LogarithmsNearIdentity.Claim := by
  intro L hL z hz
  have hL₀ : 0 < L := Nat.lt_of_lt_of_le (by norm_num) hL.2
  have hF := (hT3 L hL 0 0 le_rfl).2.1
  have hS := (hT3 L hL 0 0 le_rfl).1
  obtain ⟨hlocS, hlocB, -, -, hsymS, hsymB⟩ := (hLoc L hL z hz).1
  obtain ⟨δ₁, -, -, ⟨s₁, C₁, c₁, -, -, h₁⟩, -⟩ := hLog _ _ hF hS _ hlocS hsymS
  obtain ⟨δ₂, -, -, ⟨s₂, C₂, c₂, -, -, h₂⟩, -⟩ := hLog _ _ hF hF _ hlocB hsymB
  obtain ⟨t₀, ht₀, hlarge⟩ := hDet L hL z hz
  have hcast : ∀ m : ℕ, PeriodicLattice.torusSide L m = ((2 * L ^ m : ℕ) : ℝ) := fun m => by
    simp [PeriodicLattice.torusSide]
  obtain ⟨m, hm, hm₁, hm₂⟩ : ∃ m : ℕ, 0 < m ∧ s₁ ≤ 2 * L ^ m ∧ s₂ ≤ 2 * L ^ m := by
    have hlt : s₁ + s₂ + 1 < L ^ (s₁ + s₂ + 1) :=
      Nat.lt_pow_self (Nat.lt_of_lt_of_le (by norm_num) hL.2)
    exact ⟨s₁ + s₂ + 1, Nat.succ_pos _, by omega, by omega⟩
  refine ⟨max t₀ (PeriodicLattice.torusSide L m), ?_, fun s hs hle n hn e => ?_⟩
  · rcases max_choice t₀ (PeriodicLattice.torusSide L m) with h | h <;> rw [h]
    · exact ht₀
    · exact ⟨m, hm, rfl⟩
  have hdet := hlarge s hs ((le_max_left _ _).trans hle) n hn e
  have hmn : 2 * L ^ m ≤ 2 * L ^ n := by
    have h : PeriodicLattice.torusSide L m ≤ PeriodicLattice.torusSide L n :=
      ((le_max_right _ _).trans hle).trans_eq e.symm
    rw [hcast, hcast] at h
    exact_mod_cast h
  obtain ⟨hu₁, hW₁⟩ := h₁ (2 * L ^ n) (hm₁.trans hmn)
  obtain ⟨hu₂, hW₂⟩ := h₂ (2 * L ^ n) (hm₂.trans hmn)
  have hC : ProjCellsClassified L n 0 0 := ((hY2 L hL 0 n hn).1 0 le_rfl).1
  have hspos : 0 < 2 * L ^ n := by positivity
  have hfin : Finite ((colourEdges L 0 0).QuotMod (2 * L ^ n)) :=
    (hJ1 _ _ hF hF _ hspos).1.2.1
  obtain ⟨N, ⟨e₀⟩⟩ := Finite.exists_equiv_fin ((colourEdges L 0 0).QuotMod (2 * L ^ n))
  obtain ⟨⟨W₁, o₁, z₁, hw₁, -⟩, -, -⟩ := hW₁ N e₀.symm
  obtain ⟨⟨W₂, o₂, z₂, hw₂, -⟩, -, -⟩ := hW₂ N e₀.symm
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.1 o₁ 0 z₁
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.isOpen_iff.1 o₂ 0 z₂
  obtain ⟨hposS, hnear⟩ := (hPos L hL).2 z hz n hn
  obtain ⟨r₀, hr₀, hr⟩ := exists_radius_of_eventuallyNearIdentity hnear
  refine ⟨min r₀ (min ε₁ ε₂), lt_min hr₀ (lt_min hε₁ hε₂), fun B hB hsmall => ?_⟩
  have h0 : (0 : Edge L n 0 0 → ComplexMatrix2) ∈ edgeFormSpace L n 0 0 := Submodule.zero_mem _
  have hU₀ : PeriodicLattice.expTwist (0 : Edge L n 0 0 → ComplexMatrix2)
      (PeriodicOperators.Tempered.identityField L n) = trivialField L n 0 0 := by
    funext b
    rw [expTwist_apply h0]
    simp [trivialField]
  have hmem₀ : trivialField L n 0 0 ∈ fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup := by
    rw [← hU₀]
    exact expTwist_mem_fieldsIn h0
  obtain ⟨e₁₀, e₂₀⟩ := hdet 0 h0
  rw [remainderQuotField_zero hC, hU₀] at e₁₀ e₂₀
  have hd₁₀ := (hposS _ hmem₀).2.2
  have hd₂₀ : 0 < shiftedDetOn (edgeFormSpace L n 0 0)
      (massiveHessian (trivialField L n 0 0)) z := by
    have h := hr 0 h0 fun b => by simpa using hr₀
    rwa [hU₀] at h
  obtain ⟨e₁', e₂'⟩ := hdet B hB
  have hmem := expTwist_mem_fieldsIn hB
  have hd₁ := (hposS _ hmem).2.2
  have hd₂ := hr B hB fun b => lt_of_lt_of_le (hsmall b) (min_le_left _ _)
  have hre : ∀ c, (remainderQuotField B c).im = 0 := fun c => by
    obtain ⟨κ, rfl⟩ := Quot.exists_rep c
    refine (congrArg Complex.im (remainderQuotField_mk hC B κ)).trans ?_
    exact pauliCoeff_im_eq_zero (edgeForm_apply_mem hB _) _
  have hsm : ∀ c, ‖remainderQuotField B c‖ < min ε₁ ε₂ := fun c => by
    obtain ⟨κ, rfl⟩ := Quot.exists_rep c
    refine (congrArg norm (remainderQuotField_mk hC B κ)).trans_lt ?_
    exact (pauliCoeff_norm_le hE _ _).trans_lt
      (lt_of_lt_of_le (hsmall _) (min_le_right _ _))
  have hcoord : ofCoords e₀.symm (toCoords e₀.symm (remainderQuotField B)) =
      remainderQuotField B := by
    funext c
    simp [ofCoords, toCoords]
  have hin₁ : toCoords e₀.symm (remainderQuotField B) ∈ Metric.ball 0 ε₁ :=
    mem_ball_zero_iff.2 ((pi_norm_lt_iff hε₁).2 fun j =>
      (hsm _).trans_le (min_le_left _ _))
  have hin₂ : toCoords e₀.symm (remainderQuotField B) ∈ Metric.ball 0 ε₂ :=
    mem_ball_zero_iff.2 ((pi_norm_lt_iff hε₂).2 fun j =>
      (hsm _).trans_le (min_le_right _ _))
  have hn₁ := hw₁ _ (hb₁ hin₁)
  have hn₂ := hw₂ _ (hb₂ hin₂)
  rw [hcoord] at hn₁ hn₂
  obtain ⟨l₁, r₁⟩ := logs_of_positive_dets hu₁ e₁₀ e₁' hd₁ hd₁₀ hn₁ hre
  obtain ⟨l₂, r₂⟩ := logs_of_positive_dets hu₂ e₂₀ e₂' hd₂ hd₂₀ hn₂ hre
  have hM : massiveLogDetFunctional L n z
      (PeriodicLattice.expTwist B (PeriodicOperators.Tempered.identityField L n)) =
      (Real.log (shiftedDetOn (vertexFunctionSpace L n 0 0) (gaugeLaplacian
          (PeriodicLattice.expTwist B (PeriodicOperators.Tempered.identityField L n))) z) -
        Real.log (shiftedDetOn (vertexFunctionSpace L n 0 0)
          (gaugeLaplacian (trivialField L n 0 0)) z)) -
      1 / 2 * (Real.log (shiftedDetOn (edgeFormSpace L n 0 0) (massiveHessian
          (PeriodicLattice.expTwist B (PeriodicOperators.Tempered.identityField L n))) z) -
        Real.log (shiftedDetOn (edgeFormSpace L n 0 0)
          (massiveHessian (trivialField L n 0 0)) z)) := by
    unfold massiveLogDetFunctional massiveLogDet
    ring
  refine ⟨?_, ?_⟩
  · rw [hM, r₁, r₂]
  · rw [hM, l₁, l₂]
    push_cast
    ring
end YangMills.Construction.Tower.MassiveOpFunctions.LogarithmsNearIdentity
end
