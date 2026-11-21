import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.Towers.PeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.RealAnalyticMapsAreReadInTheChartAtOneProof
import YangMills.Construction.Towers.TheMassiveFunctionalIsRealAnalyticNearOne
import YangMills.Construction.Towers.TheMassiveFunctionalNearOneByLogarithmsOfTorusMatrices
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctionalAreLocal
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.MassiveLogDet
open YangMills.Construction.Matrices YangMills.Construction.Coordinates
open YangMills.Construction.IdentityExpChart
open YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn asLine)
section Holomorphy
theorem isHolomorphicIn_of_clm {N M : ℕ} (T : ComplexCoordinates N →L[ℂ] ComplexCoordinates M)
    {U : Set (ComplexCoordinates N)} (hU : IsOpen U) : ComplexCoordinates.IsHolomorphicIn U T := by
  refine ⟨hU, T.continuous.continuousOn, fun p _ i => Eventually.of_forall fun w => ?_⟩
  have hd : DifferentiableAt ℂ (fun w : ℂ => p + w • ComplexCoordinates.stdBasisVector i) w := by
    fun_prop
  exact T.differentiableAt.comp w hd
theorem isHolomorphicScalarIn_sub_half_mul {K : ℕ} {U₁ U₂ : Set (ComplexCoordinates K)}
    {f₁ f₂ : ComplexCoordinates K → ℂ} (hf₁ : IsHolomorphicScalarIn U₁ f₁)
    (hf₂ : IsHolomorphicScalarIn U₂ f₂) :
    IsHolomorphicScalarIn (U₁ ∩ U₂) fun u => f₁ u - 1 / 2 * f₂ u := by
  have hf₁' : ComplexCoordinates.IsHolomorphicIn U₁ (asLine f₁) := hf₁
  have hf₂' : ComplexCoordinates.IsHolomorphicIn U₂ (asLine f₂) := hf₂
  refine ⟨hf₁'.1.inter hf₂'.1, ?_, fun p hp i => ?_⟩
  · have k₁ : ContinuousOn f₁ (U₁ ∩ U₂) :=
      (continuousOn_pi.1 (hf₁'.2.1.mono inter_subset_left)) 0
    have k₂ : ContinuousOn f₂ (U₁ ∩ U₂) :=
      (continuousOn_pi.1 (hf₂'.2.1.mono inter_subset_right)) 0
    exact continuousOn_pi.2 fun _ => k₁.sub (continuousOn_const.mul k₂)
  · filter_upwards [hf₁'.2.2 p hp.1 i, hf₂'.2.2 p hp.2 i] with w d₁ d₂
    exact differentiableAt_pi.2 fun _ =>
      (differentiableAt_pi.1 d₁ 0).sub ((differentiableAt_pi.1 d₂ 0).const_mul _)
theorem realEmbed_re {N : ℕ} {w : ComplexCoordinates N} (hw : w ∈ ComplexCoordinates.realLocus N) :
    PowerSeries.RealSeries.realEmbed (fun i => (w i).re) = w := by apply _root_.YangMills.Construction.IdentityExpChart.CoordinatesInChart.realEmbed_re <;> assumption
theorem realEmbed_mem_realLocus {N : ℕ} (u : Fin N → ℝ) :
    PowerSeries.RealSeries.realEmbed u ∈ ComplexCoordinates.realLocus N := fun i => by
  simp [PowerSeries.RealSeries.realEmbed]
theorem re_realEmbed {N : ℕ} (u : Fin N → ℝ) :
    (fun i => (PowerSeries.RealSeries.realEmbed u i).re) = u := by apply _root_.YangMills.Construction.IdentityExpChart.CoordinatesInChart.re_realEmbed <;> assumption
theorem isRealAnalytic_of_isHolomorphic
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : ℕ} (Λ : E →ₗ[ℝ] (Fin K → ℝ))
    {U : Set (ComplexCoordinates K)} {F : ComplexCoordinates K → ℂ}
    (hF : IsHolomorphicScalarIn U F) {S : Set E} (hS : IsOpen S)
    (hSU : ∀ v ∈ S, PowerSeries.RealSeries.realEmbed (Λ v) ∈ U) {h : E → ℝ}
    (hh : ∀ v ∈ S, (h v : ℂ) = F (PowerSeries.RealSeries.realEmbed (Λ v))) :
    IsRealAnalyticToRealSpace S h := by
  intro M ψ
  refine ⟨hS, fun N χ => ?_⟩
  have : FiniteDimensional ℝ E := Module.Finite.equiv χ.symm
  have hχS : IsOpen (χ '' S) := χ.toContinuousLinearEquiv.toHomeomorph.isOpenMap S hS
  have hF' : ComplexCoordinates.IsHolomorphicIn U (asLine F) := hF
  let P : Matrix (Fin K) (Fin N) ℂ :=
    fun j i => ((Λ (χ.symm fun i' => if i = i' then 1 else 0) j : ℝ) : ℂ)
  let Pc : ComplexCoordinates N →L[ℂ] ComplexCoordinates K :=
    LinearMap.toContinuousLinearMap P.mulVecLin
  have hPc : ∀ u : Fin N → ℝ,
      Pc (PowerSeries.RealSeries.realEmbed u) =
        PowerSeries.RealSeries.realEmbed (Λ (χ.symm u)) := by
    intro u
    have hs := LinearMap.pi_apply_eq_sum_univ (Λ ∘ₗ χ.symm.toLinearMap) u
    funext j
    have hsj := congrFun hs j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hsj
    change ∑ i, P j i * (u i : ℂ) = ((Λ (χ.symm u) j : ℝ) : ℂ)
    rw [hsj]
    push_cast
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  let Q : ComplexCoordinates 1 →L[ℂ] ComplexCoordinates M :=
    ContinuousLinearMap.pi fun j =>
      ((ψ 1 j : ℝ) : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0
  have hU' : IsOpen (Pc ⁻¹' U) := hF'.1.preimage Pc.continuous
  have hK₁ : ComplexCoordinates.IsHolomorphicIn (Pc ⁻¹' U) (asLine F ∘ Pc) :=
    ((hP.1 K U hF'.1).1 1 (asLine F) hF').2.2.2.1 N _ Pc (isHolomorphicIn_of_clm Pc hU')
      fun _ hx => hx
  have hK₂ : ComplexCoordinates.IsHolomorphicIn (Pc ⁻¹' U) (Q ∘ (asLine F ∘ Pc)) :=
    ((hP.1 1 univ isOpen_univ).1 M Q (isHolomorphicIn_of_clm Q isOpen_univ)).2.2.2.1 N _ _ hK₁
      fun _ _ => mem_univ _
  have hK₃ := ((hP.1 N _ hU').1 M _ hK₂).2.2.2.2
  have hopen : IsOpen {w : ComplexCoordinates N | (fun i => (w i).re) ∈ χ '' S} :=
    hχS.preimage (continuous_pi fun i => Complex.continuous_re.comp (continuous_apply i))
  have himg : PowerSeries.RealSeries.realEmbed '' (χ '' S) =
      {w : ComplexCoordinates N | (fun i => (w i).re) ∈ χ '' S} ∩
        ComplexCoordinates.realLocus N := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, realEmbed_mem_realLocus u⟩
      change (fun i => (PowerSeries.RealSeries.realEmbed u i).re) ∈ χ '' S
      rw [re_realEmbed]
      exact hu
    · rintro ⟨hw₁, hw₂⟩
      exact ⟨_, hw₁, realEmbed_re hw₂⟩
  refine ⟨⟨_, hopen, himg⟩, fun p hp => ?_⟩
  have hp' := hp
  rw [himg] at hp'
  have hpU : p ∈ Pc ⁻¹' U ∩ ComplexCoordinates.realLocus N := by
    refine ⟨?_, hp'.2⟩
    obtain ⟨v, hv, hvp⟩ := hp'.1
    change Pc p ∈ U
    rw [← realEmbed_re hp'.2, ← hvp, hPc, χ.symm_apply_apply]
    exact hSU v hv
  obtain ⟨a, ha⟩ := hK₃.2 p hpU
  refine ⟨a, ?_⟩
  filter_upwards [ha, mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hp'.1), self_mem_nhdsWithin]
    with w hw₁ hw₂ hw₃
  obtain ⟨v, hv, hvw⟩ := hw₂
  have hw : w = PowerSeries.RealSeries.realEmbed (χ v) := by
    rw [hvw]
    exact (realEmbed_re hw₃).symm
  have hvalue : (Q ∘ (asLine F ∘ Pc)) w =
      PowerSeries.RealSeries.realEmbed (ψ (h (χ.symm fun i => (w i).re))) := by
    have q₁ : (fun i => (w i).re) = χ v := hvw.symm
    have q₂ : ψ (h v) = h v • ψ 1 := by
      rw [← map_smul]
      simp
    funext j
    rw [q₁, χ.symm_apply_apply, q₂]
    have q₃ : Pc w = PowerSeries.RealSeries.realEmbed (Λ v) := by
      rw [hw, hPc, χ.symm_apply_apply]
    change ((ψ 1 j : ℝ) : ℂ) * F (Pc w) = _
    rw [q₃, ← hh v hv]
    simp [PowerSeries.RealSeries.realEmbed, mul_comm]
  rw [← hvalue]
  exact hw₁
end Holomorphy
section PauliCoordinates
theorem pauliCoeff_eq_entries (a : Fin 3) (X : ComplexMatrix2.LieElement) :
    pauliCoeff a X.toMatrix =
      ![(X.toMatrix 0 1 + X.toMatrix 1 0) / 2, (X.toMatrix 1 0 - X.toMatrix 0 1) / (2 * Complex.I),
        X.toMatrix 0 0] a := by
  have hX : X.toMatrix ∈ ComplexMatrix2.traceless := X.2.2
  unfold pauliCoeff
  rw [dif_pos hX]
  rfl
theorem pauliCoeff_im_eq_zero (a : Fin 3) (X : ComplexMatrix2.LieElement) :
    (pauliCoeff a X.toMatrix).im = 0 := by
  rw [pauliCoeff_eq_entries]
  have e₁ : X.toMatrix 1 0 = (starRingEnd ℂ) (X.toMatrix 0 1) := X.toMatrix_entry_swap 0 1
  have e₀ : X.toMatrix 0 0 = (starRingEnd ℂ) (X.toMatrix 0 0) := X.toMatrix_entry_swap 0 0
  rw [e₁]
  fin_cases a
  · simp [Complex.add_conj]
  · simp [Complex.div_im]
  · simpa using (Complex.conj_eq_iff_im.1 e₀.symm)
def pauliCoord (a : Fin 3) : ComplexMatrix2.LieElement →ₗ[ℝ] ℝ where
  toFun X := (pauliCoeff a X.toMatrix).re
  map_add' X X' := by
    rw [← Complex.add_re]
    congr 1
    simp only [pauliCoeff_eq_entries]
    have e : ∀ i j, (X + X').toMatrix i j = X.toMatrix i j + X'.toMatrix i j := fun _ _ => rfl
    fin_cases a <;> simp [e] <;> ring
  map_smul' t X := by
    have e : ∀ i j, (t • X).toMatrix i j = (t : ℂ) * X.toMatrix i j := fun i j => by
      change (t • X.toMatrix) i j = _
      simp
    have : pauliCoeff a (t • X).toMatrix = (t : ℂ) * pauliCoeff a X.toMatrix := by
      simp only [pauliCoeff_eq_entries]
      fin_cases a <;> simp [e] <;> ring
    simp [this]
theorem pauliCoord_ofReal (a : Fin 3) (X : ComplexMatrix2.LieElement) :
    ((pauliCoord a X : ℝ) : ℂ) = pauliCoeff a X.toMatrix :=
  Complex.ext rfl (by simp [pauliCoeff_im_eq_zero])
end PauliCoordinates
section Quotients
variable {L n : ℕ}
open YangMills.Construction.LocalKernels
theorem exists_injective_quotMod_to_pairs
    (hC : Periodisation.ProjCellsClassified L n 0 0) :
    ∃ φ : (remainderIndex L 0).QuotMod (2 * L ^ n) → Fin 3 × PositiveEdge L n 0 0,
      Function.Injective φ ∧ ∀ κ : (remainderIndex L 0).Carrier,
        φ ((remainderIndex L 0).mkQuot (2 * L ^ n) κ) =
          (κ.1, projPositiveEdge L n 0 0 κ.2) := by
  have hb := (hC CellType.edge).2
  refine ⟨Quot.lift (fun κ => (κ.1, projPositiveEdge L n 0 0 κ.2)) ?_, ?_, fun κ => rfl⟩
  · rintro κ κ' ⟨m, rfl⟩
    have := (hb κ.2 (shiftEdge ((2 * L ^ n) • m) κ.2)).2 ⟨m, rfl⟩
    exact Prod.ext rfl this
  · intro c c'
    obtain ⟨κ, rfl⟩ := Quot.exists_rep c
    obtain ⟨κ', rfl⟩ := Quot.exists_rep c'
    intro hcc
    have hcc' : ((κ.1, projPositiveEdge L n 0 0 κ.2) : Fin 3 × PositiveEdge L n 0 0) =
        (κ'.1, projPositiveEdge L n 0 0 κ'.2) := hcc
    have e₁ : κ.1 = κ'.1 := (Prod.mk.inj hcc').1
    have e₂ : projPositiveEdge L n 0 0 κ.2 = projPositiveEdge L n 0 0 κ'.2 :=
      (Prod.mk.inj hcc').2
    obtain ⟨m, hm⟩ := (hb κ.2 κ'.2).1 e₂
    refine Quot.sound ⟨m, Prod.ext e₁.symm hm⟩
theorem remainderQuotField_eq
    {φ : (remainderIndex L 0).QuotMod (2 * L ^ n) → Fin 3 × PositiveEdge L n 0 0}
    (hφ : ∀ κ : (remainderIndex L 0).Carrier,
      φ ((remainderIndex L 0).mkQuot (2 * L ^ n) κ) =
        (κ.1, projPositiveEdge L n 0 0 κ.2))
    (A : Edge L n 0 0 → ComplexMatrix2) (c : (remainderIndex L 0).QuotMod (2 * L ^ n)) :
    remainderQuotField A c = pauliCoeff (φ c).1 (A (φ c).2.1) := by
  have hex : ∃ f : (remainderIndex L 0).QuotMod (2 * L ^ n) → ℂ,
      ∀ κ : (remainderIndex L 0).Carrier,
        f ((remainderIndex L 0).mkQuot (2 * L ^ n) κ) = remainderCoeffs A κ :=
    ⟨fun c => pauliCoeff (φ c).1 (A (φ c).2.1), fun κ => by
      simp only [hφ]
      rfl⟩
  have hspec := Classical.epsilon_spec hex
  obtain ⟨κ, rfl⟩ := Quot.exists_rep c
  have hκ := hspec κ
  have e : Quot.mk _ κ = (remainderIndex L 0).mkQuot (2 * L ^ n) κ := rfl
  rw [e, hφ]
  exact hκ
end Quotients
section ExpChart
variable {L n k j : ℕ}
theorem isPositivelyOriented_or_opposite {m : ℕ} {i : ℤ} (b : PeriodicLattice.Bond L m i) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem ofValues_positive (X : PositiveEdge L n k j → ComplexMatrix2.LieElement)
    (b : PositiveEdge L n k j) : ofValues X b.1 = (X b).toMatrix := by
  have hb : b.1.IsPositivelyOriented := b.2
  simp [ofValues, extendOddly, hb]
theorem restrictToPositiveEdges_identityChartPoint
    (X : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    restrictToPositiveEdges (identityChartPoint X) = expFamily X := by apply _root_.YangMills.Construction.Tower.IdentityChart.restrictToPositiveEdges_identityChartPoint <;> assumption
theorem fieldOfPositiveValues_expFamily {X : PositiveEdge L n k j → ComplexMatrix2.LieElement}
    (hX : identityChartPoint X ∈ fieldSpace L n k j) :
    fieldOfPositiveValues (expFamily X) = identityChartPoint X := by
  rw [← restrictToPositiveEdges_identityChartPoint]
  funext b
  unfold fieldOfPositiveValues
  by_cases hb : b.IsPositivelyOriented
  · simp [hb, restrictToPositiveEdges]
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    simp only [hb, hr, dite_false, dite_true, restrictToPositiveEdges]
    exact (hX.2 b.opposite (mem_univ _)).symm
theorem operatorNorm_ofValues_lt {X : PositiveEdge L n k j → ComplexMatrix2.LieElement} {ρ : ℝ}
    (hX : ∀ b, ComplexMatrix2.operatorNorm (X b).toMatrix < ρ) (b : Edge L n k j) :
    ComplexMatrix2.operatorNorm (ofValues X b) < ρ := by
  by_cases hb : b.IsPositivelyOriented
  · exact (ofValues_positive X ⟨b, hb⟩) ▸ hX ⟨b, hb⟩
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    have e := ofValues_positive X ⟨b.opposite, hr⟩
    have e' : ofValues X b = -ofValues X b.opposite := by
      simp [ofValues, extendOddly, hb, hr]
    rw [e', e]
    simpa [ComplexMatrix2.operatorNorm] using hX ⟨b.opposite, hr⟩
end ExpChart
section Level
variable {L n : ℕ}
theorem analyticNearIdentity_of_level (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hR : AnalyticReadInExpChartStatement)
    (hX : IdentityChartOnFields)
    (hC : LocalKernels.Periodisation.ProjCellsClassified L n 0 0)
    (hfin : Finite (PositiveEdge L n 0 0)) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {z ρ : ℝ}
    (hV : ∀ (N : ℕ) (e : Fin N ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n)),
      ∃ U : Set (ComplexCoordinates N), IsOpen U ∧ 0 ∈ U ∧ IsHolomorphicScalarIn U
        (logDetInCoords (colourEdges L 0 0) (colourVertices L 0 0) (MassiveOpFunctions.vertexOpFun L z) e))
    (hE : ∀ (N : ℕ) (e : Fin N ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n)),
      ∃ U : Set (ComplexCoordinates N), IsOpen U ∧ 0 ∈ U ∧ IsHolomorphicScalarIn U
        (logDetInCoords (colourEdges L 0 0) (colourEdges L 0 0) (MassiveOpFunctions.edgeOpFun L z) e))
    (hρ : 0 < ρ) (hI : MassiveOpFunctions.LogarithmsNearIdentity.IdentitiesBelow L n z ρ) :
    Tempered.IsAnalyticNearIdentity (massiveLogDetFunctional L n z) := by
  classical
  let _ : Fintype (PositiveEdge L n 0 0) := Fintype.ofFinite _
  obtain ⟨φ, hφi, hφ⟩ := exists_injective_quotMod_to_pairs hC
  have hfq : Finite ((remainderIndex L 0).QuotMod (2 * L ^ n)) := Finite.of_injective φ hφi
  obtain ⟨K, ⟨e₀⟩⟩ := Finite.exists_equiv_fin ((remainderIndex L 0).QuotMod (2 * L ^ n))
  let e := e₀.symm
  obtain ⟨U₁, oU₁, zU₁, hU₁⟩ := hV K e
  obtain ⟨U₂, oU₂, zU₂, hU₂⟩ := hE K e
  let Λ : (PositiveEdge L n 0 0 → ComplexMatrix2.LieElement) →ₗ[ℝ] (Fin K → ℝ) :=
    LinearMap.pi fun i => pauliCoord (φ (e i)).1 ∘ₗ LinearMap.proj (φ (e i)).2
  have hΛc : Continuous fun X => PowerSeries.RealSeries.realEmbed (Λ X) := by
    have hc : Continuous Λ := Λ.continuous_of_finiteDimensional
    exact continuous_pi fun i => Complex.continuous_ofReal.comp ((continuous_apply i).comp hc)
  let F : ComplexCoordinates K → ℂ := fun w =>
    logDetInCoords (colourEdges L 0 0) (colourVertices L 0 0) (MassiveOpFunctions.vertexOpFun L z) e w -
      1 / 2 * logDetInCoords (colourEdges L 0 0) (colourEdges L 0 0)
        (MassiveOpFunctions.edgeOpFun L z) e w
  have hF : IsHolomorphicScalarIn (U₁ ∩ U₂) F := isHolomorphicScalarIn_sub_half_mul hU₁ hU₂
  obtain ⟨hopen, h0, hpt0, hchart, hopenimg, -, -, -, -, hform, -⟩ := hX L n 0 0 hL hn le_rfl
  let S : Set (PositiveEdge L n 0 0 → ComplexMatrix2.LieElement) :=
    lieBall (PositiveEdge L n 0 0) (1 / 2) ∩
      ({X | ∀ b, ComplexMatrix2.operatorNorm (X b).toMatrix < ρ} ∩
        (fun X => PowerSeries.RealSeries.realEmbed (Λ X)) ⁻¹' (U₁ ∩ U₂))
  let toMat : ComplexMatrix2.LieElement →ₗ[ℝ] ComplexMatrix2 :=
    { toFun := ComplexMatrix2.LieElement.toMatrix, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
  have hmat : Continuous toMat := toMat.continuous_of_finiteDimensional
  have hSo : IsOpen S := by
    refine hopen.inter (IsOpen.inter ?_ ((oU₁.inter oU₂).preimage hΛc))
    have q₁ : {X : PositiveEdge L n 0 0 → ComplexMatrix2.LieElement |
        ∀ b, ComplexMatrix2.operatorNorm (X b).toMatrix < ρ} =
        ⋂ b, {X | ComplexMatrix2.operatorNorm (X b).toMatrix < ρ} := by
      ext X
      simp
    rw [q₁]
    exact isOpen_iInter_of_finite fun b =>
      isOpen_lt (continuous_norm.comp (hmat.comp (continuous_apply b))) continuous_const
  have h0S : (0 : PositiveEdge L n 0 0 → ComplexMatrix2.LieElement) ∈ S := by
    refine ⟨h0, fun b => ?_, ?_⟩
    · change ComplexMatrix2.operatorNorm (0 : ComplexMatrix2) < ρ
      simpa [ComplexMatrix2.operatorNorm] using hρ
    · have q₁ : PowerSeries.RealSeries.realEmbed (Λ 0) = 0 := by
        funext i
        simp [PowerSeries.RealSeries.realEmbed]
      change PowerSeries.RealSeries.realEmbed (Λ 0) ∈ U₁ ∩ U₂
      rw [q₁]
      exact ⟨zU₁, zU₂⟩
  let O : Set (PositiveEdge L n 0 0 → ComplexMatrix2) :=
    restrictToPositiveEdges '' (identityChartPoint '' S)
  have hOo : specialUnitaryPower.IsOpenSubset O := (hopenimg S hSo fun _ hx => hx.1).2
  have h1O : (fun _ => (1 : ComplexMatrix2)) ∈ O :=
    ⟨identityChartPoint 0, ⟨0, h0S, rfl⟩, by rw [hpt0]; rfl⟩
  have hsub : O ⊆ expImage (PositiveEdge L n 0 0) := by
    rintro _ ⟨_, ⟨X, hX', rfl⟩, rfl⟩
    exact ⟨X, hX'.1, (restrictToPositiveEdges_identityChartPoint X).symm⟩
  have hdom : pullbackDomain O = S := by
    ext X
    constructor
    · rintro ⟨hX', _, ⟨X', hX'', rfl⟩, hXX'⟩
      have q₁ : expFamily X' = expFamily X := by
        rwa [restrictToPositiveEdges_identityChartPoint] at hXX'
      have q₂ : identityChartPoint X' = identityChartPoint X := by
        rw [← fieldOfPositiveValues_expFamily (hchart X' hX''.1).1, q₁,
          fieldOfPositiveValues_expFamily (hchart X hX').1]
      have q₃ : X' = X := by rw [← (hchart X' hX''.1).2, q₂, (hchart X hX').2]
      exact q₃ ▸ hX''
    · intro hX'
      exact ⟨hX'.1, identityChartPoint X, ⟨X, hX', rfl⟩,
        restrictToPositiveEdges_identityChartPoint X⟩
  let f : (PositiveEdge L n 0 0 → ComplexMatrix2) → ℝ :=
    fun w => massiveLogDetFunctional L n z (fieldOfPositiveValues (k := 0) (j := 0) w)
  have hvalue : ∀ X ∈ S, (((f ∘ expFamily) X : ℝ) : ℂ) =
      F (PowerSeries.RealSeries.realEmbed (Λ X)) := by
    intro X hX'
    have hA := hI (ofValues X) (hform X).1 (operatorNorm_ofValues_lt hX'.2.1)
    have q₁ : (f ∘ expFamily) X = massiveLogDetFunctional L n z
        (PeriodicLattice.expTwist (ofValues X) (Tempered.identityField L n)) := by
      change massiveLogDetFunctional L n z (fieldOfPositiveValues (expFamily X)) = _
      rw [fieldOfPositiveValues_expFamily (hchart X hX'.1).1]
      rfl
    have q₂ : ofCoords e (PowerSeries.RealSeries.realEmbed (Λ X)) =
        remainderQuotField (ofValues X) := by
      funext c
      rw [remainderQuotField_eq hφ]
      have q₃ : e (e.symm c) = c := e.apply_symm_apply c
      change ((pauliCoord (φ (e (e.symm c))).1 (X (φ (e (e.symm c))).2) : ℝ) : ℂ) = _
      rw [q₃, pauliCoord_ofReal, ofValues_positive]
    rw [q₁, hA.2]
    change _ = logNormalizedDet _ _ _ _ (ofCoords e _) -
      1 / 2 * logNormalizedDet _ _ _ _ (ofCoords e _)
    rw [q₂]
  refine ⟨inferInstance, O, hOo, h1O, fun β => ?_⟩
  have hA : IsRealAnalyticToRealSpace (pullbackDomain O) (f ∘ expFamily) := by
    rw [hdom]
    exact isRealAnalytic_of_isHolomorphic hP Λ hF hSo (fun X hX' => hX'.2.2) hvalue
  exact ((hR (PositiveEdge L n 0 0) (PositiveEdge L n 0 0) β O hOo hsub).1 f).2 hA
end Level
theorem analyticNearIdentity_holds (hN : MassiveOpFunctions.LogarithmsNearIdentity.Claim)
    (hD : LogDetSecondDerivs.Claim)
    (hLoc : MassiveOpFunctions.Locality.OpFunsLocal)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hPer : LocalKernels.Periodisation.PeriodisationHolds)
    (hForms : FiniteSideFormSpaces)
    (hX : IdentityChartOnFields)
    (hR : AnalyticReadInExpChartStatement)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    AnalyticNearIdentity := by
  intro L hL z hz
  obtain ⟨hlV, hlE, -, -, hsV, hsE⟩ := (hLoc L hL z hz).1
  have hper := hIdx L hL 0 0 le_rfl
  obtain ⟨-, -, -, ⟨s₁, _, _, -, -, H₁⟩, -⟩ := hD _ _ hper.2.1 hper.1 _ hlV hsV
  obtain ⟨-, -, -, ⟨s₂, _, _, -, -, H₂⟩, -⟩ := hD _ _ hper.2.1 hper.2.1 _ hlE hsE
  obtain ⟨_, ⟨m₁, hm₁, rfl⟩, hnear⟩ := hN L hL z hz
  have hL1 : 1 < L := by
    have := hL.2
    omega
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1.le
  have hmono : ∀ {a b : ℕ}, a ≤ b →
      PeriodicLattice.torusSide L a ≤ PeriodicLattice.torusSide L b := fun hab => by
    have := pow_le_pow_right₀ hLr hab
    simp only [PeriodicLattice.torusSide]
    linarith
  refine ⟨PeriodicLattice.torusSide L (m₁ + s₁ + s₂ + 1), ⟨m₁ + s₁ + s₂ + 1, by omega, rfl⟩, ?_⟩
  rintro _ ⟨m, hm, rfl⟩ hle n hn hside
  have hle' : PeriodicLattice.torusSide L (m₁ + s₁ + s₂ + 1) ≤ PeriodicLattice.torusSide L n :=
    hside ▸ hle
  have hnat : 2 * L ^ (m₁ + s₁ + s₂ + 1) ≤ 2 * L ^ n := by
    simp only [PeriodicLattice.torusSide] at hle'
    exact_mod_cast hle'
  have hbig : m₁ + s₁ + s₂ + 1 < 2 * L ^ n :=
    lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_pow_self hL1) (by omega)) hnat
  obtain ⟨ρ, hρ, hI⟩ := hnear (PeriodicLattice.torusSide L m) ⟨m, hm, rfl⟩
    ((hmono (by omega)).trans hle) n hn hside
  refine analyticNearIdentity_of_level hP hR hX ((hPer L hL 0 n hn).1 0 le_rfl).1
    (hForms L n 0 0 hL hn le_rfl).1 hL hn (fun N e => ?_) (fun N e => ?_) hρ hI
  · obtain ⟨U, o, z₀, -, hU⟩ := ((H₁ (2 * L ^ n) (by omega)).2 N e).1
    exact ⟨U, o, z₀, hU⟩
  · obtain ⟨U, o, z₀, -, hU⟩ := ((H₂ (2 * L ^ n) (by omega)).2 N e).1
    exact ⟨U, o, z₀, hU⟩
end YangMills.Construction.Tower.MassiveLogDet
end
