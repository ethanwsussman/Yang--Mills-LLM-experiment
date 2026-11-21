import YangMills.Construction.Dirichlet.CommutatorBoundsProof
import YangMills.Construction.Dirichlet.GreenBoundsOnRegionsProof
import YangMills.Construction.Dirichlet.HolderProductBound
import YangMills.Construction.DirichletOperator.PointwiseBoundsOfTheDirichletGreenOperator
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.Torus YangMills.Construction.Dirichlet
open YangMills.Construction.WeightedGreen YangMills.Construction.Dirichlet.WalkExpansion
noncomputable section
namespace YangMills.Construction.Dirichlet.GreenPointwise
variable {d L : ℕ} {S aMinus aPlus : ℝ}
section Suprema
variable {ξ : ℝ}
theorem supNormAll_nonneg (f : LatticeSite d S ξ → ℝ) : 0 ≤ supNormAll f := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.zero_le_supNormAll <;> assumption
theorem abs_le_supNormAll [Finite (LatticeSite d S ξ)]
    (f : LatticeSite d S ξ → ℝ) (x : LatticeSite d S ξ) :
    |f x| ≤ supNormAll f := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.abs_le_supNormAll <;> assumption
theorem fieldSupNorm_nonneg (F : BondField d S ξ) : 0 ≤ fieldSupNorm F :=
  Real.iSup_nonneg fun _ => supNormAll_nonneg _
theorem supNormAll_zero : supNormAll (0 : LatticeSite d S ξ → ℝ) = 0 :=
  le_antisymm (Real.sSup_le (by rintro r ⟨x, -, rfl⟩; simp) le_rfl) (supNormAll_nonneg _)
theorem fieldSupNorm_zero : fieldSupNorm (0 : BondField d S ξ) = 0 := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.fieldSupNorm_zero_eq <;> assumption
theorem scaledHolderSeminorm_nonneg {α s : ℝ} (hs : 0 < s) (ζ : LatticeSite d S ξ → ℝ) :
    0 ≤ scaledHolderSeminorm α s ζ :=
  Real.sSup_nonneg (by
    rintro r ⟨x, x', h0, -, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (div_nonneg hs.le h0.le) _) (abs_nonneg _))
theorem latticeDiv_zero : latticeDiv (0 : BondField d S ξ) = 0 := by
  funext x
  simp [latticeDiv, backwardDiff]
theorem restrictTo_zero (X : Set (PeriodicTorus d S)) :
    restrictTo X (0 : LatticeSite d S ξ → ℝ) = 0 := by
  simp [restrictTo]
end Suprema
section Lengths
theorem lOneNorm_zero_le : lOneNorm (0 : PeriodicTorus d S) ≤ 0 := by
  refine csInf_le ⟨0, ?_⟩ ⟨0, ?_, by simp⟩
  · rintro r ⟨v, -, rfl⟩
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · funext μ
    simp [torusProj]
theorem supNorm_zero_le : supNorm (0 : PeriodicTorus d S) ≤ 0 := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_zero_le <;> assumption
end Lengths
variable (𝒮 : BlockSetting d L aMinus aPlus S)
theorem regionSolution_source (f : LatticeSite d S 𝒮.ξ → ℝ) :
    RegionBounds.regionSolution 𝒮 (𝒮.Ω 0) (boundaryBonds (𝒮.Ω 0)) f 0 = 𝒮.fullGreen f := by
  unfold RegionBounds.regionSolution BlockSetting.fullGreen
  rw [latticeDiv_zero, restrictTo_zero, add_zero]
theorem regionSolution_field (F : BondField d S 𝒮.ξ) :
    RegionBounds.regionSolution 𝒮 (𝒮.Ω 0) (boundaryBonds (𝒮.Ω 0)) 0 F =
      𝒮.fullGreen (divSource 𝒮 F) := by
  unfold RegionBounds.regionSolution BlockSetting.fullGreen divSource
  rw [zero_add]
theorem decayFactor_eq (y y' : PeriodicTorus d S) :
    RegionBounds.decayFactor 𝒮 y y' =
      WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' := by
  unfold RegionBounds.decayFactor WeightedDistance.expDecay
  congr 1
  ring
variable {𝒮}
theorem isRegionSourceData_base (hB : CentreCellFacts 𝒮)
    (hF : Forms.BaseRegionFacts 𝒮) {y' : PeriodicTorus d S} (hy' : y' ∈ 𝒮.centres)
    {f : LatticeSite d S 𝒮.ξ → ℝ} {F : BondField d S 𝒮.ξ}
    (hf : VanishesOff (𝒮.cell y') f) (hFa : 𝒮.IsFieldSupportedNear y' F) :
    RegionBounds.IsRegionSourceData 𝒮 (𝒮.Ω 0) (boundaryBonds (𝒮.Ω 0)) y' f F :=
  { cellUnion := hF.isCellUnion
    boundaryRule := (hF.rule_iff _).mpr rfl
    centre_mem := hy'
    source_vanishesOff := fun x hx => hf x fun hc => hx (hB.cell_subset y' hy' hc)
    source_supportedNear := fun x hx => hf x fun hc => hx (Or.inl hc)
    field_supportedNear := hFa
    field_zero_at_boundary := fun _ hb hn => absurd hb hn
    field_zero_away := fun b ht hh =>
      hFa b (fun hc => ht (hB.cell_subset y' hy' hc)) fun hc => hh (hB.cell_subset y' hy' hc) }
theorem mem_shellSites_centreIndex {y : PeriodicTorus d S} (hy : y ∈ 𝒮.centres) :
    y ∈ shellSites L 𝒮.ξ 𝒮.Ω (𝒮.centreIndex y) := by apply _root_.YangMills.Construction.Dirichlet.RegionBounds.mem_shellSites_centreIndex <;> assumption
theorem isInteriorCentre_base (hB : CentreCellFacts 𝒮) {y : PeriodicTorus d S}
    (hy : y ∈ 𝒮.centres) (hat : Geometry.CollarFacts 𝒮 (𝒮.centreIndex y) y) :
    𝒮.IsInteriorCentre (𝒮.Ω 0) y := by
  refine ⟨hy, hB.cell_subset y hy, ?_⟩
  rcases Nat.eq_zero_or_pos (𝒮.centreIndex y) with h | h
  · exact Or.inl h
  · exact Or.inr (hat.subset h).2
theorem blockDist_self_nonpos (hB : CentreCellFacts 𝒮) {y : PeriodicTorus d S}
    (hy : y ∈ 𝒮.centres) (hat : Geometry.CollarFacts 𝒮 (𝒮.centreIndex y) y) :
    𝒮.blockDist y y ≤ 0 := by
  have hξ := hB.centreSpacing_pos y
  have hmem : y ∈ 𝒮.collar y := by
    show supNorm (y - y) ≤ ((L : ℝ) + 9) * 𝒮.centreSpacing y
    rw [sub_self]
    exact supNorm_zero_le.trans (by positivity)
  have h := hat.blockDist_le ⟨y, hB.mem_spacingLattice y hy⟩ hmem
  have h' : 𝒮.blockDist y y ≤ (L : ℝ) * (𝒮.centreSpacing y)⁻¹ * lOneNorm (y - y) := h
  rw [sub_self] at h'
  have hc : 0 ≤ (L : ℝ) * (𝒮.centreSpacing y)⁻¹ := by positivity
  exact h'.trans (mul_nonpos_of_nonneg_of_nonpos hc lOneNorm_zero_le)
theorem supNorm_sub_le_of_mem_cell (hB : CentreCellFacts 𝒮) {y : PeriodicTorus d S}
    {x : LatticeSite d S 𝒮.ξ} (hx : (x : PeriodicTorus d S) ∈ 𝒮.cell y) :
    supNorm ((x : PeriodicTorus d S) - y) ≤ 2 * 𝒮.centreSpacing y := by
  have h : supNorm ((x : PeriodicTorus d S) - y) ≤ 𝒮.centreSpacing y / 2 := hx
  have hξ := hB.centreSpacing_pos y
  linarith
theorem centreOf_eq (hB : CentreCellFacts 𝒮) {y : PeriodicTorus d S} (hy : y ∈ 𝒮.centres)
    {x : LatticeSite d S 𝒮.ξ} (hx : (x : PeriodicTorus d S) ∈ 𝒮.cell y) :
    𝒮.centreOf x = y := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.centreOf_eq <;> assumption
theorem holderSeminorm_mul_le (hH : HolderProduct.HolderBoundOfProduct)
    (hl : Parameters d L aMinus aPlus) (hB : CentreCellFacts 𝒮) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {y : PeriodicTorus d S} (hy : y ∈ 𝒮.centres) {ζ D : LatticeSite d S 𝒮.ξ → ℝ}
    (hζ : ∀ x : LatticeSite d S 𝒮.ξ,
      𝒮.centreSpacing y ≤ supNorm ((x : PeriodicTorus d S) - y) → ζ x = 0)
    {C Cα Bα e s : ℝ} (hC : 0 ≤ C) (hCα : 0 ≤ Cα) (hBα : 2 * C + Cα ≤ Bα) (he : 0 ≤ e)
    (hs : 0 ≤ s)
    (hD₀ : ∀ x : LatticeSite d S 𝒮.ξ,
      supNorm ((x : PeriodicTorus d S) - y) ≤ 2 * 𝒮.centreSpacing y →
      |D x| ≤ C * (𝒮.centreSpacing y * s) * e)
    (hD₁ : ∀ x x' : LatticeSite d S 𝒮.ξ,
      supNorm ((x : PeriodicTorus d S) - y) ≤ 2 * 𝒮.centreSpacing y →
      supNorm ((x' : PeriodicTorus d S) - y) ≤ 2 * 𝒮.centreSpacing y →
      |D x - D x'| ≤
        Cα * RegionBounds.holderFactor 𝒮 α y x x' * (𝒮.centreSpacing y * s) * e) :
    holderSeminorm α (pointwiseMul ζ D) ≤ Bα * WalkExpansion.holderWeight 𝒮 α y ζ * e * s := by
  have hξ := hB.centreSpacing_pos y
  have h := (hH d L aMinus aPlus S hl 𝒮 α hα0.le hα1 y hy ζ D
    (C * (𝒮.centreSpacing y * s) * e) (Cα * (𝒮.centreSpacing y * s) * e) hζ hD₀
    (fun x x' hx hx' => by
      have := hD₁ x x' hx hx'
      unfold RegionBounds.holderFactor at this
      calc |D x - D x'| ≤ _ := this
        _ = _ := by ring)).2
  have hm : pointwiseMul ζ D = ζ * D := rfl
  rw [hm]
  refine h.trans ?_
  unfold HolderProduct.productConstant WalkExpansion.holderWeight
  have hpow : 𝒮.centreSpacing y ^ (1 - α) = 𝒮.centreSpacing y ^ (-α) * 𝒮.centreSpacing y := by
    rw [sub_eq_neg_add, Real.rpow_add hξ, Real.rpow_one]
  rw [hpow]
  set H := scaledHolderSeminorm α (𝒮.centreSpacing y) ζ with hHdef
  set Z := supNormAll ζ with hZdef
  have hH0 : 0 ≤ H := scaledHolderSeminorm_nonneg hξ ζ
  have hZ0 : 0 ≤ Z := supNormAll_nonneg ζ
  have hP : 0 ≤ 𝒮.centreSpacing y ^ (-α) * 𝒮.centreSpacing y * e * s :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hξ.le _) hξ.le) he) hs
  have hcore : (H + 2 * Z) * C + Z * Cα ≤ Bα * (H + Z) := by
    have h1 : (2 * C + Cα) * (H + Z) ≤ Bα * (H + Z) :=
      mul_le_mul_of_nonneg_right hBα (add_nonneg hH0 hZ0)
    have h2 : 0 ≤ C * H := mul_nonneg hC hH0
    have h3 : 0 ≤ Cα * H := mul_nonneg hCα hH0
    nlinarith
  calc 𝒮.centreSpacing y ^ (-α) * ((H + 2 * Z) * (C * (𝒮.centreSpacing y * s) * e) +
        Z * (Cα * (𝒮.centreSpacing y * s) * e))
      = 𝒮.centreSpacing y ^ (-α) * 𝒮.centreSpacing y * e * s *
          ((H + 2 * Z) * C + Z * Cα) := by ring
    _ ≤ 𝒮.centreSpacing y ^ (-α) * 𝒮.centreSpacing y * e * s * (Bα * (H + Z)) :=
        mul_le_mul_of_nonneg_left hcore hP
    _ = _ := by ring
theorem abs_latticeLaplacian_fullGreen_le (hl : Parameters d L aMinus aPlus)
    (hB : CentreCellFacts 𝒮) (hA : Forms.AveragingOpFacts 𝒮) (hF : Forms.BaseRegionFacts 𝒮)
    (hlin : GreenLinearity.BlockGreenFacts 𝒮 (𝒮.Ω 0) (boundaryBonds (𝒮.Ω 0)))
    {y y' : PeriodicTorus d S} (hy : y ∈ 𝒮.centres) (hy' : y' ∈ 𝒮.centres)
    (hself : 𝒮.blockDist y y ≤ 0)
    (hδ : 0 ≤ expDecayRate d L aMinus aPlus) {f : LatticeSite d S 𝒮.ξ → ℝ}
    (hf : VanishesOff (𝒮.cell y') f) {C : ℝ}
    (hu : ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.cell y →
      |𝒮.fullGreen f x| ≤ C * (𝒮.centreSpacing y ^ 2 * supNormAll f) *
        WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y')
    {x : LatticeSite d S 𝒮.ξ} (hx : (x : PeriodicTorus d S) ∈ 𝒮.cell y) :
    |latticeLaplacian (𝒮.fullGreen f) x| ≤ (1 + aPlus * C) *
      WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' * supNormAll f := by
  have := hB.finite_site
  have hξ := hB.centreSpacing_pos y
  set e := WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hs0 := supNormAll_nonneg f
  have hxΩ : (x : PeriodicTorus d S) ∈ 𝒮.Ω 0 := hB.cell_subset y hy hx
  have hchi : ∀ g : LatticeSite d S 𝒮.ξ → ℝ, restrictTo (𝒮.Ω 0) g x = g x := fun g =>
    Set.indicator_of_mem (s := {x : LatticeSite d S 𝒮.ξ | (x : PeriodicTorus d S) ∈ 𝒮.Ω 0})
      hxΩ g
  have huΩ : VanishesOff (𝒮.Ω 0) (𝒮.fullGreen f) := hlin.vanishesOff f
  have hchiu : restrictTo (𝒮.Ω 0) (𝒮.fullGreen f) = 𝒮.fullGreen f := by
    funext z
    by_cases hz : (z : PeriodicTorus d S) ∈ 𝒮.Ω 0
    · exact Set.indicator_of_mem
        (s := {x : LatticeSite d S 𝒮.ξ | (x : PeriodicTorus d S) ∈ 𝒮.Ω 0}) hz _
    · rw [huΩ z hz]
      exact Set.indicator_of_notMem
        (s := {x : LatticeSite d S 𝒮.ξ | (x : PeriodicTorus d S) ∈ 𝒮.Ω 0}) hz _
  have hsolve : 𝒮.fullOperator (𝒮.fullGreen f) = restrictTo (𝒮.Ω 0) f :=
    hlin.blockOperator_blockGreen f
  have hop := hF.fullOperator_apply (𝒮.fullGreen f) huΩ
  rw [hchiu] at hop
  have hkey : latticeLaplacian (𝒮.fullGreen f) x + 𝒮.averagingOp (𝒮.fullGreen f) x = f x := by
    have h := congrFun (hsolve.symm.trans hop) x
    rw [hchi, hchi] at h
    exact h.symm
  have hP : 𝒮.averagingOp (𝒮.fullGreen f) x =
      𝒮.a (𝒮.centreIndex y) * (𝒮.centreSpacing y ^ 2)⁻¹ * 𝒮.cellAverage (𝒮.fullGreen f) y := by
    unfold BlockSetting.averagingOp
    rw [hchi, centreOf_eq hB hy hx]
  have hsup : supNormOn (𝒮.cell y) (𝒮.fullGreen f) ≤
      C * (𝒮.centreSpacing y ^ 2 * supNormAll f) * e :=
    csSup_le ⟨_, x, hx, rfl⟩ (by
      rintro r ⟨z, hz, rfl⟩
      exact hu z hz)
  have havg : |𝒮.cellAverage (𝒮.fullGreen f) y| ≤
      C * (𝒮.centreSpacing y ^ 2 * supNormAll f) * e :=
    ((hA.abs_cellAverage_le _ y hy).trans (min_le_left _ _)).trans hsup
  have hbetween := 𝒮.weight_mem (𝒮.centreIndex y) (hB.centreIndex_le y hy)
  have ha0 : 0 ≤ 𝒮.a (𝒮.centreIndex y) := hl.lower_pos.le.trans hbetween.1
  have hap : 0 ≤ aPlus := ha0.trans hbetween.2
  have hPb : |𝒮.averagingOp (𝒮.fullGreen f) x| ≤ aPlus * C * e * supNormAll f := by
    rw [hP, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg (by positivity)]
    have hinv : 0 ≤ (𝒮.centreSpacing y ^ 2)⁻¹ := by positivity
    calc 𝒮.a (𝒮.centreIndex y) * (𝒮.centreSpacing y ^ 2)⁻¹ *
          |𝒮.cellAverage (𝒮.fullGreen f) y|
        ≤ aPlus * (𝒮.centreSpacing y ^ 2)⁻¹ *
            (C * (𝒮.centreSpacing y ^ 2 * supNormAll f) * e) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hbetween.2 hinv) havg (abs_nonneg _)
            (mul_nonneg hap hinv)
      _ = aPlus * C * e * supNormAll f := by
          field_simp
  have hfx : |f x| ≤ e * supNormAll f := by
    by_cases hxc : (x : PeriodicTorus d S) ∈ 𝒮.cell y'
    · have hyy : y' = y :=
        (hB.existsUnique_cell x hxΩ).unique ⟨hy', hxc⟩ ⟨hy, hx⟩
      have he1 : 1 ≤ e := by
        rw [he, hyy]
        unfold WeightedDistance.expDecay
        apply Real.one_le_exp
        have : 0 ≤ expDecayRate d L aMinus aPlus / 2 := by positivity
        nlinarith
      calc |f x| ≤ supNormAll f := abs_le_supNormAll f x
        _ = 1 * supNormAll f := (one_mul _).symm
        _ ≤ e * supNormAll f := mul_le_mul_of_nonneg_right he1 hs0
    · rw [hf x hxc, abs_zero]
      exact mul_nonneg he0 hs0
  have hlap : latticeLaplacian (𝒮.fullGreen f) x =
      f x - 𝒮.averagingOp (𝒮.fullGreen f) x := by linarith
  rw [hlap]
  calc |f x - 𝒮.averagingOp (𝒮.fullGreen f) x|
      ≤ |f x| + |𝒮.averagingOp (𝒮.fullGreen f) x| := abs_sub _ _
    _ ≤ e * supNormAll f + aPlus * C * e * supNormAll f := add_le_add hfx hPb
    _ = _ := by ring
theorem claim_holds (hR : RegionBounds.RegionBoundsStatement)
    (hW : ThresholdConsequences.Claim) (hBl : CentreCellFactsHold)
    (hG : Geometry.GeometryHolds) (hFo : Forms.FormsAndOperatorsHold)
    (hLi : GreenLinearity.BlockGreenLinear) (hH : HolderProduct.HolderBoundOfProduct)
    (hD : DecayRateSize.bounds) : Claim := by
  intro d L aMinus aPlus hl B Bα hBge hBαge S 𝒮 hfl
  have hcons := hW d L aMinus aPlus hl S 𝒮 hfl
  obtain ⟨⟨hCpos, hCb⟩, hCα⟩ := hR d L aMinus aPlus hl
  have hB := hBl d L aMinus aPlus S hl 𝒮
  obtain ⟨hA, -, hF⟩ := hFo d L aMinus aPlus S hl 𝒮
  have hlin := hLi d L aMinus aPlus hl S 𝒮 (𝒮.Ω 0) (boundaryBonds (𝒮.Ω 0)) hF.isCellUnion
    ((hF.rule_iff _).mpr rfl)
  have hL3 := hl.three_le_blockFactor
  have hMfloor : L + 10 ≤ 𝒮.M := by
    have := hcons.blockSize_floor
    nlinarith
  have hat : ∀ y ∈ 𝒮.centres, Geometry.CollarFacts 𝒮 (𝒮.centreIndex y) y := fun y hy =>
    (hG d L aMinus aPlus S hl 𝒮).2.2 hMfloor hcons.gap_floor _ y (mem_shellSites_centreIndex hy)
  have := hB.finite_site
  have : Nonempty (Fin d) := ⟨⟨0, by have := hl.three_le_dim; omega⟩⟩
  have hap : 0 < aPlus := hl.lower_pos.trans_le hl.lower_le_upper
  set C := RegionBounds.decayConstant d L aMinus aPlus with hCdef
  have hCB : C ≤ B := by nlinarith [mul_pos hap hCpos]
  have hCB1 : 1 + aPlus * C ≤ B := by nlinarith
  have hδ : 0 ≤ expDecayRate d L aMinus aPlus := by
    obtain ⟨hγ, -, heq, -⟩ := hD d L aMinus aPlus hl
    have hd : (0 : ℝ) < d := by
      have := hl.three_le_dim
      exact_mod_cast (by omega : 0 < d)
    have hpos : 0 < 2 * (d : ℝ) * ((L : ℝ) ^ 2 + aPlus) := by positivity
    by_contra hneg
    nlinarith
  have hfun : ∀ (y y' : PeriodicTorus d S) (f : LatticeSite d S 𝒮.ξ → ℝ),
      y ∈ 𝒮.centres → y' ∈ 𝒮.centres → VanishesOff (𝒮.cell y') f →
      ∀ x : LatticeSite d S 𝒮.ξ,
        supNorm ((x : PeriodicTorus d S) - y) ≤ 2 * 𝒮.centreSpacing y → ∀ ν : Fin d,
        |𝒮.fullGreen f x| ≤ C * (𝒮.centreSpacing y ^ 2 * supNormAll f) *
            WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' ∧
        |forwardDiff ν (𝒮.fullGreen f) x| ≤ C * (𝒮.centreSpacing y * supNormAll f) *
            WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' := by
    intro y y' f hy hy' hf x hx ν
    have h := hCb S 𝒮 hcons.floors _ _ y' f 0
      (isRegionSourceData_base hB hF hy' hf fun _ _ _ => rfl) y
      (isInteriorCentre_base hB hy (hat y hy)) x hx ν
    rw [regionSolution_source, decayFactor_eq] at h
    unfold RegionBounds.sourceScale at h
    rw [fieldSupNorm_zero, mul_zero, add_zero] at h
    exact ⟨h.1, h.2 rfl⟩
  have hfield : ∀ (y y' : PeriodicTorus d S) (F : BondField d S 𝒮.ξ),
      y ∈ 𝒮.centres → y' ∈ 𝒮.centres → 𝒮.IsFieldSupportedNear y' F →
      ∀ x : LatticeSite d S 𝒮.ξ,
        supNorm ((x : PeriodicTorus d S) - y) ≤ 2 * 𝒮.centreSpacing y →
        |𝒮.fullGreen (divSource 𝒮 F) x| ≤ C * (𝒮.centreSpacing y * fieldSupNorm F) *
            WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' := by
    intro y y' F hy hy' hFa x hx
    have h := hCb S 𝒮 hcons.floors _ _ y' 0 F
      (isRegionSourceData_base hB hF hy' (fun _ _ => rfl) hFa) y
      (isInteriorCentre_base hB hy (hat y hy)) x hx (Classical.arbitrary _)
    rw [regionSolution_field, decayFactor_eq] at h
    unfold RegionBounds.sourceScale at h
    rw [supNormAll_zero, mul_zero, zero_add] at h
    exact h.1
  refine ⟨?_, ?_, ?_⟩
  · intro y y' f F ζ hT x hx
    have hξ := hB.centreSpacing_pos y
    have hs0 := supNormAll_nonneg f
    have he0 : 0 ≤ WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' :=
      (Real.exp_pos _).le
    have hF0 := fieldSupNorm_nonneg F
    refine ⟨?_, ?_, ?_⟩
    · have h := (hfun y y' f hT.left_mem hT.right_mem hT.fn_vanishesOff x hx
        (Classical.arbitrary _)).1
      calc _ ≤ _ := h
        _ = C * (𝒮.centreSpacing y ^ 2 *
              WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' *
                supNormAll f) := by
            ring
        _ ≤ B * (𝒮.centreSpacing y ^ 2 *
              WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' *
                supNormAll f) :=
            mul_le_mul_of_nonneg_right hCB (by positivity)
        _ = _ := by ring
    · refine ciSup_le fun ν => ?_
      have h := (hfun y y' f hT.left_mem hT.right_mem hT.fn_vanishesOff x hx ν).2
      calc |grad (𝒮.fullGreen f) ν x| ≤ _ := h
        _ = C * (𝒮.centreSpacing y *
              WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' *
                supNormAll f) := by
            ring
        _ ≤ B * (𝒮.centreSpacing y *
              WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' *
                supNormAll f) :=
            mul_le_mul_of_nonneg_right hCB (by positivity)
        _ = _ := by ring
    · have h := hfield y y' F hT.left_mem hT.right_mem hT.field_supportedNear x hx
      calc _ ≤ _ := h
        _ = C * (𝒮.centreSpacing y *
              WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' *
                fieldSupNorm F) := by
            ring
        _ ≤ B * (𝒮.centreSpacing y *
              WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' *
                fieldSupNorm F) :=
            mul_le_mul_of_nonneg_right hCB (by positivity)
        _ = _ := by ring
  · intro y y' f F ζ hT x hx
    have hs0 := supNormAll_nonneg f
    have he0 : 0 ≤ WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' :=
      (Real.exp_pos _).le
    have h := abs_latticeLaplacian_fullGreen_le hl hB hA hF hlin hT.left_mem hT.right_mem
      (blockDist_self_nonpos hB hT.left_mem (hat y hT.left_mem)) hδ hT.fn_vanishesOff
      (C := C) (fun z hz => (hfun y y' f hT.left_mem hT.right_mem hT.fn_vanishesOff z
        (supNorm_sub_le_of_mem_cell hB hz) (Classical.arbitrary _)).1) hx
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB1 he0) hs0
  · intro y y' f F ζ hT α hα0 hα1
    obtain ⟨hCαpos, hCαb⟩ := hCα α hα0 hα1
    have hs0 := supNormAll_nonneg f
    have hF0 := fieldSupNorm_nonneg F
    have he0 : 0 ≤ WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 2) y y' :=
      (Real.exp_pos _).le
    have hy := hT.left_mem
    have hy' := hT.right_mem
    have hBα := hBαge α hα0 hα1
    have hint := isInteriorCentre_base hB hy (hat y hy)
    refine ⟨?_, ?_⟩
    · refine ciSup_le fun μ => ?_
      refine holderSeminorm_mul_le hH hl hB hα0 hα1 hy hT.cutoff_eq_zero hCpos.le hCαpos.le hBα
        he0 hs0 (fun x hx => (hfun y y' f hy hy' hT.fn_vanishesOff x hx μ).2) ?_
      intro x x' hx hx'
      have h := hCαb S 𝒮 hcons.floors _ _ y' f 0
        (isRegionSourceData_base hB hF hy' hT.fn_vanishesOff fun _ _ _ => rfl) y hint
        x x' hx hx' μ
      rw [regionSolution_source, decayFactor_eq] at h
      exact h.2 rfl
    · refine holderSeminorm_mul_le hH hl hB hα0 hα1 hy hT.cutoff_eq_zero hCpos.le hCαpos.le hBα
        he0 hF0 (fun x hx => hfield y y' F hy hy' hT.field_supportedNear x hx) ?_
      intro x x' hx hx'
      have h := hCαb S 𝒮 hcons.floors _ _ y' 0 F
        (isRegionSourceData_base hB hF hy' (fun _ _ => rfl) hT.field_supportedNear) y hint
        x x' hx hx' (Classical.arbitrary _)
      rw [regionSolution_field, decayFactor_eq] at h
      unfold RegionBounds.sourceScale at h
      rw [supNormAll_zero, mul_zero, zero_add] at h
      exact h.1
end YangMills.Construction.Dirichlet.GreenPointwise
