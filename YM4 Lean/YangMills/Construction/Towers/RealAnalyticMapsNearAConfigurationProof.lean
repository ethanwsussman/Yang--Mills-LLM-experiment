import YangMills.Construction.Towers.FunctionalAlongTheCriticalBranchIsRealAnalyticProof
import YangMills.Construction.Towers.SecondDerivativeOfARealAnalyticFunctionIsBilinearProof
import YangMills.Construction.Matrices.ExponentialOfLieElements
import YangMills.Construction.Towers.EvaluationOfARealAnalyticMapAtAPointProof
import YangMills.Construction.Towers.HessianOnAFibreOfTheCriticalBranchProof
import YangMills.Construction.Towers.RealAnalyticMapsNearAConfiguration
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.AnalyticNearField
open Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces.AnalyticCalculus
open Matrices.PowerExpCharts
variable {L n k j j' : ℕ}
theorem opposite_isPositivelyOriented {b : Edge L n k j} (hb : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
theorem apply_eq_inv_apply_opposite {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (b : Edge L n k j) : V b = (V b.opposite)⁻¹ :=
  hV.2 b.opposite (mem_univ _)
theorem fieldOfPositiveValues_restrict {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem restrict_fieldOfPositiveValues (w : PositiveEdge L n k j → ComplexMatrix2) :
    restrictToPositiveEdges (fieldOfPositiveValues w : Edge L n k j → ComplexMatrix2) = w := by apply _root_.YangMills.SharedProofs.p777 <;> assumption
theorem fieldOfPositiveValues_expMul (C U : Edge L n k j → ComplexMatrix2) :
    (fieldOfPositiveValues fun ρ : PositiveEdge L n k j =>
      ComplexMatrix2.matExp (Complex.I • C ρ.1) * U ρ.1) = PeriodicLattice.expTwist C U := by apply _root_.YangMills.DeltaSharedProofs.p502431 <;> assumption
def pureGroupPoint (w : PositiveEdge L n k j → ComplexMatrix2) :
    PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 :=
  Subspaces.ofParts w Empty.elim
abbrev fieldPoints (𝒰 : Set (Edge L n k j → ComplexMatrix2)) :
    Set (PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) :=
  {q | fieldOfPositiveValues (Subspaces.groupComponent q) ∈ 𝒰}
abbrev trivialLie : Submodule ℝ (Empty → ComplexMatrix2) := ⊥
theorem pureGroupPoint_mem {w : PositiveEdge L n k j → ComplexMatrix2}
    (hw : w ∈ edgePower L n k j PeriodicLattice.compactGaugeGroup) :
    pureGroupPoint w ∈ Subspaces.subspaceTimesGroup trivialLie (PositiveEdge L n k j) := by
  refine ⟨?_, hw⟩
  rw [Submodule.mem_bot]
  funext e
  exact e.elim
theorem isOpenFieldSet_of_fieldPoints {𝔇 : Set (Edge L n k j → ComplexMatrix2)}
    (hD : 𝔇 ⊆ fieldSpace L n k j)
    (h : ComplexMatrix2.IsRelativelyOpen
      (Subspaces.subspaceTimesGroup trivialLie (PositiveEdge L n k j)) (fieldPoints 𝔇)) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝔇 := by apply _root_.YangMills.Construction.Tower.AlongBranchAnalyticity.isOpenFieldSet_of_isRelativelyOpen <;> assumption
section Congruence
variable {S R S' R' : Type} [Fintype S] [Fintype R]
theorem isSubspaceAnalyticToCoords_congr {l : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)}
    {𝒲 : Set (R ⊕ S → ComplexMatrix2)}
    {f g : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates l}
    (h : Subspaces.IsSubspaceAnalyticToCoords E 𝒲 f) (hfg : EqOn f g 𝒲) :
    Subspaces.IsSubspaceAnalyticToCoords E 𝒲 g := by
  refine ⟨h.1, fun p hp => ?_⟩
  obtain ⟨𝒳, h1, h2, h3, Φ, h4, h5⟩ := h.2 p hp
  exact ⟨𝒳, h1, h2, h3, Φ, h4, fun x hx => (h5 hx).trans (hfg (h3 hx))⟩
theorem isSubspaceAnalyticToProduct_congr {E : Submodule ℝ (S → ComplexMatrix2)}
    {E' : Submodule ℝ (S' → ComplexMatrix2)}
    {𝒲 : Set (R ⊕ S → ComplexMatrix2)} {f g : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2}
    (h : Subspaces.IsSubspaceAnalyticToProduct E E' 𝒲 f) (hfg : EqOn f g 𝒲) :
    Subspaces.IsSubspaceAnalyticToProduct E E' 𝒲 g := by
  refine ⟨h.1, h.2.1, fun p hp => ?_, fun p hp => ?_⟩
  · rw [← hfg hp]
    exact h.2.2.1 hp
  obtain ⟨𝒳, h1, h2, h3, Φ, h4, h5⟩ := h.2.2.2 p hp
  exact ⟨𝒳, h1, h2, h3, Φ, h4, fun x hx => (h5 hx).trans (hfg (h3 hx))⟩
end Congruence
def liftMap (p : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2)
    (q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) :
    PositiveEdge L n k j' ⊕ Empty → ComplexMatrix2 :=
  Subspaces.ofParts
    (restrictToPositiveEdges (p (fieldOfPositiveValues (Subspaces.groupComponent q)))) Empty.elim
theorem fieldPoints_relPreimage {𝒲 : Set (Edge L n k j → ComplexMatrix2)}
    {𝒲' : Set (Edge L n k j' → ComplexMatrix2)}
    {p : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (hm : MapsTo p 𝒲 (fieldSpace L n k j')) :
    fieldPoints (relPreimage 𝒲 p 𝒲') = fieldPoints 𝒲 ∩ liftMap p ⁻¹' fieldPoints 𝒲' := by
  ext q
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    change fieldOfPositiveValues (restrictToPositiveEdges _) ∈ 𝒲'
    rwa [fieldOfPositiveValues_restrict (hm h1)]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h3 : fieldOfPositiveValues (restrictToPositiveEdges
      (p (fieldOfPositiveValues (Subspaces.groupComponent q)))) ∈ 𝒲' := h2
    rwa [fieldOfPositiveValues_restrict (hm h1)] at h3
theorem relPreimage_subset {𝒲 : Set (Edge L n k j → ComplexMatrix2)}
    (hW : 𝒲 ⊆ fieldSpace L n k j) (𝒲' : Set (Edge L n k j' → ComplexMatrix2))
    (p : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2) :
    relPreimage 𝒲 p 𝒲' ⊆ fieldSpace L n k j := fun _ h => hW h.1
def pauliCoeff (X : ComplexMatrix2) : Fin 3 → ℝ := ![(X 0 1).re, (X 1 0).im, (X 0 0).re]
theorem continuous_pauliCoeff (a : Fin 3) :
    Continuous fun X : ComplexMatrix2 => pauliCoeff X a := by
  have h : ∀ r s : Fin 2, Continuous fun X : ComplexMatrix2 => X r s := fun r s =>
    (continuous_apply s).comp (continuous_apply r)
  fin_cases a
  · exact Complex.continuous_re.comp (h 0 1)
  · exact Complex.continuous_im.comp (h 1 0)
  · exact Complex.continuous_re.comp (h 0 0)
theorem pauliCoeff_sum (x : Fin 3 → ℝ) :
    pauliCoeff (∑ a, (x a : ℂ) • pauliFamily a) = x := by
  funext a
  fin_cases a <;>
    simp [pauliCoeff, Fin.sum_univ_three, pauliFamily, OneLoop.pauliX,
      OneLoop.pauliY, OneLoop.pauliZ]
theorem pauliBasisForm_apply (b b' : PositiveEdge L n k j) (a : Fin 3) :
    pauliBasisForm b' a b.1 = open Classical in if b = b' then pauliFamily a else 0 := by
  classical
  simp only [pauliBasisForm, edgeFormOfPositiveValues, dif_pos b.2]
  rfl
theorem formOfCoeffs_apply [Fintype (PositiveEdge L n k j)]
    (x : PositiveEdge L n k j × Fin 3 → ℝ) (b : PositiveEdge L n k j) :
    formOfCoeffs x b.1 = ∑ a, (x (b, a) : ℂ) • pauliFamily a := by
  classical
  rw [formOfCoeffs, finsum_eq_sum_of_fintype, Finset.sum_apply,
    Fintype.sum_prod_type, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, pauliBasisForm_apply, if_pos rfl, Complex.coe_smul]
  · intro b' _ hb
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Pi.smul_apply, pauliBasisForm_apply, if_neg hb.symm, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h
theorem edgeFormOfPositiveValues_mem
    (hor : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬b.opposite.IsPositivelyOriented)
    {w : PositiveEdge L n k j → ComplexMatrix2} (hw : ∀ b, w b ∈ ComplexMatrix2.hermitianTraceless) :
    edgeFormOfPositiveValues w ∈ edgeFormSpace L n k j := by apply _root_.YangMills.Construction.Tower.FibreHessian.edgeForm_mem <;> assumption
theorem formOfCoeffs_mem [Fintype (PositiveEdge L n k j)]
    (hor : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬b.opposite.IsPositivelyOriented)
    (x : PositiveEdge L n k j × Fin 3 → ℝ) : formOfCoeffs x ∈ edgeFormSpace L n k j := by
  classical
  rw [formOfCoeffs, finsum_eq_sum_of_fintype]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  refine edgeFormOfPositiveValues_mem hor fun b => ?_
  split_ifs
  · exact pauliFamily_mem_hermitianTraceless _
  · exact Submodule.zero_mem _
def smallForms (U : Edge L n k j → ComplexMatrix2) (𝒩 : Set (Edge L n k j → ComplexMatrix2)) :
    Set (Edge L n k j → ComplexMatrix2) :=
  {C | C ∈ edgeFormSpace L n k j ∧
    (∀ ρ : PositiveEdge L n k j, ∑ a, pauliCoeff (C ρ.1) a ^ 2 < Real.log 2 ^ 2) ∧
    PeriodicLattice.expTwist C U ∈ 𝒩}
theorem expMul_mem_edgePower (hE : ComplexMatrix2.ExpImaginaryLieMem)
    {U C : Edge L n k j → ComplexMatrix2} (hU : U ∈ fieldSpace L n k j)
    (hC : C ∈ edgeFormSpace L n k j) :
    (fun ρ : PositiveEdge L n k j => ComplexMatrix2.matExp (Complex.I • C ρ.1) * U ρ.1) ∈
      edgePower L n k j PeriodicLattice.compactGaugeGroup := fun ρ =>
  Submonoid.mul_mem _ (hE.1 _ (hC.1 ρ.1 ρ.2)) (hU.1 ρ.1 (mem_univ _))
theorem expTwist_zero {U : Edge L n k j → ComplexMatrix2} (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.expTwist 0 U = U := by
  have h := fieldOfPositiveValues_expMul 0 U
  simp only [Pi.zero_apply, smul_zero] at h
  rw [← h]
  have h0 : ComplexMatrix2.matExp 0 = 1 := NormedSpace.exp_zero
  simp only [h0, one_mul]
  exact fieldOfPositiveValues_restrict hU
theorem smallForms_isZeroNhd [Finite (PositiveEdge L n k j)]
    (hE : ComplexMatrix2.ExpImaginaryLieMem)
    {U : Edge L n k j → ComplexMatrix2} {𝒩 : Set (Edge L n k j → ComplexMatrix2)}
    (hU : U ∈ fieldSpace L n k j) (hUN : U ∈ 𝒩)
    (hN : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒩) : IsZeroNhd (smallForms U 𝒩) := by
  obtain ⟨hNc, O', hO', hEq⟩ := hN
  let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
  have hexp : Continuous (ComplexMatrix2.matExp : ComplexMatrix2 → ComplexMatrix2) :=
    NormedSpace.exp_continuous
  have hval : ∀ ρ : PositiveEdge L n k j,
      Continuous fun C : Edge L n k j → ComplexMatrix2 => C ρ.1 := fun ρ => continuous_apply ρ.1
  refine ⟨⟨{C | (∀ ρ : PositiveEdge L n k j,
      ∑ a, pauliCoeff (C ρ.1) a ^ 2 < Real.log 2 ^ 2) ∧
      (fun ρ : PositiveEdge L n k j => ComplexMatrix2.matExp (Complex.I • C ρ.1) * U ρ.1) ∈ O'},
      ?_, ?_⟩, ?_⟩
  · have h1 : IsOpen (⋂ ρ : PositiveEdge L n k j, {C : Edge L n k j → ComplexMatrix2 |
        ∑ a, pauliCoeff (C ρ.1) a ^ 2 < Real.log 2 ^ 2}) := by
      refine isOpen_iInter_of_finite fun ρ => isOpen_lt ?_ continuous_const
      exact continuous_finsetSum _ fun a _ =>
        ((continuous_pauliCoeff a).comp (hval ρ)).pow 2
    have h2 : IsOpen ((fun (C : Edge L n k j → ComplexMatrix2) (ρ : PositiveEdge L n k j) =>
        ComplexMatrix2.matExp (Complex.I • C ρ.1) * U ρ.1) ⁻¹' O') := by
      refine hO'.preimage (continuous_pi fun ρ => ?_)
      exact (hexp.comp ((hval ρ).const_smul Complex.I)).mul continuous_const
    convert h1.inter h2 using 1
    ext C
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_preimage]
  · ext C
    constructor
    · rintro ⟨hC, hs, hn⟩
      refine ⟨⟨hs, ?_⟩, hC⟩
      have h1 : restrictToPositiveEdges (PeriodicLattice.expTwist C U) ∈
          restrictToPositiveEdges '' 𝒩 := ⟨_, hn, rfl⟩
      rw [hEq, ← fieldOfPositiveValues_expMul C U, restrict_fieldOfPositiveValues] at h1
      exact h1.1
    · rintro ⟨⟨hs, hO⟩, hC⟩
      refine ⟨hC, hs, ?_⟩
      have h1 : (fun ρ : PositiveEdge L n k j =>
          ComplexMatrix2.matExp (Complex.I • C ρ.1) * U ρ.1) ∈
          restrictToPositiveEdges '' 𝒩 := by
        rw [hEq]
        exact ⟨hO, expMul_mem_edgePower hE hU hC⟩
      obtain ⟨V, hV, hVw⟩ := h1
      rw [← fieldOfPositiveValues_expMul C U, ← hVw, fieldOfPositiveValues_restrict (hNc hV)]
      exact hV
  · refine ⟨Submodule.zero_mem _, fun ρ => ?_, ?_⟩
    · have h0 : ∀ a, pauliCoeff ((0 : Edge L n k j → ComplexMatrix2) ρ.1) a = 0 := by
        intro a
        fin_cases a <;> simp [pauliCoeff]
      simp only [h0]
      have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
      simpa using pow_pos hl 2
    · rwa [expTwist_zero hU]
def emptyBasis : Module.Basis (Fin 0) ℝ trivialLie := Module.Basis.empty _
section Chart
variable [Fintype (PositiveEdge L n k j)]
def indexEnumOf (ν : PositiveEdge L n k j × Fin 3 ≃
    Fin (0 + 3 * Fintype.card (PositiveEdge L n k j))) : IndexEnum (PositiveEdge L n k j) :=
  ν.trans (finCongr (zero_add _))
def chartAtField (ν : PositiveEdge L n k j × Fin 3 ≃
    Fin (0 + 3 * Fintype.card (PositiveEdge L n k j))) (U : Edge L n k j → ComplexMatrix2)
    (z : ParamSpace 0 (PositiveEdge L n k j)) : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 :=
  basisExpChart emptyBasis (indexEnumOf ν) (pureGroupPoint (restrictToPositiveEdges U)) z
theorem angularPart_indexEnumOf (ν : PositiveEdge L n k j × Fin 3 ≃
    Fin (0 + 3 * Fintype.card (PositiveEdge L n k j)))
    (z : ParamSpace 0 (PositiveEdge L n k j)) (ρ : PositiveEdge L n k j) (a : Fin 3) :
    angularPart (indexEnumOf ν) z ρ a = z (ν (ρ, a)) := by
  have h : Fin.natAdd 0 (indexEnumOf ν (ρ, a)) = ν (ρ, a) := by
    ext
    simp [indexEnumOf]
  simp only [angularPart, h]
theorem fieldOfPositiveValues_chartAtField (ν : PositiveEdge L n k j × Fin 3 ≃
    Fin (0 + 3 * Fintype.card (PositiveEdge L n k j))) (U : Edge L n k j → ComplexMatrix2)
    (y : Fin (0 + 3 * Fintype.card (PositiveEdge L n k j)) → ℝ) :
    fieldOfPositiveValues (Subspaces.groupComponent
      (chartAtField ν U (PowerSeries.RealSeries.realEmbed y))) =
      PeriodicLattice.expTwist (formOfCoords ν y) U := by
  rw [← fieldOfPositiveValues_expMul]
  congr 1
  funext ρ
  change ComplexMatrix2.matExp (Complex.I • pauliSum (angularPart (indexEnumOf ν)
    (PowerSeries.RealSeries.realEmbed y)) ρ) * U ρ.1 = _
  rw [formOfCoords, formOfCoeffs_apply]
  simp only [pauliSum, angularPart_indexEnumOf]
  rfl
theorem realEmbed_image_coordRegion
    (hor : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬b.opposite.IsPositivelyOriented)
    (ν : PositiveEdge L n k j × Fin 3 ≃ Fin (0 + 3 * Fintype.card (PositiveEdge L n k j)))
    (U : Edge L n k j → ComplexMatrix2) (𝒩 : Set (Edge L n k j → ComplexMatrix2)) :
    PowerSeries.RealSeries.realEmbed '' coordRegion ν (smallForms U 𝒩) =
      basisExpChartSource 0 (indexEnumOf ν) ∩ chartAtField ν U ⁻¹' fieldPoints 𝒩 := by
  have hco : ∀ (y : Fin (0 + 3 * Fintype.card (PositiveEdge L n k j)) → ℝ)
      (ρ : PositiveEdge L n k j) (a : Fin 3),
      pauliCoeff (formOfCoords ν y ρ.1) a = y (ν (ρ, a)) := by
    intro y ρ a
    rw [formOfCoords, formOfCoeffs_apply]
    exact congrFun (pauliCoeff_sum fun a => (y ∘ ν) (ρ, a)) a
  have hgc : ∀ (y : Fin (0 + 3 * Fintype.card (PositiveEdge L n k j)) → ℝ)
      (ρ : PositiveEdge L n k j) (a : Fin 3),
      (angularPart (indexEnumOf ν) (PowerSeries.RealSeries.realEmbed y) ρ a).re =
        y (ν (ρ, a)) := by
    intro y ρ a
    rw [angularPart_indexEnumOf]
    simp [PowerSeries.RealSeries.realEmbed]
  ext z
  constructor
  · rintro ⟨y, ⟨-, hs, hn⟩, rfl⟩
    refine ⟨⟨fun i => by simp [PowerSeries.RealSeries.realEmbed], fun ρ => ?_⟩, ?_⟩
    · have := hs ρ
      simpa only [hco, hgc] using this
    · change fieldOfPositiveValues _ ∈ 𝒩
      rwa [fieldOfPositiveValues_chartAtField]
  · rintro ⟨⟨hz, hd⟩, hq⟩
    have hzy : PowerSeries.RealSeries.realEmbed (fun i => (z i).re) = z := by
      funext i
      exact Complex.ext (by simp [PowerSeries.RealSeries.realEmbed])
        (by simp [PowerSeries.RealSeries.realEmbed, hz i])
    refine ⟨fun i => (z i).re, ⟨formOfCoeffs_mem hor _, fun ρ => ?_, ?_⟩, hzy⟩
    · have := hd ρ
      rw [← hzy] at this
      simpa only [hco, hgc] using this
    · have h : fieldOfPositiveValues (Subspaces.groupComponent (chartAtField ν U z)) ∈ 𝒩 := hq
      rw [← hzy, fieldOfPositiveValues_chartAtField] at h
      exact h
end Chart
theorem isAnalyticSmoothOn_of_isAnalyticInParams {N l : ℕ}
    {T : Set (Coordinates.ComplexCoordinates N)} {D : Set (Fin N → ℝ)}
    (hDT : PowerSeries.RealSeries.realEmbed '' D = T)
    {g : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates l}
    (hg : IsAnalyticInParams T g) (i : Fin l) (c : ℂ) {f : (Fin N → ℝ) → ℂ}
    (hf : ∀ y ∈ D, f y = c * g (PowerSeries.RealSeries.realEmbed y) i) :
    IsAnalyticSmoothOn D f := by
  obtain ⟨-, hC, hO, hA⟩ := hg
  have hre : ∀ y : Fin N → ℝ, (fun i => (PowerSeries.RealSeries.realEmbed y i).re) = y := by
    intro y
    funext i
    simp [PowerSeries.RealSeries.realEmbed]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hDT]
    exact hO
  · rw [hDT]
    intro a ha
    obtain ⟨cf, hcf⟩ := hA a ha
    refine ⟨fun m _ => c * cf m i, ?_⟩
    obtain ⟨O, hOo, hTO⟩ := hO
    have haO : a ∈ O := by
      rw [hTO] at ha
      exact ha.1
    filter_upwards [hcf, mem_nhdsWithin_of_mem_nhds (hOo.mem_nhds haO), self_mem_nhdsWithin] with
      z hz hzO hzr
    have hzT : z ∈ T := by
      rw [hTO]
      exact ⟨hzO, hzr⟩
    rw [← hDT] at hzT
    obtain ⟨y, hy, rfl⟩ := hzT
    rw [Pi.hasSum]
    intro t
    simp only [hre]
    rw [hf y hy]
    have h := ((Pi.hasSum.mp hz) i).mul_left c
    have h2 : (fun m : Fin N → ℕ =>
        ((∏ j, (PowerSeries.RealSeries.realEmbed y j - a j) ^ m j) •
        fun _ : Fin 1 => c * cf m i) t) =
        fun m => c * ((∏ j, (PowerSeries.RealSeries.realEmbed y j - a j) ^ m j) • cf m) i := by
      funext m
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [h2]
    exact h
  · have h1 := contDiffOn_pi.mp hC i
    have hD : D ⊆ ofRealVector ⁻¹' T := by
      intro y hy
      rw [← hDT]
      exact ⟨y, hy, rfl⟩
    exact ((contDiffOn_const.mul h1).mono hD).congr hf
theorem exists_matrixPiEquiv_index {σ : Type} {m : ℕ} (μ : σ ≃ Fin m) (i : σ) (r s : Fin 2) :
    ∃ t, ∀ x : σ → ComplexMatrix2, matrixPiEquiv μ x t = x i r s := by apply _root_.YangMills.Construction.Tower.AnalyticRepresentation.exists_index_eq_entry <;> assumption
theorem exists_inv_entry_eq (r s : Fin 2) :
    ∃ (c : ℂ) (r' s' : Fin 2), ∀ A ∈ ComplexMatrix2.specialUnitary, A⁻¹ r s = c * A r' s' := by
  have hinv : ∀ A ∈ ComplexMatrix2.specialUnitary, A⁻¹ = !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
    intro A hA
    have hd : A.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hA).2
    rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two]
  fin_cases r <;> fin_cases s
  · exact ⟨1, 1, 1, fun A hA => by simp [hinv A hA]⟩
  · exact ⟨-1, 0, 1, fun A hA => by simp [hinv A hA]⟩
  · exact ⟨-1, 1, 0, fun A hA => by simp [hinv A hA]⟩
  · exact ⟨1, 0, 0, fun A hA => by simp [hinv A hA]⟩
theorem isAnalyticInParams_chartAtField [Fintype (PositiveEdge L n k j)]
    [Fintype (PositiveEdge L n k j')]
    (hP : Subspaces.LocalAnalyticity.LocalAnalyticityStatement)
    (ν : PositiveEdge L n k j × Fin 3 ≃ Fin (0 + 3 * Fintype.card (PositiveEdge L n k j)))
    {U : Edge L n k j → ComplexMatrix2} {𝒩 : Set (Edge L n k j → ComplexMatrix2)}
    (hU : U ∈ fieldSpace L n k j)
    (hUN : U ∈ 𝒩) (hO : Subspaces.IsOpenInSubspaceTimesGroup trivialLie (fieldPoints 𝒩)) :
    (∀ (l : ℕ) (f : (PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) →
        Coordinates.ComplexCoordinates l),
      Subspaces.IsSubspaceAnalyticToCoords trivialLie (fieldPoints 𝒩) f →
        IsAnalyticInParams
          (basisExpChartSource 0 (indexEnumOf ν) ∩ chartAtField ν U ⁻¹' fieldPoints 𝒩)
          (f ∘ chartAtField ν U)) ∧
    ∀ (m : ℕ) (μ : PositiveEdge L n k j' ⊕ Empty ≃ Fin m)
      (f : (PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) →
        PositiveEdge L n k j' ⊕ Empty → ComplexMatrix2),
      Subspaces.IsSubspaceAnalyticToProduct trivialLie trivialLie (fieldPoints 𝒩) f →
        IsAnalyticInParams
          (basisExpChartSource 0 (indexEnumOf ν) ∩ chartAtField ν U ⁻¹' fieldPoints 𝒩)
          (matrixPiEquiv μ ∘ f ∘ chartAtField ν U) := by
  have hw : pureGroupPoint (restrictToPositiveEdges U) ∈
      Subspaces.subspaceTimesGroup trivialLie (PositiveEdge L n k j) :=
    pureGroupPoint_mem fun b => hU.1 b.1 (mem_univ _)
  have hwN : pureGroupPoint (restrictToPositiveEdges U) ∈ fieldPoints 𝒩 := by
    change fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒩
    rwa [fieldOfPositiveValues_restrict hU]
  obtain ⟨hcar, hread⟩ := ((hP Empty (PositiveEdge L n k j) Empty (PositiveEdge L n k j')
    trivialLie trivialLie bot_le bot_le (fieldPoints 𝒩) hO).2.2.2 (indexEnumOf ν)).1 0
    emptyBasis _ hw
  obtain ⟨-, -, h1, h2⟩ := hread hwN _ hcar.2.2.2.1 (hcar.2.2.2.2 hwN).1
    (by rintro _ ⟨z, hz, rfl⟩; exact hz.2)
  exact ⟨fun l f hf => (h1 l f hf).2, fun m μ f hf => (h2 f hf).2 m μ⟩
theorem not_opposite_isPositivelyOriented (hC : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.NearIdentitySurjectivity.not_isPositivelyOriented_opposite <;> assumption
theorem card_eq_of_equiv {σ : Type} [Fintype σ] {N : ℕ} (ν : σ × Fin 3 ≃ Fin N) :
    N = 0 + 3 * Fintype.card σ := by
  have h := Fintype.card_congr ν
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  omega
theorem compositionAndExpTwist_holds (hK : Subspaces.AnalyticCalculus.AnalyticCalculusStatement)
    (hP : Subspaces.LocalAnalyticity.LocalAnalyticityStatement)
    (hE : ComplexMatrix2.ExpImaginaryLieMem)
    (hC : BondSetFields.ProductStructureHolds) : CompositionAndExpTwist := by
  intro L n k j j' j'' hL hn hj hj' hj''
  have hor := not_opposite_isPositivelyOriented hC hL hn hj
  refine ⟨?_, ?_⟩
  · intro 𝒲 𝒲' p hp
    obtain ⟨hWo, hm, iR, iR', hpa⟩ := hp
    have hc := (((hK Empty (PositiveEdge L n k j) Empty (PositiveEdge L n k j')).2.2.2 trivialLie
      trivialLie bot_le bot_le).2.2.1 (fieldPoints 𝒲) hpa.1).2.2.1 (liftMap p) hpa
    have hpre : ∀ {q}, q ∈ fieldPoints 𝒲 → fieldOfPositiveValues (Subspaces.groupComponent
        (liftMap p q)) = p (fieldOfPositiveValues (Subspaces.groupComponent q)) := fun hq =>
      fieldOfPositiveValues_restrict (hm hq)
    refine ⟨fun F hF => ?_, fun F hF => ?_⟩
    · obtain ⟨hW'o, iR'', hFa⟩ := hF
      obtain rfl : iR'' = iR' := Subsingleton.elim _ _
      obtain ⟨hop, hco, -⟩ := hc.2 (fieldPoints 𝒲') hFa.1
      rw [← fieldPoints_relPreimage hm] at hop
      have hopen := isOpenFieldSet_of_fieldPoints (relPreimage_subset hWo.1 𝒲' p) hop
      refine ⟨hopen, hopen, iR, ?_⟩
      have h := hco 1 _ hFa
      rw [← fieldPoints_relPreimage hm] at h
      refine isSubspaceAnalyticToCoords_congr h fun q hq => ?_
      funext _
      simp only [Function.comp, hpre hq.1]
    · obtain ⟨hW'o, hm', iR'', iR''', hFa⟩ := hF
      obtain rfl : iR'' = iR' := Subsingleton.elim _ _
      obtain ⟨hop, -, hco⟩ := hc.2 (fieldPoints 𝒲') hFa.1
      rw [← fieldPoints_relPreimage hm] at hop
      have hopen := isOpenFieldSet_of_fieldPoints (relPreimage_subset hWo.1 𝒲' p) hop
      refine ⟨hopen, hopen, fun V hV => hm' hV.2, iR, iR''', ?_⟩
      have h := hco Empty (PositiveEdge L n k j'') trivialLie (liftMap F) hFa
      rw [← fieldPoints_relPreimage hm] at h
      refine isSubspaceAnalyticToProduct_congr h fun q hq => ?_
      simp only [Function.comp, liftMap]
      rw [show Subspaces.groupComponent (Subspaces.ofParts (restrictToPositiveEdges
        (p (fieldOfPositiveValues (Subspaces.groupComponent q)))) Empty.elim) =
          restrictToPositiveEdges (p (fieldOfPositiveValues (Subspaces.groupComponent q))) from rfl,
        fieldOfPositiveValues_restrict (hm hq.1)]
  · intro U 𝒩 hU hUN
    refine ⟨fun F hF => ?_, fun F hF => ?_⟩
    · obtain ⟨hNo, iR, hFa⟩ := hF
      refine ⟨smallForms U 𝒩, smallForms_isZeroNhd hE hU hUN hNo,
        fun C hC' => hC'.2.2, fun N ν => ?_⟩
      obtain rfl := card_eq_of_equiv ν
      have hr := (isAnalyticInParams_chartAtField (j' := j) hP ν hU hUN hFa.1).1 1 _ hFa
      refine isAnalyticSmoothOn_of_isAnalyticInParams (realEmbed_image_coordRegion hor ν U 𝒩) hr 0 1
        fun y _ => ?_
      simp only [Function.comp, one_mul]
      rw [fieldOfPositiveValues_chartAtField]
    · obtain ⟨hNo, hm, iR, iR', hFa⟩ := hF
      refine ⟨smallForms U 𝒩, smallForms_isZeroNhd hE hU hUN hNo,
        fun C hC' => hC'.2.2, fun N ν b r s => ?_⟩
      obtain rfl := card_eq_of_equiv ν
      have hr := (isAnalyticInParams_chartAtField hP ν hU hUN hFa.1).2 _
        (Fintype.equivFin (PositiveEdge L n k j' ⊕ Empty)) (liftMap F) hFa
      by_cases hb : b.IsPositivelyOriented
      · obtain ⟨t, ht⟩ := exists_matrixPiEquiv_index
          (Fintype.equivFin (PositiveEdge L n k j' ⊕ Empty)) (Sum.inl ⟨b, hb⟩) r s
        refine isAnalyticSmoothOn_of_isAnalyticInParams (realEmbed_image_coordRegion hor ν U 𝒩)
          hr t 1 fun y _ => ?_
        simp only [Function.comp, one_mul, ht, liftMap]
        rw [fieldOfPositiveValues_chartAtField]
        rfl
      · have hb' := opposite_isPositivelyOriented hb
        obtain ⟨c, r', s', hcs⟩ := exists_inv_entry_eq r s
        obtain ⟨t, ht⟩ := exists_matrixPiEquiv_index
          (Fintype.equivFin (PositiveEdge L n k j' ⊕ Empty)) (Sum.inl ⟨b.opposite, hb'⟩) r' s'
        refine isAnalyticSmoothOn_of_isAnalyticInParams (realEmbed_image_coordRegion hor ν U 𝒩)
          hr t c fun y hy => ?_
        have hcfg := hm hy.2.2
        simp only [Function.comp, ht, liftMap]
        rw [fieldOfPositiveValues_chartAtField, apply_eq_inv_apply_opposite hcfg b,
          hcs _ (hcfg.1 _ (mem_univ _))]
        rfl
end YangMills.Construction.Tower.AnalyticNearField
end
