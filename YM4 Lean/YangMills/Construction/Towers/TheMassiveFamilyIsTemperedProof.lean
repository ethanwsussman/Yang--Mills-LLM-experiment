import YangMills.Construction.PeriodicOperators.SymbolOfAnOperatorWithDecayProof
import YangMills.Construction.OneLoopLaw.BondFormsAsSumsOfPlaneWavesProof
import YangMills.Construction.OneLoopLaw.CovarianceOfASymbolProof
import YangMills.Construction.OneLoopLaw.GaugeColourMomentaAndDifferencesOfFunctionalsProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.RiemannSumsAndShiftsProof
import YangMills.Construction.PeriodicOperators.SecondDifferentialsAreBoundedOnAStrip
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.CrossingAverageOnASideProof
import YangMills.Construction.Towers.DerivativesOnFiniteSetsOfPlaquettesOnASideProof
import YangMills.Construction.Towers.KernelsOfAFieldAreRealAtRealFieldsProof
import YangMills.Construction.Towers.TheMassiveFamilyIsAFunctional
import YangMills.Construction.Towers.TheMassiveFamilyIsTempered
import YangMills.Construction.Towers.TheMassiveFunctionalNearOneByLogarithmsOfTorusMatrices
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctionalAreLocal
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.Tempered
open PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs
open InfiniteLattice (AmbientSpace)
open Matrices (ComplexMatrix2)
theorem mixedDirectionalDeriv_eq_fderiv_fderiv {α : Type*} {N : ℕ} {G : (Fin N → ℝ) → ℝ}
    (hG : HasSecondFDerivAtZero G)
    {φ : (α → ComplexMatrix2) → ℝ} {B B' : α → ComplexMatrix2} {x y : Fin N → ℝ}
    (h : ∀ᶠ q : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)),
      φ (algebraMap ℝ ℂ q.1 • B + algebraMap ℝ ℂ q.2 • B') = G (q.1 • x + q.2 • y)) :
    mixedDirectionalDeriv ℝ φ B B' = fderiv ℝ (fderiv ℝ G) 0 x y := by
  have hx : Tendsto (fun s : ℝ => s • x) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun s : ℝ => s • x) := by fun_prop
    simpa using hcont.tendsto 0
  have hcurry : ∀ᶠ s : ℝ in 𝓝 0, ∀ᶠ t : ℝ in 𝓝 0,
      φ (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B') = G (s • x + t • y) :=
    Filter.Eventually.curry_nhds h
  have hdiff : ∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ G (s • x) := hx.eventually hG.1
  have hinner : (fun s : ℝ => deriv (fun t : ℝ => φ (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B')) 0)
      =ᶠ[𝓝 0] fun s : ℝ => fderiv ℝ G (s • x) y := by
    filter_upwards [hcurry, hdiff] with s hs hd
    have hs' : (fun t : ℝ => φ (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B'))
        =ᶠ[𝓝 0] fun t : ℝ => G (s • x + t • y) := hs
    rw [hs'.deriv_eq]
    have hline : HasDerivAt (fun t : ℝ => s • x + t • y) y 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add (s • x)
    have hd' : HasFDerivAt G (fderiv ℝ G (s • x)) ((fun t : ℝ => s • x + t • y) 0) := by
      simpa using hd.hasFDerivAt
    exact (hd'.comp_hasDerivAt (0 : ℝ) hline).deriv
  have hmain : HasDerivAt (fun s : ℝ => fderiv ℝ G (s • x) y) (fderiv ℝ (fderiv ℝ G) 0 x y) 0 := by
    have hline : HasDerivAt (fun s : ℝ => s • x) x 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const x
    have hd : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) 0) ((fun s : ℝ => s • x) 0) := by
      simpa using hG.2.hasFDerivAt
    have hcomp := hd.comp_hasDerivAt (0 : ℝ) hline
    have happ := hcomp.clm_apply (hasDerivAt_const (0 : ℝ) y)
    simpa using happ
  unfold mixedDirectionalDeriv
  rw [hinner.deriv_eq]
  exact hmain.deriv
theorem hasSecondFDerivAtZero_sub_half {N : ℕ} {G₁ G₂ : (Fin N → ℝ) → ℝ}
    (h₁ : HasSecondFDerivAtZero G₁) (h₂ : HasSecondFDerivAtZero G₂) :
    HasSecondFDerivAtZero (fun v => G₁ v - 1 / 2 * G₂ v) ∧
      ∀ x y, fderiv ℝ (fderiv ℝ fun v => G₁ v - 1 / 2 * G₂ v) 0 x y =
        fderiv ℝ (fderiv ℝ G₁) 0 x y - 1 / 2 * fderiv ℝ (fderiv ℝ G₂) 0 x y := by
  have hE : (fderiv ℝ fun v => G₁ v - 1 / 2 * G₂ v) =ᶠ[𝓝 0]
      fun v => fderiv ℝ G₁ v - (1 / 2 : ℝ) • fderiv ℝ G₂ v := by
    filter_upwards [h₁.1, h₂.1] with v d₁ d₂
    rw [fderiv_fun_sub d₁ (d₂.const_mul _), fderiv_const_mul d₂]
  have hD : DifferentiableAt ℝ (fun v => fderiv ℝ G₁ v - (1 / 2 : ℝ) • fderiv ℝ G₂ v) 0 :=
    h₁.2.sub (h₂.2.const_smul (1 / 2 : ℝ) :
      DifferentiableAt ℝ (fun v => (1 / 2 : ℝ) • fderiv ℝ G₂ v) 0)
  refine ⟨⟨?_, hD.congr_of_eventuallyEq hE⟩, fun x y => ?_⟩
  · filter_upwards [h₁.1, h₂.1] with v d₁ d₂
    exact d₁.sub (d₂.const_mul _)
  · have hs : HasFDerivAt (fun v => fderiv ℝ G₁ v - (1 / 2 : ℝ) • fderiv ℝ G₂ v)
        (fderiv ℝ (fderiv ℝ G₁) 0 - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ G₂) 0) 0 :=
      h₁.2.hasFDerivAt.sub (h₂.2.hasFDerivAt.const_smul (1 / 2 : ℝ))
    rw [hE.fderiv_eq, hs.fderiv]
    simp
theorem pauliCoeff_add_smul {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (c d : ℂ) (a : Fin 3) :
    pauliCoeff a (c • X + d • Y) = c * pauliCoeff a X + d * pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.LeftChartAlgebra.FiniteFaceDerivatives.pauliCoeff_linearCombination <;> assumption
theorem pauliCoeff_im_eq_zero {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff a Y).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoeff_pauliFamily (a' a : Fin 3) :
    pauliCoeff a' (ComplexMatrix2.pauliFamily a) = if a' = a then 1 else 0 := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingContraction.pauliCoeff_pauliFamily <;> assumption
theorem pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (c : ℂ) (a : Fin 3) :
    pauliCoeff a (c • X) = c * pauliCoeff a X := by
  have h := pauliCoeff_add_smul hX hX c 0 a
  simpa using h
section FormCoefficients
open LocalKernels LocalKernels.Periodisation
open PeriodicOperators.Tempered (realComponent imagComponent UnitEdge)
variable {L n : ℕ}
theorem projPositiveEdge_shiftEdge (hc : ProjCellsClassified L n 0 0) (b : PosEdge L 0 0)
    (m : Fin 4 → ℤ) :
    projPositiveEdge L n 0 0 (shiftEdge ((2 * L ^ n) • m) b) = projPositiveEdge L n 0 0 b :=
  (((hc .edge).2 b (shiftEdge ((2 * L ^ n) • m) b)).2 ⟨m, rfl⟩).symm
theorem remainderQuotField_mkQuot (hc : ProjCellsClassified L n 0 0) (B : Edge L n 0 0 → ComplexMatrix2)
    (κ : (colourEdges L 0 0).Carrier) :
    remainderQuotField B ((colourEdges L 0 0).mkQuot (2 * L ^ n) κ) = remainderCoeffs B κ := by
  let f : (colourEdges L 0 0).QuotMod (2 * L ^ n) → ℂ :=
    Quot.lift (remainderCoeffs B) (by
      rintro ι _ ⟨m, rfl⟩
      show pauliCoeff ι.1 (B (projPositiveEdge L n 0 0 ι.2).1) =
        pauliCoeff ι.1 (B (projPositiveEdge L n 0 0 (shiftEdge ((2 * L ^ n) • m) ι.2)).1)
      rw [projPositiveEdge_shiftEdge hc])
  exact Classical.epsilon_spec
    (p := fun f : (colourEdges L 0 0).QuotMod (2 * L ^ n) → ℂ =>
      ∀ κ : (colourEdges L 0 0).Carrier,
        f ((colourEdges L 0 0).mkQuot (2 * L ^ n) κ) = remainderCoeffs B κ)
    ⟨f, fun _ => rfl⟩ κ
theorem finite_quotMod (hc : ProjCellsClassified L n 0 0) [Finite (Tower.PositiveEdge L n 0 0)] :
    Finite ((colourEdges L 0 0).QuotMod (2 * L ^ n)) := by
  let f : (colourEdges L 0 0).QuotMod (2 * L ^ n) → Fin 3 × Tower.PositiveEdge L n 0 0 :=
    Quot.lift (fun ι => (ι.1, projPositiveEdge L n 0 0 ι.2)) (by
      rintro ι _ ⟨m, rfl⟩
      exact Prod.ext rfl (projPositiveEdge_shiftEdge hc ι.2 m).symm)
  refine Finite.of_injective f ?_
  intro c c' h
  obtain ⟨ι, rfl⟩ := Quot.exists_rep c
  obtain ⟨ι', rfl⟩ := Quot.exists_rep c'
  have hpair : (ι.1, projPositiveEdge L n 0 0 ι.2) = (ι'.1, projPositiveEdge L n 0 0 ι'.2) := h
  have hfst : ι.1 = ι'.1 := (Prod.mk.inj hpair).1
  have hsnd : projPositiveEdge L n 0 0 ι.2 = projPositiveEdge L n 0 0 ι'.2 := (Prod.mk.inj hpair).2
  obtain ⟨m, hm⟩ := ((hc .edge).2 ι.2 ι'.2).1 hsnd
  exact Quot.sound ⟨m, Prod.ext hfst.symm hm⟩
theorem remainderCoeffs_add_smul {B B' : Edge L n 0 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) (hB' : B' ∈ complexEdgeForms L n 0 0) (c d : ℂ)
    (κ : (colourEdges L 0 0).Carrier) :
    remainderCoeffs (c • B + d • B') κ = c * remainderCoeffs B κ + d * remainderCoeffs B' κ :=
  pauliCoeff_add_smul (hB.1 _ (projPositiveEdge L n 0 0 κ.2).2)
    (hB'.1 _ (projPositiveEdge L n 0 0 κ.2).2) c d κ.1
theorem remainderQuotField_add_smul (hc : ProjCellsClassified L n 0 0)
    {B B' : Edge L n 0 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) (hB' : B' ∈ complexEdgeForms L n 0 0) (c d : ℂ)
    (x : (colourEdges L 0 0).QuotMod (2 * L ^ n)) :
    remainderQuotField (c • B + d • B') x =
      c * remainderQuotField B x + d * remainderQuotField B' x := by
  obtain ⟨κ, rfl⟩ := Quot.exists_rep x
  have hq : ∀ A : Edge L n 0 0 → ComplexMatrix2, remainderQuotField A (Quot.mk _ κ) =
      remainderCoeffs A κ := fun A => remainderQuotField_mkQuot hc A κ
  rw [hq, hq, hq]
  exact remainderCoeffs_add_smul hB hB' c d κ
theorem realComponent_mem {B : UnitEdge L n → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0) :
    realComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p16359 <;> assumption
theorem imagComponent_mem {B : UnitEdge L n → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0) :
    imagComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p9724 <;> assumption
theorem mem_complexEdgeForms_of_mem {R : Edge L n 0 0 → ComplexMatrix2}
    (hR : R ∈ edgeFormSpace L n 0 0) : R ∈ complexEdgeForms L n 0 0 := by apply _root_.YangMills.DeltaSharedProofs.p8199 <;> assumption
theorem eq_realComponent_add_I_imagComponent (B : UnitEdge L n → ComplexMatrix2) :
    B = (1 : ℂ) • realComponent B + Complex.I • imagComponent B := by
  funext b
  have hI : Complex.I * (2 * Complex.I)⁻¹ = (2⁻¹ : ℂ) := by
    field_simp
  simp only [realComponent, imagComponent, Pi.add_apply, Pi.smul_apply, one_smul, smul_smul,
    hI, ← smul_add]
  ext i j
  simp
  ring
theorem remainderCoeffs_re_im {B : UnitEdge L n → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0)
    (κ : (colourEdges L 0 0).Carrier) :
    (remainderCoeffs B κ).re = (remainderCoeffs (realComponent B) κ).re ∧
      (remainderCoeffs B κ).im = (remainderCoeffs (imagComponent B) κ).re := by
  have hR := realComponent_mem hB
  have hS := imagComponent_mem hB
  have h := remainderCoeffs_add_smul (mem_complexEdgeForms_of_mem hR) (mem_complexEdgeForms_of_mem hS) 1
    Complex.I κ
  rw [← eq_realComponent_add_I_imagComponent B] at h
  have iR : (remainderCoeffs (realComponent B) κ).im = 0 :=
    pauliCoeff_im_eq_zero (hR.1 _ (projPositiveEdge L n 0 0 κ.2).2) κ.1
  have iS : (remainderCoeffs (imagComponent B) κ).im = 0 :=
    pauliCoeff_im_eq_zero (hS.1 _ (projPositiveEdge L n 0 0 κ.2).2) κ.1
  rw [h]
  constructor <;> simp [iR, iS]
theorem projPositiveEdge_target_sub_source (hb : ProjEdgesCompatible L n 0 0)
    (b : PosEdge L 0 0) (ν : Fin 4)
    (hν : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L 0 0) ν) :
    (projPositiveEdge L n 0 0 b).1.target - (projPositiveEdge L n 0 0 b).1.source =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) ν := by
  obtain ⟨ht, hh⟩ := hb.1 b.1
  rw [hb.2.1 b, ht, hh]
  apply Subtype.ext
  have hv : (b.1.terminal : AmbientSpace) =
      (b.1.initial : AmbientSpace) + (InfiniteLattice.axisStep (meshAt L 0 0) ν : AmbientSpace) := by
    rw [← hν]
    simp
  funext μ
  show (((b.1.terminal : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) -
      (((b.1.initial : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) =
    PeriodicLattice.pointOnAxis L n ν (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth 0 0)) μ
  rw [hv]
  by_cases hμ : μ = ν
  · subst hμ
    simp [PeriodicLattice.pointOnAxis, InfiniteLattice.axisStep, meshAt, PeriodicLattice.meshSize]
  · simp [PeriodicLattice.pointOnAxis, InfiniteLattice.axisStep, meshAt, PeriodicLattice.meshSize,
      Pi.single_eq_of_ne hμ]
theorem one_ne_zero_addCircle :
    ((1 : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) ≠ 0 := by
  intro h
  obtain ⟨t, ht⟩ := (AddCircle.coe_eq_zero_iff _).1 h
  rw [zsmul_eq_mul, PeriodicLattice.torusSide] at ht
  have h2 : (t * (2 * (L : ℤ) ^ n) : ℤ) = 1 := by
    exact_mod_cast ht
  have h3 : t * (2 * (L : ℤ) ^ n) = 2 * (t * (L : ℤ) ^ n) := by ring
  omega
theorem unitStep_ne {ν μ : Fin 4} (h : ν ≠ μ) :
    PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) ν ≠
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) μ := by
  intro hst
  have h1 : PeriodicLattice.pointOnAxis L n ν
        (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth 0 0)) ν =
      PeriodicLattice.pointOnAxis L n μ
        (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth 0 0)) ν :=
    congrFun (congrArg Subtype.val hst) ν
  have hs : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth 0 0) = 1 := by
    simp [PeriodicLattice.meshSize]
  simp only [PeriodicLattice.pointOnAxis, Pi.single_eq_same, Pi.single_eq_of_ne h, hs] at h1
  exact one_ne_zero_addCircle h1
theorem exists_int_of_coe_eq {u v : ℝ}
    (h : (u : AddCircle (PeriodicLattice.torusSide L n)) = (v : AddCircle (PeriodicLattice.torusSide L n))) :
    ∃ t : ℤ, u = v + (t : ℝ) * ((2 * L ^ n : ℕ) : ℝ) := by apply _root_.YangMills.Construction.OneLoopLaw.FourierExpansion.exists_int_of_addCircle_coe_eq <;> assumption
theorem phase_coe (hL : 0 < L) {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n)) (y : AmbientSpace) :
    PeriodicOperators.Tempered.phase (L := L) (n := n) p
        (fun μ => ((y μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) =
      Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec y)) := by
  have hs : ((2 * L ^ n : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < 2 * L ^ n := by positivity
    exact_mod_cast hpos.ne'
  have key : ∃ w : ℂ, ∀ y' : AmbientSpace,
      (fun μ => ((y' μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) =
        (fun μ => ((y μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) →
      Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec y')) = w := by
    refine ⟨Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec y)), fun y' hy => ?_⟩
    obtain ⟨m, hm⟩ := hp
    have h1 : ∀ μ, ∃ t : ℤ, y' μ = y μ + (t : ℝ) * ((2 * L ^ n : ℕ) : ℝ) := fun μ =>
      exists_int_of_coe_eq (congrFun hy μ)
    choose t ht using h1
    have h2 : bilinDot (toComplexVec p) (toComplexVec y') =
        bilinDot (toComplexVec p) (toComplexVec y) + ((∑ μ, m μ * t μ : ℤ) : ℂ) * (2 * Real.pi) := by
      simp only [bilinDot, toComplexVec]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      have h3 : p μ * y' μ = p μ * y μ + (m μ : ℝ) * (t μ : ℝ) * (2 * Real.pi) := by
        rw [ht μ, hm μ]
        field_simp
      have h4 := congrArg (fun r : ℝ => (r : ℂ)) h3
      push_cast at h4
      exact h4
    have h5 : Complex.I * (((∑ μ, m μ * t μ : ℤ) : ℂ) * (2 * Real.pi)) =
        ((∑ μ, m μ * t μ : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      ring
    rw [h2, mul_add, Complex.exp_add, h5, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  exact (Classical.epsilon_spec key y rfl).symm
theorem castVec_mem (v : Fin 4 → ℤ) :
    castVec v ∈ InfiniteLattice.latticeSubgroup (meshAt L 0 0) :=
  ⟨v, fun μ => by simp [castVec, meshAt]⟩
theorem vertexImage_intShift (v : Fin 4 → ℤ) (x : FullSpace.Vertex L 0 0) :
    FullSpace.vertexImage (intShift v) x = x + ⟨castVec v, castVec_mem v⟩ :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun x' : InfiniteLattice.LatticePoint (meshAt L 0 0) =>
      (x' : AmbientSpace) = intShift v x)
    ⟨x + ⟨castVec v, castVec_mem v⟩, rfl⟩)
theorem edgeImage_forwardFrom (v : Fin 4 → ℤ) (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    FullSpace.edgeImage (intShift v) (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage (intShift v) x) μ := by
  have hstep : FullSpace.vertexImage (intShift v) (x + InfiniteLattice.axisStep (meshAt L 0 0) μ) =
      FullSpace.vertexImage (intShift v) x + InfiniteLattice.axisStep (meshAt L 0 0) μ := by
    rw [vertexImage_intShift, vertexImage_intShift]
    abel
  have spec := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link (meshAt L 0 0) =>
      b'.initial = FullSpace.vertexImage (intShift v) (InfiniteLattice.Link.forwardFrom x μ).initial ∧
        b'.terminal = FullSpace.vertexImage (intShift v) (InfiniteLattice.Link.forwardFrom x μ).terminal)
    ⟨InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage (intShift v) x) μ, rfl, hstep.symm⟩
  have spec' : (FullSpace.edgeImage (intShift v) (InfiniteLattice.Link.forwardFrom x μ)).initial =
        FullSpace.vertexImage (intShift v) x ∧
      (FullSpace.edgeImage (intShift v) (InfiniteLattice.Link.forwardFrom x μ)).terminal =
        FullSpace.vertexImage (intShift v) (x + InfiniteLattice.axisStep (meshAt L 0 0) μ) := spec
  exact InfiniteLattice.Link.ext spec'.1 (spec'.2.trans hstep)
theorem shiftEdge_eq_edgeAt (v : Fin 4 → ℤ) (b : PosEdge L 0 0) (μ : Fin 4)
    (hb : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L 0 0) μ) :
    shiftEdge v b = PlaneWaves.edgeAt L 0 (FullSpace.vertexImage (intShift v) b.1.initial) μ := by
  have hf : b.1 = InfiniteLattice.Link.forwardFrom b.1.initial μ :=
    InfiniteLattice.Link.ext rfl (by
      show b.1.terminal = b.1.initial + InfiniteLattice.axisStep (meshAt L 0 0) μ
      rw [← hb]
      abel)
  have hm : FullSpace.edgeImage (intShift v) b.1 =
      InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage (intShift v) b.1.initial) μ :=
    (congrArg (FullSpace.edgeImage (intShift v)) hf).trans (edgeImage_forwardFrom v _ μ)
  have spec := Classical.epsilon_spec
    (p := fun b' : PosEdge L 0 0 => b'.1 = FullSpace.edgeImage (intShift v) b.1)
    ⟨PlaneWaves.edgeAt L 0 (FullSpace.vertexImage (intShift v) b.1.initial) μ, hm.symm⟩
  exact Subtype.ext (spec.trans hm)
def HasColourAndAxis (a : Fin 3) (μ : Fin 4) (ι : (colourEdges L 0 0).Carrier) : Prop :=
  ι.1 = a ∧ ι.2.1.terminal - ι.2.1.initial = InfiniteLattice.axisStep (meshAt L 0 0) μ
theorem edgeAt_terminal_sub_initial (x : FullSpace.Vertex L 0 0) (ν : Fin 4) :
    (PlaneWaves.edgeAt L 0 x ν).1.terminal - (PlaneWaves.edgeAt L 0 x ν).1.initial =
      InfiniteLattice.axisStep (meshAt L 0 0) ν := by
  show x + InfiniteLattice.axisStep (meshAt L 0 0) ν - x = _
  abel
theorem hasColourAndAxis_translate (a : Fin 3) (μ : Fin 4) (v : Fin 4 → ℤ)
    (ι : (colourEdges L 0 0).Carrier) :
    HasColourAndAxis a μ ((colourEdges L 0 0).translate v ι) ↔ HasColourAndAxis a μ ι := by
  obtain ⟨a', b⟩ := ι
  obtain ⟨ν, hν⟩ := b.2
  have hsh : (colourEdges L 0 0).translate v (a', b) =
      (a', PlaneWaves.edgeAt L 0 (FullSpace.vertexImage (intShift v) b.1.initial) ν) :=
    Prod.ext rfl (shiftEdge_eq_edgeAt v b ν hν)
  rw [hsh]
  unfold HasColourAndAxis
  simp only
  rw [edgeAt_terminal_sub_initial, hν]
theorem mkQuot_one_eq_iff (a : Fin 3) (μ : Fin 4) (ι : (colourEdges L 0 0).Carrier) :
    (colourEdges L 0 0).mkQuot 1 ι =
        (colourEdges L 0 0).mkQuot 1 (a, PlaneWaves.edgeAt L 0 0 μ) ↔ HasColourAndAxis a μ ι := by
  constructor
  · intro h
    let g : (colourEdges L 0 0).UnitQuot → Prop := Quot.lift (HasColourAndAxis a μ) (by
      rintro ι _ ⟨m, rfl⟩
      exact propext (hasColourAndAxis_translate a μ _ ι).symm)
    have h0 : HasColourAndAxis a μ ((a, PlaneWaves.edgeAt L 0 0 μ) : (colourEdges L 0 0).Carrier) :=
      ⟨rfl, edgeAt_terminal_sub_initial 0 μ⟩
    have h1 : g ((colourEdges L 0 0).mkQuot 1 ι) = g ((colourEdges L 0 0).mkQuot 1
        ((a, PlaneWaves.edgeAt L 0 0 μ) : (colourEdges L 0 0).Carrier)) := congrArg g h
    have h2 : g ((colourEdges L 0 0).mkQuot 1
        ((a, PlaneWaves.edgeAt L 0 0 μ) : (colourEdges L 0 0).Carrier)) := h0
    rw [← h1] at h2
    exact h2
  · rintro ⟨h1, h2⟩
    obtain ⟨a', b⟩ := ι
    obtain ⟨v, hv⟩ := b.1.initial.2
    have hx : FullSpace.vertexImage (intShift v) (0 : FullSpace.Vertex L 0 0) = b.1.initial := by
      rw [vertexImage_intShift, zero_add]
      apply Subtype.ext
      funext ρ
      simp [hv ρ, castVec, meshAt]
    have hb : shiftEdge v (PlaneWaves.edgeAt L 0 0 μ) = b := by
      have h3 : (PlaneWaves.edgeAt L 0 0 μ).1.initial = (0 : FullSpace.Vertex L 0 0) := rfl
      rw [shiftEdge_eq_edgeAt v _ μ (edgeAt_terminal_sub_initial 0 μ), h3, hx]
      apply Subtype.ext
      refine InfiniteLattice.Link.ext rfl ?_
      show b.1.initial + InfiniteLattice.axisStep (meshAt L 0 0) μ = b.1.terminal
      have h4 : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L 0 0) μ := h2
      rw [← h4]
      abel
    obtain rfl : a' = a := h1
    refine (Quot.sound ⟨v, ?_⟩).symm
    rw [one_smul]
    exact Prod.ext rfl hb.symm
open Classical in
theorem colourDirectionIndicator_mkQuot (a : Fin 3) (μ : Fin 4) (ι : (colourEdges L 0 0).Carrier) :
    colourDirectionIndicator L a μ ((colourEdges L 0 0).mkQuot 1 ι) =
      if HasColourAndAxis a μ ι then 1 else 0 := by
  unfold colourDirectionIndicator
  simp only [mkQuot_one_eq_iff]
theorem remainderCoeffs_fourierModeForm (hL : 2 ≤ L) (hb : ProjEdgesCompatible L n 0 0) {p : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (a : Fin 3) (μ : Fin 4) (κ : (colourEdges L 0 0).Carrier) :
    remainderCoeffs (PeriodicOperators.Tempered.fourierModeForm L n a p μ) κ =
      blochWave (colourEdges L 0 0) (toComplexVec p) (colourDirectionIndicator L a μ) κ := by
  classical
  obtain ⟨ν, hν⟩ := κ.2.2
  have hd := projPositiveEdge_target_sub_source hb κ.2 ν hν
  have hsource : ((projPositiveEdge L n 0 0 κ.2).1.source : PeriodicLattice.FourTorus L n) =
      fun ρ => (((κ.2.1.initial : AmbientSpace) ρ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
    rw [hb.2.1 κ.2, (hb.1 κ.2.1).1]
    rfl
  have hphase : PeriodicOperators.Tempered.phase p
      ((projPositiveEdge L n 0 0 κ.2).1.source : PeriodicLattice.FourTorus L n) =
        Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec (κ.2.1.initial : AmbientSpace))) := by
    rw [hsource]
    exact phase_coe (by omega) hp _
  have hval : PeriodicOperators.Tempered.fourierModeForm L n a p μ (projPositiveEdge L n 0 0 κ.2).1 =
      if ν = μ then PeriodicOperators.Tempered.phase p
        ((projPositiveEdge L n 0 0 κ.2).1.source : PeriodicLattice.FourTorus L n) •
          ComplexMatrix2.pauliFamily a else 0 := by
    have hpos := (projPositiveEdge L n 0 0 κ.2).2
    simp only [PeriodicOperators.Tempered.fourierModeForm, extendOddly, if_pos hpos]
    by_cases h : ν = μ
    · subst h
      rw [if_pos hd, if_pos rfl]
    · rw [if_neg h, if_neg]
      intro hst
      exact unitStep_ne h (hd.symm.trans hst)
  show pauliCoeff κ.1 (PeriodicOperators.Tempered.fourierModeForm L n a p μ
      (projPositiveEdge L n 0 0 κ.2).1) =
    Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec (κ.2.1.initial : AmbientSpace))) *
      colourDirectionIndicator L a μ ((colourEdges L 0 0).mkQuot 1 κ)
  rw [colourDirectionIndicator_mkQuot, hval]
  by_cases h : ν = μ
  · subst h
    rw [if_pos rfl, pauliCoeff_smul (pauliFamily_mem_traceless a), pauliCoeff_pauliFamily, hphase]
    by_cases ha : κ.1 = a
    · have hC : HasColourAndAxis a ν κ := ⟨ha, hν⟩
      rw [if_pos ha, if_pos hC]
    · rw [if_neg ha, if_neg (fun hC : HasColourAndAxis a ν κ => ha hC.1)]
  · have hn : ¬ HasColourAndAxis a μ κ := by
      intro hC
      have h1 : InfiniteLattice.axisStep (meshAt L 0 0) ν =
          InfiniteLattice.axisStep (meshAt L 0 0) μ := hν.symm.trans hC.2
      have h2 := congrFun (congrArg Subtype.val h1) ν
      simp [InfiniteLattice.axisStep, meshAt, Pi.single_eq_of_ne h] at h2
    have h0 := pauliCoeff_smul (ComplexMatrix2.traceless.zero_mem) 0 κ.1
    rw [if_neg h, if_neg hn, mul_zero]
    simpa using h0
theorem opposite_isPositivelyOriented_of_not {b : UnitEdge L n} (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p9846 <;> assumption
theorem fourierModeForm_mem (hL : 2 ≤ L) (hn : 0 < n) (a : Fin 3) (p : AmbientSpace) (μ : Fin 4) :
    PeriodicOperators.Tempered.fourierModeForm L n a p μ ∈ complexEdgeForms L n 0 0 := by
  have hrr : ∀ b : UnitEdge L n, b.opposite.opposite = b :=
    fun b => PeriodicLattice.Bond.ext rfl rfl
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [PeriodicOperators.Tempered.fourierModeForm, extendOddly, if_pos hb]
    split_ifs
    · exact ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem_traceless a)
    · exact ComplexMatrix2.traceless.zero_mem
  · by_cases h : b.IsPositivelyOriented
    · have hr : ¬b.opposite.IsPositivelyOriented := by
        rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (L := L) (m := n)
            (j := PeriodicLattice.levelDepth 0 0) (by omega)
            (by simp [PeriodicLattice.levelDepth]; omega) b with
          ⟨-, h'⟩ | ⟨-, h'⟩
        · exact h'
        · exact absurd h h'
      simp only [PeriodicOperators.Tempered.fourierModeForm, extendOddly, if_pos h, if_neg hr, hrr]
    · simp only [PeriodicOperators.Tempered.fourierModeForm, extendOddly, if_neg h,
        if_pos (opposite_isPositivelyOriented_of_not h), neg_neg]
theorem remainderQuotField_fourierModeForm (hc : ProjCellsClassified L n 0 0) (hL : 2 ≤ L)
    (hb : ProjEdgesCompatible L n 0 0) {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n)) (a : Fin 3)
    (μ : Fin 4) :
    remainderQuotField (PeriodicOperators.Tempered.fourierModeForm L n a p μ) =
      descendField (colourEdges L 0 0) (2 * L ^ n)
        (blochWave (colourEdges L 0 0) (toComplexVec p) (colourDirectionIndicator L a μ)) := by
  funext x
  have key : ∃ w : ℂ, ∀ κ, (colourEdges L 0 0).mkQuot (2 * L ^ n) κ = x →
      blochWave (colourEdges L 0 0) (toComplexVec p) (colourDirectionIndicator L a μ) κ = w := by
    refine ⟨remainderQuotField (PeriodicOperators.Tempered.fourierModeForm L n a p μ) x, fun κ hκ => ?_⟩
    rw [← hκ, remainderQuotField_mkQuot hc, remainderCoeffs_fourierModeForm hL hb hp]
  obtain ⟨κ, hκ⟩ : ∃ κ, (colourEdges L 0 0).mkQuot (2 * L ^ n) κ = x := Quot.exists_rep x
  have h1 := Classical.epsilon_spec key κ hκ
  have h2 : remainderQuotField (PeriodicOperators.Tempered.fourierModeForm L n a p μ) x =
      blochWave (colourEdges L 0 0) (toComplexVec p) (colourDirectionIndicator L a μ) κ := by
    rw [← hκ, remainderQuotField_mkQuot hc, remainderCoeffs_fourierModeForm hL hb hp]
  rw [h2, h1]
  rfl
end FormCoefficients
section Hessian
open LocalKernels.Periodisation
open PeriodicOperators.Tempered (realComponent imagComponent UnitEdge hessianAtIdentity complexHessian
  identityField)
open scoped Matrix.Norms.L2Operator
variable {L n N : ℕ}
abbrev vertexLogDetReal (L : ℕ) (z : ℝ) {n N : ℕ}
    (e : Fin N ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n)) : (Fin N → ℝ) → ℝ :=
  realLogAbsDetDiffInCoords (colourEdges L 0 0) (colourVertices L 0 0) (vertexOpFun L z) e
abbrev edgeLogDetReal (L : ℕ) (z : ℝ) {n N : ℕ}
    (e : Fin N ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n)) : (Fin N → ℝ) → ℝ :=
  realLogAbsDetDiffInCoords (colourEdges L 0 0) (colourEdges L 0 0) (edgeOpFun L z) e
def realCoordVec (e : Fin N ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n))
    (B : Edge L n 0 0 → ComplexMatrix2) : Fin N → ℝ :=
  fun j => (remainderQuotField B (e j)).re
theorem ofRealCoords_realCoordVec (e : Fin N ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n))
    (B : Edge L n 0 0 → ComplexMatrix2) :
    ofRealCoords e (realCoordVec e B) = fun c => (remainderQuotField B c).re := by
  funext c
  simp [ofRealCoords, realCoordVec]
theorem realCoordVec_add_smul (hc : ProjCellsClassified L n 0 0)
    (e : Fin N ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n)) {R R' : Edge L n 0 0 → ComplexMatrix2}
    (hR : R ∈ edgeFormSpace L n 0 0) (hR' : R' ∈ edgeFormSpace L n 0 0) (s t : ℝ) :
    s • realCoordVec e R + t • realCoordVec e R' =
      realCoordVec e (algebraMap ℝ ℂ s • R + algebraMap ℝ ℂ t • R') := by
  funext j
  simp only [realCoordVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [remainderQuotField_add_smul hc (mem_complexEdgeForms_of_mem hR) (mem_complexEdgeForms_of_mem hR')]
  simp
theorem remainderQuotField_re_im (hc : ProjCellsClassified L n 0 0) {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) (x : (colourEdges L 0 0).QuotMod (2 * L ^ n)) :
    (remainderQuotField B x).re = (remainderQuotField (realComponent B) x).re ∧
      (remainderQuotField B x).im = (remainderQuotField (imagComponent B) x).re := by
  obtain ⟨κ, rfl⟩ := Quot.exists_rep x
  have hq : ∀ A : UnitEdge L n → ComplexMatrix2, remainderQuotField A (Quot.mk _ κ) =
      remainderCoeffs A κ := fun A => remainderQuotField_mkQuot hc A κ
  rw [hq, hq, hq]
  exact remainderCoeffs_re_im hB κ
theorem eventually_norm_lt [Finite (Tower.PositiveEdge L n 0 0)] {R R' : Edge L n 0 0 → ComplexMatrix2}
    (hR : R ∈ edgeFormSpace L n 0 0) (hR' : R' ∈ edgeFormSpace L n 0 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ q : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), ∀ b : Edge L n 0 0,
      ComplexMatrix2.operatorNorm ((algebraMap ℝ ℂ q.1 • R + algebraMap ℝ ℂ q.2 • R') b) < r := by
  have hpos : ∀ᶠ q : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), ∀ b : Tower.PositiveEdge L n 0 0,
      ComplexMatrix2.operatorNorm ((algebraMap ℝ ℂ q.1 • R + algebraMap ℝ ℂ q.2 • R') b.1) < r := by
    rw [Filter.eventually_all]
    intro b
    have hcont : Continuous fun q : ℝ × ℝ =>
        ‖(q.1 : ℂ) • R b.1 + (q.2 : ℂ) • R' b.1‖ := by
      have c1 : Continuous fun q : ℝ × ℝ => (q.1 : ℂ) := Complex.continuous_ofReal.comp continuous_fst
      have c2 : Continuous fun q : ℝ × ℝ => (q.2 : ℂ) := Complex.continuous_ofReal.comp continuous_snd
      exact ((c1.smul continuous_const).add (c2.smul continuous_const)).norm
    have h0 := hcont.tendsto ((0 : ℝ), (0 : ℝ))
    have h1 : ‖((((0 : ℝ), (0 : ℝ)) : ℝ × ℝ).1 : ℂ) • R b.1 +
        ((((0 : ℝ), (0 : ℝ)) : ℝ × ℝ).2 : ℂ) • R' b.1‖ < r := by
      simpa using hr
    exact h0.eventually (gt_mem_nhds h1)
  filter_upwards [hpos] with q hq b
  by_cases hb : b.IsPositivelyOriented
  · exact hq ⟨b, hb⟩
  · have h := hq ⟨b.opposite, opposite_isPositivelyOriented_of_not hb⟩
    have hopp : (algebraMap ℝ ℂ q.1 • R + algebraMap ℝ ℂ q.2 • R') b.opposite =
        -(algebraMap ℝ ℂ q.1 • R + algebraMap ℝ ℂ q.2 • R') b := by
      simp only [Pi.add_apply, Pi.smul_apply, hR.2 b, hR'.2 b, smul_neg, neg_add]
    simp only [ComplexMatrix2.operatorNorm] at h ⊢
    rw [hopp, norm_neg] at h
    exact h
theorem ofReal_smul_add_mem {R R' : Edge L n 0 0 → ComplexMatrix2} (hR : R ∈ edgeFormSpace L n 0 0)
    (hR' : R' ∈ edgeFormSpace L n 0 0) (s t : ℝ) :
    algebraMap ℝ ℂ s • R + algebraMap ℝ ℂ t • R' ∈ edgeFormSpace L n 0 0 := by
  rw [algebraMap_smul, algebraMap_smul]
  exact (edgeFormSpace L n 0 0).add_mem ((edgeFormSpace L n 0 0).smul_mem s hR)
    ((edgeFormSpace L n 0 0).smul_mem t hR')
theorem hessianAtIdentity_eq [Finite (Tower.PositiveEdge L n 0 0)]
    (hc : ProjCellsClassified L n 0 0) {z r : ℝ} (hr : 0 < r)
    (hform : LogarithmsNearIdentity.IdentitiesBelow L n z r)
    (e : Fin N ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n))
    (h₁ : HasSecondFDerivAtZero (vertexLogDetReal L z e))
    (h₂ : HasSecondFDerivAtZero (edgeLogDetReal L z e))
    {R R' : Edge L n 0 0 → ComplexMatrix2} (hR : R ∈ edgeFormSpace L n 0 0)
    (hR' : R' ∈ edgeFormSpace L n 0 0) :
    hessianAtIdentity (massiveFieldFamily L z) n R R' =
      fderiv ℝ (fderiv ℝ (vertexLogDetReal L z e)) 0 (realCoordVec e R) (realCoordVec e R') -
        1 / 2 * fderiv ℝ (fderiv ℝ (edgeLogDetReal L z e)) 0 (realCoordVec e R)
          (realCoordVec e R') := by
  rw [← (hasSecondFDerivAtZero_sub_half h₁ h₂).2]
  unfold hessianAtIdentity leftSecondDeriv
  refine mixedDirectionalDeriv_eq_fderiv_fderiv (hasSecondFDerivAtZero_sub_half h₁ h₂).1 ?_
  filter_upwards [eventually_norm_lt hR hR' hr] with q hq
  have h := (hform _ (ofReal_smul_add_mem hR hR' q.1 q.2) hq).1
  rw [realCoordVec_add_smul hc e hR hR']
  show massiveLogDetFunctional L n z _ = _
  rw [h]
  simp only [realLogAbsDetDiffInCoords, ofRealCoords_realCoordVec]
theorem complexHessian_eq [Finite (Tower.PositiveEdge L n 0 0)]
    (hc : ProjCellsClassified L n 0 0) {z r : ℝ} (hr : 0 < r)
    (hform : LogarithmsNearIdentity.IdentitiesBelow L n z r)
    (e : Fin N ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n))
    (h₁ : HasSecondFDerivAtZero (vertexLogDetReal L z e))
    (h₂ : HasSecondFDerivAtZero (edgeLogDetReal L z e))
    {B B' : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0)
    (hB' : B' ∈ complexEdgeForms L n 0 0) :
    complexHessian (massiveFieldFamily L z) n B B' =
      realLogAbsDetSecondDeriv (colourEdges L 0 0) (colourVertices L 0 0)
          (vertexOpFun L z) e (remainderQuotField B) (remainderQuotField B') -
        1 / 2 * realLogAbsDetSecondDeriv (colourEdges L 0 0) (colourEdges L 0 0)
          (edgeOpFun L z) e (remainderQuotField B) (remainderQuotField B') := by
  have a₁ := realComponent_mem hB
  have a₂ := imagComponent_mem hB
  have a₃ := realComponent_mem hB'
  have a₄ := imagComponent_mem hB'
  have e₁ : (fun j => (toCoords e (remainderQuotField B) j).re) = realCoordVec e (realComponent B) :=
    funext fun j => (remainderQuotField_re_im hc hB (e j)).1
  have e₂ : (fun j => (toCoords e (remainderQuotField B) j).im) = realCoordVec e (imagComponent B) :=
    funext fun j => (remainderQuotField_re_im hc hB (e j)).2
  have e₃ : (fun j => (toCoords e (remainderQuotField B') j).re) = realCoordVec e (realComponent B') :=
    funext fun j => (remainderQuotField_re_im hc hB' (e j)).1
  have e₄ : (fun j => (toCoords e (remainderQuotField B') j).im) = realCoordVec e (imagComponent B') :=
    funext fun j => (remainderQuotField_re_im hc hB' (e j)).2
  unfold complexHessian realLogAbsDetSecondDeriv complexifiedSecondDeriv
  simp only [e₁, e₂, e₃, e₄]
  rw [hessianAtIdentity_eq hc hr hform e h₁ h₂ a₁ a₃, hessianAtIdentity_eq hc hr hform e h₁ h₂ a₂ a₄,
    hessianAtIdentity_eq hc hr hform e h₁ h₂ a₁ a₄, hessianAtIdentity_eq hc hr hform e h₁ h₂ a₂ a₃]
  push_cast
  ring
end Hessian
section LargeSides
open PeriodicOperators.Tempered (EventuallyForSides)
variable {L : ℕ}
theorem torusSide_le_iff (hL : 2 ≤ L) {m n : ℕ} :
    PeriodicLattice.torusSide L m ≤ PeriodicLattice.torusSide L n ↔ m ≤ n := by
  have h1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  simp only [PeriodicLattice.torusSide]
  rw [mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)]
  exact pow_le_pow_iff_right₀ h1
theorem exists_of_eventuallyForSides (hL : 2 ≤ L) {P : ℕ → Prop} (h : EventuallyForSides L P) :
    ∃ n₀, 1 ≤ n₀ ∧ ∀ n, n₀ ≤ n → P n := by apply _root_.YangMills.Construction.OneLoopLaw.SymbolCovariance.eventually_of_eventuallyForSides <;> assumption
theorem eventuallyForSides_of_forall_ge (hL : 2 ≤ L) {P : ℕ → Prop} {n₀ : ℕ}
    (h : ∀ n, n₀ ≤ n → P n) : EventuallyForSides L P := by
  refine ⟨PeriodicLattice.torusSide L (n₀ + 1), ⟨n₀ + 1, by omega, rfl⟩, ?_⟩
  rintro s - hs n - rfl
  exact h n (by have := (torusSide_le_iff hL).1 hs; omega)
theorem tendsto_mul_exp_neg (hL : 2 ≤ L) {c : ℝ} (hc : 0 < c) (C : ℝ) :
    Tendsto (fun n : ℕ => C * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ))) atTop (𝓝 0) := by
  have h1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have h2 : Tendsto (fun n : ℕ => ((2 * L ^ n : ℕ) : ℝ)) atTop atTop := by
    have h3 : Tendsto (fun n : ℕ => (2 : ℝ) * (L : ℝ) ^ n) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt h1).const_mul_atTop (by norm_num)
    simpa using h3
  have h4 : Tendsto (fun n : ℕ => -c * ((2 * L ^ n : ℕ) : ℝ)) atTop atBot :=
    h2.const_mul_atTop_of_neg (by linarith)
  simpa using (Real.tendsto_exp_atBot.comp h4).const_mul C
end LargeSides
section SingleFunction
open Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
open StripBound
open JetQuad (logNumber)
theorem tsum_tsum_single {C : Type} [Fintype C] [DecidableEq C] (f : C → C → ℂ) (c c' : C) :
    ∑' d, ∑' d', f d d' * (Pi.single c 1 : C → ℂ) d * (Pi.single c' 1 : C → ℂ) d' = f c c' := by
  simp [tsum_fintype, Pi.single_apply]
theorem logDet_data (h4 : LogDetSecondDerivs.Claim) (h5 : StripBound.Claim) {F I : PeriodicData}
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} (hT : IsLocalOpFun F I I T)
    (hu : ∀ κ : AmbientSpace, IsUnit (symbolHom I I (coeffZero F I I T) (toComplexVec κ) :
      Module.End ℂ (I.UnitQuot → ℂ)))
    (hre : IsRealOnRealFields F I T) :
    ∃ (δ M : ℝ) (O : Set (Fin 4 → ℂ)) (a : F.UnitQuot → F.UnitQuot → (Fin 4 → ℂ) → ℂ)
      (s₀ : ℕ) (C c : ℝ),
      0 < δ ∧ imStrip δ ⊆ O ∧ IsOpen O ∧ 0 < C ∧ 0 < c ∧
      (∀ d d', IsHolomorphicScalarIn O (a d d')) ∧
      (∀ p ∈ imStrip δ, ∀ (εPlus εMinus : F.UnitQuot → ℂ),
        logNumber p (jetAlong F I I T p εPlus εMinus) =
          ∑' d, ∑' d', a d d' p * εPlus d * εMinus d') ∧
      IsLogDetFormBound F I T δ M ∧
      ∀ s : ℕ, s₀ ≤ s → ∀ (N : ℕ) (e : Fin N ≃ F.QuotMod s),
        HasSecondFDerivAtZero (realLogAbsDetDiffInCoords F I T e) ∧
        IsCloseToLogNumber F I T s (realLogAbsDetSecondDeriv F I T e) C c := by
  classical
  obtain ⟨δ, hδ, hinv, -, ⟨O, hO, hsub, a, hol, hform⟩, hreal⟩ := h4 F I hF hI T hT hu
  obtain ⟨s₀, C, c, hC, hc, hcl⟩ := hreal hre
  have : Finite F.UnitQuot := hF.finite_quot
  have := Fintype.ofFinite F.UnitQuot
  have hw : IsAdmissibleWidth F I T δ := by
    refine ⟨hinv, fun p hp => ?_, fun d d' => ⟨O, hO, hsub, a d d', hol d d', fun p hp => ?_⟩⟩
    · refine ⟨LinearMap.mk₂ ℂ (fun x y => ∑ d, ∑ d', a d d' p * x d * y d') ?_ ?_ ?_ ?_,
        fun εPlus εMinus => ?_⟩
      · intro x x' y
        simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      · intro w x y
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      · intro x y y'
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      · intro w x y
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      · show logNumber p (jetAlong F I I T p εPlus εMinus) = _
        rw [hform p hp]
        simp [tsum_fintype]
    · show a d d' p = logNumber p (jetAlong F I I T p _ _)
      rw [hform p hp]
      convert (tsum_tsum_single (fun e e' => a e e' p) d d').symm
  obtain ⟨-, -, ⟨M, hM⟩, -⟩ := h5 F I hF hI T hT hu δ hδ hw
  refine ⟨δ, M, O, a, s₀, C, c, hδ, hsub, hO, hC, hc, hol, hform, hM, fun s hs N e => ?_⟩
  obtain ⟨-, h2, -, h3⟩ := hcl s hs N e
  exact ⟨h2, h3⟩
end SingleFunction
section Holomorphy
open Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn asLine)
theorem isHolomorphicIn_sub_half {O O₁ O₂ : Set (Fin 4 → ℂ)} {g₁ g₂ f : (Fin 4 → ℂ) → ℂ}
    (hO : IsOpen O) (s₁ : O ⊆ O₁) (s₂ : O ⊆ O₂) (hg₁ : IsHolomorphicScalarIn O₁ g₁)
    (hg₂ : IsHolomorphicScalarIn O₂ g₂) (hf : ∀ κ ∈ O, f κ = g₁ κ - 1 / 2 * g₂ κ) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O fun κ _ => f κ := by
  obtain ⟨-, c₁, d₁⟩ := hg₁
  obtain ⟨-, c₂, d₂⟩ := hg₂
  have hcont : ContinuousOn (fun (κ : Fin 4 → ℂ) (_ : Fin 1) => f κ) O := by
    have q : ContinuousOn (fun κ => (1 / 2 : ℂ) • asLine g₂ κ) O :=
      (c₂.mono s₂).const_smul (1 / 2 : ℂ)
    have h : ContinuousOn (fun κ => asLine g₁ κ - (1 / 2 : ℂ) • asLine g₂ κ) O :=
      (c₁.mono s₁).sub q
    refine h.congr fun κ hκ => ?_
    funext i
    simp [hf κ hκ, asLine]
  refine ⟨hO, hcont, fun a ha j => ?_⟩
  have hmap : Continuous fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by
    fun_prop
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈ O := by
    have h0 := hmap.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.eventually (hO.mem_nhds ha)
  filter_upwards [d₁ a (s₁ ha) j, d₂ a (s₂ ha) j, eventually_eventually_nhds.2 hnear] with ζ f₁ f₂ hζ
  have q : DifferentiableAt ℂ (fun ζ : ℂ =>
      (1 / 2 : ℂ) • asLine g₂ (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ :=
    f₂.const_smul (1 / 2 : ℂ)
  have D : DifferentiableAt ℂ (fun ζ : ℂ =>
      asLine g₁ (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) -
        (1 / 2 : ℂ) • asLine g₂ (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ :=
    f₁.sub q
  refine D.congr_of_eventuallyEq ?_
  filter_upwards [hζ] with ζ' h'
  funext i
  simp [hf _ h', asLine]
theorem continuous_comp_toComplexVec {O : Set (Fin 4 → ℂ)} {g : (Fin 4 → ℂ) → ℂ}
    (hg : IsHolomorphicScalarIn O g) (hO : ∀ y : AmbientSpace, toComplexVec y ∈ O) :
    Continuous fun y : AmbientSpace => g (toComplexVec y) := by
  have h1 : ContinuousOn g O := (continuous_apply (0 : Fin 1)).comp_continuousOn hg.2.1
  have h2 : Continuous toComplexVec := by
    unfold toComplexVec
    fun_prop
  exact h1.comp_continuous h2 hO
theorem toComplexVec_mem_imStrip {δ : ℝ} (hδ : 0 ≤ δ) (y : AmbientSpace) : toComplexVec y ∈ imStrip δ := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.toComplexVec_mem_imStrip <;> assumption
theorem isOpen_openStrip (δ : ℝ) : IsOpen {κ : Fin 4 → ℂ | ∀ μ, |(κ μ).im| < δ} := by apply _root_.YangMills.Construction.PeriodicOperators.ExpDecaySymbol.isOpen_openImStrip <;> assumption
end Holomorphy
section Assembly
open Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
open StripBound
open JetQuad (logNumber)
open PeriodicOperators.Tempered
def colourAxisClass (L : ℕ) (a : Fin 3) (μ : Fin 4) : (colourEdges L 0 0).UnitQuot :=
  (colourEdges L 0 0).mkQuot 1 (a, PlaneWaves.edgeAt L 0 0 μ)
theorem colourDirectionIndicator_eq_single {L : ℕ} [DecidableEq (colourEdges L 0 0).UnitQuot]
    (a : Fin 3) (μ : Fin 4) :
    colourDirectionIndicator L a μ = Pi.single (colourAxisClass L a μ) 1 := by
  funext c
  unfold colourDirectionIndicator
  rw [Pi.single_apply]
  by_cases h : c = colourAxisClass L a μ
  · exact (if_pos h).trans (if_pos h).symm
  · exact (if_neg h).trans (if_neg h).symm
theorem norm_sub_half_le (w D₁ D₂ l₁ l₂ : ℂ) {x₁ x₂ : ℝ} (h₁ : ‖w * D₁ - l₁‖ ≤ x₁)
    (h₂ : ‖w * D₂ - l₂‖ ≤ x₂) :
    ‖w * (D₁ - 1 / 2 * D₂) - (l₁ - 1 / 2 * l₂)‖ ≤ x₁ + 1 / 2 * x₂ := by
  have hsplit : w * (D₁ - 1 / 2 * D₂) - (l₁ - 1 / 2 * l₂) =
      (w * D₁ - l₁) - (1 / 2 : ℂ) * (w * D₂ - l₂) := by
    ring
  have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    simp
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, hh]
  linarith
theorem massiveFamily_isTempered (h₁ : MassiveStiffnessFunctions.FieldFamilyIsFunctional)
    (h₂ : LogarithmsNearIdentity.Claim) (h₃ : Locality.OpFunsLocal) (h₄ : LogDetSecondDerivs.Claim)
    (h₅ : StripBound.Claim)
    (h₆ : OneLoopLaw.GaugeColourMomenta.GaugeColourMomentumClaim)
    (h₇ : PeriodicOperators.Tempered.HessianSymbolDetermined.Claim)
    (h₈ : PeriodicOperators.DualLatticeDensity.Claim) (h₉ : PeriodicOperators.TowerIndexSets.Claim)
    (h₁₀ : LocalKernels.PeriodicLiftCells.CellsAndClassesHold) : MassiveFamilyTempered := by
  classical
  intro L hL z hz
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hL0 : 0 < L := by omega
  obtain ⟨hS, hBd, -⟩ := h₉ L hL 0 0 le_rfl
  obtain ⟨loc₁, loc₂, re₁, re₂, un₁, un₂⟩ := (h₃ L hL z hz).1
  obtain ⟨δ₁, M₁, O₁, a₁, t₁, C₁, c₁, hδ₁, sub₁, -, hC₁, hc₁, hol₁, form₁, bd₁, cl₁⟩ :=
    logDet_data h₄ h₅ hBd hS loc₁ un₁ re₁
  obtain ⟨δ₂, M₂, O₂, a₂, t₂, C₂, c₂, hδ₂, sub₂, -, hC₂, hc₂, hol₂, form₂, bd₂, cl₂⟩ :=
    logDet_data h₄ h₅ hBd hBd loc₂ un₂ re₂
  have hfun : IsLatticeFunctional L (massiveFieldFamily L z) := h₁ L hL z hz
  obtain ⟨n₁, hn₁, hmem⟩ := exists_of_eventuallyForSides hL2
    (P := fun n => IsAdmissibleMember (massiveFieldFamily L z n)) hfun
  obtain ⟨n₂, -, hnear⟩ := exists_of_eventuallyForSides hL2 (h₂ L hL z hz)
  obtain ⟨n₃, -, hdiag⟩ := exists_of_eventuallyForSides hL2 ((h₆ L hL0 hL).1 _ hfun)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = max (max n₁ n₂) (max n₃ (max t₁ t₂)) := ⟨_, rfl⟩
  have g₁ : n₁ ≤ n₀ := by omega
  have g₂ : n₂ ≤ n₀ := by omega
  have g₃ : n₃ ≤ n₀ := by omega
  have g₄ : t₁ ≤ n₀ := by omega
  have g₅ : t₂ ≤ n₀ := by omega
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ∑ a : Fin 3, ∑ μ : Fin 4,
      wNorm ((colourEdges L 0 0).quotWeight 1) (colourDirectionIndicator L a μ) := ⟨_, rfl⟩
  have hNn : ∀ (a : Fin 3) (μ : Fin 4),
      0 ≤ wNorm ((colourEdges L 0 0).quotWeight 1) (colourDirectionIndicator L a μ) :=
    fun _ _ => Real.sqrt_nonneg _
  have hK : ∀ (a : Fin 3) (μ : Fin 4),
      wNorm ((colourEdges L 0 0).quotWeight 1) (colourDirectionIndicator L a μ) ≤ K := by
    intro a μ
    rw [hKdef]
    refine le_trans ?_ (Finset.single_le_sum (f := fun a : Fin 3 => ∑ μ : Fin 4,
      wNorm ((colourEdges L 0 0).quotWeight 1) (colourDirectionIndicator L a μ))
      (fun a _ => Finset.sum_nonneg fun μ _ => hNn a μ) (Finset.mem_univ a))
    exact Finset.single_le_sum (f := fun μ : Fin 4 =>
      wNorm ((colourEdges L 0 0).quotWeight 1) (colourDirectionIndicator L a μ))
      (fun μ _ => hNn a μ) (Finset.mem_univ μ)
  have hK0 : 0 ≤ K := (hNn 0 0).trans (hK 0 0)
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ → ℝ, E = fun n =>
      C₁ * Real.exp (-c₁ * ((2 * L ^ n : ℕ) : ℝ)) * K * K +
        1 / 2 * (C₂ * Real.exp (-c₂ * ((2 * L ^ n : ℕ) : ℝ)) * K * K) := ⟨_, rfl⟩
  have hE0 : ∀ n, 0 ≤ E n := by
    intro n
    rw [hEdef]
    positivity
  have hEt : Tendsto E atTop (𝓝 0) := by
    have e₁ := (tendsto_mul_exp_neg hL2 hc₁ C₁).mul_const K |>.mul_const K
    have e₂ := ((tendsto_mul_exp_neg hL2 hc₂ C₂).mul_const K |>.mul_const K).const_mul (1 / 2 : ℝ)
    have e₃ := e₁.add e₂
    rw [hEdef]
    simpa using e₃
  have hclose : ∀ n, n₀ ≤ n → ∀ p ∈ dualLattice (2 * L ^ n), ∀ (a : Fin 3) (μ ν : Fin 4),
      ‖(((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ * complexHessian (massiveFieldFamily L z) n
          (fourierModeForm L n a p μ) (fourierModeForm L n a (-p) ν) -
        logSymbol L z a μ ν (toComplexVec p)‖ ≤ E n := by
    intro n hn p hp a μ ν
    have hn0 : 0 < n := by omega
    obtain ⟨hc, hb⟩ := (h₁₀ L hL 0 n hn0).1 0 le_rfl
    obtain ⟨inst, -⟩ := (hmem n (by omega)).analytic
    have : Finite (Tower.PositiveEdge L n 0 0) := Finite.of_fintype _
    have := finite_quotMod hc
    obtain ⟨r, hr, hform⟩ := hnear n (by omega)
    have hs : n ≤ 2 * L ^ n := by
      have := Nat.lt_pow_self (n := n) (by omega : 1 < L)
      omega
    obtain ⟨d₁, k₁⟩ := cl₁ (2 * L ^ n) (by omega) _
      (Finite.equivFin ((colourEdges L 0 0).QuotMod (2 * L ^ n))).symm
    obtain ⟨d₂, k₂⟩ := cl₂ (2 * L ^ n) (by omega) _
      (Finite.equivFin ((colourEdges L 0 0).QuotMod (2 * L ^ n))).symm
    have hneg : toComplexVec (-p) = -toComplexVec p := by
      funext μ
      simp [toComplexVec]
    rw [complexHessian_eq hc hr hform _ d₁ d₂ (fourierModeForm_mem hL2 hn0 a p μ)
      (fourierModeForm_mem hL2 hn0 a (-p) ν), remainderQuotField_fourierModeForm hc hL2 hb hp a μ,
      remainderQuotField_fourierModeForm hc hL2 hb (neg_mem hp) a ν, hneg]
    have b₁ := k₁ p hp (colourDirectionIndicator L a μ) (colourDirectionIndicator L a ν)
    have b₂ := k₂ p hp (colourDirectionIndicator L a μ) (colourDirectionIndicator L a ν)
    unfold logSymbol
    have hmono : ∀ A : ℝ, 0 ≤ A →
        A * wNorm ((colourEdges L 0 0).quotWeight 1) (colourDirectionIndicator L a μ) *
          wNorm ((colourEdges L 0 0).quotWeight 1) (colourDirectionIndicator L a ν) ≤
        A * K * K := by
      intro A hA
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hK a μ) hA) (hK a ν) (hNn a ν) (mul_nonneg hA hK0)
    have m₁ := b₁.trans (hmono _ (by positivity))
    have m₂ := b₂.trans (hmono _ (by positivity))
    simp only [hEdef]
    exact norm_sub_half_le _ _ _ _ _ m₁ m₂
  have : Finite (colourEdges L 0 0).UnitQuot := hBd.finite_quot
  have := Fintype.ofFinite (colourEdges L 0 0).UnitQuot
  have ev₁ : ∀ κ ∈ imStrip δ₁, ∀ (a : Fin 3) (μ ν : Fin 4),
      logNumber κ (jetAlong (colourEdges L 0 0) (colourVertices L 0 0) (colourVertices L 0 0)
        (vertexOpFun L z) κ (colourDirectionIndicator L a μ) (colourDirectionIndicator L a ν)) =
      a₁ (colourAxisClass L a μ) (colourAxisClass L a ν) κ := by
    intro κ hκ a μ ν
    rw [form₁ κ hκ, colourDirectionIndicator_eq_single, colourDirectionIndicator_eq_single]
    exact tsum_tsum_single (fun d d' => a₁ d d' κ) _ _
  have ev₂ : ∀ κ ∈ imStrip δ₂, ∀ (a : Fin 3) (μ ν : Fin 4),
      logNumber κ (jetAlong (colourEdges L 0 0) (colourEdges L 0 0) (colourEdges L 0 0)
        (edgeOpFun L z) κ (colourDirectionIndicator L a μ) (colourDirectionIndicator L a ν)) =
      a₂ (colourAxisClass L a μ) (colourAxisClass L a ν) κ := by
    intro κ hκ a μ ν
    rw [form₂ κ hκ, colourDirectionIndicator_eq_single, colourDirectionIndicator_eq_single]
    exact tsum_tsum_single (fun d d' => a₂ d d' κ) _ _
  have hsym : ∀ (a : Fin 3) (μ ν : Fin 4), ∀ κ, κ ∈ imStrip δ₁ → κ ∈ imStrip δ₂ →
      logSymbol L z a μ ν κ =
        a₁ (colourAxisClass L a μ) (colourAxisClass L a ν) κ -
          1 / 2 * a₂ (colourAxisClass L a μ) (colourAxisClass L a ν) κ := by
    intro a μ ν κ k₁ k₂
    unfold logSymbol
    rw [ev₁ κ k₁, ev₂ κ k₂]
  have hcolour : ∀ (a : Fin 3) (μ ν : Fin 4) (y : AmbientSpace),
      logSymbol L z a μ ν (toComplexVec y) = logSymbol L z 0 μ ν (toComplexVec y) := by
    intro a μ ν
    have r₁ : ∀ y : AmbientSpace, toComplexVec y ∈ imStrip δ₁ := toComplexVec_mem_imStrip hδ₁.le
    have r₂ : ∀ y : AmbientSpace, toComplexVec y ∈ imStrip δ₂ := toComplexVec_mem_imStrip hδ₂.le
    have hcont : Continuous fun y : AmbientSpace =>
        logSymbol L z a μ ν (toComplexVec y) - logSymbol L z 0 μ ν (toComplexVec y) := by
      have hfun_eq : (fun y : AmbientSpace => logSymbol L z a μ ν (toComplexVec y) -
          logSymbol L z 0 μ ν (toComplexVec y)) = fun y : AmbientSpace =>
          (a₁ (colourAxisClass L a μ) (colourAxisClass L a ν) (toComplexVec y) -
            1 / 2 * a₂ (colourAxisClass L a μ) (colourAxisClass L a ν) (toComplexVec y)) -
          (a₁ (colourAxisClass L 0 μ) (colourAxisClass L 0 ν) (toComplexVec y) -
            1 / 2 * a₂ (colourAxisClass L 0 μ) (colourAxisClass L 0 ν) (toComplexVec y)) := by
        funext y
        rw [hsym a μ ν _ (r₁ y) (r₂ y), hsym 0 μ ν _ (r₁ y) (r₂ y)]
      rw [hfun_eq]
      have q₁ := fun d d' => continuous_comp_toComplexVec (hol₁ d d') fun y => sub₁ (r₁ y)
      have q₂ := fun d d' => continuous_comp_toComplexVec (hol₂ d d') fun y => sub₂ (r₂ y)
      exact ((q₁ _ _).sub (continuous_const.mul (q₂ _ _))).sub
        ((q₁ _ _).sub (continuous_const.mul (q₂ _ _)))
    have hzero := ((h₈ L hL).2.2 _ n₀ (fun n => E n + E n) hcont (by omega)
      (fun n _ => add_nonneg (hE0 n) (hE0 n)) (by simpa using hEt.add hEt) (fun n hn p hp => ?_)).1
    · intro y
      exact sub_eq_zero.1 (hzero y)
    · obtain ⟨c, hcd⟩ := (hdiag n (by omega)).2.2.2.1 p hp μ ν
      have b₁ := hclose n hn p hp a μ ν
      have b₂ := hclose n hn p hp 0 μ ν
      rw [hcd a a, if_pos rfl] at b₁
      rw [hcd 0 0, if_pos rfl] at b₂
      have hdiff : logSymbol L z a μ ν (toComplexVec p) - logSymbol L z 0 μ ν (toComplexVec p) =
          ((((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ * c - logSymbol L z 0 μ ν (toComplexVec p)) -
            ((((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ * c - logSymbol L z a μ ν (toComplexVec p)) := by
        ring
      rw [hdiff]
      exact (norm_sub_le _ _).trans (add_le_add b₂ b₁)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₁ δ₂ := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδdef]
    exact lt_min hδ₁ hδ₂
  have le₁ : δ ≤ δ₁ := by
    rw [hδdef]
    exact min_le_left _ _
  have le₂ : δ ≤ δ₂ := by
    rw [hδdef]
    exact min_le_right _ _
  have hOo := isOpen_openStrip δ
  have hO₁ : {κ : Fin 4 → ℂ | ∀ μ, |(κ μ).im| < δ} ⊆ imStrip δ₁ :=
    fun κ hκ μ => (hκ μ).le.trans le₁
  have hO₂ : {κ : Fin 4 → ℂ | ∀ μ, |(κ μ).im| < δ} ⊆ imStrip δ₂ :=
    fun κ hκ μ => (hκ μ).le.trans le₂
  have hhalf : imStrip (δ / 2) ⊆ {κ : Fin 4 → ℂ | ∀ μ, |(κ μ).im| < δ} :=
    fun κ hκ μ => (hκ μ).trans_lt (by linarith)
  have witness : IsTemperedWitness L (massiveFieldFamily L z) (δ / 2)
      (fun μ ν κ => logSymbol L z 0 μ ν κ) E := by
    refine ⟨by linarith, ⟨_, hhalf, fun μ ν => ⟨?_, ?_⟩⟩, ?_, hEt, ?_⟩
    · exact isHolomorphicIn_sub_half hOo (hO₁.trans sub₁) (hO₂.trans sub₂) (hol₁ _ _) (hol₂ _ _)
        fun κ hκ => hsym 0 μ ν κ (hO₁ hκ) (hO₂ hκ)
    · refine ⟨M₁ * wNorm ((colourEdges L 0 0).quotWeight 1) (colourDirectionIndicator L 0 μ) *
          wNorm ((colourEdges L 0 0).quotWeight 1) (colourDirectionIndicator L 0 ν) +
        1 / 2 * (M₂ * wNorm ((colourEdges L 0 0).quotWeight 1) (colourDirectionIndicator L 0 μ) *
          wNorm ((colourEdges L 0 0).quotWeight 1) (colourDirectionIndicator L 0 ν)),
        fun κ hκ => ?_⟩
      have x₁ : ‖logNumber κ (jetAlong (colourEdges L 0 0) (colourVertices L 0 0)
          (colourVertices L 0 0) (vertexOpFun L z) κ (colourDirectionIndicator L 0 μ)
          (colourDirectionIndicator L 0 ν))‖ ≤ _ := bd₁ κ (hO₁ hκ) _ _
      have x₂ : ‖logNumber κ (jetAlong (colourEdges L 0 0) (colourEdges L 0 0)
          (colourEdges L 0 0) (edgeOpFun L z) κ (colourDirectionIndicator L 0 μ)
          (colourDirectionIndicator L 0 ν))‖ ≤ _ := bd₂ κ (hO₂ hκ) _ _
      have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
        simp
      show ‖logSymbol L z 0 μ ν κ‖ ≤ _
      unfold logSymbol
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, hh]
      linarith
    · exact eventuallyForSides_of_forall_ge hL2 (n₀ := 0) fun n _ => hE0 n
    · refine eventuallyForSides_of_forall_ge hL2 (n₀ := n₀) fun n hn p hp a a' μ ν => ?_
      obtain ⟨c, hcd⟩ := (hdiag n (by omega)).2.2.2.1 p hp μ ν
      have hscal : (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) =
          (((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ := by
        push_cast [PeriodicLattice.torusSide]
        rw [inv_pow]
      rw [hscal, hcd a a']
      by_cases haa : a = a'
      · subst haa
        have b₂ := hclose n hn p hp 0 μ ν
        rw [hcd 0 0, if_pos rfl] at b₂
        rw [if_pos rfl, if_pos rfl]
        exact b₂
      · rw [if_neg haa, if_neg haa]
        simpa using hE0 n
  have htemp : IsTemperedFunctional L (massiveFieldFamily L z) := ⟨hfun, δ / 2, _, E, witness⟩
  refine ⟨htemp, fun p a μ ν => ?_⟩
  obtain ⟨-, P, hP, -⟩ := h₇ L hL _ htemp
  have spec : IsHessianSymbol L (massiveFieldFamily L z) (hessianSymbol L (massiveFieldFamily L z)) :=
    Classical.epsilon_spec (p := IsHessianSymbol L (massiveFieldFamily L z)) ⟨P, hP⟩
  rw [spec _ _ _ witness μ ν (toComplexVec_mem_imStrip (by linarith) p), hcolour a μ ν p]
end Assembly
end YangMills.Construction.Tower.MassiveOpFunctions.Tempered
end
