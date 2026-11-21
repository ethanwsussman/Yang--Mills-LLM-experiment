import YangMills.Construction.OneLoopLaw.KernelsOfATemperingChoiceProof
import YangMills.Construction.RunningCouplingSlope.TheNormaliserReadsTheResponseOnLongWaves
import YangMills.Construction.Towers.ImagesUnderTheResponseReadAtTheSideInfinity
import YangMills.Construction.Towers.ResponseFieldOfAPlaneWaveProof
import YangMills.Construction.Towers.TheSecondDifferentialAtTheResponseSymbolsNearZero
import YangMills.Construction.Towers.TheSecondDifferentialIsCloseToItsSymbol
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.LongWaveNormaliser
open Tower Tower.CriticalBranchResponse
open PeriodicOperators (colourEdges toComplexVec bilinDot dualLattice castVec)
open Tower.TorusResponseField
open PeriodicOperators.Tempered (UnitEdge imagComponent realComponent)
open LocalKernels (projPositiveEdge)
open LocalKernels.Periodisation (ProjCellsClassified ProjEdgesCompatible periodSide)
open InfiniteLattice (AmbientSpace)
open Matrices (ComplexMatrix2)
open SlopeCoefficient (secondAxis)
private theorem pauliCoeff_of_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a X = OneLoop.pauliCoordinateEquiv ⟨X, h⟩ a :=
  dif_pos h
private theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
section Forms
variable {L n k : ℕ}
private theorem opposite_isPositive_of_not {j : ℕ} {b : Edge L n k j} (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
private theorem complexEdgeForm_ext {j : ℕ} (hc : ProjCellsClassified L n k j)
    {A A' : complexEdgeForms L n k j}
    (h : ∀ ι : (colourEdges L k j).Carrier,
      (edgePauliCoordinates L n k j).coeffs A.1 (ι.1, projPositiveEdge L n k j ι.2) =
        (edgePauliCoordinates L n k j).coeffs A'.1 (ι.1, projPositiveEdge L n k j ι.2)) :
    A = A' := by apply _root_.YangMills.Construction.Tower.ResponseOfFourierMode.complexForm_ext_of_coeffs <;> assumption
private theorem periodicField_ext (hL : 0 < L) (hc₀ : ProjCellsClassified L n k 0)
    (hc : ProjCellsClassified L n k k) {ζ ζ' : PeriodicField L n k}
    (h : ζ.pauliCoeffs hL = ζ'.pauliCoeffs hL) : ζ = ζ' := by apply _root_.YangMills.Construction.Tower.ResponseOfFourierMode.periodicField_ext <;> assumption
private theorem exists_complexEdgeForm_of_periodic {j : ℕ} (hL : 2 ≤ L)
    (hj : -(n : ℤ) < PeriodicLattice.levelDepth k j)
    (hcf : ResponseOperators.ClassFnsAreForms L n k j)
    (g : (colourEdges L k j).Carrier → ℂ)
    (hg : ∀ (ι : (colourEdges L k j).Carrier) (m : Fin 4 → ℤ),
      g ((colourEdges L k j).translate (periodSide L n • m) ι) = g ι) :
    ∃ A : complexEdgeForms L n k j, ∀ ι : (colourEdges L k j).Carrier,
      (edgePauliCoordinates L n k j).coeffs A.1 (ι.1, projPositiveEdge L n k j ι.2) = g ι := by
  classical
  let q : (colourEdges L k j).QuotMod (periodSide L n) → ℂ :=
    Quot.lift g (by
      rintro ι _ ⟨m, rfl⟩
      exact (hg ι m).symm)
  obtain ⟨f, ⟨hf, hq⟩, -⟩ := hcf q
  let A : Edge L n k j → ComplexMatrix2 :=
    extendOddly fun b => if h : b.IsPositivelyOriented then f ⟨b, h⟩ else 0
  have hrr : ∀ b : Edge L n k j, b.opposite.opposite = b :=
    fun b => PeriodicLattice.Bond.ext rfl rfl
  have hA : A ∈ complexEdgeForms L n k j := by
    refine ⟨fun b hb => ?_, fun b => ?_⟩
    · simp only [A, extendOddly, if_pos hb, dif_pos hb]
      exact hf ⟨b, hb⟩ (Set.mem_univ _)
    · rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (L := L) (m := n)
          (j := PeriodicLattice.levelDepth k j) hL hj b with ⟨h, h'⟩ | ⟨h', h⟩
      · simp only [A, extendOddly, if_pos h, if_neg h', hrr]
      · simp only [A, extendOddly, if_pos h', if_neg h, hrr, neg_neg]
  refine ⟨⟨A, hA⟩, fun ι => ?_⟩
  have e := hq ι
  have hv : restrictToPositiveEdges A = f := by
    funext c
    simp only [restrictToPositiveEdges, A, extendOddly, if_pos c.2, dif_pos c.2]
  show toPauliCoeffs (restrictToPositiveEdges A) _ = _
  rw [hv]
  exact e.symm
end Forms
section Wave
variable {L n k : ℕ}
private theorem exp_phase_translate {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n)) (hL : 0 < L)
    (x : AmbientSpace) (m : Fin 4 → ℤ) :
    Complex.exp (Complex.I * bilinDot (toComplexVec p)
        (toComplexVec (x + castVec (periodSide L n • m)))) =
      Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec x)) := by
  have hs : ((2 * L ^ n : ℕ) : ℝ) ≠ 0 := by
    have : 0 < 2 * L ^ n := by positivity
    exact_mod_cast this.ne'
  obtain ⟨r, hr⟩ := hp
  have h2 : bilinDot (toComplexVec p) (toComplexVec (x + castVec (periodSide L n • m))) =
      bilinDot (toComplexVec p) (toComplexVec x) + ((∑ μ, r μ * m μ : ℤ) : ℂ) * (2 * Real.pi) := by
    simp only [bilinDot, toComplexVec]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have h3 : p μ * (x + castVec (periodSide L n • m)) μ =
        p μ * x μ + (r μ : ℝ) * (m μ : ℝ) * (2 * Real.pi) := by
      have e : (x + castVec (periodSide L n • m)) μ =
          x μ + ((2 * L ^ n : ℕ) : ℝ) * (m μ : ℝ) := by
        simp [castVec, periodSide]
      rw [e, hr μ]
      field_simp
    have h4 := congrArg (fun u : ℝ => (u : ℂ)) h3
    push_cast at h4
    exact h4
  have h5 : Complex.I * (((∑ μ, r μ * m μ : ℤ) : ℂ) * (2 * Real.pi)) =
      ((∑ μ, r μ * m μ : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    ring
  rw [h2, mul_add, Complex.exp_add, h5, Complex.exp_int_mul_two_pi_mul_I, mul_one]
private theorem exists_field_of_blochWave (hL : 0 < L) (hL2 : 2 ≤ L) (hnk : k < n)
    (hOn : ResponseOperators.TorusSideFacts L n k)
    (hp₀ : PeriodicOperators.IsPeriodic (colourEdges L k 0))
    (hpk : PeriodicOperators.IsPeriodic (colourEdges L k k))
    {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n))
    (ε : (FullSpace.fieldPeriodicData L k hL).UnitQuot → ℂ) :
    ∃ ζ : PeriodicField L n k, ζ.pauliCoeffs hL =
      PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL) (toComplexVec p) ε := by
  have hd₀ : -(n : ℤ) < PeriodicLattice.levelDepth k 0 := by
    simp [PeriodicLattice.levelDepth]
    omega
  have hdk : -(n : ℤ) < PeriodicLattice.levelDepth k k := by
    simp [PeriodicLattice.levelDepth]
    omega
  obtain ⟨A₁, h₁⟩ := exists_complexEdgeForm_of_periodic hL2 hd₀ hOn.forms_bottom
    (fun ι => PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL) (toComplexVec p) ε
      ⟨.background, ι⟩) (by
        intro ι m
        show Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec
            ((colourEdges L k 0).pos ((colourEdges L k 0).translate (periodSide L n • m) ι)))) *
            ε ((FullSpace.fieldPeriodicData L k hL).mkQuot 1
              ⟨.background, (colourEdges L k 0).translate (periodSide L n • m) ι⟩) =
          Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec
            ((colourEdges L k 0).pos ι))) *
            ε ((FullSpace.fieldPeriodicData L k hL).mkQuot 1 ⟨.background, ι⟩)
        rw [hp₀.pos_translate, exp_phase_translate hp hL]
        congr 2
        exact (Quot.sound ⟨periodSide L n • m, by rw [one_smul]; rfl⟩).symm)
  obtain ⟨A₂, h₂⟩ := exists_complexEdgeForm_of_periodic hL2 hd₀ hOn.forms_bottom
    (fun ι => PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL) (toComplexVec p) ε
      ⟨.source, ι⟩) (by
        intro ι m
        show Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec
            ((colourEdges L k 0).pos ((colourEdges L k 0).translate (periodSide L n • m) ι)))) *
            ε ((FullSpace.fieldPeriodicData L k hL).mkQuot 1
              ⟨.source, (colourEdges L k 0).translate (periodSide L n • m) ι⟩) =
          Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec
            ((colourEdges L k 0).pos ι))) *
            ε ((FullSpace.fieldPeriodicData L k hL).mkQuot 1 ⟨.source, ι⟩)
        rw [hp₀.pos_translate, exp_phase_translate hp hL]
        congr 2
        exact (Quot.sound ⟨periodSide L n • m, by rw [one_smul]; rfl⟩).symm)
  obtain ⟨A₃, h₃⟩ := exists_complexEdgeForm_of_periodic hL2 hdk hOn.forms_top
    (fun ι => PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL) (toComplexVec p) ε
      ⟨.coarse, ι⟩) (by
        intro ι m
        show Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec
            ((colourEdges L k k).pos ((colourEdges L k k).translate (periodSide L n • m) ι)))) *
            ε ((FullSpace.fieldPeriodicData L k hL).mkQuot 1
              ⟨.coarse, (colourEdges L k k).translate (periodSide L n • m) ι⟩) =
          Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec
            ((colourEdges L k k).pos ι))) *
            ε ((FullSpace.fieldPeriodicData L k hL).mkQuot 1 ⟨.coarse, ι⟩)
        rw [hpk.pos_translate, exp_phase_translate hp hL]
        congr 2
        exact (Quot.sound ⟨periodSide L n • m, by rw [one_smul]; rfl⟩).symm)
  refine ⟨(A₁, A₂, A₃), ?_⟩
  funext x
  rcases x with ⟨pl, ι⟩
  cases pl
  · exact h₁ ι
  · exact h₂ ι
  · exact h₃ ι
private theorem tripleAmplitude_mkQuot (hL : 0 < L) (a j : (colourEdges L k 0).UnitQuot → ℂ)
    (m : (colourEdges L k k).UnitQuot → ℂ) (x : (FullSpace.fieldPeriodicData L k hL).Carrier) :
    FullSpace.tripleAmplitude L k hL a j m ((FullSpace.fieldPeriodicData L k hL).mkQuot 1 x) =
      FullSpace.tripleIndexFunction L k hL a j m x := by apply _root_.YangMills.Construction.Tower.ResponseOfFourierMode.tripleAmplitude_mkQuot <;> assumption
private theorem blochWaveField_background_only (hL : 0 < L) (hL2 : 2 ≤ L) (hnk : k < n)
    (hOn : ResponseOperators.TorusSideFacts L n k)
    (hp₀ : PeriodicOperators.IsPeriodic (colourEdges L k 0))
    (hpk : PeriodicOperators.IsPeriodic (colourEdges L k k))
    (hc₀ : ProjCellsClassified L n k 0) (hc : ProjCellsClassified L n k k)
    {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n)) (a j : (colourEdges L k 0).UnitQuot → ℂ)
    (m : (colourEdges L k k).UnitQuot → ℂ) :
    blochWaveField L n k hL (toComplexVec p) (FullSpace.tripleAmplitude L k hL a 0 0) =
      ((blochWaveField L n k hL (toComplexVec p) (FullSpace.tripleAmplitude L k hL a j m)).1,
        0, 0) := by
  have hs := Classical.epsilon_spec (exists_field_of_blochWave (n := n) hL hL2 hnk hOn hp₀ hpk hp
    (FullSpace.tripleAmplitude L k hL a j m))
  set ζ := blochWaveField L n k hL (toComplexVec p) (FullSpace.tripleAmplitude L k hL a j m)
    with hζ
  have hs' : ζ.pauliCoeffs hL = PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL)
      (toComplexVec p) (FullSpace.tripleAmplitude L k hL a j m) := hs
  have key : (PeriodicField.pauliCoeffs hL ((ζ.1, 0, 0) : PeriodicField L n k)) =
      PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL) (toComplexVec p)
        (FullSpace.tripleAmplitude L k hL a 0 0) := by
    funext x
    have hv : PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL) (toComplexVec p)
        (FullSpace.tripleAmplitude L k hL a 0 0) x =
        Complex.exp (Complex.I * bilinDot (toComplexVec p)
            (toComplexVec ((FullSpace.fieldPeriodicData L k hL).pos x))) *
          FullSpace.tripleIndexFunction L k hL a 0 0 x :=
      congrArg (fun w => Complex.exp (Complex.I * bilinDot (toComplexVec p)
        (toComplexVec ((FullSpace.fieldPeriodicData L k hL).pos x))) * w)
        (tripleAmplitude_mkQuot hL _ _ _ x)
    rw [hv]
    rcases x with ⟨pl, ι⟩
    cases pl
    · have h1 := congrFun hs' ⟨.background, ι⟩
      have hv' : PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL) (toComplexVec p)
          (FullSpace.tripleAmplitude L k hL a j m) ⟨.background, ι⟩ =
          Complex.exp (Complex.I * bilinDot (toComplexVec p)
              (toComplexVec ((FullSpace.fieldPeriodicData L k hL).pos ⟨.background, ι⟩))) *
            FullSpace.tripleIndexFunction L k hL a j m ⟨.background, ι⟩ :=
        congrArg (fun w => Complex.exp (Complex.I * bilinDot (toComplexVec p)
          (toComplexVec ((FullSpace.fieldPeriodicData L k hL).pos ⟨.background, ι⟩))) * w)
          (tripleAmplitude_mkQuot hL _ _ _ _)
      exact h1.trans hv'
    · show pauliCoeff ι.1 ((0 : Edge L n k 0 → ComplexMatrix2) _) = _
      rw [Pi.zero_apply, pauliCoeff_zero]
      show (0 : ℂ) = _ * (0 : ℂ)
      rw [mul_zero]
    · show pauliCoeff ι.1 ((0 : Edge L n k k → ComplexMatrix2) _) = _
      rw [Pi.zero_apply, pauliCoeff_zero]
      show (0 : ℂ) = _ * (0 : ℂ)
      rw [mul_zero]
  have hex : ∃ ξ : PeriodicField L n k, ξ.pauliCoeffs hL =
      PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL) (toComplexVec p)
        (FullSpace.tripleAmplitude L k hL a 0 0) := ⟨_, key⟩
  exact periodicField_ext hL hc₀ hc ((Classical.epsilon_spec hex).trans key.symm)
end Wave
section Top
variable {L n k : ℕ}
private theorem topEdge_isPositive {b : Edge L n k k} (hb : b.IsPositivelyOriented) :
    (topEdgeEquivUnit L n k b).IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.ResponseOfFourierMode.topEdgeEquivUnit_isPositivelyOriented <;> assumption
private theorem topEdge_opposite (b : Edge L n k k) :
    topEdgeEquivUnit L n k b.opposite = (topEdgeEquivUnit L n k b).opposite :=
  PeriodicLattice.Bond.ext rfl rfl
private theorem fourierModeForm_mem (hL : 2 ≤ L) (hn : 0 < n) (a : Fin 3) (p : AmbientSpace)
    (μ : Fin 4) :
    PeriodicOperators.Tempered.fourierModeForm L n a p μ ∈ complexEdgeForms L n 0 0 := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.fourierModeForm_mem <;> assumption
private theorem phase_coe (hL : 0 < L) {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n))
    (y : AmbientSpace) :
    PeriodicOperators.Tempered.phase (L := L) (n := n) p
        (fun μ => ((y μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) =
      Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec y)) := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.phase_coe <;> assumption
private theorem coe_offsetSite (w : Fin 4 → ℤ) :
    ((PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) w :
        Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) =
      fun ρ => ((w ρ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
  have hs : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
    simp [PeriodicLattice.meshSize]
  funext ρ
  have e : ((PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) w :
      Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) =
      ∑ μ, w μ • ((PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ :
        Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) := by
    simp [PeriodicLattice.offsetSite]
  rw [e, Finset.sum_apply, Finset.sum_eq_single ρ]
  · simp only [Pi.smul_apply, PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, hs,
      Pi.single_eq_same]
    have e2 : (w ρ : ℝ) = w ρ • (1 : ℝ) := by simp
    rw [e2]
    rfl
  · intro μ _ h
    simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne (Ne.symm h)]
  · simp
private theorem fourierModeForm_topEdge (q : AmbientSpace) (b : Edge L n k k)
    (hb : b.IsPositivelyOriented) (μ : Fin 4) (a : Fin 3) :
    PeriodicOperators.Tempered.fourierModeForm L n a q μ (topEdgeEquivUnit L n k b) =
      open Classical in
      if b.target - b.source = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ then
        PeriodicOperators.Tempered.phase q (b.source : PeriodicLattice.FourTorus L n) •
          ComplexMatrix2.pauliFamily a else 0 := by
  classical
  simp only [PeriodicOperators.Tempered.fourierModeForm, extendOddly, if_pos (topEdge_isPositive hb)]
  by_cases h : b.target - b.source = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ
  · have h' : (topEdgeEquivUnit L n k b).target - (topEdgeEquivUnit L n k b).source =
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) μ := by
      show topVertexEquivUnit L n k b.target - topVertexEquivUnit L n k b.source = _
      rw [← map_sub, h, topVertexEquivUnit_unitStep]
    rw [if_pos h', if_pos h]
    rfl
  · rw [if_neg h, if_neg]
    intro e
    apply h
    apply (topVertexEquivUnit L n k).injective
    rw [map_sub]
    exact e.trans (topVertexEquivUnit_unitStep L n k μ).symm
private theorem pauliFamily_two_conjTranspose :
    (ComplexMatrix2.pauliFamily 2).conjTranspose = ComplexMatrix2.pauliFamily 2 := by
  obtain ⟨-, -, h2⟩ := ComplexMatrix2.pauliFamily_apply
  rw [h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
private theorem half_add_conjTranspose_smul (c : ℂ) :
    (2⁻¹ : ℂ) • (c • ComplexMatrix2.pauliFamily 2 + (c • ComplexMatrix2.pauliFamily 2).conjTranspose) =
      c.re • ComplexMatrix2.pauliFamily 2 := by
  rw [Matrix.conjTranspose_smul, pauliFamily_two_conjTranspose, ← add_smul, smul_smul]
  have e : (2⁻¹ : ℂ) * (c + star c) = (c.re : ℂ) := by
    apply Complex.ext <;> simp
    · ring
  rw [e]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]
private theorem half_sub_conjTranspose_smul (c : ℂ) :
    (2 * Complex.I)⁻¹ •
        (c • ComplexMatrix2.pauliFamily 2 - (c • ComplexMatrix2.pauliFamily 2).conjTranspose) =
      c.im • ComplexMatrix2.pauliFamily 2 := by
  rw [Matrix.conjTranspose_smul, pauliFamily_two_conjTranspose, ← sub_smul, smul_smul]
  have e0 : c - star c = 2 * Complex.I * (c.im : ℂ) := by
    apply Complex.ext <;> simp
    · ring
  have e : (2 * Complex.I)⁻¹ * (c - star c) = (c.im : ℂ) := by
    rw [e0]
    field_simp
  rw [e]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]
private theorem planeWaveValues_apply [NeZero (2 * L ^ n)]
    (hinj : ∀ x x' : TorusFields.TorusSite (2 * L ^ n),
      PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) (centredCoords x) =
        PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) (centredCoords x') →
        x = x')
    (f : TorusFields.TorusSite (2 * L ^ n) → ℝ) (x : TorusFields.TorusSite (2 * L ^ n))
    (b : Edge L n k k) (hb : b.IsPositivelyOriented)
    (ht : b.source = PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) (centredCoords x)) :
    planeWaveValues L n k f b =
      open Classical in
      if b.target - b.source = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) secondAxis
      then f x • ComplexMatrix2.pauliFamily 2 else 0 := by
  classical
  have hval : ∀ x' : TorusFields.TorusSite (2 * L ^ n), pauliUnitForm L n k (centredCoords x') b =
      if b = PeriodicLattice.Bond.forwardFrom
          (PeriodicLattice.offsetSite 0 (centredCoords x')) secondAxis
      then ComplexMatrix2.pauliFamily 2 else 0 := by
    intro x'
    simp only [pauliUnitForm, extendOddly, if_pos hb]
  show (∑ x', f x' • pauliUnitForm L n k (centredCoords x')) b = _
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, hval]
  by_cases h : b.target - b.source = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) secondAxis
  · rw [if_pos h, Finset.sum_eq_single x]
    · rw [if_pos]
      apply PeriodicLattice.Bond.ext ht
      show b.target = PeriodicLattice.offsetSite 0 (centredCoords x) + _
      rw [← ht, ← h]
      abel
    · intro x' _ hne
      rw [if_neg, smul_zero]
      intro e
      have e' : b.source = PeriodicLattice.offsetSite 0 (centredCoords x') := by
        rw [e]
        rfl
      exact hne (hinj x' x (e'.symm.trans ht))
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro x' _
    rw [if_neg, smul_zero]
    intro e
    apply h
    rw [e]
    simp [PeriodicLattice.Bond.forwardFrom]
private theorem topForm_part_eq [NeZero (2 * L ^ n)] (hL : 2 ≤ L) (hn : 0 < n)
    (hex : ∀ y : Tower.Vertex L n k k, ∃ x : TorusFields.TorusSite (2 * L ^ n),
      y = PeriodicLattice.offsetSite 0 (centredCoords x))
    (hinj : ∀ x x' : TorusFields.TorusSite (2 * L ^ n),
      PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) (centredCoords x) =
        PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) (centredCoords x') →
        x = x')
    (Pt : ComplexMatrix2 → ComplexMatrix2) (hneg : ∀ X, Pt (-X) = -Pt X) (hz : Pt 0 = 0)
    (g : ℂ → ℝ) (hg : ∀ c : ℂ, Pt (c • ComplexMatrix2.pauliFamily 2) = g c • ComplexMatrix2.pauliFamily 2)
    {q : AmbientSpace} (hq : q ∈ dualLattice (2 * L ^ n)) (f : TorusFields.TorusSite (2 * L ^ n) → ℝ)
    (hf : ∀ x, f x = g (Complex.exp (Complex.I * bilinDot (toComplexVec q)
      (toComplexVec (castVec (centredCoords x))))))
    (D : edgeFormSpace L n k k) (hD : (D : Edge L n k k → ComplexMatrix2) = planeWaveValues L n k f) :
    (fun b => Pt (PeriodicOperators.Tempered.fourierModeForm L n 2 q secondAxis
      (topEdgeEquivUnit L n k b))) = (D : Edge L n k k → ComplexMatrix2) := by
  classical
  have hpos : ∀ b : Edge L n k k, b.IsPositivelyOriented →
      Pt (PeriodicOperators.Tempered.fourierModeForm L n 2 q secondAxis (topEdgeEquivUnit L n k b)) =
        (D : Edge L n k k → ComplexMatrix2) b := by
    intro b hb
    obtain ⟨x, hx⟩ := hex b.source
    have hL0 : 0 < L := by omega
    rw [hD, planeWaveValues_apply hinj f x b hb hx, fourierModeForm_topEdge q b hb]
    by_cases h : b.target - b.source =
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) secondAxis
    · rw [if_pos h, if_pos h, hg, hf x, hx, coe_offsetSite]
      congr 2
      exact phase_coe hL0 hq (castVec (centredCoords x))
    · rw [if_neg h, if_neg h, hz]
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact hpos b hb
  · have r := opposite_isPositive_of_not hb
    have e : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
    have h1 := hpos _ r
    have hE := (fourierModeForm_mem hL hn 2 q secondAxis).2 (topEdgeEquivUnit L n k b.opposite)
    have hD' := D.2.2 b.opposite
    rw [e] at hD'
    rw [← topEdge_opposite, e] at hE
    rw [hE, hneg, h1, hD']
end Top
section Slots
variable {L n k : ℕ}
private theorem complexify_spec (r : RealPeriodicField L n k) :
    (complexify r).RealizedBy r := by apply _root_.YangMills.SharedProofs.p20583 <;> assumption
private def backgroundSlotField (L n k : ℕ) (X : Edge L n k k → ComplexMatrix2) : PeriodicField L n k :=
  complexify ((meshScaledResponse L n k X, 0, 0) : RealPeriodicField L n k)
private theorem complexResponse_background_slot (E : UnitEdge L n → ComplexMatrix2)
    (X Y : Edge L n k k → ComplexMatrix2)
    (hX : topForm L n k (realComponent E) = X)
    (hY : topForm L n k (imagComponent E) = Y) :
    (((complexResponse L n k E).1, 0, 0) : PeriodicField L n k) =
      backgroundSlotField L n k X + Complex.I • backgroundSlotField L n k Y := by
  have hfr := complexify_spec (responseField L n k X)
  have hfs := complexify_spec (responseField L n k Y)
  have hx := complexify_spec ((meshScaledResponse L n k X, 0, 0) : RealPeriodicField L n k)
  have hy := complexify_spec ((meshScaledResponse L n k Y, 0, 0) : RealPeriodicField L n k)
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · show ((complexResponse L n k E).1 : Edge L n k 0 → ComplexMatrix2) =
      ((backgroundSlotField L n k X).1 : Edge L n k 0 → ComplexMatrix2) +
        Complex.I • ((backgroundSlotField L n k Y).1 : Edge L n k 0 → ComplexMatrix2)
    rw [show ((backgroundSlotField L n k X).1 : Edge L n k 0 → ComplexMatrix2) = _ from hx.1,
      show ((backgroundSlotField L n k Y).1 : Edge L n k 0 → ComplexMatrix2) = _ from hy.1]
    show ((complexify (responseField L n k (topForm L n k (realComponent E)))).1 :
        Edge L n k 0 → ComplexMatrix2) +
      Complex.I • ((complexify
        (responseField L n k (topForm L n k (imagComponent E)))).1 :
          Edge L n k 0 → ComplexMatrix2) = _
    rw [hX, hY, hfr.1, hfs.1]
    rfl
  · show (0 : Edge L n k 0 → ComplexMatrix2) =
      ((backgroundSlotField L n k X).2.1 : Edge L n k 0 → ComplexMatrix2) +
        Complex.I • ((backgroundSlotField L n k Y).2.1 : Edge L n k 0 → ComplexMatrix2)
    rw [show ((backgroundSlotField L n k X).2.1 : Edge L n k 0 → ComplexMatrix2) = _ from hx.2.1,
      show ((backgroundSlotField L n k Y).2.1 : Edge L n k 0 → ComplexMatrix2) = _ from hy.2.1]
    simp
  · show (0 : Edge L n k k → ComplexMatrix2) =
      ((backgroundSlotField L n k X).2.2 : Edge L n k k → ComplexMatrix2) +
        Complex.I • ((backgroundSlotField L n k Y).2.2 : Edge L n k k → ComplexMatrix2)
    rw [show ((backgroundSlotField L n k X).2.2 : Edge L n k k → ComplexMatrix2) = _ from hx.2.2,
      show ((backgroundSlotField L n k Y).2.2 : Edge L n k k → ComplexMatrix2) = _ from hy.2.2]
    simp
private theorem backgroundSlotField_neg {X X' : Edge L n k k → ComplexMatrix2}
    (h : meshScaledResponse L n k X' = -meshScaledResponse L n k X) :
    backgroundSlotField L n k X' = -backgroundSlotField L n k X := by
  have hx := complexify_spec ((meshScaledResponse L n k X, 0, 0) : RealPeriodicField L n k)
  have hy := complexify_spec ((meshScaledResponse L n k X', 0, 0) : RealPeriodicField L n k)
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · show ((backgroundSlotField L n k X').1 : Edge L n k 0 → ComplexMatrix2) =
      -((backgroundSlotField L n k X).1 : Edge L n k 0 → ComplexMatrix2)
    rw [show ((backgroundSlotField L n k X').1 : Edge L n k 0 → ComplexMatrix2) = _ from hy.1,
      show ((backgroundSlotField L n k X).1 : Edge L n k 0 → ComplexMatrix2) = _ from hx.1]
    simp [h]
  · show ((backgroundSlotField L n k X').2.1 : Edge L n k 0 → ComplexMatrix2) =
      -((backgroundSlotField L n k X).2.1 : Edge L n k 0 → ComplexMatrix2)
    rw [show ((backgroundSlotField L n k X').2.1 : Edge L n k 0 → ComplexMatrix2) = _ from hy.2.1,
      show ((backgroundSlotField L n k X).2.1 : Edge L n k 0 → ComplexMatrix2) = _ from hx.2.1]
    simp
  · show ((backgroundSlotField L n k X').2.2 : Edge L n k k → ComplexMatrix2) =
      -((backgroundSlotField L n k X).2.2 : Edge L n k k → ComplexMatrix2)
    rw [show ((backgroundSlotField L n k X').2.2 : Edge L n k k → ComplexMatrix2) = _ from hy.2.2,
      show ((backgroundSlotField L n k X).2.2 : Edge L n k k → ComplexMatrix2) = _ from hx.2.2]
    simp
private theorem complexSecondDeriv_conj_pair (hext : IsComplexSecondDeriv L n k
      (complexSecondDeriv L n k))
    (hsym : ∀ ζ ζ' : PeriodicField L n k, complexSecondDeriv L n k ζ ζ' =
      complexSecondDeriv L n k ζ' ζ) (A B : edgeFormSpace L n k k) :
    complexSecondDeriv L n k
        (backgroundSlotField L n k A + Complex.I • backgroundSlotField L n k B)
        (backgroundSlotField L n k A + Complex.I • -backgroundSlotField L n k B) =
      ((normaliserHessianAtResponse L n k A + normaliserHessianAtResponse L n k B : ℝ) : ℂ) := by
  have hA : complexSecondDeriv L n k (backgroundSlotField L n k A) (backgroundSlotField L n k A) =
      (normaliserHessianAtResponse L n k A : ℂ) :=
    hext _ _ _ _ (complexify_spec _) (complexify_spec _)
  have hB : complexSecondDeriv L n k (backgroundSlotField L n k B) (backgroundSlotField L n k B) =
      (normaliserHessianAtResponse L n k B : ℂ) :=
    hext _ _ _ _ (complexify_spec _) (complexify_spec _)
  have hAB := hsym (backgroundSlotField L n k A) (backgroundSlotField L n k B)
  simp only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    mul_neg, hA, hB, hAB]
  push_cast
  linear_combination (-(normaliserHessianAtResponse L n k B : ℂ)) * Complex.I_mul_I
private theorem pauliCoeff_neg {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (-X) = -pauliCoeff a X := by
  rw [pauliCoeff_of_mem hX, pauliCoeff_of_mem (ComplexMatrix2.traceless.neg_mem hX)]
  have e : (⟨-X, ComplexMatrix2.traceless.neg_mem hX⟩ : ComplexMatrix2.traceless) = -⟨X, hX⟩ := rfl
  rw [e, map_neg]
  rfl
private def toComplexForm {j : ℕ} (r : edgeFormSpace L n k j) : complexEdgeForms L n k j :=
  ⟨r.1, fun b hb => (r.2.1 b hb).2, r.2.2⟩
private theorem coeffsOnEdges_neg {j : ℕ} (B : edgeFormSpace L n k j) :
    PeriodicForm.coeffsOnEdges L n k j ((-B : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) =
      -PeriodicForm.coeffsOnEdges L n k j (B : Edge L n k j → ComplexMatrix2) := by
  funext ι
  show pauliCoeff ι.1 (-(B : Edge L n k j → ComplexMatrix2) (projPositiveEdge L n k j ι.2).1) =
    -pauliCoeff ι.1 ((B : Edge L n k j → ComplexMatrix2) (projPositiveEdge L n k j ι.2).1)
  exact pauliCoeff_neg (B.2.1 _ (projPositiveEdge L n k j ι.2).2).2 _
private theorem meshScaledResponse_neg (hI : ResponseImagesFullSide.ResponseImagesHold)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    (hc₀ : ProjCellsClassified L n k 0) (B : edgeFormSpace L n k k) :
    meshScaledResponse L n k ((-B : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2) =
      -meshScaledResponse L n k B := by
  have h1 := (hI L hst k hk n hn (-B)).resp_coeffs
  have h2 := (hI L hst k hk n hn B).resp_coeffs
  have hact : PeriodicOperators.applyKernel (BackgroundFieldResponse.responseKernel L k)
      (-PeriodicForm.coeffsOnEdges L n k k (B : Edge L n k k → ComplexMatrix2)) =
      -PeriodicOperators.applyKernel (BackgroundFieldResponse.responseKernel L k)
        (PeriodicForm.coeffsOnEdges L n k k (B : Edge L n k k → ComplexMatrix2)) := by
    funext ι
    simp only [PeriodicOperators.applyKernel, Pi.neg_apply, mul_neg, tsum_neg]
  rw [coeffsOnEdges_neg, hact, ← h2, ← coeffsOnEdges_neg] at h1
  have e : periodicResponse L n k ((-B : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2) =
      -periodicResponse L n k B := by
    have h3 := complexEdgeForm_ext (A := toComplexForm (periodicResponse L n k
      ((-B : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2)))
      (A' := toComplexForm (-periodicResponse L n k B)) hc₀ (fun ι => congrFun h1 ι)
    exact Subtype.ext (congrArg (fun w : complexEdgeForms L n k 0 => (w : Edge L n k 0 → ComplexMatrix2)) h3)
  simp only [meshScaledResponse, e, smul_neg]
end Slots
section Main
open PeriodicOperators.Tempered (EventuallyForSides)
open ResponseProperties (euclidNorm)
variable {L : ℕ}
private theorem eventually_of_eventuallyForSides (hL2 : 2 ≤ L) {Q : ℕ → Prop}
    (h : EventuallyForSides L Q) : ∀ᶠ n in atTop, Q n := by apply _root_.YangMills.SharedProofs.p110886 <;> assumption
private theorem finite_positiveEdge {n k : ℕ} (hL : 0 < L) (j : ℕ) :
    Finite (Tower.PositiveEdge L n k j) := by apply _root_.YangMills.SharedProofs.p11983 <;> assumption
private theorem single_mem_dualLattice {n n₀ : ℕ} (hL : 0 < L) (hn : n₀ ≤ n) {m : ℤ} {t : ℝ}
    (ht : t = 2 * Real.pi * m / (2 * (L : ℝ) ^ n₀)) :
    (Pi.single 0 t : AmbientSpace) ∈ dualLattice (2 * L ^ n) := by
  refine ⟨Pi.single 0 (m * (L : ℤ) ^ (n - n₀)), fun μ => ?_⟩
  by_cases h : μ = 0
  · subst h
    have hp : (L : ℝ) ^ n = (L : ℝ) ^ n₀ * (L : ℝ) ^ (n - n₀) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [Pi.single_eq_same, ht]
    push_cast
    rw [hp]
    field_simp
  · simp [Pi.single_eq_of_ne h]
private theorem exp_I_mul_re_im (θ : ℝ) :
    (Complex.exp (Complex.I * (θ : ℂ))).re = Real.cos θ ∧
      (Complex.exp (Complex.I * (θ : ℂ))).im = Real.sin θ := by
  rw [mul_comm]
  exact ⟨Complex.exp_ofReal_mul_I_re θ, Complex.exp_ofReal_mul_I_im θ⟩
private theorem bilinDot_single (t : ℝ) (w : Fin 4 → ℤ) :
    bilinDot (toComplexVec (Pi.single 0 t)) (toComplexVec (castVec w)) = ((t * w 0 : ℝ) : ℂ) := by
  simp [bilinDot, toComplexVec, castVec, Fin.sum_univ_four, Pi.single_apply]
private theorem bilinDot_neg_single (t : ℝ) (w : Fin 4 → ℤ) :
    bilinDot (toComplexVec (-Pi.single 0 t)) (toComplexVec (castVec w)) =
      ((-(t * w 0) : ℝ) : ℂ) := by
  simp [bilinDot, toComplexVec, castVec, Fin.sum_univ_four, Pi.single_apply]
private theorem topForm_fourierModeForm_parts {n k : ℕ} [NeZero (2 * L ^ n)] (hL : 2 ≤ L) (hn : 0 < n)
    (hex : ∀ y : Tower.Vertex L n k k, ∃ x : TorusFields.TorusSite (2 * L ^ n),
      y = PeriodicLattice.offsetSite 0 (centredCoords x))
    (hinj : ∀ x x' : TorusFields.TorusSite (2 * L ^ n),
      PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) (centredCoords x) =
        PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) (centredCoords x') →
        x = x')
    {t : ℝ} (hq : (Pi.single 0 t : AmbientSpace) ∈ dualLattice (2 * L ^ n))
    (A B : edgeFormSpace L n k k) (hAB : IsPlaneWavePair L n k t A B) :
    topForm L n k (realComponent
        (PeriodicOperators.Tempered.fourierModeForm L n 2 (Pi.single 0 t) secondAxis)) = A ∧
      topForm L n k (imagComponent
        (PeriodicOperators.Tempered.fourierModeForm L n 2 (Pi.single 0 t) secondAxis)) = B ∧
      topForm L n k (realComponent
        (PeriodicOperators.Tempered.fourierModeForm L n 2 (-Pi.single 0 t) secondAxis)) = A ∧
      topForm L n k (imagComponent
        (PeriodicOperators.Tempered.fourierModeForm L n 2 (-Pi.single 0 t) secondAxis)) =
        ((-B : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2) := by
  have hq' : (-Pi.single 0 t : AmbientSpace) ∈ dualLattice (2 * L ^ n) := neg_mem hq
  let Re : ComplexMatrix2 → ComplexMatrix2 := fun X => (2⁻¹ : ℂ) • (X + X.conjTranspose)
  let Im : ComplexMatrix2 → ComplexMatrix2 := fun X => (2 * Complex.I)⁻¹ • (X - X.conjTranspose)
  have hRn : ∀ X, Re (-X) = -Re X := fun X => by
    simp only [Re, Matrix.conjTranspose_neg, ← neg_add, smul_neg]
  have hIn : ∀ X, Im (-X) = -Im X := fun X => by
    simp only [Im, Matrix.conjTranspose_neg, sub_neg_eq_add, ← smul_neg, neg_sub, neg_add_eq_sub]
  have hR0 : Re 0 = 0 := by simp [Re]
  have hI0 : Im 0 = 0 := by simp [Im]
  have hnegB : ((-B : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2) =
      planeWaveValues L n k (fun x => -sinePhase t x) := by
    have := hAB.2
    simp only [Submodule.coe_neg, this, planeWaveValues, neg_smul, Finset.sum_neg_distrib]
  refine ⟨topForm_part_eq hL hn hex hinj Re hRn hR0 Complex.re half_add_conjTranspose_smul hq
      (cosinePhase t) (fun x => ?_) A hAB.1,
    topForm_part_eq hL hn hex hinj Im hIn hI0 Complex.im half_sub_conjTranspose_smul hq
      (sinePhase t) (fun x => ?_) B hAB.2,
    topForm_part_eq hL hn hex hinj Re hRn hR0 Complex.re half_add_conjTranspose_smul hq'
      (cosinePhase t) (fun x => ?_) A hAB.1,
    topForm_part_eq hL hn hex hinj Im hIn hI0 Complex.im half_sub_conjTranspose_smul hq'
      (fun x => -sinePhase t x) (fun x => ?_) (-B) hnegB⟩
  · rw [bilinDot_single, (exp_I_mul_re_im _).1]
    rfl
  · rw [bilinDot_single, (exp_I_mul_re_im _).2]
    rfl
  · rw [bilinDot_neg_single, (exp_I_mul_re_im _).1, Real.cos_neg]
    rfl
  · rw [bilinDot_neg_single, (exp_I_mul_re_im _).2, Real.sin_neg]
    rfl
end Main
section Proof
open PeriodicOperators.Tempered (EventuallyForSides)
open ResponseProperties (euclidNorm)
open FullSpace (tripleAmplitude axisPauliElement responseSymbol backgroundResponseSymbol
  coarseResponseSymbol sourceResponseSymbol secondVariationSymbol)
variable {L : ℕ}
private theorem vertices_centredCoords {n k : ℕ} [NeZero (2 * L ^ n)]
    (hCo : PeriodicLattice.CoordinateDescription)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    (∀ y : Tower.Vertex L n k k, ∃ x : TorusFields.TorusSite (2 * L ^ n),
      y = PeriodicLattice.offsetSite 0 (centredCoords x)) ∧
    ∀ x x' : TorusFields.TorusSite (2 * L ^ n),
      PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) (centredCoords x) =
        PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) (centredCoords x') →
        x = x' := by
  obtain ⟨-, -, -, hex, hiff, -⟩ := (hCo L n hst.1 hst.2 hn).1 (PeriodicLattice.levelDepth k k)
    (by simp [PeriodicLattice.levelDepth])
  have hmod : 2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k k) = 2 * L ^ n := by
    simp [PeriodicLattice.halfPeriod, PeriodicLattice.levelDepth]
  simp only [hmod] at hiff
  refine ⟨fun y => ?_, fun x x' h => ?_⟩
  · obtain ⟨w, hw⟩ := hex 0 y
    refine ⟨fun μ => (w μ : ZMod (2 * L ^ n)), ?_⟩
    rw [hw]
    apply (hiff 0 _ _).2
    intro μ
    apply (ZMod.intCast_eq_intCast_iff _ _ _).1
    simp [centredCoords, ZMod.coe_valMinAbs]
  · funext μ
    have h1 := (ZMod.intCast_eq_intCast_iff _ _ _).2 ((hiff 0 _ _).1 h μ)
    simpa [centredCoords, ZMod.coe_valMinAbs] using h1
private theorem complexSecondDeriv_background_slots {n k : ℕ} [NeZero (2 * L ^ n)] (hL : 0 < L)
    (hL2 : 2 ≤ L) (hst : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hnk : k < n)
    (hn : 0 < n) (hOn : ResponseOperators.TorusSideFacts L n k)
    (hp₀ : PeriodicOperators.IsPeriodic (colourEdges L k 0))
    (hpk : PeriodicOperators.IsPeriodic (colourEdges L k k))
    (hc₀ : ProjCellsClassified L n k 0) (hc : ProjCellsClassified L n k k)
    (hext : IsComplexSecondDeriv L n k (complexSecondDeriv L n k))
    (hsym : ∀ ζ ζ' : PeriodicField L n k, complexSecondDeriv L n k ζ ζ' =
      complexSecondDeriv L n k ζ' ζ)
    (hI : ResponseImagesFullSide.ResponseImagesHold)
    (hex : ∀ y : Tower.Vertex L n k k, ∃ x : TorusFields.TorusSite (2 * L ^ n),
      y = PeriodicLattice.offsetSite 0 (centredCoords x))
    (hinj : ∀ x x' : TorusFields.TorusSite (2 * L ^ n),
      PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) (centredCoords x) =
        PeriodicLattice.offsetSite (0 : Tower.Vertex L n k k) (centredCoords x') →
        x = x')
    {t : ℝ} (hq : (Pi.single 0 t : AmbientSpace) ∈ dualLattice (2 * L ^ n))
    (A B : edgeFormSpace L n k k) (hAB : IsPlaneWavePair L n k t A B) (e : Fin 4 → ComplexMatrix2)
    (hWp : complexResponse L n k
        (PeriodicOperators.Tempered.fourierModeForm L n 2 (Pi.single 0 t) secondAxis) =
      blochWaveField L n k hL (toComplexVec (Pi.single 0 t))
        (responseSymbol L k hL (toComplexVec (Pi.single 0 t)) e))
    (hWm : complexResponse L n k
        (PeriodicOperators.Tempered.fourierModeForm L n 2 (-Pi.single 0 t) secondAxis) =
      blochWaveField L n k hL (toComplexVec (-Pi.single 0 t))
        (responseSymbol L k hL (toComplexVec (-Pi.single 0 t)) e)) :
    complexSecondDeriv L n k
        (blochWaveField L n k hL (toComplexVec (Pi.single 0 t))
          (tripleAmplitude L k hL
            (backgroundResponseSymbol L k (toComplexVec (Pi.single 0 t)) e) 0 0))
        (blochWaveField L n k hL (toComplexVec (-Pi.single 0 t))
          (tripleAmplitude L k hL
            (backgroundResponseSymbol L k (toComplexVec (-Pi.single 0 t)) e) 0 0)) =
      ((normaliserHessianAtResponse L n k A + normaliserHessianAtResponse L n k B : ℝ) : ℂ) := by
  have hq' : (-Pi.single 0 t : AmbientSpace) ∈ dualLattice (2 * L ^ n) := neg_mem hq
  obtain ⟨t1, t2, t3, t4⟩ := topForm_fourierModeForm_parts hL2 hn hex hinj hq A B hAB
  have sp := blochWaveField_background_only hL hL2 hnk hOn hp₀ hpk hc₀ hc hq
    (backgroundResponseSymbol L k (toComplexVec (Pi.single 0 t)) e)
    (sourceResponseSymbol L k (toComplexVec (Pi.single 0 t)) e)
    (coarseResponseSymbol L k (toComplexVec (Pi.single 0 t)) e)
  have sm := blochWaveField_background_only hL hL2 hnk hOn hp₀ hpk hc₀ hc hq'
    (backgroundResponseSymbol L k (toComplexVec (-Pi.single 0 t)) e)
    (sourceResponseSymbol L k (toComplexVec (-Pi.single 0 t)) e)
    (coarseResponseSymbol L k (toComplexVec (-Pi.single 0 t)) e)
  have ep := complexResponse_background_slot _ _ _ t1 t2
  have em := complexResponse_background_slot _ _ _ t3 t4
  have hWp' : complexResponse L n k
      (PeriodicOperators.Tempered.fourierModeForm L n 2 (Pi.single 0 t) secondAxis) =
    blochWaveField L n k hL (toComplexVec (Pi.single 0 t))
      (tripleAmplitude L k hL (backgroundResponseSymbol L k (toComplexVec (Pi.single 0 t)) e)
        (sourceResponseSymbol L k (toComplexVec (Pi.single 0 t)) e)
        (coarseResponseSymbol L k (toComplexVec (Pi.single 0 t)) e)) := hWp
  have hWm' : complexResponse L n k
      (PeriodicOperators.Tempered.fourierModeForm L n 2 (-Pi.single 0 t) secondAxis) =
    blochWaveField L n k hL (toComplexVec (-Pi.single 0 t))
      (tripleAmplitude L k hL (backgroundResponseSymbol L k (toComplexVec (-Pi.single 0 t)) e)
        (sourceResponseSymbol L k (toComplexVec (-Pi.single 0 t)) e)
        (coarseResponseSymbol L k (toComplexVec (-Pi.single 0 t)) e)) := hWm
  rw [hWp'] at ep
  rw [hWm', backgroundSlotField_neg (meshScaledResponse_neg hI hst hk hn hc₀ B)] at em
  rw [sp, sm, ep, em]
  exact complexSecondDeriv_conj_pair hext hsym A B
theorem normaliserHessianOnLongWaves_holds (hPol : HessianAtResponseField.Claim)
    (hWave : ResponseOfFourierMode.Claim)
    (hClose : SecondDerivNearSymbol.SecondDerivCloseToSymbol)
    (hZero : ResponseSecondVariation.NearZeroCubicBound)
    (hWidth : FullSpace.JointWidthAndTransposeTheorem)
    (hExt : HessianAndComplexExtensionHolds)
    (hImg : ResponseImagesFullSide.ResponseImagesHold)
    (hY : LocalKernels.Periodisation.PeriodisationHolds)
    (hP : PeriodicOperators.TowerIndexSets.Claim)
    (hR : ResponseOperators.Claim)
    (hCo : PeriodicLattice.CoordinateDescription) :
    NormaliserHessianOnLongWaves := by
  intro L _ hst k hk
  have hL2 : 2 ≤ L := by
    have := hst.2
    omega
  have hL : 0 < L := by omega
  have hLr : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  obtain ⟨δ₀, hδ₀, hAt'⟩ := hR
  have hAt := hAt' L hst k hk
  have hw := (hWidth L hL hst k hk).1
  obtain ⟨C₃, N, hN, -, hNb⟩ := hZero δ₀ hδ₀ L hL hst k hk _ hw
  obtain ⟨C₂, c₂, hC₂, hc₂, hcl⟩ := hClose L hL hst k hk
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hN
  have hp₀ := (hP L hst k 0 (Nat.zero_le k)).2.1
  have hpk := (hP L hst k k le_rfl).2.1
  refine ⟨|C₃|, r, abs_nonneg _, hr, ?_⟩
  intro n₀ m t ht htr ε hε
  have hneg : toComplexVec (-(Pi.single 0 t : AmbientSpace)) = -toComplexVec (Pi.single 0 t) := by
    funext μ
    simp [toComplexVec]
  have hκN : toComplexVec (Pi.single 0 t : AmbientSpace) ∈ N := hball (by
    rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
    intro μ
    by_cases h : μ = 0
    · subst h
      simpa [toComplexVec] using htr
    · simpa [toComplexVec, Pi.single_eq_of_ne h] using hr)
  have hmod : euclidNorm (toComplexVec (Pi.single 0 t : AmbientSpace)) = |t| := by
    simp [euclidNorm, toComplexVec, Pi.single_apply, Real.sqrt_sq_eq_abs]
  have hb := hNb _ hκN secondAxis secondAxis
  rw [hmod] at hb
  set κ : Fin 4 → ℂ := toComplexVec (Pi.single 0 t : AmbientSpace) with hκ
  set e := axisPauliElement secondAxis 2 with he
  set w := (FullSpace.fieldPeriodicData L k hL).quotWeight 1 with hwt
  set f₁ := PeriodicOperators.wNorm w (responseSymbol L k hL κ e) *
    PeriodicOperators.wNorm w (responseSymbol L k hL (-κ) e) with hf₁
  set f₂ := PeriodicOperators.wNorm w
      (tripleAmplitude L k hL (backgroundResponseSymbol L k κ e) 0 0) *
    PeriodicOperators.wNorm w
      (tripleAmplitude L k hL (backgroundResponseSymbol L k (-κ) e) 0 0) with hf₂
  have hexp : Tendsto (fun n : ℕ => Real.exp (-c₂ * ((2 * L ^ n : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => c₂ * (2 * (L : ℝ) ^ n)) atTop atTop :=
      Tendsto.const_mul_atTop hc₂ (Tendsto.const_mul_atTop two_pos
        (tendsto_pow_atTop_atTop_of_one_lt hLr))
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).congr fun n => ?_
    simp only [Function.comp]
    push_cast
    ring_nf
  have hsmall : ∀ᶠ n : ℕ in atTop,
      C₂ * Real.exp (-c₂ * ((2 * L ^ n : ℕ) : ℝ)) * (f₁ + f₂) ≤ ε := by
    have h := (hexp.const_mul C₂).mul_const (f₁ + f₂)
    simp only [mul_zero, zero_mul] at h
    filter_upwards [h.eventually_lt_const hε] with n hn using hn.le
  filter_upwards [eventually_of_eventuallyForSides hL2 (hPol L hst k hk),
    eventually_of_eventuallyForSides hL2 (hWave L hL hst k hk),
    eventually_of_eventuallyForSides hL2 hcl, hsmall,
    eventually_ge_atTop (max n₀ (k + 1))] with n hPn hWn hCn hE hbig
  intro A B hAB
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans hbig
  have hnk : k < n := Nat.lt_of_succ_le ((le_max_right _ _).trans hbig)
  have hn : 0 < n := by omega
  have hq : (Pi.single 0 t : AmbientSpace) ∈ dualLattice (2 * L ^ n) := single_mem_dualLattice hL hn0 ht
  have hq' : (-(Pi.single 0 t : AmbientSpace)) ∈ dualLattice (2 * L ^ n) := neg_mem hq
  have hp := hPn _ (fourierModeForm_mem hL2 hn 2 (Pi.single 0 t) secondAxis) _
    (fourierModeForm_mem hL2 hn 2 (-Pi.single 0 t) secondAxis)
  have hWp := hWn _ hq 2 secondAxis
  have hWm := hWn _ hq' 2 secondAxis
  have hc₁ := hCn _ hq (responseSymbol L k hL κ e) (responseSymbol L k hL (-κ) e)
  have hc₃ := hCn _ hq (tripleAmplitude L k hL (backgroundResponseSymbol L k κ e) 0 0)
    (tripleAmplitude L k hL (backgroundResponseSymbol L k (-κ) e) 0 0)
  obtain ⟨hcb, -⟩ := hY L hst k n hn
  have hc₀ := (hcb 0 (Nat.zero_le k)).1
  have hck := (hcb k le_rfl).1
  have fin₀ := finite_positiveEdge (n := n) (k := k) hL 0
  have fink := finite_positiveEdge (n := n) (k := k) hL k
  let _ := Fintype.ofFinite (Tower.PositiveEdge L n k 0)
  let _ := Fintype.ofFinite (Tower.PositiveEdge L n k k)
  have hX := hExt L n k hst hn hk
  obtain ⟨hsx, hsi⟩ := vertices_centredCoords (k := k) (n := n) hCo hst hn
  have hid := complexSecondDeriv_background_slots hL hL2 hst hk hnk hn (hAt.torus_sides n hn)
    hp₀ hpk hc₀ hck hX.isComplexSecondDeriv hX.complexSecondDeriv_symm hImg hsx hsi hq A B hAB e
    hWp hWm
  rw [hneg] at hid hWm
  set v : ℂ := (((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ with hv
  have hvw : ((((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ)) : ℂ) = v := by
    simp only [hv, PeriodicLattice.torusSide]
    push_cast
    rw [inv_pow]
  have hwave : normaliserCosineSum L n k t =
      (v * complexSecondDeriv L n k
        (blochWaveField L n k hL κ (responseSymbol L k hL κ e))
        (blochWaveField L n k hL (-κ) (responseSymbol L k hL (-κ) e))).re := by
    show (((((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ)) : ℂ) * _).re = _
    rw [hvw, hp, hWp, hWm]
  have hcast : (((((2 * (L : ℝ) ^ n) ^ 4)⁻¹ *
        (normaliserHessianAtResponse L n k A + normaliserHessianAtResponse L n k B) : ℝ)) : ℂ) =
      v * complexSecondDeriv L n k
        (blochWaveField L n k hL κ
          (tripleAmplitude L k hL (backgroundResponseSymbol L k κ e) 0 0))
        (blochWaveField L n k hL (-κ)
          (tripleAmplitude L k hL (backgroundResponseSymbol L k (-κ) e) 0 0)) := by
    rw [hid, hv]
    push_cast
    ring
  rw [hwave]
  set z₁ := v * complexSecondDeriv L n k
    (blochWaveField L n k hL κ (responseSymbol L k hL κ e))
    (blochWaveField L n k hL (-κ) (responseSymbol L k hL (-κ) e)) with hz₁
  set z₂ := v * complexSecondDeriv L n k
    (blochWaveField L n k hL κ
      (tripleAmplitude L k hL (backgroundResponseSymbol L k κ e) 0 0))
    (blochWaveField L n k hL (-κ)
      (tripleAmplitude L k hL (backgroundResponseSymbol L k (-κ) e) 0 0)) with hz₂
  set y := ((2 * (L : ℝ) ^ n) ^ 4)⁻¹ *
    (normaliserHessianAtResponse L n k A + normaliserHessianAtResponse L n k B) with hy
  set p₁ := secondVariationSymbol L k hL κ (responseSymbol L k hL κ e)
    (responseSymbol L k hL (-κ) e) with hp₁
  set p₀ := secondVariationSymbol L k hL κ
    (tripleAmplitude L k hL (backgroundResponseSymbol L k κ e) 0 0)
    (tripleAmplitude L k hL (backgroundResponseSymbol L k (-κ) e) 0 0) with hp₀'
  set E := Real.exp (-c₂ * ((2 * L ^ n : ℕ) : ℝ)) with hEdef
  have b₁ : ‖z₁ - p₁‖ ≤ C₂ * E * f₁ := by
    have : ‖z₁ - p₁‖ ≤ C₂ * E * PeriodicOperators.wNorm w (responseSymbol L k hL κ e) *
        PeriodicOperators.wNorm w (responseSymbol L k hL (-κ) e) := hc₁
    rw [hf₁, ← mul_assoc]
    exact this
  have b₂ : ‖z₂ - p₀‖ ≤ C₂ * E * f₂ := by
    have : ‖z₂ - p₀‖ ≤ C₂ * E * PeriodicOperators.wNorm w
          (tripleAmplitude L k hL (backgroundResponseSymbol L k κ e) 0 0) *
        PeriodicOperators.wNorm w
          (tripleAmplitude L k hL (backgroundResponseSymbol L k (-κ) e) 0 0) := hc₃
    rw [hf₂, ← mul_assoc]
    exact this
  have b₃ : ‖p₁ - p₀‖ ≤ C₃ * |t| ^ 3 := hb
  have b₄ : C₃ * |t| ^ 3 ≤ |C₃| * |t| ^ 3 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hre : |z₁.re - y| ≤ ‖z₁ - z₂‖ := by
    have e1 : z₁.re - y = (z₁ - z₂).re := by
      rw [Complex.sub_re, ← hcast, Complex.ofReal_re]
    rw [e1]
    exact Complex.abs_re_le_norm _
  have htri : ‖z₁ - z₂‖ ≤ ‖z₁ - p₁‖ + ‖p₁ - p₀‖ + ‖z₂ - p₀‖ := by
    have e2 : z₁ - z₂ = (z₁ - p₁) + (p₁ - p₀) - (z₂ - p₀) := by ring
    rw [e2]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have hsum : C₂ * E * f₁ + C₂ * E * f₂ = C₂ * E * (f₁ + f₂) := by ring
  linarith
end Proof
end YangMills.Construction.RunningCouplingSlope.LongWaveNormaliser
end
