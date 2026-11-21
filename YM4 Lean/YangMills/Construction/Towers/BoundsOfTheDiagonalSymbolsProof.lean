import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.TransposesOfProductsAndOfDiagonalKernels
import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.Towers.BoundsOfTheDiagonalSymbols
import YangMills.Construction.Towers.CalculusOfPlaneWaves
import YangMills.Construction.Towers.ElementaryBoundsOfThePlaneWaveFunctions
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.TheRootsOfTheFreePropagatorsOnTheStrip
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.DiagonalSymbolBounds
open PeriodicOperators
open PeriodicOperators.StripSymbols (openStripInterior)
open Matrices
open FreeResolvents
open PlaneWaves
open PlaneWaveCalculus
section PauliNorm
theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem pauliCoeff_smul (a : Fin 3) (c : ℂ) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (c • X) = c * pauliCoeff a X := by apply _root_.YangMills.SharedProofs.p5172 <;> assumption
theorem pauliCoeff_sub (a : Fin 3) {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X - Y) = pauliCoeff a X - pauliCoeff a Y := by
  have hXY : X - Y ∈ ComplexMatrix2.traceless := Submodule.sub_mem _ hX hY
  simp only [pauliCoeff, dif_pos hX, dif_pos hY, dif_pos hXY]
  have e : (⟨X - Y, hXY⟩ : ComplexMatrix2.traceless) =
      (⟨X, hX⟩ : ComplexMatrix2.traceless) - ⟨Y, hY⟩ := rfl
  rw [e, map_sub]
  rfl
theorem pauliCoeff_sum {ι : Type} [Fintype ι] (a : Fin 3) (X : ι → ComplexMatrix2)
    (hX : ∀ i, X i ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (∑ i, X i) = ∑ i, pauliCoeff a (X i) := by
  have hs : ∑ i, X i ∈ ComplexMatrix2.traceless := Submodule.sum_mem _ fun i _ => hX i
  have e : (⟨∑ i, X i, hs⟩ : ComplexMatrix2.traceless) =
      ∑ i, (⟨X i, hX i⟩ : ComplexMatrix2.traceless) :=
    Subtype.ext (by simp)
  have e' : ∀ i, pauliCoeff a (X i) = OneLoop.pauliCoordinateEquiv ⟨X i, hX i⟩ a :=
    fun i => by simp only [pauliCoeff, dif_pos (hX i)]
  simp only [e']
  simp only [pauliCoeff, dif_pos hs]
  rw [e, map_sum, Finset.sum_apply]
theorem pauliNorm_sq (X : ComplexMatrix2) : pauliNorm X ^ 2 = ∑ a, ‖pauliCoeff a X‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
theorem pauliNorm_smul_sq (c : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    pauliNorm (c • X) ^ 2 = ‖c‖ ^ 2 * pauliNorm X ^ 2 := by
  rw [pauliNorm_sq, pauliNorm_sq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pauliCoeff_smul a c hX, norm_mul, mul_pow]
theorem pauliNorm_sub_sq_le {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliNorm (X - Y) ^ 2 ≤ 2 * pauliNorm X ^ 2 + 2 * pauliNorm Y ^ 2 := by
  rw [pauliNorm_sq, pauliNorm_sq, pauliNorm_sq, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [pauliCoeff_sub a hX hY]
  have h := norm_sub_le (pauliCoeff a X) (pauliCoeff a Y)
  have h0 := norm_nonneg (pauliCoeff a X - pauliCoeff a Y)
  nlinarith [sq_nonneg (‖pauliCoeff a X‖ - ‖pauliCoeff a Y‖)]
theorem pauliNorm_sum_sq_le (X : Fin 4 → ComplexMatrix2)
    (hX : ∀ i, X i ∈ ComplexMatrix2.traceless) :
    pauliNorm (∑ i, X i) ^ 2 ≤ 4 * ∑ i, pauliNorm (X i) ^ 2 := by
  simp only [pauliNorm_sq]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [pauliCoeff_sum a X hX]
  calc ‖∑ i, pauliCoeff a (X i)‖ ^ 2
      ≤ (∑ i, ‖pauliCoeff a (X i)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (Finset.univ : Finset (Fin 4)).card * ∑ i, ‖pauliCoeff a (X i)‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = 4 * ∑ i, ‖pauliCoeff a (X i)‖ ^ 2 := by simp
theorem pauliNorm_sum_smul_sq_le (c : Fin 4 → ℂ) (X : Fin 4 → ComplexMatrix2)
    (hX : ∀ i, X i ∈ ComplexMatrix2.traceless) (hc : ∀ i, ‖c i‖ ^ 2 ≤ 4) :
    pauliNorm (∑ i, c i • X i) ^ 2 ≤ 16 * ∑ i, pauliNorm (X i) ^ 2 := by
  refine (pauliNorm_sum_sq_le _ fun i => Submodule.smul_mem _ _ (hX i)).trans ?_
  have : ∑ i, pauliNorm (c i • X i) ^ 2 ≤ 4 * ∑ i, pauliNorm (X i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [pauliNorm_smul_sq _ (hX i)]
    exact mul_le_mul_of_nonneg_right (hc i) (by positivity)
  linarith
end PauliNorm
section Coefficients
variable (L k : ℕ)
theorem fourierCoeff_mem_traceless (g : FullSpace.Vertex L k 0 → ComplexMatrix2)
    (hg : ∀ x, g x ∈ ComplexMatrix2.traceless) (m : Fin 4 → ℤ) :
    fourierCoeff L k g m ∈ ComplexMatrix2.traceless := by
  refine Submodule.smul_mem _ _ ?_
  exact finsum_induction (· ∈ ComplexMatrix2.traceless) (Submodule.zero_mem _)
    (fun _ _ => Submodule.add_mem _) fun c => Submodule.smul_mem _ _ (hg _)
theorem vertexFourierCoeff_mem_traceless (l : (colourVertices L k 0).UnitQuot → ℂ)
    (m : Fin 4 → ℤ) : vertexFourierCoeff L k l m ∈ ComplexMatrix2.traceless :=
  fourierCoeff_mem_traceless L k _ (fun _ => ofPauliCoeffs_mem_traceless _ _) m
theorem edgeFourierCoeff_mem_traceless (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4)
    (m : Fin 4 → ℤ) : edgeFourierCoeff L k b μ m ∈ ComplexMatrix2.traceless :=
  fourierCoeff_mem_traceless L k _ (fun _ => ofPauliCoeffs_mem_traceless _ _) m
end Coefficients
theorem quotHomNorm_le_ten {I I' : PeriodicData} (M : QuotHom I I')
    (h : ∀ f, wNorm (I'.quotWeight 1) (M f) ^ 2 ≤
      100 * wNorm (I.quotWeight 1) f ^ 2) :
    quotHomNorm M ≤ ENNReal.ofReal 10 := by
  unfold quotHomNorm wOpNorm
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
  have h1 : wNorm (I.quotWeight 1) f ≤ 1 := hf.2.2
  have h0 : 0 ≤ wNorm (I.quotWeight 1) f := Real.sqrt_nonneg _
  have h2 : 0 ≤ wNorm (I'.quotWeight 1) (M f) := Real.sqrt_nonneg _
  have h3 := h f
  nlinarith
section Numbers
variable {L k : ℕ}
theorem finestMesh_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.finestMesh_pos <;> assumption
theorem periodShift_apply (q : Fin 4 → ℂ) (e : Fin 4 → ℤ) (ν : Fin 4) :
    periodShift L k q e ν =
      q ν + ((2 * Real.pi / finestMesh L k * (e ν : ℝ) : ℝ) : ℂ) := by
  simp only [periodShift, meshC]
  push_cast
  ring
theorem exists_periodShift_re_le (hL : Conventions.IsAdmissibleBlockingFactor L)
    (q : Fin 4 → ℂ) :
    ∃ e : Fin 4 → ℤ, ∀ ν, |(periodShift L k q e ν).re| ≤ Real.pi / finestMesh L k ∧
      (periodShift L k q e ν).im = (q ν).im := by
  have hη := finestMesh_pos (k := k) hL
  refine ⟨fun ν => -round ((q ν).re * finestMesh L k / (2 * Real.pi)), fun ν => ?_⟩
  rw [periodShift_apply]
  constructor
  · rw [Complex.add_re, Complex.ofReal_re]
    set x := (q ν).re * finestMesh L k / (2 * Real.pi) with hx
    have hr := abs_sub_round x
    have e : (q ν).re + 2 * Real.pi / finestMesh L k * ((-round x : ℤ) : ℝ) =
        2 * Real.pi / finestMesh L k * (x - round x) := by
      rw [hx]
      push_cast
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / finestMesh L k)]
    calc 2 * Real.pi / finestMesh L k * |x - round x|
        ≤ 2 * Real.pi / finestMesh L k * (1 / 2) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = Real.pi / finestMesh L k := by ring
  · rw [Complex.add_im, Complex.ofReal_im, add_zero]
theorem forwardSymbol_periodShift (hL : Conventions.IsAdmissibleBlockingFactor L)
    (q : Fin 4 → ℂ) (e : Fin 4 → ℤ) (μ : Fin 4) :
    forwardSymbol L k (periodShift L k q e) μ = forwardSymbol L k q μ := by
  have hη : ((finestMesh L k : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (finestMesh_pos hL).ne'
  simp only [forwardSymbol, periodShift, meshC]
  have e1 : Complex.I * ((finestMesh L k : ℝ) : ℂ) *
      (q μ + 2 * (Real.pi : ℂ) / ((finestMesh L k : ℝ) : ℂ) * (e μ : ℂ)) =
      Complex.I * ((finestMesh L k : ℝ) : ℂ) * q μ +
        (e μ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    field_simp
  rw [e1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem neg_periodShift (q : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    -periodShift L k q e = periodShift L k (-q) (-e) := by
  funext ν
  simp only [periodShift, Pi.neg_apply]
  push_cast
  ring
theorem forwardSymbol_neg_periodShift (hL : Conventions.IsAdmissibleBlockingFactor L)
    (q : Fin 4 → ℂ) (e : Fin 4 → ℤ) (μ : Fin 4) :
    forwardSymbol L k (-periodShift L k q e) μ = forwardSymbol L k (-q) μ := by
  rw [neg_periodShift, forwardSymbol_periodShift hL]
theorem symbolSquare_periodShift (hL : Conventions.IsAdmissibleBlockingFactor L)
    (q : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    symbolSquare L k (periodShift L k q e) = symbolSquare L k q := by
  simp only [symbolSquare, forwardSymbol_periodShift hL, forwardSymbol_neg_periodShift hL]
theorem norm_principalRpow (σ : ℝ) (z : ℂ) : ‖principalRpow σ z‖ = ‖z‖ ^ σ := by
  have e : Complex.I * (σ : ℂ) * (rightHalfPlaneArg z : ℂ) =
      ((σ * rightHalfPlaneArg z : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [principalRpow, norm_mul, e, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
def MultipliersSmallAt (L k : ℕ) (q : Fin 4 → ℂ) : Prop :=
  ‖shiftedSymbolPow L k (-(1 / 2)) q‖ ^ 2 ≤ 4 ∧
    ∀ ν, ‖forwardSymbol L k q ν * shiftedSymbolPow L k (-(1 / 2)) q‖ ^ 2 ≤ 4 ∧
      ‖forwardSymbol L k (-q) ν * shiftedSymbolPow L k (-(1 / 2)) q‖ ^ 2 ≤ 4
theorem multipliersSmallAt (elem : PlaneWaveBounds.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (q : Fin 4 → ℂ)
    (hq : ∀ ν, |(q ν).im| ≤ 1 / 8) : MultipliersSmallAt L k q := by
  obtain ⟨e, he⟩ := exists_periodShift_re_le (k := k) hL q
  set p := periodShift L k q e with hp
  have hpt : PlaneWaveBounds.complexPoint (fun ν => (p ν).re) (fun ν => (p ν).im) = p := by
    funext ν
    simp only [PlaneWaveBounds.complexPoint]
    rw [mul_comm]
    exact Complex.re_add_im _
  obtain ⟨-, hb, -⟩ := elem.1 L k hL hk (fun ν => (p ν).re) (fun ν => (p ν).im)
    (fun ν => (he ν).1) (fun ν => by
      show |(p ν).im| ≤ 1 / 8
      rw [(he ν).2]
      exact hq ν)
  obtain ⟨-, h1, h2, -, h5, -⟩ := hb
  rw [hpt] at h1 h2 h5
  rw [symbolSquare_periodShift hL] at h1 h2
  set D := PlaneWaveBounds.realSymbolSquare L k (fun ν => (p ν).re) with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => by positivity
  set Z := ‖symbolSquare L k q + 1‖ with hZ
  have hZ0 : 0 < Z := by nlinarith
  have hpow : ‖shiftedSymbolPow L k (-(1 / 2)) q‖ ^ 2 = Z⁻¹ := by
    rw [shiftedSymbolPow, norm_principalRpow, ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
    norm_num
    exact Real.rpow_neg_one Z
  have hinv : Z⁻¹ ≤ 10 / 9 := by
    rw [inv_le_comm₀ hZ0 (by norm_num)]
    nlinarith
  have key : ∀ b a : ℝ, 0 ≤ a → 0 ≤ b → a ^ 2 ≤ D → b ≤ 6 / 5 * (a + 1 / 8) →
      b ^ 2 * Z⁻¹ ≤ 4 := by
    intro b a ha hb0 haD hb
    have hb2 : b ^ 2 ≤ 72 / 25 * (D + 1) := by nlinarith [sq_nonneg (a - 1 / 8)]
    have : b ^ 2 ≤ 4 * Z := by nlinarith
    rw [← div_eq_mul_inv, div_le_iff₀ hZ0]
    exact this
  have haD : ∀ ν, ‖forwardSymbol L k (toComplexVec fun ν => (p ν).re) ν‖ ^ 2 ≤ D :=
    fun ν => Finset.single_le_sum (f := fun ν =>
      ‖forwardSymbol L k (toComplexVec fun ν => (p ν).re) ν‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ ν)
  refine ⟨by rw [hpow]; linarith, fun ν => ⟨?_, ?_⟩⟩
  · rw [norm_mul, mul_pow, hpow]
    refine key _ _ (norm_nonneg _) (norm_nonneg _) (haD ν) ?_
    have := (h5 ν).1
    rwa [hp, forwardSymbol_periodShift hL] at this
  · rw [norm_mul, mul_pow, hpow]
    refine key _ _ (norm_nonneg _) (norm_nonneg _) (haD ν) ?_
    have := (h5 ν).2
    rwa [hp, forwardSymbol_neg_periodShift hL] at this
end Numbers
section Bounds
variable {L k : ℕ} {κ : Fin 4 → ℂ}
theorem le_hundred_mul_of_le {x S : ℝ} (c : ℝ) (hS : 0 ≤ S) (hc : c ≤ 100) (h : x ≤ c * S) :
    x ≤ 100 * S :=
  h.trans (mul_le_mul_of_nonneg_right hc hS)
theorem mul_le_four_mul {a x S : ℝ} (ha : a ≤ 4) (hx0 : 0 ≤ x) (hx : x ≤ S) : a * x ≤ 4 * S :=
  (mul_le_mul_of_nonneg_right ha hx0).trans (mul_le_mul_of_nonneg_left hx (by norm_num))
theorem norm_edgeMultiplier_le (cE : EdgeCoeffFacts L k)
    {A : QuotHom (colourEdges L k 0) (colourEdges L k 0)}
    (hA : ScalesEdgeCoeffs L k (shiftedSymbolPow L k (-(1 / 2))) κ A)
    (hsm : ∀ m ∈ freqBox L k, MultipliersSmallAt L k (shiftedFreq κ m)) :
    quotHomNorm A ≤ ENNReal.ofReal 10 := by
  refine quotHomNorm_le_ten A fun b => ?_
  rw [cE.norm_sq, cE.norm_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  rw [hA b μ m hm, pauliNorm_smul_sq _ (edgeFourierCoeff_mem_traceless L k b μ m)]
  exact mul_le_mul ((hsm m hm).1.trans (by norm_num)) le_rfl (by positivity) (by norm_num)
theorem norm_vertexMultiplier_le (cV : VertexCoeffFacts L k)
    {A : QuotHom (colourVertices L k 0) (colourVertices L k 0)}
    (hA : ScalesVertexCoeffs L k (shiftedSymbolPow L k (-(1 / 2))) κ A)
    (hsm : ∀ m ∈ freqBox L k, MultipliersSmallAt L k (shiftedFreq κ m)) :
    quotHomNorm A ≤ ENNReal.ofReal 10 := by
  refine quotHomNorm_le_ten A fun l => ?_
  rw [cV.norm_sq, cV.norm_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [hA l m hm, pauliNorm_smul_sq _ (vertexFourierCoeff_mem_traceless L k l m)]
  exact mul_le_mul ((hsm m hm).1.trans (by norm_num)) le_rfl (by positivity) (by norm_num)
theorem norm_edgeCoboundary_comp_le (cE : EdgeCoeffFacts L k) (cF : FaceCoeffFacts L k)
    (act : CoboundarySymbols L k)
    {A : QuotHom (colourEdges L k 0) (colourEdges L k 0)}
    (hA : ScalesEdgeCoeffs L k (shiftedSymbolPow L k (-(1 / 2))) κ A)
    (hsm : ∀ m ∈ freqBox L k, MultipliersSmallAt L k (shiftedFreq κ m)) :
    quotHomNorm ((symbolHom (colourEdges L k 0) (colourFaces L k 0)
      (FullSpace.scaledEdgeCoboundaryKernel L k 0) κ).comp A) ≤ ENNReal.ofReal 10 := by
  refine quotHomNorm_le_ten _ fun b => ?_
  rw [cF.norm_sq, cE.norm_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  set S := ∑ μ, pauliNorm (edgeFourierCoeff L k b μ m) ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hterm : ∀ μ, pauliNorm (edgeFourierCoeff L k b μ m) ^ 2 ≤ S := fun μ =>
    Finset.single_le_sum (f := fun μ => pauliNorm (edgeFourierCoeff L k b μ m) ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ μ)
  have hp : ∀ p : AxisPair, pauliNorm (faceFourierCoeff L k
      ((symbolHom (colourEdges L k 0) (colourFaces L k 0)
        (FullSpace.scaledEdgeCoboundaryKernel L k 0) κ).comp A b) p.1.1 p.1.2 p.2 m) ^ 2 ≤
        16 * S := by
    intro p
    rw [LinearMap.comp_apply, act.edgeCoboundary κ (A b) p.1.1 p.1.2 p.2 m hm,
      hA b _ m hm, hA b _ m hm, smul_smul, smul_smul]
    refine (pauliNorm_sub_sq_le
      (Submodule.smul_mem _ _ (edgeFourierCoeff_mem_traceless L k b _ m))
      (Submodule.smul_mem _ _ (edgeFourierCoeff_mem_traceless L k b _ m))).trans ?_
    rw [pauliNorm_smul_sq _ (edgeFourierCoeff_mem_traceless L k b _ m),
      pauliNorm_smul_sq _ (edgeFourierCoeff_mem_traceless L k b _ m)]
    have h1 := mul_le_four_mul ((hsm m hm).2 p.1.1).1 (by positivity) (hterm p.1.2)
    have h2 := mul_le_four_mul ((hsm m hm).2 p.1.2).1 (by positivity) (hterm p.1.1)
    linarith
  have hcard : Fintype.card AxisPair = 6 := by decide
  calc ∑ p : AxisPair, pauliNorm (faceFourierCoeff L k
        ((symbolHom (colourEdges L k 0) (colourFaces L k 0)
          (FullSpace.scaledEdgeCoboundaryKernel L k 0) κ).comp A b) p.1.1 p.1.2 p.2 m) ^ 2
      ≤ ∑ _p : AxisPair, 16 * S := Finset.sum_le_sum fun p _ => hp p
    _ = 96 * S := by
        rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 100 * S := mul_le_mul_of_nonneg_right (by norm_num) hS0
theorem norm_vertexCoboundaryT_comp_le (cE : EdgeCoeffFacts L k) (cV : VertexCoeffFacts L k)
    (act : CoboundarySymbols L k)
    {A : QuotHom (colourEdges L k 0) (colourEdges L k 0)}
    (hA : ScalesEdgeCoeffs L k (shiftedSymbolPow L k (-(1 / 2))) κ A)
    (hsm : ∀ m ∈ freqBox L k, MultipliersSmallAt L k (shiftedFreq κ m)) :
    quotHomNorm ((symbolHom (colourEdges L k 0) (colourVertices L k 0)
      (vertexCoboundaryT L k 0) κ).comp A) ≤ ENNReal.ofReal 10 := by
  refine quotHomNorm_le_ten _ fun b => ?_
  rw [cV.norm_sq, cE.norm_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [LinearMap.comp_apply, act.vertexCoboundary_transpose κ (A b) m hm]
  have e : ∑ μ, forwardSymbol L k (-shiftedFreq κ m) μ • edgeFourierCoeff L k (A b) μ m =
      ∑ μ, (forwardSymbol L k (-shiftedFreq κ m) μ *
          shiftedSymbolPow L k (-(1 / 2)) (shiftedFreq κ m)) •
        edgeFourierCoeff L k b μ m :=
    Finset.sum_congr rfl fun μ _ => by rw [hA b μ m hm, smul_smul]
  rw [e]
  exact le_hundred_mul_of_le 16 (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)
    (pauliNorm_sum_smul_sq_le _ _ (fun μ => edgeFourierCoeff_mem_traceless L k b μ m)
      fun μ => ((hsm m hm).2 μ).2)
theorem norm_comp_vertexCoboundary_le (cE : EdgeCoeffFacts L k) (cV : VertexCoeffFacts L k)
    (act : CoboundarySymbols L k)
    {A : QuotHom (colourEdges L k 0) (colourEdges L k 0)}
    (hA : ScalesEdgeCoeffs L k (shiftedSymbolPow L k (-(1 / 2))) κ A)
    (hsm : ∀ m ∈ freqBox L k, MultipliersSmallAt L k (shiftedFreq κ m)) :
    quotHomNorm (A.comp (symbolHom (colourVertices L k 0) (colourEdges L k 0)
      (FullSpace.scaledVertexCoboundaryKernel L k 0) κ)) ≤ ENNReal.ofReal 10 := by
  refine quotHomNorm_le_ten _ fun l => ?_
  rw [cE.norm_sq, cV.norm_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  set x := pauliNorm (vertexFourierCoeff L k l m) ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hμ : ∀ μ, pauliNorm (edgeFourierCoeff L k ((A.comp (symbolHom (colourVertices L k 0)
      (colourEdges L k 0) (FullSpace.scaledVertexCoboundaryKernel L k 0) κ)) l) μ m) ^ 2 ≤
        4 * x := by
    intro μ
    rw [LinearMap.comp_apply, hA _ μ m hm, act.vertexCoboundary κ l μ m hm, smul_smul, mul_comm,
      pauliNorm_smul_sq _ (vertexFourierCoeff_mem_traceless L k l m)]
    exact mul_le_mul_of_nonneg_right ((hsm m hm).2 μ).1 hx0
  calc ∑ μ, pauliNorm (edgeFourierCoeff L k ((A.comp (symbolHom (colourVertices L k 0)
        (colourEdges L k 0) (FullSpace.scaledVertexCoboundaryKernel L k 0) κ)) l) μ m) ^ 2
      ≤ ∑ _μ : Fin 4, 4 * x := Finset.sum_le_sum fun μ _ => hμ μ
    _ = 16 * x := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 100 * x := mul_le_mul_of_nonneg_right (by norm_num) hx0
theorem norm_vertexCoboundary_comp_le (cE : EdgeCoeffFacts L k) (cV : VertexCoeffFacts L k)
    (act : CoboundarySymbols L k)
    {A : QuotHom (colourVertices L k 0) (colourVertices L k 0)}
    (hA : ScalesVertexCoeffs L k (shiftedSymbolPow L k (-(1 / 2))) κ A)
    (hsm : ∀ m ∈ freqBox L k, MultipliersSmallAt L k (shiftedFreq κ m)) :
    quotHomNorm ((symbolHom (colourVertices L k 0) (colourEdges L k 0)
      (FullSpace.scaledVertexCoboundaryKernel L k 0) κ).comp A) ≤ ENNReal.ofReal 10 := by
  refine quotHomNorm_le_ten _ fun l => ?_
  rw [cE.norm_sq, cV.norm_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  set x := pauliNorm (vertexFourierCoeff L k l m) ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hμ : ∀ μ, pauliNorm (edgeFourierCoeff L k (((symbolHom (colourVertices L k 0)
      (colourEdges L k 0) (FullSpace.scaledVertexCoboundaryKernel L k 0) κ).comp A) l) μ m) ^ 2 ≤
        4 * x := by
    intro μ
    rw [LinearMap.comp_apply, act.vertexCoboundary κ (A l) μ m hm, hA l m hm, smul_smul,
      pauliNorm_smul_sq _ (vertexFourierCoeff_mem_traceless L k l m)]
    exact mul_le_mul_of_nonneg_right ((hsm m hm).2 μ).1 hx0
  calc ∑ μ, pauliNorm (edgeFourierCoeff L k (((symbolHom (colourVertices L k 0)
        (colourEdges L k 0) (FullSpace.scaledVertexCoboundaryKernel L k 0) κ).comp A) l) μ m) ^ 2
      ≤ ∑ _μ : Fin 4, 4 * x := Finset.sum_le_sum fun μ _ => hμ μ
    _ = 16 * x := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 100 * x := mul_le_mul_of_nonneg_right (by norm_num) hx0
theorem norm_comp_vertexCoboundaryT_le (cE : EdgeCoeffFacts L k) (cV : VertexCoeffFacts L k)
    (act : CoboundarySymbols L k)
    {A : QuotHom (colourVertices L k 0) (colourVertices L k 0)}
    (hA : ScalesVertexCoeffs L k (shiftedSymbolPow L k (-(1 / 2))) κ A)
    (hsm : ∀ m ∈ freqBox L k, MultipliersSmallAt L k (shiftedFreq κ m)) :
    quotHomNorm (A.comp (symbolHom (colourEdges L k 0) (colourVertices L k 0)
      (vertexCoboundaryT L k 0) κ)) ≤ ENNReal.ofReal 10 := by
  refine quotHomNorm_le_ten _ fun b => ?_
  rw [cV.norm_sq, cE.norm_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [LinearMap.comp_apply, hA _ m hm, act.vertexCoboundary_transpose κ b m hm, Finset.smul_sum]
  have e : ∑ μ, shiftedSymbolPow L k (-(1 / 2)) (shiftedFreq κ m) •
        forwardSymbol L k (-shiftedFreq κ m) μ • edgeFourierCoeff L k b μ m =
      ∑ μ, (forwardSymbol L k (-shiftedFreq κ m) μ *
          shiftedSymbolPow L k (-(1 / 2)) (shiftedFreq κ m)) •
        edgeFourierCoeff L k b μ m :=
    Finset.sum_congr rfl fun μ _ => by rw [smul_smul, mul_comm]
  rw [e]
  exact le_hundred_mul_of_le 16 (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)
    (pauliNorm_sum_smul_sq_le _ _ (fun μ => edgeFourierCoeff_mem_traceless L k b μ m)
      fun μ => ((hsm m hm).2 μ).2)
end Bounds
section Transposes
variable {J J' J'' : Type}
theorem linearMapEntry_linearMapOfEntries [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
theorem linearMap_ext_of_entry [Finite J] {M M' : (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (h : linearMapEntry M = linearMapEntry M') : M = M' := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMap_ext_of_entry <;> assumption
theorem linearMap_apply_eq_tsum [Finite J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (f : J → ℂ) (c' : J') :
    M f c' = ∑' d, linearMapEntry M c' d * f d := by
  classical
  cases nonempty_fintype J
  have hf : f = ∑ d, f d • (Pi.single d 1 : J → ℂ) := by
    funext c
    simp [Finset.sum_apply, Pi.single_apply]
  rw [tsum_fintype]
  conv_lhs => rw [hf]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl
theorem applyKernel_linearMapEntry [Finite J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) :
    applyKernel (linearMapEntry M) = fun f => M f := by
  funext f c'
  exact (linearMap_apply_eq_tsum M f c').symm
theorem linearMapEntry_comp [Finite J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (N : (J'' → ℂ) →ₗ[ℂ] (J → ℂ)) :
    linearMapEntry (M.comp N) = compKernel (linearMapEntry M) (linearMapEntry N) := by
  funext c' c
  exact linearMap_apply_eq_tsum M _ c'
variable {I I' I'' : PeriodicData}
theorem linearMapEntry_quotHomTranspose [Finite I'.UnitQuot] (M : QuotHom I I') :
    linearMapEntry (quotHomTranspose M) =
      wTranspose (I.quotWeight 1) (I'.quotWeight 1) (linearMapEntry M) :=
  linearMapEntry_linearMapOfEntries _
theorem quotHomTranspose_comp (hK : TransposeCompDiag)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    (M : QuotHom I I') (N : QuotHom I'' I) :
    quotHomTranspose (M.comp N) = (quotHomTranspose N).comp (quotHomTranspose M) := by
  have := hI.finite_quot
  have := hI'.finite_quot
  have := hI''.finite_quot
  have h := (hK.1 (.quot I hI 1 one_pos) (.quot I' hI' 1 one_pos)
    (.quot I'' hI'' 1 one_pos) (linearMapEntry M) (linearMapEntry N)
    (fun _ _ => Set.toFinite (α := I.UnitQuot) _)).2
  apply linearMap_ext_of_entry
  rw [linearMapEntry_comp, linearMapEntry_quotHomTranspose, linearMapEntry_quotHomTranspose,
    linearMapEntry_quotHomTranspose, linearMapEntry_comp]
  exact h
theorem quotHomNorm_quotHomTranspose (hQ : Quotients.QuotientTransposeNorm)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (M : QuotHom I I') :
    quotHomNorm (quotHomTranspose M) = quotHomNorm M := by
  have := hI.finite_quot
  have := hI'.finite_quot
  have h := ((hQ I I' hI hI' 1 one_pos).2.2.1 1 1 (Or.inl rfl) (Or.inl rfl)).2.2.2
    (linearMapEntry M)
  have e1 : (fun f => quotHomTranspose M f) =
      applyKernel (wTranspose (I.quotWeight 1) (I'.quotWeight 1) (linearMapEntry M)) := by
    rw [← linearMapEntry_quotHomTranspose, applyKernel_linearMapEntry]
  have e2 : (fun f => M f) = applyKernel (linearMapEntry M) :=
    (applyKernel_linearMapEntry M).symm
  unfold quotHomNorm
  rw [e1, e2]
  exact h
theorem symbolHom_kernelTranspose (q2 : StripSymbols.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} {x : Fin 4 → ℂ}
    (hT : IsPeriodicKernel I I' T) (hf : SymbolSummableAt I I' T x) :
    symbolHom I' I (kernelTranspose I I' T) (-x) = quotHomTranspose (symbolHom I I' T x) := by
  have := hI.finite_quot
  have h := ((q2.2.1 I I' hI hI').2.1 T x hT hf).transpose.2.2
  have e : linearMapEntry (symbolHom I I' T x) = quotSymbol I I' T x :=
    linearMapEntry_linearMapOfEntries _
  change linearMapOfEntries (quotSymbol I' I (kernelTranspose I I' T) (-x)) =
    linearMapOfEntries (wTranspose (I.quotWeight 1) (I'.quotWeight 1)
      (linearMapEntry (symbolHom I I' T x)))
  rw [h, e]
  rfl
end Transposes
theorem diagonalSymbolBoundsHold (roots : ResolventRootsOnStrip.ResolventRootsHold)
    (G : FreeResolventRoots) (pw : PlaneWaveCalculusHolds)
    (elem : PlaneWaveBounds.Claim) (q2 : StripSymbols.Claim)
    (hTransposeNorm : Quotients.QuotientTransposeNorm)
    (hK : TransposeCompDiag)
    (t3 : TowerIndexSets.Claim) (ops : FreeOperators.FreeOperatorsArePeriodic) :
    DiagonalSymbolBoundsHold := by
  intro L hL k hk κ hκ
  obtain ⟨hSI, hBI, hPI⟩ := t3 L hL k 0 (Nat.zero_le k)
  obtain ⟨-, cV, cE, cF, -, act, -⟩ := pw L hL k hk
  obtain ⟨rB, rS⟩ := roots L hL k hk
  obtain ⟨-, -, -, fB, fS, -⟩ := G L hL k hk
  obtain ⟨mk, -⟩ := ops.2 L hL k hk
  have hint := q2.1 (1 / 8) (by norm_num)
  have hσ : (-(1 / 2) : ℝ) ∈ resolventExponents := by simp [resolventExponents]
  have hopen : ∀ x ∈ openStripInterior (1 / 8), ∀ ν, |(x ν).im| < 1 / 8 := by
    intro x hx
    rw [hint.1] at hx
    exact hx
  have hstrip : ∀ x ∈ openStripInterior (1 / 8), x ∈ imStrip (1 / 8) := fun x hx ν =>
    (hopen x hx ν).le
  have hsm : ∀ x ∈ openStripInterior (1 / 8), ∀ m ∈ freqBox L k,
      MultipliersSmallAt L k (shiftedFreq x m) := by
    intro x hx m _
    refine multipliersSmallAt elem hL hk _ fun ν => ?_
    have e : (shiftedFreq x m ν).im = (x ν).im := by simp [PlaneWaves.shiftedFreq]
    rw [e]
    exact (hopen x hx ν).le
  have hb : ∀ x ∈ openStripInterior (1 / 8),
      ScalesEdgeCoeffs L k (shiftedSymbolPow L k (-(1 / 2))) x
        (edgeResolventSqrtSymbol L k x) := by
    intro x hx
    have h := (fB.scales_unique _ hσ x (hstrip x hx)).1
    have e : edgeResolventSqrtSymbol L k x = edgePowMatrix L k (-(1 / 2)) x :=
      rB.sqrt_symbol x hx
    rw [e]
    exact h
  have hs : ∀ x ∈ openStripInterior (1 / 8),
      ScalesVertexCoeffs L k (shiftedSymbolPow L k (-(1 / 2))) x
        (symbolHom (colourVertices L k 0) (colourVertices L k 0) (vertexResolventSqrt L k) x) := by
    intro x hx
    have h := (fS.scales_unique _ hσ x (hstrip x hx)).1
    rw [rS.sqrt_symbol x hx]
    exact h
  have hneg : -κ ∈ openStripInterior (1 / 8) := by
    rw [hint.1]
    intro ν
    have := hopen κ hκ ν
    simpa using this
  refine ⟨norm_edgeMultiplier_le cE (hb κ hκ) (hsm κ hκ),
    norm_vertexMultiplier_le cV (hs κ hκ) (hsm κ hκ),
    norm_edgeCoboundary_comp_le cE cF act (hb κ hκ) (hsm κ hκ),
    norm_vertexCoboundaryT_comp_le cE cV act (hb κ hκ) (hsm κ hκ),
    norm_comp_vertexCoboundary_le cE cV act (hb κ hκ) (hsm κ hκ), ?_,
    norm_vertexCoboundary_comp_le cE cV act (hs κ hκ) (hsm κ hκ),
    norm_comp_vertexCoboundaryT_le cE cV act (hs κ hκ) (hsm κ hκ)⟩
  have hD := (mk.edgeCoboundary 0 (Nat.zero_le k)).finite_range
  have hDf : SymbolSummableAt (colourEdges L k 0) (colourFaces L k 0)
      (FullSpace.scaledEdgeCoboundaryKernel L k 0) (-κ) :=
    (q2.2.1 _ _ hBI hPI).1.finiteRange _ hD.1 hD.2.1 (-κ) (mem_univ _)
  have e1 := symbolHom_kernelTranspose q2 hBI hPI hD.1 hDf
  rw [neg_neg] at e1
  have e2 := symbolHom_kernelTranspose q2 hBI hBI rB.sqrt_periodic (rB.sqrt_summable (-κ) hneg)
  rw [neg_neg] at e2
  have e3 : kernelTranspose (colourEdges L k 0) (colourEdges L k 0) (edgeResolventSqrt L k) =
      edgeResolventSqrt L k := fB.transpose_eq _ hσ
  rw [e3] at e2
  have e4 : (edgeResolventSqrtSymbol L k κ).comp
      (symbolHom (colourFaces L k 0) (colourEdges L k 0)
        (kernelTranspose (colourEdges L k 0) (colourFaces L k 0)
          (FullSpace.scaledEdgeCoboundaryKernel L k 0)) κ) =
      quotHomTranspose ((symbolHom (colourEdges L k 0) (colourFaces L k 0)
        (FullSpace.scaledEdgeCoboundaryKernel L k 0) (-κ)).comp
          (edgeResolventSqrtSymbol L k (-κ))) := by
    rw [quotHomTranspose_comp hK hBI hPI hBI, e1]
    exact congrArg (fun A => LinearMap.comp A _) e2
  rw [e4, quotHomNorm_quotHomTranspose hTransposeNorm hBI hPI]
  exact norm_edgeCoboundary_comp_le cE cF act (hb _ hneg) (hsm _ hneg)
end YangMills.Construction.Tower.DiagonalSymbolBounds
end
