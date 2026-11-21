import YangMills.Construction.LawInAState.DecayOverATorusProof
import YangMills.Construction.Matrices.OperatorNormAbsoluteSeriesProof
import YangMills.Construction.RunningCouplingSlope.ResponseOfAUnitFormDecays
import YangMills.Construction.RunningCouplingSlope.SizesOfTheLongWavesProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Towers.SymbolOfTheTotalNormaliserIsATemperingChoiceProof
import YangMills.Construction.Towers.TheFormsOfBondsAsFieldsOnTheClassesProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.UnitFormDecay
open Matrices OneLoop Coordinates
section LatticeSums
open PeriodicOperators
open TorusMetric (l1NormVec)
private def geometricLineBound (c : ℝ) : ℝ := Real.exp c * ∑' l : ℤ, Real.exp (-(c * |(l : ℝ)|))
private theorem summable_exp_abs_int {c : ℝ} (hc : 0 < c) :
    Summable fun l : ℤ => Real.exp (-(c * |(l : ℝ)|)) := by apply _root_.YangMills.SharedProofs.p3695 <;> assumption
private theorem geometricLineBound_nonneg (c : ℝ) : 0 ≤ geometricLineBound c :=
  mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le)
private theorem sum_exp_affine_le {c s : ℝ} (hc : 0 < c) (hs : 1 ≤ s) (t : ℝ) (J : Finset ℤ) :
    ∑ j ∈ J, Real.exp (-(c * |t + s * (j : ℝ)|)) ≤ geometricLineBound c := by
  have hs0 : 0 < s := by linarith
  set j₀ : ℤ := ⌊-t / s⌋ with hj₀
  have h₁ : (j₀ : ℝ) * s ≤ -t := by
    have := Int.floor_le (-t / s)
    rwa [le_div_iff₀ hs0] at this
  have h₂ : -t < ((j₀ : ℝ) + 1) * s := by
    have := Int.lt_floor_add_one (-t / s)
    rwa [div_lt_iff₀ hs0] at this
  have key : ∀ j : ℤ, |((j - j₀ : ℤ) : ℝ)| - 1 ≤ |t + s * (j : ℝ)| := by
    intro j
    push_cast
    rcases le_total (j₀ + 1) j with h | h
    · have hj : ((j₀ : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast h
      have e₁ : 0 ≤ (j : ℝ) - j₀ := by linarith
      rw [abs_of_nonneg e₁]
      have e₂ : ((j : ℝ) - j₀ - 1) ≤ s * ((j : ℝ) - j₀ - 1) := by
        have : 0 ≤ (j : ℝ) - j₀ - 1 := by linarith
        nlinarith
      have e₃ : s * ((j : ℝ) - j₀ - 1) ≤ t + s * (j : ℝ) := by nlinarith
      exact e₂.trans (e₃.trans (le_abs_self _))
    · have hj : (j : ℝ) ≤ (j₀ : ℝ) + 1 := by exact_mod_cast h
      have e₃ : t + s * (j : ℝ) ≤ s * ((j : ℝ) - j₀) := by nlinarith
      rcases le_total (j : ℝ) j₀ with h' | h'
      · have e₁ : (j : ℝ) - j₀ ≤ 0 := by linarith
        rw [abs_of_nonpos e₁]
        have e₂ : -((j : ℝ) - j₀) ≤ s * -((j : ℝ) - j₀) := by nlinarith
        have := neg_le_abs (t + s * (j : ℝ))
        linarith
      · have e₁ : 0 ≤ (j : ℝ) - j₀ := by linarith
        rw [abs_of_nonneg e₁]
        have := abs_nonneg (t + s * (j : ℝ))
        linarith
  have hterm : ∀ j : ℤ, Real.exp (-(c * |t + s * (j : ℝ)|)) ≤
      Real.exp c * Real.exp (-(c * |((j - j₀ : ℤ) : ℝ)|)) := by
    intro j
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left (key j) hc.le
    linarith
  calc ∑ j ∈ J, Real.exp (-(c * |t + s * (j : ℝ)|))
      ≤ ∑ j ∈ J, Real.exp c * Real.exp (-(c * |((j - j₀ : ℤ) : ℝ)|)) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = Real.exp c * ∑ l ∈ J.image (fun j => j - j₀), Real.exp (-(c * |(l : ℝ)|)) := by
        rw [← Finset.mul_sum, Finset.sum_image]
        intro a _ b _ e
        simpa using e
    _ ≤ geometricLineBound c := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact (summable_exp_abs_int hc).sum_le_tsum _ fun _ _ => (Real.exp_pos _).le
private theorem sum_exp_lattice_le {c s : ℝ} (hc : 0 < c) (hs : 1 ≤ s) (w : Fin 4 → ℝ)
    (F : Finset (Fin 4 → ℤ)) :
    ∑ m ∈ F, Real.exp (-(c * l1NormVec fun μ => w μ + s * (m μ : ℝ))) ≤ geometricLineBound c ^ 4 := by
  classical
  set P : Fin 4 → Finset ℤ := fun μ => F.image fun m => m μ with hP
  have hsub : F ⊆ Fintype.piFinset P := by
    intro m hm
    exact Fintype.mem_piFinset.2 fun μ => Finset.mem_image.2 ⟨m, hm, rfl⟩
  have hexp : ∀ m : Fin 4 → ℤ, Real.exp (-(c * l1NormVec fun μ => w μ + s * (m μ : ℝ))) =
      ∏ μ, Real.exp (-(c * |w μ + s * (m μ : ℝ)|)) := by
    intro m
    rw [← Real.exp_sum, l1NormVec, Finset.mul_sum, Finset.sum_neg_distrib]
  calc ∑ m ∈ F, Real.exp (-(c * l1NormVec fun μ => w μ + s * (m μ : ℝ)))
      ≤ ∑ m ∈ Fintype.piFinset P, Real.exp (-(c * l1NormVec fun μ => w μ + s * (m μ : ℝ))) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le
    _ = ∏ μ, ∑ j ∈ P μ, Real.exp (-(c * |w μ + s * (j : ℝ)|)) := by
        rw [Finset.prod_univ_sum]
        exact Finset.sum_congr rfl fun m _ => hexp m
    _ ≤ ∏ _μ : Fin 4, geometricLineBound c :=
        Finset.prod_le_prod (fun μ _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
          fun μ _ => sum_exp_affine_le hc hs _ _
    _ = geometricLineBound c ^ 4 := by simp
private theorem norm_tsum_periodic_translates_le (I I' : PeriodicData) (hI : IsPeriodic I)
    {T : I'.Carrier → I.Carrier → ℂ} {C υ D d : ℝ} (hC : 0 ≤ C) (hυ : 0 < υ)
    (hT : ∀ ι' ι, ‖T ι' ι‖ ≤ C * Real.exp (-υ * l1NormVec (I.pos ι - I'.pos ι')))
    {s : ℕ} (hs : 0 < s) (ι' : I'.Carrier) (ι : I.Carrier)
    (hd : ∀ m : Fin 4 → ℤ,
      d ≤ D + l1NormVec (I.pos (I.translate (s • m) ι) - I'.pos ι')) :
    ‖∑' m : Fin 4 → ℤ, T ι' (I.translate (s • m) ι)‖ ≤
      C * Real.exp (υ / 2 * D) * geometricLineBound (υ / 2) ^ 4 * Real.exp (-(υ / 2 * d)) := by
  have hc : 0 < υ / 2 := by positivity
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  set w : Fin 4 → ℝ := I.pos ι - I'.pos ι' with hw
  have hpos : ∀ m : Fin 4 → ℤ, I.pos (I.translate (s • m) ι) - I'.pos ι' =
      fun μ => w μ + (s : ℝ) * (m μ : ℝ) := by
    intro m
    rw [hI.pos_translate]
    funext μ
    simp [hw, castVec]
    ring
  have hterm : ∀ m : Fin 4 → ℤ, ‖T ι' (I.translate (s • m) ι)‖ ≤
      C * Real.exp (υ / 2 * D) * Real.exp (-(υ / 2 * d)) *
        Real.exp (-(υ / 2 * l1NormVec fun μ => w μ + (s : ℝ) * (m μ : ℝ))) := by
    intro m
    refine (hT ι' _).trans ?_
    have h := hd m
    rw [hpos m] at h ⊢
    rw [mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left h hc.le
    nlinarith
  set K := C * Real.exp (υ / 2 * D) * Real.exp (-(υ / 2 * d)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hsum : ∀ F : Finset (Fin 4 → ℤ), ∑ m ∈ F, ‖T ι' (I.translate (s • m) ι)‖ ≤
      K * geometricLineBound (υ / 2) ^ 4 := by
    intro F
    calc ∑ m ∈ F, ‖T ι' (I.translate (s • m) ι)‖
        ≤ ∑ m ∈ F, K * Real.exp (-(υ / 2 * l1NormVec fun μ => w μ + (s : ℝ) * (m μ : ℝ))) :=
          Finset.sum_le_sum fun m _ => hterm m
      _ = K * ∑ m ∈ F, Real.exp (-(υ / 2 * l1NormVec fun μ => w μ + (s : ℝ) * (m μ : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ K * geometricLineBound (υ / 2) ^ 4 :=
          mul_le_mul_of_nonneg_left (sum_exp_lattice_le hc hs1 w F) hK0
  have hsummable : Summable fun m : Fin 4 → ℤ => ‖T ι' (I.translate (s • m) ι)‖ :=
    summable_of_sum_le (fun _ => norm_nonneg _) hsum
  calc ‖∑' m : Fin 4 → ℤ, T ι' (I.translate (s • m) ι)‖
      ≤ ∑' m : Fin 4 → ℤ, ‖T ι' (I.translate (s • m) ι)‖ := norm_tsum_le_tsum_norm hsummable
    _ ≤ K * geometricLineBound (υ / 2) ^ 4 := hsummable.tsum_le_of_sum_le hsum
    _ = C * Real.exp (υ / 2 * D) * geometricLineBound (υ / 2) ^ 4 * Real.exp (-(υ / 2 * d)) := by
        rw [hK]
        ring
end LatticeSums
section SymbolEstimates
open Tower.BackgroundFieldResponse (responseKernel)
open Tower PeriodicOperators
open Tower.ResponseProperties (ResponseBound InFundamentalStrip responseSymbolForm)
open Tower.FullSpace.BackgroundProperties (edgeCoboundarySymbol edgeFormOf faceFunctionOf)
private theorem norm_matrix_entry_le (X : ComplexMatrix2) (i j : Fin 2) :
    ‖X i j‖ ≤ ComplexMatrix2.operatorNorm X := by apply _root_.YangMills.SharedProofs.p34458 <;> assumption
private theorem norm_pauli_coord_le (x : Fin 3 → ℂ) (a : Fin 3) :
    ‖x a‖ ≤ ComplexMatrix2.operatorNorm (∑ b, x b • ComplexMatrix2.pauliFamily b) := by
  set X := ∑ b, x b • ComplexMatrix2.pauliFamily b with hX
  have e := ComplexMatrix2.sum_smul_pauliFamily x
  rw [← hX] at e
  have e00 : X 0 0 = x 2 := by simp [e]
  have e01 : X 0 1 = x 0 - Complex.I * x 1 := by simp [e]
  have e10 : X 1 0 = x 0 + Complex.I * x 1 := by simp [e]
  have n01 := norm_matrix_entry_le X 0 1
  have n10 := norm_matrix_entry_le X 1 0
  fin_cases a
  · have : x 0 = (X 0 1 + X 1 0) / 2 := by rw [e01, e10]; ring
    show ‖x 0‖ ≤ _
    rw [this, norm_div]
    have := norm_add_le (X 0 1) (X 1 0)
    simp only [Complex.norm_ofNat]
    linarith
  · have : x 1 = (X 1 0 - X 0 1) / (2 * Complex.I) := by
      rw [e01, e10]
      field_simp
      ring
    show ‖x 1‖ ≤ _
    rw [this, norm_div]
    have := norm_sub_le (X 1 0) (X 0 1)
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    linarith
  · show ‖x 2‖ ≤ _
    rw [← e00]
    exact norm_matrix_entry_le X 0 0
section ScalarHolomorphy
variable {N : ℕ}
private theorem isHolomorphicIn_scalar_mono {O O' : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun w _ => u w) (hs : O' ⊆ O)
    (ho : IsOpen O') : ComplexCoordinates.IsHolomorphicIn (N' := 1) O' fun w _ => u w := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_mono <;> assumption
private theorem isHolomorphicIn_scalar_congr {O : Set (ComplexCoordinates N)} {u v : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun w _ => u w) (e : EqOn v u O) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun w _ => v w := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_congr <;> assumption
private theorem isHolomorphicIn_scalar_mul {O : Set (ComplexCoordinates N)} {u v : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun w _ => u w)
    (h' : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun w _ => v w) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun w _ => u w * v w := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_mul <;> assumption
private theorem isHolomorphicIn_scalar_sum {J : Type} (s : Finset J) {O : Set (ComplexCoordinates N)}
    (ho : IsOpen O) {u : J → ComplexCoordinates N → ℂ}
    (h : ∀ i ∈ s, ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun w _ => u i w) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun w _ => ∑ i ∈ s, u i w := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_sum <;> assumption
end ScalarHolomorphy
private theorem symbolHom_eq_applyKernel (I I' : PeriodicData) [Finite I.UnitQuot]
    (T : I'.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    symbolHom I I' T κ φ = applyKernel (quotSymbol I I' T κ) φ :=
  linearMapOfEntries_eq_applyKernel _ _
private theorem linearMap_apply_eq_sum_entry {J J' : Type} [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (f : J → ℂ) (c' : J') :
    M f c' = ∑ c, linearMapEntry M c' c * f c := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.apply_eq_sum_linearMapEntry <;> assumption
private theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
private theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem isCoboundaryFactor_of_blochWave (L k : ℕ) (q : Fin 4 → ℂ)
    (b : (colourEdges L k 0).UnitQuot → ℂ) (F : (colourFaces L k 0).UnitQuot → ℂ)
    (hmap : (FullSpace.edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (FullSpace.Face L k 0))
        FullSpace.scaledEdgeCoboundary (blochWave (colourEdges L k 0) q b) =
      blochWave (colourFaces L k 0) q F) :
    ResponseProperties.IsCoboundaryFactor L k q (edgeFormOf L k b) (faceFunctionOf L k F) := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isCoboundaryFactor_of_mapOnCoeffs <;> assumption
private theorem pauliNorm_combination_le (x : Fin 3 → ℂ) (hx : ∀ a, ‖x a‖ ≤ 1) :
    pauliNorm (∑ a, x a • ComplexMatrix2.pauliFamily a) ≤ 2 := by
  unfold pauliNorm
  simp only [pauliCoeff_combination]
  refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
  have : ∀ a, ‖x a‖ ^ 2 ≤ 1 := fun a => pow_le_one₀ (norm_nonneg _) (hx a)
  rw [Fin.sum_univ_three]
  linarith [this 0, this 1, this 2]
private theorem pauliFamilyNorm_topEdge_le (L k : ℕ) (ε : (colourEdges L k k).UnitQuot → ℂ)
    (hε : ∀ c, ‖ε c‖ ≤ 1) :
    pauliFamilyNorm (PlaneWaveCalculus.topEdgeComponent L k ε) ≤ 4 := by
  unfold pauliFamilyNorm
  refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
  have h : ∀ μ, pauliNorm (PlaneWaveCalculus.topEdgeComponent L k ε μ) ^ 2 ≤ 4 := by
    intro μ
    have h₁ : pauliNorm (PlaneWaveCalculus.topEdgeComponent L k ε μ) ≤ 2 :=
      pauliNorm_combination_le _ fun a => hε _
    have h₀ : 0 ≤ pauliNorm (PlaneWaveCalculus.topEdgeComponent L k ε μ) := Real.sqrt_nonneg _
    nlinarith
  calc ∑ μ, pauliNorm (PlaneWaveCalculus.topEdgeComponent L k ε μ) ^ 2
      ≤ ∑ _μ : Fin 4, (4 : ℝ) := Finset.sum_le_sum fun μ _ => h μ
    _ ≤ 4 ^ 2 := by norm_num
private theorem response_symbol_entries_le (hW : PlaneWaveCalculus.PlaneWaveCalculusHolds) {C₀ : ℝ}
    (hC : ResponseBound C₀) {δ₀ : ℝ} (hδ : δ₀ ∈ FreeStrip.halfSupRate) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hcurv : ∀ (q : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ),
      (FullSpace.edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (FullSpace.Face L k 0))
        FullSpace.scaledEdgeCoboundary (blochWave (colourEdges L k 0) q b) =
      blochWave (colourFaces L k 0) q (edgeCoboundarySymbol L k q b))
    {κ : Fin 4 → ℂ} (hκ : InFundamentalStrip δ₀ κ) (ε : (colourEdges L k k).UnitQuot → ℂ)
    (hε : ∀ c, ‖ε c‖ ≤ 1) :
    (∀ c', ‖responseSymbolForm L k κ ε c'‖ ≤ 4 * |C₀|) ∧
      ∀ c', ‖edgeCoboundarySymbol L k κ (responseSymbolForm L k κ ε) c'‖ ≤ 4 * |C₀| := by
  set b := responseSymbolForm L k κ ε with hb
  set F := edgeCoboundarySymbol L k κ b with hF
  have hform : ResponseProperties.IsFourierSynthesis L k b (edgeFormOf L k b) :=
    fun x ρ => (hW L hL k hk).2.2.1.expansion _ ρ x
  have hfac := isCoboundaryFactor_of_blochWave L k κ b F (hcurv κ b)
  obtain ⟨hα, hf, hsum⟩ := hC δ₀ hδ L hL k hk κ hκ ε _ _ hform hfac
  have n₁ : 0 ≤ wNorm ((colourEdges L k 0).quotWeight 1) (responseSymbolForm L k κ ε) :=
    Real.sqrt_nonneg _
  have n₂ : 0 ≤ pauliFamilyNorm (PlaneWaveCalculus.topEdgeComponent L k
      (ResponseProperties.defectSymbol L k κ ε)) := Real.sqrt_nonneg _
  have n₃ : 0 ≤ pauliNorm (PlaneWaveCalculus.topVertexElement L k
      (ResponseProperties.smoothedDivergence L k κ ε)) := Real.sqrt_nonneg _
  have n₄ : 0 ≤ PeriodicLattice.supOfOperatorNorms (edgeFormOf L k b) :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  have n₅ : 0 ≤ PeriodicLattice.supOfOperatorNorms (faceFunctionOf L k F) :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  have hfam := pauliFamilyNorm_topEdge_le L k ε hε
  have hfam₀ : 0 ≤ pauliFamilyNorm (PlaneWaveCalculus.topEdgeComponent L k ε) := Real.sqrt_nonneg _
  have hCle : C₀ * pauliFamilyNorm (PlaneWaveCalculus.topEdgeComponent L k ε) ≤ 4 * |C₀| := by
    calc _ ≤ |C₀| * pauliFamilyNorm (PlaneWaveCalculus.topEdgeComponent L k ε) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hfam₀
      _ ≤ |C₀| * 4 := mul_le_mul_of_nonneg_left hfam (abs_nonneg _)
      _ = 4 * |C₀| := mul_comm _ _
  refine ⟨fun c' => ?_, fun c' => ?_⟩
  · induction c' using Quot.ind with
    | mk ι =>
      obtain ⟨a, β⟩ := ι
      have h₁ := norm_pauli_coord_le (fun a' => b ((colourEdges L k 0).mkQuot 1 (a', β))) a
      have h₂ : ComplexMatrix2.operatorNorm (edgeFormOf L k b β) ≤
          PeriodicLattice.supOfOperatorNorms (edgeFormOf L k b) :=
        le_ciSup hα β
      have h₃ : ComplexMatrix2.operatorNorm
          (∑ a', b ((colourEdges L k 0).mkQuot 1 (a', β)) • ComplexMatrix2.pauliFamily a') ≤
          PeriodicLattice.supOfOperatorNorms (edgeFormOf L k b) := h₂
      refine (h₁.trans h₃).trans ?_
      linarith
  · induction c' using Quot.ind with
    | mk ι =>
      obtain ⟨a, P⟩ := ι
      have h₁ := norm_pauli_coord_le (fun a' => F ((colourFaces L k 0).mkQuot 1 (a', P))) a
      have h₂ : ComplexMatrix2.operatorNorm (faceFunctionOf L k F P) ≤
          PeriodicLattice.supOfOperatorNorms (faceFunctionOf L k F) := le_ciSup hf P
      have h₃ : ComplexMatrix2.operatorNorm
          (∑ a', F ((colourFaces L k 0).mkQuot 1 (a', P)) • ComplexMatrix2.pauliFamily a') ≤
          PeriodicLattice.supOfOperatorNorms (faceFunctionOf L k F) := h₂
      refine (h₁.trans h₃).trans ?_
      linarith
private theorem norm_phaseOn_eq_one (hS : SymbolCalculus.Claim) {I : PeriodicData} (hI : IsPeriodic I)
    (e : Fin 4 → ℤ) (c : I.UnitQuot) : ‖phaseOn I e c‖ = 1 := by
  induction c using Quot.ind with
  | mk ι =>
    have hph := ((hS I I hI hI).2.2.2.1 e).1
    have hspec := Classical.epsilon_spec (p := fun w => ∀ ι', I.mkQuot 1 ι' = I.mkQuot 1 ι →
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι'))) = w)
      ⟨_, fun ι' h => hph ι' ι h⟩
    have h := hspec ι rfl
    have e₁ : phaseOn I e (Quot.mk _ ι) = Classical.epsilon (fun w => ∀ ι',
        I.mkQuot 1 ι' = I.mkQuot 1 ι → Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι'))) = w) := rfl
    rw [e₁, ← h]
    have e₂ : bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι)) =
        ((∑ μ, (e μ : ℝ) * I.pos ι μ : ℝ) : ℂ) := by
      simp [bilinDot, toComplexVec, castVec]
    rw [e₂]
    have e₃ : (2 * Real.pi * Complex.I * ((∑ μ, (e μ : ℝ) * I.pos ι μ : ℝ) : ℂ) : ℂ) =
        ((2 * Real.pi * ∑ μ, (e μ : ℝ) * I.pos ι μ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e₃, Complex.norm_exp_ofReal_mul_I]
private theorem phaseMul_of_supported_at {I : PeriodicData} (e : Fin 4 → ℤ) (c : I.UnitQuot)
    (ε : I.UnitQuot → ℂ) (hε : ∀ c', c' ≠ c → ε c' = 0) : phaseMul I e ε = phaseOn I e c • ε := by
  funext c'
  by_cases h : c' = c
  · subst h
    rfl
  · show phaseOn I e c' * ε c' = phaseOn I e c * ε c'
    rw [hε c' h]
    simp
open Classical in
private theorem norm_linearMapEntry_conj_phase (hS : SymbolCalculus.Claim) {I I' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {A B : QuotHom I I'}
    (e : Fin 4 → ℤ)
    (hAB : A = (quotHomInverse (phaseMul I' e)).comp (B.comp (phaseMul I e)))
    (c' : I'.UnitQuot) (c : I.UnitQuot) : ‖linearMapEntry A c' c‖ = ‖linearMapEntry B c' c‖ := by
  have hinv : IsInvertibleQuotHom (phaseMul I' e : QuotHom I' I') :=
    ((hS I' I' hI' hI').2.2.2.2.2.2.1 1 one_pos).1 e
  unfold linearMapEntry
  have hE := phaseMul_of_supported_at (I := I) e c (Pi.single c 1) fun c'' h => Pi.single_eq_of_ne h 1
  rw [hAB, LinearMap.comp_apply, LinearMap.comp_apply, hE, map_smul, map_smul]
  set g := B (Pi.single c 1) with hg
  have hu := hinv.apply_quotHomInverse g
  set u := quotHomInverse (phaseMul I' e) g with hudef
  have e₁ : g c' = phaseOn I' e c' * u c' := by
    rw [← hu]
    rfl
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_phaseOn_eq_one hS hI, one_mul, e₁, norm_mul,
    norm_phaseOn_eq_one hS hI', one_mul]
private theorem symbolHom_addTwoPiInt (hSym : Symbols.Claim)
    (hId : IdKernelFacts.Claim) {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hper : IsPeriodicKernel I I' T)
    {κ : Fin 4 → ℂ} (hκ : SymbolSummableAt I I' T κ) (e : Fin 4 → ℤ) :
    symbolHom I I' T (addTwoPiInt κ e) =
      (quotHomInverse (phaseMul I' e)).comp
        ((symbolHom I I' T κ).comp (phaseMul I e)) := by
  obtain ⟨_, C, δ, hC, hδ, hb⟩ := id hper
  have hid := hId _ hI
  have facts := hSym.1 _ _ _ hI hI' hI T (idKernel _) δ hper ⟨hδ, C, hC, hb⟩ hid.1
    (hid.2.1 δ hδ)
  obtain ⟨_, _, h⟩ := facts.quotSymbol_addTwoPiInt κ e hκ
  have : Finite I.UnitQuot := hI.finite_quot
  refine LinearMap.ext fun f => ?_
  rw [symbolHom_eq_applyKernel, h f, LinearMap.comp_apply, LinearMap.comp_apply, symbolHom_eq_applyKernel]
  rfl
private theorem exists_addTwoPiInt_re_le_pi (κ : Fin 4 → ℂ) : ∃ e : Fin 4 → ℤ, ∀ μ,
    |(addTwoPiInt κ e μ).re| ≤ Real.pi ∧ (addTwoPiInt κ e μ).im = (κ μ).im := by
  refine ⟨fun μ => -round ((κ μ).re / (2 * Real.pi)), fun μ => ?_⟩
  have hpi := Real.pi_pos
  set x := (κ μ).re / (2 * Real.pi) with hx
  have hre : (κ μ).re = 2 * Real.pi * x := by
    rw [hx]
    field_simp
  have e₁ : (addTwoPiInt κ (fun μ => -round ((κ μ).re / (2 * Real.pi))) μ) =
      κ μ + ((2 * Real.pi * (-(round x : ℝ)) : ℝ) : ℂ) := by
    simp [addTwoPiInt, ← hx]
  rw [e₁, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, hre]
  refine ⟨?_, rfl⟩
  have h := abs_sub_round x
  have e₂ : 2 * Real.pi * x + 2 * Real.pi * -(round x : ℝ) = 2 * Real.pi * (x - round x) := by ring
  rw [e₂, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  nlinarith
private theorem scaledEdgeCoboundary_symbol_facts (hFO : FreeOperators.FreeOperatorsArePeriodic)
    (hS : SymbolCalculus.Claim) (hSym : Symbols.Claim) (hId : IdKernelFacts.Claim)
    {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hB : IsPeriodic (colourEdges L k 0))
    (hP : IsPeriodic (colourFaces L k 0)) :
    IsPeriodicKernel (colourEdges L k 0) (colourFaces L k 0)
        (FullSpace.scaledEdgeCoboundaryKernel L k 0) ∧
      FourierSymbolIsEntire (colourEdges L k 0) (colourFaces L k 0)
        (FullSpace.scaledEdgeCoboundaryKernel L k 0) ∧
      (∀ δ : ℝ, 0 < δ → IsDecayRate (colourEdges L k 0) (colourFaces L k 0)
        (FullSpace.scaledEdgeCoboundaryKernel L k 0) δ) ∧
      ∀ (q : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ),
        (FullSpace.edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (FullSpace.Face L k 0))
            FullSpace.scaledEdgeCoboundary (blochWave (colourEdges L k 0) q b) =
          blochWave (colourFaces L k 0) q (edgeCoboundarySymbol L k q b) := by
  have hk3 := (hFO.2 L hL k hk).1.edgeCoboundary 0 (Nat.zero_le k)
  obtain ⟨hper, hfin, hrate⟩ := hk3.finite_range
  have hent := (hS _ _ hB hP).1 _ hper hfin
  refine ⟨hper, hent, hrate, fun q b => ?_⟩
  have hI := hId _ hB
  have facts := hSym.1 _ _ _ hB hP hB _ (idKernel _) 1 hper (hrate 1 one_pos) hI.1
    (hI.2.1 1 one_pos)
  have : Finite (colourEdges L k 0).UnitQuot := hB.finite_quot
  rw [← hk3.applyKernel_eq]
  funext ι'
  rw [(facts.applyKernel_blochWave q (hent.1 q (mem_univ q)) b ι').2]
  exact congrArg (fun φ => blochWave (colourFaces L k 0) q φ ι')
    (symbolHom_eq_applyKernel (colourEdges L k 0) (colourFaces L k 0)
      (FullSpace.scaledEdgeCoboundaryKernel L k 0) q b).symm
private theorem symbolHom_entry_entire (hQ : StripSymbols.Claim) {I I' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hper : IsPeriodicKernel I I' T) (hent : FourierSymbolIsEntire I I' T) (c' : I'.UnitQuot)
    (c : I.UnitQuot) :
    ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) univ fun κ _ =>
      linearMapEntry (symbolHom I I' T κ) c' c := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_linearMapEntry_of_entire <;> assumption
open Classical in
private def indicatorAt {J : Type} (c : J) : J → ℂ := Pi.single c 1
private theorem norm_indicatorAt_le {J : Type} (c c' : J) : ‖indicatorAt c c'‖ ≤ 1 := by
  classical
  unfold indicatorAt
  by_cases h : c' = c
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h]
    simp
private theorem applyKernel_compKernel {J J' J'' : Type} [Fintype J] [Fintype J''] (A : J' → J → ℂ)
    (B : J → J'' → ℂ) (f : J'' → ℂ) :
    applyKernel (compKernel A B) f = applyKernel A (applyKernel B f) := by
  funext c
  simp only [applyKernel, compKernel, tsum_fintype, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
private theorem exists_translate_inFundamentalStrip {δ₀ : ℝ} {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip (2 * δ₀)) :
    ∃ e : Fin 4 → ℤ, InFundamentalStrip δ₀ (addTwoPiInt κ e) := by
  obtain ⟨e, he⟩ := exists_addTwoPiInt_re_le_pi κ
  refine ⟨e, fun μ => ?_, fun μ => (he μ).1⟩
  rw [(he μ).2]
  exact hκ μ
private theorem realDualPoints_mem_strictImStrip {δ : ℝ} (hδ : 0 < δ) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ realDualPoints) : κ ∈ strictImStrip δ := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.real_mem_imStrip_pos <;> assumption
private theorem responseKernel_decay (hFO : FreeOperators.FreeOperatorsArePeriodic)
    (hS : SymbolCalculus.Claim) (hSym : Symbols.Claim) (hId : IdKernelFacts.Claim)
    (hQ : StripSymbols.Claim) (hW : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim) {C₀ : ℝ} (hC : ResponseBound C₀) {δ₀ : ℝ}
    (hδ : δ₀ ∈ FreeStrip.halfSupRate) (hδ₀ : 0 < δ₀) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hat : ResponseOperators.AtLevel δ₀ L k) :
    (∀ ι' ι, ‖responseKernel L k ι' ι‖ ≤ 4 * |C₀| * Real.exp (-(2 * δ₀) *
      TorusMetric.l1NormVec ((colourEdges L k k).pos ι - (colourEdges L k 0).pos ι'))) ∧
    ∀ ι' ι, ‖compKernel (FullSpace.scaledEdgeCoboundaryKernel L k 0) (responseKernel L k) ι' ι‖ ≤
      4 * |C₀| * Real.exp (-(2 * δ₀) * TorusMetric.l1NormVec
        ((colourEdges L k k).pos ι - (colourFaces L k 0).pos ι')) := by
  have pB := (hIdx L hL k 0 (Nat.zero_le k)).2.1
  have pP := (hIdx L hL k 0 (Nat.zero_le k)).2.2
  have pT := (hIdx L hL k k le_rfl).2.1
  have hυ : 0 < 2 * δ₀ := by positivity
  obtain ⟨O, hOopen, hsub, hsym⟩ := hat.near
  obtain ⟨hd, hent, hdrate, hcurv⟩ := scaledEdgeCoboundary_symbol_facts hFO hS hSym hId hL hk pB pP
  let M : (Fin 4 → ℂ) → QuotHom (colourEdges L k k) (colourEdges L k 0) :=
    symbolHom (colourEdges L k k) (colourEdges L k 0) (responseKernel L k)
  let M' : (Fin 4 → ℂ) → QuotHom (colourEdges L k k) (colourFaces L k 0) :=
    fun κ => (edgeCoboundarySymbol L k κ).comp (M κ)
  have hformed : ∀ κ ∈ imStrip (2 * δ₀),
      SymbolSummableAt (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ :=
    fun κ hκ => hsym.resp_summable κ (hsub hκ)
  have hMt : ∀ κ ∈ imStrip (2 * δ₀), ∀ e, M (addTwoPiInt κ e) =
      (quotHomInverse (phaseMul (colourEdges L k 0) e)).comp
        ((M κ).comp (phaseMul (colourEdges L k k) e)) :=
    fun κ hκ e => symbolHom_addTwoPiInt hSym hId pT pB hat.resp_periodic (hformed κ hκ) e
  have hdt : ∀ κ e, edgeCoboundarySymbol L k (addTwoPiInt κ e) =
      (quotHomInverse (phaseMul (colourFaces L k 0) e)).comp
        ((edgeCoboundarySymbol L k κ).comp (phaseMul (colourEdges L k 0) e)) :=
    fun κ e => symbolHom_addTwoPiInt hSym hId pB pP hd (hent.1 κ (mem_univ κ)) e
  have hinvB : ∀ e, IsInvertibleQuotHom
      (phaseMul (colourEdges L k 0) e : QuotHom _ _) :=
    ((hS _ _ pB pB).2.2.2.2.2.2.1 1 one_pos).1
  have hMt' : ∀ κ ∈ imStrip (2 * δ₀), ∀ e, M' (addTwoPiInt κ e) =
      (quotHomInverse (phaseMul (colourFaces L k 0) e)).comp
        ((M' κ).comp (phaseMul (colourEdges L k k) e)) := by
    intro κ hκ e
    refine LinearMap.ext fun f => ?_
    show edgeCoboundarySymbol L k (addTwoPiInt κ e) (M (addTwoPiInt κ e) f) = _
    rw [hMt κ hκ e, hdt κ e]
    simp only [LinearMap.comp_apply, M']
    rw [(hinvB e).apply_quotHomInverse]
  have hE : ∀ κ ∈ imStrip (2 * δ₀), ∀ c, (∀ c', ‖linearMapEntry (M κ) c' c‖ ≤ 4 * |C₀|) ∧
      ∀ c', ‖linearMapEntry (M' κ) c' c‖ ≤ 4 * |C₀| := by
    intro κ hκ c
    obtain ⟨e, he⟩ := exists_translate_inFundamentalStrip hκ
    have hpt := response_symbol_entries_le hW hC hδ hL hk hcurv he (indicatorAt c)
      (norm_indicatorAt_le c)
    refine ⟨fun c' => ?_, fun c' => ?_⟩
    · rw [← norm_linearMapEntry_conj_phase hS pT pB e (hMt κ hκ e) c' c]
      exact hpt.1 c'
    · rw [← norm_linearMapEntry_conj_phase hS pT pP e (hMt' κ hκ e) c' c]
      exact hpt.2 c'
  have : Finite (colourEdges L k 0).UnitQuot := pB.finite_quot
  have : Finite (colourEdges L k k).UnitQuot := pT.finite_quot
  have := Fintype.ofFinite (colourEdges L k 0).UnitQuot
  have := Fintype.ofFinite (colourEdges L k k).UnitQuot
  have hfun : SymbolCalculus.IsStripSymbol _ _ (2 * δ₀) M :=
    ⟨⟨O, hOopen, hsub, fun c' c => hsym.resp_holomorphic.2.2 (c', c)⟩,
      fun e => ⟨_, fun κ hκ => (hE κ hκ e.2).1 e.1⟩, fun e κ hκ => hMt κ hκ e⟩
  have hfun' : SymbolCalculus.IsStripSymbol _ _ (2 * δ₀) M' := by
    refine ⟨⟨O, hOopen, hsub, fun c' c => ?_⟩, fun e => ⟨_, fun κ hκ => (hE κ hκ e.2).2 e.1⟩,
      fun e κ hκ => hMt' κ hκ e⟩
    refine isHolomorphicIn_scalar_congr (u := fun κ => ∑ c'', linearMapEntry (edgeCoboundarySymbol L k κ) c' c'' *
      linearMapEntry (M κ) c'' c) ?_ ?_
    · exact isHolomorphicIn_scalar_sum Finset.univ hOopen fun c'' _ => isHolomorphicIn_scalar_mul
        (isHolomorphicIn_scalar_mono (symbolHom_entry_entire hQ pB pP hd hent c' c'') (subset_univ _) hOopen)
        (hsym.resp_holomorphic.2.2 (c'', c))
    · exact fun κ _ => linearMap_apply_eq_sum_entry (edgeCoboundarySymbol L k κ) _ c'
  have K := ((hS _ _ pT pB).2.2.2.2.2.2.1 (2 * δ₀) hυ).2.1 M hfun
  have K' := ((hS _ _ pT pP).2.2.2.2.2.2.1 (2 * δ₀) hυ).2.1 M' hfun'
  have h0 : (0 : Fin 4 → ℂ) ∈ imStrip (2 * δ₀) := fun μ => by
    simp only [Pi.zero_apply, Complex.zero_im, abs_zero]
    exact hυ.le
  constructor
  · have e₁ : responseKernel L k = matFunKernel _ _ M :=
      K.unique _ hat.resp_periodic
        ⟨fun κ hκ => hformed κ (K.realDualPoints_subset.1 hκ), fun κ _ => rfl⟩
    intro ι' ι
    rw [e₁]
    refine (K.norm_le ι' ι).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    refine csSup_le ⟨_, 0, h0, rfl⟩ ?_
    rintro _ ⟨κ, hκ, rfl⟩
    exact (hE κ hκ _).1 _
  · obtain ⟨_, Ch, δh, hCh, hδh, hbh⟩ := id hat.resp_periodic
    have facts := hSym.1 _ _ _ pB pP pT _ (responseKernel L k) δh hd (hdrate δh hδh)
      hat.resp_periodic ⟨hδh, Ch, hCh, hbh⟩
    have e₂ : compKernel (FullSpace.scaledEdgeCoboundaryKernel L k 0) (responseKernel L k) =
        matFunKernel _ _ M' := by
      refine K'.unique _ facts.compKernel_isPeriodicKernel.2
        ⟨fun κ hκ => (facts.quotSymbol_compKernel κ (realDualPoints_mem_strictImStrip hδh hκ)).1,
          fun κ hκ => ?_⟩
      refine LinearMap.ext fun f => ?_
      refine (symbolHom_eq_applyKernel (colourEdges L k k) (colourFaces L k 0) _ κ f).trans ?_
      refine (congrArg (fun K => applyKernel K f)
        (facts.quotSymbol_compKernel κ (realDualPoints_mem_strictImStrip hδh hκ)).2).trans ?_
      refine (applyKernel_compKernel _ _ f).trans ?_
      show _ = edgeCoboundarySymbol L k κ (M κ f)
      refine Eq.symm ((symbolHom_eq_applyKernel (colourEdges L k 0) (colourFaces L k 0) _ κ _).trans ?_)
      exact congrArg (applyKernel _)
        (symbolHom_eq_applyKernel (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ f)
    intro ι' ι
    rw [e₂]
    refine (K'.norm_le ι' ι).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    refine csSup_le ⟨_, 0, h0, rfl⟩ ?_
    rintro _ ⟨κ, hκ, rfl⟩
    exact (hE κ hκ _).2 _
end SymbolEstimates
section PeriodicPicture
open Tower.BackgroundFieldResponse (responseKernel)
open TorusMetric (l1NormVec euclidNormVec supNormVec torusProj)
private theorem euclidNormVec_le_l1NormVec (v : Fin 4 → ℝ) : euclidNormVec v ≤ l1NormVec v := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.euclidNormVec_le_l1NormVec <;> assumption
open Tower PeriodicOperators
open Tower.CriticalBranchResponse
open LocalKernels LocalKernels.Periodisation
private theorem l1NormVec_add_le (u v : Fin 4 → ℝ) : l1NormVec (u + v) ≤ l1NormVec u + l1NormVec v := by
  unfold l1NormVec
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun μ _ => abs_add_le _ _
private theorem l1NormVec_neg (u : Fin 4 → ℝ) : l1NormVec (-u) = l1NormVec u := by
  simp [l1NormVec]
private theorem l1NormVec_sub_le (u v : Fin 4 → ℝ) : l1NormVec (u - v) ≤ l1NormVec u + l1NormVec v := by
  rw [sub_eq_add_neg]
  exact (l1NormVec_add_le _ _).trans (by rw [l1NormVec_neg])
private theorem torusProj_add {S : ℝ} (u v : Fin 4 → ℝ) :
    torusProj S (u + v) = torusProj S u + torusProj S v := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
private theorem torusProj_sub {S : ℝ} (u v : Fin 4 → ℝ) :
    torusProj S (u - v) = torusProj S u - torusProj S v := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
private theorem torusProj_surj {S : ℝ} : Function.Surjective (torusProj S) := by apply _root_.YangMills.Construction.TestFunctions.torusProj_surjective <;> assumption
private theorem torusEuclidNorm_le {S : ℝ} {v : Fin 4 → ℝ} {x : TorusMetric.Torus4 S}
    (hv : torusProj S v = x) : TorusMetric.torusEuclidNorm x ≤ euclidNormVec v :=
  csInf_le ⟨0, by rintro _ ⟨w, _, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨v, hv, rfl⟩
private theorem torusSupNorm_le {S : ℝ} {v : Fin 4 → ℝ} {x : TorusMetric.Torus4 S}
    (hv : torusProj S v = x) : TorusMetric.torusSupNorm x ≤ supNormVec v := by
  refine csInf_le ⟨0, ?_⟩ ⟨v, hv, rfl⟩
  rintro _ ⟨w, _, rfl⟩
  exact (abs_nonneg (w 0)).trans (Finset.le_sup' (fun μ => |w μ|) (Finset.mem_univ 0))
private theorem exists_lift_l1NormVec_le_four {S : ℝ} {x : TorusMetric.Torus4 S}
    (hx : TorusMetric.torusSupNorm x < 1) : ∃ v, torusProj S v = x ∧ l1NormVec v ≤ 4 := by
  obtain ⟨v₀, hv₀⟩ := torusProj_surj x
  obtain ⟨_, ⟨v, hv, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (⟨_, v₀, hv₀, rfl⟩ :
    (supNormVec '' (torusProj S ⁻¹' {x})).Nonempty) hx
  refine ⟨v, hv, ?_⟩
  have h : ∀ μ, |v μ| ≤ 1 := fun μ =>
    (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ)).trans hlt.le
  calc l1NormVec v ≤ ∑ _μ : Fin 4, (1 : ℝ) := Finset.sum_le_sum fun μ _ => h μ
    _ = 4 := by simp
variable {L n k : ℕ}
private theorem meshSize_levelDepth_self (L k : ℕ) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
  simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
private theorem meshAt_self (L k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
private def integerVertex (L k : ℕ) (z : Fin 4 → ℤ) : FullSpace.Vertex L k k :=
  ⟨fun μ => (z μ : ℝ) * meshAt L k k, z, fun _ => rfl⟩
private theorem zsmul_unitStep_apply (L n k : ℕ) (z : ℤ) (μ ρ : Fin 4) :
    (((z • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ : PeriodicLattice.Site L n _) :
      PeriodicLattice.FourTorus L n)) ρ =
    if ρ = μ then (((z : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) else 0 := by
  have e : (((z • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ : PeriodicLattice.Site L n _) :
      PeriodicLattice.FourTorus L n)) =
      z • PeriodicLattice.pointOnAxis L n μ (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k)) := rfl
  rw [e, meshSize_levelDepth_self, Pi.smul_apply, PeriodicLattice.pointOnAxis]
  by_cases h : ρ = μ
  · subst h
    simp only [Pi.single_eq_same, if_true]
    rw [← QuotientAddGroup.mk_zsmul]
    simp
  · simp [h]
private theorem projVertex_integerVertex (L n k : ℕ) (z : Fin 4 → ℤ) :
    FullSpace.projVertex L n k k (integerVertex L k z) = cellOfCoords L n k z := by
  refine Subtype.ext ?_
  funext ρ
  show ((((z ρ : ℝ) * meshAt L k k : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) = _
  have e : ((cellOfCoords L n k z : PeriodicLattice.Site L n _) : PeriodicLattice.FourTorus L n) =
      ∑ μ, (((z μ • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ :
        PeriodicLattice.Site L n _) : PeriodicLattice.FourTorus L n)) := by
    simp only [cellOfCoords, PeriodicLattice.offsetSite, zero_add]
    exact AddSubmonoidClass.coe_finsetSum _ _
  rw [e, Finset.sum_apply, Finset.sum_eq_single ρ]
  · rw [zsmul_unitStep_apply, if_pos rfl, meshAt_self, mul_one]
  · intro μ _ h
    rw [zsmul_unitStep_apply, if_neg (Ne.symm h)]
  · simp
private theorem exists_refinedBlock_mem (hc : ProjCellsClassified L n k 0) (x : Tower.Vertex L n k 0) :
    ∃ y : Tower.Vertex L n k k, (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y := by
  obtain ⟨x₀, hx₀⟩ := (hc .vertex).1 x
  let x' : FullSpace.Vertex L k 0 := x₀
  have hxc : torusProj (PeriodicLattice.torusSide L n) (x' : InfiniteLattice.AmbientSpace) =
      (x : PeriodicLattice.FourTorus L n) := by
    rw [← hx₀]
    rfl
  let r : Fin 4 → ℤ := fun μ => round ((x' : InfiniteLattice.AmbientSpace) μ)
  refine ⟨cellOfCoords L n k r, ?_, ?_⟩
  · show TorusMetric.torusSupNorm _ ≤ PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) / 2
    rw [meshSize_levelDepth_self]
    have hv : torusProj (PeriodicLattice.torusSide L n)
        ((x' : InfiniteLattice.AmbientSpace) - (integerVertex L k r : InfiniteLattice.AmbientSpace)) =
        (x : PeriodicLattice.FourTorus L n) -
          ((cellOfCoords L n k r : Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) := by
      rw [torusProj_sub, hxc, ← projVertex_integerVertex]
      rfl
    refine (torusSupNorm_le hv).trans ?_
    refine Finset.sup'_le _ _ fun μ _ => ?_
    have := abs_sub_round ((x' : InfiniteLattice.AmbientSpace) μ)
    simpa [integerVertex, meshAt_self, r] using this
  · have e : PeriodicLattice.levelDepth k k + (k : ℤ) = PeriodicLattice.levelDepth k 0 := by
      simp [PeriodicLattice.levelDepth]
    show _ ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k + (k : ℤ))
    rw [e]
    exact x.2
private theorem torusProj_neg {S : ℝ} (u : Fin 4 → ℝ) : torusProj S (-u) = -torusProj S u := by
  funext μ
  simp [torusProj]
private theorem cellDist_fineVertexCell_le (hc : ProjCellsClassified L n k 0) (x : Tower.Vertex L n k 0)
    (z : Fin 4 → ℤ) {v : Fin 4 → ℝ} (hv : torusProj (PeriodicLattice.torusSide L n) v =
      ((cellOfCoords L n k z : Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) -
        (x : PeriodicLattice.FourTorus L n)) :
    cellDist (fineVertexCell x) (cellOfCoords L n k z) ≤ 4 + l1NormVec v := by
  have hm : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k (fineVertexCell x) :=
    Classical.epsilon_spec (exists_refinedBlock_mem hc x)
  have h₁ : TorusMetric.torusSupNorm ((x : PeriodicLattice.FourTorus L n) -
      ((fineVertexCell x : Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n)) ≤
      PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) / 2 := hm.1
  rw [meshSize_levelDepth_self] at h₁
  obtain ⟨u, hu, hu4⟩ := exists_lift_l1NormVec_le_four (lt_of_le_of_lt h₁ (by norm_num))
  have hlift : torusProj (PeriodicLattice.torusSide L n) (-u - v) =
      ((fineVertexCell x : Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) -
        ((cellOfCoords L n k z : Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) := by
    rw [torusProj_sub, torusProj_neg, hu, hv]
    abel
  refine (torusEuclidNorm_le hlift).trans ((euclidNormVec_le_l1NormVec _).trans ?_)
  refine (l1NormVec_sub_le _ _).trans ?_
  rw [l1NormVec_neg]
  linarith
private theorem projPositiveEdge_shiftEdge {j : ℕ} (hc : ProjCellsClassified L n k j)
    (b : PeriodicOperators.PosEdge L k j) (m : Fin 4 → ℤ) :
    projPositiveEdge L n k j (PeriodicOperators.shiftEdge (periodSide L n • m) b) =
      projPositiveEdge L n k j b :=
  (((hc .edge).2 b (PeriodicOperators.shiftEdge (periodSide L n • m) b)).2 ⟨m, rfl⟩).symm
private theorem mkQuot_periodSide_eq_iff {j : ℕ} (hc : ProjCellsClassified L n k j)
    (ι ι' : (colourEdges L k j).Carrier) :
    (colourEdges L k j).mkQuot (periodSide L n) ι =
        (colourEdges L k j).mkQuot (periodSide L n) ι' ↔
      ι.1 = ι'.1 ∧ projPositiveEdge L n k j ι.2 = projPositiveEdge L n k j ι'.2 := by
  constructor
  · intro e
    let f : (colourEdges L k j).QuotMod (periodSide L n) →
        Fin 3 × Tower.PositiveEdge L n k j :=
      Quot.lift (fun ι => (ι.1, projPositiveEdge L n k j ι.2)) (by
        rintro ι _ ⟨m, rfl⟩
        exact Prod.ext rfl (projPositiveEdge_shiftEdge hc ι.2 m).symm)
    have h : (ι.1, projPositiveEdge L n k j ι.2) = (ι'.1, projPositiveEdge L n k j ι'.2) :=
      congrArg f e
    exact ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨m, hm⟩ := ((hc .edge).2 ι.2 ι'.2).1 h₂
    exact Quot.sound ⟨m, Prod.ext h₁.symm hm⟩
private theorem toPauliCoeffs_periodicImage_eq {T : (colourEdges L k 0).Carrier → (colourEdges L k k).Carrier → ℂ}
    (hdep : ∀ ι₁' ι₂' ι₁ ι₂,
      (colourEdges L k 0).mkQuot (periodSide L n) ι₁' =
          (colourEdges L k 0).mkQuot (periodSide L n) ι₂' →
        (colourEdges L k k).mkQuot (periodSide L n) ι₁ =
          (colourEdges L k k).mkQuot (periodSide L n) ι₂ →
        periodization (colourEdges L k k) (colourEdges L k 0) T (periodSide L n) ι₁' ι₁ =
          periodization (colourEdges L k k) (colourEdges L k 0) T (periodSide L n) ι₂' ι₂)
    {B : Tower.Edge L n k k → ComplexMatrix2} {X : Tower.edgeFormSpace L n k 0}
    (h : IsPeriodicImage L n k k 0 T B X)
    (ι₀ : (colourEdges L k k).Carrier)
    (hB : ∀ ι : (colourEdges L k k).Carrier,
      toPauliCoeffs (restrictToPositiveEdges B) (ι.1, projPositiveEdge L n k k ι.2) =
        open Classical in
        if (colourEdges L k k).mkQuot (periodSide L n) ι =
          (colourEdges L k k).mkQuot (periodSide L n) ι₀ then 1 else 0)
    (ι' : (colourEdges L k 0).Carrier) :
    toPauliCoeffs (restrictToPositiveEdges (X : Tower.Edge L n k 0 → ComplexMatrix2))
        (ι'.1, projPositiveEdge L n k 0 ι'.2) =
      periodization (colourEdges L k k) (colourEdges L k 0) T (periodSide L n) ι' ι₀ := by
  classical
  obtain ⟨g, a, b⟩ := h
  have hg : ∀ c, c ≠ (colourEdges L k k).mkQuot (periodSide L n) ι₀ → g c = 0 := by
    intro c hc
    induction c using Quot.ind with
    | mk ι =>
      exact ((a ι).trans (hB ι)).trans (if_neg hc)
  have hg₀ : g ((colourEdges L k k).mkQuot (periodSide L n) ι₀) = 1 :=
    ((a ι₀).trans (hB ι₀)).trans (if_pos rfl)
  have hm : periodicMatrix (colourEdges L k k) (colourEdges L k 0) T (periodSide L n)
      ((colourEdges L k 0).mkQuot (periodSide L n) ι')
      ((colourEdges L k k).mkQuot (periodSide L n) ι₀) =
      periodization (colourEdges L k k) (colourEdges L k 0) T (periodSide L n) ι' ι₀ :=
    (Classical.epsilon_spec (p := fun w => ∀ ι₁' ι₁,
      (colourEdges L k 0).mkQuot (periodSide L n) ι₁' =
          (colourEdges L k 0).mkQuot (periodSide L n) ι' →
        (colourEdges L k k).mkQuot (periodSide L n) ι₁ =
          (colourEdges L k k).mkQuot (periodSide L n) ι₀ →
      periodization (colourEdges L k k) (colourEdges L k 0) T (periodSide L n) ι₁' ι₁ = w)
      ⟨_, fun ι₁' ι₁ h₁ h₂ => hdep ι₁' ι' ι₁ ι₀ h₁ h₂⟩ ι' ι₀ rfl rfl).symm
  refine (b ι').symm.trans ?_
  show ∑' c, periodicMatrix (colourEdges L k k) (colourEdges L k 0) T (periodSide L n)
      ((colourEdges L k 0).mkQuot (periodSide L n) ι') c * g c = _
  rw [tsum_eq_single ((colourEdges L k k).mkQuot (periodSide L n) ι₀) fun c hc => by
    rw [hg c hc, mul_zero]]
  rw [hg₀, mul_one, hm]
private def thirdColourIndexAt (L k : ℕ) (z : Fin 4 → ℤ) : (colourEdges L k k).Carrier :=
  (2, PlaneWaveCalculus.posEdgeAt L k k (integerVertex L k z) SlopeCoefficient.secondAxis)
private theorem projPositiveEdge_thirdColourIndexAt (hb : ProjEdgesCompatible L n k k) (z : Fin 4 → ℤ) :
    (projPositiveEdge L n k k (thirdColourIndexAt L k z).2).1 =
      PeriodicLattice.Bond.forwardFrom (cellOfCoords L n k z) SlopeCoefficient.secondAxis := by
  rw [hb.2.1 (thirdColourIndexAt L k z).2]
  obtain ⟨h₁, h₂⟩ := hb.1 (thirdColourIndexAt L k z).2.1
  refine PeriodicLattice.Bond.ext ?_ ?_
  · rw [h₁]
    exact projVertex_integerVertex L n k z
  · rw [h₂]
    refine Subtype.ext ?_
    funext ρ
    have e₁ := congrFun (congrArg Subtype.val (projVertex_integerVertex L n k z)) ρ
    show (((integerVertex L k z : InfiniteLattice.AmbientSpace) ρ +
        (Pi.single SlopeCoefficient.secondAxis (meshAt L k k) : InfiniteLattice.AmbientSpace) ρ : ℝ) :
          AddCircle (PeriodicLattice.torusSide L n)) =
      ((cellOfCoords L n k z : Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) ρ +
        PeriodicLattice.pointOnAxis L n SlopeCoefficient.secondAxis
          (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k)) ρ
    rw [AddCircle.coe_add, meshSize_levelDepth_self, ← e₁]
    refine congrArg₂ (· + ·) rfl ?_
    by_cases h : ρ = SlopeCoefficient.secondAxis
    · subst h
      simp [PeriodicLattice.pointOnAxis, meshAt_self]
    · simp [PeriodicLattice.pointOnAxis, h]
private theorem pauliCoeff_pauliZ (a : Fin 3) :
    pauliCoeff a (ComplexMatrix2.pauliFamily 2) = if a = 2 then 1 else 0 := by apply _root_.YangMills.Construction.Tower.MassiveOperators.EdgeFormQuotIndicator.pauliCoeff_pauliZ <;> assumption
private theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem toPauliCoeffs_pauliUnitForm (hc : ProjCellsClassified L n k k)
    (hb : ProjEdgesCompatible L n k k) (z : Fin 4 → ℤ) (ι : (colourEdges L k k).Carrier) :
    toPauliCoeffs (restrictToPositiveEdges (pauliUnitForm L n k z))
        (ι.1, projPositiveEdge L n k k ι.2) =
      open Classical in
      if (colourEdges L k k).mkQuot (periodSide L n) ι =
        (colourEdges L k k).mkQuot (periodSide L n) (thirdColourIndexAt L k z) then 1 else 0 := by
  classical
  have hpos := (projPositiveEdge L n k k ι.2).2
  show pauliCoeff ι.1 (pauliUnitForm L n k z (projPositiveEdge L n k k ι.2).1) = _
  simp only [pauliUnitForm, Tower.extendOddly, if_pos hpos]
  have htop := projPositiveEdge_thirdColourIndexAt hb z
  by_cases h : (projPositiveEdge L n k k ι.2).1 =
      PeriodicLattice.Bond.forwardFrom (PeriodicLattice.offsetSite 0 z) SlopeCoefficient.secondAxis
  · rw [if_pos h, pauliCoeff_pauliZ]
    have hq : projPositiveEdge L n k k ι.2 = projPositiveEdge L n k k (thirdColourIndexAt L k z).2 :=
      Subtype.ext (h.trans htop.symm)
    by_cases ha : ι.1 = 2
    · rw [if_pos ha, if_pos ((mkQuot_periodSide_eq_iff hc ι (thirdColourIndexAt L k z)).2 ⟨ha, hq⟩)]
    · rw [if_neg ha, if_neg fun e => ha ((mkQuot_periodSide_eq_iff hc ι (thirdColourIndexAt L k z)).1 e).1]
  · rw [if_neg h, pauliCoeff_zero, if_neg]
    intro e
    exact h ((congrArg Subtype.val ((mkQuot_periodSide_eq_iff hc ι (thirdColourIndexAt L k z)).1 e).2).trans htop)
private theorem pauliUnitForm_mem_edgeFormSpace (hL : 2 ≤ L) (hn : 0 < n) (z : Fin 4 → ℤ) :
    pauliUnitForm L n k z ∈ Tower.edgeFormSpace L n k k := by apply _root_.YangMills.SharedProofs.p46171 <;> assumption
end PeriodicPicture
section Conclusion
open Tower PeriodicOperators
open Tower.BackgroundFieldResponse (responseKernel)
open Tower.CriticalBranchResponse
open TorusMetric (l1NormVec euclidNormVec supNormVec torusProj)
open LocalKernels LocalKernels.Periodisation
variable {L n k : ℕ}
private abbrev faceEdgeOne (P : FullSpace.Face L k 0) : PeriodicOperators.PosEdge L k 0 :=
  PlaneWaveCalculus.posEdgeAt L k 0 P.corner P.lowAxis
private abbrev faceEdgeTwo (P : FullSpace.Face L k 0) : PeriodicOperators.PosEdge L k 0 :=
  PlaneWaveCalculus.posEdgeAt L k 0
    (P.corner + InfiniteLattice.axisStep (meshAt L k 0) P.lowAxis) P.highAxis
private abbrev faceEdgeThree (P : FullSpace.Face L k 0) : PeriodicOperators.PosEdge L k 0 :=
  PlaneWaveCalculus.posEdgeAt L k 0
    (P.corner + InfiniteLattice.axisStep (meshAt L k 0) P.highAxis) P.lowAxis
private abbrev faceEdgeFour (P : FullSpace.Face L k 0) : PeriodicOperators.PosEdge L k 0 :=
  PlaneWaveCalculus.posEdgeAt L k 0 P.corner P.highAxis
private def scaledFaceCombination (F : PeriodicOperators.PosEdge L k 0 → ℂ)
    (P : FullSpace.Face L k 0) : ℂ :=
  (((meshAt L k 0)⁻¹ : ℝ) : ℂ) *
    (F (faceEdgeOne P) + F (faceEdgeTwo P) - F (faceEdgeThree P) - F (faceEdgeFour P))
private theorem real_smul_four_pauli_sums (c : ℂ) (x₁ x₂ x₃ x₄ : Fin 3 → ℂ) (r : ℝ) (hr : (r : ℂ) = c) :
    r • (∑ a, x₁ a • ComplexMatrix2.pauliFamily a + ∑ a, x₂ a • ComplexMatrix2.pauliFamily a -
      ∑ a, x₃ a • ComplexMatrix2.pauliFamily a - ∑ a, x₄ a • ComplexMatrix2.pauliFamily a) =
    ∑ a, (c * (x₁ a + x₂ a - x₃ a - x₄ a)) • ComplexMatrix2.pauliFamily a := by
  rw [← Complex.coe_smul, hr, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_smul, sub_smul, sub_smul, add_smul]
private theorem compKernel_scaledEdgeCoboundaryKernel_apply (hFO : FreeOperators.FreeOperatorsArePeriodic)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {J : Type}
    (T : (colourEdges L k 0).Carrier → J → ℂ) (a : Fin 3) (P : FullSpace.Face L k 0) (ι : J) :
    compKernel (FullSpace.scaledEdgeCoboundaryKernel L k 0) T (a, P) ι =
      scaledFaceCombination (fun β => T (a, β) ι) P := by
  classical
  have hk3 := (hFO.2 L hL k hk).1.edgeCoboundary 0 (Nat.zero_le k)
  have e := congrFun (hk3.applyKernel_eq fun ι'' => T ι'' ι) (a, P)
  refine e.trans ?_
  set W := (FullSpace.edgePauliCoordinates L k 0).ofCoeffs (fun ι'' => T ι'' ι) with hW
  show pauliCoeff a (FullSpace.scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P) = _
  have hval : ∀ β : PeriodicOperators.PosEdge L k 0, W β.1 =
      ∑ c, T (c, β) ι • ComplexMatrix2.pauliFamily c := by
    intro β
    simp only [hW, FullSpace.edgePauliCoordinates, FullSpace.extendOddly, if_pos β.2, dif_pos β.2, ofPauliCoeffs]
  have e₂ : FullSpace.scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P =
      ∑ c, scaledFaceCombination (fun β => T (c, β) ι) P • ComplexMatrix2.pauliFamily c := by
    show (meshAt L k 0)⁻¹ • (W (faceEdgeOne P).1 + W (faceEdgeTwo P).1 - W (faceEdgeThree P).1 -
      W (faceEdgeFour P).1) = _
    rw [hval, hval, hval, hval]
    exact real_smul_four_pauli_sums _ _ _ _ _ _ rfl
  rw [e₂, pauliCoeff_combination]
private theorem torusProj_castVec_periods (L n : ℕ) (m : Fin 4 → ℤ) :
    torusProj (PeriodicLattice.torusSide L n) (castVec (periodSide L n • m)) = 0 := by
  funext μ
  show (((((periodSide L n • m) μ : ℤ) : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) = 0
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨m μ, ?_⟩
  simp [periodSide, PeriodicLattice.torusSide, mul_comm]
private theorem cellDist_le_translates (hc : ProjCellsClassified L n k 0)
    (pT : IsPeriodic (colourEdges L k k)) (z : Fin 4 → ℤ) (x : FullSpace.Vertex L k 0)
    (m : Fin 4 → ℤ) :
    cellDist (fineVertexCell (FullSpace.projVertex L n k 0 x)) (cellOfCoords L n k z) ≤
      4 + l1NormVec ((colourEdges L k k).pos
        ((colourEdges L k k).translate (periodSide L n • m) (thirdColourIndexAt L k z)) -
          (x : InfiniteLattice.AmbientSpace)) := by
  refine cellDist_fineVertexCell_le hc _ z ?_
  rw [pT.pos_translate, torusProj_sub, torusProj_add, torusProj_castVec_periods, add_zero]
  show torusProj (PeriodicLattice.torusSide L n) (integerVertex L k z : InfiniteLattice.AmbientSpace) - _ = _
  rw [← projVertex_integerVertex]
  rfl
private theorem edgeForm_at_projPositiveEdge (X : Tower.edgeFormSpace L n k 0)
    (β : PeriodicOperators.PosEdge L k 0) :
    (X : Tower.Edge L n k 0 → ComplexMatrix2) (projPositiveEdge L n k 0 β).1 =
      ∑ a, toPauliCoeffs (restrictToPositiveEdges (X : Tower.Edge L n k 0 → ComplexMatrix2))
        (a, projPositiveEdge L n k 0 β) • ComplexMatrix2.pauliFamily a :=
  (sum_pauliCoeff_smul (X.2.1 _ (projPositiveEdge L n k 0 β).2).2).symm
private theorem operatorNorm_pauli_combination_le (x : Fin 3 → ℂ) {K : ℝ} (hx : ∀ a, ‖x a‖ ≤ K) :
    ComplexMatrix2.operatorNorm (∑ a, x a • ComplexMatrix2.pauliFamily a) ≤
      (∑ a, ‖ComplexMatrix2.pauliFamily a‖) * K := by
  calc ComplexMatrix2.operatorNorm (∑ a, x a • ComplexMatrix2.pauliFamily a)
      ≤ ∑ a, ‖x a • ComplexMatrix2.pauliFamily a‖ := norm_sum_le _ _
    _ = ∑ a, ‖x a‖ * ‖ComplexMatrix2.pauliFamily a‖ := by simp only [norm_smul]
    _ ≤ ∑ a, K * ‖ComplexMatrix2.pauliFamily a‖ :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hx a) (norm_nonneg _)
    _ = (∑ a, ‖ComplexMatrix2.pauliFamily a‖) * K := by rw [← Finset.mul_sum, mul_comm]
private theorem norm_tsum_translates_thirdColour_le {I' : PeriodicData}
    {T : I'.Carrier → (colourEdges L k k).Carrier → ℂ}
    (pT : IsPeriodic (colourEdges L k k)) {C₁ δ₀ : ℝ} (hC₁ : 0 ≤ C₁) (hδ₀ : 0 < δ₀)
    (hT : ∀ ι' ι, ‖T ι' ι‖ ≤ C₁ * Real.exp (-(2 * δ₀) *
      l1NormVec ((colourEdges L k k).pos ι - I'.pos ι')))
    (hs : 0 < periodSide L n) (ι' : I'.Carrier) (z : Fin 4 → ℤ) {d : ℝ}
    (hd : ∀ m : Fin 4 → ℤ, d ≤ 5 + l1NormVec ((colourEdges L k k).pos
      ((colourEdges L k k).translate (periodSide L n • m) (thirdColourIndexAt L k z)) - I'.pos ι')) :
    ‖∑' m : Fin 4 → ℤ, T ι' ((colourEdges L k k).translate (periodSide L n • m)
        (thirdColourIndexAt L k z))‖ ≤
      C₁ * Real.exp (δ₀ * 5) * geometricLineBound δ₀ ^ 4 * Real.exp (-(δ₀ * d)) := by
  have h := norm_tsum_periodic_translates_le (colourEdges L k k) I' pT hC₁
    (by positivity : 0 < 2 * δ₀) hT hs ι' (thirdColourIndexAt L k z) hd
  have e : 2 * δ₀ / 2 = δ₀ := by ring
  rwa [e] at h
private theorem abs_meshAt_bottom_le (hL : 1 ≤ L) : |meshAt L k 0| ≤ 1 := by
  have h₀ : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have e : meshAt L k 0 = ((L : ℝ) ^ k)⁻¹ := by
    simp [meshAt, zpow_neg]
  rw [e, abs_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ h₀)
private theorem l1NormVec_terminal_sub_initial_le (hL : 1 ≤ L) (β : PeriodicOperators.PosEdge L k 0) :
    l1NormVec ((β.1.terminal : InfiniteLattice.AmbientSpace) -
      (β.1.initial : InfiniteLattice.AmbientSpace)) ≤ 1 := by
  obtain ⟨μ, hμ⟩ := β.2
  have e : (β.1.terminal : InfiniteLattice.AmbientSpace) - (β.1.initial : InfiniteLattice.AmbientSpace) =
      Pi.single μ (meshAt L k 0) := congrArg Subtype.val hμ
  rw [e]
  have e₂ : l1NormVec (Pi.single μ (meshAt L k 0) : Fin 4 → ℝ) = |meshAt L k 0| := by
    unfold l1NormVec
    rw [Finset.sum_eq_single μ]
    · simp
    · intro ν _ h
      simp [Pi.single_eq_of_ne h]
    · simp
  rw [e₂]
  exact abs_meshAt_bottom_le hL
private theorem scaledFaceCombination_tsum {f : PeriodicOperators.PosEdge L k 0 → (Fin 4 → ℤ) → ℂ}
    (hf : ∀ β, Summable (f β)) (P : FullSpace.Face L k 0) :
    scaledFaceCombination (fun β => ∑' m, f β m) P =
      ∑' m, scaledFaceCombination (fun β => f β m) P := by
  have s₁ := hf (faceEdgeOne P)
  have s₂ := hf (faceEdgeTwo P)
  have s₃ := hf (faceEdgeThree P)
  have s₄ := hf (faceEdgeFour P)
  unfold scaledFaceCombination
  rw [tsum_mul_left]
  congr 1
  show _ = ∑' x, (f (faceEdgeOne P) x + f (faceEdgeTwo P) x - f (faceEdgeThree P) x - f (faceEdgeFour P) x)
  rw [((s₁.add s₂).sub s₃).tsum_sub s₄, (s₁.add s₂).tsum_sub s₃, s₁.tsum_add s₂]
private theorem periodicResponse_pauliUnitForm_bounds (hFO : FreeOperators.FreeOperatorsArePeriodic)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hn : 0 < n) (hc : ProjCellsClassified L n k 0) (hb : ProjEdgesCompatible L n k 0)
    (pT : IsPeriodic (colourEdges L k k)) {C₁ δ₀ : ℝ} (hC₁ : 0 ≤ C₁) (hδ₀ : 0 < δ₀)
    (hh : ∀ ι' ι, ‖responseKernel L k ι' ι‖ ≤ C₁ * Real.exp (-(2 * δ₀) *
      l1NormVec ((colourEdges L k k).pos ι - (colourEdges L k 0).pos ι')))
    (hD : ∀ ι' ι, ‖compKernel (FullSpace.scaledEdgeCoboundaryKernel L k 0) (responseKernel L k) ι' ι‖ ≤
      C₁ * Real.exp (-(2 * δ₀) *
        l1NormVec ((colourEdges L k k).pos ι - (colourFaces L k 0).pos ι')))
    (hcol : PlaneWaveCalculus.IsRealColourTrivial (responseKernel L k))
    (hformed : ∀ ι' ι, PeriodizationSummableAt (colourEdges L k k) (colourEdges L k 0)
      (responseKernel L k) (periodSide L n) ι' ι)
    (z : Fin 4 → ℤ)
    (hA : ∀ ι' : (colourEdges L k 0).Carrier,
      toPauliCoeffs (restrictToPositiveEdges
          (periodicResponse L n k (pauliUnitForm L n k z) : Tower.Edge L n k 0 → ComplexMatrix2))
          (ι'.1, projPositiveEdge L n k 0 ι'.2) =
        periodization (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) (periodSide L n) ι'
          (thirdColourIndexAt L k z)) :
    (∀ b : Tower.Edge L n k 0,
      ComplexMatrix2.operatorNorm
          ((periodicResponse L n k (pauliUnitForm L n k z) : Tower.Edge L n k 0 → ComplexMatrix2) b) ≤
        (∑ a, ‖ComplexMatrix2.pauliFamily a‖) * (C₁ * Real.exp (δ₀ * 5) * geometricLineBound δ₀ ^ 4 *
          Real.exp (-(δ₀ * cellDist (fineVertexCell b.source) (cellOfCoords L n k z))))) ∧
    (∀ p : Tower.Face L n k 0,
      ComplexMatrix2.operatorNorm (Tower.scaledEdgeCoboundary
          (periodicResponse L n k (pauliUnitForm L n k z) : Tower.Edge L n k 0 → ComplexMatrix2) p) ≤
        (∑ a, ‖ComplexMatrix2.pauliFamily a‖) * (C₁ * Real.exp (δ₀ * 5) * geometricLineBound δ₀ ^ 4 *
          Real.exp (-(δ₀ * cellDist (fineVertexCell p.origin) (cellOfCoords L n k z))))) ∧
    ∀ b : Tower.Edge L n k 0, ∃ x : ℝ,
      (periodicResponse L n k (pauliUnitForm L n k z) : Tower.Edge L n k 0 → ComplexMatrix2) b =
        (x : ℂ) • ComplexMatrix2.pauliFamily 2 := by
  classical
  set X := periodicResponse L n k (pauliUnitForm L n k z) with hX
  have hL1 : 1 ≤ L := by have := hL.2; omega
  have hL2 : 2 ≤ L := by have := hL.2; omega
  have hs : 0 < periodSide L n := by
    have : 0 < L ^ n := pow_pos (by omega) n
    simp only [periodSide]
    omega
  have hj : -(n : ℤ) < PeriodicLattice.levelDepth k 0 := by simp [PeriodicLattice.levelDepth]; omega
  have hrr : ∀ b : Tower.Edge L n k 0, b.opposite.opposite = b :=
    fun b => PeriodicLattice.Bond.ext rfl rfl
  have hneg : ∀ b : Tower.Edge L n k 0, (X : Tower.Edge L n k 0 → ComplexMatrix2) b =
      -(X : Tower.Edge L n k 0 → ComplexMatrix2) b.opposite := by
    intro b
    have := X.2.2 b.opposite
    rwa [hrr] at this
  have hrev : ∀ b : Tower.Edge L n k 0, ¬b.IsPositivelyOriented → b.opposite.IsPositivelyOriented := by
    intro b h
    rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2 hj b with ⟨h', -⟩ | ⟨h', -⟩
    · exact absurd h' h
    · exact h'
  have hcoef : ∀ (a : Fin 3) (β : PeriodicOperators.PosEdge L k 0) {d : ℝ},
      (∀ m : Fin 4 → ℤ, d ≤ 5 + l1NormVec ((colourEdges L k k).pos
        ((colourEdges L k k).translate (periodSide L n • m) (thirdColourIndexAt L k z)) -
          (β.1.initial : InfiniteLattice.AmbientSpace))) →
      ‖toPauliCoeffs (restrictToPositiveEdges (X : Tower.Edge L n k 0 → ComplexMatrix2))
        (a, projPositiveEdge L n k 0 β)‖ ≤
        C₁ * Real.exp (δ₀ * 5) * geometricLineBound δ₀ ^ 4 * Real.exp (-(δ₀ * d)) := by
    intro a β d hd
    have e : toPauliCoeffs (restrictToPositiveEdges (X : Tower.Edge L n k 0 → ComplexMatrix2))
        (a, projPositiveEdge L n k 0 β) = _ := hA (a, β)
    rw [e]
    exact norm_tsum_translates_thirdColour_le pT hC₁ hδ₀ hh hs (a, β) z hd
  have hlift : ∀ b : Tower.Edge L n k 0, b.IsPositivelyOriented →
      ∃ β : PeriodicOperators.PosEdge L k 0, (projPositiveEdge L n k 0 β).1 = b := by
    intro b hpos
    obtain ⟨β, hβ⟩ := (hc .edge).1 ⟨b, hpos⟩
    exact ⟨β, congrArg Subtype.val hβ⟩
  have hbond : ∀ β : PeriodicOperators.PosEdge L k 0,
      (projPositiveEdge L n k 0 β).1 = FullSpace.projEdge L n k 0 β.1 := hb.2.1
  refine ⟨fun b => ?_, fun p => ?_, fun b => ?_⟩
  · by_cases hpos : b.IsPositivelyOriented
    · obtain ⟨β, rfl⟩ := hlift b hpos
      have ht : (projPositiveEdge L n k 0 β).1.source = FullSpace.projVertex L n k 0 β.1.initial := by
        rw [hbond β]
        exact (hb.1 β.1).1
      rw [ht, edgeForm_at_projPositiveEdge]
      refine operatorNorm_pauli_combination_le _ fun a => hcoef a β fun m => ?_
      have := cellDist_le_translates hc pT z β.1.initial m
      linarith
    · obtain ⟨β, hβ⟩ := hlift b.opposite (hrev b hpos)
      have ht : b.source = FullSpace.projVertex L n k 0 β.1.terminal := by
        have e : b.source = (projPositiveEdge L n k 0 β).1.target := by rw [hβ]; rfl
        rw [e, hbond β]
        exact (hb.1 β.1).2
      rw [hneg b, ← hβ, ht, ComplexMatrix2.operatorNorm, norm_neg, edgeForm_at_projPositiveEdge]
      refine operatorNorm_pauli_combination_le _ fun a => hcoef a β fun m => ?_
      have h₁ := cellDist_le_translates hc pT z β.1.terminal m
      have h₂ := l1NormVec_terminal_sub_initial_le hL1 β
      have e : (colourEdges L k k).pos
            ((colourEdges L k k).translate (periodSide L n • m) (thirdColourIndexAt L k z)) -
            (β.1.terminal : InfiniteLattice.AmbientSpace) =
          ((colourEdges L k k).pos
            ((colourEdges L k k).translate (periodSide L n • m) (thirdColourIndexAt L k z)) -
            (β.1.initial : InfiniteLattice.AmbientSpace)) -
          ((β.1.terminal : InfiniteLattice.AmbientSpace) -
            (β.1.initial : InfiniteLattice.AmbientSpace)) := by abel
      have h₃ := l1NormVec_sub_le ((colourEdges L k k).pos
            ((colourEdges L k k).translate (periodSide L n • m) (thirdColourIndexAt L k z)) -
            (β.1.initial : InfiniteLattice.AmbientSpace))
          ((β.1.terminal : InfiniteLattice.AmbientSpace) - (β.1.initial : InfiniteLattice.AmbientSpace))
      rw [← e] at h₃
      linarith
  · obtain ⟨P₀, rfl⟩ := (hc .face).1 p
    let P : FullSpace.Face L k 0 := P₀
    have h4 := hb.2.2 P
    simp only [Tower.faceEdges, FullSpace.faceEdges, List.map_cons, List.map_nil, List.cons.injEq,
      and_true] at h4
    obtain ⟨e₁, e₂, e₃, e₄⟩ := h4
    have hval : ∀ β : PeriodicOperators.PosEdge L k 0,
        (X : Tower.Edge L n k 0 → ComplexMatrix2) (FullSpace.projEdge L n k 0 β.1) =
          ∑ a, toPauliCoeffs (restrictToPositiveEdges (X : Tower.Edge L n k 0 → ComplexMatrix2))
            (a, projPositiveEdge L n k 0 β) • ComplexMatrix2.pauliFamily a := by
      intro β
      rw [← hbond β]
      exact edgeForm_at_projPositiveEdge X β
    have v₁ := (congrArg (X : Tower.Edge L n k 0 → ComplexMatrix2) e₁).trans (hval (faceEdgeOne P))
    have v₂ := (congrArg (X : Tower.Edge L n k 0 → ComplexMatrix2) e₂).trans (hval (faceEdgeTwo P))
    have v₃ := (congrArg (X : Tower.Edge L n k 0 → ComplexMatrix2) e₃).trans (hval (faceEdgeThree P))
    have v₄ := (congrArg (X : Tower.Edge L n k 0 → ComplexMatrix2) e₄).trans (hval (faceEdgeFour P))
    have hsum : Tower.scaledEdgeCoboundary (X : Tower.Edge L n k 0 → ComplexMatrix2)
          (FullSpace.projFace L n k 0 P) =
        ∑ a, scaledFaceCombination (fun β => toPauliCoeffs
          (restrictToPositiveEdges (X : Tower.Edge L n k 0 → ComplexMatrix2))
            (a, projPositiveEdge L n k 0 β)) P • ComplexMatrix2.pauliFamily a := by
      have hd : Tower.edgeCoboundary (X : Tower.Edge L n k 0 → ComplexMatrix2)
          (FullSpace.projFace L n k 0 P) =
          _ := congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· + ·) v₁ v₂) v₃) v₄
      show (meshAt L k 0)⁻¹ • Tower.edgeCoboundary (X : Tower.Edge L n k 0 → ComplexMatrix2)
        (FullSpace.projFace L n k 0 P) = _
      rw [hd]
      exact real_smul_four_pauli_sums _ _ _ _ _ _ rfl
    have hY : ∀ a : Fin 3, scaledFaceCombination (fun β => toPauliCoeffs
        (restrictToPositiveEdges (X : Tower.Edge L n k 0 → ComplexMatrix2))
          (a, projPositiveEdge L n k 0 β)) P =
        ∑' m : Fin 4 → ℤ, compKernel (FullSpace.scaledEdgeCoboundaryKernel L k 0) (responseKernel L k)
          (a, P) ((colourEdges L k k).translate (periodSide L n • m) (thirdColourIndexAt L k z)) := by
      intro a
      have e : (fun β => toPauliCoeffs (restrictToPositiveEdges (X : Tower.Edge L n k 0 → ComplexMatrix2))
          (a, projPositiveEdge L n k 0 β)) = fun β => ∑' m : Fin 4 → ℤ, responseKernel L k (a, β)
            ((colourEdges L k k).translate (periodSide L n • m) (thirdColourIndexAt L k z)) :=
        funext fun β => hA (a, β)
      rw [e, scaledFaceCombination_tsum fun β => (hformed (a, β) (thirdColourIndexAt L k z)).of_norm]
      exact tsum_congr fun m => (compKernel_scaledEdgeCoboundaryKernel_apply hFO hL hk _ a P _).symm
    show ComplexMatrix2.operatorNorm (Tower.scaledEdgeCoboundary (X : Tower.Edge L n k 0 → ComplexMatrix2)
      (FullSpace.projFace L n k 0 P)) ≤ _
    rw [hsum]
    refine operatorNorm_pauli_combination_le _ fun a => ?_
    rw [hY a]
    refine norm_tsum_translates_thirdColour_le (I' := colourFaces L k 0) pT hC₁ hδ₀ hD hs (a, P) z
      fun m => ?_
    refine (cellDist_le_translates hc pT z P.corner m).trans ?_
    show 4 + l1NormVec (_ - (P.corner : InfiniteLattice.AmbientSpace)) ≤
      5 + l1NormVec (_ - (P.corner : InfiniteLattice.AmbientSpace))
    linarith
  · have hpositive : ∀ β : PeriodicOperators.PosEdge L k 0, ∃ x : ℝ,
        (X : Tower.Edge L n k 0 → ComplexMatrix2) (projPositiveEdge L n k 0 β).1 =
          (x : ℂ) • ComplexMatrix2.pauliFamily 2 := by
      intro β
      have hz : ∀ a : Fin 3, a ≠ 2 → toPauliCoeffs
          (restrictToPositiveEdges (X : Tower.Edge L n k 0 → ComplexMatrix2))
          (a, projPositiveEdge L n k 0 β) = 0 := by
        intro a ha
        have e : toPauliCoeffs (restrictToPositiveEdges (X : Tower.Edge L n k 0 → ComplexMatrix2))
            (a, projPositiveEdge L n k 0 β) = _ := hA (a, β)
        rw [e]
        show ∑' m : Fin 4 → ℤ, responseKernel L k (a, β)
          ((colourEdges L k k).translate (periodSide L n • m) (thirdColourIndexAt L k z)) = 0
        have e₂ : (fun m : Fin 4 → ℤ => responseKernel L k (a, β)
            ((colourEdges L k k).translate (periodSide L n • m) (thirdColourIndexAt L k z))) =
              fun _ => 0 :=
          funext fun m => hcol.2.1 2 a β _ ha
        rw [e₂, tsum_zero]
      have hv := edgeForm_at_projPositiveEdge X β
      rw [Fin.sum_univ_three, hz 0 (by decide), hz 1 (by decide), zero_smul, zero_smul, zero_add,
        zero_add] at hv
      set c := toPauliCoeffs (restrictToPositiveEdges (X : Tower.Edge L n k 0 → ComplexMatrix2))
        (2, projPositiveEdge L n k 0 β) with hcdef
      have hsu := (X.2.1 _ (projPositiveEdge L n k 0 β).2).1
      have h00 := congrFun (congrFun hsu 0) 0
      rw [Matrix.conjTranspose_apply, hv] at h00
      have e₀ : (c • ComplexMatrix2.pauliFamily 2) 0 0 = c := by
        simp [ComplexMatrix2.pauliFamily, OneLoop.pauliZ]
      rw [e₀] at h00
      obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h00.symm
      exact ⟨x, by rw [hv, hx]⟩
    by_cases hpos : b.IsPositivelyOriented
    · obtain ⟨β, rfl⟩ := hlift b hpos
      exact hpositive β
    · obtain ⟨β, hβ⟩ := hlift b.opposite (hrev b hpos)
      obtain ⟨x, hx⟩ := hpositive β
      refine ⟨-x, ?_⟩
      rw [hneg b, ← hβ, hx]
      simp
private theorem pos_of_mem_halfSupRate {δ₀ : ℝ} (h : δ₀ ∈ FreeStrip.halfSupRate) : 0 < δ₀ := by apply _root_.YangMills.Construction.Tower.NormaliserSymbol.pos_of_mem_halfSupRate <;> assumption
theorem unitFormResponseDecays_holds (hFO : FreeOperators.FreeOperatorsArePeriodic)
    (hS : SymbolCalculus.Claim) (hSym : Symbols.Claim) (hId : IdKernelFacts.Claim)
    (hQ : StripSymbols.Claim) (hW : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim) (hP : ResponseProperties.AllProperties)
    (hRO : ResponseOperators.Claim) (hIm : ResponseImagesFullSide.ResponseImagesHold)
    (hCC : LocalKernels.PeriodicLiftCells.CellsAndClassesHold) :
    UnitFormResponseDecays := by
  obtain ⟨δ₀, hδ, hat⟩ := hRO
  have hδ₀ := pos_of_mem_halfSupRate hδ
  have hC := hP.2.2.1
  intro L hL
  have hC₁ : 0 ≤ 4 * |ResponseProperties.responseConstant| := by positivity
  set K := 4 * |ResponseProperties.responseConstant| * Real.exp (δ₀ * 5) *
    geometricLineBound δ₀ ^ 4 with hK
  set cp := ∑ a, ‖ComplexMatrix2.pauliFamily a‖ with hcp
  refine ⟨cp * K + 1, δ₀, by positivity, hδ₀, fun k hk => ⟨0, fun n _ hn z => ?_⟩⟩
  have hatk := hat L hL k hk
  have hker := responseKernel_decay hFO hS hSym hId hQ hW hIdx hC hδ hδ₀ hL hk hatk
  have pT := (hIdx L hL k k le_rfl).2.1
  have hcc := (hCC L hL k n hn).1
  obtain ⟨hc0, hb0⟩ := hcc 0 (Nat.zero_le k)
  obtain ⟨hck, hbk⟩ := hcc k le_rfl
  have hon := hatk.torus_sides n hn
  have hU := pauliUnitForm_mem_edgeFormSpace (L := L) (n := n) (k := k) (by have := hL.2; omega) hn z
  have himg : IsPeriodicImage L n k k 0 (responseKernel L k) (pauliUnitForm L n k z)
      (periodicResponse L n k (pauliUnitForm L n k z)) :=
    (hIm L hL k hk n hn ⟨_, hU⟩).resp_isImage
  have hA := toPauliCoeffs_periodicImage_eq hon.resp.factorsThroughQuot himg (thirdColourIndexAt L k z)
    (toPauliCoeffs_pauliUnitForm hck hbk z)
  obtain ⟨h₁, h₂, h₃⟩ := periodicResponse_pauliUnitForm_bounds hFO hL hk hn hc0 hb0 pT hC₁ hδ₀
    hker.1 hker.2 hatk.resp_real hon.resp.summable z hA
  have hfin : ∀ E : ℝ, 0 < E → cp * (K * E) ≤ (cp * K + 1) * E := by
    intro E hE
    nlinarith
  exact ⟨fun b => (h₁ b).trans (hfin _ (Real.exp_pos _)),
    fun p => (h₂ p).trans (hfin _ (Real.exp_pos _)), h₃⟩
end Conclusion
end YangMills.Construction.RunningCouplingSlope.UnitFormDecay
end
