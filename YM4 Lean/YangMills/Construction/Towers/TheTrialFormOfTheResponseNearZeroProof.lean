import YangMills.Construction.Towers.FormsOfTheFreeOperatorsInCoefficientsProof
import YangMills.Construction.Towers.PropertiesOfTheBackgroundsProof
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.TheResponseNearZeroProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology Asymptotics
noncomputable section
namespace YangMills.Construction.Tower.TrialResponse
open Matrices
open PeriodicOperators hiding addIVec
open PlaneWaveCalculus (SymbolFormulas EdgeCoeffFacts periodShift freeOps
  posEdgeAt vertexCoboundaryT meshC topEdgeComponent topVertexElement)
open FreeResolvents (trivialRescaledOperators)
open PlaneWaves
open ResponseProperties (InFundamentalStrip euclidNorm)
open FreeStrip (halfSupRate)
section PauliCoordinates
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem pauliNorm_nonneg (A : ComplexMatrix2) : 0 ≤ pauliNorm A := Real.sqrt_nonneg _
theorem pauliNorm_add_le {A B : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.traceless)
    (hB : B ∈ ComplexMatrix2.traceless) :
    pauliNorm (A + B) ≤ pauliNorm A + pauliNorm B := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.pauliNorm_add_le <;> assumption
theorem pauliNorm_smul (c : ℂ) {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.traceless) :
    pauliNorm (c • A) = ‖c‖ * pauliNorm A := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.pauliNorm_smul <;> assumption
theorem pauliNorm_zero : pauliNorm (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.pauliNorm_zero <;> assumption
theorem pauliNorm_sum_le {ι : Type} (s : Finset ι) (A : ι → ComplexMatrix2)
    (h : ∀ i, A i ∈ ComplexMatrix2.traceless) :
    pauliNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, pauliNorm (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pauliNorm_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (pauliNorm_add_le (h i) (Submodule.sum_mem _ fun j _ => h j)).trans
      (add_le_add_right ih _)
theorem pauliNorm_le_familyNorm (F : Fin 4 → ComplexMatrix2) (μ : Fin 4) :
    pauliNorm (F μ) ≤ pauliFamilyNorm F := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.pauliNorm_le_familyNorm <;> assumption
theorem pauliFamilyNorm_nonneg (F : Fin 4 → ComplexMatrix2) : 0 ≤ pauliFamilyNorm F :=
  Real.sqrt_nonneg _
theorem pauliFamilyNorm_le_of_le_mul {F G : Fin 4 → ComplexMatrix2} {c : Fin 4 → ℝ} {s : ℝ}
    (hc : ∀ μ, 0 ≤ c μ) (hs : ∀ μ, c μ ≤ s) (h : ∀ μ, pauliNorm (G μ) ≤ c μ * pauliNorm (F μ)) :
    pauliFamilyNorm G ≤ s * pauliFamilyNorm F := by
  have hs₀ : 0 ≤ s := (hc 0).trans (hs 0)
  have hF : pauliFamilyNorm F ^ 2 = ∑ μ, pauliNorm (F μ) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  refine Real.sqrt_le_iff.2 ⟨mul_nonneg hs₀ (pauliFamilyNorm_nonneg F), ?_⟩
  rw [mul_pow, hF, Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (pauliNorm_nonneg _)
    ((h μ).trans (mul_le_mul_of_nonneg_right (hs μ) (pauliNorm_nonneg _))) 2
end PauliCoordinates
section EdgeCoefficients
variable {L k : ℕ}
theorem edgeFourierCoeff_mem (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) (m : Fin 4 → ℤ) :
    edgeFourierCoeff L k b μ m ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.DiagonalSymbolBounds.edgeFourierCoeff_mem_traceless <;> assumption
theorem topEdgeComponent_mem (z : (colourEdges L k k).UnitQuot → ℂ) (μ : Fin 4) :
    topEdgeComponent L k z μ ∈ ComplexMatrix2.traceless :=
  ofPauliCoeffs_mem _ _
theorem finite_vertexClass (h : Finite (colourVertices L k 0).UnitQuot) :
    Finite (VertexClass L k) := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.finite_vertexClass <;> assumption
theorem edgeFourierCoeff_sub [Finite (VertexClass L k)]
    (b b' : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) (m : Fin 4 → ℤ) :
    edgeFourierCoeff L k (b - b') μ m = edgeFourierCoeff L k b μ m - edgeFourierCoeff L k b' μ m := by apply _root_.YangMills.Construction.Tower.ResponseAtSmallMomentum.edgeFourierCoeff_sub <;> assumption
theorem wNorm_le_of_edgeFourierCoeff_le (hC : EdgeCoeffFacts L k)
    (c : (colourEdges L k 0).UnitQuot → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ m ∈ freqBox L k, ∀ μ, pauliNorm (edgeFourierCoeff L k c μ m) ≤ B) :
    wNorm ((colourEdges L k 0).quotWeight 1) c ≤
      (4 * ((freqBox L k).card : ℝ) + 1) * B := by
  have hn : (0 : ℝ) ≤ (freqBox L k).card := Nat.cast_nonneg _
  refine (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1 ?_
  show wNorm ((colourEdges L k 0).quotWeight 1) c ^ 2 ≤ _
  rw [hC.norm_sq c]
  have h₁ : ∑ m ∈ freqBox L k, ∑ μ, pauliNorm (edgeFourierCoeff L k c μ m) ^ 2 ≤
      ∑ m ∈ freqBox L k, ∑ _μ : Fin 4, B ^ 2 :=
    Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun μ _ =>
      pow_le_pow_left₀ (pauliNorm_nonneg _) (h m hm μ) 2
  refine h₁.trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  nlinarith [sq_nonneg B, mul_nonneg hn (sq_nonneg B), mul_nonneg (mul_nonneg hn hn) (sq_nonneg B)]
end EdgeCoefficients
section EdgeClasses
variable {L k : ℕ}
theorem meshAt_self (L k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {μ ρ : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ρ) : μ = ρ := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
def edgeClass (L k : ℕ) (a : Fin 3) (μ : Fin 4) : (colourEdges L k k).UnitQuot :=
  (colourEdges L k k).mkQuot 1 (a, posEdgeAt L k k 0 μ)
variable (hT : TowerTranslations.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hk : 1 ≤ k)
include hT hL hk
theorem exists_eq_edgeClass (c : (colourEdges L k k).UnitQuot) : ∃ a μ, c = edgeClass L k a μ := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.exists_unitEdgeClass <;> assumption
theorem edgeClass_injective {a a' : Fin 3} {μ μ' : Fin 4}
    (h : edgeClass L k a μ = edgeClass L k a' μ') : a = a' ∧ μ = μ' := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.unitEdgeClass_injective <;> assumption
omit hT hL hk
theorem pauliCoeff_topEdgeComponent (z : (colourEdges L k k).UnitQuot → ℂ) (a : Fin 3) (μ : Fin 4) :
    pauliCoeff a (topEdgeComponent L k z μ) = z (edgeClass L k a μ) := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.pauliCoeff_topEdgeComponent <;> assumption
include hT hL hk
theorem eq_of_topEdgeComponent {z z' : (colourEdges L k k).UnitQuot → ℂ}
    (h : ∀ μ, topEdgeComponent L k z μ = topEdgeComponent L k z' μ) : z = z' := by
  funext c
  obtain ⟨a, μ, rfl⟩ := exists_eq_edgeClass hT hL hk c
  rw [← pauliCoeff_topEdgeComponent z, ← pauliCoeff_topEdgeComponent z', h]
theorem exists_topEdgeComponent_smul (w : Fin 4 → ℂ) (z : (colourEdges L k k).UnitQuot → ℂ) :
    ∃ z' : (colourEdges L k k).UnitQuot → ℂ,
      ∀ μ, topEdgeComponent L k z' μ = w μ • topEdgeComponent L k z μ := by
  choose col dir hc using exists_eq_edgeClass hT hL hk (L := L) (k := k)
  refine ⟨fun c => w (dir c) * z c, fun μ => ?_⟩
  have hd : ∀ a, dir (edgeClass L k a μ) = μ := fun a =>
    (edgeClass_injective hT hL hk (hc (edgeClass L k a μ))).2.symm
  have e : ∀ y : (colourEdges L k k).UnitQuot → ℂ,
      topEdgeComponent L k y μ = ∑ a, y (edgeClass L k a μ) • ComplexMatrix2.pauliFamily a :=
    fun _ => rfl
  rw [e, e, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, hd]
end EdgeClasses
section PlaneWaveWeights
variable (L k : ℕ)
theorem differentiable_dirichletSum : Differentiable ℂ (dirichletSum L k) := by
  have e : dirichletSum L k = fun τ => ((finestMesh L k : ℝ) : ℂ) * ∑ j ∈ freqWindow L k,
      Complex.exp (Complex.I * ((finestMesh L k : ℝ) : ℂ) * (j : ℂ) * τ) := rfl
  rw [e]
  fun_prop
theorem differentiable_vertexWeight : Differentiable ℂ (PlaneWaves.vertexWeight L k) := by
  have e : PlaneWaves.vertexWeight L k = fun q => ∏ ν, dirichletSum L k (q ν) := rfl
  have h : ∀ ν, Differentiable ℂ fun q : Fin 4 → ℂ => dirichletSum L k (q ν) := fun ν =>
    (differentiable_dirichletSum L k).comp (differentiable_apply ν)
  rw [e]
  simp only [Fin.prod_univ_four]
  exact (((h 0).mul (h 1)).mul (h 2)).mul (h 3)
theorem differentiable_edgeWeight (μ : Fin 4) :
    Differentiable ℂ fun q : Fin 4 → ℂ => edgeWeight L k q μ := by
  have e : (fun q : Fin 4 → ℂ => edgeWeight L k q μ) = fun q =>
      Complex.exp (Complex.I * (1 - ((finestMesh L k : ℝ) : ℂ)) * q μ / 2) *
        dirichletSum L k (q μ) * PlaneWaves.vertexWeight L k q := rfl
  rw [e]
  refine (Differentiable.mul ?_ ((differentiable_dirichletSum L k).comp (differentiable_apply μ))).mul
    (differentiable_vertexWeight L k)
  fun_prop
theorem differentiable_forwardSymbol (μ : Fin 4) :
    Differentiable ℂ fun q : Fin 4 → ℂ => forwardSymbol L k q μ := by
  have e : (fun q : Fin 4 → ℂ => forwardSymbol L k q μ) = fun q =>
      ((finestMesh L k : ℝ) : ℂ)⁻¹ *
        (Complex.exp (Complex.I * ((finestMesh L k : ℝ) : ℂ) * q μ) - 1) := rfl
  rw [e]
  fun_prop
theorem differentiable_shiftedFreq (m : Fin 4 → ℤ) :
    Differentiable ℂ fun p : Fin 4 → ℂ => shiftedFreq p m := by apply _root_.YangMills.Construction.Tower.FreeResolvents.differentiable_shiftedFreq <;> assumption
theorem shiftedFreq_zero (κ : Fin 4 → ℂ) : shiftedFreq κ 0 = κ := by
  funext μ
  simp [shiftedFreq]
variable {L k}
theorem finestMesh_inv : (finestMesh L k)⁻¹ = (L : ℝ) ^ k := by
  simp [finestMesh, meshAt, zpow_neg]
theorem zero_mem_freqBox (hL : Conventions.IsAdmissibleBlockingFactor L) :
    (0 : Fin 4 → ℤ) ∈ freqBox L k := by apply _root_.YangMills.Construction.Tower.ResponseAtSmallMomentum.zero_mem_freqBox <;> assumption
theorem finestMesh_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.finestMesh_pos <;> assumption
theorem dirichletSum_zero (hL : Conventions.IsAdmissibleBlockingFactor L) (hf : SymbolFormulas L k) :
    dirichletSum L k 0 = 1 := by
  have h := hf.geom_sum_eq 0
  simp only [mul_zero, zero_div, Complex.exp_zero, one_mul, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at h
  rw [← h]
  have e : finestMesh L k * (L : ℝ) ^ k = 1 := by
    rw [← finestMesh_inv]
    exact mul_inv_cancel₀ (finestMesh_pos hL).ne'
  have e' : (((finestMesh L k * (L : ℝ) ^ k : ℝ)) : ℂ) = 1 := by
    rw [e]
    simp
  simpa using e'
theorem vertexWeight_zero (hL : Conventions.IsAdmissibleBlockingFactor L) (hf : SymbolFormulas L k) :
    PlaneWaves.vertexWeight L k 0 = 1 := by
  simp [PlaneWaves.vertexWeight, dirichletSum_zero hL hf]
theorem edgeWeight_zero (hL : Conventions.IsAdmissibleBlockingFactor L) (hf : SymbolFormulas L k)
    (μ : Fin 4) : edgeWeight L k 0 μ = 1 := by
  simp [edgeWeight, dirichletSum_zero hL hf, vertexWeight_zero hL hf]
theorem forwardSymbol_zero (μ : Fin 4) : forwardSymbol L k 0 μ = 0 := by
  simp [forwardSymbol]
theorem dirichletSum_add_period (hL : Conventions.IsAdmissibleBlockingFactor L) (τ : ℂ) (n : ℤ) :
    dirichletSum L k (τ + 2 * (Real.pi : ℂ) / meshC L k * (n : ℂ)) = dirichletSum L k τ := by
  have hη : meshC L k ≠ 0 := Complex.ofReal_ne_zero.2 (finestMesh_pos hL).ne'
  unfold dirichletSum
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Complex.I * ((finestMesh L k : ℝ) : ℂ) * (j : ℂ) *
        (τ + 2 * (Real.pi : ℂ) / meshC L k * (n : ℂ)) =
      Complex.I * ((finestMesh L k : ℝ) : ℂ) * (j : ℂ) * τ +
        ((j * n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem vertexWeight_periodShift (hL : Conventions.IsAdmissibleBlockingFactor L) (q : Fin 4 → ℂ)
    (e : Fin 4 → ℤ) :
    PlaneWaves.vertexWeight L k (periodShift L k q e) = PlaneWaves.vertexWeight L k q := by
  simp only [PlaneWaves.vertexWeight, periodShift, dirichletSum_add_period hL]
theorem vertexWeight_shiftedFreq_eq_zero (hE : PlaneWaveBounds.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {m : Fin 4 → ℤ}
    (hm : m ∈ freqBox L k) (hm₀ : m ≠ 0) : PlaneWaves.vertexWeight L k (shiftedFreq 0 m) = 0 := by
  obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hm₀
  have hm' := (mem_freqBox L k m).1 hm
  let q' : Fin 4 → ℝ := fun ν => 2 * Real.pi * (m ν : ℝ)
  have hq : ∀ ν, |q' ν| ≤ Real.pi / finestMesh L k := by
    intro ν
    have h₁ := hm' ν
    have hπ := Real.pi_pos
    rw [div_eq_mul_inv]
    simp only [q']
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith
  have hb := (hE.1 L k hL hk q' 0 hq (by simp)).2.2 μ
  have hs := (hb.2.2 0 (m μ) (by simp [PlaneWaveBounds.complexPoint, q']) (by simp [Real.pi_pos.le])
    (by exact_mod_cast hμ)).1
  simp only [zero_div, Complex.sin_zero, norm_zero, zero_mul] at hs
  have h0 : dirichletSum L k (PlaneWaveBounds.complexPoint q' 0 μ) = 0 := norm_le_zero_iff.1 hs
  refine Finset.prod_eq_zero (Finset.mem_univ μ) ?_
  have e : shiftedFreq 0 m μ = PlaneWaveBounds.complexPoint q' 0 μ := by
    simp [PlaneWaveBounds.complexPoint, q', shiftedFreq]
  rw [e, h0]
theorem norm_le_euclidNorm (p : Fin 4 → ℂ) : ‖p‖ ≤ euclidNorm p := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun ρ => ?_
  exact (le_abs_self _).trans (Real.abs_le_sqrt (Finset.single_le_sum
    (f := fun ρ => ‖p ρ‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ ρ)))
theorem isBigO_euclidNorm_of_eq_zero {f : (Fin 4 → ℂ) → ℂ} (hf : DifferentiableAt ℂ f 0)
    (h₀ : f 0 = 0) : f =O[𝓝 0] euclidNorm := by
  have h := hf.hasFDerivAt.isBigO_sub
  simp only [h₀, sub_zero] at h
  refine h.trans (IsBigO.of_bound 1 (Eventually.of_forall fun p => ?_))
  have h₁ : 0 ≤ euclidNorm p := Real.sqrt_nonneg _
  rw [one_mul, Real.norm_of_nonneg h₁]
  exact norm_le_euclidNorm p
variable (L k)
def edgeWeightInv (μ : Fin 4) (p : Fin 4 → ℂ) : ℂ := (edgeWeight L k p μ)⁻¹
def gradFactor (ν : Fin 4) (p : Fin 4 → ℂ) : ℂ :=
  PlaneWaves.vertexWeight L k p * (forwardSymbol L k (-p) ν * edgeWeightInv L k ν p)
def aliasFactor (m : Fin 4 → ℤ) (μ : Fin 4) (p : Fin 4 → ℂ) : ℂ :=
  forwardSymbol L k (shiftedFreq p m) μ * PlaneWaves.vertexWeight L k (-shiftedFreq p m)
def residualRate (p : Fin 4 → ℂ) : ℝ :=
  ∑ μ, ‖symbolSquare L k p * edgeWeightInv L k μ p‖ +
    (∑ m ∈ freqBox L k, ∑ μ, ‖aliasFactor L k m μ p‖) * ∑ ν, ‖gradFactor L k ν p‖
def weightDefect (p : Fin 4 → ℂ) : ℝ := ∑ μ, ‖edgeWeightInv L k μ p - 1‖
variable {L k}
theorem differentiableAt_edgeWeightInv (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hf : SymbolFormulas L k) (μ : Fin 4) :
    DifferentiableAt ℂ (edgeWeightInv L k μ) 0 :=
  DifferentiableAt.inv (differentiable_edgeWeight L k μ 0) (by
    rw [edgeWeight_zero hL hf]
    exact one_ne_zero)
theorem differentiable_forwardSymbol_neg (ν : Fin 4) :
    Differentiable ℂ fun p : Fin 4 → ℂ => forwardSymbol L k (-p) ν :=
  (differentiable_forwardSymbol L k ν).comp
    (differentiable_id.neg : Differentiable ℂ fun p : Fin 4 → ℂ => -p)
theorem gradFactor_isBigO (hL : Conventions.IsAdmissibleBlockingFactor L) (hf : SymbolFormulas L k)
    (ν : Fin 4) : gradFactor L k ν =O[𝓝 0] euclidNorm := by
  refine isBigO_euclidNorm_of_eq_zero ?_ (by simp [gradFactor, forwardSymbol_zero])
  exact (differentiable_vertexWeight L k 0).mul
    ((differentiable_forwardSymbol_neg ν 0).mul (differentiableAt_edgeWeightInv hL hf ν))
theorem aliasFactor_isBigO (hE : PlaneWaveBounds.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hneg : ∀ m ∈ freqBox L k, -m ∈ freqBox L k) {m : Fin 4 → ℤ}
    (hm : m ∈ freqBox L k) (μ : Fin 4) : aliasFactor L k m μ =O[𝓝 0] euclidNorm := by
  refine isBigO_euclidNorm_of_eq_zero ?_ ?_
  · exact (((differentiable_forwardSymbol L k μ).comp (differentiable_shiftedFreq m)) 0).mul
      (((differentiable_vertexWeight L k).comp
        (differentiable_shiftedFreq m).neg) 0)
  · by_cases h : m = 0
    · subst h
      simp [aliasFactor, shiftedFreq_zero, forwardSymbol_zero]
    · have e : -shiftedFreq (0 : Fin 4 → ℂ) m = shiftedFreq 0 (-m) := by
        funext ν
        simp [shiftedFreq]
      simp only [aliasFactor]
      rw [e, vertexWeight_shiftedFreq_eq_zero hE hL hk (hneg m hm) (neg_ne_zero.2 h), mul_zero]
theorem symbolSquare_mul_isBigO (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hf : SymbolFormulas L k) (μ : Fin 4) :
    (fun p => symbolSquare L k p * edgeWeightInv L k μ p) =O[𝓝 0]
      fun p => euclidNorm p * euclidNorm p := by
  have e : (fun p => symbolSquare L k p * edgeWeightInv L k μ p) = fun p =>
      ∑ ν, forwardSymbol L k p ν * (forwardSymbol L k (-p) ν * edgeWeightInv L k μ p) := by
    funext p
    simp only [symbolSquare, Finset.sum_mul, mul_assoc]
  rw [e]
  refine IsBigO.fun_sum fun ν _ => IsBigO.mul ?_ ?_
  · exact isBigO_euclidNorm_of_eq_zero (differentiable_forwardSymbol L k ν 0) (forwardSymbol_zero ν)
  · exact isBigO_euclidNorm_of_eq_zero
      ((differentiable_forwardSymbol_neg ν 0).mul (differentiableAt_edgeWeightInv hL hf μ))
      (by simp [forwardSymbol_zero])
theorem residualRate_isBigO (hE : PlaneWaveBounds.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hneg : ∀ m ∈ freqBox L k, -m ∈ freqBox L k)
    (hf : SymbolFormulas L k) :
    residualRate L k =O[𝓝 0] fun p => euclidNorm p * euclidNorm p := by
  refine IsBigO.add (IsBigO.fun_sum fun μ _ => (symbolSquare_mul_isBigO hL hf μ).norm_left)
    (IsBigO.mul ?_ ?_)
  · exact IsBigO.fun_sum fun m hm => IsBigO.fun_sum fun μ _ =>
      (aliasFactor_isBigO hE hL hk hneg hm μ).norm_left
  · exact IsBigO.fun_sum fun ν _ => (gradFactor_isBigO hL hf ν).norm_left
theorem weightDefect_isBigO (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hf : SymbolFormulas L k) :
    weightDefect L k =O[𝓝 0] euclidNorm := by
  refine IsBigO.fun_sum fun μ _ => IsBigO.norm_left ?_
  exact isBigO_euclidNorm_of_eq_zero ((differentiableAt_edgeWeightInv hL hf μ).sub_const 1)
    (by simp [edgeWeightInv, edgeWeight_zero hL hf])
end PlaneWaveWeights
section SymbolOfX
variable {L k : ℕ}
theorem edgeFourierCoeff_symbolHom_X (hI : TowerIndexSets.Claim) (hS : StripSymbols.Claim)
    (hC : PlaneWaveCalculus.PlaneWaveCalculusHolds) (hF : FreeOperators.FreeOperatorsArePeriodic)
    (hOne : FullSpace.RescaledTrivialRelations)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (κ : Fin 4 → ℂ)
    (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) {m : Fin 4 → ℤ}
    (hm : m ∈ freqBox L k) :
    edgeFourierCoeff L k
        (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X κ b) μ m =
      symbolSquare L k (shiftedFreq κ m) • edgeFourierCoeff L k b μ m -
        (forwardSymbol L k (shiftedFreq κ m) μ * PlaneWaves.vertexWeight L k (-shiftedFreq κ m)) •
          ∑ m' ∈ freqBox L k, PlaneWaves.vertexWeight L k (shiftedFreq κ m') •
            ∑ ν, forwardSymbol L k (-shiftedFreq κ m') ν • edgeFourierCoeff L k b ν m' := by
  obtain ⟨-, -, -, -, -, hAct, hAvg, -⟩ := hC L hL k hk
  obtain ⟨hM, hOp⟩ := hF.2 L hL k hk
  obtain ⟨sS, sB, -⟩ := hI L hL k 0 (Nat.zero_le k)
  obtain ⟨tS, -, -⟩ := hI L hL k k le_rfl
  have : Finite (VertexClass L k) := finite_vertexClass sS.finite_quot
  have pd := (hM.vertexCoboundary 0 (Nat.zero_le k)).finite_range
  have pdt := hOp.vertexCoboundary_transpose 0 (Nat.zero_le k)
  have pR := hM.vertexAverage.finite_range
  have pRt := hOp.vertexAverage_transpose
  have pK := hOp.K
  have fd := (hS.2.1 _ _ sS sB).1.finiteRange _ pd.1 pd.2.1 κ (mem_univ _)
  have fdt := (hS.2.1 _ _ sB sS).1.finiteRange _ pdt.1 pdt.2.1 κ (mem_univ _)
  have fR := (hS.2.1 _ _ sS tS).1.finiteRange _ pR.1 pR.2.1 κ (mem_univ _)
  have fRt := (hS.2.1 _ _ tS sS).1.finiteRange _ pRt.1 pRt.2.1 κ (mem_univ _)
  have fK := (hS.2.1 _ _ sB sB).1.finiteRange _ pK.1 pK.2.1 κ (mem_univ _)
  have eDk : (trivialRescaledOperators L k).D = FullSpace.scaledVertexCoboundaryKernel L k 0 :=
    (hOne L hL k hk).D_eq
  have eDt : (trivialRescaledOperators L k).Dt =
      kernelTranspose (colourVertices L k 0) (colourEdges L k 0)
        (FullSpace.scaledVertexCoboundaryKernel L k 0) := by
    rw [← eDk]
    rfl
  obtain ⟨-, q₁, f₁, e₁⟩ := ((hS.2.1 _ _ sS sB).2.1 _ κ pd.1 fd).comp _ tS _ pRt.1 fRt
  obtain ⟨-, q₂, f₂, e₂⟩ := ((hS.2.1 _ _ sS tS).2.1 _ κ pR.1 fR).comp _ sB _ pdt.1 fdt
  obtain ⟨-, q₃, f₃, e₃⟩ := ((hS.2.1 _ _ tS sB).2.1 _ κ q₁ f₁).comp _ sB _ q₂ f₂
  have c := ((hS.2.1 _ _ sB sB).2.1 _ κ pK.1 fK).linComb _ q₃ f₃ 1 (-1)
  have eX : (trivialRescaledOperators L k).X =
      StripSymbols.linCombKernel 1 (-1) (trivialRescaledOperators L k).K
        (compKernel
          (compKernel (FullSpace.scaledVertexCoboundaryKernel L k 0) (trivialRescaledOperators L k).Rt)
          (compKernel (trivialRescaledOperators L k).R
            (kernelTranspose (colourVertices L k 0) (colourEdges L k 0)
              (FullSpace.scaledVertexCoboundaryKernel L k 0)))) := by
    rw [← eDt, ← eDk]
    funext ι' ι
    change (trivialRescaledOperators L k).K ι' ι -
        compKernel (compKernel (trivialRescaledOperators L k).D (trivialRescaledOperators L k).Rt)
          (compKernel (trivialRescaledOperators L k).R (trivialRescaledOperators L k).Dt) ι' ι +
        compKernel (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q ι' ι -
        compKernel (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q ι' ι = _
    simp only [StripSymbols.linCombKernel]
    ring
  have eMap := (congrArg (fun T => symbolHom (colourEdges L k 0) (colourEdges L k 0) T κ)
    eX).trans c.2.2
  have hb := LinearMap.congr_fun eMap b
  rw [e₃, e₁, e₂] at hb
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, one_smul,
    neg_smul] at hb
  have hK : edgeFourierCoeff L k
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K κ b) μ m =
      symbolSquare L k (shiftedFreq κ m) • edgeFourierCoeff L k b μ m :=
    hAct.K κ b μ m hm
  have hRt : ∀ g, vertexFourierCoeff L k
      (symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ g) m =
      PlaneWaves.vertexWeight L k (-shiftedFreq κ m) • topVertexElement L k g :=
    fun g => hAvg.Rt κ g m hm
  have hR : ∀ l, topVertexElement L k
      (symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R κ l) =
      ∑ m' ∈ freqBox L k, PlaneWaves.vertexWeight L k (shiftedFreq κ m') •
        vertexFourierCoeff L k l m' := fun l => hAvg.R κ l
  have hb' : symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X κ b =
      symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K κ b -
        symbolHom (colourVertices L k 0) (colourEdges L k 0)
          (FullSpace.scaledVertexCoboundaryKernel L k 0) κ
          (symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ
            (symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R κ
              (symbolHom (colourEdges L k 0) (colourVertices L k 0)
                (vertexCoboundaryT L k 0) κ b))) :=
    hb.trans (sub_eq_add_neg _ _).symm
  rw [hb', edgeFourierCoeff_sub, hK, hAct.vertexCoboundary κ _ μ m hm, hRt, hR, smul_smul]
  congr 2
  refine Finset.sum_congr rfl fun m' hm' => ?_
  rw [hAct.vertexCoboundary_transpose κ b m' hm']
theorem exists_edgeField_zero_mode (hS : TowerTranslations.Claim)
    (hE : PlaneWaveBounds.Claim) (hC : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (w : Fin 4 → ℂ)
    (ε : (colourEdges L k k).UnitQuot → ℂ) :
    ∃ b : (colourEdges L k 0).UnitQuot → ℂ,
      (∀ μ, edgeFourierCoeff L k b μ 0 = w μ • topEdgeComponent L k ε μ) ∧
      ∀ m ∈ freqBox L k, m ≠ 0 → ∀ μ, edgeFourierCoeff L k b μ m = 0 := by
  obtain ⟨-, -, -, -, hf, -, hAvg, -, -, hMt⟩ := hC L hL k hk
  obtain ⟨z, hz⟩ := exists_topEdgeComponent_smul hS hL hk w ε
  obtain ⟨-, FB, -⟩ := hMt 1 one_pos (PlaneWaves.vertexWeight L k)
    fun q _ e => vertexWeight_periodShift hL q e
  have h₀ : (0 : Fin 4 → ℂ) ∈ openImStrip 1 := fun μ => by simp
  have hmul := (FB.scales_unique 0 h₀).1
  have hQt : ∀ μ, ∀ m ∈ freqBox L k, edgeFourierCoeff L k
      (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt 0 z) μ m =
      edgeWeight L k (-shiftedFreq 0 m) μ • topEdgeComponent L k z μ :=
    fun μ m hm => hAvg.Qt 0 z μ m hm
  refine ⟨edgeFourierMultiplier L k (PlaneWaves.vertexWeight L k) 0
    (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt 0 z),
    fun μ => ?_, fun m hm hm₀ μ => ?_⟩
  · have h00 := zero_mem_freqBox (k := k) hL
    rw [hmul _ μ 0 h00, hQt μ 0 h00, shiftedFreq_zero, neg_zero, vertexWeight_zero hL hf,
      edgeWeight_zero hL hf, one_smul, one_smul, hz]
  · rw [hmul _ μ m hm, vertexWeight_shiftedFreq_eq_zero hE hL hk hm hm₀, zero_smul]
end SymbolOfX
theorem pauliNorm_sub_le {A B : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.traceless)
    (hB : B ∈ ComplexMatrix2.traceless) :
    pauliNorm (A - B) ≤ pauliNorm A + pauliNorm B := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.pauliNorm_sub_le <;> assumption
theorem trialFieldNearZero_holds (hI : TowerIndexSets.Claim) (hS : StripSymbols.Claim)
    (hTr : TowerTranslations.Claim) (hC : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hE : PlaneWaveBounds.Claim) (hF : FreeOperators.FreeOperatorsArePeriodic)
    (hOne : FullSpace.RescaledTrivialRelations) :
    TrialFieldNearZero := by
  intro δ₀ _ L hL k hk
  obtain ⟨hneg, -, hcoef, -, hf, -, hAvg, -, -, -⟩ := hC L hL k hk
  obtain ⟨C₁, h₁⟩ := (residualRate_isBigO hE hL hk hneg hf).bound
  obtain ⟨C₂, h₂⟩ := (weightDefect_isBigO hL hf).bound
  have hne : ∀ᶠ p in 𝓝 (0 : Fin 4 → ℂ), ∀ μ, edgeWeight L k p μ ≠ 0 :=
    eventually_all.2 fun μ =>
      (differentiable_edgeWeight L k μ).continuous.continuousAt.eventually_ne
        (by rw [edgeWeight_zero hL hf]; exact one_ne_zero)
  refine ⟨(4 * ((freqBox L k).card : ℝ) + 1) * |C₁| + |C₂|, _, h₁.and (h₂.and hne), ?_⟩
  rintro p ⟨hp₁, hp₂, hu⟩ - ε
  obtain ⟨b, hc₀, hcm⟩ := exists_edgeField_zero_mode hTr hE hC hL hk
    (fun μ => (edgeWeight L k p μ)⁻¹) ε
  have h00 := zero_mem_freqBox (k := k) hL
  have hM₀ : 0 ≤ 4 * ((freqBox L k).card : ℝ) + 1 := by positivity
  have he₀ : 0 ≤ pauliFamilyNorm (topEdgeComponent L k ε) := pauliFamilyNorm_nonneg _
  have hr₀ : 0 ≤ euclidNorm p := Real.sqrt_nonneg _
  refine ⟨b, ⟨hc₀, hcm⟩, ?_, ?_, ?_⟩
  · refine eq_of_topEdgeComponent hTr hL hk fun μ => ?_
    have h : topEdgeComponent L k
        (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q p b) μ =
        ∑ m ∈ freqBox L k, edgeWeight L k (shiftedFreq p m) μ • edgeFourierCoeff L k b μ m :=
      hAvg.Q p b μ
    rw [h, Finset.sum_eq_single 0 (fun m hm hm₀ => by rw [hcm m hm hm₀, smul_zero])
      (fun h => absurd h00 h), shiftedFreq_zero, hc₀, smul_smul, mul_inv_cancel₀ (hu μ), one_smul]
  · have hY : ∑ m' ∈ freqBox L k, PlaneWaves.vertexWeight L k (shiftedFreq p m') •
        ∑ ν, forwardSymbol L k (-shiftedFreq p m') ν • edgeFourierCoeff L k b ν m' =
        ∑ ν, gradFactor L k ν p • topEdgeComponent L k ε ν := by
      rw [Finset.sum_eq_single 0 (fun m hm hm₀ => by simp [hcm m hm hm₀])
        (fun h => absurd h00 h), shiftedFreq_zero, Finset.smul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [hc₀, smul_smul, smul_smul]
      simp only [gradFactor, edgeWeightInv, mul_assoc]
    have hYmem : ∀ ν, gradFactor L k ν p • topEdgeComponent L k ε ν ∈ ComplexMatrix2.traceless :=
      fun ν => Submodule.smul_mem _ _ (topEdgeComponent_mem ε ν)
    have hYn : pauliNorm (∑ ν, gradFactor L k ν p • topEdgeComponent L k ε ν) ≤
        (∑ ν, ‖gradFactor L k ν p‖) * pauliFamilyNorm (topEdgeComponent L k ε) := by
      refine (pauliNorm_sum_le _ _ hYmem).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun ν _ => ?_
      rw [pauliNorm_smul _ (topEdgeComponent_mem ε ν)]
      exact mul_le_mul_of_nonneg_left (pauliNorm_le_familyNorm _ ν) (norm_nonneg _)
    have hS₁ : 0 ≤ ∑ μ, ‖symbolSquare L k p * edgeWeightInv L k μ p‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hS₂ : 0 ≤ ∑ m ∈ freqBox L k, ∑ μ, ‖aliasFactor L k m μ p‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hS₃ : 0 ≤ ∑ ν, ‖gradFactor L k ν p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hρ₀ : 0 ≤ residualRate L k p := add_nonneg hS₁ (mul_nonneg hS₂ hS₃)
    have hT : ∀ m ∈ freqBox L k, ∀ μ, pauliNorm (edgeFourierCoeff L k
        (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X p b) μ m) ≤
        residualRate L k p * pauliFamilyNorm (topEdgeComponent L k ε) := by
      intro m hm μ
      rw [edgeFourierCoeff_symbolHom_X hI hS hC hF hOne hL hk p b μ hm, hY]
      have hA : pauliNorm (symbolSquare L k (shiftedFreq p m) • edgeFourierCoeff L k b μ m) ≤
          (∑ μ, ‖symbolSquare L k p * edgeWeightInv L k μ p‖) *
            pauliFamilyNorm (topEdgeComponent L k ε) := by
        by_cases h : m = 0
        · subst h
          rw [shiftedFreq_zero, hc₀, smul_smul, pauliNorm_smul _ (topEdgeComponent_mem ε μ)]
          refine mul_le_mul ?_ (pauliNorm_le_familyNorm _ μ) (pauliNorm_nonneg _) hS₁
          exact Finset.single_le_sum (f := fun μ => ‖symbolSquare L k p * edgeWeightInv L k μ p‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ μ)
        · rw [hcm m hm h μ, smul_zero, pauliNorm_zero]
          exact mul_nonneg hS₁ he₀
      have hB : pauliNorm ((forwardSymbol L k (shiftedFreq p m) μ *
            PlaneWaves.vertexWeight L k (-shiftedFreq p m)) •
            ∑ ν, gradFactor L k ν p • topEdgeComponent L k ε ν) ≤
          (∑ m ∈ freqBox L k, ∑ μ, ‖aliasFactor L k m μ p‖) *
            ((∑ ν, ‖gradFactor L k ν p‖) * pauliFamilyNorm (topEdgeComponent L k ε)) := by
        rw [pauliNorm_smul _ (Submodule.sum_mem _ fun ν _ => hYmem ν)]
        refine mul_le_mul ?_ hYn (pauliNorm_nonneg _) hS₂
        have i₁ : ‖aliasFactor L k m μ p‖ ≤ ∑ μ, ‖aliasFactor L k m μ p‖ :=
          Finset.single_le_sum (f := fun μ => ‖aliasFactor L k m μ p‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ μ)
        exact i₁.trans (Finset.single_le_sum (f := fun m => ∑ μ, ‖aliasFactor L k m μ p‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hm)
      refine (pauliNorm_sub_le (Submodule.smul_mem _ _ (edgeFourierCoeff_mem b μ m))
        (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun ν _ => hYmem ν))).trans
        ((add_le_add hA hB).trans (le_of_eq ?_))
      simp only [residualRate]
      ring
    have hN := wNorm_le_of_edgeFourierCoeff_le hcoef _ (mul_nonneg hρ₀ he₀) hT
    have hρ : residualRate L k p ≤ |C₁| * euclidNorm p ^ 2 := by
      have i₁ : ‖residualRate L k p‖ ≤ C₁ * ‖euclidNorm p * euclidNorm p‖ := hp₁
      rw [Real.norm_of_nonneg hρ₀, Real.norm_of_nonneg (mul_nonneg hr₀ hr₀)] at i₁
      refine i₁.trans ?_
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hr₀ hr₀)
    have hA₀ : 0 ≤ euclidNorm p ^ 2 * pauliFamilyNorm (topEdgeComponent L k ε) := by positivity
    calc _ ≤ (4 * ((freqBox L k).card : ℝ) + 1) *
            (residualRate L k p * pauliFamilyNorm (topEdgeComponent L k ε)) := hN
      _ ≤ (4 * ((freqBox L k).card : ℝ) + 1) *
            (|C₁| * euclidNorm p ^ 2 * pauliFamilyNorm (topEdgeComponent L k ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρ he₀) hM₀
      _ = (4 * ((freqBox L k).card : ℝ) + 1) * |C₁| *
            (euclidNorm p ^ 2 * pauliFamilyNorm (topEdgeComponent L k ε)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) hA₀
  · have hσ₀ : 0 ≤ weightDefect L k p := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hD : pauliFamilyNorm (fun μ => edgeFourierCoeff L k b μ 0 - topEdgeComponent L k ε μ) ≤
        weightDefect L k p * pauliFamilyNorm (topEdgeComponent L k ε) := by
      refine pauliFamilyNorm_le_of_le_mul (c := fun μ => ‖edgeWeightInv L k μ p - 1‖)
        (fun _ => norm_nonneg _) (fun μ => ?_) (fun μ => ?_)
      · exact Finset.single_le_sum (f := fun μ => ‖edgeWeightInv L k μ p - 1‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ μ)
      · have e : edgeFourierCoeff L k b μ 0 - topEdgeComponent L k ε μ =
            (edgeWeightInv L k μ p - 1) • topEdgeComponent L k ε μ := by
          rw [hc₀, sub_smul, one_smul]
          rfl
        rw [e, pauliNorm_smul _ (topEdgeComponent_mem ε μ)]
    have hσ : weightDefect L k p ≤ |C₂| * euclidNorm p := by
      have i₁ : ‖weightDefect L k p‖ ≤ C₂ * ‖euclidNorm p‖ := hp₂
      rw [Real.norm_of_nonneg hσ₀, Real.norm_of_nonneg hr₀] at i₁
      exact i₁.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hr₀)
    have hA₀ : 0 ≤ euclidNorm p * pauliFamilyNorm (topEdgeComponent L k ε) := by positivity
    have hC₀ : 0 ≤ (4 * ((freqBox L k).card : ℝ) + 1) * |C₁| := by positivity
    calc _ ≤ weightDefect L k p * pauliFamilyNorm (topEdgeComponent L k ε) := hD
      _ ≤ |C₂| * euclidNorm p * pauliFamilyNorm (topEdgeComponent L k ε) :=
        mul_le_mul_of_nonneg_right hσ he₀
      _ = |C₂| * (euclidNorm p * pauliFamilyNorm (topEdgeComponent L k ε)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀) hA₀
end YangMills.Construction.Tower.TrialResponse
end
