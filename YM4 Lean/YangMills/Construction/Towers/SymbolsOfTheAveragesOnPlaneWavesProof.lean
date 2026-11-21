import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.PeriodicOperators.SumsOfExponentialsProof
import YangMills.Construction.PeriodicOperators.SymbolAtAPoint
import YangMills.Construction.Towers.FormulasOfThePlaneWaveFunctions
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.PlaneWaveCoefficientsOnTheBonds
import YangMills.Construction.Towers.PlaneWaveCoefficientsOnTheSites
import YangMills.Construction.Towers.SandwichesOfTheFreeOperatorsInCoefficientsProof
import YangMills.Construction.Towers.SymbolsOfTheAveragesOnPlaneWaves
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
namespace PlaneWaveSmoothingSymbols
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (PeriodicData IsPeriodic IsPeriodicKernel IsFiniteRange
  SymbolSummableAt colourVertices colourEdges applyKernel quotSymbol symbolHom blochWave
  kernelTranspose quotTranspose intShift toComplexVec castVec bilinDot
  linearMapOfEntries_eq_applyKernel)
open Matrices (ComplexMatrix2)
open PlaneWaves
open PlaneWaveCalculus
variable {L k : ℕ}
theorem meshAt_zero_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < meshAt L k 0 := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.finestMesh_pos <;> assumption
theorem meshAt_self : meshAt L k k = 1 := by simp [meshAt]
theorem meshAt_zero_mul_pow (hL : Conventions.IsAdmissibleBlockingFactor L) :
    meshAt L k 0 * (L : ℝ) ^ k = 1 := by
  have : (L : ℝ) ≠ 0 := by exact_mod_cast (by have := hL.2; omega : L ≠ 0)
  simp [meshAt, zpow_neg, this]
theorem finestMesh_inv (hL : Conventions.IsAdmissibleBlockingFactor L) :
    (finestMesh L k)⁻¹ = (L : ℝ) ^ k :=
  (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact meshAt_zero_mul_pow hL)).symm
def cubePoint (L k : ℕ) (ν : Fin 4 → ℤ) : FullSpace.Vertex L k 0 :=
  ⟨fun μ => (ν μ : ℝ) * meshAt L k 0, ν, fun _ => rfl⟩
theorem mem_freqBox_iff (hL : Conventions.IsAdmissibleBlockingFactor L) (ν : Fin 4 → ℤ) :
    ν ∈ freqBox L k ↔ ∀ μ, 2 * |ν μ| ≤ (L : ℤ) ^ k - 1 := by
  rw [mem_freqBox]
  refine forall_congr' fun μ => ?_
  rw [finestMesh_inv hL, ← Int.cast_le (R := ℝ)]
  push_cast
  constructor <;> intro h <;> linarith
theorem exists_cubePoint (hL : Conventions.IsAdmissibleBlockingFactor L) (x : FullSpace.Vertex L k 0) :
    ∃ ν ∈ freqBox L k, ∃ n : Fin 4 → ℤ,
      (x : AmbientSpace) = (cubePoint L k ν : AmbientSpace) + castVec n := by
  obtain ⟨N', hN⟩ := x.2
  obtain ⟨h, hh⟩ : ∃ h : ℤ, (L : ℤ) ^ k = 2 * h + 1 := by
    have : Odd ((L : ℤ) ^ k) := by
      have : Odd (L : ℤ) := by exact_mod_cast hL.1
      exact this.pow
    exact this
  have hpos : 0 < (L : ℤ) ^ k := by
    have : (0 : ℤ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
    positivity
  refine ⟨fun μ => (N' μ + h) % (L : ℤ) ^ k - h, ?_, fun μ => (N' μ + h) / (L : ℤ) ^ k, ?_⟩
  · rw [mem_freqBox_iff hL]
    intro μ
    have h₁ := Int.emod_nonneg (N' μ + h) hpos.ne'
    have h₂ := Int.emod_lt_of_pos (N' μ + h) hpos
    show 2 * |(N' μ + h) % (L : ℤ) ^ k - h| ≤ (L : ℤ) ^ k - 1
    generalize (N' μ + h) % (L : ℤ) ^ k = r at h₁ h₂ ⊢
    rcases abs_cases (r - h) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> omega
  · funext μ
    have e := Int.mul_ediv_add_emod (N' μ + h) ((L : ℤ) ^ k)
    have e' : (((L : ℤ) ^ k * ((N' μ + h) / (L : ℤ) ^ k) + (N' μ + h) % (L : ℤ) ^ k : ℤ) : ℝ) =
        ((N' μ + h : ℤ) : ℝ) := by rw [e]
    have hs := meshAt_zero_mul_pow (k := k) hL
    push_cast at e'
    simp only [cubePoint, castVec, Pi.add_apply, hN μ]
    push_cast
    have : (N' μ : ℝ) = (L : ℝ) ^ k * (((N' μ + h) / (L : ℤ) ^ k : ℤ) : ℝ) +
        (((N' μ + h) % (L : ℤ) ^ k : ℤ) : ℝ) - h := by linarith
    rw [this]
    linear_combination (((N' μ + h) / (L : ℤ) ^ k : ℤ) : ℝ) * hs
theorem cubePoint_unique (hL : Conventions.IsAdmissibleBlockingFactor L) {ν ν' : Fin 4 → ℤ}
    (hν : ν ∈ freqBox L k) (hν' : ν' ∈ freqBox L k) {n : Fin 4 → ℤ}
    (e : (cubePoint L k ν' : AmbientSpace) = (cubePoint L k ν : AmbientSpace) + castVec n) :
    ν' = ν := by
  rw [mem_freqBox_iff hL] at hν hν'
  have hpos : 0 < (L : ℤ) ^ k := by
    have : (0 : ℤ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
    positivity
  funext μ
  have hs := meshAt_zero_mul_pow (k := k) hL
  have e₁ : (ν' μ : ℝ) * meshAt L k 0 = (ν μ : ℝ) * meshAt L k 0 + (n μ : ℝ) :=
    congrFun e μ
  have e₂ : (ν' μ : ℝ) = (ν μ : ℝ) + (n μ : ℝ) * (L : ℝ) ^ k := by
    linear_combination (L : ℝ) ^ k * e₁ + ((ν μ : ℝ) - (ν' μ : ℝ)) * hs
  have e₃ : ν' μ - ν μ = n μ * (L : ℤ) ^ k := by
    have : ((ν' μ - ν μ : ℤ) : ℝ) = ((n μ * (L : ℤ) ^ k : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have h₁ := hν μ
  have h₂ := hν' μ
  have habs : |ν' μ - ν μ| < (L : ℤ) ^ k := by
    have := abs_sub (ν' μ) (ν μ)
    omega
  have := Int.eq_zero_of_abs_lt_dvd (Dvd.intro_left (n μ) e₃.symm) habs
  omega
theorem castVec_zero : castVec 0 = 0 := by
  funext μ
  simp [castVec]
theorem castVec_neg (n : Fin 4 → ℤ) : castVec (-n) = -castVec n := by
  funext μ
  simp [castVec]
theorem castVec_add (m n : Fin 4 → ℤ) : castVec (m + n) = castVec m + castVec n := by apply _root_.YangMills.Construction.PeriodicOperators.ExponentialSums.castVec_add <;> assumption
structure Hypotheses (L k : ℕ) : Prop where
  admissible : Conventions.IsAdmissibleBlockingFactor L
  one_le : 1 ≤ k
  translations : PeriodicOperators.TowerTranslations.Claim
  indexSets : PeriodicOperators.TowerIndexSets.Claim
  waves : PeriodicOperators.SymbolOnQuotients.Claim
  strips : PeriodicOperators.StripSymbols.Claim
  pointwise : PeriodicOperators.SymbolPointwise.Properties
  means : FullSpace.RescaledConditions.TrivialAverages L k
  maps : FreeOperators.FreeMapsRangeThree L k
  vertexCoeffs : VertexCoeffFacts L k
  edgeCoeffs : EdgeCoeffFacts L k
  formulas : SymbolFormulas L k
variable (F : Hypotheses L k)
include F
theorem coe_vertexImage {j : ℕ} (hj : j ≤ k) (n : Fin 4 → ℤ) (x : FullSpace.Vertex L k j) :
    ((FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k j) : AmbientSpace) =
      (x : AmbientSpace) + castVec n :=
  ((F.translations L F.admissible k j F.one_le hj n).2.1 x).1
theorem exists_of_vertexClass_eq {x x' : FullSpace.Vertex L k 0}
    (h : (Quot.mk _ x : VertexClass L k) = Quot.mk _ x') :
    ∃ n : Fin 4 → ℤ, (x' : AmbientSpace) = (x : AmbientSpace) + castVec n := by
  have hg := Quot.eqvGen_exact h
  clear h
  induction hg with
  | rel x y h =>
    obtain ⟨n, rfl⟩ := h
    exact ⟨n, coe_vertexImage F (Nat.zero_le k) n x⟩
  | refl x => exact ⟨0, by simp [castVec_zero]⟩
  | symm x y _ ih =>
    obtain ⟨n, e⟩ := ih
    exact ⟨-n, by rw [e, castVec_neg]; simp⟩
  | trans x y z _ _ ih₁ ih₂ =>
    obtain ⟨m, e⟩ := ih₁
    obtain ⟨n, e'⟩ := ih₂
    exact ⟨m + n, by rw [e', e, castVec_add, add_assoc]⟩
theorem vertexClass_bijective :
    Function.Bijective fun ν : freqBox L k =>
      (Quot.mk _ (cubePoint L k ν.1) : VertexClass L k) := by
  constructor
  · rintro ⟨ν, hν⟩ ⟨ν', hν'⟩ e
    obtain ⟨n, e'⟩ := exists_of_vertexClass_eq F e
    exact Subtype.ext (cubePoint_unique F.admissible hν hν' e').symm
  · intro c
    induction c using Quot.ind with
    | mk x =>
      obtain ⟨ν, hν, n, e⟩ := exists_cubePoint F.admissible x
      exact ⟨⟨ν, hν⟩, Quot.sound ⟨n, Subtype.ext (by
        rw [coe_vertexImage F (Nat.zero_le k)]
        exact e)⟩⟩
theorem finsum_vertexClass {M : Type*} [AddCommMonoid M] (h : FullSpace.Vertex L k 0 → M)
    (hper : ∀ n x, h (FullSpace.vertexImage (intShift n) x) = h x) :
    ∑ᶠ c : VertexClass L k, h (Quot.out c) = ∑ ν ∈ freqBox L k, h (cubePoint L k ν) := by
  let H : VertexClass L k → M := Quot.lift h (by
    rintro a b ⟨n, rfl⟩
    exact (hper n a).symm)
  have e₁ : ∀ c, h (Quot.out c) = H c := fun c => by
    conv_rhs => rw [← Quot.out_eq c]
  rw [finsum_congr e₁,
    ← finsum_eq_of_bijective _ (vertexClass_bijective F) (f := fun ν : freqBox L k =>
      h (cubePoint L k ν.1)) (g := H) fun _ => rfl,
    finsum_eq_sum_of_fintype]
  exact Finset.sum_coe_sort (freqBox L k) fun ν => h (cubePoint L k ν)
omit F in
theorem eq_of_mkQuot_eq (I : PeriodicData) {β : Type*} (φ : I.Carrier → β)
    (h : ∀ n ι, φ (I.translate n ι) = φ ι) {ι ι' : I.Carrier}
    (e : I.mkQuot 1 ι = I.mkQuot 1 ι') : φ ι = φ ι' := by apply _root_.YangMills.Construction.Tower.FreeSandwiches.eq_of_mkQuot_eq <;> assumption
omit F in
theorem mkQuot_translate (I : PeriodicData) (n : Fin 4 → ℤ) (ι : I.Carrier) :
    I.mkQuot 1 (I.translate n ι) = I.mkQuot 1 ι :=
  (Quot.sound ⟨n, by simp⟩).symm
omit F in
theorem expWave_cubePoint (q : Fin 4 → ℂ) (ν : Fin 4 → ℤ) :
    expWave q (cubePoint L k ν) = ∏ μ, Complex.exp (Complex.I * meshC L k * (ν μ : ℂ) * q μ) := by
  rw [← Complex.exp_sum, expWave]
  congr 1
  simp only [bilinDot, toComplexVec, cubePoint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [meshC, finestMesh]
  push_cast
  ring
omit F in
theorem sum_expWave_cube (q : Fin 4 → ℂ) :
    ((finestMesh L k ^ 4 : ℝ) : ℂ) * ∑ ν ∈ freqBox L k, expWave q (cubePoint L k ν) =
      PlaneWaves.vertexWeight L k q := by
  simp only [expWave_cubePoint, PlaneWaves.vertexWeight, dirichletSum, freqBox]
  rw [Finset.prod_mul_distrib, ← Finset.prod_univ_sum (fun _ : Fin 4 => freqWindow L k)
    (fun μ j => Complex.exp (Complex.I * meshC L k * (j : ℂ) * q μ))]
  simp
omit F in
theorem sum_smul_pauliFamily_mem (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
omit F in
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
omit F in
theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
omit F in
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) :
    ofPauliCoeffs c ∈ Matrices.GroupLieProduct.tracelessFunctions σ :=
  fun x _ => sum_smul_pauliFamily_mem fun a => c (a, x)
omit F in
theorem real_smul_eq_complex_smul (r : ℝ) (A : ComplexMatrix2) : r • A = (r : ℂ) • A := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
omit F in
theorem symbolHom_eq_applyKernel {I I' : PeriodicData} (hI : IsPeriodic I)
    (T : I'.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ) (f : I.UnitQuot → ℂ) :
    symbolHom I I' T κ f = applyKernel (quotSymbol I I' T κ) f := by
  have := hI.finite_quot
  exact linearMapOfEntries_eq_applyKernel _ _
omit F in
theorem applyKernel_blochWave_eq (hw : PeriodicOperators.SymbolOnQuotients.Claim)
    {I I' : PeriodicData} (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) {κ : Fin 4 → ℂ}
    (hF : SymbolSummableAt I I' T κ) (φ : I.UnitQuot → ℂ) (ι' : I'.Carrier) :
    applyKernel T (blochWave I κ φ) ι' =
      Complex.exp (Complex.I * bilinDot κ (toComplexVec (I'.pos ι'))) *
        symbolHom I I' T κ φ (I'.mkQuot 1 ι') := by
  rw [symbolHom_eq_applyKernel hI]
  exact ((hw I I' hI hI' T hT).applyKernel_blochWave κ hF φ ι').2
theorem colourVertices_isPeriodic {j : ℕ} (hj : j ≤ k) : IsPeriodic (colourVertices L k j) :=
  (F.indexSets L F.admissible k j hj).1
theorem colourEdges_isPeriodic {j : ℕ} (hj : j ≤ k) : IsPeriodic (colourEdges L k j) :=
  (F.indexSets L F.admissible k j hj).2.1
theorem R_isPeriodicKernel :
    IsPeriodicKernel (colourVertices L k 0) (colourVertices L k k) (freeOps L k).R :=
  F.maps.vertexAverage.finite_range.1
theorem Q_isPeriodicKernel :
    IsPeriodicKernel (colourEdges L k 0) (colourEdges L k k) (freeOps L k).Q :=
  F.maps.edgeAverage.finite_range.1
theorem R_symbolSummable (κ : Fin 4 → ℂ) :
    SymbolSummableAt (colourVertices L k 0) (colourVertices L k k) (freeOps L k).R κ :=
  (F.strips.2.1 _ _ (colourVertices_isPeriodic F (Nat.zero_le k))
    (colourVertices_isPeriodic F le_rfl)).1.finiteRange _
    F.maps.vertexAverage.finite_range.1 F.maps.vertexAverage.finite_range.2.1 κ (mem_univ κ)
theorem Q_symbolSummable (κ : Fin 4 → ℂ) :
    SymbolSummableAt (colourEdges L k 0) (colourEdges L k k) (freeOps L k).Q κ :=
  (F.strips.2.1 _ _ (colourEdges_isPeriodic F (Nat.zero_le k))
    (colourEdges_isPeriodic F le_rfl)).1.finiteRange _
    F.maps.edgeAverage.finite_range.1 F.maps.edgeAverage.finite_range.2.1 κ (mem_univ κ)
omit F in
theorem sum_pi_single (c : Fin 4 → ℝ) : ∑ μ, (Pi.single μ (c μ) : Fin 4 → ℝ) = c := by
  funext ν
  simp [Finset.sum_apply, Pi.single_apply]
theorem baseVerticesOfCube_eq :
    FullSpace.TrivialLinearization.baseVerticesOfCube L k k 0 =
      cubePoint L k '' (freqBox L k : Set (Fin 4 → ℤ)) := by
  ext x
  constructor
  · rintro ⟨ν, hν, e⟩
    refine ⟨ν, ?_, Subtype.ext ?_⟩
    · exact (mem_freqBox_iff F.admissible ν).2 hν
    · rw [e]
      simp only [ZeroMemClass.coe_zero, zero_add]
      exact (sum_pi_single fun μ => (ν μ : ℝ) * meshAt L k 0).symm
  · rintro ⟨ν, hν, rfl⟩
    refine ⟨ν, (mem_freqBox_iff F.admissible ν).1 hν, ?_⟩
    simp only [ZeroMemClass.coe_zero, zero_add]
    exact (sum_pi_single fun μ => (ν μ : ℝ) * meshAt L k 0).symm
theorem cubePoint_injOn : Set.InjOn (cubePoint L k) (freqBox L k : Set (Fin 4 → ℤ)) := by
  intro ν hν ν' hν' e
  refine (cubePoint_unique F.admissible hν' hν (n := 0) ?_)
  rw [castVec_zero, add_zero, e]
theorem finsum_cube {M : Type*} [AddCommMonoid M] (h : FullSpace.Vertex L k 0 → M) :
    ∑ᶠ x ∈ FullSpace.TrivialLinearization.baseVerticesOfCube L k k 0, h x =
      ∑ ν ∈ freqBox L k, h (cubePoint L k ν) := by
  rw [baseVerticesOfCube_eq F, finsum_mem_image (cubePoint_injOn F), finsum_mem_coe_finset]
theorem topVertexElement_symbolHom (κ : Fin 4 → ℂ) (l : (colourVertices L k 0).UnitQuot → ℂ) :
    topVertexElement L k
        (symbolHom (colourVertices L k 0) (colourVertices L k k) (freeOps L k).R κ l) =
      ((finestMesh L k ^ 4 : ℝ) : ℂ) • ∑ ν ∈ freqBox L k,
        expWave κ (cubePoint L k ν) • vertexFieldOfClasses L k l (cubePoint L k ν) := by
  let f : Fin 3 × FullSpace.Vertex L k 0 → ℂ := blochWave (colourVertices L k 0) κ l
  have e0 : Complex.exp (Complex.I * bilinDot κ
      (toComplexVec ((0 : FullSpace.Vertex L k k) : AmbientSpace))) = 1 := by
    simp [bilinDot, toComplexVec]
  have hw : ∀ a : Fin 3, applyKernel (freeOps L k).R f (a, 0) =
      symbolHom (colourVertices L k 0) (colourVertices L k k) (freeOps L k).R κ l
        ((colourVertices L k k).mkQuot 1 (a, 0)) := fun a => by
    refine (applyKernel_blochWave_eq F.waves (colourVertices_isPeriodic F (Nat.zero_le k))
      (colourVertices_isPeriodic F le_rfl) (R_isPeriodicKernel F) (R_symbolSummable F κ) l
      (a, 0)).trans ?_
    show Complex.exp (Complex.I * bilinDot κ
      (toComplexVec ((0 : FullSpace.Vertex L k k) : AmbientSpace))) * _ = _
    rw [e0, one_mul]
  have hm := F.means.1 (ofPauliCoeffs f) (ofPauliCoeffs_mem f) 0
  rw [toPauliCoeffs_ofPauliCoeffs, finsum_cube F] at hm
  have e₁ : topVertexElement L k
      (symbolHom (colourVertices L k 0) (colourVertices L k k) (freeOps L k).R κ l) =
      ofPauliCoeffs (applyKernel (FullSpace.rescaledOperators L k fun _ => 1).R f) 0 := by
    simp only [topVertexElement, ofPauliCoeffs]
    exact Finset.sum_congr rfl fun a _ => by rw [← hw a]
  rw [e₁, hm, real_smul_eq_complex_smul]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [vertexFieldOfClasses, ofPauliCoeffs, Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun a _ => rfl
theorem R_symbol_formula (κ : Fin 4 → ℂ) (l : (colourVertices L k 0).UnitQuot → ℂ) :
    topVertexElement L k
        (symbolHom (colourVertices L k 0) (colourVertices L k k) (freeOps L k).R κ l) =
      ∑ m ∈ freqBox L k,
        PlaneWaves.vertexWeight L k (shiftedFreq κ m) • vertexFourierCoeff L k l m := by
  rw [topVertexElement_symbolHom F]
  simp_rw [F.vertexCoeffs.exp_expansion κ l]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_smul, smul_smul, sum_expWave_cube]
omit F in
theorem mem_forwardSteps {a : ℝ} (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ)
    (b : InfiniteLattice.Link a) :
    b ∈ FullSpace.forwardSteps x μ n ↔
      ∃ l < n, b = InfiniteLattice.Link.forwardFrom (x + l • InfiniteLattice.axisStep a μ) μ := by apply _root_.YangMills.Construction.Tower.FullSpace.CubesAndPaths.mem_forwardSteps <;> assumption
omit F in
theorem axisPath_eq {a : ℝ} (ha : a ≠ 0) (x x' : InfiniteLattice.LatticePoint a) (μ : Fin 4)
    (n : ℕ) (hn : 0 < n) (h : x' - x = (n : ℤ) • InfiniteLattice.axisStep a μ) :
    FullSpace.axisPath x x' = FullSpace.forwardSteps x μ n := by
  have hex : ∃ q : Fin 4 × ℤ, FullSpace.IsAxisDisplacement x x' q.1 q.2 := ⟨(μ, n), h⟩
  unfold FullSpace.axisPath
  rw [dif_pos hex]
  have hs := hex.choose_spec
  generalize hex.choose = q at hs ⊢
  obtain ⟨μ', n'⟩ := q
  have e : (n' : ℤ) • InfiniteLattice.axisStep a μ' = (n : ℤ) • InfiniteLattice.axisStep a μ := by
    rw [← h]
    exact hs.symm
  have e₁ := congrFun (congrArg Subtype.val e) μ
  simp only [AddSubgroup.coe_zsmul, InfiniteLattice.axisStep, Pi.smul_apply, Pi.single_eq_same,
    zsmul_eq_mul] at e₁
  have hμ : μ' = μ := by
    by_contra hne
    rw [Pi.single_eq_of_ne (Ne.symm hne)] at e₁
    have : (n : ℝ) * a ≠ 0 := mul_ne_zero (by positivity) ha
    simp at e₁
    rcases e₁ with h | h
    · omega
    · exact ha h
  subst hμ
  rw [Pi.single_eq_same] at e₁
  have hn' : n' = n := by
    have : (n' : ℝ) = n := by
      have := mul_right_cancel₀ ha (by simpa using e₁ : (n' : ℝ) * a = (n : ℝ) * a)
      exact this
    exact_mod_cast this
  subst hn'
  simp [FullSpace.signedSteps]
omit F in
theorem reverse_pos_of_not_pos {a : ℝ} {b : InfiniteLattice.Link a}
    (h : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
omit F in
theorem not_pos_reverse {a : ℝ} (ha : 0 < a) {b : InfiniteLattice.Link a}
    (h : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
omit F in
theorem extendOddly_ofCoeffs_pos (c : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ)
    (b : FullSpace.PositiveEdge (meshAt L k 0)) :
    (FullSpace.edgePauliCoordinates L k 0).ofCoeffs c b.1 = ofPauliCoeffs c b := by
  simp only [FullSpace.edgePauliCoordinates, FullSpace.extendOddly, if_pos b.2, dif_pos b.2]
theorem edgePauliCoordinates_ofCoeffs_mem (c : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ) :
    (FullSpace.edgePauliCoordinates L k 0).ofCoeffs c ∈
      (FullSpace.edgePairedSpace (meshAt L k 0)).complexSubmodule := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [extendOddly_ofCoeffs_pos c ⟨b, hb⟩]
    exact sum_smul_pauliFamily_mem _
  · have ha := meshAt_zero_pos (k := k) F.admissible
    by_cases hb : b.IsPositivelyOriented
    · have hr := not_pos_reverse ha hb
      have hrr : b.opposite.opposite.IsPositivelyOriented := hb
      simp only [FullSpace.edgePauliCoordinates, FullSpace.extendOddly, if_neg hr, if_pos hb, dif_pos hb,
        dif_pos hrr]
      rfl
    · have hr := reverse_pos_of_not_pos hb
      simp only [FullSpace.edgePauliCoordinates, FullSpace.extendOddly, if_neg hb, if_pos hr, dif_pos hr,
        neg_neg]
omit F in
theorem toPauliCoeffs_restrict_edgeValue
    (c : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ) :
    toPauliCoeffs (FullSpace.restrictToPositiveEdges ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs c)) =
      c := by
  have : FullSpace.restrictToPositiveEdges ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs c) =
      ofPauliCoeffs c := by
    funext b
    exact extendOddly_ofCoeffs_pos c b
  rw [this, toPauliCoeffs_ofPauliCoeffs]
theorem toFiner_axisStep (μ : Fin 4) :
    FullSpace.toFiner (meshAt L k 0) (InfiniteLattice.axisStep (meshAt L k k) μ) =
      (L ^ k) • InfiniteLattice.axisStep (meshAt L k 0) μ := by
  have hs := meshAt_zero_mul_pow (k := k) F.admissible
  have hval : (((L ^ k) • InfiniteLattice.axisStep (meshAt L k 0) μ :
      InfiniteLattice.LatticePoint (meshAt L k 0)) : AmbientSpace) =
      (InfiniteLattice.axisStep (meshAt L k k) μ : AmbientSpace) := by
    funext ν
    by_cases h : ν = μ
    · subst h
      simp [InfiniteLattice.axisStep, meshAt_self]
      linarith
    · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne h]
  have hex : ∃ x : InfiniteLattice.LatticePoint (meshAt L k 0),
      (x : AmbientSpace) = (InfiniteLattice.axisStep (meshAt L k k) μ : AmbientSpace) := ⟨_, hval⟩
  exact Subtype.ext ((Classical.epsilon_spec hex).trans hval.symm)
theorem crossingPath_eq (x : FullSpace.Vertex L k 0) (μ : Fin 4) :
    FullSpace.crossingPath (posEdgeAt L k k 0 μ).1 x = FullSpace.forwardSteps x μ (L ^ k) := by
  have hpos : 0 < L ^ k := Nat.pow_pos (by have := F.admissible.2; omega)
  refine axisPath_eq (meshAt_zero_pos F.admissible).ne' x _ μ (L ^ k) hpos ?_
  have : (posEdgeAt L k k 0 μ).1.terminal - (posEdgeAt L k k 0 μ).1.initial =
      InfiniteLattice.axisStep (meshAt L k k) μ := by
    simp [posEdgeAt, InfiniteLattice.Link.forwardFrom]
  rw [FullSpace.shifted, this, toFiner_axisStep F, add_sub_cancel_left]
  exact (natCast_zsmul _ _).symm
def axisPoint (L k : ℕ) (ν : Fin 4 → ℤ) (μ : Fin 4) (l : ℕ) : FullSpace.Vertex L k 0 :=
  cubePoint L k ν + l • InfiniteLattice.axisStep (meshAt L k 0) μ
theorem crossingIncidences_eq (μ : Fin 4) :
    FullSpace.RescaledConditions.crossingIncidences L k (posEdgeAt L k k 0 μ).1 =
      (fun p : (Fin 4 → ℤ) × ℕ =>
        ((cubePoint L k p.1, InfiniteLattice.Link.forwardFrom (axisPoint L k p.1 μ p.2) μ) :
          FullSpace.Vertex L k 0 × FullSpace.Edge L k 0)) ''
        ((freqBox L k ×ˢ Finset.range (L ^ k) : Finset _) : Set _) := by
  ext ⟨x, b⟩
  constructor
  · rintro ⟨hx, hb⟩
    have hx' : x ∈ FullSpace.TrivialLinearization.baseVerticesOfCube L k k 0 := hx
    rw [baseVerticesOfCube_eq F] at hx'
    obtain ⟨ν, hν, rfl⟩ := hx'
    have hb' : b ∈ FullSpace.forwardSteps (cubePoint L k ν) μ (L ^ k) := by
      rw [← crossingPath_eq F]
      exact hb
    obtain ⟨l, hl, rfl⟩ := (mem_forwardSteps _ _ _ _).1 hb'
    exact ⟨(ν, l), by simpa using ⟨hν, hl⟩, rfl⟩
  · rintro ⟨⟨ν, l⟩, hp, e⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    have hp' : ν ∈ freqBox L k ∧ l < L ^ k := by simpa using hp
    refine ⟨?_, ?_⟩
    · show cubePoint L k ν ∈ FullSpace.TrivialLinearization.baseVerticesOfCube L k k 0
      rw [baseVerticesOfCube_eq F]
      exact ⟨ν, hp'.1, rfl⟩
    · show _ ∈ FullSpace.crossingPath _ _
      rw [crossingPath_eq F]
      exact (mem_forwardSteps _ _ _ _).2 ⟨l, hp'.2, rfl⟩
theorem crossingIncidences_injOn (μ : Fin 4) :
    Set.InjOn (fun p : (Fin 4 → ℤ) × ℕ =>
        ((cubePoint L k p.1, InfiniteLattice.Link.forwardFrom (axisPoint L k p.1 μ p.2) μ) :
          FullSpace.Vertex L k 0 × FullSpace.Edge L k 0))
      ((freqBox L k ×ˢ Finset.range (L ^ k) : Finset _) : Set _) := by
  rintro ⟨ν, l⟩ hp ⟨ν', l'⟩ hp' e
  have hp₁ : ν ∈ freqBox L k ∧ l < L ^ k := by simpa using hp
  have hp₂ : ν' ∈ freqBox L k ∧ l' < L ^ k := by simpa using hp'
  obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
  have hν : ν = ν' := cubePoint_injOn F hp₁.1 hp₂.1 e₁
  subst hν
  have e₃ : axisPoint L k ν μ l = axisPoint L k ν μ l' :=
    congrArg InfiniteLattice.Link.initial e₂
  have e₄ : l • InfiniteLattice.axisStep (meshAt L k 0) μ =
      l' • InfiniteLattice.axisStep (meshAt L k 0) μ := add_left_cancel e₃
  have e₅ := congrFun (congrArg Subtype.val e₄) μ
  have ha := (meshAt_zero_pos (k := k) F.admissible).ne'
  simp only [AddSubgroup.coe_nsmul, InfiniteLattice.axisStep, Pi.smul_apply, Pi.single_eq_same,
    nsmul_eq_mul] at e₅
  have : l = l' := by exact_mod_cast mul_right_cancel₀ ha e₅
  rw [this]
theorem finsum_crossingIncidences {M : Type*} [AddCommMonoid M] (μ : Fin 4)
    (h : FullSpace.Edge L k 0 → M) :
    ∑ᶠ q ∈ FullSpace.RescaledConditions.crossingIncidences L k (posEdgeAt L k k 0 μ).1, h q.2 =
      ∑ ν ∈ freqBox L k, ∑ l ∈ Finset.range (L ^ k),
        h (InfiniteLattice.Link.forwardFrom (axisPoint L k ν μ l) μ) := by
  rw [crossingIncidences_eq F, finsum_mem_image (crossingIncidences_injOn F μ),
    finsum_mem_coe_finset, Finset.sum_product]
omit F in
theorem expWave_axisPoint (q : Fin 4 → ℂ) (ν : Fin 4 → ℤ) (μ : Fin 4) (l : ℕ) :
    expWave q (axisPoint L k ν μ l) = expWave q (cubePoint L k ν) *
      Complex.exp (Complex.I * meshC L k * (l : ℂ) * q μ) := by
  rw [expWave, expWave, ← Complex.exp_add]
  congr 1
  have : bilinDot q (toComplexVec (axisPoint L k ν μ l : AmbientSpace)) =
      bilinDot q (toComplexVec (cubePoint L k ν : AmbientSpace)) + meshC L k * (l : ℂ) * q μ := by
    simp only [bilinDot, toComplexVec, axisPoint, AddSubgroup.coe_add, AddSubgroup.coe_nsmul,
      Pi.add_apply, InfiniteLattice.axisStep, nsmul_eq_mul]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single μ]
    · simp [meshC, finestMesh]
      ring
    · intro ν' _ h
      simp [Pi.single_eq_of_ne h]
    · simp
  rw [this]
  ring
theorem sum_expWave_axis (q : Fin 4 → ℂ) (μ : Fin 4) :
    ((finestMesh L k ^ 5 : ℝ) : ℂ) * ∑ ν ∈ freqBox L k, ∑ l ∈ Finset.range (L ^ k),
        expWave q (axisPoint L k ν μ l) = edgeWeight L k q μ := by
  simp only [expWave_axisPoint, ← Finset.mul_sum, ← Finset.sum_mul]
  have h₁ := sum_expWave_cube (L := L) (k := k) q
  have h₂ := F.formulas.geom_sum_eq (q μ)
  rw [edgeWeight, ← h₁]
  simp only [meshC, finestMesh] at h₂ ⊢
  push_cast at h₂ ⊢
  linear_combination (meshAt L k 0 : ℂ) ^ 4 *
    (∑ ν ∈ freqBox L k, expWave q (cubePoint L k ν)) * h₂
theorem topEdgeComponent_symbolHom (κ : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ)
    (μ : Fin 4) :
    topEdgeComponent L k
        (symbolHom (colourEdges L k 0) (colourEdges L k k) (freeOps L k).Q κ b) μ =
      ((finestMesh L k ^ 5 : ℝ) : ℂ) • ∑ ν ∈ freqBox L k, ∑ l ∈ Finset.range (L ^ k),
        expWave κ (axisPoint L k ν μ l) •
          edgeFieldOfClasses L k b (edgeAt L k (axisPoint L k ν μ l) μ) := by
  let f : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ := blochWave (colourEdges L k 0) κ b
  have e0 : Complex.exp (Complex.I * bilinDot κ
      (toComplexVec ((0 : FullSpace.Vertex L k k) : AmbientSpace))) = 1 := by
    simp [bilinDot, toComplexVec]
  have hw : ∀ a : Fin 3, applyKernel (freeOps L k).Q f (a, posEdgeAt L k k 0 μ) =
      symbolHom (colourEdges L k 0) (colourEdges L k k) (freeOps L k).Q κ b
        ((colourEdges L k k).mkQuot 1 (a, posEdgeAt L k k 0 μ)) := fun a => by
    refine (applyKernel_blochWave_eq F.waves (colourEdges_isPeriodic F (Nat.zero_le k))
      (colourEdges_isPeriodic F le_rfl) (Q_isPeriodicKernel F) (Q_symbolSummable F κ) b
      (a, posEdgeAt L k k 0 μ)).trans ?_
    show Complex.exp (Complex.I * bilinDot κ
      (toComplexVec ((0 : FullSpace.Vertex L k k) : AmbientSpace))) * _ = _
    rw [e0, one_mul]
  have hm := F.means.2.2.1 ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs f)
    (edgePauliCoordinates_ofCoeffs_mem F f) (posEdgeAt L k k 0 μ)
  rw [toPauliCoeffs_restrict_edgeValue] at hm
  have hsum := finsum_crossingIncidences F μ
    (show FullSpace.Edge L k 0 → ComplexMatrix2 from (FullSpace.edgePauliCoordinates L k 0).ofCoeffs f)
  replace hm := hm.trans (congrArg _ hsum)
  have e₁ : topEdgeComponent L k
      (symbolHom (colourEdges L k 0) (colourEdges L k k) (freeOps L k).Q κ b) μ =
      ofPauliCoeffs (applyKernel (FullSpace.rescaledOperators L k fun _ => 1).Q f)
        (posEdgeAt L k k 0 μ) := by
    simp only [topEdgeComponent, ofPauliCoeffs]
    exact Finset.sum_congr rfl fun a _ => by rw [← hw a]
  rw [e₁, hm, real_smul_eq_complex_smul]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun l _ => ?_
  refine (extendOddly_ofCoeffs_pos f (edgeAt L k (axisPoint L k ν μ l) μ)).trans ?_
  simp only [edgeFieldOfClasses, ofPauliCoeffs, Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun a _ => rfl
theorem Q_symbol_formula (κ : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) :
    topEdgeComponent L k
        (symbolHom (colourEdges L k 0) (colourEdges L k k) (freeOps L k).Q κ b) μ =
      ∑ m ∈ freqBox L k, edgeWeight L k (shiftedFreq κ m) μ • edgeFourierCoeff L k b μ m := by
  rw [topEdgeComponent_symbolHom F]
  simp_rw [F.edgeCoeffs.exp_expansion κ b μ]
  simp_rw [Finset.sum_comm (s := Finset.range (L ^ k))]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp_rw [← Finset.sum_smul]
  rw [smul_smul, sum_expWave_axis F]
omit F in
theorem quotWeight_eq {I : PeriodicData} {w : ℝ} (hw : ∀ ι, I.weightOf ι = w) (c : I.UnitQuot) :
    I.quotWeight 1 c = w := by apply _root_.YangMills.Construction.Tower.PlaneWaveCoboundaries.quotWeight_of_const <;> assumption
omit F in
theorem applyKernel_quotTranspose {I I' : PeriodicData} {w w' : ℝ} (hw : ∀ ι, I.weightOf ι = w)
    (hw' : ∀ ι, I'.weightOf ι = w') (M : I'.UnitQuot → I.UnitQuot → ℂ) (g : I'.UnitQuot → ℂ)
    (c : I.UnitQuot) :
    applyKernel (quotTranspose I I' M) g c = ∑' c', ((w' / w : ℝ) : ℂ) * M c' c * g c' := by
  simp only [applyKernel, quotTranspose, PeriodicOperators.wTranspose, quotWeight_eq hw,
    quotWeight_eq hw']
omit F in
open Classical in
theorem applyKernel_indicator_sum {J J' E : Type} [Finite J] (M : J' → J → ℂ) (S : Finset E)
    (p : E → ℂ) (c : E → J) (c' : J') :
    applyKernel M (fun C => ∑ e ∈ S, p e * if C = c e then 1 else 0) c' =
      ∑ e ∈ S, p e * M c' (c e) := by
  have := Fintype.ofFinite J
  simp only [applyKernel, tsum_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [mul_comm]
theorem fourierPhase_vertexImage (m : Fin 4 → ℤ) (n : Fin 4 → ℤ) (x : FullSpace.Vertex L k 0) :
    fourierPhase m (FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k 0) =
      fourierPhase m x := by
  rw [coe_vertexImage F (Nat.zero_le k)]
  have e : bilinDot (toComplexVec (castVec m)) (toComplexVec ((x : AmbientSpace) + castVec n)) =
      bilinDot (toComplexVec (castVec m)) (toComplexVec (x : AmbientSpace)) +
        ((∑ μ, m μ * n μ : ℤ) : ℂ) := by
    simp only [bilinDot, toComplexVec, castVec, Pi.add_apply]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
  rw [fourierPhase, fourierPhase, e, mul_add, Complex.exp_add]
  have : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ μ, m μ * n μ : ℤ) : ℂ)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-(∑ μ, m μ * n μ))
    rw [← this]
    congr 1
    push_cast
    ring
  rw [this, mul_one]
theorem fourierCoeff_eq_sum (G : FullSpace.Vertex L k 0 → ComplexMatrix2)
    (hper : ∀ n x, G (FullSpace.vertexImage (intShift n) x) = G x) (m : Fin 4 → ℤ) :
    fourierCoeff L k G m = ((finestMesh L k ^ 4 : ℝ) : ℂ) •
      ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) • G (cubePoint L k ν) := by
  rw [PlaneWaves.fourierCoeff]
  congr 1
  exact finsum_vertexClass F (fun x => fourierPhase m (x : AmbientSpace) • G x) fun n x => by
    simp only [hper, fourierPhase_vertexImage F]
omit F in
theorem expWave_mul_fourierPhase (κ : Fin 4 → ℂ) (m : Fin 4 → ℤ) (x : AmbientSpace) :
    expWave (-κ) x * fourierPhase m x = expWave (-shiftedFreq κ m) x := by
  rw [expWave, expWave, fourierPhase, ← Complex.exp_add]
  congr 1
  simp only [bilinDot, toComplexVec, castVec, shiftedFreq, Pi.neg_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  push_cast
  ring
omit F in
theorem vertex_mkQuot_vertexImage {j : ℕ} (a : Fin 3) (n : Fin 4 → ℤ) (x : FullSpace.Vertex L k j) :
    (colourVertices L k j).mkQuot 1 (a, FullSpace.vertexImage (intShift n) x) =
      (colourVertices L k j).mkQuot 1 (a, x) :=
  mkQuot_translate (colourVertices L k j) n (a, x)
omit F in
theorem vertex_mkQuot_inj {a a' : Fin 3} {x x' : FullSpace.Vertex L k 0}
    (e : (colourVertices L k 0).mkQuot 1 (a, x) = (colourVertices L k 0).mkQuot 1 (a', x')) :
    a = a' ∧ (Quot.mk _ x : VertexClass L k) = Quot.mk _ x' := by
  have := eq_of_mkQuot_eq (colourVertices L k 0)
    (fun ι : Fin 3 × FullSpace.Vertex L k 0 => (ι.1, (Quot.mk _ ι.2 : VertexClass L k)))
    (fun n ι => Prod.ext rfl (Quot.sound ⟨n, rfl⟩).symm) e
  exact Prod.mk.inj this
theorem top_vertex_quot_bijective :
    Function.Bijective fun a : Fin 3 => (colourVertices L k k).mkQuot 1 (a, 0) := by
  constructor
  · intro a a' e
    exact eq_of_mkQuot_eq (colourVertices L k k) (fun ι : Fin 3 × FullSpace.Vertex L k k => ι.1)
      (fun _ _ => rfl) e
  · intro c
    obtain ⟨⟨a, y⟩, rfl⟩ := Quot.exists_rep c
    obtain ⟨n, hn⟩ := y.2
    refine ⟨a, ?_⟩
    have : y = FullSpace.vertexImage (intShift n) (0 : FullSpace.Vertex L k k) := Subtype.ext (by
      rw [coe_vertexImage F le_rfl]
      funext μ
      simp [hn μ, castVec, meshAt_self])
    rw [this]
    exact (vertex_mkQuot_vertexImage a n 0).symm
def vertexWave (L k : ℕ) (m : Fin 4 → ℤ) (b : Fin 3) : (colourVertices L k 0).UnitQuot → ℂ :=
  open Classical in fun C => ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) *
    if C = (colourVertices L k 0).mkQuot 1 (b, cubePoint L k ν) then 1 else 0
theorem vertexWave_apply (m : Fin 4 → ℤ) (b b' : Fin 3) (x : FullSpace.Vertex L k 0) :
    vertexWave L k m b ((colourVertices L k 0).mkQuot 1 (b', x)) =
      if b' = b then fourierPhase m x else 0 := by
  classical
  obtain ⟨ν, hν, n, e⟩ := exists_cubePoint F.admissible x
  have hx : x = FullSpace.vertexImage (intShift n) (cubePoint L k ν) := Subtype.ext (by
    rw [coe_vertexImage F (Nat.zero_le k)]
    exact e)
  rw [hx, vertex_mkQuot_vertexImage, fourierPhase_vertexImage F, vertexWave]
  by_cases hb : b' = b
  · subst hb
    rw [if_pos rfl, Finset.sum_eq_single ν]
    · simp
    · intro ν' hν' hne
      rw [if_neg, mul_zero]
      intro e'
      have h₁ := (vertex_mkQuot_inj e').2
      exact hne (congrArg Subtype.val ((vertexClass_bijective F).1
        (a₁ := ⟨ν', hν'⟩) (a₂ := ⟨ν, hν⟩) h₁.symm))
    · exact fun h => absurd hν h
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun ν' _ => ?_
    rw [if_neg, mul_zero]
    exact fun e' => hb (vertex_mkQuot_inj e').1
theorem vertexFieldOfClasses_vertexWave (m : Fin 4 → ℤ) (b : Fin 3) (x : FullSpace.Vertex L k 0) :
    vertexFieldOfClasses L k (vertexWave L k m b) x =
      fourierPhase m x • ComplexMatrix2.pauliFamily b := by
  simp only [vertexFieldOfClasses, ofPauliCoeffs]
  have : ∀ a : Fin 3, vertexWave L k m b ((colourVertices L k 0).mkQuot 1 (a, x)) •
      ComplexMatrix2.pauliFamily a =
      if a = b then fourierPhase m x • ComplexMatrix2.pauliFamily b else 0 := fun a => by
    rw [vertexWave_apply F]
    by_cases h : a = b
    · subst h
      simp
    · simp [h]
  rw [Finset.sum_congr rfl fun a _ => this a]
  simp
omit F in
theorem eq_ite_of_sum_smul_eq {x : Fin 3 → ℂ} {v : ℂ} {b : Fin 3}
    (e : ∑ a, x a • ComplexMatrix2.pauliFamily a = v • ComplexMatrix2.pauliFamily b) (a : Fin 3) :
    x a = if a = b then v else 0 := by
  have e₂ : v • ComplexMatrix2.pauliFamily b =
      ∑ a, (if a = b then v else 0) • ComplexMatrix2.pauliFamily a := by
    simp [ite_smul]
  have := congrArg (pauliCoeff a) (e.trans e₂)
  rwa [pauliCoeff_sum_smul, pauliCoeff_sum_smul] at this
theorem Rt_quotSymbol (κ : Fin 4 → ℂ) :
    quotSymbol (colourVertices L k k) (colourVertices L k 0) (freeOps L k).Rt κ =
      quotTranspose (colourVertices L k 0) (colourVertices L k k)
        (quotSymbol (colourVertices L k 0) (colourVertices L k k) (freeOps L k).R (-κ)) := by
  have h := (F.pointwise _ _ (colourVertices_isPeriodic F (Nat.zero_le k))
    (colourVertices_isPeriodic F le_rfl) _ (-κ)
    (R_isPeriodicKernel F) (R_symbolSummable F (-κ))).2.2.2.2.2.2
  rw [neg_neg] at h
  exact h.2
theorem Rt_symbol_formula (κ : Fin 4 → ℂ)
    (g : (colourVertices L k k).UnitQuot → ℂ) (m : Fin 4 → ℤ) :
    vertexFourierCoeff L k
        (symbolHom (colourVertices L k k) (colourVertices L k 0) (freeOps L k).Rt κ g) m =
      PlaneWaves.vertexWeight L k (-shiftedFreq κ m) • topVertexElement L k g := by
  have hη : finestMesh L k ≠ 0 := (meshAt_zero_pos F.admissible).ne'
  set M := quotSymbol (colourVertices L k 0) (colourVertices L k k) (freeOps L k).R (-κ) with hM
  set f := symbolHom (colourVertices L k k) (colourVertices L k 0) (freeOps L k).Rt κ g with hf
  let C : Fin 3 → (colourVertices L k k).UnitQuot := fun a =>
    (colourVertices L k k).mkQuot 1 (a, 0)
  have hfc : ∀ c, f c = ((finestMesh L k ^ 4 : ℝ) : ℂ)⁻¹ * ∑ a, M (C a) c * g (C a) := fun c => by
    have h₁ : f c = applyKernel
        (quotSymbol (colourVertices L k k) (colourVertices L k 0) (freeOps L k).Rt κ) g c :=
      congrFun (symbolHom_eq_applyKernel (colourVertices_isPeriodic F le_rfl) _ κ g) c
    refine h₁.trans ((congrFun (congrArg (fun A => applyKernel A g) (Rt_quotSymbol F κ)) c).trans
      ((applyKernel_quotTranspose (w := meshAt L k 0 ^ 4) (w' := meshAt L k k ^ 4)
        (fun _ => rfl) (fun _ => rfl) M g c).trans ?_))
    rw [← (Equiv.ofBijective _ (top_vertex_quot_bijective F)).tsum_eq, tsum_fintype,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Equiv.ofBijective_apply, meshAt_self, finestMesh]
    push_cast
    simp only [one_pow, one_div, C]
    ring
  have hact : ∀ a b, ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) *
      M (C a) ((colourVertices L k 0).mkQuot 1 (b, cubePoint L k ν)) =
      if a = b then PlaneWaves.vertexWeight L k (-shiftedFreq κ m) else 0 := fun a b => by
    have hfin := (colourVertices_isPeriodic F (Nat.zero_le k) (L := L) (k := k)).finite_quot
    have h₁ : ∀ a', applyKernel M (vertexWave L k m b) (C a') =
        ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) *
          M (C a') ((colourVertices L k 0).mkQuot 1 (b, cubePoint L k ν)) := fun a' =>
      applyKernel_indicator_sum M (freqBox L k) (fun ν => fourierPhase m (cubePoint L k ν))
        (fun ν => (colourVertices L k 0).mkQuot 1 (b, cubePoint L k ν)) (C a')
    have h₂ := topVertexElement_symbolHom F (-κ) (vertexWave L k m b)
    have h₃ : topVertexElement L k
        (symbolHom (colourVertices L k 0) (colourVertices L k k) (freeOps L k).R (-κ)
          (vertexWave L k m b)) =
          ∑ a', applyKernel M (vertexWave L k m b) (C a') • ComplexMatrix2.pauliFamily a' := by
      exact (congrArg (topVertexElement L k)
        (symbolHom_eq_applyKernel (colourVertices_isPeriodic F (Nat.zero_le k)) _ (-κ)
          (vertexWave L k m b))).trans rfl
    have h₄ : ((finestMesh L k ^ 4 : ℝ) : ℂ) • ∑ ν ∈ freqBox L k,
        expWave (-κ) (cubePoint L k ν) •
          vertexFieldOfClasses L k (vertexWave L k m b) (cubePoint L k ν) =
        PlaneWaves.vertexWeight L k (-shiftedFreq κ m) • ComplexMatrix2.pauliFamily b := by
      simp_rw [vertexFieldOfClasses_vertexWave F, smul_smul, expWave_mul_fourierPhase]
      rw [← Finset.sum_smul, smul_smul, sum_expWave_cube]
    have h₅ := eq_ite_of_sum_smul_eq (h₃.symm.trans (h₂.trans h₄)) a
    rw [h₁ a] at h₅
    exact h₅
  have hper : ∀ n x, vertexFieldOfClasses L k f (FullSpace.vertexImage (intShift n) x) =
      vertexFieldOfClasses L k f x := fun n x => by
    simp only [vertexFieldOfClasses, ofPauliCoeffs, vertex_mkQuot_vertexImage]
  have hη' : ((finestMesh L k ^ 4 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 4 hη
  rw [vertexFourierCoeff, fourierCoeff_eq_sum F _ hper]
  have hsum : ∀ b, ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) *
      f ((colourVertices L k 0).mkQuot 1 (b, cubePoint L k ν)) =
      ((finestMesh L k ^ 4 : ℝ) : ℂ)⁻¹ *
        (PlaneWaves.vertexWeight L k (-shiftedFreq κ m) * g (C b)) := fun b => by
    simp only [hfc, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ a, ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) *
        (((finestMesh L k ^ 4 : ℝ) : ℂ)⁻¹ *
          (M (C a) ((colourVertices L k 0).mkQuot 1 (b, cubePoint L k ν)) * g (C a))) =
        ((finestMesh L k ^ 4 : ℝ) : ℂ)⁻¹ * (g (C a) *
          if a = b then PlaneWaves.vertexWeight L k (-shiftedFreq κ m) else 0) := fun a => by
      rw [← hact a b, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ν _ => by ring
    rw [Finset.sum_congr rfl fun a _ => this a]
    simp [mul_comm]
  have e₁ : ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) •
      vertexFieldOfClasses L k f (cubePoint L k ν) =
      ∑ b, (∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) *
        f ((colourVertices L k 0).mkQuot 1 (b, cubePoint L k ν))) •
          ComplexMatrix2.pauliFamily b := by
    simp only [vertexFieldOfClasses, ofPauliCoeffs, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [e₁]
  simp only [hsum, topVertexElement, ofPauliCoeffs, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  field_simp
  rfl
omit F in
theorem posEdge_eq_posEdgeAt {j : ℕ} (b : PeriodicOperators.PosEdge L k j) :
    ∃ μ, b = posEdgeAt L k j b.1.initial μ := by apply _root_.YangMills.Construction.Tower.FreeSandwiches.exists_eq_posEdgeAt <;> assumption
omit F in
theorem terminal_sub_initial {j : ℕ} (x : FullSpace.Vertex L k j) (μ : Fin 4) :
    (posEdgeAt L k j x μ).1.terminal - (posEdgeAt L k j x μ).1.initial =
      InfiniteLattice.axisStep (meshAt L k j) μ := by
  simp [posEdgeAt, InfiniteLattice.Link.forwardFrom]
omit F in
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {μ μ' : Fin 4}
    (e : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a μ') : μ = μ' := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
theorem edge_translate {j : ℕ} (hj : j ≤ k) (a : Fin 3) (n : Fin 4 → ℤ)
    (x : FullSpace.Vertex L k j) (μ : Fin 4) :
    (colourEdges L k j).translate n (a, posEdgeAt L k j x μ) =
      (a, posEdgeAt L k j (FullSpace.vertexImage (intShift n) x) μ) :=
  (F.translations L F.admissible k j F.one_le hj n).2.2.2.1 a (posEdgeAt L k j x μ) μ
    (terminal_sub_initial x μ)
theorem edge_mkQuot_vertexImage {j : ℕ} (hj : j ≤ k) (a : Fin 3) (n : Fin 4 → ℤ)
    (x : FullSpace.Vertex L k j) (μ : Fin 4) :
    (colourEdges L k j).mkQuot 1 (a, posEdgeAt L k j (FullSpace.vertexImage (intShift n) x) μ) =
      (colourEdges L k j).mkQuot 1 (a, posEdgeAt L k j x μ) := by
  rw [← edge_translate F hj]
  exact mkQuot_translate _ n _
theorem edge_mkQuot_inj {a a' : Fin 3} {y y' : FullSpace.Vertex L k 0} {μ μ' : Fin 4}
    (e : (colourEdges L k 0).mkQuot 1 (a, posEdgeAt L k 0 y μ) =
      (colourEdges L k 0).mkQuot 1 (a', posEdgeAt L k 0 y' μ')) :
    a = a' ∧ μ = μ' ∧ (Quot.mk _ y : VertexClass L k) = Quot.mk _ y' := by
  have h := eq_of_mkQuot_eq (colourEdges L k 0)
    (fun ι : Fin 3 × PeriodicOperators.PosEdge L k 0 =>
      (ι.1, ι.2.1.terminal - ι.2.1.initial, (Quot.mk _ ι.2.1.initial : VertexClass L k)))
    (fun n ι => by
      obtain ⟨c, b⟩ := ι
      obtain ⟨μ₀, hb⟩ := posEdge_eq_posEdgeAt b
      rw [hb, edge_translate F (Nat.zero_le k)]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · exact (terminal_sub_initial _ μ₀).trans (terminal_sub_initial _ μ₀).symm
      · exact (Quot.sound ⟨n, rfl⟩).symm) e
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  obtain ⟨h₂, h₃⟩ := Prod.mk.inj h₂
  refine ⟨h₁, axisStep_injective (a := meshAt L k 0) (meshAt_zero_pos F.admissible).ne' ?_, h₃⟩
  exact (terminal_sub_initial y μ).symm.trans (h₂.trans (terminal_sub_initial y' μ'))
theorem top_edge_quot_bijective :
    Function.Bijective fun p : Fin 3 × Fin 4 =>
      (colourEdges L k k).mkQuot 1 (p.1, posEdgeAt L k k 0 p.2) := by
  constructor
  · rintro ⟨a, μ⟩ ⟨a', μ'⟩ e
    have h := eq_of_mkQuot_eq (colourEdges L k k)
      (fun ι : Fin 3 × PeriodicOperators.PosEdge L k k => (ι.1, ι.2.1.terminal - ι.2.1.initial))
      (fun n ι => by
        obtain ⟨c, b⟩ := ι
        obtain ⟨μ₀, hb⟩ := posEdge_eq_posEdgeAt b
        rw [hb, edge_translate F le_rfl]
        exact Prod.ext rfl ((terminal_sub_initial _ μ₀).trans (terminal_sub_initial _ μ₀).symm)) e
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    have h₃ : μ = μ' := axisStep_injective (a := meshAt L k k) (by simp [meshAt_self])
      ((terminal_sub_initial 0 μ).symm.trans (h₂.trans (terminal_sub_initial 0 μ')))
    exact Prod.ext h₁ h₃
  · intro c
    obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep c
    obtain ⟨μ, hb⟩ := posEdge_eq_posEdgeAt b
    obtain ⟨n, hn⟩ := b.1.initial.2
    refine ⟨(a, μ), ?_⟩
    have : b.1.initial = FullSpace.vertexImage (intShift n) (0 : FullSpace.Vertex L k k) :=
      Subtype.ext (by
        rw [coe_vertexImage F le_rfl]
        funext ν
        simp [hn ν, castVec, meshAt_self])
    show _ = (colourEdges L k k).mkQuot 1 (a, b)
    rw [hb, this]
    exact (edge_mkQuot_vertexImage F le_rfl a n 0 μ).symm
def edgeWave (L k : ℕ) (m : Fin 4 → ℤ) (b : Fin 3) (μ : Fin 4) :
    (colourEdges L k 0).UnitQuot → ℂ :=
  open Classical in fun C => ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) *
    if C = (colourEdges L k 0).mkQuot 1 (b, posEdgeAt L k 0 (cubePoint L k ν) μ) then 1
    else 0
theorem edgeWave_apply (m : Fin 4 → ℤ) (b b' : Fin 3) (μ μ' : Fin 4)
    (x : FullSpace.Vertex L k 0) :
    edgeWave L k m b μ ((colourEdges L k 0).mkQuot 1 (b', posEdgeAt L k 0 x μ')) =
      if b' = b ∧ μ' = μ then fourierPhase m x else 0 := by
  classical
  obtain ⟨ν, hν, n, e⟩ := exists_cubePoint F.admissible x
  have hx : x = FullSpace.vertexImage (intShift n) (cubePoint L k ν) := Subtype.ext (by
    rw [coe_vertexImage F (Nat.zero_le k)]
    exact e)
  rw [hx, edge_mkQuot_vertexImage F (Nat.zero_le k), fourierPhase_vertexImage F, edgeWave]
  by_cases hb : b' = b ∧ μ' = μ
  · obtain ⟨rfl, rfl⟩ := hb
    rw [if_pos ⟨rfl, rfl⟩, Finset.sum_eq_single ν]
    · simp
    · intro ν' hν' hne
      rw [if_neg, mul_zero]
      intro e'
      have h₁ := (edge_mkQuot_inj F e').2.2
      exact hne (congrArg Subtype.val ((vertexClass_bijective F).1
        (a₁ := ⟨ν', hν'⟩) (a₂ := ⟨ν, hν⟩) h₁.symm))
    · exact fun h => absurd hν h
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun ν' _ => ?_
    rw [if_neg, mul_zero]
    exact fun e' => hb ⟨(edge_mkQuot_inj F e').1, (edge_mkQuot_inj F e').2.1⟩
theorem edgeFieldOfClasses_edgeWave (m : Fin 4 → ℤ) (b : Fin 3) (μ μ' : Fin 4)
    (x : FullSpace.Vertex L k 0) :
    edgeFieldOfClasses L k (edgeWave L k m b μ) (edgeAt L k x μ') =
      (if μ' = μ then fourierPhase m x else 0) • ComplexMatrix2.pauliFamily b := by
  simp only [edgeFieldOfClasses, ofPauliCoeffs]
  have : ∀ a : Fin 3, edgeWave L k m b μ ((colourEdges L k 0).mkQuot 1 (a, edgeAt L k x μ')) •
      ComplexMatrix2.pauliFamily a =
      if a = b then (if μ' = μ then fourierPhase m x else 0) • ComplexMatrix2.pauliFamily b
      else 0 :=
    fun a => by
      have e := edgeWave_apply F m b a μ μ' x
      have e' : edgeWave L k m b μ ((colourEdges L k 0).mkQuot 1 (a, edgeAt L k x μ')) =
          if a = b ∧ μ' = μ then fourierPhase m x else 0 := e
      rw [e']
      by_cases h : a = b
      · subst h
        simp
      · simp [h]
  rw [Finset.sum_congr rfl fun a _ => this a]
  simp
theorem Qt_quotSymbol (κ : Fin 4 → ℂ) :
    quotSymbol (colourEdges L k k) (colourEdges L k 0) (freeOps L k).Qt κ =
      quotTranspose (colourEdges L k 0) (colourEdges L k k)
        (quotSymbol (colourEdges L k 0) (colourEdges L k k) (freeOps L k).Q (-κ)) := by
  have h := (F.pointwise _ _ (colourEdges_isPeriodic F (Nat.zero_le k))
    (colourEdges_isPeriodic F le_rfl) _ (-κ)
    (Q_isPeriodicKernel F) (Q_symbolSummable F (-κ))).2.2.2.2.2.2
  rw [neg_neg] at h
  exact h.2
theorem Qt_symbol_formula (κ : Fin 4 → ℂ)
    (z : (colourEdges L k k).UnitQuot → ℂ) (μ : Fin 4) (m : Fin 4 → ℤ) :
    edgeFourierCoeff L k
        (symbolHom (colourEdges L k k) (colourEdges L k 0) (freeOps L k).Qt κ z) μ m =
      edgeWeight L k (-shiftedFreq κ m) μ • topEdgeComponent L k z μ := by
  have hη : finestMesh L k ≠ 0 := (meshAt_zero_pos F.admissible).ne'
  set M := quotSymbol (colourEdges L k 0) (colourEdges L k k) (freeOps L k).Q (-κ) with hM
  set f := symbolHom (colourEdges L k k) (colourEdges L k 0) (freeOps L k).Qt κ z with hf
  let C : Fin 3 × Fin 4 → (colourEdges L k k).UnitQuot := fun p =>
    (colourEdges L k k).mkQuot 1 (p.1, posEdgeAt L k k 0 p.2)
  let c : Fin 3 → (Fin 4 → ℤ) → (colourEdges L k 0).UnitQuot := fun b ν =>
    (colourEdges L k 0).mkQuot 1 (b, posEdgeAt L k 0 (cubePoint L k ν) μ)
  have hfc : ∀ c', f c' = ((finestMesh L k ^ 4 : ℝ) : ℂ)⁻¹ * ∑ p, M (C p) c' * z (C p) :=
    fun c' => by
      have h₁ : f c' = applyKernel
          (quotSymbol (colourEdges L k k) (colourEdges L k 0) (freeOps L k).Qt κ) z c' :=
        congrFun (symbolHom_eq_applyKernel (colourEdges_isPeriodic F le_rfl) _ κ z) c'
      refine h₁.trans ((congrFun (congrArg (fun A => applyKernel A z) (Qt_quotSymbol F κ)) c').trans
        ((applyKernel_quotTranspose (w := meshAt L k 0 ^ 4) (w' := meshAt L k k ^ 4)
          (fun _ => rfl) (fun _ => rfl) M z c').trans ?_))
      rw [← (Equiv.ofBijective _ (top_edge_quot_bijective F)).tsum_eq, tsum_fintype,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [Equiv.ofBijective_apply, meshAt_self, finestMesh]
      push_cast
      simp only [one_pow, one_div, C]
      ring
  have hact : ∀ p b, ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) * M (C p) (c b ν) =
      if p.1 = b then (if p.2 = μ then edgeWeight L k (-shiftedFreq κ m) μ else 0) else 0 :=
    fun p b => by
      have hfin := (colourEdges_isPeriodic F (Nat.zero_le k) (L := L) (k := k)).finite_quot
      have h₁ : ∀ a', applyKernel M (edgeWave L k m b μ) (C (a', p.2)) =
          ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) * M (C (a', p.2)) (c b ν) :=
        fun a' =>
          applyKernel_indicator_sum M (freqBox L k) (fun ν => fourierPhase m (cubePoint L k ν))
            (fun ν => c b ν) (C (a', p.2))
      have h₂ := topEdgeComponent_symbolHom F (-κ) (edgeWave L k m b μ) p.2
      have h₃ : topEdgeComponent L k
          (symbolHom (colourEdges L k 0) (colourEdges L k k) (freeOps L k).Q (-κ)
            (edgeWave L k m b μ)) p.2 =
          ∑ a', applyKernel M (edgeWave L k m b μ) (C (a', p.2)) • ComplexMatrix2.pauliFamily a' :=
        (congrArg (fun h => topEdgeComponent L k h p.2)
          (symbolHom_eq_applyKernel (colourEdges_isPeriodic F (Nat.zero_le k)) _ (-κ)
            (edgeWave L k m b μ))).trans rfl
      have h₄ : ((finestMesh L k ^ 5 : ℝ) : ℂ) • ∑ ν ∈ freqBox L k,
          ∑ l ∈ Finset.range (L ^ k), expWave (-κ) (axisPoint L k ν p.2 l) •
            edgeFieldOfClasses L k (edgeWave L k m b μ) (edgeAt L k (axisPoint L k ν p.2 l) p.2) =
          (if p.2 = μ then edgeWeight L k (-shiftedFreq κ m) μ else 0) •
            ComplexMatrix2.pauliFamily b := by
        by_cases hp : p.2 = μ
        · simp_rw [edgeFieldOfClasses_edgeWave F, if_pos hp, smul_smul, expWave_mul_fourierPhase]
          rw [hp]
          simp_rw [← Finset.sum_smul]
          rw [smul_smul, sum_expWave_axis F]
        · simp_rw [edgeFieldOfClasses_edgeWave F, if_neg hp]
          simp
      have h₅ := eq_ite_of_sum_smul_eq (h₃.symm.trans (h₂.trans h₄)) p.1
      rw [h₁ p.1] at h₅
      exact h₅
  have hper : ∀ n x, edgeFieldOfClasses L k f (edgeAt L k (FullSpace.vertexImage (intShift n) x) μ) =
      edgeFieldOfClasses L k f (edgeAt L k x μ) := fun n x => by
    simp only [edgeFieldOfClasses, ofPauliCoeffs]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e : (colourEdges L k 0).mkQuot 1
        (a, edgeAt L k (FullSpace.vertexImage (intShift n) x) μ) =
        (colourEdges L k 0).mkQuot 1 (a, edgeAt L k x μ) :=
      edge_mkQuot_vertexImage F (Nat.zero_le k) a n x μ
    rw [e]
  rw [edgeFourierCoeff, fourierCoeff_eq_sum F _ hper]
  have hsum : ∀ b, ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) * f (c b ν) =
      ((finestMesh L k ^ 4 : ℝ) : ℂ)⁻¹ *
        (edgeWeight L k (-shiftedFreq κ m) μ * z (C (b, μ))) := fun b => by
    simp only [hfc, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ p, ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) *
        (((finestMesh L k ^ 4 : ℝ) : ℂ)⁻¹ * (M (C p) (c b ν) * z (C p))) =
        ((finestMesh L k ^ 4 : ℝ) : ℂ)⁻¹ * (z (C p) *
          if p.1 = b then (if p.2 = μ then edgeWeight L k (-shiftedFreq κ m) μ else 0)
          else 0) := fun p => by
      rw [← hact p b, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ν _ => by ring
    rw [Finset.sum_congr rfl fun p _ => this p, ← Finset.mul_sum, Fintype.sum_prod_type]
    simp [mul_comm]
  have e₁ : ∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) •
      edgeFieldOfClasses L k f (edgeAt L k (cubePoint L k ν) μ) =
      ∑ b, (∑ ν ∈ freqBox L k, fourierPhase m (cubePoint L k ν) * f (c b ν)) •
        ComplexMatrix2.pauliFamily b := by
    simp only [edgeFieldOfClasses, ofPauliCoeffs, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hη' : ((finestMesh L k ^ 4 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 4 hη
  rw [e₁]
  simp only [hsum, topEdgeComponent, ofPauliCoeffs, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  field_simp
  rfl
end PlaneWaveSmoothingSymbols
namespace PlaneWaveSmoothingSymbols
theorem smoothingSymbolsHold_of
    (hTranslations : PeriodicOperators.TowerTranslations.Claim)
    (hIndexSets : PeriodicOperators.TowerIndexSets.Claim)
    (hWaves : PeriodicOperators.SymbolOnQuotients.Claim)
    (hStrips : PeriodicOperators.StripSymbols.Claim)
    (hPoint : PeriodicOperators.SymbolPointwise.Properties)
    (hMeans : FullSpace.TrivialFieldMeansCondition)
    (hFree : FreeOperators.FreeOperatorsArePeriodic)
    (hSites : PlaneWaveCalculus.VertexCoeffsHold)
    (hBonds : PlaneWaveEdgeCoefficientsHold)
    (hFormulas : PlaneWaveSymbolFormulas.Holds) :
    SmoothingSymbolsHold := by
  intro L hL k hk
  have F : Hypotheses L k :=
    ⟨hL, hk, hTranslations, hIndexSets, hWaves, hStrips, hPoint, hMeans L hL k hk,
      (hFree.2 L hL k hk).1, hSites L hL k hk, hBonds L hL k hk, hFormulas L hL k hk⟩
  exact ⟨R_symbol_formula F, Q_symbol_formula F,
    fun κ g m _ => Rt_symbol_formula F κ g m,
    fun κ z μ m _ => Qt_symbol_formula F κ z μ m⟩
end PlaneWaveSmoothingSymbols
end YangMills.Construction.Tower
end
