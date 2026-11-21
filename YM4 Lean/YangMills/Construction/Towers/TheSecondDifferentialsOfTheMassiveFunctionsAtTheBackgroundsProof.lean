import YangMills.Construction.Towers.TheBackgroundFieldAsASumOfWaves
import YangMills.Construction.Towers.TheDilationOfAWaveOfTheThirdColourProof
import YangMills.Construction.Towers.ThePolarisationOfTheMassiveFamilyBySecondDifferentials
import YangMills.Construction.Towers.TheSecondDifferentialsOfTheMassiveFunctionsAtTheBackgrounds
import YangMills.Construction.Towers.TheSecondDifferentialsOfTheMassiveFunctionsUnderTheDilation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.BackgroundHessians
open PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs
open Scaling
open FullSpace.BackgroundJets
section Large
variable {L : ℕ}
theorem torusSide_le_torusSide_iff (hL : 2 ≤ L) {i j : ℕ} :
    PeriodicLattice.torusSide L i ≤ PeriodicLattice.torusSide L j ↔ i ≤ j := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.torusSide_le_iff <;> assumption
theorem exists_forall_ge_of_eventuallyForSides (hL : 2 ≤ L) {P : ℕ → Prop}
    (h : PeriodicOperators.Tempered.EventuallyForSides L P) :
    ∃ j₀, ∀ j, j₀ ≤ j → P j := by
  obtain ⟨s₀, ⟨i, hi0, hi⟩, h⟩ := h
  refine ⟨i, fun j hj => ?_⟩
  have hj0 : 0 < j := lt_of_lt_of_le hi0 hj
  refine h (PeriodicLattice.torusSide L j) ⟨j, hj0, rfl⟩ ?_ j hj0 rfl
  rw [hi]
  exact (torusSide_le_torusSide_iff hL).2 hj
theorem eventuallyForSides_of_forall_ge (hL : 2 ≤ L) {P : ℕ → Prop} {j₀ : ℕ}
    (h : ∀ j, j₀ ≤ j → P j) :
    PeriodicOperators.Tempered.EventuallyForSides L P := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.eventuallyForSides_of_forall_ge <;> assumption
end Large
theorem descendField_mkQuot {F : PeriodicData} {s : ℕ} {f : F.Carrier → ℂ}
    (h : ∀ (v : Fin 4 → ℤ) x, f (F.translate (s • v) x) = f x) (x : F.Carrier) :
    descendField F s f (F.mkQuot s x) = f x := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.ThirdColourScaling.descendField_mkQuot <;> assumption
section Lattice
variable {a : ℝ} {N : ℕ}
def intPoint (h : a * N = 1) (v : Fin 4 → ℤ) : InfiniteLattice.LatticePoint a :=
  ⟨castVec v, fun μ => v μ * N, fun μ => by
    have e : ((v μ * (N : ℤ) : ℤ) : ℝ) * a = (v μ : ℝ) * (a * N) := by
      push_cast
      ring
    rw [e, h, mul_one]
    rfl⟩
theorem vertexImage_intShift (h : a * N = 1) (v : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a) :
    FullSpace.vertexImage (intShift v) x = x + intPoint h v :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun y : InfiniteLattice.LatticePoint a =>
      (y : InfiniteLattice.AmbientSpace) = intShift v x)
    ⟨x + intPoint h v, rfl⟩ |>.trans rfl)
theorem edgeImage_intShift_ends (h : a * N = 1) (v : Fin 4 → ℤ) (b : InfiniteLattice.Link a) :
    (FullSpace.edgeImage (intShift v) b).initial = b.initial + intPoint h v ∧
      (FullSpace.edgeImage (intShift v) b).terminal = b.terminal + intPoint h v := by
  have spec := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a =>
      b'.initial = FullSpace.vertexImage (intShift v) b.initial ∧
        b'.terminal = FullSpace.vertexImage (intShift v) b.terminal)
    ⟨⟨FullSpace.vertexImage (intShift v) b.initial, FullSpace.vertexImage (intShift v) b.terminal, by
      obtain ⟨μ, hμ⟩ := b.isAdjacent
      refine ⟨μ, ?_⟩
      rw [vertexImage_intShift h, vertexImage_intShift h, add_sub_add_right_eq_sub]
      exact hμ⟩, rfl, rfl⟩
  have spec' : (FullSpace.edgeImage (intShift v) b).initial =
        FullSpace.vertexImage (intShift v) b.initial ∧
      (FullSpace.edgeImage (intShift v) b).terminal =
        FullSpace.vertexImage (intShift v) b.terminal := spec
  rw [vertexImage_intShift h, vertexImage_intShift h] at spec'
  exact spec'
variable {L k j : ℕ}
theorem shiftEdge_ends (h : meshAt L k j * N = 1) (v : Fin 4 → ℤ)
    (b : PeriodicOperators.PosEdge L k j) :
    (shiftEdge v b).1.initial = b.1.initial + intPoint h v ∧
      (shiftEdge v b).1.terminal = b.1.terminal + intPoint h v := by
  have spec := Classical.epsilon_spec
    (p := fun b' : PeriodicOperators.PosEdge L k j => b'.1 = FullSpace.edgeImage (intShift v) b.1)
    ⟨⟨FullSpace.edgeImage (intShift v) b.1, by
      obtain ⟨μ, hμ⟩ := b.2
      refine ⟨μ, ?_⟩
      rw [(edgeImage_intShift_ends h v b.1).1, (edgeImage_intShift_ends h v b.1).2,
        add_sub_add_right_eq_sub]
      exact hμ⟩, rfl⟩
  have spec' : (shiftEdge v b).1 = FullSpace.edgeImage (intShift v) b.1 := spec
  rw [spec']
  exact edgeImage_intShift_ends h v b.1
theorem meshAt_mul_pow (hL : 0 < L) (k : ℕ) : meshAt L k 0 * ((L ^ k : ℕ) : ℝ) = 1 := by
  have e := pow_mul_meshAt hL (Nat.zero_le k) 0
  have e₀ : meshAt L 0 0 = 1 := by simp [meshAt]
  rw [e₀, Nat.sub_zero] at e
  push_cast
  rw [mul_comm]
  exact e
theorem meshAt_zero_mul_one : meshAt L 0 0 * ((1 : ℕ) : ℝ) = 1 := by simp [meshAt]
theorem scaleVertex_intPoint (hL : 0 < L) (v : Fin 4 → ℤ) :
    FullSpace.scaleVertex hL (Nat.zero_le k) 0 (intPoint (meshAt_mul_pow hL k) v) =
      intPoint (meshAt_zero_mul_one (L := L)) (L ^ k • v) :=
  Subtype.ext (by
    rw [FullSpace.coe_scaleVertex, FullSpace.scaling_apply]
    funext μ
    simp [intPoint, castVec])
theorem scaleEdgeIndex_translate (hL : 0 < L) (k : ℕ) (v : Fin 4 → ℤ)
    (x : (colourEdges L k 0).Carrier) :
    scaleEdgeIndex hL k ((colourEdges L k 0).translate v x) =
      (colourEdges L 0 0).translate (L ^ k • v) (scaleEdgeIndex hL k x) := by
  obtain ⟨c, b⟩ : Fin 3 × PeriodicOperators.PosEdge L k 0 := x
  change (c, scalePosEdge hL k (shiftEdge v b)) =
    (c, shiftEdge (L ^ k • v) (scalePosEdge hL k b))
  refine Prod.ext rfl (Subtype.ext (InfiniteLattice.Link.ext ?_ ?_))
  · change FullSpace.scaleVertex hL (Nat.zero_le k) 0 (shiftEdge v b).1.initial = _
    rw [(shiftEdge_ends (meshAt_mul_pow hL k) v b).1,
      (shiftEdge_ends (meshAt_zero_mul_one (L := L)) _ _).1, map_add, scaleVertex_intPoint]
    rfl
  · change FullSpace.scaleVertex hL (Nat.zero_le k) 0 (shiftEdge v b).1.terminal = _
    rw [(shiftEdge_ends (meshAt_mul_pow hL k) v b).2,
      (shiftEdge_ends (meshAt_zero_mul_one (L := L)) _ _).2, map_add, scaleVertex_intPoint]
    rfl
theorem scaleEdgeIndex_symm_translate (hL : 0 < L) (k : ℕ) (v : Fin 4 → ℤ)
    (y : (colourEdges L 0 0).Carrier) :
    (scaleEdgeIndex hL k).symm ((colourEdges L 0 0).translate (L ^ k • v) y) =
      (colourEdges L k 0).translate v ((scaleEdgeIndex hL k).symm y) := by
  apply (scaleEdgeIndex hL k).injective
  rw [scaleEdgeIndex_translate, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
theorem scaledQuotField_mkQuot (hL : 0 < L) (k n : ℕ)
    (ζ : (colourEdges L k 0).QuotMod (2 * L ^ n) → ℂ) (y : (colourEdges L 0 0).Carrier) :
    scaledQuotField hL k n ζ ((colourEdges L 0 0).mkQuot (2 * L ^ (n + k)) y) =
      ζ ((colourEdges L k 0).mkQuot (2 * L ^ n) ((scaleEdgeIndex hL k).symm y)) := by
  refine (descendField_mkQuot
    (f := scaledField hL k (liftQuotField (colourEdges L k 0) (2 * L ^ n) ζ)) ?_ y).trans rfl
  intro u y'
  have e : (2 * L ^ (n + k)) • u = L ^ k • (2 * L ^ n) • u := by
    rw [← mul_smul]
    congr 1
    ring
  change ζ ((colourEdges L k 0).mkQuot (2 * L ^ n)
      ((scaleEdgeIndex hL k).symm ((colourEdges L 0 0).translate _ y'))) =
    ζ ((colourEdges L k 0).mkQuot (2 * L ^ n) ((scaleEdgeIndex hL k).symm y'))
  rw [e, scaleEdgeIndex_symm_translate]
  exact congrArg ζ (Quot.sound ⟨u, rfl⟩).symm
end Lattice
section Momenta
variable {L : ℕ}
theorem bilinDot_dualLattice_castVec {s : ℕ} (hs : s ≠ 0) {q : InfiniteLattice.AmbientSpace}
    (hq : q ∈ dualLattice s) (u : Fin 4 → ℤ) :
    ∃ t : ℤ, bilinDot (toComplexVec q) (toComplexVec (castVec (s • u))) =
      (t : ℂ) * (2 * Real.pi) := by
  have hq' : ∃ j : Fin 4 → ℤ, ∀ μ, q μ = (j μ : ℝ) * (2 * Real.pi / s) := hq
  obtain ⟨j, hj⟩ := hq'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  refine ⟨∑ μ, j μ * u μ, ?_⟩
  simp only [bilinDot, toComplexVec, castVec, hj]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Pi.smul_apply, nsmul_eq_mul]
  push_cast
  field_simp
theorem shiftedMomentum_mem {s : ℕ} (hs : s ≠ 0) {p : InfiniteLattice.AmbientSpace}
    (hp : p ∈ dualLattice s) (m : Fin 4 → ℤ) : shiftedMomentum p m ∈ dualLattice s := by
  have hp' : ∃ j : Fin 4 → ℤ, ∀ μ, p μ = (j μ : ℝ) * (2 * Real.pi / s) := hp
  obtain ⟨j, hj⟩ := hp'
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
  refine ⟨fun μ => j μ + s * m μ, fun μ => ?_⟩
  simp only [shiftedMomentum, hj]
  push_cast
  field_simp
theorem finestMesh_mul_pow (hL : 0 < L) (k : ℕ) : finestMesh L k * (L : ℝ) ^ k = 1 := by
  have e := meshAt_mul_pow hL k
  push_cast at e
  exact e
theorem finestMesh_smul_mem (hL : 0 < L) (k n : ℕ) {q : InfiniteLattice.AmbientSpace}
    (hq : q ∈ dualLattice (2 * L ^ n)) : finestMesh L k • q ∈ dualLattice (2 * L ^ (n + k)) := by
  have hq' : ∃ j : Fin 4 → ℤ, ∀ μ, q μ = (j μ : ℝ) * (2 * Real.pi / ((2 * L ^ n : ℕ) : ℝ)) := hq
  obtain ⟨j, hj⟩ := hq'
  have hη : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := eq_inv_of_mul_eq_one_left (finestMesh_mul_pow hL k)
  refine ⟨j, fun μ => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hj, hη]
  push_cast
  rw [pow_add]
  field_simp
theorem scaled_add_not_mem_periodLattice (hL : 0 < L) {k : ℕ} (p : InfiniteLattice.AmbientSpace)
    {m m' : Fin 4 → ℤ} (hm : m ∈ PlaneWaves.freqBox L k) (hm' : m' ∈ PlaneWaves.freqBox L k)
    (hne : m' ≠ -m) :
    finestMesh L k • shiftedMomentum p m + finestMesh L k • shiftedMomentum (-p) m' ∉
      RiemannSums.periodLattice := by
  have hη : 0 < finestMesh L k := by
    have e := finestMesh_mul_pow hL k
    have hp : 0 < (L : ℝ) ^ k := by positivity
    by_contra h
    have : finestMesh L k * (L : ℝ) ^ k ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) hp.le
    linarith
  intro hmem
  have hmem' : ∃ t : Fin 4 → ℤ, ∀ μ,
      (finestMesh L k • shiftedMomentum p m + finestMesh L k • shiftedMomentum (-p) m') μ =
        (t μ : ℝ) * (2 * Real.pi) := hmem
  obtain ⟨t, ht⟩ := hmem'
  obtain ⟨ν, hν⟩ : ∃ ν, m' ν ≠ -m ν := by
    by_contra h
    exact hne (funext fun ν => by_contra fun hν => h ⟨ν, hν⟩)
  have e := ht ν
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, shiftedMomentum, Pi.neg_apply] at e
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have e' : finestMesh L k * ((m ν : ℝ) + (m' ν : ℝ)) = (t ν : ℝ) := by
    apply mul_right_cancel₀ hpi
    linear_combination e
  have b₁ := (PlaneWaves.mem_freqBox L k m).1 hm ν
  have b₂ := (PlaneWaves.mem_freqBox L k m').1 hm' ν
  have hinv : finestMesh L k * (finestMesh L k)⁻¹ = 1 := mul_inv_cancel₀ hη.ne'
  have hb : |(m ν : ℝ) + (m' ν : ℝ)| ≤ (finestMesh L k)⁻¹ - 1 := by
    refine (abs_add_le _ _).trans ?_
    linarith
  have habs : |(t ν : ℝ)| < 1 := by
    rw [← e', abs_mul, abs_of_pos hη]
    have := mul_le_mul_of_nonneg_left hb hη.le
    rw [mul_sub, hinv, mul_one] at this
    linarith
  have ht0 : t ν = 0 := by
    have : |t ν| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.1 this
  rw [ht0] at e'
  have hz : (m ν : ℝ) + (m' ν : ℝ) = 0 := by
    have := e'
    simp only [Int.cast_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hη.ne'
  apply hν
  have : m ν + m' ν = 0 := by exact_mod_cast hz
  omega
end Momenta
section Waves
variable {L : ℕ}
open Classical in
theorem thirdColourWave_translate (hL : 0 < L) (k : ℕ) {s : ℕ} (hs : s ≠ 0)
    {q : InfiniteLattice.AmbientSpace} (hq : q ∈ dualLattice s) (ρ : Fin 4) (u : Fin 4 → ℤ)
    (x : (colourEdges L k 0).Carrier) :
    thirdColourWave L k q ρ ((colourEdges L k 0).translate (s • u) x) =
      thirdColourWave L k q ρ x := by
  obtain ⟨c, b⟩ : Fin 3 × PeriodicOperators.PosEdge L k 0 := x
  obtain ⟨ht, hh⟩ := shiftEdge_ends (meshAt_mul_pow hL k) (s • u) b
  have hd : (shiftEdge (s • u) b).1.terminal - (shiftEdge (s • u) b).1.initial =
      b.1.terminal - b.1.initial := by
    rw [ht, hh, add_sub_add_right_eq_sub]
  have hpos : ((shiftEdge (s • u) b).1.initial : InfiniteLattice.AmbientSpace) =
      (b.1.initial : InfiniteLattice.AmbientSpace) + castVec (s • u) := by
    rw [ht]
    rfl
  obtain ⟨t, htt⟩ := bilinDot_dualLattice_castVec hs hq u
  have hdot : bilinDot (toComplexVec q) (toComplexVec
        ((b.1.initial : InfiniteLattice.AmbientSpace) + castVec (s • u))) =
      bilinDot (toComplexVec q) (toComplexVec (b.1.initial : InfiniteLattice.AmbientSpace)) +
        (t : ℂ) * (2 * Real.pi) := by
    rw [← htt]
    simp only [bilinDot, toComplexVec, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    push_cast
    ring
  have hphase : Complex.exp (Complex.I * bilinDot (toComplexVec q) (toComplexVec
        ((shiftEdge (s • u) b).1.initial : InfiniteLattice.AmbientSpace))) =
      Complex.exp (Complex.I * bilinDot (toComplexVec q)
        (toComplexVec (b.1.initial : InfiniteLattice.AmbientSpace))) := by
    rw [hpos, hdot, mul_add, Complex.exp_add]
    have e : Complex.I * ((t : ℂ) * (2 * Real.pi)) = (t : ℂ) * (2 * Real.pi * Complex.I) := by ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  change (if c = 2 ∧ (shiftEdge (s • u) b).1.terminal - (shiftEdge (s • u) b).1.initial =
        InfiniteLattice.axisStep (meshAt L k 0) ρ then
      Complex.exp (Complex.I * bilinDot (toComplexVec q) (toComplexVec
        ((shiftEdge (s • u) b).1.initial : InfiniteLattice.AmbientSpace)))
    else 0) = (if c = 2 ∧ b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k 0) ρ then
      Complex.exp (Complex.I * bilinDot (toComplexVec q)
        (toComplexVec (b.1.initial : InfiniteLattice.AmbientSpace)))
    else 0)
  simp only [hd, hphase]
end Waves
section EvaluationMaps
open LocalKernels LocalKernels.Periodisation
variable {L n : ℕ}
theorem pauliCoeff_linComb {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless)
    (c d : ℂ) (i : Fin 3) :
    pauliCoeff i (c • X + d • Y) = c * pauliCoeff i X + d * pauliCoeff i Y := by apply _root_.YangMills.Construction.Tower.LeftChartAlgebra.FiniteFaceDerivatives.pauliCoeff_linearCombination <;> assumption
theorem remainderQuotField_mkQuot (hc : ProjCellsClassified L n 0 0)
    (B : Edge L n 0 0 → Matrices.ComplexMatrix2) (y : (colourEdges L 0 0).Carrier) :
    remainderQuotField B ((colourEdges L 0 0).mkQuot (2 * L ^ n) y) = remainderCoeffs B y := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.remainderQuotField_mkQuot <;> assumption
theorem remainderCoeffs_linComb {B B' : Edge L n 0 0 → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) (hB' : B' ∈ complexEdgeForms L n 0 0) (c d : ℂ)
    (y : (colourEdges L 0 0).Carrier) :
    remainderCoeffs (c • B + d • B') y = c * remainderCoeffs B y + d * remainderCoeffs B' y := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.remainderCoeffs_add_smul <;> assumption
theorem remainderCoeffs_sum {α : Type*} (t : Finset α) (c : α → ℂ)
    (B : α → Edge L n 0 0 → Matrices.ComplexMatrix2) (hB : ∀ i ∈ t, B i ∈ complexEdgeForms L n 0 0)
    (y : (colourEdges L 0 0).Carrier) :
    remainderCoeffs (∑ i ∈ t, c i • B i) y = ∑ i ∈ t, c i * remainderCoeffs (B i) y := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h := pauliCoeff_linComb Matrices.ComplexMatrix2.traceless.zero_mem
      Matrices.ComplexMatrix2.traceless.zero_mem 1 1 y.1
    simp only [smul_zero, add_zero, one_mul] at h
    have hz : pauliCoeff y.1 (0 : Matrices.ComplexMatrix2) = 0 := by linear_combination -h
    simp only [Finset.sum_empty]
    exact hz
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hS : ∑ j ∈ t, c j • B j ∈ complexEdgeForms L n 0 0 :=
      Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hB j (Finset.mem_insert_of_mem hj))
    have h := remainderCoeffs_linComb (hB i (Finset.mem_insert_self _ _)) hS (c i) 1 y
    rw [one_smul, one_mul] at h
    rw [h, ih fun j hj => hB j (Finset.mem_insert_of_mem hj)]
theorem remainderQuotField_sum (hc : ProjCellsClassified L n 0 0) {α : Type*} (t : Finset α)
    (c : α → ℂ) (B : α → Edge L n 0 0 → Matrices.ComplexMatrix2)
    (hB : ∀ i ∈ t, B i ∈ complexEdgeForms L n 0 0) (y : (colourEdges L 0 0).Carrier) :
    remainderQuotField (∑ i ∈ t, c i • B i) ((colourEdges L 0 0).mkQuot (2 * L ^ n) y) =
      ∑ i ∈ t, c i * remainderQuotField (B i) ((colourEdges L 0 0).mkQuot (2 * L ^ n) y) := by
  simp only [remainderQuotField_mkQuot hc]
  exact remainderCoeffs_sum t c B hB y
end EvaluationMaps
section Sums
variable {L n : ℕ} {F : PeriodicOperators.Tempered.FieldFamily L}
theorem complexHessian_sum_left (H : OneLoopLaw.ComplexHessianOfMember.Properties F n) {α : Type*}
    (t : Finset α) (c : α → ℂ) (B : α → Edge L n 0 0 → Matrices.ComplexMatrix2)
    (hB : ∀ i ∈ t, B i ∈ complexEdgeForms L n 0 0) {B' : Edge L n 0 0 → Matrices.ComplexMatrix2}
    (hB' : B' ∈ complexEdgeForms L n 0 0) :
    PeriodicOperators.Tempered.complexHessian F n (∑ i ∈ t, c i • B i) B' =
      ∑ i ∈ t, c i * PeriodicOperators.Tempered.complexHessian F n (B i) B' := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h := H.linear_left 1 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) B' hB'
    rw [one_smul, add_zero, one_mul] at h
    simp only [Finset.sum_empty]
    linear_combination -h
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hS : ∑ j ∈ t, c j • B j ∈ complexEdgeForms L n 0 0 :=
      Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hB j (Finset.mem_insert_of_mem hj))
    rw [H.linear_left (c i) _ (hB i (Finset.mem_insert_self _ _)) _ hS B' hB',
      ih fun j hj => hB j (Finset.mem_insert_of_mem hj)]
theorem complexHessian_sum_right (H : OneLoopLaw.ComplexHessianOfMember.Properties F n) {α : Type*}
    (t : Finset α) (c : α → ℂ) (B : α → Edge L n 0 0 → Matrices.ComplexMatrix2)
    (hB : ∀ i ∈ t, B i ∈ complexEdgeForms L n 0 0) {B' : Edge L n 0 0 → Matrices.ComplexMatrix2}
    (hB' : B' ∈ complexEdgeForms L n 0 0) :
    PeriodicOperators.Tempered.complexHessian F n B' (∑ i ∈ t, c i • B i) =
      ∑ i ∈ t, c i * PeriodicOperators.Tempered.complexHessian F n B' (B i) := by
  have hS : ∑ j ∈ t, c j • B j ∈ complexEdgeForms L n 0 0 :=
    Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hB j hj)
  rw [H.symm _ hB' _ hS, complexHessian_sum_left H t c B hB hB']
  exact Finset.sum_congr rfl fun i hi => by rw [H.symm _ (hB i hi) _ hB']
end Sums
section Backgrounds
variable {L : ℕ}
abbrev modeIndices (L k : ℕ) : Finset ((Fin 4 → ℤ) × Fin 4) :=
  PlaneWaves.freqBox L k ×ˢ Finset.univ
abbrev scaledBackgroundCoeff (L k : ℕ) (w : Fin 4 → ℂ) (μ : Fin 4) (i : (Fin 4 → ℤ) × Fin 4) : ℂ :=
  ((finestMesh L k : ℝ) : ℂ) * backgroundCoeff L k w μ i.2 i.1
abbrev scaledFourierMode (L k n : ℕ) (p : InfiniteLattice.AmbientSpace) (i : (Fin 4 → ℤ) × Fin 4) :
    Edge L (n + k) 0 0 → Matrices.ComplexMatrix2 :=
  PeriodicOperators.Tempered.fourierModeForm L (n + k) 2 (finestMesh L k • shiftedMomentum p i.1) i.2
theorem scaledQuotField_backgroundMode (hB : Conventions.IsAdmissibleBlockingFactor L) (hL : 0 < L)
    {k n : ℕ} (hk : 1 ≤ k) (hn : 0 < n) (hWave : WaveExpansion.BackgroundFieldWaveSum)
    (hDW : ThirdColourScaling.ScaledThirdColourWaveIsFourierMode)
    (hc : LocalKernels.Periodisation.ProjCellsClassified L (n + k) 0 0)
    (hmem : ∀ q ∈ dualLattice (2 * L ^ (n + k)), ∀ ρ : Fin 4,
      PeriodicOperators.Tempered.fourierModeForm L (n + k) 2 q ρ ∈ complexEdgeForms L (n + k) 0 0)
    {p : InfiniteLattice.AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n))
    (hpw : toComplexVec p ∈ momentumPolydisc stripHalfWidth) (μ : Fin 4) :
    scaledQuotField hL k n (backgroundModeOnQuotient L k n (toComplexVec p) μ) =
      remainderQuotField (k := 0) (∑ i ∈ modeIndices L k,
        scaledBackgroundCoeff L k (toComplexVec p) μ i • scaledFourierMode L k n p i) := by
  have hs : 2 * L ^ n ≠ 0 := by positivity
  have hexp := hWave L hB k hk p hpw μ
  have hF : ∀ (u : Fin 4 → ℤ) (x : (colourEdges L k 0).Carrier),
      blochWave (colourEdges L k 0) (toComplexVec p) (scaledResponseField L k (toComplexVec p) μ)
          ((colourEdges L k 0).translate ((2 * L ^ n) • u) x) =
        blochWave (colourEdges L k 0) (toComplexVec p)
          (scaledResponseField L k (toComplexVec p) μ) x := by
    intro u x
    rw [hexp, hexp]
    congr 1
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun ρ _ => ?_
    rw [thirdColourWave_translate hL k hs (shiftedMomentum_mem hs hp m) ρ u x]
  funext z
  obtain ⟨y, rfl⟩ := Quot.exists_rep z
  change scaledQuotField hL k n _ ((colourEdges L 0 0).mkQuot (2 * L ^ (n + k)) y) =
    remainderQuotField _ ((colourEdges L 0 0).mkQuot (2 * L ^ (n + k)) y)
  rw [scaledQuotField_mkQuot, remainderQuotField_sum hc _ _ _
    (fun i _ => hmem _ (finestMesh_smul_mem hL k n (shiftedMomentum_mem hs hp i.1)) i.2)]
  have hterm : ∀ i : (Fin 4 → ℤ) × Fin 4,
      remainderQuotField (scaledFourierMode L k n p i)
          ((colourEdges L 0 0).mkQuot (2 * L ^ (n + k)) y) =
        thirdColourWave L k (shiftedMomentum p i.1) i.2 ((scaleEdgeIndex hL k).symm y) := by
    intro i
    rw [scaledFourierMode, ← hDW L hL hB k hk n hn _ (shiftedMomentum_mem hs hp i.1) i.2,
      scaledQuotField_mkQuot,
      descendField_mkQuot (thirdColourWave_translate hL k hs (shiftedMomentum_mem hs hp i.1) i.2)]
  simp only [hterm]
  simp only [backgroundModeOnQuotient]
  rw [descendField_mkQuot hF, hexp, Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  dsimp only
  ring
end Backgrounds
theorem hessianRelation (hD : ScaledSecondDerivs.ScalingInvariance)
    (hPol : HessianBySecondDerivs.HessianIdentity)
    (hWave : WaveExpansion.BackgroundFieldWaveSum)
    (hDW : ThirdColourScaling.ScaledThirdColourWaveIsFourierMode)
    (hT : MassiveOpFunctions.Tempered.MassiveFamilyTempered)
    (hG : OneLoopLaw.GaugeColourMomenta.GaugeColourMomentumClaim)
    (hM : OneLoopLaw.ComplexHessianOfMember.Statement)
    (hPW : OneLoopLaw.PlaneWaveSymmetries.PlaneWaveLawsHold)
    (hC : LocalKernels.PeriodicLiftCells.CellsAndClassesHold) : HessianRelation := by
  intro L hB k hk z hz
  have hL2 : 2 ≤ L := by
    have := hB.2
    omega
  have hL : 0 < L := by omega
  have hη : 0 < finestMesh L k := by
    simp only [finestMesh, meshAt]
    exact zpow_pos (by exact_mod_cast hL) _
  have hw : 0 < finestMesh L k ^ 2 * z := by positivity
  have hfun := (hT L hB _ hw).1.1
  obtain ⟨n₁, h₁⟩ := exists_forall_ge_of_eventuallyForSides hL2 (hD L hL hB k hk z hz)
  obtain ⟨n₂, h₂⟩ := exists_forall_ge_of_eventuallyForSides hL2 (hPol L hB _ hw)
  obtain ⟨n₃, h₃⟩ := exists_forall_ge_of_eventuallyForSides hL2 hfun
  obtain ⟨n₄, h₄⟩ := exists_forall_ge_of_eventuallyForSides hL2 ((hG L hL hB).1 _ hfun)
  refine eventuallyForSides_of_forall_ge hL2 (j₀ := n₁ + n₂ + n₃ + n₄ + 1) ?_
  intro n hn N e p hp hpw μPlus μMinus
  have hn0 : 0 < n := by omega
  have hn' : 0 < n + k := by omega
  have hs : 2 * L ^ n ≠ 0 := by positivity
  have hc := ((hC L hB 0 (n + k) hn').1 0 le_rfl).1
  have facts := hM L (n + k) hB hn' _ (h₃ (n + k) (by omega))
  have off := (h₄ (n + k) (by omega)).2.2.2.2
  have pw : ∀ q ∈ dualLattice (2 * L ^ (n + k)), ∀ ρ : Fin 4,
      PeriodicOperators.Tempered.fourierModeForm L (n + k) 2 q ρ ∈ complexEdgeForms L (n + k) 0 0 :=
    fun q hq ρ => (hPW L (n + k) hB hn').mem_complex 2 ρ q hq
  obtain ⟨e', he'⟩ := h₁ n (by omega) N e
  have hneg : -toComplexVec p = toComplexVec (-p) := by
    funext μ
    simp [toComplexVec]
  have hp' : -p ∈ dualLattice (2 * L ^ n) := neg_mem hp
  have hpw' : toComplexVec (-p) ∈ momentumPolydisc stripHalfWidth := by
    rw [← hneg]
    intro μ
    simpa using hpw μ
  have wmem : ∀ (r : InfiniteLattice.AmbientSpace), r ∈ dualLattice (2 * L ^ n) →
      ∀ i : (Fin 4 → ℤ) × Fin 4, scaledFourierMode L k n r i ∈ complexEdgeForms L (n + k) 0 0 :=
    fun r hr i => pw _ (finestMesh_smul_mem hL k n (shiftedMomentum_mem hs hr i.1)) i.2
  have fmem : ∀ (r : InfiniteLattice.AmbientSpace), r ∈ dualLattice (2 * L ^ n) →
      ∀ (w : Fin 4 → ℂ) (μ : Fin 4),
      ∑ i ∈ modeIndices L k, scaledBackgroundCoeff L k w μ i • scaledFourierMode L k n r i ∈
        complexEdgeForms L (n + k) 0 0 :=
    fun r hr w μ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (wmem r hr i)
  rw [hneg]
  obtain ⟨a₁, a₂⟩ := he' (backgroundModeOnQuotient L k n (toComplexVec p) μPlus)
    (backgroundModeOnQuotient L k n (toComplexVec (-p)) μMinus)
  rw [a₁, a₂, scaledQuotField_backgroundMode hB hL hk hn0 hWave hDW hc pw hp hpw,
    scaledQuotField_backgroundMode hB hL hk hn0 hWave hDW hc pw hp' hpw',
    ← h₂ (n + k) (by omega) N e' _ (fmem p hp _ _) _ (fmem (-p) hp' _ _),
    complexHessian_sum_left facts _ _ _ (fun i _ => wmem p hp i) (fmem (-p) hp' _ _),
    Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [complexHessian_sum_right facts _ _ _ (fun i _ => wmem (-p) hp' i) (wmem p hp (m, ρ)),
    Finset.sum_product]
  have hnegm : -m ∈ PlaneWaves.freqBox L k := by
    rw [PlaneWaves.mem_freqBox] at hm ⊢
    intro ν
    simpa using hm ν
  have hzero : ∀ m' ∈ PlaneWaves.freqBox L k, m' ≠ -m →
      ∑ σ : Fin 4, scaledBackgroundCoeff L k (toComplexVec (-p)) μMinus (m', σ) *
        PeriodicOperators.Tempered.complexHessian (massiveFieldFamily L (finestMesh L k ^ 2 * z))
          (n + k) (scaledFourierMode L k n p (m, ρ)) (scaledFourierMode L k n (-p) (m', σ)) = 0 := by
    intro m' hm' hne
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [off 2 2 ρ σ _ (finestMesh_smul_mem hL k n (shiftedMomentum_mem hs hp m)) _
      (finestMesh_smul_mem hL k n (shiftedMomentum_mem hs hp' m'))
      (scaled_add_not_mem_periodLattice hL p hm hm' hne), mul_zero]
  rw [Finset.sum_eq_single_of_mem (-m) hnegm hzero]
  have hq : finestMesh L k • shiftedMomentum (-p) (-m) =
      -(finestMesh L k • shiftedMomentum p m) := by
    funext μ
    simp only [shiftedMomentum, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    push_cast
    ring
  simp only [scaledFourierMode, scaledBackgroundCoeff, hq]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring
end YangMills.Construction.Tower.MassiveOpFunctions.BackgroundHessians
end
