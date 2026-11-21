import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfG
import YangMills.Construction.Matrices.SpecialUnitaryScalarVectorParts
import YangMills.Construction.Lattice.BondsWithinSiteSets
import YangMills.Construction.Lattice.CommutationOfTheDifferenceWithTheLaplaciansProof
import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposes
import YangMills.Construction.Lattice.MatrixValuedFormOperators
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.Matrices YangMills.Construction.Matrices.ComplexMatrix2
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.LieInnerProductProof
theorem halfTracePairing_eq_entries (X Y : ComplexMatrix2) : halfTracePairing X Y =
    (1 / 2 : ℂ) * (X 0 0 * Y 0 0 + X 0 1 * Y 1 0 + (X 1 0 * Y 0 1 + X 1 1 * Y 1 1)) := by
  change (1 / 2 : ℂ) * Matrix.trace (X * Y) = _
  rw [Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
theorem halfTracePairing_comm (X Y : ComplexMatrix2) :
    halfTracePairing X Y = halfTracePairing Y X := by
  rw [halfTracePairing_eq_entries, halfTracePairing_eq_entries]; ring
theorem halfTracePairing_add_left (X X' Y : ComplexMatrix2) :
    halfTracePairing (X + X') Y = halfTracePairing X Y + halfTracePairing X' Y := by
  simp only [halfTracePairing_eq_entries, Matrix.add_apply]; ring
theorem halfTracePairing_smul_left (c : ℂ) (X Y : ComplexMatrix2) :
    halfTracePairing (c • X) Y = c * halfTracePairing X Y := by
  simp only [halfTracePairing_eq_entries, Matrix.smul_apply, smul_eq_mul]; ring
theorem halfTracePairing_zero_left (Y : ComplexMatrix2) : halfTracePairing 0 Y = 0 := by
  simp [halfTracePairing_eq_entries]
theorem entry_one_one_of_mem_traceless {Y : ComplexMatrix2} (h : Y ∈ traceless) :
    Y 1 1 = -Y 0 0 := by
  have h' : fullTrace Y = 0 := h
  rw [fullTrace, Matrix.trace_fin_two] at h'
  linear_combination h'
theorem pauliCombination_eq_matrix (y : Fin 3 → ℂ) :
    pauliCombination y = !![y 2, y 0 - Complex.I * y 1; y 0 + Complex.I * y 1, -y 2] := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.sum_smul_pauliFamily <;> assumption
theorem pauli_zero_eq : pauli 0 = !![0, 1; 1, 0] := rfl
theorem pauli_one_eq : pauli 1 = !![0, -Complex.I; Complex.I, 0] := rfl
theorem pauli_two_eq : pauli 2 = !![1, 0; 0, -1] := rfl
theorem halfTracePairing_pauli_pauliCombination (a : Fin 3) (y : Fin 3 → ℂ) :
    halfTracePairing (pauli a) (pauliCombination y) = y a := by
  rw [halfTracePairing_eq_entries, pauliCombination_eq_matrix]
  fin_cases a
  · simp [pauli_zero_eq]; ring
  · simp [pauli_one_eq]
    linear_combination (-(y 1)) * Complex.I_sq
  · simp [pauli_two_eq]; ring
theorem halfTracePairing_pauliCombination (y y' : Fin 3 → ℂ) :
    halfTracePairing (pauliCombination y) (pauliCombination y') = ∑ a, y a * y' a := by
  rw [halfTracePairing_eq_entries, pauliCombination_eq_matrix, pauliCombination_eq_matrix,
    Fin.sum_univ_three]
  simp
  linear_combination (-(y 1 * y' 1)) * Complex.I_sq
theorem eq_pauliCombination_of_mem_traceless {Y : ComplexMatrix2} (h : Y ∈ traceless) :
    Y = pauliCombination fun a => halfTracePairing (pauli a) Y := by
  have h11 := entry_one_one_of_mem_traceless h
  rw [pauliCombination_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [halfTracePairing_eq_entries, pauli_two_eq, h11]; ring
  · simp [halfTracePairing_eq_entries, pauli_zero_eq, pauli_one_eq]
    linear_combination ((Y 0 1 - Y 1 0) / 2) * Complex.I_sq
  · simp [halfTracePairing_eq_entries, pauli_zero_eq, pauli_one_eq]
    linear_combination (-(Y 0 1 - Y 1 0) / 2) * Complex.I_sq
  · simp [halfTracePairing_eq_entries, pauli_two_eq, h11]; ring
theorem pauliCombination_mem_traceless (y : Fin 3 → ℂ) : pauliCombination y ∈ traceless := by
  have : fullTrace (pauliCombination y) = 0 := by
    rw [pauliCombination_eq_matrix, fullTrace, Matrix.trace_fin_two]; simp
  exact this
theorem pauliCombination_injective {y y' : Fin 3 → ℂ}
    (h : pauliCombination y = pauliCombination y') : y = y' := by
  funext a
  rw [← halfTracePairing_pauli_pauliCombination a y, h, halfTracePairing_pauli_pauliCombination]
theorem conjTranspose_pauliCombination (y : Fin 3 → ℂ) :
    (pauliCombination y).conjTranspose = pauliCombination fun a => star (y a) := by
  rw [pauliCombination_eq_matrix, pauliCombination_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring
theorem pauliCombination_mem_hermitianTraceless_iff (y : Fin 3 → ℂ) :
    pauliCombination y ∈ hermitianTraceless ↔ ∀ a, (y a).im = 0 := by
  constructor
  · rintro ⟨h, -⟩
    rw [conjTranspose_pauliCombination] at h
    have := pauliCombination_injective h
    intro a
    exact Complex.conj_eq_iff_im.mp (congrFun this a).symm
  · intro h
    refine ⟨?_, pauliCombination_mem_traceless y⟩
    rw [conjTranspose_pauliCombination]
    congr 1
    funext a
    exact (Complex.conj_eq_iff_im.mpr (h a)).symm
theorem halfTrace_conjTranspose_mul_pauliCombination (y : Fin 3 → ℂ) :
    halfTrace ((pauliCombination y).conjTranspose * pauliCombination y) =
      ((∑ a, ‖y a‖ ^ 2 : ℝ) : ℂ) := by
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj z).symm
  rw [conjTranspose_pauliCombination, pauliCombination_eq_matrix, pauliCombination_eq_matrix]
  push_cast [Fin.sum_univ_three]
  simp only [← Complex.ofReal_pow, hn]
  simp [halfTrace, fullTrace, Matrix.trace_fin_two]
  linear_combination (-((starRingEnd ℂ) (y 1) * y 1)) * Complex.I_sq
theorem pauli_mem_hermitianTraceless (a : Fin 3) : pauli a ∈ hermitianTraceless := by apply _root_.YangMills.Construction.Matrices.PowerExpCharts.pauliFamily_mem_hermitianTraceless <;> assumption
theorem sq_eq_smul_one_of_mem_traceless {Y : ComplexMatrix2} (h : Y ∈ traceless) :
    Y ^ 2 = halfTracePairing Y Y • (1 : ComplexMatrix2) := by
  have h11 := entry_one_one_of_mem_traceless h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, halfTracePairing_eq_entries, Matrix.mul_apply, Fin.sum_univ_two, h11] <;> ring
theorem halfTracePairing_self_of_mem_hermitianTraceless {Y : ComplexMatrix2}
    (h : Y ∈ hermitianTraceless) :
    halfTracePairing Y Y = ((operatorNorm Y ^ 2 : ℝ) : ℂ) := by
  have hc : ∃ r : ℝ, 0 ≤ r ∧ halfTracePairing Y Y = (r : ℂ) := by
    refine ⟨(1 / 2) * ∑ i, ∑ j, ‖Y i j‖ ^ 2, by positivity, ?_⟩
    have : fullTrace (Y * Y) = ((∑ i, ∑ j, ‖Y i j‖ ^ 2 : ℝ) : ℂ) :=
      LieElement.fullTrace_mul_self (⟨Y, h⟩ : hermitianTraceless)
    change (1 / 2 : ℂ) * fullTrace (Y * Y) = _
    rw [this]
    push_cast
    ring
  obtain ⟨r, hr, hc⟩ := hc
  have hcs : Y.conjTranspose * Y = (r : ℂ) • (1 : ComplexMatrix2) := by
    rw [← h.1, ← pow_two, sq_eq_smul_one_of_mem_traceless h.2, hc]
  have hn : ‖Y‖ * ‖Y‖ = r := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hcs, norm_smul, norm_one, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  rw [hc, ← hn]
  simp [operatorNorm, pow_two]
theorem realInnerProduct_holds : LieInnerProduct.RealInnerProduct := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX Y hY
    have := LieElement.star_fullTrace_mul (⟨X, hX⟩ : hermitianTraceless)
      (⟨Y, hY⟩ : hermitianTraceless)
    change star (fullTrace (X * Y)) = fullTrace (X * Y) at this
    have h2 := Complex.conj_eq_iff_im.mp this
    change ((1 / 2 : ℂ) * fullTrace (X * Y)).im = 0
    simp [Complex.mul_im, h2]
  · intro Y hY
    refine ⟨?_, sq_eq_smul_one_of_mem_traceless hY.2,
      (halfTracePairing_self_of_mem_hermitianTraceless hY).symm⟩
    rw [← hY.1, pow_two]
  · intro X Y
    have him : (halfTracePairing X.toMatrix Y.toMatrix).im = 0 := by
      have := LieElement.star_fullTrace_mul X Y
      have h2 := Complex.conj_eq_iff_im.mp this
      change ((1 / 2 : ℂ) * fullTrace (X.toMatrix * Y.toMatrix)).im = 0
      simp [Complex.mul_im, h2]
    have hre : inner ℝ X Y = (halfTracePairing X.toMatrix Y.toMatrix).re := rfl
    rw [hre]
    exact Complex.ext (by simp) (by simp [him])
  · intro Y
    have h1 : ‖Y‖ ^ 2 = (halfTracePairing Y.toMatrix Y.toMatrix).re := by
      rw [← real_inner_self_eq_norm_sq]; rfl
    have h2 := halfTracePairing_self_of_mem_hermitianTraceless Y.2
    have h3 : halfTracePairing Y.toMatrix Y.toMatrix =
        ((operatorNorm Y.toMatrix ^ 2 : ℝ) : ℂ) := h2
    rw [h3, Complex.ofReal_re] at h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
theorem pauliExpansion_holds : LieInnerProduct.PauliExpansion := by
  refine ⟨fun Y hY => ⟨⟨_, eq_pauliCombination_of_mem_traceless hY, ?_⟩,
      eq_pauliCombination_of_mem_traceless hY⟩,
    pauliCombination_mem_traceless, pauliCombination_mem_hermitianTraceless_iff,
    halfTracePairing_pauliCombination, halfTrace_conjTranspose_mul_pauliCombination⟩
  intro y hy
  exact pauliCombination_injective (hy.symm.trans (eq_pauliCombination_of_mem_traceless hY))
section FiniteSets
variable {S S' : Type*}
theorem scaledPairingSum_eq_sum [Fintype S] (t : ℝ) (f f' : BondMaps.BondValued S) :
    scaledPairingSum t f f' =
      (t : ℂ) * ∑ s, halfTracePairing (f s : ComplexMatrix2) (f' s : ComplexMatrix2) := by
  rw [scaledPairingSum, finsum_eq_sum_of_fintype]
theorem scaledPairingSum_comm [Finite S] (t : ℝ) (f f' : BondMaps.BondValued S) :
    scaledPairingSum t f f' = scaledPairingSum t f' f := by
  cases nonempty_fintype S
  rw [scaledPairingSum_eq_sum, scaledPairingSum_eq_sum]
  congr 1
  exact Finset.sum_congr rfl fun s _ => halfTracePairing_comm _ _
theorem scaledPairingSum_add_left [Finite S] (t : ℝ) (f g h : BondMaps.BondValued S) :
    scaledPairingSum t (f + g) h = scaledPairingSum t f h + scaledPairingSum t g h := by
  cases nonempty_fintype S
  simp only [scaledPairingSum_eq_sum, Pi.add_apply, Submodule.coe_add, halfTracePairing_add_left,
    Finset.sum_add_distrib, mul_add]
theorem scaledPairingSum_smul_left [Finite S] (t : ℝ) (z : ℂ) (f h : BondMaps.BondValued S) :
    scaledPairingSum t (z • f) h = z * scaledPairingSum t f h := by
  cases nonempty_fintype S
  simp only [scaledPairingSum_eq_sum, Pi.smul_apply, Submodule.coe_smul,
    halfTracePairing_smul_left, ← Finset.mul_sum]
  ring
theorem scaledPairingSum_smul_right [Finite S] (t : ℝ) (z : ℂ) (f h : BondMaps.BondValued S) :
    scaledPairingSum t f (z • h) = z * scaledPairingSum t f h := by
  rw [scaledPairingSum_comm, scaledPairingSum_smul_left, scaledPairingSum_comm]
theorem scaledPairingSum_sub_right [Finite S] (t : ℝ) (f h h' : BondMaps.BondValued S) :
    scaledPairingSum t f (h - h') = scaledPairingSum t f h - scaledPairingSum t f h' := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ h', scaledPairingSum_comm, scaledPairingSum_add_left,
    scaledPairingSum_smul_left, scaledPairingSum_comm t h, scaledPairingSum_comm t h']
  ring
theorem scaledPairingSum_mul_scale [Finite S] (t r : ℝ) (f h : BondMaps.BondValued S) :
    scaledPairingSum (r * t) f h = r * scaledPairingSum t f h := by
  simp only [scaledPairingSum]
  push_cast
  ring
def pairingToDual [Finite S] (t : ℝ) :
    BondMaps.BondValued S →ₗ[ℂ] Module.Dual ℂ (BondMaps.BondValued S) :=
  LinearMap.mk₂ ℂ (fun f g => scaledPairingSum t g f)
    (fun f f' g => by
      rw [scaledPairingSum_comm, scaledPairingSum_add_left, scaledPairingSum_comm t f,
        scaledPairingSum_comm t f'])
    (fun z f g => by rw [scaledPairingSum_smul_right, smul_eq_mul])
    (fun f g g' => scaledPairingSum_add_left t g g' f)
    (fun z f g => by rw [scaledPairingSum_smul_left, smul_eq_mul])
theorem pairingToDual_apply [Finite S] (t : ℝ) (f g : BondMaps.BondValued S) :
    pairingToDual t f g = scaledPairingSum t g f := rfl
open Classical in
theorem scaledPairingSum_single_left [Finite S] (t : ℝ) (s : S) (X : ↥traceless)
    (f : BondMaps.BondValued S) :
    scaledPairingSum t (Pi.single s X) f =
      t * halfTracePairing (X : ComplexMatrix2) (f s : ComplexMatrix2) := by
  cases nonempty_fintype S
  rw [scaledPairingSum_eq_sum, Finset.sum_eq_single s]
  · simp
  · intro s' _ h
    simp [Pi.single_eq_of_ne h, halfTracePairing_zero_left]
  · simp
open Classical in
theorem eq_zero_of_scaledPairingSum_eq_zero [Finite S] {t : ℝ} (ht : 0 < t)
    (f : BondMaps.BondValued S)
    (h : ∀ f' : BondMaps.BondValued S, (∀ s, (f' s : ComplexMatrix2) ∈ hermitianTraceless) →
      scaledPairingSum t f' f = 0) : f = 0 := by
  funext s
  apply Subtype.ext
  have ha : ∀ a, halfTracePairing (pauli a) (f s : ComplexMatrix2) = 0 := by
    intro a
    have h1 := h (Pi.single s (pauliTraceless a)) (by
      intro s'
      by_cases hs : s' = s
      · subst hs
        simpa [pauliTraceless] using pauli_mem_hermitianTraceless a
      · simp [Pi.single_eq_of_ne hs, hermitianTraceless.zero_mem])
    rw [scaledPairingSum_single_left] at h1
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    exact (mul_eq_zero.mp h1).resolve_left ht'
  have hY := eq_pauliCombination_of_mem_traceless (f s).2
  simp only [ha] at hY
  rw [hY]
  simp [pauliCombination]
theorem scaledPairingSum_right_injective [Finite S] {t : ℝ} (ht : 0 < t)
    {h h' : BondMaps.BondValued S}
    (H : ∀ g, scaledPairingSum t g h = scaledPairingSum t g h') : h = h' := by
  apply sub_eq_zero.mp
  apply eq_zero_of_scaledPairingSum_eq_zero ht
  intro f' _
  rw [scaledPairingSum_sub_right, H, sub_self]
theorem exists_pairingAdjoint [Finite S] [Finite S'] {t : ℝ} (t' : ℝ) (ht : 0 < t)
    (M : BondMaps.BondValued S →ₗ[ℂ] BondMaps.BondValued S') :
    ∃ M' : BondMaps.BondValued S' →ₗ[ℂ] BondMaps.BondValued S, IsPairingAdjoint t t' M M' := by
  have hinj : Function.Injective (pairingToDual (S := S) t) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    apply eq_zero_of_scaledPairingSum_eq_zero ht
    intro f' _
    exact LinearMap.congr_fun hf f'
  let e := LinearMap.linearEquivOfInjective (pairingToDual (S := S) t) hinj
    (Subspace.dual_finrank_eq).symm
  refine ⟨e.symm.toLinearMap ∘ₗ M.dualMap ∘ₗ pairingToDual t', fun f f' => ?_⟩
  have h1 : pairingToDual t ((e.symm.toLinearMap ∘ₗ M.dualMap ∘ₗ pairingToDual t') f') =
      M.dualMap (pairingToDual t' f') := e.apply_symm_apply _
  have h2 := LinearMap.congr_fun h1 f
  rw [pairingToDual_apply] at h2
  rw [h2]
  rfl
end FiniteSets
theorem pairingNondegenerate_holds : LieInnerProduct.PairingNondegenerate := by
  intro S _ t ht f h
  exact eq_zero_of_scaledPairingSum_eq_zero ht f h
theorem uniqueAdjointOfLinearMap_holds : LieInnerProduct.UniqueAdjointOfLinearMap := by
  intro S S' _ _ t t' ht ht' M
  refine ⟨?_, ?_⟩
  · obtain ⟨M', h⟩ := exists_pairingAdjoint t' ht M
    refine ⟨M', h, fun M'' h'' => ?_⟩
    refine LinearMap.ext fun f' => scaledPairingSum_right_injective ht fun g => ?_
    rw [← h'' g f', ← h g f']
  · intro θ r hr M' h f f'
    have h1 := h f f'
    simp only [LinearMap.smul_apply]
    rw [scaledPairingSum_mul_scale, scaledPairingSum_mul_scale, scaledPairingSum_smul_left,
      scaledPairingSum_smul_right, h1]
theorem scaledPairingSum_of_unique (P : Type) [Unique P] (t : ℝ) (f f' : BondMaps.BondValued P) :
    scaledPairingSum t f f' =
      t * halfTracePairing (f default : ComplexMatrix2) (f' default : ComplexMatrix2) := by
  rw [scaledPairingSum_eq_sum, Fintype.sum_unique]
theorem eq_of_halfTracePairing_pauli_eq {Z Z' : ComplexMatrix2} (hZ : Z ∈ traceless)
    (hZ' : Z' ∈ traceless)
    (H : ∀ a, halfTracePairing (pauli a) Z = halfTracePairing (pauli a) Z') : Z = Z' := by
  rw [eq_pauliCombination_of_mem_traceless hZ, eq_pauliCombination_of_mem_traceless hZ']
  exact congrArg pauliCombination (funext H)
theorem exists_endAdjoint (T : ↥traceless →ₗ[ℂ] ↥traceless) :
    ∃ S : ↥traceless →ₗ[ℂ] ↥traceless, ∀ Y Y' : ↥traceless,
      halfTracePairing (T Y : ComplexMatrix2) (Y' : ComplexMatrix2) =
        halfTracePairing (Y : ComplexMatrix2) (S Y' : ComplexMatrix2) := by
  obtain ⟨M', h⟩ := exists_pairingAdjoint (t := 1) 1 one_pos (T.compLeft Unit)
  refine ⟨LinearMap.proj () ∘ₗ M' ∘ₗ LinearMap.pi fun _ => LinearMap.id, fun Y Y' => ?_⟩
  have h1 := h (fun _ => Y) (fun _ => Y')
  have h2 : halfTracePairing (T Y : ComplexMatrix2) (Y' : ComplexMatrix2) =
      halfTracePairing (Y : ComplexMatrix2) (M' (fun _ => Y') () : ComplexMatrix2) := by
    simpa [scaledPairingSum_of_unique] using h1
  exact h2
theorem endTranspose_spec (T : ↥traceless →ₗ[ℂ] ↥traceless) (Y Y' : ↥traceless) :
    halfTracePairing (T Y : ComplexMatrix2) (Y' : ComplexMatrix2) =
      halfTracePairing (Y : ComplexMatrix2) (endTranspose T Y' : ComplexMatrix2) :=
  Classical.epsilon_spec (exists_endAdjoint T) Y Y'
theorem adjointInPauliBasis_holds : LieInnerProduct.AdjointInPauliBasis := by
  intro T τ hT
  have key : ∀ a, endTranspose T (pauliTraceless a) = ∑ b, τ a b • pauliTraceless b := by
    intro a
    apply Subtype.ext
    have hZ := eq_pauliCombination_of_mem_traceless (endTranspose T (pauliTraceless a)).2
    have hc : (fun b => halfTracePairing (pauli b)
        (endTranspose T (pauliTraceless a) : ComplexMatrix2)) = τ a := by
      funext b
      have h1 := endTranspose_spec T (pauliTraceless b) (pauliTraceless a)
      have h2 : (pauliTraceless b : ComplexMatrix2) = pauli b := rfl
      rw [h2] at h1
      rw [← h1, hT b]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      change halfTracePairing (pauliCombination fun c => τ c b) (pauli a) = τ a b
      rw [halfTracePairing_comm, halfTracePairing_pauli_pauliCombination]
    rw [hc] at hZ
    rw [hZ]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl
  exact ⟨key, fun b => by simpa [Matrix.transpose_apply] using key b⟩
theorem onePointAndFiniteSetPairings_holds : LieInnerProduct.OnePointAndFiniteSetPairings := by
  refine ⟨fun P _ Y Y' => ?_, fun C _ ω ω' => ?_, fun T => ⟨fun S => ⟨fun h => ?_, ?_⟩, ?_⟩⟩
  · rw [scaledPairingSum_of_unique]
    simp
  · simp [SeparatedSequence.DepthChain.plainInner, scaledPairingSum]
  · refine LinearMap.ext fun Y' => Subtype.ext ?_
    refine eq_of_halfTracePairing_pauli_eq (S Y').2 (endTranspose T Y').2 fun a => ?_
    have h1 := h (pauliTraceless a) Y'
    have h2 := endTranspose_spec T (pauliTraceless a) Y'
    exact h1.symm.trans h2
  · rintro rfl
    exact endTranspose_spec T
  · intro P _ f f'
    rw [scaledPairingSum_of_unique, scaledPairingSum_of_unique]
    simpa using congrArg (fun z => ((1 : ℝ) : ℂ) * z)
      (endTranspose_spec T (f default) (f' default))
structure ValueChart (E S : Type*) [AddCommGroup E] [Module ℂ E] where
  forms : Set E
  extend : BondMaps.BondValued S →ₗ[ℂ] E
  restrict : E →ₗ[ℂ] S → ComplexMatrix2
  extend_mem : ∀ g, extend g ∈ forms
  restrict_extend : ∀ g s, restrict (extend g) s = (g s : ComplexMatrix2)
  restrict_mem : ∀ x ∈ forms, ∀ s, restrict x s ∈ traceless
  extend_restrict : ∀ x ∈ forms, ∀ g : BondMaps.BondValued S,
    (∀ s, restrict x s = (g s : ComplexMatrix2)) → extend g = x
namespace ValueChart
variable {E E' S S' : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
def values (c : ValueChart E S) (x : c.forms) : BondMaps.BondValued S :=
  fun s => ⟨c.restrict x.1 s, c.restrict_mem x.1 x.2 s⟩
theorem extend_values (c : ValueChart E S) (x : c.forms) : c.extend (c.values x) = x.1 :=
  c.extend_restrict x.1 x.2 _ fun _ => rfl
theorem values_extend (c : ValueChart E S) (g : BondMaps.BondValued S) :
    c.values ⟨c.extend g, c.extend_mem g⟩ = g := by
  funext s
  exact Subtype.ext (c.restrict_extend g s)
theorem values_bijective (c : ValueChart E S) : Function.Bijective c.values :=
  ⟨fun x y h => Subtype.ext (by rw [← c.extend_values x, h, c.extend_values]),
    fun g => ⟨_, c.values_extend g⟩⟩
def transfer (c : ValueChart E S) (c' : ValueChart E' S') (D : E →ₗ[ℂ] E')
    (hD : ∀ x ∈ c.forms, D x ∈ c'.forms) :
    BondMaps.BondValued S →ₗ[ℂ] BondMaps.BondValued S' where
  toFun g := c'.values ⟨D (c.extend g), hD _ (c.extend_mem g)⟩
  map_add' g g' := by
    funext s
    apply Subtype.ext
    simp [values]
  map_smul' z g := by
    funext s
    apply Subtype.ext
    simp [values]
theorem transfer_values (c : ValueChart E S) (c' : ValueChart E' S') (D : E →ₗ[ℂ] E')
    (hD : ∀ x ∈ c.forms, D x ∈ c'.forms) (x : c.forms) :
    c.transfer c' D hD (c.values x) = c'.values ⟨D x.1, hD _ x.2⟩ :=
  congrArg c'.values (Subtype.ext (congrArg D (c.extend_values x)))
theorem exists_adjoint_transfer [Finite S] [Finite S'] {t t' : ℝ} (ht : 0 < t)
    (c : ValueChart E S) (c' : ValueChart E' S') (D : E →ₗ[ℂ] E')
    (hD : ∀ x ∈ c.forms, D x ∈ c'.forms) (P : E → E → ℂ) (Q : E' → E' → ℂ)
    (hP : ∀ x y : c.forms, P x y = scaledPairingSum t (c.values x) (c.values y))
    (hQ : ∀ x y : c'.forms, Q x y = scaledPairingSum t' (c'.values x) (c'.values y)) :
    ∃ M', IsPairingAdjoint t t' (c.transfer c' D hD) M' ∧ ∀ y : c'.forms, ∃ T : c.forms,
      c.values T = M' (c'.values y) ∧
      ∀ B, (B ∈ c.forms ∧ ∀ f ∈ c.forms, P B f = Q y.1 (D f)) ↔ B = T.1 := by
  obtain ⟨M', hM'⟩ := exists_pairingAdjoint t' ht (c.transfer c' D hD)
  refine ⟨M', hM', fun y => ?_⟩
  let T : c.forms := ⟨c.extend (M' (c'.values y)), c.extend_mem _⟩
  have hvT : c.values T = M' (c'.values y) := c.values_extend _
  have hpair : ∀ f : c.forms, P T.1 f.1 = Q y.1 (D f.1) := by
    intro f
    rw [hP T f, hvT, scaledPairingSum_comm, ← hM', transfer_values, hQ y ⟨D f.1, hD _ f.2⟩,
      scaledPairingSum_comm]
  refine ⟨T, hvT, fun B => ⟨?_, ?_⟩⟩
  · rintro ⟨hB, h⟩
    have h1 : (⟨B, hB⟩ : c.forms) = T := by
      refine c.values_bijective.1 (scaledPairingSum_right_injective ht fun g => ?_)
      obtain ⟨f, rfl⟩ := c.values_bijective.2 g
      rw [scaledPairingSum_comm, scaledPairingSum_comm t _ (c.values T), ← hP, ← hP, hpair f]
      exact h f.1 f.2
    exact congrArg Subtype.val h1
  · rintro rfl
    exact ⟨T.2, fun f hf => hpair ⟨f, hf⟩⟩
end ValueChart
theorem epsilon_eq_of_unique {α : Type*} [Nonempty α] {p : α → Prop} {T : α}
    (h : ∀ B, p B ↔ B = T) : Classical.epsilon p = T :=
  (h _).1 (Classical.epsilon_spec ⟨T, (h T).2 rfl⟩)
open Classical in
def zeroExtension {X : Type*} (P : Set X) : BondMaps.BondValued ↥P →ₗ[ℂ] X → ComplexMatrix2 where
  toFun g x := if h : x ∈ P then (g ⟨x, h⟩ : ComplexMatrix2) else 0
  map_add' g g' := by
    funext x
    by_cases h : x ∈ P <;> simp [h]
  map_smul' z g := by
    funext x
    by_cases h : x ∈ P <;> simp [h]
theorem zeroExtension_of_mem {X : Type*} {P : Set X} (g : BondMaps.BondValued ↥P) {x : X}
    (h : x ∈ P) : zeroExtension P g x = (g ⟨x, h⟩ : ComplexMatrix2) := dif_pos h
theorem zeroExtension_of_notMem {X : Type*} {P : Set X} (g : BondMaps.BondValued ↥P) {x : X}
    (h : x ∉ P) : zeroExtension P g x = 0 := dif_neg h
def subsetChart {X : Type*} (P : Set X) (𝒞 : Set (X → ComplexMatrix2))
    (h𝒞 : ∀ a, a ∈ 𝒞 ↔ (∀ x, a x ∈ traceless) ∧ P.indicator a = a) :
    ValueChart (X → ComplexMatrix2) ↥P where
  forms := 𝒞
  extend := zeroExtension P
  restrict := LinearMap.funLeft ℂ ComplexMatrix2 Subtype.val
  extend_mem g := by
    refine (h𝒞 _).2 ⟨fun x => ?_, ?_⟩
    · by_cases h : x ∈ P
      · rw [zeroExtension_of_mem g h]
        exact (g _).2
      · rw [zeroExtension_of_notMem g h]
        exact traceless.zero_mem
    · funext x
      by_cases h : x ∈ P
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, zeroExtension_of_notMem g h]
  restrict_extend g s := zeroExtension_of_mem g s.2
  restrict_mem x hx s := ((h𝒞 x).1 hx).1 s
  extend_restrict x hx g hg := by
    funext y
    by_cases h : y ∈ P
    · rw [zeroExtension_of_mem g h]
      exact (hg ⟨y, h⟩).symm
    · rw [zeroExtension_of_notMem g h, ← ((h𝒞 x).1 hx).2, Set.indicator_of_notMem h]
section Bonds
variable {L m : ℕ} {j : ℤ}
theorem opposite_opposite (b : Bond L m j) : b.opposite.opposite = b := Bond.ext rfl rfl
open Classical in
def bondFormExtend (p : Bond L m j → Prop) :
    BondMaps.BondValued (Subtype p) →ₗ[ℂ] Bond L m j → ComplexMatrix2 where
  toFun g b := if h : p b then (g ⟨b, h⟩ : ComplexMatrix2)
    else if h' : p b.opposite then -(g ⟨b.opposite, h'⟩ : ComplexMatrix2) else 0
  map_add' g g' := by
    funext b
    by_cases h : p b
    · simp [h]
    · by_cases h' : p b.opposite
      · simp [h, h', add_comm]
      · simp [h, h']
  map_smul' z g := by
    funext b
    by_cases h : p b
    · simp [h]
    · by_cases h' : p b.opposite
      · simp [h, h']
      · simp [h, h']
theorem bondFormExtend_of_pos {p : Bond L m j → Prop} (g : BondMaps.BondValued (Subtype p))
    {b : Bond L m j} (h : p b) : bondFormExtend p g b = (g ⟨b, h⟩ : ComplexMatrix2) := dif_pos h
theorem bondFormExtend_of_opposite {p : Bond L m j → Prop} (g : BondMaps.BondValued (Subtype p))
    {b : Bond L m j} (h : ¬p b) (h' : p b.opposite) :
    bondFormExtend p g b = -(g ⟨b.opposite, h'⟩ : ComplexMatrix2) :=
  (dif_neg h).trans (dif_pos h')
theorem bondFormExtend_of_neither {p : Bond L m j → Prop} (g : BondMaps.BondValued (Subtype p))
    {b : Bond L m j} (h : ¬p b) (h' : ¬p b.opposite) : bondFormExtend p g b = 0 :=
  (dif_neg h).trans (dif_neg h')
def bondFormChart (hL : 2 ≤ L) (hj : -(m : ℤ) < j) (𝓑 : Set (Bond L m j))
    (h𝓑 : ∀ b ∈ 𝓑, b.opposite ∈ 𝓑) (p : Bond L m j → Prop)
    (hp : ∀ b, p b ↔ b ∈ 𝓑 ∧ b.IsPositivelyOriented)
    (𝒞 : Set (Bond L m j → ComplexMatrix2))
    (h𝒞 : ∀ a, a ∈ 𝒞 ↔ IsBondForm complexLieAlgebra a ∧ 𝓑.indicator a = a) :
    ValueChart (Bond L m j → ComplexMatrix2) (Subtype p) where
  forms := 𝒞
  extend := bondFormExtend p
  restrict := LinearMap.funLeft ℂ ComplexMatrix2 Subtype.val
  extend_mem g := by
    have hnot : ∀ b, p b → ¬p b.opposite := by
      intro b hb hr
      rcases MatrixValued.xor_isPositivelyOriented_opposite hL hj b with ⟨_, h⟩ | ⟨_, h⟩
      · exact h ((hp _).1 hr).2
      · exact h ((hp _).1 hb).2
    refine (h𝒞 _).2 ⟨⟨fun b _ => ?_, fun b => ?_⟩, ?_⟩
    · by_cases h : p b
      · rw [bondFormExtend_of_pos g h]
        exact (g _).2
      · by_cases h' : p b.opposite
        · rw [bondFormExtend_of_opposite g h h']
          exact traceless.neg_mem (g _).2
        · rw [bondFormExtend_of_neither g h h']
          exact traceless.zero_mem
    · by_cases h : p b
      · have h2 : p b.opposite.opposite := h
        rw [bondFormExtend_of_opposite g (hnot b h) h2, bondFormExtend_of_pos g h]
        rfl
      · by_cases h' : p b.opposite
        · rw [bondFormExtend_of_pos g h', bondFormExtend_of_opposite g h h', neg_neg]
        · have h2 : ¬p b.opposite.opposite := h
          rw [bondFormExtend_of_neither g h' h2, bondFormExtend_of_neither g h h', neg_zero]
    · funext b
      by_cases hb : b ∈ 𝓑
      · rw [Set.indicator_of_mem hb]
      · have h : ¬p b := fun h => hb ((hp _).1 h).1
        have h' : ¬p b.opposite := fun h' => hb (h𝓑 _ ((hp _).1 h').1)
        rw [Set.indicator_of_notMem hb, bondFormExtend_of_neither g h h']
  restrict_extend g s := bondFormExtend_of_pos g s.2
  restrict_mem x hx s := ((h𝒞 x).1 hx).1.1 s.1 ((hp _).1 s.2).2
  extend_restrict x hx g hg := by
    obtain ⟨⟨-, hrev⟩, hind⟩ := (h𝒞 x).1 hx
    funext b
    by_cases h : p b
    · rw [bondFormExtend_of_pos g h]
      exact (hg ⟨b, h⟩).symm
    · by_cases h' : p b.opposite
      · rw [bondFormExtend_of_opposite g h h',
          ← show x b.opposite = (g ⟨b.opposite, h'⟩ : ComplexMatrix2) from
          hg ⟨b.opposite, h'⟩, hrev, neg_neg]
      · rw [bondFormExtend_of_neither g h h']
        by_cases hb : b ∈ 𝓑
        · exfalso
          rcases MatrixValued.xor_isPositivelyOriented_opposite hL hj b with
            ⟨hpos, _⟩ | ⟨hpos, _⟩
          · exact h ((hp _).2 ⟨hb, hpos⟩)
          · exact h' ((hp _).2 ⟨h𝓑 _ hb, hpos⟩)
        · rw [← hind, Set.indicator_of_notMem hb]
def plaquetteFormExtend :
    BondMaps.BondValued (Plaquette L m j) →ₗ[ℂ] Fin 4 → Fin 4 → Site L m j → ComplexMatrix2 where
  toFun g := plaquetteFormOf fun p => (g p : ComplexMatrix2)
  map_add' g g' := by
    funext μ ν x
    simp only [plaquetteFormOf, Pi.add_apply, Submodule.coe_add]
    split_ifs
    · rfl
    · rw [neg_add]
    · simp
  map_smul' z g := by
    funext μ ν x
    simp only [plaquetteFormOf, Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply]
    split_ifs
    · rfl
    · rw [smul_neg]
    · simp
def plaquetteFormRestrict :
    (Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) →ₗ[ℂ] Plaquette L m j → ComplexMatrix2 where
  toFun F p := F p.firstAxis p.secondAxis p.origin
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem plaquetteFormExtend_of_lt (g : BondMaps.BondValued (Plaquette L m j)) {μ ν : Fin 4}
    (h : μ < ν) (x : Site L m j) :
    plaquetteFormExtend g μ ν x = (g ⟨x, μ, ν, h⟩ : ComplexMatrix2) := dif_pos h
theorem plaquetteFormExtend_of_gt (g : BondMaps.BondValued (Plaquette L m j)) {μ ν : Fin 4}
    (h : ν < μ) (x : Site L m j) :
    plaquetteFormExtend g μ ν x = -(g ⟨x, ν, μ, h⟩ : ComplexMatrix2) :=
  (dif_neg (not_lt.mpr h.le)).trans (dif_pos h)
theorem plaquetteFormExtend_self (g : BondMaps.BondValued (Plaquette L m j)) (μ : Fin 4)
    (x : Site L m j) : plaquetteFormExtend g μ μ x = 0 :=
  (dif_neg (lt_irrefl μ)).trans (dif_neg (lt_irrefl μ))
def plaquetteFormChart :
    ValueChart (Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) (Plaquette L m j) where
  forms := {F | IsPlaquetteForm complexLieAlgebra F}
  extend := plaquetteFormExtend
  restrict := plaquetteFormRestrict
  extend_mem g := by
    refine ⟨fun μ ν x h => ?_, fun μ ν x => ?_⟩
    · rw [plaquetteFormExtend_of_lt g h]
      exact (g _).2
    · rcases lt_trichotomy μ ν with h | rfl | h
      · rw [plaquetteFormExtend_of_lt g h, plaquetteFormExtend_of_gt g h]
      · rw [plaquetteFormExtend_self, neg_zero]
      · rw [plaquetteFormExtend_of_lt g h, plaquetteFormExtend_of_gt g h, neg_neg]
  restrict_extend g s := plaquetteFormExtend_of_lt g s.firstAxis_lt_secondAxis s.origin
  restrict_mem F hF s := hF.1 _ _ _ s.firstAxis_lt_secondAxis
  extend_restrict F hF g hg := by
    funext μ ν x
    rcases lt_trichotomy μ ν with h | rfl | h
    · rw [plaquetteFormExtend_of_lt g h]
      exact (hg ⟨x, μ, ν, h⟩).symm
    · rw [plaquetteFormExtend_self]
      have h0 := hF.2 μ μ x
      ext i k
      have h1 := congrFun (congrFun h0 i) k
      simp only [Matrix.neg_apply] at h1
      have h2 : F μ μ x i k = 0 := by linear_combination h1 / 2
      simp [h2]
    · rw [plaquetteFormExtend_of_gt g h, ← show F ν μ x = (g ⟨x, ν, μ, h⟩ : ComplexMatrix2) from
        hg ⟨x, ν, μ, h⟩, hF.2 ν μ x]
end Bonds
theorem conjugateBy_mem_traceless (V : ComplexMatrix2) {Y : ComplexMatrix2} (h : Y ∈ traceless) :
    conjugateBy V Y ∈ traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
theorem conjugateBy_add (V A B : ComplexMatrix2) :
    conjugateBy V (A + B) = conjugateBy V A + conjugateBy V B := by
  simp [conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (V : ComplexMatrix2) (z : ℂ) (A : ComplexMatrix2) :
    conjugateBy V (z • A) = z • conjugateBy V A := by
  simp [conjugateBy]
section Derivatives
variable {L m : ℕ} {j : ℤ}
theorem covDeriv_mem_traceless (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) (μ : Fin 4)
    (f : Site L m j → ComplexMatrix2) (x : Site L m j) (h : f x ∈ traceless)
    (h' : f (x + unitStep L m j μ) ∈ traceless) :
    covDeriv ξ U μ f x ∈ traceless :=
  traceless.smul_mem _ (traceless.sub_mem (conjugateBy_mem_traceless _ h') h)
def covExteriorDerivLinear (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) :
    (Bond L m j → ComplexMatrix2) →ₗ[ℂ] Fin 4 → Fin 4 → Site L m j → ComplexMatrix2 where
  toFun := covExteriorDeriv ξ U
  map_add' A B := by
    funext μ ν x
    simp only [covExteriorDeriv, covDeriv, bondFormComponent, Pi.add_apply, conjugateBy_add]
    module
  map_smul' z A := by
    funext μ ν x
    simp only [covExteriorDeriv, covDeriv, bondFormComponent, Pi.smul_apply, conjugateBy_smul,
      RingHom.id_apply]
    module
theorem covExteriorDeriv_mem_traceless (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    {A : Bond L m j → ComplexMatrix2} (hA : IsBondForm complexLieAlgebra A) (μ ν : Fin 4)
    (x : Site L m j) : covExteriorDeriv ξ U A μ ν x ∈ traceless := by
  have hf : ∀ (y : Site L m j) (κ : Fin 4), bondFormComponent A κ y ∈ traceless := fun y κ =>
    hA.1 _ ⟨κ, by simp [Bond.forwardFrom]⟩
  exact traceless.sub_mem (covDeriv_mem_traceless _ _ _ _ _ (hf _ _) (hf _ _))
    (covDeriv_mem_traceless _ _ _ _ _ (hf _ _) (hf _ _))
end Derivatives
section Lattice
variable {L m : ℕ} {j : ℤ}
theorem sum_positivelyOrientedBond (hL : 2 ≤ L) (hj : -(m : ℤ) < j) [Fintype (Site L m j)]
    [Fintype (PositivelyOrientedBond L m j)] (φ : Bond L m j → ℂ) :
    ∑ b : PositivelyOrientedBond L m j, φ b.1 =
      ∑ x : Site L m j, ∑ μ : Fin 4, φ (Bond.forwardFrom x μ) := by
  let e : Site L m j × Fin 4 → PositivelyOrientedBond L m j := fun q =>
    ⟨Bond.forwardFrom q.1 q.2, ⟨q.2, by simp [Bond.forwardFrom]⟩⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨x, μ⟩ ⟨y, ν⟩ h
      have h1 : Bond.forwardFrom x μ = Bond.forwardFrom y ν := congrArg Subtype.val h
      have h2 : x = y := congrArg Bond.source h1
      subst h2
      have h3 : x + unitStep L m j μ = x + unitStep L m j ν := congrArg Bond.target h1
      have h4 : μ = ν := by
        by_contra hne
        exact MatrixValued.unitStep_ne_unitStep (by omega) hj hne (add_left_cancel h3)
      rw [h4]
    · rintro ⟨b, μ, hμ⟩
      refine ⟨(b.source, μ), Subtype.ext (Bond.ext rfl ?_)⟩
      change b.source + unitStep L m j μ = b.target
      rw [← hμ]
      abel
  rw [← Fintype.sum_prod_type' (f := fun x μ => φ (Bond.forwardFrom x μ))]
  exact (he.sum_comp fun b => φ b.1).symm
theorem sum_increasing_pairs (g : Fin 4 → Fin 4 → ℂ) :
    ∑ q : {q : Fin 4 × Fin 4 // q.1 < q.2}, g q.1.1 q.1.2 =
      ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ, g μ ν := by
  calc ∑ q : {q : Fin 4 × Fin 4 // q.1 < q.2}, g q.1.1 q.1.2
      = ∑ q ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2), g q.1 q.2 :=
        (Finset.sum_subtype (Finset.univ.filter fun q : Fin 4 × Fin 4 => q.1 < q.2)
          (fun q => by simp) fun q => g q.1 q.2).symm
    _ = ∑ q : Fin 4 × Fin 4, if q.1 < q.2 then g q.1 q.2 else 0 := Finset.sum_filter _ _
    _ = ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then g μ ν else 0 := Fintype.sum_prod_type _
    _ = ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ, g μ ν :=
        Finset.sum_congr rfl fun μ _ => by rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
theorem sum_plaquette [Fintype (Site L m j)] [Fintype (Plaquette L m j)]
    (ψ : Site L m j → Fin 4 → Fin 4 → ℂ) :
    ∑ p : Plaquette L m j, ψ p.origin p.firstAxis p.secondAxis =
      ∑ x : Site L m j, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ, ψ x μ ν := by
  let e : Site L m j × {q : Fin 4 × Fin 4 // q.1 < q.2} → Plaquette L m j := fun q =>
    ⟨q.1, q.2.1.1, q.2.1.2, q.2.2⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨x, ⟨⟨μ, ν⟩, h⟩⟩ ⟨y, ⟨⟨μ', ν'⟩, h'⟩⟩ hh
      simp only [e, Plaquette.mk.injEq] at hh
      obtain ⟨rfl, rfl, rfl⟩ := hh
      rfl
    · rintro ⟨x, μ, ν, h⟩
      exact ⟨(x, ⟨(μ, ν), h⟩), rfl⟩
  simp only [← sum_increasing_pairs]
  rw [← Fintype.sum_prod_type' (f := fun x (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) =>
    ψ x q.1.1 q.1.2)]
  exact (he.sum_comp fun p => ψ p.origin p.firstAxis p.secondAxis).symm
def latticeBondChart (hL : 2 ≤ L) (hj : -(m : ℤ) < j) :
    ValueChart (Bond L m j → ComplexMatrix2) (PositivelyOrientedBond L m j) :=
  bondFormChart hL hj univ (fun _ _ => mem_univ _) (fun b => b.IsPositivelyOriented)
    (fun _ => ⟨fun h => ⟨mem_univ _, h⟩, fun h => h.2⟩) {A | IsBondForm complexLieAlgebra A}
    (fun a => ⟨fun h => ⟨h, Set.indicator_univ a⟩, fun h => h.1⟩)
theorem bondFormInner_eq_scaledPairingSum (hL : 2 ≤ L) (hj : -(m : ℤ) < j) (ξ : ℝ)
    [Finite (Site L m j)] [Finite (PositivelyOrientedBond L m j)] (A B : ComplexBondForm L m j) :
    bondFormInner ξ A.1 B.1 = scaledPairingSum (ξ ^ 4) A.onPositive B.onPositive := by
  cases nonempty_fintype (Site L m j)
  cases nonempty_fintype (PositivelyOrientedBond L m j)
  rw [scaledPairingSum_eq_sum, bondFormInner, finsum_eq_sum_of_fintype]
  congr 1
  exact (sum_positivelyOrientedBond hL hj fun b => halfTracePairing (A.1 b) (B.1 b)).symm
theorem plaquetteFormInner_eq_scaledPairingSum (ξ : ℝ) [Finite (Site L m j)]
    [Finite (Plaquette L m j)] (F H : ComplexPlaquetteForm L m j) :
    plaquetteFormInner ξ F.1 H.1 = scaledPairingSum (ξ ^ 4) F.onPlaquettes H.onPlaquettes := by
  cases nonempty_fintype (Site L m j)
  cases nonempty_fintype (Plaquette L m j)
  rw [scaledPairingSum_eq_sum, plaquetteFormInner, finsum_eq_sum_of_fintype]
  congr 1
  exact (sum_plaquette fun x μ ν => halfTracePairing (F.1 μ ν x) (H.1 μ ν x)).symm
theorem innersAreScaledSums_lattice (hL : 2 ≤ L) (hj : -(m : ℤ) < j) (ξ : ℝ)
    [Finite (Site L m j)] [Finite (PositivelyOrientedBond L m j)] [Finite (Plaquette L m j)] :
    PeriodicLattice.InnersAreScaledSums L m j ξ :=
  ⟨(latticeBondChart hL hj).values_bijective, plaquetteFormChart.values_bijective,
    fun _ _ => rfl, bondFormInner_eq_scaledPairingSum hL hj ξ,
    plaquetteFormInner_eq_scaledPairingSum ξ⟩
theorem covDerivAdjoint_lattice (hL : 2 ≤ L) (hj : -(m : ℤ) < j) {ξ : ℝ} (hξ : 0 < ξ)
    [Finite (Site L m j)] [Finite (PositivelyOrientedBond L m j)] [Finite (Plaquette L m j)] :
    CovDerivAdjointIsPairingAdjoint L m j ξ := by
  intro U _
  let c := latticeBondChart (m := m) hL hj
  let c' := plaquetteFormChart (L := L) (m := m) (j := j)
  let D := covExteriorDerivLinear ξ U
  have hD : ∀ x ∈ c.forms, D x ∈ c'.forms := by
    intro x hx
    refine ⟨fun μ ν y _ => covExteriorDeriv_mem_traceless ξ U hx μ ν y, fun μ ν y => ?_⟩
    exact (neg_sub _ _).symm
  obtain ⟨M', hM', hT⟩ := c.exists_adjoint_transfer (t := ξ ^ 4) (t' := ξ ^ 4) (by positivity)
    c' D hD (bondFormInner ξ) (plaquetteFormInner ξ)
    (fun x y => bondFormInner_eq_scaledPairingSum hL hj ξ ⟨x.1, x.2⟩ ⟨y.1, y.2⟩)
    (fun x y => plaquetteFormInner_eq_scaledPairingSum ξ ⟨x.1, x.2⟩ ⟨y.1, y.2⟩)
  refine ⟨c.transfer c' D hD, M', hM', fun A p => ?_, fun F b => ?_, fun F B => ?_⟩
  · have h := c.transfer_values c' D hD ⟨A.1, A.2⟩
    exact congrArg (fun g : BondMaps.BondValued (Plaquette L m j) => (g p : ComplexMatrix2)) h
  · obtain ⟨T, hvT, hT⟩ := hT ⟨F.1, F.2⟩
    have he : covExteriorDerivAdjoint ξ U F.1 = T.1 := epsilon_eq_of_unique hT
    rw [he]
    exact (congrArg (fun g : BondMaps.BondValued (PositivelyOrientedBond L m j) =>
      (g b : ComplexMatrix2)) hvT).symm
  · obtain ⟨T, hvT, hT⟩ := hT ⟨F.1, F.2⟩
    have he : covExteriorDerivAdjoint ξ U F.1 = T.1 := epsilon_eq_of_unique hT
    rw [he]
    exact hT B
end Lattice
theorem bond_finite {L m : ℕ} {j : ℤ} [Finite (Site L m j)] : Finite (Bond L m j) := by apply _root_.YangMills.SharedProofs.p19159 <;> assumption
theorem plaquette_finite {L m : ℕ} {j : ℤ} [Finite (Site L m j)] : Finite (Plaquette L m j) := by apply _root_.YangMills.Construction.GradLaplacianCommutation.plaquette_finite <;> assumption
theorem periodicLatticePairings_holds : LieInnerProduct.PeriodicLatticePairings := by
  intro L m j ξ hL _ hj hξ
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hS : Finite (Site L m j) := SeparatedSequences.BaseParameters.site_finite (by omega) m j
  have hB : Finite (Bond L m j) := bond_finite
  have hP : Finite (Plaquette L m j) := plaquette_finite
  exact ⟨hS, inferInstance, hP, innersAreScaledSums_lattice hL2 hj ξ,
    covDerivAdjoint_lattice hL2 hj hξ⟩
section BaseLattice
open YangMills.Construction.SeparatedSequence
theorem scaledPairingSum_of_subset {X : Type*} (P : Set X) [Finite ↥P] (t : ℝ)
    (a a' : X → ComplexMatrix2) (g g' : BondMaps.BondValued ↥P)
    (h : ∀ s : ↥P, a s.1 = (g s : ComplexMatrix2))
    (h' : ∀ s : ↥P, a' s.1 = (g' s : ComplexMatrix2)) :
    (t : ℂ) * ∑ᶠ (x : X) (_ : x ∈ P), halfTracePairing (a x) (a' x) = scaledPairingSum t g g' := by
  rw [scaledPairingSum,
    ← finsum_set_coe_eq_finsum_mem P (f := fun x => halfTracePairing (a x) (a' x))]
  congr 1
  exact finsum_congr fun s => by rw [h s, h' s]
theorem bondFormOfPositive_opposite {L m : ℕ} {j : ℤ} (hL : 2 ≤ L) (hj : -(m : ℤ) < j)
    (a : Bond L m j → ComplexMatrix2) (b : Bond L m j) :
    bondFormOfPositive a b.opposite = -bondFormOfPositive a b := by
  rcases MatrixValued.xor_isPositivelyOriented_opposite hL hj b with ⟨hb, hr⟩ | ⟨hr, hb⟩
  · simp only [bondFormOfPositive, if_pos hb, if_neg hr, opposite_opposite]
  · simp only [bondFormOfPositive, if_pos hr, if_neg hb, neg_neg]
variable {L m : ℕ} {N : DepthParameters L m} (A : DepthChain N)
theorem two_le_L (N : DepthParameters L m) : 2 ≤ L := by
  have := N.base.thirteen_le_L
  omega
theorem neg_lt_levelDepth (N : DepthParameters L m) : -(m : ℤ) < levelDepth N.K 0 := by
  have := N.base.m_pos
  simp only [levelDepth]
  omega
theorem eta_pos (N : DepthParameters L m) : 0 < N.eta := by
  have h := two_le_L N
  have h0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  exact zpow_pos h0 _
def siteChart : ValueChart (SiteAtLevel L m N.K 0 → ComplexMatrix2) ↥A.baseSites :=
  subsetChart A.baseSites (A.siteFields complexLieAlgebra) fun _ => Iff.rfl
def bondChart : ValueChart (BondAtLevel L m N.K 0 → ComplexMatrix2) ↥A.orientedBaseBonds :=
  bondFormChart (two_le_L N) (neg_lt_levelDepth N) (bondsInside (A.region 0))
    (fun _ hb => ⟨hb.2, hb.1⟩) (· ∈ A.orientedBaseBonds) (fun _ => Iff.rfl)
    (A.formSpace : Set (BondAtLevel L m N.K 0 → ComplexMatrix2)) fun _ => Iff.rfl
def plaquetteChart :
    ValueChart (PlaquetteAtLevel L m N.K 0 → ComplexMatrix2) ↥A.basePlaquettes :=
  subsetChart A.basePlaquettes (A.plaquetteForms complexLieAlgebra) fun _ => Iff.rfl
theorem siteInner_eq [Finite ↥A.baseSites] (f f' : (siteChart A).forms) :
    A.siteInner f.1 f'.1 =
      scaledPairingSum (N.eta ^ 4) ((siteChart A).values f) ((siteChart A).values f') :=
  scaledPairingSum_of_subset _ _ _ _ _ _ (fun _ => rfl) fun _ => rfl
theorem bondInner_eq [Finite ↥A.orientedBaseBonds] (a a' : (bondChart A).forms) :
    A.bondInner a.1 a'.1 =
      scaledPairingSum (N.eta ^ 4) ((bondChart A).values a) ((bondChart A).values a') :=
  scaledPairingSum_of_subset _ _ _ _ _ _ (fun _ => rfl) fun _ => rfl
theorem plaquetteInner_eq [Finite ↥A.basePlaquettes] (X X' : (plaquetteChart A).forms) :
    A.plaquetteInner X.1 X'.1 = scaledPairingSum (N.eta ^ 4) ((plaquetteChart A).values X)
      ((plaquetteChart A).values X') :=
  scaledPairingSum_of_subset _ _ _ _ _ _ (fun _ => rfl) fun _ => rfl
theorem innersAreScaledSums_chain [Finite ↥A.baseSites] [Finite ↥A.orientedBaseBonds]
    [Finite ↥A.basePlaquettes] : A.InnersAreScaledSums :=
  ⟨(siteChart A).values_bijective, (bondChart A).values_bijective,
    (plaquetteChart A).values_bijective, siteInner_eq A, bondInner_eq A,
    plaquetteInner_eq A⟩
def covGradientLinear (U : BondAtLevel L m N.K 0 → ComplexMatrix2) :
    (SiteAtLevel L m N.K 0 → ComplexMatrix2) →ₗ[ℂ] BondAtLevel L m N.K 0 → ComplexMatrix2 where
  toFun := A.covGradient U
  map_add' f f' := by
    funext b
    simp only [DepthChain.covGradient, Set.indicator, bondFormOfPositive, Pi.add_apply,
      conjugateBy_add]
    split_ifs
    · module
    · module
    · simp
  map_smul' z f := by
    funext b
    simp only [DepthChain.covGradient, Set.indicator, bondFormOfPositive, Pi.smul_apply,
      conjugateBy_smul, RingHom.id_apply]
    split_ifs
    · module
    · module
    · simp
def covCurlLinear (U : BondAtLevel L m N.K 0 → ComplexMatrix2) :
    (BondAtLevel L m N.K 0 → ComplexMatrix2) →ₗ[ℂ] PlaquetteAtLevel L m N.K 0 → ComplexMatrix2 where
  toFun := A.covCurl U
  map_add' a a' := by
    funext p
    have h := congrFun (congrFun (congrFun ((covExteriorDerivLinear N.eta U).map_add a a')
      p.firstAxis) p.secondAxis) p.origin
    simp only [DepthChain.covCurl, Set.indicator, Pi.add_apply]
    split_ifs
    · exact h
    · simp
  map_smul' z a := by
    funext p
    have h := congrFun (congrFun (congrFun ((covExteriorDerivLinear N.eta U).map_smul z a)
      p.firstAxis) p.secondAxis) p.origin
    simp only [DepthChain.covCurl, Set.indicator, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · exact h
    · simp
theorem covGradient_mem (U : BondAtLevel L m N.K 0 → ComplexMatrix2)
    (f : SiteAtLevel L m N.K 0 → ComplexMatrix2) (hf : f ∈ (siteChart A).forms) :
    covGradientLinear A U f ∈ (bondChart A).forms := by
  have hv : ∀ x, f x ∈ traceless := hf.1
  refine ⟨⟨fun b hb => ?_, fun b => ?_⟩, ?_⟩
  · change A.covGradient U f b ∈ complexLieAlgebra
    simp only [DepthChain.covGradient, Set.indicator, bondFormOfPositive, if_pos hb]
    split_ifs
    · exact traceless.smul_mem _ (traceless.sub_mem (conjugateBy_mem_traceless _ (hv _)) (hv _))
    · exact traceless.zero_mem
  · change A.covGradient U f b.opposite = -A.covGradient U f b
    by_cases hb : b ∈ bondsInside (A.region 0)
    · have hr : b.opposite ∈ bondsInside (A.region 0) := ⟨hb.2, hb.1⟩
      simp only [DepthChain.covGradient]
      rw [Set.indicator_of_mem hb, Set.indicator_of_mem hr,
        bondFormOfPositive_opposite (two_le_L N) (neg_lt_levelDepth N)]
    · have hr : b.opposite ∉ bondsInside (A.region 0) := fun h => hb ⟨h.2, h.1⟩
      simp only [DepthChain.covGradient]
      rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hr, neg_zero]
  · change (bondsInside (A.region 0)).indicator (A.covGradient U f) = A.covGradient U f
    simp only [DepthChain.covGradient, Set.indicator_indicator, Set.inter_self]
theorem covCurl_mem (U : BondAtLevel L m N.K 0 → ComplexMatrix2)
    (a : BondAtLevel L m N.K 0 → ComplexMatrix2) (ha : a ∈ (bondChart A).forms) :
    covCurlLinear A U a ∈ (plaquetteChart A).forms := by
  refine ⟨fun p => ?_, ?_⟩
  · change A.covCurl U a p ∈ complexLieAlgebra
    simp only [DepthChain.covCurl, Set.indicator]
    split_ifs
    · exact covExteriorDeriv_mem_traceless N.eta U ha.1 _ _ _
    · exact traceless.zero_mem
  · change (plaquettesInside (A.region 0)).indicator (A.covCurl U a) = A.covCurl U a
    simp only [DepthChain.covCurl, Set.indicator_indicator, Set.inter_self]
theorem covDivergence_isAdjoint [Finite ↥A.baseSites] [Finite ↥A.orientedBaseBonds] :
    A.CovDivergenceIsPairingAdjoint := by
  intro U _
  let c := siteChart A
  let c' := bondChart A
  let D := covGradientLinear A U
  have hD : ∀ x ∈ c.forms, D x ∈ c'.forms := covGradient_mem A U
  obtain ⟨M', hM', hT⟩ := c.exists_adjoint_transfer (t := N.eta ^ 4) (t' := N.eta ^ 4)
    (pow_pos (eta_pos N) 4) c' D hD A.siteInner A.bondInner (siteInner_eq A)
    (bondInner_eq A)
  refine ⟨c.transfer c' D hD, M', hM', fun f b => ?_, fun a x => ?_, fun a B => ?_⟩
  · have h := c.transfer_values c' D hD f
    exact congrArg (fun g : BondMaps.BondValued ↥A.orientedBaseBonds => (g b : ComplexMatrix2)) h
  · obtain ⟨T, hvT, hT⟩ := hT a
    have he : A.covDivergence complexLieAlgebra U a.1 = T.1 := epsilon_eq_of_unique hT
    rw [he]
    exact (congrArg (fun g : BondMaps.BondValued ↥A.baseSites => (g x : ComplexMatrix2)) hvT).symm
  · obtain ⟨T, hvT, hT⟩ := hT a
    have he : A.covDivergence complexLieAlgebra U a.1 = T.1 := epsilon_eq_of_unique hT
    rw [he]
    exact hT B
theorem covCurlAdjoint_isAdjoint [Finite ↥A.orientedBaseBonds] [Finite ↥A.basePlaquettes] :
    A.CovCurlAdjointIsPairingAdjoint := by
  intro U _
  let c := bondChart A
  let c' := plaquetteChart A
  let D := covCurlLinear A U
  have hD : ∀ x ∈ c.forms, D x ∈ c'.forms := covCurl_mem A U
  obtain ⟨M', hM', hT⟩ := c.exists_adjoint_transfer (t := N.eta ^ 4) (t' := N.eta ^ 4)
    (pow_pos (eta_pos N) 4) c' D hD A.bondInner A.plaquetteInner (bondInner_eq A)
    (plaquetteInner_eq A)
  refine ⟨c.transfer c' D hD, M', hM', fun a p => ?_, fun X b => ?_, fun X B => ?_⟩
  · have h := c.transfer_values c' D hD a
    exact congrArg (fun g : BondMaps.BondValued ↥A.basePlaquettes => (g p : ComplexMatrix2)) h
  · obtain ⟨T, hvT, hT⟩ := hT X
    have he : A.covCurlAdjoint complexLieAlgebra U X.1 = T.1 := epsilon_eq_of_unique hT
    rw [he]
    exact (congrArg (fun g : BondMaps.BondValued ↥A.orientedBaseBonds =>
      (g b : ComplexMatrix2)) hvT).symm
  · obtain ⟨T, hvT, hT⟩ := hT X
    have he : A.covCurlAdjoint complexLieAlgebra U X.1 = T.1 := epsilon_eq_of_unique hT
    rw [he]
    exact hT B
theorem formTranspose_isAdjoint [Finite ↥A.orientedBaseBonds] :
    A.FormTransposeIsPairingAdjoint := by
  intro C _ K
  let c := bondChart A
  have ht : 0 < N.eta ^ 4 := pow_pos (eta_pos N) 4
  let e : BondMaps.BondValued ↥A.orientedBaseBonds →ₗ[ℂ] ↥A.formSpace :=
    LinearMap.codRestrict A.formSpace c.extend c.extend_mem
  have he : ∀ a : ↥A.formSpace, e (A.formEval a) = a := fun a =>
    Subtype.ext (c.extend_values a)
  obtain ⟨M', hM'⟩ := exists_pairingAdjoint 1 ht (K ∘ₗ e)
  have hM : ∀ a, (K ∘ₗ e) (A.formEval a) = K a := fun a => congrArg K (he a)
  have hv : ∀ g, A.formEval (e g) = g := c.values_extend
  have hspec : ∀ (ω : BondMaps.BondValued C) (a : ↥A.formSpace),
      DepthChain.plainInner (K a) ω = A.bondInner a.1 (e (M' ω)).1 := by
    intro ω a
    have h1 : DepthChain.plainInner (K a) ω = scaledPairingSum 1 (K a) ω := by
      simp [DepthChain.plainInner, scaledPairingSum]
    have h2 := bondInner_eq A a (e (M' ω))
    rw [h1, ← hM a, hM' (A.formEval a) ω]
    refine Eq.trans ?_ h2.symm
    exact congrArg _ (hv _).symm
  have hiff : ∀ (ω : BondMaps.BondValued C) (B : ↥A.formSpace),
      (∀ a : ↥A.formSpace, DepthChain.plainInner (K a) ω = A.bondInner a.1 B.1) ↔
        B = e (M' ω) := by
    intro ω B
    constructor
    · intro h
      refine c.values_bijective.1 (scaledPairingSum_right_injective ht fun g => ?_)
      obtain ⟨a, rfl⟩ := c.values_bijective.2 g
      have h1 := bondInner_eq A a B
      have h2 := bondInner_eq A a (e (M' ω))
      exact h1.symm.trans (((h a).symm.trans (hspec ω a)).trans h2)
    · rintro rfl
      exact hspec ω
  have hK : ∀ ω, A.formTranspose K ω = e (M' ω) := fun ω => epsilon_eq_of_unique (hiff ω)
  refine ⟨K ∘ₗ e, M', hM', hM, fun ω => ?_, fun ω B => ?_⟩
  · rw [hK, hv]
  · rw [hK]
    exact hiff ω B
end BaseLattice
theorem baseLatticePairings_holds : LieInnerProduct.BaseLatticePairings := by
  intro L m N A
  have hS : Finite (SiteAtLevel L m N.K 0) :=
    SeparatedSequences.BaseParameters.site_finite (by have := two_le_L N; omega) m _
  have hB : Finite (BondAtLevel L m N.K 0) := bond_finite
  have hP : Finite (PlaquetteAtLevel L m N.K 0) := plaquette_finite
  exact ⟨inferInstance, inferInstance, inferInstance, innersAreScaledSums_chain A,
    formTranspose_isAdjoint A, covDivergence_isAdjoint A, covCurlAdjoint_isAdjoint A⟩
theorem statement_holds : LieInnerProduct.Statement :=
  ⟨realInnerProduct_holds, pauliExpansion_holds, pairingNondegenerate_holds,
    uniqueAdjointOfLinearMap_holds, adjointInPauliBasis_holds, onePointAndFiniteSetPairings_holds,
    baseLatticePairings_holds, periodicLatticePairings_holds⟩
end YangMills.Construction.LieInnerProductProof
