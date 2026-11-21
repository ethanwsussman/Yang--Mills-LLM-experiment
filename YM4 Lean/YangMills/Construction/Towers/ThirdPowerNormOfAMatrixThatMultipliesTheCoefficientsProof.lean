import YangMills.Construction.PeriodicOperators.OrderOfHermitianMatricesUnderARootProof
import YangMills.Construction.Towers.ActionOfTheDifferencesOnPlaneWavesProof
import YangMills.Construction.Towers.FactsOfTheMatricesOfAPeriodicFunctionProof
import YangMills.Construction.Towers.PlaneWaveCoefficientsOnTheBondsProof
import YangMills.Construction.Towers.ThirdPowerNormOfAMatrixThatMultipliesTheCoefficients
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.PlaneWaves.SchattenCubeProof
open PeriodicOperators (QuotHom PeriodicData IsQuotInvariant descendFn descendFn_mkQuot
  colourEdges colourVertices toComplexVec bilinDot wInner castVec intShift)
open TraceBound (IsHermitianForm IsOrthonormalBasisOf schattenThreeNorm)
open RealPower (rpowPos)
open PlaneWaveCalculus (WavesOrthonormalBasis posEdgeAt integerWave waveOnQuot)
open scoped ComplexOrder
section WeightedInner
variable {J : Type}
theorem wInner_apply [Fintype J] (w : J → ℝ) (f g : J → ℂ) :
    wInner w f g = ∑ i, (w i : ℂ) * (starRingEnd ℂ (f i) * g i) := by apply _root_.YangMills.Construction.PeriodicOperators.RootConjugationOrder.wInner_eq_sum <;> assumption
theorem isHermitianForm_wInner [Finite J] (w : J → ℝ) (hw : ∀ i, 0 < w i) :
    IsHermitianForm (wInner w) := by
  have := Fintype.ofFinite J
  refine ⟨fun v => ⟨fun f g => ?_, fun z f => ?_⟩, fun v u => ?_, fun v hv => ?_⟩
  · simp only [wInner_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  · simp only [wInner_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [wInner_apply, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    exact Finset.sum_congr rfl fun i _ => by ring
  · have hval : wInner w v v = ((∑ i, w i * ‖v i‖ ^ 2 : ℝ) : ℂ) := by
      rw [wInner_apply]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.conj_mul']
    rw [hval, Complex.zero_lt_real]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    refine Finset.sum_pos' (fun j _ => mul_nonneg (hw j).le (sq_nonneg _)) ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_pos (hw i) (pow_pos (norm_pos_iff.2 hi) 2)
end WeightedInner
theorem linearIndependent_of_orthonormal {E : Type} [AddCommGroup E] [Module ℂ E]
    {B : E → E → ℂ} (hB : IsHermitianForm B) {J : Type} [Fintype J] {x : J → E}
    (hself : ∀ j, B (x j) (x j) = 1) (hoff : ∀ j l, j ≠ l → B (x j) (x l) = 0) :
    LinearIndependent ℂ x := by
  classical
  refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
  have hsum : B (x i) (∑ j, g j • x j) = g i := by
    have hmap := map_sum ((hB.linear_right (x i)).mk' (B (x i))) (fun j => g j • x j) Finset.univ
    simp only [IsLinearMap.mk'_apply] at hmap
    rw [hmap, Finset.sum_eq_single i]
    · rw [(hB.linear_right (x i)).map_smul, hself, smul_eq_mul, mul_one]
    · intro j _ hj
      rw [(hB.linear_right (x i)).map_smul, hoff i j hj.symm, smul_zero]
    · simp
  rw [← hsum, hg]
  exact (hB.linear_right (x i)).map_zero
theorem schattenCube_of_diagonal (h6 : TraceBound.TraceSixFoldProductBound)
    {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    {B : E → E → ℂ} (hB : IsHermitianForm B) {J : Type} [Fintype J] [Nonempty J] {x : J → E}
    (hself : ∀ j, B (x j) (x j) = 1) (hoff : ∀ j l, j ≠ l → B (x j) (x l) = 0)
    (hspan : Submodule.span ℂ (Set.range x) = ⊤) (M : Module.End ℂ E) (a : J → ℂ)
    (hM : ∀ j, M (x j) = a j • x j) :
    rpowPos (schattenThreeNorm B M) 3 = ∑ j, rpowPos ‖a j‖ 3 := by
  classical
  have hli := linearIndependent_of_orthonormal hB hself hoff
  let b : Module.Basis J ℂ E := Module.Basis.mk hli hspan.ge
  have hb : ⇑b = x := Module.Basis.coe_mk hli hspan.ge
  have hrank : Module.finrank ℂ E = Fintype.card J := Module.finrank_eq_card_basis b
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hN : 1 ≤ Fintype.card J := Fintype.card_pos
  have hdiag := (h6 (Fintype.card J) hN E hrank B hB).2.1 M (fun j => x (e j)) (fun j => a (e j))
    ⟨⟨b.reindex e.symm, funext fun j => by simp [hb]⟩,
      fun j => hself (e j), fun j l hjl => hoff (e j) (e l) fun h => hjl (e.injective h)⟩
    (fun j => hM (e j))
  rw [hdiag.2]
  exact e.sum_comp fun j => rpowPos ‖a j‖ 3
theorem schattenCube_of_waves (h6 : TraceBound.TraceSixFoldProductBound) (L k : ℕ)
    (I : PeriodicData) [Finite I.UnitQuot] {C : Type} [Fintype C] [Nonempty C]
    {carries : C → I.Carrier → Prop} (hbasis : WavesOrthonormalBasis L k I carries)
    (hw : ∀ c, 0 < I.quotWeight 1 c) (hne : (freqBox L k).Nonempty)
    (A : QuotHom I I) (T : (Fin 4 → ℤ) → ℂ)
    (hA : ∀ c, ∀ m ∈ freqBox L k,
      A (waveOnQuot I (carries c) m) = T m • waveOnQuot I (carries c) m) :
    rpowPos (schattenThreeNorm (wInner (I.quotWeight 1)) A) 3 =
      (Fintype.card C : ℝ) * ∑ m ∈ freqBox L k, rpowPos ‖T m‖ 3 := by
  classical
  have : Nonempty {m // m ∈ freqBox L k} := hne.to_subtype
  let x : C × {m // m ∈ freqBox L k} → I.UnitQuot → ℂ :=
    fun j => waveOnQuot I (carries j.1) j.2.1
  have hrange : Set.range x =
      {f | ∃ c : C, ∃ m ∈ freqBox L k, f = waveOnQuot I (carries c) m} := by
    ext f
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.1, j.2.1, j.2.2, rfl⟩
    · rintro ⟨c, m, hm, rfl⟩
      exact ⟨(c, ⟨m, hm⟩), rfl⟩
  have hmain := schattenCube_of_diagonal h6 (isHermitianForm_wInner (I.quotWeight 1) hw) (x := x)
    (fun j => by
      have := hbasis.1 j.1 j.1 j.2.1 j.2.2 j.2.1 j.2.2
      simpa [x] using this)
    (fun j l hjl => by
      have := hbasis.1 j.1 l.1 j.2.1 j.2.2 l.2.1 l.2.2
      rw [if_neg] at this
      · exact this
      · rintro ⟨h1, h2⟩
        exact hjl (Prod.ext h1 (Subtype.ext h2)))
    (by rw [hrange]; exact hbasis.2) A (fun j => T j.2.1)
    (fun j => hA j.1 j.2.1 j.2.2)
  rw [hmain, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  exact Finset.sum_coe_sort (freqBox L k) fun m => rpowPos ‖T m‖ 3
theorem isQuotInvariant_of_translate (I : PeriodicData) {f : I.Carrier → ℂ}
    (h : ∀ n ι, f (I.translate n ι) = f ι) : IsQuotInvariant I f := by apply _root_.YangMills.Construction.Tower.EdgeWaves.isQuotInvariant_of_forall <;> assumption
theorem quotWeight_eq_of_const (I : PeriodicData) {w : ℝ} (hw : ∀ ι, I.weightOf ι = w)
    (c : I.UnitQuot) : I.quotWeight 1 c = w := by apply _root_.YangMills.Construction.Tower.PlaneWaveCoboundaries.quotWeight_of_const <;> assumption
theorem integerWave_add_castVec (m n : Fin 4 → ℤ) (y : InfiniteLattice.AmbientSpace) :
    integerWave m (y + castVec n) = integerWave m y := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.integerWave_add_castVec <;> assumption
open Classical in
theorem waveOnQuot_mkQuot (I : PeriodicData) {carries : I.Carrier → Prop}
    (hcar : ∀ n ι, carries (I.translate n ι) ↔ carries ι)
    (hpos : ∀ n ι, I.pos (I.translate n ι) = I.pos ι + castVec n)
    (m : Fin 4 → ℤ) (ι : I.Carrier) :
    waveOnQuot I carries m (I.mkQuot 1 ι) =
      if carries ι then integerWave m (I.pos ι) else 0 := by
  rw [waveOnQuot]
  refine descendFn_mkQuot (isQuotInvariant_of_translate I fun n ι' => ?_) ι
  simp only [hcar, hpos, integerWave_add_castVec]
theorem pauliFamily_coeffs_injective {x y : Fin 3 → ℂ}
    (h : ∑ a, x a • Matrices.ComplexMatrix2.pauliFamily a =
      ∑ a, y a • Matrices.ComplexMatrix2.pauliFamily a) : x = y := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.pauliFamily_sum_injective <;> assumption
theorem map_wave_eq_smul {V Lb S : Type} [AddCommGroup V] [Module ℂ V] [DecidableEq Lb]
    {F : Finset (Fin 4 → ℤ)} (u : (Fin 4 → ℤ) → S → ℂ)
    (read : V → Lb → S → Matrices.ComplexMatrix2)
    (coeff : V → Lb → (Fin 4 → ℤ) → Matrices.ComplexMatrix2)
    (expansion : ∀ b μ x, read b μ x = ∑ m ∈ F, u m x • coeff b μ m)
    (read_smul : ∀ (z : ℂ) b μ x, read (z • b) μ x = z • read b μ x)
    (read_injective : ∀ b b', (∀ μ x, read b μ x = read b' μ x) → b = b')
    (independent : ∀ Y : (Fin 4 → ℤ) → Matrices.ComplexMatrix2,
      (∀ x, ∑ m ∈ F, u m x • Y m = 0) → ∀ m ∈ F, Y m = 0)
    (A : V →ₗ[ℂ] V) (T : (Fin 4 → ℤ) → ℂ)
    (hA : ∀ b μ, ∀ m ∈ F, coeff (A b) μ m = T m • coeff b μ m)
    {w : V} {μ₀ : Lb} {m₀ : Fin 4 → ℤ} (hm₀ : m₀ ∈ F) {P : Matrices.ComplexMatrix2}
    (hw : ∀ μ x, read w μ x = if μ = μ₀ then u m₀ x • P else 0) :
    A w = T m₀ • w := by
  classical
  have hcoeff : ∀ μ, ∀ m ∈ F, coeff w μ m = if μ = μ₀ ∧ m = m₀ then P else 0 := by
    intro μ m hm
    have hzero := independent (fun m => coeff w μ m - if μ = μ₀ ∧ m = m₀ then P else 0)
      (fun x => by
        simp only [smul_sub, Finset.sum_sub_distrib, ← expansion, hw]
        by_cases hμ : μ = μ₀
        · simp [hμ, hm₀]
        · simp [hμ]) m hm
    exact sub_eq_zero.1 hzero
  refine read_injective _ _ fun μ x => ?_
  have hsum : ∑ m ∈ F, u m x • coeff (A w) μ m =
      ∑ m ∈ F, u m x • (T m • if μ = μ₀ ∧ m = m₀ then P else 0) :=
    Finset.sum_congr rfl fun m hm => by rw [hA w μ m hm, hcoeff μ m hm]
  rw [expansion, hsum, read_smul, hw]
  by_cases hμ : μ = μ₀
  · simp [hμ, hm₀, smul_comm (T m₀) (u m₀ x) P]
  · simp [hμ]
section Lattice
variable {L k : ℕ}
theorem waves_linearIndependent [Finite (colourVertices L k 0).UnitQuot]
    (hs : PlaneWaveCalculus.VertexCoeffFacts L k)
    (hweight : ∀ c, 0 < (colourVertices L k 0).quotWeight 1 c)
    (hval : ∀ (a a' : Fin 3) (m : Fin 4 → ℤ) (x : FullSpace.Vertex L k 0),
      waveOnQuot (colourVertices L k 0) (fun ι => ι.1 = a) m
          ((colourVertices L k 0).mkQuot 1 (a', x)) =
        if a' = a then integerWave m x else 0)
    (Y : (Fin 4 → ℤ) → Matrices.ComplexMatrix2)
    (hY : ∀ x : FullSpace.Vertex L k 0, ∑ m ∈ freqBox L k, integerWave m x • Y m = 0) :
    ∀ m ∈ freqBox L k, Y m = 0 := by
  classical
  intro m hm
  let v : {m // m ∈ freqBox L k} → (colourVertices L k 0).UnitQuot → ℂ :=
    fun m => waveOnQuot (colourVertices L k 0) (fun ι => ι.1 = (0 : Fin 3)) m.1
  have hli : LinearIndependent ℂ v :=
    linearIndependent_of_orthonormal (isHermitianForm_wInner _ hweight)
      (fun j => by
        have := hs.basis.1 0 0 j.1 j.2 j.1 j.2
        simpa [v] using this)
      (fun j l hjl => by
        have := hs.basis.1 0 0 j.1 j.2 l.1 l.2
        rw [if_neg] at this
        · exact this
        · rintro ⟨-, h⟩
          exact hjl (Subtype.ext h))
  refine Matrix.ext fun i j => ?_
  let ent : Matrices.ComplexMatrix2 →ₗ[ℂ] ℂ := Matrix.entryLinearMap ℂ ℂ i j
  have hzero := Fintype.linearIndependent_iff.1 hli (fun m => ent (Y m.1)) (by
    funext c
    induction c using Quot.ind with
    | mk ι =>
      obtain ⟨a, x⟩ := ι
      have hentry : ∑ m ∈ freqBox L k, integerWave m x * ent (Y m) = 0 := by
        have := congrArg ent (hY x)
        simpa only [map_sum, map_smul, map_zero, smul_eq_mul] using this
      have hread : ∀ m : {m // m ∈ freqBox L k},
          v m ((colourVertices L k 0).mkQuot 1 (a, x)) =
            if a = 0 then integerWave m.1 x else 0 := fun m => hval 0 a m.1 x
      change (∑ m, ent (Y m.1) • v m) ((colourVertices L k 0).mkQuot 1 (a, x)) = 0
      generalize (colourVertices L k 0).mkQuot 1 (a, x) = c₀ at hread ⊢
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hread]
      by_cases ha : a = 0
      · simp only [ha, if_true]
        rw [Finset.sum_coe_sort (freqBox L k) fun m => ent (Y m) * integerWave m x]
        simpa [mul_comm] using hentry
      · simp [ha]) ⟨m, hm⟩
  exact hzero
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {μ ν : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ν) : μ = ν := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
theorem carries_iff_displacement (c : Fin 3 × Fin 4)
    (ι : Fin 3 × PeriodicOperators.PosEdge L k 0) :
    (ι.1 = c.1 ∧ ∃ x, ι.2 = posEdgeAt L k 0 x c.2) ↔
      ι.1 = c.1 ∧ ι.2.1.terminal - ι.2.1.initial = InfiniteLattice.axisStep (meshAt L k 0) c.2 := by
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨ι.2.1.initial, Subtype.ext ?_⟩⟩
  · rintro ⟨x, hx⟩
    rw [hx]
    simp [posEdgeAt, InfiniteLattice.Link.forwardFrom]
  · refine InfiniteLattice.Link.ext rfl ?_
    change ι.2.1.terminal = ι.2.1.initial + InfiniteLattice.axisStep (meshAt L k 0) c.2
    rw [← h]
    abel
variable (ht : PeriodicOperators.TowerTranslations.Claim)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
include ht hL hk
theorem vertex_waveOnQuot (a a' : Fin 3) (m : Fin 4 → ℤ) (x : FullSpace.Vertex L k 0) :
    waveOnQuot (colourVertices L k 0) (fun ι => ι.1 = a) m
        ((colourVertices L k 0).mkQuot 1 (a', x)) =
      if a' = a then integerWave m x else 0 := by
  classical
  rw [waveOnQuot_mkQuot (colourVertices L k 0) (fun _ _ => Iff.rfl)
    (fun n ι => ((ht L hL k 0 hk (Nat.zero_le _) n).2.1 ι.2).1) m (a', x)]
  by_cases h : a' = a
  · simp only [h, if_true]
    rfl
  · simp [h]
theorem edge_translate_displacement (n : Fin 4 → ℤ)
    (ι : Fin 3 × PeriodicOperators.PosEdge L k 0) :
    (((colourEdges L k 0).translate n ι : Fin 3 × PeriodicOperators.PosEdge L k 0).2.1.terminal -
        ((colourEdges L k 0).translate n ι :
          Fin 3 × PeriodicOperators.PosEdge L k 0).2.1.initial) =
      ι.2.1.terminal - ι.2.1.initial ∧
    ((((colourEdges L k 0).translate n ι :
        Fin 3 × PeriodicOperators.PosEdge L k 0).2.1.initial : FullSpace.Vertex L k 0) :
          InfiniteLattice.AmbientSpace) = (ι.2.1.initial : InfiniteLattice.AmbientSpace) + castVec n := by
  obtain ⟨c, b⟩ := ι
  obtain ⟨μ, hμ⟩ := b.2
  have hclauses := ht L hL k 0 hk (Nat.zero_le _) n
  rw [hclauses.2.2.2.1 c b μ hμ]
  refine ⟨?_, (hclauses.2.1 b.1.initial).1⟩
  exact (add_sub_cancel_left (FullSpace.vertexImage (intShift n) b.1.initial)
    (InfiniteLattice.axisStep (meshAt L k 0) μ)).trans hμ.symm
theorem edge_waveOnQuot (c : Fin 3 × Fin 4) (a : Fin 3) (μ : Fin 4) (m : Fin 4 → ℤ)
    (x : FullSpace.Vertex L k 0) :
    waveOnQuot (colourEdges L k 0)
        (fun ι => ι.1 = c.1 ∧ ∃ x, ι.2 = posEdgeAt L k 0 x c.2) m
        ((colourEdges L k 0).mkQuot 1 (a, edgeAt L k x μ)) =
      if a = c.1 ∧ μ = c.2 then integerWave m x else 0 := by
  classical
  have hη : meshAt L k 0 ≠ 0 := by
    have hpos : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    exact (zpow_pos hpos _).ne'
  rw [waveOnQuot_mkQuot (colourEdges L k 0)
    (fun n ι => (carries_iff_displacement c ((colourEdges L k 0).translate n ι)).trans
      ((and_congr Iff.rfl (iff_of_eq (congrArg
        (fun z => z = InfiniteLattice.axisStep (meshAt L k 0) c.2)
        (edge_translate_displacement ht hL hk n ι).1))).trans
          (carries_iff_displacement c ι).symm))
    (fun n ι => (edge_translate_displacement ht hL hk n ι).2) m (a, edgeAt L k x μ)]
  have hiff : (a = c.1 ∧ ∃ y, edgeAt L k x μ = posEdgeAt L k 0 y c.2) ↔
      a = c.1 ∧ μ = c.2 := by
    rw [show (a = c.1 ∧ ∃ y, edgeAt L k x μ = posEdgeAt L k 0 y c.2) ↔ _ from
      carries_iff_displacement c (a, edgeAt L k x μ)]
    refine and_congr_right fun _ => ⟨fun h => axisStep_injective hη ?_, fun h => ?_⟩
    · rw [← h]
      simp [edgeAt, InfiniteLattice.Link.forwardFrom]
    · rw [← h]
      simp [edgeAt, InfiniteLattice.Link.forwardFrom]
  by_cases h : a = c.1 ∧ μ = c.2
  · rw [if_pos (hiff.2 h), if_pos h]
    rfl
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
omit ht hL hk
theorem edgeField_injective {b b' : (colourEdges L k 0).UnitQuot → ℂ}
    (h : ∀ μ x, edgeFieldOfClasses L k b (edgeAt L k x μ) =
      edgeFieldOfClasses L k b' (edgeAt L k x μ)) :
    b = b' := by
  funext c
  induction c using Quot.ind with
  | mk ι =>
    obtain ⟨a, β⟩ := ι
    obtain ⟨μ, hμ⟩ := β.2
    have hβ : edgeAt L k β.1.initial μ = β := by
      refine Subtype.ext (InfiniteLattice.Link.ext rfl ?_)
      change β.1.initial + InfiniteLattice.axisStep _ μ = β.1.terminal
      rw [← hμ]
      abel
    have hx := congrFun (pauliFamily_coeffs_injective
      (x := fun a => b ((colourEdges L k 0).mkQuot 1 (a, edgeAt L k β.1.initial μ)))
      (y := fun a => b' ((colourEdges L k 0).mkQuot 1 (a, edgeAt L k β.1.initial μ)))
      (h μ β.1.initial)) a
    simp only [hβ] at hx
    exact hx
theorem vertexField_injective {l l' : (colourVertices L k 0).UnitQuot → ℂ}
    (h : ∀ x, vertexFieldOfClasses L k l x = vertexFieldOfClasses L k l' x) : l = l' := by
  funext c
  induction c using Quot.ind with
  | mk ι =>
    obtain ⟨a, x⟩ := ι
    exact congrFun (pauliFamily_coeffs_injective
      (x := fun a => l ((colourVertices L k 0).mkQuot 1 (a, x)))
      (y := fun a => l' ((colourVertices L k 0).mkQuot 1 (a, x))) (h x)) a
theorem freqBox_nonempty (hL : Conventions.IsAdmissibleBlockingFactor L) :
    (freqBox L k).Nonempty := by
  refine ⟨0, (mem_freqBox L k 0).2 fun ν => ?_⟩
  have hinv : (finestMesh L k)⁻¹ = (L : ℝ) ^ k := by
    simp [finestMesh, meshAt, zpow_neg]
  have hone : (1 : ℝ) ≤ (L : ℝ) ^ k := by
    refine one_le_pow₀ ?_
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  rw [hinv]
  simp only [Pi.zero_apply, Int.cast_zero, abs_zero]
  linarith
end Lattice
theorem scalingMatrixSchattenCube_holds (h6 : TraceBound.TraceSixFoldProductBound)
    (hb : PlaneWaveEdgeCoefficientsHold)
    (hs : PlaneWaveCalculus.VertexCoeffsHold)
    (ht : PeriodicOperators.TowerTranslations.Claim) : ScalingMatrixSchattenCube := by
  intro L hL k hk _ _ t κ
  have hcb := hb L hL k hk
  have hcs := hs L hL k hk
  have hpos : 0 < meshAt L k 0 ^ 4 := by
    have h0 : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    exact pow_pos (zpow_pos h0 _) 4
  have hwb : ∀ c, 0 < (colourEdges L k 0).quotWeight 1 c := fun c => by
    rw [quotWeight_eq_of_const (colourEdges L k 0) (w := meshAt L k 0 ^ 4) (fun _ => rfl) c]
    exact hpos
  have hws : ∀ c, 0 < (colourVertices L k 0).quotWeight 1 c := fun c => by
    rw [quotWeight_eq_of_const (colourVertices L k 0) (w := meshAt L k 0 ^ 4) (fun _ => rfl) c]
    exact hpos
  have hne : (freqBox L k).Nonempty := freqBox_nonempty hL
  have hind := waves_linearIndependent hcs hws (vertex_waveOnQuot ht hL hk)
  refine ⟨fun A hA => ?_, fun A hA => ?_⟩
  · have hmain := schattenCube_of_waves h6 L k (colourEdges L k 0) hcb.basis hwb hne A
      (fun m => t (shiftedFreq κ m)) (fun c m hm => by
        refine map_wave_eq_smul (F := freqBox L k) (S := FullSpace.Vertex L k 0)
          (fun m x => integerWave m x)
          (fun b μ x => edgeFieldOfClasses L k b (edgeAt L k x μ))
          (fun b μ m => edgeFourierCoeff L k b μ m)
          (fun b μ x => hcb.expansion b μ x) ?_ (fun _ _ h => edgeField_injective h) hind A
          (fun m => t (shiftedFreq κ m)) (fun b μ m hm => hA b μ m hm)
          (μ₀ := c.2) hm (P := Matrices.ComplexMatrix2.pauliFamily c.1) ?_
        · intro z b μ x
          simp only [edgeFieldOfClasses, ofPauliCoeffs, Pi.smul_apply, Finset.smul_sum, smul_smul,
            smul_eq_mul]
        · intro μ x
          simp only [edgeFieldOfClasses, ofPauliCoeffs]
          simp only [edge_waveOnQuot ht hL hk]
          by_cases hμ : μ = c.2
          · simp [hμ]
          · simp [hμ])
    rw [hmain]
    simp [Fintype.card_prod]
  · have hmain := schattenCube_of_waves h6 L k (colourVertices L k 0) hcs.basis hws hne A
      (fun m => t (shiftedFreq κ m)) (fun a m hm => by
        refine map_wave_eq_smul (F := freqBox L k) (S := FullSpace.Vertex L k 0)
          (Lb := Unit) (fun m x => integerWave m x)
          (fun l _ x => vertexFieldOfClasses L k l x)
          (fun l _ m => vertexFourierCoeff L k l m)
          (fun l _ x => hcs.expansion l x) ?_ (fun _ _ h => vertexField_injective (h ())) hind A
          (fun m => t (shiftedFreq κ m)) (fun l _ m hm => hA l m hm)
          (μ₀ := ()) hm (P := Matrices.ComplexMatrix2.pauliFamily a) ?_
        · intro z l _ x
          simp only [vertexFieldOfClasses, ofPauliCoeffs, Pi.smul_apply, Finset.smul_sum, smul_smul,
            smul_eq_mul]
        · intro _ x
          simp only [vertexFieldOfClasses, ofPauliCoeffs]
          simp only [vertex_waveOnQuot ht hL hk]
          simp)
    rw [hmain]
    simp
end YangMills.Construction.Tower.PlaneWaves.SchattenCubeProof
end
