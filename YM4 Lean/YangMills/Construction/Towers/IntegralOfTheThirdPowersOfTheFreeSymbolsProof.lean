import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.Towers.ElementaryBoundsOfThePlaneWaveFunctions
import YangMills.Construction.Towers.IntegralOfTheThirdPowersOfTheFreeSymbols
import YangMills.Construction.Towers.TheMassiveJetsProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.Tower.FreeResolvents.CubicSumIntegral
open YangMills.Construction.PeriodicOperators (toComplexVec imStrip)
open YangMills.Construction.Tower.PlaneWaves
open YangMills.Construction.Tower.PlaneWaves.PlaneWaveBounds (complexPoint realSymbolSquare SymbolBounds)
open YangMills.Construction.RealPower (rpowPos)
open YangMills.Construction.Conventions (IsAdmissibleBlockingFactor)
theorem continuous_decayMajorant : Continuous decayMajorant := by
  have hc : Continuous fun q : Fin 4 → ℝ => (1 + 4 / Real.pi ^ 2 * ∑ ν, q ν ^ 2) ^ 3 := by
    fun_prop
  refine hc.inv₀ fun q => ?_
  have : 0 ≤ 4 / Real.pi ^ 2 * ∑ ν, q ν ^ 2 := by positivity
  positivity
theorem decayMajorant_nonneg (q : Fin 4 → ℝ) : 0 ≤ decayMajorant q := by
  unfold decayMajorant
  positivity
theorem sq_norm_le_sum_sq (q : Fin 4 → ℝ) : ‖q‖ ^ 2 ≤ ∑ ν, q ν ^ 2 := by
  have hs : 0 ≤ ∑ ν, q ν ^ 2 := by positivity
  have h : ‖q‖ ≤ Real.sqrt (∑ ν, q ν ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun ν => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun ν => q ν ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ ν))
  calc ‖q‖ ^ 2 ≤ Real.sqrt (∑ ν, q ν ^ 2) ^ 2 := by gcongr
    _ = ∑ ν, q ν ^ 2 := Real.sq_sqrt hs
theorem decayMajorant_le_rpow (q : Fin 4 → ℝ) :
    decayMajorant q ≤ 512 * (1 + ‖q‖) ^ (-(6 : ℝ)) := by
  have hpi : Real.pi ^ 2 ≤ 16 := by
    have := Real.pi_le_four
    have := Real.pi_pos
    nlinarith
  have hc : 1 / 4 ≤ 4 / Real.pi ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  have hs := sq_norm_le_sum_sq q
  have hA : (1 + ‖q‖) ^ 2 / 8 ≤ 1 + 4 / Real.pi ^ 2 * ∑ ν, q ν ^ 2 := by
    have h1 : 1 / 4 * ‖q‖ ^ 2 ≤ 4 / Real.pi ^ 2 * ∑ ν, q ν ^ 2 :=
      mul_le_mul hc hs (sq_nonneg _) (by positivity)
    nlinarith [sq_nonneg (1 - ‖q‖)]
  have hC : ((1 + ‖q‖) ^ 2 / 8) ^ 3 ≤ (1 + 4 / Real.pi ^ 2 * ∑ ν, q ν ^ 2) ^ 3 := by gcongr
  have hrp : (1 + ‖q‖) ^ (-(6 : ℝ)) = (((1 + ‖q‖) ^ 6)⁻¹ : ℝ) := by
    rw [Real.rpow_neg (by positivity)]
    norm_num
  rw [hrp]
  unfold decayMajorant
  calc ((1 + 4 / Real.pi ^ 2 * ∑ ν, q ν ^ 2) ^ 3)⁻¹ ≤ (((1 + ‖q‖) ^ 2 / 8) ^ 3)⁻¹ :=
        inv_anti₀ (by positivity) hC
    _ = 512 * ((1 + ‖q‖) ^ 6)⁻¹ := by
        field_simp
        norm_num
theorem integrable_decayMajorant : Integrable decayMajorant := by
  have hr : (Module.finrank ℝ (Fin 4 → ℝ) : ℝ) < 6 := by
    simp only [Module.finrank_fin_fun]
    norm_num
  have h := (integrable_one_add_norm (μ := (volume : Measure (Fin 4 → ℝ))) hr).const_mul 512
  refine h.mono' continuous_decayMajorant.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_of_nonneg (decayMajorant_nonneg q)]
  exact decayMajorant_le_rpow q
def invCubeNorm (L k : ℕ) (q : Fin 4 → ℂ) : ℝ := ‖symbolSquare L k q + 1‖⁻¹ ^ 3
theorem invCubeNorm_nonneg (L k : ℕ) (q : Fin 4 → ℂ) : 0 ≤ invCubeNorm L k q := by
  unfold invCubeNorm
  positivity
theorem rpowPos_norm_shiftedSymbolPow (L k : ℕ) (q : Fin 4 → ℂ)
    (h : symbolSquare L k q + 1 ≠ 0) :
    rpowPos ‖shiftedSymbolPow L k (-1) q‖ 3 = invCubeNorm L k q := by
  have hpos : 0 < ‖symbolSquare L k q + 1‖ := norm_pos_iff.mpr h
  have hn : ‖shiftedSymbolPow L k (-1) q‖ = ‖symbolSquare L k q + 1‖⁻¹ := by
    unfold shiftedSymbolPow principalRpow
    have he : Complex.I * ((-1 : ℝ) : ℂ) * (rightHalfPlaneArg (symbolSquare L k q + 1) : ℂ) =
        ((-rightHalfPlaneArg (symbolSquare L k q + 1) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.rpow_neg_one]
  have hy : 0 < ‖symbolSquare L k q + 1‖⁻¹ := inv_pos.mpr hpos
  rw [hn, invCubeNorm, rpowPos, if_pos hy, mul_comm, ← Real.rpow_def_of_pos hy]
  exact_mod_cast Real.rpow_natCast _ 3
theorem continuous_symbolSquare (L k : ℕ) : Continuous (symbolSquare L k) := by
  unfold symbolSquare
  refine continuous_finsetSum _ fun μ _ => ?_
  simp only [forwardSymbol, Pi.neg_apply]
  fun_prop
theorem continuous_toComplexVec : Continuous toComplexVec := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.continuous_toComplexVec <;> assumption
theorem add_mem_imStrip {ϑ : Fin 4 → ℂ} (hϑ : ϑ ∈ imStrip (1 / 8))
    (κ : InfiniteLattice.AmbientSpace) : toComplexVec κ + ϑ ∈ imStrip (1 / 8) := by
  intro μ
  simpa [toComplexVec] using hϑ μ
theorem symbolSquare_shiftedFreq_add_one_ne_zero (hG : FreeResolventRoots) {L k : ℕ}
    (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip (1 / 8))
    {m : Fin 4 → ℤ} (hm : m ∈ freqBox L k) : symbolSquare L k (shiftedFreq κ m) + 1 ≠ 0 := by
  intro h0
  have := (hG L hL k hk).1 κ hκ m hm
  rw [h0] at this
  norm_num at this
theorem cubicResolventSum_eq_sum (hG : FreeResolventRoots) {L k : ℕ}
    (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {ϑ : Fin 4 → ℂ} (hϑ : ϑ ∈ imStrip (1 / 8))
    (κ : InfiniteLattice.AmbientSpace) :
    cubicResolventSum L k ϑ κ =
      ∑ m ∈ freqBox L k, invCubeNorm L k (shiftedFreq (toComplexVec κ + ϑ) m) :=
  Finset.sum_congr rfl fun _ hm =>
    rpowPos_norm_shiftedSymbolPow L k _
      (symbolSquare_shiftedFreq_add_one_ne_zero hG hL hk (add_mem_imStrip hϑ κ) hm)
def periodHom (P : ℝ) : (Fin 4 → ℤ) →+ (Fin 4 → ℝ) where
  toFun n := fun ν => (n ν : ℝ) * P
  map_zero' := by
    funext ν
    simp
  map_add' a b := by
    funext ν
    simp [add_mul]
theorem periodHom_apply (P : ℝ) (n : Fin 4 → ℤ) (ν : Fin 4) :
    periodHom P n ν = (n ν : ℝ) * P := rfl
def halfOpenCube (P : ℝ) (a : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  Set.pi univ fun ν => Ico (a ν) (a ν + P)
theorem mem_halfOpenCube {P : ℝ} {a x : Fin 4 → ℝ} :
    x ∈ halfOpenCube P a ↔ ∀ ν, a ν ≤ x ν ∧ x ν < a ν + P := by
  simp only [halfOpenCube, mem_pi, mem_univ, forall_true_left, mem_Ico]
theorem measurableSet_halfOpenCube (P : ℝ) (a : Fin 4 → ℝ) : MeasurableSet (halfOpenCube P a) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico
theorem integrableOn_halfOpenCube {g : (Fin 4 → ℝ) → ℝ} (hg : Continuous g) (P : ℝ)
    (a : Fin 4 → ℝ) : IntegrableOn g (halfOpenCube P a) volume := by
  refine (hg.integrableOn_Icc (a := a) (b := fun ν => a ν + P)).mono_set fun x hx => ?_
  have h := mem_halfOpenCube.mp hx
  exact ⟨fun ν => (h ν).1, fun ν => (h ν).2.le⟩
instance (P : ℝ) : Countable (periodHom P).range :=
  (periodHom P).rangeRestrict_surjective.countable
theorem isAddFundamentalDomain_halfOpenCube {P : ℝ} (hP : 0 < P) (a : Fin 4 → ℝ) :
    IsAddFundamentalDomain (periodHom P).range (halfOpenCube P a) volume := by
  refine IsAddFundamentalDomain.mk' (measurableSet_halfOpenCube P a).nullMeasurableSet fun x => ?_
  choose n hn huniq using fun ν => existsUnique_add_zsmul_mem_Ico hP (x ν) (a ν)
  have key : ∀ n' : Fin 4 → ℤ,
      ((⟨periodHom P n', n', rfl⟩ : (periodHom P).range) +ᵥ x ∈ halfOpenCube P a) ↔
        ∀ ν, x ν + n' ν • P ∈ Ico (a ν) (a ν + P) := by
    intro n'
    simp only [halfOpenCube, mem_pi, mem_univ, forall_true_left]
    refine forall_congr' fun ν => ?_
    have h : ((⟨periodHom P n', n', rfl⟩ : (periodHom P).range) +ᵥ x) ν = x ν + n' ν • P := by
      change (periodHom P n' + x) ν = _
      simp [periodHom_apply, add_comm]
    rw [h]
  refine ⟨⟨periodHom P n, n, rfl⟩, (key n).mpr hn, ?_⟩
  rintro ⟨_, n', rfl⟩ h
  have h' := (key n').mp h
  have hn' : n' = n := funext fun ν => huniq ν _ (h' ν)
  subst hn'
  rfl
theorem setIntegral_halfOpenCube_add (g : (Fin 4 → ℝ) → ℝ) (P : ℝ) (a v : Fin 4 → ℝ) :
    ∫ x in halfOpenCube P a, g (x + v) = ∫ x in halfOpenCube P (a + v), g x := by
  have h := (measurePreserving_add_right (volume : Measure (Fin 4 → ℝ)) v).setIntegral_preimage_emb
    (measurableEmbedding_addRight v) g (halfOpenCube P (a + v))
  have hs : (fun x => x + v) ⁻¹' halfOpenCube P (a + v) = halfOpenCube P a := by
    ext x
    simp only [mem_preimage, mem_halfOpenCube, Pi.add_apply]
    refine forall_congr' fun ν => ?_
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hs] at h
  exact h
theorem forwardSymbol_add_period {L k : ℕ} (hη : finestMesh L k ≠ 0) (q : Fin 4 → ℂ)
    (n : Fin 4 → ℤ) :
    forwardSymbol L k (q + toComplexVec (periodHom (2 * Real.pi * (finestMesh L k)⁻¹) n)) =
      forwardSymbol L k q := by
  funext μ
  have hc : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη
  have he : Complex.I * ((finestMesh L k : ℝ) : ℂ) *
        (q + toComplexVec (periodHom (2 * Real.pi * (finestMesh L k)⁻¹) n)) μ =
      Complex.I * ((finestMesh L k : ℝ) : ℂ) * q μ +
        (n μ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp only [Pi.add_apply, toComplexVec, periodHom_apply]
    push_cast
    field_simp
  simp only [forwardSymbol]
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem invCubeNorm_add_period {L k : ℕ} (hη : finestMesh L k ≠ 0) (q : Fin 4 → ℂ)
    (n : Fin 4 → ℤ) :
    invCubeNorm L k (q + toComplexVec (periodHom (2 * Real.pi * (finestMesh L k)⁻¹) n)) =
      invCubeNorm L k q := by
  have hneg : -(q + toComplexVec (periodHom (2 * Real.pi * (finestMesh L k)⁻¹) n)) =
      -q + toComplexVec (periodHom (2 * Real.pi * (finestMesh L k)⁻¹) (-n)) := by
    funext μ
    simp only [Pi.add_apply, Pi.neg_apply, toComplexVec, periodHom_apply]
    push_cast
    ring
  unfold invCubeNorm symbolSquare
  simp only [forwardSymbol_add_period hη, hneg]
theorem invCubeNorm_complexPoint_le {L k : ℕ} {y θ : Fin 4 → ℝ} (B : SymbolBounds L k y θ) :
    invCubeNorm L k (complexPoint y θ) ≤ (10 / 9) ^ 3 * decayMajorant y := by
  obtain ⟨B1, B2, B3, -⟩ := B
  have hD : 4 / Real.pi ^ 2 * ∑ ν, y ν ^ 2 ≤ realSymbolSquare L k y := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ν _ => ?_
    have h1 := (B1 ν).1
    calc 4 / Real.pi ^ 2 * y ν ^ 2 = (2 / Real.pi * |y ν|) ^ 2 := by
          rw [mul_pow, sq_abs]
          norm_num [div_pow]
      _ ≤ _ := by gcongr
  set A : ℝ := 1 + 4 / Real.pi ^ 2 * ∑ ν, y ν ^ 2 with hA
  have hA1 : 0 < A := by
    have : 0 ≤ 4 / Real.pi ^ 2 * ∑ ν, y ν ^ 2 := by positivity
    linarith
  have hw : 9 / 10 * A ≤ ‖symbolSquare L k (complexPoint y θ) + 1‖ := by
    have : 9 / 10 * A ≤ 9 / 10 * (realSymbolSquare L k y + 1) := by
      rw [hA]
      linarith
    linarith
  unfold invCubeNorm decayMajorant
  rw [← hA]
  calc ‖symbolSquare L k (complexPoint y θ) + 1‖⁻¹ ^ 3 ≤ (9 / 10 * A)⁻¹ ^ 3 := by
        gcongr
    _ = (10 / 9) ^ 3 * (A ^ 3)⁻¹ := by
        field_simp
theorem finestMesh_pos {L : ℕ} (hL : IsAdmissibleBlockingFactor L) (k : ℕ) :
    0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.finestMesh_pos <;> assumption
theorem finestMesh_le_one {L : ℕ} (hL : IsAdmissibleBlockingFactor L) (k : ℕ) :
    finestMesh L k ≤ 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.finestMesh_le_one <;> assumption
theorem zero_mem_freqBox {L : ℕ} (hL : IsAdmissibleBlockingFactor L) (k : ℕ) :
    (0 : Fin 4 → ℤ) ∈ freqBox L k := by
  rw [mem_freqBox]
  intro ν
  have h0 := finestMesh_pos hL k
  have h1 : 1 ≤ (finestMesh L k)⁻¹ := (one_le_inv₀ h0).mpr (finestMesh_le_one hL k)
  simp only [Pi.zero_apply, Int.cast_zero, abs_zero]
  linarith
theorem symbolSquare_add_one_ne_zero (hG : FreeResolventRoots) {L k : ℕ}
    (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip (1 / 8)) :
    symbolSquare L k κ + 1 ≠ 0 := by
  have h := symbolSquare_shiftedFreq_add_one_ne_zero hG hL hk hκ (zero_mem_freqBox hL k)
  have hs : shiftedFreq κ 0 = κ := by
    funext μ
    simp [shiftedFreq]
  rwa [hs] at h
theorem continuous_invCubeNorm_comp {X : Type*} [TopologicalSpace X] {L k : ℕ}
    {c : X → Fin 4 → ℂ} (hc : Continuous c) (h : ∀ x, symbolSquare L k (c x) + 1 ≠ 0) :
    Continuous fun x => invCubeNorm L k (c x) := by
  unfold invCubeNorm
  exact Continuous.pow (Continuous.inv₀
    (((continuous_symbolSquare L k).comp hc).add continuous_const).norm
    fun x => norm_ne_zero_iff.mpr (h x)) 3
theorem continuous_shiftedFreq_toComplexVec (ϑ : Fin 4 → ℂ) (m : Fin 4 → ℤ) :
    Continuous fun κ : InfiniteLattice.AmbientSpace => shiftedFreq (toComplexVec κ + ϑ) m := by
  refine continuous_pi fun μ => ?_
  have h : Continuous fun κ : InfiniteLattice.AmbientSpace => toComplexVec κ μ :=
    (continuous_apply μ).comp continuous_toComplexVec
  simp only [shiftedFreq, Pi.add_apply]
  fun_prop
theorem continuous_cubicResolventSum (hG : FreeResolventRoots) {L k : ℕ}
    (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {ϑ : Fin 4 → ℂ} (hϑ : ϑ ∈ imStrip (1 / 8)) :
    Continuous (cubicResolventSum L k ϑ) := by
  rw [funext (cubicResolventSum_eq_sum hG hL hk hϑ)]
  refine continuous_finsetSum _ fun m hm => ?_
  exact continuous_invCubeNorm_comp (continuous_shiftedFreq_toComplexVec ϑ m)
    fun κ => symbolSquare_shiftedFreq_add_one_ne_zero hG hL hk (add_mem_imStrip hϑ κ) hm
def twoPiVec (m : Fin 4 → ℤ) : Fin 4 → ℝ := fun ν => 2 * Real.pi * (m ν : ℝ)
theorem shiftedFreq_toComplexVec_add (ϑ : Fin 4 → ℂ) (κ : Fin 4 → ℝ) (m : Fin 4 → ℤ) :
    shiftedFreq (toComplexVec κ + ϑ) m = toComplexVec (κ + twoPiVec m) + ϑ := by
  funext μ
  simp only [shiftedFreq, Pi.add_apply, toComplexVec, twoPiVec]
  push_cast
  ring
def negPiCorner : Fin 4 → ℝ := fun _ => -Real.pi
theorem disjoint_halfOpenCube_twoPiVec (m m' : Fin 4 → ℤ) (h : m ≠ m') :
    Disjoint (halfOpenCube (2 * Real.pi) (negPiCorner + twoPiVec m))
      (halfOpenCube (2 * Real.pi) (negPiCorner + twoPiVec m')) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  apply h
  funext ν
  have h1 := mem_halfOpenCube.mp hx ν
  have h2 := mem_halfOpenCube.mp hx' ν
  simp only [Pi.add_apply, negPiCorner, twoPiVec] at h1 h2
  have a1 : (m ν : ℝ) < m' ν + 1 := by
    refine lt_of_mul_lt_mul_left (a := 2 * Real.pi) ?_ (by positivity)
    nlinarith
  have a2 : (m' ν : ℝ) < m ν + 1 := by
    refine lt_of_mul_lt_mul_left (a := 2 * Real.pi) ?_ (by positivity)
    nlinarith
  have b1 : m ν < m' ν + 1 := by exact_mod_cast a1
  have b2 : m' ν < m ν + 1 := by exact_mod_cast a2
  omega
theorem halfOpenCube_twoPiVec_subset {L k : ℕ} {m : Fin 4 → ℤ} (hm : m ∈ freqBox L k) :
    halfOpenCube (2 * Real.pi) (negPiCorner + twoPiVec m) ⊆
      halfOpenCube (2 * Real.pi * (finestMesh L k)⁻¹)
        fun _ => -(Real.pi * (finestMesh L k)⁻¹) := by
  intro x hx
  rw [mem_halfOpenCube] at hx ⊢
  intro ν
  have h1 := hx ν
  have h2 := abs_le.mp ((mem_freqBox L k m).mp hm ν)
  simp only [Pi.add_apply, negPiCorner, twoPiVec] at h1
  have c1 := mul_le_mul_of_nonneg_left h2.1 (by positivity : 0 ≤ 2 * Real.pi)
  have c2 := mul_le_mul_of_nonneg_left h2.2 (by positivity : 0 ≤ 2 * Real.pi)
  constructor <;> nlinarith
theorem setIntegral_cubicResolventSum_le (hG : FreeResolventRoots)
    (hE : PlaneWaves.PlaneWaveBounds.Claim) {L k : ℕ} (hL : IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) {ϑ : Fin 4 → ℂ} (hϑ : ϑ ∈ imStrip (1 / 8)) :
    ∫ κ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), cubicResolventSum L k ϑ κ ≤
      (10 / 9) ^ 3 * ∫ q, decayMajorant q := by
  have hη := finestMesh_pos hL k
  set P : ℝ := 2 * Real.pi * (finestMesh L k)⁻¹ with hPdef
  have hP : 0 < P := by positivity
  set box : Set (Fin 4 → ℝ) := halfOpenCube P fun _ => -(Real.pi * (finestMesh L k)⁻¹) with hbox
  let a : Fin 4 → ℝ := fun ν => (ϑ ν).re
  let θ : Fin 4 → ℝ := fun ν => (ϑ ν).im
  let f : (Fin 4 → ℝ) → ℝ := fun x => invCubeNorm L k (toComplexVec x + ϑ)
  let F : (Fin 4 → ℝ) → ℝ := fun y => invCubeNorm L k (complexPoint y θ)
  have hf : Continuous f := continuous_invCubeNorm_comp
    (continuous_toComplexVec.add continuous_const)
    fun x => symbolSquare_add_one_ne_zero hG hL hk (add_mem_imStrip hϑ x)
  have hpoint : ∀ x, toComplexVec x + ϑ = complexPoint (x + a) θ := by
    intro x
    funext ν
    simp only [Pi.add_apply, toComplexVec, complexPoint, a, θ]
    apply Complex.ext <;> simp
  have hfF : ∀ x, f x = F (x + a) := fun x => by
    simp only [f, F, hpoint]
  have hF : Continuous F := by
    have hc : Continuous fun y : Fin 4 → ℝ => complexPoint y θ := by
      refine continuous_pi fun ν => ?_
      simp only [complexPoint]
      fun_prop
    refine continuous_invCubeNorm_comp hc fun y => symbolSquare_add_one_ne_zero hG hL hk ?_
    intro μ
    simpa [complexPoint, θ] using hϑ μ
  have hIcc : Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi) =
      Icc negPiCorner (fun ν => negPiCorner ν + 2 * Real.pi) := by
    congr 1
    funext ν
    simp only [negPiCorner]
    ring
  have hae : halfOpenCube (2 * Real.pi) negPiCorner =ᵐ[volume]
      Icc negPiCorner (fun ν => negPiCorner ν + 2 * Real.pi) :=
    Measure.univ_pi_Ico_ae_eq_Icc
  have hterm : ∀ m ∈ freqBox L k,
      ∫ κ in halfOpenCube (2 * Real.pi) negPiCorner,
          invCubeNorm L k (shiftedFreq (toComplexVec κ + ϑ) m) =
        ∫ x in halfOpenCube (2 * Real.pi) (negPiCorner + twoPiVec m), f x := by
    intro m _
    rw [← setIntegral_halfOpenCube_add f]
    simp only [shiftedFreq_toComplexVec_add, f]
  have hsum : ∫ κ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi),
        cubicResolventSum L k ϑ κ =
      ∫ x in ⋃ m ∈ freqBox L k, halfOpenCube (2 * Real.pi) (negPiCorner + twoPiVec m), f x := by
    rw [integral_biUnion_finset _ (fun m _ => measurableSet_halfOpenCube _ _)
      (fun m _ m' _ h => disjoint_halfOpenCube_twoPiVec m m' h)
      (fun m _ => integrableOn_halfOpenCube hf _ _),
      hIcc, ← setIntegral_congr_set hae, ← Finset.sum_congr rfl hterm,
      ← integral_finsetSum _ fun m hm => integrableOn_halfOpenCube
        (continuous_invCubeNorm_comp (continuous_shiftedFreq_toComplexVec ϑ m)
          fun κ => symbolSquare_shiftedFreq_add_one_ne_zero hG hL hk (add_mem_imStrip hϑ κ) hm) _ _]
    exact integral_congr_ae (Filter.Eventually.of_forall (cubicResolventSum_eq_sum hG hL hk hϑ))
  have hsub : (⋃ m ∈ freqBox L k, halfOpenCube (2 * Real.pi) (negPiCorner + twoPiVec m)) ⊆ box :=
    iUnion₂_subset fun m hm => halfOpenCube_twoPiVec_subset hm
  have hstep1 : ∫ x in ⋃ m ∈ freqBox L k,
        halfOpenCube (2 * Real.pi) (negPiCorner + twoPiVec m), f x ≤
      ∫ x in box, f x :=
    setIntegral_mono_set (integrableOn_halfOpenCube hf _ _)
      (Filter.Eventually.of_forall fun x => invCubeNorm_nonneg L k _)
      (Filter.Eventually.of_forall hsub)
  have hinv : ∀ (g : (periodHom P).range) (y : Fin 4 → ℝ), F (g +ᵥ y) = F y := by
    rintro ⟨_, n, rfl⟩ y
    have hy : complexPoint (periodHom P n + y) θ =
        complexPoint y θ + toComplexVec (periodHom P n) := by
      funext ν
      simp only [complexPoint, Pi.add_apply, toComplexVec]
      push_cast
      ring
    change invCubeNorm L k (complexPoint (periodHom P n + y) θ) = _
    rw [hy]
    exact invCubeNorm_add_period hη.ne' _ n
  have hstep2 : ∫ x in box, f x = ∫ y in box, F y := by
    simp only [hfF]
    rw [hbox, setIntegral_halfOpenCube_add F]
    exact (isAddFundamentalDomain_halfOpenCube hP _).setIntegral_eq
      (isAddFundamentalDomain_halfOpenCube hP _) hinv
  have hstep3 : ∫ y in box, F y ≤ ∫ y in box, (10 / 9) ^ 3 * decayMajorant y := by
    refine setIntegral_mono_on (integrableOn_halfOpenCube hF _ _)
      (integrableOn_halfOpenCube (continuous_const.mul continuous_decayMajorant) _ _)
      (measurableSet_halfOpenCube _ _) fun y hy => ?_
    have hy' : ∀ ν, |y ν| ≤ Real.pi / finestMesh L k := by
      intro ν
      obtain ⟨h1, h2⟩ := mem_halfOpenCube.mp hy ν
      rw [div_eq_mul_inv]
      refine abs_le.mpr ⟨h1, ?_⟩
      rw [hPdef] at h2
      linarith
    have hθ : ∀ ν, |θ ν| ≤ 1 / 8 := fun ν => hϑ ν
    exact invCubeNorm_complexPoint_le (hE.1 L k hL hk y θ hy' hθ).2.1
  have hstep4 : ∫ y in box, (10 / 9) ^ 3 * decayMajorant y ≤
      (10 / 9) ^ 3 * ∫ q, decayMajorant q := by
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_le_integral integrable_decayMajorant
      (Filter.Eventually.of_forall decayMajorant_nonneg)
  rw [hsum]
  linarith
theorem claim_holds (hG : FreeResolventRoots) (hE : PlaneWaves.PlaneWaveBounds.Claim) :
    Claim := by
  refine ⟨integrable_decayMajorant,
    fun L hL k hk ϑ hϑ => ⟨continuous_cubicResolventSum hG hL hk hϑ, ?_⟩⟩
  have h := setIntegral_cubicResolventSum_le hG hE hL hk hϑ
  have hc : 0 ≤ ((2 * Real.pi) ^ 4)⁻¹ := by
    have := Real.pi_pos
    positivity
  calc _ ≤ ((2 * Real.pi) ^ 4)⁻¹ * ((10 / 9) ^ 3 * ∫ q, decayMajorant q) :=
        mul_le_mul_of_nonneg_left h hc
    _ = cubicBound := by
        unfold cubicBound
        ring
end YangMills.Construction.Tower.FreeResolvents.CubicSumIntegral
end
