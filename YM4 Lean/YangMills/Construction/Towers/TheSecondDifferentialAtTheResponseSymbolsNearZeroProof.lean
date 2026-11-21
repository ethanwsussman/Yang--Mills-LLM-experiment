import YangMills.Construction.Towers.TheBackgroundFieldAmongTheTriplesProof
import YangMills.Construction.Towers.TheResponseSymbolComponentsNearZeroProof
import YangMills.Construction.Towers.TheSecondDifferentialAtTheResponseSymbolsNearZero
import YangMills.Construction.Towers.TheSymbolAtZeroOnConstantForms
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.ResponseSecondVariation
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.EntriesDets
open YangMills.Construction.Tower.ResponseProperties (euclidNorm)
open YangMills.Construction.Tower.TorusResponseField (constantFieldAmplitude)
open YangMills.Construction.Tower.ResponseSymbolNearZero (constantFormOnQuot)
open YangMills.Construction.Tower.ResponseSymbolNearStrip (IsTracelessTuple)
open YangMills.Construction.Tower.FreeStrip (admissibleRates halfSupRate)
open YangMills.Construction.Tower.FullSpace
section BilinearSums
variable {X : Type} [Fintype X]
def bilinSum (a : X → X → ℂ) (u v : X → ℂ) : ℂ := ∑ c, ∑ c', a c c' * u c * v c'
theorem bilinSum_add_left (a : X → X → ℂ) (u u' v : X → ℂ) :
    bilinSum a (u + u') v = bilinSum a u v + bilinSum a u' v := by
  simp only [bilinSum, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
theorem bilinSum_add_right (a : X → X → ℂ) (u v v' : X → ℂ) :
    bilinSum a u (v + v') = bilinSum a u v + bilinSum a u v' := by
  simp only [bilinSum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem bilinSum_sub_kernel (a a' : X → X → ℂ) (u v : X → ℂ) :
    bilinSum (fun c c' => a c c' - a' c c') u v =
      bilinSum a u v - bilinSum a' u v := by
  simp only [bilinSum, sub_mul, Finset.sum_sub_distrib]
theorem norm_bilinSum_le {a : X → X → ℂ} {u v : X → ℂ} {M x y : ℝ}
    (ha : ∀ c c', ‖a c c'‖ ≤ M) (hu : ∀ c, ‖u c‖ ≤ x) (hv : ∀ c, ‖v c‖ ≤ y) :
    ‖bilinSum a u v‖ ≤ (Fintype.card X : ℝ) ^ 2 * (M * x * y) := by
  have hterm : ∀ c c', ‖a c c' * u c * v c'‖ ≤ M * x * y := fun c c' => by
    rw [norm_mul, norm_mul]
    have hM : 0 ≤ M := (norm_nonneg _).trans (ha c c')
    have hx : 0 ≤ x := (norm_nonneg _).trans (hu c)
    exact mul_le_mul (mul_le_mul (ha c c') (hu c) (norm_nonneg _) hM) (hv c') (norm_nonneg _)
      (mul_nonneg hM hx)
  calc ‖bilinSum a u v‖ ≤ ∑ c, ∑ c', ‖a c c' * u c * v c'‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => norm_sum_le _ _)
    _ ≤ ∑ _c : X, ∑ _c' : X, M * x * y :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => hterm c c'
    _ = (Fintype.card X : ℝ) ^ 2 * (M * x * y) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
theorem norm_bilinSum_sub_le_cube {a a₀ : X → X → ℂ} {f g fA fθ gA gθ f₀ g₀ : X → ℂ}
    {r M K D : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hM : 0 ≤ M) (hf : f = fA + fθ) (hg : g = gA + gθ)
    (ha : ∀ c c', ‖a c c'‖ ≤ M) (had : ∀ c c', ‖a c c' - a₀ c c'‖ ≤ K * r)
    (hfA : ∀ c, ‖(fA - f₀) c‖ ≤ D * r) (hgA : ∀ c, ‖(gA - g₀) c‖ ≤ D * r)
    (hfθ : ∀ c, ‖fθ c‖ ≤ D * r ^ 2) (hgθ : ∀ c, ‖gθ c‖ ≤ D * r ^ 2)
    (hf₀ : ∀ c, ‖f₀ c‖ ≤ D) (hg₀ : ∀ c, ‖g₀ c‖ ≤ D)
    (hleft : bilinSum a₀ f₀ gθ = 0) (hright : bilinSum a₀ fθ g₀ = 0) :
    ‖bilinSum a f g - bilinSum a fA gA‖ ≤
      (Fintype.card X : ℝ) ^ 2 * (D ^ 2 * (3 * M + 2 * K)) * r ^ 3 := by
  have h1 : bilinSum a fA gθ = bilinSum a (fA - f₀) gθ + bilinSum a f₀ gθ := by
    rw [← bilinSum_add_left, sub_add_cancel]
  have h2 : bilinSum a fθ gA = bilinSum a fθ (gA - g₀) + bilinSum a fθ g₀ := by
    rw [← bilinSum_add_right, sub_add_cancel]
  have h3 : bilinSum (fun c c' => a c c' - a₀ c c') f₀ gθ = bilinSum a f₀ gθ := by
    rw [bilinSum_sub_kernel, hleft, sub_zero]
  have h4 : bilinSum (fun c c' => a c c' - a₀ c c') fθ g₀ = bilinSum a fθ g₀ := by
    rw [bilinSum_sub_kernel, hright, sub_zero]
  have e : bilinSum a f g - bilinSum a fA gA =
      bilinSum a (fA - f₀) gθ + bilinSum (fun c c' => a c c' - a₀ c c') f₀ gθ +
        bilinSum a fθ (gA - g₀) + bilinSum (fun c c' => a c c' - a₀ c c') fθ g₀ +
        bilinSum a fθ gθ := by
    rw [hf, hg, bilinSum_add_left, bilinSum_add_right, bilinSum_add_right, h1, h2,
      h3, h4]
    ring
  have b1 := norm_bilinSum_le ha hfA hgθ
  have b2 := norm_bilinSum_le had hf₀ hgθ
  have b3 := norm_bilinSum_le ha hfθ hgA
  have b4 := norm_bilinSum_le had hfθ hg₀
  have b5 := norm_bilinSum_le ha hfθ hgθ
  have hn : (0 : ℝ) ≤ (Fintype.card X : ℝ) ^ 2 := by positivity
  have h43 : r ^ 4 ≤ r ^ 3 := pow_le_pow_of_le_one hr hr1 (by norm_num)
  have h5 : (Fintype.card X : ℝ) ^ 2 * (M * (D * r ^ 2) * (D * r ^ 2)) ≤
      (Fintype.card X : ℝ) ^ 2 * (M * D ^ 2 * r ^ 3) := by
    refine mul_le_mul_of_nonneg_left ?_ hn
    have : M * (D * r ^ 2) * (D * r ^ 2) = M * D ^ 2 * r ^ 4 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h43 (mul_nonneg hM (sq_nonneg D))
  rw [e]
  calc _ ≤ ‖bilinSum a (fA - f₀) gθ‖ +
        ‖bilinSum (fun c c' => a c c' - a₀ c c') f₀ gθ‖ + ‖bilinSum a fθ (gA - g₀)‖ +
        ‖bilinSum (fun c c' => a c c' - a₀ c c') fθ g₀‖ + ‖bilinSum a fθ gθ‖ :=
        norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le _ _) le_rfl) le_rfl)
          le_rfl
    _ ≤ _ := by nlinarith [b1, b2, b3, b4, b5, h5]
end BilinearSums
theorem halfSupRate_pos {δ₀ : ℝ} (h : δ₀ ∈ halfSupRate) : 0 < δ₀ := by apply _root_.YangMills.Construction.Tower.NormaliserSymbol.pos_of_mem_halfSupRate <;> assumption
theorem norm_le_euclidNorm (p : Fin 4 → ℂ) (σ : Fin 4) : ‖p σ‖ ≤ euclidNorm p := by
  unfold euclidNorm
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (f := fun ρ => ‖p ρ‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ σ)
theorem euclidNorm_neg (p : Fin 4 → ℂ) : euclidNorm (-p) = euclidNorm p := by
  simp [euclidNorm]
theorem euclidNorm_nonneg (p : Fin 4 → ℂ) : 0 ≤ euclidNorm p := Real.sqrt_nonneg _
theorem euclidNorm_le_one {p : Fin 4 → ℂ} (h : ‖p‖ < 1 / 2) : euclidNorm p ≤ 1 := by apply _root_.YangMills.Construction.Tower.ResponseSymbolNearZero.euclidNorm_le_one <;> assumption
theorem tripleAmplitude_mkQuot {L k : ℕ} (hL : 0 < L)
    (x j : (colourEdges L k 0).UnitQuot → ℂ) (m : (colourEdges L k k).UnitQuot → ℂ)
    (ι : (fieldPeriodicData L k hL).Carrier) :
    tripleAmplitude L k hL x j m ((fieldPeriodicData L k hL).mkQuot 1 ι) =
      tripleIndexFunction L k hL x j m ι := by apply _root_.YangMills.Construction.Tower.ResponseOfFourierMode.tripleAmplitude_mkQuot <;> assumption
theorem tripleAmplitude_eq_add {L k : ℕ} (hL : 0 < L)
    (x j : (colourEdges L k 0).UnitQuot → ℂ) (m : (colourEdges L k k).UnitQuot → ℂ) :
    tripleAmplitude L k hL x j m =
      tripleAmplitude L k hL x 0 0 + tripleAmplitude L k hL 0 j m := by
  funext c
  induction c using Quot.ind with
  | mk ι =>
    change tripleAmplitude L k hL x j m ((fieldPeriodicData L k hL).mkQuot 1 ι) =
      tripleAmplitude L k hL x 0 0 ((fieldPeriodicData L k hL).mkQuot 1 ι) +
        tripleAmplitude L k hL 0 j m ((fieldPeriodicData L k hL).mkQuot 1 ι)
    rw [tripleAmplitude_mkQuot, tripleAmplitude_mkQuot, tripleAmplitude_mkQuot]
    obtain ⟨pl, ι⟩ := ι
    cases pl <;> simp [tripleIndexFunction]
theorem norm_tripleAmplitude_zero_le {L k : ℕ} (hL : 0 < L)
    {j : (colourEdges L k 0).UnitQuot → ℂ} {m : (colourEdges L k k).UnitQuot → ℂ} {y : ℝ}
    (hy : 0 ≤ y) (hj : ∀ c, ‖j c‖ ≤ y) (hm : ∀ c, ‖m c‖ ≤ y)
    (c : (fieldPeriodicData L k hL).UnitQuot) :
    ‖tripleAmplitude L k hL 0 j m c‖ ≤ y := by
  induction c using Quot.ind with
  | mk ι =>
    change ‖tripleAmplitude L k hL 0 j m ((fieldPeriodicData L k hL).mkQuot 1 ι)‖ ≤ y
    rw [tripleAmplitude_mkQuot]
    obtain ⟨pl, ι⟩ := ι
    cases pl
    · simpa [tripleIndexFunction] using hy
    · exact hj _
    · exact hm _
theorem norm_tripleAmplitude_sub_le {L k : ℕ} (hL : 0 < L)
    {x x' : (colourEdges L k 0).UnitQuot → ℂ} {y : ℝ} (hy : 0 ≤ y)
    (hx : ∀ c, ‖x c - x' c‖ ≤ y) (c : (fieldPeriodicData L k hL).UnitQuot) :
    ‖(tripleAmplitude L k hL x 0 0 - tripleAmplitude L k hL x' 0 0) c‖ ≤ y := by
  induction c using Quot.ind with
  | mk ι =>
    change ‖tripleAmplitude L k hL x 0 0 ((fieldPeriodicData L k hL).mkQuot 1 ι) -
      tripleAmplitude L k hL x' 0 0 ((fieldPeriodicData L k hL).mkQuot 1 ι)‖ ≤ y
    rw [tripleAmplitude_mkQuot, tripleAmplitude_mkQuot]
    obtain ⟨pl, ι⟩ := ι
    cases pl
    · exact hx _
    · simpa [tripleIndexFunction] using hy
    · simpa [tripleIndexFunction] using hy
theorem axisPauliElement_isTraceless (μ : Fin 4) : IsTracelessTuple (axisPauliElement μ 2) := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.BackgroundTriple.axisPauliElement_isTraceless <;> assumption
theorem norm_sub_at_zero_le
    (hEnt : YangMills.Construction.PeriodicOperators.EntriesDets.Claim)
    {δPlus M : ℝ} (hδ : 0 < δPlus) (hM : 0 ≤ M) {u : (Fin 4 → ℂ) → ℂ}
    (hu : YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv.IsHolomorphicScalarIn
      (interior (imStrip δPlus)) u)
    (hb : ∀ p ∈ imStrip δPlus, ‖u p‖ ≤ M) {p : Fin 4 → ℂ} (hp : ∀ σ, ‖p σ‖ < δPlus / 2) :
    ‖u p - u 0‖ ≤ 4 * M / (δPlus / 2) * euclidNorm p := by
  have hϱ : 0 < δPlus / 2 := by positivity
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hEnt
  obtain ⟨-, -, -, -, -, -, -, -, hX, -, -⟩ :=
    h7 4 (interior (imStrip δPlus)) (by norm_num) isOpen_interior
  have hEst := (hX ℂ (normSeminorm ℂ ℂ)).2
  have hopen : IsOpen {κ : Fin 4 → ℂ | ∀ μ, |(κ μ).im| < δPlus} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun μ =>
      isOpen_lt (continuous_abs.comp (Complex.continuous_im.comp (continuous_apply μ)))
        continuous_const
  have hin : ∀ z : Fin 4 → ℂ, (∀ j, ‖z j‖ < δPlus) → z ∈ interior (imStrip δPlus) := fun z hz =>
    interior_maximal (fun κ hκ μ => (hκ μ).le) hopen fun μ =>
      (Complex.abs_im_le_norm (z μ)).trans_lt (hz μ)
  have hc : ∀ z, linComb (fun _ : Fin 1 => u) (fun _ => (1 : ℂ)) z = u z := fun z => by
    simp [linComb]
  have hside : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      openPolydisc (fun _ : Fin 4 => δPlus / 2) ((0 : Fin 4 → ℂ) + (s : ℂ) • (p - 0)) ⊆
          interior (imStrip δPlus) ∧
        ∀ z ∈ openPolydisc (fun _ : Fin 4 => δPlus / 2) ((0 : Fin 4 → ℂ) + (s : ℂ) • (p - 0)),
          normSeminorm ℂ ℂ (linComb (fun _ : Fin 1 => u) (fun _ => (1 : ℂ)) z) ≤ M := by
    intro s hs
    have hz : ∀ z ∈ openPolydisc (fun _ : Fin 4 => δPlus / 2)
        ((0 : Fin 4 → ℂ) + (s : ℂ) • (p - 0)), ∀ j, ‖z j‖ < δPlus := by
      intro z hz j
      have h1 := hz j
      have h2 : ‖((0 : Fin 4 → ℂ) + (s : ℂ) • (p - 0)) j‖ ≤ ‖p j‖ := by
        simp only [zero_add, sub_zero, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hs.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hs.2
      have h3 := norm_add_le (z j - ((0 : Fin 4 → ℂ) + (s : ℂ) • (p - 0)) j)
        (((0 : Fin 4 → ℂ) + (s : ℂ) • (p - 0)) j)
      rw [sub_add_cancel] at h3
      linarith [hp j]
    refine ⟨fun z h => hin z (hz z h), fun z h => ?_⟩
    rw [hc]
    simpa using hb z (interior_subset (hin z (hz z h)))
  have key := (hEst 1 (fun _ => (1 : ℂ)) (fun _ => u) (fun _ => hu) (fun _ => δPlus / 2) M
    (fun _ => hϱ) hM).2 0 p hside
  rw [hc, hc] at key
  have hsum : ∑ j, ‖p j - (0 : Fin 4 → ℂ) j‖ / (δPlus / 2) ≤ 4 * euclidNorm p / (δPlus / 2) := by
    calc ∑ j, ‖p j - (0 : Fin 4 → ℂ) j‖ / (δPlus / 2)
        ≤ ∑ _j : Fin 4, euclidNorm p / (δPlus / 2) := Finset.sum_le_sum fun j _ => by
          simpa using div_le_div_of_nonneg_right (norm_le_euclidNorm p j) hϱ.le
      _ = 4 * euclidNorm p / (δPlus / 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  calc ‖u p - u 0‖ ≤ M * ∑ j, ‖p j - (0 : Fin 4 → ℂ) j‖ / (δPlus / 2) := by simpa using key
    _ ≤ M * (4 * euclidNorm p / (δPlus / 2)) := mul_le_mul_of_nonneg_left hsum hM
    _ = 4 * M / (δPlus / 2) * euclidNorm p := by ring
def constantAxisField (L k : ℕ) (hL : 0 < L) (μ : Fin 4) :
    (fieldPeriodicData L k hL).UnitQuot → ℂ :=
  constantFieldAmplitude L k hL (((finestMesh L k : ℝ) : ℂ) • axisPauliElement μ 2)
theorem nearZeroCubicBound_holds
    (hZero : YangMills.Construction.Tower.SymbolAtZero.SymmetricAndKillsConstantForms)
    (hCoef : YangMills.Construction.Tower.FullSpace.SymbolCoefficients.SymbolCoefficientsExist)
    (hComp : YangMills.Construction.Tower.ResponseSymbolNearZero.ComponentsNearZero)
    (hEnt : YangMills.Construction.PeriodicOperators.EntriesDets.Claim)
    (hPer : YangMills.Construction.LocalKernels.IndexSetPeriodicity.Statement) :
    NearZeroCubicBound := by
  intro δ₀ hδ₀ L hL hs k hk δ hδ
  have hδ₀pos : 0 < δ₀ := halfSupRate_pos hδ₀
  have hδpos : 0 < δ := hδ.1.1
  obtain ⟨δPlus, hlt, -, a, hhol, hgive⟩ := hCoef L hL hs k hk δ hδ
  have hδPlus : 0 < δPlus := hδpos.trans hlt
  have hfin : Finite (fieldPeriodicData L k hL).UnitQuot :=
    ((hPer L hs k).2 (YangMills.Construction.LocalKernels.fieldIndices L k hL)).1.finite_quot
  let _ : Fintype (fieldPeriodicData L k hL).UnitQuot := Fintype.ofFinite _
  have hvalue : ∀ p ∈ imStrip δ, ∀ u v : (fieldPeriodicData L k hL).UnitQuot → ℂ,
      secondVariationSymbol L k hL p u v = bilinSum (fun c c' => a c c' p) u v := by
    intro p hp u v
    rw [hgive p hp u v]
    simp only [finsum_eq_sum_of_fintype, bilinSum]
  choose Mc hMc using fun c c' => (hhol c c').2
  obtain ⟨M, hM0, hMle⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ c c', ∀ p ∈ imStrip δPlus, ‖a c c' p‖ ≤ M := by
    refine ⟨∑ c, ∑ c', |Mc c c'|, Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun c' _ =>
      abs_nonneg _, fun c c' p hp => (hMc c c' p hp).trans ((le_abs_self _).trans ?_)⟩
    calc |Mc c c'| ≤ ∑ c'', |Mc c c''| :=
          Finset.single_le_sum (f := fun c'' => |Mc c c''|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ c')
      _ ≤ ∑ c₁, ∑ c'', |Mc c₁ c''| :=
          Finset.single_le_sum (f := fun c₁ => ∑ c'', |Mc c₁ c''|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ c)
  have hLip : ∀ c c' p, (∀ σ, ‖p σ‖ < δPlus / 2) →
      ‖a c c' p - a c c' 0‖ ≤ 4 * M / (δPlus / 2) * euclidNorm p := fun c c' p hp =>
    norm_sub_at_zero_le hEnt hδPlus hM0 (hhol c c').1 (hMle c c') hp
  choose Cμ Nμ hN using fun μ : Fin 4 =>
    hComp δ₀ hδ₀ L hs k hk (axisPauliElement μ 2) (axisPauliElement_isTraceless μ)
  have hξ : ∀ μ ρ, (((finestMesh L k : ℝ) : ℂ) • axisPauliElement μ 2) ρ ∈
      YangMills.Construction.Matrices.ComplexMatrix2.traceless :=
    fun μ ρ => Submodule.smul_mem _ _ (axisPauliElement_isTraceless μ ρ)
  obtain ⟨D, hD0, hDC, hDf⟩ : ∃ D : ℝ, 0 ≤ D ∧ (∀ μ, Cμ μ ≤ D) ∧
      ∀ μ c, ‖constantAxisField L k hL μ c‖ ≤ D := by
    have h1 : 0 ≤ ∑ μ, |Cμ μ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h2 : 0 ≤ ∑ μ, ∑ c, ‖constantAxisField L k hL μ c‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine ⟨∑ μ, |Cμ μ| + ∑ μ, ∑ c, ‖constantAxisField L k hL μ c‖, add_nonneg h1 h2,
      fun μ => ?_, fun μ c => ?_⟩
    · have := Finset.single_le_sum (f := fun μ => |Cμ μ|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ μ)
      have h3 := le_abs_self (Cμ μ)
      linarith
    · have h3 : ‖constantAxisField L k hL μ c‖ ≤ ∑ c', ‖constantAxisField L k hL μ c'‖ :=
        Finset.single_le_sum (f := fun c' => ‖constantAxisField L k hL μ c'‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
      have h4 : ∑ c', ‖constantAxisField L k hL μ c'‖ ≤
          ∑ μ', ∑ c', ‖constantAxisField L k hL μ' c'‖ :=
        Finset.single_le_sum (f := fun μ' => ∑ c', ‖constantAxisField L k hL μ' c'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ μ)
      linarith
  have hρ0 : 0 < min (min (δPlus / 2) (1 / 2)) (min δ (2 * δ₀)) :=
    lt_min (lt_min (by positivity) (by norm_num)) (lt_min hδpos (by positivity))
  refine ⟨(Fintype.card (fieldPeriodicData L k hL).UnitQuot : ℝ) ^ 2 *
      (D ^ 2 * (3 * M + 2 * (4 * M / (δPlus / 2)))),
    {p | ‖p‖ < min (min (δPlus / 2) (1 / 2)) (min δ (2 * δ₀)) ∧
      ∀ μ, p ∈ Nμ μ ∧ -p ∈ Nμ μ}, ?_, ?_, ?_⟩
  · have h1 : ∀ᶠ p in 𝓝 (0 : Fin 4 → ℂ),
        ‖p‖ < min (min (δPlus / 2) (1 / 2)) (min δ (2 * δ₀)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Fin 4 → ℂ) hρ0] with p hp
      simpa using hp
    have ht : Tendsto (fun p : Fin 4 → ℂ => -p) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : Fin 4 → ℂ))
    have h2 : ∀ᶠ p in 𝓝 (0 : Fin 4 → ℂ), ∀ μ, p ∈ Nμ μ ∧ -p ∈ Nμ μ :=
      eventually_all.2 fun μ => (Filter.Eventually.and (hN μ).1 (ht.eventually (hN μ).1))
    exact h1.and h2
  · rintro p ⟨hp, -⟩
    have hσ : ∀ σ, |(p σ).im| < min (min (δPlus / 2) (1 / 2)) (min δ (2 * δ₀)) := fun σ =>
      (Complex.abs_im_le_norm _).trans_lt ((norm_le_pi_norm p σ).trans_lt hp)
    exact ⟨fun σ => (hσ σ).le.trans ((min_le_right _ _).trans (min_le_left _ _)),
      fun σ => (hσ σ).le.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  · rintro p ⟨hp, hpN⟩ μ ν
    have hσ : ∀ σ, ‖p σ‖ < min (min (δPlus / 2) (1 / 2)) (min δ (2 * δ₀)) := fun σ =>
      (norm_le_pi_norm p σ).trans_lt hp
    have hρ : ∀ σ, ‖p σ‖ < δPlus / 2 := fun σ =>
      (hσ σ).trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hps : p ∈ imStrip δ := fun σ => ((Complex.abs_im_le_norm _).trans (hσ σ).le).trans
      ((min_le_right _ _).trans (min_le_left _ _))
    have hpPlus : p ∈ imStrip δPlus := fun σ =>
      ((Complex.abs_im_le_norm _).trans (hρ σ).le).trans (by linarith)
    have h0s : (0 : Fin 4 → ℂ) ∈ imStrip δ := fun σ => by simpa using hδpos.le
    have hhalf : ‖p‖ < 1 / 2 := hp.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hr0 := euclidNorm_nonneg p
    have hr1 := euclidNorm_le_one hhalf
    obtain ⟨hJ, hm, hA⟩ := (hN μ).2 p (hpN μ).1
    obtain ⟨hJ', hm', hA'⟩ := (hN ν).2 (-p) (hpN ν).2
    simp only [euclidNorm_neg] at hJ' hm' hA'
    have hCD : ∀ (μ : Fin 4) (x : ℝ), 0 ≤ x → Cμ μ * x ≤ D * x := fun μ x hx =>
      mul_le_mul_of_nonneg_right (hDC μ) hx
    have hr2 : 0 ≤ euclidNorm p ^ 2 := by positivity
    have hleft : bilinSum (fun c c' => a c c' 0) (constantAxisField L k hL μ)
        (tripleAmplitude L k hL 0 (sourceResponseSymbol L k (-p) (axisPauliElement ν 2))
          (coarseResponseSymbol L k (-p) (axisPauliElement ν 2))) = 0 := by
      rw [← hvalue 0 h0s]
      exact ((hZero L hL hs k hk).2 _ (hξ μ) _).1
    have hright : bilinSum (fun c c' => a c c' 0)
        (tripleAmplitude L k hL 0 (sourceResponseSymbol L k p (axisPauliElement μ 2))
          (coarseResponseSymbol L k p (axisPauliElement μ 2))) (constantAxisField L k hL ν) = 0 := by
      rw [← hvalue 0 h0s]
      exact ((hZero L hL hs k hk).2 _ (hξ ν) _).2
    have main := norm_bilinSum_sub_le_cube (a := fun c c' => a c c' p)
      (a₀ := fun c c' => a c c' 0)
      (f := responseSymbol L k hL p (axisPauliElement μ 2))
      (g := responseSymbol L k hL (-p) (axisPauliElement ν 2))
      (fA := tripleAmplitude L k hL (backgroundResponseSymbol L k p (axisPauliElement μ 2)) 0 0)
      (fθ := tripleAmplitude L k hL 0 (sourceResponseSymbol L k p (axisPauliElement μ 2))
        (coarseResponseSymbol L k p (axisPauliElement μ 2)))
      (gA := tripleAmplitude L k hL (backgroundResponseSymbol L k (-p) (axisPauliElement ν 2)) 0 0)
      (gθ := tripleAmplitude L k hL 0 (sourceResponseSymbol L k (-p) (axisPauliElement ν 2))
        (coarseResponseSymbol L k (-p) (axisPauliElement ν 2)))
      (f₀ := constantAxisField L k hL μ) (g₀ := constantAxisField L k hL ν)
      (r := euclidNorm p) (M := M) (K := 4 * M / (δPlus / 2)) (D := D)
      hr0 hr1 hM0 (tripleAmplitude_eq_add hL _ _ _) (tripleAmplitude_eq_add hL _ _ _)
      (fun c c' => hMle c c' p hpPlus) (fun c c' => hLip c c' p hρ)
      (norm_tripleAmplitude_sub_le hL
        (x' := constantFormOnQuot L k (((finestMesh L k : ℝ) : ℂ) • axisPauliElement μ 2))
        (mul_nonneg hD0 hr0) fun c => (hA c).trans (hCD μ _ hr0))
      (norm_tripleAmplitude_sub_le hL
        (x' := constantFormOnQuot L k (((finestMesh L k : ℝ) : ℂ) • axisPauliElement ν 2))
        (mul_nonneg hD0 hr0) fun c => (hA' c).trans (hCD ν _ hr0))
      (norm_tripleAmplitude_zero_le hL (mul_nonneg hD0 hr2)
        (fun c => (hJ c).trans (hCD μ _ hr2)) fun c => (hm c).trans (hCD μ _ hr2))
      (norm_tripleAmplitude_zero_le hL (mul_nonneg hD0 hr2)
        (fun c => (hJ' c).trans (hCD ν _ hr2)) fun c => (hm' c).trans (hCD ν _ hr2))
      (hDf μ) (hDf ν) hleft hright
    unfold freePolarizationEntry
    rw [hvalue p hps, hvalue p hps]
    exact main
end YangMills.Construction.Tower.ResponseSecondVariation
end
