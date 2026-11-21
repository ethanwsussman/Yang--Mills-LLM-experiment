import YangMills.Construction.PeriodicOperators.TranslationsOnTheIndexSetsOfATower
import YangMills.Construction.Towers.FourierSumsOnTheSitesOfTheFinestLatticeProof
import YangMills.Construction.Towers.PlaneWaveCoefficientsOnTheBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
namespace EdgeWaves
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (PeriodicData colourEdges intShift descendFn_mkQuot IsQuotInvariant wInner wNorm)
open PlaneWaves
open PlaneWaveCalculus
open FinestFourierSums (FourierFacts IsIntPeriodic)
variable {L k : ℕ}
def edgeAxis (e : PeriodicOperators.PosEdge L k 0) : Fin 4 := e.2.choose
theorem terminal_sub_initial (e : PeriodicOperators.PosEdge L k 0) :
    e.1.terminal - e.1.initial = InfiniteLattice.axisStep _ (edgeAxis e) := e.2.choose_spec
theorem eq_edgeAt (e : PeriodicOperators.PosEdge L k 0) :
    e = edgeAt L k e.1.initial (edgeAxis e) := by
  apply Subtype.ext
  refine InfiniteLattice.Link.ext rfl ?_
  show e.1.terminal = e.1.initial + InfiniteLattice.axisStep _ (edgeAxis e)
  rw [← terminal_sub_initial]
  abel
theorem meshAt_ne_zero (hL : Conventions.IsAdmissibleBlockingFactor L) : meshAt L k 0 ≠ 0 := by apply _root_.YangMills.Construction.Tower.FinestFourierSums.meshAt_zero_ne_zero <;> assumption
theorem axisStep_injective (hL : Conventions.IsAdmissibleBlockingFactor L) {μ ν : Fin 4}
    (h : InfiniteLattice.axisStep (meshAt L k 0) μ = InfiniteLattice.axisStep (meshAt L k 0) ν) :
    μ = ν := by
  by_contra hne
  have h1 := congrArg (fun s : FullSpace.Vertex L k 0 => (s : AmbientSpace) μ) h
  simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hne] at h1
  exact meshAt_ne_zero hL h1
theorem edgeAxis_edgeAt (hL : Conventions.IsAdmissibleBlockingFactor L) (x : FullSpace.Vertex L k 0)
    (μ : Fin 4) : edgeAxis (edgeAt L k x μ) = μ := by
  apply axisStep_injective (k := k) hL
  rw [← terminal_sub_initial]
  show x + _ - x = _
  abel
variable (hG : PeriodicOperators.TowerTranslations.Claim)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
include hG hL hk
theorem translate_edgeAt (n : Fin 4 → ℤ) (c : Fin 3) (x : FullSpace.Vertex L k 0) (μ : Fin 4) :
    (colourEdges L k 0).translate n (c, edgeAt L k x μ) =
      (c, edgeAt L k (FullSpace.vertexImage (intShift n) x) μ) := by
  obtain ⟨-, -, -, h, -⟩ := hG L hL k 0 hk (Nat.zero_le k) n
  exact h c (edgeAt L k x μ) μ (by show x + _ - x = _; abel)
theorem exists_quotEquiv : ∃ e : Fin 3 × Fin 4 × VertexClass L k ≃ (colourEdges L k 0).UnitQuot,
    ∀ a μ x, e (a, μ, Quot.mk _ x) = (colourEdges L k 0).mkQuot 1 (a, edgeAt L k x μ) := by
  refine ⟨⟨fun p => Quot.lift (fun x => (colourEdges L k 0).mkQuot 1 (p.1, edgeAt L k x p.2.1))
      ?_ p.2.2,
    Quot.lift (fun ι : Fin 3 × PeriodicOperators.PosEdge L k 0 =>
      (ι.1, edgeAxis ι.2, Quot.mk _ ι.2.1.initial)) ?_, ?_, ?_⟩, fun _ _ _ => rfl⟩
  · rintro x _ ⟨n, rfl⟩
    refine Quot.sound ⟨n, ?_⟩
    rw [one_smul]
    exact (translate_edgeAt hG hL hk n p.1 x p.2.1).symm
  · rintro ⟨c, e⟩ _ ⟨n, rfl⟩
    obtain ⟨x, μ, rfl⟩ : ∃ x μ, e = edgeAt L k x μ := ⟨_, _, eq_edgeAt e⟩
    rw [one_smul]
    show (c, edgeAxis (edgeAt L k x μ), Quot.mk _ x) = _
    have := translate_edgeAt hG hL hk n c x μ
    show _ = (((colourEdges L k 0).translate n (c, edgeAt L k x μ)).1, edgeAxis ((colourEdges L k 0).translate n (c, edgeAt L k x μ)).2, Quot.mk _ ((colourEdges L k 0).translate n (c, edgeAt L k x μ)).2.1.initial)
    rw [this]
    simp only [edgeAxis_edgeAt hL]
    exact congrArg (fun s => (c, μ, s)) (Quot.sound ⟨n, rfl⟩)
  · rintro ⟨a, μ, c⟩
    induction c using Quot.ind with
    | mk x =>
      show (a, edgeAxis (edgeAt L k x μ), Quot.mk _ x) = _
      rw [edgeAxis_edgeAt hL]
  · intro c
    induction c using Quot.ind with
    | mk ι =>
      obtain ⟨a, e⟩ := ι
      show (colourEdges L k 0).mkQuot 1 (a, edgeAt L k e.1.initial (edgeAxis e)) = _
      rw [← eq_edgeAt e]
      rfl
omit hG hL hk in
theorem isQuotInvariant_of_forall (I : PeriodicData) (f : I.Carrier → ℂ)
    (h : ∀ (n : Fin 4 → ℤ) ι, f (I.translate n ι) = f ι) : IsQuotInvariant I f := by
  intro ι ι' e
  have h' : ∀ ι ι' : I.Carrier, (∃ n : Fin 4 → ℤ, ι' = I.translate (1 • n) ι) → f ι = f ι' := by
    rintro ι _ ⟨n, rfl⟩
    rw [one_smul, h]
  exact congrArg (Quot.lift f h') e
omit hG hL hk in
theorem quotWeight_eq (c : (colourEdges L k 0).UnitQuot) :
    (colourEdges L k 0).quotWeight 1 c = finestMesh L k ^ 4 := by
  induction c using Quot.ind with
  | mk ι =>
    exact (Classical.epsilon_spec
      (p := fun w => ∀ ι', (colourEdges L k 0).mkQuot 1 ι' = Quot.mk _ ι →
        (colourEdges L k 0).weightOf ι' = w) ⟨meshAt L k 0 ^ 4, fun _ _ => rfl⟩ ι rfl).symm
omit hG hL hk in
theorem tsum_quot_eq {M : Type} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]
    [Finite (VertexClass L k)] (e : Fin 3 × Fin 4 × VertexClass L k ≃ (colourEdges L k 0).UnitQuot)
    (F : (colourEdges L k 0).UnitQuot → M) :
    ∑' c, F c = ∑ a, ∑ μ, ∑ᶠ s : VertexClass L k, F (e (a, μ, s)) := by
  have := Fintype.ofFinite (VertexClass L k)
  rw [← e.tsum_eq F, tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [finsum_eq_sum_of_fintype]
abbrev labelled (L k : ℕ) (p : Fin 3 × Fin 4) (ι : (colourEdges L k 0).Carrier) : Prop :=
  ι.1 = p.1 ∧ ∃ x, ι.2 = posEdgeAt L k 0 x p.2
omit hG hk in
theorem labelled_iff (p : Fin 3 × Fin 4) (a : Fin 3) (x : FullSpace.Vertex L k 0) (μ : Fin 4) :
    labelled L k p (a, edgeAt L k x μ) ↔ (a, μ) = p := by
  constructor
  · rintro ⟨h, y, e⟩
    have h2 : μ = p.2 := by
      have := congrArg edgeAxis e
      rw [edgeAxis_edgeAt hL] at this
      exact this.trans (edgeAxis_edgeAt hL y p.2)
    exact Prod.ext h h2
  · rintro rfl
    exact ⟨rfl, x, rfl⟩
def coord (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) :
    Fin 3 × FullSpace.Vertex L k 0 → ℂ :=
  fun ι => b ((colourEdges L k 0).mkQuot 1 (ι.1, edgeAt L k ι.2 μ))
theorem coord_periodic (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) (a : Fin 3) :
    IsIntPeriodic L k fun x => coord b μ (a, x) := by
  intro n x
  refine congrArg b (Eq.symm (Quot.sound ⟨n, ?_⟩))
  rw [one_smul]
  exact (translate_edgeAt hG hL hk n a x μ).symm
theorem edgeField_periodic (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) :
    IsIntPeriodic L k fun x => edgeFieldOfClasses L k b (edgeAt L k x μ) := by
  intro n x
  show ∑ a, coord b μ (a, _) • Matrices.ComplexMatrix2.pauliFamily a = ∑ a, coord b μ (a, x) • Matrices.ComplexMatrix2.pauliFamily a
  exact Finset.sum_congr rfl fun a _ =>
    congrArg (· • Matrices.ComplexMatrix2.pauliFamily a) (coord_periodic hG hL hk b μ a n x)
theorem waveOnQuot_apply (F : FourierFacts L k) (p : Fin 3 × Fin 4) (m : Fin 4 → ℤ) (a : Fin 3)
    (x : FullSpace.Vertex L k 0) (μ : Fin 4) :
    open Classical in
    waveOnQuot (colourEdges L k 0) (labelled L k p) m
        ((colourEdges L k 0).mkQuot 1 (a, edgeAt L k x μ)) =
      if (a, μ) = p then integerWave m (x : AmbientSpace) else 0 := by
  classical
  have hone : IsQuotInvariant (colourEdges L k 0) fun ι =>
      @ite ℂ (labelled L k p ι) (Classical.propDecidable _)
        (integerWave m ((colourEdges L k 0).pos ι)) 0 := by
    refine isQuotInvariant_of_forall _ _ ?_
    rintro n ⟨c, β⟩
    obtain ⟨y, ν, rfl⟩ : ∃ y ν, β = edgeAt L k y ν := ⟨_, _, eq_edgeAt β⟩
    rw [translate_edgeAt hG hL hk n c y ν]
    simp only [labelled_iff hL]
    split_ifs
    · exact F.integerWave_periodic m n y
    · rfl
  refine (descendFn_mkQuot hone (a, edgeAt L k x μ)).trans ?_
  by_cases h : (a, μ) = p
  · rw [if_pos ((labelled_iff hL p a x μ).2 h), if_pos h]
    rfl
  · rw [if_neg (mt (labelled_iff hL p a x μ).1 h), if_neg h]
omit hG hL hk in
theorem apply_eq_mkQuot_out (e : Fin 3 × Fin 4 × VertexClass L k ≃ (colourEdges L k 0).UnitQuot)
    (he : ∀ a μ x, e (a, μ, Quot.mk _ x) = (colourEdges L k 0).mkQuot 1 (a, edgeAt L k x μ))
    (a : Fin 3) (μ : Fin 4) (s : VertexClass L k) :
    e (a, μ, s) = (colourEdges L k 0).mkQuot 1 (a, edgeAt L k (Quot.out s) μ) := by
  rw [← he, Quot.out_eq]
theorem wInner_waves (F : FourierFacts L k) (p p' : Fin 3 × Fin 4) (m m' : Fin 4 → ℤ)
    (hm : m ∈ freqBox L k) (hm' : m' ∈ freqBox L k) :
    open Classical in
    wInner ((colourEdges L k 0).quotWeight 1)
        (waveOnQuot (colourEdges L k 0) (labelled L k p) m)
        (waveOnQuot (colourEdges L k 0) (labelled L k p') m') =
      if p = p' ∧ m = m' then 1 else 0 := by
  classical
  have := F.finite_vertexClass
  obtain ⟨e, he⟩ := exists_quotEquiv hG hL hk
  have key : ∀ a μ s, ((colourEdges L k 0).quotWeight 1 (e (a, μ, s)) : ℂ) *
      ((starRingEnd ℂ) (waveOnQuot (colourEdges L k 0) (labelled L k p) m (e (a, μ, s))) *
        waveOnQuot (colourEdges L k 0) (labelled L k p') m' (e (a, μ, s))) =
      if (a, μ) = p then (if p = p' then
        ((finestMesh L k ^ 4 : ℝ) : ℂ) *
          ((starRingEnd ℂ) (integerWave m (Quot.out s : FullSpace.Vertex L k 0)) *
            integerWave m' (Quot.out s : FullSpace.Vertex L k 0)) else 0) else 0 := by
    intro a μ s
    rw [quotWeight_eq, apply_eq_mkQuot_out e he, waveOnQuot_apply hG hL hk F, waveOnQuot_apply hG hL hk F]
    by_cases h : (a, μ) = p
    · by_cases h' : p = p'
      · rw [if_pos h, if_pos (h.trans h'), if_pos h, if_pos h']
      · rw [if_pos h, if_neg (fun h2 => h' (h.symm.trans h2)), if_pos h, if_neg h']
        simp
    · rw [if_neg h, if_neg h]
      simp
  show PeriodicOperators.wPairing _ _ _ = _
  unfold PeriodicOperators.wPairing
  rw [tsum_quot_eq e]
  simp only [key]
  set G : VertexClass L k → ℂ := fun s => if p = p' then
    ((finestMesh L k ^ 4 : ℝ) : ℂ) *
      ((starRingEnd ℂ) (integerWave m (Quot.out s : FullSpace.Vertex L k 0)) *
        integerWave m' (Quot.out s : FullSpace.Vertex L k 0)) else 0 with hGdef
  calc _ = ∑ q : Fin 3 × Fin 4, if q = p then ∑ᶠ s, G s else 0 := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun μ _ => ?_
        by_cases h : (a, μ) = p
        · simp only [if_pos h]
          rfl
        · simp only [if_neg h, finsum_zero]
    _ = ∑ᶠ s, G s := by simp
    _ = _ := by
        by_cases hpp : p = p'
        · simp only [hGdef, if_pos hpp]
          rw [← mul_finsum, F.orthonormal m hm m' hm']
          simp [hpp]
        · simp [hGdef, hpp]
theorem waves_basis (F : FourierFacts L k) :
    WavesOrthonormalBasis L k (colourEdges L k 0) (labelled L k) := by
  classical
  refine ⟨fun p p' m hm m' hm' => ?_, ?_⟩
  · convert wInner_waves hG hL hk F p p' m m' hm hm'
  have := F.finite_vertexClass
  obtain ⟨e, he⟩ := exists_quotEquiv hG hL hk
  rw [Submodule.eq_top_iff']
  intro f
  have hz : ∀ p : Fin 3 × Fin 4, ∃ z : (Fin 4 → ℤ) → ℂ, ∀ x : FullSpace.Vertex L k 0,
      coord f p.2 (p.1, x) = ∑ m ∈ freqBox L k, z m * integerWave m (x : AmbientSpace) :=
    fun p => F.span _ (coord_periodic hG hL hk f p.2 p.1)
  choose z hz using hz
  have hf : f = ∑ p : Fin 3 × Fin 4, ∑ m ∈ freqBox L k,
      z p m • waveOnQuot (colourEdges L k 0) (labelled L k p) m := by
    funext d
    obtain ⟨⟨a, μ, s⟩, rfl⟩ := e.surjective d
    rw [Finset.sum_apply, Finset.sum_eq_single (a, μ)]
    · rw [Finset.sum_apply, apply_eq_mkQuot_out e he]
      refine (hz (a, μ) (Quot.out s)).trans (Finset.sum_congr rfl fun m _ => ?_)
      rw [Pi.smul_apply, waveOnQuot_apply hG hL hk F, if_pos rfl, smul_eq_mul]
    · intro q _ hq
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [Pi.smul_apply, apply_eq_mkQuot_out e he, waveOnQuot_apply hG hL hk F, if_neg (Ne.symm hq), smul_zero]
    · simp
  rw [hf]
  exact Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun m hm =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, m, hm, rfl⟩)
theorem wNorm_sq_eq (F : FourierFacts L k) (b : (colourEdges L k 0).UnitQuot → ℂ) :
    wNorm ((colourEdges L k 0).quotWeight 1) b ^ 2 =
      ∑ m ∈ freqBox L k, ∑ μ, pauliNorm (edgeFourierCoeff L k b μ m) ^ 2 := by
  have := F.finite_vertexClass
  obtain ⟨e, he⟩ := exists_quotEquiv hG hL hk
  have hnn : 0 ≤ ∑' c, (colourEdges L k 0).quotWeight 1 c * ‖b c‖ ^ 2 :=
    tsum_nonneg fun c => by
      rw [quotWeight_eq]
      positivity
  rw [wNorm, Real.sq_sqrt hnn, tsum_quot_eq e]
  calc _ = ∑ μ, finestMesh L k ^ 4 *
        ∑ a, ∑ᶠ s : VertexClass L k, ‖coord b μ (a, Quot.out s)‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_finsum]
        refine finsum_congr fun s => ?_
        rw [quotWeight_eq, apply_eq_mkQuot_out e he]
        rfl
    _ = ∑ μ, ∑ m ∈ freqBox L k, pauliNorm (edgeFourierCoeff L k b μ m) ^ 2 :=
        Finset.sum_congr rfl fun μ _ =>
          F.norm_sq (coord b μ) (coord_periodic hG hL hk b μ)
    _ = _ := Finset.sum_comm
theorem wPairing_eq (F : FourierFacts L k) (b b' : (colourEdges L k 0).UnitQuot → ℂ) :
    PeriodicOperators.wPairing ((colourEdges L k 0).quotWeight 1) b b' =
      ∑ m ∈ freqBox L k, ∑ μ,
        tracelessPairing (edgeFourierCoeff L k b μ m) (edgeFourierCoeff L k b' μ (-m)) := by
  have := F.finite_vertexClass
  obtain ⟨e, he⟩ := exists_quotEquiv hG hL hk
  unfold PeriodicOperators.wPairing
  rw [tsum_quot_eq e]
  calc _ = ∑ μ, ((finestMesh L k ^ 4 : ℝ) : ℂ) *
        ∑ a, ∑ᶠ s : VertexClass L k,
          coord b μ (a, Quot.out s) * coord b' μ (a, Quot.out s) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_finsum]
        refine finsum_congr fun s => ?_
        rw [quotWeight_eq, apply_eq_mkQuot_out e he]
        rfl
    _ = ∑ μ, ∑ m ∈ freqBox L k,
        tracelessPairing (edgeFourierCoeff L k b μ m) (edgeFourierCoeff L k b' μ (-m)) :=
        Finset.sum_congr rfl fun μ _ =>
          F.pairing_eq (coord b μ) (coord b' μ) (coord_periodic hG hL hk b μ)
            (coord_periodic hG hL hk b' μ)
    _ = _ := Finset.sum_comm
omit hG hL hk in
theorem edgeCoeffFacts (hG : PeriodicOperators.TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (F : FourierFacts L k) :
    EdgeCoeffFacts L k where
  basis := waves_basis hG hL hk F
  expansion := fun b μ x => F.expansion _ (edgeField_periodic hG hL hk b μ) x
  exp_expansion := fun κ b μ x => by
    rw [F.expansion _ (edgeField_periodic hG hL hk b μ) x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, F.expWave_mul_integerWave]
    rfl
  norm_sq := wNorm_sq_eq hG hL hk F
  pairing_eq := wPairing_eq hG hL hk F
end EdgeWaves
theorem EdgeWaves.planeWaveEdgeCoefficientsHold
    (hF : FinestFourierSums.Claim)
    (hG : PeriodicOperators.TowerTranslations.Claim) :
    PlaneWaveEdgeCoefficientsHold :=
  fun L hL k hk => EdgeWaves.edgeCoeffFacts hG hL hk (hF L hL k hk)
end YangMills.Construction.Tower
end
