import YangMills.Construction.PeriodicOperators.SumOfLocalOperatorFunctionsProof
import YangMills.Construction.Towers.ResponseFieldOfAPlaneWaveProof
import YangMills.Construction.Towers.TheBackgroundNumbersNearZeroProof
import YangMills.Construction.Towers.WeightedTransposesOfTheScaledPictureOnASideProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.ResponseSymbolNearStrip
open PeriodicOperators
open BackgroundFieldResponse (responseKernel responseDefect)
open FullSpace
section Holomorphic
variable {N : ℕ}
theorem isHolomorphicIn_scalar_mono {O O' : Set (Coordinates.ComplexCoordinates N)}
    {u : Coordinates.ComplexCoordinates N → ℂ}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z) (hs : O' ⊆ O)
    (ho : IsOpen O') :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O' fun z _ => u z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_mono <;> assumption
theorem isHolomorphicIn_scalar_congr {O : Set (Coordinates.ComplexCoordinates N)}
    {u v : Coordinates.ComplexCoordinates N → ℂ}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z)
    (e : EqOn v u O) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => v z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_congr <;> assumption
theorem isHolomorphicIn_scalar_const {O : Set (Coordinates.ComplexCoordinates N)} (ho : IsOpen O)
    (c : ℂ) : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun _ _ => c := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_const <;> assumption
theorem isHolomorphicIn_scalar_add {O : Set (Coordinates.ComplexCoordinates N)}
    {u v : Coordinates.ComplexCoordinates N → ℂ}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z)
    (h' : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => v z) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z + v z := by apply _root_.YangMills.Construction.PeriodicOperators.OpFunAdd.isHolomorphicIn_add <;> assumption
theorem isHolomorphicIn_scalar_mul {O : Set (Coordinates.ComplexCoordinates N)}
    {u v : Coordinates.ComplexCoordinates N → ℂ}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z)
    (h' : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => v z) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z * v z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_mul <;> assumption
end Holomorphic
def HolomorphicBoundedOn (O : Set (Fin 4 → ℂ)) (u : (Fin 4 → ℂ) → ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O (fun z _ => u z) ∧
    ∃ C : ℝ, ∀ x ∈ O, ‖u x‖ ≤ C
namespace HolomorphicBoundedOn
variable {O : Set (Fin 4 → ℂ)} {u v : (Fin 4 → ℂ) → ℂ}
theorem congr (h : HolomorphicBoundedOn O u) (e : EqOn v u O) : HolomorphicBoundedOn O v := by
  obtain ⟨h₁, C, hC⟩ := h
  exact ⟨isHolomorphicIn_scalar_congr h₁ e, C, fun x hx => by rw [e hx]; exact hC x hx⟩
theorem const (ho : IsOpen O) (c : ℂ) : HolomorphicBoundedOn O fun _ => c :=
  ⟨isHolomorphicIn_scalar_const ho c, ‖c‖, fun _ _ => le_rfl⟩
theorem mul (h : HolomorphicBoundedOn O u) (h' : HolomorphicBoundedOn O v) :
    HolomorphicBoundedOn O fun x => u x * v x := by
  obtain ⟨h₁, C, hC⟩ := h
  obtain ⟨h₁', C', hC'⟩ := h'
  refine ⟨isHolomorphicIn_scalar_mul h₁ h₁', |C| * |C'|, fun x hx => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hC x hx).trans (le_abs_self C)) ((hC' x hx).trans (le_abs_self C'))
    (norm_nonneg _) (abs_nonneg C)
theorem add (h : HolomorphicBoundedOn O u) (h' : HolomorphicBoundedOn O v) :
    HolomorphicBoundedOn O fun x => u x + v x := by
  obtain ⟨h₁, C, hC⟩ := h
  obtain ⟨h₁', C', hC'⟩ := h'
  exact ⟨isHolomorphicIn_scalar_add h₁ h₁', C + C', fun x hx =>
    (norm_add_le _ _).trans (add_le_add (hC x hx) (hC' x hx))⟩
theorem sum {J : Type} (s : Finset J) (ho : IsOpen O) {w : J → (Fin 4 → ℂ) → ℂ}
    (h : ∀ i ∈ s, HolomorphicBoundedOn O (w i)) :
    HolomorphicBoundedOn O fun x => ∑ i ∈ s, w i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact const ho 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))
end HolomorphicBoundedOn
theorem apply_eq_sum_linearMapEntry {J J' : Type} [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (f : J → ℂ) (c' : J') :
    M f c' = ∑ c, linearMapEntry M c' c * f c := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.apply_eq_sum_linearMapEntry <;> assumption
theorem holomorphicBoundedOn_apply {J J' : Type} [Finite J] {O : Set (Fin 4 → ℂ)} (ho : IsOpen O)
    {M : (Fin 4 → ℂ) → (J → ℂ) →ₗ[ℂ] (J' → ℂ)} {b : (Fin 4 → ℂ) → J → ℂ}
    (hM : ∀ c' c, HolomorphicBoundedOn O fun p => linearMapEntry (M p) c' c)
    (hb : ∀ c, HolomorphicBoundedOn O fun p => b p c) (c' : J') :
    HolomorphicBoundedOn O fun p => M p (b p) c' := by
  have := Fintype.ofFinite J
  exact (HolomorphicBoundedOn.sum Finset.univ ho fun c _ => (hM c' c).mul (hb c)).congr
    fun p _ => apply_eq_sum_linearMapEntry _ _ _
theorem waveAmplitude_blochWave (I : PeriodicData) (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    waveAmplitude I κ (blochWave I κ φ) = φ := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.waveAmplitude_blochWave <;> assumption
theorem smul_blochWave (I : PeriodicData) (κ : Fin 4 → ℂ) (z : ℂ) (φ : I.UnitQuot → ℂ) :
    z • blochWave I κ φ = blochWave I κ (z • φ) := by
  funext ι
  simp only [blochWave, Pi.smul_apply, smul_eq_mul]
  ring
theorem symbolHom_apply (I I' : PeriodicData) [Finite I.UnitQuot] (T : I'.Carrier → I.Carrier → ℂ)
    (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    symbolHom I I' T κ φ = applyKernel (quotSymbol I I' T κ) φ :=
  linearMapOfEntries_eq_applyKernel _ _
theorem applyKernel_blochWave_eq {I I' : PeriodicData} [Finite I.UnitQuot]
    {T : I'.Carrier → I.Carrier → ℂ} {κ : Fin 4 → ℂ} {φ : I.UnitQuot → ℂ}
    (h : ∀ ι', applyKernel T (blochWave I κ φ) ι' =
      blochWave I' κ (applyKernel (quotSymbol I I' T κ) φ) ι') :
    applyKernel T (blochWave I κ φ) = blochWave I' κ (symbolHom I I' T κ φ) := by
  funext ι'
  rw [h ι', symbolHom_apply]
theorem constantFormAmplitude_mkQuot (hT : PeriodicOperators.TowerTranslations.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0)
    (ε : Fin 4 → Matrices.ComplexMatrix2) (a : Fin 3) (b : PeriodicOperators.PosEdge L k k)
    (ρ : Fin 4) (hb : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k k) ρ) :
    constantFormAmplitude L k ε ((colourEdges L k k).mkQuot 1 (a, b)) =
      pauliCoeff a (ε ρ) := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.BackgroundCoeffsNearZero.constantFormAmplitude_mkQuot <;> assumption
theorem pauliCoeff_smul_add (a : Fin 3) (c : ℂ) {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless) :
    pauliCoeff a (c • X + Y) = c * pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.WeightedTransposesOnTorus.pauliCoeff_smul_add <;> assumption
theorem constantFormAmplitude_smul_add (hT : PeriodicOperators.TowerTranslations.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (c : ℂ)
    {ε ε' : Fin 4 → Matrices.ComplexMatrix2}
    (hε : IsTracelessTuple ε) (hε' : IsTracelessTuple ε') :
    constantFormAmplitude L k (c • ε + ε') =
      c • constantFormAmplitude L k ε + constantFormAmplitude L k ε' := by
  have hs : meshAt L k k ≠ 0 := by simp [meshAt]
  funext x
  induction x using Quot.ind with
  | mk ι =>
    obtain ⟨a, b⟩ := ι
    obtain ⟨μ, hμ⟩ := b.2
    have e₀ := constantFormAmplitude_mkQuot hT hL hk hs (c • ε + ε') a b μ hμ
    have e₁ := constantFormAmplitude_mkQuot hT hL hk hs ε a b μ hμ
    have e₂ := constantFormAmplitude_mkQuot hT hL hk hs ε' a b μ hμ
    show constantFormAmplitude L k (c • ε + ε') ((colourEdges L k k).mkQuot 1 (a, b)) =
      c * constantFormAmplitude L k ε ((colourEdges L k k).mkQuot 1 (a, b)) +
        constantFormAmplitude L k ε' ((colourEdges L k k).mkQuot 1 (a, b))
    rw [e₀, e₁, e₂]
    exact pauliCoeff_smul_add a c (hε μ) (hε' μ)
theorem tripleAmplitude_mkQuot {L k : ℕ} (hL : 0 < L) (x j : (colourEdges L k 0).UnitQuot → ℂ)
    (m : (colourEdges L k k).UnitQuot → ℂ) (ι : (fieldPeriodicData L k hL).Carrier) :
    tripleAmplitude L k hL x j m ((fieldPeriodicData L k hL).mkQuot 1 ι) =
      tripleIndexFunction L k hL x j m ι := by apply _root_.YangMills.Construction.Tower.ResponseOfFourierMode.tripleAmplitude_mkQuot <;> assumption
theorem tripleAmplitude_smul_add {L k : ℕ} (hL : 0 < L) (c : ℂ)
    (x x' j j' : (colourEdges L k 0).UnitQuot → ℂ) (m m' : (colourEdges L k k).UnitQuot → ℂ) :
    tripleAmplitude L k hL (c • x + x') (c • j + j') (c • m + m') =
      c • tripleAmplitude L k hL x j m + tripleAmplitude L k hL x' j' m' := by
  funext y
  induction y using Quot.ind with
  | mk ι =>
    have e₀ := tripleAmplitude_mkQuot hL (c • x + x') (c • j + j') (c • m + m') ι
    have e₁ := tripleAmplitude_mkQuot hL x j m ι
    have e₂ := tripleAmplitude_mkQuot hL x' j' m' ι
    show tripleAmplitude L k hL (c • x + x') (c • j + j') (c • m + m')
        ((fieldPeriodicData L k hL).mkQuot 1 ι) =
      c * tripleAmplitude L k hL x j m ((fieldPeriodicData L k hL).mkQuot 1 ι) +
        tripleAmplitude L k hL x' j' m' ((fieldPeriodicData L k hL).mkQuot 1 ι)
    rw [e₀, e₁, e₂]
    obtain ⟨pl, ι₀⟩ := ι
    cases pl <;> rfl
theorem tripleAmplitude_holomorphicBoundedOn {L k : ℕ} (hL : 0 < L) {O : Set (Fin 4 → ℂ)}
    {x j : (Fin 4 → ℂ) → (colourEdges L k 0).UnitQuot → ℂ}
    {m : (Fin 4 → ℂ) → (colourEdges L k k).UnitQuot → ℂ}
    (hx : ∀ c, HolomorphicBoundedOn O fun p => x p c)
    (hj : ∀ c, HolomorphicBoundedOn O fun p => j p c)
    (hm : ∀ c, HolomorphicBoundedOn O fun p => m p c) (c : (fieldPeriodicData L k hL).UnitQuot) :
    HolomorphicBoundedOn O fun p => tripleAmplitude L k hL (x p) (j p) (m p) c := by
  induction c using Quot.ind with
  | mk ι =>
    obtain ⟨pl, ι₀⟩ := ι
    cases pl
    · refine (hx ((colourEdges L k 0).mkQuot 1 ι₀)).congr fun p _ => ?_
      exact tripleAmplitude_mkQuot hL (x p) (j p) (m p) ⟨.background, ι₀⟩
    · refine (hj ((colourEdges L k 0).mkQuot 1 ι₀)).congr fun p _ => ?_
      exact tripleAmplitude_mkQuot hL (x p) (j p) (m p) ⟨.source, ι₀⟩
    · refine (hm ((colourEdges L k k).mkQuot 1 ι₀)).congr fun p _ => ?_
      exact tripleAmplitude_mkQuot hL (x p) (j p) (m p) ⟨.coarse, ι₀⟩
section Components
variable {L k : ℕ} [Finite (colourEdges L k k).UnitQuot] {υ : ℝ} {p : Fin 4 → ℂ}
def defectAmplitude (L k : ℕ) (p : Fin 4 → ℂ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    (colourEdges L k k).UnitQuot → ℂ :=
  symbolHom (colourEdges L k k) (colourEdges L k k) (responseDefect L k) p
    (constantFormAmplitude L k ε)
theorem responseKernel_planeWaveOfConstant
    (hr : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k 0)
      (responseKernel L k) υ)
    (hp : p ∈ openImStrip υ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    applyKernel (responseKernel L k) (planeWaveOfConstant L k p ε) =
      blochWave (colourEdges L k 0) p
        (symbolHom (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) p
          (constantFormAmplitude L k ε)) :=
  applyKernel_blochWave_eq fun ι' => (hr.applyKernel_blochWave p hp _ ι').2
theorem defectOfWave_eq
    (hn : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k k)
      (responseDefect L k) υ)
    (hp : p ∈ openImStrip υ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    defectOfWave L k p ε = blochWave (colourEdges L k k) p (defectAmplitude L k p ε) :=
  applyKernel_blochWave_eq fun ι' => (hn.applyKernel_blochWave p hp _ ι').2
theorem backgroundResponseSymbol_eq
    (hr : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k 0)
      (responseKernel L k) υ)
    (hp : p ∈ openImStrip υ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    backgroundResponseSymbol L k p ε =
      ((finestMesh L k : ℝ) : ℂ) •
        symbolHom (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) p
          (constantFormAmplitude L k ε) := by
  rw [backgroundResponseSymbol, responseKernel_planeWaveOfConstant hr hp, smul_blochWave,
    waveAmplitude_blochWave]
theorem coarseResponseSymbol_eq
    (hn : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k k)
      (responseDefect L k) υ)
    (hp : p ∈ openImStrip υ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    coarseResponseSymbol L k p ε = defectAmplitude L k p ε := by
  rw [coarseResponseSymbol, defectOfWave_eq hn hp, waveAmplitude_blochWave]
theorem crossingSmoothingTranspose_blochWave (hQ : TransposeKernelProps L k) (p : Fin 4 → ℂ)
    (φ : (colourEdges L k k).UnitQuot → ℂ) :
    crossingSmoothingTranspose L k (blochWave (colourEdges L k k) p φ) =
      blochWave (colourEdges L k 0) p
        (symbolHom (colourEdges L k k) (colourEdges L k 0)
          (crossingSmoothingTransposeKernel L k) p φ) := by
  rw [← (hQ.represents _).2]
  exact applyKernel_blochWave_eq fun ι' => (hQ.acts_on_blochWave p φ ι').2
theorem sourceResponseSymbol_eq (hQ : TransposeKernelProps L k)
    (hn : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k k)
      (responseDefect L k) υ)
    (hp : p ∈ openImStrip υ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    sourceResponseSymbol L k p ε =
      symbolHom (colourEdges L k k) (colourEdges L k 0) (crossingSmoothingTransposeKernel L k) p
        (defectAmplitude L k p ε) := by
  rw [sourceResponseSymbol, defectOfWave_eq hn hp, crossingSmoothingTranspose_blochWave hQ,
    waveAmplitude_blochWave]
end Components
theorem linearMapEntry_holomorphic_of_entire (hQ : PeriodicOperators.StripSymbols.Claim)
    {I I' : PeriodicData} (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hper : IsPeriodicKernel I I' T)
    (hent : FourierSymbolIsEntire I I' T) (c' : I'.UnitQuot) (c : I.UnitQuot) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) univ fun κ _ =>
      linearMapEntry (symbolHom I I' T κ) c' c := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_linearMapEntry_of_entire <;> assumption
theorem isOpen_openImStrip (υ : ℝ) : IsOpen (openImStrip υ) := by apply _root_.YangMills.Construction.PeriodicOperators.ExpDecaySymbol.isOpen_openImStrip <;> assumption
theorem componentsHolomorphicBoundedOn_of_forall {C : Type} {O : Set (Fin 4 → ℂ)} (ho : IsOpen O)
    {a : (Fin 4 → ℂ) → C → ℂ} (h : ∀ c, HolomorphicBoundedOn O fun p => a p c) :
    EntriesHolomorphicBoundedOn O a :=
  ⟨⟨by norm_num, ho, fun c => (h c).1⟩, fun c => (h c).2⟩
theorem holdsOn_inter_openImStrip (hT : PeriodicOperators.TowerTranslations.Claim)
    (hSy : PeriodicOperators.StripSymbols.Claim) {L k : ℕ} (hL : 0 < L)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hB₀ : IsPeriodic (colourEdges L k 0)) (hBk : IsPeriodic (colourEdges L k k))
    (hQ : TransposeKernelProps L k) {O₁ : Set (Fin 4 → ℂ)} (ho₁ : IsOpen O₁)
    (hon : ResponseOperators.ResponseSymbolsOn L k O₁) {υ : ℝ}
    (hr : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k 0)
      (responseKernel L k) υ)
    (hn : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k k)
      (responseDefect L k) υ) :
    HoldsOn L k hL (O₁ ∩ openImStrip υ) := by
  have : Finite (colourEdges L k k).UnitQuot := hBk.finite_quot
  have ho : IsOpen (O₁ ∩ openImStrip υ) := ho₁.inter (isOpen_openImStrip υ)
  have hsub₁ : O₁ ∩ openImStrip υ ⊆ O₁ := inter_subset_left
  have hsub₂ : O₁ ∩ openImStrip υ ⊆ openImStrip υ := inter_subset_right
  have hsub₃ : O₁ ∩ openImStrip υ ⊆ imStrip (max υ 1) := fun p hp μ =>
    ((hsub₂ hp μ).le).trans (le_max_left _ _)
  have hh : ∀ c' c, HolomorphicBoundedOn (O₁ ∩ openImStrip υ) fun p =>
      linearMapEntry
        (symbolHom (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) p) c' c :=
    fun c' c => by
      obtain ⟨C, hC⟩ := hon.resp_bounded (c', c)
      exact ⟨isHolomorphicIn_scalar_mono (hon.resp_holomorphic.2.2 (c', c)) hsub₁ ho, C,
        fun x hx => hC x (hsub₁ hx)⟩
  have hν : ∀ c' c, HolomorphicBoundedOn (O₁ ∩ openImStrip υ) fun p =>
      linearMapEntry
        (symbolHom (colourEdges L k k) (colourEdges L k k) (responseDefect L k) p) c' c :=
    fun c' c => by
      obtain ⟨C, hC⟩ := hon.defect_bounded (c', c)
      exact ⟨isHolomorphicIn_scalar_mono (hon.defect_holomorphic.2.2 (c', c)) hsub₁ ho, C,
        fun x hx => hC x (hsub₁ hx)⟩
  have hq : ∀ c' c, HolomorphicBoundedOn (O₁ ∩ openImStrip υ) fun p =>
      linearMapEntry (symbolHom (colourEdges L k k) (colourEdges L k 0)
        (crossingSmoothingTransposeKernel L k) p) c' c :=
    fun c' c => by
      obtain ⟨C, hC⟩ := hQ.bounded (max υ 1) (lt_of_lt_of_le one_pos (le_max_right _ _)) (c', c)
      exact ⟨isHolomorphicIn_scalar_mono
        (linearMapEntry_holomorphic_of_entire hSy hBk hB₀ hQ.periodic hQ.entire c' c)
        (subset_univ _) ho, C, fun x hx => hC x (hsub₃ hx)⟩
  have hconst : ∀ (ε : Fin 4 → Matrices.ComplexMatrix2) c,
      HolomorphicBoundedOn (O₁ ∩ openImStrip υ) fun _ => constantFormAmplitude L k ε c :=
    fun ε c => HolomorphicBoundedOn.const ho _
  have hμ : ∀ (ε : Fin 4 → Matrices.ComplexMatrix2) c,
      HolomorphicBoundedOn (O₁ ∩ openImStrip υ) fun p => defectAmplitude L k p ε c := fun ε c =>
    holomorphicBoundedOn_apply ho hν (hconst ε) c
  have hbg : ∀ (ε : Fin 4 → Matrices.ComplexMatrix2) c,
      HolomorphicBoundedOn (O₁ ∩ openImStrip υ) fun p => backgroundResponseSymbol L k p ε c :=
    fun ε c =>
      ((HolomorphicBoundedOn.const ho ((finestMesh L k : ℝ) : ℂ)).mul
        (holomorphicBoundedOn_apply ho hh (hconst ε) c)).congr fun p hp =>
          congrFun (backgroundResponseSymbol_eq hr (hsub₂ hp) ε) c
  have hco : ∀ (ε : Fin 4 → Matrices.ComplexMatrix2) c,
      HolomorphicBoundedOn (O₁ ∩ openImStrip υ) fun p => coarseResponseSymbol L k p ε c :=
    fun ε c => (hμ ε c).congr fun p hp => congrFun (coarseResponseSymbol_eq hn (hsub₂ hp) ε) c
  have hcu : ∀ (ε : Fin 4 → Matrices.ComplexMatrix2) c,
      HolomorphicBoundedOn (O₁ ∩ openImStrip υ) fun p => sourceResponseSymbol L k p ε c :=
    fun ε c => (holomorphicBoundedOn_apply ho hq (hμ ε) c).congr fun p hp =>
      congrFun (sourceResponseSymbol_eq hQ hn (hsub₂ hp) ε) c
  refine
    { map_smul_add := ?_
      symbol_entries := fun ε _ => componentsHolomorphicBoundedOn_of_forall ho
        (tripleAmplitude_holomorphicBoundedOn hL (hbg ε) (hcu ε) (hco ε))
      background_entries := fun ε _ => componentsHolomorphicBoundedOn_of_forall ho (hbg ε)
      source_entries := fun ε _ => componentsHolomorphicBoundedOn_of_forall ho (hcu ε)
      coarse_entries := fun ε _ => componentsHolomorphicBoundedOn_of_forall ho (hco ε)
      background_wave := fun p hp ε _ =>
        ⟨fun ι' => (hr.applyKernel_blochWave p (hsub₂ hp) _ ι').1, ?_⟩
      source_wave := fun p hp ε _ => ?_
      coarse_wave := fun p hp ε _ =>
        ⟨fun ι' => (hn.applyKernel_blochWave p (hsub₂ hp) _ ι').1, ?_⟩ }
  · intro p hp c ε ε' hε hε'
    have ea := constantFormAmplitude_smul_add hT hs hk c hε hε'
    have hp₂ := hsub₂ hp
    have e₁ : backgroundResponseSymbol L k p (c • ε + ε') =
        c • backgroundResponseSymbol L k p ε + backgroundResponseSymbol L k p ε' := by
      simp only [backgroundResponseSymbol_eq hr hp₂, ea, map_add, map_smul, smul_add]
      rw [smul_comm]
    have e₃ : defectAmplitude L k p (c • ε + ε') =
        c • defectAmplitude L k p ε + defectAmplitude L k p ε' := by
      simp only [defectAmplitude, ea, map_add, map_smul]
    have e₂ : sourceResponseSymbol L k p (c • ε + ε') =
        c • sourceResponseSymbol L k p ε + sourceResponseSymbol L k p ε' := by
      simp only [sourceResponseSymbol_eq hQ hn hp₂, e₃, map_add, map_smul]
    have e₄ : coarseResponseSymbol L k p (c • ε + ε') =
        c • coarseResponseSymbol L k p ε + coarseResponseSymbol L k p ε' := by
      simp only [coarseResponseSymbol_eq hn hp₂, e₃]
    rw [FullSpace.responseSymbol, e₁, e₂, e₄, tripleAmplitude_smul_add]
    rfl
  · rw [backgroundResponseSymbol_eq hr (hsub₂ hp), responseKernel_planeWaveOfConstant hr (hsub₂ hp),
      smul_blochWave]
  · rw [sourceResponseSymbol_eq hQ hn (hsub₂ hp), defectOfWave_eq hn (hsub₂ hp),
      crossingSmoothingTranspose_blochWave hQ]
  · rw [coarseResponseSymbol_eq hn (hsub₂ hp), defectOfWave_eq hn (hsub₂ hp)]
theorem responseSymbolHolomorphicNearStrip_holds (hResp : ResponseOperators.Claim)
    (hCom : FullSpace.JointWidthAndTransposeTheorem)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hT : PeriodicOperators.TowerTranslations.Claim)
    (hSy : PeriodicOperators.StripSymbols.Claim) : ResponseSymbolHolomorphicNearStrip := by
  obtain ⟨δ₀, hδ, h⟩ := hResp
  refine ⟨δ₀, hδ, fun L hL hs k hk => ?_⟩
  have A := h L hs k hk
  obtain ⟨O₁, ho₁, hsub, hon⟩ := A.near
  obtain ⟨υ, hυ, _, hr, hn⟩ := A.exists_rate
  refine ⟨O₁ ∩ openImStrip υ, ho₁.inter (isOpen_openImStrip υ),
    fun p hp => ⟨hsub hp, fun μ => (hp μ).trans_lt hυ⟩, ?_⟩
  exact holdsOn_inter_openImStrip hT hSy hL hs hk (hIdx L hs k 0 (Nat.zero_le k)).2.1
    (hIdx L hs k k le_rfl).2.1 (hCom L hL hs k hk).2.2.1 ho₁ hon hr hn
end YangMills.Construction.Tower.ResponseSymbolNearStrip
end
