import YangMills.Construction.OneLoopLaw.CovarianceOfASymbol
import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLattice
import YangMills.Construction.OneLoopLaw.PolarisationIsInvariantUnderIsometries
import YangMills.Construction.OneLoopLaw.PolarisationOfAMember
import YangMills.Construction.PeriodicOperators.MomentaOfTheToriWithASide
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.OneLoopLaw.SymbolCovariance
open YangMills.Construction.Tower
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.OneLoopLaw.TemperedStiffness
open YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries (tangentPushforward flipCoord)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
theorem eventually_of_eventuallyForSides {L : ℕ} (hL : 2 ≤ L) {P : ℕ → Prop}
    (h : EventuallyForSides L P) : ∃ n₁ : ℕ, 1 ≤ n₁ ∧ ∀ n, n₁ ≤ n → P n := by
  obtain ⟨s₀, ⟨m, hm, rfl⟩, hs⟩ := h
  refine ⟨m, hm, fun n hn => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le hm hn
  refine hs (PeriodicLattice.torusSide L n) ⟨n, hn0, rfl⟩ ?_ n hn0 rfl
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h2 := pow_le_pow_right₀ h1 hn
  unfold PeriodicLattice.torusSide
  linarith
def HoloOn (O : Set (Fin 4 → ℂ)) (f : (Fin 4 → ℂ) → ℂ) : Prop :=
  IsOpen O ∧ ContinuousOn f O ∧ ∀ a ∈ O, ∀ j : Fin 4, ∀ᶠ ζ in 𝓝 (0 : ℂ),
    DifferentiableAt ℂ (fun ζ : ℂ => f (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ
theorem isHolomorphicIn_iff_holoOn {O : Set (Fin 4 → ℂ)} {f : (Fin 4 → ℂ) → ℂ} :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O (fun κ _ => f κ) ↔
      HoloOn O f := by
  unfold Coordinates.ComplexCoordinates.IsHolomorphicIn HoloOn
  refine and_congr_right fun _ => and_congr ?_ ?_
  · constructor
    · intro h
      exact (continuous_apply (0 : Fin 1)).comp_continuousOn h
    · intro h
      exact continuousOn_pi.2 fun _ => h
  · refine forall₂_congr fun a _ => forall_congr' fun j => ?_
    refine eventually_congr (Eventually.of_forall fun ζ => ?_)
    rw [differentiableAt_pi]
    simp
theorem holoOn_twistedSymbol {O : Set (Fin 4 → ℂ)} {π : SymbolArray} {μ ν : Fin 4}
    (h : HoloOn O (π μ ν)) : HoloOn O (twistedSymbol π μ ν) := by
  obtain ⟨ho, hc, hd⟩ := h
  have hE : Continuous fun κ : Fin 4 → ℂ => Complex.exp (Complex.I * ((κ μ - κ ν) / 2)) := by
    fun_prop
  refine ⟨ho, hE.continuousOn.mul hc, fun a ha j => ?_⟩
  filter_upwards [hd a ha j] with ζ h
  have hE' : DifferentiableAt ℂ (fun ζ : ℂ => Complex.exp (Complex.I *
      (((a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) μ -
        (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ν) / 2))) ζ := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  exact hE'.mul h
theorem holoOn_comp {O : Set (Fin 4 → ℂ)} {f : (Fin 4 → ℂ) → ℂ} {T : (Fin 4 → ℂ) → Fin 4 → ℂ}
    (h : HoloOn O f) (hT : Continuous T)
    (hl : ∀ (a : Fin 4 → ℂ) (j : Fin 4), ∃ (k : Fin 4) (c : ℂ), ∀ ζ : ℂ,
      T (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) =
        T a + (c * ζ) • Coordinates.ComplexCoordinates.stdBasisVector k) :
    HoloOn (T ⁻¹' O) (fun κ => f (T κ)) := by
  obtain ⟨ho, hc, hd⟩ := h
  refine ⟨ho.preimage hT, hc.comp hT.continuousOn (fun _ h => h), fun a ha j => ?_⟩
  obtain ⟨k, c, hk⟩ := hl a j
  have ht : Tendsto (fun ζ : ℂ => c * ζ) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous fun ζ : ℂ => c * ζ := by fun_prop
    simpa using hcont.tendsto 0
  filter_upwards [ht.eventually (hd (T a) ha k)] with ζ h
  have h2 : DifferentiableAt ℂ (fun ζ : ℂ => c * ζ) ζ := by fun_prop
  have h3 := DifferentiableAt.comp ζ h h2
  simp only [hk]
  exact h3
theorem holoOn_sub_smul {O O' : Set (Fin 4 → ℂ)} {f g : (Fin 4 → ℂ) → ℂ} (s : ℂ)
    (h : HoloOn O f) (h' : HoloOn O' g) : HoloOn (O ∩ O') (fun κ => f κ - s * g κ) := by
  obtain ⟨ho, hc, hd⟩ := h
  obtain ⟨ho', hc', hd'⟩ := h'
  refine ⟨ho.inter ho', (hc.mono inter_subset_left).sub
    (continuousOn_const.mul (hc'.mono inter_subset_right)), fun a ha j => ?_⟩
  filter_upwards [hd a ha.1 j, hd' a ha.2 j] with ζ u v
  exact u.sub (v.const_mul s)
theorem eq_zero_on_imStrip_of_small (hJ : DualLatticeDensity.Claim) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {F : FieldFamily L} {δ : ℝ} {π : SymbolArray}
    {e : ℕ → ℝ} (c : IsTemperedWitness L F δ π e) {G : (Fin 4 → ℂ) → ℂ} {O : Set (Fin 4 → ℂ)}
    (hO : imStrip δ ⊆ O) (hG : HoloOn O G) {N : ℕ} (hN : 1 ≤ N) (hnn : ∀ n, N ≤ n → 0 ≤ e n)
    (hb : ∀ n, N ≤ n → ∀ p ∈ dualLattice (2 * L ^ n), ‖G (toComplexVec p)‖ ≤ 2 * e n) :
    ∀ κ ∈ imStrip δ, G κ = 0 := by
  have hreal : ∀ y, toComplexVec y ∈ imStrip δ := fun y μ => by
    simpa [toComplexVec] using c.delta_pos.le
  have hcv : Continuous toComplexVec :=
    continuous_pi fun μ => Complex.continuous_ofReal.comp (continuous_apply μ)
  have hg : Continuous fun y => G (toComplexVec y) :=
    hG.2.1.comp_continuous hcv fun y => hO (hreal y)
  have hlim : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
    simpa using c.err_tendsto.const_mul 2
  exact ((hJ L hL).2.2 (fun y => G (toComplexVec y)) N (fun n => 2 * e n) hg hN
    (fun n hn => mul_nonneg zero_le_two (hnn n hn)) hlim hb).2 δ G c.delta_pos
    ⟨O, hO, isHolomorphicIn_iff_holoOn.2 hG⟩ (fun _ => rfl)
theorem complexHessian_smul_smul {L n : ℕ} {F : FieldFamily L}
    (P : ComplexHessianOfMember.Properties F n)
    {A B : UnitEdge L n → Matrices.ComplexMatrix2} (hA : A ∈ complexEdgeForms L n 0 0)
    (hB : B ∈ complexEdgeForms L n 0 0) (α β : ℂ) :
    complexHessian F n (α • A) (β • B) = α * β * complexHessian F n A B := by
  have z := (complexEdgeForms L n 0 0).zero_mem
  have zero : ∀ B' ∈ complexEdgeForms L n 0 0, complexHessian F n 0 B' = 0 := by
    intro B' hB'
    have h := P.linear_left 1 0 z 0 z B' hB'
    simpa using h
  have left : ∀ (c : ℂ) (A' B' : UnitEdge L n → Matrices.ComplexMatrix2),
      A' ∈ complexEdgeForms L n 0 0 → B' ∈ complexEdgeForms L n 0 0 →
      complexHessian F n (c • A') B' = c * complexHessian F n A' B' := by
    intro c A' B' hA' hB'
    have h := P.linear_left c A' hA' 0 z B' hB'
    simpa [zero B' hB'] using h
  have hβB := (complexEdgeForms L n 0 0).smul_mem β hB
  rw [left α A _ hA hβB, P.symm A hA _ hβB, left β B A hB hA, P.symm B hB A hA]
  ring
theorem symbol_close_of_motion (hW : PlaneWaveSymmetries.PlaneWaveLawsHold)
    (hI : ComplexHessianInvariance.Statement)
    (hM : ComplexHessianOfMember.Statement) {L n : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {F : FieldFamily L} (hm : IsAdmissibleMember (F n)) {π : SymbolArray} {E : ℝ}
    (hb : ∀ p ∈ dualLattice (2 * L ^ n), ∀ (a a' : Fin 3) (μ ν : Fin 4),
      ‖(((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) *
          complexHessian F n (fourierModeForm L n a p μ) (fourierModeForm L n a' (-p) ν) -
        (if a = a' then π μ ν (toComplexVec p) else 0)‖ ≤ E)
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hf : IsDistancePreserving f)
    (hf' : MapsSublatticeOnto 0 0 f) {p q : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n))
    (hq : q ∈ dualLattice (2 * L ^ n)) {μ ν μ' ν' : Fin 4} {α β : ℂ} (hα : ‖α‖ = 1)
    (hβ : ‖β‖ = 1)
    (h1 : tangentPushforward f (fourierModeForm L n 0 p μ) = α • fourierModeForm L n 0 q μ')
    (h2 : tangentPushforward f (fourierModeForm L n 0 (-p) ν) =
      β • fourierModeForm L n 0 (-q) ν') :
    ‖π μ ν (toComplexVec p) - α * β * π μ' ν' (toComplexVec q)‖ ≤ 2 * E := by
  have W := hW L n hL hn
  have P := hM L n hL hn F hm
  have wp := W.mem_complex 0 μ p hp
  have wp' := W.mem_complex 0 ν (-p) (neg_mem hp)
  have wq := W.mem_complex 0 μ' q hq
  have wq' := W.mem_complex 0 ν' (-q) (neg_mem hq)
  have inv := hI L n hL hn F hm f hf hf' _ wp _ wp'
  have inv' : complexHessian F n (α • fourierModeForm L n 0 q μ')
      (β • fourierModeForm L n 0 (-q) ν') =
      complexHessian F n (fourierModeForm L n 0 p μ) (fourierModeForm L n 0 (-p) ν) := by
    rw [← h1, ← h2]
    exact inv
  rw [complexHessian_smul_smul P wq wq' α β] at inv'
  have b1 := hb p hp 0 0 μ ν
  have b2 := hb q hq 0 0 μ' ν'
  rw [if_pos rfl] at b1 b2
  rw [← inv'] at b1
  have hsplit : π μ ν (toComplexVec p) - α * β * π μ' ν' (toComplexVec q) =
      -((((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) *
          (α * β * complexHessian F n (fourierModeForm L n 0 q μ')
            (fourierModeForm L n 0 (-q) ν')) -
        π μ ν (toComplexVec p)) +
      α * β * ((((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) *
          complexHessian F n (fourierModeForm L n 0 q μ') (fourierModeForm L n 0 (-q) ν') -
        π μ' ν' (toComplexVec q)) := by
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_mul, norm_mul α β, hα, hβ, one_mul, one_mul]
  linarith
theorem norm_twisted_sub_le {a b c s u w : ℂ} {E : ℝ} (hs : ‖s‖ = 1) (hu : ‖u‖ = 1)
    (h : ‖a - c * b‖ ≤ E) (hw : w = s * u * c) : ‖w * b - s * (u * a)‖ ≤ E := by
  have hsplit : w * b - s * (u * a) = -(s * u) * (a - c * b) := by
    rw [hw]
    ring
  rw [hsplit, norm_mul, norm_neg, norm_mul, hs, hu]
  simpa using h
theorem norm_halfPhase (p : AmbientSpace) (μ ν : Fin 4) :
    ‖Complex.exp (Complex.I * ((toComplexVec p μ - toComplexVec p ν) / 2))‖ = 1 := by
  have h : Complex.I * ((toComplexVec p μ - toComplexVec p ν) / 2) =
      (((p μ - p ν) / 2 : ℝ) : ℂ) * Complex.I := by
    simp only [toComplexVec]
    push_cast
    ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _
theorem witness_data {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {F : FieldFamily L}
    {δ : ℝ} {π : SymbolArray} {e : ℕ → ℝ} (hF : IsLatticeFunctional L F)
    (c : IsTemperedWitness L F δ π e) :
    (∃ O : Set (Fin 4 → ℂ), imStrip δ ⊆ O ∧ ∀ μ ν, HoloOn O (twistedSymbol π μ ν)) ∧
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n → 0 ≤ e n ∧ IsAdmissibleMember (F n) ∧
      ∀ p ∈ dualLattice (2 * L ^ n), ∀ (a a' : Fin 3) (μ ν : Fin 4),
        ‖(((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) *
            complexHessian F n (fourierModeForm L n a p μ) (fourierModeForm L n a' (-p) ν) -
          (if a = a' then π μ ν (toComplexVec p) else 0)‖ ≤ e n := by
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  obtain ⟨O, hO, hh⟩ := c.analytic
  refine ⟨⟨O, hO, fun μ ν => holoOn_twistedSymbol (isHolomorphicIn_iff_holoOn.1 (hh μ ν).1)⟩, ?_⟩
  obtain ⟨n₁, h₁, p₁⟩ := eventually_of_eventuallyForSides hL2 c.err_nonneg
  obtain ⟨n₂, -, p₂⟩ := eventually_of_eventuallyForSides hL2 hF
  obtain ⟨n₃, -, p₃⟩ := eventually_of_eventuallyForSides hL2 c.approx
  refine ⟨max n₁ (max n₂ n₃), h₁.trans (le_max_left _ _), fun n hn => ?_⟩
  have a₁ : n₁ ≤ n := (le_max_left _ _).trans hn
  have a₂ : n₂ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have a₃ : n₃ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  exact ⟨p₁ n a₁, p₂ n a₂, p₃ n a₃⟩
theorem comp_perm_mem_dualLattice {s : ℕ} {p : AmbientSpace} (hp : p ∈ dualLattice s)
    (σ : Equiv.Perm (Fin 4)) : p ∘ σ.symm ∈ dualLattice s := by
  obtain ⟨k, hk⟩ := hp
  exact ⟨k ∘ σ.symm, fun μ => hk _⟩
theorem permutationCovariant_of_witness (hJ : DualLatticeDensity.Claim)
    (hT : UnitLatticeMotions.Statement)
    (hW : PlaneWaveSymmetries.PlaneWaveLawsHold)
    (hI : ComplexHessianInvariance.Statement)
    (hM : ComplexHessianOfMember.Statement) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {F : FieldFamily L} {δ : ℝ} {π : SymbolArray} {e : ℕ → ℝ} (hF : IsLatticeFunctional L F)
    (c : IsTemperedWitness L F δ π e) : PermutationCovariant δ π := by
  obtain ⟨⟨O, hO, hol⟩, N, hN, hlarge⟩ := witness_data hL hF c
  intro σ κ hκ μ ν
  have hcont : Continuous fun κ : Fin 4 → ℂ => κ ∘ σ.symm :=
    continuous_pi fun i => continuous_apply (σ.symm i)
  have hline : ∀ (a : Fin 4 → ℂ) (j : Fin 4), ∃ (k : Fin 4) (c : ℂ), ∀ ζ : ℂ,
      (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ∘ σ.symm =
        a ∘ σ.symm + (c * ζ) • Coordinates.ComplexCoordinates.stdBasisVector k := by
    intro a j
    refine ⟨σ j, 1, fun ζ => ?_⟩
    ext i
    simp [Coordinates.ComplexCoordinates.stdBasisVector, Pi.single_apply, Equiv.symm_apply_eq]
  have hG := holoOn_sub_smul 1 (holoOn_comp (hol (σ μ) (σ ν)) hcont hline) (hol μ ν)
  have hsub : imStrip δ ⊆ ((fun κ : Fin 4 → ℂ => κ ∘ σ.symm) ⁻¹' O) ∩ O :=
    fun κ hκ => ⟨hO fun i => hκ (σ.symm i), hO hκ⟩
  have key := eq_zero_on_imStrip_of_small hJ hL c hsub hG hN (fun n hn => (hlarge n hn).1) ?_ κ hκ
  · simpa [sub_eq_zero] using key
  intro n hn p hp
  obtain ⟨-, hm, hb⟩ := hlarge n hn
  have hn0 : 0 < n := lt_of_lt_of_le hN hn
  obtain ⟨f, hind, hf, hf'⟩ :=
    (hT.2.2.2 L n hL hn0) (UnitLatticeMotions.permMatrix σ) (hT.1 σ).1 (hT.1 σ).2 0
  have W := hW L n hL hn0
  have hclose := symbol_close_of_motion hW hI hM hL hn0 hm hb hf hf' hp
    (comp_perm_mem_dualLattice hp σ)
    (μ := μ) (ν := ν) (μ' := σ μ) (ν' := σ ν) (α := 1) (β := 1) norm_one norm_one
    (by rw [one_smul]; exact W.permute f σ hf hf' hind 0 μ p hp)
    (by rw [one_smul]; exact W.permute f σ hf hf' hind 0 ν (-p) (neg_mem hp))
  refine norm_twisted_sub_le
    (u := Complex.exp (Complex.I * ((toComplexVec p μ - toComplexVec p ν) / 2)))
    (c := 1 * 1) norm_one (norm_halfPhase p μ ν) hclose ?_
  simp [toComplexVec]
theorem flipCoord_self (ρ : Fin 4) (p : AmbientSpace) : flipCoord ρ p ρ = -p ρ := by
  simp [flipCoord]
theorem flipCoord_of_ne {ρ μ : Fin 4} (h : μ ≠ ρ) (p : AmbientSpace) :
    flipCoord ρ p μ = p μ := by
  simp [flipCoord, h]
theorem flipCoord_neg (ρ : Fin 4) (p : AmbientSpace) :
    flipCoord ρ (-p) = -flipCoord ρ p := by
  ext μ
  by_cases h : μ = ρ
  · subst h
    simp [flipCoord_self]
  · simp [flipCoord_of_ne h]
theorem toComplexVec_flipCoord (ρ : Fin 4) (p : AmbientSpace) :
    toComplexVec (flipCoord ρ p) = reflectCoord ρ (toComplexVec p) := by
  ext μ
  by_cases h : μ = ρ
  · subst h
    simp [flipCoord_self, reflectCoord, toComplexVec]
  · simp [flipCoord_of_ne h, reflectCoord, toComplexVec, h]
theorem flipCoord_mem_dualLattice {s : ℕ} {p : AmbientSpace} (hp : p ∈ dualLattice s)
    (ρ : Fin 4) : flipCoord ρ p ∈ dualLattice s := by
  obtain ⟨k, hk⟩ := hp
  refine ⟨Function.update k ρ (-k ρ), fun μ => ?_⟩
  by_cases h : μ = ρ
  · subst h
    simp [flipCoord_self, hk]
  · simp [flipCoord_of_ne h, hk, h]
def flipFactor (ρ : Fin 4) (p : AmbientSpace) (μ : Fin 4) : ℂ :=
  if μ = ρ then -Complex.exp (-(Complex.I * (p ρ : ℂ))) else 1
theorem norm_flipFactor (ρ : Fin 4) (p : AmbientSpace) (μ : Fin 4) :
    ‖flipFactor ρ p μ‖ = 1 := by
  unfold flipFactor
  split_ifs
  · have h : -(Complex.I * (p ρ : ℂ)) = ((-p ρ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [norm_neg, h]
    exact Complex.norm_exp_ofReal_mul_I _
  · exact norm_one
theorem norm_reflectSign_mul (ρ μ ν : Fin 4) : ‖reflectSign ρ μ * reflectSign ρ ν‖ = 1 := by
  unfold reflectSign
  split_ifs <;> simp
theorem halfPhase_reflectCoord (ρ μ ν : Fin 4) (p : AmbientSpace) :
    Complex.exp (Complex.I * ((reflectCoord ρ (toComplexVec p) μ -
        reflectCoord ρ (toComplexVec p) ν) / 2)) =
      reflectSign ρ μ * reflectSign ρ ν *
        Complex.exp (Complex.I * ((toComplexVec p μ - toComplexVec p ν) / 2)) *
        (flipFactor ρ p μ * flipFactor ρ (-p) ν) := by
  rw [← toComplexVec_flipCoord]
  by_cases hμ : μ = ρ <;> by_cases hν : ν = ρ
  · subst hμ
    subst hν
    have h : ∀ z : ℂ, (-1 : ℂ) * -1 * z * (-Complex.exp (-(Complex.I * ((p ν : ℝ) : ℂ))) *
        -Complex.exp (-(Complex.I * (((-p) ν : ℝ) : ℂ)))) = z := by
      intro z
      have h2 : Complex.exp (-(Complex.I * ((p ν : ℝ) : ℂ))) *
          Complex.exp (-(Complex.I * (((-p) ν : ℝ) : ℂ))) = 1 := by
        rw [← Complex.exp_add]
        simp
      linear_combination z * h2
    simp only [reflectSign, flipFactor, if_true]
    rw [h]
    simp [toComplexVec]
  · subst hμ
    simp only [reflectSign, flipFactor, if_true, if_neg hν, toComplexVec,
      flipCoord_self, flipCoord_of_ne hν]
    have h : (-1 : ℂ) * 1 * Complex.exp (Complex.I * (((p μ : ℝ) - (p ν : ℝ)) / 2)) *
        (-Complex.exp (-(Complex.I * ((p μ : ℝ) : ℂ))) * 1) =
        Complex.exp (Complex.I * (((p μ : ℝ) - (p ν : ℝ)) / 2)) *
          Complex.exp (-(Complex.I * ((p μ : ℝ) : ℂ))) := by
      ring
    rw [h, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · subst hν
    simp only [reflectSign, flipFactor, if_true, if_neg hμ, toComplexVec,
      flipCoord_self, flipCoord_of_ne hμ]
    have h : (1 : ℂ) * -1 * Complex.exp (Complex.I * (((p μ : ℝ) - (p ν : ℝ)) / 2)) *
        (1 * -Complex.exp (-(Complex.I * (((-p) ν : ℝ) : ℂ)))) =
        Complex.exp (Complex.I * (((p μ : ℝ) - (p ν : ℝ)) / 2)) *
          Complex.exp (-(Complex.I * (((-p) ν : ℝ) : ℂ))) := by
      ring
    rw [h, ← Complex.exp_add]
    congr 1
    simp only [Pi.neg_apply]
    push_cast
    ring
  · simp [reflectSign, flipFactor, hμ, hν, toComplexVec, flipCoord_of_ne hμ,
      flipCoord_of_ne hν]
theorem reflectionCovariant_of_witness (hJ : DualLatticeDensity.Claim)
    (hT : UnitLatticeMotions.Statement)
    (hW : PlaneWaveSymmetries.PlaneWaveLawsHold)
    (hI : ComplexHessianInvariance.Statement)
    (hM : ComplexHessianOfMember.Statement) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {F : FieldFamily L} {δ : ℝ} {π : SymbolArray} {e : ℕ → ℝ} (hF : IsLatticeFunctional L F)
    (c : IsTemperedWitness L F δ π e) : ReflectionCovariant δ π := by
  obtain ⟨⟨O, hO, hol⟩, N, hN, hlarge⟩ := witness_data hL hF c
  intro ρ κ hκ μ ν
  have hcont : Continuous (reflectCoord ρ) :=
    continuous_id.update ρ (continuous_apply ρ).neg
  have hline : ∀ (a : Fin 4 → ℂ) (j : Fin 4), ∃ (k : Fin 4) (c : ℂ), ∀ ζ : ℂ,
      reflectCoord ρ (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) =
        reflectCoord ρ a + (c * ζ) • Coordinates.ComplexCoordinates.stdBasisVector k := by
    intro a j
    refine ⟨j, reflectSign ρ j, fun ζ => ?_⟩
    ext i
    by_cases hi : i = ρ <;> by_cases hj : j = ρ <;> by_cases hij : i = j <;>
      simp_all [reflectCoord, reflectSign, Coordinates.ComplexCoordinates.stdBasisVector,
        Function.update_apply]
    all_goals ring
  have hG := holoOn_sub_smul (reflectSign ρ μ * reflectSign ρ ν)
    (holoOn_comp (hol μ ν) hcont hline) (hol μ ν)
  have hsub : imStrip δ ⊆ (reflectCoord ρ ⁻¹' O) ∩ O := by
    refine fun κ hκ => ⟨hO fun i => ?_, hO hκ⟩
    by_cases hi : i = ρ
    · subst hi
      simpa [reflectCoord] using hκ i
    · simpa [reflectCoord, hi] using hκ i
  have key := eq_zero_on_imStrip_of_small hJ hL c hsub hG hN (fun n hn => (hlarge n hn).1) ?_ κ hκ
  · exact sub_eq_zero.1 key
  intro n hn p hp
  obtain ⟨-, hm, hb⟩ := hlarge n hn
  have hn0 : 0 < n := lt_of_lt_of_le hN hn
  obtain ⟨f, hind, hf, hf'⟩ :=
    (hT.2.2.2 L n hL hn0) (UnitLatticeMotions.axisReflectionMatrix ρ) (hT.2.1 ρ).1
      (hT.2.1 ρ).2 0
  have W := hW L n hL hn0
  have moved_wave : ∀ (q : AmbientSpace), q ∈ dualLattice (2 * L ^ n) → ∀ τ : Fin 4,
      tangentPushforward f (fourierModeForm L n 0 q τ) =
        flipFactor ρ q τ • fourierModeForm L n 0 (flipCoord ρ q) τ := by
    intro q hq τ
    by_cases hτ : τ = ρ
    · subst hτ
      simpa [flipFactor] using W.reflect_on_axis f τ hf hf' hind 0 q hq
    · simpa [flipFactor, hτ] using W.reflect_off_axis f ρ hf hf' hind 0 τ hτ q hq
  have hclose := symbol_close_of_motion hW hI hM hL hn0 hm hb hf hf' hp
    (flipCoord_mem_dualLattice hp ρ)
    (μ := μ) (ν := ν) (μ' := μ) (ν' := ν) (norm_flipFactor ρ p μ)
    (norm_flipFactor ρ (-p) ν) (moved_wave p hp μ)
    (by rw [← flipCoord_neg]; exact moved_wave (-p) (neg_mem hp) ν)
  rw [toComplexVec_flipCoord] at hclose
  exact norm_twisted_sub_le (norm_reflectSign_mul ρ μ ν) (norm_halfPhase p μ ν) hclose
    (halfPhase_reflectCoord ρ μ ν p)
theorem symbolCovarianceClaim_holds (h₁ : DualLatticeDensity.Claim)
    (h₂ : UnitLatticeMotions.Statement)
    (h₃ : PlaneWaveSymmetries.PlaneWaveLawsHold)
    (h₄ : ComplexHessianInvariance.Statement)
    (h₅ : ComplexHessianOfMember.Statement) : SymbolCovarianceClaim := by
  intro L hL F δ π e hF c
  exact ⟨permutationCovariant_of_witness h₁ h₂ h₃ h₄ h₅ hL hF c,
    reflectionCovariant_of_witness h₁ h₂ h₃ h₄ h₅ hL hF c⟩
end YangMills.Construction.OneLoopLaw.SymbolCovariance
end
