import YangMills.Construction.EnergyMomentum.JointSpectralMeasureExistence
import YangMills.Construction.HilbertSpace.BoundedSesqFormRepresentation
import YangMills.Construction.SpectralCalculus.FormCompletionAndBoundedExtension
import YangMills.Construction.SpectralCalculus.JointSpectralMeasure
import YangMills.Construction.SpectralCalculus.VectorSpectralMeasure
import YangMills.Construction.TwoPoints.ComplexMeasureDeterminedByItsTransform
import YangMills.Construction.TwoPoints.SmearedGroupAndTheTwoBounds
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ComplexOrder NNReal ENNReal
noncomputable section
namespace YangMills.Construction.SpectralCalculus.JointSpectralProof
section Calculus
variable {α : Type*} [MeasurableSpace α]
theorem integrable_of_isBoundedMeasurable {F : α → ℂ} (hF : IsBoundedMeasurable F)
    (μ : ComplexMeasure α) : μ.Integrable F := by
  obtain ⟨hm, C, hC⟩ := hF
  exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)
theorem isBoundedMeasurable_mul {F G : α → ℂ} (hF : IsBoundedMeasurable F)
    (hG : IsBoundedMeasurable G) : IsBoundedMeasurable (F * G) := by
  obtain ⟨hm, C, hC⟩ := hF
  obtain ⟨hm', C', hC'⟩ := hG
  refine ⟨hm.mul hm', C * C', fun x => ?_⟩
  have h0 : 0 ≤ C := (norm_nonneg _).trans (hC x)
  simpa using mul_le_mul (hC x) (hC' x) (norm_nonneg _) h0
theorem isBoundedMeasurable_simpleFunc (f : SimpleFunc α ℂ) : IsBoundedMeasurable f :=
  ⟨f.measurable, f.exists_forall_norm_le⟩
structure IsBoundedlyContinuousAdditive (Ψ : (α → ℂ) → ℂ) : Prop where
  add : ∀ f g, IsBoundedMeasurable f → IsBoundedMeasurable g → Ψ (f + g) = Ψ f + Ψ g
  lim : ∀ (f : ℕ → α → ℂ) (F : α → ℂ) (C : ℝ), (∀ n, Measurable (f n)) → Measurable F →
    (∀ n x, ‖f n x‖ ≤ C) → (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x))) →
    Tendsto (fun n => Ψ (f n)) atTop (𝓝 (Ψ F))
theorem IsBoundedlyContinuousAdditive.eq_of_indicator {Ψ Ψ' : (α → ℂ) → ℂ}
    (h : IsBoundedlyContinuousAdditive Ψ) (h' : IsBoundedlyContinuousAdditive Ψ')
    (hind : ∀ A, MeasurableSet A → ∀ c : ℂ,
      Ψ (A.indicator fun _ => c) = Ψ' (A.indicator fun _ => c))
    {F : α → ℂ} (hF : IsBoundedMeasurable F) : Ψ F = Ψ' F := by
  have hs : ∀ f : SimpleFunc α ℂ, Ψ f = Ψ' f := by
    intro f
    induction f using SimpleFunc.induction with
    | @const c s hs =>
      have e : ((SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const α 0) :
          SimpleFunc α ℂ) : α → ℂ) = s.indicator fun _ => c := by
        funext x
        by_cases hx : x ∈ s <;> simp [hx]
      rw [e]
      exact hind s hs c
    | add hd h1 h2 =>
      rw [SimpleFunc.coe_add,
        h.add _ _ (isBoundedMeasurable_simpleFunc _) (isBoundedMeasurable_simpleFunc _),
        h'.add _ _ (isBoundedMeasurable_simpleFunc _) (isBoundedMeasurable_simpleFunc _), h1, h2]
  obtain ⟨hm, C, hC⟩ := hF
  have hC0 : ∀ x : α, 0 ≤ C := fun x => (norm_nonneg _).trans (hC x)
  by_cases hα : Nonempty α
  · obtain ⟨x₀⟩ := hα
    have hsm := hm.stronglyMeasurable
    have hb : ∀ n x, ‖hsm.approxBounded C n x‖ ≤ C := fun n x =>
      hsm.norm_approxBounded_le (hC0 x₀) n x
    have hl : ∀ x, Tendsto (fun n => hsm.approxBounded C n x) atTop (𝓝 (F x)) := fun x =>
      hsm.tendsto_approxBounded_of_norm_le (hC x)
    have t₁ := h.lim (fun n => hsm.approxBounded C n) F C
      (fun n => (hsm.approxBounded C n).measurable) hm hb hl
    have t₂ := h'.lim (fun n => hsm.approxBounded C n) F C
      (fun n => (hsm.approxBounded C n).measurable) hm hb hl
    exact tendsto_nhds_unique t₁ (t₂.congr fun n => (hs _).symm)
  · have hα' : IsEmpty α := not_nonempty_iff.mp hα
    have e : F = ((SimpleFunc.const α (0 : ℂ) : SimpleFunc α ℂ) : α → ℂ) :=
      funext fun x => (hα'.false x).elim
    rw [e]
    exact hs _
theorem isBoundedlyContinuousAdditive_complexIntegral (μ : ComplexMeasure α) :
    IsBoundedlyContinuousAdditive (complexIntegral μ) where
  add _ _ hf hg := VectorMeasure.integral_add (integrable_of_isBoundedMeasurable hf μ)
    (integrable_of_isBoundedMeasurable hg μ)
  lim _ _ C hf _ hb hl := VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (hf n).aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall (hb n)) (Eventually.of_forall hl)
theorem isBoundedlyContinuousAdditive_integral (m : Measure α) [IsFiniteMeasure m] :
    IsBoundedlyContinuousAdditive fun F : α → ℂ => ∫ x, F x ∂m where
  add f g hf hg := by
    obtain ⟨hm, C, hC⟩ := hf
    obtain ⟨hm', C', hC'⟩ := hg
    exact integral_add (Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC))
      (Integrable.of_bound hm'.aestronglyMeasurable C' (Eventually.of_forall hC'))
  lim f F C hf _ hb hl := tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (hf n).aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall (hb n)) (Eventually.of_forall hl)
theorem IsBoundedlyContinuousAdditive.const_mul {Ψ : (α → ℂ) → ℂ}
    (h : IsBoundedlyContinuousAdditive Ψ) (c : ℂ) :
    IsBoundedlyContinuousAdditive fun F => c * Ψ F where
  add f g hf hg := by rw [h.add f g hf hg, mul_add]
  lim f F C hf hF hb hl := (h.lim f F C hf hF hb hl).const_mul c
theorem IsBoundedlyContinuousAdditive.comp_mul {Ψ : (α → ℂ) → ℂ}
    (h : IsBoundedlyContinuousAdditive Ψ) {G : α → ℂ} (hG : IsBoundedMeasurable G) :
    IsBoundedlyContinuousAdditive fun F => Ψ (G * F) where
  add f g hf hg := by
    rw [mul_add, h.add _ _ (isBoundedMeasurable_mul hG hf) (isBoundedMeasurable_mul hG hg)]
  lim f F C hf hF hb hl := by
    obtain ⟨hm, C', hC'⟩ := hG
    refine h.lim (fun n => G * f n) (G * F) (C' * C) (fun n => hm.mul (hf n)) (hm.mul hF)
      (fun n x => ?_) (fun x => (hl x).const_mul (G x))
    have h0 : 0 ≤ C' := (norm_nonneg _).trans (hC' x)
    simpa using mul_le_mul (hC' x) (hb n x) (norm_nonneg _) h0
theorem IsBoundedlyContinuousAdditive.conj {Ψ : (α → ℂ) → ℂ}
    (h : IsBoundedlyContinuousAdditive Ψ) :
    IsBoundedlyContinuousAdditive fun F => (starRingEnd ℂ) (Ψ fun x => (starRingEnd ℂ) (F x)) where
  add f g hf hg := by
    have e : (fun x => (starRingEnd ℂ) ((f + g) x)) =
        (fun x => (starRingEnd ℂ) (f x)) + fun x => (starRingEnd ℂ) (g x) := by
      funext x
      simp
    obtain ⟨hm, C, hC⟩ := hf
    obtain ⟨hm', C', hC'⟩ := hg
    rw [e, h.add (fun x => (starRingEnd ℂ) (f x)) (fun x => (starRingEnd ℂ) (g x))
      ⟨Complex.continuous_conj.measurable.comp hm, C, by simpa using hC⟩
      ⟨Complex.continuous_conj.measurable.comp hm', C', by simpa using hC'⟩, map_add]
  lim f F C hf hF hb hl := by
    refine (Complex.continuous_conj.tendsto _).comp (h.lim (fun n x => (starRingEnd ℂ) (f n x))
      (fun x => (starRingEnd ℂ) (F x)) C (fun n => Complex.continuous_conj.measurable.comp (hf n))
      (Complex.continuous_conj.measurable.comp hF) (fun n x => by simpa using hb n x)
      (fun x => (Complex.continuous_conj.tendsto _).comp (hl x)))
theorem complexIntegral_indicator_const (μ : ComplexMeasure α) {A : Set α} (hA : MeasurableSet A)
    (c : ℂ) : complexIntegral μ (A.indicator fun _ => c) = c * μ A :=
  VectorMeasure.integral_indicator_const c hA
theorem complexIntegral_const_mul (μ : ComplexMeasure α) (c : ℂ) {F : α → ℂ}
    (hF : IsBoundedMeasurable F) :
    complexIntegral μ ((fun _ => c) * F) = c * complexIntegral μ F := by
  have hc : IsBoundedMeasurable (fun _ => c : α → ℂ) := ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩
  refine ((isBoundedlyContinuousAdditive_complexIntegral μ).comp_mul hc).eq_of_indicator
    ((isBoundedlyContinuousAdditive_complexIntegral μ).const_mul c) (fun A hA d => ?_) hF
  have e : (fun _ => c : α → ℂ) * (A.indicator fun _ => d) = A.indicator fun _ => c * d := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  simp only [e, complexIntegral_indicator_const μ hA]
  ring
theorem complexIntegral_smul_measure (a : ℂ) (μ : ComplexMeasure α) {F : α → ℂ}
    (hF : IsBoundedMeasurable F) : complexIntegral (a • μ) F = a * complexIntegral μ F := by
  refine (isBoundedlyContinuousAdditive_complexIntegral (a • μ)).eq_of_indicator
    ((isBoundedlyContinuousAdditive_complexIntegral μ).const_mul a) (fun A hA d => ?_) hF
  simp only [complexIntegral_indicator_const _ hA, smul_apply, smul_eq_mul]
  ring
theorem complexIntegral_add_measure (μ ν : ComplexMeasure α) {F : α → ℂ}
    (hF : IsBoundedMeasurable F) :
    complexIntegral (μ + ν) F = complexIntegral μ F + complexIntegral ν F :=
  VectorMeasure.integral_add_vectorMeasure (integrable_of_isBoundedMeasurable hF μ)
    (integrable_of_isBoundedMeasurable hF ν)
theorem complexIntegral_conjMeasure (μ : ComplexMeasure α) {F : α → ℂ}
    (hF : IsBoundedMeasurable F) : complexIntegral (conjMeasure μ) F =
      (starRingEnd ℂ) (complexIntegral μ fun x => (starRingEnd ℂ) (F x)) := by
  refine (isBoundedlyContinuousAdditive_complexIntegral (conjMeasure μ)).eq_of_indicator
    (isBoundedlyContinuousAdditive_complexIntegral μ).conj (fun A hA d => ?_) hF
  have e : (fun x => (starRingEnd ℂ) (A.indicator (fun _ => d) x)) =
      A.indicator fun _ => (starRingEnd ℂ) d := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  simp only [e, complexIntegral_indicator_const _ hA, conjMeasure_apply, map_mul,
    Complex.conj_conj]
theorem complexIntegral_withDensityComplex (μ : ComplexMeasure α) {G F : α → ℂ}
    (hG : IsBoundedMeasurable G) (hF : IsBoundedMeasurable F) :
    complexIntegral (withDensityComplex G μ) F = complexIntegral μ (G * F) := by
  refine (isBoundedlyContinuousAdditive_complexIntegral (withDensityComplex G μ)).eq_of_indicator
    ((isBoundedlyContinuousAdditive_complexIntegral μ).comp_mul hG) (fun A hA d => ?_) hF
  have e : G * (A.indicator fun _ => d) = A.indicator ((fun _ => d) * G) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx, mul_comm]
  simp only [e]
  rw [complexIntegral_indicator_const _ hA, withDensityComplex_apply hG]
  unfold complexIntegral
  rw [VectorMeasure.integral_indicator hA]
  exact (complexIntegral_const_mul (μ.restrict A) d hG).symm
def ofFiniteMeasure (m : Measure α) : ComplexMeasure α := m.withDensityᵥ fun _ => (1 : ℂ)
theorem ofFiniteMeasure_apply (m : Measure α) [IsFiniteMeasure m] {A : Set α}
    (hA : MeasurableSet A) : ofFiniteMeasure m A = (m.real A : ℂ) := by
  rw [ofFiniteMeasure, withDensityᵥ_apply (integrable_const _) hA]
  simp
theorem complexIntegral_ofFiniteMeasure (m : Measure α) [IsFiniteMeasure m] {F : α → ℂ}
    (hF : IsBoundedMeasurable F) : complexIntegral (ofFiniteMeasure m) F = ∫ x, F x ∂m := by
  refine (isBoundedlyContinuousAdditive_complexIntegral (ofFiniteMeasure m)).eq_of_indicator
    (isBoundedlyContinuousAdditive_integral m) (fun A hA d => ?_) hF
  rw [complexIntegral_indicator_const _ hA, ofFiniteMeasure_apply m hA,
    integral_indicator_const d hA]
  simp [mul_comm]
end Calculus
section Transforms
theorem isBoundedMeasurable_spectralCharacter (t : ℝ≥0) (s : ℝ) :
    IsBoundedMeasurable (spectralCharacter t s) := by apply _root_.YangMills.Construction.EnergyMomentum.JointSpectral.Existence.isBoundedMeasurable_laplaceFourierExpLine <;> assumption
theorem spectralCharacter_mul (t t' : ℝ≥0) (s s' : ℝ) :
    spectralCharacter t s * spectralCharacter t' s' = spectralCharacter (t + t') (s + s') := by
  funext p
  simp only [Pi.mul_apply, spectralCharacter, ← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem spectralCharacter_zero : spectralCharacter 0 0 = fun _ => 1 := by
  funext p
  simp [spectralCharacter]
theorem conj_spectralCharacter (t : ℝ≥0) (s : ℝ) :
    (fun p => (starRingEnd ℂ) (spectralCharacter t s p)) = spectralCharacter t (-s) := by
  funext p
  simp only [spectralCharacter, ← Complex.exp_conj, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1
  push_cast
  ring
theorem laplaceFourier_add (μ ν : ComplexMeasure SpectralPlane) (t : ℝ≥0) (s : ℝ) :
    laplaceFourier (μ + ν) t s = laplaceFourier μ t s + laplaceFourier ν t s :=
  complexIntegral_add_measure μ ν (isBoundedMeasurable_spectralCharacter t s)
theorem laplaceFourier_smul (a : ℂ) (μ : ComplexMeasure SpectralPlane) (t : ℝ≥0) (s : ℝ) :
    laplaceFourier (a • μ) t s = a * laplaceFourier μ t s :=
  complexIntegral_smul_measure a μ (isBoundedMeasurable_spectralCharacter t s)
theorem laplaceFourier_ofFiniteMeasure (m : Measure SpectralPlane) [IsFiniteMeasure m] (t : ℝ≥0)
    (s : ℝ) : laplaceFourier (ofFiniteMeasure m) t s = ∫ p, spectralCharacter t s p ∂m :=
  complexIntegral_ofFiniteMeasure m (isBoundedMeasurable_spectralCharacter t s)
theorem laplaceFourier_conjMeasure (μ : ComplexMeasure SpectralPlane) (t : ℝ≥0) (s : ℝ) :
    laplaceFourier (conjMeasure μ) t s = (starRingEnd ℂ) (laplaceFourier μ t (-s)) := by
  rw [laplaceFourier, complexIntegral_conjMeasure μ (isBoundedMeasurable_spectralCharacter t s),
    conj_spectralCharacter]
  rfl
theorem laplaceFourier_withDensityComplex (μ : ComplexMeasure SpectralPlane) (t t' : ℝ≥0)
    (s s' : ℝ) : laplaceFourier (withDensityComplex (spectralCharacter t s) μ) t' s' =
      laplaceFourier μ (t + t') (s + s') := by
  rw [laplaceFourier, complexIntegral_withDensityComplex μ
    (isBoundedMeasurable_spectralCharacter t s) (isBoundedMeasurable_spectralCharacter t' s'),
    spectralCharacter_mul]
  rfl
theorem laplaceFourier_zero_zero (μ : ComplexMeasure SpectralPlane) :
    laplaceFourier μ 0 0 = μ univ := by
  rw [laplaceFourier, spectralCharacter_zero]
  simp [complexIntegral]
end Transforms
theorem inner_apply_eq_polarization {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (u v : H) :
    inner ℂ u (A v) = (1 / 4 : ℂ) * inner ℂ (u + v) (A (u + v)) +
      (Complex.I / 4) * inner ℂ (Complex.I • u + v) (A (Complex.I • u + v)) +
      (-1 / 4 : ℂ) * inner ℂ ((-1 : ℂ) • u + v) (A ((-1 : ℂ) • u + v)) +
      (-Complex.I / 4) * inner ℂ ((-Complex.I) • u + v) (A ((-Complex.I) • u + v)) := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    map_neg, Complex.conj_I, map_one]
  linear_combination ((inner ℂ u (A v) - inner ℂ v (A u)) / 2) * Complex.I_sq
section Pair
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {T : ℝ≥0 → H →L[ℂ] H} {U : ℝ → H →L[ℂ] H}
structure PairHypotheses (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H) : Prop where
  pair : IsCommutingSemigroupGroup T U
  positive : ∀ v : H, ∃ m : Measure SpectralPlane, IsFiniteMeasure m ∧ m.real univ = ‖v‖ ^ 2 ∧
    ∀ (t : ℝ≥0) (s : ℝ), inner ℂ v (T t (U s v)) = ∫ p, spectralCharacter t s p ∂m
  unique : ∀ μ ν : ComplexMeasure SpectralPlane,
    (∀ (t : ℝ≥0) (s : ℝ), laplaceFourier μ t s = laplaceFourier ν t s) → μ = ν
  group : ∀ (u v : H) (s : ℝ), inner ℂ (U s u) v = inner ℂ u (U (-s) v)
  cauchySchwarz : ∀ b : H → H → ℂ, IsPosHermitianForm b →
    ∀ f g, ‖b f g‖ ≤ formSeminorm b f * formSeminorm b g
  riesz : HilbertSpace.BoundedSesqRep.Claim
namespace PairHypotheses
theorem exists_hasSpectralTransform (h : PairHypotheses T U) (u v : H) :
    ∃ μ, HasSpectralTransform T U u v μ := by
  have key : ∀ w : H, ∃ ν : ComplexMeasure SpectralPlane, ∀ (t : ℝ≥0) (s : ℝ),
      inner ℂ w (T t (U s w)) = laplaceFourier ν t s := fun w => by
    obtain ⟨m, hf, -, hm⟩ := h.positive w
    exact ⟨ofFiniteMeasure m, fun t s => by rw [hm, laplaceFourier_ofFiniteMeasure]⟩
  choose ν hν using key
  refine ⟨(1 / 4 : ℂ) • ν (u + v) + (Complex.I / 4) • ν (Complex.I • u + v) +
    (-1 / 4 : ℂ) • ν ((-1 : ℂ) • u + v) + (-Complex.I / 4) • ν ((-Complex.I) • u + v),
    fun t s => ?_⟩
  simp only [laplaceFourier_add, laplaceFourier_smul, ← hν]
  exact inner_apply_eq_polarization (T t * U s) u v
theorem transform_spec (h : PairHypotheses T U) (u v : H) :
    HasSpectralTransform T U u v (pairSpectralMeasure T U u v) :=
  Classical.epsilon_spec (h.exists_hasSpectralTransform u v)
theorem eq_of_hasSpectralTransform (h : PairHypotheses T U) {u v : H}
    {μ : ComplexMeasure SpectralPlane} (hμ : HasSpectralTransform T U u v μ) :
    μ = pairSpectralMeasure T U u v :=
  h.unique _ _ fun t s => by rw [← hμ t s, ← h.transform_spec u v t s]
theorem add_left (h : PairHypotheses T U) (u₁ u₂ v : H) : pairSpectralMeasure T U (u₁ + u₂) v =
    pairSpectralMeasure T U u₁ v + pairSpectralMeasure T U u₂ v :=
  (h.eq_of_hasSpectralTransform fun t s => by
    rw [laplaceFourier_add, ← h.transform_spec, ← h.transform_spec, inner_add_left]).symm
theorem smul_left (h : PairHypotheses T U) (a : ℂ) (u v : H) :
    pairSpectralMeasure T U (a • u) v = (starRingEnd ℂ) a • pairSpectralMeasure T U u v :=
  (h.eq_of_hasSpectralTransform fun t s => by
    rw [laplaceFourier_smul, ← h.transform_spec, inner_smul_left]).symm
theorem add_right (h : PairHypotheses T U) (u v₁ v₂ : H) : pairSpectralMeasure T U u (v₁ + v₂) =
    pairSpectralMeasure T U u v₁ + pairSpectralMeasure T U u v₂ :=
  (h.eq_of_hasSpectralTransform fun t s => by
    rw [laplaceFourier_add, ← h.transform_spec, ← h.transform_spec, map_add, map_add,
      inner_add_right]).symm
theorem smul_right (h : PairHypotheses T U) (a : ℂ) (u v : H) :
    pairSpectralMeasure T U u (a • v) = a • pairSpectralMeasure T U u v :=
  (h.eq_of_hasSpectralTransform fun t s => by
    rw [laplaceFourier_smul, ← h.transform_spec, map_smul, map_smul, inner_smul_right]).symm
theorem commute_apply (h : PairHypotheses T U) (t : ℝ≥0) (s : ℝ) (x : H) :
    T t (U s x) = U s (T t x) :=
  DFunLike.congr_fun (h.pair.commute t s).eq x
theorem semigroup_apply (h : PairHypotheses T U) (t t' : ℝ≥0) (x : H) :
    T t (T t' x) = T (t + t') x :=
  DFunLike.congr_fun (h.pair.semigroup.map_add t t') x
theorem group_apply (h : PairHypotheses T U) (s s' : ℝ) (x : H) : U s (U s' x) = U (s + s') x :=
  DFunLike.congr_fun (h.pair.group.map_add s s') x
theorem inner_semigroup_symm (h : PairHypotheses T U) (t : ℝ≥0) (u v : H) :
    inner ℂ (T t u) v = inner ℂ u (T t v) :=
  h.pair.semigroup.isSymmetricBounded t u v
theorem conj_symm (h : PairHypotheses T U) (u v : H) : pairSpectralMeasure T U v u =
    conjMeasure (pairSpectralMeasure T U u v) :=
  (h.eq_of_hasSpectralTransform fun t s => by
    rw [laplaceFourier_conjMeasure, ← h.transform_spec u v t (-s), inner_conj_symm,
      h.inner_semigroup_symm, h.group, neg_neg, h.commute_apply]).symm
theorem exists_finiteMeasure_self (h : PairHypotheses T U) (v : H) :
    ∃ m : Measure SpectralPlane, IsFiniteMeasure m ∧ m.real univ = ‖v‖ ^ 2 ∧
      ∀ B, MeasurableSet B → pairSpectralMeasure T U v v B = (m.real B : ℂ) := by
  obtain ⟨m, hf, hmass, hm⟩ := h.positive v
  have e : ofFiniteMeasure m = pairSpectralMeasure T U v v :=
    h.eq_of_hasSpectralTransform fun t s => by rw [hm, laplaceFourier_ofFiniteMeasure]
  exact ⟨m, hf, hmass, fun B hB => by rw [← e, ofFiniteMeasure_apply m hB]⟩
theorem nonneg (h : PairHypotheses T U) (v : H) (B : MeasurableSubtype SpectralPlane) :
    0 ≤ pairSpectralMeasure T U v v B.1 := by
  obtain ⟨m, hf, -, hm⟩ := h.exists_finiteMeasure_self v
  rw [hm _ B.2]
  exact Complex.zero_le_real.mpr measureReal_nonneg
theorem mass (h : PairHypotheses T U) (v : H) :
    pairSpectralMeasure T U v v univ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨m, hf, hmass, hm⟩ := h.exists_finiteMeasure_self v
  rw [hm _ MeasurableSet.univ, hmass]
theorem isPosHermitianForm (h : PairHypotheses T U) (B : MeasurableSubtype SpectralPlane) :
    IsPosHermitianForm fun u v => pairSpectralMeasure T U u v B.1 where
  add_left u₁ u₂ v := by rw [h.add_left]; rfl
  smul_left a u v := by rw [h.smul_left]; rfl
  add_right u v₁ v₂ := by rw [h.add_right]; rfl
  smul_right a u v := by rw [h.smul_right]; rfl
  conj_symm u v := by rw [h.conj_symm u v]; rfl
  nonneg v := h.nonneg v B
theorem norm_sq_le (h : PairHypotheses T U) (u v : H) (B : MeasurableSubtype SpectralPlane) :
    ‖pairSpectralMeasure T U u v B.1‖ ^ 2 ≤
      (pairSpectralMeasure T U u u B.1).re * (pairSpectralMeasure T U v v B.1).re := by
  have hx : 0 ≤ (pairSpectralMeasure T U u u B.1).re := (Complex.le_def.mp (h.nonneg u B)).1
  have hy : 0 ≤ (pairSpectralMeasure T U v v B.1).re := (Complex.le_def.mp (h.nonneg v B)).1
  have hcs := h.cauchySchwarz _ (h.isPosHermitianForm B) u v
  calc ‖pairSpectralMeasure T U u v B.1‖ ^ 2
      ≤ (Real.sqrt (pairSpectralMeasure T U u u B.1).re *
          Real.sqrt (pairSpectralMeasure T U v v B.1).re) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hcs 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]
theorem zero_left (h : PairHypotheses T U) (v : H) : pairSpectralMeasure T U 0 v = 0 := by
  have := h.add_left 0 0 v
  rw [add_zero] at this
  exact left_eq_add.mp this
theorem zero_right (h : PairHypotheses T U) (u : H) : pairSpectralMeasure T U u 0 = 0 := by
  have := h.add_right u 0 0
  rw [add_zero] at this
  exact left_eq_add.mp this
theorem variation_le (h : PairHypotheses T U) (u v : H) :
    (pairSpectralMeasure T U u v).variation.real univ ≤ ‖u‖ * ‖v‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [h.zero_left]
  rcases eq_or_ne v 0 with rfl | hv
  · simp [h.zero_right]
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨mu, hfu, hmu, hu'⟩ := h.exists_finiteMeasure_self u
  obtain ⟨mv, hfv, hmv, hv'⟩ := h.exists_finiteMeasure_self v
  set r : ℝ := ‖v‖ / ‖u‖ with hr
  have hr0 : 0 < r := div_pos hvn hun
  have hle : (pairSpectralMeasure T U u v).variation ≤
      ENNReal.ofReal (r / 2) • mu + ENNReal.ofReal (1 / (2 * r)) • mv := by
    refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
    have hsq := h.norm_sq_le u v ⟨E, hE⟩
    simp only [hu' E hE, hv' E hE, Complex.ofReal_re] at hsq
    set x := mu.real E
    set y := mv.real E
    have hx : 0 ≤ x := measureReal_nonneg
    have hy : 0 ≤ y := measureReal_nonneg
    have ha : 0 ≤ r / 2 * x := by positivity
    have hb : 0 ≤ 1 / (2 * r) * y := by positivity
    have hab : 4 * (r / 2 * x * (1 / (2 * r) * y)) = x * y := by
      field_simp
      ring
    have key : ‖pairSpectralMeasure T U u v E‖ ≤ r / 2 * x + 1 / (2 * r) * y := by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (add_nonneg ha hb) two_ne_zero).mp ?_
      nlinarith [sq_nonneg (r / 2 * x - 1 / (2 * r) * y)]
    calc ‖pairSpectralMeasure T U u v E‖ₑ
        = ENNReal.ofReal ‖pairSpectralMeasure T U u v E‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (r / 2 * x + 1 / (2 * r) * y) := ENNReal.ofReal_le_ofReal key
      _ = (ENNReal.ofReal (r / 2) • mu + ENNReal.ofReal (1 / (2 * r)) • mv) E := by
        rw [ENNReal.ofReal_add ha hb, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ofReal_measureReal, ofReal_measureReal]
        simp
  have hmass : (ENNReal.ofReal (r / 2) • mu + ENNReal.ofReal (1 / (2 * r)) • mv) univ =
      ENNReal.ofReal (‖u‖ * ‖v‖) := by
    have e : r / 2 * ‖u‖ ^ 2 + 1 / (2 * r) * ‖v‖ ^ 2 = ‖u‖ * ‖v‖ := by
      rw [hr]
      field_simp
      ring
    rw [← e, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ← hmu, ← hmv,
      ofReal_measureReal, ofReal_measureReal]
    simp
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) ((hle univ).trans hmass.le)
theorem pair_apply (h : PairHypotheses T U) (t t' : ℝ≥0) (s s' : ℝ) (x : H) :
    T t (U s (T t' (U s' x))) = T (t + t') (U (s + s') x) := by
  rw [← h.commute_apply t' s, h.semigroup_apply, h.group_apply]
theorem right_eq_density (h : PairHypotheses T U) (u v : H) (t : ℝ≥0) (s : ℝ) :
    pairSpectralMeasure T U u (T t (U s v)) =
      withDensityComplex (spectralCharacter t s) (pairSpectralMeasure T U u v) :=
  (h.eq_of_hasSpectralTransform fun t' s' => by
    rw [laplaceFourier_withDensityComplex, ← h.transform_spec u v, h.pair_apply, add_comm t',
      add_comm s']).symm
theorem expNegTwoMul_eq (t : ℝ≥0) : expNegTwoMul t = spectralCharacter (2 * t) 0 := by
  funext p
  simp [expNegTwoMul, spectralCharacter]
theorem both_eq_density (h : PairHypotheses T U) (v : H) (t : ℝ≥0) :
    pairSpectralMeasure T U (T t v) (T t v) =
      withDensityComplex (expNegTwoMul t) (pairSpectralMeasure T U v v) :=
  (h.eq_of_hasSpectralTransform fun t' s' => by
    have e : t + (t' + t) = 2 * t + t' := by ring
    rw [expNegTwoMul_eq, laplaceFourier_withDensityComplex, ← h.transform_spec v v,
      h.inner_semigroup_symm, ← h.commute_apply t s' v, h.semigroup_apply t' t,
      h.semigroup_apply t, zero_add, e]).symm
theorem norm_apply_le (h : PairHypotheses T U) (u v : H) (B : Set SpectralPlane) :
    ‖pairSpectralMeasure T U u v B‖ ≤ ‖u‖ * ‖v‖ :=
  (VectorMeasure.norm_measure_le_variation (hE := measure_ne_top _ _)).trans
    ((measureReal_mono (subset_univ _)).trans (h.variation_le u v))
theorem exists_symmetric_operator (h : PairHypotheses T U) (B : MeasurableSubtype SpectralPlane) :
    ∃ P : H →L[ℂ] H, (∀ u v, inner ℂ u (P v) = pairSpectralMeasure T U u v B.1) ∧
      IsSymmetricBounded P := by
  have hf := h.isPosHermitianForm B
  obtain ⟨P, h₁, -, -, h₄⟩ := h.riesz H 1 (fun u v => pairSpectralMeasure T U u v B.1)
    zero_le_one ⟨hf.add_left, hf.smul_left, hf.add_right, hf.smul_right⟩
    (fun u v => by simpa using h.norm_apply_le u v B.1)
  exact ⟨P, h₁, h₄ hf.conj_symm⟩
theorem measure_apply_left_eq_restrict (h : PairHypotheses T U)
    {B : MeasurableSubtype SpectralPlane} {P : H →L[ℂ] H}
    (hP : ∀ u v, inner ℂ u (P v) = pairSpectralMeasure T U u v B.1)
    (hs : IsSymmetricBounded P) (u v : H) :
    pairSpectralMeasure T U (P u) v = (pairSpectralMeasure T U u v).restrict B.1 :=
  (h.eq_of_hasSpectralTransform fun t s => by
    rw [hs, hP, h.right_eq_density, withDensityComplex_apply (isBoundedMeasurable_spectralCharacter t s)]
    rfl).symm
theorem exists_pvm (h : PairHypotheses T U) : ∃ P : ProjValuedMeasure H,
    ∀ u v (B : MeasurableSubtype SpectralPlane),
      inner ℂ u (P B v) = pairSpectralMeasure T U u v B.1 := by
  choose P hP hs using h.exists_symmetric_operator
  have hinter : ∀ B B' : MeasurableSubtype SpectralPlane,
      P B * P B' = P ⟨B.1 ∩ B'.1, B.2.inter B'.2⟩ := fun B B' => by
    refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
    rw [hP ⟨B.1 ∩ B'.1, B.2.inter B'.2⟩ u v]
    change inner ℂ u (P B (P B' v)) = _
    rw [← hs B u, hP B' (P B u) v, h.measure_apply_left_eq_restrict (hP B) (hs B),
      VectorMeasure.restrict_apply _ B.2 B'.2, inter_comm]
  have huniv : P ⟨univ, MeasurableSet.univ⟩ = 1 := by
    refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
    have hs₀ := h.transform_spec u v 0 0
    rw [h.pair.semigroup.map_zero, h.pair.group.map_zero,
      laplaceFourier_zero_zero] at hs₀
    rw [hP]
    exact hs₀.symm
  refine ⟨⟨P, fun B => ⟨hs B, ?_⟩, huniv, hinter, fun u v =>
    ⟨pairSpectralMeasure T U u v, fun B => (hP B u v).symm⟩⟩, fun u v B => hP B u v⟩
  rw [hinter]
  exact congrArg P (Subtype.ext (inter_self _))
theorem matrixCoeff_eq (h : PairHypotheses T U) {P : ProjValuedMeasure H}
    (hP : IsJointSpectralPVM T U P) (u v : H) :
    P.matrixCoeff u v = pairSpectralMeasure T U u v :=
  h.eq_of_hasSpectralTransform fun t s => hP t s u v
theorem inner_pvm (h : PairHypotheses T U) {P : ProjValuedMeasure H}
    (hP : IsJointSpectralPVM T U P) (u v : H) (B : MeasurableSubtype SpectralPlane) :
    inner ℂ u (P B v) = pairSpectralMeasure T U u v B.1 := by
  rw [← P.matrixCoeff_apply, h.matrixCoeff_eq hP]
theorem existsUnique_pvm (h : PairHypotheses T U) :
    ∃! P : ProjValuedMeasure H, IsJointSpectralPVM T U P := by
  obtain ⟨P, hP⟩ := h.exists_pvm
  have hc : ∀ u v, P.matrixCoeff u v = pairSpectralMeasure T U u v := fun u v =>
    VectorMeasure.ext fun B hB => by
      rw [P.matrixCoeff_apply u v ⟨B, hB⟩, hP]
  refine ⟨P, fun t s u v => ?_, fun P' hP' => ?_⟩
  · rw [hc]
    exact h.transform_spec u v t s
  · have e : P'.toFun = P.toFun := by
      funext B
      refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
      exact (h.inner_pvm hP' u v B).trans (hP u v B).symm
    cases P
    cases P'
    cases e
    rfl
end PairHypotheses
end Pair
theorem jointSpectralTheorem_proof
    (hPositive : VectorSpectralMeasureExists)
    (hUnique : TwoPoints.SpectralMeasureUniqueness.Statement)
    (hRiesz : HilbertSpace.BoundedSesqRep.Claim)
    (hForms : FormCompletionAndBoundedExtension)
    (hSmeared : TwoPoints.LineTransforms.SmearedPairBounds) :
    JointSpectralTheorem := by
  intro H _ _ _ T U hp
  have g : PairHypotheses T U :=
    { pair := hp
      positive := hPositive H T U hp
      unique := hUnique.2
      group := (hSmeared H T U hp).1.inner_group_left
      cauchySchwarz := fun b hb => (hForms.1 H b hb).1.norm_le_mul
      riesz := hRiesz }
  exact
    { hasSpectralTransform := g.transform_spec
      eq_of_hasSpectralTransform := fun u v μ hμ => g.eq_of_hasSpectralTransform hμ
      add_left := g.add_left
      smul_left := g.smul_left
      add_right := g.add_right
      smul_right := g.smul_right
      conj_symm := g.conj_symm
      nonneg := g.nonneg
      mass := g.mass
      norm_sq_le := g.norm_sq_le
      variation_le := g.variation_le
      right_eq_density := g.right_eq_density
      both_eq_density := g.both_eq_density
      existsUnique_pvm := g.existsUnique_pvm
      inner_pvm := fun P hP u v B => g.inner_pvm hP u v B }
end YangMills.Construction.SpectralCalculus.JointSpectralProof
end
