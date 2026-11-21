import YangMills.Construction.Lattice.ComplexAverageOnHolomorphicFamilies
import YangMills.Construction.Lattice.LinearisedConstraintAtAFormedBond
import YangMills.Construction.Lattice.LinearisedConstraintOnHolomorphicFamilies
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.Matrices.MatrixOperationsKeepHolomorphy
import YangMills.Construction.Matrices.ParameterDerivativeHolomorphy
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice.HolomorphicConstraint
open YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
variable {ι κ : Type}
private theorem isClosed_traceless : IsClosed (ComplexMatrix2.traceless : Set ComplexMatrix2) :=
  Submodule.closed_of_finiteDimensional ComplexMatrix2.traceless
private theorem deriv_mem_traceless {g : ℂ → ComplexMatrix2} {t : ℂ}
    (h : ∀ᶠ s in 𝓝 t, g s ∈ ComplexMatrix2.traceless) :
    deriv g t ∈ ComplexMatrix2.traceless := by
  by_cases hd : DifferentiableAt ℂ g t
  · refine isClosed_traceless.mem_of_tendsto hd.hasDerivAt.tendsto_slope ?_
    filter_upwards [h.filter_mono nhdsWithin_le_nhds] with s hs
    exact ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.sub_mem hs h.self_of_nhds)
  · rw [deriv_zero_of_not_differentiableAt hd]
    exact ComplexMatrix2.traceless.zero_mem
private theorem iteratedDeriv_mem_traceless {f : ℂ → ComplexMatrix2}
    (h : ∀ᶠ t in 𝓝 (0 : ℂ), f t ∈ ComplexMatrix2.traceless)
    (n : ℕ) : iteratedDeriv n f 0 ∈ ComplexMatrix2.traceless := by
  have key : ∀ n : ℕ, ∀ᶠ t in 𝓝 (0 : ℂ), iteratedDeriv n f t ∈ ComplexMatrix2.traceless := by
    intro n
    induction n with
    | zero => simpa [iteratedDeriv_zero] using h
    | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.eventually_nhds.mono fun t ht => deriv_mem_traceless ht
  exact (key n).self_of_nhds
private def dropExtra (q : ι ⊕ (κ ⊕ Unit) → ComplexMatrix2) : ι ⊕ κ → ComplexMatrix2
  | .inl i => q (.inl i)
  | .inr k => q (.inr (.inl k))
private def extraCoordinate (q : ι ⊕ (κ ⊕ Unit) → ComplexMatrix2) : ℂ := q (.inr (.inr ())) 0 0
private theorem dropExtra_withParameter (p : ι ⊕ κ → ComplexMatrix2) (t : ℂ) :
    dropExtra (withParameter p t) = p := by
  funext x
  cases x <;> rfl
private theorem extraCoordinate_withParameter (p : ι ⊕ κ → ComplexMatrix2) (t : ℂ) :
    extraCoordinate (withParameter p t) = t := by
  simp [extraCoordinate, withParameter, cartanDirection]
private theorem continuous_dropExtra :
    Continuous (dropExtra : (ι ⊕ (κ ⊕ Unit) → ComplexMatrix2) → ι ⊕ κ → ComplexMatrix2) := by
  refine continuous_pi fun x => ?_
  cases x with
  | inl i => exact continuous_apply _
  | inr k => exact continuous_apply _
private theorem dropExtra_mem {q : ι ⊕ (κ ⊕ Unit) → ComplexMatrix2}
    (hq : q ∈ GroupLieProduct ι (κ ⊕ Unit)) :
    dropExtra q ∈ GroupLieProduct ι κ := by
  intro x
  cases x with
  | inl i => exact hq (.inl i)
  | inr k => exact hq (.inr (.inl k))
private theorem cartanDirection_mem : cartanDirection ∈ ComplexMatrix2.traceless := by
  show Matrix.trace cartanDirection = 0
  simp [cartanDirection, Matrix.trace]
private theorem withParameter_mem {p : ι ⊕ κ → ComplexMatrix2} (hp : p ∈ GroupLieProduct ι κ)
    (t : ℂ) : withParameter p t ∈ GroupLieProduct ι (κ ⊕ Unit) := by
  intro x
  rcases x with i | k | u
  · exact hp (.inl i)
  · exact hp (.inr k)
  · exact ComplexMatrix2.traceless.smul_mem t cartanDirection_mem
private def liftedDomain (W : Set (ι ⊕ κ → ComplexMatrix2)) :
    Set (ι ⊕ (κ ⊕ Unit) → ComplexMatrix2) :=
  {q | q ∈ GroupLieProduct ι (κ ⊕ Unit) ∧ dropExtra q ∈ W}
private theorem liftedDomain_open {W : Set (ι ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι (κ ⊕ Unit)) (liftedDomain W) := by
  obtain ⟨O, hO, rfl⟩ := hW
  refine ⟨dropExtra ⁻¹' O, hO.preimage continuous_dropExtra, ?_⟩
  ext q
  constructor
  · rintro ⟨hq, h, -⟩
    exact ⟨h, hq⟩
  · rintro ⟨h, hq⟩
    exact ⟨hq, h, dropExtra_mem hq⟩
variable [Fintype ι] [Fintype κ]
private theorem dropExtra_holomorphic (hM : HolomorphyClosureStatement)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {W : Set (ι ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) :
    IsHolomorphicToProduct b (liftedDomain W) dropExtra := by
  have hW' := liftedDomain_open hW
  have hmember := (hM ι (κ ⊕ Unit) b (liftedDomain W) hW').2.1
  refine ⟨hW', fun i => ?_, fun k => ?_⟩
  · have hmaps : MapsTo (fun q : ι ⊕ (κ ⊕ Unit) → ComplexMatrix2 => dropExtra q (.inl i))
        (liftedDomain W) ComplexMatrix2.unitDeterminant := fun _ hq => hq.1 (.inl i)
    exact ((hE.2.2.2.1 ι (κ ⊕ Unit)).2.1 b (liftedDomain W) _ hW' hmaps).2 (hmember (.inl i))
  · exact ⟨fun _ hq => hq.1 (.inr (.inl k)), hmember (.inr (.inl k))⟩
private theorem comp_dropExtra_holomorphic (hM : HolomorphyClosureStatement)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {W : Set (ι ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToMatrixEntries b W Φ) :
    IsHolomorphicToMatrixEntries b (liftedDomain W) fun q => Φ (dropExtra q) := by
  have h := (hE.2.2.2.2.1 ι (κ ⊕ Unit) ι κ b (liftedDomain W) dropExtra (liftedDomain_open hW)
    (dropExtra_holomorphic hM hE b hW) ComplexMatrix2 4
    Coordinates.ComplexCoordinates.matrixEquiv W Φ hΦ).2.2
  have hset : liftedDomain W ∩ dropExtra ⁻¹' W = liftedDomain W :=
    inter_eq_left.2 fun q hq => hq.2
  rw [hset] at h
  exact h
private theorem gaugeField_family (hM : HolomorphyClosureStatement)
    (hE : ExpChartHolomorphy.ExpChartTheory) {L m : ℕ} {j : ℤ}
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {U : (ι ⊕ κ → ComplexMatrix2) → Bond L m j → ComplexMatrix2}
    (hU : IsHolomorphicGaugeFieldFamily b W U) :
    IsHolomorphicGaugeFieldFamily b (liftedDomain W) fun q => U (dropExtra q) :=
  ⟨liftedDomain_open hU.isOpen, fun _ hq => hU.isGaugeField _ hq.2,
    fun e => comp_dropExtra_holomorphic hM hE b hU.isOpen (hU.holomorphic e)⟩
private def topLeftScalar : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 :=
  (LinearMap.toSpanSingleton ℂ ComplexMatrix2 1) ∘ₗ
    (Matrix.entryLinearMap ℂ ℂ (0 : Fin 2) (0 : Fin 2))
private theorem scaled_form_family (hM : HolomorphyClosureStatement)
    (hE : ExpChartHolomorphy.ExpChartTheory) {L m : ℕ} {j : ℤ}
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {A : (ι ⊕ κ → ComplexMatrix2) → Bond L m j → ComplexMatrix2}
    (hA : IsHolomorphicBondFormFamily b W A) :
    IsHolomorphicBondFormFamily b (liftedDomain W)
      fun q => extraCoordinate q • A (dropExtra q) := by
  have hW' := liftedDomain_open hA.isOpen
  obtain ⟨-, hmember, -, hmul, hlin, -, -, -, -, -, hcongr⟩ := hM ι (κ ⊕ Unit) b (liftedDomain W) hW'
  refine ⟨hW', fun q hq => ⟨fun e he => ?_, fun e => ?_⟩, fun e => ?_⟩
  · exact ComplexMatrix2.traceless.smul_mem _ ((hA.isBondForm _ hq.2).1 e he)
  · simp [(hA.isBondForm _ hq.2).2 e]
  · refine hcongr _ _ (hmul _ _ (hlin topLeftScalar _ (hmember (.inr (.inr ()))))
      (comp_dropExtra_holomorphic hM hE b hA.isOpen (hA.holomorphic e))) fun q _ => ?_
    simp [topLeftScalar, extraCoordinate, LinearMap.toSpanSingleton_apply]
private theorem parameter_derivatives (hM : HolomorphyClosureStatement)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hC : HolomorphicFamilyComplexAverage)
    (hD : ParameterDerivativesHolomorphic)
    (hF : LinearizedConstraintAtBond.Statement)
    {L m K k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {U : (ι ⊕ κ → ComplexMatrix2) → BondAtLevel L m K k → ComplexMatrix2}
    (hU : IsHolomorphicGaugeFieldFamily b W U)
    {c : BondAtLevel L m K (k + 1)} (hc : c.IsPositivelyOriented)
    (hin : ∀ p ∈ W, U p ∈
      (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)))
    {A : (ι ⊕ κ → ComplexMatrix2) → BondAtLevel L m K k → ComplexMatrix2}
    (hA : IsHolomorphicBondFormFamily b W A) :
    (∀ n : ℕ, IsHolomorphicToMatrixEntries b W fun p =>
      iteratedDeriv n (fun t : ℂ => constraintMap (U p) (t • A p) c) 0) ∧
    ∀ p ∈ W, ∀ᶠ t in 𝓝 (0 : ℂ), constraintMap (U p) (t • A p) c ∈ ComplexMatrix2.traceless := by
  have hW := hU.isOpen
  obtain ⟨-, hS⟩ := (hC L m K k hL hm hk ι (κ ⊕ Unit) b (liftedDomain W) _
    (gaugeField_family hM hE hU) c hc).2.2.2 _ (scaled_form_family hM hE hA)
  have hvalue : ∀ (p : ι ⊕ κ → ComplexMatrix2) (t : ℂ),
      constraintMap (U (dropExtra (withParameter p t)))
        (extraCoordinate (withParameter p t) • A (dropExtra (withParameter p t))) c =
      constraintMap (U p) (t • A p) c := by
    intro p t
    rw [dropExtra_withParameter, extraCoordinate_withParameter]
  have hpoint : ∀ p ∈ W, ∀ t : ℂ, ConstraintMapDefined (U p) (t • A p) c →
      withParameter p t ∈ {q | q ∈ liftedDomain W ∧
        U (dropExtra q) ∈
          (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
        ConstraintMapDefined (U (dropExtra q))
          (extraCoordinate q • A (dropExtra q)) c} := by
    intro p hp t ht
    obtain ⟨O, -, rfl⟩ := hW
    refine ⟨⟨withParameter_mem hp.2 t, ?_⟩, ?_, ?_⟩
    · rw [dropExtra_withParameter]
      exact hp
    · rw [dropExtra_withParameter]
      exact hin p hp
    · rw [dropExtra_withParameter, extraCoordinate_withParameter]
      exact ht
  have hdefined : ∀ p ∈ W, ∀ᶠ t in 𝓝 (0 : ℂ), ConstraintMapDefined (U p) (t • A p) c :=
    fun p hp => (hF L m K k hL hm hk (U p) c hc (hin p hp)).eventually_constraintMapDefined (A p)
      (hA.isBondForm p hp)
  refine ⟨fun n => ?_, fun p hp => ?_⟩
  · have h := hD ι κ b W _ _ hW hS.2
      (fun p hp => hpoint p hp 0 (hdefined p hp).self_of_nhds) n
    simpa only [hvalue] using h
  · filter_upwards [hdefined p hp] with t ht
    have h := hS.1 (hpoint p hp t ht)
    beta_reduce at h
    rwa [hvalue] at h
theorem claim_holds (closure : HolomorphyClosureStatement)
    (expChart : ExpChartHolomorphy.ExpChartTheory)
    (average : HolomorphicFamilyComplexAverage)
    (derivs : ParameterDerivativesHolomorphic)
    (atBond : LinearizedConstraintAtBond.Statement) : claim := by
  intro L m K k hL hm hk ι κ _ _ b W U hU c hc hin
  obtain ⟨-, -, hadd, -, hlin, -, -, -, -, -, hcongr⟩ := closure ι κ b W hU.isOpen
  have hLne : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hL.2; omega)
  have hscale : ∀ (z : ℂ) (Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2),
      IsHolomorphicToMatrixEntries b W Φ → IsHolomorphicToMatrixEntries b W fun p => z • Φ p :=
    fun z Φ hΦ => hcongr _ _ (hlin (z • LinearMap.id) Φ hΦ) fun p _ => by simp
  have bond := fun (p : ι ⊕ κ → ComplexMatrix2) (hp : p ∈ W) =>
    atBond L m K k hL hm hk (U p) c hc (hin p hp)
  have P := fun (B : (ι ⊕ κ → ComplexMatrix2) → BondAtLevel L m K k → ComplexMatrix2)
    (h : IsHolomorphicBondFormFamily b W B) =>
      parameter_derivatives closure expChart average derivs atBond hL hm hk b hU hc hin h
  constructor
  · intro A hA
    refine ⟨fun p hp => (bond p hp).mem_complexLieAlgebra (A p) (hA.isBondForm p hp),
      hcongr _ _ (hscale (L : ℂ)⁻¹ _ ((P A hA).1 1)) fun p hp => ?_⟩
    rw [iteratedDeriv_one, ((bond p hp).hasDerivAt_constraintMap (A p) (hA.isBondForm p hp)).deriv,
      smul_smul, inv_mul_cancel₀ hLne, one_smul]
  · intro A₁ A₂ h₁ h₂
    have hsum : IsHolomorphicBondFormFamily b W fun p => A₁ p + A₂ p := by
      refine ⟨hU.isOpen, fun p hp => ?_, fun e => hadd _ _ (h₁.holomorphic e) (h₂.holomorphic e)⟩
      obtain ⟨f₁, g₁⟩ := h₁.isBondForm p hp
      obtain ⟨f₂, g₂⟩ := h₂.isBondForm p hp
      exact ⟨fun e he => ComplexMatrix2.traceless.add_mem (f₁ e he) (f₂ e he),
        fun e => by simp only [Pi.add_apply, g₁, g₂, neg_add]⟩
    obtain ⟨hol₁, near₁⟩ := P A₁ h₁
    obtain ⟨hol₂, near₂⟩ := P A₂ h₂
    obtain ⟨hol₃, near₃⟩ := P _ hsum
    refine ⟨fun p hp => ?_, ?_⟩
    · refine ComplexMatrix2.traceless.smul_mem _ (sub_mem (sub_mem ?_ ?_) ?_) <;>
        refine ComplexMatrix2.traceless.smul_mem _ (iteratedDeriv_mem_traceless ?_ 2)
      exacts [near₃ p hp, near₁ p hp, near₂ p hp]
    · have g₃ := hscale (2⁻¹ : ℂ) _ (hol₃ 2)
      have g₁ := hscale (-2⁻¹ : ℂ) _ (hol₁ 2)
      have g₂ := hscale (-2⁻¹ : ℂ) _ (hol₂ 2)
      refine hcongr _ _ (hscale (2⁻¹ : ℂ) _ (hadd _ _ (hadd _ _ g₃ g₁) g₂)) fun p _ => ?_
      simp only [constraintBilinear, constraintQuadratic, sub_eq_add_neg, neg_smul, one_div]
end YangMills.Construction.PeriodicLattice.HolomorphicConstraint
