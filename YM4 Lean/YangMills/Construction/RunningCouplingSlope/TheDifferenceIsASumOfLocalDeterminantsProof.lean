import YangMills.Construction.PeriodicOperators.JetsOnADisjointSumAndOnTheUnionOfAPair
import YangMills.Construction.PeriodicOperators.OrbitsOfAPeriodicIndexSetProof
import YangMills.Construction.RunningCouplingSlope.GhostOfTheSoftChainIsTheMixedGhost
import YangMills.Construction.RunningCouplingSlope.SoftSaddleIsTheMixedSaddle
import YangMills.Construction.RunningCouplingSlope.SymbolsOfThePlainSaddles
import YangMills.Construction.RunningCouplingSlope.TheDifferenceIsASumOfLocalDeterminants
import YangMills.Construction.RunningCouplingSlope.ThePlainSaddlesAreLocal
import YangMills.Construction.RunningCouplingSlope.ThePlainSaddlesDescend
import YangMills.Construction.Towers.DeterminantsOfTheTwoOperatorFunctionsOnTheTorusProof
import YangMills.Construction.Towers.TheBackgroundFieldAmongTheTriples
import YangMills.Construction.Towers.TheSecondDifferentialIsCloseToItsSymbolProof
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.LocalLogDetSum
open Tower PeriodicOperators PeriodicOperators.LogDetSecondDerivs
open Tower.ResponseOperators (ClassFnEqForm)
open LocalKernels (projPositiveEdge)
open LocalKernels.Periodisation
variable {L n k : ℕ}
private theorem det_linearMapOfEntries {C : Type} [Fintype C] [DecidableEq C] (K : C → C → ℂ) :
    LinearMap.det (linearMapOfEntries K) = (Matrix.of K).det := by apply _root_.YangMills.Construction.Tower.PeriodicDeterminants.det_linearMapOfEntries <;> assumption
private theorem det_quotOperator_of_periodizesTo {I : PeriodicData} {P : Type} [Fintype P]
    [DecidableEq P]
    {T : ((colourEdges L k 0).Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} {im : I.Carrier → P}
    {M : Matrix P P ℂ} {s : ℕ} {g : (colourEdges L k 0).QuotMod s → ℂ}
    (φ : I.QuotMod s ≃ P) (hφ : ∀ ι, φ (I.mkQuot s ι) = im ι)
    (h : PeriodizesTo T im M s g) :
    LinearMap.det (quotOperator (colourEdges L k 0) I T s g) = M.det := by
  classical
  have : Fintype (I.QuotMod s) := Fintype.ofEquiv P φ.symm
  have hK : ∀ c' c, descendMatrix I I s (periodicValue (colourEdges L k 0) I I T s g) c' c =
      M (φ c') (φ c) := by
    intro c' c
    have hex : ∃ z, ∀ ι' ι, I.mkQuot s ι' = c' → I.mkQuot s ι = c →
        periodicValue (colourEdges L k 0) I I T s g ι' ι = z :=
      ⟨M (φ c') (φ c), fun ι' ι h1 h2 => by rw [h ι' ι, ← hφ, ← hφ, h1, h2]⟩
    obtain ⟨ι', rfl⟩ : ∃ ι', I.mkQuot s ι' = c' := Quot.exists_rep c'
    obtain ⟨ι, rfl⟩ : ∃ ι, I.mkQuot s ι = c := Quot.exists_rep c
    have hs := Classical.epsilon_spec hex ι' ι rfl rfl
    refine hs.symm.trans ?_
    rw [h ι' ι, hφ, hφ]
  unfold LogDetSecondDerivs.quotOperator
  rw [det_linearMapOfEntries]
  have e : Matrix.of (descendMatrix I I s (periodicValue (colourEdges L k 0) I I T s g)) =
      M.submatrix φ φ := by
    ext c' c
    exact hK c' c
  rw [e, Matrix.det_submatrix_equiv_self]
private theorem exists_quotEquiv {I : PeriodicData} {P : Type} {s : ℕ} (im : I.Carrier → P)
    (hsurj : Function.Surjective im)
    (hfib : ∀ x y, im x = im y ↔ I.mkQuot s x = I.mkQuot s y) :
    ∃ φ : I.QuotMod s ≃ P, ∀ ι, φ (I.mkQuot s ι) = im ι := by
  let φ₀ : I.QuotMod s → P := Quot.lift im fun a b h => (hfib a b).2 (Quot.sound h)
  refine ⟨Equiv.ofBijective φ₀ ⟨fun c c' h => ?_, fun p => ?_⟩, fun ι => rfl⟩
  · obtain ⟨x, rfl⟩ : ∃ x, I.mkQuot s x = c := Quot.exists_rep c
    obtain ⟨y, rfl⟩ : ∃ y, I.mkQuot s y = c' := Quot.exists_rep c'
    exact (hfib x y).1 h
  · obtain ⟨x, rfl⟩ := hsurj p
    exact ⟨I.mkQuot s x, rfl⟩
private theorem mkQuot_eq_iff {F : PeriodicData} (hF : IsPeriodic F) (s : ℕ)
    (ι ι' : F.Carrier) :
    F.mkQuot s ι = F.mkQuot s ι' ↔ ∃ m : Fin 4 → ℤ, ι' = F.translate (s • m) ι := by apply _root_.YangMills.Construction.PeriodicOperators.QuotOrbits.mkQuot_eq_iff <;> assumption
private theorem edges_classified {j : ℕ} (hP : IsPeriodic (colourEdges L k j))
    (hC : ProjCellsClassified L n k j) :
    Function.Surjective (fun ι : (colourEdges L k j).Carrier =>
      ((ι.1, projPositiveEdge L n k j ι.2) : Fin 3 × PositiveEdge L n k j)) ∧
    ∀ x y : (colourEdges L k j).Carrier,
      ((x.1, projPositiveEdge L n k j x.2) : Fin 3 × PositiveEdge L n k j) =
          (y.1, projPositiveEdge L n k j y.2) ↔
        (colourEdges L k j).mkQuot (periodSide L n) x =
          (colourEdges L k j).mkQuot (periodSide L n) y := by
  obtain ⟨hs, hf⟩ := hC .edge
  refine ⟨fun p => ?_, fun x y => ?_⟩
  · obtain ⟨b, hb⟩ := hs p.2
    exact ⟨(p.1, b), Prod.ext rfl hb⟩
  · rw [mkQuot_eq_iff hP]
    constructor
    · intro h
      obtain ⟨m, hm⟩ := (hf x.2 y.2).1 (congrArg Prod.snd h)
      exact ⟨m, Prod.ext (congrArg Prod.fst h).symm hm⟩
    · rintro ⟨m, hm⟩
      have h2 := (hf x.2 y.2).2 ⟨m, congrArg Prod.snd hm⟩
      exact Prod.ext (congrArg Prod.fst hm).symm h2
private theorem vertices_classified {j : ℕ} (hP : IsPeriodic (colourVertices L k j))
    (hC : ProjCellsClassified L n k j) :
    Function.Surjective (fun ι : (colourVertices L k j).Carrier =>
      ((ι.1, FullSpace.projVertex L n k j ι.2) : Fin 3 × Vertex L n k j)) ∧
    ∀ x y : (colourVertices L k j).Carrier,
      ((x.1, FullSpace.projVertex L n k j x.2) : Fin 3 × Vertex L n k j) =
          (y.1, FullSpace.projVertex L n k j y.2) ↔
        (colourVertices L k j).mkQuot (periodSide L n) x =
          (colourVertices L k j).mkQuot (periodSide L n) y := by
  obtain ⟨hs, hf⟩ := hC .vertex
  refine ⟨fun p => ?_, fun x y => ?_⟩
  · obtain ⟨b, hb⟩ := hs p.2
    exact ⟨(p.1, b), Prod.ext rfl hb⟩
  · rw [mkQuot_eq_iff hP]
    constructor
    · intro h
      obtain ⟨m, hm⟩ := (hf x.2 y.2).1 (congrArg Prod.snd h)
      exact ⟨m, Prod.ext (congrArg Prod.fst h).symm hm⟩
    · rintro ⟨m, hm⟩
      have h2 := (hf x.2 y.2).2 ⟨m, congrArg Prod.snd hm⟩
      exact Prod.ext (congrArg Prod.fst hm).symm h2
private theorem disjSum_classified {I₁ I₂ : PeriodicData} {P₁ P₂ : Type} {s : ℕ}
    (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂) (h : IsPeriodic (I₁.disjSum I₂))
    {f₁ : I₁.Carrier → P₁} {f₂ : I₂.Carrier → P₂} (s₁ : Function.Surjective f₁)
    (s₂ : Function.Surjective f₂)
    (b₁ : ∀ x y, f₁ x = f₁ y ↔ I₁.mkQuot s x = I₁.mkQuot s y)
    (b₂ : ∀ x y, f₂ x = f₂ y ↔ I₂.mkQuot s x = I₂.mkQuot s y) :
    ∃ φ : (I₁.disjSum I₂).QuotMod s ≃ (P₁ ⊕ P₂),
      ∀ ι, φ ((I₁.disjSum I₂).mkQuot s ι) = Sum.map f₁ f₂ ι := by
  refine exists_quotEquiv (I := I₁.disjSum I₂) (P := P₁ ⊕ P₂) (Sum.map f₁ f₂)
    (Sum.map_surjective.2 ⟨s₁, s₂⟩) fun x y => ?_
  rw [mkQuot_eq_iff h]
  rcases x with x | x <;> rcases y with y | y
  · simp only [Sum.map_inl, Sum.inl.injEq]
    rw [b₁, mkQuot_eq_iff h₁]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, congrArg Sum.inl hm⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, Sum.inl_injective hm⟩
  · simp only [Sum.map_inl, Sum.map_inr, reduceCtorEq, false_iff]
    rintro ⟨m, hm⟩
    exact Sum.inr_ne_inl hm
  · simp only [Sum.map_inl, Sum.map_inr, reduceCtorEq, false_iff]
    rintro ⟨m, hm⟩
    exact Sum.inl_ne_inr hm
  · simp only [Sum.map_inr, Sum.inr.injEq]
    rw [b₂, mkQuot_eq_iff h₂]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, congrArg Sum.inr hm⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, Sum.inr_injective hm⟩
private theorem isUnit_symbolHom_of_invertible {I : PeriodicData} {T : I.Carrier → I.Carrier → ℂ}
    (h : SymbolInvertibleOnReals I T) (κ : InfiniteLattice.AmbientSpace) :
    IsUnit (symbolHom I I T (toComplexVec κ) : Module.End ℂ (I.UnitQuot → ℂ)) := by apply _root_.YangMills.Construction.Tower.FullSpace.JointWidthProof.isUnit_symbolHom <;> assumption
private theorem isRealOnRealFields_of_near {F I : PeriodicData}
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
    (hHol : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hnear : ∀ f : F.Carrier → ℂ, (∀ κ, (f κ).im = 0) → IsSupBelow F f ρ₀ →
      ∀ ι' ι, (T f ι' ι).im = 0) :
    IsRealOnRealFields F I T := by apply _root_.YangMills.Construction.Tower.SecondDerivNearSymbol.isRealOnRealFields_of_eventually <;> assumption
private theorem pauliCoeff_zero (a : Fin 3) :
    pauliCoeff a (0 : Matrices.ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem sum_pauliCoeff {X : Matrices.ComplexMatrix2}
    (h : X ∈ Matrices.ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • Matrices.ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem isCompactValued_of_pauliCoeffs {L k : ℕ} (hL : 0 < L) (ζ : FullSpace.FullField L k)
    (h : ∀ κ, (ζ.pauliCoeffs hL κ).im = 0) : ζ.IsCompactValued := by apply _root_.YangMills.Construction.Tower.SecondDerivNearSymbol.isCompactValued_of_pauliCoeffs <;> assumption
private theorem continuous_matExp :
    Continuous (fun X : Matrices.ComplexMatrix2 => Matrices.ComplexMatrix2.matExp X) := by apply _root_.YangMills.Construction.Tower.FirstDerivVanishing.continuous_matExp <;> assumption
private theorem inv_matExp_neg (X : Matrices.ComplexMatrix2) :
    (Matrices.ComplexMatrix2.matExp (-X))⁻¹ = Matrices.ComplexMatrix2.matExp X := by
  rw [Matrices.ComplexMatrix2.matExp, Matrix.exp_neg, Matrix.nonsing_inv_nonsing_inv]
  exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp X)
private theorem matExp_mem_compactGaugeGroup {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    Matrices.ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
private theorem expTwist_eq {j : ℕ} {Y : Edge L n k j → Matrices.ComplexMatrix2}
    (hY : ∀ b, Y b.opposite = -Y b) (b : Edge L n k j) :
    PeriodicLattice.expTwist Y (fun _ => 1) b = Matrices.ComplexMatrix2.matExp (Complex.I • Y b) := by
  classical
  simp only [PeriodicLattice.expTwist, mul_one]
  split_ifs
  · rfl
  · rw [hY, smul_neg, inv_matExp_neg]
private theorem expTwist_mem
    (hX : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (B : edgeFormSpace L n k 0) :
    PeriodicLattice.expTwist (B : Edge L n k 0 → Matrices.ComplexMatrix2) (fun _ => 1) ∈
      fieldSpace L n k 0 := by
  have hsu : ∀ b : Edge L n k 0,
      (B : Edge L n k 0 → Matrices.ComplexMatrix2) b ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
    intro b
    rcases hX b with ⟨hp, -⟩ | ⟨hp, -⟩
    · exact B.2.1 b hp
    · have h1 : (B : Edge L n k 0 → Matrices.ComplexMatrix2) b.opposite ∈
          Matrices.ComplexMatrix2.hermitianTraceless := B.2.1 _ hp
      rw [B.2.2 b] at h1
      simpa using Matrices.ComplexMatrix2.hermitianTraceless.neg_mem h1
  have he := expTwist_eq (L := L) (n := n) (k := k) (j := 0) B.2.2
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · rw [he]
    exact matExp_mem_compactGaugeGroup (hsu b)
  · rw [he, he, B.2.2 b, smul_neg, Matrices.ComplexMatrix2.matExp, Matrices.ComplexMatrix2.matExp,
      Matrix.exp_neg]
private theorem eventually_of_small_form
    (hX : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hsurj : Function.Surjective (fun ι : (colourEdges L k 0).Carrier =>
      ((ι.1, projPositiveEdge L n k 0 ι.2) : Fin 3 × PositiveEdge L n k 0)))
    {P : (Edge L n k 0 → Matrices.ComplexMatrix2) → Prop}
    (hP : EventuallyNearIdentity (fieldSpace L n k 0) P) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (r : edgeFormSpace L n k 0)
      (g : (colourEdges L k 0).QuotMod (periodSide L n) → ℝ),
      ClassFnEqForm L n k 0 (restrictToPositiveEdges (r : Edge L n k 0 → Matrices.ComplexMatrix2))
        (fun x => (g x : ℂ)) →
      (∀ x, |g x| < ε) →
      P (PeriodicLattice.expTwist (r : Edge L n k 0 → Matrices.ComplexMatrix2)
        (trivialField L n k 0)) := by
  classical
  have h1 := eventually_nhdsWithin_iff.1 hP
  rw [Filter.Eventually, nhds_pi, Filter.mem_pi'] at h1
  obtain ⟨I, t, ht, hsub⟩ := h1
  let G : (Fin 3 → ℝ) → Matrices.ComplexMatrix2 := fun x =>
    Matrices.ComplexMatrix2.matExp
      (Complex.I • ∑ a, ((x a : ℝ) : ℂ) • Matrices.ComplexMatrix2.pauliFamily a)
  have hG : Continuous G := by
    refine continuous_matExp.comp (Continuous.const_smul ?_ Complex.I)
    refine continuous_finsetSum _ fun a _ => ?_
    exact Continuous.smul (f := fun x : Fin 3 → ℝ => ((x a : ℝ) : ℂ))
      (g := fun _ => Matrices.ComplexMatrix2.pauliFamily a)
      (Complex.continuous_ofReal.comp (continuous_apply a)) continuous_const
  have hG0 : G 0 = 1 := by
    simp [G, Matrices.ComplexMatrix2.matExp]
  have hmem : ⋂ b ∈ I, G ⁻¹' t b ∈ 𝓝 (0 : Fin 3 → ℝ) := by
    refine (Filter.biInter_finset_mem I).2 fun b _ => hG.continuousAt.preimage_mem_nhds ?_
    rw [hG0]
    exact ht b
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨ε, hε, fun r g hr hg => ?_⟩
  have hval : ∀ b : Edge L n k 0, b.IsPositivelyOriented → ∃ x : Fin 3 → ℝ, (∀ a, |x a| < ε) ∧
      (r : Edge L n k 0 → Matrices.ComplexMatrix2) b =
        ∑ a, ((x a : ℝ) : ℂ) • Matrices.ComplexMatrix2.pauliFamily a := by
    intro b hb
    have hchoose : ∀ a : Fin 3, ∃ ι : (colourEdges L k 0).Carrier,
        ((ι.1, projPositiveEdge L n k 0 ι.2) : Fin 3 × PositiveEdge L n k 0) = (a, ⟨b, hb⟩) :=
      fun a => hsurj (a, ⟨b, hb⟩)
    choose ι hι using hchoose
    refine ⟨fun a => g ((colourEdges L k 0).mkQuot _ (ι a)), fun a => hg _, ?_⟩
    have hco : ∀ a, pauliCoeff a ((r : Edge L n k 0 → Matrices.ComplexMatrix2) b) =
        ((g ((colourEdges L k 0).mkQuot _ (ι a)) : ℝ) : ℂ) := by
      intro a
      have h2 := hr (ι a)
      rw [show (((ι a).1, projPositiveEdge L n k 0 (ι a).2) :
        Fin 3 × PositiveEdge L n k 0) = (a, ⟨b, hb⟩) from hι a] at h2
      exact h2.symm
    conv_lhs => rw [← sum_pauliCoeff (r.2.1 b hb).2]
    exact Finset.sum_congr rfl fun a _ => by rw [hco]
  have hin : ∀ b ∈ I, PeriodicLattice.expTwist (r : Edge L n k 0 → Matrices.ComplexMatrix2)
      (trivialField L n k 0) b ∈ t b := by
    intro b hb
    have hU : PeriodicLattice.expTwist (r : Edge L n k 0 → Matrices.ComplexMatrix2)
        (trivialField L n k 0) b =
        Matrices.ComplexMatrix2.matExp (Complex.I • (r : Edge L n k 0 → Matrices.ComplexMatrix2) b) :=
      expTwist_eq r.2.2 b
    rw [hU]
    have key : ∀ x : Fin 3 → ℝ, (∀ a, |x a| < ε) → G x ∈ t b := by
      intro x hx
      have hxb : x ∈ Metric.ball (0 : Fin 3 → ℝ) ε := by
        rw [Metric.mem_ball, dist_pi_lt_iff hε]
        intro a
        simpa [Real.dist_eq] using hx a
      have := hball hxb
      simp only [Set.mem_iInter, Set.mem_preimage] at this
      exact this b hb
    rcases hX b with ⟨hp, -⟩ | ⟨hp, -⟩
    · obtain ⟨x, hx, hxe⟩ := hval b hp
      rw [hxe]
      exact key x hx
    · obtain ⟨x, hx, hxe⟩ := hval _ hp
      have e2 : (r : Edge L n k 0 → Matrices.ComplexMatrix2) b =
          ∑ a, (((-x) a : ℝ) : ℂ) • Matrices.ComplexMatrix2.pauliFamily a := by
        have h3 : (r : Edge L n k 0 → Matrices.ComplexMatrix2) b =
            -(r : Edge L n k 0 → Matrices.ComplexMatrix2) b.opposite := by
          rw [r.2.2 b, neg_neg]
        rw [h3, hxe, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp
      rw [e2]
      exact key (-x) fun a => by simpa using hx a
  exact hsub (fun b hb => hin b (by simpa using hb)) (expTwist_mem hX r)
private theorem det_ne_zero_of_small {F I : PeriodicData}
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
    {s : ℕ} [Finite (F.QuotMod s)]
    (h : ∀ (N : ℕ) (e : Fin N ≃ F.QuotMod s), ∀ᶠ v in 𝓝 (0 : Fin N → ℝ),
      LinearMap.det (quotOperator F I T s fun c => (ofRealCoords e v c : ℂ)) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : F.QuotMod s → ℝ, (∀ x, |g x| < ε) →
      LinearMap.det (quotOperator F I T s fun c => (g c : ℂ)) ≠ 0 := by
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (F.QuotMod s)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.1 (h N e.symm)
  refine ⟨ε, hε, fun g hg => ?_⟩
  have hv : dist (fun j => g (e.symm j)) (0 : Fin N → ℝ) < ε := by
    rw [dist_pi_lt_iff hε]
    intro j
    simpa [Real.dist_eq] using hg _
  have := hb hv
  simpa [ofRealCoords] using this
private theorem extendByZero_zero {G F : PeriodicData} (e : G.Carrier → F.Carrier) :
    _root_.YangMills.Construction.PeriodicOperators.extendByZero e (0 : G.Carrier → ℂ) = 0 := by
  classical
  funext κ
  by_cases h : ∃ a, e a = κ
  · obtain ⟨a, rfl⟩ := h
    simp [PeriodicOperators.extendByZero, Function.extend_def]
  · simp [PeriodicOperators.extendByZero, h]
private theorem extendByZero_cases {G F : PeriodicData} (e : G.Carrier → F.Carrier)
    (f : G.Carrier → ℂ) (κ : F.Carrier) :
    _root_.YangMills.Construction.PeriodicOperators.extendByZero e f κ = 0 ∨ ∃ a, _root_.YangMills.Construction.PeriodicOperators.extendByZero e f κ = f a := by
  classical
  by_cases h : ∃ a, e a = κ
  · refine Or.inr ⟨h.choose, ?_⟩
    rw [PeriodicOperators.extendByZero, Function.extend_def, dif_pos h]
  · left
    simp [PeriodicOperators.extendByZero, h]
private theorem liftQuotField_onQuotient (hL : 0 < L)
    (hcl : QuotientClassesPeriodic L n (LocalKernels.fieldIndices L k hL))
    (ζ : PeriodicField L n k) :
    liftQuotField (FullSpace.fieldPeriodicData L k hL) (2 * L ^ n) (ζ.onQuotient hL) =
      ζ.pauliCoeffs hL := by apply _root_.YangMills.Construction.Tower.PeriodicDeterminants.liftQuotField_onQuotient <;> assumption
theorem differenceIsLocalLogDetSum
    (h₁ : QuietSaddleDetEqSaddleMatrixDet)
    (h₂ : GhostDeterminantAtQuietPoint)
    (hLoc : SaddleKernelsAreLocal)
    (hSym : MeanSaddleSymbolsInvertible)
    (hDesc : SaddleKernelsPeriodize)
    (hLogdet : PeriodicOperators.LogDetSecondDerivs.Claim)
    (hTwo : FullSpace.OperatorFunctions.OperatorFunctionsTheorem)
    (hRealT : FullSpace.OperatorFunctionsRealOnCompactFields)
    (hVal : FullSpace.FieldValues.FieldsAndValuesClaim)
    (hEmb : FullSpace.BackgroundJets.BackgroundTriple.ExtendsByZero)
    (hJets : ExtendByZeroJets.Claim)
    (hSum : DisjSumJets.Claim)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hTow : LocalKernels.IndexSetPeriodicity.Statement)
    (hCells : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hHol : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (hQuot : Quotients.QuotientTransposeNorm)
    (hNum : ParameterIndependence.Claim)
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy) : DifferenceIsLocalLogDetSum := by
  classical
  intro a ha L hS k hk
  have hL : 0 < L := by have := hS.2; omega
  have hk0 : 0 < k := hk
  obtain ⟨hs0, hb0, -⟩ := hIdx L hS k 0 (Nat.zero_le k)
  obtain ⟨hsk, hbk, -⟩ := hIdx L hS k k le_rfl
  have hfd : IsPeriodic (FullSpace.fieldPeriodicData L k hL) :=
    ((hTow L hS k).2 (LocalKernels.fieldIndices L k hL)).1
  have hV : IsPeriodic (FullSpace.vectorIndices L k) := (hSum _ _ _ hb0 hb0 hbk).1
  have hG : IsPeriodic (FullSpace.ghostIndices L k) := (hSum _ _ _ hb0 hs0 hsk).1
  have hemb := (hEmb L hL hS k hk).1
  obtain ⟨⟨-, -, -, hlv, hlg⟩, hFunc, hsv, hsg⟩ := hTwo L hL hS k hk
  set e := FullSpace.BackgroundJets.backgroundIndex L k hL with he
  let Tv : ((colourEdges L k 0).Carrier → ℂ) → (FullSpace.vectorIndices L k).Carrier →
      (FullSpace.vectorIndices L k).Carrier → ℂ :=
    fun f => FullSpace.vectorOpFn L k hL (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f)
  let Tg : ((colourEdges L k 0).Carrier → ℂ) → (FullSpace.ghostIndices L k).Carrier →
      (FullSpace.ghostIndices L k).Carrier → ℂ :=
    fun f => FullSpace.ghostOpFn L k hL (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f)
  have hlocv : IsLocalOpFun (colourEdges L k 0) (FullSpace.vectorIndices L k)
      (FullSpace.vectorIndices L k) Tv := (hJets _ _ _ _ hb0 hfd hV hV e hemb _ hlv).1
  have hlocg : IsLocalOpFun (colourEdges L k 0) (FullSpace.ghostIndices L k)
      (FullSpace.ghostIndices L k) Tg := (hJets _ _ _ _ hb0 hfd hG hG e hemb _ hlg).1
  have hzv : coeffZero (colourEdges L k 0) (FullSpace.vectorIndices L k)
      (FullSpace.vectorIndices L k) Tv = FullSpace.vectorOpFn L k hL 0 := by
    show FullSpace.vectorOpFn L k hL (_root_.YangMills.Construction.PeriodicOperators.extendByZero e 0) = _
    rw [extendByZero_zero]
  have hzg : coeffZero (colourEdges L k 0) (FullSpace.ghostIndices L k)
      (FullSpace.ghostIndices L k) Tg = FullSpace.ghostOpFn L k hL 0 := by
    show FullSpace.ghostOpFn L k hL (_root_.YangMills.Construction.PeriodicOperators.extendByZero e 0) = _
    rw [extendByZero_zero]
  obtain ⟨ρ₀, hρ₀, hreal⟩ := hRealT L hL hS k hk
  have hfield : ∀ f : (colourEdges L k 0).Carrier → ℂ, (∀ κ, (f κ).im = 0) →
      IsSupBelow (colourEdges L k 0) f ρ₀ →
      (∀ ι' ι, (Tv f ι' ι).im = 0) ∧ ∀ ι' ι, (Tg f ι' ι).im = 0 := by
    rintro f hf ⟨r, hr, hle⟩
    obtain ⟨ζ, hζ⟩ := (hVal L hL k).2.1 (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f)
    obtain ⟨-, -, -, e₄, e₅, -⟩ := (hVal L hL k).1 ζ
    have him : ∀ κ, (ζ.pauliCoeffs hL κ).im = 0 := by
      intro κ
      rw [hζ]
      rcases extendByZero_cases e f κ with h | ⟨a', h⟩
      · simp [h]
      · rw [h]
        exact hf a'
    have hbelow : IsSupBelow (FullSpace.fieldPeriodicData L k hL) (ζ.pauliCoeffs hL) ρ₀ := by
      refine ⟨max r 0, max_lt hr hρ₀, fun κ => ?_⟩
      rw [hζ]
      rcases extendByZero_cases e f κ with h | ⟨a', h⟩
      · simp [h]
      · rw [h]
        exact (hle a').trans (le_max_left _ _)
    have hrz := hreal ζ hbelow (isCompactValued_of_pauliCoeffs hL ζ him)
    have a₁ : Tv f = FullSpace.vectorOp ζ := by
      show FullSpace.vectorOpFn L k hL (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f) = _
      rw [← hζ, e₄]
    have a₂ : Tg f = FullSpace.ghostOp ζ := by
      show FullSpace.ghostOpFn L k hL (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f) = _
      rw [← hζ, e₅]
    rw [a₁, a₂]
    exact hrz
  have hrv : IsRealOnRealFields (colourEdges L k 0) (FullSpace.vectorIndices L k) Tv :=
    isRealOnRealFields_of_near hHol hρ₀ fun f hf hb => (hfield f hf hb).1
  have hrg : IsRealOnRealFields (colourEdges L k 0) (FullSpace.ghostIndices L k) Tg :=
    isRealOnRealFields_of_near hHol hρ₀ fun f hf hb => (hfield f hf hb).2
  obtain ⟨hl₁, hl₂, hr₁, hr₂⟩ := hLoc a ha L hS k hk
  have hsy₁ := fun κ => (hSym a ha L hS k hk κ).1
  have hsy₂ := fun κ => (hSym a ha L hS k hk κ).2
  obtain ⟨-, -, -, -, -, hrp₁⟩ := hLogdet _ _ hb0 hV _ hl₁ hsy₁
  obtain ⟨-, -, -, -, -, hrp₂⟩ := hLogdet _ _ hb0 hG _ hl₂ hsy₂
  obtain ⟨s₁, C₁, d₁', -, -, hd₁⟩ := hrp₁ hr₁
  obtain ⟨s₂, C₂, d₂', -, -, hd₂⟩ := hrp₂ hr₂
  obtain ⟨ρv, Rv, hMv⟩ := id hlv
  obtain ⟨ρg, Rg, hMg⟩ := id hlg
  have hMv' := (hNum _ _ _ hfd hV hV _ ρv Rv ρv Rv hMv hMv).1.1 ρv (max Rv Rg) hMv.radius_pos
    le_rfl (le_max_left _ _)
  have hMg' := (hNum _ _ _ hfd hG hG _ ρg Rg ρg Rg hMg hMg).1.1 ρg (max Rv Rg) hMg.radius_pos
    le_rfl (le_max_right _ _)
  obtain ⟨s₄, hs₄⟩ := exists_nat_gt (4 * max Rv Rg)
  have hsideTo : Tendsto (fun n => periodSide L n) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    have h1 : n < L ^ n := Nat.lt_pow_self (by have := hS.2; omega)
    simp only [periodSide, id]
    omega
  let D₁ : LocalLogDetTerm L k := ⟨FullSpace.vectorIndices L k,
    FullLattice.edgeSaddleOfForm a L k, -(1 / 2)⟩
  let D₂ : LocalLogDetTerm L k := ⟨FullSpace.ghostIndices L k,
    FullLattice.vertexSaddleOfForm L k, 1⟩
  let D₃ : LocalLogDetTerm L k := ⟨FullSpace.vectorIndices L k, Tv, 1 / 2⟩
  let D₄ : LocalLogDetTerm L k := ⟨FullSpace.ghostIndices L k, Tg, -1⟩
  refine ⟨[D₁, D₂, D₃, D₄], ?_, ?_⟩
  · intro D hD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl | rfl
    · exact ⟨hV, hl₁, hsy₁, hr₁⟩
    · exact ⟨hG, hl₂, hsy₂, hr₂⟩
    · refine ⟨hV, hlocv, fun κ => ?_, hrv⟩
      show IsUnit (symbolHom _ _ (coeffZero (colourEdges L k 0) (FullSpace.vectorIndices L k)
        (FullSpace.vectorIndices L k) Tv) (toComplexVec κ) : Module.End ℂ _)
      rw [hzv]
      exact isUnit_symbolHom_of_invertible hsv κ
    · refine ⟨hG, hlocg, fun κ => ?_, hrg⟩
      show IsUnit (symbolHom _ _ (coeffZero (colourEdges L k 0) (FullSpace.ghostIndices L k)
        (FullSpace.ghostIndices L k) Tg) (toComplexVec κ) : Module.End ℂ _)
      rw [hzg]
      exact isUnit_symbolHom_of_invertible hsg κ
  filter_upwards [hDesc a ha L hS k hk, eventually_gt_atTop 0, hsideTo.eventually_ge_atTop s₁,
    hsideTo.eventually_ge_atTop s₂, hsideTo.eventually_ge_atTop s₄] with n hdn hn hn₁ hn₂ hn₄
  obtain ⟨ε₁, hε₁, hread⟩ := hdn
  obtain ⟨hcells, hclasses⟩ := hCells L hS k n hn
  obtain ⟨hC0, -⟩ := hcells 0 (Nat.zero_le k)
  obtain ⟨hCk, -⟩ := hcells k le_rfl
  have rb0 := edges_classified hb0 hC0
  have rbk := edges_classified hbk hCk
  have rs0 := vertices_classified hs0 hC0
  have rsk := vertices_classified hsk hCk
  obtain ⟨φv, hφv⟩ := disjSum_classified hb0 hbk hV rb0.1 rbk.1 rb0.2 rbk.2
  obtain ⟨φg, hφg⟩ := disjSum_classified hs0 hsk hG rs0.1 rsk.1 rs0.2 rsk.2
  have hs' : 0 < periodSide L n := by
    have := pow_pos hL n
    simp only [periodSide]
    omega
  have finF : Finite ((colourEdges L k 0).QuotMod (periodSide L n)) :=
    (hQuot _ _ hb0 hb0 _ hs').1.2.1
  have finV : Finite ((FullSpace.vectorIndices L k).QuotMod (periodSide L n)) :=
    (hQuot _ _ hV hV _ hs').1.2.1
  have finG : Finite ((FullSpace.ghostIndices L k).QuotMod (periodSide L n)) :=
    (hQuot _ _ hG hG _ hs').1.2.1
  have fV : Finite (Fin 3 × PositiveEdge L n k 0 ⊕ Fin 3 × PositiveEdge L n k k) :=
    Finite.of_equiv _ φv
  have fG : Finite (Fin 3 × Vertex L n k 0 ⊕ Fin 3 × Vertex L n k k) := Finite.of_equiv _ φg
  have f1 : Finite (Fin 3 × PositiveEdge L n k 0) :=
    Finite.of_injective (β := Fin 3 × PositiveEdge L n k 0 ⊕ Fin 3 × PositiveEdge L n k k)
      Sum.inl Sum.inl_injective
  have f2 : Finite (Fin 3 × PositiveEdge L n k k) :=
    Finite.of_injective (β := Fin 3 × PositiveEdge L n k 0 ⊕ Fin 3 × PositiveEdge L n k k)
      Sum.inr Sum.inr_injective
  have f3 : Finite (Fin 3 × Vertex L n k 0) :=
    Finite.of_injective (β := Fin 3 × Vertex L n k 0 ⊕ Fin 3 × Vertex L n k k)
      Sum.inl Sum.inl_injective
  have f4 : Finite (Fin 3 × Vertex L n k k) :=
    Finite.of_injective (β := Fin 3 × Vertex L n k 0 ⊕ Fin 3 × Vertex L n k k)
      Sum.inr Sum.inr_injective
  let _ := Fintype.ofFinite (Fin 3 × PositiveEdge L n k 0)
  let _ := Fintype.ofFinite (Fin 3 × PositiveEdge L n k k)
  let _ := Fintype.ofFinite (Fin 3 × Vertex L n k 0)
  let _ := Fintype.ofFinite (Fin 3 × Vertex L n k k)
  have hX : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => h₉ L n k hS hn hk0 0 (Nat.zero_le k) b
  obtain ⟨c₁, hc₁, e₁⟩ := h₁ a ha L hS k n hk hn
  obtain ⟨c₂, hc₂, e₂⟩ := h₂ L hS k n hk hn
  obtain ⟨ε₂, hε₂, n₂⟩ := eventually_of_small_form hX rb0.1 e₁
  obtain ⟨ε₃, hε₃, n₃⟩ := eventually_of_small_form hX rb0.1 e₂
  obtain ⟨ε₄, hε₄, hfun⟩ := hFunc (max Rv Rg) ⟨ρv, hMv'⟩ ⟨ρg, hMg'⟩ n hn
    (lt_of_lt_of_le hs₄ (by exact_mod_cast hn₄))
  obtain ⟨ε₅, hε₅, d₁⟩ := det_ne_zero_of_small (fun N e' => (hd₁ _ hn₁ N e').1)
  obtain ⟨ε₆, hε₆, d₂⟩ := det_ne_zero_of_small (fun N e' => (hd₂ _ hn₂ N e').1)
  refine ⟨-(1 / 2) * Real.log c₁ + Real.log c₂, min ε₁ (min ε₂ (min ε₃ (min ε₄ (min ε₅ ε₆)))),
    by simp [hε₁, hε₂, hε₃, hε₄, hε₅, hε₆], fun r g hr hg => ?_⟩
  have g₁ : ∀ x, |g x| < ε₁ := fun x => (hg x).trans_le (min_le_left _ _)
  have g₂ : ∀ x, |g x| < ε₂ := fun x =>
    (hg x).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have g₃ : ∀ x, |g x| < ε₃ := fun x =>
    (hg x).trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have g₄ : ∀ x, |g x| < ε₄ := fun x =>
    (hg x).trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have g₅ : ∀ x, |g x| < ε₅ := fun x =>
    (hg x).trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have g₆ : ∀ x, |g x| < ε₆ := fun x =>
    (hg x).trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  set U := PeriodicLattice.expTwist (r : Edge L n k 0 → Matrices.ComplexMatrix2)
    (trivialField L n k 0) with hU
  obtain ⟨ra, rb⟩ := hread r g hr g₁
  have m₁ := det_quotOperator_of_periodizesTo φv (im := edgeIndexProj L n k) (fun ι => hφv ι) ra
  have m₂ := det_quotOperator_of_periodizesTo φg (im := ghostIndexProj L n k) (fun ι => hφg ι) rb
  have nz₁ : Matrix.det (saddleMatrix a U) ≠ 0 := by
    rw [← m₁]
    exact d₁ g g₅
  have nz₂ : Matrix.det (ghostMatrix U) ≠ 0 := by
    rw [← m₂]
    exact d₂ g g₆
  have hS₁ := n₂ r g hr g₂
  have hS₂ := n₃ r g hr g₃
  have hmem : (r : Edge L n k 0 → Matrices.ComplexMatrix2) ∈ complexEdgeForms L n k 0 :=
    ⟨fun b hb => (r.2.1 b hb).2, r.2.2⟩
  let ζ : PeriodicField L n k := (⟨_, hmem⟩, 0, 0)
  let rt : RealPeriodicField L n k := (r, 0, 0)
  have hzr : ζ.RealizedBy rt := ⟨rfl, rfl, rfl⟩
  have hco : ∀ ι : (colourEdges L k 0).Carrier, ζ.pauliCoeffs hL ⟨.background, ι⟩ =
      ((g ((colourEdges L k 0).mkQuot (periodSide L n) ι) : ℝ) : ℂ) := fun ι => (hr ι).symm
  have hc2 : ∀ ι : (colourEdges L k 0).Carrier, ζ.pauliCoeffs hL ⟨.source, ι⟩ = 0 := fun ι =>
    pauliCoeff_zero _
  have hc3 : ∀ ι : (colourEdges L k k).Carrier, ζ.pauliCoeffs hL ⟨.coarse, ι⟩ = 0 := fun ι =>
    pauliCoeff_zero _
  have hne : Nonempty ((colourEdges L k 0).QuotMod (periodSide L n)) :=
    ⟨(colourEdges L k 0).mkQuot _ (0, ⟨InfiniteLattice.Link.forwardFrom 0 0, 0, by
      simp [InfiniteLattice.Link.forwardFrom]⟩)⟩
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max fun x => |g x|
  have hbelow : IsSupBelow (FullSpace.fieldPeriodicData L k hL) (ζ.pauliCoeffs hL) ε₄ := by
    refine ⟨|g x₀|, g₄ x₀, ?_⟩
    rintro ⟨p, ι⟩
    cases p with
    | background =>
      rw [hco ι, Complex.norm_real, Real.norm_eq_abs]
      exact hx₀ _
    | source =>
      rw [hc2 ι, norm_zero]
      exact abs_nonneg _
    | coarse =>
      rw [hc3 ι, norm_zero]
      exact abs_nonneg _
  obtain ⟨-, hvalF⟩ := hfun ζ rt hzr hbelow
  have hcl := liftQuotField_onQuotient hL (hclasses (LocalKernels.fieldIndices L k hL)) ζ
  have hfe : liftQuotField (FullSpace.fieldPeriodicData L k hL) (2 * L ^ n) (ζ.onQuotient hL) =
      _root_.YangMills.Construction.PeriodicOperators.extendByZero e (liftQuotField (colourEdges L k 0) (periodSide L n)
        fun x => ((g x : ℝ) : ℂ)) := by
    rw [hcl]
    funext κ
    obtain ⟨p, ι⟩ := κ
    cases p with
    | background =>
      rw [hco ι]
      unfold PeriodicOperators.extendByZero
      exact (hemb.injective.extend_apply (liftQuotField (colourEdges L k 0) (periodSide L n)
        fun x => ((g x : ℝ) : ℂ)) 0 ι).symm
    | source =>
      rw [hc2 ι]
      unfold PeriodicOperators.extendByZero
      refine (Function.extend_apply' (liftQuotField (colourEdges L k 0) (periodSide L n)
        fun x => ((g x : ℝ) : ℂ)) (0 : (FullSpace.fieldPeriodicData L k hL).Carrier → ℂ) _ ?_).symm
      rintro ⟨b, hb⟩
      cases hb
    | coarse =>
      rw [hc3 ι]
      unfold PeriodicOperators.extendByZero
      refine (Function.extend_apply' (liftQuotField (colourEdges L k 0) (periodSide L n)
        fun x => ((g x : ℝ) : ℂ)) (0 : (FullSpace.fieldPeriodicData L k hL).Carrier → ℂ) _ ?_).symm
      rintro ⟨b, hb⟩
      cases hb
  have t₃ : LogDetSecondDerivs.quotOperator (FullSpace.fieldPeriodicData L k hL)
      (FullSpace.vectorIndices L k) (FullSpace.vectorOpFn L k hL) (2 * L ^ n) (ζ.onQuotient hL) =
      LogDetSecondDerivs.quotOperator (colourEdges L k 0)
        (FullSpace.vectorIndices L k) Tv (periodSide L n) fun x => ((g x : ℝ) : ℂ) := by
    simp only [LogDetSecondDerivs.quotOperator, periodicValue]
    rw [hfe]
    rfl
  have t₄ : LogDetSecondDerivs.quotOperator (FullSpace.fieldPeriodicData L k hL)
      (FullSpace.ghostIndices L k) (FullSpace.ghostOpFn L k hL) (2 * L ^ n) (ζ.onQuotient hL) =
      LogDetSecondDerivs.quotOperator (colourEdges L k 0)
        (FullSpace.ghostIndices L k) Tg (periodSide L n) fun x => ((g x : ℝ) : ℂ) := by
    simp only [LogDetSecondDerivs.quotOperator, periodicValue]
    rw [hfe]
    rfl
  have hfunctional : backgroundFunctional U 0 0 =
      -(1 / 2) * Real.log ‖LinearMap.det (LogDetSecondDerivs.quotOperator
          (colourEdges L k 0) (FullSpace.vectorIndices L k) Tv (periodSide L n)
          fun x => ((g x : ℝ) : ℂ))‖ +
        Real.log ‖LinearMap.det (LogDetSecondDerivs.quotOperator
          (colourEdges L k 0) (FullSpace.ghostIndices L k) Tg (periodSide L n)
          fun x => ((g x : ℝ) : ℂ))‖ := by
    have h := hvalF
    simp only [FullSpace.OperatorFunctions.logDetCombination] at h
    rw [t₃, t₄] at h
    exact h
  have nc₁ : Matrix.det (saddleMatrix a U) ≠ 0 := nz₁
  have hlog₁ : Real.log |levelSaddleDet (gaugedOperator a (quietPoint U) 0 0)
      (shiftedGaugeMap (quietPoint U))| = Real.log c₁ + 3 * logRadiusSum (quietPoint U) +
        Real.log ‖Matrix.det (saddleMatrix a U)‖ := by
    rw [hS₁, Real.log_mul (by positivity) (norm_ne_zero_iff.2 nz₁),
      Real.log_mul hc₁.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlog₂ : Real.log |LinearMap.det (ghostBlockOperator (quietPoint U))| = Real.log c₂ +
      Real.log ‖Matrix.det (ghostMatrix U)‖ := by
    rw [hS₂, Real.log_mul hc₂.ne' (norm_ne_zero_iff.2 nz₂)]
  have hsoft : chainFreeEnergy a (quietPoint U) 0 0 = -(1 / 2) * Real.log c₁ + Real.log c₂ -
      1 / 2 * Real.log ‖Matrix.det (saddleMatrix a U)‖ +
      Real.log ‖Matrix.det (ghostMatrix U)‖ := by
    rw [chainFreeEnergy, hlog₁, hlog₂]
    ring
  show chainMinusBackground a U = _
  rw [chainMinusBackground, hsoft, hfunctional]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, LocalLogDetTerm.eval]
  change _ = (-(1 / 2) : ℝ) * Real.log ‖LinearMap.det
        (LogDetSecondDerivs.quotOperator (colourEdges L k 0)
          (FullSpace.vectorIndices L k) (FullLattice.edgeSaddleOfForm a L k) (periodSide L n)
          fun x => ((g x : ℝ) : ℂ))‖ +
      ((1 : ℝ) * Real.log ‖LinearMap.det
        (LogDetSecondDerivs.quotOperator (colourEdges L k 0)
          (FullSpace.ghostIndices L k) (FullLattice.vertexSaddleOfForm L k) (periodSide L n)
          fun x => ((g x : ℝ) : ℂ))‖ +
      ((1 / 2 : ℝ) * Real.log ‖LinearMap.det
        (LogDetSecondDerivs.quotOperator (colourEdges L k 0)
          (FullSpace.vectorIndices L k) Tv (periodSide L n) fun x => ((g x : ℝ) : ℂ))‖ +
      ((-1 : ℝ) * Real.log ‖LinearMap.det
        (LogDetSecondDerivs.quotOperator (colourEdges L k 0)
          (FullSpace.ghostIndices L k) Tg (periodSide L n) fun x => ((g x : ℝ) : ℂ))‖ + 0))) +
      (-(1 / 2) * Real.log c₁ + Real.log c₂)
  rw [m₁, m₂]
  ring
end YangMills.Construction.RunningCouplingSlope.LocalLogDetSum
end
