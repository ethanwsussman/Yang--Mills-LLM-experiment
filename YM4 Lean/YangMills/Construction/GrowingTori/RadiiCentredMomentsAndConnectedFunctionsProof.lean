import YangMills.Construction.Cumulants.CumulantsOfALinearMapIntoBoundedRandomVariables
import YangMills.Construction.GrowingTori.RadiiCentredMomentsAndConnectedFunctions
import YangMills.Construction.GrowingTori.TransportThroughABallToTheTorusOfAnExponent
import YangMills.Construction.Lattice.LatticeAsAProbabilitySpace
import Mathlib
set_option autoImplicit false
open Filter Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ToriLimits.MomentsAndConnected
open Probability (IsBoundedRealRV IsBoundedComplexRV)
open LatticeProbability (GaugeConfig gibbsMeasureOn observableOn)
theorem sum_prod_singletonFree_zero {R : Type*} [CommRing R]
    (g : SetPartition.PartitionsFin 0 → Finset (Fin 0) → R) :
    ∑ π ∈ SetPartition.singletonFree 0, ∏ B ∈ π.parts, g π B = 1 := by
  have hp : ∀ P : SetPartition.PartitionsFin 0, P.parts = ∅ :=
    fun P => SetPartition.parts_eq_empty_of_empty P
  have h : SetPartition.singletonFree 0 = {⊥} :=
    Finset.eq_singleton_iff_unique_mem.2 ⟨SetPartition.mem_singletonFree_zero _,
      fun P _ => Finpartition.ext ((hp P).trans (hp ⊥).symm)⟩
  rw [h, Finset.sum_singleton, hp, Finset.prod_empty]
abbrev standingParams (D : Setup) (K m : ℕ+) : Conventions.StandingParameters :=
  ⟨D.L, D.admissible, K, m⟩
structure ConnectedProperties (D : Setup) (K m : ℕ+) (β : ℝ) : Prop where
  im_eq_zero : ∀ {n : ℕ}, 1 ≤ n → ∀ f : Fin n → PeriodicLattice.FourTorus D.L m → ℝ,
    (D.connectedOnTorus K m β f).im = 0
  perm : ∀ {n : ℕ}, 1 ≤ n → ∀ (f : Fin n → PeriodicLattice.FourTorus D.L m → ℝ)
    (σ : Equiv.Perm (Fin n)),
    D.connectedOnTorus K m β (fun i => f (σ i)) = D.connectedOnTorus K m β f
  add : ∀ {n : ℕ}, 1 ≤ n → ∀ (f : Fin n → PeriodicLattice.FourTorus D.L m → ℝ) (i : Fin n)
    (g g' : PeriodicLattice.FourTorus D.L m → ℝ),
    D.connectedOnTorus K m β (Function.update f i (g + g')) =
      D.connectedOnTorus K m β (Function.update f i g) +
        D.connectedOnTorus K m β (Function.update f i g')
  smul : ∀ {n : ℕ}, 1 ≤ n → ∀ (f : Fin n → PeriodicLattice.FourTorus D.L m → ℝ) (i : Fin n) (a : ℝ)
    (g : PeriodicLattice.FourTorus D.L m → ℝ),
    D.connectedOnTorus K m β (Function.update f i (a • g)) =
      (a : ℂ) * D.connectedOnTorus K m β (Function.update f i g)
  moment : ∀ (q : ℕ) (t : Fin q → PeriodicLattice.FourTorus D.L m → ℝ),
    ((D.expectation K m β (fun U => ∏ l, (PeriodicLattice.smearedObservable (t l) U -
        D.expectation K m β (PeriodicLattice.smearedObservable (t l)))) : ℝ) : ℂ) =
      ∑ π ∈ SetPartition.singletonFree q, ∏ J ∈ π.parts,
        D.connectedOnTorus K m β (fun k : Fin J.card => t (J.orderEmbOfFin rfl k))
theorem isBoundedRealRV_prod_sub {Ω : Type*} [MeasurableSpace Ω] {q : ℕ} {X : Fin q → Ω → ℝ}
    (hX : ∀ l, IsBoundedRealRV (X l)) (c : Fin q → ℝ) :
    IsBoundedRealRV fun ω => ∏ l, (X l ω - c l) := by
  refine ⟨Finset.measurable_prod _ fun l _ => (hX l).measurable.sub_const _, ?_⟩
  choose C hC using fun l => (hX l).bounded
  refine ⟨∏ l, (C l + |c l|), fun ω => ?_⟩
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun l _ =>
    (abs_sub _ _).trans (add_le_add_left (hC l ω) _)
theorem connectedProperties (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hC : Cumulants.LinearMapCumulantProperties)
    (D : Setup) (K m : ℕ+) {β : ℝ} (hβ : 0 < β) : ConnectedProperties D K m β := by
  obtain ⟨⟨-, -, hprob, -, -, hexp⟩, -, -, ⟨hbdd, -, ⟨𝓑, T, -, hT⟩, -⟩, hcum, -⟩ :=
    hP (standingParams D K m) β hβ
  have := hprob
  let O : (PeriodicLattice.FourTorus D.L m → ℝ) →ₗ[ℝ] (GaugeConfig (standingParams D K m) → ℝ) :=
    𝓑.subtype ∘ₗ T
  have hO : ∀ f, O f = observableOn (standingParams D K m) f := hT
  have hOb : ∀ f, IsBoundedRealRV (O f) := fun f => by
    rw [hO]
    exact hbdd f
  obtain ⟨ha, -, hb⟩ := hC _ (gibbsMeasureOn (standingParams D K m) β) _ O hOb
  have conn : ∀ {n : ℕ}, 1 ≤ n → ∀ f : Fin n → PeriodicLattice.FourTorus D.L m → ℝ,
      D.connectedOnTorus K m β f =
        Cumulants.linearMapCumulant (gibbsMeasureOn (standingParams D K m) β) O f := by
    intro n hn f
    refine (hcum n f hn).1.trans ?_
    unfold Cumulants.linearMapCumulant
    congr 1
    funext i
    exact (hO _).symm
  have expct : ∀ F : (PeriodicLattice.Bond D.L m ((K : ℕ) : ℤ) → Matrices.ComplexMatrix2) → ℝ,
      IsBoundedRealRV (fun U : GaugeConfig (standingParams D K m) => F U.1) →
      ((D.expectation K m β F : ℝ) : ℂ) =
        Probability.complexExpectation (gibbsMeasureOn (standingParams D K m) β)
          fun U => ((F U.1 : ℝ) : ℂ) := by
    intro F hF
    obtain ⟨C, hC'⟩ := hF.bounded
    have hb' : IsBoundedComplexRV
        (fun U : GaugeConfig (standingParams D K m) => ((F U.1 : ℝ) : ℂ)) :=
      ⟨by simpa using hF.measurable, by simp, ⟨C, fun ω => by simpa using hC' ω⟩⟩
    rw [← hexp (fun U => ((F U : ℝ) : ℂ)) hb']
    exact (integral_ofReal (f := F)).symm
  refine ⟨fun hn f => ?_, fun hn f σ => ?_, fun hn f i g g' => ?_, fun hn f i a g => ?_,
    fun q t => ?_⟩
  · rw [conn hn]
    exact (ha _ hn).1 f
  · rw [conn hn, conn hn]
    exact (ha _ hn).2.1 f σ
  · rw [conn hn, conn hn, conn hn]
    exact (ha _ hn).2.2.1 f i g g'
  · rw [conn hn, conn hn]
    exact (ha _ hn).2.2.2 f i a g
  · have hc : ∀ l, ((D.expectation K m β (PeriodicLattice.smearedObservable (t l)) : ℝ) : ℂ) =
        Probability.complexExpectation (gibbsMeasureOn (standingParams D K m) β)
          fun ω => ((O (t l) ω : ℝ) : ℂ) := by
      intro l
      refine (expct _ (hbdd (t l))).trans ?_
      rw [hO]
      rfl
    have hO' : ∀ l (U : GaugeConfig (standingParams D K m)),
        O (t l) U = PeriodicLattice.smearedObservable (t l) U.1 := fun l U => by
      rw [hO]
      rfl
    have hprod := isBoundedRealRV_prod_sub (fun l => hOb (t l))
      (fun l => D.expectation K m β (PeriodicLattice.smearedObservable (t l)))
    have hprod' : IsBoundedRealRV
        (fun U : GaugeConfig (standingParams D K m) => ∏ l, (PeriodicLattice.smearedObservable (t l) U.1 -
          D.expectation K m β (PeriodicLattice.smearedObservable (t l)))) := by
      simpa only [hO'] using hprod
    rw [expct _ hprod']
    have h₁ := hb q t
    refine Eq.trans ?_ (h₁.trans (Finset.sum_congr rfl fun π _ =>
      Finset.prod_congr rfl fun J hJ => (conn ?_ _).symm))
    · refine congrArg (Probability.complexExpectation _) ?_
      funext ω
      push_cast
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [← hc l, hO']
    · exact Finset.card_pos.2 (π.nonempty_of_mem_parts hJ)
theorem periodizeAll_update {L m n : ℕ} (h : Fin n → RealFn) (i : Fin n) (x : RealFn) :
    SchwingerFunctions.periodizeAll L m (Function.update h i x) =
      Function.update (SchwingerFunctions.periodizeAll L m h) i
        (TestFunctions.periodize (PeriodicLattice.torusSide L m) x) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [SchwingerFunctions.periodizeAll]
  · simp [SchwingerFunctions.periodizeAll, Function.update_of_ne hk]
theorem connected_update_linear (hT : ExponentTorusPeriodization.Statement) {D : Setup}
    {K m : ℕ+} {β ρ : ℝ} (hF : ConnectedProperties D K m β) (hρ : 0 < ρ)
    (hle : ρ ≤ ((D.L : ℝ) ^ (m : ℕ) - 2) / 2) {n : ℕ} (hn : 1 ≤ n)
    (h : Fin n → RealFn) (i : Fin n) {g g' : RealFn}
    (hg : SupportedIn g (ballOrigin ρ)) (hg' : SupportedIn g' (ballOrigin ρ)) (c c' : ℝ) :
    D.connectedOnFourSpace K m β (Function.update h i (c • g + c' • g')) =
      (c : ℂ) * D.connectedOnFourSpace K m β (Function.update h i g) +
        (c' : ℂ) * D.connectedOnFourSpace K m β (Function.update h i g') := by
  have hlin := (((hT D m).2 ρ hρ hle).2.1 ℝ).1.2 g g' c c' hg hg'
  unfold Setup.connectedOnFourSpace
  rw [periodizeAll_update, periodizeAll_update, periodizeAll_update, hlin.2, hF.add hn,
    hF.smul hn, hF.smul hn]
theorem connected_update_add (hT : ExponentTorusPeriodization.Statement) {D : Setup}
    {K m : ℕ+} {β ρ : ℝ} (hF : ConnectedProperties D K m β) (hρ : 0 < ρ)
    (hle : ρ ≤ ((D.L : ℝ) ^ (m : ℕ) - 2) / 2) {n : ℕ} (hn : 1 ≤ n)
    (h : Fin n → RealFn) (i : Fin n) {g g' : RealFn}
    (hg : SupportedIn g (ballOrigin ρ)) (hg' : SupportedIn g' (ballOrigin ρ)) :
    D.connectedOnFourSpace K m β (Function.update h i (g + g')) =
      D.connectedOnFourSpace K m β (Function.update h i g) +
        D.connectedOnFourSpace K m β (Function.update h i g') := by
  simpa using connected_update_linear hT hF hρ hle hn h i hg hg' 1 1
theorem connected_update_smul (hT : ExponentTorusPeriodization.Statement) {D : Setup}
    {K m : ℕ+} {β ρ : ℝ} (hF : ConnectedProperties D K m β) (hρ : 0 < ρ)
    (hle : ρ ≤ ((D.L : ℝ) ^ (m : ℕ) - 2) / 2) {n : ℕ} (hn : 1 ≤ n)
    (h : Fin n → RealFn) (i : Fin n) {g : RealFn}
    (hg : SupportedIn g (ballOrigin ρ)) (a : ℝ) :
    D.connectedOnFourSpace K m β (Function.update h i (a • g)) =
      (a : ℂ) * D.connectedOnFourSpace K m β (Function.update h i g) := by
  simpa using connected_update_linear hT hF hρ hle hn h i hg hg a 0
theorem centred_eq_partitionSum (D : Setup) (K m : ℕ+) (β : ℝ) {q : ℕ}
    (h : Fin q → RealFn) :
    D.centredOnFourSpace K m β h = D.partitionSumOfConnected K m β h := by
  match q, h with
  | 0, h =>
    unfold Setup.partitionSumOfConnected
    rw [sum_prod_singletonFree_zero
      (fun _ B => D.connectedOnFourSpace K m β (subfamily h B))]
    rfl
  | 1, h =>
    unfold Setup.partitionSumOfConnected
    rw [SetPartition.singletonFree_one, Finset.sum_empty]
    rfl
  | q + 2, h =>
    unfold Setup.partitionSumOfConnected
    change SchwingerFunctions.partitionSum (fun _ g => SchwingerFunctions.connectedSchwinger D.L m K β g)
      (SchwingerFunctions.periodizeAll D.L m h) = _
    unfold SchwingerFunctions.partitionSum
    rw [SetPartition.singletonFree_eq_nonSingletonPartitions]
    refine Finset.sum_congr ?_ fun π _ => Finset.prod_congr rfl fun B _ => rfl
    ext π
    simp [SetPartition.nonSingletonPartitions]
theorem moments_eq {D : Setup} {K m : ℕ+} {β : ℝ} (hF : ConnectedProperties D K m β) {q : ℕ}
    (h : Fin q → RealFn) :
    D.centredOnFourSpace K m β h = (D.centredProductExpectation K m β h : ℝ) ∧
      ((D.centredProductExpectation K m β h : ℝ) : ℂ) =
        D.partitionSumOfConnected K m β h := by
  have h₁ : ((D.centredProductExpectation K m β h : ℝ) : ℂ) =
      D.partitionSumOfConnected K m β h := hF.moment q (SchwingerFunctions.periodizeAll D.L m h)
  exact ⟨(centred_eq_partitionSum D K m β h).trans h₁.symm, h₁⟩
theorem ofReal_re_connected {D : Setup} {K m : ℕ+} {β : ℝ} (hF : ConnectedProperties D K m β)
    {n : ℕ} (hn : 1 ≤ n) (f : Fin n → RealFn) :
    (((D.connectedOnFourSpace K m β f).re : ℝ) : ℂ) = D.connectedOnFourSpace K m β f := by
  have h : (D.connectedOnFourSpace K m β f).im = 0 :=
    hF.im_eq_zero hn (SchwingerFunctions.periodizeAll D.L m f)
  exact Complex.ext (by simp) (by simp [h])
theorem connected_perm {D : Setup} {K m : ℕ+} {β : ℝ} (hF : ConnectedProperties D K m β) {n : ℕ}
    (hn : 1 ≤ n) (f : Fin n → RealFn) (σ : Equiv.Perm (Fin n)) :
    D.connectedOnFourSpace K m β (fun i => f (σ i)) = D.connectedOnFourSpace K m β f :=
  hF.perm hn (SchwingerFunctions.periodizeAll D.L m f) σ
theorem supportedIn_of_mem {ρ : ℝ} {hρ : 0 < ρ} {n : ℕ} {h : Fin n → RealFn}
    (hh : h ∈ sepLipTuplesInBall n ρ hρ) (i : Fin n) :
    SupportedIn (h i) (ballOrigin ρ) :=
  ⟨hh.1.2.1 i, hh.2 i⟩
theorem supportedIn_of_mem_lipSubmodule {L : ℕ} {A : Set (Fin 4 → ℝ)} {ρ : ℝ}
    (hA : A ⊆ ballOrigin ρ)
    (x : (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).lipSubmodule A) :
    SupportedIn x.1 (ballOrigin ρ) := by
  have hcc : ∀ A : Set (Fin 4 → ℝ),
      (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).IsEuclidCompact A ↔ IsCompact A := by
    intro A
    change @IsCompact _ (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).topology A ↔ _
    rw [ambient_topology_eq]
    exact Iff.rfl
  have hx : x.1 ∈ (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).lipCompact A :=
    x.2
  obtain ⟨-, hc, hs⟩ := hx
  have e := ambient_supp_eq L (x.1 : RealFn)
  have hs' : fnSupport (x.1 : RealFn) ⊆ A := by
    rw [← e]
    exact hs
  exact ⟨(hcc _).1 (by rw [← e]; exact hc), hs'.trans hA⟩
theorem isClassMultilinear_connected (hT : ExponentTorusPeriodization.Statement) {D : Setup}
    {K m : ℕ+} {β ρ : ℝ} (hF : ConnectedProperties D K m β) (hρ : 0 < ρ)
    (hle : ρ ≤ ((D.L : ℝ) ^ (m : ℕ) - 2) / 2) {n : ℕ} (hn : 1 ≤ n) :
    IsClassMultilinear (D.transportData K m) (.ball ρ hρ) hn
      (fun f => (D.connectedOnFourSpace K m β f.1).re) := by
  intro i h h' hagree c c' hmem
  have e₁ : Function.update h.1 i (h.1 i) = h.1 := Function.update_eq_self _ _
  have e₂ : Function.update h.1 i (h'.1 i) = h'.1 := by
    funext k
    by_cases hk : k = i
    · subst hk
      exact Function.update_self _ _ _
    · exact (Function.update_of_ne hk _ _).trans (hagree k hk)
  have h₁ := connected_update_linear hT hF hρ hle hn h.1 i (supportedIn_of_mem (hρ := hρ) h.2 i)
    (supportedIn_of_mem (hρ := hρ) h'.2 i) c c'
  have h₂ := h₁.trans (congrArg₂ (fun u v => (c : ℂ) * u + (c' : ℂ) * v)
    (congrArg (D.connectedOnFourSpace K m β) e₁) (congrArg (D.connectedOnFourSpace K m β) e₂))
  refine (congrArg Complex.re h₂).trans ?_
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  rfl
theorem isMultilinearOnTuples_connected (hT : ExponentTorusPeriodization.Statement)
    {D : Setup} {K m : ℕ+} {β ρ : ℝ} (hF : ConnectedProperties D K m β) (hρ : 0 < ρ)
    (hle : ρ ≤ ((D.L : ℝ) ^ (m : ℕ) - 2) / 2) {n : ℕ} (hn : 2 ≤ n) :
    GrowingTori.IsMultilinearOnTuples (L := D.L) hn (r := ρ)
      (fun f => (D.connectedOnFourSpace K m β f.1).re) := by
  intro A hball hA
  have hsup := fun i x => supportedIn_of_mem_lipSubmodule (L := D.L) (hball i) x
  have e : ∀ (f : (i : Fin n) → (GrowingTori.Ambient.euclidean :
        GrowingTori.Ambient D.L).lipSubmodule (A i)) (i : Fin n)
      (z : (GrowingTori.Ambient.euclidean : GrowingTori.Ambient D.L).lipSubmodule (A i)),
      (fun k => (Function.update f i z k).1) = Function.update (fun k => (f k).1) i z.1 := by
    intro f i z
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Function.update_of_ne hk]
  refine ⟨{ toFun := fun f => (D.connectedOnFourSpace K m β fun i => (f i).1).re
            map_update_add' := ?_
            map_update_smul' := ?_ }, fun f => rfl⟩
  · intro inst f i x y
    obtain rfl : inst = fun a b => instDecidableEqFin n a b := Subsingleton.elim _ _
    have h₁ := connected_update_add hT hF hρ hle (by omega : 1 ≤ n) (fun k => (f k).1) i
      (hsup i x) (hsup i y)
    change (D.connectedOnFourSpace K m β fun k => (Function.update f i (x + y) k).1).re =
      (D.connectedOnFourSpace K m β fun k => (Function.update f i x k).1).re +
        (D.connectedOnFourSpace K m β fun k => (Function.update f i y k).1).re
    rw [e, e, e]
    exact (congrArg Complex.re h₁).trans (Complex.add_re _ _)
  · intro inst f i a x
    obtain rfl : inst = fun a b => instDecidableEqFin n a b := Subsingleton.elim _ _
    have h₁ := connected_update_smul hT hF hρ hle (by omega : 1 ≤ n) (fun k => (f k).1) i
      (hsup i x) a
    change (D.connectedOnFourSpace K m β fun k => (Function.update f i (a • x) k).1).re =
      a • (D.connectedOnFourSpace K m β fun k => (Function.update f i x k).1).re
    rw [e, e]
    exact (congrArg Complex.re h₁).trans (by rw [Complex.re_ofReal_mul, smul_eq_mul]; rfl)
theorem radiusProperties {D : Setup} (S : ToriSequence D) : RadiusProperties S := by
  have hL : (1 : ℝ) < D.L := by exact_mod_cast D.one_lt_L
  refine ⟨S.radius_pos, ?_, fun j ρ _ => ?_⟩
  · have h₁ : Tendsto (fun j => (D.L : ℝ) ^ (S.m j : ℕ)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hL).comp S.m_tendsto
    have h₂ : Tendsto (fun j => (D.L : ℝ) ^ (S.m j : ℕ) + (-2)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ h₁
    have h₃ := h₂.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    refine h₃.congr fun j => ?_
    simp only [ToriSequence.radius]
    ring
  · unfold ToriSequence.radius
    constructor <;> intro h <;> linarith
theorem momentBoundLowOrders_holds : MomentBoundLowOrders := by
  intro C d R _ _
  refine ⟨?_, ?_⟩
  · exact sum_prod_singletonFree_zero (fun _ B => C.val B.card d R)
  · unfold momentBoundSum
    rw [SetPartition.singletonFree_one, Finset.sum_empty]
theorem holds (hT : ExponentTorusPeriodization.Statement)
    (hP : LatticeProbability.ProbabilitySpaceTheorem.claim)
    (hC : Cumulants.LinearMapCumulantProperties) : Statement := by
  intro D S
  refine ⟨radiusProperties S, ?_, ?_, momentBoundLowOrders_holds, ?_, ?_⟩
  · intro K m β ρ hβ _ _ q h _
    exact moments_eq (connectedProperties hP hC D K m hβ) h
  · intro j q h _
    exact moments_eq (connectedProperties hP hC D (S.K j) (S.m j) (S.β_pos j)) h
  · intro K m β ρ hβ hρ hle n hn
    have hF := connectedProperties hP hC D K m hβ
    have hn₁ : 1 ≤ n := by omega
    refine ⟨fun f => (D.connectedOnFourSpace K m β f.1).re,
      fun f => ofReal_re_connected hF hn₁ _, fun σ h => ?_,
      isClassMultilinear_connected hT hF hρ hle hn₁⟩
    exact congrArg Complex.re (connected_perm hF hn₁ h.1 σ)
  · intro j
    have hF := connectedProperties hP hC D (S.K j) (S.m j) (S.β_pos j)
    have hle : S.radius j ≤ ((D.L : ℝ) ^ (S.m j : ℕ) - 2) / 2 := le_rfl
    refine ⟨{ radius_pos := S.radius_pos j
              phi := fun n _ f => (S.connected j f.1).re
              phi_symm := fun n hn σ f => ?_
              phi_multilinear := fun n hn => isMultilinearOnTuples_connected hT hF (S.radius_pos j)
                hle hn }, fun n hn f => ofReal_re_connected hF (by omega) _, fun q h => ?_⟩
    · exact congrArg Complex.re (connected_perm hF (by omega) f.1 σ)
    · refine (centred_eq_partitionSum D _ _ _ h.1).trans ?_
      unfold Setup.partitionSumOfConnected centredMomentOf
      push_cast
      rw [← Finset.sum_attach]
      refine Finset.sum_congr rfl fun π _ => ?_
      rw [← Finset.prod_attach π.1.parts]
      refine Finset.prod_congr rfl fun B _ => ?_
      have hB := PeriodicSpace.two_le_card_of_mem_singletonFree π.2 B.2
      exact (ofReal_re_connected hF (by omega) _).symm
end YangMills.Construction.ToriLimits.MomentsAndConnected
end
