import YangMills.Construction.ReflectionPositivity.DenseSetOfMirrorsThenContinuityInThePosition
import YangMills.Construction.ReflectionPositivity.InequalityPassesToTheLimitAtFixedTuplesProof
import YangMills.Construction.ReflectionPositivity.MirrorThatMovesWithTheCutoff
import YangMills.Construction.ReflectionPositivity.NestedLatticesAdicPointsAndMirrorsProof
import YangMills.Construction.ReflectionPositivity.PositivityInTheLimits
import YangMills.Construction.ReflectionPositivity.PositivityOfTheWilsonMeasureAtALinkMirror
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ComplexConjugate ComplexOrder ENNReal Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.LimitPositivity
open Ambient
theorem positivity_on_torus (hM : MovingMirror.MovingMirrorLimit) : OnTorus := by
  rintro D S T hST ⟨μ, c⟩ I
  obtain ⟨hex, hall⟩ := hM D torus S T hST μ c
  choose cj hcj using hex
  exact (hall cj hcj).2.2 I
variable {D : MirrorData}
theorem pairwise_get_of_symm {α : Type*} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a)
    {X : List α} (h : X.Pairwise R) : Pairwise fun i j : Fin X.length => R (X.get i) (X.get j) := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.LimitPositivity.list_pairwise_get_of_symm <;> assumption
theorem isSepLipList_of_mem (hs : Sides.HyperplaneSidesClaim) (E : Ambient)
    {X : FnList D E} (hX : X ∈ separatedAll D E) : IsSepLipList D E X := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.CenteredConvergence.isSepLipList_of_mem <;> assumption
def lipTupleOfSeparated (hs : Sides.HyperplaneSidesClaim) {n : ℕ} (X : separatedN D torus n) :
    LipTuple D n :=
  ⟨fun i => X.1.get (i.cast X.2.1.symm), by
    have h : LimitSpaces.Ambient.periodic.IsSepTuple D.toStandingParameters .lip univ X.1.get :=
      isSepLipList_of_mem hs torus (separatedN_subset_separatedAll D torus n X.2)
    exact LimitSpaces.Ambient.IsSepTuple.comp_inj h (Fin.cast_injective _)⟩
def smoothRestriction (hs : Sides.HyperplaneSidesClaim) (Ψ : LipFamily D) :
    FunctionalFamily D torus :=
  fun n hn X => Ψ n hn (lipTupleOfSeparated hs X)
theorem tendsto_pnat_add_left (k₀ : ℕ+) : Tendsto (fun j : ℕ+ => k₀ + j) atTop atTop :=
  tendsto_atTop_mono (fun j => by
    show (j : ℕ) ≤ ((k₀ + j : ℕ+) : ℕ)
    rw [PNat.add_coe]
    omega) tendsto_id
theorem tendsto_pnat_coe : Tendsto (fun j : ℕ+ => (j : ℕ)) atTop atTop := by apply _root_.YangMills.Construction.ReflectionPositivity.AdicLattices.tendsto_pnat_coe_atTop <;> assumption
def couplingSeq (D : MirrorData) (k₀ : ℕ+) (β : ℕ+ → ℝ) (hβ : ∀ k, k₀ ≤ k → 0 < β k) :
    LatticeDataSeq D torus where
  K j := k₀ + j
  ℓ _ := D.side
  β j := β (k₀ + j)
  ℓ_mem _ := ⟨D.m, D.m.pos, rfl⟩
  β_pos j := hβ _ (by
    show (k₀ : ℕ) ≤ ((k₀ + j : ℕ+) : ℕ)
    rw [PNat.add_coe]
    omega)
  K_tendsto := tendsto_pnat_coe.comp (tendsto_pnat_add_left k₀)
  isSideSequence _ := rfl
section Coupling
variable {k₀ : ℕ+} {β : ℕ+ → ℝ} (hβ : ∀ k, k₀ ≤ k → 0 < β k) {Ψ : LipFamily D}
include hβ in
theorem couplingSeq_tendsToFamily (hs : Sides.HyperplaneSidesClaim)
    (hlim : IsConnectedLimit D β Ψ) :
    (couplingSeq D k₀ β hβ).TendsToFamily (smoothRestriction hs Ψ) := by
  rintro n hn ⟨X, hlen, hX⟩
  subst hlen
  refine ((hlim _ hn (lipTupleOfSeparated hs ⟨X, rfl, hX⟩)).comp (tendsto_pnat_add_left k₀)).congr
    fun j => ?_
  rw [LatticeDataSeq.connectedAt_torus]
  rfl
include hβ in
theorem couplingSeq_lipLimitsExist (hlim : IsConnectedLimit D β Ψ) :
    (couplingSeq D k₀ β hβ).LipLimitsExist := fun n hn f =>
  ⟨Ψ n hn f, (hlim n hn f).comp (tendsto_pnat_add_left k₀)⟩
include hβ in
theorem couplingSeq_lipLimitFamily (hlim : IsConnectedLimit D β Ψ) :
    (couplingSeq D k₀ β hβ).lipLimitFamily = Ψ := by
  funext n hn f
  have h : Tendsto ((couplingSeq D k₀ β hβ).connectedAtLip f) atTop
      (𝓝 ((Ψ n hn f : ℝ) : ℂ)) := (hlim n hn f).comp (tendsto_pnat_add_left k₀)
  simp only [LatticeDataSeq.lipLimitFamily, h.limUnder_eq, Complex.ofReal_re]
include hβ in
theorem couplingSeq_lipLimitCenteredFunctional (hlim : IsConnectedLimit D β Ψ) :
    (couplingSeq D k₀ β hβ).lipLimitCenteredFunctional = limitCentred Ψ := by
  funext X
  unfold LatticeDataSeq.lipLimitCenteredFunctional limitCentred
  rw [couplingSeq_lipLimitFamily hβ hlim]
include hβ in
theorem centeredFunctional_smoothRestriction (hs : Sides.HyperplaneSidesClaim)
    (hsig : LatticeDataSeq.CenteredFunctionalsConverge)
    (hlim : IsConnectedLimit D β Ψ) :
    (smoothRestriction hs Ψ).centeredFunctional = limitCentredSmooth Ψ := by
  funext X
  have hval := ((hsig.1 D torus _ _ (couplingSeq_tendsToFamily hβ hs hlim)).1.2).1 X
  have hL : X.1 ∈ sepLipTuples D := isSepLipList_of_mem hs torus X.2
  rw [hval]
  have e : limitCentredSmooth Ψ X = limitCentred Ψ ⟨X.1, hL⟩ := by
    simp [limitCentredSmooth, evalOrZero, hL]
  rw [e]
  refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => ?_
  refine congrArg (Ψ J.1.card _) (Subtype.ext (funext fun i => ?_))
  simp [lipTupleOfSeparated, subList, LimitSpaces.Ambient.restrictTuple,
    LimitSpaces.Ambient.pickComponents]
  rfl
end Coupling
theorem exists_ofReal_le_of_pos {q : ℕ} (a : Fin q → Fin q → ℝ≥0∞)
    (h : ∀ l l', l ≠ l' → 0 < a l l') :
    ∃ d : ℝ, 0 < d ∧ ∀ l l', l ≠ l' → ENNReal.ofReal d ≤ a l l' := by
  have ht : Tendsto ENNReal.ofReal (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h₀ := ENNReal.continuous_ofReal.tendsto (0 : ℝ)
    rw [ENNReal.ofReal_zero] at h₀
    exact h₀.mono_left nhdsWithin_le_nhds
  have h₁ : ∀ l l', ∀ᶠ ε in 𝓝[>] (0 : ℝ), l ≠ l' → ENNReal.ofReal ε ≤ a l l' := by
    intro l l'
    by_cases e : l = l'
    · exact Eventually.of_forall fun _ hne => absurd e hne
    · filter_upwards [ht.eventually_lt_const (h l l' e)] with ε hε _ using hε.le
  have h₂ := (eventually_all.2 fun l => eventually_all.2 (h₁ l)).and self_mem_nhdsWithin
  obtain ⟨d, hd, hpos⟩ := h₂.exists
  exact ⟨d, hpos, fun l l' e => hd l l' e⟩
theorem setDist_torus_antitone {A A' B B' : Set (torus.Point D)} (hA : A ⊆ A') (hB : B ⊆ B') :
    setDist D torus A' B' ≤ setDist D torus A B :=
  (biInf_mono hA).trans (iInf₂_mono fun _ _ => biInf_mono hB)
theorem separatedCompactBound_of_sharpBounded (hs : Sides.HyperplaneSidesClaim)
    {M : LimitSpaces.SharpParameter} {Ψ : LipFamily D}
    (hb : SharpBounded D M Ψ) :
    DenseMirrors.SeparatedCompactBound M (smoothRestriction hs Ψ) := by
  intro q _ A _ hApos
  obtain ⟨C, hC0, hC⟩ := hb
  obtain ⟨d, hd, hdA⟩ := exists_ofReal_le_of_pos (fun l l' => setDist D torus (A l) (A l')) hApos
  refine ⟨fun n => C n d, fun n hn _ => hC0 n hn d hd, ?_⟩
  rintro n hn _ ⟨X, hlen, hX⟩ ⟨ι, hinj, hsup⟩
  subst hlen
  have hpair : Pairwise fun i j => ENNReal.ofReal d ≤
      LimitSpaces.Ambient.periodic.infSetDist D.toStandingParameters
        (LimitSpaces.Ambient.periodic.closedSupport D.toStandingParameters
          ((lipTupleOfSeparated hs ⟨X, rfl, hX⟩).1 i))
        (LimitSpaces.Ambient.periodic.closedSupport D.toStandingParameters
          ((lipTupleOfSeparated hs ⟨X, rfl, hX⟩).1 j)) := by
    intro i j hij
    have hne : ι i ≠ ι j := fun e => hij (hinj (congrArg A e))
    exact (hdA _ _ hne).trans (setDist_torus_antitone (hsup i).2 (hsup j).2)
  have h := hC _ hn d hd (lipTupleOfSeparated hs ⟨X, rfl, hX⟩) hpair
  have e : (X.map (normSharp D M torus)).prod = ∏ i : Fin X.length, normSharp D M torus (X.get i) := by
    rw [← Fin.prod_univ_fun_getElem]
    rfl
  rw [e]
  exact h
theorem boundedLimit_of_continuityInHeight (hD : DenseMirrors.ContinuityInHeight)
    (hfix : LatticeDataSeq.PositivityPassesToLimit)
    (hs : Sides.HyperplaneSidesClaim)
    (hsig : LatticeDataSeq.CenteredFunctionalsConverge) :
    BoundedLimitCondition := by
  intro D M k₀ β hβ Ψ hlim hb μ
  have hconv := couplingSeq_tendsToFamily hβ hs hlim
  refine ⟨fun c hc I => ?_, fun c I => ?_⟩
  · have h := hfix.2 D _ _ hconv μ c hc (couplingSeq_lipLimitsExist hβ hlim) I
    rwa [couplingSeq_lipLimitCenteredFunctional hβ hlim] at h
  · have h := (hD D torus _ _ hconv M (separatedCompactBound_of_sharpBounded hs hb) μ c).2.2 I
    rwa [centeredFunctional_smoothRestriction hβ hs hsig hlim] at h
def hermSum {t : ℕ} (m : Fin t → Fin t → ℂ) (a b : Fin t → ℂ) : ℂ :=
  ∑ i, ∑ k, conj (a i) * b k * m i k
theorem hermSum_add_smul {t : ℕ} (m : Fin t → Fin t → ℂ) (a b : Fin t → ℂ) (s u : ℂ) :
    hermSum m (s • a + u • b) (s • a + u • b) =
      conj s * s * hermSum m a a + conj s * u * hermSum m a b +
        conj u * s * hermSum m b a + conj u * u * hermSum m b b := by
  simp only [hermSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring
theorem mixed_eq_of_diag_eq {g₁₁ g₁₂ g₂₁ g₂₂ a₁₁ a₁₂ a₂₁ a₂₂ : ℂ}
    (h : ∀ s t : ℂ,
      conj s * s * g₁₁ + conj s * t * g₁₂ + conj t * s * g₂₁ + conj t * t * g₂₂ =
        conj s * s * a₁₁ + conj s * t * a₁₂ + conj t * s * a₂₁ + conj t * t * a₂₂) :
    g₁₂ = a₁₂ := by
  have h₁ := h 1 0
  have h₂ := h 0 1
  have h₃ := h 1 1
  have h₄ := h 1 Complex.I
  simp only [map_one, map_zero, Complex.conj_I, one_mul, mul_one, zero_mul, mul_zero, add_zero,
    zero_add] at h₁ h₂ h₃ h₄
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h₅ : -Complex.I * Complex.I = 1 := by rw [neg_mul, hI, neg_neg]
  rw [h₅] at h₄
  have h₆ : g₁₂ - a₁₂ + (g₂₁ - a₂₁) = 0 := by linear_combination h₃ - h₁ - h₂
  have h₇ : Complex.I * (g₁₂ - a₁₂ - (g₂₁ - a₂₁)) = 0 := by linear_combination h₄ - h₁ - h₂
  have h₈ : g₁₂ - a₁₂ - (g₂₁ - a₂₁) = 0 :=
    (mul_eq_zero.1 h₇).resolve_left Complex.I_ne_zero
  linear_combination (1 / 2 : ℂ) * h₆ + (1 / 2 : ℂ) * h₈
def toCutoffData (d : MirrorData) (μ : Fin 4) : CutoffMirrors.MirrorData :=
  ⟨d.toStandingParameters, d.β, d.β_pos, μ⟩
theorem reflect_torus_eq_cutoff (d : MirrorData) (μ : Fin 4) (c : ℝ) :
    CoordMirror.reflect d ⟨μ, c⟩ .torus = (toCutoffData d μ).reflect c := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.LimitPositivity.reflect_eq_cutoffReflect <;> assumption
theorem upperSide_eq_openSlab (d : MirrorData) (μ : Fin 4) (c : ℝ) :
    (CoordMirror.mk μ c).upperSide d .torus =
      (toCutoffData d μ).openSlab c CutoffMirrors.SlabSide.pos := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.LimitPositivity.upperSide_eq_openSlab <;> assumption
section AtIndex
variable (S : LatticeDataSeq D euclidean)
def momentMatrix {t : ℕ} (Z : Fin t → separatedWithin D euclidean (upperHalf D)) (j : ℕ+)
    (i k : Fin t) : ℂ :=
  ((S.centredAt j ((CoordMirror.timeAt (S.linkHeight j)).reflectAppend D euclidean
    (Z i).1 (Z k).1) : ℝ) : ℂ)
theorem thetaForm_at_index (hs : Sides.HyperplaneSidesClaim)
    (hin : CutoffMirrors.TupleInequality.Statement)
    (htr : LimitSpaces.Periodization.Properties)
    {t : ℕ} (ht : 1 ≤ t) (Z : Fin t → separatedWithin D euclidean (upperHalf D)) (j : ℕ+)
    (hfit : ∀ i k, LimitSpaces.FitsInTorus (S.standingAt j)
      ((CoordMirror.timeAt (S.linkHeight j)).reflectAppend D euclidean (Z i).1 (Z k).1))
    (hslab : ∀ i, MovingMirror.ElementsInOpenSlab S j
      (CoordMirror.timeAt (S.linkHeight j)) (Z i).1) (ζ : Fin t → ℂ) :
    S.latticeFn ζ Z j ∈ (S.linkLevel j).halfAlgebra .pos ∧
      hermSum (momentMatrix S Z j) ζ ζ =
        (S.linkLevel j).thetaForm (S.latticeFn ζ Z j) (S.latticeFn ζ Z j) ∧
      0 ≤ (S.linkLevel j).thetaForm (S.latticeFn ζ Z j)
        (S.latticeFn ζ Z j) := by
  let d : MirrorData := MovingMirror.dataAt S j
  let s' : Conventions.StandingParameters := S.standingAt j
  have hcompact : ∀ i, ∀ f ∈ (Z i).1,
      LimitSpaces.Ambient.euclidean.IsCompactSubset d.toStandingParameters
        (LimitSpaces.Ambient.euclidean.closedSupport d.toStandingParameters f) := fun i f hf =>
    ((isSeparatedList_of_mem_separatedAll (Z i).2.1).1 f hf).2
  have hcat := fun i k => (htr d).2.2 (Z i).1 (Z k).1 (hcompact i) (hcompact k) 3 (S.linkHeight j)
    (hfit i k)
  have hfits : ∀ i, LimitSpaces.FitsInTorus s' (Z i).1 := fun i => (hcat i i).1
  let Xl : Fin t → List ((Fin 4 → ℝ) → ℝ) := fun i => (Z i).1
  have hsepT := fun i => (htr d).2.1 _ (Xl i).get
  have hlists : ∀ i, LimitSpaces.periodizeList s' (Xl i) =
      List.ofFn fun l => LimitSpaces.periodizeFun s' ((Xl i).get l) := fun i => by
    have e := LimitSpaces.periodizeList_ofFn s' (Xl i).get
    rwa [List.ofFn_get] at e
  have hr : ∀ i, LimitSpaces.Ambient.periodic.IsSepLipTuple s' univ
      (fun l => LimitSpaces.periodizeFun s' ((Xl i).get l)) := fun i =>
    (hsepT i (isSepLipList_of_mem hs euclidean (Z i).2.1)
      (by rw [List.ofFn_get]; exact hfits i)).1
  let X' : Fin t → FnList d torus := fun i => LimitSpaces.periodizeList s' (Z i).1
  have hlip : ∀ i, ∀ f ∈ X' i, TestFunctions.IsLipschitzFor (toCutoffData d 3).torusDist f := by
    intro i f hf
    have hf' : f ∈ List.ofFn fun l => LimitSpaces.periodizeFun s' ((Xl i).get l) :=
      (hlists i) ▸ hf
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hf'
    exact ((hr i).1 l).1
  have hdis : ∀ i, (X' i).Pairwise fun f g =>
      Disjoint (closedSupport d torus f) (closedSupport d torus g) := by
    intro i
    have hp : (List.ofFn fun l => LimitSpaces.periodizeFun s' ((Xl i).get l)).Pairwise
        fun f g => Disjoint (closedSupport d torus f) (closedSupport d torus g) :=
      List.pairwise_ofFn.2 fun a b hab => (hr i).2 hab.ne
    exact Eq.mpr (congrArg (List.Pairwise _) (hlists i)) hp
  let C : CutoffMirrors.LinkLevel (toCutoffData d 3) := S.linkLevel j
  have hargs : ∀ i, CutoffMirrors.TupleInequality.IsPosSideArgs C (X' i).get := fun i => by
    refine ⟨⟨fun l => hlip i _ (List.get_mem _ _), fun l l' hll => ?_⟩, fun l => ?_⟩
    · exact Set.disjoint_iff_inter_eq_empty.1
        (pairwise_get_of_symm (fun _ _ h => h.symm) (hdis i) hll)
    · have h := hslab i _ (List.get_mem (X' i) l)
      have e := upperSide_eq_openSlab d 3 (S.linkHeight j)
      have h' : closedSupport d torus ((X' i).get l) ⊆
          (CoordMirror.mk 3 (S.linkHeight j)).upperSide d torus := h
      rw [e] at h'
      exact h'
  obtain ⟨-, hmem, ⟨e, hn⟩, -⟩ := (hin (toCutoffData d 3) C).1 t ht X' ζ hargs
  refine ⟨hmem, ?_, hn⟩
  refine Eq.trans ?_ e
  simp only [hermSum, CutoffMirrors.TupleInequality.pairSum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  have hθ : (CoordMirror.mk 3 (S.linkHeight j)).pullback d torus (α := ℝ) = C.reflectFn := by
    funext f
    show f ∘ CoordMirror.reflect d ⟨3, S.linkHeight j⟩ .torus =
      f ∘ (toCutoffData d 3).reflect (S.linkHeight j)
    rw [reflect_torus_eq_cutoff]
    rfl
  let Xd : Fin t → (toCutoffData d 3).FunTuple ℝ := X'
  have eT : (CoordMirror.mk 3 (S.linkHeight j)).reflectAppend d torus (X' i) (X' k) =
      C.reflectTuple (Xd i) ++ Xd k :=
    congrArg (fun g : (Point d torus → ℝ) → (Point d torus → ℝ) => List.map g (X' i) ++ X' k) hθ
  have e₁ : S.centredAt j ((CoordMirror.timeAt (S.linkHeight j)).reflectAppend D euclidean
      (Z i).1 (Z k).1) = (toCutoffData d 3).gibbsFunctionalList
        (C.reflectTuple (Xd i) ++ Xd k) :=
    (congrArg (toCutoffData d 3).gibbsFunctionalList (hcat i k).2.2).trans
      (congrArg (toCutoffData d 3).gibbsFunctionalList eT)
  exact congrArg (fun z : ℝ => conj (ζ i) * ζ k * (z : ℂ)) e₁
def appendTuples {r r' : ℕ} (X : Fin r → separatedWithin D euclidean (upperHalf D))
    (Y : Fin r' → separatedWithin D euclidean (upperHalf D)) :
    Fin (r + r' + 1) → separatedWithin D euclidean (upperHalf D) :=
  Fin.append (Fin.append X Y) fun _ : Fin 1 => ⟨[], nil_mem_separatedWithin D euclidean _⟩
def appendCoeffs {r r' : ℕ} (c : Fin r → ℂ) (c' : Fin r' → ℂ) : Fin (r + r' + 1) → ℂ :=
  Fin.append (Fin.append c c') fun _ : Fin 1 => 0
variable {r r' : ℕ} (X : Fin r → separatedWithin D euclidean (upperHalf D))
  (Y : Fin r' → separatedWithin D euclidean (upperHalf D))
theorem latticeFn_appendLeft (c : Fin r → ℂ) (j : ℕ+) :
    S.latticeFn (appendCoeffs c 0) (appendTuples X Y) j = S.latticeFn c X j := by
  funext U
  simp [LatticeDataSeq.latticeFn_apply, Fin.sum_univ_add, appendCoeffs, appendTuples]
theorem latticeFn_appendRight (c' : Fin r' → ℂ) (j : ℕ+) :
    S.latticeFn (appendCoeffs 0 c') (appendTuples X Y) j = S.latticeFn c' Y j := by
  funext U
  simp [LatticeDataSeq.latticeFn_apply, Fin.sum_univ_add, appendCoeffs, appendTuples]
theorem hermSum_append (c : Fin r → ℂ) (c' : Fin r' → ℂ) (j : ℕ+) :
    hermSum (momentMatrix S (appendTuples X Y) j) (appendCoeffs c 0) (appendCoeffs 0 c') =
      ∑ i, ∑ k, conj (c i) * c' k *
        ((S.centredAt j ((CoordMirror.timeAt (S.linkHeight j)).reflectAppend D euclidean
          (X i).1 (Y k).1) : ℝ) : ℂ) := by
  simp [hermSum, momentMatrix, Fin.sum_univ_add, appendCoeffs, appendTuples]
theorem latticeFn_add_smul {t : ℕ}
    (Z : Fin t → separatedWithin D euclidean (upperHalf D)) (a b : Fin t → ℂ) (s u : ℂ)
    (j : ℕ+) :
    S.latticeFn (s • a + u • b) Z j =
      s • S.latticeFn a Z j + u • S.latticeFn b Z j := by
  funext U
  simp only [LatticeDataSeq.latticeFn_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
theorem isNearLinkLevel_linkHeight (j : ℕ+) :
    MovingMirror.IsNearLinkLevel S 0 j (S.linkHeight j) := by
  have ha : 0 ≤ MovingMirror.meshOf S j := by
    have hL : (0 : ℝ) < D.L := by
      have h := D.isAdmissible.2
      exact_mod_cast (by omega : 0 < D.L)
    simp only [MovingMirror.meshOf, PeriodicLattice.meshSize]
    exact (zpow_pos hL _).le
  have e : S.linkHeight j = MovingMirror.meshOf S j / 2 := rfl
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rw [e]
    push_cast
    ring
  · rw [e, sub_zero, abs_of_nonneg (by positivity)]
    linarith
theorem latticePairing_eventually (hM : MovingMirror.MovingMirrorLimit)
    (hs : Sides.HyperplaneSidesClaim)
    (hin : CutoffMirrors.TupleInequality.Statement)
    (hos : CutoffMirrors.LinkPositivity.ReflectionPositivityAtLink)
    (htr : LimitSpaces.Periodization.Properties)
    {T : FunctionalFamily D euclidean} (hST : S.TendsToFamily T) (c : Fin r → ℂ)
    (c' : Fin r' → ℂ) : LatticePairingEventually S c X c' Y := by
  obtain ⟨-, hall⟩ := hM D euclidean S T hST 3 0
  obtain ⟨hI, hII, -⟩ := hall S.linkHeight (isNearLinkLevel_linkHeight S)
  let Z := appendTuples X Y
  let a := appendCoeffs c (0 : Fin r' → ℂ)
  let b := appendCoeffs (0 : Fin r → ℂ) c'
  let I : (CoordMirror.mk 3 0).PositivityInstance D euclidean := ⟨r + r' + 1, by omega, Z, a⟩
  have hfit : ∀ᶠ j in atTop, ∀ i k, LimitSpaces.FitsInTorus (S.standingAt j)
      ((CoordMirror.timeAt (S.linkHeight j)).reflectAppend D euclidean (Z i).1 (Z k).1) :=
    eventually_all.2 fun i => eventually_all.2 fun k => (hII (Z i) (Z k)).1.mono fun j h => h.2
  filter_upwards [hI I, hfit] with j h₁ h₂
  have core := thetaForm_at_index S hs hin htr (by omega) Z j h₂ h₁.2.1
  have ha := latticeFn_appendLeft S X Y c j
  have hb := latticeFn_appendRight S X Y c' j
  obtain ⟨haM, -, haN⟩ := core a
  obtain ⟨hbM, -, -⟩ := core b
  have hses := (hos _ (S.linkLevel j)).2.1.1
  have haM' : S.latticeFn c X j ∈ (S.linkLevel j).halfAlgebra .pos := ha ▸ haM
  have hbM' : S.latticeFn c' Y j ∈ (S.linkLevel j).halfAlgebra .pos := hb ▸ hbM
  refine ⟨haM', hbM', ?_, ?_⟩
  swap
  · show 0 ≤ (S.linkLevel j).thetaForm (S.latticeFn c X j) (S.latticeFn c X j)
    rw [← ha]
    exact haN
  have hform : ∀ s u : ℂ,
      (S.linkLevel j).thetaForm (S.latticeFn (s • a + u • b) Z j)
        (S.latticeFn (s • a + u • b) Z j) =
      conj s * s * (S.linkLevel j).thetaForm (S.latticeFn a Z j) (S.latticeFn a Z j) +
      conj s * u * (S.linkLevel j).thetaForm (S.latticeFn a Z j) (S.latticeFn b Z j) +
      conj u * s * (S.linkLevel j).thetaForm (S.latticeFn b Z j) (S.latticeFn a Z j) +
      conj u * u * (S.linkLevel j).thetaForm (S.latticeFn b Z j) (S.latticeFn b Z j) := by
    intro s u
    rw [latticeFn_add_smul]
    have hW := (hses s u _ haM _ hbM _ haM).1
    obtain ⟨-, h₃, -⟩ := hses s u _ haM _ hbM _ hW
    obtain ⟨-, -, h₄⟩ := hses s u _ haM _ hbM _ haM
    obtain ⟨-, -, h₅⟩ := hses s u _ haM _ hbM _ hbM
    rw [h₃, h₄, h₅]
    ring
  have hpol := mixed_eq_of_diag_eq (g₁₁ := hermSum (momentMatrix S Z j) a a)
    (g₁₂ := hermSum (momentMatrix S Z j) a b) (g₂₁ := hermSum (momentMatrix S Z j) b a)
    (g₂₂ := hermSum (momentMatrix S Z j) b b)
    (a₁₁ := (S.linkLevel j).thetaForm (S.latticeFn a Z j) (S.latticeFn a Z j))
    (a₁₂ := (S.linkLevel j).thetaForm (S.latticeFn a Z j) (S.latticeFn b Z j))
    (a₂₁ := (S.linkLevel j).thetaForm (S.latticeFn b Z j) (S.latticeFn a Z j))
    (a₂₂ := (S.linkLevel j).thetaForm (S.latticeFn b Z j) (S.latticeFn b Z j))
    fun s u => by
      rw [← hermSum_add_smul, ← hform]
      exact (core (s • a + u • b)).2.1
  have hpj := hermSum_append S X Y c c' j
  show (S.linkLevel j).thetaForm (S.latticeFn c X j) (S.latticeFn c' Y j) = _
  rw [← hpj, ← ha, ← hb]
  exact hpol.symm
end AtIndex
theorem euclideanInvariance_limit (hM : MovingMirror.MovingMirrorLimit)
    (hs : Sides.HyperplaneSidesClaim)
    (hin : CutoffMirrors.TupleInequality.Statement)
    (hos : CutoffMirrors.LinkPositivity.ReflectionPositivityAtLink)
    (htr : LimitSpaces.Periodization.Properties) : OnEuclidean := by
  intro D S T hST
  obtain ⟨-, hall⟩ := hM D euclidean S T hST 3 0
  obtain ⟨-, hII, -⟩ := hall S.linkHeight (isNearLinkLevel_linkHeight S)
  have hlarge := fun (r r' : ℕ) (c : Fin r → ℂ)
      (X : Fin r → separatedWithin D euclidean (upperHalf D)) (c' : Fin r' → ℂ)
      (Y : Fin r' → separatedWithin D euclidean (upperHalf D)) =>
    latticePairing_eventually S X Y hM hs hin hos htr hST c c'
  have hlim : ∀ (r r' : ℕ) (c : Fin r → ℂ)
      (X : Fin r → separatedWithin D euclidean (upperHalf D)) (c' : Fin r' → ℂ)
      (Y : Fin r' → separatedWithin D euclidean (upperHalf D)),
      PairingTendsto S T c X c' Y := by
    intro r r' c X c' Y
    have e : limitPairing T c X c' Y = ∑ i, ∑ k, conj (c i) * c' k *
        ((evalOrZero T.centeredFunctional
          ((CoordMirror.timeAt 0).reflectAppend D euclidean (X i).1 (Y k).1) : ℝ) : ℂ) := by
      unfold limitPairing
      rw [CoordMirror.reflectionForm_sumOf]
      simp only [evalOrZeroC_ofReal]
    have ht : Tendsto (fun j => ∑ i, ∑ k, conj (c i) * c' k *
        ((S.centredAt j ((CoordMirror.timeAt (S.linkHeight j)).reflectAppend D euclidean
          (X i).1 (Y k).1) : ℝ) : ℂ)) atTop (𝓝 (limitPairing T c X c' Y)) := by
      rw [e]
      refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun k _ => ?_
      exact ((Complex.continuous_ofReal.tendsto _).comp (hII (X i) (Y k)).2).const_mul _
    refine ht.congr' ?_
    filter_upwards [hlarge r r' c X c' Y] with j hj
    exact hj.2.2.1.symm
  have hnonneg : ∀ (r : ℕ) (c : Fin r → ℂ)
      (X : Fin r → separatedWithin D euclidean (upperHalf D)), 0 ≤ limitPairing T c X c X := by
    intro r c X
    have hclosed : IsClosed {z : ℂ | 0 ≤ z} := by
      have e : {z : ℂ | 0 ≤ z} = {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
        refine Set.ext fun z => ?_
        show 0 ≤ z ↔ z.im = 0 ∧ 0 ≤ z.re
        simp only [Complex.le_def, Complex.zero_re, Complex.zero_im]
        exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
      rw [e]
      exact (isClosed_eq Complex.continuous_im continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_re)
    exact hclosed.mem_of_tendsto (hlim r r c X c X)
      ((hlarge r r c X c X).mono fun j hj => hj.2.2.2)
  refine ⟨fun r r' c X c' Y => ⟨hlarge r r' c X c' Y, hlim r r' c X c' Y, hnonneg r c X⟩, ?_, ?_⟩
  · intro F
    obtain ⟨r, c, X, rfl⟩ := TupleCombination.exists_eq_sumOf F
    exact hnonneg r c X
  · rintro ⟨μ, c⟩ I
    obtain ⟨hex, hall'⟩ := hM D euclidean S T hST μ c
    choose cj hcj using hex
    exact (hall' cj hcj).2.2 I
theorem limitPositivity (hM : MovingMirror.MovingMirrorLimit)
    (hD : DenseMirrors.ContinuityInHeight)
    (hfix : LatticeDataSeq.PositivityPassesToLimit)
    (hs : Sides.HyperplaneSidesClaim)
    (hsig : LatticeDataSeq.CenteredFunctionalsConverge)
    (hin : CutoffMirrors.TupleInequality.Statement)
    (hos : CutoffMirrors.LinkPositivity.ReflectionPositivityAtLink)
    (htr : LimitSpaces.Periodization.Properties) : LimitPositivityStatement :=
  ⟨positivity_on_torus hM, boundedLimit_of_continuityInHeight hD hfix hs hsig, euclideanInvariance_limit hM hs hin hos htr⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror.LimitPositivity
end
