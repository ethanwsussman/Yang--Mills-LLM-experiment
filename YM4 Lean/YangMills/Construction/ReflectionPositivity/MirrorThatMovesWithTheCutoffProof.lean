import YangMills.Construction.ReflectionPositivity.CentredFunctionalsAlongAConvergentSequenceProof
import YangMills.Construction.ReflectionPositivity.SequencesOfLatticeDataAndTheirLimits
import YangMills.Construction.PassageToTheLimit.EquicontinuityWithoutABound
import YangMills.Construction.ReflectionPositivity.CentredMomentsAreSumsOfCumulants
import YangMills.Construction.ReflectionPositivity.CommonSetsForAMirrorThatMovesProof
import YangMills.Construction.ReflectionPositivity.InequalityPassesToTheLimitAtFixedTuplesProof
import YangMills.Construction.ReflectionPositivity.MirrorThatMovesWithTheCutoff
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ComplexConjugate ComplexOrder ENNReal Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.MovingMirror
open AxisMirror.Ambient
variable {D : MirrorData}
theorem eventually_forall_mem {α β : Type*} {l : Filter β} {p : α → β → Prop} (X : List α)
    (h : ∀ f ∈ X, ∀ᶠ j in l, p f j) : ∀ᶠ j in l, ∀ f ∈ X, p f j := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.LimitPositivity.eventually_forall_mem_of_list <;> assumption
theorem pairwise_get_of_symm {α : Type*} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a)
    {X : List α} (h : X.Pairwise R) : Pairwise fun i j : Fin X.length => R (X.get i) (X.get j) := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.LimitPositivity.list_pairwise_get_of_symm <;> assumption
theorem forall₂_imp_of_mem {α β : Type*} {R R' : α → β → Prop} {p : α → Prop} {X : List α}
    {Y : List β} (h : List.Forall₂ R X Y) (hp : ∀ a ∈ X, p a)
    (himp : ∀ a b, p a → R a b → R' a b) : List.Forall₂ R' X Y := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih =>
    exact List.Forall₂.cons (himp _ _ (hp _ (by simp)) hab)
      (ih fun a ha => hp a (List.mem_cons_of_mem _ ha))
theorem exists_mem_of_forall₂ {α β : Type*} {R : α → β → Prop} {X : List α} {Y : List β}
    (h : List.Forall₂ R X Y) {a : α} (ha : a ∈ X) : ∃ b ∈ Y, R a b := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.MovingMirrorSets.exists_mem_of_forall₂ <;> assumption
theorem meshOf_pos {E : Ambient} (S : LatticeDataSeq D E) (j : ℕ+) :
    0 < meshOf S j := by
  have hL : (0 : ℝ) < D.L := by
    have h := D.isAdmissible.2
    exact_mod_cast (by omega : 0 < D.L)
  simp only [meshOf, PeriodicLattice.meshSize]
  exact zpow_pos hL _
theorem tendsto_meshOf {E : Ambient} (S : LatticeDataSeq D E) :
    Tendsto (meshOf S) atTop (𝓝 0) := by
  have hL : (1 : ℝ) < D.L := by
    have h := D.isAdmissible.2
    exact_mod_cast (by omega : 1 < D.L)
  have h₁ : Tendsto (fun n : ℕ => ((D.L : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hL)
  refine (h₁.comp S.K_tendsto).congr fun j => ?_
  simp [meshOf, PeriodicLattice.meshSize, zpow_neg]
theorem exists_isNearLinkLevel {E : Ambient} (S : LatticeDataSeq D E) (c : ℝ) (j : ℕ+) :
    ∃ c', IsNearLinkLevel S c j c' := by
  have ha := meshOf_pos S j
  set a := meshOf S j with hadef
  refine ⟨a * ((⌊c / a⌋ : ℝ) + 1 / 2), ⟨⌊c / a⌋, rfl⟩, ?_⟩
  have h₁ := Int.floor_le (c / a)
  have h₂ := Int.lt_floor_add_one (c / a)
  have e : a * ((⌊c / a⌋ : ℝ) + 1 / 2) - c = a * ((⌊c / a⌋ : ℝ) + 1 / 2 - c / a) := by
    field_simp
  have h₃ : |(⌊c / a⌋ : ℝ) + 1 / 2 - c / a| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  rw [e, abs_mul, abs_of_pos ha]
  nlinarith
theorem tendsto_abs_sub_level {E : Ambient} (S : LatticeDataSeq D E) {c : ℝ} {cj : ℕ+ → ℝ}
    (h : ∀ j, IsNearLinkLevel S c j (cj j)) :
    Tendsto (fun j => |cj j - c|) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => abs_nonneg _) (fun j => (h j).2) ?_
  have h := (tendsto_meshOf S).const_mul (1 / 2)
  simpa only [mul_zero] using h
theorem isSepLipList_of_mem (hs : Sides.HyperplaneSidesClaim) (E : Ambient)
    {X : FnList D E} (hX : X ∈ separatedAll D E) : IsSepLipList D E X := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.CenteredConvergence.isSepLipList_of_mem <;> assumption
theorem eventually_closedSupport_subset_upperSide (hs : Sides.HyperplaneSidesClaim) (E : Ambient)
    {μ : Fin 4} {c : ℝ} {cj : ℕ+ → ℝ} (hcj : Tendsto (fun j => |cj j - c|) atTop (𝓝 0))
    {f : E.Point D → ℝ} (hf : f ∈ compactC1 D ℝ E)
    (hsub : closedSupport D E f ⊆ (CoordMirror.mk μ c).upperSide D E) :
    ∀ᶠ j in atTop, closedSupport D E f ⊆ (CoordMirror.mk μ (cj j)).upperSide D E := by
  have ht : Tendsto (fun j => ENNReal.ofReal |cj j - c|) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hcj
  cases E with
  | torus =>
    obtain ⟨-, -, -, hd, -⟩ := (hs D μ c).1 .periodic
    obtain ⟨hpos, hmove⟩ := hd _ hf.2 hsub
    filter_upwards [ht.eventually_lt_const hpos] with j hj
    exact hmove _ hj
  | euclidean =>
    obtain ⟨-, -, -, hd, -⟩ := (hs D μ c).1 .euclidean
    obtain ⟨hpos, hmove⟩ := hd _ hf.2 hsub
    filter_upwards [ht.eventually_lt_const hpos] with j hj
    exact hmove _ hj
def cutoffMirrorData (d : MirrorData) (μ : Fin 4) : CutoffMirrors.MirrorData :=
  ⟨d.toStandingParameters, d.β, d.β_pos, μ⟩
theorem reflect_torus_eq_cutoff (d : MirrorData) (μ : Fin 4) (c : ℝ) :
    CoordMirror.reflect d ⟨μ, c⟩ .torus = (cutoffMirrorData d μ).reflect c := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.LimitPositivity.reflect_eq_cutoffReflect <;> assumption
theorem gibbsFunctionalList_ofFn (D' : CutoffMirrors.MirrorData) {q : ℕ}
    (e : Fin q → D'.Torus → ℝ) :
    D'.gibbsFunctionalList (List.ofFn e) = D'.gibbsFunctional e := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.CenteredConvergence.gibbsFunctional_get_ofFn <;> assumption
theorem gibbsFunctional_eq_re (hF : CutoffMirrors.CentredMomentCumulantExpansion)
    (D' : CutoffMirrors.MirrorData) {q : ℕ} {e : Fin q → D'.Torus → ℝ}
    (he : CutoffMirrors.MirrorData.IsAdmissibleArg (D := D') e) :
    D'.gibbsFunctional e = (D'.truncatedFunctional e).re := by
  obtain ⟨h₁, h₂⟩ := hF.2 D' q e he
  rw [← h₂, Complex.ofReal_re, h₁]
theorem reflected_sum_nonneg_at_cutoff (hin : CutoffMirrors.TupleInequality.Statement)
    (d : MirrorData) (μ : Fin 4) {c : ℝ}
    (hc : c ∈ LimitSpaces.halfShiftedMultiplesOf (PeriodicLattice.meshSize d.L (d.K : ℕ)))
    {r : ℕ} (hr : 1 ≤ r) (X : Fin r → FnList d torus) (a : Fin r → ℂ)
    (hlip : ∀ i, ∀ f ∈ X i, TestFunctions.IsLipschitzFor (cutoffMirrorData d μ).torusDist f)
    (hdis : ∀ i, (X i).Pairwise fun f g =>
      Disjoint (closedSupport d torus f) (closedSupport d torus g))
    (hsupp : ∀ i, ∀ f ∈ X i, closedSupport d torus f ⊆ (CoordMirror.mk μ c).upperSide d torus) :
    (∑ i, ∑ k, conj (a i) * a k * (((cutoffMirrorData d μ).gibbsFunctionalList
        ((CoordMirror.mk μ c).reflectAppend d torus (X i) (X k)) : ℝ) : ℂ)).im = 0 ∧
      0 ≤ (∑ i, ∑ k, conj (a i) * a k * (((cutoffMirrorData d μ).gibbsFunctionalList
        ((CoordMirror.mk μ c).reflectAppend d torus (X i) (X k)) : ℝ) : ℂ)).re := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.LimitPositivity.positivity_at_cutoff <;> assumption
section Product
def productPoint {P : LimitSpaces.Ambient} {s : Conventions.StandingParameters}
    {Z : List (P.Carrier s → ℝ)} {A : List (Set (P.Carrier s))}
    (h : List.Forall₂ (fun g B => g ∈ P.c1Within s B) Z A) : P.C1ProductSpace s A.get :=
  fun l => ⟨Z.get (l.cast (List.forall₂_iff_get.1 h).1.symm),
    (List.forall₂_iff_get.1 h).2 l.1 _ l.2⟩
theorem ofFn_components_productPoint {P : LimitSpaces.Ambient} {s : Conventions.StandingParameters}
    {Z : List (P.Carrier s → ℝ)} {A : List (Set (P.Carrier s))}
    (h : List.Forall₂ (fun g B => g ∈ P.c1Within s B) Z A) :
    List.ofFn (LimitSpaces.Ambient.components (productPoint h)) = Z := by
  refine List.ext_getElem (by simp [(List.forall₂_iff_get.1 h).1]) fun i h₁ h₂ => ?_
  simp [LimitSpaces.Ambient.components, productPoint]
theorem normC1_nonneg (P : LimitSpaces.Ambient) (s : Conventions.StandingParameters)
    (f : P.Carrier s → ℝ) : 0 ≤ P.normC1 s f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem normC1_zero (P : LimitSpaces.Ambient) (s : Conventions.StandingParameters) :
    P.normC1 s (0 : P.Carrier s → ℝ) = 0 := by
  simp [LimitSpaces.Ambient.normC1, TestFunctions.uniformNorm,
    LimitSpaces.Ambient.partialDeriv, LimitSpaces.Ambient.grad,
    LimitSpaces.Ambient.gradR4, TestFunctions.partialDerivR4,
    LimitSpaces.Ambient.liftFun]
theorem tendsto_of_indexAtTop {𝒥 : Set ℕ+} (hJ : ∀ᶠ j in atTop, j ∈ 𝒥) {β : Type*}
    {f : ℕ+ → β} {l : Filter β}
    (h : Tendsto (fun j : 𝒥 => f j) (LimitSpaces.indexAtTop 𝒥) l) : Tendsto f atTop l := by
  have hr : range (Subtype.val : 𝒥 → ℕ+) ∈ (atTop : Filter ℕ+) := by
    rw [Subtype.range_val]
    exact hJ
  have e := map_comap_of_mem hr
  rw [← e, tendsto_map'_iff]
  exact h
theorem indexAtTop_neBot {𝒥 : Set ℕ+} (hJ : ∀ᶠ j in atTop, j ∈ 𝒥) :
    (LimitSpaces.indexAtTop 𝒥).NeBot := by
  have hr : range (Subtype.val : 𝒥 → ℕ+) ∈ (atTop : Filter ℕ+) := by
    rw [Subtype.range_val]
    exact hJ
  have e := map_comap_of_mem hr
  have h : (map (Subtype.val : 𝒥 → ℕ+) (LimitSpaces.indexAtTop 𝒥)).NeBot := by
    show (map _ (comap _ atTop)).NeBot
    rw [e]
    infer_instance
  exact h.of_map
theorem infinite_of_eventually_mem {𝒥 : Set ℕ+} (hJ : ∀ᶠ j in atTop, j ∈ 𝒥) : 𝒥.Infinite := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hJ
  exact (Set.Ici_infinite N).mono fun j hj => hN j hj
theorem tendsto_along_moving_lists {P : LimitSpaces.Ambient} {s : Conventions.StandingParameters}
    {A : List (Set (P.Carrier s))} {𝒥 : Set ℕ+} (hJ : ∀ᶠ j in atTop, j ∈ 𝒥)
    {Ψ : 𝒥 → P.C1ProductSpace s A.get → ℝ}
    (hΨ : LimitSpaces.Ambient.ConvergesPointwise Ψ →
      LimitSpaces.Ambient.IsUniformlyBounded Ψ ∧ LimitSpaces.Ambient.IsEquicontinuousFamily Ψ)
    (val : ℕ+ → List (P.Carrier s → ℝ) → ℝ) (lim : List (P.Carrier s → ℝ) → ℝ)
    (hval : ∀ (j : 𝒥) (h : P.C1ProductSpace s A.get),
      Ψ j h = val j (List.ofFn (LimitSpaces.Ambient.components h)))
    (hlim : ∀ h : P.C1ProductSpace s A.get,
      Tendsto (fun j => val j (List.ofFn (LimitSpaces.Ambient.components h))) atTop
        (𝓝 (lim (List.ofFn (LimitSpaces.Ambient.components h)))))
    {Z : List (P.Carrier s → ℝ)} {Zm : ℕ+ → List (P.Carrier s → ℝ)}
    (hZ : List.Forall₂ (fun g B => g ∈ P.c1Within s B) Z A)
    (hZm : ∀ j ∈ 𝒥, List.Forall₂ (fun g B => g ∈ P.c1Within s B) (Zm j) A)
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      List.Forall₂ (fun f g => P.normC1 s (f - g) < ε) (Zm j) Z) :
    Tendsto (fun j => val j (Zm j)) atTop (𝓝 (lim Z)) := by
  have := indexAtTop_neBot hJ
  have hcomap : Tendsto (fun j : 𝒥 => (j : ℕ+)) (LimitSpaces.indexAtTop 𝒥) atTop :=
    tendsto_comap
  have hconv : LimitSpaces.Ambient.ConvergesPointwise Ψ := fun h =>
    ⟨lim (List.ofFn (LimitSpaces.Ambient.components h)),
      ((hlim h).comp hcomap).congr fun j => (hval j h).symm⟩
  obtain ⟨⟨⟨C, hC⟩, -, -⟩, heq⟩ := hΨ hconv
  let moving : 𝒥 → P.C1ProductSpace s A.get := fun j => productPoint (hZm j.1 j.2)
  have hmoving : ∀ l, Tendsto (fun j => P.normC1 s ((moving j l).1 - (productPoint hZ l).1))
      (LimitSpaces.indexAtTop 𝒥) (𝓝 0) := by
    intro l
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hcomap.eventually (hclose ε hε)] with j hj
    have h₁ := List.forall₂_iff_get.1 hj
    have hl₁ : l.1 < (Zm j).length := by
      have := (List.forall₂_iff_get.1 (hZm j.1 j.2)).1
      omega
    have hl₂ : l.1 < Z.length := by
      have := (List.forall₂_iff_get.1 hZ).1
      omega
    have h₂ := h₁.2 l.1 hl₁ hl₂
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (normC1_nonneg _ _ _)]
    exact h₂
  obtain ⟨L, h₁, h₂⟩ := (heq C hC).2 moving (productPoint hZ) hmoving
  have hz := hlim (productPoint hZ)
  rw [ofFn_components_productPoint] at hz
  have hL : L = lim Z := tendsto_nhds_unique h₂ ((hz.comp hcomap).congr fun j => by
    simp only [Function.comp_apply]
    rw [hval, ofFn_components_productPoint])
  refine tendsto_of_indexAtTop hJ ?_
  rw [← hL]
  refine h₁.congr fun j => ?_
  rw [hval]
  show val j (List.ofFn (LimitSpaces.Ambient.components (productPoint (hZm j.1 j.2)))) = _
  rw [ofFn_components_productPoint]
theorem forall₂_normC1_lt_map_append {P : LimitSpaces.Ambient}
    {s : Conventions.StandingParameters} {X Y : List (P.Carrier s → ℝ)}
    {F G : (P.Carrier s → ℝ) → P.Carrier s → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hX : ∀ f ∈ X, P.normC1 s (F f - G f) < ε) :
    List.Forall₂ (fun f g => P.normC1 s (f - g) < ε) (X.map F ++ Y) (X.map G ++ Y) := by
  refine List.rel_append ?_ ?_
  · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 hX))
  · refine List.forall₂_same.2 fun f _ => ?_
    rw [sub_self, normC1_zero]
    exact hε
theorem euclidNormVec_smul_stdBasisVec (t : ℝ) (μ : Fin 4) :
    TorusMetric.euclidNormVec (t • LimitSpaces.stdBasisVec μ) = |t| := by apply _root_.YangMills.Construction.LimitSpaces.MirrorTranslation.euclidNormVec_smul_stdBasisVec <;> assumption
theorem pointDist_proj_zero_le (hs : Sides.HyperplaneSidesClaim) (d : MirrorData)
    (P : LimitSpaces.Ambient) (v : Fin 4 → ℝ) :
    P.pointDist d.toStandingParameters (P.proj d.toStandingParameters v) 0 ≤
      TorusMetric.euclidNormVec v := by
  have h0 : ∀ Q : LimitSpaces.Ambient, Q.proj d.toStandingParameters 0 = 0 := fun Q => by
    have h := Q.proj_add d.toStandingParameters 0 0
    simpa using h
  cases P with
  | periodic =>
    obtain ⟨-, h2, -⟩ := ((hs d 0 0).1 .periodic).1
    have h := h2 v 0
    rw [h0, sub_zero] at h
    exact h
  | euclidean =>
    show TorusMetric.euclidNormVec (v - 0) ≤ _
    rw [sub_zero]
def sharpOne : LimitSpaces.SharpParameter := ⟨1, Set.mem_Ici.2 le_rfl⟩
theorem eventually_normC1_reflectFun_sub_lt (hs : Sides.HyperplaneSidesClaim)
    (hm : LimitSpaces.MirrorTranslation.Claim)
    (hfr : LimitSpaces.Ambient.uniformBoundednessEquicontinuity) (d : MirrorData)
    (P : LimitSpaces.Ambient) (μ : Fin 4) {c : ℝ} {cj : ℕ+ → ℝ}
    (hcj : Tendsto (fun j => |cj j - c|) atTop (𝓝 0)) {f : P.Carrier d.toStandingParameters → ℝ}
    (hf : f ∈ P.c1Compact d.toStandingParameters) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, P.normC1 d.toStandingParameters
      (P.reflectFun d.toStandingParameters μ (cj j) f -
        P.reflectFun d.toStandingParameters μ c f) < ε := by
  obtain ⟨-, -, -, -, -, -, -, h8⟩ := ((hs d μ c).1 P).1
  have hg := (h8 f hf).1
  obtain ⟨δ, hδ, hc⟩ := (((hfr sharpOne 1 le_rfl).1 d.toStandingParameters P).2.1
    ⟨_, hg⟩).2 ε hε
  filter_upwards [hcj.eventually_lt_const (half_pos hδ)] with j hj
  have e := ((hm d.toStandingParameters sharpOne P μ).1 c (cj j) 0 f).1
  have e0 : P.translateFun d.toStandingParameters 0 (P.reflectFun d.toStandingParameters μ c f) =
      P.reflectFun d.toStandingParameters μ c f := by
    funext x
    simp [LimitSpaces.Ambient.translateFun]
  have hdist : P.pointDist d.toStandingParameters (P.proj d.toStandingParameters
      ((2 * (cj j - c)) • LimitSpaces.stdBasisVec μ)) 0 < δ := by
    refine (pointDist_proj_zero_le hs d P _).trans_lt ?_
    rw [euclidNormVec_smul_stdBasisVec, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h := hc _ _ hdist
  rw [e0] at h
  rw [e]
  exact h
end Product
theorem reflectAppend_torus (d : MirrorData) (μ : Fin 4) (c : ℝ)
    (X Y : List (LimitSpaces.Ambient.periodic.Carrier d.toStandingParameters → ℝ)) :
    ((CoordMirror.mk μ c).reflectAppend d torus X Y : FnList d torus) =
      (X.map (LimitSpaces.Ambient.periodic.reflectFun d.toStandingParameters μ c) ++ Y :
        List (LimitSpaces.Ambient.periodic.Carrier d.toStandingParameters → ℝ)) := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.LimitPositivity.reflectAppend_torus <;> assumption
theorem reflectAppend_euclidean (d : MirrorData) (μ : Fin 4) (c : ℝ)
    (X Y : List (LimitSpaces.Ambient.euclidean.Carrier d.toStandingParameters → ℝ)) :
    ((CoordMirror.mk μ c).reflectAppend d euclidean X Y : FnList d euclidean) =
      (X.map (LimitSpaces.Ambient.euclidean.reflectFun d.toStandingParameters μ c) ++ Y :
        List (LimitSpaces.Ambient.euclidean.Carrier d.toStandingParameters → ℝ)) := by
  have h : (CoordMirror.mk μ c).pullback d euclidean (α := ℝ) =
      LimitSpaces.Ambient.euclidean.reflectFun d.toStandingParameters μ c := by
    funext f
    show f ∘ CoordMirror.reflect d ⟨μ, c⟩ .euclidean = _
    rw [Sides.reflect_euclidean]
    rfl
  exact congrArg (fun g : (LimitSpaces.Ambient.euclidean.Carrier d.toStandingParameters → ℝ) →
    (LimitSpaces.Ambient.euclidean.Carrier d.toStandingParameters → ℝ) => List.map g X ++ Y) h
theorem tendsto_centredAt (hsig : LatticeDataSeq.CenteredFunctionalsConverge) {E : Ambient}
    (S : LatticeDataSeq D E) (T : FunctionalFamily D E) (hST : S.TendsToFamily T)
    {Z : FnList D E} (hZ : Z ∈ separatedAll D E) :
    Tendsto (fun j => S.centredAt j Z) atTop
      (𝓝 (evalOrZero (FunctionalFamily.centeredFunctional T) Z)) := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.LimitPositivity.tendsto_centredAt <;> assumption
theorem tendsto_reflectAppend_torus (hs : Sides.HyperplaneSidesClaim)
    (hc : MovingMirrorSets.SharedSetsProperties)
    (hsig : LatticeDataSeq.CenteredFunctionalsConverge)
    (hfr : LimitSpaces.Ambient.uniformBoundednessEquicontinuity)
    (hm : LimitSpaces.MirrorTranslation.Claim)
    (hF : CutoffMirrors.CentredMomentCumulantExpansion)
    (S : LatticeDataSeq D torus) (T : FunctionalFamily D torus) (hST : S.TendsToFamily T)
    (μ : Fin 4) {c : ℝ} {cj : ℕ+ → ℝ} (hcj : ∀ j, IsNearLinkLevel S c j (cj j))
    {X Y : FnList D torus}
    (hX : X ∈ separatedWithin D torus ((CoordMirror.mk μ c).upperSide D torus))
    (hY : Y ∈ separatedWithin D torus ((CoordMirror.mk μ c).upperSide D torus)) :
    Tendsto (fun j => S.centredAt j ((CoordMirror.mk μ (cj j)).reflectAppend D torus X Y))
      atTop (𝓝 (evalOrZero (FunctionalFamily.centeredFunctional T)
        ((CoordMirror.mk μ c).reflectAppend D torus X Y))) := by
  by_cases hq : X = [] ∧ Y = []
  · obtain ⟨rfl, rfl⟩ := hq
    exact tendsto_centredAt hsig S T hST (emptyList D torus).2
  obtain ⟨⟨hη, -, hcomp, hpos, hfar⟩, hmove, -⟩ :=
    hc D torus μ c X Y hX hY
  have hlen : 1 ≤ (MovingMirrorSets.sharedSets D torus μ c X Y).length := by
    have hne : X.length + Y.length ≠ 0 := by
      intro h0
      exact hq ⟨List.length_eq_zero_iff.1 (by omega), List.length_eq_zero_iff.1 (by omega)⟩
    simp only [MovingMirrorSets.sharedSets, List.length_append, List.length_map]
    omega
  let 𝒥 : Set ℕ+ := {j | meshOf S j ≤ MovingMirrorSets.margin D torus μ c X Y}
  have hJ : ∀ᶠ j in atTop, j ∈ 𝒥 :=
    ((tendsto_meshOf S).eventually_lt_const hη).mono fun j hj => hj.le
  have hmoved : ∀ j ∈ 𝒥, MovingMirrorSets.MovedListInSharedSets D torus μ c (cj j)
      X Y := fun j hj => hmove _ (by
    have h₁ := (hcj j).2
    have h₂ : meshOf S j ≤ _ := hj
    linarith)
  have hZ0 := hmove c (by simpa using hη.le)
  let s := D.toStandingParameters
  let A : List (Set (LimitSpaces.Ambient.periodic.Carrier s)) :=
    MovingMirrorSets.sharedSets D torus μ c X Y
  have hWc : ∀ l, LimitSpaces.Ambient.periodic.IsCompactSubset s (A.get l) := fun l =>
    hcomp _ (List.get_mem _ _)
  have hWd : Pairwise (Function.onFun Disjoint A.get) := fun l l' hll =>
    disjoint_of_setDist_pos D torus (lt_of_lt_of_le hpos (hfar l l' hll))
  have hP := ((hfr sharpOne A.length hlen).1 s .periodic).2.2 A.get hWc hWd
  have hseq := (hfr sharpOne A.length hlen).2.2.2.2.1 s A.get hWc hWd 𝒥
    (fun j => S.K j) (fun j => S.β j) (fun j => S.β_pos j) (infinite_of_eventually_mem hJ)
  have hmem : ∀ h : LimitSpaces.Ambient.periodic.C1ProductSpace s A.get,
      (List.ofFn (LimitSpaces.Ambient.components h) : FnList D torus) ∈
        separatedAll D torus := fun h =>
    separatedN_subset_separatedAll D torus _ ⟨List.length_ofFn, fun g hg => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
        exact (hP.1 h).2 i,
      List.pairwise_ofFn.2 fun i k hik => (hP.1 h).1.2 hik.ne⟩
  refine tendsto_along_moving_lists (P := .periodic) (s := s) (A := A) hJ hseq.2
    (fun j Z => S.centredAt j Z)
    (fun Z => evalOrZero (FunctionalFamily.centeredFunctional T) Z) ?_ ?_
    (Zm := fun j => (CoordMirror.mk μ (cj j)).reflectAppend D torus X Y)
    (forall₂_imp_of_mem hZ0.1 (p := fun g => g ∈ compactC1 D ℝ torus)
      (fun g hg => hZ0.2.2.1 g hg) fun g B hp hR => ⟨hp, hR⟩)
    (fun j hj => forall₂_imp_of_mem (hmoved j hj).1 (p := fun g => g ∈ compactC1 D ℝ torus)
      (fun g hg => (hmoved j hj).2.2.1 g hg) fun g B hp hR => ⟨hp, hR⟩) ?_
  · intro j h
    have he : CutoffMirrors.MirrorData.IsAdmissibleArg (D := S.mirrorDataAtExp j D.m)
        (LimitSpaces.Ambient.components h) :=
      ⟨fun l => ((hP.1 h).1.1 l).1, fun l l' hll =>
        Set.disjoint_iff_inter_eq_empty.1 ((hP.1 h).1.2 hll)⟩
    exact ((S.centredAt_torus j _).trans
      ((gibbsFunctionalList_ofFn (S.mirrorDataAtExp j D.m)
        (LimitSpaces.Ambient.components h)).trans (gibbsFunctional_eq_re hF _ he))).symm
  · exact fun h => tendsto_centredAt hsig S T hST (hmem h)
  · intro ε hε
    have habs := tendsto_abs_sub_level S hcj
    have h₁ : ∀ f ∈ X, ∀ᶠ j in atTop, LimitSpaces.Ambient.periodic.normC1 s
        (LimitSpaces.Ambient.periodic.reflectFun s μ (cj j) f -
          LimitSpaces.Ambient.periodic.reflectFun s μ c f) < ε := fun f hf =>
      eventually_normC1_reflectFun_sub_lt hs hm hfr D .periodic μ habs
        ((isSeparatedList_of_mem_separatedAll hX.1).1 f hf) hε
    filter_upwards [eventually_forall_mem X h₁] with j hj
    exact Eq.mpr (congrArg₂ (List.Forall₂ _) (reflectAppend_torus D μ (cj j) X Y)
      (reflectAppend_torus D μ c X Y)) (forall₂_normC1_lt_map_append hε hj)
theorem exists_bound_of_forall_mem (A : List (Set (Fin 4 → ℝ)))
    (hA : ∀ B ∈ A, MetricNotions.IsCompactWrt InfiniteLattice.euclidDist B) :
    ∃ R : ℝ, ∀ B ∈ A, ∀ x ∈ B, TorusMetric.euclidNormVec x ≤ R := by
  induction A with
  | nil => exact ⟨0, by simp⟩
  | cons B A ih =>
    obtain ⟨R₁, h₁⟩ := LatticeDataSeq.exists_bound_of_isCompactWrt (hA B (by simp))
    obtain ⟨R₂, h₂⟩ := ih fun B' hB' => hA B' (by simp [hB'])
    refine ⟨max R₁ R₂, fun B' hB' x hx => ?_⟩
    rcases List.mem_cons.1 hB' with rfl | hB'
    · exact (h₁ x hx).trans (le_max_left _ _)
    · exact (h₂ B' hB' x hx).trans (le_max_right _ _)
theorem side_dataAt {E : Ambient} (S : LatticeDataSeq D E) (j : ℕ+) :
    (dataAt S j).side = S.ℓ j := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.side_standingAt <;> assumption
theorem eventually_hasDiameterLE (S : LatticeDataSeq D euclidean) (A : List (Set (Fin 4 → ℝ)))
    (hA : ∀ B ∈ A, MetricNotions.IsCompactWrt InfiniteLattice.euclidDist B) :
    ∀ᶠ j in atTop, TestFunctions.HasDiameterLE (⋃ B ∈ A, B) ((dataAt S j).side / 2) := by
  obtain ⟨R, hR⟩ := exists_bound_of_forall_mem A hA
  have hℓ : Tendsto S.ℓ atTop atTop := S.isSideSequence
  filter_upwards [hℓ.eventually_ge_atTop (4 * R)] with j hj x hx y hy
  obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.1 hx
  obtain ⟨B', hB', hyB⟩ := mem_iUnion₂.1 hy
  have h₁ := hR B hB x hxB
  have h₂ := hR B' hB' y hyB
  have h₃ : TorusMetric.euclidNormVec (x - y) ≤
      TorusMetric.euclidNormVec x + TorusMetric.euclidNormVec y := by
    simp only [LatticeDataSeq.euclidNormVec_eq_norm, WithLp.toLp_sub]
    exact norm_sub_le _ _
  rw [side_dataAt]
  show TorusMetric.euclidNormVec (x - y) ≤ _
  linarith
theorem eventually_movedListInSharedSets (hc : MovingMirrorSets.SharedSetsProperties) {E : Ambient}
    (S : LatticeDataSeq D E) {μ : Fin 4} {c : ℝ} {cj : ℕ+ → ℝ}
    (hcj : ∀ j, IsNearLinkLevel S c j (cj j)) {X Y : FnList D E}
    (hX : X ∈ separatedWithin D E ((CoordMirror.mk μ c).upperSide D E))
    (hY : Y ∈ separatedWithin D E ((CoordMirror.mk μ c).upperSide D E)) :
    ∀ᶠ j in atTop, MovingMirrorSets.MovedListInSharedSets D E μ c (cj j) X Y := by
  obtain ⟨⟨hη, -⟩, hmove, -⟩ := hc D E μ c X Y hX hY
  filter_upwards [(tendsto_meshOf S).eventually_lt_const hη] with j hj
  exact hmove _ (by
    have h₁ := (hcj j).2
    linarith)
theorem eventually_fitsInTorus (hc : MovingMirrorSets.SharedSetsProperties)
    (S : LatticeDataSeq D euclidean) {μ : Fin 4} {c : ℝ} {cj : ℕ+ → ℝ}
    (hcj : ∀ j, IsNearLinkLevel S c j (cj j)) {X Y : FnList D euclidean}
    (hX : X ∈ separatedWithin D euclidean ((CoordMirror.mk μ c).upperSide D euclidean))
    (hY : Y ∈ separatedWithin D euclidean ((CoordMirror.mk μ c).upperSide D euclidean)) :
    ∀ᶠ j in atTop, LimitSpaces.FitsInTorus (S.standingAt j)
      ((CoordMirror.mk μ (cj j)).reflectAppend D euclidean X Y) := by
  obtain ⟨⟨-, -, hcomp, -⟩, -, -⟩ := hc D euclidean μ c X Y hX hY
  filter_upwards [eventually_movedListInSharedSets hc S hcj hX hY,
    eventually_hasDiameterLE S _ hcomp] with j h₁ h₂
  refine ⟨fun f hf => (h₁.2.2.1 f hf).2, fun x hx y hy => ?_⟩
  have hsub : ∀ x ∈ LimitSpaces.Ambient.euclidean.listSupport (S.standingAt j)
      ((CoordMirror.mk μ (cj j)).reflectAppend D euclidean X Y),
      x ∈ ⋃ B ∈ MovingMirrorSets.sharedSets D euclidean μ c X Y, B := fun x hx => by
    obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.1 hx
    obtain ⟨B, hB, hR⟩ := exists_mem_of_forall₂ h₁.1 hf
    exact mem_iUnion₂.2 ⟨B, hB, hR.2 hxf⟩
  exact h₂ x (hsub x hx) y (hsub y hy)
theorem tendsto_reflectAppend_euclidean (hs : Sides.HyperplaneSidesClaim)
    (hc : MovingMirrorSets.SharedSetsProperties)
    (hsig : LatticeDataSeq.CenteredFunctionalsConverge)
    (hfr : LimitSpaces.Ambient.uniformBoundednessEquicontinuity)
    (hm : LimitSpaces.MirrorTranslation.Claim)
    (hF : CutoffMirrors.CentredMomentCumulantExpansion)
    (S : LatticeDataSeq D euclidean) (T : FunctionalFamily D euclidean)
    (hST : S.TendsToFamily T) (μ : Fin 4) {c : ℝ} {cj : ℕ+ → ℝ}
    (hcj : ∀ j, IsNearLinkLevel S c j (cj j)) {X Y : FnList D euclidean}
    (hX : X ∈ separatedWithin D euclidean ((CoordMirror.mk μ c).upperSide D euclidean))
    (hY : Y ∈ separatedWithin D euclidean ((CoordMirror.mk μ c).upperSide D euclidean)) :
    Tendsto (fun j => S.centredAt j
        ((CoordMirror.mk μ (cj j)).reflectAppend D euclidean X Y))
      atTop (𝓝 (evalOrZero (FunctionalFamily.centeredFunctional T)
        ((CoordMirror.mk μ c).reflectAppend D euclidean X Y))) := by
  by_cases hq : X = [] ∧ Y = []
  · obtain ⟨rfl, rfl⟩ := hq
    exact tendsto_centredAt hsig S T hST (emptyList D euclidean).2
  obtain ⟨⟨hη, -, hcomp, hpos, hfar⟩, hmove, -⟩ :=
    hc D euclidean μ c X Y hX hY
  have hlen : 1 ≤ (MovingMirrorSets.sharedSets D euclidean μ c X Y).length := by
    have hne : X.length + Y.length ≠ 0 := by
      intro h0
      exact hq ⟨List.length_eq_zero_iff.1 (by omega), List.length_eq_zero_iff.1 (by omega)⟩
    simp only [MovingMirrorSets.sharedSets, List.length_append, List.length_map]
    omega
  let s := D.toStandingParameters
  let A : List (Set (LimitSpaces.Ambient.euclidean.Carrier s)) :=
    MovingMirrorSets.sharedSets D euclidean μ c X Y
  let 𝒥 : Set ℕ+ := {j | meshOf S j ≤ MovingMirrorSets.margin D euclidean μ c X Y ∧
    LimitSpaces.TorusSideAdmissible (S.mirrorDataAt j) A.get}
  have hJ : ∀ᶠ j in atTop, j ∈ 𝒥 := by
    filter_upwards [(tendsto_meshOf S).eventually_lt_const hη,
      eventually_hasDiameterLE S _ hcomp] with j h₁ h₂
    refine ⟨h₁.le, fun x hx y hy => ?_⟩
    have hsub : ∀ x ∈ ⋃ l, A.get l, x ∈ ⋃ B ∈ A, B := fun x hx => by
      obtain ⟨l, hl⟩ := mem_iUnion.1 hx
      exact mem_iUnion₂.2 ⟨_, List.get_mem _ _, hl⟩
    exact h₂ x (hsub x hx) y (hsub y hy)
  have hmoved : ∀ j ∈ 𝒥, MovingMirrorSets.MovedListInSharedSets D euclidean μ c (cj j)
      X Y := fun j hj => hmove _ (by
    have h₁ := (hcj j).2
    have h₂ := hj.1
    linarith)
  have hZ0 := hmove c (by simpa using hη.le)
  have hWc : ∀ l, LimitSpaces.Ambient.euclidean.IsCompactSubset s (A.get l) := fun l =>
    hcomp _ (List.get_mem _ _)
  have hWd : Pairwise (Function.onFun Disjoint A.get) := fun l l' hll =>
    disjoint_of_setDist_pos D euclidean (lt_of_lt_of_le hpos (hfar l l' hll))
  have hP := ((hfr sharpOne A.length hlen).1 s .euclidean).2.2 A.get hWc hWd
  have hseq := (hfr sharpOne A.length hlen).2.2.2.2.2 s A.get hWc hWd 𝒥
    (fun j => S.mirrorDataAt j) (infinite_of_eventually_mem hJ) (fun _ => rfl) (fun j => j.2.2)
  have hmem : ∀ h : LimitSpaces.Ambient.euclidean.C1ProductSpace s A.get,
      (List.ofFn (LimitSpaces.Ambient.components h) : FnList D euclidean) ∈
        separatedAll D euclidean := fun h =>
    separatedN_subset_separatedAll D euclidean _ ⟨List.length_ofFn, fun g hg => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
        exact (hP.1 h).2 i,
      List.pairwise_ofFn.2 fun i k hik => (hP.1 h).1.2 hik.ne⟩
  refine tendsto_along_moving_lists (P := .euclidean) (s := s) (A := A) hJ hseq.2
    (fun j Z => S.centredAt j Z)
    (fun Z => evalOrZero (FunctionalFamily.centeredFunctional T) Z) ?_ ?_
    (Zm := fun j => (CoordMirror.mk μ (cj j)).reflectAppend D euclidean X Y)
    (forall₂_imp_of_mem hZ0.1 (p := fun g => g ∈ compactC1 D ℝ euclidean)
      (fun g hg => hZ0.2.2.1 g hg) fun g B hp hR => ⟨hp, hR⟩)
    (fun j hj => forall₂_imp_of_mem (hmoved j hj).1
      (p := fun g => g ∈ compactC1 D ℝ euclidean)
      (fun g hg => (hmoved j hj).2.2.1 g hg) fun g B hp hR => ⟨hp, hR⟩) ?_
  · intro j h
    obtain ⟨h₁, -, h₃, -⟩ := (hfr sharpOne A.length hlen).2.2.2.1 s (S.mirrorDataAt j) A.get rfl
      hWc hWd j.2.2
    have he : CutoffMirrors.MirrorData.IsAdmissibleArg (D := S.mirrorDataAt j)
        (fun l => TestFunctions.periodize
          (PeriodicLattice.torusSide (S.mirrorDataAt j).L (S.mirrorDataAt j).m) (h l).1) :=
      ⟨fun l => (h₁ (h l).1 ((hP.1 h).1.1 l)).1, h₃ h⟩
    have e₁ : S.centredAt j (List.ofFn (LimitSpaces.Ambient.components h)) =
        (S.mirrorDataAt j).gibbsFunctionalList (List.ofFn fun l =>
          TestFunctions.periodize
            (PeriodicLattice.torusSide (S.mirrorDataAt j).L (S.mirrorDataAt j).m) (h l).1) :=
      congrArg (S.mirrorDataAt j).gibbsFunctionalList
        (LimitSpaces.periodizeList_ofFn (S.standingAt j)
          (LimitSpaces.Ambient.components h))
    exact (e₁.trans ((gibbsFunctionalList_ofFn (S.mirrorDataAt j) _).trans
      (gibbsFunctional_eq_re hF _ he))).symm
  · exact fun h => tendsto_centredAt hsig S T hST (hmem h)
  · intro ε hε
    have habs := tendsto_abs_sub_level S hcj
    have h₁ : ∀ f ∈ X, ∀ᶠ j in atTop, LimitSpaces.Ambient.euclidean.normC1 s
        (LimitSpaces.Ambient.euclidean.reflectFun s μ (cj j) f -
          LimitSpaces.Ambient.euclidean.reflectFun s μ c f) < ε := fun f hf =>
      eventually_normC1_reflectFun_sub_lt hs hm hfr D .euclidean μ habs
        ((isSeparatedList_of_mem_separatedAll hX.1).1 f hf) hε
    filter_upwards [eventually_forall_mem X h₁] with j hj
    exact Eq.mpr (congrArg₂ (List.Forall₂ _) (reflectAppend_euclidean D μ (cj j) X Y)
      (reflectAppend_euclidean D μ c X Y)) (forall₂_normC1_lt_map_append hε hj)
theorem eventually_suppUnion_subset (hs : Sides.HyperplaneSidesClaim) {E : Ambient} {μ : Fin 4}
    {c : ℝ} {cj : ℕ+ → ℝ} (hcj : Tendsto (fun j => |cj j - c|) atTop (𝓝 0))
    (I : (CoordMirror.mk μ c).PositivityInstance D E) :
    ∀ᶠ j in atTop, I.suppUnion ⊆ (CoordMirror.mk μ (cj j)).upperSide D E := by
  have h : ∀ i, ∀ᶠ j in atTop, ∀ f ∈ (I.tuples i).1,
      closedSupport D E f ⊆ (CoordMirror.mk μ (cj j)).upperSide D E := fun i =>
    eventually_forall_mem _ fun f hf => eventually_closedSupport_subset_upperSide hs E hcj
      ((isSeparatedList_of_mem_separatedAll (I.tuples i).2.1).1 f hf) ((I.tuples i).2.2 f hf)
  filter_upwards [eventually_all.2 h] with j hj x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.1 hi
  exact hj i f hf hxf
theorem reflectedGram_nonneg_torus (hs : Sides.HyperplaneSidesClaim)
    (hin : CutoffMirrors.TupleInequality.Statement)
    (S : LatticeDataSeq D torus) {μ : Fin 4} {c c' : ℝ} {j : ℕ+}
    (hlink : c' ∈ LimitSpaces.halfShiftedMultiplesOf (meshOf S j))
    (I : (CoordMirror.mk μ c).PositivityInstance D torus)
    (hsub : I.suppUnion ⊆ (CoordMirror.mk μ c').upperSide D torus) :
    (reflectedGram S I (CoordMirror.mk μ c') j).im = 0 ∧
      0 ≤ (reflectedGram S I (CoordMirror.mk μ c') j).re := by
  let d : MirrorData := ⟨S.standingAtExp j D.m, S.β j, S.β_pos j⟩
  have hlip : ∀ i, ∀ f ∈ ((I.tuples i).1 : FnList d torus),
      TestFunctions.IsLipschitzFor (cutoffMirrorData d μ).torusDist f := fun i f hf => by
    obtain ⟨-, -, -, -, -, -, -, h8⟩ := ((hs D 0 0).1 .periodic).1
    exact (h8 f ((isSeparatedList_of_mem_separatedAll (I.tuples i).2.1).1 f hf)).2.2
  have h := reflected_sum_nonneg_at_cutoff hin d μ hlink I.one_le_size
    (fun i => ((I.tuples i).1 : FnList d torus)) I.coeffs hlip
    (fun i => (isSeparatedList_of_mem_separatedAll (I.tuples i).2.1).2)
    (fun i f hf x hx => hsub (mem_iUnion.2 ⟨i, mem_iUnion₂.2 ⟨f, hf, hx⟩⟩))
  have e : reflectedGram S I (CoordMirror.mk μ c') j =
      ∑ i, ∑ k, conj (I.coeffs i) * I.coeffs k *
        (((cutoffMirrorData d μ).gibbsFunctionalList ((CoordMirror.mk μ c').reflectAppend d torus
          ((I.tuples i).1 : FnList d torus) ((I.tuples k).1 : FnList d torus)) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [S.centredAt_torus]
    rfl
  rw [e]
  exact h
theorem reflectedGram_nonneg_euclidean (hs : Sides.HyperplaneSidesClaim)
    (hin : CutoffMirrors.TupleInequality.Statement)
    (htr : LimitSpaces.Periodization.Properties)
    (S : LatticeDataSeq D euclidean) {μ : Fin 4} {c c' : ℝ} {j : ℕ+}
    (hlink : c' ∈ LimitSpaces.halfShiftedMultiplesOf (meshOf S j))
    (I : (CoordMirror.mk μ c).PositivityInstance D euclidean)
    (hfit : ∀ i k, LimitSpaces.FitsInTorus (S.standingAt j)
      ((CoordMirror.mk μ c').reflectAppend D euclidean (I.tuples i).1 (I.tuples k).1))
    (hslab : ∀ i, ∀ f ∈ (I.tuples i).1, closedSupport D euclidean f ⊆
      coordSet μ fun t => c' < t ∧ t < c' + (dataAt S j).side / 2) :
    (∀ i, ElementsInOpenSlab S j (CoordMirror.mk μ c') (I.tuples i).1) ∧
      (reflectedGram S I (CoordMirror.mk μ c') j).im = 0 ∧
      0 ≤ (reflectedGram S I (CoordMirror.mk μ c') j).re := by
  let d : MirrorData := dataAt S j
  let s' : Conventions.StandingParameters := S.standingAt j
  have hcompact : ∀ i, ∀ f ∈ (I.tuples i).1,
      LimitSpaces.Ambient.euclidean.IsCompactSubset d.toStandingParameters
        (LimitSpaces.Ambient.euclidean.closedSupport d.toStandingParameters f) := fun i f hf =>
    ((isSeparatedList_of_mem_separatedAll (I.tuples i).2.1).1 f hf).2
  have hcat := fun i k => (htr d).2.2 (I.tuples i).1 (I.tuples k).1 (hcompact i) (hcompact k) μ c'
    (hfit i k)
  have hfits : ∀ i, LimitSpaces.FitsInTorus s' (I.tuples i).1 := fun i => (hcat i i).1
  have hslabs : ∀ i, ElementsInOpenSlab S j (CoordMirror.mk μ c') (I.tuples i).1 := by
    intro i g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    have hsup : LimitSpaces.Ambient.euclidean.SupportedWithin d.toStandingParameters
        (LimitSpaces.Ambient.euclidean.listSupport d.toStandingParameters (I.tuples i).1) f :=
      ⟨hcompact i f hf, fun x hx => mem_iUnion₂.2 ⟨f, hf, hx⟩⟩
    exact ((htr d).1 _ f f (hfits i).2 hsup hsup).2.2.2.2.2.2 μ c' (hslab i f hf) |>.2
  let Xl : Fin I.size → List ((Fin 4 → ℝ) → ℝ) := fun i => (I.tuples i).1
  have hsepT := fun i => (htr d).2.1 _ (Xl i).get
  have hlists : ∀ i, LimitSpaces.periodizeList s' (Xl i) =
      List.ofFn fun l => LimitSpaces.periodizeFun s' ((Xl i).get l) := fun i => by
    have e := LimitSpaces.periodizeList_ofFn s' (Xl i).get
    rwa [List.ofFn_get] at e
  have hr : ∀ i, LimitSpaces.Ambient.periodic.IsSepLipTuple s' univ
      (fun l => LimitSpaces.periodizeFun s' ((Xl i).get l)) := fun i =>
    (hsepT i (isSepLipList_of_mem hs euclidean (I.tuples i).2.1)
      (by rw [List.ofFn_get]; exact hfits i)).1
  let X' : Fin I.size → FnList d torus := fun i => LimitSpaces.periodizeList s' (I.tuples i).1
  have hlip : ∀ i, ∀ f ∈ X' i, TestFunctions.IsLipschitzFor (cutoffMirrorData d μ).torusDist f := by
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
  have h := reflected_sum_nonneg_at_cutoff hin d μ hlink I.one_le_size X' I.coeffs hlip hdis
    (fun i => hslabs i)
  have e : reflectedGram S I (CoordMirror.mk μ c') j =
      ∑ i, ∑ k, conj (I.coeffs i) * I.coeffs k *
        (((cutoffMirrorData d μ).gibbsFunctionalList
          ((CoordMirror.mk μ c').reflectAppend d torus (X' i) (X' k)) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    have e₁ : S.centredAt j ((CoordMirror.mk μ c').reflectAppend D euclidean
        (I.tuples i).1 (I.tuples k).1) = (cutoffMirrorData d μ).gibbsFunctionalList
          ((CoordMirror.mk μ c').reflectAppend d torus (X' i) (X' k)) :=
      congrArg (cutoffMirrorData d μ).gibbsFunctionalList (hcat i k).2.2
    exact congrArg (fun z : ℝ => conj (I.coeffs i) * I.coeffs k * (z : ℂ)) e₁
  rw [e]
  exact ⟨hslabs, h⟩
theorem apply_le_euclidNormVec (y : Fin 4 → ℝ) (μ : Fin 4) :
    y μ ≤ TorusMetric.euclidNormVec y := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.LimitPositivity.coord_le_euclidNormVec <;> assumption
theorem eventually_closedSupport_subset_slab (hs : Sides.HyperplaneSidesClaim)
    (S : LatticeDataSeq D euclidean) {μ : Fin 4} {c : ℝ} {cj : ℕ+ → ℝ}
    (hcj : Tendsto (fun j => |cj j - c|) atTop (𝓝 0))
    {f : Point D euclidean → ℝ} (hf : f ∈ compactC1 D ℝ euclidean)
    (hsub : closedSupport D euclidean f ⊆ (CoordMirror.mk μ c).upperSide D euclidean) :
    ∀ᶠ j in atTop, closedSupport D euclidean f ⊆
      coordSet μ fun t => cj j < t ∧ t < cj j + (dataAt S j).side / 2 := by
  obtain ⟨R, hR⟩ := LatticeDataSeq.exists_bound_of_isCompactWrt hf.2
  have hℓ : Tendsto S.ℓ atTop atTop := S.isSideSequence
  filter_upwards [eventually_closedSupport_subset_upperSide hs euclidean hcj hf hsub,
    hcj.eventually_lt_const one_pos, hℓ.eventually_ge_atTop (2 * (R + |c| + 2))]
    with j h₁ h₂ h₃ y hy
  refine ⟨h₁ hy, ?_⟩
  have h₄ : y μ ≤ R := (apply_le_euclidNormVec y μ).trans (hR y hy)
  have h₅ := (abs_lt.1 h₂).1
  have h₆ := neg_abs_le c
  rw [side_dataAt]
  linarith
theorem eventuallyPositive (hs : Sides.HyperplaneSidesClaim)
    (hc : MovingMirrorSets.SharedSetsProperties)
    (hin : CutoffMirrors.TupleInequality.Statement)
    (htr : LimitSpaces.Periodization.Properties) {E : Ambient}
    (S : LatticeDataSeq D E) (μ : Fin 4) {c : ℝ} {cj : ℕ+ → ℝ}
    (hcj : ∀ j, IsNearLinkLevel S c j (cj j)) : EventuallyPositive S μ c cj := by
  intro I
  have habs := tendsto_abs_sub_level S hcj
  cases E with
  | torus =>
    filter_upwards [eventually_suppUnion_subset hs habs I] with j hj
    obtain ⟨h₁, h₂⟩ := reflectedGram_nonneg_torus hs hin S (hcj j).1 I hj
    exact ⟨hj, fun _ => trivial, h₁, h₂⟩
  | euclidean =>
    have hfit : ∀ᶠ j in atTop, ∀ i k, LimitSpaces.FitsInTorus (S.standingAt j)
        ((CoordMirror.mk μ (cj j)).reflectAppend D euclidean (I.tuples i).1 (I.tuples k).1) :=
      eventually_all.2 fun i => eventually_all.2 fun k =>
        eventually_fitsInTorus hc S hcj (I.tuples i).2 (I.tuples k).2
    have hslab : ∀ᶠ j in atTop, ∀ i, ∀ f ∈ (I.tuples i).1, closedSupport D euclidean f ⊆
        coordSet μ fun t => cj j < t ∧ t < cj j + (dataAt S j).side / 2 :=
      eventually_all.2 fun i => eventually_forall_mem _ fun f hf =>
        eventually_closedSupport_subset_slab hs S habs
          ((isSeparatedList_of_mem_separatedAll (I.tuples i).2.1).1 f hf) ((I.tuples i).2.2 f hf)
    filter_upwards [eventually_suppUnion_subset hs habs I, hfit, hslab] with j h₁ h₂ h₃
    obtain ⟨h₄, h₅, h₆⟩ := reflectedGram_nonneg_euclidean hs hin htr S (hcj j).1 I h₂ h₃
    exact ⟨h₁, h₄, h₅, h₆⟩
theorem tendsAlongMovingMirror (hs : Sides.HyperplaneSidesClaim)
    (hc : MovingMirrorSets.SharedSetsProperties)
    (hsig : LatticeDataSeq.CenteredFunctionalsConverge)
    (hfr : LimitSpaces.Ambient.uniformBoundednessEquicontinuity)
    (hm : LimitSpaces.MirrorTranslation.Claim)
    (hF : CutoffMirrors.CentredMomentCumulantExpansion) {E : Ambient}
    (S : LatticeDataSeq D E) (T : FunctionalFamily D E) (hST : S.TendsToFamily T)
    (μ : Fin 4) {c : ℝ} {cj : ℕ+ → ℝ} (hcj : ∀ j, IsNearLinkLevel S c j (cj j)) :
    TendsAlongMovingMirror S T μ c cj := by
  intro X Y
  cases E with
  | torus =>
    refine ⟨?_, tendsto_reflectAppend_torus hs hc hsig hfr hm hF S T hST μ hcj X.2 Y.2⟩
    filter_upwards [eventually_movedListInSharedSets hc S hcj X.2 Y.2] with j hj
    exact isSepLipList_of_mem hs torus (separatedN_subset_separatedAll D torus _ hj.2)
  | euclidean =>
    refine ⟨?_, tendsto_reflectAppend_euclidean hs hc hsig hfr hm hF S T hST μ hcj X.2 Y.2⟩
    filter_upwards [eventually_movedListInSharedSets hc S hcj X.2 Y.2,
      eventually_fitsInTorus hc S hcj X.2 Y.2] with j h₁ h₂
    exact ⟨isSepLipList_of_mem hs euclidean (separatedN_subset_separatedAll D euclidean _ h₁.2),
      h₂⟩
theorem tendsto_reflectedGram {E : Ambient} (S : LatticeDataSeq D E)
    (T : FunctionalFamily D E) {μ : Fin 4} {c : ℝ} {cj : ℕ+ → ℝ}
    (hlim : TendsAlongMovingMirror S T μ c cj) (I : (CoordMirror.mk μ c).PositivityInstance D E) :
    Tendsto (fun j => reflectedGram S I (CoordMirror.mk μ (cj j)) j) atTop
      (𝓝 (I.lhs fun X => (FunctionalFamily.centeredFunctional T X : ℂ))) := by
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun k _ => ?_
  rw [evalOrZeroC_ofReal]
  exact ((Complex.continuous_ofReal.tendsto _).comp (hlim (I.tuples i) (I.tuples k)).2).const_mul _
theorem movingMirrorLimit_holds (hs : Sides.HyperplaneSidesClaim)
    (hc : MovingMirrorSets.SharedSetsProperties)
    (hsig : LatticeDataSeq.CenteredFunctionalsConverge)
    (hfr : LimitSpaces.Ambient.uniformBoundednessEquicontinuity)
    (hm : LimitSpaces.MirrorTranslation.Claim)
    (hF : CutoffMirrors.CentredMomentCumulantExpansion)
    (hin : CutoffMirrors.TupleInequality.Statement)
    (htr : LimitSpaces.Periodization.Properties) : MovingMirrorLimit := by
  intro D E S T hST μ c
  refine ⟨fun j => exists_isNearLinkLevel S c j, fun cj hcj => ?_⟩
  have hpos := eventuallyPositive hs hc hin htr S μ hcj
  have hlim := tendsAlongMovingMirror hs hc hsig hfr hm hF S T hST μ hcj
  refine ⟨hpos, hlim, fun I => ?_⟩
  have hclosed : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  exact hclosed.mem_of_tendsto (tendsto_reflectedGram S T hlim I)
    ((hpos I).mono fun j hj => hj.2.2)
end YangMills.Construction.ReflectionPositivity.AxisMirror.MovingMirror
end
