import YangMills.Construction.FamiliesOfLimits.ReflectionPositivityOnTuplesAtEveryCoordinateMirror
import YangMills.Construction.FamiliesOfLimits.TheTwoListsOfProperties
import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesOfFourSpace
import YangMills.Construction.ReflectionPositivity.NestedLatticesAdicPointsAndMirrorsProof
import YangMills.Construction.TorusOrFourSpace.BallsTuplesInABallAndAdmissibleTuplesOfFourSpace
import YangMills.Construction.TotalDensitiesGiveASystem.DataOfTheLimitsAtLargeBlockingFactors
import YangMills.Construction.TotalDensitiesGiveASystem.WhatALimitAlongToriHas
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ComplexOrder Matrix Topology
noncomputable section
namespace YangMills.Construction
open AmbientPoints
namespace TotalDensities
open LimitTheorem ToriLimits ToriLimits.GrowingVolumeLimits
open TestFunctions (IsLipschitzFor euclidDistTorus closedBallTorus sharpNormTorus HasSeparatedSupportsTorus)
namespace ToriLimit
section Preliminaries
variable (s : Conventions.StandingParameters)
private theorem mem_separatedTuples_iff_closureWrt {d : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ}
    (hd : ∀ x y, d x y = TorusMetric.euclidNormVec (x - y)) {n : ℕ}
    (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    f ∈ separatedTuples s .euclidean n ↔
      (∀ i, ContDiff ℝ 1 (f i)) ∧
        (∀ i, MetricNotions.IsCompactWrt d (MetricNotions.closureWrt d {y | f i y ≠ 0})) ∧
        ∀ i k, i ≠ k → Disjoint (MetricNotions.closureWrt d {y | f i y ≠ 0})
          (MetricNotions.closureWrt d {y | f k y ≠ 0}) := by
  have hs : ∀ i, MetricNotions.closureWrt d {y | f i y ≠ 0} = tsupport (f i) := fun i =>
    SeparatedTuplesR4.closureWrt_euclid_eq_closure hd _
  have hc : ∀ Z : Set (Fin 4 → ℝ), MetricNotions.IsCompactWrt d Z ↔ IsCompact Z :=
    SeparatedTuplesR4.isCompactWrt_euclid_iff hd
  refine (ToriLimits.mem_sepTuplesR4_iff s f).trans ?_
  simp only [hs, hc]
  exact Iff.rfl
private theorem mem_sepC1Tuples_iff_separatedTuples (Y : PeriodicSpace.Params) {n : ℕ}
    (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    f ∈ PeriodicSpace.Kind.sepC1Tuples Y .euclidean n ↔
      f ∈ separatedTuples s .euclidean n :=
  (mem_separatedTuples_iff_closureWrt s (d := PeriodicSpace.Kind.quotDist Y .euclidean)
    (PeriodicSpace.EuclideanCase.quotDist_euclidean_eq Y) f).symm
private theorem atTop_inf_principal_neBot {𝒥 : Set ℕ+} (h : 𝒥.Infinite) : (atTop ⊓ 𝓟 𝒥 : Filter ℕ+).NeBot := by
  refine inf_principal_neBot_iff.2 fun U hU => ?_
  obtain ⟨a, ha⟩ := mem_atTop_sets.1 hU
  obtain ⟨b, hb, hab⟩ := h.exists_gt a
  exact ⟨b, ha b hab.le, hb⟩
abbrev _root_.YangMills.SharedProofs.p125520 := @atTop_inf_principal_neBot
private theorem isTupleMultilinear_of_add_smul {s : Conventions.StandingParameters} {n : ℕ}
    (Ψ : separatedTuples s .euclidean n → ℝ)
    (hadd : ∀ (i : Fin n) (X X' : separatedTuples s .euclidean n),
      (∀ j, j ≠ i → X.1 j = X'.1 j) →
      ∀ hm : Function.update X.1 i (X.1 i + X'.1 i) ∈ separatedTuples s .euclidean n,
        Ψ ⟨_, hm⟩ = Ψ X + Ψ X')
    (hsmul : ∀ (i : Fin n) (X : separatedTuples s .euclidean n) (c : ℝ)
      (hm : Function.update X.1 i (c • X.1 i) ∈ separatedTuples s .euclidean n),
        Ψ ⟨_, hm⟩ = c * Ψ X) :
    IsTupleMultilinear Ψ := by
  intro A hA
  let T : ((i : Fin n) → c1Submodule (A i)) → separatedTuples s .euclidean n := fun g =>
    ⟨fun i => (g i : Pt s .euclidean → ℝ),
      mem_separatedTuples_of_forall_mem_c1 hA fun i => (g i).2⟩
  have hT : ∀ (g : (i : Fin n) → c1Submodule (A i)) (i : Fin n)
      (x : c1Submodule (A i)) (j : Fin n), j ≠ i →
      (T (Function.update g i x)).1 j = (T g).1 j := fun g i x j hj => by
    simp only [T, Function.update_of_ne hj]
  have hTi : ∀ (g : (i : Fin n) → c1Submodule (A i)) (i : Fin n)
      (x : c1Submodule (A i)),
      (T (Function.update g i x)).1 i = x := fun g i x => by
    simp only [T, Function.update_self]
  refine ⟨{ toFun := fun g => Ψ (T g), map_update_add' := ?_, map_update_smul' := ?_ },
    fun g => rfl⟩
  · intro inst g i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have e : Function.update (T (Function.update g i x)).1 i
        ((T (Function.update g i x)).1 i + (T (Function.update g i y)).1 i) =
        (T (Function.update g i (x + y))).1 := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, hTi, hTi, hTi]
        rfl
      · rw [Function.update_of_ne hj, hT _ _ _ _ hj, hT _ _ _ _ hj]
    have hm := e ▸ (T (Function.update g i (x + y))).2
    rw [← hadd i (T (Function.update g i x)) (T (Function.update g i y))
      (fun j hj => by rw [hT _ _ _ _ hj, hT _ _ _ _ hj]) hm]
    exact congrArg Ψ (Subtype.ext e.symm)
  · intro inst g i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have e : Function.update (T (Function.update g i x)).1 i
        (c • (T (Function.update g i x)).1 i) = (T (Function.update g i (c • x))).1 := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, hTi, hTi]
        rfl
      · rw [Function.update_of_ne hj, hT _ _ _ _ hj, hT _ _ _ _ hj]
    have hm := e ▸ (T (Function.update g i (c • x))).2
    rw [smul_eq_mul, ← hsmul i (T (Function.update g i x)) c hm]
    exact congrArg Ψ (Subtype.ext e.symm)
end Preliminaries
section Tail
variable {D : ToriLimits.Setup}
private theorem tendsto_add_const_atTop (j₀ : ℕ+) : Tendsto (fun j : ℕ+ => j + j₀) atTop atTop :=
  tendsto_atTop_mono (fun j => by
    show j ≤ j + j₀
    exact (PNat.lt_add_right j j₀).le) tendsto_id
private theorem tendsto_pnat_coe_atTop : Tendsto (fun K : ℕ+ => (K : ℕ)) atTop atTop := by apply _root_.YangMills.Construction.ReflectionPositivity.AdicLattices.tendsto_pnat_coe_atTop <;> assumption
private def shiftedSeq (Q : TotalDensities.ToriSequence D.L) (j₀ : ℕ+)
    (h : ∀ j, j₀ ≤ j → D.referenceExponent ≤ (Q.m j : ℕ)) :
    ToriLimits.ToriSequence D where
  K j := Q.K (j + j₀)
  m j := Q.m (j + j₀)
  β j := Q.β (j + j₀)
  β_pos _ := Q.β_pos _
  referenceExponent_le j := h _ (PNat.lt_add_left j₀ j).le
  K_tendsto := tendsto_pnat_coe_atTop.comp (Q.K_tendsto.comp (tendsto_add_const_atTop j₀))
  m_tendsto := tendsto_pnat_coe_atTop.comp (Q.m_tendsto.comp (tendsto_add_const_atTop j₀))
private theorem sharpNormTorus_one_le {ℓ : ℝ} {M : ℝ} (hM : 1 ≤ M) (f : TorusMetric.Torus4 ℓ → ℝ) :
    sharpNormTorus 1 f ≤ sharpNormTorus M f := by
  have hl : 0 ≤ TestFunctions.lipConstTorus f := Real.sInf_nonneg fun C hC => hC.1
  unfold sharpNormTorus
  refine max_le_max le_rfl ?_
  nlinarith
private theorem sharpNormTorus_nonneg' {ℓ : ℝ} (M : ℝ) (f : TorusMetric.Torus4 ℓ → ℝ) :
    0 ≤ sharpNormTorus M f :=
  le_trans (Real.iSup_nonneg fun _ => norm_nonneg _) (le_max_left _ _)
private def boundFamilyOf (c : ℕ → ℝ → ℝ → ℝ)
    (h₀ : ∀ n, 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ c n d R)
    (h₁ : ∀ n, 2 ≤ n → ∀ R : ℝ, 0 < R → AntitoneOn (fun d => c n d R) (Ioi 0)) :
    PeriodicSpace.BoundFamily where
  val := c
  nonneg := h₀
  antitoneOn := h₁
private theorem hasBallwiseBoundAlong_shiftedSeq (Q : TotalDensities.ToriSequence D.L) (j₀ : ℕ+)
    (h : ∀ j, j₀ ≤ j → D.referenceExponent ≤ (Q.m j : ℕ)) {c : ℕ → ℝ → ℝ → ℝ}
    (h₀ : ∀ n, 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ c n d R)
    (h₁ : ∀ n, 2 ≤ n → ∀ R : ℝ, 0 < R → AntitoneOn (fun d => c n d R) (Ioi 0))
    (hP : Q.HasBallwiseBound c) :
    HasBallwiseBoundAlong (shiftedSeq Q j₀ h) (boundFamilyOf c h₀ h₁) := by
  intro n hn d R hd hR
  refine ⟨h₀ n hn d R hd hR, fun j hs f hf hb hsep => ?_⟩
  have hat : HasSeparatedSupportsTorus (ℓ := PeriodicLattice.torusSide D.L (Q.m (j + j₀))) (E := ℝ) f d :=
    (supportsApartBy_torus_iff f d).1 ⟨hd, hsep⟩
  have hball : ∀ i, ∃ x, tsupport (X := PeriodicLattice.FourTorus D.L (Q.m (j + j₀))) (f i) ⊆
      closedBallTorus x R := fun i => by
    obtain ⟨x, hx⟩ := hb i
    exact ⟨x, fun y hy => hx ((tsupport_eq_of_torus (s := ⟨D.L, D.admissible, Q.K (j + j₀), Q.m (j + j₀)⟩) (f i)).ge hy)⟩
  have h₂ := hP (j + j₀) n hn R d hR hd f (fun i => hf.1 i) hball hat
  refine h₂.trans (mul_le_mul_of_nonneg_left ?_ (h₀ n hn d R hd hR))
  refine Finset.prod_le_prod (fun i _ => sharpNormTorus_nonneg' _ _) fun i _ => sharpNormTorus_one_le ?_ _
  exact_mod_cast D.one_le_M
end Tail
private def familyOnR4 (s : Conventions.StandingParameters) (S : LimitTheorem.CumulantFamily) :
    TupleMapFamily s .euclidean :=
  fun n hn X => S n hn (Continuum.SeparatedFourTuples.sepLenEquiv s n X)
section Mirrors
open SeparatedTuples (SepTuple push pushList supportedIn)
open LatticeConventions (basisVector)
open TupleLists (ofList toList)
private theorem axialReflect_eq (s : Conventions.StandingParameters) (M : Mirrors.ReflectingHyperplane) {μ : Fin 4}
    (hμ : M.normalVec = Pi.single μ 1) (x : Fin 4 → ℝ) :
    (AmbientMirror.reflect s .euclidean (AmbientMirror.ofAxisLevel .euclidean μ M.offset) x : Fin 4 → ℝ) =
      M.reflect x := by
  have hdot : ∀ y : Fin 4 → ℝ, LatticeConventions.euclidDot (basisVector μ) y = y μ := fun y => by
    simp [LatticeConventions.euclidDot, basisVector, Pi.single_apply]
  have hv : TorusMetric.euclidNormVec (basisVector μ) ^ 2 = 1 := by
    unfold TorusMetric.euclidNormVec
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [basisVector, Pi.single_apply]
  refine (AmbientMirror.reflect_euclidean_apply s
    (⟨⟨basisVector μ, Or.inl ⟨μ, rfl⟩⟩, M.offset⟩ : InfiniteLattice.EuclideanMirrors.AffineMirror) x).trans ?_
  show x - (2 * (LatticeConventions.euclidDot (basisVector μ) x - M.offset) /
    TorusMetric.euclidNormVec (basisVector μ) ^ 2) • basisVector μ = _
  rw [hdot, hv]
  unfold Mirrors.ReflectingHyperplane.reflect
  rw [hμ]
  simp [basisVector, dotProduct, Pi.single_apply]
private theorem mem_positiveSide_iff (s : Conventions.StandingParameters) (M : Mirrors.ReflectingHyperplane)
    {μ : Fin 4} (hμ : M.normalVec = Pi.single μ 1) (x : Fin 4 → ℝ) :
    x ∈ AmbientMirror.positiveSide s .euclidean (AmbientMirror.ofAxisLevel .euclidean μ M.offset) ↔
      x ∈ M.positiveSide := by
  show M.offset < LatticeConventions.euclidDot (basisVector μ) x ↔ M.normalVec ⬝ᵥ x > M.offset
  rw [hμ]
  simp [LatticeConventions.euclidDot, basisVector, dotProduct, Pi.single_apply]
private theorem invMap_reflect (M : Mirrors.ReflectingHyperplane) {μ : Fin 4}
    (hμ : M.normalVec = Pi.single μ 1) (s : Conventions.StandingParameters) :
    SeparatedTuples.invMap M.reflect = M.reflect := by
  have hi : Function.Involutive M.reflect := fun x => by
    have h := AmbientMirror.reflect_reflect s .euclidean (AmbientMirror.ofAxisLevel .euclidean μ M.offset) x
    rwa [show (AmbientMirror.reflect s .euclidean (AmbientMirror.ofAxisLevel .euclidean μ M.offset) x :
        Fin 4 → ℝ) = M.reflect x from axialReflect_eq s M hμ x,
      show (AmbientMirror.reflect s .euclidean (AmbientMirror.ofAxisLevel .euclidean μ M.offset)
        (M.reflect x) : Fin 4 → ℝ) = M.reflect (M.reflect x) from axialReflect_eq s M hμ _] at h
  funext x
  have h := Function.leftInverse_invFun hi.injective (M.reflect x)
  unfold SeparatedTuples.invMap
  rw [hi x] at h
  exact h
private theorem reflectionPositiveAxial_of_family (hFacts : SeparatedTuples.BasicFacts.MainFacts)
    (s : Conventions.StandingParameters) (S : LimitTheorem.CumulantFamily)
    (h : ∀ (μ : Fin 4) (c : ℝ), AmbientMirror.IsReflectionPositive s .euclidean
      (AmbientMirror.ofAxisLevel .euclidean μ c) (centredOfMaps (familyOnR4 s S))) :
    IsReflectionPositiveAxial (centredOf S) := by
  intro M hM J _ X hX c
  obtain ⟨μ, hμ'⟩ := hM
  have hμ : M.normalVec = Pi.single μ 1 := hμ'
  have hiso : SeparatedTuples.IsEuclidIsometry M.reflect := by
    rw [M.reflect_eq_hyperplaneReflect]
    exact InfiniteLattice.euclidNormVec_hyperplaneReflect_sub
      (Mirrors.dotProduct_self_ne_zero_of_mem M.normalVec_mem) _
  have hact := hFacts.1 M.reflect hiso
  have hprod := hFacts.2.2.1 M
  have hinv := invMap_reflect M hμ s
  let Y : Fin J → AmbientMirror.separatedIn
      (AmbientMirror.positiveSide s .euclidean (AmbientMirror.ofAxisLevel .euclidean μ M.offset)) :=
    fun b => ⟨⟨(X b).1.length, (X b).1.get⟩,
      (mem_separatedTuples_r4_iff _).2 (TupleLists.get_mem_disjointSupportTuples (X b)),
      fun i x hx => (mem_positiveSide_iff s M hμ x).2
        (hX b _ (List.get_mem _ i) ((tsupport_eq_of_r4 _).le hx))⟩
  have key : ∀ b b', centredOfMaps (familyOnR4 s S)
      (AmbientMirror.reflectAppend s .euclidean _ (Y b) (Y b')) =
      (centredOf S) (SepTuple.juxt (push M.reflect (X b)) (X b')) := by
    intro b b'
    set Z := AmbientMirror.reflectAppend s .euclidean _ (Y b) (Y b') with hZ
    have e₁ := centredOfMaps_r4 (familyOnR4 s S) S (fun _ _ _ => rfl)
      (⟨Z.1.2, Z.2⟩ : separatedTuples s .euclidean Z.1.1)
    refine e₁.trans ?_
    have e₂ : SepTuple.juxt (push M.reflect (X b)) (X b') =
        toList ⟨Z.1.1, toR4Tuple (⟨Z.1.2, Z.2⟩ : separatedTuples s .euclidean Z.1.1)⟩ := by
      refine Subtype.ext ?_
      have hv : (push M.reflect (X b)).1 = (X b).1.map fun f => f ∘ M.reflect := by
        unfold push
        rw [dif_pos (hact (X b) (X b)).1]
        simp [pushList, hinv]
      have e₃ : (X b).1.map (fun f => f ∘ M.reflect) =
          List.ofFn (fun i => (X b).1.get i ∘ M.reflect) := by
        conv_lhs => rw [← List.ofFn_get (X b).1]
        rw [List.map_ofFn]
        rfl
      let g : Fin (X b).1.length → Pt s .euclidean → ℝ := (X b).1.get
      have e₄ : transportTuple
          (AmbientMirror.reflect s .euclidean (AmbientMirror.ofAxisLevel .euclidean μ M.offset)) g =
          fun i => (X b).1.get i ∘ M.reflect := by
        funext i
        rw [AmbientMirror.transportTuple_reflect]
        funext x
        exact congrArg (g i) (axialReflect_eq s M hμ x)
      rw [SepTuple.juxt_val (hprod _ _ (hX b) (hX b')).2, hv, e₃]
      refine (?_ : _ = List.ofFn (Fin.append (fun i => (X b).1.get i ∘ M.reflect) (X b').1.get :
        _ → SeparatedTuples.RealValued)).trans ?_
      · rw [List.ofFn_fin_append, List.ofFn_get]
      · exact congrArg (fun k : Fin (X b).1.length → SeparatedTuples.RealValued =>
          List.ofFn (Fin.append k (X b').1.get : _ → SeparatedTuples.RealValued)) e₄.symm
    show _ = TestSpaces.centredOfCumulants S (ofList (SepTuple.juxt (push M.reflect (X b)) (X b')))
    rw [e₂, TupleLists.ofList_toList]
  obtain ⟨him, hre⟩ := h μ M.offset J Y c
  have e : AmbientMirror.gramSum s .euclidean _ (centredOfMaps (familyOnR4 s S)) Y c =
      ∑ b, ∑ b', (starRingEnd ℂ) (c b) * c b' *
        ((centredOf S (SepTuple.juxt (push M.reflect (X b)) (X b')) : ℝ) : ℂ) :=
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by rw [key]
  rw [e] at him hre
  exact Complex.le_def.2 ⟨hre, him.symm⟩
end Mirrors
section Limit
variable {D : ToriLimits.Setup} (T : ToriLimits.ToriSequence D) {J : Sequences.PNatIndexSet}
  {Ξ : D.LimitHierarchy} (s : Conventions.StandingParameters)
private def hierarchyOnR4 (Ξ : D.LimitHierarchy) : TupleMapFamily s .euclidean := fun n hn Y =>
  Ξ.func n hn ⟨Y.1, (mem_sepC1Tuples_iff_separatedTuples s D.euclidParams Y.1).2 Y.2⟩
variable {s}
private theorem tendsto_connected_along (hΞ : T.IsLimitHierarchy J Ξ) (n : ℕ) (hn : 2 ≤ n)
    (Y : separatedTuples s .euclidean n) :
    Tendsto (fun j => T.connected j Y.1) (atTop ⊓ 𝓟 J.carrier)
      (𝓝 ((hierarchyOnR4 s Ξ n hn Y : ℝ) : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨j', hj'⟩ := hΞ n hn ⟨Y.1, (mem_sepC1Tuples_iff_separatedTuples s D.euclidParams Y.1).2 Y.2⟩ ε hε
  refine eventually_inf_principal.2 ?_
  filter_upwards [eventually_ge_atTop (⟨j'.toNat + 1, by omega⟩ : ℕ+)] with j hle hjJ
  have hle' : j'.toNat + 1 ≤ (j : ℕ) := hle
  obtain ⟨_, hlt⟩ := hj' j hjJ (by omega)
  rw [dist_eq_norm]
  exact hlt
private theorem hierarchyOnR4_multilinear (Ξ : D.LimitHierarchy) (n : ℕ) (hn : 2 ≤ n) :
    IsTupleMultilinear (hierarchyOnR4 s Ξ n hn) := by
  refine isTupleMultilinear_of_add_smul _ (fun i X X' he hm => ?_) fun i X c hm => ?_
  · exact (Ξ.multilinear n hn i ⟨X.1, _⟩ ⟨X'.1, _⟩ he).1 _
  · exact (Ξ.multilinear n hn i ⟨X.1, _⟩ ⟨X.1, _⟩ fun _ _ => rfl).2 c _
private theorem hierarchyOnR4_reflectionPositive
    (hMirrors : FamiliesOfLimits.CoordinateMirrorPositivity.Holds)
    {C : PeriodicSpace.BoundFamily} (cl : LimitRequirements T C J Ξ) :
    FamiliesOfLimits.R4ReflectionPositive (hierarchyOnR4 s Ξ) := by
  intro M hM
  have hv : FamiliesOfLimits.LimitFamilyAsVolumeLimit.HierarchyAgrees Ξ
      (FamiliesOfLimits.complexOfMaps (hierarchyOnR4 s Ξ)) := fun _ _ _ _ => rfl
  obtain ⟨-, -, -, hRP⟩ := hMirrors D T C J Ξ cl s _ hv
  have hreal : FamiliesOfLimits.TupleHilbert.realPartMaps
      (FamiliesOfLimits.complexOfMaps (hierarchyOnR4 s Ξ)) = hierarchyOnR4 s Ξ := by
    funext n hn X
    simp [FamiliesOfLimits.TupleHilbert.realPartMaps, FamiliesOfLimits.complexOfMaps]
  obtain ⟨μ, hμ⟩ := (AmbientMirror.isAxial_euclidean_iff M).1 hM
  obtain ⟨⟨nv, hnv⟩, c⟩ := M
  have hμ' : nv = LatticeConventions.basisVector μ := hμ
  subst hμ'
  have := (hRP μ c).2
  rw [FamiliesOfLimits.TupleHilbert.centredMap, hreal] at this
  exact this
end Limit
section Main
variable {D : ToriLimits.Setup}
private theorem hierarchyOnR4_eq_limit (Q : TotalDensities.ToriSequence D.L) (j₀ : ℕ+)
    (h : ∀ j, j₀ ≤ j → D.referenceExponent ≤ (Q.m j : ℕ)) {S : LimitTheorem.CumulantFamily}
    (hS : Q.HasCumulantLimit S) {J : Sequences.PNatIndexSet} {Ξ : D.LimitHierarchy}
    (hΞ : (shiftedSeq Q j₀ h).IsLimitHierarchy J Ξ) (s : Conventions.StandingParameters) {n : ℕ}
    (hn : 2 ≤ n) (X : TestSpaces.SepTupleOfCard n) :
    hierarchyOnR4 s Ξ n hn ⟨X.1, (mem_separatedTuples_r4_iff X.1).2 X.2⟩ = S n hn X := by
  have h₁ := tendsto_connected_along (s := s) (shiftedSeq Q j₀ h) hΞ n hn
    ⟨X.1, (mem_separatedTuples_r4_iff X.1).2 X.2⟩
  have h₂ : Tendsto (fun j => (shiftedSeq Q j₀ h).connected j X.1) (atTop ⊓ 𝓟 J.carrier)
      (𝓝 ((S n hn X : ℝ) : ℂ)) :=
    ((hS n hn X).comp (tendsto_add_const_atTop j₀)).mono_left inf_le_left
  have := atTop_inf_principal_neBot J.infinite
  exact Complex.ofReal_injective (tendsto_nhds_unique h₁ h₂)
private theorem invFun_eq_hyperoctahedral {r : Motions.RigidMotion} {w : TorusTransport.hyperoctahedral}
    (hw : ∀ x, r.mat.mulVec x = w.1 x) (x : Fin 4 → ℝ) :
    r.invFun x = (w⁻¹ : TorusTransport.hyperoctahedral).1 (x - r.shift) := by
  have h₁ : r.mat.mulVec (r.invFun x) + r.shift = x := r.toFun_invFun x
  have h₂ : w.1 (r.invFun x) = x - r.shift := by rw [← hw]; exact eq_sub_of_add_eq h₁
  rw [← h₂]
  show r.invFun x = (w.1)⁻¹ (w.1 (r.invFun x))
  simp
end Main
theorem claim_of_limitSetup
    (hData : TotalDensitiesGiveASystem.LargeOddBlockingFactorsHaveLimitSetup)
    (hThm : ToriLimits.GrowingVolumeLimits.Holds)
    (hMirrors : FamiliesOfLimits.CoordinateMirrorPositivity.Holds)
    (hFacts : SeparatedTuples.BasicFacts.MainFacts) : Claim := by
  obtain ⟨floor, hD⟩ := hData
  refine ⟨floor, fun L hodd hfl Q c hc₀ hc₁ hP S hS => ?_⟩
  obtain ⟨D, rfl⟩ := hD L hodd hfl
  obtain ⟨j₀, h⟩ : ∃ j₀, ∀ j, j₀ ≤ j → D.referenceExponent ≤ (Q.m j : ℕ) :=
    eventually_atTop.1 ((tendsto_pnat_coe_atTop.comp Q.m_tendsto).eventually_ge_atTop D.referenceExponent)
  have hPB := hasBallwiseBoundAlong_shiftedSeq Q j₀ h hc₀ hc₁ hP
  obtain ⟨-, hEx, hCl⟩ := hThm D (shiftedSeq Q j₀ h) _ hPB
  obtain ⟨J, hJ⟩ := hEx ToriLimits.BoundedFamily.empty
  have hJ₀ := hJ.toIsConvergenceSet
  have hΞ := hJ₀.isLimitHierarchy_lim
  have cl := hCl J _ hJ₀ hΞ
  generalize hJ₀.lim = Ξ at hΞ cl
  have hval : ∀ (n : ℕ) (hn : 2 ≤ n) (X : TestSpaces.SepTupleOfCard n),
      Ξ.evalSigma ⟨n, X.1⟩ = S n hn X := by
    intro n hn X
    have s : Conventions.StandingParameters := ⟨D.L, D.admissible, 1, 1⟩
    rw [← hierarchyOnR4_eq_limit Q j₀ h hS hΞ s hn X]
    exact PeriodicSpace.Kind.Hierarchy.evalSigma_of_sep Ξ hn
      ⟨X.1, (mem_sepC1Tuples_iff_separatedTuples s D.euclidParams X.1).2
        ((mem_separatedTuples_r4_iff X.1).2 X.2)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn X Y ς hY
    have hp := cl.symmetries.perm_invariant n hn
      ⟨X.1, (mem_sepC1Tuples_iff_separatedTuples ⟨D.L, D.admissible, 1, 1⟩ _ X.1).2
        ((mem_separatedTuples_r4_iff X.1).2 X.2)⟩ ς
    rw [← hval n hn Y, ← hval n hn X, hY]
    refine hp.trans ?_
    exact (PeriodicSpace.Kind.Hierarchy.evalSigma_of_sep Ξ hn _).symm
  · rintro r ⟨w, hw⟩ n hn X
    have hm := UpperHalfTensors.actOnTuple_mem_disjointSupportTuples r X.2
    refine ⟨hm, ?_⟩
    let s : Conventions.StandingParameters := ⟨D.L, D.admissible, 1, 1⟩
    let r₀ : Motions.RigidMotion := ⟨r.mat, r.mat_mem, 0⟩
    have hm₀ := UpperHalfTensors.actOnTuple_mem_disjointSupportTuples r₀ X.2
    have e₀ : GrowingTori.hyperoctahedralActFamily w X.1 = Motions.actOnTuple r₀ X.1 := by
      funext i x
      show X.1 i ((w⁻¹ : TorusTransport.hyperoctahedral).1 x) = X.1 i (r₀.invFun x)
      rw [invFun_eq_hyperoctahedral (r := r₀) (w := w) hw x]
      simp [r₀]
    have e₁ : GrowingTori.shiftFamily r.shift (Motions.actOnTuple r₀ X.1) =
        Motions.actOnTuple r X.1 := by
      funext i x
      rw [GrowingTori.shiftFamily_apply]
      show X.1 i (r₀.invFun (x - r.shift)) = X.1 i (r.invFun x)
      rw [invFun_eq_hyperoctahedral (r := r₀) (w := w) hw, invFun_eq_hyperoctahedral hw x]
      simp [r₀]
    have h₁ := cl.symmetries.hyperoctahedral_invariant n hn
      ⟨X.1, (mem_sepC1Tuples_iff_separatedTuples s _ X.1).2
        ((mem_separatedTuples_r4_iff X.1).2 X.2)⟩ w
    have h₂ := cl.symmetries.shift_invariant n hn
      ⟨Motions.actOnTuple r₀ X.1, (mem_sepC1Tuples_iff_separatedTuples s _ _).2
        ((mem_separatedTuples_r4_iff _).2 hm₀)⟩ r.shift
    rw [← hval n hn ⟨_, hm⟩, ← hval n hn X]
    show Ξ.evalSigma ⟨n, Motions.actOnTuple r X.1⟩ = _
    rw [← e₁]
    refine h₂.trans ?_
    refine Eq.trans ?_ (h₁.trans ?_)
    · rw [e₀]
      exact (PeriodicSpace.Kind.Hierarchy.evalSigma_of_sep Ξ hn _).symm
    · exact (PeriodicSpace.Kind.Hierarchy.evalSigma_of_sep Ξ hn _).symm
  · intro s n hn
    have e : familyOnR4 s S n hn = hierarchyOnR4 s Ξ n hn := by
      funext Y
      exact (hierarchyOnR4_eq_limit Q j₀ h hS hΞ s hn
        (Continuum.SeparatedFourTuples.sepLenEquiv s n Y)).symm
    show IsTupleMultilinear (familyOnR4 s S n hn)
    rw [e]
    exact hierarchyOnR4_multilinear (D := D) (s := s) Ξ n hn
  · refine reflectionPositiveAxial_of_family hFacts ⟨D.L, D.admissible, 1, 1⟩ S fun μ c => ?_
    have e : familyOnR4 ⟨D.L, D.admissible, 1, 1⟩ S = hierarchyOnR4 ⟨D.L, D.admissible, 1, 1⟩ Ξ := by
      funext n hn Y
      exact (hierarchyOnR4_eq_limit Q j₀ h hS hΞ _ hn
        (Continuum.SeparatedFourTuples.sepLenEquiv _ n Y)).symm
    rw [e]
    exact hierarchyOnR4_reflectionPositive (s := ⟨D.L, D.admissible, 1, 1⟩) (shiftedSeq Q j₀ h) hMirrors cl _
      ((AmbientMirror.isAxial_euclidean_iff (AmbientMirror.ofAxisLevel .euclidean μ c)).2 ⟨μ, rfl⟩)
end ToriLimit
end TotalDensities
end YangMills.Construction
end
