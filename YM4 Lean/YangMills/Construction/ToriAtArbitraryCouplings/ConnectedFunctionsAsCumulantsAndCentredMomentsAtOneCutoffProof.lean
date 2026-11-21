import YangMills.Construction.Continuum.FactsOfCentredMomentsMirrorsClassesAndTheSeparatingFamilyProof
import YangMills.Construction.Lattice.LatticeIntegralIsEntireAndPositive
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.ToriAtArbitraryCouplings.BoundedFormsAlongABoundedSequenceProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings.OneCutoffCumulants
open ReflectionPositivity.AxisMirror (Ambient)
open ConnectedFunctionExpansion (IsBoundedOnTorus)
private abbrev asCouplingData (D : ReflectionPositivity.AxisMirror.MirrorData) :
    ConnectedFunctions.CouplingData :=
  ⟨D.toStandingParameters, D.β, D.β_pos⟩
private abbrev asCutoffData (D : ReflectionPositivity.AxisMirror.MirrorData) :
    ReflectionPositivity.CutoffMirrors.MirrorData :=
  ⟨D.toStandingParameters, D.β, D.β_pos, 0⟩
private theorem isBoundedOnTorus_of_bound {L m : ℕ} {f : PeriodicLattice.FourTorus L m → ℝ}
    (h : TestFunctions.IsBoundedFun f) : IsBoundedOnTorus f := by apply _root_.YangMills.Construction.ToriAtArbitraryCouplings.BoundedMultilinearForms.isBoundedOnTorus_of_isBoundedFun <;> assumption
private theorem smearedObservable_ofReal {L m : ℕ} {j : ℤ} (g : PeriodicLattice.FourTorus L m → ℝ)
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    PeriodicLattice.smearedObservable (fun x => (g x : ℂ)) U =
      ((PeriodicLattice.smearedObservable g U : ℝ) : ℂ) := by apply _root_.YangMills.Construction.ContinuumSetting.smearedObservable_ofReal <;> assumption
variable (D : ReflectionPositivity.AxisMirror.MirrorData)
private theorem latticeMoment_eq_centredMoment {q : ℕ} (f : Fin q → D.Torus → ℝ) :
    (D.latticeMoment (List.ofFn f) : ℂ) =
      (asCouplingData D).centredMomentFn ((asCouplingData D).ofRealTuple f) := by
  have hexp : ∀ g : D.Torus → ℝ,
      (asCouplingData D).expect ((asCouplingData D).obs ((asCouplingData D).ofRealFun g)) =
        ((PeriodicLattice.gibbsExpectation D.L D.m D.K D.β
          (PeriodicLattice.smearedObservable g) : ℝ) : ℂ) := by
    intro g
    unfold ConnectedFunctions.CouplingData.expect PeriodicLattice.gibbsExpectation
    rw [← integral_complex_ofReal]
    refine congrArg _ (funext fun U => ?_)
    exact smearedObservable_ofReal g U
  unfold ReflectionPositivity.AxisMirror.MirrorData.latticeMoment
    ConnectedFunctions.CouplingData.centredMomentFn
  change _ = PeriodicLattice.gibbsExpectation D.L D.m D.K D.β _
  unfold PeriodicLattice.gibbsExpectation
  rw [← integral_complex_ofReal]
  refine congrArg _ (funext fun U => ?_)
  rw [List.map_ofFn, List.prod_ofFn, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  unfold ConnectedFunctions.CouplingData.centred
  change ((D.centeredObservable (f l) U : ℝ) : ℂ) = _ -
    (asCouplingData D).expect ((asCouplingData D).obs ((asCouplingData D).ofRealFun (f l)))
  rw [hexp (f l)]
  unfold ReflectionPositivity.AxisMirror.MirrorData.centeredObservable
  rw [Complex.ofReal_sub]
  congr 1
  exact (smearedObservable_ofReal (f l) U).symm
section Hypotheses
variable (hP : ConnectedFunctionExpansion.Statement)
  (hE : PartitionFunctionAnalyticity.Statement)
  (hA : ConnectedFunctions.CentredIdentityAtAllFunctions)
  (hC : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
  (hN : LipschitzEstimates.Combined)
include hE in
private theorem coupling_mem_nonvanishing :
    (D.β : ℂ) ∈ PeriodicLattice.nonvanishingCouplings D.L D.m D.K :=
  (hE D.L D.m D.K D.isAdmissible D.m.pos).2.2.2.2.1.2.2 D.β
include hE in
private theorem isBoundedOnTorus_of_hasFiniteLip {f : D.Torus → ℝ}
    (h : CutoffNotation.HasFiniteLip D.toStandingParameters f) : IsBoundedOnTorus f :=
  (hE D.L D.m 0 D.isAdmissible D.m.pos).2.2.2.2.2.1 f h
include hC in
private theorem isBoundedOnTorus_of_lipschitz {f : D.Torus → ℝ}
    (h : TestFunctions.IsLipschitzFor (asCutoffData D).torusDist f) : IsBoundedOnTorus f :=
  isBoundedOnTorus_of_bound ((hC (asCutoffData D)).2.1 ℝ f h).2.1
include hP hE in
private theorem isJointCumulant_holds : IsJointCumulant D := by
  intro n hn f hf
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := (hP D.L D.m D.K D.isAdmissible D.m.pos).2.2.2.2.2 k (D.β : ℂ) f
    (coupling_mem_nonvanishing D hE) hf
  unfold connectedValue
  rw [← h]
  unfold PeriodicLattice.observableCumulant
  rw [if_pos ⟨D.K.pos, by simpa using D.β_pos, by simp⟩]
  simp
include hP hE in
private theorem isSchwingerFunction_holds : IsSchwingerFunction D := by
  intro n hn f hf
  rw [isJointCumulant_holds D hP hE n (by omega) f fun i => isBoundedOnTorus_of_bound (hf.1 i)]
  rfl
include hP hE in
private theorem isLipschitzNumber_holds : IsLipschitzNumber D := by
  intro n hn f hf
  rw [isJointCumulant_holds D hP hE n (by omega) f fun i =>
      isBoundedOnTorus_of_hasFiniteLip D hE (hf i),
    CutoffNotation.connectedFn_ofReal]
  rfl
include hP hE in
private theorem isRealSymmMultilinear_holds : IsRealSymmMultilinear D := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := (hP D.L D.m D.K D.isAdmissible D.m.pos).2.2.2.1 k
  have hm := h.2 (D.β : ℂ) (coupling_mem_nonvanishing D hE)
  exact ⟨fun f hf => (h.1 f hf).2 D.β, fun f σ hf => hm.2 f σ hf,
    fun f i g g' a a' hf hg hg' => hm.1 f i g g' a a' hf hg hg'⟩
private theorem connectedValue_get {n : ℕ} (f : Fin n → D.Torus → ℝ) :
    connectedValue D (List.ofFn f).get = connectedValue D f :=
  ConnectedFunctions.CouplingData.apply_get_ofFn_eq (fun _ g => connectedValue D g) f
private theorem evalOrZero_restrictLip {n : ℕ} {f : Fin n → D.Torus → ℝ}
    (h : List.ofFn f ∈ (torusSide D).lipDisjointOfLength .torus n) :
    Ambient.evalOrZero (restrictLip D n) (List.ofFn f) =
      (connectedValue D f).re := by
  unfold Ambient.evalOrZero
  exact (dif_pos h).trans (congrArg Complex.re (connectedValue_get D f))
private theorem closedSupport_linComb_subset (f g : D.Torus → ℝ) (a b : ℝ) {A : Set D.Torus}
    (hf : (torusSide D).closedSupport .torus f ⊆ A) (hg : (torusSide D).closedSupport .torus g ⊆ A) :
    (torusSide D).closedSupport .torus (a • f + b • g) ⊆ A := by
  intro x hx
  by_contra hxA
  have hxf : x ∉ (torusSide D).closedSupport .torus f := fun h => hxA (hf h)
  have hxg : x ∉ (torusSide D).closedSupport .torus g := fun h => hxA (hg h)
  change ¬ ∀ r : ℝ, 0 < r → ∃ y ∈ {y | f y ≠ 0}, (torusSide D).pointDist .torus x y < r at hxf
  change ¬ ∀ r : ℝ, 0 < r → ∃ y ∈ {y | g y ≠ 0}, (torusSide D).pointDist .torus x y < r at hxg
  push Not at hxf hxg
  obtain ⟨r, hr, hfr⟩ := hxf
  obtain ⟨r', hr', hgr⟩ := hxg
  change ∀ r : ℝ, 0 < r → ∃ y ∈ {y | (a • f + b • g) y ≠ 0},
    (torusSide D).pointDist .torus x y < r at hx
  obtain ⟨y, hy, hd⟩ := hx (min r r') (lt_min hr hr')
  have hy0 : f y = 0 := by
    by_contra h
    exact absurd (lt_of_lt_of_le hd (min_le_left _ _)) (not_lt.2 (hfr y h))
  have hy1 : g y = 0 := by
    by_contra h
    exact absurd (lt_of_lt_of_le hd (min_le_right _ _)) (not_lt.2 (hgr y h))
  exact hy (by simp [hy0, hy1])
include hN in
private theorem linComb_mem_lipSuppIn (hL : 8 * 105 ^ 4 ≤ D.L)
    {A : Set ((torusSide D).Point .torus)}
    {f g : (torusSide D).Point .torus → ℝ} (hf : f ∈ (torusSide D).lipSuppIn .torus A)
    (hg : g ∈ (torusSide D).lipSuppIn .torus A) (a b : ℝ) :
    a • f + b • g ∈ (torusSide D).lipSuppIn .torus A := by
  obtain ⟨-, V, -, hV, -⟩ := (hN (torusSide D) hL 0 .torus).1.2.2
  have hf' : f ∈ V := by
    have : f ∈ (V : Set ((torusSide D).Point .torus → ℝ)) := by
      rw [hV]
      exact ⟨hf.1, hf.2.1, subset_univ _⟩
    exact this
  have hg' : g ∈ V := by
    have : g ∈ (V : Set ((torusSide D).Point .torus → ℝ)) := by
      rw [hV]
      exact ⟨hg.1, hg.2.1, subset_univ _⟩
    exact this
  have hc : a • f + b • g ∈ (V : Set ((torusSide D).Point .torus → ℝ)) :=
    V.add_mem (V.smul_mem a hf') (V.smul_mem b hg')
  rw [hV] at hc
  exact ⟨hc.1, hc.2.1, closedSupport_linComb_subset D f g a b hf.2.2 hg.2.2⟩
include hC in
private theorem isBoundedOnTorus_of_mem_lipDisjoint {n : ℕ} {f : Fin n → D.Torus → ℝ}
    (h : List.ofFn f ∈ (torusSide D).lipDisjointOfLength .torus n) (i : Fin n) :
    IsBoundedOnTorus (f i) :=
  isBoundedOnTorus_of_lipschitz D hC
    ((((torusSide D).ofFn_mem_lipDisjointOfLength_iff .torus f).1 h).1 i)
include hC hA in
private theorem isBoundedOnTorus_of_isC1Fn {f : D.Torus → ℝ}
    (h : AmbientPoints.IsC1Fn (s := D.toStandingParameters) (E := .torus) f) :
    IsBoundedOnTorus f :=
  isBoundedOnTorus_of_lipschitz D hC ((hA (asCouplingData D)).2.2.2.2.2.2 f
    ((AmbientPoints.isC1Fn_torus_iff (asCouplingData D) f).1 h))
omit hP hE hA hC hN in
private theorem coe_update_eq {X : Type*} [AddCommMonoid X] [Module ℝ X] {n : ℕ}
    {V : Fin n → Submodule ℝ X} (m : ∀ i, V i) (i : Fin n) (x : V i) :
    (fun j => (Function.update m i x j).1) = Function.update (fun j => (m j).1) i x.1 := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]
private theorem re_update_linComb_self {n : ℕ}
    (hlin : ∀ (f : Fin n → D.Torus → ℝ) (i : Fin n) (g g' : D.Torus → ℝ) (a a' : ℝ),
      (∀ k, IsBoundedOnTorus (f k)) → IsBoundedOnTorus g → IsBoundedOnTorus g' →
        connectedValue D (Function.update f i (a • g + a' • g')) =
          (a : ℂ) * connectedValue D (Function.update f i g) +
            (a' : ℂ) * connectedValue D (Function.update f i g'))
    (f : Fin n → D.Torus → ℝ) (i : Fin n) (g : D.Torus → ℝ) (a b : ℝ)
    (hf : ∀ k, IsBoundedOnTorus (f k)) (hg : IsBoundedOnTorus g) :
    (connectedValue D (Function.update f i (a • f i + b • g))).re =
      a * (connectedValue D f).re + b * (connectedValue D (Function.update f i g)).re := by
  rw [hlin f i (f i) g a b hf (hf i) hg, Function.update_eq_self, Complex.add_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
private theorem re_update_add {n : ℕ}
    (hlin : ∀ (f : Fin n → D.Torus → ℝ) (i : Fin n) (g g' : D.Torus → ℝ) (a a' : ℝ),
      (∀ k, IsBoundedOnTorus (f k)) → IsBoundedOnTorus g → IsBoundedOnTorus g' →
        connectedValue D (Function.update f i (a • g + a' • g')) =
          (a : ℂ) * connectedValue D (Function.update f i g) +
            (a' : ℂ) * connectedValue D (Function.update f i g'))
    (f : Fin n → D.Torus → ℝ) (i : Fin n) (x y : D.Torus → ℝ)
    (hf : ∀ k, IsBoundedOnTorus (f k)) (hx : IsBoundedOnTorus x) (hy : IsBoundedOnTorus y) :
    (connectedValue D (Function.update f i (x + y))).re =
      (connectedValue D (Function.update f i x)).re +
        (connectedValue D (Function.update f i y)).re := by
  have h := hlin f i x y 1 1 hf hx hy
  simp only [one_smul, Complex.ofReal_one, one_mul] at h
  rw [h, Complex.add_re]
private theorem re_update_smul {n : ℕ}
    (hlin : ∀ (f : Fin n → D.Torus → ℝ) (i : Fin n) (g g' : D.Torus → ℝ) (a a' : ℝ),
      (∀ k, IsBoundedOnTorus (f k)) → IsBoundedOnTorus g → IsBoundedOnTorus g' →
        connectedValue D (Function.update f i (a • g + a' • g')) =
          (a : ℂ) * connectedValue D (Function.update f i g) +
            (a' : ℂ) * connectedValue D (Function.update f i g'))
    (f : Fin n → D.Torus → ℝ) (i : Fin n) (x : D.Torus → ℝ) (c : ℝ)
    (hf : ∀ k, IsBoundedOnTorus (f k)) (hx : IsBoundedOnTorus x) :
    (connectedValue D (Function.update f i (c • x))).re =
      c * (connectedValue D (Function.update f i x)).re := by
  have h := hlin f i x x c 0 hf hx hx
  simp only [zero_smul, add_zero, Complex.ofReal_zero, zero_mul] at h
  rw [h, Complex.re_ofReal_mul]
include hP hE hA hC hN in
private theorem restrictionsMultilinearSymm_holds (hL : 8 * 105 ^ 4 ≤ D.L) :
    RestrictionsMultilinearSymm D := by
  intro n hn
  obtain ⟨-, hsymm, hlin⟩ := isRealSymmMultilinear_holds D hP hE n hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A hA' f hf i g hg a b
    have hbd : ∀ h ∈ (torusSide D).lipSuppIn .torus (A i),
        List.ofFn (Function.update f i h) ∈ (torusSide D).lipDisjointOfLength .torus n := by
      intro h hh
      refine (torusSide D).ofFn_mem_lipDisjointOfLength hA' fun k => ?_
      by_cases hk : k = i
      · subst hk
        simpa using hh
      · simpa [hk] using hf k
    have hfi : List.ofFn f ∈ (torusSide D).lipDisjointOfLength .torus n :=
      (torusSide D).ofFn_mem_lipDisjointOfLength hA' hf
    have hcomb := linComb_mem_lipSuppIn D hN hL (hf i) hg a b
    rw [evalOrZero_restrictLip D (hbd _ hcomb), evalOrZero_restrictLip D hfi,
      evalOrZero_restrictLip D (hbd _ hg)]
    have hgb : IsBoundedOnTorus g := isBoundedOnTorus_of_lipschitz D hC hg.1
    exact re_update_linComb_self D hlin f i g a b
      (isBoundedOnTorus_of_mem_lipDisjoint D hC hfi) hgb
  · intro f ς h h'
    exact congrArg Complex.re ((connectedValue_get D (f ∘ ς)).trans
      ((hsymm f ς (isBoundedOnTorus_of_mem_lipDisjoint D hC h)).trans
        (connectedValue_get D f).symm))
  · intro A hA'
    have hb : ∀ {i : Fin n} (x : AmbientPoints.c1Submodule (s := D.toStandingParameters)
        (E := .torus) (A i)), IsBoundedOnTorus x.1 :=
      fun x => isBoundedOnTorus_of_isC1Fn D hA hC x.2.1
    have hF : ∀ {u v : Fin n → D.Torus → ℝ}, u = v →
        (connectedValue D u).re = (connectedValue D v).re := fun h => by rw [h]
    refine ⟨{ toFun := fun g => (connectedValue D fun i => (g i).1).re
              map_update_add' := ?_
              map_update_smul' := ?_ }, fun g => rfl⟩
    · intro inst m i x y
      obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
      exact (hF (coe_update_eq m i (x + y))).trans
        ((re_update_add D hlin (fun j => (m j).1) i x.1 y.1 (fun k => hb (m k)) (hb x)
          (hb y)).trans
          (congrArg₂ (· + ·) (hF (coe_update_eq m i x).symm) (hF (coe_update_eq m i y).symm)))
    · intro inst m i c x
      obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
      exact (hF (coe_update_eq m i (c • x))).trans
        ((re_update_smul D hlin (fun j => (m j).1) i x.1 c (fun k => hb (m k)) (hb x)).trans
          (congrArg (c * ·) (hF (coe_update_eq m i x).symm)))
  · intro f ς
    change (connectedValue D (f.1 ∘ ς)).re = (connectedValue D f.1).re
    rw [hsymm f.1 ς fun i => isBoundedOnTorus_of_isC1Fn D hA hC (f.2.1 i).1]
include hP hE hA in
private theorem momentEqPartitionSum_holds : MomentEqPartitionSum D := by
  intro q f hf
  have hc := (hA (asCouplingData D)).2.2.1 q ((asCouplingData D).ofRealTuple f) fun _ => mem_univ _
  rw [latticeMoment_eq_centredMoment, hc]
  unfold ConnectedFunctions.CouplingData.centredFunctionalFn
  refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J hJ => ?_
  have hpos : 1 ≤ J.card := Finset.card_pos.mpr (π.nonempty_of_mem_parts hJ)
  exact (ConnectedFunctions.CouplingData.connected_ofReal (asCouplingData D)
    (AmbientPoints.restrictTuple f J)).trans
      (isJointCumulant_holds D hP hE _ hpos (AmbientPoints.restrictTuple f J)
        fun k => hf _).symm
include hP hE hA in
private theorem momentEqCentredMoment_holds : MomentEqCentredMoment D := by
  intro q f hf
  have hb : ∀ l, IsBoundedOnTorus (f l) := fun l => isBoundedOnTorus_of_hasFiniteLip D hE (hf l)
  refine ⟨?_, fun hd => ⟨fun l => ?_, fun l l' hll => ?_⟩⟩
  · rw [momentEqPartitionSum_holds D hP hE hA q f hb]
    unfold CutoffNotation.centredMomentFn
    refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J hJ => ?_
    have hpos : 1 ≤ J.card := Finset.card_pos.mpr (π.nonempty_of_mem_parts hJ)
    exact (isJointCumulant_holds D hP hE _ hpos (AmbientPoints.restrictTuple f J)
        fun k => hb _).trans
      (CutoffNotation.connectedFn_ofReal D.toStandingParameters D.β
        (AmbientPoints.restrictTuple f J)).symm
  · have h := hf l
    unfold CutoffNotation.HasFiniteLip CutoffNotation.lipConst PeriodicLattice.torusLipConst
      at h ⊢
    simpa only [← Complex.ofReal_sub, Complex.norm_real] using h
  · have hs : ∀ g : D.Torus → ℝ,
        (CutoffNotation.defaultMirrorData D.toStandingParameters).supp
          (fun x => (g x : ℂ)) = (CutoffNotation.defaultMirrorData D.toStandingParameters).supp g := by
      intro g
      unfold ReflectionPositivity.CutoffMirrors.MirrorData.supp
      congr 1
      ext x
      simp
    have h := hd l l' hll
    rw [← hs, ← hs] at h
    exact h
theorem statement_holds (hP : ConnectedFunctionExpansion.Statement)
    (hE : PartitionFunctionAnalyticity.Statement)
    (hA : ConnectedFunctions.CentredIdentityAtAllFunctions)
    (hC : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hN : LipschitzEstimates.Combined) : Statement := fun D hL =>
  ⟨⟨isJointCumulant_holds D hP hE, isSchwingerFunction_holds D hP hE,
      isLipschitzNumber_holds D hP hE, isRealSymmMultilinear_holds D hP hE,
      restrictionsMultilinearSymm_holds D hP hE hA hC hN hL⟩,
    momentEqPartitionSum_holds D hP hE hA, momentEqCentredMoment_holds D hP hE hA⟩
end Hypotheses
end YangMills.Construction.ToriAtArbitraryCouplings.OneCutoffCumulants
end
