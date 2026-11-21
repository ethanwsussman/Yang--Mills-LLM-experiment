import YangMills.Construction.InfiniteLattice.FactsOfTheSignsAtACutoffProof
import YangMills.Construction.ReflectionPositivity.ConcatenationOfSeparatedTuplesAtAMirror
import YangMills.Construction.ReflectionPositivity.CovarianceOfTheCurvatureDensity
import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesAndIsometriesOfOneTorus
import YangMills.Construction.ReflectionPositivity.ModulusAndTwoParallelMirrors
import YangMills.Construction.ReflectionPositivity.NestedLatticesLinkPositionsAndDensity
import YangMills.Construction.ReflectionPositivity.PositivityInTheLimits
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.TotalDensitiesGiveASystem.ListOfALimitOnATorusProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient CoordMirror)
open Filter Set
open scoped ENNReal Topology
noncomputable section
namespace TotalDensities.BoundedSequenceLimit
open YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ToriAtArbitraryCouplings.TorusSide
namespace Symmetry
private abbrev stdParams (s : TorusSide) : Conventions.StandingParameters :=
  s.asMirrorData.toStandingParameters
private theorem mem_disjointTuples_of_mem_sepOfLength
    (hNorms : ToriAtArbitraryCouplings.LipschitzEstimates.Combined) (s : TorusSide)
    (hL : 8 * 105 ^ 4 ≤ s.L) {n : ℕ} (hn : 1 ≤ n) {X : s.FnTuple .torus}
    (hX : X ∈ s.sepOfLength .torus n) :
    X ∈ ReflectionPositivity.TorusTuples.disjointTuples (stdParams s) n := by
  have h := (hNorms s hL 0 .torus).1.2.1.2 ⟨n, hn⟩ hX
  obtain ⟨hlen, hent, hpw⟩ := (s.mem_lipDisjointOfLength_iff .torus _ X).1 h
  refine ⟨⟨fun l => (hent _ (List.get_mem _ _)).1, fun l l' hl => ?_⟩, hlen⟩
  have hd : Disjoint (s.closedSupport .torus (X.get l)) (s.closedSupport .torus (X.get l')) := by
    rcases lt_or_gt_of_ne hl with h' | h'
    · exact List.pairwise_iff_get.1 hpw _ _ h'
    · exact (List.pairwise_iff_get.1 hpw _ _ h').symm
  exact Set.disjoint_iff_inter_eq_empty.1 hd
private theorem isCompactWrt_image {X : Type*} {d : X → X → ℝ} (r : X ≃ X)
    (hr : ∀ x y, d (r x) (r y) = d x y) {Z : Set X} (hZ : MetricNotions.IsCompactWrt d Z) :
    MetricNotions.IsCompactWrt d (r '' Z) := by apply _root_.YangMills.Construction.AtCutoff.SignFacts.IsCompactWrt.image <;> assumption
private theorem transport_mem (hNorms : ToriAtArbitraryCouplings.LipschitzEstimates.Combined)
    (hFacts : ReflectionPositivity.TorusTuples.SeparationAndSymmetry.Statement) (s : TorusSide)
    (hL : 8 * 105 ^ 4 ≤ s.L) (r : (stdParams s).Torus ≃ (stdParams s).Torus)
    (hr : ReflectionPositivity.TorusTuples.IsTorusIsometry (stdParams s) r)
    {g : s.Point .torus → ℝ}
    (hg : g ∈ Ambient.compactC1 s.asMirrorData ℝ .torus) :
    ReflectionPositivity.TorusTuples.transport (s := stdParams s) r g ∈
        Ambient.compactC1 s.asMirrorData ℝ .torus ∧
      s.closedSupport .torus (ReflectionPositivity.TorusTuples.transport (s := stdParams s) r g) =
        r '' s.closedSupport .torus g := by
  have hlip : ReflectionPositivity.TorusTuples.IsLipschitzReal (s := stdParams s) g := by
    have h := (hNorms s hL 0 .torus).1.2.1.1 univ
      (show g ∈ s.c1SuppIn .torus univ from ⟨hg.1, hg.2, subset_univ _⟩)
    exact h.1
  have h := (hFacts (stdParams s)).2.2.2.2.2.2.2.1 r hr g hlip
  have hsupp : s.closedSupport .torus
      (ReflectionPositivity.TorusTuples.transport (s := stdParams s) r g) =
      r '' s.closedSupport .torus g := h.2.1
  refine ⟨⟨h.2.2.2.2.2 hg.1, ?_⟩, hsupp⟩
  change s.IsCompactWrt .torus (s.closedSupport .torus _)
  rw [hsupp]
  exact isCompactWrt_image r hr hg.2
private theorem transportTuple_mem_sepOfLength
    (hNorms : ToriAtArbitraryCouplings.LipschitzEstimates.Combined)
    (hFacts : ReflectionPositivity.TorusTuples.SeparationAndSymmetry.Statement) (s : TorusSide)
    (hL : 8 * 105 ^ 4 ≤ s.L) (r : (stdParams s).Torus ≃ (stdParams s).Torus)
    (hr : ReflectionPositivity.TorusTuples.IsTorusIsometry (stdParams s) r) {n : ℕ}
    {X : s.FnTuple .torus} (hX : X ∈ s.sepOfLength .torus n) :
    ReflectionPositivity.TorusTuples.transportTuple (s := stdParams s) r X ∈
      s.sepOfLength .torus n := by
  refine ⟨(List.length_map _).trans hX.1, ?_, ?_⟩
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact (transport_mem hNorms hFacts s hL r hr (hX.2.1 g hg)).1
  · have h' : X.Pairwise fun a b =>
        Disjoint
          (s.closedSupport .torus (ReflectionPositivity.TorusTuples.transport (s := stdParams s) r a))
          (s.closedSupport .torus
            (ReflectionPositivity.TorusTuples.transport (s := stdParams s) r b)) :=
      hX.2.2.imp_of_mem fun {a b} ha hb h => by
        rw [(transport_mem hNorms hFacts s hL r hr (hX.2.1 a ha)).2,
          (transport_mem hNorms hFacts s hL r hr (hX.2.1 b hb)).2]
        exact (Set.disjoint_image_iff r.injective).2 h
    exact List.pairwise_map.2 h'
private theorem connectedFunction_get_congr (L m c : ℕ) (b : ℂ)
    (Y : List (PeriodicLattice.FourTorus L m → ℝ)) {n : ℕ}
    (h : Y.length = n) (g : Fin n → PeriodicLattice.FourTorus L m → ℝ)
    (hg : ∀ i, Y.get (Fin.cast h.symm i) = g i) :
    PeriodicLattice.connectedFunction L m c b Y.get =
      PeriodicLattice.connectedFunction L m c b g := by
  subst h
  have e : g = Y.get := funext fun i => (hg i).symm
  rw [e]
private theorem connectedSchwinger_comp_isometry
    (hIso : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    (hFacts : ReflectionPositivity.TorusTuples.SeparationAndSymmetry.Statement)
    (S : Conventions.StandingParameters) {k : ℕ+}
    {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 2 ≤ n)
    (X : ReflectionPositivity.TorusTuples.disjointTuples S n)
    (t : (ReflectionPositivity.TorusCutoffs.cutoffData S k β hβ 0).Symmetry) :
    SchwingerFunctions.IsTorusTestFamily (L := S.L) (m := S.m)
        (ReflectionPositivity.TorusTuples.componentFamily X.1 X.2.2) ∧
      SchwingerFunctions.IsTorusTestFamily (L := S.L) (m := S.m)
        (fun i => ReflectionPositivity.TorusTuples.componentFamily X.1 X.2.2 i ∘ t.toFun) ∧
      SchwingerFunctions.connectedSchwinger S.L S.m k β
          (fun i => ReflectionPositivity.TorusTuples.componentFamily X.1 X.2.2 i ∘ t.toFun) =
        SchwingerFunctions.connectedSchwinger S.L S.m k β
          (ReflectionPositivity.TorusTuples.componentFamily X.1 X.2.2) := by
  obtain ⟨hb, hm, d, hd⟩ := (hFacts S).2.2.2.1 n hn X
  obtain ⟨-, -, t', -, -, -, -, -, -, -, hc, -⟩ :=
    (hIso (ReflectionPositivity.TorusCutoffs.cutoffData S k β hβ 0)).2 t
  obtain ⟨hb', hm', hd', e⟩ :=
    hc n hn (ReflectionPositivity.TorusTuples.componentFamily X.1 X.2.2) d hb hm hd
  exact ⟨⟨hb, hm, d, hd⟩, ⟨hb', hm', d, hd'⟩, e⟩
private theorem get_map_cast_eq {α γ : Type*} (g : α → γ) (X : List α) {n : ℕ}
    (h : (X.map g).length = n) (h' : X.length = n) (i : Fin n) :
    (X.map g).get (Fin.cast h.symm i) = g (X.get (Fin.cast h'.symm i)) := by
  subst h'
  simp
private theorem connectedFunction_eq_connectedSchwinger
    (hCent : ToriAtArbitraryCouplings.OneCutoffCumulants.Statement)
    (D : ReflectionPositivity.AxisMirror.MirrorData) (hL : 8 * 105 ^ 4 ≤ D.L) {n : ℕ}
    (hn : 2 ≤ n) (f : Fin n → D.Torus → ℝ)
    (h : SchwingerFunctions.IsTorusTestFamily (L := D.L) (m := D.m) f) :
    PeriodicLattice.connectedFunction D.L D.m D.K (D.β : ℂ) f =
      SchwingerFunctions.connectedSchwinger D.L D.m D.K D.β f :=
  (hCent D hL).1.2.1 n hn f h
private theorem cumulantAt_transportTuple
    (hIso : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    (hCent : ToriAtArbitraryCouplings.OneCutoffCumulants.Statement)
    (hNorms : ToriAtArbitraryCouplings.LipschitzEstimates.Combined)
    (hFacts : ReflectionPositivity.TorusTuples.SeparationAndSymmetry.Statement) (s : TorusSide)
    (hL : 8 * 105 ^ 4 ≤ s.L) {k : ℕ+} {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 2 ≤ n)
    {X : s.FnTuple .torus} (hX : X ∈ s.sepOfLength .torus n)
    (r : (stdParams s).Torus ≃ (stdParams s).Torus)
    (t : (ReflectionPositivity.TorusCutoffs.cutoffData (stdParams s) k β hβ 0).Symmetry)
    (ht : t.toFun = r.symm) :
    s.cumulantAt k β (ReflectionPositivity.TorusTuples.transportTuple (s := stdParams s) r X) =
      s.cumulantAt k β X := by
  have hY := mem_disjointTuples_of_mem_sepOfLength hNorms s hL (by omega) hX
  obtain ⟨h₁, h₂, e⟩ := connectedSchwinger_comp_isometry hIso hFacts (stdParams s) hβ hn ⟨X, hY⟩ t
  have e₁ := connectedFunction_eq_connectedSchwinger hCent (s.mirrorDataOf k β hβ) hL hn _ h₁
  have e₂ := connectedFunction_eq_connectedSchwinger hCent (s.mirrorDataOf k β hβ) hL hn _ h₂
  have hlen : (ReflectionPositivity.TorusTuples.transportTuple (s := stdParams s) r X).length = n :=
    (List.length_map _).trans hY.2
  have a₁ : s.cumulantAt k β X = PeriodicLattice.connectedFunction s.L s.m k (β : ℂ)
      (ReflectionPositivity.TorusTuples.componentFamily (s := stdParams s) X hY.2) := by
    unfold TorusSide.cumulantAt
    exact connectedFunction_get_congr s.L s.m k (β : ℂ) X hY.2 _ fun i => rfl
  have a₂ : s.cumulantAt k β
      (ReflectionPositivity.TorusTuples.transportTuple (s := stdParams s) r X) =
      PeriodicLattice.connectedFunction s.L s.m k (β : ℂ)
        (fun i => ReflectionPositivity.TorusTuples.componentFamily (s := stdParams s) X hY.2 i ∘
          t.toFun) := by
    unfold TorusSide.cumulantAt
    refine connectedFunction_get_congr s.L s.m k (β : ℂ) _ hlen _ fun i => ?_
    rw [ht]
    exact get_map_cast_eq (ReflectionPositivity.TorusTuples.transport (s := stdParams s) r) X
      hlen hY.2 i
  rw [a₁, a₂]
  exact e₂.trans (e.trans e₁.symm)
private theorem cumulantsInvariantUnder_of_eventually
    (hIso : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    (hCent : ToriAtArbitraryCouplings.OneCutoffCumulants.Statement)
    (hNorms : ToriAtArbitraryCouplings.LipschitzEstimates.Combined)
    (hFacts : ReflectionPositivity.TorusTuples.SeparationAndSymmetry.Statement) (s : TorusSide)
    (hL : 8 * 105 ^ 4 ≤ s.L) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (hβ : ∀ j, 0 < β j)
    (hK : Tendsto K atTop atTop) (J : Set ℕ+) (hJ : J.Infinite)
    (F : Ambient.ConnectedFamily s.asMirrorData .torus)
    (hlim : s.TendstoAlong K β J (s.toComplexTupleFns F))
    (r : (stdParams s).Torus ≃ (stdParams s).Torus)
    (hr : ReflectionPositivity.TorusTuples.IsTorusIsometry (stdParams s) r)
    (ht : ∀ᶠ k in atTop, ∀ (b : ℝ) (hb : 0 < b),
      ∃ t : (ReflectionPositivity.TorusCutoffs.cutoffData (stdParams s) k b hb 0).Symmetry,
        t.toFun = r.symm) :
    s.CumulantsInvariantUnder F r := by
  intro n hn X
  have hm := transportTuple_mem_sepOfLength hNorms hFacts s hL r hr X.2
  refine ⟨hm, ?_⟩
  have hne : (atTop ⊓ 𝓟 J : Filter ℕ+).NeBot := by
    rw [← Filter.frequently_mem_iff_neBot, Filter.frequently_atTop]
    intro a
    obtain ⟨b, hb, hab⟩ := hJ.exists_gt a
    exact ⟨b, hab.le, hb⟩
  have h₁ := hlim n hn ⟨_, hm⟩
  have h₂ := hlim n hn X
  have hev : ∀ᶠ j in atTop ⊓ 𝓟 J, s.cumulantFnsAt (K j) (β j) n hn X =
      s.cumulantFnsAt (K j) (β j) n hn ⟨_, hm⟩ := by
    refine ((hK.eventually ht).filter_mono inf_le_left).mono fun j hj => ?_
    obtain ⟨t, e⟩ := hj (β j) (hβ j)
    exact (cumulantAt_transportTuple hIso hCent hNorms hFacts s hL (hβ j) hn X.2 r t e).symm
  have := tendsto_nhds_unique h₁ (h₂.congr' hev)
  exact Complex.ofReal_injective this
private theorem exists_latticeIsometry_signedMatrix
    (hIso : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    (s : Conventions.StandingParameters) {k : ℕ+}
    {b : ℝ} (hb : 0 < b) {w : Matrix (Fin 4) (Fin 4) ℝ}
    (hw : w ∈ PeriodicLattice.signedPermMatrices) :
    ∃ t : (ReflectionPositivity.TorusCutoffs.cutoffData s k b hb 0).Symmetry,
      t.toFun = (ReflectionPositivity.TorusTuples.signedMatrixEquiv s hw).symm := by
  obtain ⟨R, hR⟩ := (PeriodicLattice.mem_signedPermMatrices_iff w⁻¹).mp
    (ReflectionPositivity.TorusTuples.inv_mem_signedPermMatrices hw)
  have h0 : (0 : Fin 4 → ℝ) ∈ PeriodicLattice.meshVectors
      (ReflectionPositivity.TorusCutoffs.cutoffData s k b hb 0).L
      (((ReflectionPositivity.TorusCutoffs.cutoffData s k b hb 0).K : ℕ) : ℤ) :=
    ⟨0, fun μ => by simp⟩
  obtain ⟨t, ht⟩ := ((hIso (ReflectionPositivity.TorusCutoffs.cutoffData s k b hb 0)).1).1 R 0 h0
  refine ⟨t, funext fun x => ?_⟩
  obtain ⟨y, rfl⟩ := ReflectionPositivity.TorusCutoffs.exists_proj_eq s x
  have h₁ := ht y
  rw [add_zero, ← PeriodicLattice.SignedFrame.toMatrix_mulVec, ← hR] at h₁
  exact h₁.trans (ReflectionPositivity.TorusTuples.signedMatrixMap_proj s
    (ReflectionPositivity.TorusTuples.inv_mem_signedPermMatrices hw) y).symm
private theorem exists_latticeIsometry_shiftBy
    (hIso : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    (s : Conventions.StandingParameters) {k : ℕ+}
    {b : ℝ} (hb : 0 < b) {v : s.Torus}
    (hv : v ∈ ReflectionPositivity.EveryCutoff.sublatticeAt s k) :
    ∃ t : (ReflectionPositivity.TorusCutoffs.cutoffData s k b hb 0).Symmetry,
      t.toFun = (ReflectionPositivity.TorusTuples.shiftBy v).symm := by
  obtain ⟨m, hm⟩ : ∃ m : Fin 4 → ℤ, ∀ μ, v μ =
      (((m μ : ℝ) * PeriodicLattice.meshSize s.L ((k : ℕ) : ℤ) : ℝ) : AddCircle _) := hv
  let w : Fin 4 → ℝ := fun μ => -((m μ : ℝ) * PeriodicLattice.meshSize s.L ((k : ℕ) : ℤ))
  have hw : w ∈ PeriodicLattice.meshVectors
      (ReflectionPositivity.TorusCutoffs.cutoffData s k b hb 0).L
      (((ReflectionPositivity.TorusCutoffs.cutoffData s k b hb 0).K : ℕ) : ℤ) := ⟨-m, fun μ => by
    simp only [w, Pi.neg_apply, Int.cast_neg, neg_mul]
    rfl⟩
  obtain ⟨t, ht⟩ :=
    ((hIso (ReflectionPositivity.TorusCutoffs.cutoffData s k b hb 0)).1).1 (1, fun _ => 1) w hw
  refine ⟨t, funext fun x => ?_⟩
  obtain ⟨y, rfl⟩ := ReflectionPositivity.TorusCutoffs.exists_proj_eq s x
  have h₁ := ht y
  have e₁ : PeriodicLattice.SignedFrame.actOnVector (1, fun _ => 1) y = y := by
    funext μ
    simp [PeriodicLattice.SignedFrame.actOnVector]
  rw [e₁] at h₁
  have e₂ : ReflectionPositivity.TorusCutoffs.proj s w = -v := by
    funext μ
    change ((w μ : ℝ) : AddCircle _) = - v μ
    rw [hm μ]
    simp only [w]
    rfl
  have e₃ : (ReflectionPositivity.TorusTuples.shiftBy v).symm
      (ReflectionPositivity.TorusCutoffs.proj s y) =
      ReflectionPositivity.TorusCutoffs.proj s y + ReflectionPositivity.TorusCutoffs.proj s w := by
    rw [ReflectionPositivity.TorusTuples.shiftBy_symm, e₂]
    rfl
  rw [e₃, ← ReflectionPositivity.TorusCutoffs.proj_add]
  exact h₁
private theorem torusDist_isMetric
    (hcl : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (S : Conventions.StandingParameters) :
    FamilyTopology.IsMetricFunction (ReflectionPositivity.TorusCutoffs.torusDist (s := S)) :=
  (hcl (ReflectionPositivity.TorusMirrors.unitCouplingData S 0)).1.2.1
private theorem ofReal_le_setDist (s : TorusSide) {A B : Set (s.Point .torus)} {d : ℝ}
    (h : ∀ a ∈ A, ∀ b ∈ B, d ≤ s.pointDist .torus a b) :
    ENNReal.ofReal d ≤ s.setDist .torus A B := by
  simp only [TorusSide.setDist, TorusMetric.setEuclidDist, le_iInf_iff]
  intro a ha b hb
  exact ENNReal.ofReal_le_ofReal (h a ha b hb)
private theorem le_torusDist_of_ofReal_le (S : Conventions.StandingParameters)
    {A B : Set S.Torus} {d : ℝ} (hd : 0 < d)
    (h : ENNReal.ofReal d ≤ ReflectionPositivity.TorusCutoffs.setDist A B)
    {a b : S.Torus} (ha : a ∈ A) (hb : b ∈ B) :
    d ≤ ReflectionPositivity.TorusCutoffs.torusDist a b := by
  simp only [ReflectionPositivity.TorusCutoffs.setDist, TorusMetric.setEuclidDist,
    le_iInf_iff] at h
  rcases ENNReal.ofReal_le_ofReal_iff'.mp (h a ha b hb) with h | h
  · exact h
  · linarith
private def closedNbhd (s : TorusSide) (B : Set (s.Point .torus)) (ρ : ℝ) :
    Set (s.Point .torus) :=
  {x | ∃ z ∈ B, s.pointDist .torus x z ≤ ρ}
private theorem sharpNormAt_eq_sharpNorm (s : TorusSide) (m' : ℕ) (f : s.Point .torus → ℝ) :
    s.sharpNormAt m' .torus f =
      ReflectionPositivity.TorusCutoffs.TorusData.sharpNorm ⟨stdParams s, m'⟩ f := by
  rw [s.sharpNormAt_eq]
  have hM : ((cubeEdge s.L m' : ℕ) : ℝ) =
      (⟨stdParams s, m'⟩ : ReflectionPositivity.TorusCutoffs.TorusData).sharpScale := by
    simp [cubeEdge, ReflectionPositivity.TorusCutoffs.TorusData.sharpScale]
    rfl
  rw [hM]
  rfl
private theorem sharpNormAt_nonneg (s : TorusSide) (m' : ℕ) (f : s.Point .torus → ℝ) :
    0 ≤ s.sharpNormAt m' .torus f := by apply _root_.YangMills.Construction.TotalDensities.TorusLimit.sharpNorm_nonneg <;> assumption
private theorem tendsto_fn_of_components
    (hcl : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hNorms : ToriAtArbitraryCouplings.LipschitzEstimates.Combined)
    (hFacts : ReflectionPositivity.TorusTuples.SeparationAndSymmetry.Statement)
    (s : TorusSide) (hL : 8 * 105 ^ 4 ≤ s.L) (m' : ℕ) (C : ℕ → ℝ → ℝ)
    (hC : TorusSide.IsClusterConstant C)
    (F : Ambient.ConnectedFamily s.asMirrorData .torus)
    (hE : s.IsEquicontinuousBound m' C (s.toComplexTupleFns F)) {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → s.Point .torus → ℝ) (ha : List.ofFn a ∈ s.sepOfLength .torus n)
    (b : ℕ → Fin n → s.Point .torus → ℝ) (hb : ∀ t, List.ofFn (b t) ∈ s.sepOfLength .torus n)
    (hsupp : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ t in atTop, ∀ l, s.closedSupport .torus (b t l) ⊆
      closedNbhd s (s.closedSupport .torus (a l)) ρ)
    (hnorm : ∀ l, Tendsto (fun t => s.sharpNormAt m' .torus (b t l - a l)) atTop (𝓝 0))
    (hbd : ∀ t l, s.sharpNormAt m' .torus (b t l) ≤ s.sharpNormAt m' .torus (a l)) :
    Tendsto (fun t => F.fn n hn ⟨_, hb t⟩) atTop (𝓝 (F.fn n hn ⟨_, ha⟩)) := by
  classical
  have hdist := torusDist_isMetric hcl (stdParams s)
  have hm : List.ofFn a ∈ ⋃ (d : ℝ) (_ : 0 < d),
      ReflectionPositivity.TorusTuples.SeparationAndSymmetry.lipTuplesSeparatedBy
        (stdParams s) n d := by
    rw [← (hFacts (stdParams s)).2.1 n hn]
    exact mem_disjointTuples_of_mem_sepOfLength hNorms s hL (by omega) ha
  obtain ⟨d, hd, -, -, hp⟩ := Set.mem_iUnion₂.1 hm
  have hp' : ∀ l l', l ≠ l' → ∀ x ∈ s.closedSupport .torus (a l),
      ∀ y ∈ s.closedSupport .torus (a l'), d ≤ s.pointDist .torus x y := by
    intro l l' hne x hx y hy
    have h₁ := hp (l.cast List.length_ofFn.symm) (l'.cast List.length_ofFn.symm)
      (fun c => hne (Fin.cast_injective _ c))
    have eget : ∀ l : Fin n, (List.ofFn a).get (l.cast List.length_ofFn.symm) = a l :=
      fun l => by simp
    have key : ∀ g g' : (stdParams s).Torus → ℝ, g = a l → g' = a l' →
        ENNReal.ofReal d ≤ ReflectionPositivity.TorusCutoffs.setDist
          (ReflectionPositivity.TorusTuples.supp (s := stdParams s) g)
          (ReflectionPositivity.TorusTuples.supp (s := stdParams s) g') →
        d ≤ s.pointDist .torus x y := by
      rintro _ _ rfl rfl h
      exact le_torusDist_of_ofReal_le (stdParams s) hd h hx hy
    exact key _ _ (eget l) (eget l') h₁
  let A : Fin n → Set (s.Point .torus) := fun l =>
    closedNbhd s (s.closedSupport .torus (a l)) (d / 4)
  have hA : ∀ l l', l ≠ l' → ENNReal.ofReal (d / 2) ≤ s.setDist .torus (A l) (A l') := by
    intro l l' hne
    refine ofReal_le_setDist s fun x hx y hy => ?_
    obtain ⟨z, hz, hxz⟩ := hx
    obtain ⟨z', hz', hyz⟩ := hy
    have h₁ := hp' l l' hne z hz z' hz'
    have h₂ : s.pointDist .torus z z' ≤ s.pointDist .torus z x + s.pointDist .torus x z' :=
      hdist.triangle z x z'
    have h₃ : s.pointDist .torus x z' ≤ s.pointDist .torus x y + s.pointDist .torus y z' :=
      hdist.triangle x y z'
    have h₄ : s.pointDist .torus z x = s.pointDist .torus x z := hdist.symm z x
    linarith
  have haA : ∀ l, s.closedSupport .torus (a l) ⊆ A l := fun l x hx =>
    ⟨x, hx, by
      have e : s.pointDist .torus x x = 0 := (hdist.eq_zero_iff x x).mpr rfl
      rw [e]
      positivity⟩
  have hpos : 0 < d / 2 := by positivity
  let G : ℕ → ℝ := fun t => C n (d / 2) * ∑ l, s.sharpNormAt m' .torus (b t l - a l) *
    ∏ l' ∈ Finset.univ.erase l, (2 * s.sharpNormAt m' .torus (a l'))
  have hG : Tendsto G atTop (𝓝 0) := by
    have h₁ : Tendsto G atTop (𝓝 (C n (d / 2) * ∑ l : Fin n, 0 *
        ∏ l' ∈ Finset.univ.erase l, (2 * s.sharpNormAt m' .torus (a l')))) :=
      Tendsto.const_mul _ (tendsto_finsetSum _ fun l _ => (hnorm l).mul_const _)
    simpa using h₁
  have hle : ∀ᶠ t in atTop, |F.fn n hn ⟨_, hb t⟩ - F.fn n hn ⟨_, ha⟩| ≤ G t := by
    filter_upwards [hsupp (d / 4) (by positivity)] with t ht
    have h₁ := hE n hn (d / 2) hpos A hA (b t) a (hb t) ha ht haA
    have e : ‖s.toComplexTupleFns F n hn ⟨_, hb t⟩ - s.toComplexTupleFns F n hn ⟨_, ha⟩‖ =
        |F.fn n hn ⟨_, hb t⟩ - F.fn n hn ⟨_, ha⟩| := by
      simp only [TorusSide.toComplexTupleFns]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [e] at h₁
    refine h₁.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_)
      (hC.nonneg n hn _ hpos))
    refine mul_le_mul_of_nonneg_left ?_ (sharpNormAt_nonneg s m' _)
    refine Finset.prod_le_prod (fun _ _ => ?_) fun k _ => ?_
    · exact add_nonneg (sharpNormAt_nonneg s m' _) (sharpNormAt_nonneg s m' _)
    · linarith [hbd t k]
  have h₀ : Tendsto (fun t => |F.fn n hn ⟨_, hb t⟩ - F.fn n hn ⟨_, ha⟩|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hle hG
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact h₀
private theorem cumulantsInvariantUnder_shiftBy
    (hcl : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hne : ReflectionPositivity.NestedRefinement.NestedAndDense)
    (hNorms : ToriAtArbitraryCouplings.LipschitzEstimates.Combined)
    (hFacts : ReflectionPositivity.TorusTuples.SeparationAndSymmetry.Statement)
    (hMod : ReflectionPositivity.TorusCutoffs.ParallelMirrors.ModulusProperties)
    (s : TorusSide) (hL : 8 * 105 ^ 4 ≤ s.L) (m' : ℕ) (C : ℕ → ℝ → ℝ)
    (hC : TorusSide.IsClusterConstant C)
    (F : Ambient.ConnectedFamily s.asMirrorData .torus)
    (hE : s.IsEquicontinuousBound m' C (s.toComplexTupleFns F))
    (hinv : ∀ v ∈ ReflectionPositivity.EveryCutoff.unionOfSublattices (stdParams s),
      s.CumulantsInvariantUnder F (ReflectionPositivity.TorusTuples.shiftBy v))
    (v : (stdParams s).Torus) :
    s.CumulantsInvariantUnder F (ReflectionPositivity.TorusTuples.shiftBy v) := by
  intro n hn X
  have hiso : ∀ u : (stdParams s).Torus, ReflectionPositivity.TorusTuples.IsTorusIsometry
      (stdParams s) (ReflectionPositivity.TorusTuples.shiftBy u) :=
    (hFacts (stdParams s)).2.2.2.2.2.1.2
  have hdist := torusDist_isMetric hcl (stdParams s)
  have hact : ∀ u : (stdParams s).Torus,
      ReflectionPositivity.TorusTuples.transportTuple (s := stdParams s)
        (ReflectionPositivity.TorusTuples.shiftBy u) X.1 ∈ s.sepOfLength .torus n :=
    fun u => transportTuple_mem_sepOfLength hNorms hFacts s hL _ (hiso u) X.2
  refine ⟨hact v, ?_⟩
  let f : Fin n → s.Point .torus → ℝ :=
    ReflectionPositivity.TorusTuples.componentFamily (s := stdParams s) X.1 X.2.1
  have hXf : List.ofFn f = X.1 :=
    ReflectionPositivity.TorusTuples.ofFn_componentFamily (s := stdParams s) X.1 X.2.1
  have hfm : ∀ l, f l ∈ Ambient.compactC1 s.asMirrorData ℝ .torus := fun l =>
    X.2.2.1 _ (List.get_mem _ _)
  let D : ReflectionPositivity.TorusCutoffs.TorusData := ⟨stdParams s, m'⟩
  have hfc : ∀ l, ReflectionPositivity.TorusCutoffs.IsC1 (s := D.toStandingParameters) (f l) :=
    fun l => (hfm l).1
  let τ : (stdParams s).Torus → Fin n → s.Point .torus → ℝ := fun u l =>
    ReflectionPositivity.TorusTuples.transport (s := stdParams s)
      (ReflectionPositivity.TorusTuples.shiftBy u) (f l)
  have hτ : ∀ u, List.ofFn (τ u) =
      ReflectionPositivity.TorusTuples.transportTuple (s := stdParams s)
        (ReflectionPositivity.TorusTuples.shiftBy u) X.1 := fun u => by
    rw [← hXf]
    change List.ofFn (ReflectionPositivity.TorusTuples.transport (s := stdParams s)
        (ReflectionPositivity.TorusTuples.shiftBy u) ∘ f) =
      List.map (ReflectionPositivity.TorusTuples.transport (s := stdParams s)
        (ReflectionPositivity.TorusTuples.shiftBy u)) (List.ofFn f)
    exact List.map_ofFn.symm
  have hsep : ∀ u, List.ofFn (τ u) ∈ s.sepOfLength .torus n := fun u => by
    rw [hτ]
    exact hact u
  have val : ∀ u, F.fn n hn ⟨_, hact u⟩ = F.fn n hn ⟨_, hsep u⟩ := fun u =>
    congrArg (F.fn n hn) (Subtype.ext (hτ u).symm)
  choose vs hvs hvd using fun t : ℕ =>
    (hne (stdParams s)).2.1.2 v (1 / ((t : ℝ) + 1)) (by positivity)
  have hδ : Tendsto (fun t => ReflectionPositivity.TorusCutoffs.torusDist (vs t) v) atTop (𝓝 0) :=
    squeeze_zero (fun t => hdist.nonneg _ _)
      (fun t => (hdist.symm _ _).trans_le (hvd t).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hsup : ∀ u l, s.closedSupport .torus (τ u l) =
      ReflectionPositivity.TorusTuples.shiftBy u '' s.closedSupport .torus (f l) :=
    fun u l => (transport_mem hNorms hFacts s hL _ (hiso u) (hfm l)).2
  have hfl : ∀ l, ReflectionPositivity.TorusTuples.IsLipschitzReal (s := stdParams s) (f l) :=
    fun l => ((hNorms s hL 0 .torus).1.2.1.1 univ
      (show f l ∈ s.c1SuppIn .torus univ from ⟨(hfm l).1, (hfm l).2, subset_univ _⟩)).1
  have hnormτ : ∀ u l, s.sharpNormAt m' .torus (τ u l) = s.sharpNormAt m' .torus (f l) :=
    fun u l => by
      rw [sharpNormAt_eq_sharpNorm, sharpNormAt_eq_sharpNorm]
      exact ((hFacts (stdParams s)).2.2.2.2.2.2.2.1 _ (hiso u) (f l) (hfl l)).2.2.2.2.1 m'
  have key : Tendsto (fun t => F.fn n hn ⟨_, hsep (vs t)⟩) atTop
      (𝓝 (F.fn n hn ⟨_, hsep v⟩)) := by
    refine tendsto_fn_of_components hcl hNorms hFacts s hL m' C hC F hE hn (τ v) (hsep v)
      (fun t => τ (vs t)) (fun t => hsep _) ?_ ?_ ?_
    · intro ρ hρ
      filter_upwards [hδ.eventually (Iio_mem_nhds hρ)] with t ht l x hx
      have hx' : x ∈ ReflectionPositivity.TorusTuples.shiftBy (vs t) ''
          s.closedSupport .torus (f l) := by
        rw [← hsup]
        exact hx
      obtain ⟨z, hz, rfl⟩ := hx'
      refine ⟨ReflectionPositivity.TorusTuples.shiftBy v z, ?_, ?_⟩
      · rw [hsup]
        exact ⟨z, hz, rfl⟩
      · have e : s.pointDist .torus (ReflectionPositivity.TorusTuples.shiftBy (vs t) z)
            (ReflectionPositivity.TorusTuples.shiftBy v z) =
            ReflectionPositivity.TorusCutoffs.torusDist (vs t) v := by
          change ReflectionPositivity.TorusCutoffs.torusNorm (z + vs t - (z + v)) =
            ReflectionPositivity.TorusCutoffs.torusNorm (vs t - v)
          rw [add_sub_add_left_eq_sub]
        rw [e]
        exact le_of_lt ht
    · intro l
      refine squeeze_zero (fun _ => sharpNormAt_nonneg s m' _) (fun t => ?_)
        (((hMod D).1 (f l) (hfc l)).1.2.comp (tendsto_nhdsWithin_iff.mpr
          ⟨hδ, Eventually.of_forall fun t => hdist.nonneg _ _⟩))
      rw [sharpNormAt_eq_sharpNorm]
      exact ((hMod D).1 (f l) (hfc l)).2.1 (vs t) v
    · intro t l
      rw [hnormτ, hnormτ]
  have hconst : ∀ t, F.fn n hn ⟨_, hsep (vs t)⟩ = F.fn n hn X := fun t => by
    obtain ⟨h, e⟩ := hinv (vs t) (hvs t) n hn X
    rw [← val]
    exact e
  rw [val]
  simp only [hconst] at key
  exact (tendsto_nhds_unique key tendsto_const_nhds).symm ▸ rfl
theorem cumulantsInvariant
    (hcl : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hne : ReflectionPositivity.NestedRefinement.NestedAndDense)
    (hIso : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    (hCent : ToriAtArbitraryCouplings.OneCutoffCumulants.Statement)
    (hNorms : ToriAtArbitraryCouplings.LipschitzEstimates.Combined)
    (hFacts : ReflectionPositivity.TorusTuples.SeparationAndSymmetry.Statement)
    (hMod : ReflectionPositivity.TorusCutoffs.ParallelMirrors.ModulusProperties)
    (s : TorusSide) (hL : 8 * 105 ^ 4 ≤ s.L) (m' : ℕ) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ)
    (C : ℕ → ℝ → ℝ)
    (h : s.IsUniformlyBoundedSeq m' K β C) (J : Set ℕ+) (hJ : J.Infinite)
    (F : Ambient.ConnectedFamily s.asMirrorData .torus)
    (hlim : s.TendstoAlong K β J (s.toComplexTupleFns F))
    (hEq : s.IsEquicontinuousBound m' C (s.toComplexTupleFns F)) :
    s.CumulantsInvariant F := by
  have hlat : ∀ v ∈ ReflectionPositivity.EveryCutoff.unionOfSublattices (stdParams s),
      s.CumulantsInvariantUnder F (ReflectionPositivity.TorusTuples.shiftBy v) := by
    intro v hv
    obtain ⟨Kv, hKv⟩ := Set.mem_iUnion.mp hv
    exact cumulantsInvariantUnder_of_eventually hIso hCent hNorms hFacts s hL K β h.β_pos
      h.tendsto_cutoff J hJ F hlim _ ((hFacts (stdParams s)).2.2.2.2.2.1.2 v)
      ((eventually_ge_atTop Kv).mono fun k hk b hb =>
        exists_latticeIsometry_shiftBy hIso (stdParams s) hb
          ((hne (stdParams s)).1.2.1 v Kv hKv k hk))
  refine ⟨fun v => cumulantsInvariantUnder_shiftBy hcl hne hNorms hFacts hMod s hL m' C
    h.isClusterConstant F hEq hlat v, fun w hw => ?_⟩
  exact cumulantsInvariantUnder_of_eventually hIso hCent hNorms hFacts s hL K β h.β_pos
    h.tendsto_cutoff J hJ F hlim _ ((hFacts (stdParams s)).2.2.2.2.2.1.1 w hw)
    (Eventually.of_forall fun k b hb =>
      exists_latticeIsometry_signedMatrix hIso (stdParams s) hb hw)
end Symmetry
namespace Reflection
private theorem isBoundedOnTorus_of_mem
    (hNorms : ToriAtArbitraryCouplings.LipschitzEstimates.Combined) (s : TorusSide)
    (hL : 8 * 105 ^ 4 ≤ s.L) {f : s.Point .torus → ℝ}
    (hf : f ∈ Ambient.compactC1 s.asMirrorData ℝ .torus) :
    ConnectedFunctionExpansion.IsBoundedOnTorus (L := s.L) (m := s.m) f := by
  obtain ⟨C, hC⟩ := ((hNorms s hL 0 .torus).1.1 f hf).1
  unfold ConnectedFunctionExpansion.IsBoundedOnTorus PeriodicLattice.torusSupNorm
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (iSup_le fun y => ENNReal.ofReal_le_ofReal (hC y))
private theorem connectedSchwinger_eq_cumulantAt
    (hCent : ToriAtArbitraryCouplings.OneCutoffCumulants.Statement)
    (hNorms : ToriAtArbitraryCouplings.LipschitzEstimates.Combined) (s : TorusSide)
    (hL : 8 * 105 ^ 4 ≤ s.L)
    (K : ℕ+) (β : ℝ) (hβ : 0 < β) (X : s.FnTuple .torus) (hn : 1 ≤ X.length)
    (hX : ∀ f ∈ X, f ∈ Ambient.compactC1 s.asMirrorData ℝ .torus) :
    SchwingerFunctions.connectedSchwinger s.L s.m K β X.get = s.cumulantAt K β X :=
  ((hCent (s.mirrorDataOf K β hβ) hL).1.1 X.length hn X.get
    fun _ => isBoundedOnTorus_of_mem hNorms s hL (hX _ (List.get_mem _ _))).symm
private theorem exists_tendsto_enumeration {J : Set ℕ+} (hJ : J.Infinite) :
    ∃ φ : ℕ+ → ℕ+, Tendsto φ atTop (atTop ⊓ 𝓟 J) := by
  let e := hJ.natEmbedding J
  let φ : ℕ+ → ℕ+ := fun j => (e (j : ℕ)).1
  have hinj : Function.Injective φ := fun a b h =>
    PNat.eq (e.injective (Subtype.ext h))
  refine ⟨φ, tendsto_inf.2 ⟨?_, tendsto_principal.2 (Eventually.of_forall fun j => (e _).2)⟩⟩
  refine tendsto_atTop.2 fun b => ?_
  have hfin : (φ ⁻¹' Set.Iic b).Finite := (Set.finite_Iic b).preimage hinj.injOn
  have hco : ∀ᶠ j in cofinite, b ≤ φ j := by
    refine eventually_cofinite.2 (hfin.subset fun j hj => ?_)
    exact (not_le.1 hj).le
  exact atTop_le_cofinite hco
private def latticeDataAlong (s : TorusSide) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (hβ : ∀ j, 0 < β j)
    (hK : Tendsto K atTop atTop) (φ : ℕ+ → ℕ+) (hφ : Tendsto φ atTop atTop) :
    Ambient.LatticeDataSeq s.asMirrorData .torus where
  K := K ∘ φ
  ℓ := fun _ => s.asMirrorData.side
  β := β ∘ φ
  ℓ_mem := fun _ => ⟨(s.m : ℕ), s.m.pos, rfl⟩
  β_pos := fun j => hβ _
  K_tendsto := by
    refine tendsto_atTop.2 fun b => ?_
    have h := tendsto_atTop.1 (hK.comp hφ) (Nat.succPNat b)
    refine h.mono fun j hj => ?_
    have h' : ((Nat.succPNat b : ℕ+) : ℕ) ≤ ((K ∘ φ) j : ℕ) := by exact_mod_cast hj
    have h'' : b + 1 ≤ ((K ∘ φ) j : ℕ) := by simpa using h'
    omega
  isSideSequence := fun _ => rfl
theorem reflectionPositiveAt
    (hPos : ReflectionPositivity.AxisMirror.LimitPositivity.LimitPositivityStatement)
    (hCent : ToriAtArbitraryCouplings.OneCutoffCumulants.Statement)
    (hConc : ReflectionPositivity.AxisMirror.ReflectAppendSeparated)
    (hNorms : ToriAtArbitraryCouplings.LipschitzEstimates.Combined)
    (s : TorusSide) (hL : 8 * 105 ^ 4 ≤ s.L) (m' : ℕ) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ)
    (C : ℕ → ℝ → ℝ)
    (h : s.IsUniformlyBoundedSeq m' K β C) (J : Set ℕ+) (hJ : J.Infinite)
    (F : Ambient.ConnectedFamily s.asMirrorData .torus)
    (hlim : s.TendstoAlong K β J (s.toComplexTupleFns F)) (S' : CoordMirror) :
    s.ReflectionPositiveAt F S' := by
  obtain ⟨μ, c⟩ := S'
  refine ⟨fun X hX Y hY => (hConc s.asMirrorData .torus μ c X Y hX hY).2, ?_⟩
  intro I X hX ζ
  rcases Nat.eq_zero_or_pos I with rfl | hI
  · simp [CoordMirror.reflectedGramSum]
  obtain ⟨φ, hφ⟩ := exists_tendsto_enumeration hJ
  have hφ' : Tendsto φ atTop atTop := hφ.mono_right inf_le_left
  have hconv : (latticeDataAlong s K β h.β_pos h.tendsto_cutoff φ hφ').TendsToFamily F.fn := by
    intro n hn Y
    have hY := (hlim n hn Y).comp hφ
    refine hY.congr fun j => ?_
    have hlen : 1 ≤ Y.1.length := by
      have := Y.2.1
      omega
    refine Eq.trans ?_ (Ambient.LatticeDataSeq.connectedAt_torus _ j Y.1).symm
    exact (connectedSchwinger_eq_cumulantAt hCent hNorms s hL _ _ (h.β_pos _) Y.1 hlen
      Y.2.2.1).symm
  have hsat := hPos.1 s.asMirrorData _ F.fn hconv ⟨μ, c⟩
    ⟨I, hI, fun i => ⟨X i, hX i⟩, ζ⟩
  have e : ∀ (σ : Ambient.separatedAll s.asMirrorData .torus → ℝ),
      CoordMirror.PositivityInstance.lhs
        (⟨I, hI, fun i => ⟨X i, hX i⟩, ζ⟩ :
          (CoordMirror.mk μ c).PositivityInstance s.asMirrorData .torus) (fun Z => (σ Z : ℂ)) =
      CoordMirror.reflectedGramSum s.asMirrorData ⟨μ, c⟩ .torus σ X ζ := by
    intro σ
    simp only [CoordMirror.PositivityInstance.lhs, CoordMirror.positivitySum,
      CoordMirror.reflectedGramSum, Ambient.evalOrZeroC_ofReal]
  have h3 : (CoordMirror.PositivityInstance.lhs
        (⟨I, hI, fun i => ⟨X i, hX i⟩, ζ⟩ :
          (CoordMirror.mk μ c).PositivityInstance s.asMirrorData .torus)
        (fun Z => ((F.centeredFunctional Z : ℝ) : ℂ))).im = 0 ∧
      0 ≤ (CoordMirror.PositivityInstance.lhs
        (⟨I, hI, fun i => ⟨X i, hX i⟩, ζ⟩ :
          (CoordMirror.mk μ c).PositivityInstance s.asMirrorData .torus)
        (fun Z => ((F.centeredFunctional Z : ℝ) : ℂ))).re := hsat
  rwa [e] at h3
end Reflection
theorem holds
    (hcl : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hne : ReflectionPositivity.NestedRefinement.NestedAndDense)
    (hIso : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance)
    (hCent : ToriAtArbitraryCouplings.OneCutoffCumulants.Statement)
    (hNorms : ToriAtArbitraryCouplings.LipschitzEstimates.Combined)
    (hFacts : ReflectionPositivity.TorusTuples.SeparationAndSymmetry.Statement)
    (hMod : ReflectionPositivity.TorusCutoffs.ParallelMirrors.ModulusProperties)
    (hPos : ReflectionPositivity.AxisMirror.LimitPositivity.LimitPositivityStatement)
    (hConc : ReflectionPositivity.AxisMirror.ReflectAppendSeparated) :
    TotalDensities.BoundedSequenceLimit.Claim := by
  intro s hL m' K β C hseq J hJ F hlim hEq
  exact ⟨Symmetry.cumulantsInvariant hcl hne hIso hCent hNorms hFacts hMod
      s hL m' K β C hseq J hJ F hlim hEq,
    Reflection.reflectionPositiveAt hPos hCent hConc hNorms
      s hL m' K β C hseq J hJ F hlim⟩
end TotalDensities.BoundedSequenceLimit
end
end YangMills.Construction
