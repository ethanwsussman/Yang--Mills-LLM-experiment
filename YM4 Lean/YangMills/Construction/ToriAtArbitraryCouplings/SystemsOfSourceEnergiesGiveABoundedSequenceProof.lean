import YangMills.Construction.Lattice.TorusBound
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.ToriAtArbitraryCouplings.BoundedFormsAlongABoundedSequenceProof
import YangMills.Construction.ToriAtArbitraryCouplings.SystemsOfSourceEnergiesGiveABoundedSequence
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open TorusBound
namespace ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace LocalizedEnergySystemsBound
open TorusSide
open Classical in
def uvConstant (L M : ℕ) (Ce κe d : ℝ) : ℝ :=
  if h : ∃ c : ConstantParameters, c.L = L ∧ c.cubeSide = M ∧ c.Ce = Ce ∧ c.κe = κe then
    h.choose.uvReal d
  else 1
theorem uvConstant_eq (hU : ∀ c : ConstantParameters, c.UVConstantWellBehaved)
    (c : ConstantParameters) {d : ℝ} (hd : 0 < d) :
    uvConstant c.L c.cubeSide c.Ce c.κe d = c.uvReal d := by
  have h : ∃ c' : ConstantParameters,
      c'.L = c.L ∧ c'.cubeSide = c.cubeSide ∧ c'.Ce = c.Ce ∧ c'.κe = c.κe :=
    ⟨c, rfl, rfl, rfl, rfl⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h.choose_spec
  rw [uvConstant, dif_pos h]
  unfold ConstantParameters.uvReal
  rw [(hU c).eq_of_params h.choose h₁ h₂ h₃ h₄ d hd]
theorem uvReal_pos {c : ConstantParameters} (hc : c.UVConstantWellBehaved) {d : ℝ}
    (hd : 0 < d) : 0 < c.uvReal d :=
  ENNReal.toReal_pos (hc.pos d hd).ne' (hc.lt_top d hd).ne
theorem uvReal_antitoneOn {c : ConstantParameters} (hc : c.UVConstantWellBehaved) :
    AntitoneOn c.uvReal (Ioi 0) := fun _ ha _ hb hab =>
  ENNReal.toReal_mono (hc.lt_top _ ha).ne (hc.antitoneOn ha hb hab)
theorem closure_subset_closureWrt {ℓ : ℝ} (Z : Set (TorusMetric.Torus4 ℓ)) :
    closure Z ⊆ MetricNotions.closureWrt TestFunctions.euclidDistTorus Z := by
  intro x hx r hr
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 hx (r / 2) (half_pos hr)
  refine ⟨y, hy, ?_⟩
  have h₁ := TorusAnalysis.torusEuclidNorm_le_two_mul_pi_norm (x - y)
  have h₂ : ‖x - y‖ < r / 2 := by simpa [dist_eq_norm] using hd
  change TorusMetric.torusEuclidNorm (x - y) < r
  linarith
theorem setEuclidDist_anti {ℓ : ℝ} {A A' B B' : Set (TorusMetric.Torus4 ℓ)}
    (hA : A' ⊆ A) (hB : B' ⊆ B) :
    TorusMetric.setEuclidDist A B ≤ TorusMetric.setEuclidDist A' B' :=
  le_iInf₂ fun a ha => le_iInf₂ fun b hb => iInf₂_le_of_le a (hA ha) (iInf₂_le b (hB hb))
theorem isBoundedOnTorus_of_isBoundedFun {L m : ℕ} {f : PeriodicLattice.FourTorus L m → ℝ}
    (h : TestFunctions.IsBoundedFun f) :
    ConnectedFunctionExpansion.IsBoundedOnTorus f := by apply _root_.YangMills.Construction.ToriAtArbitraryCouplings.BoundedMultilinearForms.isBoundedOnTorus_of_isBoundedFun <;> assumption
theorem clusterBoundOfFamilies_nonneg (s : TorusSide) {CUV : ℝ → ℝ} {Eplus Clow ϱ' : ℝ}
    (hϱ' : 0 < ϱ') (n : ℕ) {d : ℝ} (hCUV : 0 < CUV d) :
    0 ≤ s.clusterBoundOfFamilies CUV Eplus Clow ϱ' n d := by
  have hQ : 0 < s.expVolumeFactor Eplus Clow := Real.exp_pos _
  unfold clusterBoundOfFamilies
  positivity
theorem clusterBoundOfFamilies_antitoneOn (s : TorusSide) {CUV : ℝ → ℝ} {Eplus Clow ϱ' : ℝ}
    (hϱ' : 0 < ϱ') (n : ℕ) (hCUV : AntitoneOn CUV (Ioi 0)) :
    AntitoneOn (s.clusterBoundOfFamilies CUV Eplus Clow ϱ' n) (Ioi 0) := fun a ha b hb hab => by
  have hs : 0 ≤ s.length ^ 4 := by positivity
  have hn : 0 ≤ ((n : ℝ) / ϱ') ^ n := by positivity
  unfold clusterBoundOfFamilies
  have := mul_le_mul_of_nonneg_left (hCUV ha hb hab) hs
  exact mul_le_mul_of_nonneg_right (by linarith) hn
theorem cumulant_le_of_family (hT : TorusBound.TorusBoundHolds)
    (hS : OneCutoffCumulants.Statement)
    (hC : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (s : TorusSide) (hL : 8 * 105 ^ 4 ≤ s.L) (m' : ℕ) {Ce κe : ℝ} (hCe : 0 ≤ Ce)
    (hκe : PolymerActivities.DomainCounting.countingRate < κe) (K : ℕ+) (β : ℝ) (hβ : 0 < β)
    {Eplus Clow ϱ' : ℝ} (hϱ' : 0 < ϱ') (e : (s.torusBoundSetup m' K β hβ).RadiusFamily ϱ' hϱ')
    (he : e.SatisfiesFiveBounds Ce κe Eplus Clow) (n : ℕ) (hn : 2 ≤ n) {d : ℝ} (hd : 0 < d)
    (X : s.FnTuple .torus) (hX : X ∈ s.lipDisjointOfLength .torus n)
    (hsep : ENNReal.ofReal d ≤ s.gapAllLengths .torus X) :
    ‖s.cumulantAt K β X‖ ≤
      s.clusterBoundOfFamilies (uvConstant s.L (cubeEdge s.L m') Ce κe) Eplus Clow ϱ' n d *
        s.sharpNormProduct m' .torus X := by
  obtain ⟨rfl, hentries, -⟩ := (s.mem_lipDisjointOfLength_iff .torus n X).1 hX
  let D := s.torusBoundSetup m' K β hβ
  let f : Fin X.length → D.Torus → ℝ := X.get
  have hlip : ∀ i, TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus (f i) := fun i =>
    (hentries (X.get i) (List.get_mem X i)).1
  have hf : D.IsRealFamily f := ⟨by omega, hlip⟩
  have hseparated : TestFunctions.HasSeparatedSupportsTorus f d := by
    refine ⟨hd, fun i k hik => ?_⟩
    rw [s.gapAllLengths_eq_supportGap] at hsep
    have h₁ : ENNReal.ofReal d ≤
        s.setDist .torus (s.closedSupport .torus (X.get i)) (s.closedSupport .torus (X.get k)) :=
      hsep.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le_of_le hik le_rfl)))
    exact h₁.trans (setEuclidDist_anti (closure_subset_closureWrt _)
      (closure_subset_closureWrt _))
  have hU := hT.1
  have hclauses := ((hT.2 D Ce κe Eplus Clow ϱ' hCe hκe hϱ' e he.isLocal he.analytic
    he.expBounded he.upperStable he.floorBounded X.length f hf).2).truncated_bound d hn hseparated
  let Dm : ReflectionPositivity.AxisMirror.MirrorData := s.mirrorDataOf K β hβ
  have hbdd : ∀ i, ConnectedFunctionExpansion.IsBoundedOnTorus (f i) := fun i =>
    isBoundedOnTorus_of_isBoundedFun
      (((hC ⟨Dm.toStandingParameters, β, hβ, 0⟩).2.1 ℝ (f i) (hlip i)).2.1)
  have hcum := (hS Dm hL).1.1 X.length (by omega) f hbdd
  have hconn : s.cumulantAt K β X = D.truncatedCorrelation f := hcum
  have hprod : s.sharpNormProduct m' .torus X = ∏ i, D.sharpNorm (f i) := by
    unfold sharpNormProduct
    exact (Fin.prod_univ_fun_getElem X (s.sharpNormAt (𝕜 := ℝ) m' .torus)).symm
  have hval := uvConstant_eq hU (ConstantParameters.ofSetup D Ce κe Eplus Clow hCe hκe) hd
  have hval' : uvConstant s.L (cubeEdge s.L m') Ce κe d =
      (ConstantParameters.ofSetup D Ce κe Eplus Clow hCe hκe).uvReal d := hval
  rw [hconn, hprod]
  refine hclauses.trans (le_of_eq ?_)
  congr 1
  unfold clusterBoundOfFamilies ConstantParameters.truncatedCoeff
  rw [hval']
  rfl
theorem holds_of_torusBound (hT : TorusBound.TorusBoundHolds)
    (hS : OneCutoffCumulants.Statement)
    (hC : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts) :
    Holds := by
  refine ⟨uvConstant, fun s hL m' Ce κe hCe hκe => ?_⟩
  have hU := hT.1
  let c₀ : ConstantParameters := ⟨s.L, s.admissible, m', Ce, hCe, κe, hκe, 0, 0⟩
  have hval : ∀ d : ℝ, 0 < d →
      uvConstant s.L (cubeEdge s.L m') Ce κe d = c₀.uvReal d := fun d hd =>
    uvConstant_eq hU c₀ hd
  have hpos : ∀ d : ℝ, 0 < d → 0 < uvConstant s.L (cubeEdge s.L m') Ce κe d := fun d hd => by
    rw [hval d hd]
    exact uvReal_pos (hU c₀) hd
  have hanti : AntitoneOn (uvConstant s.L (cubeEdge s.L m') Ce κe) (Ioi 0) :=
    fun a ha b hb hab => by
      rw [hval a ha, hval b hb]
      exact uvReal_antitoneOn (hU c₀) ha hb hab
  refine ⟨hpos, hanti, fun K β hβ hK _ Eplus Clow ϱ' hϱ' hsys => ?_⟩
  refine ⟨hK, hβ, ⟨fun n _ d hd => clusterBoundOfFamilies_nonneg s hϱ' n (hpos d hd),
    fun n _ => clusterBoundOfFamilies_antitoneOn s hϱ' n hanti⟩, fun j n hn d hd X hX hsep => ?_⟩
  obtain ⟨e, he⟩ := hsys j
  exact cumulant_le_of_family hT hS hC s hL m' hCe hκe (K j) (β j) (hβ j) hϱ' e he n hn hd X hX hsep
end LocalizedEnergySystemsBound
end ToriAtArbitraryCouplings
end YangMills.Construction
end
