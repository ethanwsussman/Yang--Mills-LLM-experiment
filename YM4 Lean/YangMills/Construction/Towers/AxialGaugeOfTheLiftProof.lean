import YangMills.Construction.Towers.AveragingOnSmallFamiliesOfTheChartAtOneProof
import YangMills.Construction.Towers.AxialGaugeOfTheLift
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import YangMills.Construction.Towers.GaugeAndIsometricImagesAreConfigurations
import YangMills.Construction.Towers.GaugeFixingFunctionAsASumOfCosinesProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace AxialProlongation
open YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces
variable {L n k a b i : ℕ}
theorem inv_eq_adjugate_of_mem {X : Matrices.ComplexMatrix2}
    (hX : X ∈ PeriodicLattice.compactGaugeGroup) : X⁻¹ = X.adjugate := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.inv_eq_adjugate_of_mem <;> assumption
theorem fieldOfPositiveValues_restrict {A : Edge L n k a → Matrices.ComplexMatrix2}
    (hA : A ∈ fieldSpace L n k a) : fieldOfPositiveValues (restrictToPositiveEdges A) = A := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem continuousOn_of_isAnalyticFieldMap
    (hK : Matrices.GroupLieProduct.Subspaces.AnalyticCalculus.AnalyticCalculusStatement)
    {U : Set (Edge L n k a → Matrices.ComplexMatrix2)}
    {f : (Edge L n k a → Matrices.ComplexMatrix2) → Edge L n k b → Matrices.ComplexMatrix2}
    (h : IsAnalyticFieldMap U f) : ContinuousOn f U := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.continuousOn_of_isAnalyticFieldMap <;> assumption
theorem continuousWithinAt_of_analyticMatrixValued
    {U : Set (Edge L n k a → Matrices.ComplexMatrix2)}
    {F : (Edge L n k a → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (hF : IsAnalyticMatrixValuedOn U F)
    {A₀ : Edge L n k a → Matrices.ComplexMatrix2} (hA₀ : A₀ ∈ U) : ContinuousWithinAt F U A₀ := by
  have hU : U ⊆ fieldSpace L n k a := hF.1.1
  obtain ⟨-, i₀, hRA⟩ := hF
  obtain ⟨W, h, hxW, hhol, heq⟩ := hRA.2 (restrictToPositiveEdges A₀) ⟨A₀, hA₀, rfl⟩
  obtain ⟨⟨O, hO, hWO⟩, -, hloc⟩ := hhol
  obtain ⟨G, hG, hGh⟩ := hloc _ hxW
  have hD : restrictToPositiveEdges '' U ⊆ Matrices.ComplexMatrix2.complexifiedProduct
      (fun _ : PositiveEdge L n k a => Matrices.ComplexMatrix2.FactorKind.group) := by
    obtain ⟨O', -, hD'⟩ := hRA.1
    intro v hv
    rw [hD'] at hv
    exact fun c => (Matrix.mem_specialUnitaryGroup_iff.1 (hv.2 c)).2
  have hWmem : W ∈ 𝓝[restrictToPositiveEdges '' U] (restrictToPositiveEdges A₀) := by
    have hxO : restrictToPositiveEdges A₀ ∈ O := by
      rw [hWO] at hxW
      exact hxW.1
    refine mem_nhdsWithin.2 ⟨O, hO, hxO, fun v hv => ?_⟩
    rw [hWO]
    exact ⟨hv.1, hD hv.2⟩
  have hev : (fun v (_ : Fin 1) => F (fieldOfPositiveValues v)) =ᶠ[𝓝[restrictToPositiveEdges '' U]
      (restrictToPositiveEdges A₀)] G := by
    filter_upwards [heq, nhdsWithin_le_of_mem hWmem hGh] with v h₁ h₂
    exact h₁.trans h₂
  have hself := hev.self_of_nhdsWithin ⟨A₀, hA₀, rfl⟩
  have hc : ContinuousWithinAt (fun v (_ : Fin 1) => F (fieldOfPositiveValues v))
      (restrictToPositiveEdges '' U) (restrictToPositiveEdges A₀) :=
    hG.continuousAt.continuousWithinAt.congr_of_eventuallyEq hev hself
  have hρ : Continuous (restrictToPositiveEdges :
      (Edge L n k a → Matrices.ComplexMatrix2) → PositiveEdge L n k a → Matrices.ComplexMatrix2) :=
    continuous_pi fun c => continuous_apply _
  have hcomp := ((continuous_apply (0 : Fin 1)).continuousAt.comp_continuousWithinAt hc).comp
    hρ.continuousWithinAt (mapsTo_image _ _)
  have hval : ∀ A ∈ U, F A = F (fieldOfPositiveValues (restrictToPositiveEdges A)) := by
    intro A hA
    rw [fieldOfPositiveValues_restrict (hU hA)]
  exact hcomp.congr hval (hval A₀ hA₀)
theorem mem_nhdsWithin_trivialField (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (ha : a ≤ k)
    (U : Set (Edge L n k a → Matrices.ComplexMatrix2)) (h : IsOpenNhdOfOne U) :
    U ∈ 𝓝[fieldSpace L n k a] trivialField L n k a := by
  have B := ((hE L hL k a ha).1 n hn).2.2.2.2.2.2.2.2.1
  obtain ⟨O, hO, heq⟩ := (B U h.1.1).2 h.1.2
  have h1 : trivialField L n k a ∈ O := by
    have := h.2
    rw [heq] at this
    exact this.1
  refine mem_nhdsWithin.2 ⟨O, hO, h1, fun A hA => ?_⟩
  rw [heq]
  exact hA
def axialGaugeTransform (A : Edge L n k i → Matrices.ComplexMatrix2) (x : Vertex L n k i) :
    Matrices.ComplexMatrix2 :=
  open Classical in
  if h : (x : PeriodicLattice.FourTorus L n) ∉
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) then
    PeriodicLattice.meanContourHolonomy A (cubeCentre ⟨x, h⟩) x
  else 1
theorem cubeCentre_spec (hZ : BlocksPartitionFiner L n k (i + 1)) (x : FineOnlyVertex L n k i) :
    x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) (cubeCentre x) ∧
      (x.1 : PeriodicLattice.FourTorus L n) ≠ cubeCentre x := by apply _root_.YangMills.SharedProofs.p27590 <;> assumption
theorem not_mem_sublattice_of_mem_block (hZ : BlocksPartitionFiner L n k (i + 1))
    {y : Vertex L n k (i + 1)} {z : Vertex L n k i}
    (hz : z ∈ PeriodicLattice.blockSitesExceptCenter k i y) :
    (z : PeriodicLattice.FourTorus L n) ∉
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) := by apply _root_.YangMills.SharedProofs.p129669 <;> assumption
theorem cubeCentre_eq (hZ : BlocksPartitionFiner L n k (i + 1))
    {y : Vertex L n k (i + 1)} (x : FineOnlyVertex L n k i)
    (hx : x.1 ∈ PeriodicLattice.blockSitesExceptCenter k i y) : cubeCentre x = y := by
  obtain ⟨w, -, huniq⟩ := hZ.2.2 x.1 x.2
  have hs := cubeCentre_spec hZ x
  exact (huniq _ ⟨hs.1, hs.2⟩).trans (huniq _ ⟨hx.1, hx.2⟩).symm
theorem axialGaugeTransform_of_mem_block (hZ : BlocksPartitionFiner L n k (i + 1))
    (A : Edge L n k i → Matrices.ComplexMatrix2) {y : Vertex L n k (i + 1)} {z : Vertex L n k i}
    (hz : z ∈ PeriodicLattice.blockSitesExceptCenter k i y) :
    axialGaugeTransform A z = PeriodicLattice.meanContourHolonomy A y z := by
  unfold axialGaugeTransform
  rw [dif_pos (not_mem_sublattice_of_mem_block hZ hz),
    cubeCentre_eq hZ ⟨z, not_mem_sublattice_of_mem_block hZ hz⟩ hz]
theorem axialGaugeTransform_coarse (hL : 0 < L) (A : Edge L n k i → Matrices.ComplexMatrix2)
    (y : Vertex L n k (i + 1)) :
    axialGaugeTransform A (y.toSublattice (PeriodicLattice.levelDepth k i)) = 1 := by
  have hle : PeriodicLattice.levelDepth k (i + 1) ≤ PeriodicLattice.levelDepth k i := by
    unfold PeriodicLattice.levelDepth
    push_cast
    omega
  have hcoe : ((y.toSublattice (PeriodicLattice.levelDepth k i) : Vertex L n k i) :
      PeriodicLattice.FourTorus L n) = y :=
    Classical.epsilon_spec (p := fun x : Vertex L n k i => (x : PeriodicLattice.FourTorus L n) = y)
      ⟨⟨y, PeriodicLattice.sublattice_mono hL n hle y.2⟩, rfl⟩
  unfold axialGaugeTransform
  rw [dif_neg]
  rw [not_not, hcoe]
  exact y.2
theorem meanContourHolonomy_mem {A : Edge L n k i → Matrices.ComplexMatrix2}
    {y : Vertex L n k (i + 1)} {x : Vertex L n k i} (h : PeriodicLattice.HasContourMean A y x) :
    PeriodicLattice.meanContourHolonomy A y x ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p41932 <;> assumption
theorem axialGaugeTransform_mem (hZ : BlocksPartitionFiner L n k (i + 1))
    {A : Edge L n k i → Matrices.ComplexMatrix2}
    (hA : ∀ (y : Vertex L n k (i + 1)),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
        PeriodicLattice.HasContourMean A y x) :
    axialGaugeTransform A ∈ gaugeGroupAt L n k i := by
  exact show ∀ x : Vertex L n k i,
      axialGaugeTransform A x ∈ PeriodicLattice.compactGaugeGroup from by
    intro x
    by_cases h : (x : PeriodicLattice.FourTorus L n) ∉
        PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1))
    · have hx := (cubeCentre_spec hZ ⟨x, h⟩).1
      have hh := hA (cubeCentre ⟨x, h⟩) x hx
      have hm := meanContourHolonomy_mem hh
      simpa only [axialGaugeTransform, dif_pos h] using hm
    · have hm : (1 : Matrices.ComplexMatrix2) ∈ PeriodicLattice.compactGaugeGroup :=
        one_mem Matrices.ComplexMatrix2.specialUnitary
      simpa only [axialGaugeTransform, dif_neg h] using hm
theorem gaugeTransform_one {W : Edge L n k (i + 1) → Matrices.ComplexMatrix2} :
    PeriodicLattice.gaugeTransform (fun _ => (1 : Matrices.ComplexMatrix2)) W = W := by
  funext c
  simp [PeriodicLattice.gaugeTransform]
end AxialProlongation
open AxialProlongation in
theorem axialGaugeOfProlongation_holds
    (hProp : AxialFunctionFacts.statement)
    (hAvg : SmoothingNearIdentity)
    (hConf : GaugeAndSymmetryImages.statement)
    (hBlocks : BlockStructure)
    (hFin : BondSetFields.ProductStructureHolds)
    (hK : Matrices.GroupLieProduct.Subspaces.AnalyticCalculus.AnalyticCalculusStatement) :
    AxialGaugeOfProlongation := by
  intro L n k i hL hn hi b U ε p hb hp
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
  have hP := hProp L n k i hL hn hi
  have hA := ((hAvg.1 L hL).1 n k i hn hi).1
  obtain ⟨Ua, hUa, -, hcon⟩ := hA.analytic
  have hZ : BlocksPartitionFiner L n k (i + 1) :=
    ((hBlocks L k (i + 1) hL (by omega) (by omega) (by omega)).1 n hn).2.1
  have hmemUa := mem_nhdsWithin_trivialField hFin hL hn hi.le Ua hUa
  have hT₁ : Tendsto axialGaugeTransform (𝓝[fieldSpace L n k i] trivialField L n k i)
      (𝓝[gaugeGroupAt L n k i] fun _ => (1 : Matrices.ComplexMatrix2)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun x => ?_, ?_⟩
    · unfold axialGaugeTransform
      by_cases h : (x : PeriodicLattice.FourTorus L n) ∉
          PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1))
      · simp only [dif_pos h]
        have hx := (cubeCentre_spec hZ ⟨x, h⟩).1
        have hc := continuousWithinAt_of_analyticMatrixValued ((hcon _ _ hx).2) hUa.2
        have hone := hP.meanContourHolonomy_trivial _ _ hx
        have ht := hc.tendsto
        rw [hone] at ht
        exact ht.mono_left (nhdsWithin_le_of_mem hmemUa)
      · simp only [dif_neg h]
        exact tendsto_const_nhds
    · filter_upwards [hmemUa] with A hA'
      exact axialGaugeTransform_mem hZ fun y x hx => ((hcon y x hx).1 A hA')
  have hsub : PeriodicLattice.compactGaugeGroup ⊆ PeriodicLattice.complexGaugeGroup :=
    fun X hX => (Matrix.mem_specialUnitaryGroup_iff.1 hX).2
  have hT₂ : Tendsto (fun A => PeriodicLattice.gaugeTransform (axialGaugeTransform A) A)
      (𝓝[fieldSpace L n k i] trivialField L n k i)
      (𝓝[fieldSpace L n k i] trivialField L n k i) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun c => ?_, ?_⟩
    · have hu := tendsto_pi_nhds.1 (hT₁.mono_right nhdsWithin_le_nhds)
      have h₁ := hu c.source
      have h₂ := hu c.target
      have hV : Tendsto (fun A : Edge L n k i → Matrices.ComplexMatrix2 => A c)
          (𝓝[fieldSpace L n k i] trivialField L n k i) (𝓝 (1 : Matrices.ComplexMatrix2)) :=
        ((continuous_apply c).tendsto _).mono_left nhdsWithin_le_nhds
      have hadj : Tendsto (fun A : Edge L n k i → Matrices.ComplexMatrix2 =>
            (axialGaugeTransform A c.target).adjugate)
          (𝓝[fieldSpace L n k i] trivialField L n k i) (𝓝 (1 : Matrices.ComplexMatrix2)) := by
        have h := ((Continuous.matrix_adjugate continuous_id).tendsto
          (1 : Matrices.ComplexMatrix2)).comp h₂
        simpa [Function.comp_def] using h
      have hprod := (h₁.mul hV).mul hadj
      simp only [mul_one] at hprod
      refine hprod.congr' ?_
      filter_upwards [hmemUa] with A hA'
      have hu' := axialGaugeTransform_mem hZ fun y x hx => ((hcon y x hx).1 A hA')
      change _ = axialGaugeTransform A c.source * A c * (axialGaugeTransform A c.target)⁻¹
      rw [inv_eq_adjugate_of_mem (hu' c.target)]
    · filter_upwards [hmemUa, self_mem_nhdsWithin] with A hU hA'
      have hu' := axialGaugeTransform_mem hZ fun y x hx => ((hcon y x hx).1 A hU)
      exact ((hConf L k i hL hi.le).1 n hn A (axialGaugeTransform A) id
        ⟨fun c hc => hsub (hA'.1 c hc), hA'.2⟩ (fun x => hsub (hu' x)) (fun _ _ => rfl)
        (by simp [MapsSublatticeOnto])).2.2.1 hA' hu'
  have hT₃ : Tendsto p (𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1))
      (𝓝[fieldSpace L n k i] trivialField L n k i) := by
    obtain ⟨Wn, hWn, hpa⟩ := hp.analytic_section
    have hc := continuousOn_of_isAnalyticFieldMap hK hpa _ hWn.2
    have hmemWn := mem_nhdsWithin_trivialField hFin hL hn (Nat.succ_le_of_lt hi) Wn hWn
    have ht := hc.tendsto
    rw [hp.section_trivial] at ht
    refine tendsto_nhdsWithin_iff.2 ⟨ht.mono_left (nhdsWithin_le_of_mem hmemWn), ?_⟩
    filter_upwards [hmemWn] with W hW
    exact hpa.2.1 hW
  have hclaim : ∀ᶠ A in 𝓝[fieldSpace L n k i] trivialField L n k i,
      PeriodicLattice.gaugeTransform (axialGaugeTransform A) A ∈ U ∧
      smoothingStep L n k i (PeriodicLattice.gaugeTransform (axialGaugeTransform A) A) =
        smoothingStep L n k i A ∧
      axialFunction L n k i (PeriodicLattice.gaugeTransform (axialGaugeTransform A) A) = 0 ∧
      b.energy i (PeriodicLattice.gaugeTransform (axialGaugeTransform A) A) = b.energy i A ∧
      0 ≤ axialFunction L n k i A ∧
      (axialFunction L n k i A = 0 ↔ IsAxialGaugeAt L n k i A) := by
    have hinv := (hT₁.prodMk Filter.tendsto_id).eventually (hb.energy_gauge_invariant i le_rfl).1
    have hcov : ∀ᶠ A in 𝓝[fieldSpace L n k i] trivialField L n k i,
        ∀ u ∈ gaugeGroupAt L n k i,
          smoothingStep L n k i (PeriodicLattice.gaugeTransform u A) =
              PeriodicLattice.gaugeTransform (restrictVertexFunction (i + 1) u)
                (smoothingStep L n k i A) ∧
            ∀ (y : Vertex L n k (i + 1)),
              ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
                PeriodicLattice.meanContourHolonomy (PeriodicLattice.gaugeTransform u A) y x =
                  u (y.toSublattice (PeriodicLattice.levelDepth k i)) *
                    PeriodicLattice.meanContourHolonomy A y x * (u x)⁻¹ := hA.gauge_covariant
    have hnn : ∀ᶠ A in 𝓝[fieldSpace L n k i] trivialField L n k i,
        0 ≤ axialFunction L n k i A := hP.nonneg
    have hiff : ∀ᶠ A in 𝓝[fieldSpace L n k i] trivialField L n k i,
        axialFunction L n k i A = 0 ↔ IsAxialGaugeAt L n k i A := hP.eq_zero_iff
    filter_upwards [hmemUa, hcov, hT₂.eventually hp.ball_mem_nhds, hinv, hnn, hiff] with
      A hU hc hball hS hnn' hiff'
    have hu' := axialGaugeTransform_mem hZ fun y x hx => ((hcon y x hx).1 A hU)
    obtain ⟨hav, hcontour⟩ := hc _ hu'
    refine ⟨hp.ball_subset hball, ?_, ?_, hS, hnn', hiff'⟩
    · have hres : restrictVertexFunction (i + 1) (axialGaugeTransform A) =
          fun _ => (1 : Matrices.ComplexMatrix2) := by
        funext y
        exact axialGaugeTransform_coarse hLpos A y
      rw [hav, hres]
      exact gaugeTransform_one
    · unfold axialFunction PeriodicLattice.axialGaugeFunction
      simp only [finsum_mem_univ]
      refine finsum_eq_zero_of_forall_eq_zero fun y => ?_
      refine (finsum_mem_congr rfl fun z hz => ?_).trans (finsum_mem_zero _)
      have hcz := hcontour y z hz.1
      have hw := meanContourHolonomy_mem ((hcon y z hz.1).1 A hU)
      have hdet : (PeriodicLattice.meanContourHolonomy A y z).det = 1 :=
        (Matrix.mem_specialUnitaryGroup_iff.1 hw).2
      rw [axialGaugeTransform_coarse hLpos A y, axialGaugeTransform_of_mem_block hZ A hz, one_mul,
        Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one)] at hcz
      rw [hcz]
      norm_num [PeriodicLattice.traceDeficit, Matrices.ComplexMatrix2.fullTrace, Matrix.trace_one]
  have hsec : ∀ᶠ W in 𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1),
      smoothingStep L n k i (p W) = W := hp.smoothing_section
  have hmin : ∀ᶠ W in 𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1),
      ∀ A ∈ CriticalBranchData.levelFibre U W, A ≠ p W →
        b.gaugeFixedEnergy i (p W) < b.gaugeFixedEnergy i A := hp.isMin_fibre
  exact show ∀ᶠ W in 𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1),
      IsAxialGaugeAt L n k i (p W) ∧ b.gaugeFixedEnergy i (p W) = b.energy i (p W) from by
    filter_upwards [hT₃.eventually hclaim, hsec, hmin] with W hW hs hm
    obtain ⟨hU, hav, hz, hS, hnn, hiff⟩ := hW
    have hfib : PeriodicLattice.gaugeTransform (axialGaugeTransform (p W)) (p W) ∈
        CriticalBranchData.levelFibre U W := ⟨hU, hav.trans hs⟩
    have hF' : b.gaugeFixedEnergy i
        (PeriodicLattice.gaugeTransform (axialGaugeTransform (p W)) (p W)) = b.energy i (p W) := by
      unfold CriticalBranchData.gaugeFixedEnergy
      rw [hz, hS, add_zero]
    have hFV : b.energy i (p W) ≤ b.gaugeFixedEnergy i (p W) := by
      unfold CriticalBranchData.gaugeFixedEnergy
      linarith
    have heq : PeriodicLattice.gaugeTransform (axialGaugeTransform (p W)) (p W) = p W := by
      by_contra hne
      have hlt := hm _ hfib hne
      linarith
    have hGF : axialFunction L n k i (p W) = 0 := by
      rw [heq] at hz
      exact hz
    refine ⟨hiff.1 hGF, ?_⟩
    unfold CriticalBranchData.gaugeFixedEnergy
    rw [hGF, add_zero]
end YangMills.Construction.Tower
end
