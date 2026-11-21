import YangMills.Construction.Towers.AverageIsDifferentiableOnThePolydisc
import YangMills.Construction.Towers.ChainRuleAtTheSideInfinityInTheLeftChartProof
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinityProof
import YangMills.Construction.Towers.RelationsOfOneCovariantStepAtTheSideInfinityProof
import YangMills.Construction.Towers.WritingOfTheRealAveragingMap
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.CompactPresentation
open YangMills.Construction.Tower.BondSetFields
open YangMills.Construction.Tower.DoubleBlockPolydisc
variable {L k j : ℕ}
theorem isPositivelyOriented_or_opposite {a : ℝ} (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem mem_complexGaugeGroup_of_mem_compact {X : Matrices.ComplexMatrix2}
    (h : X ∈ PeriodicLattice.compactGaugeGroup) : X ∈ PeriodicLattice.complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.mp h).2
theorem inv_inv_of_mem_complexGaugeGroup {X : Matrices.ComplexMatrix2}
    (h : X ∈ PeriodicLattice.complexGaugeGroup) : X⁻¹⁻¹ = X := by apply _root_.YangMills.SharedProofs.p6288 <;> assumption
theorem mem_finset_iff {c : Edge L k (j + 1)} {F : Finset (Edge L k j)}
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (b : Edge L k j) :
    b ∈ F ↔ b ∈ doubleCubeLinks L (meshAt L k j) c ∧ b.IsPositivelyOriented := by
  have h : b ∈ (F : Set (Edge L k j)) ↔
      b ∈ DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c := by rw [hF]
  exact Finset.mem_coe.symm.trans h
theorem opposite_mem_doubleCubeLinks {c : Edge L k (j + 1)} {b : Edge L k j}
    (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) :
    b.opposite ∈ doubleCubeLinks L (meshAt L k j) c := ⟨hb.2, hb.1⟩
theorem fieldOfValues_apply_eq {c : Edge L k (j + 1)} {V : Edge L k j → Matrices.ComplexMatrix2}
    (hV : IsFieldOn PeriodicLattice.complexGaugeGroup
      (doubleCubeLinks L (meshAt L k j) c) V)
    {b : Edge L k j} (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) :
    DoubleBlockPolydisc.Infinite.fieldOfValues L k j c (fun b => V b.1) b = V b := by
  unfold DoubleBlockPolydisc.Infinite.fieldOfValues extendFromPositive
  by_cases hp : b.IsPositivelyOriented
  · rw [dif_pos (⟨hb, hp⟩ : b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c ∧
      b.IsPositivelyOriented)]
  · have hrp : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left hp
    have hrb : b.opposite ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c :=
      opposite_mem_doubleCubeLinks hb
    rw [dif_neg (fun h : b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c ∧
        b.IsPositivelyOriented => hp h.2),
      dif_pos (⟨hrb, hrp⟩ : b.opposite ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c ∧
        b.opposite.IsPositivelyOriented)]
    have e : (V b.opposite)⁻¹ = ((V b)⁻¹)⁻¹ := congrArg (·⁻¹) (hV.2 b hb)
    exact e.trans (inv_inv_of_mem_complexGaugeGroup (hV.1 b hb))
theorem mem_polydisc_of_eqOn {ρ : ℝ} {c : Edge L k (j + 1)}
    {V V' : Edge L k j → Matrices.ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k j ρ c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V' b = V b) :
    V' ∈ nearIdentityPolydisc L k j ρ c := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.mem_polydisc_of_eqOn <;> assumption
theorem complexSmoothing_congr (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {V V' : Edge L k j → Matrices.ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (hV' : V' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    complexSmoothing L V c = complexSmoothing L V' c := by apply _root_.YangMills.Construction.Tower.FullSpace.StepRelations.complexSmoothing_congr <;> assumption
theorem complexSmoothing_eq_smoothingOfRestriction (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {V : Edge L k j → Matrices.ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c) :
    complexSmoothing L V c = smoothingOfRestriction c V := by
  have he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
      DoubleBlockPolydisc.Infinite.fieldOfValues L k j c (fun b => V b.1) b = V b :=
    fun b hb => fieldOfValues_apply_eq hV.1 hb
  exact complexSmoothing_congr hS hQ hL hj hc hV (mem_polydisc_of_eqOn hV he)
    fun b hb => (he b hb).symm
theorem mem_polydisc_of_mem_fieldSpace {ρ : ℝ} {c : Edge L k (j + 1)}
    {U : Edge L k j → Matrices.ComplexMatrix2} (hU : U ∈ fieldSpace L k j)
    (hn : ∀ b, Matrices.ComplexMatrix2.operatorNorm (U b - 1) < ρ) :
    U ∈ nearIdentityPolydisc L k j ρ c :=
  ⟨⟨fun b _ => mem_complexGaugeGroup_of_mem_compact (hU.1 b), fun b _ => hU.2 b⟩, fun b _ => hn b⟩
theorem mem_compactPolydiscOn_iff {c : Edge L k (j + 1)} {F : Finset (Edge L k j)}
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    {ρ : ℝ} {w : F → Matrices.ComplexMatrix2} :
    w ∈ compactPolydiscOn hF ρ ↔ ∃ V : Edge L k j → Matrices.ComplexMatrix2,
      V ∈ nearIdentityPolydisc L k j ρ c ∧
      IsFieldOn PeriodicLattice.compactGaugeGroup (doubleCubeLinks L (meshAt L k j) c) V ∧
      ∀ b (hb : b ∈ F), V b = w ⟨b, hb⟩ := by
  constructor
  · rintro ⟨_, ⟨V, hV, rfl⟩, he⟩
    refine ⟨V, hV.1, hV.2, fun b hb => ?_⟩
    exact congrFun he ⟨b, (mem_finset_iff hF b).1 hb⟩
  · rintro ⟨V, h1, h2, h3⟩
    refine ⟨_, ⟨V, ⟨h1, h2⟩, rfl⟩, ?_⟩
    funext b
    exact h3 _ _
theorem restrictToEdges_mem_compactPolydiscOn {c : Edge L k (j + 1)} {F : Finset (Edge L k j)}
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    {ρ : ℝ} {U : Edge L k j → Matrices.ComplexMatrix2} (hU : U ∈ fieldSpace L k j)
    (hn : ∀ b, Matrices.ComplexMatrix2.operatorNorm (U b - 1) < ρ) :
    restrictToEdges F U ∈ compactPolydiscOn hF ρ :=
  (mem_compactPolydiscOn_iff hF).2 ⟨U, mem_polydisc_of_mem_fieldSpace hU hn,
    ⟨fun b _ => hU.1 b, fun b _ => hU.2 b⟩, fun _ _ => rfl⟩
theorem mem_polydisc_of_restrictToEdges_mem {c : Edge L k (j + 1)} {F : Finset (Edge L k j)}
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    {ρ : ℝ} {U : Edge L k j → Matrices.ComplexMatrix2} (hU : U ∈ fieldSpace L k j)
    (hw : restrictToEdges F U ∈ compactPolydiscOn hF ρ) : U ∈ nearIdentityPolydisc L k j ρ c := by
  obtain ⟨V, hV, _, he⟩ := (mem_compactPolydiscOn_iff hF).1 hw
  refine mem_polydisc_of_eqOn hV fun b hb => ?_
  rcases isPositivelyOriented_or_opposite b with hp | hp
  · exact (he b ((mem_finset_iff hF b).2 ⟨hb, hp⟩)).symm
  · have hr := (mem_finset_iff hF _).2 ⟨opposite_mem_doubleCubeLinks hb, hp⟩
    have h1 : U b = (U b.opposite)⁻¹ := hU.2 b.opposite
    have h2 : V b = (V b.opposite)⁻¹ := hV.1.2 b.opposite (opposite_mem_doubleCubeLinks hb)
    rw [h1, h2]
    exact congrArg (·⁻¹) (he _ hr).symm
theorem isRelativelyOpen_compactPolydiscOn {c : Edge L k (j + 1)} {F : Finset (Edge L k j)}
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    {ρ : ℝ}
    (h : Matrices.ComplexMatrix2.IsRelativelyOpen
      (Matrices.specialUnitaryPower
        (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c))
      (compactPolydiscImage ρ c)) :
    Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.specialUnitaryPower F)
      (compactPolydiscOn hF ρ) := by
  obtain ⟨W, hW, he⟩ := h
  refine ⟨reindexPositive hF ⁻¹' W,
    hW.preimage (continuous_pi fun b => continuous_apply _), ?_⟩
  ext w
  show reindexPositive hF w ∈ compactPolydiscImage ρ c ↔ _
  rw [he]
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · intro b
    exact h.2 ⟨b.1, (mem_finset_iff hF b.1).1 b.2⟩
  · intro b
    exact h.2 _
theorem fieldOfValues_reindexPositive {c : Edge L k (j + 1)} {F : Finset (Edge L k j)}
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (w : F → Matrices.ComplexMatrix2) :
    DoubleBlockPolydisc.Infinite.fieldOfValues L k j c (reindexPositive hF w) =
      fieldOfValuesOn F w := by
  have hm := mem_finset_iff hF
  funext b
  unfold DoubleBlockPolydisc.Infinite.fieldOfValues extendFromPositive fieldOfValuesOn
  by_cases h : b ∈ F
  · rw [dif_pos ((hm b).1 h), dif_pos h]
    rfl
  · rw [dif_neg (fun h' => h ((hm b).2 h')), dif_neg h]
    by_cases h' : b.opposite ∈ F
    · rw [dif_pos ((hm _).1 h'), dif_pos h']
      rfl
    · rw [dif_neg (fun h'' => h' ((hm _).2 h'')), dif_neg h']
theorem differentiableOnOpen_smoothingOn (hD : ComplexSmoothingDifferentiableOnPolydisc)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {ρ : ℝ}
    (hρ : IsAdmissiblePolydiscRadius L ρ)
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented) {F : Finset (Edge L k j)}
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (hopen : Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.specialUnitaryPower F)
      (compactPolydiscOn hF ρ)) :
    Matrices.EmbeddedSubmanifold.DifferentiableOnOpen (Matrices.specialUnitaryPower F)
      (compactPolydiscOn hF ρ) (smoothingOn hF) := by
  refine ⟨hopen, fun χ => ?_⟩
  have hsub : compactPolydiscOn hF ρ ⊆ nearIdentityValues F ρ := by
    intro w hw
    obtain ⟨V, hV, hV', he⟩ := (mem_compactPolydiscOn_iff hF).1 hw
    refine ⟨fun b => ?_, fun b => ?_⟩
    · have h := hV'.1 b.1 ((mem_finset_iff hF b.1).1 b.2).1
      rw [he b.1 b.2] at h
      exact h
    · have h := hV.2 b.1 ((mem_finset_iff hF b.1).1 b.2).1
      rw [he b.1 b.2] at h
      exact h
  have hfun : smoothingOn hF = fun w => complexSmoothing L (fieldOfValuesOn F w) c := by
    funext w
    show complexSmoothing L (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c
      (reindexPositive hF w)) c = _
    rw [fieldOfValues_reindexPositive hF w]
  rw [hfun]
  exact ((hD L hL k j hj ρ hρ c hc F (mem_finset_iff hF)).2 χ).mono fun u hu => ⟨hu.1, hsub hu.2⟩
theorem hasPolydiscPresentation (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hD : ComplexSmoothingDifferentiableOnPolydisc)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {𝔇 : Set (Edge L k j → Matrices.ComplexMatrix2)}
    (h𝔇 : 𝔇 ⊆ smoothingDomain L k j)
    {U : Edge L k j → Matrices.ComplexMatrix2} (hU : U ∈ 𝔇)
    (hn : ∀ b : Edge L k j, Matrices.ComplexMatrix2.operatorNorm (U b - 1) < polydiscRadius L) :
    HasPolydiscPresentation 𝔇 U c := by
  have hfo := ((hP L hL k j hj).2 c hc).finite_open
  refine ⟨hfo.positive_finite, hfo.positive_nonempty, fun F hF => ?_⟩
  have hopen := isRelativelyOpen_compactPolydiscOn hF hfo.isRelativelyOpen_compact
  refine ⟨hopen, differentiableOnOpen_smoothingOn hD hL hj (hS.1 L hL).2.2 hc hF hopen,
    ⟨?_, fun b hb => ((mem_finset_iff hF b).1 hb).2⟩, hopen,
    restrictToEdges_mem_compactPolydiscOn hF (h𝔇 hU).1 hn, fun U' hU' hw => ?_⟩
  · obtain ⟨b, hb⟩ := hfo.positive_nonempty
    exact ⟨b, (mem_finset_iff hF b).2 hb⟩
  · exact complexSmoothing_eq_smoothingOfRestriction hS hQ hL hj hc
      (mem_polydisc_of_restrictToEdges_mem hF (h𝔇 hU').1 hw)
theorem deriv_ofReal_eq_deriv {g : ℂ → Matrices.ComplexMatrix2} (hg : DifferentiableAt ℂ g 0) :
    deriv (fun t : ℝ => g (t : ℂ)) 0 = deriv g 0 := by
  have hof : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have h : HasDerivAt g (deriv g 0) ((fun t : ℝ => (t : ℂ)) 0) := by
    simpa using hg.hasDerivAt
  have e := (HasDerivAt.scomp (0 : ℝ) h hof).deriv
  rw [one_smul] at e
  exact e
theorem differentiableAt_logSeries_twist (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {U B : Edge L k j → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldSpace L k j)
    (hn : ∀ b : Edge L k j, Matrices.ComplexMatrix2.operatorNorm (U b - 1) < polydiscRadius L)
    (hB : B ∈ edgeFormSpace (meshAt L k j)) :
    DifferentiableAt ℂ (fun z : ℂ => Matrices.ComplexMatrix2.logSeries
      (smoothingOfRestriction c (expTwist (z • B) U) * (smoothingOfRestriction c U)⁻¹)) 0 := by
  have hserve := (hS.1 L hL).2.2.fullSpace k j hj c hc
  obtain ⟨inst, hhol⟩ := hserve.holomorphic_smoothing.1
  have hUp : U ∈ nearIdentityPolydisc L k j (polydiscRadius L) c :=
    mem_polydisc_of_mem_fieldSpace hU hn
  have hLeft := ((hA.2.2 L k j hL hj.le).2.1.1).2
  have hUc : U ∈ (LeftChartFields.fullData L k j).fields
      PeriodicLattice.complexGaugeGroup :=
    ⟨fun b => mem_complexGaugeGroup_of_mem_compact (hU.1 b), hU.2⟩
  have hBc : B ∈ (LeftChartFields.fullData L k j).cforms :=
    ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
  let v : ℂ → PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → Matrices.ComplexMatrix2 :=
    fun z b => Matrices.ComplexMatrix2.matExp (Complex.I • (z • B b.1)) * U b.1
  have hvmem : ∀ z b, v z b ∈ PeriodicLattice.complexGaugeGroup := fun z b =>
    (hLeft U hUc B hBc ⟨b.1, b.2.2⟩).1 z
  have hvd : DifferentiableAt ℂ v 0 := by
    refine differentiableAt_pi.2 fun b => ?_
    have h : HasDerivAt (fun z : ℂ => v z b) _ 0 := (hLeft U hUc B hBc ⟨b.1, b.2.2⟩).2
    exact h.differentiableAt
  have hv0 : v 0 = restrictPositive (doubleCubeLinks L (meshAt L k j) c) U := by
    funext b
    simp [v, restrictPositive]
  have hD0 : v 0 ∈ restrictPositive (doubleCubeLinks L (meshAt L k j) c) ''
      nearIdentityPolydisc L k j (polydiscRadius L) c := ⟨U, hUp, hv0.symm⟩
  obtain ⟨W, hWo, hWe⟩ := hhol.1
  have hDnear : ∀ᶠ z in 𝓝 (0 : ℂ), v z ∈
      restrictPositive (doubleCubeLinks L (meshAt L k j) c) ''
        nearIdentityPolydisc L k j (polydiscRadius L) c := by
    have hW0 : v 0 ∈ W := by
      rw [hWe] at hD0
      exact hD0.1
    filter_upwards [hvd.continuousAt.eventually (hWo.mem_nhds hW0)] with z hz
    rw [hWe]
    exact ⟨hz, fun b => hvmem z b⟩
  obtain ⟨G, hGa, hGe⟩ := hhol.2.2 _ hD0
  have htend : Tendsto v (𝓝 0) (𝓝[restrictPositive
      (doubleCubeLinks L (meshAt L k j) c) ''
        nearIdentityPolydisc L k j (polydiscRadius L) c] (v 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hvd.continuousAt, hDnear⟩
  have hev := htend.eventually hGe
  have hψ : ∀ z : ℂ, smoothingOfRestriction c (expTwist (z • B) U) =
      complexSmoothing L (extendFromPositive
        (doubleCubeLinks L (meshAt L k j) c) (v z)) c := by
    intro z
    have : (readPositive InfiniteLattice.Link.IsPositivelyOriented
        (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c)
        (restrictTo (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c)
          (expTwist (z • B) U))) = v z := by
      funext b
      show expTwist (z • B) U b.1 = _
      unfold expTwist
      rw [if_pos b.2.2]
      rfl
    unfold smoothingOfRestriction smoothingAtValues
    rw [this]
  have hψd : DifferentiableAt ℂ
      (fun z : ℂ => smoothingOfRestriction c (expTwist (z • B) U)) 0 := by
    have hg : DifferentiableAt ℂ (fun z => G (v z) ()) 0 :=
      (differentiableAt_pi.1 (hGa.differentiableAt.comp (0 : ℂ) hvd)) ()
    refine hg.congr_of_eventuallyEq ?_
    filter_upwards [hev] with z hz
    rw [hψ]
    exact congrFun hz ()
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hDnear
  have hmaps : MapsTo (fun z : ℂ => smoothingOfRestriction c (expTwist (z • B) U))
      (Metric.ball 0 r) PeriodicLattice.complexGaugeGroup := by
    intro z hz
    show smoothingOfRestriction c (expTwist (z • B) U) ∈ PeriodicLattice.complexGaugeGroup
    rw [hψ]
    exact hhol.2.1 (hball z hz) ()
  have hlog := ((hA.2.1 r hr) _ hmaps hψd).2.1
  have h0 : smoothingOfRestriction c (expTwist ((0 : ℂ) • B) U) =
      smoothingOfRestriction c U := by
    rw [hψ, hv0]
    rfl
  simp only [h0] at hlog
  exact hlog
theorem perturbedTuple_eq_twistedPoint (F : Finset (Edge L k j))
    (U B : Edge L k j → Matrices.ComplexMatrix2) (s : ℂ) :
    UniqueValue.perturbedTuple F B 0 U s 0 = twistedPoint F U (s • B) := by
  funext b
  simp [UniqueValue.perturbedTuple, twistedPoint]
theorem smoothingOn_twistedPoint {c : Edge L k (j + 1)} {F : Finset (Edge L k j)}
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (U X : Edge L k j → Matrices.ComplexMatrix2) :
    smoothingOn hF (twistedPoint F U X) = smoothingOfRestriction c (expTwist X U) := by
  have : reindexPositive hF (twistedPoint F U X) =
      readPositive InfiniteLattice.Link.IsPositivelyOriented
        (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c)
        (restrictTo (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c)
          (expTwist X U)) := by
    funext b
    show _ = expTwist X U b.1
    unfold expTwist
    rw [if_pos b.2.2]
    rfl
  unfold smoothingOn smoothingOfRestriction
  rw [this]
theorem logDirectionalDeriv_congr_complex {α : Type}
    {φ₁ φ₂ : (α → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    {W : Matrices.ComplexMatrix2} {B : α → Matrices.ComplexMatrix2}
    (h : ∀ᶠ t in 𝓝 (0 : ℂ), φ₁ (algebraMap ℂ ℂ t • B) = φ₂ (algebraMap ℂ ℂ t • B)) :
    logDirectionalDeriv ℂ φ₁ W B = logDirectionalDeriv ℂ φ₂ W B := by apply _root_.YangMills.Construction.Tower.FullSpaceChainRule.logDirectionalDeriv_congr_complex <;> assumption
theorem logDirectionalDeriv_eq_complexSmoothingDeriv (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hO : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {U B : Edge L k j → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldSpace L k j)
    (hn : ∀ b : Edge L k j, Matrices.ComplexMatrix2.operatorNorm (U b - 1) < polydiscRadius L)
    (hB : B ∈ edgeFormSpace (meshAt L k j)) :
    logDirectionalDeriv ℂ (fun X => smoothingOfRestriction c (expTwist X U))
        (smoothingOfRestriction c U) B =
      complexSmoothingDeriv U B c := by
  have hsmall : U ∈ MeanStableFields.Infinite.fieldsNearOne L k j :=
    ⟨⟨fun b => mem_complexGaugeGroup_of_mem_compact (hU.1 b), hU.2⟩, hn⟩
  have hWhole := (hW L hL k (by omega)).2
  obtain ⟨F₁, O₁, f₁, hw₁, hk₁⟩ :=
    (hWhole.holomorphic_smoothing j hj c hc OneLoop.pauliBasis).2 U hsmall
  have hex : ∃ w : LocalData L k j Matrices.ComplexMatrix2,
      IsLocalPresentation PeriodicLattice.complexGaugeGroup (smallComplexFields L k j)
        (fun U' => smoothingMap L k j U' c) U w.support w.region w.fn ∧
      holomorphicPresentations L k j OneLoop.pauliBasis
        Coordinates.ComplexCoordinates.matrixEquiv w.support w.region w.fn :=
    ⟨⟨F₁, O₁, f₁⟩, hw₁, hk₁⟩
  have spec := Classical.epsilon_spec hex
  have e : complexSmoothingDeriv U B c = logDirectionalDeriv ℂ
      (valueViaPresentation PeriodicLattice.complexGaugeGroup (smallComplexFields L k j)
        (holomorphicPresentations L k j OneLoop.pauliBasis
          Coordinates.ComplexCoordinates.matrixEquiv)
        (fun U' => smoothingMap L k j U' c) U) (smoothingMap L k j U c) B := by
    unfold complexSmoothingDeriv holLeftDifferential extendOddly
    exact if_pos hc
  have hWU : smoothingMap L k j U c = smoothingOfRestriction c U :=
    complexSmoothing_eq_smoothingOfRestriction hS hQ hL hj hc
      (mem_polydisc_of_mem_fieldSpace hU hn)
  obtain ⟨F₂, hF₂, hpw⟩ := hWhole.polydisc_presentation j hj c hc
  have hone := (hO L k j hL.1 hL.2 hj.le).1.2.2.2
  obtain ⟨ε, hε, h⟩ := hone (smallComplexFields L k j) (hWhole.isFinitelyOpen_nearOne j hj)
    (fun U' => smoothingMap L k j U' c) U hsmall _ _ _ F₂ _ _ spec.1 (hpw U hsmall) B 0
    (fun b hb => (hB.1 b hb).2) (fun _ _ => Submodule.zero_mem _)
  rw [e, hWU]
  refine logDirectionalDeriv_congr_complex ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with t ht
  have ht' : ‖t‖ < ε := by simpa using ht
  have h3 := (h t 0 ht' (by simpa using hε)).2.2
  simp only [map_zero, perturbedTuple_eq_twistedPoint] at h3
  exact (h3.trans (smoothingOn_twistedPoint hF₂ U _)).symm
theorem derivAgrees (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hD : ComplexSmoothingDifferentiableOnPolydisc)
    (hO : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {𝔇 : Set (Edge L k j → Matrices.ComplexMatrix2)}
    (h𝔇 : 𝔇 ⊆ smoothingDomain L k j)
    {U : Edge L k j → Matrices.ComplexMatrix2} (hU : U ∈ 𝔇)
    (hn : ∀ b : Edge L k j, Matrices.ComplexMatrix2.operatorNorm (U b - 1) < polydiscRadius L)
    (hopen : IsFinitelyOpen PeriodicLattice.compactGaugeGroup 𝔇)
    {B : Edge L k j → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace (meshAt L k j)) :
    DerivAgrees 𝔇 U c B := by
  have hUc : U ∈ fieldSpace L k j := (h𝔇 hU).1
  obtain ⟨hfin, _, hall⟩ := hasPolydiscPresentation hS hP hQ hD hL hj hc h𝔇 hU hn
  have hF₀ : ((hfin.toFinset : Finset (Edge L k j)) : Set (Edge L k j)) =
      DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c := hfin.coe_toFinset
  obtain ⟨_, hd₀, hW₀⟩ := hall hfin.toFinset hF₀
  have hone := (hO L k j hL.1 hL.2 hj.le).1.2.1
  have hvalue : ∀ (F : Finset (Edge L k j)) (O : Set (F → Matrices.ComplexMatrix2))
      (f : (F → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2),
      IsLocalPresentation PeriodicLattice.compactGaugeGroup 𝔇 (smoothingAt c) U F O f →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
        twistedPoint F U ((t : ℂ) • B) ∈ O ∧
          f (twistedPoint F U ((t : ℂ) • B)) =
            smoothingOfRestriction c (expTwist ((t : ℂ) • B) U) := by
    intro F O f hw
    obtain ⟨ε, hε, h⟩ := hone 𝔇 hopen (smoothingAt c) U hU F O f _ _ _ hw hW₀ B 0 hB
      (Submodule.zero_mem _)
    refine ⟨ε, hε, fun t ht => ?_⟩
    obtain ⟨h1, _, h3⟩ := h t 0 (by simpa using ht) (by simpa using hε)
    simp only [map_zero, perturbedTuple_eq_twistedPoint] at h1 h3
    exact ⟨h1, h3.trans (smoothingOn_twistedPoint hF₀ U _)⟩
  have hh := logDirectionalDeriv_eq_complexSmoothingDeriv hS hQ hO hW hL hj hc hUc hn hB
  have hcurve := differentiableAt_logSeries_twist hS hA hL hj hc hUc hn hB
  have hWU : smoothingAt c U = smoothingOfRestriction c U :=
    complexSmoothing_eq_smoothingOfRestriction hS hQ hL hj hc
      (mem_polydisc_of_mem_fieldSpace hUc hn)
  have helem : ∀ (F : Finset (Edge L k j)) (O : Set (F → Matrices.ComplexMatrix2))
      (f : (F → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2),
      IsLocalPresentation PeriodicLattice.compactGaugeGroup 𝔇 (smoothingAt c) U F O f →
      logDirectionalDeriv ℝ (fun X => f (twistedPoint F U X)) (smoothingAt c U) B =
        logDirectionalDeriv ℂ (fun X => smoothingOfRestriction c (expTwist X U))
          (smoothingOfRestriction c U) B := by
    intro F O f hw
    obtain ⟨ε, hε, hv⟩ := hvalue F O f hw
    rw [hWU]
    unfold logDirectionalDeriv
    refine congrArg (fun z => Complex.I⁻¹ • z) ?_
    have hr := deriv_ofReal_eq_deriv hcurve
    refine Eq.trans (Filter.EventuallyEq.deriv_eq ?_) hr
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    have ht' : |t| < ε := by simpa using ht
    exact congrArg (fun Y => Matrices.ComplexMatrix2.logSeries
      (Y * (smoothingOfRestriction c U)⁻¹)) (hv t ht').2
  refine ⟨hvalue, helem, hh, ?_⟩
  have hex : ∃ w : LocalData L k j Matrices.ComplexMatrix2,
      IsLocalPresentation PeriodicLattice.compactGaugeGroup 𝔇
        (fun U' => smoothingMap L k j U' c) U w.support w.region w.fn ∧
      differentiablePresentations L k j Matrices.ComplexMatrix2 w.support w.region w.fn :=
    ⟨⟨hfin.toFinset, _, _⟩, hW₀, hd₀⟩
  have spec := Classical.epsilon_spec hex
  have e : leftDifferential 𝔇 (smoothingMap L k j) U B c = logDirectionalDeriv ℝ
      (valueViaPresentation PeriodicLattice.compactGaugeGroup 𝔇
        (differentiablePresentations L k j Matrices.ComplexMatrix2)
        (fun U' => smoothingMap L k j U' c) U) (smoothingMap L k j U c) B := by
    unfold leftDifferential extendOddly
    exact if_pos hc
  rw [e]
  exact (helem _ _ _ spec.1).trans hh
theorem presentationTheorem_holds
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hD : ComplexSmoothingDifferentiableOnPolydisc)
    (hO : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hA : LeftChartFields.Claim) :
    PresentationTheorem := by
  intro L hL k j hj c hc 𝔇 h𝔇 U hU hn
  exact ⟨hasPolydiscPresentation hS hP hQ hD hL hj hc h𝔇 hU hn, fun hopen B hB =>
    derivAgrees hS hP hQ hD hO hW hA hL hj hc h𝔇 hU hn hopen hB⟩
end YangMills.Construction.Tower.FullSpace.CompactPresentation
end
