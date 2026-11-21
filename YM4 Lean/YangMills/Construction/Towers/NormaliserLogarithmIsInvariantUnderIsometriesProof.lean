import YangMills.Construction.Towers.GaussianNumberUnderMapsThatKeepThePairing
import YangMills.Construction.Towers.IsometriesInTheLeftChart
import YangMills.Construction.Towers.IsometryCovarianceOfTheLiftProof
import YangMills.Construction.Towers.NormaliserLogarithmIsInvariantUnderIsometries
import YangMills.Construction.Towers.RealAnalyticMapsAlongPaths
import YangMills.Construction.Towers.TheFixedFamilyOfTheCriticalBranch
import YangMills.Construction.Towers.TheFormOnAFibreOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace SymmetryInvariance
theorem eventually_forall_of_finite_range {α X K : Type*} [Finite K] {l : Filter X} (key : α → K)
    {Q : K → X → Prop} (h : ∀ a, ∀ᶠ x in l, Q (key a) x) : ∀ᶠ x in l, ∀ a, Q (key a) x := by apply _root_.YangMills.Construction.Tower.LiftSymmetryCovariance.eventually_forall_of_finite_index <;> assumption
theorem eventually_comp_within_of_const {ι X : Type*} [Finite ι] [TopologicalSpace X] (x : X)
    {D : Set (ι → X)} {Q : (ι → X) → Prop} (h : ∀ᶠ W in 𝓝[D] (fun _ : ι => x), Q W) :
    ∀ᶠ W in 𝓝[D] (fun _ : ι => x), ∀ g : ι → ι, W ∘ g ∈ D → Q (W ∘ g) := by apply _root_.YangMills.Construction.Tower.LiftSymmetryCovariance.eventually_comp_within <;> assumption
theorem exists_adjugate_clm :
    ∃ A : Matrices.ComplexMatrix2 →L[ℝ] Matrices.ComplexMatrix2,
      ∀ X : Matrices.ComplexMatrix2, A X = X.adjugate := by
  let A₀ : Matrices.ComplexMatrix2 →ₗ[ℝ] Matrices.ComplexMatrix2 :=
    { toFun := Matrix.adjugate
      map_add' := fun X Y => by
        rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
        ext a b
        fin_cases a <;> fin_cases b <;> simp <;> ring
      map_smul' := fun c X => by
        rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
        ext a b
        fin_cases a <;> fin_cases b <;> simp }
  exact ⟨LinearMap.toContinuousLinearMap A₀, fun _ => rfl⟩
theorem inv_eq_adjugate_of_mem {X : Matrices.ComplexMatrix2}
    (hX : X ∈ PeriodicLattice.compactGaugeGroup) : X⁻¹ = X.adjugate := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.inv_eq_adjugate_of_mem <;> assumption
theorem mul_adjugate_eq_one {X : Matrices.ComplexMatrix2}
    (hX : X ∈ PeriodicLattice.compactGaugeGroup) : X * X.adjugate = 1 := by
  have hdet : X.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.1 hX).2
  rw [Matrix.mul_adjugate, hdet, one_smul]
theorem adjugate_mul_eq_one {X : Matrices.ComplexMatrix2}
    (hX : X ∈ PeriodicLattice.compactGaugeGroup) : X.adjugate * X = 1 := by
  have hdet : X.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.1 hX).2
  rw [Matrix.adjugate_mul, hdet, one_smul]
variable {L n k i j : ℕ}
theorem isPositivelyOriented_or_opposite (b : Edge L n k i) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem apply_eq_adjugate_opposite {V : Edge L n k j → Matrices.ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (b : Edge L n k j) : V b = (V b.opposite).adjugate := by
  have h2 := hV.2 b.opposite (mem_univ _)
  rw [← inv_eq_adjugate_of_mem (hV.1 b.opposite (mem_univ _)), ← h2]
  rfl
theorem curveTangent_congr {δ δ' : ℝ → Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), δ t = δ' t) : curveTangent δ = curveTangent δ' := by
  unfold curveTangent
  congr 1
  funext b
  have h0 : δ 0 = δ' 0 := h.self_of_nhds
  have hd : (fun t => δ t b) =ᶠ[𝓝 0] fun t => δ' t b := h.mono fun t ht => by
    show δ t b = δ' t b
    rw [ht]
  rw [hd.deriv_eq, h0]
variable {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
theorem tangentEdgeValue_of_path {δ : ℝ → Edge L n k j → Matrices.ComplexMatrix2}
    (hδ : IsDiffAtZeroPath δ) (b : Edge L n k j) :
    DifferentiableAt ℝ (fun t => δ t b) 0 ∧
      Complex.I⁻¹ • (deriv (fun t => δ t b) 0 * (δ 0 b)⁻¹) =
        tangentEdgeValue (δ 0) (curveTangent δ) b := by
  obtain ⟨hc, hd⟩ := hδ
  by_cases hb : b.IsPositivelyOriented
  · refine ⟨hd b hb, ?_⟩
    unfold tangentEdgeValue curveTangent extendOddly
    rw [if_pos hb, if_pos hb]
  have hr : b.opposite.IsPositivelyOriented :=
    (isPositivelyOriented_or_opposite b).resolve_left hb
  obtain ⟨A, hA⟩ := exists_adjugate_clm
  set g : ℝ → Matrices.ComplexMatrix2 := fun t => δ t b.opposite with hg
  have hgd : HasDerivAt g (deriv g 0) 0 := (hd _ hr).hasDerivAt
  set D : Matrices.ComplexMatrix2 := deriv g 0 with hD
  have hAg : HasDerivAt (fun t => A (g t)) (A D) 0 := A.hasFDerivAt.comp_hasDerivAt 0 hgd
  have hval : (fun t => δ t b) =ᶠ[𝓝 0] fun t => A (g t) :=
    hc.mono fun t ht => by
      show δ t b = A (g t)
      rw [hA]
      exact apply_eq_adjugate_opposite ht b
  have hbd : HasDerivAt (fun t => δ t b) (A D) 0 := hAg.congr_of_eventuallyEq hval
  refine ⟨hbd.differentiableAt, ?_⟩
  have hc0 : δ 0 ∈ fieldSpace L n k j := hc.self_of_nhds
  have hgG : g 0 ∈ PeriodicLattice.compactGaugeGroup := hc0.1 b.opposite (mem_univ _)
  set a : Matrices.ComplexMatrix2 := (g 0).adjugate with ha
  have h₁ : a * g 0 = 1 := adjugate_mul_eq_one hgG
  have h₂ : g 0 * a = 1 := mul_adjugate_eq_one hgG
  have hprod : HasDerivAt (fun t => g t * A (g t)) (D * A (g 0) + g 0 * A D) 0 := hgd.mul hAg
  have hone : (fun t => g t * A (g t)) =ᶠ[𝓝 0] fun _ => (1 : Matrices.ComplexMatrix2) :=
    hc.mono fun t ht => by
      show g t * A (g t) = 1
      rw [hA]
      exact mul_adjugate_eq_one (ht.1 b.opposite (mem_univ _))
  have hzero : D * a + g 0 * A D = 0 := by
    have h := (hprod.congr_of_eventuallyEq hone.symm).unique
      (hasDerivAt_const (0 : ℝ) (1 : Matrices.ComplexMatrix2))
    rwa [hA] at h
  have h₃ : A D * g 0 = -(a * D) := by
    have h : a * (D * a + g 0 * A D) * g 0 = 0 := by
      rw [hzero]
      simp
    have e : a * (D * a + g 0 * A D) * g 0 = a * D + A D * g 0 := by
      rw [mul_add, add_mul]
      congr 1
      · rw [← mul_assoc, mul_assoc (a * D), h₁, mul_one]
      · rw [← mul_assoc a, h₁, one_mul]
    rw [e] at h
    exact eq_neg_of_add_eq_zero_right h
  have hb0 : δ 0 b = a := apply_eq_adjugate_opposite hc0 b
  have hbinv : (δ 0 b)⁻¹ = g 0 := by
    rw [hb0]
    exact Matrix.inv_eq_left_inv h₂
  have hginv : (g 0)⁻¹ = a := inv_eq_adjugate_of_mem hgG
  have hainv : a⁻¹ = g 0 := Matrix.inv_eq_left_inv h₂
  have hrev : curveTangent δ b.opposite = Complex.I⁻¹ • (D * (g 0)⁻¹) := by
    unfold curveTangent extendOddly
    rw [if_pos hr]
  unfold tangentEdgeValue
  rw [if_neg hb, hbd.deriv, hbinv, hrev]
  change _ = -Matrices.ComplexMatrix2.conjugateBy (g 0)⁻¹ (Complex.I⁻¹ • (D * (g 0)⁻¹))
  unfold Matrices.ComplexMatrix2.conjugateBy
  rw [hginv, hainv, h₃, mul_smul_comm, smul_mul_assoc, smul_neg, ← mul_assoc, mul_assoc (a * D),
    h₁, mul_one]
theorem pushField_path
    (hmem : ∀ U ∈ fieldSpace L n k j, pushField (k := k) (j := j) f U ∈ fieldSpace L n k j)
    {δ : ℝ → Edge L n k j → Matrices.ComplexMatrix2} (hδ : IsDiffAtZeroPath δ) :
    IsDiffAtZeroPath (fun t => pushField (k := k) (j := j) f (δ t)) ∧
      curveTangent (fun t => pushField (k := k) (j := j) f (δ t)) =
        isometryOnTangent f (δ 0) (curveTangent δ) := by
  refine ⟨⟨hδ.1.mono fun t ht => hmem _ ht, fun c _ => (tangentEdgeValue_of_path hδ _).1⟩, ?_⟩
  unfold curveTangent isometryOnTangent
  congr 1
  funext c
  exact (tangentEdgeValue_of_path hδ (edgePreimage f c)).2
theorem pushField_curve
    (hmem : ∀ U ∈ fieldSpace L n k j, pushField (k := k) (j := j) f U ∈ fieldSpace L n k j)
    {I J : Set ℝ} {γ : ℝ → Edge L n k j → Matrices.ComplexMatrix2}
    (hγ : (fieldCurveData L n k j).IsTwiceDiffCurve I γ)
    (hJ : IsOpenIntervalAroundZero J) (hJI : J ⊆ I) :
    (fieldCurveData L n k j).IsTwiceDiffCurve J
      (fun t => pushField (k := k) (j := j) f (γ t)) := by
  obtain ⟨⟨-, hmaps, hdiff⟩, hdd⟩ := hγ
  obtain ⟨A, hA⟩ := exists_adjugate_clm
  have hval : ∀ (b : Edge L n k j) (t : ℝ), t ∈ J → γ t b = A (γ t b.opposite) :=
    fun b t ht => by
      rw [hA]
      exact apply_eq_adjugate_opposite (hmaps (hJI ht)) b
  refine ⟨⟨hJ, fun t ht => hmem _ (hmaps (hJI ht)), fun c _ => ?_⟩, fun c _ => ?_⟩
  · change DifferentiableOn ℝ (fun t => γ t (edgePreimage f c)) J
    by_cases hb : (edgePreimage (k := k) (j := j) f c).IsPositivelyOriented
    · exact (hdiff _ hb).mono hJI
    · have hr := (isPositivelyOriented_or_opposite (edgePreimage (k := k) (j := j) f c)).resolve_left hb
      exact (A.differentiable.comp_differentiableOn ((hdiff _ hr).mono hJI)).congr
        fun t ht => hval _ t ht
  · change DifferentiableOn ℝ (deriv fun t => γ t (edgePreimage f c)) J
    by_cases hb : (edgePreimage (k := k) (j := j) f c).IsPositivelyOriented
    · exact (hdd _ hb).mono hJI
    · have hr := (isPositivelyOriented_or_opposite (edgePreimage (k := k) (j := j) f c)).resolve_left hb
      refine (A.differentiable.comp_differentiableOn ((hdd _ hr).mono hJI)).congr fun t ht => ?_
      have hev : (fun s => γ s (edgePreimage f c)) =ᶠ[𝓝 t]
          fun s => A (γ s (edgePreimage (k := k) (j := j) f c).opposite) :=
        Filter.eventually_of_mem (hJ.1.mem_nhds ht) fun s hs => hval _ s hs
      have hd := (hdiff _ hr t (hJI ht)).differentiableAt
        (Filter.mem_of_superset (hJ.1.mem_nhds ht) hJI)
      rw [hev.deriv_eq]
      exact (A.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv
section Vertices
theorem axialFunction_pushField [Finite (Vertex L n k i)] [Finite (Vertex L n k (i + 1))]
    (hm₀ : MapsSublatticeOnto k i f) (hm₁ : MapsSublatticeOnto k (i + 1) f)
    (hblock : ∀ y : Vertex L n k (i + 1),
      f '' PeriodicLattice.unitBlock y = PeriodicLattice.unitBlock (vertexImage (k := k) f y))
    (hsub : ∀ y : Vertex L n k (i + 1), PeriodicLattice.unitBlock y ⊆
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
        Set (PeriodicLattice.FourTorus L n)))
    (hself : ∀ y : Vertex L n k (i + 1),
      (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y)
    {V : Edge L n k i → Matrices.ComplexMatrix2}
    (hc : ∀ y : Vertex L n k (i + 1),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
        PeriodicLattice.meanContourHolonomy (pushField f V) (vertexImage (k := k) f y)
          (vertexImage (k := k) (j := i) f x) = PeriodicLattice.meanContourHolonomy V y x) :
    axialFunction L n k i (pushField f V) = axialFunction L n k i V := by apply _root_.YangMills.Construction.Tower.LiftSymmetryCovariance.axialFunction_pushField <;> assumption
end Vertices
end SymmetryInvariance
open SymmetryInvariance in
theorem logNormaliserRatio_symmetry_invariant
    (hForm : CriticalFibreHessianPosDef)
    (hFixed : ChosenBranchIsCritical)
    (hGauss : ConstrainedGaussianIsometryInvariance)
    (hPaths : diffAtZeroPathsStatement)
    (hMaps : AnalyticMapsAlongCurves)
    (hIso : LeftChartIsometryEquivariance)
    (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hFinite : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hImages : GaugeAndSymmetryImages.statement)
    (hBlocks : BlockStructure)
    (hAvg : SmoothingEquivariantOnSides) :
    LogNormaliserRatioSymmetryInvariant := by
  intro L n k hL hn i hi
  have hik : i < k := hi
  have hL0 : 0 < L := by have := hL.2; omega
  have finite₀ := hFinite L hL n i k hn hik.le
  have finite₁ := hFinite L hL n (i + 1) k hn hik
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hS₀, hB₀, -⟩, -⟩ := finite₀
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hS₁, hB₁, -⟩, -⟩ := finite₁
  have : Finite (Vertex L n k i) := hS₀
  have : Finite (Vertex L n k (i + 1)) := hS₁
  have : Finite (Edge L n k i) := hB₀
  have : Finite (Edge L n k (i + 1)) := hB₁
  have hfacts : ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
      IsLevelSymmetry k (i + 1) f → MapsSublatticeOnto k i f := by
    intro f hf
    obtain ⟨-, hrest⟩ := (hT L hL0 hL k).2.2.2.1 n hn (i + 1) hik f hf.1 hf.2
    exact (hrest i (Nat.le_succ i)).1
  have hblocks := (hBlocks L k (i + 1) hL (by omega) (by omega) hik).1 n hn
  have hself : ∀ y : Vertex L n k (i + 1),
      (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
    intro y
    have h : (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∩
        (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) :
          Set (PeriodicLattice.FourTorus L n)) := by
      rw [hblocks.2.1.1 y]
      exact mem_singleton _
    exact h.1
  have hsub : ∀ y : Vertex L n k (i + 1), PeriodicLattice.unitBlock y ⊆
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
        Set (PeriodicLattice.FourTorus L n)) :=
    fun y => (hblocks.1 y).2.2.2
  have hmem : ∀ {j : ℕ}, j ≤ k → ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
      IsDistancePreserving f → MapsSublatticeOnto k j f → ∀ U ∈ fieldSpace L n k j,
        pushField (k := k) (j := j) f U ∈ fieldSpace L n k j := by
    intro j hj f hf hm U hU
    have hUc : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ U :=
      ⟨fun c hc => (Matrix.mem_specialUnitaryGroup_iff.1 (hU.1 c hc)).2, hU.2⟩
    have hu : PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup
        (fun _ : Vertex L n k j => (1 : Matrices.ComplexMatrix2)) := fun _ => Matrix.det_one
    exact ((hImages L k j hL hj).1 n hn U _ f hUc hu hf hm).2.2.2 hU
  obtain ⟨hb, hU'⟩ := hFixed L n k hL hn
  have hU := hU' i hik
  let Key : Type :=
    (Edge L n k i → Edge L n k i) × (Edge L n k (i + 1) → Edge L n k (i + 1)) ×
      (Vertex L n k i → Vertex L n k i) × (Vertex L n k (i + 1) → Vertex L n k (i + 1))
  let Iso : Type := {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n //
    IsLevelSymmetry k (i + 1) f}
  let key : Iso → Key := fun f =>
    (edgePreimage (k := k) (j := i) f.1, edgePreimage (k := k) (j := i + 1) f.1,
      vertexImage (k := k) (j := i) f.1, vertexImage (k := k) (j := i + 1) f.1)
  let Q : Key → (Edge L n k i → Matrices.ComplexMatrix2) → Prop := fun c V =>
    (∀ y : Vertex L n k (i + 1),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
        PeriodicLattice.meanContourHolonomy (V ∘ c.1) (c.2.2.2 y) (c.2.2.1 x) =
          PeriodicLattice.meanContourHolonomy V y x) ∧
    smoothingStep L n k i (V ∘ c.1) = smoothingStep L n k i V ∘ c.2.1
  have : Finite Key := by
    dsimp only [Key]
    infer_instance
  have hQ : ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : Matrices.ComplexMatrix2)),
      ∀ f : Iso, Q (key f) V :=
    eventually_forall_of_finite_range key fun f => hAvg L hL n k i hn hik f.1 f.2.1 f.2.2
  have hFun : ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : Matrices.ComplexMatrix2)),
      ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n, IsLevelSymmetry k i f →
        (chosenCriticalBranch L n k).energy i (pushField f V) =
          (chosenCriticalBranch L n k).energy i V :=
    hb.energy_symmetry_invariant i hik.le
  let Good : (Edge L n k i → Matrices.ComplexMatrix2) → Prop := fun V =>
    ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n, IsLevelSymmetry k (i + 1) f →
      chosenGaugeFixedEnergy L n k i (pushField f V) = chosenGaugeFixedEnergy L n k i V ∧
        smoothingStep L n k i (pushField f V) = pushField f (smoothingStep L n k i V)
  have hGood : ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : Matrices.ComplexMatrix2)), Good V := by
    filter_upwards [hQ, hFun] with V h₁ h₂ f hf
    have hm₀ := hfacts f hf
    obtain ⟨hc, ha⟩ := h₁ ⟨f, hf⟩
    refine ⟨?_, ha⟩
    change (chosenCriticalBranch L n k).gaugeFixedEnergy i _ =
      (chosenCriticalBranch L n k).gaugeFixedEnergy i _
    unfold CriticalBranchData.gaugeFixedEnergy
    rw [h₂ f ⟨hf.1, hm₀⟩, axialFunction_pushField hm₀ hf.2 (hblocks.2.2.2 f hf.1 hf.2) hsub
      hself hc]
  have hGood₂ := eventually_eventually_nhdsWithin.2 hGood
  have hTend : Tendsto (chosenProlong L n k i)
      (𝓝[fieldSpace L n k (i + 1)] (fun _ => (1 : Matrices.ComplexMatrix2)))
      (𝓝[fieldSpace L n k i] (fun _ => (1 : Matrices.ComplexMatrix2))) := by
    obtain ⟨𝒲, h𝒲, hA⟩ := hb.analytic_prolong i hik
    have hc := ((hMaps L n k (i + 1) i hL hn hi hik.le).1 𝒲 _ hA).1 _ h𝒲.2
    have hnear := (hPaths L n k (i + 1) hL hn hi).2.1 𝒲 h𝒲.1 _ h𝒲.2
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.mem_of_superset hnear fun W hW => hA.2.1 hW⟩
    have h := hc.tendsto.mono_left (nhdsWithin_le_of_mem hnear)
    rwa [hb.prolong_trivial i hik] at h
  have hP := hForm L n k hL hn i hi
  have hPaths₀ := hPaths L n k i hL hn hik.le
  have hm := (hMaps L n k i (i + 1) hL hn hik.le hi).1 _ _ hU.analytic_smoothing
  have hsub𝒰 : chosenFibreNhd L n k i ⊆ fieldSpace L n k i :=
    hU.isOpenNhd.1.1
  unfold EventuallyNearIdentity at hP ⊢
  filter_upwards [eventually_comp_within_of_const (1 : Matrices.ComplexMatrix2) hP, hP,
    hTend.eventually hGood₂, hb.prolong_symmetry_equivariant i hik, self_mem_nhdsWithin]
    with W hrel hPW hgoodV hliftW hWD f hf
  have hm₀ := hfacts f hf
  have hmem₀ := hmem hik.le f hf.1 hm₀
  have hmem₁ := hmem hi f hf.1 hf.2
  have hsWD := hmem₁ W hWD
  have hPs := hrel (edgePreimage (k := k) (j := i + 1) f) hsWD
  have hcomp : W ∘ edgePreimage (k := k) (j := i + 1) f = pushField f W := rfl
  rw [hcomp] at hPs
  obtain ⟨hcrit, -, hhess, hcurves, -⟩ := hPW
  obtain ⟨hcrit', -, hhess', -, -⟩ := hPs
  have hV' : chosenProlong L n k i (pushField f W) =
      pushField f (chosenProlong L n k i W) := hliftW f hf
  set V := chosenProlong L n k i W with hVdef
  have hVN := hcrit.1
  have hV'N := hcrit'.1
  rw [hV'] at hV'N
  have hVc : V ∈ fieldSpace L n k i := hsub𝒰 hVN.1
  have hVC : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ V :=
    ⟨fun c hc => (Matrix.mem_specialUnitaryGroup_iff.1 (hVc.1 c hc)).2, hVc.2⟩
  have hWC : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ W :=
    ⟨fun c hc => (Matrix.mem_specialUnitaryGroup_iff.1 (hWD.1 c hc)).2, hWD.2⟩
  obtain ⟨e, he, hpair⟩ := ((hIso L k i hL hik.le).1 n hn f hf.1 hm₀ V hVC).2 hVc
  obtain ⟨e', he', hpair'⟩ := ((hIso L k (i + 1) hL hi).1 n hn f hf.1 hf.2 W hWC).2 hWD
  have hZ : gaussianNormaliser L n k i (pushField f W) = gaussianNormaliser L n k i W := by
    refine hGauss L n k i (i + 1) L n k i (i + 1) e e' ?_ ?_ _ _ ?_ _ _ ?_
    · intro B B'
      rw [he, he, hpair]
    · intro B B'
      rw [he', he', hpair']
    · intro B
      apply Subtype.ext
      obtain ⟨hδp, hδ0, hδt⟩ := hPaths₀.2.2 V hVc B B.2
      set δ : ℝ → Edge L n k i → Matrices.ComplexMatrix2 :=
        fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k i → Matrices.ComplexMatrix2)) V
        with hδdef
      have hδ0' : δ 0 = V := hδ0
      obtain ⟨hsδ, hsδt⟩ := pushField_path hmem₀ hδp
      obtain ⟨hspecV, hpathV⟩ := hm.2 V hVN.1
      obtain ⟨hspecV', hpathV'⟩ := hm.2 _ hV'N.1
      obtain ⟨hMδ, hMδt⟩ := hpathV δ hδp hδ0'
      obtain ⟨-, hsMδt⟩ := pushField_path hmem₁ hMδ
      obtain ⟨-, hMsδt⟩ := hpathV' _ hsδ (by
        show pushField f (δ 0) = _
        rw [hδ0'])
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), smoothingStep L n k i (pushField f (δ t)) =
          pushField f (smoothingStep L n k i (δ t)) := by
        have ht := (hPaths₀.1 δ hδp).2
        rw [hδ0'] at ht
        exact (ht.eventually hgoodV).mono fun t h => (h f hf).2
      have hM0 : smoothingStep L n k i (δ 0) = W := by
        rw [hδ0']
        exact hVN.2
      have e1 : ((e B : edgeFormSpace L n k i) : Edge L n k i → Matrices.ComplexMatrix2) =
          curveTangent (fun t => pushField f (δ t)) := by
        rw [he, hsδt, hδt, hδ0']
      have hcL : constraintDifferential L n k i (pushField f W) =
          leftDifferentialLinear (smoothingStep L n k i) (pushField f V) := by
        unfold constraintDifferential
        rw [hV']
      have hcW : ((constraintDifferential L n k i W B : edgeFormSpace L n k (i + 1)) :
          Edge L n k (i + 1) → Matrices.ComplexMatrix2) =
          leftDifferential (smoothingStep L n k i) V B := hspecV B
      rw [hcL, hspecV', e1, ← hMsδt, curveTangent_congr hev, hsMδt, he', hM0, hMδt, hδt, hcW]
    · intro B B' hB
      obtain ⟨I, γ, htw, hmaps, h0, ht⟩ := hcurves B
      have hT₁ := hhess I γ B htw hmaps h0 ht
      have hI := htw.1.1
      have hI0 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
      have hγ : IsDiffAtZeroPath γ :=
        ⟨Filter.eventually_of_mem hI0 fun t ht => htw.1.2.1 ht,
          fun b hb => (htw.1.2.2 b hb 0 hI.2.2).differentiableAt hI0⟩
      obtain ⟨hsγ, hsγt⟩ := pushField_path hmem₀ hγ
      have ev₁ : ∀ᶠ t in 𝓝 (0 : ℝ), pushField f (γ t) ∈ chosenFibreNhd L n k i := by
        have h₁ := (hPaths₀.1 _ hsγ).2
        refine h₁.eventually ?_
        show chosenFibreNhd L n k i ∈ 𝓝[fieldSpace L n k i] (pushField f (γ 0))
        rw [h0]
        exact hPaths₀.2.1 _ hU.isOpenNhd.1 _ hV'N.1
      have ev₂ : ∀ᶠ t in 𝓝 (0 : ℝ), Good (γ t) := by
        have h₁ := (hPaths₀.1 γ hγ).2
        rw [h0] at h₁
        exact h₁.eventually hgoodV
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (ev₁.and ev₂)
      have hJ : IsOpenIntervalAroundZero (I ∩ Metric.ball (0 : ℝ) ε) := by
        refine ⟨hI.1.inter Metric.isOpen_ball, ?_, hI.2.2, Metric.mem_ball_self hε⟩
        have hb : (Metric.ball (0 : ℝ) ε).OrdConnected := by
          rw [Real.ball_eq_Ioo]
          exact ordConnected_Ioo
        exact hI.2.1.inter hb
      have hcurve := pushField_curve hmem₀ htw hJ inter_subset_left
      have hmapsJ : MapsTo (fun t => pushField f (γ t)) (I ∩ Metric.ball (0 : ℝ) ε)
          (chosenLevelFibre L n k i (pushField f W)) := fun t ht' => by
        refine ⟨(hball t ht'.2).1, ?_⟩
        rw [((hball t ht'.2).2 f hf).2, (hmaps ht'.1).2]
      have hT₂ := hhess' _ _ B' hcurve hmapsJ (by
        show pushField f (γ 0) = _
        rw [h0, hV']) (by
        show curveTangent _ = ((B'.1 : edgeFormSpace L n k i) : Edge L n k i → Matrices.ComplexMatrix2)
        have ht' : curveTangent γ =
            ((B.1 : edgeFormSpace L n k i) : Edge L n k i → Matrices.ComplexMatrix2) := ht
        rw [hsγt, h0, hB, he, ht'])
      rw [hT₁, hT₂]
      have hev : (fun t => chosenGaugeFixedEnergy L n k i (pushField f (γ t))) =ᶠ[𝓝 0]
          fun t => chosenGaugeFixedEnergy L n k i (γ t) :=
        (Metric.eventually_nhds_iff_ball.2 ⟨ε, hε, hball⟩).mono fun t h => (h.2 f hf).1
      exact hev.deriv.deriv_eq
  unfold logNormaliserRatio
  rw [hZ]
end YangMills.Construction.Tower
end
