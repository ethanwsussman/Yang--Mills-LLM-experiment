import YangMills.Construction.Towers.PolydiscServesAtTheSideInfinityProof
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadiusProof
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinity
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATowerProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.LinearityProof
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.LeftChartFields (CurveLogDerivative)
section TwistedCurves
variable {σ : Type}
def twistedFamily (v A : σ → ComplexMatrix2) (z : ℂ) : σ → ComplexMatrix2 :=
  fun b => ComplexMatrix2.matExp (Complex.I • (z • A b)) * v b
def familyDeriv [Fintype σ] (G : (σ → ComplexMatrix2) → ComplexMatrix2) (v : σ → ComplexMatrix2)
    (W : ComplexMatrix2) (A : σ → ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • (fderiv ℂ G v (fun b => Complex.I • A b * v b) * W⁻¹)
theorem familyDeriv_linear [Fintype σ] (G : (σ → ComplexMatrix2) → ComplexMatrix2)
    (v : σ → ComplexMatrix2) (W : ComplexMatrix2) (c : ℂ) (A A' : σ → ComplexMatrix2) :
    familyDeriv G v W (c • A + A') =
      c • familyDeriv G v W A + familyDeriv G v W A' := by
  have e : (fun b => Complex.I • (c • A + A') b * v b) =
      c • (fun b => Complex.I • A b * v b) + fun b => Complex.I • A' b * v b := by
    funext b
    simp only [Pi.add_apply, Pi.smul_apply, smul_add, add_mul, smul_mul_assoc]
    rw [smul_comm Complex.I c]
  unfold familyDeriv
  rw [e, map_add, map_smul, add_mul, smul_mul_assoc, smul_add, smul_comm Complex.I⁻¹ c]
theorem logDeriv_along_twistedFamily [Fintype σ]
    (hlog : ∀ ρ : ℝ, 0 < ρ → CurveLogDerivative ℂ (Metric.ball 0 ρ)
      PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra)
    {D : Set (σ → ComplexMatrix2)} {Φ : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hhol : ComplexMatrix2.IsHolomorphicBetween (fun _ : σ => ComplexMatrix2.FactorKind.group)
      (fun _ : Unit => ComplexMatrix2.FactorKind.group) D fun v _ => Φ v)
    {v : σ → ComplexMatrix2} (hv : v ∈ D) :
    ∃ G : (σ → ComplexMatrix2) → ComplexMatrix2, ∀ A : σ → ComplexMatrix2,
      (∀ z b, twistedFamily v A z b ∈ PeriodicLattice.complexGaugeGroup) →
      (∀ b, HasDerivAt (fun z => twistedFamily v A z b) (Complex.I • A b * v b) 0) →
      (∀ᶠ z in 𝓝 (0 : ℂ), twistedFamily v A z ∈ D) ∧
      Complex.I⁻¹ • deriv (fun z => ComplexMatrix2.logSeries
          (Φ (twistedFamily v A z) * (Φ v)⁻¹)) 0 =
        familyDeriv G v (Φ v) A ∧
      familyDeriv G v (Φ v) A ∈ ComplexMatrix2.traceless := by
  obtain ⟨F, hFa, hFe⟩ := hhol.2.2 v hv
  refine ⟨fun w => F w (), fun A hmem hder => ?_⟩
  have hd : HasDerivAt (twistedFamily v A) (fun b => Complex.I • A b * v b) 0 :=
    hasDerivAt_pi.2 hder
  have hv0 : twistedFamily v A 0 = v := by
    funext b
    simp [twistedFamily]
  obtain ⟨O, hOo, hOe⟩ := hhol.1
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), twistedFamily v A z ∈ D := by
    have hvO : twistedFamily v A 0 ∈ O := by
      rw [hv0]
      rw [hOe] at hv
      exact hv.1
    filter_upwards [hd.continuousAt.eventually (hOo.mem_nhds hvO)] with z hz
    rw [hOe]
    exact ⟨hz, fun b => hmem z b⟩
  have htend : Tendsto (twistedFamily v A) (𝓝 0) (𝓝[D] v) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hnear⟩
    have := hd.continuousAt.tendsto
    rwa [hv0] at this
  have hev := htend.eventually hFe
  have hG : HasFDerivAt (fun w => F w ()) (fderiv ℂ (fun w => F w ()) v)
      (twistedFamily v A 0) := by
    rw [hv0]
    exact ((differentiableAt_pi.1 hFa.differentiableAt) ()).hasFDerivAt
  have hψ : HasDerivAt (fun z => Φ (twistedFamily v A z))
      (fderiv ℂ (fun w => F w ()) v (fun b => Complex.I • A b * v b)) 0 := by
    refine (hG.comp_hasDerivAt (0 : ℂ) hd).congr_of_eventuallyEq ?_
    filter_upwards [hev] with z hz
    exact congrFun hz ()
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnear
  have hmaps : MapsTo (fun z => Φ (twistedFamily v A z)) (Metric.ball 0 r)
      PeriodicLattice.complexGaugeGroup := fun z hz => hhol.2.1 (hball z hz) ()
  obtain ⟨-, -, e, m⟩ := hlog r hr _ hmaps hψ.differentiableAt
  simp only [hv0, hψ.deriv] at e m
  exact ⟨hnear, e, m⟩
end TwistedCurves
section OddForms
variable {a : ℝ}
theorem isPositivelyOriented_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem extendOddly_of_pos (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_of_pos <;> assumption
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) : extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem extendOddly_mem (ha : 0 < a) {f : InfiniteLattice.Link a → ComplexMatrix2}
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.traceless) :
    extendOddly f ∈ complexEdgeForms a :=
  ⟨fun b hb => by
    rw [extendOddly_of_pos f hb]
    exact h b hb, extendOddly_opposite ha f⟩
theorem complexEdgeForms_ext {X Y : InfiniteLattice.Link a → ComplexMatrix2}
    (hX : X ∈ complexEdgeForms a) (hY : Y ∈ complexEdgeForms a)
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → X b = Y b) : X = Y := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    have eX : X b.opposite.opposite = -X b.opposite := hX.2 b.opposite
    have eY : Y b.opposite.opposite = -Y b.opposite := hY.2 b.opposite
    have eX' : X b = -X b.opposite := eX
    have eY' : Y b = -Y b.opposite := eY
    rw [eX', eY', h _ hr]
end OddForms
theorem conjugateBy_traceless (V : ComplexMatrix2) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy V A ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
theorem conjugateBy_linear (V : ComplexMatrix2) (c : ℂ) (A A' : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (c • A + A') =
      c • ComplexMatrix2.conjugateBy V A + ComplexMatrix2.conjugateBy V A' := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.conjugateBy_smul_add <;> assumption
theorem cubeVertices_finite (L : ℕ) {a : ℝ} (a' : ℝ) (y : InfiniteLattice.LatticePoint a) :
    (cubeVertices L a' y : Set (InfiniteLattice.LatticePoint a')).Finite := by
  have hb : {ν : Fin 4 → ℤ | ∀ μ, 2 * |ν μ| ≤ (L : ℤ) ^ 1 - 1}.Finite := by
    refine (Set.Finite.pi' fun _ : Fin 4 => Set.finite_Icc (-(L : ℤ)) L).subset fun ν h μ => ?_
    have h1 := h μ
    rw [pow_one] at h1
    have h2 := abs_le.1 (show |ν μ| ≤ (L : ℤ) by linarith [abs_nonneg (ν μ)])
    exact ⟨h2.1, h2.2⟩
  have hcube : (cube L a' y).Finite := by
    refine (hb.image fun ν : Fin 4 → ℤ =>
      (y : InfiniteLattice.AmbientSpace) + ∑ μ, Pi.single μ ((ν μ : ℝ) * a')).subset ?_
    rintro x ⟨ν, hν, rfl⟩
    exact ⟨ν, hν, rfl⟩
  exact hcube.preimage Subtype.val_injective.injOn
section WeightedSums
variable {ι : Type}
theorem weighted_sum_traceless (L : ℕ) {S : Set ι} (hS : S.Finite) {f : ι → ComplexMatrix2}
    (h : ∀ x ∈ S, f x ∈ ComplexMatrix2.traceless) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ S, f x ∈ ComplexMatrix2.traceless := by
  refine ComplexMatrix2.traceless.smul_mem _ ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ hS]
  exact Submodule.sum_mem _ fun x hx => h x (hS.mem_toFinset.1 hx)
theorem weighted_sum_linear (L : ℕ) {S : Set ι} (hS : S.Finite) {f g h : ι → ComplexMatrix2}
    (c : ℂ) (e : ∀ x ∈ S, f x = c • g x + h x) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ S, f x =
      c • (PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ S, g x) +
        PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ S, h x := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
    finsum_mem_eq_finite_toFinset_sum _ hS,
    Finset.sum_congr rfl fun x hx => e x (hS.mem_toFinset.1 hx), Finset.sum_add_distrib,
    ← Finset.smul_sum, smul_add, smul_comm (PeriodicLattice.inverseFourthPowerWeight L) c]
end WeightedSums
section Levels
variable {L k j : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem inv_inv_of_mem_complexGaugeGroup {X : ComplexMatrix2}
    (h : X ∈ PeriodicLattice.complexGaugeGroup) : X⁻¹⁻¹ = X := by apply _root_.YangMills.SharedProofs.p6288 <;> assumption
theorem opposite_mem_doubleCubeLinks {c : Edge L k (j + 1)} {b : Edge L k j}
    (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) :
    b.opposite ∈ doubleCubeLinks L (meshAt L k j) c := ⟨hb.2, hb.1⟩
theorem extendFromPositive_restrictPositive {c : Edge L k (j + 1)}
    {V : Edge L k j → ComplexMatrix2}
    (hV : IsFieldOn PeriodicLattice.complexGaugeGroup (doubleCubeLinks L (meshAt L k j) c) V)
    {b : Edge L k j} (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) :
    extendFromPositive (doubleCubeLinks L (meshAt L k j) c)
      (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V) b = V b := by apply _root_.YangMills.Construction.Tower.InfiniteSideAdmissibility.fullSpace_extendFromPositive_restrictPositive <;> assumption
theorem mem_polydisc_of_eqOn {ρ : ℝ} {c : Edge L k (j + 1)} {V V' : Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k j ρ c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V' b = V b) :
    V' ∈ nearIdentityPolydisc L k j ρ c := by
  refine ⟨⟨fun b hb => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩
  · rw [he b hb]
    exact hV.1.1 b hb
  · rw [he _ (opposite_mem_doubleCubeLinks hb), he b hb]
    exact hV.1.2 b hb
  · rw [he b hb]
    exact hV.2 b hb
theorem complexContourMean_congr (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {y : Vertex L k (j + 1)}
    (hy : y = c.initial ∨ y = c.terminal)
    {x : Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {V V' : Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (hV' : V' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    complexContourMean L V y x = complexContourMean L V' y x := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hserve := (hS.1 L hL).2.2.fullSpace k j hj c hc
  have hQ' := ((hQ L hL0 hL k).2.2.2.2.2.2 (by omega) 1 one_pos).2 j hj c hc
  have e1 := hQ'.complexContourMean_eq V (hserve.subset_complexDomain hV) y hy x hx
  have e2 := hQ'.complexContourMean_eq V' (hserve.subset_complexDomain hV') y hy x hx
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  funext x'
  unfold projField
  split_ifs with h
  · exact he _ h.choose_spec.1
  · rfl
theorem complexContourMean_eq_extend (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {y : Vertex L k (j + 1)}
    (hy : y = c.initial ∨ y = c.terminal)
    {x : Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {U U' : Edge L k j → ComplexMatrix2}
    (hU' : U' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, U b = U' b) :
    complexContourMean L U y x =
      complexContourMean L (extendFromPositive
        (doubleCubeLinks L (meshAt L k j) c)
        (restrictPositive (doubleCubeLinks L (meshAt L k j) c) U')) y x := by
  have hv := fun b (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) =>
    extendFromPositive_restrictPositive hU'.1 hb
  exact complexContourMean_congr hS hQ hL hj hc hy hx (mem_polydisc_of_eqOn hU' he)
    (mem_polydisc_of_eqOn hU' hv) fun b hb => (he b hb).trans (hv b hb).symm
theorem expTwist_eqOn {ρ : ℝ} {c : Edge L k (j + 1)} {V B U' : Edge L k j → ComplexMatrix2}
    {z : ℂ} (hU' : U' ∈ nearIdentityPolydisc L k j ρ c)
    (e : restrictPositive (doubleCubeLinks L (meshAt L k j) c) U' =
      twistedFamily (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V)
        (fun b => B b.1) z) :
    ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, expTwist (z • B) V b = U' b := by
  have hpos : ∀ b (hb : b ∈ doubleCubeLinks L (meshAt L k j) c)
      (hp : b.IsPositivelyOriented), expTwist (z • B) V b = U' b := by
    intro b hb hp
    have h := congrFun e ⟨b, hb, hp⟩
    have h' : expTwist (z • B) V b =
        ComplexMatrix2.matExp (Complex.I • (z • B) b) * V b := if_pos hp
    rw [h']
    exact h.symm
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · exact hpos b hb hp
  · have hr : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left hp
    have h1 : expTwist (z • B) V b =
        (ComplexMatrix2.matExp (Complex.I • (z • B) b.opposite) * V b.opposite)⁻¹ := if_neg hp
    have h3 : expTwist (z • B) V b.opposite =
        ComplexMatrix2.matExp (Complex.I • (z • B) b.opposite) * V b.opposite := if_pos hr
    rw [h1, ← h3, hpos b.opposite (opposite_mem_doubleCubeLinks hb) hr, hU'.1.2 b hb]
    exact inv_inv_of_mem_complexGaugeGroup (hU'.1.1 b hb)
def IsComplexLinearOnForms (Q : (Edge L k j → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  (∀ B ∈ complexEdgeForms (meshAt L k j), Q B ∈ ComplexMatrix2.traceless) ∧
    ∀ B ∈ complexEdgeForms (meshAt L k j), ∀ B' ∈ complexEdgeForms (meshAt L k j), ∀ c : ℂ,
      Q (c • B + B') = c • Q B + Q B'
theorem isComplexLinearOnForms_of_holomorphic (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) (c : Edge L k (j + 1))
    [Fintype (PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c))]
    {D : Set (PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2)}
    {Φ : (PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2) →
      ComplexMatrix2}
    (hhol : ComplexMatrix2.IsHolomorphicBetween
      (fun _ : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) =>
        ComplexMatrix2.FactorKind.group)
      (fun _ : Unit => ComplexMatrix2.FactorKind.group) D fun v _ => Φ v)
    (hv : restrictPositive (doubleCubeLinks L (meshAt L k j) c) V ∈ D)
    (Q : (Edge L k j → ComplexMatrix2) → ComplexMatrix2)
    (hQ : ∀ B ∈ complexEdgeForms (meshAt L k j),
      (∀ᶠ z in 𝓝 (0 : ℂ), twistedFamily
        (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V)
        (fun b => B b.1) z ∈ D) →
      Q B = Complex.I⁻¹ • deriv (fun z => ComplexMatrix2.logSeries (Φ (twistedFamily
        (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V)
        (fun b => B b.1) z) *
          (Φ (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V))⁻¹)) 0) :
    IsComplexLinearOnForms Q := by
  obtain ⟨G, hG⟩ := logDeriv_along_twistedFamily (fun ρ hρ => hA.2.1 ρ hρ) hhol hv
  have hLeft := ((hA.2.2 L k j hL hj.le).2.1.1).2
  have key : ∀ B ∈ complexEdgeForms (meshAt L k j),
      Q B = familyDeriv G (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V)
          (Φ (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V))
          (fun b => B b.1) ∧
        familyDeriv G (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V)
          (Φ (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V))
          (fun b => B b.1) ∈ ComplexMatrix2.traceless := by
    intro B hB
    obtain ⟨h1, h2, h3⟩ := hG (fun b => B b.1)
      (fun z b => (hLeft V hV.1 B hB ⟨b.1, b.2.2⟩).1 z)
      (fun b => (hLeft V hV.1 B hB ⟨b.1, b.2.2⟩).2)
    exact ⟨(hQ B hB h1).trans h2, h3⟩
  refine ⟨fun B hB => ?_, fun B hB B' hB' c' => ?_⟩
  · rw [(key B hB).1]
    exact (key B hB).2
  · rw [(key _ (Submodule.add_mem _ (Submodule.smul_mem _ c' hB) hB')).1, (key B hB).1,
      (key B' hB').1]
    exact familyDeriv_linear G _ _ c' (fun b => B b.1) (fun b => B' b.1)
theorem complexContourMean_linear (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) (y : Vertex L k (j + 1))
    {x : Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y) :
    IsComplexLinearOnForms fun B => logDirectionalDeriv ℂ
      (fun X => complexContourMean L (expTwist X V) y x)
      (complexContourMean L V y x) B := by
  let c : Edge L k (j + 1) := InfiniteLattice.Link.forwardFrom y 0
  have hc : c.IsPositivelyOriented := ⟨0, by
    show y + InfiniteLattice.axisStep _ 0 - y = _
    abel⟩
  have hserve := (hS.1 L hL).2.2.fullSpace k j hj c hc
  have hyc : y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))) := Or.inl rfl
  have hy : y = c.initial ∨ y = c.terminal := Or.inl rfl
  obtain ⟨inst, hhol⟩ := (hserve.holomorphic_contourMean y hyc x hx).1
  have hVp : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c :=
    ⟨⟨fun b _ => hV.1.1 b, fun b _ => hV.1.2 b⟩, fun b _ => hV.2 b⟩
  have hW := complexContourMean_eq_extend hS hQ hL hj hc hy hx hVp fun _ _ => rfl
  refine isComplexLinearOnForms_of_holomorphic hA hL hj hV c
    (Φ := fun v => complexContourMean L (extendFromPositive
      (doubleCubeLinks L (meshAt L k j) c) v) y x) hhol ⟨V, hVp, rfl⟩ _ fun B _ hnear => ?_
  show logDirectionalDeriv ℂ _ _ B = _
  unfold logDirectionalDeriv
  refine congrArg (fun w => Complex.I⁻¹ • w) (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [hnear] with z hz
  obtain ⟨U', hU', e⟩ := hz
  have e1 := complexContourMean_eq_extend hS hQ hL hj hc hy hx hU' (expTwist_eqOn hU' e)
  rw [e] at e1
  show ComplexMatrix2.logSeries (complexContourMean L (expTwist (z • B) V) y x * _) = _
  rw [e1, hW]
theorem complexSmoothingDeriv_linear (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hO : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) :
    IsComplexLinearOnForms fun B => complexSmoothingDeriv V B c := by
  have hserve := (hS.1 L hL).2.2.fullSpace k j hj c hc
  obtain ⟨inst, hhol⟩ := hserve.holomorphic_smoothing.1
  have hVp : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c :=
    ⟨⟨fun b _ => hV.1.1 b, fun b _ => hV.1.2 b⟩, fun b _ => hV.2 b⟩
  have hFull := (hW L hL k (by omega)).2
  have hsmall : V ∈ MeanStableFields.Infinite.fieldsNearOne L k j := hV
  obtain ⟨F₂, hF₂, hpw⟩ := hFull.polydisc_presentation j hj c hc
  have hw₂ := hpw V hsmall
  obtain ⟨F₁, O₁, f₁, hw₁, hk₁⟩ :=
    (hFull.holomorphic_smoothing j hj c hc OneLoop.pauliBasis).2 V hsmall
  have hex : ∃ w : LocalData L k j ComplexMatrix2,
      IsLocalPresentation PeriodicLattice.complexGaugeGroup (smallComplexFields L k j)
        (fun U' => smoothingMap L k j U' c) V w.support w.region w.fn ∧
      holomorphicPresentations L k j OneLoop.pauliBasis
        Coordinates.ComplexCoordinates.matrixEquiv w.support w.region w.fn :=
    ⟨⟨F₁, O₁, f₁⟩, hw₁, hk₁⟩
  have spec := Classical.epsilon_spec hex
  have hone := (hO L k j hL.1 hL.2 hj.le).1.2.2.2
  have hV0 : smoothingMap L k j V c = complexSmoothing L (extendFromPositive
      (doubleCubeLinks L (meshAt L k j) c)
      (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V)) c :=
    hw₂.2.2.2 V hsmall hw₂.2.2.1
  refine isComplexLinearOnForms_of_holomorphic hA hL hj hV c
    (Φ := fun v => complexSmoothing L (extendFromPositive
      (doubleCubeLinks L (meshAt L k j) c) v) c) hhol ⟨V, hVp, rfl⟩ _ fun B hB _ => ?_
  obtain ⟨ε, hε, h⟩ := hone (smallComplexFields L k j) (hFull.isFinitelyOpen_nearOne j hj)
    (fun U' => smoothingMap L k j U' c) V hsmall _ _ _ F₂ _ _ spec.1 hw₂ B 0
    (fun b hb => hB.1 b hb) (fun _ _ => ComplexMatrix2.traceless.zero_mem)
  have e : complexSmoothingDeriv V B c = logDirectionalDeriv ℂ
      (valueViaPresentation PeriodicLattice.complexGaugeGroup (smallComplexFields L k j)
        (holomorphicPresentations L k j OneLoop.pauliBasis
          Coordinates.ComplexCoordinates.matrixEquiv)
        (fun U' => smoothingMap L k j U' c) V) (smoothingMap L k j V c) B := by
    unfold complexSmoothingDeriv holLeftDifferential extendOddly
    exact if_pos hc
  show complexSmoothingDeriv V B c = _
  rw [e, hV0]
  unfold logDirectionalDeriv
  refine congrArg (fun w => Complex.I⁻¹ • w) (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with t ht
  have ht' : ‖t‖ < ε := by simpa using ht
  have h3 := (h t 0 ht' (by simpa using hε)).2.2
  have m1 : ∀ F : Finset (Edge L k j),
      UniqueValue.perturbedTuple F B 0 V (algebraMap ℂ ℂ t) (algebraMap ℂ ℂ 0) =
        fun b : F => ComplexMatrix2.matExp (Complex.I • (t • B) b.1) * V b.1 := by
    intro F
    funext b
    simp [UniqueValue.perturbedTuple]
  rw [m1, m1] at h3
  have m2 : MeanStableFields.Infinite.smoothingOnFinset c F₂ hF₂
      (fun b : F₂ => ComplexMatrix2.matExp (Complex.I • (t • B) b.1) * V b.1) =
      complexSmoothing L (extendFromPositive
        (doubleCubeLinks L (meshAt L k j) c)
        (twistedFamily (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V)
          (fun b => B b.1) t)) c := rfl
  show ComplexMatrix2.logSeries ((chosenPresentation PeriodicLattice.complexGaugeGroup
    (smallComplexFields L k j)
    (holomorphicPresentations L k j OneLoop.pauliBasis Coordinates.ComplexCoordinates.matrixEquiv)
    (fun U' => smoothingMap L k j U' c) V).fn
      (fun b => ComplexMatrix2.matExp (Complex.I • (t • B) b.1) * V b.1) * _) = _
  exact congrArg (fun Y => ComplexMatrix2.logSeries (Y * _)) (h3.trans m2)
end Levels
theorem covariantStepComplexLinear_holds (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hO : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hA : LeftChartFields.Claim) :
    CovariantStepComplexLinear := by
  intro L hL k j hj V hV
  have ha := meshAt_pos hL k j
  have ha' := meshAt_pos hL k (j + 1)
  have avg := fun (c : Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
    complexSmoothingDeriv_linear hS hO hW hA hL hj hV hc
  have ctr := fun (y : Vertex L k (j + 1)) (x : Vertex L k j)
      (hx : x ∈ cubeVertices L (meshAt L k j) y) =>
    complexContourMean_linear hS hQ hA hL hj hV y hx
  have formQ : ∀ B ∈ complexEdgeForms (meshAt L k j),
      complexSmoothingDeriv V B ∈ complexEdgeForms (meshAt L k (j + 1)) :=
    fun B hB => ⟨fun c hc => (avg c hc).1 B hB, fun b => by
      unfold complexSmoothingDeriv holLeftDifferential
      exact extendOddly_opposite ha' _ b⟩
  have formD : ∀ l : Vertex L k j → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
      covDiff V l ∈ complexEdgeForms (meshAt L k j) := fun l hl =>
    extendOddly_mem ha fun b _ =>
      ComplexMatrix2.traceless.sub_mem (conjugateBy_traceless _ (hl _)) (hl _)
  refine ⟨fun B hB => ⟨formQ B hB, fun y => ?_⟩, fun B hB B' hB' c => ⟨?_, ?_⟩, fun l hl =>
    ⟨formD l hl, fun y => ?_⟩, fun l l' hl hl' c => ⟨?_, ?_⟩⟩
  · exact weighted_sum_traceless L (cubeVertices_finite L _ y) fun x hx => (ctr y x hx).1 B hB
  · refine complexEdgeForms_ext (formQ _ (Submodule.add_mem _ (Submodule.smul_mem _ c hB) hB'))
      (Submodule.add_mem _ (Submodule.smul_mem _ c (formQ B hB)) (formQ B' hB')) fun b hb => ?_
    exact (avg b hb).2 B hB B' hB' c
  · funext y
    exact weighted_sum_linear L (cubeVertices_finite L _ y) c fun x hx =>
      (ctr y x hx).2 B hB B' hB' c
  · exact weighted_sum_traceless L (cubeVertices_finite L _ y) fun x _ =>
      conjugateBy_traceless _ (hl x)
  · refine complexEdgeForms_ext
      (formD _ fun x => ComplexMatrix2.traceless.add_mem
        (ComplexMatrix2.traceless.smul_mem c (hl x)) (hl' x))
      (Submodule.add_mem _ (Submodule.smul_mem _ c (formD l hl)) (formD l' hl')) fun b hb => ?_
    show extendOddly _ b = c • extendOddly _ b + extendOddly _ b
    rw [extendOddly_of_pos _ hb, extendOddly_of_pos _ hb, extendOddly_of_pos _ hb]
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [conjugateBy_linear, smul_sub]
    abel
  · funext y
    exact weighted_sum_linear L (cubeVertices_finite L _ y) c fun x _ =>
      conjugateBy_linear _ c _ _
end YangMills.Construction.Tower.FullSpace.LinearityProof
