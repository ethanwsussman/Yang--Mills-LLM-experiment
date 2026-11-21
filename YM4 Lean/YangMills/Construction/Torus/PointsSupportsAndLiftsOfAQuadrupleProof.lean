import YangMills.Construction.Continuum.RingsRingTracesAndTheirIntegrals
import YangMills.Construction.Torus.OneBallLiftAndTransportOfQuadruplesProof
import YangMills.Construction.Torus.PointsSupportsAndLiftsOfAQuadruple
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric TestFunctions TorusMeasure PlaquetteSupports
namespace QuadrupleGeometry
abbrev GeometryInput : Prop := QuadrupleGeometryStatement
abbrev CellsInput : Prop := TorusMeasure.TranslatedLatticeCells.CellsAndBallsStatement
abbrev CoveringInput : Prop := TorusCovering.CoveringIntegralVolumeStatement
abbrev RingsInput : Prop := FreeRingKernels.RingIntegrals.Statement
theorem dist_le_eight_mul_of_iInf_le {Y : Type*} (D : Y → Y → ℝ) (hsymm : ∀ a b, D a b = D b a)
    (htri : ∀ a b c, D a b ≤ D a c + D c b) {d : ℝ} (hd : 0 < d) {A B : Set Y} {x y : Y}
    (hA : ∀ u ∈ A, D u x ≤ d) (hB : ∀ v ∈ B, D v y ≤ d)
    (hinf : (⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (D a b)) ≤ ENNReal.ofReal (6 * d)) :
    D x y ≤ 8 * d := by apply _root_.YangMills.Construction.QuadrupleBalls.dist_centers_le_of_infDist_le <;> assumption
theorem euclidDistR4_comm (a b : Fin 4 → ℝ) : euclidDistR4 a b = euclidDistR4 b a := by apply _root_.YangMills.Construction.QuadrupleGeometry.euclidDistR4_symm <;> assumption
theorem euclidDistR4_triangle (a b c : Fin 4 → ℝ) :
    euclidDistR4 a b ≤ euclidDistR4 a c + euclidDistR4 c b := by apply _root_.YangMills.Construction.QuadrupleGeometry.euclidDistR4_le_add <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem isCompact_of_subset_closedBallR4 {A : Set (Fin 4 → ℝ)} (hA : IsClosed A) {c : Fin 4 → ℝ}
    {r : ℝ} (hsub : A ⊆ closedBallR4 c r) : IsCompact A := by
  refine (isCompact_closedBall c r).of_isClosed_subset hA fun y hy => ?_
  have hy' : euclidNormVec (y - c) ≤ r := hsub hy
  have hr : 0 ≤ r := (Real.sqrt_nonneg _).trans hy'
  rw [mem_closedBall_iff_norm, pi_norm_le_iff_of_nonneg hr]
  intro μ
  exact (abs_apply_le_euclidNormVec (y - c) μ).trans hy'
theorem memQuadsR4Iff_holds (hg : GeometryInput) {d ϑ : ℝ} (hd : 0 < d) (hϑ : ϑ ∈ Ioc (0 : ℝ) 1) :
    MemQuadsR4Iff d ϑ := by
  intro f hlip
  constructor
  · intro hf
    obtain ⟨hne, hx, hdist⟩ := (hg.1 d ϑ hd hϑ f hf).1
    choose x hx using hx
    refine ⟨hne, x, fun i => ?_, hdist⟩
    obtain ⟨-, -, -, -, h1, h2, h3⟩ := hx i
    exact ⟨h1, h2, h3⟩
  · rintro ⟨hne, x, hx, hdist⟩
    refine ⟨⟨hd, hϑ⟩, hlip, fun i j hij => ⟨x i, x j, ?_, ?_, (hdist i j hij).1, (hdist i j hij).2⟩⟩
    · exact ⟨(hlip i).1, (hlip i).2, hne i, (hx i).1, (hx i).2.1, (hx i).2.2⟩
    · exact ⟨(hlip j).1, (hlip j).2, hne j, (hx j).1, (hx j).2.1, (hx j).2.2⟩
theorem witnessGeometryR4_holds (hg : GeometryInput) {d ϑ : ℝ} (hd : 0 < d)
    (hϑ : ϑ ∈ Ioc (0 : ℝ) 1) : WitnessGeometryR4 d ϑ := by
  intro f hf x hx
  obtain ⟨hdist, -, hone⟩ := (hg.1 d ϑ hd hϑ f hf).2.1
  obtain ⟨-, hlip, -⟩ := hf
  have hsub : ∀ i, euclideanTSupport (f i) ⊆ closedBallR4 (x 0) (9 * d) :=
    hone (x 0) ⟨hd, hϑ, (hlip 0).1, (hlip 0).2, (hx.1 0).1, (hx.1 0).2.1, (hx.1 0).2.2⟩
  refine ⟨fun i j hij => ?_, hdist, hsub, fun i => ?_, fun i j hij => ?_⟩
  · exact dist_le_eight_mul_of_iInf_le euclidDistR4 euclidDistR4_comm euclidDistR4_triangle hd
      (fun u hu => (hx.1 i).1 hu) (fun v hv => (hx.1 j).1 hv) (hx.2 i j hij).2
  · exact isCompact_of_subset_closedBallR4 (isClosed_tsupport _) (hsub i)
  · refine Set.disjoint_left.2 fun u hu hv => ?_
    have h := (hdist i j hij u hu u hv).1
    have e : euclidDistR4 u u = 0 := by simp [euclidDistR4, euclidNormVec]
    linarith
section Torus
variable {s : Conventions.StandingParameters}
theorem closedWrapBall_eq_closedBallTorus (hc : CellsInput) (x : s.Torus) {r : ℝ} (hr : 0 < r)
    (hrl : r < PeriodicLattice.torusSide s.L s.m / 2) :
    closedWrapBall x r = closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m) x r := by
  obtain ⟨-, -, -, -, -, h⟩ := (hc s).2.1 x r hr
  exact h hrl
theorem memQuadsTorusIff_holds (hg : GeometryInput) (hc : CellsInput) {d ϑ : ℝ} (hd : 0 < d)
    (hϑ : ϑ ∈ Ioc (0 : ℝ) 1) (h40 : 40 * d ≤ PeriodicLattice.torusSide s.L s.m) :
    MemQuadsTorusIff s d ϑ := by
  have hdl : d < PeriodicLattice.torusSide s.L s.m / 2 := by linarith
  intro f hlip
  constructor
  · intro hf
    obtain ⟨hne, hx, hdist⟩ := (hg.2 s d ϑ hd hϑ h40 f hf).1
    choose x hx using hx
    refine ⟨hne, x, fun i => ?_, hdist⟩
    obtain ⟨-, -, -, -, h1, h2, h3⟩ := hx i
    have h1' : torusTSupport (f i) ⊆ closedWrapBall (x i) d := h1
    rw [closedWrapBall_eq_closedBallTorus hc (x i) hd hdl] at h1'
    exact ⟨h1', h2, h3⟩
  · rintro ⟨hne, x, hx, hdist⟩
    refine ⟨⟨hd, hϑ⟩, h40, hlip,
      fun i j hij => ⟨x i, x j, ?_, ?_, (hdist i j hij).1, (hdist i j hij).2⟩⟩
    · exact ⟨(hlip i).1, (hlip i).2, hne i, (hx i).1, (hx i).2.1, (hx i).2.2⟩
    · exact ⟨(hlip j).1, (hlip j).2, hne j, (hx j).1, (hx j).2.1, (hx j).2.2⟩
theorem witnessGeometryTorus_holds (hg : GeometryInput) (hc : CellsInput)
    {d ϑ : ℝ} (hd : 0 < d) (hϑ : ϑ ∈ Ioc (0 : ℝ) 1)
    (h40 : 40 * d ≤ PeriodicLattice.torusSide s.L s.m) :
    WitnessGeometryTorus s d ϑ := by
  have hdl : d < PeriodicLattice.torusSide s.L s.m / 2 := by linarith
  intro f hf x hx
  obtain ⟨hdist, -, hone⟩ := (hg.2 s d ϑ hd hϑ h40 f hf).2.1
  obtain ⟨-, -, hlip, -⟩ := hf
  have hfirst : torusTSupport (f 0) ⊆ closedWrapBall (x 0) d := by
    rw [closedWrapBall_eq_closedBallTorus hc (x 0) hd hdl]
    exact (hx.1 0).1
  have hsub : ∀ i, torusTSupport (f i) ⊆
      closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (x 0) (9 * d) :=
    hone (x 0) ⟨hd, hϑ, (hlip 0).1, (hlip 0).2, hfirst, (hx.1 0).2.1, (hx.1 0).2.2⟩
  refine ⟨fun i j hij => ?_, hdist, hsub, fun i => ?_, fun i j hij => ?_⟩
  · exact dist_le_eight_mul_of_iInf_le pointDist (fun a b => ((hc s).1.1 b a a).1)
      (fun a b c => ((hc s).1.1 a b c).2) hd
      (fun u hu => (hx.1 i).1 hu) (fun v hv => (hx.1 j).1 hv) (hx.2 i j hij).2
  · have : Fact (0 < PeriodicLattice.torusSide s.L s.m) := ⟨by linarith⟩
    exact (isClosed_tsupport _).isCompact
  · refine Set.disjoint_left.2 fun u hu hv => ?_
    have h := (hdist i j hij u hu u hv).1
    have e : pointDist u u ≤ 0 := by
      have h0 := (hc s).1.2 0
      have e0 : proj s 0 = 0 := by
        funext μ
        simp [proj, torusProj]
      have e1 : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by simp [euclidNormVec]
      rw [e0, e1] at h0
      have e2 : pointDist u u = pointNorm (0 : s.Torus) := by
        unfold pointDist pointNorm euclidDistTorus
        rw [sub_self]
      rw [e2]
      exact h0
    linarith
theorem torusLiftFacts_holds (hg : GeometryInput) (hc : CellsInput) (hm : CoveringInput)
    (hw : RingsInput) {d ϑ : ℝ} (hd : 0 < d) (hϑ : ϑ ∈ Ioc (0 : ℝ) 1)
    (h40 : 40 * d ≤ PeriodicLattice.torusSide s.L s.m) :
    TorusLiftFacts s d ϑ := by
  intro f hf
  have hrad : IsAdmissibleRadius s.L s.m (9 * d) := ⟨by positivity, by linarith⟩
  obtain ⟨-, -, ⟨-, himg⟩, hlifts, -⟩ := hg.2 s d ϑ hd hϑ h40 f hf
  obtain ⟨-, -, -, hL, hper, -, hsurj, -, -, -⟩ := (hm s).1
  obtain ⟨-, -, htwo, hwords⟩ := hw.2.2.2.2.2 s
  obtain ⟨-, hlifteq, -, -, hsupeq, -⟩ := hwords
  have himage : ∀ c, proj s '' closedBallR4 c (9 * d) =
      closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (proj s c) (9 * d) :=
    fun c => himg _ c ((hL _ _).2 rfl)
  have hmemlift : ∀ c, c ∈ PeriodicLattice.liftsOf (proj s c) :=
    fun c => (hlifteq _ _).1 ((hL _ _).2 rfl)
  have hpts := witnessGeometryTorus_holds hg hc hd hϑ h40 f hf
  have h1 : ∀ x, HasWitnessPointsTorus d ϑ f x → ∀ c, proj s c = x 0 →
      ∀ i, torusTSupport (f i) ⊆ proj s '' closedBallR4 c (9 * d) := by
    intro x hx c hcx i
    rw [himage, hcx]
    exact (hpts x hx).2.2.1 i
  have hlie : ∀ (z : s.Torus),
      (∀ i, torusTSupport (f i) ⊆ closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m) z (9 * d)) →
      SupportsInBall (L := s.L) (m := s.m) z (9 * d) f := by
    intro z hz
    refine ⟨hrad, fun i => ?_⟩
    rw [← hsupeq (f i)]
    exact hz i
  have h2 : ∀ c, (∀ i, torusTSupport (f i) ⊆ proj s '' closedBallR4 c (9 * d)) →
      BallLiftProperties s d ϑ f c := by
    intro c hcs
    have hsub : ∀ i, torusTSupport (f i) ⊆
        closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (proj s c) (9 * d) := by
      intro i
      rw [← himage]
      exact hcs i
    obtain ⟨-, hq, hag⟩ := hlifts (proj s c) c hsub (himage c)
    have hsl := hlie _ hsub
    refine ⟨himage c, ⟨hrad, c, hmemlift c, rfl⟩, hsl, fun i => ⟨hrad, hmemlift c, hsl.2 i, rfl⟩,
      ⟨hf, c, hcs, fun i => rfl⟩, hq, fun i => ?_⟩
    obtain ⟨e1, e2, e3, -, e5, -⟩ := hag i
    exact ⟨e1, e2, e5, e3⟩
  have h3 : ∀ g, IsTupleLift (L := s.L) (m := s.m) f g →
      ∃ c, (∀ i, torusTSupport (f i) ⊆ proj s '' closedBallR4 c (9 * d)) ∧
        g = quadLift s d c f := by
    rintro g ⟨z, ρ, hz, c', hc', hgc⟩
    obtain ⟨-, x, hx⟩ := (memQuadsTorusIff_holds hg hc hd hϑ h40 f hf.2.2.1).1 hf
    obtain ⟨c₁, hc₁⟩ := hsurj (x 0)
    have hs₁ := hlie (x 0) (hpts x hx).2.2.1
    have hc₁l : c₁ ∈ PeriodicLattice.liftsOf (x 0) := (hlifteq _ _).1 ((hL _ _).2 hc₁)
    obtain ⟨⟨k, hk⟩, -⟩ := htwo 4 (by norm_num) f (x 0) z (9 * d) ρ hs₁ hz c₁ hc₁l c' hc'
    have hcov : ∀ y : Fin 4 → ℝ,
        proj s (y + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) = proj s y := fun y =>
      (hL _ _).1 ((hper _ y ((hL _ _).2 rfl) _).2 ⟨k, rfl⟩)
    refine ⟨c₁ + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k, h1 x hx _ ?_, ?_⟩
    · rw [hcov, hc₁]
    · funext i y
      rw [hgc i, hk i]
      have eq : (fun α => y α - PeriodicLattice.torusSide s.L s.m * (k α : ℝ)) =
          y - latticeTranslate (PeriodicLattice.torusSide s.L s.m) k := rfl
      have hvec : y - latticeTranslate (PeriodicLattice.torusSide s.L s.m) k - c₁ =
          y - (c₁ + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) := by
        funext α
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      have hmem : y - latticeTranslate (PeriodicLattice.torusSide s.L s.m) k ∈ closedBallR4 c₁ (9 * d) ↔
          y ∈ closedBallR4 (c₁ + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) (9 * d) := by
        show euclidNormVec _ ≤ _ ↔ euclidNormVec _ ≤ _
        rw [hvec]
      have hback : proj s (y - latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) = proj s y := by
        have := hcov (y - latticeTranslate (PeriodicLattice.torusSide s.L s.m) k)
        rw [sub_add_cancel] at this
        exact this.symm
      show (closedBallR4 c₁ (9 * d)).indicator (f i ∘ torusProj (PeriodicLattice.torusSide s.L s.m))
          (fun α => y α - PeriodicLattice.torusSide s.L s.m * (k α : ℝ)) =
        (closedBallR4 (c₁ + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) (9 * d)).indicator
          (f i ∘ proj s) y
      rw [eq]
      by_cases hy : y ∈ closedBallR4 (c₁ + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) (9 * d)
      · rw [Set.indicator_of_mem (hmem.2 hy), Set.indicator_of_mem hy]
        exact congrArg (f i) hback
      · rw [Set.indicator_of_notMem (fun h => hy (hmem.1 h)), Set.indicator_of_notMem hy]
  refine ⟨h1, h2, h3, fun g => ⟨fun hg' => ?_, fun hg' => ?_⟩⟩
  · obtain ⟨c, hcs, e⟩ := h3 g hg'
    exact ⟨hf, c, hcs, fun i => by rw [e]; rfl⟩
  · obtain ⟨-, c, hcs, e⟩ := hg'
    exact ⟨proj s c, 9 * d, (h2 c hcs).2.2.1, c, hmemlift c, e⟩
end Torus
theorem statement_holds (hg : QuadrupleGeometryStatement)
    (hc : TorusMeasure.TranslatedLatticeCells.CellsAndBallsStatement)
    (hm : TorusCovering.CoveringIntegralVolumeStatement)
    (hw : FreeRingKernels.RingIntegrals.Statement) : Statement := by
  refine ⟨fun d ϑ hd hϑ => ⟨memQuadsR4Iff_holds hg hd hϑ, witnessGeometryR4_holds hg hd hϑ⟩,
    fun s d ϑ hd hϑ h40 => ⟨memQuadsTorusIff_holds hg hc hd hϑ h40,
      witnessGeometryTorus_holds hg hc hd hϑ h40, by linarith, torusLiftFacts_holds hg hc hm hw hd hϑ h40⟩⟩
end QuadrupleGeometry
end YangMills.Construction
