import YangMills.Construction.Torus.GeometryOfASeparatedQuadrupleProof
import YangMills.Construction.Torus.OneBallLiftAndTransportOfQuadruples
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions YangMills.Construction.TorusMeasure YangMills.Construction.PlaquetteSupports YangMills.Construction.QuadrupleClasses YangMills.Construction.QuadrupleGeometry
open YangMills.Construction.TorusMeasure.BallProjection
noncomputable section
namespace YangMills.Construction.QuadrupleBalls
theorem dist_centers_le_of_infDist_le {Y : Type*} (D : Y → Y → ℝ) (hsymm : ∀ a b, D a b = D b a)
    (htri : ∀ a b c, D a b ≤ D a c + D c b) {d : ℝ} (hd : 0 < d) {A B : Set Y} {x y : Y}
    (hA : ∀ u ∈ A, D u x ≤ d) (hB : ∀ v ∈ B, D v y ≤ d)
    (hgap : (⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (D a b)) ≤ ENNReal.ofReal (6 * d)) :
    D x y ≤ 8 * d := by
  have hclose : ∀ ε, 0 < ε → ∃ a ∈ A, ∃ b ∈ B, D a b ≤ 6 * d + ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hle : ENNReal.ofReal (6 * d + ε) ≤ ⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (D a b) :=
      le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal (hcon a ha b hb).le
    rcases ENNReal.ofReal_le_ofReal_iff'.1 (hle.trans hgap) with hle | hle <;> linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, b, hb, hab⟩ := hclose ε hε
  have t1 := htri x y a
  have t2 := htri a y b
  have t3 := hA a ha
  have t4 := hB b hb
  rw [hsymm x a] at t1
  linarith
theorem centers_and_supports_le_of_pairwise {Y : Type*} (D : Y → Y → ℝ)
    (hsymm : ∀ a b, D a b = D b a)
    (htri : ∀ a b c, D a b ≤ D a c + D c b) {d : ℝ} (hd : 0 < d) (S : Fin 4 → Set Y)
    (hne : ∀ i, (S i).Nonempty)
    (hgap : ∀ i j, i ≠ j →
      (⨅ a ∈ S i, ⨅ b ∈ S j, ENNReal.ofReal (D a b)) ≤ ENNReal.ofReal (6 * d))
    (x : Fin 4 → Y) (hx : ∀ i, ∀ u ∈ S i, D u (x i) ≤ d) :
    (∀ i, D (x i) (x 0) ≤ 8 * d) ∧ ∀ i, ∀ u ∈ S i, D u (x 0) ≤ 9 * d := by
  have h8 : ∀ i, D (x i) (x 0) ≤ 8 * d := by
    intro i
    by_cases hi : i = 0
    · rw [hi]
      obtain ⟨u, hu⟩ := hne 0
      have t1 := htri (x 0) (x 0) u
      have t2 := hx 0 u hu
      rw [hsymm (x 0) u] at t1
      linarith
    · exact dist_centers_le_of_infDist_le D hsymm htri hd (hx i) (hx 0) (hgap i 0 hi)
  refine ⟨h8, fun i u hu => ?_⟩
  have t1 := htri u (x 0) (x i)
  have t2 := hx i u hu
  have t3 := h8 i
  linarith
theorem euclidDistR4_comm (a b : Fin 4 → ℝ) : euclidDistR4 a b = euclidDistR4 b a := by apply _root_.YangMills.Construction.QuadrupleGeometry.euclidDistR4_symm <;> assumption
theorem euclidDistR4_triangle (a b c : Fin 4 → ℝ) :
    euclidDistR4 a b ≤ euclidDistR4 a c + euclidDistR4 c b := by apply _root_.YangMills.Construction.QuadrupleGeometry.euclidDistR4_le_add <;> assumption
theorem oneBallPropertyR4_of_supportGaps {d ϑ : ℝ} (hd : 0 < d) {f : Fin 4 → (Fin 4 → ℝ) → ℝ}
    (hgaps : SupportGapsR4 d ϑ f) : OneBallPropertyR4 d f := by
  obtain ⟨hne, hcen, hdist⟩ := hgaps
  refine ⟨hne, ?_, fun x hx => ⟨hdist, ?_⟩⟩
  · choose x hx using hcen
    exact ⟨x, fun i => (hx i).2.2.2.2.1⟩
  · have hb := centers_and_supports_le_of_pairwise euclidDistR4 euclidDistR4_comm
      euclidDistR4_triangle hd
      (fun i => euclideanTSupport (f i))
      (fun i => by
        obtain ⟨t, ht⟩ := hne i
        exact ⟨t, subset_tsupport _ ht⟩)
      (fun i j hij => (hdist i j hij).2) x (fun i u hu => hx i hu)
    exact ⟨hb.1, fun i u hu => hb.2 i u hu⟩
theorem sub_mem_tsupport_of_translate {g g' : (Fin 4 → ℝ) → ℝ} {w : Fin 4 → ℝ}
    (hshift : ∀ t, g' t = g (t - w)) {u : Fin 4 → ℝ} (hu : u ∈ euclideanTSupport g') :
    u - w ∈ euclideanTSupport g := by
  have hsupp : Function.support g' = (Homeomorph.addRight (-w)) ⁻¹' Function.support g := by
    ext t
    simp [Function.mem_support, hshift, sub_eq_add_neg]
  have hu' : u ∈ closure (Function.support g') := hu
  rw [hsupp, ← Homeomorph.preimage_closure] at hu'
  rw [sub_eq_add_neg]
  exact hu'
theorem mem_shapeQuadsR4_of_translate {d ϑ : ℝ} {g g' : Fin 4 → (Fin 4 → ℝ) → ℝ} (w : Fin 4 → ℝ)
    (hg : g ∈ shapeQuadsR4 d ϑ) (hq : g' ∈ quadsR4 d ϑ)
    (hshift : ∀ i t, g' i t = g i (t - w)) : g' ∈ shapeQuadsR4 d ϑ := by
  obtain ⟨-, -, e, he, hdir⟩ := hg
  refine ⟨hq, hq, e, he, fun i j hij u hu v hv => ?_⟩
  have hkey := hdir i j hij (u - w) (sub_mem_tsupport_of_translate (hshift i) hu) (v - w)
    (sub_mem_tsupport_of_translate (hshift j) hv)
  rwa [sub_sub_sub_cancel_right] at hkey
theorem mem_collinearQuadsR4_of_translate {d ϑ : ℝ} {g g' : Fin 4 → (Fin 4 → ℝ) → ℝ}
    (w : Fin 4 → ℝ)
    (hg : g ∈ collinearQuadsR4 d ϑ) (hq : g' ∈ quadsR4 d ϑ)
    (hshift : ∀ i t, g' i t = g i (t - w)) : g' ∈ collinearQuadsR4 d ϑ := by
  obtain ⟨-, c, ⟨e, he, hline⟩, hc⟩ := hg
  refine ⟨hq, fun i => c i + w, ⟨e, he, fun i j => ?_⟩, fun i u hu => ?_⟩
  · show c i + w - (c j + w) ∈ realLine e
    rw [add_sub_add_right_eq_sub]
    exact hline i j
  · have h1 : euclidNormVec ((u - w) - c i) ≤ d / 16 :=
      hc i (sub_mem_tsupport_of_translate (hshift i) hu)
    have e1 : u - (c i + w) = (u - w) - c i := by abel
    show euclidNormVec (u - (c i + w)) ≤ d / 16
    rw [e1]
    exact h1
section Torus
variable {s : YangMills.Construction.Conventions.StandingParameters}
theorem isLift_proj (t : Fin 4 → ℝ) : IsLift s (proj s t) t := by apply _root_.YangMills.Construction.QuadrupleGeometry.isLift_proj <;> assumption
theorem oneBallPropertyTorus_of_supportGaps
    (hcells : YangMills.Construction.TorusMeasure.TranslatedLatticeCells.CellsAndBallsStatement)
    {d ϑ : ℝ} (hd : 0 < d)
    {f : Fin 4 → s.Torus → ℝ} (hgaps : SupportGapsTorus d ϑ f) : OneBallPropertyTorus d f := by
  obtain ⟨hne, hcen, hdist⟩ := hgaps
  refine ⟨hne, ?_, fun x hx => ⟨hdist, ?_⟩⟩
  · choose x hx using hcen
    exact ⟨x, fun i => (hx i).2.2.2.2.1⟩
  · have hb := centers_and_supports_le_of_pairwise (pointDist (s := s))
      (fun a b => ((hcells s).1.1 b a a).1)
      (fun a b c => ((hcells s).1.1 a b c).2) hd (fun i => torusTSupport (f i))
      (fun i => by
        obtain ⟨t, ht⟩ := hne i
        exact ⟨t, subset_tsupport _ ht⟩)
      (fun i j hij => (hdist i j hij).2) x (fun i u hu => hx i hu)
    exact ⟨hb.1, fun i u hu => hb.2 i u hu⟩
theorem mem_quadsR4_of_isBallLift {d ϑ : ℝ} {f : Fin 4 → s.Torus → ℝ}
    (himages : BallImagesCover s d)
    (hlifts : LiftsOverBall d ϑ f) {g : Fin 4 → (Fin 4 → ℝ) → ℝ}
    (hg : IsBallLift s d ϑ f g) : g ∈ quadsR4 d ϑ := by
  obtain ⟨-, c, hsub, hgc⟩ := hg
  have himg := himages.2 (proj s c) c (isLift_proj c)
  have hmem := (hlifts (proj s c) c (fun i => by rw [← himg]; exact hsub i) himg).2.1
  have hfun : g = fun i => liftOverBall c d (f i) := funext hgc
  rw [hfun]
  exact hmem
theorem isDeterminedByLifts_of_translate {d ϑ : ℝ} {f : Fin 4 → s.Torus → ℝ}
    {A : Set (Fin 4 → s.Torus → ℝ)}
    {B : Set (Fin 4 → (Fin 4 → ℝ) → ℝ)}
    (hA : f ∈ A ↔ ∃ g, IsBallLift s d ϑ f g ∧ g ∈ B)
    (hinv : ∀ (g g' : Fin 4 → (Fin 4 → ℝ) → ℝ) (w : Fin 4 → ℝ), g ∈ B →
      g' ∈ quadsR4 d ϑ → (∀ i t, g' i t = g i (t - w)) → g' ∈ B)
    (hone : ∃ g, IsBallLift s d ϑ f g)
    (hmem : ∀ g, IsBallLift s d ϑ f g → g ∈ quadsR4 d ϑ)
    (hperiod : LiftsDifferByPeriod d ϑ f) : IsDeterminedByLifts d ϑ f A B := by
  refine ⟨hA, fun hfA g hg => ?_, fun hall => ?_⟩
  · obtain ⟨g₀, hg₀, hB⟩ := hA.1 hfA
    obtain ⟨k, hk⟩ := hperiod g₀ g hg₀ hg
    exact hinv g₀ g _ hB (hmem g hg) hk
  · obtain ⟨g, hg⟩ := hone
    exact hA.2 ⟨g, hg, hall g hg⟩
theorem propertiesTorus_holds (hgeom : QuadrupleGeometryStatement)
    (hcells : YangMills.Construction.TorusMeasure.TranslatedLatticeCells.CellsAndBallsStatement)
    {d ϑ : ℝ} (hd : 0 < d) (hϑ : ϑ ∈ Ioc (0 : ℝ) 1)
    (h40 : 40 * d ≤ YangMills.Construction.PeriodicLattice.torusSide s.L s.m) :
    PropertiesTorus s d ϑ := by
  refine ⟨fun f hf => hf.1, by linarith, fun f hf => ?_⟩
  obtain ⟨hgaps, -, himages, hlifts, hperiod⟩ := hgeom.2 s d ϑ hd hϑ h40 f hf
  have hball := oneBallPropertyTorus_of_supportGaps hcells hd hgaps
  have hover : BallLiftProperty d ϑ f := by
    intro x c hx hcov
    have hsup := (hball.2.2 x hx).2.2
    have himg : proj s '' closedBallR4 c (9 * d) = ballOnTorus (x 0) (9 * d) :=
      himages.2 (x 0) c (hcov ▸ isLift_proj c)
    obtain ⟨hiso, hq, -⟩ := hlifts (x 0) c hsup himg
    exact ⟨hiso, ⟨hf, c, fun i => by rw [himg]; exact hsup i, fun i => rfl⟩, hq⟩
  have hdiff : LiftsDifferByPeriod d ϑ f := by
    rintro g g' ⟨-, c, hB, hg⟩ ⟨-, c', hB', hg'⟩
    obtain ⟨k, hk⟩ := hperiod c c' hB hB'
    refine ⟨k, fun i t => ?_⟩
    have e := hk (t - latticeTranslate (YangMills.Construction.PeriodicLattice.torusSide s.L s.m) k) i
    rw [sub_add_cancel] at e
    rw [hg i, hg' i]
    exact e
  have hone : ∃ g, IsBallLift s d ϑ f g := by
    obtain ⟨x, hx⟩ := hball.2.1
    exact ⟨_, (hover x (liftPoint (ℓ := YangMills.Construction.PeriodicLattice.torusSide s.L s.m)
      (x 0)) hx
      (torusProj_liftPoint (ℓ := YangMills.Construction.PeriodicLattice.torusSide s.L s.m)
        (x 0))).2.1⟩
  have hmem := fun g (hg : IsBallLift s d ϑ f g) => mem_quadsR4_of_isBallLift himages hlifts hg
  refine ⟨hball, hover, hdiff, ?_, ?_⟩
  · refine isDeterminedByLifts_of_translate ⟨?_, ?_⟩
      (fun g g' w hg hq h => mem_shapeQuadsR4_of_translate w hg hq h) hone hmem hdiff
    · rintro ⟨-, g, hg, hsh⟩
      exact ⟨g, hg, hsh.1, hsh⟩
    · rintro ⟨g, hg, hB⟩
      exact ⟨hf, g, hg, hB.2⟩
  · refine isDeterminedByLifts_of_translate ⟨?_, ?_⟩
      (fun g g' w hg hq h => mem_collinearQuadsR4_of_translate w hg hq h) hone hmem hdiff
    · rintro ⟨-, g, hg, hB⟩
      exact ⟨g, hg, hB⟩
    · rintro ⟨g, hg, hB⟩
      exact ⟨hf, g, hg, hB⟩
theorem uniformNorm_pushdown_eq (hproj : BallProjectionStatement)
    (hcells : YangMills.Construction.TorusMeasure.TranslatedLatticeCells.CellsAndBallsStatement)
    {R : ℝ} {c : Fin 4 → ℝ} (hR : 0 < R)
    (hRl : R ≤ YangMills.Construction.PeriodicLattice.torusSide s.L s.m / 4)
    {g : (Fin 4 → ℝ) → ℝ} {h : s.Torus → ℝ}
    (hdown : IsPushdown s c R g h) (hg : IsLipschitzFor euclidDistR4 g) :
    uniformNorm h = uniformNorm g := by
  obtain ⟨-, ⟨hbij, -⟩, -, hfun⟩ := hproj s R c hR hRl
  obtain ⟨-, -, hlip, -, -⟩ := hfun g h hdown
  obtain ⟨⟨C, hC⟩, -⟩ := (hcells s).2.2.1 h (hlip.1.2 hg)
  have hgC : ∀ t, ‖g t‖ ≤ max C 0 := by
    intro t
    by_cases ht : t ∈ closedBallR4 c R
    · rw [← hdown.2.1 t ht]
      exact (hC _).trans (le_max_left _ _)
    · rw [hdown.1 t ht, norm_zero]
      exact le_max_right _ _
  have bddh : BddAbove (range fun u => ‖h u‖) := ⟨C, by rintro _ ⟨u, rfl⟩; exact hC u⟩
  have bddg : BddAbove (range fun t => ‖g t‖) := ⟨max C 0, by rintro _ ⟨t, rfl⟩; exact hgC t⟩
  apply le_antisymm
  · refine ciSup_le fun u => ?_
    by_cases hu : u ∈ torusBallOver s c R
    · obtain ⟨t, ht, rfl⟩ := hbij.surjOn hu
      rw [hdown.2.1 t ht]
      exact le_ciSup bddg t
    · rw [hdown.2.2 u hu, norm_zero]
      exact Real.iSup_nonneg fun _ => norm_nonneg _
  · refine ciSup_le fun t => ?_
    by_cases ht : t ∈ closedBallR4 c R
    · rw [← hdown.2.1 t ht]
      exact le_ciSup bddh (proj s t)
    · rw [hdown.1 t ht, norm_zero]
      exact Real.iSup_nonneg fun _ => norm_nonneg _
end Torus
theorem periodizationsMapInto_of_lift (hgeom : QuadrupleGeometryStatement)
    (hproj : BallProjectionStatement)
    (hcells : YangMills.Construction.TorusMeasure.TranslatedLatticeCells.CellsAndBallsStatement)
    {s : YangMills.Construction.Conventions.StandingParameters} {d ϑ : ℝ} (hd : 0 < d)
    (hϑ : ϑ ∈ Ioc (0 : ℝ) 1)
    (h40 : 40 * d ≤ YangMills.Construction.PeriodicLattice.torusSide s.L s.m)
    {B : Set (Fin 4 → (Fin 4 → ℝ) → ℝ)}
    {A : Set (Fin 4 → s.Torus → ℝ)} (hsub : B ⊆ quadsR4 d ϑ)
    (hin : ∀ f ∈ B,
      (fun i => periodize (YangMills.Construction.PeriodicLattice.torusSide s.L s.m) (f i)) ∈
        quadsTorus s d ϑ →
      IsBallLift s d ϑ
        (fun i => periodize (YangMills.Construction.PeriodicLattice.torusSide s.L s.m) (f i)) f →
      (fun i => periodize (YangMills.Construction.PeriodicLattice.torusSide s.L s.m) (f i)) ∈ A) :
    PeriodizationsMapInto s B A := by
  intro f hfB
  have hf := hsub hfB
  obtain ⟨-, ⟨-, ⟨c, hcb⟩, -⟩, hT⟩ := hgeom.1 d ϑ hd hϑ f hf
  obtain ⟨hform, hq⟩ := hT s h40
  have hR : 0 < 9 * d := by positivity
  have hRl : 9 * d ≤ YangMills.Construction.PeriodicLattice.torusSide s.L s.m / 4 := by linarith
  obtain ⟨-, -, hcorr, hfun⟩ := hproj s (9 * d) c hR hRl
  have hvan : ∀ i t, t ∉ closedBallR4 c (9 * d) → f i t = 0 := by
    intro i t ht
    by_contra hne
    exact ht (hcb i (subset_tsupport _ hne))
  have hdown : ∀ i, IsPushdown s c (9 * d) (f i)
      (periodize (YangMills.Construction.PeriodicLattice.torusSide s.L s.m) (f i)) := by
    intro i
    obtain ⟨h, hh, -⟩ := hcorr.1 (f i) (hvan i)
    have e := (hfun _ _ hh).1.2.2.2
    rw [← e]
    exact hh
  have hlift : IsBallLift s d ϑ
      (fun i => periodize (YangMills.Construction.PeriodicLattice.torusSide s.L s.m) (f i)) f := by
    refine ⟨hq, c, fun i => ?_, fun i => ?_⟩
    · exact (hfun _ _ (hdown i)).2.2.2.1.2.2.subset.trans (image_mono (hcb i))
    · funext t
      by_cases ht : t ∈ closedBallR4 c (9 * d)
      · rw [ballLift, indicator_of_mem ht]
        exact ((hdown i).2.1 t ht).symm
      · rw [ballLift, indicator_of_notMem ht]
        exact hvan i t ht
  refine ⟨hform, hin f hfB hq hlift, fun i => ?_⟩
  have hlipf : IsLipschitzFor euclidDistR4 (f i) := by
    obtain ⟨-, hl, -⟩ := hf
    exact (hl i).1
  exact uniformNorm_pushdown_eq hproj hcells hR hRl (hdown i) hlipf
theorem ballLiftPeriodization_holds (hgeom : QuadrupleGeometryStatement)
    (hproj : BallProjectionStatement)
    (hcells : YangMills.Construction.TorusMeasure.TranslatedLatticeCells.CellsAndBallsStatement) :
    BallLiftPeriodizationStatement := by
  intro d ϑ hd hϑ
  refine ⟨⟨fun f hf => hf.1, fun f hf => ?_⟩,
    fun s h40 => ⟨propertiesTorus_holds hgeom hcells hd hϑ h40, ?_, ?_⟩⟩
  · exact oneBallPropertyR4_of_supportGaps hd (hgeom.1 d ϑ hd hϑ f hf).1
  · exact periodizationsMapInto_of_lift hgeom hproj hcells hd hϑ h40 (fun f hf => hf.1)
      fun f hfB hq hl => ⟨hq, f, hl, hfB⟩
  · exact periodizationsMapInto_of_lift hgeom hproj hcells hd hϑ h40 (fun f hf => hf.1)
      fun f hfB hq hl => ⟨hq, f, hl, hfB.2⟩
end YangMills.Construction.QuadrupleBalls
