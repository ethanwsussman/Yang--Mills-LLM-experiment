import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.Torus.CellsOfATranslatedLatticeAndBallsOfTheTorusProof
import YangMills.Construction.Torus.GeometryOfASeparatedQuadruple
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions YangMills.Construction.TorusMeasure YangMills.Construction.PlaquetteSupports YangMills.Construction.QuadrupleClasses
open YangMills.Construction.TorusMeasure.BallProjection
noncomputable section
namespace YangMills.Construction.QuadrupleGeometry
theorem gap_bounds_of_near_sets {Y : Type*} (D : Y → Y → ℝ) (hsymm : ∀ a b, D a b = D b a)
    (htri : ∀ a b c, D a b ≤ D a c + D c b) {d : ℝ} (hd : 0 < d) {A B : Set Y} {x y : Y}
    (hA : ∀ u ∈ A, D u x ≤ d) (hB : ∀ v ∈ B, D v y ≤ d)
    (hlow : ENNReal.ofReal d ≤ ⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (D a b))
    (hhigh : (⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (D a b)) ≤ ENNReal.ofReal (6 * d))
    {u v : Y} (hu : u ∈ A) (hv : v ∈ B) :
    d ≤ D u v ∧ D u v ≤ 10 * d ∧ D v x ≤ 9 * d := by
  have h1 : d ≤ D u v := by
    have h : ENNReal.ofReal d ≤ ENNReal.ofReal (D u v) :=
      hlow.trans ((iInf₂_le u hu).trans (iInf₂_le v hv))
    rcases ENNReal.ofReal_le_ofReal_iff'.1 h with h | h
    · exact h
    · exact absurd h (not_le.2 hd)
  have key : ∀ ε, 0 < ε → ∃ a ∈ A, ∃ b ∈ B, D a b ≤ 6 * d + ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have h : ENNReal.ofReal (6 * d + ε) ≤ ⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (D a b) :=
      le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal (hcon a ha b hb).le
    rcases ENNReal.ofReal_le_ofReal_iff'.1 (h.trans hhigh) with h | h <;> linarith
  refine ⟨h1, ?_, ?_⟩
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨a, ha, b, hb, hab⟩ := key ε hε
    have e1 := htri u v x
    have e2 := htri x v a
    have e3 := htri a v b
    have e4 := htri b v y
    have e5 := hA u hu
    have e6 := hA a ha
    have e7 := hB b hb
    have e8 := hB v hv
    rw [hsymm x a] at e2
    rw [hsymm y v] at e4
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨a, ha, b, hb, hab⟩ := key ε hε
    have e1 := htri v x y
    have e2 := htri y x b
    have e3 := htri b x a
    have e5 := hA a ha
    have e7 := hB b hb
    have e8 := hB v hv
    rw [hsymm y b] at e2
    rw [hsymm b a] at e3
    linarith
theorem euclidNormVec_add_le (u v : Fin 4 → ℝ) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem euclidDistR4_symm (a b : Fin 4 → ℝ) : euclidDistR4 a b = euclidDistR4 b a := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidDistR4_le_add (a b c : Fin 4 → ℝ) :
    euclidDistR4 a b ≤ euclidDistR4 a c + euclidDistR4 c b := by
  unfold euclidDistR4
  have h := euclidNormVec_add_le (a - c) (c - b)
  rwa [sub_add_sub_cancel] at h
theorem abs_coord_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem continuous_of_isLipschitzFor {g : (Fin 4 → ℝ) → ℝ} (hg : IsLipschitzFor euclidDistR4 g) :
    Continuous g := by apply _root_.YangMills.Construction.TestPairs.continuous_of_isLipschitzFor_r4 <;> assumption
theorem eq_zero_of_latticeTranslate_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ}
    (h : euclidNormVec (latticeTranslate ℓ k) < ℓ) : k = 0 := by
  funext μ
  have h1 := abs_coord_le_euclidNormVec (latticeTranslate ℓ k) μ
  have h2 : |latticeTranslate ℓ k μ| = ℓ * |(k μ : ℝ)| := by
    simp [latticeTranslate, abs_mul, abs_of_pos hℓ]
  have h3 : ℓ * |(k μ : ℝ)| < ℓ * 1 := by
    rw [mul_one, ← h2]
    exact h1.trans_lt h
  have h4 : |(k μ : ℝ)| < 1 := lt_of_mul_lt_mul_left h3 hℓ.le
  have h5 : |k μ| < 1 := by exact_mod_cast h4
  simpa using Int.abs_lt_one_iff.1 h5
section Periodic
variable {s : Conventions.StandingParameters}
theorem torusSide_pos (s : Conventions.StandingParameters) :
    0 < PeriodicLattice.torusSide s.L s.m := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.torusSide_pos <;> assumption
theorem proj_sub (a b : Fin 4 → ℝ) :
    proj s (a - b) = proj s a - proj s b := by apply _root_.YangMills.Construction.TorusMeasure.BallProjection.proj_map_sub <;> assumption
theorem isLift_proj (t : Fin 4 → ℝ) : IsLift s (proj s t) t := by
  refine ⟨t, fun μ => rfl, fun μ => ?_⟩
  simp [PeriodicLattice.toLevelUnits, PeriodicLattice.levelDepth]
theorem pointDist_comm (hc : TranslatedLatticeCells.CellsAndBallsStatement) (a b : s.Torus) :
    pointDist a b = pointDist b a :=
  ((hc s).1.1 b a a).1
theorem pointDist_triangle (hc : TranslatedLatticeCells.CellsAndBallsStatement) (a b c : s.Torus) :
    pointDist a b ≤ pointDist a c + pointDist c b :=
  ((hc s).1.1 a b c).2
theorem setDist_image_eq {Ball A B : Set (Fin 4 → ℝ)}
    (hdist : ∀ t ∈ Ball, ∀ t' ∈ Ball,
      pointDist (proj s t) (proj s t') = euclidDistR4 t t')
    (hA : A ⊆ Ball) (hB : B ⊆ Ball) :
    setDist (proj s '' A) (proj s '' B) = setDistR4 A B := by
  unfold setDist setEuclidDist setDistR4
  rw [iInf_image]
  refine iInf_congr fun a => iInf_congr fun ha => ?_
  rw [iInf_image]
  refine iInf_congr fun b => iInf_congr fun hb => ?_
  congr 1
  exact hdist a (hA ha) b (hB hb)
theorem pushdown_invariants (hb : BallProjectionStatement)
    (hc : TranslatedLatticeCells.CellsAndBallsStatement) {R : ℝ} {c : Fin 4 → ℝ} (hR : 0 < R)
    (hRl : R ≤ PeriodicLattice.torusSide s.L s.m / 4) {g : (Fin 4 → ℝ) → ℝ} {h : s.Torus → ℝ}
    (hdown : IsPushdown s c R g h) (hg : IsLipschitzFor euclidDistR4 g) :
    IsLipschitzFor (euclidDistTorus (ℓ := PeriodicLattice.torusSide s.L s.m)) h ∧
      uniformNorm g = uniformNorm h ∧
      lipConstR4 g = lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) h ∧
      integralR4 g = torusIntegral h := by
  obtain ⟨-, ⟨hbij, -⟩, -, hfun⟩ := hb s R c hR hRl
  obtain ⟨-, -, hlip, -, hint⟩ := hfun g h hdown
  have hLh := hlip.1.2 hg
  obtain ⟨⟨C, hC⟩, -⟩ := (hc s).2.2.1 h hLh
  have hgC : ∀ t, ‖g t‖ ≤ max C 0 := by
    intro t
    by_cases ht : t ∈ closedBallR4 c R
    · rw [← hdown.2.1 t ht]
      exact (hC _).trans (le_max_left _ _)
    · rw [hdown.1 t ht, norm_zero]
      exact le_max_right _ _
  have bddh : BddAbove (range fun u => ‖h u‖) := ⟨C, by rintro _ ⟨u, rfl⟩; exact hC u⟩
  have bddg : BddAbove (range fun t => ‖g t‖) := ⟨max C 0, by rintro _ ⟨t, rfl⟩; exact hgC t⟩
  have hsup : uniformNorm g = uniformNorm h := by
    apply le_antisymm
    · refine ciSup_le fun t => ?_
      by_cases ht : t ∈ closedBallR4 c R
      · rw [← hdown.2.1 t ht]
        exact le_ciSup bddh (proj s t)
      · rw [hdown.1 t ht, norm_zero]
        exact Real.iSup_nonneg fun _ => norm_nonneg _
    · refine ciSup_le fun u => ?_
      by_cases hu : u ∈ torusBallOver s c R
      · obtain ⟨t, ht, rfl⟩ := hbij.surjOn hu
        rw [hdown.2.1 t ht]
        exact le_ciSup bddg t
      · rw [hdown.2.2 u hu, norm_zero]
        exact Real.iSup_nonneg fun _ => norm_nonneg _
  have hmeas : IsNullMeasurableFunR4 g :=
    (continuous_of_isLipschitzFor hg).measurable.nullMeasurable
  exact ⟨hLh, hsup, (hlip.2 hg).symm, (hint ⟨_, hgC⟩ hmeas).2.2.symm⟩
abbrev IsTorusBump (s : Conventions.StandingParameters) (d ϑ : ℝ) (x : s.Torus)
    (g : s.Torus → ℝ) : Prop :=
  IsShapedBump (Y := s.Torus) (euclidDistTorus (ℓ := PeriodicLattice.torusSide s.L s.m))
    (closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m)) (torusIntegral (s := s)) d ϑ x g
abbrev IsR4Bump (d ϑ : ℝ) (x : Fin 4 → ℝ) (g : (Fin 4 → ℝ) → ℝ) : Prop :=
  IsShapedBump euclidDistR4 closedBallR4 integralR4 d ϑ x g
theorem pair_of_mem_quadsTorus {d ϑ : ℝ} {f : Fin 4 → s.Torus → ℝ} (hf : f ∈ quadsTorus s d ϑ)
    {i j : Fin 4} (hij : i ≠ j) :
    ∃ x y, IsTorusBump s d ϑ x (f i) ∧ IsTorusBump s d ϑ y (f j) ∧
      ENNReal.ofReal d ≤ setDist (torusTSupport (f i)) (torusTSupport (f j)) ∧
      setDist (torusTSupport (f i)) (torusTSupport (f j)) ≤ ENNReal.ofReal (6 * d) := by
  obtain ⟨-, -, -, hp⟩ := hf
  exact hp i j hij
theorem pair_of_mem_quadsR4 {d ϑ : ℝ} {f : Fin 4 → (Fin 4 → ℝ) → ℝ} (hf : f ∈ quadsR4 d ϑ)
    {i j : Fin 4} (hij : i ≠ j) :
    ∃ x y, IsR4Bump d ϑ x (f i) ∧ IsR4Bump d ϑ y (f j) ∧
      ENNReal.ofReal d ≤ setDistR4 (euclideanTSupport (f i)) (euclideanTSupport (f j)) ∧
      setDistR4 (euclideanTSupport (f i)) (euclideanTSupport (f j)) ≤ ENNReal.ofReal (6 * d) := by
  obtain ⟨-, -, hp⟩ := hf
  exact hp i j hij
theorem exists_isTorusBump {d ϑ : ℝ} {f : Fin 4 → s.Torus → ℝ} (hf : f ∈ quadsTorus s d ϑ)
    (i : Fin 4) : ∃ x, IsTorusBump s d ϑ x (f i) := by
  obtain ⟨j, hj⟩ := exists_ne i
  obtain ⟨x, -, hx, -⟩ := pair_of_mem_quadsTorus hf hj.symm
  exact ⟨x, hx⟩
theorem exists_isR4Bump {d ϑ : ℝ} {f : Fin 4 → (Fin 4 → ℝ) → ℝ} (hf : f ∈ quadsR4 d ϑ)
    (i : Fin 4) : ∃ x, IsR4Bump d ϑ x (f i) := by
  obtain ⟨j, hj⟩ := exists_ne i
  obtain ⟨x, -, hx, -⟩ := pair_of_mem_quadsR4 hf hj.symm
  exact ⟨x, hx⟩
theorem supportGapsTorus_of_mem {d ϑ : ℝ} (hd : 0 < d) (hϑ : ϑ ∈ Ioc (0 : ℝ) 1)
    {f : Fin 4 → s.Torus → ℝ} (hf : f ∈ quadsTorus s d ϑ) :
    SupportGapsTorus d ϑ f := by
  refine ⟨fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨x, -, -, h, -⟩ := exists_isTorusBump hf i
    exact h
  · obtain ⟨x, h1, h2, -, h4, h5, h6⟩ := exists_isTorusBump hf i
    exact ⟨x, hd, hϑ, h1, h2, h4, h5, h6⟩
  · obtain ⟨x, y, -, -, h1, h2⟩ := pair_of_mem_quadsTorus hf hij
    exact ⟨h1, h2⟩
theorem supportGapsR4_of_mem {d ϑ : ℝ} (hd : 0 < d) (hϑ : ϑ ∈ Ioc (0 : ℝ) 1)
    {f : Fin 4 → (Fin 4 → ℝ) → ℝ} (hf : f ∈ quadsR4 d ϑ) :
    SupportGapsR4 d ϑ f := by
  refine ⟨fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨x, -, -, h, -⟩ := exists_isR4Bump hf i
    exact h
  · obtain ⟨x, h1, h2, -, h4, h5, h6⟩ := exists_isR4Bump hf i
    exact ⟨x, hd, hϑ, h1, h2, h4, h5, h6⟩
  · obtain ⟨x, y, -, -, h1, h2⟩ := pair_of_mem_quadsR4 hf hij
    exact ⟨h1, h2⟩
theorem pointGapsAndBallTorus_of_mem (hc : TranslatedLatticeCells.CellsAndBallsStatement)
    {d ϑ : ℝ} (hd : 0 < d) {f : Fin 4 → s.Torus → ℝ} (hf : f ∈ quadsTorus s d ϑ) :
    PointGapsAndBallTorus d ϑ f := by
  have main : ∀ {i j : Fin 4}, i ≠ j → ∀ x : s.Torus, torusTSupport (f i) ⊆ ballOnTorus x d →
      ∀ u ∈ torusTSupport (f i), ∀ v ∈ torusTSupport (f j),
        d ≤ pointDist u v ∧ pointDist u v ≤ 10 * d ∧ pointDist v x ≤ 9 * d := by
    intro i j hij x hx u hu v hv
    obtain ⟨-, y, -, ⟨-, -, -, hy, -⟩, h1, h2⟩ := pair_of_mem_quadsTorus hf hij
    exact gap_bounds_of_near_sets pointDist (pointDist_comm hc) (pointDist_triangle hc) hd
      (fun _ h => hx h) (fun _ h => hy h) h1 h2 hu hv
  have third : ∀ x : s.Torus, torusTSupport (f 0) ⊆ ballOnTorus x d →
      ∀ i, torusTSupport (f i) ⊆ ballOnTorus x (9 * d) := by
    intro x hx i
    by_cases hi : i = 0
    · subst hi
      intro u hu
      have h1 : pointDist u x ≤ d := hx hu
      exact show pointDist u x ≤ 9 * d from by linarith
    · obtain ⟨-, -, -, ⟨u₀, hu₀⟩, -⟩ := exists_isTorusBump hf 0
      intro v hv
      exact (main (Ne.symm hi) x hx u₀ (subset_tsupport _ hu₀) v hv).2.2
  refine ⟨fun i j hij u hu v hv => ?_, ?_, ?_⟩
  · obtain ⟨x, -, -, -, hx, -⟩ := exists_isTorusBump hf i
    have h := main hij x hx u hu v hv
    exact ⟨h.1, h.2.1⟩
  · obtain ⟨x, -, -, -, hx, -⟩ := exists_isTorusBump hf 0
    exact ⟨x, third x hx⟩
  · intro x₁ h₁
    obtain ⟨-, -, -, -, hx, -⟩ := h₁
    exact third x₁ hx
theorem pointGapsAndBallR4_of_mem {d ϑ : ℝ} (hd : 0 < d)
    {f : Fin 4 → (Fin 4 → ℝ) → ℝ} (hf : f ∈ quadsR4 d ϑ) :
    PointGapsAndBallR4 d ϑ f := by
  have main : ∀ {i j : Fin 4}, i ≠ j → ∀ x : Fin 4 → ℝ, euclideanTSupport (f i) ⊆ closedBallR4 x d →
      ∀ u ∈ euclideanTSupport (f i), ∀ v ∈ euclideanTSupport (f j),
        d ≤ euclidDistR4 u v ∧ euclidDistR4 u v ≤ 10 * d ∧ euclidDistR4 v x ≤ 9 * d := by
    intro i j hij x hx u hu v hv
    obtain ⟨-, y, -, ⟨-, -, -, hy, -⟩, h1, h2⟩ := pair_of_mem_quadsR4 hf hij
    exact gap_bounds_of_near_sets euclidDistR4 euclidDistR4_symm euclidDistR4_le_add hd
      (fun _ h => hx h) (fun _ h => hy h) h1 h2 hu hv
  have third : ∀ x : Fin 4 → ℝ, euclideanTSupport (f 0) ⊆ closedBallR4 x d →
      ∀ i, euclideanTSupport (f i) ⊆ closedBallR4 x (9 * d) := by
    intro x hx i
    by_cases hi : i = 0
    · subst hi
      intro u hu
      have h1 : euclidDistR4 u x ≤ d := hx hu
      exact show euclidDistR4 u x ≤ 9 * d from by linarith
    · obtain ⟨-, -, -, ⟨u₀, hu₀⟩, -⟩ := exists_isR4Bump hf 0
      intro v hv
      exact (main (Ne.symm hi) x hx u₀ (subset_tsupport _ hu₀) v hv).2.2
  refine ⟨fun i j hij u hu v hv => ?_, ?_, ?_⟩
  · obtain ⟨x, -, -, -, hx, -⟩ := exists_isR4Bump hf i
    have h := main hij x hx u hu v hv
    exact ⟨h.1, h.2.1⟩
  · obtain ⟨x, -, -, -, hx, -⟩ := exists_isR4Bump hf 0
    exact ⟨x, third x hx⟩
  · intro x₁ h₁
    obtain ⟨-, -, -, -, hx, -⟩ := h₁
    exact third x₁ hx
theorem liftsOverBall_of_mem (hb : BallProjectionStatement)
    (hc : TranslatedLatticeCells.CellsAndBallsStatement) {d ϑ : ℝ} (hd : 0 < d)
    (hϑ : ϑ ∈ Ioc (0 : ℝ) 1) (h40 : 40 * d ≤ PeriodicLattice.torusSide s.L s.m)
    {f : Fin 4 → s.Torus → ℝ} (hf : f ∈ quadsTorus s d ϑ) : LiftsOverBall d ϑ f := by
  intro y c hsupp himg
  have hR : 0 < 9 * d := by positivity
  have hRl : 9 * d ≤ PeriodicLattice.torusSide s.L s.m / 4 := by linarith
  obtain ⟨hshort, ⟨hbij, hdist⟩, hcorr, hfun⟩ := hb s (9 * d) c hR hRl
  have hyc : ballOnTorus y (9 * d) = torusBallOver s c (9 * d) := himg.symm.trans hbij.image_eq
  have hdown : ∀ i, IsPushdown s c (9 * d) (liftOverBall c d (f i)) (f i) := by
    intro i
    refine (hcorr.2 (f i) fun u hu => ?_).2
    by_contra hne
    apply hu
    rw [← hyc]
    exact hsupp i (subset_tsupport _ hne)
  have hlipf : ∀ i, IsLipschitzFor (euclidDistTorus (ℓ := PeriodicLattice.torusSide s.L s.m)) (f i) ∧
      ∀ u, 0 ≤ f i u := by
    obtain ⟨-, -, hl, -⟩ := hf
    exact hl
  have hlipg : ∀ i, IsLipschitzFor euclidDistR4 (liftOverBall c d (f i)) :=
    fun i => (hfun _ _ (hdown i)).2.2.1.1.1 (hlipf i).1
  have hnn : ∀ i t, 0 ≤ liftOverBall c d (f i) t :=
    fun i => (hfun _ _ (hdown i)).2.1.2.2.1 (hlipf i).2
  have hnum := fun i => pushdown_invariants hb hc hR hRl (hdown i) (hlipg i)
  have hsupports := fun i => (hfun _ _ (hdown i)).2.2.2.1
  have hsets : ∀ i j, setDist (torusTSupport (f i)) (torusTSupport (f j)) =
      setDistR4 (euclideanTSupport (liftOverBall c d (f i)))
        (euclideanTSupport (liftOverBall c d (f j))) := by
    intro i j
    rw [(hsupports i).2.2, (hsupports j).2.2]
    exact setDist_image_eq hdist (hsupports i).1 (hsupports j).1
  have hbump : ∀ i, ∃ x, IsR4Bump d ϑ x (liftOverBall c d (f i)) := by
    intro i
    obtain ⟨x, -, -, ⟨u₀, hu₀⟩, hx4, hx5, hx6⟩ := exists_isTorusBump hf i
    have hu₀B : u₀ ∈ torusBallOver s c (9 * d) := by
      rw [← hyc]
      exact hsupp i (subset_tsupport _ hu₀)
    obtain ⟨t₀, ht₀, rfl⟩ := hbij.surjOn hu₀B
    obtain ⟨-, hwb, -⟩ := (hc s).2.1 (proj s t₀) d hd
    have hxw : x ∈ closedWrapBall (proj s t₀) d := by
      have h1 : pointDist (proj s t₀) x ≤ d := hx4 (subset_tsupport _ hu₀)
      rw [pointDist_comm hc] at h1
      exact h1
    rw [(hwb t₀ (isLift_proj t₀)).1] at hxw
    obtain ⟨xt, hxt, rfl⟩ := hxw
    refine ⟨xt, hlipg i, hnn i, ⟨t₀, ?_⟩, ?_, ?_, ?_⟩
    · rw [← (hdown i).2.1 t₀ ht₀]
      exact hu₀
    · intro t ht
      have htB : euclidDistR4 t c ≤ 9 * d := (hsupports i).1 ht
      have himgs : proj s t ∈ torusTSupport (f i) := by
        rw [(hsupports i).2.2]
        exact mem_image_of_mem _ ht
      have hsmall : euclidNormVec (t - xt) ≤ PeriodicLattice.torusSide s.L s.m / 2 := by
        have e1 := euclidDistR4_le_add t xt c
        have e2 := euclidDistR4_le_add c xt t₀
        have e4 : euclidDistR4 t₀ c ≤ 9 * d := ht₀
        have e5 : euclidDistR4 xt t₀ ≤ d := hxt
        rw [euclidDistR4_symm c t₀, euclidDistR4_symm t₀ xt] at e2
        exact show euclidDistR4 t xt ≤ PeriodicLattice.torusSide s.L s.m / 2 from by linarith
      have hk := hshort (t - xt) hsmall
      rw [proj_sub] at hk
      have hle : pointNorm (proj s t - proj s xt) ≤ d := hx4 himgs
      rw [hk] at hle
      exact hle
    · rw [(hnum i).2.1, (hnum i).2.2.2]
      exact hx5
    · have e : bestLipschitzConstant euclidDistR4 (liftOverBall c d (f i)) =
          lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (f i) := (hnum i).2.2.1
      rw [e, (hnum i).2.1]
      exact hx6
  refine ⟨?_, ?_, fun i => ?_⟩
  · unfold IsBallIsometry
    rw [hyc]
    exact ⟨hbij, hdist⟩
  · refine ⟨⟨hd, hϑ⟩, fun i => ⟨hlipg i, hnn i⟩, fun i j hij => ?_⟩
    obtain ⟨x, hx⟩ := hbump i
    obtain ⟨x', hx'⟩ := hbump j
    obtain ⟨-, -, -, -, h1, h2⟩ := pair_of_mem_quadsTorus hf hij
    rw [hsets i j] at h1 h2
    exact ⟨x, x', hx, hx', h1, h2⟩
  · obtain ⟨htr, -, -, hs', -⟩ := hfun _ _ (hdown i)
    exact ⟨htr.2.2.1, htr.2.2.2, (hnum i).2.1, (hnum i).2.2.1, (hnum i).2.2.2, hs'.2.2.symm⟩
theorem liftOverBall_of_mem {c t : Fin 4 → ℝ} {d : ℝ} {g : s.Torus → ℝ}
    (h : t ∈ closedBallR4 c (9 * d)) : liftOverBall c d g t = g (proj s t) :=
  Set.indicator_of_mem h _
theorem liftOverBall_of_notMem {c t : Fin 4 → ℝ} {d : ℝ} {g : s.Torus → ℝ}
    (h : t ∉ closedBallR4 c (9 * d)) : liftOverBall c d g t = 0 :=
  Set.indicator_of_notMem h _
theorem euclidNormVec_sub_le_of_mem {c a b : Fin 4 → ℝ} {r : ℝ} (ha : a ∈ closedBallR4 c r)
    (hb : b ∈ closedBallR4 c r) : euclidNormVec (a - b) ≤ 2 * r := by apply _root_.YangMills.Construction.TestPairs.euclidNormVec_sub_le_two_mul_of_mem <;> assumption
theorem liftsDifferByPeriod_of_mem (hb : BallProjectionStatement) {d ϑ : ℝ}
    (hd : 0 < d) (h40 : 40 * d ≤ PeriodicLattice.torusSide s.L s.m) {f : Fin 4 → s.Torus → ℝ}
    (hf : f ∈ quadsTorus s d ϑ) : LiftsDifferByPeriod d f := by
  intro c c' hB hB'
  have hR : 0 < 9 * d := by positivity
  have hRl : 9 * d ≤ PeriodicLattice.torusSide s.L s.m / 4 := by linarith
  obtain ⟨-, ⟨hbij, -⟩, -, -⟩ := hb s (9 * d) c hR hRl
  obtain ⟨-, ⟨hbij', -⟩, -, -⟩ := hb s (9 * d) c' hR hRl
  obtain ⟨-, -, -, ⟨u₀, hu₀⟩, -⟩ := exists_isTorusBump hf 0
  obtain ⟨t₀, ht₀, h0⟩ := hB 0 (subset_tsupport _ hu₀)
  obtain ⟨t₀', ht₀', h0'⟩ := hB' 0 (subset_tsupport _ hu₀)
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq (h0'.trans h0.symm)
  have hsame : ∀ t ∈ closedBallR4 c (9 * d), ∀ t' ∈ closedBallR4 c' (9 * d),
      proj s t' = proj s t →
      t' = t + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k := by
    intro t ht t' ht' he
    obtain ⟨k₁, hk₁⟩ := exists_latticeTranslate_of_torusProj_eq he
    have e : latticeTranslate (PeriodicLattice.torusSide s.L s.m) (k₁ - k) =
        (t' - t₀') + -(t - t₀) := by
      rw [hk₁, hk]
      funext μ
      simp only [latticeTranslate, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
      push_cast
      ring
    have hsmall : euclidNormVec (latticeTranslate (PeriodicLattice.torusSide s.L s.m) (k₁ - k)) <
        PeriodicLattice.torusSide s.L s.m := by
      rw [e]
      have e1 := euclidNormVec_add_le (t' - t₀') (-(t - t₀))
      rw [euclidNormVec_neg] at e1
      have e2 := euclidNormVec_sub_le_of_mem ht' ht₀'
      have e3 := euclidNormVec_sub_le_of_mem ht ht₀
      linarith
    have hz := eq_zero_of_latticeTranslate_lt (torusSide_pos s) hsmall
    rw [hk₁, sub_eq_zero.1 hz]
  refine ⟨k, fun t i => ?_⟩
  have hcov : proj s (t + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) = proj s t :=
    torusProj_add_latticeTranslate _ _ _
  by_cases hz : f i (proj s t) = 0
  · have a : ∀ (b w : Fin 4 → ℝ), proj s w = proj s t → liftOverBall b d (f i) w = 0 := by
      intro b w hw
      by_cases hm : w ∈ closedBallR4 b (9 * d)
      · rw [liftOverBall_of_mem hm, hw, hz]
      · exact liftOverBall_of_notMem hm
    rw [a c' _ hcov, a c _ rfl]
  · have hne : proj s t ∈ torusTSupport (f i) := subset_tsupport _ hz
    obtain ⟨t₁, ht₁, h1⟩ := hB i hne
    obtain ⟨t₁', ht₁', h1'⟩ := hB' i hne
    have hs' := hsame t₁ ht₁ t₁' ht₁' (h1'.trans h1.symm)
    by_cases hm : t ∈ closedBallR4 c (9 * d)
    · have e : t = t₁ := hbij.injOn hm ht₁ h1.symm
      have hm' : t + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k ∈
          closedBallR4 c' (9 * d) := by
        rw [e, ← hs']
        exact ht₁'
      rw [liftOverBall_of_mem hm', liftOverBall_of_mem hm, hcov]
    · have hm' : t + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k ∉
          closedBallR4 c' (9 * d) := by
        intro hm'
        have e : t + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k = t₁' :=
          hbij'.injOn hm' ht₁' (hcov.trans h1'.symm)
        apply hm
        have e' : t = t₁ := add_right_cancel (e.trans hs')
        rw [e']
        exact ht₁
      rw [liftOverBall_of_notMem hm', liftOverBall_of_notMem hm]
end Periodic
theorem periodizationIsQuadruple_of_mem (hb : BallProjectionStatement)
    (hc : TranslatedLatticeCells.CellsAndBallsStatement) {s : Conventions.StandingParameters}
    {d ϑ : ℝ} (hd : 0 < d) (hϑ : ϑ ∈ Ioc (0 : ℝ) 1)
    (h40 : 40 * d ≤ PeriodicLattice.torusSide s.L s.m)
    {f : Fin 4 → (Fin 4 → ℝ) → ℝ} (hf : f ∈ quadsR4 d ϑ)
    (hball : ∃ c, ∀ i, euclideanTSupport (f i) ⊆ closedBallR4 c (9 * d)) :
    PeriodizationIsQuadruple s d ϑ f := by
  obtain ⟨c, hsub⟩ := hball
  have hR : 0 < 9 * d := by positivity
  have hRl : 9 * d ≤ PeriodicLattice.torusSide s.L s.m / 4 := by linarith
  obtain ⟨-, ⟨-, hdist⟩, hcorr, hfun⟩ := hb s (9 * d) c hR hRl
  have hvan : ∀ i t, t ∉ closedBallR4 c (9 * d) → f i t = 0 := by
    intro i t ht
    by_contra hne
    exact ht (hsub i (subset_tsupport _ hne))
  have hdown : ∀ i, IsPushdown s c (9 * d) (f i)
      (periodize (PeriodicLattice.torusSide s.L s.m) (f i)) := by
    intro i
    obtain ⟨h, hh, -⟩ := hcorr.1 (f i) (hvan i)
    have e := (hfun _ _ hh).1.2.2.2
    rw [← e]
    exact hh
  have hlipf : ∀ i, IsLipschitzFor euclidDistR4 (f i) ∧ ∀ t, 0 ≤ f i t := by
    obtain ⟨-, hl, -⟩ := hf
    exact hl
  have hnum := fun i => pushdown_invariants hb hc hR hRl (hdown i) (hlipf i).1
  have hsupports := fun i => (hfun _ _ (hdown i)).2.2.2.1
  have hnn : ∀ i u, 0 ≤ periodize (PeriodicLattice.torusSide s.L s.m) (f i) u :=
    fun i => (hfun _ _ (hdown i)).2.1.2.2.2 (hlipf i).2
  have hsets : ∀ i j,
      setDist (s := s) (torusTSupport (periodize (PeriodicLattice.torusSide s.L s.m) (f i)))
        (torusTSupport (periodize (PeriodicLattice.torusSide s.L s.m) (f j))) =
      setDistR4 (euclideanTSupport (f i)) (euclideanTSupport (f j)) := by
    intro i j
    rw [(hsupports i).2.2, (hsupports j).2.2]
    exact setDist_image_eq hdist (hsupports i).1 (hsupports j).1
  have hbump : ∀ i, ∃ x,
      IsTorusBump s d ϑ x (periodize (PeriodicLattice.torusSide s.L s.m) (f i)) := by
    intro i
    obtain ⟨x, -, -, ⟨t₀, ht₀⟩, hx4, hx5, hx6⟩ := exists_isR4Bump hf i
    refine ⟨proj s x, (hnum i).1, hnn i, ⟨proj s t₀, ?_⟩, ?_, ?_, ?_⟩
    · have hm : t₀ ∈ closedBallR4 c (9 * d) := by
        by_contra hm
        exact ht₀ (hvan i t₀ hm)
      rw [(hdown i).2.1 t₀ hm]
      exact ht₀
    · intro u hu
      have hu' : u ∈ torusTSupport (s := s)
          (periodize (PeriodicLattice.torusSide s.L s.m) (f i)) := hu
      rw [(hsupports i).2.2] at hu'
      obtain ⟨t, ht, rfl⟩ := hu'
      have e := (hc s).1.2 (t - x)
      rw [proj_sub] at e
      have e2 : euclidNormVec (t - x) ≤ d := hx4 ht
      exact e.trans e2
    · rw [← (hnum i).2.1, ← (hnum i).2.2.2]
      exact hx5
    · have e : bestLipschitzConstant (euclidDistTorus (ℓ := PeriodicLattice.torusSide s.L s.m))
          (periodize (PeriodicLattice.torusSide s.L s.m) (f i)) = lipConstR4 (f i) :=
        (hnum i).2.2.1.symm
      rw [e, ← (hnum i).2.1]
      exact hx6
  refine ⟨fun i => ⟨_, (hfun _ _ (hdown i)).1.2.2.1⟩,
    ⟨hd, hϑ⟩, h40, fun i => ⟨(hnum i).1, hnn i⟩, fun i j hij => ?_⟩
  obtain ⟨x, hx⟩ := hbump i
  obtain ⟨x', hx'⟩ := hbump j
  obtain ⟨-, -, -, -, h1, h2⟩ := pair_of_mem_quadsR4 hf hij
  rw [← hsets i j] at h1 h2
  exact ⟨x, x', hx, hx', h1, h2⟩
theorem quadrupleGeometryStatement_holds (hb : BallProjectionStatement)
    (hc : TranslatedLatticeCells.CellsAndBallsStatement) : QuadrupleGeometryStatement := by
  refine ⟨?_, ?_⟩
  · intro d ϑ hd hϑ f hf
    have hpts := pointGapsAndBallR4_of_mem hd hf
    refine ⟨supportGapsR4_of_mem hd hϑ hf, hpts, fun s h40 =>
      periodizationIsQuadruple_of_mem hb hc hd hϑ h40 hf ?_⟩
    obtain ⟨-, hball, -⟩ := hpts
    exact hball
  · intro s d ϑ hd hϑ h40 f hf
    refine ⟨supportGapsTorus_of_mem hd hϑ hf, pointGapsAndBallTorus_of_mem hc hd hf,
      ⟨by linarith, fun y t ht => ?_⟩, liftsOverBall_of_mem hb hc hd hϑ h40 hf,
      liftsDifferByPeriod_of_mem hb hd h40 hf⟩
    have hR : 0 < 9 * d := by positivity
    obtain ⟨-, hwb, -, -, -, hr⟩ := (hc s).2.1 y (9 * d) hR
    exact (hwb t ht).1.symm.trans (hr (by linarith))
end YangMills.Construction.QuadrupleGeometry
