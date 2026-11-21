import YangMills.Construction.TorusOrFourSpace.FunctionalBoundedInTheSharpNormIsADistributionProof
import YangMills.Construction.TorusOrFourSpace.PartsAtAFamilyWithNoEmptyMember
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.NonemptyMembersBoxProperties
open Tuple AdmissibleCharts
variable {D : Params} {E : Kind}
def realPullback (z : Fin 4 → ℝ) (A : Set (E.Pt D)) (φ : E.Pt D → ℝ) :
    euclidean.Pt D → ℝ :=
  fun u => (singlePullback D E z A (fun y => (φ y : ℂ)) u).re
def realPushforward (z : Fin 4 → ℝ) (A : Set (E.Pt D)) (g : euclidean.Pt D → ℝ) :
    E.Pt D → ℝ :=
  fun y => (singlePushforward D E z A (fun u => (g u : ℂ)) y).re
def pushforwardTuple {n : ℕ} (z : Fin n → Fin 4 → ℝ) (G : Fin n → Set (E.Pt D))
    (g : Fin n → euclidean.Pt D → ℝ) : FnTuple D E n :=
  fun i => realPushforward (z i) (G i) (g i)
theorem singlePushforward_singlePullback (hChart : AdmissibleCharts.Claim) {n : ℕ+} {R d : ℝ}
    {G : Fin (n : ℕ) → Set (E.Pt D)} (hG : AdmissibleWith D E R d G) (i : Fin (n : ℕ))
    {z : Fin 4 → ℝ} (hz : E.quotMap D z ∈ G i) {φ : E.Pt D → ℂ}
    (hφ : φ ∈ singleTestFns D E (G i)) :
    singlePushforward D E z (G i) (singlePullback D E z (G i) φ) = φ := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.singlePushforward_singlePullback <;> assumption
theorem singlePullback_of_mem {z : Fin 4 → ℝ} {A : Set (E.Pt D)} {u : euclidean.Pt D}
    (hu : u ∈ chartSource D E z A) (φ : E.Pt D → ℂ) :
    singlePullback D E z A φ u = φ (translateChart D E z u) := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.singlePullback_of_mem <;> assumption
theorem setInfDist_mono {A A' B B' : Set (E.Pt D)} (hA : A ⊆ A') (hB : B ⊆ B') :
    setInfDist D E A' B' ≤ setInfDist D E A B := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.CentredMoments.setInfDist_anti <;> assumption
theorem toReal_mem_allowedRadii {r : ℝ≥0∞} (h0 : 0 < r) (hq : r < periodQuarter D E)
    (htop : r ≠ ∞) : r.toReal ∈ allowedRadii D E := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.toReal_mem_allowedRadii <;> assumption
theorem composePullback_eq {n : ℕ+} {z : Fin (n : ℕ) → Fin 4 → ℝ}
    {G : Fin (n : ℕ) → Set (E.Pt D)}
    (T : testFns D euclidean (chartSources D E z G) → ℂ)
    (F : testFns D E (boxSet D E G))
    (H : testFns D euclidean (chartSources D E z G))
    (hH : H.1 = pullback D E z G F.1) : composePullback D E z G T F = T H := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.composePullback_eq <;> assumption
section Single
variable {n : ℕ+} {G : Fin (n : ℕ) → Set (E.Pt D)} {z : Fin (n : ℕ) → Fin 4 → ℝ}
theorem coe_realPullback (hc : SingleMapsOnClasses D E z G) (i : Fin (n : ℕ)) {φ : E.Pt D → ℝ}
    (hφ : (fun y => (φ y : ℂ)) ∈ singleTestFns D E (G i)) :
    (fun u => (realPullback (z i) (G i) φ u : ℂ)) =
      singlePullback D E (z i) (G i) fun y => (φ y : ℂ) := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.coe_pullReal <;> assumption
theorem realPullback_mem (hc : SingleMapsOnClasses D E z G) (i : Fin (n : ℕ)) {φ : E.Pt D → ℝ}
    (hφ : (fun y => (φ y : ℂ)) ∈ singleTestFns D E (G i)) :
    (fun u => (realPullback (z i) (G i) φ u : ℂ)) ∈
      singleTestFns D euclidean (chartSource D E (z i) (G i)) := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.pullReal_mem <;> assumption
theorem realPushforward_mem (hc : SingleMapsOnClasses D E z G) (i : Fin (n : ℕ))
    {g : euclidean.Pt D → ℝ} (hg : g ∈ c1SupportedIn D euclidean (chartSource D E (z i) (G i))) :
    realPushforward (z i) (G i) g ∈ c1SupportedIn D E (G i) ∧
      (fun y => (realPushforward (z i) (G i) g y : ℂ)) =
        singlePushforward D E (z i) (G i) fun u => (g u : ℂ) := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.pushReal_mem <;> assumption
theorem realPushforward_realPullback (hc : SingleMapsOnClasses D E z G)
    (hpp : ∀ i, ∀ φ ∈ singleTestFns D E (G i),
      singlePushforward D E (z i) (G i) (singlePullback D E (z i) (G i) φ) = φ)
    (i : Fin (n : ℕ)) {φ : E.Pt D → ℝ}
    (hφ : (fun y => (φ y : ℂ)) ∈ singleTestFns D E (G i)) :
    realPushforward (z i) (G i) (realPullback (z i) (G i) φ) = φ := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.pushReal_pullReal <;> assumption
theorem exists_realPullback_eq (hc : SingleMapsOnClasses D E z G)
    (hpp : ∀ i, ∀ φ ∈ singleTestFns D E (G i),
      singlePushforward D E (z i) (G i) (singlePullback D E (z i) (G i) φ) = φ)
    (i : Fin (n : ℕ)) {g : euclidean.Pt D → ℝ}
    (hg : (fun u => (g u : ℂ)) ∈
      singleTestFns D euclidean (chartSource D E (z i) (G i)))
    (hg1 : g ∈ c1SupportedIn D euclidean (chartSource D E (z i) (G i))) :
    ∃ φ : E.Pt D → ℝ, (fun y => (φ y : ℂ)) ∈ singleTestFns D E (G i) ∧
      realPullback (z i) (G i) φ = g := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.exists_pullReal_eq <;> assumption
end Single
theorem holds (hChart : AdmissibleCharts.Claim)
    (hForm : C1BoundedFormDistribution)
    (hDense : TensorSpanDenseOnBoxes)
    (hFacts : LiftsProductsDistributions.Statement)
    (hProd : DisjointProducts.Claim)
    (hPts : TupleFacts.AllFacts) : Statement := by
  intro D E C S hS n hn R d G hG hne
  have hS' : S.IsBoundedBy C := hS
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  have hd : 0 < d := hG.sep_pos
  obtain ⟨hCov, hLift, -, -, hLip, -, -⟩ := hFacts D E
  have hlift : ∀ y : E.Pt D, ∃ x, E.quotMap D x = y := fun y => by
    obtain ⟨x, hx, -⟩ := hLift 0 y
    exact ⟨x, hx⟩
  have hzex : ∀ i, ∃ x, E.quotMap D x ∈ G i := fun i => by
    obtain ⟨y, hy⟩ := hne i
    obtain ⟨x, rfl⟩ := hlift y
    exact ⟨x, hy⟩
  choose z hz using hzex
  obtain ⟨⟨hr0, hr2, hrq, hfac⟩, -, hinv, -, hiso, hconv, hcls⟩ :=
    hChart D E n R d G z hG hne hz
  have hpp : ∀ i, ∀ φ ∈ singleTestFns D E (G i),
      singlePushforward D E (z i) (G i) (singlePullback D E (z i) (G i) φ) = φ :=
    fun i φ hφ => singlePushforward_singlePullback hChart hG i (hz i) hφ
  have hdist0 : ∀ y : E.Pt D, ENNReal.ofReal (quotDist D E y y) = 0 := fun y => by
    obtain ⟨x, rfl⟩ := hlift y
    refine ENNReal.ofReal_eq_zero.mpr ((hCov x x).1.trans (le_of_eq ?_))
    simp [TorusMetric.euclidNormVec]
  have hdisj : ∀ l l', l ≠ l' → Disjoint (G l) (G l') := fun l l' hll =>
    Set.disjoint_left.mpr fun y h1 h2 => by
      have h3 : setInfDist D E (G l) (G l') ≤ 0 := by
        rw [← hdist0 y]
        exact iInf₂_le_of_le y h1 (iInf₂_le_of_le y h2 le_rfl)
      have h4 : ENNReal.ofReal d ≤ 0 := (hG.sep_le_setInfDist l l' hll).trans h3
      have h5 : 0 < ENNReal.ofReal d := ENNReal.ofReal_pos.mpr hd
      exact absurd h4 (not_le.mpr h5)
  obtain ⟨hVec, hSepP, hLinP, -, -⟩ := hProd D E n hn1
  have hVec4 := (hProd D euclidean n hn1).1
  have hTen : TupleFacts.TensorTestFns D E n :=
    (hPts D E n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmemP : ∀ g : C1Components D euclidean (fun i => chartSource D E (z i) (G i)),
      pushforwardTuple z G (fun j => (g j).1) ∈
        productSet D E (fun l => c1SupportedIn D E (G l)) :=
    fun g i _ => (realPushforward_mem hcls i (g i).2).1
  have hsep : ∀ g : C1Components D euclidean (fun i => chartSource D E (z i) (G i)),
      pushforwardTuple z G (fun j => (g j).1) ∈ sepC1Tuples D E (n : ℕ) :=
    fun g => hSepP G hdisj (hmemP g)
  obtain ⟨B, hB⟩ : ∃ B : C1Components D euclidean (fun i => chartSource D E (z i) (G i)) → ℝ,
      ∀ g, B g = S.func (n : ℕ) hn ⟨_, hsep g⟩ := ⟨_, fun _ => rfl⟩
  have hrtop : maxMemberDiam D E G ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hr2
  have hrpos : 0 < (maxMemberDiam D E G).toReal := ENNReal.toReal_pos hr0.ne' hrtop
  have hradm := toReal_mem_allowedRadii hr0 hrq hrtop
  have h80 : 0 ≤ 80 * D.M := by linarith [D.one_le_M]
  have hCv : 0 ≤ C.val (n : ℕ) d (maxMemberDiam D E G).toReal :=
    C.nonneg _ hn d _ hd hrpos
  have hc0 : 0 ≤ (80 * D.M) ^ (n : ℕ) * C.val (n : ℕ) d (maxMemberDiam D E G).toReal :=
    mul_nonneg (pow_nonneg h80 _) hCv
  have hlin : IsMultilinearReal B := by
    intro g i u v w a b hw
    have hN := hLinP (S.func (n : ℕ) hn) (S.multilinear (n : ℕ) hn) G hdisj
    have hupd : ∀ x : c1SupportedIn D euclidean (chartSource D E (z i) (G i)),
        pushforwardTuple z G (fun j => (Function.update g i x j).1) =
          Function.update (pushforwardTuple z G fun j => (g j).1) i
            (realPushforward (z i) (G i) x.1) := by
      intro x
      funext j
      by_cases h : j = i
      · subst h
        simp [pushforwardTuple]
      · simp [pushforwardTuple, Function.update_of_ne h]
    have hpw : realPushforward (z i) (G i) w.1 =
        a • realPushforward (z i) (G i) u.1 + b • realPushforward (z i) (G i) v.1 := by
      have e := (hcls.2.2 i).2.1 a b u.1 u.2 v.1 v.2
      have hw' : (fun x => ((w.1 x : ℝ) : ℂ)) = fun x => ((a * u.1 x + b * v.1 x : ℝ) : ℂ) := by
        funext x
        rw [hw]
        rfl
      funext y
      show (singlePushforward D E (z i) (G i) (fun x => ((w.1 x : ℝ) : ℂ)) y).re =
        a * (singlePushforward D E (z i) (G i) (fun x => ((u.1 x : ℝ) : ℂ)) y).re +
          b * (singlePushforward D E (z i) (G i) (fun x => ((v.1 x : ℝ) : ℂ)) y).re
      rw [hw', e]
      simp
    have hm : ∀ x : c1SupportedIn D euclidean (chartSource D E (z i) (G i)),
        Function.update (pushforwardTuple z G fun j => (g j).1) i
            (realPushforward (z i) (G i) x.1) ∈
          sepC1Tuples D E (n : ℕ) :=
      fun x => hupd x ▸ hsep (Function.update g i x)
    have hww : Function.update (pushforwardTuple z G fun j => (g j).1) i
        (a • realPushforward (z i) (G i) u.1 + b • realPushforward (z i) (G i) v.1) ∈
          sepC1Tuples D E (n : ℕ) := by
      rw [← hpw]
      exact hm w
    have key := hN.2 _ (hmemP g) i _ (realPushforward_mem hcls i u.2).1 _
      (realPushforward_mem hcls i v.2).1 a b (hm u) (hm v) hww
    have eu : ∀ x : c1SupportedIn D euclidean (chartSource D E (z i) (G i)),
        S.func (n : ℕ) hn ⟨_, hm x⟩ = B (Function.update g i x) := fun x => by
      rw [hB]
      exact congrArg _ (Subtype.ext (hupd x).symm)
    rw [← eu u, ← eu v, ← key, hB]
    exact congrArg _ (Subtype.ext ((hupd w).trans (by rw [hpw])))
  have hbd : C1Bounded
      ((80 * D.M) ^ (n : ℕ) * C.val (n : ℕ) d (maxMemberDiam D E G).toReal) B := by
    intro g
    have hmem := hmemP g
    have hl : pushforwardTuple z G (fun j => (g j).1) ∈ lipTuplesSpacedInBalls D E (n : ℕ) d
        (maxMemberDiam D E G).toReal := by
      refine ⟨fun i => ?_, fun i => ?_, fun i k hik => ?_⟩
      · exact (hLip _ ⟨(hmem i trivial).1, (hmem i trivial).2.1, Set.subset_univ _⟩).1
      · exact ⟨closedBallAbout D E (E.quotMap D (z i)) (maxMemberDiam D E G).toReal,
          ⟨hrpos, _, rfl⟩, (hmem i trivial).2.2.trans (hfac i).2.2.2.2.2.2⟩
      · exact (hG.sep_le_setInfDist i k hik).trans
          (setInfDist_mono (hmem i trivial).2.2 (hmem k trivial).2.2)
    have h1 := hS' (n : ℕ) hn d _ hd hradm ⟨_, hsep g⟩ hl
    have hsh : ∀ i, sharpNormQ D E (pushforwardTuple z G (fun j => (g j).1) i) ≤
        ENNReal.ofReal (80 * D.M) * c1NormSingleReal D euclidean (g i).1 := fun i => by
      have h2 := (hLip _ ⟨(hmem i trivial).1, (hmem i trivial).2.1, Set.subset_univ _⟩).2.2
      have h3 := (hcls.2.2 i).2.2 (g i).1 (g i).2
      have h4 : c1NormSingleReal D E (pushforwardTuple z G (fun j => (g j).1) i) =
          c1NormSingleReal D euclidean (g i).1 := by
        rw [← h3, ← (realPushforward_mem hcls i (g i).2).2]
        rfl
      rw [← h4]
      exact h2
    rw [hB g]
    calc ENNReal.ofReal |S.func (n : ℕ) hn ⟨_, hsep g⟩|
        ≤ ENNReal.ofReal (C.val (n : ℕ) d (maxMemberDiam D E G).toReal) *
            ∏ i, sharpNormQ D E (pushforwardTuple z G (fun j => (g j).1) i) := h1
      _ ≤ ENNReal.ofReal (C.val (n : ℕ) d (maxMemberDiam D E G).toReal) *
            ∏ i, (ENNReal.ofReal (80 * D.M) * c1NormSingleReal D euclidean (g i).1) := by
          gcongr with i _
          exact hsh i
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ENNReal.ofReal_mul (pow_nonneg h80 _), ENNReal.ofReal_pow h80, ← mul_assoc,
            mul_comm (ENNReal.ofReal (C.val _ _ _))]
  obtain ⟨hF1, ⟨T0, hT0, hT0u⟩, hT0b⟩ := hForm D n (2 * R) _
    (by have := hG.radius_pos; positivity) hc0 (fun i => chartSource D E (z i) (G i))
    (fun i => (hfac i).1) (fun i u hu => (hfac i).2.2.2.2.2.1 ((hfac i).2.2.2.2.1 hu)) B hlin hbd
  have hcut : ∀ φ, IsCutoffFamily D E G φ →
      φ ∈ sepC1Tuples D E (n : ℕ) ∧
        cutoffTensor D E φ ∈ testFns D E (boxSet D E G) ∧
        tensorProd D euclidean (fun i u => ((realPullback (z i) (G i) (φ i) u : ℝ) : ℂ)) =
          pullback D E z G (cutoffTensor D E φ) ∧
        ∀ i, (fun u => ((realPullback (z i) (G i) (φ i) u : ℝ) : ℂ)) ∈
          singleTestFns D euclidean (chartSource D E (z i) (G i)) := by
    intro φ hφ
    refine ⟨hSepP G hdisj fun i _ => hVec.2 (G i) (hG.isOpen_mem i) _ (hφ i),
      hTen G _ hG.isOpen_mem hφ, ?_, fun i => realPullback_mem hcls i (hφ i)⟩
    exact (congrArg _ (funext fun i => coe_realPullback hcls i (hφ i))).trans
      (hcls.2.1 (fun i y => (φ i y : ℂ)) hφ).symm
  have hBp : ∀ φ, IsCutoffFamily D E G φ →
      ∀ (h : ∀ i, realPullback (z i) (G i) (φ i) ∈
          c1SupportedIn D euclidean (chartSource D E (z i) (G i)))
        (hs : φ ∈ sepC1Tuples D E (n : ℕ)),
        B (fun i => ⟨_, h i⟩) = S.func (n : ℕ) hn ⟨φ, hs⟩ := by
    intro φ hφ h hs
    rw [hB]
    exact congrArg _ (Subtype.ext (funext fun i => realPushforward_realPullback hcls hpp i (hφ i)))
  have hexist : S.IsBoxDistrib hn G (composePullback D E z G T0) := by
    refine ⟨hconv.2.1.mapsTo hT0.1, fun φ hφ => ?_⟩
    obtain ⟨hs, hF, hpb, hm⟩ := hcut φ hφ
    obtain ⟨h1, hF', e⟩ := hT0.2 (fun i => realPullback (z i) (G i) (φ i)) hm
    refine ⟨hs, hF, ?_⟩
    exact (composePullback_eq T0 ⟨_, hF⟩ ⟨_, hF'⟩ hpb).trans
      (e.trans (congrArg _ (hBp φ hφ h1 hs)))
  have hu : ∀ T', S.IsBoxDistrib hn G T' → T' = composePullback D E z G T0 := by
    intro T' hT'
    obtain ⟨T, hTd, rfl⟩ := hconv.2.1.surjOn hT'.1
    have hform : IsDistribExtending B T := by
      refine ⟨hTd, fun ψ hψ => ?_⟩
      obtain ⟨h1, hF', -⟩ := hT0.2 ψ hψ
      choose φ hφ hpl using fun i => exists_realPullback_eq hcls hpp i (hψ i) (h1 i)
      obtain ⟨hs, hF, hpb, hm⟩ := hcut φ hφ
      obtain ⟨hs', hF2, e⟩ := hT'.2 φ hφ
      have hψe : ψ = fun i => realPullback (z i) (G i) (φ i) := funext fun i => (hpl i).symm
      subst hψe
      refine ⟨h1, hF', ?_⟩
      exact (composePullback_eq T ⟨_, hF2⟩ ⟨_, hF'⟩ hpb).symm.trans
        (e.trans (congrArg _ (hBp φ hφ h1 hs').symm))
    exact congrArg _ (hT0u T hform)
  refine ⟨⟨_, hexist, hu⟩, hDense D E n R d G hG hne,
    fun ⟨i, hi⟩ => absurd hi (hne i).ne_empty, fun T hT => ?_⟩
  have hTe := hu T hT
  subst hTe
  refine ⟨fun _ χ hχ F hFχ => ?_, fun ⟨i, hi⟩ => absurd hi (hne i).ne_empty,
    (hconv.2.2.2 T0 hT0.1 _).mpr (hT0b T0 hT0).2⟩
  have hcs : HasCompactSupportWithin D E (boxSet D E G) F.1 := ⟨F.2.2.1, F.2.2.2⟩
  have hpF := hiso.1.mapsTo F.2
  have hχ' : IsCutoffFamily D euclidean (fun i => chartSource D E (z i) (G i))
      (fun i => realPullback (z i) (G i) (χ i)) := fun i => realPullback_mem hcls i (hχ i)
  have hone : OneOnCoordProjs D euclidean (pullback D E z G F.1)
      (fun i => realPullback (z i) (G i) (χ i)) := by
    rintro i _ ⟨u, hu', rfl⟩
    rw [(hinv.2.2.1 F.1 hcs).2.2] at hu'
    obtain ⟨huO, huF⟩ := hu'
    obtain ⟨U, -, hsub, h1⟩ := hFχ i
    have h2 : χ i (translateChart D E (z i) (u i)) = 1 := h1 _ (hsub ⟨_, huF, rfl⟩)
    show (singlePullback D E (z i) (G i) (fun y => (χ i y : ℂ)) (u i)).re = 1
    rw [singlePullback_of_mem (huO i), h2]
    simp
  have hcf := (hF1 ⟨_, hpF⟩).1 _ hχ' hone
  have hb := (hT0b T0 hT0).1 ⟨_, hpF⟩ _ hcf
  have hTF : composePullback D E z G T0 F = T0 ⟨_, hpF⟩ :=
    composePullback_eq T0 F ⟨_, hpF⟩ rfl
  have hnorm : ∀ i, c1NormSingleReal D euclidean (realPullback (z i) (G i) (χ i)) =
      c1NormSingleReal D E (χ i) := fun i => by
    have h1 := hVec4.2 _ (hfac i).1 _ (realPullback_mem hcls i (hχ i))
    have h3 := (hcls.2.2 i).2.2 _ h1
    rw [← h3, coe_realPullback hcls i (hχ i), hpp i _ (hχ i)]
    rfl
  unfold Hierarchy.CutoffBound
  rw [hTF]
  refine hb.trans (le_of_eq ?_)
  have hconst : 2 ^ (n : ℕ) * ((80 * D.M) ^ (n : ℕ) *
      C.val (n : ℕ) d (maxMemberDiam D E G).toReal) * cutoffBound n (2 * R) =
      factorBoundBase D.M ^ (n : ℕ) * C.val (n : ℕ) d (maxMemberDiam D E G).toReal *
        cutoffBound n (2 * R) := by
    have : factorBoundBase D.M = 2 * (80 * D.M) := by
      unfold factorBoundBase
      ring
    rw [this, mul_pow 2 (80 * D.M)]
    ring
  rw [hconst, Finset.prod_congr rfl fun i _ => hnorm i, hiso.2.2 F.1 F.2]
end YangMills.Construction.PeriodicSpace.Kind.NonemptyMembersBoxProperties
