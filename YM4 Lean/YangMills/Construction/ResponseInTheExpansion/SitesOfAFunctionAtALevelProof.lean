import YangMills.Construction.LawByMomentsOfTheFlow.PlacesOfTheSitesOfASupportProof
import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOnACircle
import YangMills.Construction.ResponseInTheExpansion.SitesOfAFunctionAtALevel
import YangMills.Construction.ResponseInTheExpansion.SupportsStayApartProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps WeightedResponses FreeEnergies
open LevelTestFunctions (circleRep barycenterCoord)
private abbrev plaqBarycenter {m : ℕ} (p : TorusPlaquette m) : Fin 4 → ℝ := barycenterCoord p
private abbrev sitesAtLevel (L : ℕ) [NeZero L] (t n : ℕ) [NeZero n] (f : FinePlaquetteFunction) :
    Finset (TorusSite n) :=
  weightSupportSites L t n (fineWeight f (fineSide L t n))
private theorem supDist_attained {n : ℕ} (x y : TorusSite n) :
    ∃ i, _root_.YangMills.Construction.TorusFields.supDist x y = ((x i - y i).valMinAbs).natAbs := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨(0 : Fin 4), Finset.mem_univ _⟩
    (fun i => ((x i - y i).valMinAbs).natAbs)
  exact ⟨i, hi⟩
private theorem coord_natAbs_le_supDist {n : ℕ} [NeZero n] (x y : TorusSite n) (i : Fin 4) :
    ((x i - y i).valMinAbs).natAbs ≤ _root_.YangMills.Construction.TorusFields.supDist x y :=
  (_root_.YangMills.Construction.TorusFields.supDist_le_iff x y _).1 le_rfl i
private theorem intCast_mul_eq_of_intCast_eq {N P : ℕ} {M a b : ℤ} (hP : (P : ℤ) = N * M)
    (h : (a : ZMod N) = (b : ZMod N)) :
    ((M * a : ℤ) : ZMod P) = ((M * b : ℤ) : ZMod P) := by apply _root_.YangMills.Construction.BlockAverages.intCast_mul_eq_of_eq <;> assumption
private theorem supDist_fineCentre_parent_le (L : ℕ) [NeZero L] {k : ℕ} (hk : L = 2 * k + 1) (t n : ℕ) [NeZero n]
    (y : TorusSite (n * L)) :
    _root_.YangMills.Construction.TorusFields.supDist (n := fineSide L t (n * L)) (fineCentre L (t + 1) (parentBlock L y)) (fineCentre L t y) ≤ L ^ t * k := by apply _root_.YangMills.SharedProofs.p21417 <;> assumption
private theorem two_mul_supDist_fineCentre_add_one_le (L : ℕ) [NeZero L] (hL : Odd L) :
    (t n : ℕ) → [NeZero n] → (y : TorusSite n) →
    (c : TorusSite (fineSide L t n)) → c ∈ fineBlock L t n y → 2 * _root_.YangMills.Construction.TorusFields.supDist c (fineCentre L t y) + 1 ≤ L ^ t
  | 0, n, _, y, c, hc => by
    have hcy : c = y := Finset.mem_singleton.1 hc
    have hy : (fineCentre L 0 y : TorusSite n) = y := by
      funext i
      show (((L : ℤ) ^ 0 * ((y i).cast : ℤ) : ℤ) : ZMod n) = y i
      rw [pow_zero, one_mul, ZMod.intCast_zmod_cast]
    have h0 : _root_.YangMills.Construction.TorusFields.supDist (n := n) c (fineCentre L 0 y) = 0 := by
      rw [hy, hcy]
      exact _root_.YangMills.Construction.TorusFields.supDist_self y
    change 2 * _root_.YangMills.Construction.TorusFields.supDist (n := n) c (fineCentre L 0 y) + 1 ≤ L ^ 0
    simp [h0]
  | t + 1, n, _, Y, c, hc => by
    obtain ⟨k, hk⟩ := hL
    obtain ⟨y, hy, hcy⟩ := Finset.mem_biUnion.1 hc
    have hY : parentBlock L y = Y := by simpa [sitesInBlocks] using hy
    subst hY
    have ih := two_mul_supDist_fineCentre_add_one_le L ⟨k, hk⟩ t (n * L) y c hcy
    have hstep := supDist_fineCentre_parent_le L hk t n y
    obtain ⟨B, hB⟩ : ∃ B : TorusSite (fineSide L t (n * L)), B = fineCentre L (t + 1) (parentBlock L y) := ⟨_, rfl⟩
    rw [← hB] at hstep
    have htri := _root_.YangMills.Construction.TorusFields.supDist_triangle (n := fineSide L t (n * L)) c (fineCentre L t y) B
    have hcomm := _root_.YangMills.Construction.TorusFields.supDist_comm (n := fineSide L t (n * L)) B (fineCentre L t y)
    have hpow : L ^ (t + 1) = L ^ t + 2 * (L ^ t * k) := by
      rw [pow_succ, hk]
      ring
    change 2 * _root_.YangMills.Construction.TorusFields.supDist (n := fineSide L t (n * L)) c (fineCentre L (t + 1) (parentBlock L y)) + 1 ≤ L ^ (t + 1)
    rw [← hB]
    omega
private theorem supDist_fineCentre_le (L t n : ℕ) [NeZero L] [NeZero n] (y y' : TorusSite n) :
    _root_.YangMills.Construction.TorusFields.supDist (fineCentre L t y) (fineCentre L t y') ≤ L ^ t * _root_.YangMills.Construction.TorusFields.supDist y y' := by apply _root_.YangMills.SharedProofs.p11320 <;> assumption
private theorem le_supDist_fineCentre (L t n : ℕ) [NeZero L] [NeZero n] (y y' : TorusSite n) :
    L ^ t * _root_.YangMills.Construction.TorusFields.supDist y y' ≤ _root_.YangMills.Construction.TorusFields.supDist (fineCentre L t y) (fineCentre L t y') := by
  obtain ⟨i, hi⟩ := supDist_attained y y'
  rw [hi]
  refine le_trans ?_ (coord_natAbs_le_supDist (fineCentre L t y) (fineCentre L t y') i)
  obtain ⟨w, hw⟩ : ∃ w : ℤ, w = (y i - y' i).valMinAbs := ⟨_, rfl⟩
  have hcast : ((((y i).cast : ℤ) - ((y' i).cast : ℤ) : ℤ) : ZMod n) = ((w : ℤ) : ZMod n) := by
    rw [hw, ZMod.coe_valMinAbs]
    push_cast
    simp
  have hscale := intCast_mul_eq_of_intCast_eq (N := n) (P := fineSide L t n) (M := (L : ℤ) ^ t)
    (by rw [fineSide_eq]; push_cast; ring) hcast
  have hdiff : (fineCentre L t y) i - (fineCentre L t y') i =
      (((L : ℤ) ^ t * w : ℤ) : ZMod (fineSide L t n)) := by
    rw [← hscale]
    show (((L : ℤ) ^ t * ((y i).cast : ℤ) : ℤ) : ZMod (fineSide L t n)) -
      (((L : ℤ) ^ t * ((y' i).cast : ℤ) : ℤ) : ZMod (fineSide L t n)) = _
    rw [← Int.cast_sub]
    congr 1
    ring
  have hle : (((L : ℤ) ^ t * w : ℤ)).natAbs ≤ fineSide L t n / 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, fineSide_eq, Nat.le_div_iff_mul_le (by norm_num)]
    have h1 : w.natAbs ≤ n / 2 := by
      rw [hw]
      exact ZMod.natAbs_valMinAbs_le _
    have h2 : w.natAbs * 2 ≤ n := by omega
    calc L ^ t * w.natAbs * 2 = L ^ t * (w.natAbs * 2) := by ring
      _ ≤ L ^ t * n := Nat.mul_le_mul_left _ h2
      _ = n * L ^ t := by ring
  have hmin := ZMod.natAbs_min_of_le_div_two (fineSide L t n) ((L : ℤ) ^ t * w)
    (((fineCentre L t y) i - (fineCentre L t y') i).valMinAbs) (by rw [ZMod.coe_valMinAbs, hdiff]) hle
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at hmin
  rw [← hw]
  exact hmin
private theorem supDist_fineBlock_bounds (L : ℕ) [NeZero L] (hL : Odd L) (t n : ℕ) [NeZero n] {y y' : TorusSite n}
    {c c' : TorusSite (fineSide L t n)} (hc : c ∈ fineBlock L t n y) (hc' : c' ∈ fineBlock L t n y') :
    _root_.YangMills.Construction.TorusFields.supDist c c' + 1 ≤ L ^ t * _root_.YangMills.Construction.TorusFields.supDist y y' + L ^ t ∧ L ^ t * _root_.YangMills.Construction.TorusFields.supDist y y' + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist c c' + L ^ t := by
  have h1 := two_mul_supDist_fineCentre_add_one_le L hL t n y c hc
  have h2 := two_mul_supDist_fineCentre_add_one_le L hL t n y' c' hc'
  have h3 := supDist_fineCentre_le L t n y y'
  have h4 := le_supDist_fineCentre L t n y y'
  have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle c (fineCentre L t y) c'
  have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (fineCentre L t y) (fineCentre L t y') c'
  have t3 := _root_.YangMills.Construction.TorusFields.supDist_triangle (fineCentre L t y) c (fineCentre L t y')
  have t4 := _root_.YangMills.Construction.TorusFields.supDist_triangle c c' (fineCentre L t y')
  have c1 := _root_.YangMills.Construction.TorusFields.supDist_comm c (fineCentre L t y)
  have c2 := _root_.YangMills.Construction.TorusFields.supDist_comm c' (fineCentre L t y')
  constructor <;> omega
abbrev _root_.YangMills.SharedProofs.p19253 := @supDist_fineBlock_bounds
private theorem abs_circleRep_vertex_sub_barycenter_le {m : ℕ} [NeZero m]
    (hper : ∀ (c : ℝ), 0 < c → ∀ (v : ℝ) (e : ℤ), circleRep c (v + c * e) = circleRep c v)
    (hsh : ∀ (c : ℝ), 0 < c → ∀ v : ℝ, |circleRep c v| ≤ |v|) (p : TorusPlaquette m) (hp : p.2.1 < p.2.2)
    (c : TorusSite m) (hc : c ∈ plaquetteVertices p.1 p.2.1 p.2.2) (a : Fin 4) :
    |circleRep m (((c a).val : ℝ) - plaqBarycenter p a)| ≤ 1 / 2 := by apply _root_.YangMills.DeltaSharedProofs.p502487 <;> assumption
private theorem circleRep_barycenter_sub_bounds (hC : LevelTestFunctions.CircleRepProperties) {m : ℕ} [NeZero m]
    (p p' : TorusPlaquette m) (ho : p.2.1 < p.2.2) (ho' : p'.2.1 < p'.2.2) {c c' : TorusSite m}
    (hc : c ∈ plaquetteVertices p.1 p.2.1 p.2.2) (hc' : c' ∈ plaquetteVertices p'.1 p'.2.1 p'.2.2) (q : Fin 4) :
    |circleRep m (plaqBarycenter p q - plaqBarycenter p' q)| ≤ 1 + (((c q - c' q).valMinAbs).natAbs : ℝ) ∧
      (((c q - c' q).valMinAbs).natAbs : ℝ) ≤ 1 + |circleRep m (plaqBarycenter p q - plaqBarycenter p' q)| := by
  obtain ⟨hper, hsh, hsub, hneg, -, -, hsite⟩ := hC
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have h1 := abs_circleRep_vertex_sub_barycenter_le hper hsh p ho c hc q
  have h2 := abs_circleRep_vertex_sub_barycenter_le hper hsh p' ho' c' hc' q
  have h3 := hsite m (c q) (c' q)
  generalize ((c q).val : ℝ) = vc at h1 h3
  generalize ((c' q).val : ℝ) = vc' at h2 h3
  generalize plaqBarycenter p q = x at h1 ⊢
  generalize plaqBarycenter p' q = z at h2 ⊢
  constructor
  · have e : x - z = -(vc - x) + ((vc - vc') + (vc' - z)) := by ring
    rw [e]
    have a1 := hsub _ hm (-(vc - x)) ((vc - vc') + (vc' - z))
    have a2 := hsub _ hm (vc - vc') (vc' - z)
    have a3 := hneg _ hm (vc - x)
    rw [h3] at a2
    linarith
  · have e : vc - vc' = (vc - x) + ((x - z) + -(vc' - z)) := by ring
    rw [← h3, e]
    have a1 := hsub _ hm (vc - x) ((x - z) + -(vc' - z))
    have a2 := hsub _ hm (x - z) (-(vc' - z))
    have a3 := hneg _ hm (vc' - z)
    linarith
private theorem euclidNormVec_le (v : Fin 4 → ℝ) {R : ℝ} (h : ∀ a, |v a| ≤ R) :
    TorusMetric.euclidNormVec v ≤ 2 * R := by
  have hR : 0 ≤ R := (abs_nonneg _).trans (h 0)
  have hs : ∀ a, v a ^ 2 ≤ R ^ 2 := fun a => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h a) 2
  refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
  rw [Fin.sum_univ_four]
  nlinarith [hs 0, hs 1, hs 2, hs 3]
private theorem le_of_mem_sitesAtLevel_pair (hC : LevelTestFunctions.CircleRepProperties) {L t n : ℕ} [NeZero L] [NeZero n]
    (hL : Odd L) (W : ℝ) {f g : FinePlaquetteFunction}
    (hfg : ∀ p p' : OrientedPlaquette (fineSide L t n), f (plaqBarycenter p.1) ≠ 0 → g (plaqBarycenter p'.1) ≠ 0 →
      W ≤ MomentSetup.fineDist (fineSide L t n) (plaqBarycenter p.1) (plaqBarycenter p'.1))
    {a a' : TorusSite n} (ha : a ∈ sitesAtLevel L t n f) (ha' : a' ∈ sitesAtLevel L t n g) :
    W ≤ 2 * ((L : ℝ) ^ t * _root_.YangMills.Construction.TorusFields.supDist a a' + (L : ℝ) ^ t) := by
  classical
  obtain ⟨p, ⟨ho, c, hc, hcb⟩, hne⟩ := (Finset.mem_filter.1 ha).2
  obtain ⟨p', ⟨ho', c', hc', hcb'⟩, hne'⟩ := (Finset.mem_filter.1 ha').2
  have hW := hfg ⟨p, ho⟩ ⟨p', ho'⟩ hne hne'
  have hup : ((_root_.YangMills.Construction.TorusFields.supDist c c' : ℕ) : ℝ) + 1 ≤ (L : ℝ) ^ t * _root_.YangMills.Construction.TorusFields.supDist a a' + (L : ℝ) ^ t := by
    exact_mod_cast (supDist_fineBlock_bounds L hL t n hcb hcb').1
  have hb : ∀ q, |circleRep (fineSide L t n) (plaqBarycenter p q - plaqBarycenter p' q)| ≤
      1 + ((_root_.YangMills.Construction.TorusFields.supDist c c' : ℕ) : ℝ) := fun q => by
    have h1 := (circleRep_barycenter_sub_bounds hC p p' ho ho' hc hc' q).1
    have h2 : (((c q - c' q).valMinAbs).natAbs : ℝ) ≤ ((_root_.YangMills.Construction.TorusFields.supDist c c' : ℕ) : ℝ) := by
      exact_mod_cast coord_natAbs_le_supDist c c' q
    linarith
  have hd := euclidNormVec_le (fun q => circleRep (fineSide L t n) (plaqBarycenter p q - plaqBarycenter p' q)) hb
  have hW' : W ≤ TorusMetric.euclidNormVec
      (fun q => circleRep (fineSide L t n) (plaqBarycenter p q - plaqBarycenter p' q)) := hW
  linarith
private theorem mul_supDist_le_of_mem_sitesAtLevel (hC : LevelTestFunctions.CircleRepProperties) {L t n : ℕ}
    [NeZero L] [NeZero n] (hL : Odd L) (R : ℝ) {f : FinePlaquetteFunction}
    (hb : ∀ p p' : OrientedPlaquette (fineSide L t n), f (plaqBarycenter p.1) ≠ 0 → f (plaqBarycenter p'.1) ≠ 0 →
      ∀ q, |circleRep (fineSide L t n) (plaqBarycenter p.1 q - plaqBarycenter p'.1 q)| ≤ R)
    {a a' : TorusSite n} (ha : a ∈ sitesAtLevel L t n f) (ha' : a' ∈ sitesAtLevel L t n f) :
    (L : ℝ) ^ t * _root_.YangMills.Construction.TorusFields.supDist a a' ≤ R + (L : ℝ) ^ t := by
  classical
  obtain ⟨p, ⟨ho, c, hc, hcb⟩, hne⟩ := (Finset.mem_filter.1 ha).2
  obtain ⟨p', ⟨ho', c', hc', hcb'⟩, hne'⟩ := (Finset.mem_filter.1 ha').2
  have hlow : (L : ℝ) ^ t * _root_.YangMills.Construction.TorusFields.supDist a a' + 1 ≤ ((_root_.YangMills.Construction.TorusFields.supDist c c' : ℕ) : ℝ) + (L : ℝ) ^ t := by
    exact_mod_cast (supDist_fineBlock_bounds L hL t n hcb hcb').2
  obtain ⟨q, hq⟩ := supDist_attained c c'
  have h1 := (circleRep_barycenter_sub_bounds hC p p' ho ho' hc hc' q).2
  have h2 := hb ⟨p, ho⟩ ⟨p', ho'⟩ hne hne' q
  have h3 : ((_root_.YangMills.Construction.TorusFields.supDist c c' : ℕ) : ℝ) = (((c q - c' q).valMinAbs).natAbs : ℝ) := by rw [hq]
  linarith
private theorem card_le_of_supDist_le {N : ℕ} [NeZero N] {A : Finset (TorusSite N)} {R : ℕ}
    (h : ∀ a ∈ A, ∀ a' ∈ A, _root_.YangMills.Construction.TorusFields.supDist a a' ≤ R) :
    A.card ≤ (2 * R + 1) ^ 4 := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | ⟨a₀, h₀⟩
  · simp
  · refine le_trans (Finset.card_le_card fun a ha => ?_) (TorusCounting.card_thickening_singleton_le R a₀)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, a₀, Finset.mem_singleton_self _, h a ha a₀ h₀⟩
theorem levelSitesStatement_holds (hC : LevelTestFunctions.CircleRepProperties) :
    levelSitesStatement := by
  intro L _ hL t n _
  refine ⟨fun f g W hfg a ha a' ha' => le_of_mem_sitesAtLevel_pair hC hL W hfg ha ha',
    fun f R hb a ha a' ha' => mul_supDist_le_of_mem_sitesAtLevel hC hL R hb ha ha',
    fun A R h => card_le_of_supDist_le h⟩
end YangMills.Construction.ResponseInTheExpansion
end
