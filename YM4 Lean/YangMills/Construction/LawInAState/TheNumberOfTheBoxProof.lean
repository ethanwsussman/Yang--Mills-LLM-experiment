import YangMills.Construction.LawInAState.DecayOverATorus
import YangMills.Construction.LawInAState.PairMovedByAVector
import YangMills.Construction.LawInAState.PairOfTheLawIsNearAPoint
import YangMills.Construction.LawInAState.SitesOfAPair
import YangMills.Construction.LawInAState.TheCouplingOfTheLevelGrows
import YangMills.Construction.LawInAState.TheLevelOfTheLaw
import YangMills.Construction.LawInAState.TheNumberOfTheBox
import YangMills.Construction.LawInAState.TraceOfOnePair
import YangMills.Construction.LawOnABoxOfTheFlow.BoundsOfTheCurlKernel
import YangMills.Construction.LawOnABoxOfTheFlow.KernelOfTheCurlOnABox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BoxMarks
open TorusFields TorusLumps RenormalizationStepParameters StepSettings WeightedResponses ResponseInTheExpansion BoxGaussian
open StateLaws TraceBounds BoxResponses CellAverages ReflectionKernel LimitForms TorusSums
open InfiniteLattice (AmbientSpace)
private theorem kernel_entry_abs_le {a : ℝ} {L k : ℕ} {n : ℕ} [NeZero n] {o : TorusSite n} {R : ℕ} {c : ℝ}
    (hsym : ∀ p p' : TorusPlaquette n, curlCovariance a L k o R p p' = curlCovariance a L k o R p' p)
    (hV : ∀ u : TorusPlaquette n → Fin 3 → ℝ, 0 ≤ curlQuadForm a L k o R u ∧
      curlQuadForm a L k o R u ≤ c * ∑ e : Fin 3, ∑ p ∈ plaquettesIn (supBall o (2 * R)), u p e ^ 2)
    {p p' : TorusPlaquette n} (hp : p ∈ plaquettesIn (supBall o (2 * (R : ℝ))))
    (hp' : p' ∈ plaquettesIn (supBall o (2 * (R : ℝ)))) :
    |curlCovariance a L k o R p p'| ≤ c := by
  classical
  set P := plaquettesIn (supBall o (2 * (R : ℝ))) with hP
  set T := curlCovariance a L k o R with hT
  have hval : ∀ w : TorusPlaquette n → ℝ, curlQuadForm a L k o R (fun q e => if e = 0 then w q else 0) =
      ∑ q ∈ P, ∑ q' ∈ P, w q * T q q' * w q' := by
    intro w
    simp only [curlQuadForm, Fin.sum_univ_three]
    simp
    rfl
  have hsq : ∀ w : TorusPlaquette n → ℝ, ∑ e : Fin 3, ∑ q ∈ P, (if e = 0 then w q else 0) ^ 2 = ∑ q ∈ P, w q ^ 2 := by
    intro w
    simp [Fin.sum_univ_three]
  have hlin : ∀ (s : ℝ) (g : TorusPlaquette n → ℝ), ∑ q ∈ P, ((if q = p then 1 else 0) + s * (if q = p' then 1 else 0)) * g q =
      g p + s * g p' := by
    intro s g
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' P p, Finset.sum_ite_eq' P p', if_pos hp, if_pos hp']
  have hquad : ∀ s : ℝ, ∑ q ∈ P, ∑ q' ∈ P, ((if q = p then 1 else 0) + s * (if q = p' then 1 else 0)) * T q q' *
      ((if q' = p then 1 else 0) + s * (if q' = p' then 1 else 0)) =
      T p p + s * T p p' + s * (T p' p + s * T p' p') := by
    intro s
    have h1 : ∀ q, ∑ q' ∈ P, ((if q = p then 1 else 0) + s * (if q = p' then 1 else 0)) * T q q' *
        ((if q' = p then 1 else 0) + s * (if q' = p' then 1 else 0)) =
        ((if q = p then 1 else 0) + s * (if q = p' then 1 else 0)) * (T q p + s * T q p') := by
      intro q
      have := hlin s (T q)
      rw [← this, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q' _ => by ring
    simp only [h1]
    exact hlin s fun q => T q p + s * T q p'
  have hdiag : ∀ r ∈ P, T r r ≤ c := by
    intro r hr
    have h1 := (hV fun q e => if e = 0 then (if q = r then 1 else 0) else 0).2
    rw [hval, hsq] at h1
    have h2 : ∑ q ∈ P, ∑ q' ∈ P, (if q = r then (1 : ℝ) else 0) * T q q' * (if q' = r then 1 else 0) = T r r := by
      have h3 : ∀ q, ∑ q' ∈ P, (if q = r then (1 : ℝ) else 0) * T q q' * (if q' = r then 1 else 0) =
          (if q = r then 1 else 0) * T q r := by
        intro q
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' P r, if_pos hr]
      calc _ = ∑ q ∈ P, (if q = r then (1 : ℝ) else 0) * T q r := Finset.sum_congr rfl fun q _ => h3 q
        _ = T r r := by
          simp only [ite_mul, one_mul, zero_mul]
          rw [Finset.sum_ite_eq' P r, if_pos hr]
    have h4 : ∑ q ∈ P, (if q = r then (1 : ℝ) else 0) ^ 2 = 1 := by
      simp only [ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      rw [Finset.sum_ite_eq' P r, if_pos hr]
    rw [h2, h4, mul_one] at h1
    exact h1
  have hpos : ∀ s : ℝ, 0 ≤ T p p + s * T p p' + s * (T p' p + s * T p' p') := by
    intro s
    have h1 := (hV fun q e => if e = 0 then ((if q = p then 1 else 0) + s * (if q = p' then 1 else 0)) else 0).1
    rw [hval, hquad] at h1
    exact h1
  have h1 := hpos 1
  have h2 := hpos (-1)
  have h3 := hdiag p hp
  have h4 := hdiag p' hp'
  have h5 : T p' p = T p p' := hsym p' p
  rw [h5] at h1 h2
  rw [abs_le]
  constructor <;> linarith
private theorem weighted_kernel_sum_le {N : ℕ} [NeZero N] {S c₁ C₁ : ℝ} (hc₁ : 0 < c₁) (hC₁ : 0 ≤ C₁)
    (hS : ∀ y : TorusSite N, ∑ s : TorusSite N, Real.exp (-(c₁ / 2 * (supDist s y : ℝ))) * (1 + (supDist s y : ℝ)) ^ 5 ≤ S)
    (k : TorusPlaquette N → TorusPlaquette N → ℝ) (y : TorusSite N)
    (hdec : ∀ p p', |k p p'| ≤ C₁ * Real.exp (-(c₁ * max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ))))
    (Q : Finset (TorusPlaquette N)) :
    ∑ p ∈ Q, ∑ p' ∈ Q, |k p p'| * (siteWeight y p * siteWeight y p') ≤ C₁ * (16 * S) ^ 2 := by
  set g : TorusPlaquette N → ℝ := fun p => Real.exp (-(c₁ / 2 * (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ))) * (1 + (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ)) ^ 5 with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => by
    have : (0 : ℝ) ≤ supDist p.1 y := Nat.cast_nonneg _
    simp only [hg]
    positivity
  have hW0 : ∀ p, 0 ≤ siteWeight y p := fun p => by
    have : (0 : ℝ) ≤ supDist p.1 y := Nat.cast_nonneg _
    unfold siteWeight
    positivity
  have hpt : ∀ p p', |k p p'| * (siteWeight y p * siteWeight y p') ≤ C₁ * (g p * g p') := by
    intro p p'
    have h1 := hdec p p'
    have h2 : Real.exp (-(c₁ * max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ))) ≤
        Real.exp (-(c₁ / 2 * (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ))) * Real.exp (-(c₁ / 2 * (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ))) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have m1 := le_max_left (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ)
      have m2 := le_max_right (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ)
      nlinarith
    calc _ ≤ (C₁ * (Real.exp (-(c₁ / 2 * (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ))) * Real.exp (-(c₁ / 2 * (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ))))) *
          (siteWeight y p * siteWeight y p') :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 hC₁)) (mul_nonneg (hW0 _) (hW0 _))
      _ = _ := by simp only [hg, siteWeight]; ring
  have hsum : ∑ p ∈ Q, g p ≤ 16 * S := by
    calc ∑ p ∈ Q, g p ≤ ∑ p : TorusPlaquette N, g p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => hg0 p
      _ = ∑ s : TorusSite N, ∑ _q : Fin 4 × Fin 4, Real.exp (-(c₁ / 2 * (_root_.YangMills.Construction.TorusFields.supDist s y : ℝ))) * (1 + (_root_.YangMills.Construction.TorusFields.supDist s y : ℝ)) ^ 5 := by
          rw [Fintype.sum_prod_type]
      _ = 16 * ∑ s : TorusSite N, Real.exp (-(c₁ / 2 * (_root_.YangMills.Construction.TorusFields.supDist s y : ℝ))) * (1 + (_root_.YangMills.Construction.TorusFields.supDist s y : ℝ)) ^ 5 := by
          simp [Finset.mul_sum]
      _ ≤ _ := by linarith [hS y]
  have hsum0 : 0 ≤ ∑ p ∈ Q, g p := Finset.sum_nonneg fun p _ => hg0 p
  calc _ ≤ ∑ p ∈ Q, ∑ p' ∈ Q, C₁ * (g p * g p') := Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun p' _ => hpt p p'
    _ = C₁ * (∑ p ∈ Q, g p) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum0 hsum 2) hC₁
private theorem flowCoupling_le_pow {Tb : ParameterAssignment} {y β : ℝ} {T : StageTower (Tb.stepParameters y)} {K : ℕ}
    (hs : IsTowerAtParameters Tb y T β (K - 1)) (hK : 1 ≤ K) (e : ℕ) (k : ℕ) (hek : k + e = K) :
    flowCouplings (Tb.stepParameters y) β k ≤ (1.01 : ℝ) ^ e * flowCouplings (Tb.stepParameters y) β K := by
  induction e generalizing k with
  | zero =>
    have : k = K := by omega
    subst this
    simp
  | succ e ih =>
    have hk1 : k ≤ K - 1 := by omega
    have h1 := ih (k + 1) (by omega)
    have h2 : (T.stage k).coupling ≤ 1.01 * (T.stage k).nextCoupling := (hs.onFamily k hk1).isStep.2.1
    have h3 : (T.stage k).coupling = flowCouplings (Tb.stepParameters y) β k := hs.coupling_eq k (by omega)
    have h4 : (T.stage (k + 1)).coupling = flowCouplings (Tb.stepParameters y) β (k + 1) := hs.coupling_eq (k + 1) (by omega)
    have h5 : (T.stage (k + 1)).coupling = (T.stage k).nextCoupling := rfl
    rw [h3, ← h5, h4] at h2
    calc _ ≤ 1.01 * flowCouplings (Tb.stepParameters y) β (k + 1) := h2
      _ ≤ 1.01 * ((1.01 : ℝ) ^ e * flowCouplings (Tb.stepParameters y) β K) := by linarith
      _ = _ := by ring
private theorem lengthInSites_eq_div {L K k : ℕ} [NeZero L] (hk : k ≤ K) (d : ℝ) :
    lengthInSites L K k d = d / ((L : ℝ) ^ k / (L : ℝ) ^ K) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h1 : (L : ℝ) ^ (K - k) * (L : ℝ) ^ k = (L : ℝ) ^ K := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  simp only [lengthInSites]
  field_simp
  rw [mul_assoc, h1]
private theorem siteKernelFamily_of_weightKernel {L k : ℕ} [NeZero L] {N : ℕ} [NeZero N] {o : TorusSite N}
    {n al C₁ c₁ err errp S : ℝ} {R : ℕ}
    {w : PlaquetteWeight (fineSide L k N)} {κ : TorusSite N → TorusPlaquette N → TorusPlaquette N → ℝ} (hc₁ : 0 < c₁)
    (hS : ∀ y : TorusSite N, ∑ s : TorusSite N, Real.exp (-(c₁ / 2 * (supDist s y : ℝ))) * (1 + (supDist s y : ℝ)) ^ 5 ≤ S)
    (hnear : weightSupportSites L k N w ⊆ supBall o ((R : ℝ) / 8 - n))
    (hcard : ((sitesWithinTwo (weightSupportSites L k N w)).card : ℝ) ≤ (15 * n) ^ 4)
    (hzero : ∀ y, y ∉ weightSupportSites L k N w → blockMean L k N y w = 0)
    (hκ : IsWeightKernel L k al C₁ c₁ err w κ) (herr : err ≤ errp) :
    IsSiteKernelFamily o n R (|C₁| * (16 * S) ^ 2) errp (sitesWithinTwo (weightSupportSites L k N w)) κ
      (fun y => al * blockMean L k N y w) := by
  classical
  have hself : ∀ y, y ∉ sitesWithinTwo (weightSupportSites L k N w) → y ∉ weightSupportSites L k N w := fun y hy hs =>
    hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hs, by simp [_root_.YangMills.Construction.TorusFields.supDist_self]⟩)
  refine ⟨fun y hy => ?_, hcard, fun y hy p p' => ?_, fun y hy => ?_, fun y _ => ?_, fun y _ A hA B hB => ?_⟩
  · obtain ⟨-, z, hz, hd⟩ := Finset.mem_filter.mp hy
    have h1 : (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ) ≤ (R : ℝ) / 8 - n := (Finset.mem_filter.mp (hnear hz)).2
    have h2 : _root_.YangMills.Construction.TorusFields.supDist y o ≤ _root_.YangMills.Construction.TorusFields.supDist y z + _root_.YangMills.Construction.TorusFields.supDist z o := _root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _
    have h3 : (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ) := by exact_mod_cast h2
    have h4 : (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) ≤ 2 := by exact_mod_cast hd
    linarith
  · refine hκ.vanish_far y (fun z hz => ?_) p p'
    by_contra hcon
    push_neg at hcon
    exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hz, hcon⟩)
  · simp only [hzero y (hself y hy), mul_zero]
  · refine weighted_kernel_sum_le hc₁ (abs_nonneg C₁) hS (κ y) y (fun p p' => ?_) _
    exact (hκ.decay y p p').trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  · have hA' : A.1 < A.2 := (Finset.mem_filter.mp hA).2
    have hB' : B.1 < B.2 := (Finset.mem_filter.mp hB).2
    have := hκ.plane_sums y A.1 A.2 B.1 B.2 hA' hB'
    simp only [Prod.mk.eta] at this
    exact this.trans herr
private theorem translated_pair_trace_bound (hTrace : PairTraceApprox) (hSites : pairSitesStatement) {L K k : ℕ} [NeZero L]
    (hodd : Odd L) (hk : k ≤ K) {c : AmbientSpace} {d Λ n al C₁ c₁ err errp S Ck cT : ℝ} {R : ℕ}
    {o : TorusSite (boxSide L K k)}
    {T : TorusPlaquette (boxSide L K k) → TorusPlaquette (boxSide L K k) → ℝ} {f h : AmbientSpace → ℝ}
    {κ κ' : TorusSite (boxSide L K k) → TorusPlaquette (boxSide L K k) → TorusPlaquette (boxSide L K k) → ℝ}
    (hp : IsLocalizedLipschitzPair c d Λ f h) (hd : 0 < d) (hd1 : d ≤ 1 / 100)
    (ha64 : 64 * ((L : ℝ) ^ k / (L : ℝ) ^ K) ≤ d)
    (hn : n = d / ((L : ℝ) ^ k / (L : ℝ) ^ K)) (hn64 : 64 ≤ n) (hN : 64 * n ≤ (boxSide L K k : ℕ)) (hR8 : 8 ≤ R)
    (herr0 : 0 ≤ errp) (hc₁ : 0 < c₁)
    (hS0 : 0 ≤ S)
    (hS : ∀ y : TorusSite (boxSide L K k), ∑ s : TorusSite (boxSide L K k),
      Real.exp (-(c₁ / 2 * (_root_.YangMills.Construction.TorusFields.supDist s y : ℝ))) * (1 + (_root_.YangMills.Construction.TorusFields.supDist s y : ℝ)) ^ 5 ≤ S)
    (hTn : ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 8)), ∀ p' ∈ plaquettesIn (supBall o ((R : ℝ) / 8)),
      ∀ z : Fin 4 → ℤ, (∀ i, z i = ((p.1 - p'.1) i).valMinAbs) → z ≠ 0 →
        |T p p' - maxwellKernel z p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
          Ck * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ + Ck * ((R : ℝ) ^ 4)⁻¹)
    (hTb : ∀ p ∈ plaquettesIn (supBall o (2 * (R : ℝ))), ∀ p' ∈ plaquettesIn (supBall o (2 * (R : ℝ))), |T p p'| ≤ cT)
    (hsym : ∀ p p', T p p' = T p' p)
    (hf : weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k f) ⊆ supBall o ((R : ℝ) / 8 - n))
    (hh : weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k h) ⊆ supBall o ((R : ℝ) / 8 - n))
    (hκ : IsWeightKernel L k al C₁ c₁ err (unitTorusWeight L K k f) κ)
    (hκ' : IsWeightKernel L k al C₁ c₁ err (unitTorusWeight L K k h) κ') (herr : err ≤ errp) :
    |∑ p₁ ∈ plaquettesIn (supBall o (2 * (R : ℝ))), ∑ p₂ ∈ plaquettesIn (supBall o (2 * (R : ℝ))),
        ∑ p₃ ∈ plaquettesIn (supBall o (2 * (R : ℝ))), ∑ p₄ ∈ plaquettesIn (supBall o (2 * (R : ℝ))),
        (∑ y, κ y p₁ p₂) * T p₂ p₃ * (∑ z, κ' z p₃ p₄) * T p₄ p₁ -
      6 / Real.pi ^ 4 * (al ^ 2 * blockMeanKernelSum L K k f h)| ≤
    pairTraceBound n R (1024 * |Ck| + 192000 + (|cT| + 1) * 16 ^ 5) (|C₁| * (16 * S) ^ 2) errp := by
  obtain ⟨z₁, z₂, c₁', c₂', hpair⟩ := hSites L hodd K k hk c d Λ f h hp hd hd1 ha64
  rw [← hn] at c₁' c₂' hpair
  have htr := hTrace T Ck cT n errp (|C₁| * (16 * S) ^ 2) R o _ _ κ κ'
    (fun y => al * blockMean L k (boxSide L K k) y (unitTorusWeight L K k f))
    (fun y => al * blockMean L k (boxSide L K k) y (unitTorusWeight L K k h)) hn64 hN hR8 herr0 (by positivity) hTn hTb hsym
    (siteKernelFamily_of_weightKernel hc₁ hS hf c₁' z₁ hκ herr) (siteKernelFamily_of_weightKernel hc₁ hS hh c₂' z₂ hκ' herr) hpair
  have e : 6 / Real.pi ^ 4 * (al ^ 2 * blockMeanKernelSum L K k f h) =
      6 / Real.pi ^ 4 * ∑ y, ∑ z, al * blockMean L k (boxSide L K k) y (unitTorusWeight L K k f) *
        (al * blockMean L k (boxSide L K k) z (unitTorusWeight L K k h)) *
        (normSq (fun i => (minimalSiteDiff y z i : ℝ)) ^ 4)⁻¹ := by
    congr 1
    unfold blockMeanKernelSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  rw [e]
  exact htr
private theorem relative_error_exists {Num Kf al x D B H κ₀ : ℝ} (hal : 3 / 4 ≤ al) (hK : κ₀ ≤ Kf) (hκ : 0 < κ₀)
    (hx : x ≠ 0) (hB : 0 ≤ B) (hH : 0 ≤ H) (hN : Num = 3 / 2 * (x ^ 2)⁻¹ * (6 / Real.pi ^ 4 * (al ^ 2 * Kf) + D))
    (hD : |D| ≤ B + 6 / Real.pi ^ 4 * (al ^ 2 * H)) :
    ∃ ε : ℝ, |ε| ≤ 30 * B / κ₀ + H / κ₀ ∧ Num = al ^ 2 * (9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * Kf * (1 + ε) := by
  have hKf : 0 < Kf := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hp4 : Real.pi ^ 4 ≤ 100 := by
    have h1 := Real.pi_lt_d2
    have h2 : Real.pi ^ 2 ≤ 10 := by nlinarith
    nlinarith [sq_nonneg (Real.pi ^ 2)]
  set D₀ : ℝ := 6 / Real.pi ^ 4 * al ^ 2 with hD₀
  have hD₀0 : 1 / 30 ≤ D₀ := by
    have h1 : 6 / 100 ≤ 6 / Real.pi ^ 4 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hp4
    have h2 : (3 / 4 : ℝ) ^ 2 ≤ al ^ 2 := pow_le_pow_left₀ (by norm_num) hal 2
    rw [hD₀]
    nlinarith
  have hD₀p : 0 < D₀ := by linarith
  refine ⟨D / (D₀ * Kf), ?_, ?_⟩
  · rw [abs_div, abs_of_pos (by positivity : 0 < D₀ * Kf), div_le_iff₀ (by positivity)]
    have e1 : 6 / Real.pi ^ 4 * (al ^ 2 * H) = D₀ * H := by rw [hD₀]; ring
    rw [e1] at hD
    have h1 : B ≤ 30 * B / κ₀ * (D₀ * Kf) := by
      have : κ₀ / 30 ≤ D₀ * Kf := by nlinarith
      calc B = 30 * B / κ₀ * (κ₀ / 30) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
    have h2 : D₀ * H ≤ H / κ₀ * (D₀ * Kf) := by
      have : H ≤ H / κ₀ * Kf := by
        calc H = H / κ₀ * κ₀ := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hK (by positivity)
      calc D₀ * H ≤ D₀ * (H / κ₀ * Kf) := mul_le_mul_of_nonneg_left this hD₀p.le
        _ = _ := by ring
    nlinarith
  · rw [hN, hD₀]
    field_simp
    ring
private theorem shiftAverage_eq {m : ℕ} (c₀ b x : ℝ) (tr : (Fin 4 → ℤ) → ℝ) (hb : ∀ v ∈ shiftSet m, |tr v - c₀| ≤ b) :
    ∃ D : ℝ, |D| ≤ b ∧ shiftAverage m (fun v => 3 / 2 * (x ^ 2)⁻¹ * tr v) = 3 / 2 * (x ^ 2)⁻¹ * (c₀ + D) := by
  have h0 : (0 : Fin 4 → ℤ) ∈ shiftSet m := by
    refine Fintype.mem_piFinset.mpr fun i => ?_
    simp
  have hc : 0 < ((shiftSet m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨_, h0⟩
  refine ⟨shiftAverage m fun v => tr v - c₀, ?_, ?_⟩
  · unfold shiftAverage
    rw [abs_mul, abs_of_pos (inv_pos.mpr hc), inv_mul_le_iff₀ hc]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _v ∈ shiftSet m, b := Finset.sum_le_sum hb
      _ = _ := by simp
  · unfold shiftAverage
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
    ring
private theorem scale_sizes {x w₀ Lr n : ℝ} {R r : ℕ} (hw8 : 8 ≤ w₀) (hLr : 1 ≤ Lr) (hwL : 2 ^ 14 * Lr ≤ w₀)
    (hx : w₀ ^ 2700 ≤ x) (hR : R = ⌈x ^ ((1 : ℝ) / 27)⌉₊) (hr : r = ⌈x ^ ((1 : ℝ) / 100)⌉₊)
    (hn1 : 2 ^ 12 * (r : ℝ) ≤ n) (hn2 : n ≤ 2 ^ 13 * Lr * r) :
    w₀ ≤ (R : ℝ) ∧ 64 ≤ n ∧ w₀ ≤ n ∧ n ≤ R ∧ (R : ℝ) < 2 * x ^ ((1 : ℝ) / 27) ∧ w₀ ≤ x ^ ((1 : ℝ) / 27) ∧
      n ^ 4 * ((R : ℝ) ^ 4)⁻¹ ≤ (2 ^ 14 * Lr) ^ 4 * x ^ (-(1 / 130) : ℝ) := by
  have hx1 : 1 ≤ x := (one_le_pow₀ (by linarith)).trans hx
  have hx0 : 0 ≤ x := by linarith
  set w : ℝ := x ^ ((1 : ℝ) / 2700) with hw
  have hww : w₀ ≤ w := by
    have h1 : (w₀ ^ 2700) ^ ((1 : ℝ) / 2700) ≤ w := Real.rpow_le_rpow (by positivity) hx (by norm_num)
    have h2 : (w₀ ^ 2700) ^ ((1 : ℝ) / 2700) = w₀ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rwa [h2] at h1
  have hw1 : 1 ≤ w := by linarith
  have ht : x ^ ((1 : ℝ) / 27) = w ^ 100 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hs : x ^ ((1 : ℝ) / 100) = w ^ 27 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  rw [ht] at hR ⊢
  rw [hs] at hr
  have hR1 : w ^ 100 ≤ (R : ℝ) := by rw [hR]; exact Nat.le_ceil _
  have hR2 : (R : ℝ) < w ^ 100 + 1 := by
    rw [hR]
    exact Nat.ceil_lt_add_one (by positivity)
  have hr1 : w ^ 27 ≤ (r : ℝ) := by rw [hr]; exact Nat.le_ceil _
  have hr2 : (r : ℝ) < w ^ 27 + 1 := by
    rw [hr]
    exact Nat.ceil_lt_add_one (by positivity)
  have hw27 : w ≤ w ^ 27 := by
    calc w = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ 27 := pow_le_pow_right₀ hw1 (by norm_num)
  have hr3 : (r : ℝ) ≤ 2 * w ^ 27 := by linarith
  have hn3 : n ≤ 2 ^ 14 * Lr * w ^ 27 := by
    have : 2 ^ 13 * Lr * (r : ℝ) ≤ 2 ^ 13 * Lr * (2 * w ^ 27) := mul_le_mul_of_nonneg_left hr3 (by positivity)
    linarith
  have hn4 : n ≤ w ^ 28 := by
    have : 2 ^ 14 * Lr * w ^ 27 ≤ w * w ^ 27 := mul_le_mul_of_nonneg_right (hwL.trans hww) (by positivity)
    calc n ≤ _ := hn3
      _ ≤ w * w ^ 27 := this
      _ = _ := by ring
  have hnR : n ≤ R := by
    have : w ^ 28 ≤ w ^ 100 := pow_le_pow_right₀ hw1 (by norm_num)
    linarith
  have hn64 : 64 ≤ n := by
    have : 1 ≤ (r : ℝ) := by linarith
    linarith
  have hnw : w₀ ≤ n := by
    have : (r : ℝ) ≤ 2 ^ 12 * r := by
      have : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
      linarith
    linarith
  refine ⟨by linarith, hn64, hnw, hnR, ?_, by linarith, ?_⟩
  · have : 1 ≤ w ^ 100 := by linarith
    linarith [hR2]
  · have hn0 : 0 ≤ n := by linarith
    have hRp : 0 < (R : ℝ) := by
      have : 0 < w ^ 100 := by positivity
      linarith
    have hnp : n ^ 4 ≤ (2 ^ 14 * Lr) ^ 4 * w ^ 108 := by
      calc n ^ 4 ≤ (2 ^ 14 * Lr * w ^ 27) ^ 4 := pow_le_pow_left₀ hn0 hn3 4
        _ = _ := by ring
    have hRq : ((R : ℝ) ^ 4)⁻¹ ≤ (w ^ 400)⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      calc w ^ 400 = (w ^ 100) ^ 4 := by ring
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hR1 4
    have hw292 : (w ^ 292)⁻¹ ≤ x ^ (-(1 / 130) : ℝ) := by
      have e : (w ^ 292)⁻¹ = x ^ (-(292 / 2700) : ℝ) := by
        rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0, Real.rpow_neg hx0]
        norm_num
      rw [e]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    calc n ^ 4 * ((R : ℝ) ^ 4)⁻¹ ≤ ((2 ^ 14 * Lr) ^ 4 * w ^ 108) * (w ^ 400)⁻¹ :=
          mul_le_mul hnp hRq (by positivity) (by positivity)
      _ = (2 ^ 14 * Lr) ^ 4 * (w ^ 292)⁻¹ := by
          have hw0 : w ≠ 0 := by linarith
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hw292 (by positivity)
private theorem sixteen_radius_lt_boxSide {Tb : ParameterAssignment} {y β Xi x : ℝ} {T : StageTower (Tb.stepParameters y)}
    {K k R : ℕ}
    (hs : IsTowerAtParameters Tb y T β (K - 1)) (hdat : IsFlowDatum (Tb.stepParameters y) Xi K β) (hkK : k < K)
    (hx : flowCouplings (Tb.stepParameters y) β k = x) (hL : (2 : ℝ) ≤ Tb.side) (ht8 : 8 ≤ x ^ ((1 : ℝ) / 27))
    (ht : 16 * Xi ≤ x ^ ((1 : ℝ) / 27)) (hRt : (R : ℝ) < 2 * x ^ ((1 : ℝ) / 27)) (hx0 : 0 ≤ x) :
    16 * R < boxSide (Tb.stepParameters y).side K k := by
  obtain ⟨e, he⟩ : ∃ e, k + e = K := ⟨K - k, by omega⟩
  have hc := flowCoupling_le_pow hs (by omega) e k he
  have htop := hdat.coupling_le_top
  rw [hx] at hc
  set t : ℝ := x ^ ((1 : ℝ) / 27) with htd
  have ht27 : t ^ 27 = x := by
    rw [htd, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hp : (0 : ℝ) < (1.01 : ℝ) ^ e := by positivity
  have hxX : x ≤ (1.01 : ℝ) ^ e * Xi := hc.trans (mul_le_mul_of_nonneg_left htop hp.le)
  have hxpos : 0 < x := by
    rw [← ht27]
    positivity
  have hXi : 0 < Xi := by
    by_contra hcon
    push_neg at hcon
    have : (1.01 : ℝ) ^ e * Xi ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le hcon
    linarith
  have hLe : (1.01 : ℝ) ^ e ≤ (Tb.side : ℝ) ^ e := pow_le_pow_left₀ (by norm_num) (by linarith) e
  have h1 : t * t ≤ x := by
    rw [← ht27]
    have : t ^ 2 ≤ t ^ 27 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have h2 : 16 * t * Xi ≤ (Tb.side : ℝ) ^ e * Xi := by
    have k1 : 16 * Xi * t ≤ t * t := mul_le_mul_of_nonneg_right ht (by linarith)
    have k2 : (1.01 : ℝ) ^ e * Xi ≤ (Tb.side : ℝ) ^ e * Xi := mul_le_mul_of_nonneg_right hLe hXi.le
    nlinarith
  have h3 : 16 * t ≤ (Tb.side : ℝ) ^ e := le_of_mul_le_mul_right h2 hXi
  have hKk : K - k = e := by omega
  have hside : ((boxSide (Tb.stepParameters y).side K k : ℕ) : ℝ) = 2 * (Tb.side : ℝ) ^ e := by
    simp only [boxSide, hKk]
    push_cast
    rfl
  have h4 : ((16 * R : ℕ) : ℝ) < ((boxSide (Tb.stepParameters y).side K k : ℕ) : ℝ) := by
    rw [hside]
    push_cast
    linarith
  exact_mod_cast h4
set_option maxHeartbeats 8000000 in
theorem boxCoefficientStatement_holds (hK : curlCovarianceNearMaxwellStatement) (hB : curlCovarianceBoundsStatement)
    (hLv : separationLevelStatement) (hGr : couplingAtSeparation_tendsto_statement)
    (hPair : normalizedPairLocalizedStatement) (hMv : localizedPairTranslateStatement)
    (hSites : pairSitesStatement) (hHats : blockMeanSumApproxKernelStatement)
    (hTrace : PairTraceApprox) (hDec : ExpDecaySumBounded)
    (hSize : PairTraceBoundIsSmall) : boxCoefficientStatement := by
  intro a ha
  obtain ⟨L₁, rt₁, hrt₁, h₁⟩ := hK a ha
  obtain ⟨L₂, rt₂, C₂, hrt₂, h₂⟩ := hLv a ha
  obtain ⟨L₃, rt₃, C₃, hrt₃, h₃⟩ := hGr a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (rt₁ c) (min (rt₂ c) (rt₃ c)), max C₂ C₃,
    fun c => lt_min (hrt₁ c) (lt_min (hrt₂ c) (hrt₃ c)), ?_⟩
  intro L hL hLf Tb hTa hTL hTd hTc hTh hTr hTC Kr
  obtain ⟨y₁, g₁⟩ := h₁ L hL (le_trans (le_max_left _ _) hLf) Tb hTa hTL hTd (hTr.trans (min_le_left _ _))
  obtain ⟨y₂, g₂⟩ := h₂ L hL (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLf) Tb hTa hTL hTd hTc hTh
    (hTr.trans ((min_le_right _ _).trans (min_le_left _ _))) (le_trans (le_max_left _ _) hTC)
  obtain ⟨y₃, g₃⟩ := h₃ L hL (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLf) Tb hTa hTL hTd hTc hTh
    (hTr.trans ((min_le_right _ _).trans (min_le_right _ _))) (le_trans (le_max_right _ _) hTC)
  refine ⟨max y₁ (max y₂ y₃), fun y hy hRS hKr Xi hXi vt hvt hvt1 => ?_⟩
  have hret := hRS.returns_at
  have hwil := hRS.wilson_expansion
  have e₁ := g₁ y (le_trans (le_max_left _ _) hy) hret hwil
  have e₂ := g₂ y (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy) hret hwil
  have e₃ := g₃ y (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy) hret hwil
  intro C₁ c₁ hc₁
  obtain ⟨Ck, R₁, hCk⟩ := e₁
  obtain ⟨R₂, hbd⟩ := hB Tb hTd
  obtain ⟨S, hS0, hS⟩ := hDec (c₁ / 2) (by positivity)
  have hcK : 0 < Tb.coercivity := hTd.cK_pos
  obtain ⟨cT, hcT⟩ : ∃ cT : ℝ, cT = (2 * Tb.coercivity)⁻¹ := ⟨_, rfl⟩
  obtain ⟨c₄, hc₄⟩ : ∃ c₄ : ℝ, c₄ = 1024 * |Ck| + 192000 + (|cT| + 1) * 16 ^ 5 := ⟨_, rfl⟩
  have hc₄0 : 0 ≤ c₄ := by rw [hc₄]; positivity
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, M₀ = |C₁| * (16 * S) ^ 2 := ⟨_, rfl⟩
  have hM₀0 : 0 ≤ M₀ := by rw [hM₀]; positivity
  obtain ⟨A, hA0, hA⟩ := hSize c₄ M₀ |C₁| c₁ vt hc₄0 hM₀0 (abs_nonneg _) hc₁ hvt
  obtain ⟨CH, hCH0, hCH⟩ := hHats
  have hL40 : (2 : ℝ) ^ 40 ≤ Tb.side := by exact_mod_cast hTd.L_ge
  obtain ⟨Lr, hLr⟩ : ∃ Lr : ℝ, Lr = (Tb.side : ℝ) := ⟨_, rfl⟩
  have hLr1 : 1 ≤ Lr := by rw [hLr]; linarith [(by norm_num : (1 : ℝ) ≤ 2 ^ 40)]
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ℝ,
      w₀ = max 8 (max (R₁ : ℝ) (max (R₂ : ℝ) (max (16 * Xi) (max (2 ^ 14 * Lr) (2 / vt))))) := ⟨_, rfl⟩
  have hw8 : 8 ≤ w₀ := hw₀ ▸ le_max_left _ _
  have hwR₁ : (R₁ : ℝ) ≤ w₀ := hw₀ ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hwR₂ : (R₂ : ℝ) ≤ w₀ := hw₀ ▸ ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hwX : 16 * Xi ≤ w₀ :=
    hw₀ ▸ (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hwL : 2 ^ 14 * Lr ≤ w₀ :=
    hw₀ ▸ ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)
  have hwv : 2 / vt ≤ w₀ :=
    hw₀ ▸ ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)
  obtain ⟨d₁, hd₁, hgr⟩ := e₃ Xi hXi (w₀ ^ 2700)
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : ℝ, κ₀ = 10 ^ (-8 : ℤ) * vt ^ 2 := ⟨_, rfl⟩
  have hκ₀0 : 0 < κ₀ := by rw [hκ₀]; positivity
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = 30 * A / κ₀ + CH * (3 / vt) / κ₀ := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (2 ^ 14 * Lr) ^ 4 := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := by
    rw [hP]
    exact one_le_pow₀ (by nlinarith)
  refine ⟨G * (1 + P), min (1 / 100) d₁, lt_min (by norm_num) hd₁, ?_⟩
  intro d hd hdd K β al T hch k m R x hk hx hR hm f h hpair hal o hof hoh κ κ' hκ hκ'
  have hd1 : d ≤ 1 / 100 := hdd.trans (min_le_left _ _)
  have hdd₁ : d ≤ d₁ := hdd.trans (min_le_right _ _)
  obtain ⟨hfar, hkK, hnle⟩ := e₂ Xi hXi d hd (by linarith) K β hch.isFlowDatum hch.minimalCutoff_le
  have hX := hgr d hd hdd₁ K β hch.isFlowDatum hch.minimalCutoff_le
  rw [← hx] at hX hnle
  rw [← hk] at hfar hkK hnle
  have hxk : flowCouplings (Tb.stepParameters y) β k = x := by rw [hx, hk]; rfl
  have hfar' : 2 ^ 12 * (clusterRange x : ℝ) ≤ lengthInSites (Tb.stepParameters y).side K k d := by
    have := hfar
    unfold IsSeparatedAt at this
    rwa [hxk] at this
  have hk' : k ≤ K := hkK.le
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = lengthInSites (Tb.stepParameters y).side K k d := ⟨_, rfl⟩
  rw [← hn] at hfar' hnle
  obtain ⟨hRw, hn64, hnw, hnR, hRt, htw, hq⟩ := scale_sizes (r := clusterRange x) hw8 hLr1 hwL hX hR rfl hfar'
    (by rw [hLr]; exact hnle)
  have hn0 : 0 < n := by linarith
  have hodd : Odd (Tb.stepParameters y).side := hTd.L_odd
  have hLp : (0 : ℝ) < ((Tb.stepParameters y).side : ℝ) := by
    linarith [(by positivity : (0 : ℝ) < 2 ^ 40), hL40,
      show ((Tb.stepParameters y).side : ℝ) = (Tb.side : ℝ) from rfl]
  have hapos : 0 < ((Tb.stepParameters y).side : ℝ) ^ k / ((Tb.stepParameters y).side : ℝ) ^ K := by positivity
  have hnd : n = d / (((Tb.stepParameters y).side : ℝ) ^ k / ((Tb.stepParameters y).side : ℝ) ^ K) :=
    hn.trans (lengthInSites_eq_div hk' d)
  have hna : n * (((Tb.stepParameters y).side : ℝ) ^ k / ((Tb.stepParameters y).side : ℝ) ^ K) = d := by
    rw [hnd]
    field_simp
  have ha64 : 64 * (((Tb.stepParameters y).side : ℝ) ^ k / ((Tb.stepParameters y).side : ℝ) ^ K) ≤ d := by
    rw [← hna]
    exact mul_le_mul_of_nonneg_right hn64 hapos.le
  have hx0 : 0 ≤ x := (by positivity : (0 : ℝ) ≤ w₀ ^ 2700).trans hX
  have hxne : x ≠ 0 := by
    have : (0 : ℝ) < w₀ ^ 2700 := by positivity
    linarith
  have hL2 : (2 : ℝ) ≤ Tb.side := by linarith [(by norm_num : (2 : ℝ) ≤ 2 ^ 40)]
  have h16 : 16 * R < boxSide (Tb.stepParameters y).side K k :=
    sixteen_radius_lt_boxSide hch.onFamily hch.isFlowDatum hkK hxk hL2 (hw8.trans htw) (hwX.trans htw) hRt hx0
  have hN : 64 * n ≤ ((boxSide (Tb.stepParameters y).side K k : ℕ) : ℝ) := by
    have e1 : ((boxSide (Tb.stepParameters y).side K k : ℕ) : ℝ) =
        2 * ((Tb.stepParameters y).side : ℝ) ^ (K - k) := by
      simp only [boxSide]
      push_cast
      rfl
    rw [e1, hn]
    simp only [lengthInSites]
    have h0 : 0 ≤ ((Tb.stepParameters y).side : ℝ) ^ (K - k) := by positivity
    have h1 : 64 * d ≤ 2 := by linarith
    calc 64 * (d * ((Tb.stepParameters y).side : ℝ) ^ (K - k)) =
          (64 * d) * ((Tb.stepParameters y).side : ℝ) ^ (K - k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 h0
  have hR8 : 8 ≤ R := by
    have : (8 : ℝ) ≤ R := hw8.trans hRw
    exact_mod_cast this
  have hRR₁ : R₁ ≤ R := by
    have : (R₁ : ℝ) ≤ R := hwR₁.trans hRw
    exact_mod_cast this
  have hRR₂ : R₂ ≤ R := by
    have : (R₂ : ℝ) ≤ R := hwR₂.trans hRw
    exact_mod_cast this
  obtain ⟨c, hp, hKf⟩ := hPair d vt f h hd hvt hvt1 hpair
  obtain ⟨errp, herrp⟩ : ∃ errp : ℝ, errp = |C₁| * ((vt * n)⁻¹ + Real.exp (-(c₁ * R))) := ⟨_, rfl⟩
  have hvn : 2 ≤ vt * n := by
    have h1 : 2 / vt ≤ n := hwv.trans hnw
    rw [div_le_iff₀ hvt] at h1
    linarith
  have hvn1 : (vt * n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have herr0 : 0 ≤ errp := by
    rw [herrp]
    have : 0 < vt * n := by positivity
    positivity
  have hle : C₁ * ((vt * lengthInSites (Tb.stepParameters y).side K k d)⁻¹ + Real.exp (-(c₁ * R))) ≤ errp := by
    rw [← hn, herrp]
    have : 0 ≤ (vt * n)⁻¹ + Real.exp (-(c₁ * R)) := by
      have : 0 < vt * n := by positivity
      positivity
    exact mul_le_mul_of_nonneg_right (le_abs_self _) this
  obtain ⟨-, hsym, hV⟩ := hbd k (boxSide (Tb.stepParameters y).side K k) o R hRR₂ h16
  have hTb : ∀ p ∈ plaquettesIn (supBall o (2 * (R : ℝ))), ∀ p' ∈ plaquettesIn (supBall o (2 * (R : ℝ))),
      |curlCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side k o R p p'| ≤ cT := fun p hp p' hp' => by
    rw [hcT]
    exact kernel_entry_abs_le hsym hV hp hp'
  have hBd : pairTraceBound n R c₄ M₀ errp ≤ A * (n⁻¹ + n ^ 4 * ((R : ℝ) ^ 4)⁻¹) :=
    hA n R errp (by linarith) hnR herr0 hvn1 herrp.le
  obtain ⟨H, hHd⟩ : ∃ H : ℝ, H = CH * (3 / vt * n⁻¹) := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := by rw [hHd]; positivity
  have hΛ0 : 0 ≤ 2 / (vt * d) := by positivity
  have hΛa : 2 / (vt * d) * (((Tb.stepParameters y).side : ℝ) ^ k / ((Tb.stepParameters y).side : ℝ) ^ K) =
      2 / (vt * n) := by
    have hane := hapos.ne'
    rw [← hna]
    field_simp
  have hvb : ∀ v ∈ shiftSet m, |boxTrace (Tb.stepParameters y).coupling (Tb.stepParameters y).side k o R
      (totalKernel (κ v)) (totalKernel (κ' v)) -
        6 / Real.pi ^ 4 * (al k ^ 2 * TestFunctions.inverseEighthKernel f h)| ≤
      A * (n⁻¹ + n ^ 4 * ((R : ℝ) ^ 4)⁻¹) + 6 / Real.pi ^ 4 * (al k ^ 2 * H) := by
    intro v hvQ
    obtain ⟨hmv, hKv⟩ := hMv c (latticeShift (Tb.stepParameters y).side K k v) d (2 / (vt * d)) f h hp
    have hmv' : IsLocalizedLipschitzPair (c + latticeShift (Tb.stepParameters y).side K k v) d (2 / (vt * d))
        (translateBy (Tb.stepParameters y).side K k v f) (translateBy (Tb.stepParameters y).side K k v h) := hmv
    have hKv' : TestFunctions.inverseEighthKernel (translateBy (Tb.stepParameters y).side K k v f)
        (translateBy (Tb.stepParameters y).side K k v h) = TestFunctions.inverseEighthKernel f h := hKv
    have e1 := translated_pair_trace_bound
      (T := curlCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side k o R) (Ck := Ck) (cT := cT)
      (n := n) (errp := errp) (S := S) hTrace hSites hodd hk' hmv' hd hd1 ha64 hnd hn64 hN hR8 herr0 hc₁ hS0
      (fun y => hS _ y)
      (fun p hp p' hp' z hz hz0 => hCk k _ o R hRR₁ h16 p hp p' hp' z hz hz0) hTb hsym
      (by rw [hn]; exact hof v hvQ) (by rw [hn]; exact hoh v hvQ) (hκ v hvQ) (hκ' v hvQ) hle
    rw [← hc₄, ← hM₀] at e1
    have e2 := hCH (Tb.stepParameters y).side hodd K k hk' _ d (2 / (vt * d)) _ _ hmv' hd hΛ0 hd1 ha64
      (by rw [hΛa, div_le_one (by positivity)]; exact hvn)
    rw [hKv', hΛa] at e2
    have e3 : |blockMeanKernelSum (Tb.stepParameters y).side K k (translateBy (Tb.stepParameters y).side K k v f)
        (translateBy (Tb.stepParameters y).side K k v h) - TestFunctions.inverseEighthKernel f h| ≤ H := by
      refine e2.trans ?_
      rw [hHd]
      refine mul_le_mul_of_nonneg_left ?_ hCH0
      have q1 : (((Tb.stepParameters y).side : ℝ) ^ k / ((Tb.stepParameters y).side : ℝ) ^ K) / d = n⁻¹ := by
        rw [hnd]
        have hane := hapos.ne'
        field_simp
      rw [q1]
      have q2 : 2 / (vt * n) = 2 / vt * n⁻¹ := by field_simp
      rw [q2]
      have q3 : n⁻¹ ≤ 1 / vt * n⁻¹ := by
        have : 1 ≤ 1 / vt := by rw [le_div_iff₀ hvt]; linarith
        have h0 : 0 ≤ n⁻¹ := by positivity
        nlinarith
      have q4 : 3 / vt * n⁻¹ = 2 / vt * n⁻¹ + 1 / vt * n⁻¹ := by ring
      linarith
    unfold boxTrace totalKernel
    set tr := ∑ p₁ ∈ plaquettesIn (supBall o (2 * (R : ℝ))), ∑ p₂ ∈ plaquettesIn (supBall o (2 * (R : ℝ))),
        ∑ p₃ ∈ plaquettesIn (supBall o (2 * (R : ℝ))), ∑ p₄ ∈ plaquettesIn (supBall o (2 * (R : ℝ))),
        (∑ y, κ v y p₁ p₂) * curlCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side k o R p₂ p₃ *
          (∑ z, κ' v z p₃ p₄) *
          curlCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side k o R p₄ p₁ with htr
    set Sv := blockMeanKernelSum (Tb.stepParameters y).side K k (translateBy (Tb.stepParameters y).side K k v f)
      (translateBy (Tb.stepParameters y).side K k v h) with hSv
    have hpi : 0 ≤ 6 / Real.pi ^ 4 := by positivity
    have e4 : |6 / Real.pi ^ 4 * (al k ^ 2 * Sv) - 6 / Real.pi ^ 4 * (al k ^ 2 * TestFunctions.inverseEighthKernel f h)| ≤
        6 / Real.pi ^ 4 * (al k ^ 2 * H) := by
      rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_nonneg hpi, abs_of_nonneg (by positivity : 0 ≤ al k ^ 2)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e3 (by positivity)) hpi
    have e5 := abs_sub_le tr (6 / Real.pi ^ 4 * (al k ^ 2 * Sv))
      (6 / Real.pi ^ 4 * (al k ^ 2 * TestFunctions.inverseEighthKernel f h))
    linarith
  obtain ⟨D, hD, hmean⟩ := shiftAverage_eq (m := m) _ _ x
    (fun v => boxTrace (Tb.stepParameters y).coupling (Tb.stepParameters y).side k o R (totalKernel (κ v))
      (totalKernel (κ' v))) hvb
  have hq0 : 0 ≤ n⁻¹ + n ^ 4 * ((R : ℝ) ^ 4)⁻¹ := by positivity
  obtain ⟨ε, hε, hNum⟩ := relative_error_exists
    (Num := boxCoefficient (Tb.stepParameters y).coupling (Tb.stepParameters y).side k m o R x κ κ') (al := al k)
    (Kf := TestFunctions.inverseEighthKernel f h) (x := x) (D := D) (B := A * (n⁻¹ + n ^ 4 * ((R : ℝ) ^ 4)⁻¹)) (H := H)
    (κ₀ := κ₀) hal (by rw [hκ₀]; exact hKf) hκ₀0 hxne (by positivity) hH0 hmean hD
  refine ⟨ε, ?_, hNum⟩
  rw [← hn]
  have hn1 : 1 ≤ n := by linarith
  have hinv : n⁻¹ ≤ n ^ (-(1 / 2) : ℝ) := by
    have : n⁻¹ = n ^ (-1 : ℝ) := (Real.rpow_neg_one n).symm
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hxp : 0 ≤ x ^ (-(1 / 130) : ℝ) := Real.rpow_nonneg hx0 _
  have hnp : 0 ≤ n ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hn0.le _
  have hq' : n ^ 4 * ((R : ℝ) ^ 4)⁻¹ ≤ P * x ^ (-(1 / 130) : ℝ) := by
    rw [hP, ← hLr] at *
    exact hq
  have hsum : 30 * (A * (n⁻¹ + n ^ 4 * ((R : ℝ) ^ 4)⁻¹)) / κ₀ + H / κ₀ ≤ G * (n⁻¹ + n ^ 4 * ((R : ℝ) ^ 4)⁻¹) := by
    have hvt3 : 0 ≤ CH * (3 / vt) / κ₀ := by positivity
    have hq2 : 0 ≤ n ^ 4 * ((R : ℝ) ^ 4)⁻¹ := by positivity
    rw [hG, hHd]
    have e : 30 * (A * (n⁻¹ + n ^ 4 * ((R : ℝ) ^ 4)⁻¹)) / κ₀ + CH * (3 / vt * n⁻¹) / κ₀ =
        30 * A / κ₀ * (n⁻¹ + n ^ 4 * ((R : ℝ) ^ 4)⁻¹) + CH * (3 / vt) / κ₀ * n⁻¹ := by ring
    rw [e]
    have hq3 : n⁻¹ ≤ n⁻¹ + n ^ 4 * ((R : ℝ) ^ 4)⁻¹ := by linarith
    have := mul_le_mul_of_nonneg_left hq3 hvt3
    linarith
  have hfin : G * (n⁻¹ + n ^ 4 * ((R : ℝ) ^ 4)⁻¹) ≤
      G * (1 + P) * n ^ (-(1 / 2) : ℝ) + G * (1 + P) * x ^ (-(1 / 130) : ℝ) := by
    have h1 : n⁻¹ + n ^ 4 * ((R : ℝ) ^ 4)⁻¹ ≤ n ^ (-(1 / 2) : ℝ) + P * x ^ (-(1 / 130) : ℝ) := add_le_add hinv hq'
    have h2 : n ^ (-(1 / 2) : ℝ) + P * x ^ (-(1 / 130) : ℝ) ≤
        (1 + P) * n ^ (-(1 / 2) : ℝ) + (1 + P) * x ^ (-(1 / 130) : ℝ) := by
      have a1 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ 1 + P) hnp
      have a2 := mul_le_mul_of_nonneg_right (by linarith : P ≤ 1 + P) hxp
      linarith
    calc _ ≤ G * ((1 + P) * n ^ (-(1 / 2) : ℝ) + (1 + P) * x ^ (-(1 / 130) : ℝ)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hG0
      _ = _ := by ring
  linarith
end YangMills.Construction.BoxMarks
end
