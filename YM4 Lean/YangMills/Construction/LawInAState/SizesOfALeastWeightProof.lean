import YangMills.Construction.LawByMomentsOfTheFlow.PlacesOfTheSitesOfASupportProof
import YangMills.Construction.LawInAState.SizesOfALeastWeight
import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsTheDescendedFormProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion BoxResponses
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
private theorem abs_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem euclidNormVec_le_two_mul (v : Fin 4 → ℝ) (s : ℝ) (hs : 0 ≤ s) (h : ∀ i, |v i| ≤ s) :
    euclidNormVec v ≤ 2 * s := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
private theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
section
variable {g : AmbientSpace → ℝ} {c : AmbientSpace} {d : ℝ}
private theorem periodize_lift_unique (hd : d < 1 / 2) (hg : ∀ x, g x ≠ 0 → euclidNormVec (x - c) ≤ d)
    (x : AmbientSpace) (z z' : Fin 4 → ℤ) (h : g (fun i => x i + 2 * (z i : ℝ)) ≠ 0)
    (h' : g (fun i => x i + 2 * (z' i : ℝ)) ≠ 0) : z = z' := by
  funext i
  have h1 := (abs_le_euclidNormVec _ i).trans (hg _ h)
  have h2 := (abs_le_euclidNormVec _ i).trans (hg _ h')
  simp only [Pi.sub_apply] at h1 h2
  rw [abs_le] at h1 h2
  have h3 : |(z i : ℝ) - (z' i : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have h4 : |z i - z' i| < 1 := by exact_mod_cast h3
  have h5 := Int.abs_lt_one_iff.mp h4
  omega
private theorem periodize_cases (hd : d < 1 / 2) (hg : ∀ x, g x ≠ 0 → euclidNormVec (x - c) ≤ d)
    (x : AmbientSpace) :
    (periodizeUnitTorus g x = 0 ∧ ∀ z : Fin 4 → ℤ, g (fun i => x i + 2 * (z i : ℝ)) = 0) ∨
      ∃ z : Fin 4 → ℤ, periodizeUnitTorus g x = g (fun i => x i + 2 * (z i : ℝ)) ∧
        g (fun i => x i + 2 * (z i : ℝ)) ≠ 0 := by
  by_cases h : ∃ z : Fin 4 → ℤ, g (fun i => x i + 2 * (z i : ℝ)) ≠ 0
  · obtain ⟨z, hz⟩ := h
    refine Or.inr ⟨z, ?_, hz⟩
    unfold periodizeUnitTorus
    refine finsum_eq_single _ z fun z' hz' => ?_
    by_contra hne
    exact hz' (periodize_lift_unique hd hg x z' z hne hz)
  · push_neg at h
    refine Or.inl ⟨?_, h⟩
    unfold periodizeUnitTorus
    simp [h]
private theorem abs_periodize_le (hd : d < 1 / 2) (hg : ∀ x, g x ≠ 0 → euclidNormVec (x - c) ≤ d)
    (h1 : ∀ x, |g x| ≤ 1) (x : AmbientSpace) : |periodizeUnitTorus g x| ≤ 1 := by
  rcases periodize_cases hd hg x with ⟨h, -⟩ | ⟨z, h, -⟩
  · simp [h]
  · rw [h]
    exact h1 _
private theorem abs_periodize_sub_le (hd : d < 1 / 2) (hg : ∀ x, g x ≠ 0 → euclidNormVec (x - c) ≤ d)
    {A : ℝ} (hA : 0 ≤ A) (hl : ∀ x x', |g x - g x'| ≤ A * euclidNormVec (x - x'))
    (x x' u : AmbientSpace) (e : Fin 4 → ℤ)
    (hu : ∀ i, x i - x' i = u i + 2 * (e i : ℝ)) (hu1 : ∀ i, |u i| ≤ 1) :
    |periodizeUnitTorus g x - periodizeUnitTorus g x'| ≤ A * euclidNormVec u := by
  have key : ∀ z : Fin 4 → ℤ,
      (fun i => x i + 2 * (z i : ℝ)) - (fun i => x' i + 2 * ((z + e) i : ℝ)) = u := by
    intro z
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Int.cast_add]
    linarith [hu i]
  rcases periodize_cases hd hg x with ⟨h, h0⟩ | ⟨z, h, hz⟩ <;>
    rcases periodize_cases hd hg x' with ⟨h', h0'⟩ | ⟨z', h', hz'⟩
  · rw [h, h']
    simpa using mul_nonneg hA (euclidNormVec_nonneg u)
  · have hk := key (z' - e)
    have hs := hl (fun i => x i + 2 * ((z' - e) i : ℝ)) (fun i => x' i + 2 * ((z' - e + e) i : ℝ))
    rw [hk, sub_add_cancel, h0 (z' - e)] at hs
    rw [h, h']
    exact hs
  · have hk := key z
    have hs := hl (fun i => x i + 2 * (z i : ℝ)) (fun i => x' i + 2 * ((z + e) i : ℝ))
    rw [hk, h0' (z + e)] at hs
    rw [h, h']
    exact hs
  · by_cases hzz : z' = z + e
    · subst hzz
      have hk := key z
      have hs := hl (fun i => x i + 2 * (z i : ℝ)) (fun i => x' i + 2 * ((z + e) i : ℝ))
      rw [hk] at hs
      rw [h, h']
      exact hs
    · exfalso
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hzz
      have h1 := (abs_le_euclidNormVec _ i).trans (hg _ hz)
      have h2 := (abs_le_euclidNormVec _ i).trans (hg _ hz')
      simp only [Pi.sub_apply] at h1 h2
      rw [abs_le] at h1 h2
      have h3 : 1 ≤ |((z' i - (z + e) i : ℤ) : ℝ)| := by
        have : z' i - (z + e) i ≠ 0 := sub_ne_zero.mpr hi
        exact_mod_cast Int.one_le_abs this
      have hw : (((z' i - (z + e) i : ℤ) : ℝ)) = (z' i : ℝ) - (z i : ℝ) - (e i : ℝ) := by
        simp only [Pi.add_apply, Int.cast_sub, Int.cast_add]
        ring
      rw [hw] at h3
      have h4 := hu i
      have h5 := abs_le.mp (hu1 i)
      rcases le_abs'.mp h3 with h6 | h6 <;> linarith [h1.1, h1.2, h2.1, h2.2, h5.1, h5.2]
end
section
private theorem two_mul_supDist_fineCentre_add_one_le (L : ℕ) [NeZero L] (hL : Odd L) :
    ∀ (t n : ℕ) [NeZero n] (y : TorusSite n) (c : TorusSite (fineSide L t n)),
      c ∈ fineBlock L t n y → 2 * _root_.YangMills.Construction.TorusFields.supDist c (fineCentre L t y) + 1 ≤ L ^ t := by apply _root_.YangMills.SharedProofs.p17606 <;> assumption
private theorem supDist_mul_pow_le_supDist_fineCentre (L t N : ℕ) [NeZero L] [NeZero N]
    (y y' : TorusSite N) :
    _root_.YangMills.Construction.TorusFields.supDist y y' * L ^ t ≤ _root_.YangMills.Construction.TorusFields.supDist (fineCentre L t y : TorusSite (fineSide L t N)) (fineCentre L t y') := by
  set T := _root_.YangMills.Construction.TorusFields.supDist (fineCentre L t y : TorusSite (fineSide L t N)) (fineCentre L t y') with hT
  have hLt : 0 < L ^ t := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) t
  have hM : fineSide L t N = N * L ^ t := fineSide_eq L t N
  have hsup : _root_.YangMills.Construction.TorusFields.supDist y y' ≤ T / L ^ t := by
    rw [_root_.YangMills.Construction.TorusFields.supDist_le_iff]
    intro i
    set a : ℤ := (((fineCentre L t y : TorusSite (fineSide L t N)) i) -
      (fineCentre L t y' : TorusSite (fineSide L t N)) i).valMinAbs with ha
    have haT : a.natAbs ≤ T := (_root_.YangMills.Construction.TorusFields.supDist_le_iff _ _ _).mp le_rfl i
    have hcast : ((a : ℤ) : ZMod (fineSide L t N)) =
        (((L : ℤ) ^ t * (((y i).cast : ℤ) - ((y' i).cast : ℤ)) : ℤ) : ZMod (fineSide L t N)) := by
      rw [ha, ZMod.coe_valMinAbs]
      simp only [fineCentre, siteOfInt]
      push_cast
      ring
    obtain ⟨w, hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast
    rw [hM] at hw
    push_cast at hw
    set Y : ℤ := ((y i).cast : ℤ) with hY
    set Y' : ℤ := ((y' i).cast : ℤ) with hY'
    have hq : a = (L : ℤ) ^ t * (Y - Y' - N * w) := by linarith
    have hyy : y i - y' i = ((Y - Y' - N * w : ℤ) : ZMod N) := by
      push_cast
      rw [hY, hY']
      simp
    rw [hyy]
    refine Nat.le_div_iff_mul_le hLt |>.mpr ?_
    refine le_trans (Nat.mul_le_mul_right _ (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _)) ?_
    have : a.natAbs = L ^ t * (Y - Y' - N * w).natAbs := by
      rw [hq, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    rw [mul_comm]
    omega
  calc _root_.YangMills.Construction.TorusFields.supDist y y' * L ^ t ≤ T / L ^ t * L ^ t := Nat.mul_le_mul_right _ hsup
    _ ≤ T := Nat.div_mul_le_self _ _
private theorem card_le_of_supDist_le {N : ℕ} [NeZero N] (s : Finset (TorusSite N)) (y₀ : TorusSite N)
    (D : ℕ) (h : ∀ y ∈ s, _root_.YangMills.Construction.TorusFields.supDist y₀ y ≤ D) : (s.card : ℝ) ≤ (2 * (D : ℝ) + 1) ^ 4 := by
  classical
  have hinj : Set.InjOn (fun y : TorusSite N => fun i : Fin 4 => ((y i - y₀ i).valMinAbs : ℤ))
      (s : Set (TorusSite N)) := by
    intro a _ b _ hab
    funext i
    have h1 := congrFun hab i
    have h2 : a i - y₀ i = b i - y₀ i := by
      have := congrArg (fun v : ℤ => (v : ZMod N)) h1
      simpa [ZMod.coe_valMinAbs] using this
    exact sub_left_injective h2
  have hmaps : ∀ y ∈ s, (fun i : Fin 4 => ((y i - y₀ i).valMinAbs : ℤ)) ∈
      Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(D : ℤ)) D := by
    intro y hy
    refine Fintype.mem_piFinset.mpr fun i => ?_
    have h0 : _root_.YangMills.Construction.TorusFields.supDist y y₀ ≤ D := by
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      exact h y hy
    have h1 := (_root_.YangMills.Construction.TorusFields.supDist_le_iff y y₀ D).mp h0 i
    rw [Finset.mem_Icc]
    omega
  have hc := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Fintype.card_piFinset] at hc
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  have h3 : ((D : ℤ) + 1 - -(D : ℤ)).toNat = 2 * D + 1 := by omega
  rw [h3] at hc
  have : (s.card : ℝ) ≤ ((2 * D + 1) ^ 4 : ℕ) := by exact_mod_cast hc
  simpa using this
private theorem supDist_plaquetteVertex_le_two {m : ℕ} [NeZero m] (x c : TorusSite m) (μ ν : Fin 4)
    (hc : c ∈ plaquetteVertices x μ ν) : _root_.YangMills.Construction.TorusFields.supDist c x ≤ 2 := by apply _root_.YangMills.SharedProofs.p38261 <;> assumption
private theorem exists_val_doubledBarycentre {m : ℕ} [NeZero m] (p : TorusPlaquette m)
    (hp : p.2.1 < p.2.2) (i : Fin 4) :
    ∃ η : ℕ, η ≤ 1 ∧ ((doubledBarycentre p i).val : ℕ) = 2 * (p.1 i).val + η := by
  have hne : p.2.1 ≠ p.2.2 := ne_of_lt hp
  have hη : (if i = p.2.1 then 1 else 0) + (if i = p.2.2 then 1 else 0) ≤ 1 := by
    by_cases h1 : i = p.2.1
    · have : i ≠ p.2.2 := fun h => hne (h1.symm.trans h)
      simp [h1, this, hne]
    · simp only [h1, if_false]
      split_ifs <;> omega
  refine ⟨(if i = p.2.1 then 1 else 0) + (if i = p.2.2 then 1 else 0), hη, ?_⟩
  have hv : (p.1 i).val < m := ZMod.val_lt _
  unfold doubledBarycentre
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  ring
end
private theorem supDist_le_of_mem_weightSupportSites (L K k : ℕ) [NeZero L] (hL : Odd L) (hk : k ≤ K)
    (d : ℝ) (hd0 : 0 < d) (hd : d < 1 / 2) (c : AmbientSpace) (g : AmbientSpace → ℝ)
    (hg : ∀ x, g x ≠ 0 → euclidNormVec (x - c) ≤ d) {y y' : TorusSite (boxSide L K k)}
    (hy : y ∈ weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k g))
    (hy' : y' ∈ weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k g)) :
    (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ) ≤ 2 * lengthInSites L K k d + 5 := by
  simp only [weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and] at hy hy'
  obtain ⟨p, ⟨hlt, c₁, hc₁, hb₁⟩, hne⟩ := hy
  obtain ⟨p', ⟨hlt', c₂, hc₂, hb₂⟩, hne'⟩ := hy'
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLone : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hm : fineSide L k (boxSide L K k) = 2 * L ^ K := by
    rw [fineSide_eq]
    unfold boxSide
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  have hmR : ((fineSide L k (boxSide L K k) : ℕ) : ℝ) = 2 * (L : ℝ) ^ K := by rw [hm]; push_cast; ring
  have hLk : (1 : ℝ) ≤ (L : ℝ) ^ k := one_le_pow₀ hLone
  have lift : ∀ q : TorusPlaquette (fineSide L k (boxSide L K k)), unitTorusWeight L K k g q ≠ 0 →
      ∃ z : Fin 4 → ℤ, ∀ i,
        |((doubledBarycentre q i).val : ℝ) / (2 * (L : ℝ) ^ K) + 2 * (z i : ℝ) - c i| ≤ d := by
    intro q hq
    rcases periodize_cases hd hg (fun i => ((doubledBarycentre q i).val : ℝ) / (2 * (L : ℝ) ^ K)) with
      ⟨h, -⟩ | ⟨z, -, hz⟩
    · exact absurd h hq
    · exact ⟨z, fun i => (abs_le_euclidNormVec _ i).trans (hg _ hz)⟩
  obtain ⟨z, hz⟩ := lift p hne
  obtain ⟨z', hz'⟩ := lift p' hne'
  set E0 : ℕ := ⌊d * ((fineSide L k (boxSide L K k)) : ℝ) + 1 / 2⌋₊ with hE0
  have hpp : _root_.YangMills.Construction.TorusFields.supDist p.1 p'.1 ≤ E0 := by
    have hoff : ∀ i, ∃ e : ℤ, p'.1 i = p.1 i + ((e : ℤ) : ZMod (fineSide L k (boxSide L K k))) ∧
        e.natAbs ≤ E0 := by
      intro i
      obtain ⟨η, hη, hv⟩ := exists_val_doubledBarycentre p hlt i
      obtain ⟨η', hη', hv'⟩ := exists_val_doubledBarycentre p' hlt' i
      set e : ℤ := ((p.1 i).val : ℤ) - ((p'.1 i).val : ℤ) +
        ((fineSide L k (boxSide L K k)) : ℤ) * (z i - z' i) with he
      refine ⟨-e, ?_, ?_⟩
      · have h1 : (((p.1 i).val : ℤ) : ZMod (fineSide L k (boxSide L K k))) = p.1 i := by simp
        have h2 : (((p'.1 i).val : ℤ) : ZMod (fineSide L k (boxSide L K k))) = p'.1 i := by simp
        rw [he]
        push_cast
        rw [show (((p.1 i).val : ZMod (fineSide L k (boxSide L K k)))) = p.1 i from by simpa using h1,
          show (((p'.1 i).val : ZMod (fineSide L k (boxSide L K k)))) = p'.1 i from by simpa using h2]
        simp
      · have h1 := abs_le.mp (hz i)
        have h2 := abs_le.mp (hz' i)
        have hv1 : ((doubledBarycentre p i).val : ℝ) = 2 * ((p.1 i).val : ℝ) + (η : ℝ) := by
          exact_mod_cast hv
        have hv2 : ((doubledBarycentre p' i).val : ℝ) = 2 * ((p'.1 i).val : ℝ) + (η' : ℝ) := by
          exact_mod_cast hv'
        have hη1 : (η : ℝ) ≤ 1 := by exact_mod_cast hη
        have hη2 : (η' : ℝ) ≤ 1 := by exact_mod_cast hη'
        rw [hv1] at h1
        rw [hv2] at h2
        have hmpos : (0 : ℝ) < ((fineSide L k (boxSide L K k) : ℕ) : ℝ) := by rw [hmR]; positivity
        have hmne : ((fineSide L k (boxSide L K k) : ℕ) : ℝ) ≠ 0 := hmpos.ne'
        have hA : ∀ v η : ℝ, (2 * v + η) / (2 * (L : ℝ) ^ K) =
            (2 * v + η) / ((fineSide L k (boxSide L K k)) : ℝ) := by
          intro v η; rw [hmR]
        rw [hA] at h1 h2
        have hdiff : ((2 * ((p.1 i).val : ℝ) + (η : ℝ)) / ((fineSide L k (boxSide L K k)) : ℝ) +
            2 * (z i : ℝ)) - ((2 * ((p'.1 i).val : ℝ) + (η' : ℝ)) /
              ((fineSide L k (boxSide L K k)) : ℝ) + 2 * (z' i : ℝ)) =
            (2 * (e : ℝ) + (η : ℝ) - (η' : ℝ)) / ((fineSide L k (boxSide L K k)) : ℝ) := by
          rw [he]
          push_cast
          field_simp
          ring
        have h3 : |(2 * (e : ℝ) + (η : ℝ) - (η' : ℝ)) / ((fineSide L k (boxSide L K k)) : ℝ)| ≤ 2 * d := by
          rw [← hdiff, abs_le]
          constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        rw [abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos] at h3
        have h4 := abs_le.mp h3
        have h5 : |(e : ℝ)| ≤ d * ((fineSide L k (boxSide L K k)) : ℝ) + 1 / 2 := by
          rw [abs_le]
          constructor <;> linarith [h4.1, h4.2]
        rw [Int.natAbs_neg]
        apply Nat.le_floor
        have : ((e.natAbs : ℕ) : ℝ) = |(e : ℝ)| := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        rw [this]
        exact h5
    choose e he he' using hoff
    have : p'.1 = p.1 + siteOfInt e := by
      funext i
      simpa [siteOfInt] using he i
    rw [this]
    exact _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ he'
  have hn1 := two_mul_supDist_fineCentre_add_one_le L hL k (boxSide L K k) y c₁ hb₁
  have hn2 := two_mul_supDist_fineCentre_add_one_le L hL k (boxSide L K k) y' c₂ hb₂
  have hcor1 := supDist_plaquetteVertex_le_two p.1 c₁ p.2.1 p.2.2 hc₁
  have hcor2 := supDist_plaquetteVertex_le_two p'.1 c₂ p'.2.1 p'.2.2 hc₂
  have hT : _root_.YangMills.Construction.TorusFields.supDist (fineCentre L k y : TorusSite (fineSide L k (boxSide L K k))) (fineCentre L k y') + 1 ≤
      L ^ k + E0 + 4 := by
    have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle (fineCentre L k y : TorusSite (fineSide L k (boxSide L K k))) c₁ (fineCentre L k y')
    have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle c₁ p.1 (fineCentre L k y' : TorusSite (fineSide L k (boxSide L K k)))
    have t3 := _root_.YangMills.Construction.TorusFields.supDist_triangle p.1 p'.1 (fineCentre L k y' : TorusSite (fineSide L k (boxSide L K k)))
    have t4 := _root_.YangMills.Construction.TorusFields.supDist_triangle p'.1 c₂ (fineCentre L k y' : TorusSite (fineSide L k (boxSide L K k)))
    have s1 := _root_.YangMills.Construction.TorusFields.supDist_comm (fineCentre L k y : TorusSite (fineSide L k (boxSide L K k))) c₁
    have s2 := _root_.YangMills.Construction.TorusFields.supDist_comm p'.1 c₂
    omega
  have hS := supDist_mul_pow_le_supDist_fineCentre L k (boxSide L K k) y y'
  have hR : (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ) * (L : ℝ) ^ k + 1 ≤ (L : ℝ) ^ k + (E0 : ℝ) + 4 := by
    have : _root_.YangMills.Construction.TorusFields.supDist y y' * L ^ k + 1 ≤ L ^ k + E0 + 4 := by omega
    exact_mod_cast this
  have hE : (E0 : ℝ) ≤ d * ((fineSide L k (boxSide L K k)) : ℝ) + 1 / 2 := Nat.floor_le (by positivity)
  have hnk : lengthInSites L K k d * (L : ℝ) ^ k = d * (L : ℝ) ^ K := by
    unfold lengthInSites
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  have hfin : (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ) * (L : ℝ) ^ k ≤ (2 * lengthInSites L K k d + 5) * (L : ℝ) ^ k := by
    have : (2 * lengthInSites L K k d + 5) * (L : ℝ) ^ k = 2 * (d * (L : ℝ) ^ K) + 5 * (L : ℝ) ^ k := by
      rw [← hnk]; ring
    rw [this, hmR] at *
    nlinarith
  exact le_of_mul_le_mul_right hfin (by linarith)
private theorem nonempty_orientedPlaquette (m : ℕ) [NeZero m] : Nonempty (OrientedPlaquette m) :=
  ⟨⟨(0, (0, 1)), show (0 : Fin 4) < 1 by decide⟩⟩
theorem unitTorusWeightSizes : unitTorusWeightSizesStatement := by
  intro L _ hL K k hk d vt c g hd0 hd hvt h1 hlip hsup
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hnpos : 0 < lengthInSites L K k d := by
    unfold lengthInSites
    positivity
  have hm : fineSide L k (boxSide L K k) = 2 * L ^ K := by
    rw [fineSide_eq]
    unfold boxSide
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  have hmR : ((fineSide L k (boxSide L K k) : ℕ) : ℝ) = 2 * (L : ℝ) ^ K := by rw [hm]; push_cast; ring
  have hnk : lengthInSites L K k d * (L : ℝ) ^ k = d * (L : ℝ) ^ K := by
    unfold lengthInSites
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  haveI := nonempty_orientedPlaquette (fineSide L k (boxSide L K k))
  refine ⟨?_, ?_, ?_⟩
  · unfold weightSup
    exact ciSup_le fun p => abs_periodize_le hd hsup h1 _
  · unfold weightLipschitz
    refine ciSup_le fun pp => ?_
    obtain ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩ := pp
    dsimp only
    have hrhs : 0 ≤ 2 / (vt * lengthInSites L K k d) := by positivity
    set D := _root_.YangMills.Construction.TorusFields.supDist (doubledBarycentre p) (doubledBarycentre p') with hD
    have hb : barycentreDist L k p p' = (D : ℝ) / (2 * (L : ℝ) ^ k) := rfl
    rw [hb]
    by_cases hD0 : D = 0
    · simpa [hD0] using hrhs
    rw [div_le_iff₀ (by positivity)]
    have hoff : ∀ i, ∃ a e : ℤ, a.natAbs ≤ D ∧ a.natAbs ≤ (fineSide L k (boxSide L K k)) ∧
        (((doubledBarycentre p i).val : ℤ) - ((doubledBarycentre p' i).val : ℤ)) =
          a + 2 * ((fineSide L k (boxSide L K k) : ℕ) : ℤ) * e := by
      intro i
      refine ⟨(doubledBarycentre p i - doubledBarycentre p' i).valMinAbs, ?_⟩
      have hcast : (((((doubledBarycentre p i).val : ℤ) - ((doubledBarycentre p' i).val : ℤ) : ℤ)) :
            ZMod (2 * fineSide L k (boxSide L K k))) =
          (((doubledBarycentre p i - doubledBarycentre p' i).valMinAbs : ℤ) :
            ZMod (2 * fineSide L k (boxSide L K k))) := by
        rw [ZMod.coe_valMinAbs]
        push_cast
        simp
      obtain ⟨w, hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast
      refine ⟨-w, (_root_.YangMills.Construction.TorusFields.supDist_le_iff _ _ _).mp le_rfl i, ?_, ?_⟩
      · have := ZMod.natAbs_valMinAbs_le (doubledBarycentre p i - doubledBarycentre p' i)
        omega
      · push_cast at hw
        linarith
    choose a e ha ha' hae using hoff
    have hu : ∀ i, ((doubledBarycentre p i).val : ℝ) / (2 * (L : ℝ) ^ K) -
        ((doubledBarycentre p' i).val : ℝ) / (2 * (L : ℝ) ^ K) =
        (a i : ℝ) / (2 * (L : ℝ) ^ K) + 2 * (e i : ℝ) := by
      intro i
      have h2 : ((doubledBarycentre p i).val : ℝ) - ((doubledBarycentre p' i).val : ℝ) =
          (a i : ℝ) + 2 * ((fineSide L k (boxSide L K k) : ℕ) : ℝ) * (e i : ℝ) := by
        exact_mod_cast hae i
      rw [← sub_div, h2, hmR]
      field_simp
    have habs : ∀ i, |(a i : ℝ)| ≤ (D : ℝ) := fun i => by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      exact_mod_cast ha i
    have habs' : ∀ i, |(a i : ℝ)| ≤ 2 * (L : ℝ) ^ K := fun i => by
      rw [← hmR, ← Int.cast_abs, Int.abs_eq_natAbs]
      exact_mod_cast ha' i
    have hu1 : ∀ i, |(a i : ℝ) / (2 * (L : ℝ) ^ K)| ≤ 1 := fun i => by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ K), div_le_one (by positivity)]
      exact habs' i
    have hA : (0 : ℝ) ≤ (vt * d)⁻¹ := by positivity
    have hsl := abs_periodize_sub_le hd hsup hA (fun x x' => by
        rw [inv_mul_eq_div]
        exact hlip x x') _ _ (fun i => (a i : ℝ) / (2 * (L : ℝ) ^ K)) e hu hu1
    have hE : euclidNormVec (fun i => (a i : ℝ) / (2 * (L : ℝ) ^ K)) ≤
        2 * ((D : ℝ) / (2 * (L : ℝ) ^ K)) := by
      refine euclidNormVec_le_two_mul _ _ (by positivity) fun i => ?_
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ K)]
      exact div_le_div_of_nonneg_right (habs i) (by positivity)
    have hgoal : (vt * d)⁻¹ * (2 * ((D : ℝ) / (2 * (L : ℝ) ^ K))) =
        2 / (vt * lengthInSites L K k d) * ((D : ℝ) / (2 * (L : ℝ) ^ k)) := by
      have e1 : vt * lengthInSites L K k d * (L : ℝ) ^ k = vt * d * (L : ℝ) ^ K := by
        rw [mul_assoc, hnk, mul_assoc]
      have e2 : 2 / (vt * lengthInSites L K k d) * ((D : ℝ) / (2 * (L : ℝ) ^ k)) =
          (D : ℝ) / (vt * lengthInSites L K k d * (L : ℝ) ^ k) := by
        field_simp
      rw [e2, e1]
      field_simp
    rw [← hgoal]
    exact hsl.trans (mul_le_mul_of_nonneg_left hE hA)
  · set s := weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k g) with hs
    by_cases hne : s.Nonempty
    · obtain ⟨y₀, hy₀⟩ := hne
      set D : ℕ := ⌊2 * lengthInSites L K k d + 5⌋₊ with hDdef
      have h2 : (s.card : ℝ) ≤ (2 * (D : ℝ) + 1) ^ 4 := by
        refine card_le_of_supDist_le s y₀ D fun y hy => ?_
        exact Nat.le_floor (supDist_le_of_mem_weightSupportSites L K k hL hk d hd0 hd c g hsup hy₀ hy)
      have h3 : (D : ℝ) ≤ 2 * lengthInSites L K k d + 5 := Nat.floor_le (by positivity)
      refine h2.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
end YangMills.Construction.StateLaws
end
