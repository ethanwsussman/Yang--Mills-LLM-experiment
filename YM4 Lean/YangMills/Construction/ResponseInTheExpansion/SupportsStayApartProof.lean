import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ResponseInTheExpansion.SupportsStayApart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps WeightedResponses
namespace SupportsSeparated
private theorem intCast_mul_eq_of_eq {N P : ℕ} {M a b : ℤ} (hP : (P : ℤ) = N * M) (h : (a : ZMod N) = (b : ZMod N)) :
    ((M * a : ℤ) : ZMod P) = ((M * b : ℤ) : ZMod P) := by apply _root_.YangMills.Construction.BlockAverages.intCast_mul_eq_of_eq <;> assumption
private def doubleSite {m : ℕ} (c : TorusSite m) : TorusSite (2 * m) := fun i => ((2 * (c i).val : ℕ) : ZMod (2 * m))
private theorem doubleSite_add_siteOfInt {m : ℕ} [NeZero m] (c : TorusSite m) (e : Fin 4 → ℤ) :
    doubleSite (c + siteOfInt e) = doubleSite c + siteOfInt (fun i => 2 * e i) := by
  funext i
  have hcg : (((((c + siteOfInt e : TorusSite m)) i).val : ℤ) : ZMod m) = ((((c i).val : ℤ) + e i : ℤ) : ZMod m) := by
    simp [siteOfInt]
  have := intCast_mul_eq_of_eq (N := m) (P := 2 * m) (M := 2) (by push_cast; ring) hcg
  simp only [doubleSite, siteOfInt, Pi.add_apply]
  push_cast at this ⊢
  simp only [siteOfInt, Pi.add_apply] at this
  rw [mul_add] at this
  exact this
private theorem supDist_doubleSite_le {m : ℕ} [NeZero m] (c c' : TorusSite m) :
    _root_.YangMills.Construction.TorusFields.supDist (doubleSite c) (doubleSite c') ≤ 2 * _root_.YangMills.Construction.TorusFields.supDist c c' := by
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist c c'
  have h := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le (doubleSite c) (fun i => 2 * e i) (2 * _root_.YangMills.Construction.TorusFields.supDist c c') fun i => by
    have := hb i
    show (2 * e i).natAbs ≤ 2 * _root_.YangMills.Construction.TorusFields.supDist c c'
    omega
  rw [← doubleSite_add_siteOfInt, ← he] at h
  exact h
private def axisVector (j : Fin 4) : Fin 4 → ℤ := fun i => if i = j then 1 else 0
private theorem unitStep_eq_siteOfInt {m : ℕ} (j : Fin 4) : unitStep m j = siteOfInt (axisVector j) := by
  funext i
  by_cases h : i = j
  · subst h
    simp [unitStep, siteOfInt, axisVector]
  · simp [unitStep, siteOfInt, axisVector, h]
private theorem exists_of_mem_plaquetteVertices {m : ℕ} (x : TorusSite m) (μ ν : Fin 4) {c : TorusSite m}
    (hc : c ∈ plaquetteVertices x μ ν) :
    ∃ a b : ℤ, (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧
      c = x + siteOfInt (fun i => a * axisVector μ i + b * axisVector ν i) := by
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by simp, by simp, by funext i; simp [siteOfInt]⟩
  · exact ⟨1, 0, by simp, by simp, by rw [unitStep_eq_siteOfInt]; funext i; simp [siteOfInt]⟩
  · exact ⟨0, 1, by simp, by simp, by rw [unitStep_eq_siteOfInt]; funext i; simp [siteOfInt]⟩
  · exact ⟨1, 1, by simp, by simp, by
      rw [unitStep_eq_siteOfInt, unitStep_eq_siteOfInt]; funext i; simp [siteOfInt, add_assoc]⟩
private theorem doubledBarycentre_eq {m : ℕ} (p : TorusPlaquette m) :
    doubledBarycentre p = doubleSite p.1 + siteOfInt (fun i => axisVector p.2.1 i + axisVector p.2.2 i) := by
  funext i
  simp only [doubledBarycentre, doubleSite, siteOfInt, axisVector, Pi.add_apply]
  split_ifs <;> push_cast <;> ring
private theorem supDist_doubleSite_doubledBarycentre_le {m : ℕ} [NeZero m] (p : TorusPlaquette m)
    (hp : p.2.1 < p.2.2) {c : TorusSite m} (hc : c ∈ plaquetteVertices p.1 p.2.1 p.2.2) :
    _root_.YangMills.Construction.TorusFields.supDist (doubleSite c) (doubledBarycentre p) ≤ 1 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_of_mem_plaquetteVertices p.1 p.2.1 p.2.2 hc
  have hne : p.2.1 ≠ p.2.2 := ne_of_lt hp
  have key : doubledBarycentre p =
      doubleSite (p.1 + siteOfInt (fun i => a * axisVector p.2.1 i + b * axisVector p.2.2 i)) +
        siteOfInt (fun i => (1 - 2 * a) * axisVector p.2.1 i + (1 - 2 * b) * axisVector p.2.2 i) := by
    rw [doubledBarycentre_eq, doubleSite_add_siteOfInt, add_assoc]
    congr 1
    funext i
    simp only [siteOfInt, Pi.add_apply]
    rw [← Int.cast_add]
    congr 1
    ring
  rw [key]
  refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ 1 fun i => ?_
  by_cases h1 : i = p.2.1
  · have h2 : i ≠ p.2.2 := fun h => hne (h1 ▸ h)
    rcases ha with rfl | rfl <;> simp [axisVector, h1, hne]
  · by_cases h2 : i = p.2.2
    · rcases hb with rfl | rfl <;> simp [axisVector, h2, hne.symm]
    · simp [axisVector, h1, h2]
private theorem supDist_le_of_offset {P : ℕ} [NeZero P] (x y : TorusSite P) (w : Fin 4 → ℤ) (m : ℕ)
    (h : ∀ i, y i = x i + ((w i : ℤ) : ZMod P)) (hw : ∀ i, (w i).natAbs ≤ m) : _root_.YangMills.Construction.TorusFields.supDist x y ≤ m := by
  have hy : y = x + siteOfInt w := funext fun i => by simpa [siteOfInt] using h i
  rw [hy]
  exact _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le x w m hw
private theorem supDist_fineCentre_parentBlock_le (L : ℕ) [NeZero L] {k : ℕ} (hk : L = 2 * k + 1) (t n : ℕ)
    [NeZero n] (y : TorusSite (n * L)) :
    _root_.YangMills.Construction.TorusFields.supDist (n := fineSide L t (n * L)) (fineCentre L (t + 1) (parentBlock L y)) (fineCentre L t y) ≤ L ^ t * k := by
  have hLz : (0 : ℤ) < L := by
    have := NeZero.pos L
    exact_mod_cast this
  have hhalf : ((L : ℤ) - 1) / 2 = k := by
    rw [hk]
    push_cast
    omega
  let s : Fin 4 → ℤ := fun i => (((y i).cast : ℤ) + k) / L
  let v : Fin 4 → ℤ := fun i => ((y i).cast : ℤ) - L * s i
  have hv : ∀ i, (v i).natAbs ≤ k := by
    intro i
    have h1 := Int.emod_add_mul_ediv (((y i).cast : ℤ) + k) L
    have h2 := Int.emod_nonneg (((y i).cast : ℤ) + k) hLz.ne'
    have h3 := Int.emod_lt_of_pos (((y i).cast : ℤ) + k) hLz
    have h4 : v i = (((y i).cast : ℤ) + k) % L - k := by
      simp only [v, s]
      linarith
    rw [h4]
    have hLk : (L : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
    omega
  refine supDist_le_of_offset (P := fineSide L t (n * L)) _ _ (fun i => (L : ℤ) ^ t * v i) _ (fun i => ?_)
    fun i => ?_
  · have hcast : ((((parentBlock L y i).cast : ℤ) : ℤ) : ZMod n) = ((s i : ℤ) : ZMod n) := by
      rw [ZMod.intCast_zmod_cast]
      simp only [parentBlock, s, hhalf]
    have hscale := intCast_mul_eq_of_eq (N := n) (P := fineSide L t (n * L)) (M := (L : ℤ) ^ (t + 1))
      (by rw [fineSide_eq]; push_cast; ring) hcast
    show (((L : ℤ) ^ t * ((y i).cast : ℤ) : ℤ) : ZMod (fineSide L t (n * L))) =
      (((L : ℤ) ^ (t + 1) * ((parentBlock L y i).cast : ℤ) : ℤ) : ZMod (fineSide L t (n * L))) +
        (((L : ℤ) ^ t * v i : ℤ) : ZMod (fineSide L t (n * L)))
    rw [hscale, ← Int.cast_add]
    congr 1
    simp only [v]
    ring
  · rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (hv i)
abbrev _root_.YangMills.SharedProofs.p21417 := @supDist_fineCentre_parentBlock_le
private theorem two_mul_supDist_fineCentre_add_one_le (L : ℕ) [NeZero L] (hL : Odd L) :
    (t n : ℕ) → [NeZero n] → (y : TorusSite n) → (c : TorusSite (fineSide L t n)) → c ∈ fineBlock L t n y →
      2 * _root_.YangMills.Construction.TorusFields.supDist c (fineCentre L t y) + 1 ≤ L ^ t
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
    have hstep := supDist_fineCentre_parentBlock_le L hk t n y
    obtain ⟨B, hB⟩ : ∃ B : TorusSite (fineSide L t (n * L)), B = fineCentre L (t + 1) (parentBlock L y) :=
      ⟨_, rfl⟩
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
    _root_.YangMills.Construction.TorusFields.supDist (fineCentre L t y) (fineCentre L t y') ≤ L ^ t * _root_.YangMills.Construction.TorusFields.supDist y y' := by
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist y y'
  refine supDist_le_of_offset (P := fineSide L t n) _ _ (fun i => (L : ℤ) ^ t * e i) _ (fun i => ?_) fun i => ?_
  · have hcast : ((((y' i).cast : ℤ) : ℤ) : ZMod n) = ((((y i).cast : ℤ) + e i : ℤ) : ZMod n) := by
      rw [he]
      simp [siteOfInt]
    have hscale := intCast_mul_eq_of_eq (N := n) (P := fineSide L t n) (M := (L : ℤ) ^ t)
      (by rw [fineSide_eq]; push_cast; ring) hcast
    show (((L : ℤ) ^ t * ((y' i).cast : ℤ) : ℤ) : ZMod (fineSide L t n)) =
      (((L : ℤ) ^ t * ((y i).cast : ℤ) : ℤ) : ZMod (fineSide L t n)) +
        (((L : ℤ) ^ t * e i : ℤ) : ZMod (fineSide L t n))
    rw [hscale, ← Int.cast_add]
    congr 1
    ring
  · rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (hb i)
abbrev _root_.YangMills.SharedProofs.p11320 := @supDist_fineCentre_le
private theorem supDist_doubledBarycentre_le (L : ℕ) [NeZero L] (hL : Odd L) (t n : ℕ) [NeZero n]
    (y y' : TorusSite n) (p p' : TorusPlaquette (fineSide L t n)) (hp : IsPlaquetteAt L t y p)
    (hp' : IsPlaquetteAt L t y' p') :
    _root_.YangMills.Construction.TorusFields.supDist (doubledBarycentre p) (doubledBarycentre p') ≤ 2 * L ^ t * (1 + _root_.YangMills.Construction.TorusFields.supDist y y') := by
  obtain ⟨ho, c, hc, hcb⟩ := hp
  obtain ⟨ho', c', hc', hcb'⟩ := hp'
  have h1 := supDist_doubleSite_doubledBarycentre_le p ho hc
  have h2 := supDist_doubleSite_doubledBarycentre_le p' ho' hc'
  have h3 := supDist_doubleSite_le c c'
  have h4 := two_mul_supDist_fineCentre_add_one_le L hL t n y c hcb
  have h5 := two_mul_supDist_fineCentre_add_one_le L hL t n y' c' hcb'
  have h6 := supDist_fineCentre_le L t n y y'
  have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle (doubledBarycentre p) (doubleSite c) (doubledBarycentre p')
  have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (doubleSite c) (doubleSite c') (doubledBarycentre p')
  have t3 := _root_.YangMills.Construction.TorusFields.supDist_triangle c (fineCentre L t y) c'
  have t4 := _root_.YangMills.Construction.TorusFields.supDist_triangle (fineCentre L t y) (fineCentre L t y') c'
  have c1 := _root_.YangMills.Construction.TorusFields.supDist_comm (doubledBarycentre p) (doubleSite c)
  have c2 := _root_.YangMills.Construction.TorusFields.supDist_comm c' (fineCentre L t y')
  rw [mul_add, mul_one, mul_assoc]
  omega
end SupportsSeparated
theorem supportsSeparatedAtLowerLevels_holds : supportsSeparatedAtLowerLevels := by
  intro L _ hL K t n _ htK d h h' hap Y hY Y' hY'
  classical
  obtain ⟨y, hy, hYy⟩ := (Finset.mem_filter.1 hY).2
  obtain ⟨y', hy', hYy'⟩ := (Finset.mem_filter.1 hY').2
  obtain ⟨p, hp, hne⟩ := (Finset.mem_filter.1 hy).2
  obtain ⟨p', hp', hne'⟩ := (Finset.mem_filter.1 hy').2
  have hd : d ≤ barycentreDist L K p p' := hap ⟨p, hp.1⟩ ⟨p', hp'.1⟩ hne hne'
  have hfar := SupportsSeparated.supDist_doubledBarycentre_le L hL t n y y' p p' hp hp'
  have hLpos : (0 : ℝ) < L := by
    have := NeZero.pos L
    exact_mod_cast this
  have hfarR : (_root_.YangMills.Construction.TorusFields.supDist (doubledBarycentre p) (doubledBarycentre p') : ℝ) ≤
      2 * (L : ℝ) ^ t * (1 + _root_.YangMills.Construction.TorusFields.supDist y y') := by
    exact_mod_cast hfar
  have hKt : (L : ℝ) ^ K = (L : ℝ) ^ t * (L : ℝ) ^ (K - t) := by
    rw [← pow_add, Nat.add_sub_cancel' htK]
  have hbar : d * (L : ℝ) ^ (K - t) ≤ 1 + _root_.YangMills.Construction.TorusFields.supDist y y' := by
    have h1 : d * (2 * (L : ℝ) ^ K) ≤ (_root_.YangMills.Construction.TorusFields.supDist (doubledBarycentre p) (doubledBarycentre p') : ℝ) := by
      have := hd
      rw [barycentreDist, le_div_iff₀ (by positivity)] at this
      exact this
    have h2 : (2 * (L : ℝ) ^ t) * (d * (L : ℝ) ^ (K - t)) ≤ (2 * (L : ℝ) ^ t) * (1 + _root_.YangMills.Construction.TorusFields.supDist y y') := by
      calc (2 * (L : ℝ) ^ t) * (d * (L : ℝ) ^ (K - t)) = d * (2 * (L : ℝ) ^ K) := by rw [hKt]; ring
        _ ≤ _ := h1.trans hfarR
    exact le_of_mul_le_mul_left h2 (by positivity)
  have htri : _root_.YangMills.Construction.TorusFields.supDist y y' ≤ _root_.YangMills.Construction.TorusFields.supDist y Y + _root_.YangMills.Construction.TorusFields.supDist Y Y' + _root_.YangMills.Construction.TorusFields.supDist Y' y' :=
    (_root_.YangMills.Construction.TorusFields.supDist_triangle y Y' y').trans (Nat.add_le_add_right (_root_.YangMills.Construction.TorusFields.supDist_triangle y Y Y') _)
  have hc1 := _root_.YangMills.Construction.TorusFields.supDist_comm y Y
  have hsum : _root_.YangMills.Construction.TorusFields.supDist y y' ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y' + 4 := by omega
  have hsumR : (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y' + 4 := by exact_mod_cast hsum
  linarith
end YangMills.Construction.ResponseInTheExpansion
end
