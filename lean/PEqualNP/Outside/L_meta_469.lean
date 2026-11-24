import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Card

namespace PEqualNP.Outside.L_meta_469

def slots {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)

lemma slots_card {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    (slots H).card = H.edgeSet.ncard := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · intro p hp
    simp only [slots, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simpa using hp.2
  · intro p hp q hq h
    simp only [slots, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd hq.1 (by rw [← h1, ← h2]; exact not_lt.mpr hp.1.le)
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases lt_trichotomy a b with hab | hab | hab
      · exact ⟨(a, b), by simp [slots, hab, he], rfl⟩
      · exact absurd hab he.ne
      · exact ⟨(b, a), by simp [slots, hab, he.symm], Sym2.eq_swap⟩

lemma index_inj {base q r a b : ℕ} (ha : a < base) (hb : b < base)
    (h : base * q + a = base * r + b) : q = r ∧ a = b := by
  rcases lt_trichotomy q r with hlt | heq | hgt
  · have hstep := Nat.mul_le_mul_left base (show q + 1 ≤ r from hlt)
    rw [Nat.mul_succ] at hstep
    omega
  · subst r
    exact ⟨rfl, by omega⟩
  · have hstep := Nat.mul_le_mul_left base (show r + 1 ≤ q from hgt)
    rw [Nat.mul_succ] at hstep
    omega

def offset {m : ℕ} (T : Finset (Fin m)) (u : Fin m) (j : ℕ) : ℕ :=
  2 * j + if u ∈ T then 1 else 0

lemma offset_lt {m k : ℕ} (T : Finset (Fin m)) (u : Fin m) {j : ℕ} (hj : j < k) :
    offset T u j < 2 * k := by
  unfold offset
  split <;> omega

lemma offset_parity {m : ℕ} (T : Finset (Fin m)) (u : Fin m) (j : ℕ) :
    offset T u j % 2 = 1 ↔ u ∈ T := by
  unfold offset
  split <;> rename_i h <;> simp [h]

lemma parity_recovers_offset {m : ℕ} (T : Finset (Fin m)) (u : Fin m) (i : ℕ)
    (hpar : i % 2 = 1 ↔ u ∈ T) : offset T u (i / 2) = i := by
  have hdiv := Nat.div_add_mod i 2
  unfold offset
  split
  · next h => have hm := hpar.mpr h; omega
  · next h => have hm : i % 2 ≠ 1 := fun he => h (hpar.mp he); omega

def innerIndex {m : ℕ} (k : ℕ) (T : Finset (Fin m)) (p : (Fin m × Fin m) × ℕ) : ℕ :=
  m + 2 * k * (p.1.1.val * m + p.1.2.val) + offset T p.1.1 p.2

lemma index_lt {m k : ℕ} (u v : Fin m) {i : ℕ} (hi : i < 2 * k) :
    m + 2 * k * (u.val * m + v.val) + i < m + 2 * k * (m * m) := by
  have hu := Nat.mul_le_mul_right m (show u.val + 1 ≤ m from u.isLt)
  rw [Nat.succ_mul] at hu
  have hv := v.isLt
  have hmul := Nat.mul_le_mul_left (2 * k) (show u.val * m + v.val + 1 ≤ m * m by omega)
  rw [Nat.mul_succ] at hmul
  omega

end PEqualNP.Outside.L_meta_469

open PEqualNP.Outside.L_meta_469

theorem PEqualNP.Outside.L_meta_469 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m))
      (T' : Finset (Fin (m + 2 * k * (m * m)))),
      (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨
        ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧
          x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) →
      T'.card = T.card + k * H.edgeSet.ncard := by
  classical
  intro m k H T T' hT
  let P := slots H ×ˢ Finset.range k
  have hset : T'.image Fin.val = T.image Fin.val ∪ P.image (innerIndex k T) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_union, P, Finset.mem_product, Finset.mem_range,
      slots, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases (hT x).mp hx with ⟨u, hu, hux⟩ | ⟨u, v, i, hi, huv, hadj, heq, hpar⟩
      · exact Or.inl ⟨u, hu, hux.symm⟩
      · refine Or.inr ⟨((u, v), i / 2), ⟨⟨huv, hadj⟩, by omega⟩, ?_⟩
        rw [innerIndex, parity_recovers_offset T u i hpar, heq]
    · rintro (⟨u, hu, rfl⟩ | ⟨⟨⟨u, v⟩, j⟩, ⟨⟨huv, he⟩, hj⟩, rfl⟩)
      · let x : Fin (m + 2 * k * (m * m)) := ⟨u.val, u.isLt.trans_le (Nat.le_add_right _ _)⟩
        exact ⟨x, (hT x).mpr (Or.inl ⟨u, hu, rfl⟩), rfl⟩
      · have hlt := offset_lt T u hj
        let x : Fin (m + 2 * k * (m * m)) := ⟨innerIndex k T ((u, v), j), index_lt u v hlt⟩
        exact ⟨x, (hT x).mpr (Or.inr ⟨u, v, offset T u j, hlt, huv, he, rfl, offset_parity T u j⟩), rfl⟩
  have hdisjoint : Disjoint (T.image Fin.val) (P.image (innerIndex k T)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨⟨⟨v, w⟩, j⟩, _, h⟩ := Finset.mem_image.mp hn'
    have hu := u.isLt
    change m + 2 * k * (v.val * m + w.val) + offset T v j = u.val at h
    omega
  have hinj : Set.InjOn (innerIndex k T) (P : Set ((Fin m × Fin m) × ℕ)) := by
    rintro ⟨⟨u, v⟩, j⟩ h ⟨⟨u', v'⟩, j'⟩ h' heq
    have hj := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_coe.mp h)).2
    have hj' := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_coe.mp h')).2
    change m + 2 * k * (u.val * m + v.val) + offset T u j =
      m + 2 * k * (u'.val * m + v'.val) + offset T u' j' at heq
    have hleft : offset T u j < 2 * k := offset_lt T u hj
    have hright : offset T u' j' < 2 * k := offset_lt T u' hj'
    have hbase : 2 * k * (u.val * m + v.val) + offset T u j =
        2 * k * (u'.val * m + v'.val) + offset T u' j' := by omega
    obtain ⟨hcode, ho⟩ := index_inj hleft hright hbase
    have hcode' : m * u.val + v.val = m * u'.val + v'.val := by
      simpa [Nat.mul_comm m] using hcode
    obtain ⟨hu, hv⟩ := index_inj v.isLt v'.isLt hcode'
    have hu' : u = u' := Fin.ext hu
    have hv' : v = v' := Fin.ext hv
    subst u'
    subst v'
    unfold offset at ho
    have he : j = j' := by omega
    subst j'
    rfl
  rw [← Finset.card_image_of_injective T' Fin.val_injective, hset,
    Finset.card_union_of_disjoint hdisjoint, Finset.card_image_of_injective T Fin.val_injective,
    Finset.card_image_of_injOn hinj]
  rw [show P.card = H.edgeSet.ncard * k by simp [P, Finset.card_product, slots_card], Nat.mul_comm H.edgeSet.ncard k]
