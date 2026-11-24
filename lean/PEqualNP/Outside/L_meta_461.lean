import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Field.Rat

namespace PEqualNP.Outside.L_meta_461

def triangle : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (1, 2)]

def pendants : List (Fin 6 × Fin 6) := [(0, 3), (1, 4), (2, 5)]

def net : List (Fin 6 × Fin 6) := triangle ++ pendants

lemma singleton_independent (i : Fin 6) :
    ∀ f ∈ net, ¬ (f.1 ∈ ({i} : Finset (Fin 6)) ∧ f.2 ∈ ({i} : Finset (Fin 6))) := by
  decide +revert

def SingletonTyping (τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6) : Prop :=
  ∀ e ∈ net, ∀ i : Fin 6, (τ e {i} = e.1 ∨ τ e {i} = e.2) ∧ τ e {i} ≠ i

-- Marking a leaf's neighbour forces its unique incident edge into the leaf.
lemma leaf_zero (τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6)
    (hτ : SingletonTyping τ) (c : Fin 6 × Fin 6 → ℚ)
    (hc : ∀ i v : Fin 6, ((net.filter (fun e => τ e {i} = v)).map c).sum = 0)
    (u leaf : Fin 6) (he : (u, leaf) ∈ net)
    (hunique : ∀ e ∈ net, e.1 = leaf ∨ e.2 = leaf → e = (u, leaf))
    (hlist : net.filter (fun e => e = (u, leaf)) = [(u, leaf)]) :
    c (u, leaf) = 0 := by
  have hdirection : τ (u, leaf) {u} = leaf := ((hτ (u, leaf) he u).1).resolve_left (hτ (u, leaf) he u).2
  have hfilter : net.filter (fun e => τ e {u} = leaf) = [(u, leaf)] := by
    rw [← hlist]
    apply List.filter_congr
    intro e hm
    apply decide_eq_decide.mpr
    constructor
    · intro h
      apply hunique e hm
      exact ((hτ e hm u).1).elim (fun h₁ => Or.inl (h₁.symm.trans h)) (fun h₂ => Or.inr (h₂.symm.trans h))
    · rintro rfl
      exact hdirection
  have h := hc u leaf
  rw [hfilter] at h
  simpa using h

lemma weights_sum_zero {α : Type*} (c : α → ℚ) (es : List α) (h : ∀ e ∈ es, c e = 0) :
    (es.map c).sum = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp [h e List.mem_cons_self, ih (fun f hf => h f (List.mem_cons_of_mem e hf))]

-- After removing the zero-weight pendant edges, the triangle's three
-- singleton tests force all the remaining edge weights to vanish.
set_option maxRecDepth 2048 in
lemma triangle_zero (τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6)
    (hτ : ∀ e ∈ triangle, ∀ i : Fin 6, (τ e {i} = e.1 ∨ τ e {i} = e.2) ∧ τ e {i} ≠ i)
    (c : Fin 6 × Fin 6 → ℚ)
    (hc : ∀ i v : Fin 6, ((triangle.filter (fun e => τ e {i} = v)).map c).sum = 0) :
    c (0, 1) = 0 ∧ c (0, 2) = 0 ∧ c (1, 2) = 0 := by
  have h₀₁₀ : τ (0, 1) {0} = 1 := ((hτ (0, 1) (by decide) 0).1).resolve_left (hτ (0, 1) (by decide) 0).2
  have h₀₂₀ : τ (0, 2) {0} = 2 := ((hτ (0, 2) (by decide) 0).1).resolve_left (hτ (0, 2) (by decide) 0).2
  have h₀₁₁ : τ (0, 1) {1} = 0 := ((hτ (0, 1) (by decide) 1).1).resolve_right (hτ (0, 1) (by decide) 1).2
  have h₁₂₁ : τ (1, 2) {1} = 2 := ((hτ (1, 2) (by decide) 1).1).resolve_left (hτ (1, 2) (by decide) 1).2
  have h₀₂₂ : τ (0, 2) {2} = 0 := ((hτ (0, 2) (by decide) 2).1).resolve_right (hτ (0, 2) (by decide) 2).2
  have h₁₂₂ : τ (1, 2) {2} = 1 := ((hτ (1, 2) (by decide) 2).1).resolve_right (hτ (1, 2) (by decide) 2).2
  have x₁ := hc 0 1
  have x₂ := hc 0 2
  have y₀ := hc 1 0
  have y₂ := hc 1 2
  have z₀ := hc 2 0
  have z₁ := hc 2 1
  have ha := (hτ (1, 2) (by decide) 0).1
  have hb := (hτ (0, 2) (by decide) 1).1
  have hd := (hτ (0, 1) (by decide) 2).1
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hd with hd | hd <;>
    simp [triangle, h₀₁₀, h₀₂₀, h₀₁₁, h₁₂₁, h₀₂₂, h₁₂₂, ha, hb, hd] at x₁ x₂ y₀ y₂ z₀ z₁ <;>
    grind

end PEqualNP.Outside.L_meta_461

open PEqualNP.Outside.L_meta_461

theorem PEqualNP.Outside.L_meta_461 :
    ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] →
      ∀ τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6,
        (∀ e ∈ E, ∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
          (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) →
        ∀ c : Fin 6 × Fin 6 → ℚ,
          (∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
            ∀ v : Fin 6, ((E.filter (fun e => τ e I = v)).map c).sum = 0) →
          ∀ e ∈ E, c e = 0 := by
  intro E hE τ hτ c hc
  subst E
  have ht : SingletonTyping τ := by
    intro e he i
    have h := hτ e he {i} (singleton_independent i)
    simpa only [Finset.mem_singleton] using h
  have hz (i v : Fin 6) : ((net.filter (fun e => τ e {i} = v)).map c).sum = 0 :=
    hc {i} (singleton_independent i) v
  have h03 := leaf_zero τ ht c hz 0 3 (by decide) (by decide) (by decide)
  have h14 := leaf_zero τ ht c hz 1 4 (by decide) (by decide) (by decide)
  have h25 := leaf_zero τ ht c hz 2 5 (by decide) (by decide) (by decide)
  have hp : ∀ e ∈ pendants, c e = 0 := by
    intro e he
    simp only [pendants, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> assumption
  have htriangle (i v : Fin 6) : ((triangle.filter (fun e => τ e {i} = v)).map c).sum = 0 := by
    have h := hz i v
    simp only [net, List.filter_append, List.map_append, List.sum_append] at h
    have hpendant := weights_sum_zero c (pendants.filter (fun e => τ e {i} = v))
      (fun e he => hp e (List.mem_of_mem_filter he))
    simpa only [hpendant, add_zero] using h
  obtain ⟨h01, h02, h12⟩ := triangle_zero τ
    (fun e he i => ht e (List.mem_append_left _ he) i) c htriangle
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
