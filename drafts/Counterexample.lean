import Std.Tactic

namespace Cyclic
def fwd (n p a : Int) := if p+a < n then p+a else p+a-n
def back (n x a : Int) := if x < a then x-a+n else x-a
def hit (x p : Int) : Int := if x=p then 1 else 0

theorem noCompletion (n p q r s a b : Int) (U : Int → Int)
    (hp : 0 ≤ p) (hpq : p < q) (hqr : q < r) (hrs : r < s) (hs : s < n)
    (ha : 0 ≤ a) (han : a < n) (hb : 0 ≤ b) (hbn : b < n)
    (D : ∀ x, 0 ≤ x → x < n →
      U (back n x a) - U x = hit x s - hit x r)
    (F : ∀ x, 0 ≤ x → x < n →
      U (back n x b) - U (back n x a) = hit x p - hit x q) : False := by
  have ha0 : a ≠ 0 := by
    intro h
    have := D s (by omega) hs
    simp [h, back, hit, show ¬ s < 0 by omega, show s ≠ r by omega] at this
  have hab : a ≠ b := by
    intro h
    have := F p hp (by omega)
    simp [h, hit, show p ≠ q by omega] at this
  have balance (x : Int) (hx : 0 ≤ x) (hxn : x < n) :
      hit x p + hit x (fwd n q a) + hit x (fwd n r a) + hit x (fwd n s b) =
      hit x (fwd n p a) + hit x q + hit x (fwd n r b) + hit x (fwd n s a) := by
    have range (t : Int) (ht : 0 ≤ t) (htn : t < n) :
        0 ≤ back n x t ∧ back n x t < n := by unfold back; split <;> omega
    have comm : back n (back n x a) b = back n (back n x b) a := by
      simp only [back]; split_ifs <;> omega
    have transport (y t : Int) (hy : 0 ≤ y) (hyn : y < n) (ht : 0 ≤ t) (htn : t < n) :
        hit (back n x t) y = hit x (fwd n y t) := by
      unfold hit back fwd
      split_ifs <;> omega
    have h1 := D (back n x b) (range b hb hbn).1 (range b hb hbn).2
    have h2 := D (back n x a) (range a ha han).1 (range a ha han).2
    have h3 := F (back n x a) (range a ha han).1 (range a ha han).2
    have h4 := F x hx hxn
    rw [comm] at h3
    rw [transport s b (by omega) hs hb hbn, transport r b (by omega) (by omega) hb hbn] at h1
    rw [transport s a (by omega) hs ha han, transport r a (by omega) (by omega) ha han] at h2
    rw [transport p a hp (by omega) ha han, transport q a (by omega) (by omega) ha han] at h3
    omega
  have nonneg (x y : Int) : 0 ≤ hit x y := by unfold hit; split <;> omega
  have force (x : Int) (hx : 0 ≤ x) (hxn : x < n)
      (present : x = p ∨ x = fwd n q a ∨ x = fwd n r a) :
      x = fwd n p a ∨ x = q ∨ x = fwd n r b ∨ x = fwd n s a := by
    have h := balance x hx hxn
    by_contra! neg
    obtain ⟨h1,h2,h3,h4⟩ := neg
    simp [hit,h1,h2,h3,h4] at h
    rcases present with e|e|e <;> simp [e] at h <;> split_ifs at h <;> omega
  have qmatch : fwd n q a = fwd n r b := by
    have h := force (fwd n q a) (by unfold fwd; split <;> omega)
      (by unfold fwd; split <;> omega) (Or.inr (Or.inl rfl))
    unfold fwd at *; split_ifs at h <;> omega
  have rmatch : fwd n r a = q := by
    have h := force (fwd n r a) (by unfold fwd; split <;> omega)
      (by unfold fwd; split <;> omega) (Or.inr (Or.inr rfl))
    unfold fwd at h ⊢; split_ifs at * <;> omega
  have pmatch : p = fwd n s a := by
    have h := balance p hp (by omega)
    rw [← qmatch, ← rmatch] at h
    by_contra! neg
    have ne : p ≠ fwd n p a := by unfold fwd; split <;> omega
    simp [hit, neg, ne] at h
    split_ifs at h <;> omega
  unfold fwd at rmatch pmatch
  split_ifs at * <;> omega

#print axioms noCompletion
end Cyclic
