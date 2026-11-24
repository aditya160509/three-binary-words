import Std.Tactic

namespace Cyclic
def fwd (n p a : Int) := if p+a < n then p+a else p+a-n
def back (n x a : Int) := if x < a then x-a+n else x-a
def hit (x p : Int) : Int := if x=p then 1 else 0

theorem noCompletion (n p q r s a b : Int) (U : Int → Int)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs0 : 0 ≤ s)
    (hpn : p < n) (hqn : q < n) (hrn : r < n) (hs : s < n)
    (order : (p < q ∧ q < r ∧ r < s) ∨ (q < r ∧ r < s ∧ s < p) ∨
      (r < s ∧ s < p ∧ p < q) ∨ (s < p ∧ p < q ∧ q < r))
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
      simp only [back]; (repeat' split) <;> omega
    have transport (y t : Int) (hy : 0 ≤ y) (hyn : y < n) (ht : 0 ≤ t) (htn : t < n) :
        hit (back n x t) y = hit x (fwd n y t) := by
      unfold hit back fwd
      (repeat' split) <;> omega
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
  have span (y t : Int) (hy : 0 ≤ y) (hyn : y < n) (ht : 0 ≤ t) (htn : t < n) :
      0 ≤ fwd n y t ∧ fwd n y t < n := by unfold fwd; split <;> omega
  have inj (y z : Int) (hy : 0 ≤ y) (hyn : y < n) (hz : 0 ≤ z) (hzn : z < n)
      (e : fwd n y a = fwd n z a) : y = z := by
    unfold fwd at e
    repeat' split at e
    all_goals omega
  have moved (y : Int) : fwd n y a ≠ y := by unfold fwd; split <;> omega
  have qmatch : fwd n q a = fwd n r b := by
    apply Classical.byContradiction
    intro neq
    have bounds := span q a (by omega) (by omega) ha han
    have h := balance _ bounds.1 bounds.2
    have n1 : fwd n q a ≠ fwd n p a := fun e => by
      have := inj q p (by omega) (by omega) hp (by omega) e; omega
    have n2 : fwd n q a ≠ fwd n s a := fun e => by
      have := inj q s (by omega) (by omega) (by omega) hs e; omega
    have h0 := nonneg (fwd n q a) p
    have h1 := nonneg (fwd n q a) (fwd n r a)
    have h2 := nonneg (fwd n q a) (fwd n s b)
    simp only [hit, if_true, if_neg n1, if_neg n2, if_neg neq, if_neg (moved q)] at h
    unfold hit at h0 h1 h2
    omega
  have rmatch : fwd n r a = q := by
    apply Classical.byContradiction
    intro neq
    have bounds := span r a (by omega) (by omega) ha han
    have h := balance _ bounds.1 bounds.2
    rw [← qmatch] at h
    have n1 : fwd n r a ≠ fwd n p a := fun e => by
      have := inj r p (by omega) (by omega) hp (by omega) e; omega
    have n2 : fwd n r a ≠ fwd n s a := fun e => by
      have := inj r s (by omega) (by omega) (by omega) hs e; omega
    have h0 := nonneg (fwd n r a) p
    have h1 := nonneg (fwd n r a) (fwd n s b)
    simp only [hit, if_true, if_neg n1, if_neg n2, if_neg neq] at h
    unfold hit at h0 h1
    omega
  have pmatch : p = fwd n s a := by
    apply Classical.byContradiction
    intro neg
    have h := balance p hp (by omega)
    rw [← qmatch] at h
    have eq : hit p (fwd n r a) = hit p q := congrArg (hit p) rmatch
    rw [eq] at h
    have ne : p ≠ fwd n p a := Ne.symm (moved p)
    have h0 := nonneg p (fwd n s b)
    simp only [hit, if_true, if_neg neg, if_neg ne] at h
    unfold hit at h0
    omega
  unfold fwd at rmatch pmatch
  repeat' split at rmatch
  all_goals repeat' split at pmatch
  all_goals omega

#print axioms noCompletion

/-- A four-letter word, most significant bit first, in a common insertion frame. -/
def padded (p q r s : Int) (word : Nat) (filler : Int → Int) (x : Int) : Int :=
  if x = p then (word / 8 % 2 : Nat)
  else if x = q then (word / 4 % 2 : Nat)
  else if x = r then (word / 2 % 2 : Nat)
  else if x = s then (word % 2 : Nat)
  else filler x

def Rotates (n : Int) (u v : Int → Int) : Prop :=
  ∃ a, 0 ≤ a ∧ a < n ∧ ∀ x, 0 ≤ x → x < n → v x = u (back n x a)

/-- At all unmarked columns every row reads the same binary filler.
Requiring pairwise rotations here refers to the very same completed rows. -/
def Realizes4 (i j k : Nat) : Prop :=
  ∃ (n p q r s : Int) (h : Int → Int),
    0 ≤ p ∧ p < q ∧ q < r ∧ r < s ∧ s < n ∧
    (∀ x, h x = 0 ∨ h x = 1) ∧
    ∀ u ∈ [i,j,k], ∀ v ∈ [i,j,k],
      Rotates n (padded p q r s u h) (padded p q r s v h)

theorem bad3_5_12 : ¬ Realizes4 3 5 12 := by
  rintro ⟨n,p,q,r,s,h,hp,hpq,hqr,hrs,hs,_,rot⟩
  obtain ⟨a,ha,han,va⟩ := rot 3 (by decide) 5 (by decide)
  obtain ⟨b,hb,hbn,wb⟩ := rot 3 (by decide) 12 (by decide)
  apply noCompletion n s p q r a b (fun x => 1 - padded p q r s 3 h x) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ha han hb hbn
  · intro x hx hxn
    simp only [← va x hx hxn]
    unfold padded hit
    repeat' split
    all_goals first | omega | decide
  · intro x hx hxn
    simp only [← wb x hx hxn, ← va x hx hxn]
    unfold padded hit
    repeat' split
    all_goals first | omega | decide

theorem bad3_10_12 : ¬ Realizes4 3 10 12 := by
  rintro ⟨n,p,q,r,s,h,hp,hpq,hqr,hrs,hs,_,rot⟩
  obtain ⟨a,ha,han,va⟩ := rot 3 (by decide) 10 (by decide)
  obtain ⟨b,hb,hbn,wb⟩ := rot 3 (by decide) 12 (by decide)
  apply noCompletion n q r s p a b (padded p q r s 3 h) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ha han hb hbn
  · intro x hx hxn
    simp only [← va x hx hxn]
    unfold padded hit
    repeat' split
    all_goals first | omega | decide
  · intro x hx hxn
    simp only [← wb x hx hxn, ← va x hx hxn]
    unfold padded hit
    repeat' split
    all_goals first | omega | decide

theorem bad5_6_9 : ¬ Realizes4 5 6 9 := by
  rintro ⟨n,p,q,r,s,h,hp,hpq,hqr,hrs,hs,_,rot⟩
  obtain ⟨a,ha,han,va⟩ := rot 6 (by decide) 5 (by decide)
  obtain ⟨b,hb,hbn,wb⟩ := rot 6 (by decide) 9 (by decide)
  apply noCompletion n p q r s a b (padded p q r s 6 h) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ha han hb hbn
  · intro x hx hxn
    simp only [← va x hx hxn]
    unfold padded hit
    repeat' split
    all_goals first | omega | decide
  · intro x hx hxn
    simp only [← wb x hx hxn, ← va x hx hxn]
    unfold padded hit
    repeat' split
    all_goals first | omega | decide

theorem bad6_9_10 : ¬ Realizes4 6 9 10 := by
  rintro ⟨n,p,q,r,s,h,hp,hpq,hqr,hrs,hs,_,rot⟩
  obtain ⟨a,ha,han,va⟩ := rot 6 (by decide) 10 (by decide)
  obtain ⟨b,hb,hbn,wb⟩ := rot 6 (by decide) 9 (by decide)
  apply noCompletion n r s p q a b (fun x => 1 - padded p q r s 6 h x) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ha han hb hbn
  · intro x hx hxn
    simp only [← va x hx hxn]
    unfold padded hit
    repeat' split
    all_goals first | omega | decide
  · intro x hx hxn
    simp only [← wb x hx hxn, ← va x hx hxn]
    unfold padded hit
    repeat' split
    all_goals first | omega | decide

def digit (code : Nat) (x : Int) : Int :=
  if code.testBit x.toNat then 1 else 0

private theorem ofCert (i j k n p q r s h : Nat)
    (hord : p < q ∧ q < r ∧ r < s ∧ s < n)
    (cert : ∀ u ∈ [i,j,k], ∀ v ∈ [i,j,k], ∃ a : Fin n, ∀ x : Fin n,
      padded p q r s v (digit h) x.val =
        padded p q r s u (digit h) (back n x.val a.val)) :
    Realizes4 i j k := by
  refine ⟨n,p,q,r,s,digit h,by omega,by omega,by omega,by omega,by omega,?_,?_⟩
  · intro x; unfold digit; split <;> simp
  · intro u hu v hv
    obtain ⟨a,ha⟩ := cert u hu v hv
    refine ⟨a.val,by omega,by omega,?_⟩
    intro x hx hxn
    have eq := ha ⟨x.toNat, by omega⟩
    simpa [Int.toNat_of_nonneg hx] using eq

private theorem good3_5_6 : Realizes4 3 5 6 :=
  ofCert 3 5 6 6 0 1 3 5 40 (by decide) (by decide)

private theorem good3_5_9 : Realizes4 3 5 9 :=
  ofCert 3 5 9 6 0 2 4 5 58 (by decide) (by decide)

private theorem good3_5_10 : Realizes4 3 5 10 :=
  ofCert 3 5 10 5 0 1 2 4 20 (by decide) (by decide)

private theorem good3_6_9 : Realizes4 3 6 9 :=
  ofCert 3 6 9 4 0 1 2 3 12 (by decide) (by decide)

private theorem good3_6_10 : Realizes4 3 6 10 :=
  ofCert 3 6 10 6 0 2 3 4 58 (by decide) (by decide)

private theorem good3_6_12 : Realizes4 3 6 12 :=
  ofCert 3 6 12 4 0 1 2 3 12 (by decide) (by decide)

private theorem good3_9_10 : Realizes4 3 9 10 :=
  ofCert 3 9 10 6 1 2 3 5 40 (by decide) (by decide)

private theorem good3_9_12 : Realizes4 3 9 12 :=
  ofCert 3 9 12 4 0 1 2 3 12 (by decide) (by decide)

private theorem good5_6_10 : Realizes4 5 6 10 :=
  ofCert 5 6 10 5 0 1 3 4 18 (by decide) (by decide)

private theorem good5_6_12 : Realizes4 5 6 12 :=
  ofCert 5 6 12 6 0 1 2 4 58 (by decide) (by decide)

private theorem good5_9_10 : Realizes4 5 9 10 :=
  ofCert 5 9 10 5 1 2 3 4 20 (by decide) (by decide)

private theorem good5_9_12 : Realizes4 5 9 12 :=
  ofCert 5 9 12 6 1 3 4 5 40 (by decide) (by decide)

private theorem good5_10_12 : Realizes4 5 10 12 :=
  ofCert 5 10 12 5 0 2 3 4 20 (by decide) (by decide)

private theorem good6_9_12 : Realizes4 6 9 12 :=
  ofCert 6 9 12 4 0 1 2 3 6 (by decide) (by decide)

private theorem good6_10_12 : Realizes4 6 10 12 :=
  ofCert 6 10 12 6 0 2 4 5 20 (by decide) (by decide)

private theorem good9_10_12 : Realizes4 9 10 12 :=
  ofCert 9 10 12 6 0 1 3 5 53 (by decide) (by decide)

def forbidden : List (Nat × Nat × Nat) := [(3,5,12), (3,10,12), (5,6,9), (6,9,10)]

/-- The numbers 3, 5, 6, 9, 10, 12 encode the six four-bit words of weight two. -/
theorem classify (i j k : Nat) (hi : i ∈ [3,5,6,9,10,12]) (hj : j ∈ [3,5,6,9,10,12])
    (hk : k ∈ [3,5,6,9,10,12]) (hij : i < j) (hjk : j < k) :
    Realizes4 i j k ↔ (i,j,k) ∉ forbidden := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj hk
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> first | omega | skip
  all_goals first
    | exact ⟨fun _ => by decide, fun _ => good3_5_6⟩
    | exact ⟨fun _ => by decide, fun _ => good3_5_9⟩
    | exact ⟨fun _ => by decide, fun _ => good3_5_10⟩
    | exact ⟨fun h => False.elim (bad3_5_12 h), fun h => False.elim (h (by decide))⟩
    | exact ⟨fun _ => by decide, fun _ => good3_6_9⟩
    | exact ⟨fun _ => by decide, fun _ => good3_6_10⟩
    | exact ⟨fun _ => by decide, fun _ => good3_6_12⟩
    | exact ⟨fun _ => by decide, fun _ => good3_9_10⟩
    | exact ⟨fun _ => by decide, fun _ => good3_9_12⟩
    | exact ⟨fun h => False.elim (bad3_10_12 h), fun h => False.elim (h (by decide))⟩
    | exact ⟨fun h => False.elim (bad5_6_9 h), fun h => False.elim (h (by decide))⟩
    | exact ⟨fun _ => by decide, fun _ => good5_6_10⟩
    | exact ⟨fun _ => by decide, fun _ => good5_6_12⟩
    | exact ⟨fun _ => by decide, fun _ => good5_9_10⟩
    | exact ⟨fun _ => by decide, fun _ => good5_9_12⟩
    | exact ⟨fun _ => by decide, fun _ => good5_10_12⟩
    | exact ⟨fun h => False.elim (bad6_9_10 h), fun h => False.elim (h (by decide))⟩
    | exact ⟨fun _ => by decide, fun _ => good6_9_12⟩
    | exact ⟨fun _ => by decide, fun _ => good6_10_12⟩
    | exact ⟨fun _ => by decide, fun _ => good9_10_12⟩

#print axioms classify

/-- The least equivalence relation generated by the filler equalities. -/
inductive Linked {X : Type} (edge : X → X → Prop) : X → X → Prop
  | refl (x) : Linked edge x x
  | step {x y} : edge x y → Linked edge x y
  | symm {x y} : Linked edge x y → Linked edge y x
  | trans {x y z} : Linked edge x y → Linked edge y z → Linked edge x z

/-- X may be a cycle, with edges between the base-word positions read at
an insertion and unary pins for the original letters. -/
theorem components {X : Type} (edge : X → X → Prop) (pin : X → Bool → Prop) :
    (∃ f : X → Bool, (∀ x y, edge x y → f x = f y) ∧
      ∀ x b, pin x b → f x = b) ↔
    ¬ ∃ x y, pin x true ∧ pin y false ∧ Linked edge x y := by
  classical
  constructor
  · rintro ⟨f,he,hp⟩ ⟨x,y,hx,hy,hxy⟩
    have same {z w} (path : Linked edge z w) : f z = f w := by
      induction path with
      | refl => rfl
      | step h => exact he _ _ h
      | symm _ ih => exact ih.symm
      | trans _ _ ih jk => exact ih.trans jk
    have eq := same hxy
    rw [hp _ _ hx,hp _ _ hy] at eq
    contradiction
  · intro safe
    let one (x : X) := ∃ y, pin y true ∧ Linked edge y x
    refine ⟨fun x => decide (one x), ?_, ?_⟩
    · intro x y h
      have move {v w} (path : Linked edge v w) : one v → one w := by
        rintro ⟨z,hz,hzv⟩
        exact ⟨z,hz,.trans hzv path⟩
      have iffxy : one x ↔ one y := ⟨move (.step h),move (.symm (.step h))⟩
      simp [propext iffxy]
    · intro x b h
      cases b with
      | false =>
        have no : ¬ one x := by
          rintro ⟨y,hy,path⟩
          exact safe ⟨y,x,hy,h,path⟩
        simp [no]
      | true =>
        have yes : one x := ⟨x,h,.refl x⟩
        simp [yes]

#print axioms components

/-- Prefix sums in the traversal order of one generating rotation. -/
def scan (d : Nat → Int) : Nat → Int
  | 0 => 0
  | t+1 => scan d t + d t

private theorem scan_add (f : Nat → Int) (k n : Nat) :
    scan f (k+n) = scan f k + scan (fun t => f (k+t)) n := by
  induction n with
  | zero => simp [scan]
  | succ n ih => simp [scan,ih,Int.add_assoc]

private theorem scan_ext (f g : Nat → Int) (h : ∀ t, f t = g t) (n : Nat) :
    scan f n = scan g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [scan,ih,h]

/-- An exact range test for binary integration of two commuting differences
in the traversal order of a generator.  k expresses the second rotation
as a power of the first. -/
theorem primitiveScan (d e : Nat → Int) (n k : Nat) (hn : 0 < n)
    (period : ∀ t, d (n+t) = d t) (dz : scan d n = 0) (ez : scan e n = 0)
    (curl : ∀ t, e (t+1) - e t = d (t+k) - d t) :
    (∃ lo, ∀ t, lo ≤ scan d t ∧ scan d t ≤ lo+1) ↔
    ∃ u : Nat → Int, (∀ t, u t = 0 ∨ u t = 1) ∧ (∀ t, u (n+t) = u t) ∧
      (∀ t, u (t+1) - u t = d t) ∧ (∀ t, u (t+k) - u t = e t) := by
  constructor
  · rintro ⟨lo,bound⟩
    let u (t : Nat) := scan d t - lo
    have per (t : Nat) : u (n+t) = u t := by
      unfold u
      rw [scan_add,dz,scan_ext _ _ period]
      omega
    have step (t : Nat) : u (t+1) - u t = d t := by simp [u,scan]; omega
    let c := e 0 - (u k - u 0)
    have residual (t : Nat) : e t - (u (t+k) - u t) = c := by
      induction t with
      | zero => simp [c]
      | succ t ih =>
        have h := curl t
        have i := step (t+k)
        have j := step t
        rw [Nat.succ_add]
        change e (t+1) - (u ((t+k)+1) - u (t+1)) = c
        omega
    have total (t : Nat) : scan e t =
        scan (fun j => u (k+j)) t - scan u t + (t : Int)*c := by
      induction t with
      | zero => simp [scan]
      | succ t ih =>
        have h := residual t
        rw [Nat.add_comm t k] at h
        simp only [scan, ih, Int.natCast_succ, Int.add_mul, Int.one_mul]
        omega
    have shifted : scan (fun j => u (k+j)) n = scan u n := by
      have left := scan_add u k n
      have right := scan_add u n k
      rw [Nat.add_comm k n] at left
      rw [scan_ext _ _ per] at right
      omega
    have zeroProd : (n : Int)*c = 0 := by
      have := total n
      rw [ez,shifted] at this
      omega
    have cz : c = 0 := (Int.mul_eq_zero.mp zeroProd).resolve_left (by omega)
    refine ⟨u, ?_, per, step, ?_⟩
    · intro t; have := bound t; dsimp [u]; omega
    · intro t; have := residual t; omega
  · rintro ⟨u,bits,_,step,_⟩
    have integrates (t : Nat) : scan d t = u t - u 0 := by
      induction t with
      | zero => simp [scan]
      | succ t ih => have := step t; simp only [scan,ih]; omega
    refine ⟨-u 0, ?_⟩
    intro t; have := bits t; rw [integrates]; omega

#print axioms primitiveScan
end Cyclic
