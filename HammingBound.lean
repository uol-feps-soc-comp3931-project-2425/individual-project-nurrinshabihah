 /-
Author: Nurrin Shabihah

# Hamming bound

The Hamming bound provides a limit on the number of codewords a code can have while ensuring error correction 
within a given distance. It calculates the maximum number of disjoint Hamming balls that can fit in the space 
of a finite Π-type, where each ball corresponds to the set of elements differing from a codeword in at most a 
fixed number of positions.
-/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

-- alphabet q is a set of symbols of size q, which consists of {0,...,q-1}
-- ensures alphabet type is finite and decidable
def alphabet (q : ℕ) := Fin q

instance (q : ℕ) : Fintype (alphabet q) := Fin.fintype q
instance (q : ℕ) : DecidableEq (alphabet q) := by
  unfold alphabet
  infer_instance


--`codeword q n` is a codeword of length `n` over an alphabet of size `q`
-- ensures codeword type is finite and decidable
def codeword (q n : ℕ) := Fin n → alphabet q
instance (q n : ℕ) : Fintype (codeword q n) := Pi.instFintype
instance (q : ℕ) : DecidableEq (codeword q n) := by
  unfold codeword
  infer_instance

-- defines a Hamming ball of radius `r` centered at codeword `x`
-- consists of all codewords `y` such that the Hamming distance between `x` and `y` is at most `r`
def hammingBall {q n : ℕ} (x : codeword q n) (r : ℕ) : Finset (codeword q n) :=
  Finset.filter (fun y => hammingDist x y ≤ r) Finset.univ

-- the volume of a Hamming ball of radius `r` is the number of codewords within that radius from any given center 
def volumeHamming (q n r : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (r + 1), Nat.choose n i * (q - 1) ^ i

/--
1. Proof disjoint of Hamming Balls
The proof follows by contradiction: if two distinct codewords have overlapping Hamming balls, then 
their Hamming distance would be less than `d`, contradicting the definition of a code.
-/
lemma hammingDisjoint {q n d : ℕ} (C : Finset (codeword q n)) 
-- minimum distance between distinct codewords is at least d
(hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → hammingDist x y ≥ d) 
-- to ensure Hamming balls cannot overlap
(ht : 2 * r < d):
-- Goal : Show that for any two distinct codewords v, w ∈ C, their Hamming balls do not overlap.
∀ v ∈ C, ∀ w ∈ C, v ≠ w → Disjoint (hammingBall v r) (hammingBall w r) := by

-- Assume for contradiction that there exist distinct `v, w ∈ C` whose Hamming balls overlap
intro v hv w hw hdiff
rw [Finset.disjoint_iff_ne]
-- Let z exists in both balls
rintro z hzv c hzw rfl

-- how elements belong to a filtered Finset
 -- z ∈ Finset.univ ∧ hammingDist v z ≤ t
 -- extract the second condition
have hammingDist_v : hammingDist v z ≤ r := (Finset.mem_filter.mp hzv).2
have hammingDist_w : hammingDist w z ≤ r := (Finset.mem_filter.mp hzw).2

-- show the symmetry of hamming distance
have hammingDist_w_symm : hammingDist z w ≤ r := by
    rw [hammingDist_comm]  
    exact hammingDist_w

-- using the triangle inequality: d(v, w) ≤ d(v, z) + d(z, w)
have hamming_triangle : hammingDist v w ≤ hammingDist v z + hammingDist z w := 
  hammingDist_triangle v z w
   
-- upper bound the sum using `r`
have hamming_bound : hammingDist v z + hammingDist z w ≤ r + r := 
  -- hammingDist v z + hammingDist z w ≤ t + t
  add_le_add hammingDist_v hammingDist_w_symm

-- rewrite r+r=2r and apply assumption 2r<d
have h_eq : r + r = 2 * r := by ring
have h_final : 2 * r < d := ht

-- contradiction: d(v, w) < d but should be ≥ d
have h_contra : hammingDist v w < d := 
  -- hammingDist v w < d
  lt_of_le_of_lt (le_trans hamming_triangle hamming_bound) (by rw [h_eq]; exact h_final)
have h_min_dist : hammingDist v w ≥ d := hC v hv w hw hdiff

-- arrive to contradiction
have h_false : False := by
    linarith [h_contra, h_min_dist]  

contradiction


/--
2. Count the cardinality of Hamming Ball
The cardinality of a Hamming ball of radius `r` centered at a codeword `y` is equal to the volume of the 
Hamming ball. This follows by viewing the ball as a disjoint union of spheres.
-/
-- count the number of codewords at each Hamming distance i from y and then sum over all i from 0 to r
lemma hammingCard {q n r : ℕ} (y : codeword q n):
(hammingBall y r).card = volumeHamming q n r := by
unfold hammingBall volumeHamming
-- Hamming ball of radius r s the disjoint union of Hamming spheres of radius i for i ∈ {0,1,...,r}, 
-- each Hamming sphere of radius i contains (n choose i)*(q-1)^i codewords

-- 1. Define a Hamming sphere of radius i
let hammingSphere (y : codeword q n) (i : ℕ):= 
Finset.filter (fun z => hammingDist y z = i) Finset.univ

-- 2. Disjointness of Hamming spheres at a different distances
have h_disjoint : ∀ i j , i ∈ Finset.range (r + 1) → j ∈ Finset.range (r + 1) → i ≠ j → 
Disjoint (hammingSphere y i) (hammingSphere y j):= by 
  rintro i j hi hj hdiff
  rw [Finset.disjoint_iff_ne]
  rintro z hzi c hzj rfl
  have h_dist_i := (Finset.mem_filter.mp hzi).2
  have h_dist_j := (Finset.mem_filter.mp hzj).2
  exact hdiff (h_dist_i.symm.trans h_dist_j)

-- 3. Union of all spheres is the full Hamming ball
have h_union : Finset.filter (fun z => hammingDist y z ≤ r) Finset.univ = Finset.biUnion (Finset.range (r + 1)) (hammingSphere y) := by
  apply Finset.ext
  intro z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
  constructor
  intro hz
  use hammingDist y z
  simp [hammingSphere, hz, Finset.mem_range.mpr (Nat.lt_succ_of_le hz)]
  rintro ⟨i, hi, hz⟩
  rw [(Finset.mem_filter.mp hz).2]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)

-- 4. Inductive argument to count sphere sizes
have sphereCard : ∀ i, i ∈ Finset.range (r + 1) → 
  (hammingSphere y i).card = Nat.choose n i * (q - 1) ^ i := by
  intro i hi
  -- base case: i=0
  -- the only word at distance 0 is y itself so cardinality is 1
  induction i with 
  | zero =>
  simp [hammingSphere] 
  --rw [Nat.choose_zero_right, pow_zero, mul_one]
  rw [Finset.card_eq_one]
  use y
  apply Finset.ext
  intro z
  simp
  rw [eq_comm]
  | succ i ih  => 
  sorry
-- inductive step: i=i+1
-- construct bipartite graph
-- define bipartite relations
-- apply double counting


--3. Prove the Hamming bound theorem
theorem hammingBound {q n d : ℕ} (C : Finset (codeword q n)) 
(hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → hammingDist x y ≥ d) 
(hd : d ≥ 1)
(ht : 2 * t < d):
C.card ≤ (q ^ n)/(∑ i ∈ Finset.range (r + 1), Nat.choose n i * (q - 1) ^ i) := by
sorry
-- 1. Disjointness
--have disjoint_balls := hammingDisjoint C hC ht

-- 2. Count the number of words in all Hamming balls
-- Use cardinality of Hamming sphere to calculate the words in each ball
--have hammingCard {q n r : ℕ} (y : codeword q n) :
--(hammingBall y r).card = ∑ i ∈ Finset.range (r + 1), Nat.choose n i * (q - 1) ^ i := by
 
-- 3. F^n represents the space of all possible codewords of length n, on alphabet of size q. 
-- All words in  belong to F^n (union of spheres is a subset of F^n) and is a disjoint, so it 
-- cannot exceed |F^n| = q^n



