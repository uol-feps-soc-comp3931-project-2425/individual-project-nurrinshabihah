 /-
Author: Nurrin Shabihah

# Disjointness of Hamming balls

This file formalises a lemma from coding theory: 
if two codewods ina code have Hamming distance of at least d, then their respective 
Hamming balls of radius r are disjoint, given that 2r < d. This disjointness condition 
is a foundational lemma in the classical proof for Hamming bound.
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


/--
Main Lemma: Proof disjoint of Hamming Balls
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




