(* In Isabelle (version Isabelle2011) zero divides zero *)

theory ZeroDividesZero
imports Nat Rings
begin

(* dvd is defined in the Rings.thy *)
theorem zero_divides_zero : "(0 :: nat) dvd (0 :: nat)"
unfolding dvd_def
apply (rule exI)
apply simp
done
