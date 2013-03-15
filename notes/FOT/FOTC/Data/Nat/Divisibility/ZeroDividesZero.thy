(* In Isabelle, zero divides zero *)

theory ZeroDividesZero
imports Nat Rings
begin

(* dvd is defined in the Rings.thy *)

(* Proof suggested by Isabelle 2012 *)
theorem zero_divides_zero : "(0 :: nat) dvd (0 :: nat)"
by auto


(* Old proof *)
theorem zero_divides_zero_old : "(0 :: nat) dvd (0 :: nat)"
unfolding dvd_def
apply (rule exI)
apply simp
done

