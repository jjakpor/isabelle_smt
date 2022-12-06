theory Regular      
  imports Words
begin


(* Regulars *)
datatype 'a regex = None | Const "'a word" | Union "'a regex" "'a regex" | Concat "'a regex" "'a regex" | Star "'a regex"


primrec pow:: "'a word set \<Rightarrow> nat \<Rightarrow> 'a word set" 
  where
   "pow s 0 = {Epsilon}"|
   "pow s (Suc n) = {u*v |u v. u:s & v:(pow s n)}"

lemma pow_neutral: "Epsilon \<in> pow s 0"
  apply(auto)
  done

primrec lang:: "'a regex \<Rightarrow> 'a word set" 
  where
   "lang None = {}"|
   "lang (Const w) = {w}" |
   "lang (Union r1 r2) = (lang r1) Un (lang r2)" |
   "lang (Concat r1 r2) = {u*v |u v. u:(lang r1) & v:(lang r2)}"|
   "lang (Star r) = (\<Union>n. pow (lang r) n)"

(* Epsilon is always in the Kleene closure of a regular expression *)
lemma epsi_in_star: "Epsilon \<in> lang (Star r)"
proof - 
  have "Epsilon \<in> (pow (lang  r) 0)" by (simp add: pow_neutral)
  hence "EX n. Epsilon \<in> (pow (lang  r) n)" by (rule exI)
  hence "Epsilon \<in> (\<Union>n. pow (lang  r) n)" by simp
  thus "Epsilon \<in> lang (Star r)" by simp
qed

(* A language is nullable if it accepts the empty word*)
primrec nullable:: "'a regex \<Rightarrow> bool" 
  where
  "nullable None = False" |
  "nullable (Const w) = (w = Epsilon)" |
  "nullable (Union r1 r2) = ((nullable r1) \<or> (nullable r2))" |
  "nullable (Concat r1 r2) = ((nullable r1) \<and> (nullable r2))" |
  "nullable (Star r) = True"


(* Define derivatives of regular languages *)

primrec deriv :: "'a \<Rightarrow> 'a regex \<Rightarrow> 'a regex"
  where
  "deriv c None = None" |
  "deriv c (Const w) = (if (at w 0) = (Some c) then (Const (fac w 1 (size w))) else None)" |
  "deriv c (Union r1 r2) = Union (deriv c r1) (deriv c r2)" |
  "deriv c (Concat r1 r2) = (if nullable r1 then Union (Concat (deriv c r1) r2) (deriv c r2) else (Concat (deriv c r1) r2))" |
  "deriv c (Star r) = Concat (deriv c r) (Star r)"


(* Lifiting derivatives to words *)
primrec deriv_word:: "'a word \<Rightarrow> 'a regex \<Rightarrow> 'a regex"
  where
  "deriv_word Epsilon r = r" |
  "deriv_word (a . u) r = deriv_word u (deriv a r)"

(* Correctness of word derivatives *)
lemma derivate_correct: "((a . w)  \<in> (lang r)) = (w \<in> (lang (deriv a r)))"
  apply(induct r)
      apply(auto)
  sorry

lemma word_derivate_correct[simp]: "(nullable  (deriv_word w r)) = (w \<in> (lang r))"
  apply(induct w)
   apply(auto)
  sorry

lemma none_empty: "nullable (deriv_word w None) = False"
  apply(induct w)
   apply(auto)
  done
  

(* Define containment a nullability of derivative *)
abbreviation contains:: "'a word \<Rightarrow> 'a regex \<Rightarrow> bool" where "contains w r \<equiv> nullable (deriv_word w r)"


lemma "EX x. contains x (Star (Const (of_list ''ab'')))"
  apply(simp)
  sorry

end