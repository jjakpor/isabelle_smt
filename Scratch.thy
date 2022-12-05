theory Scratch        
  imports Main
begin

no_notation Groups.times_class.times (infixl "*" 70)

datatype 'a  word = Epsilon | Con "'a" "'a word" (infixr "." 67) 

(* Basic Operations *)

primrec at :: "'a word \<Rightarrow> nat \<Rightarrow> 'a option"
  where 
  "at Epsilon i = None" |
  "at (a . w) i = (if i = 0 then Some a else at w (i-1))"



primrec concat:: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word" (infixr "*" 100)
  where
    "concat Epsilon v = v" |
    "concat (Con a u)  v = (Con a (concat u v))" 

primrec rev :: "'a word \<Rightarrow> 'a word"
  where
    "rev Epsilon = Epsilon" |
    "rev (Con a u) = concat (rev u) (a . Epsilon)"

fun fac :: "'a word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word"
  where
   "fac Epsilon s l  = Epsilon" |
   "fac w s 0 = Epsilon" |
   "fac (Con a w) s l = (if s=0 then (Con a (fac w 0 (l-1))) else (fac w (s-1) l))"


lemma epsilon_neutrality[simp]: "w * Epsilon = w \<and> Epsilon * w = w"
  apply(induct_tac w)
   apply(auto)
  done

(* Associativity of word concatenation *)
lemma concat_associativity [simp]: "(u * v) * w = u * (v * w)" 
  apply(induct u)
   apply(auto)
  done

lemma rev_concat [simp]: "rev (w * v) = (rev v) * (rev w)"
  apply(induct_tac w)
   apply(auto)
  done
 
theorem rev_rev: "\<And> w. rev(rev w) = w"
  apply(induct_tac w)
  apply(auto)
  done

(* Conversion *)
primrec of_list:: "'a list \<Rightarrow> 'a word"
  where
  "of_list [] = Epsilon" |
  "of_list (x#xs) = x . (of_list xs)"


lemma "ALL i. i < size w \<Longrightarrow> at (of_list (w)) i  = Some (w!i)"
  apply(induct w)
   apply(auto)
  done




(* Regulars *)
datatype 'a regex = None | Const "'a word" | Union "'a regex" "'a regex" | Concat "'a regex" "'a regex" | Star "'a regex"


primrec pow:: "'a word set \<Rightarrow> nat \<Rightarrow> 'a word set" 
  where
   "pow s 0 = {Epsilon}"|
   "pow s (Suc n) = {u*v |u v. u:s & v:(pow s n)}"

primrec lang:: "'a regex \<Rightarrow> 'a word set" 
  where
   "lang None = {}"|
   "lang (Const w) = {w}" |
   "lang (Union r1 r2) = (lang r1) Un (lang r2)" |
   "lang (Concat r1 r2) = {u*v |u v. u:(lang r1) & v:(lang r2)}"|
   "lang (Star r) = (\<Union>n. pow (lang r) n)"

primrec nullable:: "'a regex \<Rightarrow> bool" 
  where
  "nullable None = False" |
  "nullable (Const w) = ((size w) = 0)" |
  "nullable (Union r1 r2) = ((nullable r1) \<or> (nullable r2))" |
  "nullable (Concat r1 r2) = ((nullable r1) \<and> (nullable r2))" |
  "nullable (Star r) = True"

primrec deriv :: "'a \<Rightarrow> 'a regex \<Rightarrow> 'a regex"
  where
  "deriv c None = None" |
  "deriv c (Const w) = (if (at w 0) = (Some c) then (Const (fac w 1 (size w))) else None)" |
  "deriv c (Union r1 r2) = Union (deriv c r1) (deriv c r2)" |
  "deriv c (Concat r1 r2) = (if nullable r1 then Union (Concat (deriv c r1) r2) (deriv c r2) else (Concat (deriv c r1) r2))" |
  "deriv c (Star r) = Concat (deriv c r) (Star r)"


primrec deriv_word:: "'a word => 'a regex \<Rightarrow> 'a regex"
  where
  "deriv_word Epsilon r = r" |
  "deriv_word (a . u) r = deriv_word u (deriv a r)"



definition contains:: "'a word \<Rightarrow> 'a regex \<Rightarrow> bool" where "contains w r = nullable (deriv_word w r)"

lemma x: "contains Epsilon (Star r)"
  sorry


lemma containment [simp]: "(contains w (Const w)) = (w \<in> (lang (Const w)))"
  sorry
  

lemma "EX x. contains x (Star (Const (of_list ''ab'')))"
  apply(simp)
  done






end





