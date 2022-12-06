theory Words        
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





end





